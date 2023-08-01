use crate::deriving::generic::ty::*;
use crate::deriving::generic::*;
use crate::deriving::path_std;

use rustc_ast::{self as ast, ptr::P, EnumDef, MetaItem};
use rustc_expand::base::{Annotatable, ExtCtxt};
use rustc_span::symbol::{kw, sym, Ident};
use rustc_span::Span;
use thin_vec::{thin_vec, ThinVec};

pub(crate) fn expand_deriving_debug(
    cx: &ExtCtxt<'_>,
    span: Span,
    mitem: &MetaItem,
    item: &Annotatable,
    push: &mut dyn FnMut(Annotatable),
    is_const: bool,
) {
    // &mut ::std::fmt::Formatter
    let fmtr = Ref(Box::new(Path(path_std!(fmt::Formatter))), ast::Mutability::Mut);

    let trait_def = TraitDef {
        span,
        path: path_std!(fmt::Debug),
        skip_path_as_bound: false,
        needs_copy_as_bound_if_packed: true,
        additional_bounds: Vec::new(),
        supports_unions: false,
        methods: vec![MethodDef {
            name: sym::fmt,
            generics: Bounds::empty(),
            explicit_self: true,
            nonself_args: vec![(fmtr, sym::f)],
            ret_ty: Path(path_std!(fmt::Result)),
            attributes: thin_vec![cx.attr_word(sym::inline, span)],
            fieldless_variants_strategy:
                FieldlessVariantsStrategy::SpecializeIfAllVariantsFieldless,
            combine_substructure: combine_substructure(Box::new(|a, b, c| {
                show_substructure(a, b, c)
            })),
        }],
        associated_types: Vec::new(),
        is_const,
    };
    trait_def.expand(cx, mitem, item, push)
}

fn make_table(
    cx: &ExtCtxt<'_>,
    span: Span,
    vdata: &ast::VariantData,
    name: P<ast::Expr>,
    vname: Option<Ident>,
) -> (ast::Stmt, P<ast::Expr>) {
    let [sized_fields @ .., last_field] = vdata.fields() else {
        panic!("make_table assumes at least one field");
    };
    let self_upper = cx.ty_ident(span, Ident::new(kw::SelfUpper, span));
    let has_names = last_field.ident.is_some();

    let row_path = cx.path_global(
        span,
        cx.std_path(&[
            sym::fmt,
            sym::builders,
            if has_names { sym::DebugStructTableRow } else { sym::DebugTupleTableRow },
        ]),
    );
    let mut table_path = cx.path_global(
        span,
        cx.std_path(&[
            sym::fmt,
            sym::builders,
            if has_names { sym::DebugStructTable } else { sym::DebugTupleTable },
        ]),
    );

    let mut rows = ThinVec::with_capacity(sized_fields.len());
    // Using a double reference requires stack space, and therefore prevents tail call
    // optimization. To allow TCO, check whether a double reference is really needed.
    // The function pointer has to be consistent with whether a double reference is
    // passed, so the condition used here is returned to the caller for use determining that.
    let size_of_ref_last = size_of_ref(cx, span, last_field.ty.clone());
    let size_of_ref_unit = size_of_ref(cx, span, cx.ty(span, ast::TyKind::Tup(thin_vec![])));
    let last_needs_fat_ptr =
        cx.expr_binary(span, ast::BinOpKind::Ne, size_of_ref_last, size_of_ref_unit);
    let last_fmt_fat_ptr = opaque_debug_fmt(
        cx,
        span,
        cx.ty_ref(span, last_field.ty.clone(), None, ast::Mutability::Not),
    );
    let last_fmt_thin_ptr = Some(opaque_debug_fmt(cx, span, last_field.ty.clone()));
    let last_fmt =
        cx.expr_if(span, last_needs_fat_ptr.clone(), last_fmt_fat_ptr, last_fmt_thin_ptr);

    for (i, field) in sized_fields.iter().enumerate() {
        // Produce `EnumVariant.field_name`, `field_name`, or `0`, etc.
        let field_ident = struct_field_ident(field, i);
        let offset_path: P<[_]> = vname.into_iter().chain(Some(field_ident)).collect();
        let offset = cx.expr(span, ast::ExprKind::OffsetOf(self_upper.clone(), offset_path));

        let debug_fmt = opaque_debug_fmt(cx, span, field.ty.clone());
        let mut row = thin_vec![
            cx.field_imm(span, Ident::new(sym::fmt, span), debug_fmt),
            cx.field_imm(span, Ident::new(sym::offset, span), offset),
        ];
        if let Some(Ident { name, .. }) = field.ident {
            row.push(cx.field_imm(span, Ident::new(sym::name, span), cx.expr_str(span, name)));
        }
        rows.push(cx.expr_struct(span, row_path.clone(), row));
    }
    let mut table_fields = ThinVec::with_capacity(4);
    table_fields.push(cx.field_imm(span, Ident::new(sym::name, span), name));
    table_fields.push(cx.field_imm(span, Ident::new(sym::last_fmt, span), last_fmt));
    table_fields.push(cx.field_imm(span, Ident::new(sym::fields, span), cx.expr_array(span, rows)));
    if let Some(Ident { name, .. }) = last_field.ident {
        table_fields.push(cx.field_imm(
            span,
            Ident::new(sym::last_name, span),
            cx.expr_str(span, name),
        ));
    }
    let expr = cx.expr_addr_of(
        span,
        cx.expr(
            span,
            ast::ExprKind::ConstBlock(ast::AnonConst {
                id: ast::DUMMY_NODE_ID,
                value: cx.expr_struct(span, table_path.clone(), table_fields),
            }),
        ),
    );
    let rows_ty = cx.ty(span, ast::TyKind::Slice(cx.ty_path(row_path)));
    table_path.segments.last_mut().unwrap().args =
        Some(P(ast::GenericArgs::AngleBracketed(ast::AngleBracketedArgs {
            span,
            args: thin_vec![ast::AngleBracketedArg::Arg(ast::GenericArg::Type(rows_ty))],
        })));
    let mut table_ty = cx.ty_path(table_path);
    table_ty = cx.ty_ref(span, table_ty, Some(cx.lifetime_static(span)), ast::Mutability::Not);
    (
        cx.stmt_let_ty(span, false, Ident::new(sym::values, span), Some(table_ty), expr),
        last_needs_fat_ptr,
    )
}

fn size_of_ref(cx: &ExtCtxt<'_>, span: Span, ty: P<ast::Ty>) -> P<ast::Expr> {
    cx.expr_call(
        span,
        cx.expr_path(cx.path_all(
            span,
            true,
            cx.std_path(&[sym::mem, sym::size_of]),
            vec![ast::GenericArg::Type(cx.ty_ref(span, ty, None, ast::Mutability::Not))],
        )),
        thin_vec![],
    )
}

fn opaque_debug_fmt(cx: &ExtCtxt<'_>, span: Span, ty: P<ast::Ty>) -> P<ast::Expr> {
    let fn_item = cx.expr(
        span,
        ast::ExprKind::Path(
            Some(P(ast::QSelf { path_span: span, position: 3, ty })),
            cx.path_global(span, cx.std_path(&[sym::fmt, sym::Debug, sym::fmt])),
        ),
    );
    let fn_ptr = cx.expr_cast(
        span,
        fn_item,
        cx.ty(
            span,
            ast::TyKind::BareFn(P(ast::BareFnTy {
                unsafety: ast::Unsafe::No,
                ext: ast::Extern::None,
                generic_params: thin_vec![],
                decl: P(ast::FnDecl {
                    inputs: thin_vec![ast::Param {
                    attrs: thin_vec![],
                    ty: cx.ty_infer(span),
                    pat: cx.pat_ident(span, Ident::new(kw::Empty, span)),
                    id: ast::DUMMY_NODE_ID,
                    span,
                    is_placeholder: false,
                }; 2],
                    output: ast::FnRetTy::Ty(cx.ty_infer(span)),
                }),
                decl_span: span,
            })),
        ),
    );

    transmute(cx, span, fn_ptr)
}

fn transmute(cx: &ExtCtxt<'_>, span: Span, expr: P<ast::Expr>) -> P<ast::Expr> {
    let path = cx.std_path(&[sym::mem, sym::transmute]);
    let call = cx.expr_call_global(span, path, thin_vec![expr]);
    cx.unsafe_expr(span, call)
}

/// Takes a reference to anything, returns &core::fmt::rt::Opaque.
fn cast_to_opaque(cx: &ExtCtxt<'_>, span: Span, expr: P<ast::Expr>) -> P<ast::Expr> {
    let opaque_path = cx.path_global(span, cx.std_path(&[sym::fmt, sym::rt, sym::Opaque]));
    cx.unsafe_expr(
        span,
        cx.expr_addr_of(
            span,
            cx.expr_deref(
                span,
                cx.expr_cast(
                    span,
                    cx.expr_cast(
                        span,
                        expr,
                        cx.ty_ptr(span, cx.ty_infer(span), ast::Mutability::Not),
                    ),
                    cx.ty_ptr(span, cx.ty_path(opaque_path), ast::Mutability::Not),
                ),
            ),
        ),
    )
}

fn show_substructure(cx: &ExtCtxt<'_>, span: Span, substr: &Substructure<'_>) -> BlockOrExpr {
    // We want to make sure we have the ctxt set so that we can use unstable methods
    let span = cx.with_def_site_ctxt(span);

    let (ident, vdata, fields) = match substr.fields {
        Struct(vdata, fields) => (substr.type_ident, *vdata, fields),
        EnumMatching(_, v, fields) => (v.ident, &v.data, fields),
        AllFieldlessEnum(enum_def) => return show_fieldless_enum(cx, span, enum_def, substr),
        EnumDiscr(..) | StaticStruct(..) | StaticEnum(..) => {
            cx.dcx().span_bug(span, "nonsensical .fields in `#[derive(Debug)]`")
        }
    };

    let name = cx.expr_str(span, ident.name);
    let fmt = substr.nonselflike_args[0].clone();

    if let Some(last) = fields.last() {
        let vname = matches!(substr.fields, EnumMatching(..)).then_some(ident);
        let (table, last_needs_fat_ptr) = make_table(cx, span, vdata, name, vname);

        // Unsized types need an extra indirection, but only the last field
        // may be unsized.
        let ref_last = cx.expr_if(
            span,
            last_needs_fat_ptr,
            cast_to_opaque(cx, span, cx.expr_addr_of(last.span, last.self_expr.clone())),
            Some(cast_to_opaque(cx, span, last.self_expr.clone())),
        );

        let fn_path = cx.std_path(&[
            sym::fmt,
            if last.name.is_some() {
                sym::write_debug_struct_table
            } else {
                sym::write_debug_tuple_table
            },
        ]);

        let args = thin_vec![
            cast_to_opaque(cx, span, cx.expr_self(span)),
            fmt,
            cx.expr_ident(span, Ident::new(sym::values, span)),
            ref_last,
        ];
        let expr = cx.expr_call_global(span, fn_path, args);

        BlockOrExpr::new_mixed(thin_vec![table], Some(expr))
    } else {
        // Special case for no fields.
        let fn_path_write_str = cx.std_path(&[sym::fmt, sym::Formatter, sym::write_str]);
        let expr = cx.expr_call_global(span, fn_path_write_str, thin_vec![fmt, name]);
        BlockOrExpr::new_expr(expr)
    }
}

/// Special case for enums with no fields. Builds:
/// ```text
/// impl ::core::fmt::Debug for A {
///     fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
///          ::core::fmt::Formatter::write_str(f,
///             match self {
///                 A::A => "A",
///                 A::B() => "B",
///                 A::C {} => "C",
///             })
///     }
/// }
/// ```
fn show_fieldless_enum(
    cx: &ExtCtxt<'_>,
    span: Span,
    def: &EnumDef,
    substr: &Substructure<'_>,
) -> BlockOrExpr {
    let fmt = substr.nonselflike_args[0].clone();
    let arms = def
        .variants
        .iter()
        .map(|v| {
            let variant_path = cx.path(span, vec![substr.type_ident, v.ident]);
            let pat = match &v.data {
                ast::VariantData::Tuple(fields, _) => {
                    debug_assert!(fields.is_empty());
                    cx.pat_tuple_struct(span, variant_path, ThinVec::new())
                }
                ast::VariantData::Struct { fields, .. } => {
                    debug_assert!(fields.is_empty());
                    cx.pat_struct(span, variant_path, ThinVec::new())
                }
                ast::VariantData::Unit(_) => cx.pat_path(span, variant_path),
            };
            cx.arm(span, pat, cx.expr_str(span, v.ident.name))
        })
        .collect::<ThinVec<_>>();
    let name = cx.expr_match(span, cx.expr_self(span), arms);
    let fn_path_write_str = cx.std_path(&[sym::fmt, sym::Formatter, sym::write_str]);
    BlockOrExpr::new_expr(cx.expr_call_global(span, fn_path_write_str, thin_vec![fmt, name]))
}

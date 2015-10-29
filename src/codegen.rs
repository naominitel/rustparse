// common codegen functions

use std::collections::{hash_map, HashMap};

use syntax::{ast, codemap, parse, ptr};
use syntax::ext::base::ExtCtxt;
use syntax::ext::build::AstBuilder;

use grammar;

// creates a variant with the given name and type
fn make_variant(ident: ast::Ident, ty: ptr::P<ast::Ty>, sp: codemap::Span)
                -> ptr::P<ast::Variant> {
    ptr::P(codemap::Spanned {
        span: sp,
        node: ast::Variant_ {
            name: ident,
            attrs: vec!(),
            kind: ast::TupleVariantKind(vec![
                ast::VariantArg { id: ast::DUMMY_NODE_ID, ty: ty }
            ]),
            id: ast::DUMMY_NODE_ID,
            disr_expr: None,
        }
    })
}

pub struct ParserEnums {
    pub token: ptr::P<ast::Item>,
    pub data: ptr::P<ast::Item>,
    pub next_tok: ptr::P<ast::Item>,
    pub data_variants: HashMap<ptr::P<ast::Ty>, ast::Ident>,
}

pub fn parser_enums(grammar: &grammar::Grammar, cx: &mut ExtCtxt) -> ParserEnums {
    let sp = cx.original_span();

    // yytype. the type of the data accumulated on the data stack and that
    // are pushed back and forth by actions. just a big enum that can handle
    // all possible types for all tokens and non terminals we also remember
    // the association between a type and the corresponding constructor in
    // the yytype enum
    let yytype_name = parse::token::gensym_ident("YYTYPE");
    let mut yyvariants = HashMap::new();
    let mut yytype_variants = Vec::with_capacity(grammar.terminals.len() +
                                                 grammar.nonterms.len());

    // we also generate the Token type and the match to convert input tokens
    // into their internal representation as an integer. this match must also
    // return the data associated to that token to be pushed onto the data stack.
    let mut tok_variants  = Vec::with_capacity(grammar.terminals.len());
    let mut next_tok_arms = Vec::with_capacity(grammar.terminals.len());

    {
        // creates a variant in the yytype enum for the given type
        let mut make_yy_variant = |ty| {
            let variant = parse::token::gensym_ident("");
            yytype_variants.push(make_variant(variant, ty, sp));
            variant
        };

        // first create variants for the types of all nonterminal symbols
        for sym in grammar.nonterms.iter() {
            match yyvariants.entry(sym.ty.clone()) {
                hash_map::Entry::Occupied(_) => (),
                hash_map::Entry::Vacant(v) => {
                    v.insert(make_yy_variant(sym.ty.clone()));
                }
            }
        }

        // this counter generates the internal
        // representation of the tokens
        let mut tok_repr = 0;

        for term in grammar.terminals.iter() {
            // create a variant in the yytype enum
            let yy_variant_name = *match yyvariants.entry(term.ty.clone()) {
                hash_map::Entry::Occupied(ident) => ident.into_mut(),
                hash_map::Entry::Vacant(v) => v.insert(make_yy_variant(term.ty.clone()))
            };

            // the path of the variant in the token type
            let path = cx.path(sp, vec!(cx.ident_of("Token"), term.name));

            // we create an arm for the match which binds the
            // data inside the token to a gensymed ident
            let data_ident = parse::token::gensym_ident("");
            let pattern = cx.pat_enum(sp, path, vec!(cx.pat_ident(sp, data_ident)));

            // the yytype variant for the type of this token
            let data_expr = cx.expr_call(sp,
                cx.expr_path(cx.path(sp, vec![yytype_name, yy_variant_name])),
                vec![cx.expr_ident(sp, data_ident)]
            );

            // the action of the arm. pushes the data onto the
            // stack and then returns the token representation
            let ret_expr = cx.expr_usize(sp, tok_repr);

            next_tok_arms.push(cx.arm(sp,
                vec!(pattern),
                quote_expr!(cx, ($data_expr, $ret_expr))
            ));

            // create a variant in the Token type
            // (external representation of the tokens)
            tok_variants.push(make_variant(term.name, term.ty.clone(), sp));
            tok_repr += 1;
        }
    }

    // finally create the external token and the yytype enum types
    // token must be created by hand because ExtCtxt doesn't let
    // us make it "pub" easily and it is part of the external interface...
    let yytype_enum = ast::ItemEnum(
        ast::EnumDef { variants: yytype_variants },
        ast::Generics {
            lifetimes: vec!(),
            ty_params: ::syntax::owned_slice::OwnedSlice::empty(),
            where_clause: ast::WhereClause {
                id: ast::DUMMY_NODE_ID,
                predicates: vec!()
            }
        }
    );

    let derive = parse::token::InternedString::new("derive");
    let debug = parse::token::InternedString::new("Debug");
    let item = cx.meta_list(sp, derive, vec![cx.meta_word(sp, debug)]);
    let attr = cx.attribute(sp, item);
    let yytype_def = cx.item(sp, yytype_name, vec![attr.clone()], yytype_enum);

    let token = ptr::P(ast::Item {
        ident: cx.ident_of("Token"),
        attrs: vec![attr],
        id: ast::DUMMY_NODE_ID,
        node: ast::ItemEnum(
            ast::EnumDef { variants: tok_variants },
            ast::Generics {
                lifetimes: vec!(),
                ty_params: ::syntax::owned_slice::OwnedSlice::empty(),
                where_clause: ast::WhereClause {
                    id: ast::DUMMY_NODE_ID,
                    predicates: vec!()
                }
            }
        ),
        vis: ast::Public,
        span: sp
    });

    // ew.
    let eof = grammar.terminals.len();

    let next_tok = quote_item!(cx,
        fn next_token<'a, T>(lexer: &mut T) -> ($yytype_name, usize)
            where T: Iterator<Item = Token> {
            let tok = match lexer.next() {
                Some(t) => t,
                None => return (unsafe { ::std::mem::uninitialized() }, $eof)
            };

            match tok { $next_tok_arms }
        }
    ).unwrap();

    ParserEnums {
        token: token,
        data: yytype_def,
        next_tok: next_tok,
        data_variants: yyvariants,
    }
}

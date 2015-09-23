use std::collections::hash_map::{HashMap, Entry};

use syntax::{ast, ptr};
use syntax::codemap;
use syntax::ext::base::ExtCtxt;
use syntax::parse::{parser, token};

// utility "do while" macro. useful to parse FOO+ like sequences
macro_rules! dow {
    ($blk:block while $cond:expr) => (loop { $blk if !$cond { break } })
}

// generates a dummy unit type used when no type
// annotation is provided, with a dummy span
#[macro_export]
macro_rules! make_unit {
    () => (::syntax::ptr::P(::syntax::ast::Ty {
        id: ::syntax::ast::DUMMY_NODE_ID,
        node: ::syntax::ast::TyTup(vec!()),
        span: ::syntax::codemap::DUMMY_SP
    }))
}

// this is the parser for grammar descriptions
// it's called grammar and not parser because this would be too confusing with
// the generated parser. this also exports type definitions for the interal
// representation of the grammar that are used in the rest of the code

// final exported representatiom (AST) of the grammar
// a grammar is made of
// * a set of terminals (tokens)
// * a set of non-terminals
// * a set of production rules of the form
//   non-terminal -> (terminal or non-terminal)*
// rules have actions attached to them.
// terminals and non-terminals have types attached to them

// a single symbol (terminal or not) as it
// may appear in the right-hand side of a rule
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Symbol {
    Term(usize),
    NonTerm(usize)
}

// an argument is a symbol optionnaly bound to
// an identifier that can be used to reference
// the data attached to the symbol in an action
pub type Arg = (Symbol, Option<ast::Ident>);

// an action is just Rust code
pub type Action = ptr::P<ast::Expr>;

pub struct Rule {
    pub args: Vec<Arg>,
    pub action: Option<Action>
}

// a non-terminal symbol.ast.terminals.push( references the
// rules that have this non-terminal as LHS
pub struct NonTerminal {
    pub name: ast::Ident,
    pub span: codemap::Span,
    pub productions: Vec<usize>,
    pub ty: ptr::P<ast::Ty>
}

pub struct Terminal {
    pub name: ast::Ident,
    pub span: codemap::Span,
    pub ty: ptr::P<ast::Ty>
}

pub struct Grammar {
    pub nonterms: Vec<NonTerminal>,
    pub terminals: Vec<Terminal>,
    pub rules: Vec<Rule>
}

impl Grammar {
    pub fn gen_nonterm(&mut self) -> usize {
        let idx = self.nonterms.len();
        self.nonterms.push(NonTerminal {
            name: token::gensym_ident(""),
            span: codemap::DUMMY_SP,
            productions: Vec::new(),
            ty: make_unit!()
        });
        idx
    }

    pub fn gen_term(&mut self) -> usize {
        let idx = self.terminals.len();
        self.terminals.push(Terminal {
            name: token::gensym_ident(""),
            span: codemap::DUMMY_SP,
            ty: make_unit!()
        });
        idx
    }
}

// first stage of the parser. this first pass tries to parse all rules and
// token definitions. since the definitions can be in any order and mutually
// recursive, wa cannot check yet that every symbol used is well defined. but
// we can check that there are no multiple definitions of a single symbol name
// (terminal or non-terminal).

pub enum EBNFExpr {
    // reflexive, transitive closure, i.e. Foo*
    RTClosure,
    // transitive closure, i.e. Foo+
    TClosure,
    Maybe,
}

type IdRef = (codemap::Span, ast::Ident);

pub enum Expr<T> {
    Id(T),
    Ext(EBNFExpr, Vec<Expr<T>>)
}

// at this stage, we don't know yet wether the
// symbols in a rule are terminals or tokens
// an argument is optionnally bound to a name
// to refer to it in the associated action
struct UncheckedArg {
    expr: Expr<IdRef>,
    binding: Option<ast::Ident>
}

// contains all the alternative rules for a single
// non-terminal, since all alternatives must be
// defined at a single place in the input grammar.
struct UncheckedRule {
     symbol: usize,
     rules: Vec<(Vec<UncheckedArg>, Option<Action>)>
}

// unchecked grammar. contains data harvested
// during the first pass of the parser:
// * list of unchecked rules
// * an interner that contains bindings of
//   I the formdent number -> symbol number
//   we remap because having symbol numbers that range from
//   0 to some number without gaps allows much simpler code
//   when processing the grammar by the generators
struct ParseContext<'a, 'b> where 'b: 'a {
    rules: Vec<UncheckedRule>,
    nonterms: Vec<NonTerminal>,
    terminals: Vec<Terminal>,
    interner: HashMap<ast::Ident, Symbol>,
    cx: &'a mut ExtCtxt<'b>
}

// tries to parse a sequence of one or more expressions.
// stops whenever it encounters a token that cannot start
// an expression, and returns without consuming it
fn parse_sequence(parser: &mut parser::Parser) -> Vec<Expr<IdRef>> {
    // make sure we have at least one expr
    let mut ret = match parse_expr(parser) {
        Some(expr) => vec!(expr),
        None => panic!(parser.unexpected())
    };

    while let Some(expr) = parse_expr(parser) {
        ret.push(expr);
    }

    ret
}

// tries to parse an expression.  returns Some(expr)
// in case of success and None if the first token is
// not a valid start of expression
fn parse_expr(parser: &mut parser::Parser) -> Option<Expr<IdRef>> {
    match parser.token {
        token::Ident(id, _) => {
            let sym = Expr::Id((parser.span, id));
            parser.bump().ok().unwrap();

            let ext_expr = match parser.token {
                token::BinOp(token::Star) => EBNFExpr::RTClosure,
                token::BinOp(token::Plus) => EBNFExpr::TClosure,
                token::Question => EBNFExpr::Maybe,
                _ => return Some(sym)
            };

            // EBNF extended expression
            parser.bump().ok().unwrap();
            Some(Expr::Ext(ext_expr, vec!(sym)))
        }

        token::OpenDelim(token::Paren) => {
            parser.bump().ok().unwrap();
            let seq = parse_sequence(parser);
            parser.expect(&token::CloseDelim(token::Paren))
                .unwrap_or_else(|e| panic!(e));
            
            // parenthesized expressions can only be part of an EBNF extended
            // expression, which means we must have + or * or ? here
            let ext_expr = match parser.bump_and_get() {
                Ok(token::BinOp(token::Star)) => EBNFExpr::RTClosure,
                Ok(token::BinOp(token::Plus)) => EBNFExpr::TClosure,
                Ok(token::Question) => EBNFExpr::Maybe,
                Ok(tok) => panic!(parser.unexpected_last(&tok)),
                Err(err) => panic!(err)
            };

            Some(Expr::Ext(ext_expr, seq))
        }

        _ => return None
    }
}

// tries to parse an arguments returns Some(args) an in
// case of success, and None if the first token cannot start argument
fn parse_arg(parser: &mut parser::Parser) -> Option<UncheckedArg> {
    if parser.token == token::OpenDelim(token::Paren) {
        // maybe we have a binding here
        // ew.
        if let Some(id) = parser.look_ahead(1, |t| {
                if let token::Ident(id, _) = *t { Some(id) } else { None }
            }) {
            if parser.look_ahead(2, |t| *t == token::Colon) {
                parser.bump().ok().unwrap();
                parser.bump().ok().unwrap();
                parser.bump().ok().unwrap();

                let ret = match parse_expr(parser) {
                    Some(expr) => Some(UncheckedArg {
                        expr: expr,
                        binding: Some(id)
                    }),
                    None => panic!(parser.unexpected())
                };
                parser.expect(&token::CloseDelim(token::Paren))
                    .unwrap_or_else(|e| panic!(e));
                return ret;
            }
        }
    }

    parse_expr(parser).map(|e| UncheckedArg { expr: e, binding: None })
}

// parse an argument sequence. each argument is either a bounded
// sequence like (x: FOO BAR BAZ) or just an expression like FOO
// stops whenever it encounters a token that cannot starts an
// argument, and returns without consuming it
fn parse_args(parser: &mut parser::Parser) -> Vec<UncheckedArg> {
    // make sure we have at least one argument
    let mut ret = match parse_arg(parser) {
        Some(arg) => vec!(arg),
        None => panic!(parser.unexpected())
    };

    while let Some(arg) = parse_arg(parser) {
        ret.push(arg);
    }

    ret
}

// parse a sequence of non-terminal definitions (i.e. production rules)
// or terminal definitions of the form token NAME (: TYPE)? ;
// tries to parse rules until it reaches the end of the file
fn parse_rules(parser: &mut parser::Parser, ctxt: &mut ParseContext) {
    let tok_kwd = token::intern("token");
    let empty_kwd = token::intern("empty");

    while parser.token != token::Eof {
        let id = parser.parse_ident().unwrap_or_else(|e| panic!(e));
        let sp = parser.span;

        let (id, sym) = if id.name == tok_kwd {
            // this is a token declaration
            let term = parser.parse_ident().unwrap_or_else(|e| panic!(e));
            let ty = match parser.bump_and_get().unwrap_or_else(|e| panic!(e)) {
                token::Colon => {
                    let ty = parser.parse_ty();
                    parser.expect(&token::Semi).unwrap_or_else(|e| panic!(e));
                    ty
                }
        
                token::Semi => make_unit!(),
                tok => panic!(parser.unexpected_last(&tok))
            };

            let idx = ctxt.terminals.len();
            ctxt.terminals.push(Terminal {
                name: term,
                span: sp,
                ty: ty
            });

            (term, Symbol::Term(idx))
        } else {
            // this is a non-terminal declaration
            // rule ::= ID (: ty)? (::=) (productions (| productions+))? ;
        
            // optionnal type annotation
            let ty =
                if parser.eat(&token::RArrow).unwrap_or_else(|e| panic!(e)) {
                    parser.parse_ty()
                }
                else { make_unit!() };

            // ::=
            parser.expect(&token::ModSep).unwrap_or_else(|e| panic!(e));
            parser.expect(&token::Eq).unwrap_or_else(|e| panic!(e));

            // alternatives
            let mut productions = Vec::new();
            dow!({
                let args = match parser.token {
                    token::Ident(id, _) if id.name == empty_kwd => {
                        parser.bump().ok().unwrap();
                        vec!()
                    }
                    _ => parse_args(parser)
                };

                let expr =
                    if parser.eat(&token::FatArrow).unwrap_or_else(|e| panic!(e)) {
                        Some(parser.parse_expr())
                    }
                    else { None };

                productions.push((args, expr));
            } while match parser.bump_and_get().unwrap_or_else(|e| panic!(e)) {
                token::Semi => false,
                token::Comma => true,
                tok => panic!(parser.unexpected_last(&tok))
            });

            let idx = ctxt.nonterms.len();
            ctxt.nonterms.push(NonTerminal {
                name: id,
                span: sp,
                productions: Vec::with_capacity(productions.len()),
                ty: ty
            });

            ctxt.rules.push(UncheckedRule { symbol: idx, rules: productions });
            (id, Symbol::NonTerm(idx))
        };

        // only check that now, so that the parsing
        // can continue and detect more errors
        match ctxt.interner.entry(id) {
            Entry::Occupied(v) => match *v.get() {
                Symbol::NonTerm(idx) => {
                    let nonterm = &ctxt.nonterms[idx];
                    parser.span_err(sp, &format!("redifinition of symbol {}",
                                                 nonterm.name.name.as_str())[..]);
                    parser.span_note(nonterm.span, "previous definition was here");
                }

                Symbol::Term(idx) => {
                    let term = &ctxt.terminals[idx];
                    parser.span_err(sp, &format!("redefinition of terminal {}",
                                                 term.name.name.as_str())[..]);
                    parser.span_note(term.span, "previous definition was here");
                }
            },

            Entry::Vacant(v) => { v.insert(sym); }
        }
    }
}

// now that we gathered all terms and nonterms definitions, we
// check that there are no undefined symbols left in the rules,
// and flags them as terminals or non-terminals, repsectively
// during this, will expand EBNF expressions into something
// more appropriate for the grammar class we're parsing

pub trait EBNFExpander {
    fn expand(expr: EBNFExpr, symbols: Vec<Symbol>, grammar: &mut Grammar)
        -> (usize, Vec<Vec<Expr<Symbol>>>);
}

fn check_and_expand<T>(rules: ParseContext) -> Grammar where T: EBNFExpander {
    let ParseContext { nonterms, terminals, rules, mut interner, mut cx } = rules;
    let mut ret = Grammar {
        terminals: terminals,
        nonterms: nonterms,
        rules: Vec::with_capacity(rules.capacity())
    };

    // track already expanded expressions to
    // avoid duplicate generated rules. we
    // remember (expression, symbol) pairs
    // where symbol is a non-term which produces
    // the expansion of the expression
    let mut exp_map = HashMap::new();

    fn expand_expr<T>(expr: Expr<Symbol>, exp_map: &mut HashMap<Vec<Symbol>, usize>,
                      grammar: &mut Grammar) -> Symbol where T: EBNFExpander {
        match expr {
            Expr::Id(s) => s,
            Expr::Ext(e, exprs) => {
                let syms: Vec<Symbol> = exprs.into_iter()
                    .map(|e| expand_expr::<T>(e, exp_map, grammar))
                    .collect();

                match exp_map.get(&syms) {
                    Some(v) => return Symbol::NonTerm(*v),
                    None => ()
                }

                let (exp, rules) = <T as EBNFExpander>::expand(e, syms.clone(),
                                                               grammar);
                let rules = rules.into_iter().map(|r| {
                    let rule = r.into_iter().map(|expr|
                        (expand_expr::<T>(expr, exp_map, grammar), None)
                    ).collect();

                    let idx = grammar.rules.len();
                    grammar.rules.push(Rule { args: rule, action: None });
                    idx
                }).collect();

                grammar.nonterms[exp].productions = rules;
                exp_map.insert(syms, exp);
                Symbol::NonTerm(exp)
            }
        }
    };
    
    fn check_and_expand_expr<T>(expr: Expr<IdRef>,
                                exp_map: &mut HashMap<Vec<Symbol>, usize>,
                                interner: &mut HashMap<ast::Ident, Symbol>,
                                cx: &mut ExtCtxt, grammar: &mut Grammar)
                                -> Symbol where T: EBNFExpander {
        match expr {
            Expr::Id((sp, id)) => match interner.get(&id) {
                Some(&sym) => sym,
                None => cx.span_fatal(sp,
                    &format!("undefined symbol {}", id.name.as_str())[..]
                )
            },

            Expr::Ext(expr, ids) => {
                let syms = ids.into_iter()
                    .map(|e| Expr::Id(
                        check_and_expand_expr::<T>(e, exp_map, interner, cx, grammar))
                    ).collect();
                expand_expr::<T>(Expr::Ext(expr, syms), exp_map, grammar)
            }
        }
    };

    for unchecked_rule in rules.into_iter() {
        for (alt, action) in unchecked_rule.rules.into_iter() {
            let rule: Vec<Arg> = alt.into_iter().map(|arg|
                (check_and_expand_expr::<T>(arg.expr, &mut exp_map,  &mut interner,
                                            &mut cx, &mut ret), arg.binding)
            ).collect();

            let idx = ret.rules.len();
            ret.rules.push(Rule { args: rule, action: action });
            ret.nonterms[unchecked_rule.symbol].productions.push(idx);
        }
    }

    ret
}

// parse a grammar definition
// a grammar definition is made of
//  * zero or more token (terminal) definitions
//  * zero or more non-terminal definitions (production rules)
pub fn parse<T>(args: Vec<ast::TokenTree>, cx: &mut ExtCtxt)
                -> Grammar where T: EBNFExpander {
    let mut parser = ::syntax::parse::new_parser_from_tts(
        cx.parse_sess, cx.cfg.clone(), args
    );

    let mut ctxt = ParseContext {
        terminals: Vec::new(),
        nonterms: Vec::new(),
        rules: Vec::new(),
        interner: HashMap::new(),
        cx: cx
    };

    parse_rules(&mut parser, &mut ctxt);
    parser.abort_if_errors();
    check_and_expand::<T>(ctxt)
}

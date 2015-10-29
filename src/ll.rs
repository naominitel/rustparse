use std::collections::HashSet;
use std::fmt::Write;

use syntax::{ast, parse, ptr};
use syntax::ext::base::ExtCtxt;
use syntax::ext::build::AstBuilder;
use syntax::ext::quote::rt::ToTokens;

use codegen;
use grammar;
use grammar::Symbol;

pub struct LL;

// expands EBNF expression according to the Extended-LL
// grammar class, to product an LL grammar
impl grammar::EBNFExpander for LL {
    fn expand(expr: grammar::EBNFExpr, syms: Vec<Symbol>,
              grammar: &mut grammar::Grammar)
              -> (usize, Vec<Vec<grammar::Expr<Symbol>>>) {
        let sym = grammar.gen_nonterm();
        let mut rule: Vec<grammar::Expr<Symbol>> =
            syms.into_iter().map(|s| grammar::Expr::Id(s)).collect();

        (sym, match expr {
            grammar::EBNFExpr::RTClosure => {
                // expand foo* into foo_list ::= empty | foo_list foo
                rule.push(grammar::Expr::Id(Symbol::NonTerm(sym)));
                vec![vec![], rule]
            }

            grammar::EBNFExpr::TClosure => {
                // expand foo* into foo_list ::= empty | foo foo*
                rule.push(grammar::Expr::Ext(
                    grammar::EBNFExpr::RTClosure,
                    vec![grammar::Expr::Id(Symbol::NonTerm(sym))]
                ));
                vec![vec![], rule]
            }

            grammar::EBNFExpr::Maybe => {
                // expand foo* into foo_list ::= empty | foo
                vec![vec![], rule]
            }
        })
    }
}

// first compute the FIRST sets for every non-terminal
// in the grammar. this is a fix point-search until
// we cannot add more symbols to any set anymore

pub struct FirstSet {
    pub set: HashSet<usize>,
    pub epsilon: bool
}

pub fn firsts(grammar: &grammar::Grammar) -> Vec<FirstSet> {
    let mut ret = Vec::with_capacity(grammar.nonterms.len());
    for _ in 0 .. grammar.nonterms.len() {
        ret.push(FirstSet {
            set: HashSet::new(),
            epsilon: false
        })
    }

    // fix point search
    let mut fp = false;
    while !fp {
        fp = true;

        for idx in 0 .. grammar.nonterms.len() {
            let ref nonterm = grammar.nonterms[idx];
            'a: for &rule in nonterm.productions.iter() {
                for &(sym, _) in grammar.rules[rule].args.iter() {
                    match sym {
                        // if we encounter an opaque symbol (i.e. either a
                        // terminal of a non-terminal that does not derive
                        // epsilon, we just stop processing this rule. This
                        // is done with "continue 'a"

                        Symbol::Term(sym) => {
                            fp &= !ret[idx].set.insert(sym);
                            continue 'a
                        }

                        Symbol::NonTerm(sym) => {
                            // trick to be able to access mutably ret[idx]
                            // while ret[sym] is immutabily borrowed. this
                            // is safe since the case sym == idx doesn't
                            // interest us anyway...
                            let ((sub1, sub2), idx1, idx2) =
                                if sym > idx {
                                    let (fst, snd) = ret.split_at_mut(sym);
                                    ((snd, fst), 0, idx)
                                } else if sym < idx {
                                    (ret.split_at_mut(idx), sym, 0)
                                } else { continue };

                            for &s in sub1[idx1].set.iter() {
                                fp &= !sub2[idx2].set.insert(s);
                            }

                            if !sub1[idx1].epsilon { continue 'a }
                        }
                    }
                }

                // if we arrive here without jumping to the next
                // iteration of 'a, it means all the symbols in
                // this production devive epsilon, or there are
                // no symbols (i.e. this is a e-rule) so:
                fp &= ret[idx].epsilon;
                ret[idx].epsilon = true;
            }
        }
    }

    ret
}

// similarly, we can then compute the follow sets for
// every non-terminal. this is again a fix-point search.
// in the meantime, we also compute the first sets of
// whole sentences that appear as RHS

type FollowSet = HashSet<usize>;

fn follow(grammar: &grammar::Grammar, firsts: &Vec<FirstSet>)
          -> (Vec<FollowSet>, Vec<FirstSet>) {
    let mut rules_firsts = Vec::with_capacity(grammar.rules.len());
    let mut follows = Vec::with_capacity(grammar.nonterms.len());

    for _ in 0 .. grammar.nonterms.len() {
        follows.push(HashSet::new())
    }

    for _ in 0 .. grammar.rules.len() {
        rules_firsts.push(FirstSet {
            set: HashSet::new(),
            epsilon: false
        });
    }

    let mut fp = true;

    // we do a first pass to compute the rules_firsts sets
    // FIXME: currently all following iterations will re-
    // compute the accu. we could store it but this would
    // represent quite an amout of memory... we could also
    // remove accu and re-compute it each time it is needed
    // by first if !first.epsilon or first U follow(LHF) in
    // the other case... but that would be slower.
    for idx in 0 .. grammar.nonterms.len() {
        let ref nonterm = grammar.nonterms[idx];
        for &rule in nonterm.productions.iter() {
            // FIRST set of the suffix of the sentence at a
            // given point. one can view this as the set of
            // symbols that will be added to the FOLLOW set
            // of the next non-terminal we will process. at
            // the end of the iteration, it will correspond
            // to the first set of the whole sentence (with
            // the exception described below)
            // initially, it contains the FOLLOW set of
            // the non-terminal that this rule produces
            let mut accu = follows[idx].clone();

            // the first set of the whole sentence. same
            // that the accu, except that this one does
            // not contain the FOLLOW from the LHS
            let mut first = FirstSet {
                set: HashSet::new(),
                epsilon: true
            };

            for &(sym, _) in grammar.rules[rule].args.iter().rev() {
                // let's browse the sentence backward so that we
                // compute the FIRST set of the suffix as we progress
                match sym {
                    // when encountering a terminal, the suffix of the
                    // sentence becomes opaque, so we have to drop the
                    // accumulated tokens, and continue with this
                    // only terminal.,
                    Symbol::Term(sym) => {
                        accu.clear();
                        accu.insert(sym);
                        first.set.clear();
                        first.set.insert(sym);
                        first.epsilon = false;
                    }

                    Symbol::NonTerm(sym) => {
                        for &s in accu.iter() {
                            fp &= !follows[sym].insert(s);
                        }

                        // if we encounter a non-terminal which does
                        // NOT derive epsilon, the same happens than
                        // for a terminal (see the comment above)
                        if !firsts[sym].epsilon {
                            accu.clear();
                            first.set.clear();
                            first.epsilon = false;
                        }

                        // in any case, all the FIRST items of this
                        // symbol will be added to future follow sets
                        // if we do not encounter other opaque symbols
                        for &s in firsts[sym].set.iter() {
                            accu.insert(s);
                            first.set.insert(s);
                        }
                    }
                }
            }

            rules_firsts[rule] = first;
        }
    }

    // now find the fix point
    while !fp {
        fp = true;
        for idx in 0 .. grammar.nonterms.len() {
            let ref nonterm = grammar.nonterms[idx];
            for &rule in nonterm.productions.iter() {
                // same as above but with only accu
                let mut accu = follows[idx].clone();
                for &(sym, _) in grammar.rules[rule].args.iter().rev() {
                    match sym {
                        Symbol::Term(sym) => {
                            accu.clear();
                            accu.insert(sym);
                        }

                        Symbol::NonTerm(sym) => {
                            for &s in accu.iter() {
                                fp &= !follows[sym].insert(s);
                            }

                            if !firsts[sym].epsilon {
                                accu.clear();
                            }

                            for &s in firsts[sym].set.iter() {
                                accu.insert(s);
                            }
                        }
                    }
                }
            }
        }
    }

    (follows, rules_firsts)
}

// FIXME: using 0 for errors would be better than using Some since
// this divides by 2 memory required to store the table at run time
type ParseTable = Vec<Vec<Option<usize>>>;
enum Error {
    Conflict(usize, usize, usize)
}

// with the first and follow sets we have enough
// information to construct a parse table
fn parse_table(grammar: &grammar::Grammar, follow: &Vec<FollowSet>,
               rules_firsts: &Vec<FirstSet>) -> Result<ParseTable, Error> {
    let mut ret = Vec::with_capacity(rules_firsts.len());

    for idx in 0 .. grammar.nonterms.len() {
        let mut entries = Vec::with_capacity(grammar.terminals.len());
        for _ in 0 .. grammar.terminals.len() {
            entries.push(None);
        }

        let ref nonterm = grammar.nonterms[idx];
        for &rule in nonterm.productions.iter() {
            for &first in rules_firsts[rule].set.iter() {
                match entries[first] {
                    None => entries[first] = Some(rule),
                    Some(r) => return Err(Error::Conflict(r, rule, first))
                }
            }

            if rules_firsts[rule].epsilon {
                for &follow in follow[idx].iter() {
                    match entries[follow] {
                        None => entries[follow] = Some(rule),
                        Some(r) => return Err(Error::Conflict(r, rule, follow))
                    }
                }
            }
        }

        ret.push(entries);
    }

    Ok(ret)
}

fn codegen(mut grammar: grammar::Grammar, table: &ParseTable, cx: &mut ExtCtxt)
           -> Vec<ptr::P<ast::Item>> {
    let sp = cx.original_span();

    // remove the eof token as we must not process it further. keep
    // its index, which will be used as its internal representation
    let eof = cx.expr_usize(sp, grammar.terminals.len() - 1);
    grammar.terminals.pop();

    let enums = codegen::parser_enums(&grammar, cx);
    let yytype_name = enums.data.ident;

    // will be used later to generate match statements. we generate
    // a fallback arm (that is never supposed to be used anyay...)
    // only when we can have more than a single type on the stack
    let unreachable =
        if enums.data_variants.len() > 1 { Some(cx.arm_unreachable(sp)) }
        else { None };

    // generate a static array for each rule. the generated parse table
    // will only contain slices to them. we need indirection here because
    // those arrays are not of the same size, hence the impossibility of
    // directly inlining them into the parse table entries... :(
    let mut rules = Vec::with_capacity(grammar.rules.len());

    for rule_no in 0 .. grammar.rules.len() {
        let rule = &grammar.rules[rule_no].args[..];
        let mut vec = Vec::with_capacity(rule.len());
        for &(sym, _) in rule.iter() {
            vec.push(match sym {
                Symbol::Term(sym) =>
                    cx.expr_call(sp,
                        quote_expr!(cx, Step::Term),
                        vec!(cx.expr_usize(sp, sym))
                    ),
                Symbol::NonTerm(sym) =>
                    cx.expr_call(sp,
                        quote_expr!(cx, Step::NonTerm),
                        vec!(cx.expr_usize(sp, sym))
                    )
            });
        }

        let count = cx.expr_usize(sp, rule.len());
        let static_value = cx.expr_vec(sp, vec);
        let ident = cx.ident_of(&format!("RULE_{}", rule_no)[..]);
        rules.push(quote_item!(cx,
            static $ident: [Step; $count] = $static_value;
        ).unwrap());
    }

    // also generate the actions table, as an array of function pointers
    // FIXME: for now we assume we can just map the rules number on the
    // number of the LHS nonterm plus an offset, which happens to be the
    // case because of the way we build the grammar, but we should change
    // the representation to have stronger static guarantees
    let mut actions_funs = Vec::with_capacity(table.len());
    let mut rule_no = 0;

    for nonterm in grammar.nonterms.iter() {
        for &prod in nonterm.productions.iter() {
            let rule = &mut grammar.rules[prod];

            let arg_ident = parse::token::gensym_ident("stack");
            let arg = cx.arg(sp, arg_ident, quote_ty!(cx, &mut Vec<$yytype_name>));

            // generate the action. first we need to generate code to
            // retreive the data from bound symbols from the stack
            let mut statements = Vec::new();

            for &(sym, binding) in rule.args.iter().rev() {
                statements.push(if let Some(ident) = binding {
                    let ty = match sym {
                        Symbol::Term(sym) => &grammar.terminals[sym].ty,
                        Symbol::NonTerm(sym) => &grammar.nonterms[sym].ty,
                    };

                    let variant = enums.data_variants.get(ty).unwrap();
                    quote_stmt!(cx,
                        let $ident = match $arg_ident.pop().unwrap() {
                            $yytype_name::$variant(data) => data,
                            $unreachable
                        };
                    ).unwrap()
                } else {
                    quote_stmt!(cx, $arg_ident.pop().map(|_|()).unwrap();).unwrap()
                });
            }

            // generate code to push the returned
            // expression back onto the stack
            // take ownership of the expr
            let mut expr = None;
            ::std::mem::swap(&mut rule.action, &mut expr);
            let expr = match expr {
                Some(expr) => expr,
                None => quote_expr!(cx, ())
            };

            let variant = enums.data_variants.get(&nonterm.ty).unwrap();
            statements.push(quote_stmt!(cx,
                $arg_ident.push($yytype_name::$variant($expr))
            ).unwrap());

            let blk = cx.block(sp, statements, None);
            let ident = cx.ident_of(&format!("action_{}", rule_no)[..]);
            actions_funs.push(cx.item_fn(sp, ident, vec![arg], make_unit!(), blk));

            rule_no += 1;
        }
    };

    // generate parse table
    let mut table_vec = Vec::with_capacity(table.len());

    for line in table.iter() {
        let mut line_vec = Vec::with_capacity(line.len());
        for &entry in line.iter() {
            line_vec.push(match entry {
                Some(rule) => {
                    let ident = cx.ident_of(&format!("RULE_{}", rule)[..]);
                    let action = cx.ident_of(&format!("action_{}", rule)[..]);
                    quote_expr!(cx, Some((&$ident, $action)))
                }
                None => quote_expr!(cx, None)
            });
        }
        table_vec.push(cx.expr_vec(sp, line_vec));
    }

    let static_value = cx.expr_vec(sp, table_vec);
    let term_count = cx.expr_usize(sp, grammar.terminals.len() + 1);
    let nonterm_count = cx.expr_usize(sp, grammar.nonterms.len());
    let table = quote_item!(cx,
        static PARSE_TABLE: [[Option<(&'static [Step],
                                      fn(&mut Vec<$yytype_name>) -> ())>;
                              $term_count];
                             $nonterm_count] = $static_value;
    ).unwrap();

    // the other types
    // FIXME: hardcoded for now, should be user-defined
    let error = quote_item!(cx, pub type Error = &'static str;).unwrap();

    // FIXME: hardcoded variant (see below)
    let ret_ty = &grammar.nonterms[0].ty;
    let ret_variant = enums.data_variants.get(ret_ty).unwrap();
    let yytype_def = enums.data;
    let next_tok_def = enums.next_tok;

    let parse_fun = quote_item!(cx,
        pub fn parse<'a, T>(mut lexer: T) -> Result<$ret_ty, Error>
                            where T: Iterator<Item = Token> {
            $yytype_def
            $next_tok_def

            #[derive(Copy)]
            enum Step {
                Term(usize),
                NonTerm(usize),
                Action(fn(&mut Vec<$yytype_name>) -> ())
            }

            impl Clone for Step {
                fn clone(&self) -> Step {
                    match *self {
                        Step::Term(s) => Step::Term(s),
                        Step::NonTerm(s) => Step::NonTerm(s),
                        Step::Action(a) => Step::Action(a)
                    }
                }
            }

            impl ::std::fmt::Debug for Step {
                fn fmt(&self, fmt: &mut ::std::fmt::Formatter)
                       -> Result<(), ::std::fmt::Error> {
                    match *self {
                        Step::Term(sym) => write!(fmt, "(Token {})", sym),
                        Step::NonTerm(sym) => write!(fmt, "(Symbol {})", sym),
                        Step::Action(_) => write!(fmt, "(Action)")
                    }
                }
            }

            $actions_funs
            $rules
            $table

            let mut stack = Vec::new();
            let mut data_stack = Vec::new();
            stack.push(Step::NonTerm(0));

            let (mut yylval, mut cur) = next_token(&mut lexer);
            debug!("stack {:?}", stack);
            debug!("stack state: {:?}", data_stack);

            while let Some(symbol) = stack.pop() {
                debug!("attempting to parse {:?}", symbol);
                debug!("current token = {:?}", cur);

                match symbol {
                    // predict
                    Step::NonTerm(sym) =>
                        match PARSE_TABLE[sym][cur] {
                            Some((rule, action)) => {
                                stack.push(Step::Action(action));
                                for &tok in rule.iter().rev() {
                                    stack.push(tok);
                                }
                            }

                            None => return Err("syntax error")
                        },

                    // match
                    Step::Term(sym)
                        if sym == cur => {
                            data_stack.push(yylval);
                            let (val, st) = next_token(&mut lexer);
                            yylval = val;
                            cur = st;
                        }

                    Step::Term(_) => return Err("syntax error"),

                    // execute an action
                    Step::Action(action) => action(&mut data_stack)
                }

                debug!("stack {:?}", stack);
                debug!("stack state: {:?}", data_stack);
            }

            if cur != $eof { return Err("extra tokens at end of stream"); }

            match data_stack.pop().unwrap() {
                $yytype_name::$ret_variant(u) => Ok(u),
                $unreachable
            }
        }
    ).unwrap();

    vec!(enums.token, error, parse_fun)
}

impl ::Generator for LL {
    fn run(mut ast: grammar::Grammar, cx: &mut ExtCtxt) -> Vec<ptr::P<ast::Item>> {
        // add an EOF token, and add the information that EOF may follow
        // the start symbol. this is useful to properly compute FIRSTS
        // and FOLLOW sets in the case where the start symbol can be empty
        let eof = ast.gen_term();
        let start = ast.gen_nonterm();
        let rule = ast.rules.len();
        ast.rules.push(grammar::Rule {
            // FIXME: actual start symbol is not necessarily 0...
            args: vec!((Symbol::NonTerm(0), None), (Symbol::Term(eof), None)),
            action: None
        });
        ast.nonterms[start].productions = vec!(rule);

        for idx in 0 .. ast.terminals.len() {
            let ref term = ast.terminals[idx];
            debug!("terminal {} is {}", idx, term.name.name.as_str());
        }

        for idx in 0 .. ast.nonterms.len() {
            let ref nonterm = ast.nonterms[idx];
            debug!("non-terminal {} is {}", idx, nonterm.name.name.as_str());
            for &rule in nonterm.productions.iter() {
                let mut debug = String::new();
                write!(debug, "   {} ->", rule).unwrap();
                for &(sym, _) in ast.rules[rule].args.iter() {
                    write!(debug, " {}", match sym {
                        Symbol::Term(s) => ast.terminals[s].name.name.as_str(),
                        Symbol::NonTerm(s) => ast.nonterms[s].name.name.as_str()
                    }).unwrap();
                }
                debug!("{}", debug)
            }
        }

        debug!("computing firsts");
        let firsts = firsts(&ast);
        debug!("computing follow");
        let (follow, rules_firsts) = follow(&ast, &firsts);

        // remove the rule we added for the start symbol
        // we don't need it in the parse table. also remove
        // the associated non terminal
        ast.nonterms.pop();
        ast.rules.pop();
        debug!("computing parse table");
        let parse_table = parse_table(&ast, &follow, &rules_firsts);

        debug!(" === FIRST table === ");
        for sym in 0 .. ast.nonterms.len() {
            let mut debug = String::new();
            write!(debug, "FIRST({}) = {{", ast.nonterms[sym].name.name.as_str())
                .unwrap();
            for &f in firsts[sym].set.iter() {
                write!(debug, " {}", ast.terminals[f].name.name.as_str()).unwrap();
            }
            if firsts[sym].epsilon {
                write!(debug, " epsilon").unwrap();
            }
            debug!("{} }}", debug);
        }

        debug!(" === FOLLOW table === ");
        for sym in 0 .. ast.nonterms.len() {
            let mut debug = String::new();
            write!(debug, "FOLLOW({}) = {{", ast.nonterms[sym].name.name.as_str())
                .unwrap();
            for &f in follow[sym].iter() {
                write!(debug, " {}", ast.terminals[f].name.name.as_str()).unwrap();
            }
            debug!("{} }}", debug);
        }

        let parse_table = match parse_table {
            Ok(table) => table,
            Err(e) => match e {
                Error::Conflict(r1, r2, term) => {
                    cx.span_fatal(cx.original_span(), &format!(
                        "conflict: rules {} and {} can both start with {}",
                        r1, r2, ast.terminals[term].name.name.as_str()
                    )[..])
                }
            }
        };

        debug!(" === parse table === ");
        for sym in 0 .. ast.nonterms.len() {
            let mut debug = String::new();
            write!(debug, "When parsing {}: ", ast.nonterms[sym].name.name.as_str())
                .unwrap();
            for idx in 0 .. ast.terminals.len() {
                write!(debug, " {}:{:?}", idx, parse_table[sym][idx]).unwrap();
            }
            debug!("{}", debug);
        }

        codegen(ast, &parse_table, cx)
    }
}

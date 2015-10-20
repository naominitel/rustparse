use std::collections::{hash_map, HashMap, HashSet};

use syntax::{ast, parse, ptr};
use syntax::ext::base::ExtCtxt;
use syntax::ext::build::AstBuilder;

use fsa::{dfa, nfa};

use codegen;
use grammar;
use ll;

pub struct LR;

impl grammar::EBNFExpander for LR {
    fn expand(expr: grammar::EBNFExpr, syms: Vec<grammar::Symbol>,
              grammar: &mut grammar::Grammar)
              -> (usize, Vec<Vec<grammar::Expr<grammar::Symbol>>>) {
        ll::LL::expand(expr, syms, grammar)
    }
}

fn firsts_seq(symbols: &[(grammar::Symbol, Option<ast::Ident>)],
              firsts: &[ll::FirstSet]) -> ll::FirstSet {
    let mut ret = ll::FirstSet {
        set: HashSet::new(),
        epsilon: true
    };

    for &(sym, _) in symbols.iter().rev() {
        match sym {
            grammar::Symbol::NonTerm(sym) => {
                if !firsts[sym].epsilon {
                    ret.set.clear();
                    ret.epsilon = false;
                }

                for &i in firsts[sym].set.iter() {
                    ret.set.insert(i);
                }
            }

            grammar::Symbol::Term(sym) => {
                ret.set.clear();
                ret.epsilon = false;
                ret.set.insert(sym);
            }
        }
    }

    ret
}

// rule * lookahead
#[derive(Clone)]
#[derive(Debug)]
struct Data(Vec<(usize, usize)>);

impl nfa::StateData for Data {
    fn no_data() -> Data {
        Data(vec![])
    }

    fn combine(x: Data, y: Data) -> Data {
        let (Data(mut x), Data(y)) = (x, y);
        x.extend(&y[..]);
        Data(x)
    }

    fn is_final(&self) -> bool {
        let &Data(ref dat) = self;
        !dat.is_empty()
    }
}

#[derive(Debug)]
struct State {
    etrans: nfa::Etrans,
    // FIXME: why u8s? this is not a lexer.
    trans: Option<(u8, usize)>,
    action: Data
}

impl nfa::State for State {
    type Data = Data;
    type Iter = ::std::option::IntoIter<usize>;

    fn new() -> State {
        State {
            trans: None,
            etrans: nfa::Etrans::More(vec![]),
            action: <Data as nfa::StateData>::no_data()
        }
    }

    fn etransition<'a>(&'a self) -> &'a nfa::Etrans {
        &self.etrans
    }

    fn transition(&self, c: u8) -> Self::Iter {
        match self.trans {
            Some((n, dst)) if n == c => Some(dst),
            _ => None
        }.into_iter()
    }

    fn data(&self) -> Self::Data {
        self.action.clone()
    }
}

fn build_nfa(ast: &mut grammar::Grammar) -> nfa::Automaton<State> {
    // first compute the FIRST(k) sets for every non-terminal k
    // symbol. this will be useful to properly handle ε-rules.
    let firsts = ll::firsts(&ast);

    let mut auto = nfa::Automaton::<State> {
        states: Vec::new(),
        initial: 0
    };

    // stach that remembers the stations which must be constructed
    // (i.e. a state where the automaton starts to recognize a non
    // terminal with a given look-ahead)
    let mut stack = Vec::new();

    // stations already created
    let mut stations = HashMap::new();

    // FIXME: actual start symbol is not necessarily 0
    let eof = ast.gen_term();
    let state = auto.create_state();
    stack.push((state, 0, eof));
    stations.insert((0, eof), state);

    while let Some((state, nonterm, lookahead)) = stack.pop() {
        for &rule in ast.nonterms[nonterm].productions.iter() {
            // create final state
            let f1nal = auto.create_state();
            auto.states[f1nal].action = Data(vec![(rule, lookahead)]);

            let mut initial = f1nal;
            let ref rule = ast.rules[rule];

            for (i, &(sym, _)) in rule.args.iter().enumerate().rev() {
                let state = auto.create_state();

                let label = match sym {
                    grammar::Symbol::NonTerm(nt) => {
                        let mut firsts = firsts_seq(&rule.args[i + 1 ..], &firsts);
                        if firsts.epsilon {
                            firsts.set.insert(lookahead);
                        }

                        for i in firsts.set.into_iter() {
                            let station = (nt, i);
                            let s = stations.entry(station).or_insert_with(|| {
                                let s = auto.create_state();
                                stack.push((s, nt, i));
                                s
                            });
                            auto.states[state].etrans.push(*s);
                        }

                        ast.terminals.len() + nt
                    }

                    grammar::Symbol::Term(t) => t
                };

                // FIXME: why u8?
                auto.states[state].trans = Some((label as u8, initial));
                initial = state;
            }

            auto.states[state].etrans.push(initial);
        }
    }

    auto
}

enum Action {
    Err,
    Acc,
    Reduce(usize),
    Shift(usize)
}

struct ParseTable {
    action: Vec<Vec<Action>>,
    goto: Vec<Vec<usize>>
}

fn codegen(mut grammar: grammar::Grammar, table: ParseTable, cx: &mut ExtCtxt,
           initial: usize)
    -> Vec<ptr::P<ast::Item>> {
    grammar.terminals.pop();

    let enums = codegen::parser_enums(&grammar, cx);
    let yytype_name = enums.data.ident;
    let sp = cx.original_span();

    let unreachable =
        if enums.data_variants.len() > 1 { Some(cx.arm_unreachable(sp)) }
        else { None };

    let act_table: Vec<_> = table.action.iter().map(|v| {
        cx.expr_vec(sp, v.iter().map(|v| {
            match *v {
                Action::Reduce(x) => {
                    let x = cx.ident_of(&format!("RULE_{}", x)[..]);
                    quote_expr!(cx, Action::Reduce($x))
                }
                Action::Shift(x) => {
                    let x = cx.expr_usize(sp, x);
                    quote_expr!(cx, Action::Shift($x))
                }
                Action::Acc => quote_expr!(cx, Action::Acc),
                Action::Err => quote_expr!(cx, Action::Err)
            }
        }).collect())
    }).collect();

    // TODO: functional flatten
    let mut functions = Vec::with_capacity(grammar.rules.len());
    for (nt_no, nt) in grammar.nonterms.iter().enumerate() {
        for &rule_no in nt.productions.iter() {
            let ref rule = grammar.rules[rule_no];

            let stmts: Vec<_> = rule.args.iter().rev().map(|&(sym, binding)| {
                let ident = match binding {
                    Some(id) => id,
                    None => parse::token::gensym_ident("_")
                };

                let ty = match sym {
                    grammar::Symbol::Term(sym) => &grammar.terminals[sym].ty,
                    grammar::Symbol::NonTerm(sym) => &grammar.nonterms[sym].ty,
                };

                let variant = enums.data_variants.get(ty).unwrap();
                quote_stmt!(cx,
                    let (state, mut $ident) = match stack.pop().unwrap() {
                        (state, $yytype_name::$variant(data)) => (state, data),
                        $unreachable
                    };
                ).unwrap()
            }).collect();

            let variant = enums.data_variants.get(&nt.ty).unwrap();
            let action = match rule.action {
                Some(ref act) => act.clone(),
                None => quote_expr!(cx, ())
            };

            let fn_name = cx.ident_of(&format!("RULE_{}", rule_no)[..]);

            // we need unused_variables because we repeatidly re-define state
            // so that its final value is the one we need. we could know that
            // statically and generate _ instead of state for the ones that are
            // not needed, I guess...
            functions.push(quote_item!(cx,
                #[allow(non_snake_case)]
                #[allow(unused_variables)]
                fn $fn_name(state: usize, stack: &mut Vec<(usize, $yytype_name)>)
                    -> usize {
                    $stmts
                    let value = $action;
                    stack.push((state, $yytype_name::$variant(value)));
                    GOTO_TABLE[state][$nt_no]
                }
            ).unwrap());
        }
    };

    let term_count = cx.expr_usize(sp, grammar.terminals.len() + 1);
    let nterm_count = cx.expr_usize(sp, grammar.nonterms.len());
    let state_count = cx.expr_usize(sp, act_table.len());
    let static_value = cx.expr_vec(sp, act_table);

    let goto_table = cx.expr_vec(sp, table.goto.iter().map(|v| {
        cx.expr_vec(sp, v.iter().map(|v| {
            cx.expr_usize(sp, *v)
        }).collect())
    }).collect());

    let goto_table = quote_item!(cx,
        static GOTO_TABLE: [[usize ; $nterm_count] ; $state_count] = $goto_table;
    ).unwrap();

    let table = quote_item!(cx,
        static PARSE_TABLE: [[Action ; $term_count] ; $state_count]
            = $static_value;
    ).unwrap();

    // FIXME: not necessarily 0
    let ret_ty = &grammar.nonterms[0].ty;
    let final_variant = enums.data_variants.get(ret_ty).unwrap();

    let yytype_def = enums.data;
    let next_tok = enums.next_tok;

    let parse_fun = quote_item!(cx,
        pub fn parse<'a, T>(mut lexer: T) -> Result<$ret_ty, ()>
            where T: Iterator<Item = &'a Token> {
            enum Action {
                Err,
                Acc,
                Reduce(fn(usize, &mut Vec<(usize, $yytype_name)>) -> usize),
                Shift(usize)
            }

            $functions
            $yytype_def
            $next_tok
            $table
            $goto_table

            // the current state
            let mut state = $initial;

            // the current token and its semantic data
            let (mut yylval, mut tok) = next_token(&mut lexer);
            let mut stack = Vec::new();

            loop {
                match PARSE_TABLE[state][tok] {
                    Action::Shift(shift) => {
                        stack.push((state, yylval));
                        state = shift;
                        let (v, t) = next_token(&mut lexer);
                        tok = t;
                        yylval = v;
                    }

                    Action::Reduce(reduce) => state = reduce(state, &mut stack),
                    Action::Acc => break,
                    Action::Err => return Err(())
                }
            }

            match stack.pop().unwrap() {
                (_, $yytype_name::$final_variant(ret)) => Ok(ret),
                $unreachable
            }
        }
    ).unwrap();

    vec![enums.token, parse_fun]
}

impl ::Generator for LR {
    fn run(mut ast: grammar::Grammar, cx: &mut ExtCtxt) -> Vec<ptr::P<ast::Item>> {
        let auto = build_nfa(&mut ast);
        let mut dfa = dfa::Automaton::<Data>::new();
        let initial = dfa.determinize(&auto);
        let sp = cx.original_span();

        let (mut action, goto) = dfa.states.iter().enumerate().map(|(i, s)| {
            let mut reductions = HashMap::new();
            let Data(vec) = s.data.clone();
            for &(r, la) in vec.iter() {
                match reductions.entry(la) {
                    hash_map::Entry::Vacant(e) => { e.insert(r); },
                    hash_map::Entry::Occupied(e) => {
                        cx.span_err(sp, &format!("reduce/reduce conflict on state {}.
                                             Reduction by {} or by {} on {}.",
                                            i, e.get(), r, la))
                    }
                }
            }

            let action = s.trans[0 .. ast.terminals.len()].iter().enumerate().map(
                |(t, &dst)| {
                    match reductions.get(&t) {
                        Some(r) if dst != 0 => {
                            cx.span_err(
                                sp, &format!("shift/reduce conflict on state {}.
                                              Reduction by {} or shift to {} on {}.",
                                             i, r, dst, t)
                            );

                            Action::Err
                        }

                        Some(&r) => Action::Reduce(r),
                        None if dst != 0 => Action::Shift(dst),
                        None => Action::Err
                    }
                }
            ).collect::<Vec<_>>();

            let goto =
                s.trans[ast.terminals.len() ..
                        ast.terminals.len() + ast.nonterms.len()]
                    .iter().map(|&x| x).collect::<Vec<_>>();

            (action, goto)
        }).unzip::<_, _, Vec<_>, Vec<_>>();

        cx.parse_sess.span_diagnostic.handler.abort_if_errors();

        // FIXME?
        let eof = ast.terminals.len() - 1;
        let initial = dfa.initials[initial];
        action[goto[initial][0]][eof] = Action::Acc;

        codegen(ast, ParseTable { action: action, goto: goto }, cx, initial)
    }
}

#![allow(dead_code)]
#![feature(plugin)]
#![feature(rt)]
#![feature(rustc_private)]
#![plugin(rustparse)]

#[macro_use] extern crate log;

#[derive(Debug)]
pub enum Addition {
    Add(i32),
    Sub(i32),
    Nop
}

pub use Addition::*;
pub use Multiplication::*;

#[derive(Debug)]
pub enum Multiplication {
    Div(i32),
    Mul(i32),
    TNop
}

LL_parser! arith_parser(
    token INT: i32;
    token PLUS;
    token MINUS;
    token TIMES;
    token SLASH;
    token OP;
    token CL;

    // start expr;

    expr -> (i32) ::=
        (x: term) (op: expr_) => {
            match op {
                Add(y) => x + y,
                Sub(y) => x - y,
                Nop => x
            }
        };

    expr_ -> (Addition) ::=
        PLUS (x: term) (op: expr_) => match op {
            Add(y) => Add(x + y),
            Sub(y) => Add(x - y),
            Nop => Add(x)
        },

        MINUS (x: term) (op: expr_) => match op {
            Add(y) => Sub(x + y),
            Sub(y) => Sub(x - y),
            Nop => Sub(x)
        },

        empty => Nop
    ;

    term -> (i32) ::=
        (f: factor) (op: term_) => match op {
            Mul(y) => f * y,
            Div(y) => f * y,
            TNop => f
        };

    term_ -> (Multiplication) ::=
        TIMES (x: factor) (op: term_) => match op {
            Mul(y) => Mul(x + y),
            Div(y) => Mul(x - y),
            TNop => Mul(x)
        },

        SLASH (x: factor) (op: term_) => match op {
            Mul(y) => Div(x + y),
            Div(y) => Div(x - y),
            TNop => Div(x)
        },

        empty => TNop
    ;

    factor -> (i32) ::=
        OP (e: expr) CL => e,
        (cst: INT) => cst
    ;
);

fn main() {
    use arith_parser::Token::*;
    let test = vec![
        INT(5),
        TIMES(()),
        INT(3),
        MINUS(()),
        INT(2),
        MINUS(()),
        INT(6)
    ];
    let ret = arith_parser::parse(test.iter());
    match ret {
        Ok(u) => println!("{}", u),
        Err(e) => println!("{}", e)
    }
}

### rust-parsegen

This repository contains a pure Rust implementation of both LL and LR parsers
generators (implemented in Rust and producing Rust executable parsers).

It used to aim at being a full-feature parser generator tool for Rust. But
implementing good parsers generators is hard and this work has been made quite
obsolete by both:
* [LALRPOP](https://github.com/nikomatsakis/lalrpop)
* The [Menhir](https://menhir-rs.github.io/doc/menhir/) backend for Rust.

However, I am publishing this code here cause it's kinda clean and can still be
of some educational interest. Be aware though that it's possibly buggy and most
likely not working on modern Rust versions.

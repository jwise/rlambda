import std::io;
import io::{reader_util, writer_util};

import lambda::*;

fn main() {
    let gen = newctx();
    
    let s = gen();
    let z = gen();
    let ZERO = e_lam(s, @e_lam(z, @e_var(z)));
    let ONE = e_lam(s, @e_lam(z, @e_app(@e_var(s), @e_var(z)))); 
    let PR_ONE = e_app(@e_app(@ONE, @e_lam(s, @e_prim(p_succ, @e_var(s)))),
                       @e_prim(p_zero, @e_lam(s, @e_var(s))));
    
    let x = gen();
    let OMEGA = e_app(
                  @e_lam(x, @e_app(@e_var(x), @e_var(x))),
                  @e_lam(x, @e_app(@e_var(x), @e_var(x))));

    io::stdout().write_str(PR_ONE.str() + " -> " + PR_ONE.eval(gen).str() + "\n");
}

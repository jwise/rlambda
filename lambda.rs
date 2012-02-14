import std::map;

export var, expr, prim;
export exprops;
export newctx;

type var = uint;
enum expr {
  e_app(@expr, @expr),
  e_lam(var, @expr),
  e_var(var),
  
  e_prim(prim, @expr),
  e_nat(uint),
}

enum prim {
  p_zero,
  p_succ,
}
 
impl exprops_priv for expr {
  /*pure */fn is_value() -> bool {
    alt self {
      e_app(_, _) { false }
      e_lam(_, _) { true }
      e_var(_) { true }
      
      e_prim(_, _) { false }
      e_nat(_) { true }
    }
  }

  fn freevars() -> map::set<var> {
    let m : map::set<var> = map::new_uint_hash();
    
    fn fv_e(m: map::set<var>, G: map::set<var>, e: expr) {
      alt e {
        e_app(e1, e2) {
          fv_e(m, G, *e1);
          fv_e(m, G, *e2);
        }
        e_lam(v, ep) {
          let Gp = copy G;
          map::set_add(Gp, v);
          fv_e(m, Gp, *ep);
        }
        e_var(v) {
          alt G.find(v) {
            option::none { map::set_add(m, v); }
            option::some(_) { /* not a free variable */ }
          }
        }
        e_prim(_, ep) {
          fv_e(m, G, *ep)
        }
        e_nat(_) { }
      }
    }
    fv_e(m, map::new_uint_hash(), self);
    
    m
  }

  /* e.subst(x, y) := [x/y]e */
  fn subst(gen: fn() -> var, x: expr, y: var) -> expr {
    let fvs = x.freevars();
  
    fn subst_(gen: fn() -> var, fvs: map::set<var>, x: expr, y: var, e: expr) -> expr {
      alt e {
        e_app(e1, e2) {
          e_app(@subst_(gen, fvs, x, y, *e1), @subst_(gen, fvs, x, y, *e2))
        }
        e_lam(v, ep) {
          alt fvs.find(v) { /* v free in x? */
            option::none { /* no */
              e_lam(v, @subst_(gen, fvs, x, y, *ep))
            }
            option::some(_) { /* yes, alpha-vary \v.ep */
              let vp = gen();
              e_lam(vp, @subst_(gen, fvs, x, y, (*ep).subst(gen, e_var(vp), v)))
            }
          }
        }
        e_var(v) {
          if v == y { x }
          else { e }
        }
        e_prim(p, ep) {
          e_prim(p, @subst_(gen, fvs, x, y, *ep))
        }
        e_nat(_) { e }
      }
    }
    
    subst_(gen, fvs, x, y, self)
  }

  fn step(gen: fn() -> var) -> expr {
    alt self {
      e_app(e1, e2) {
        if !(*e1).is_value() { ret e_app(@(*e1).step(gen), e2) }
        let (v, e1s) = alt *e1 {
          e_lam(v, e1s) { (v, e1s) }
          _ { fail "free variable in e_app" }
        };
        (*e1s).subst(gen, *e2, v)
      }
      e_prim(p, ep) {
        if !(*ep).is_value() { ret e_prim(p, @(*ep).step(gen)) }
        alt p {
          p_zero { e_nat(0u) }
          p_succ {
            alt *ep {
              e_nat(n) { e_nat(n+1u) }
              _ { fail "succ on non-nat" }
            }
          }
        }
      }
      _ { fail "step on a value" }
    }
  }
}

impl exprops for expr {
  fn str() -> str {
    alt self {
      e_lam(v, ep) { #fmt("(\\%u.%s)", v, (*ep).str()) }
      e_app(e1, e2) { #fmt("APP(%s,%s)", (*e1).str(), (*e2).str()) }
      e_var(v) { #fmt("%u", v) }
      e_prim(pr, e) { #fmt("%s(%s)",
        alt pr {
        p_succ { "SUCC" }
        p_zero { "ZERO" }
        }, (*e).str())
      }
      e_nat(n) { #fmt("NAT(%u)", n) }
    }
  }
  
  fn eval(gen: fn() -> var) -> expr {
    let e = self;
    while (!e.is_value()) {
      log(info, (e.str(), e));
      e = e.step(gen);
    }
    e
  }
}
  
fn newctx() -> fn@() -> var {
  let i = 0u;    

  fn next(i: @mutable uint) -> var {
    *i = *i + 1u;
    *i
  }
  
  bind next(@mutable i)
}


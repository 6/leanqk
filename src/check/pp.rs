//! A compact printer for terms in error messages. It is not meant to be
//! read back: binder names may repeat, and deep or long terms are cut off.

use crate::expr::{ExprId, ExprNode};
use crate::level::LevelNode;

use super::store::Store;
use super::tc::LocalDecl;

const MAX_LEN: usize = 400;
const MAX_DEPTH: u32 = 12;

pub fn pp(st: &Store<'_>, lctx: &[LocalDecl], e: ExprId) -> String {
    let mut out = String::new();
    let mut names = Vec::new();
    go(st, lctx, e, &mut names, 0, &mut out);
    if out.len() > MAX_LEN {
        let mut cut = MAX_LEN;
        while !out.is_char_boundary(cut) {
            cut -= 1;
        }
        out.truncate(cut);
        out.push('…');
    }
    out
}

pub fn pp_level(st: &Store<'_>, l: crate::level::LevelId) -> String {
    let mut k = 0;
    let mut cur = l;
    while let LevelNode::Succ(a) = st.level(cur) {
        k += 1;
        cur = a;
    }
    let base = match st.level(cur) {
        LevelNode::Zero => return k.to_string(),
        LevelNode::Param(n) => st.show(n),
        LevelNode::Max(a, b) => format!("(max {} {})", pp_level(st, a), pp_level(st, b)),
        LevelNode::IMax(a, b) => format!("(imax {} {})", pp_level(st, a), pp_level(st, b)),
        LevelNode::Succ(_) => unreachable!(),
    };
    if k == 0 { base } else { format!("{base}+{k}") }
}

fn go(
    st: &Store<'_>,
    lctx: &[LocalDecl],
    e: ExprId,
    names: &mut Vec<String>,
    depth: u32,
    out: &mut String,
) {
    if out.len() > MAX_LEN {
        return;
    }
    if depth > MAX_DEPTH {
        out.push('…');
        return;
    }
    match st.node(e) {
        ExprNode::BVar(i) => match names.len().checked_sub(i as usize + 1) {
            Some(k) => out.push_str(&names[k]),
            None => out.push_str(&format!("#{i}")),
        },
        ExprNode::FVar(i) => match lctx.get(i as usize) {
            Some(d) => out.push_str(&st.show(d.name)),
            None => out.push_str(&format!("?fv{i}")),
        },
        ExprNode::Sort(l) => {
            if l == crate::level::LevelId::ZERO {
                out.push_str("Prop")
            } else {
                out.push_str(&format!("Sort {}", pp_level(st, l)))
            }
        }
        ExprNode::Const(n, ls) => {
            out.push_str(&st.show(n));
            let ls = st.list(ls);
            if !ls.is_empty() {
                out.push_str(".{");
                for (i, &l) in ls.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    out.push_str(&pp_level(st, l));
                }
                out.push('}');
            }
        }
        ExprNode::App(..) => {
            let mut args = Vec::new();
            let f = st.spine(e, &mut args);
            out.push('(');
            go(st, lctx, f, names, depth + 1, out);
            for a in args {
                out.push(' ');
                go(st, lctx, a, names, depth + 1, out);
            }
            out.push(')');
        }
        ExprNode::Lam(_, n, t, b) | ExprNode::Pi(_, n, t, b) => {
            let lam = matches!(st.node(e), ExprNode::Lam(..));
            let nm = st.show(n);
            out.push_str(if lam { "(fun (" } else { "((" });
            out.push_str(&nm);
            out.push_str(" : ");
            go(st, lctx, t, names, depth + 1, out);
            out.push_str(if lam { ") => " } else { ") → " });
            names.push(nm);
            go(st, lctx, b, names, depth + 1, out);
            names.pop();
            out.push(')');
        }
        ExprNode::Let(h, b) => {
            let lb = st.let_binder(h);
            let nm = st.show(lb.name);
            out.push_str(&format!("(let {nm} := "));
            go(st, lctx, lb.value, names, depth + 1, out);
            out.push_str("; ");
            names.push(nm);
            go(st, lctx, b, names, depth + 1, out);
            names.pop();
            out.push(')');
        }
        ExprNode::NatSmall(lo, hi) => out.push_str(&((hi as u64) << 32 | lo as u64).to_string()),
        ExprNode::NatBig(b) => out.push_str(&st.big(b).to_string()),
        ExprNode::Str(s) => out.push_str(&format!("{:?}", st.str(s))),
        ExprNode::Proj(s, i, x) => {
            go(st, lctx, x, names, depth + 1, out);
            out.push_str(&format!(".{}#{}", st.show(s), i + 1));
        }
    }
}

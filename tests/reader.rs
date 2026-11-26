//! Reader tests on small hand-written exports.

use nitrolean::env::{BlockKind, DeclKind, Hints, QuotKind, Safety};
use nitrolean::expr::{BinderInfo, ExprNode};
use nitrolean::level::{LevelId, LevelNode};
use nitrolean::reader::{ErrorClass, ReadError, read_buffered, read_str};

const META: &str = r#"{"meta":{"exporter":{"name":"handwritten","version":"0"},"format":{"version":"3.1.0"},"lean":{"githash":"0","version":"4.36.0"}}}"#;

fn export(lines: &[&str]) -> String {
    let mut s = String::from(META);
    s.push('\n');
    for l in lines {
        s.push_str(l);
        s.push('\n');
    }
    s
}

/// A small but complete export: `Nat` with its constructors and recursor,
/// plus one declaration of every other kind.
const SAMPLE: &[&str] = &[
    r#"{"in":1,"str":{"pre":0,"str":"Nat"}}"#,
    r#"{"in":2,"str":{"pre":1,"str":"zero"}}"#,
    r#"{"in":3,"str":{"pre":1,"str":"succ"}}"#,
    r#"{"in":4,"str":{"pre":0,"str":"n"}}"#,
    r#"{"in":5,"str":{"pre":1,"str":"rec"}}"#,
    r#"{"in":6,"str":{"pre":0,"str":"u"}}"#,
    r#"{"il":1,"succ":0}"#,
    r#"{"il":2,"param":6}"#,
    r#"{"il":3,"max":[1,2]}"#,
    r#"{"il":4,"imax":[2,1]}"#,
    r#"{"ie":0,"sort":1}"#,
    r#"{"ie":1,"const":{"name":1,"us":[]}}"#,
    r#"{"ie":2,"forallE":{"name":4,"type":1,"body":1,"binderInfo":"default"}}"#,
    r#"{"ie":3,"sort":2}"#,
    concat!(
        r#"{"inductive":{"types":[{"name":1,"levelParams":[],"type":0,"numParams":0,"#,
        r#""numIndices":0,"all":[1],"ctors":[2,3],"numNested":0,"isRec":true,"#,
        r#""isReflexive":false,"isUnsafe":false}],"ctors":[{"name":2,"levelParams":[],"#,
        r#""type":1,"induct":1,"cidx":0,"numParams":0,"numFields":0,"isUnsafe":false},"#,
        r#"{"name":3,"levelParams":[],"type":2,"induct":1,"cidx":1,"numParams":0,"#,
        r#""numFields":1,"isUnsafe":false}],"recs":[{"name":5,"levelParams":[6],"type":3,"#,
        r#""all":[1],"numParams":0,"numIndices":0,"numMotives":1,"numMinors":2,"#,
        r#""rules":[{"ctor":2,"nfields":0,"rhs":3},{"ctor":3,"nfields":1,"rhs":3}],"#,
        r#""k":false,"isUnsafe":false}]}}"#
    ),
    r#"{"in":7,"str":{"pre":0,"str":"id"}}"#,
    r#"{"ie":4,"bvar":0}"#,
    r#"{"ie":5,"lam":{"name":4,"type":1,"body":4,"binderInfo":"implicit"}}"#,
    r#"{"def":{"name":7,"levelParams":[],"type":2,"value":5,"hints":{"regular":3},"safety":"safe","all":[7]}}"#,
    r#"{"in":8,"str":{"pre":0,"str":"ax"}}"#,
    r#"{"axiom":{"name":8,"levelParams":[],"type":1,"isUnsafe":false}}"#,
    r#"{"in":9,"str":{"pre":0,"str":"two"}}"#,
    r#"{"ie":6,"natVal":"2"}"#,
    r#"{"def":{"name":9,"levelParams":[],"type":1,"value":6,"hints":"abbrev","safety":"safe","all":[9]}}"#,
    r#"{"in":10,"str":{"pre":0,"str":"big"}}"#,
    r#"{"ie":7,"natVal":"340282366920938463463374607431768211456"}"#,
    r#"{"def":{"name":10,"levelParams":[],"type":1,"value":7,"hints":"opaque","safety":"partial","all":[10]}}"#,
    r#"{"in":11,"str":{"pre":0,"str":"thm"}}"#,
    r#"{"ie":8,"mdata":{"data":{"k":"v"},"expr":6}}"#,
    r#"{"thm":{"name":11,"levelParams":[],"type":1,"value":8,"all":[11]}}"#,
    r#"{"in":12,"str":{"pre":0,"str":"op"}}"#,
    r#"{"ie":9,"strVal":"héllo \"w\"\n"}"#,
    r#"{"opaque":{"name":12,"levelParams":[],"type":1,"value":9,"all":[12],"isUnsafe":true}}"#,
    r#"{"in":13,"str":{"pre":0,"str":"op2"}}"#,
    r#"{"opaque":{"name":13,"levelParams":[],"type":1,"value":9,"all":[13]}}"#,
    r#"{"in":14,"str":{"pre":0,"str":"Quot"}}"#,
    r#"{"in":15,"str":{"pre":14,"str":"mk"}}"#,
    r#"{"in":16,"str":{"pre":14,"str":"lift"}}"#,
    r#"{"in":17,"str":{"pre":14,"str":"ind"}}"#,
    r#"{"quot":{"name":14,"levelParams":[6],"type":3,"kind":"type"}}"#,
    r#"{"quot":{"name":15,"levelParams":[6],"type":3,"kind":"ctor"}}"#,
    r#"{"quot":{"name":16,"levelParams":[6],"type":3,"kind":"lift"}}"#,
    r#"{"quot":{"name":17,"levelParams":[6],"type":3,"kind":"ind"}}"#,
    r#"{"in":18,"num":{"pre":7,"i":42}}"#,
    r#"{"ie":10,"app":{"fn":5,"arg":6}}"#,
    r#"{"ie":11,"letE":{"name":4,"type":1,"value":6,"body":4,"nondep":false}}"#,
    r#"{"ie":12,"proj":{"typeName":1,"idx":0,"struct":10}}"#,
    r#"{"ie":13,"const":{"name":14,"us":[2,3,4]}}"#,
    r#"{"def":{"name":18,"levelParams":[6],"type":13,"value":12,"hints":{"regular":0},"safety":"unsafe","all":[18,7]}}"#,
];

#[test]
fn reads_every_declaration_kind() {
    let env = read_str(&export(SAMPLE)).unwrap();
    assert_eq!(env.meta.format_version, "3.1.0");
    assert_eq!(env.meta.lean_version.as_deref(), Some("4.36.0"));
    let c = env.counts();
    assert_eq!(
        (c.axioms, c.definitions, c.theorems, c.opaques, c.quotients),
        (1, 4, 1, 2, 4)
    );
    assert_eq!((c.inductives, c.constructors, c.recursors), (1, 2, 1));
    assert_eq!(env.decls.len(), 16);
    // One inductive block of four declarations, then one block per record.
    assert_eq!(
        env.blocks[0].kind,
        BlockKind::Inductive {
            types: 1,
            ctors: 2,
            recs: 1
        }
    );
    assert_eq!(env.blocks.len(), 13);

    let nat = env.find_dotted("Nat").unwrap();
    let DeclKind::Inductive {
        ctors, is_rec, all, ..
    } = nat.kind
    else {
        panic!("Nat is not an inductive");
    };
    assert!(is_rec);
    assert_eq!(all.len(), 1);
    let ctor_names: Vec<String> = env
        .name_list(ctors)
        .iter()
        .map(|&n| env.names.display(n).to_string())
        .collect();
    assert_eq!(ctor_names, ["Nat.zero", "Nat.succ"]);

    let succ = env.find_dotted("Nat.succ").unwrap();
    assert!(matches!(
        succ.kind,
        DeclKind::Constructor {
            cidx: 1,
            num_fields: 1,
            ..
        }
    ));
    let rec = env.find_dotted("Nat.rec").unwrap();
    let DeclKind::Recursor { rules, k, .. } = rec.kind else {
        panic!("Nat.rec is not a recursor");
    };
    assert!(!k);
    assert_eq!(env.name_list(rec.level_params).len(), 1);
    let rules = env.rec_rules(rules);
    assert_eq!(rules.len(), 2);
    assert_eq!(rules[1].ctor, succ.name);
    assert_eq!(rules[1].nfields, 1);

    let id = env.find_dotted("id").unwrap();
    let DeclKind::Definition {
        value,
        hints,
        safety,
        ..
    } = id.kind
    else {
        panic!("id is not a definition");
    };
    assert_eq!((hints, safety), (Hints::Regular(3), Safety::Safe));
    let ExprNode::Lam(bi, _, ty, body) = env.exprs.get(value) else {
        panic!("id's value is not a lambda");
    };
    assert_eq!(bi, BinderInfo::Implicit);
    assert_eq!(env.exprs.get(body), ExprNode::BVar(0));
    assert_eq!(env.exprs.data(body).loose_bvar_range(), 1);
    assert_eq!(env.exprs.data(value).loose_bvar_range(), 0);
    assert!(matches!(env.exprs.get(ty), ExprNode::Const(..)));

    let two = env.find_dotted("two").unwrap();
    let DeclKind::Definition { value: two_v, .. } = two.kind else {
        panic!()
    };
    assert_eq!(env.exprs.get(two_v), ExprNode::NatSmall(2, 0));

    let big = env.find_dotted("big").unwrap();
    let DeclKind::Definition {
        value,
        hints,
        safety,
        ..
    } = big.kind
    else {
        panic!()
    };
    assert_eq!((hints, safety), (Hints::Opaque, Safety::Partial));
    let ExprNode::NatBig(b) = env.exprs.get(value) else {
        panic!("2^128 should be a big literal")
    };
    assert_eq!(
        env.exprs.big(b).to_string(),
        "340282366920938463463374607431768211456"
    );

    // `mdata` is transparent: the theorem's value is the literal itself.
    let thm = env.find_dotted("thm").unwrap();
    let DeclKind::Theorem { value, .. } = thm.kind else {
        panic!("thm is not a theorem")
    };
    assert_eq!(value, two_v);

    let op = env.find_dotted("op").unwrap();
    let DeclKind::Opaque {
        value, is_unsafe, ..
    } = op.kind
    else {
        panic!()
    };
    assert!(is_unsafe);
    let ExprNode::Str(s) = env.exprs.get(value) else {
        panic!()
    };
    assert_eq!(env.names.strings.get(s), "h\u{e9}llo \"w\"\n");
    let op2 = env.find_dotted("op2").unwrap();
    assert!(matches!(
        op2.kind,
        DeclKind::Opaque {
            is_unsafe: false,
            ..
        }
    ));

    let kinds: Vec<QuotKind> = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"]
        .iter()
        .map(|n| match env.find_dotted(n).unwrap().kind {
            DeclKind::Quot { kind } => kind,
            _ => panic!("{n} is not a quotient"),
        })
        .collect();
    assert_eq!(
        kinds,
        [
            QuotKind::Type,
            QuotKind::Ctor,
            QuotKind::Lift,
            QuotKind::Ind
        ]
    );

    let d = env.find_dotted("id.42").unwrap();
    assert_eq!(env.names.display(d.name).to_string(), "id.42");
    let DeclKind::Definition {
        value, safety, all, ..
    } = d.kind
    else {
        panic!()
    };
    assert_eq!(safety, Safety::Unsafe);
    assert_eq!(env.name_list(all).len(), 2);
    let ExprNode::Proj(_, 0, s) = env.exprs.get(value) else {
        panic!()
    };
    assert!(matches!(env.exprs.get(s), ExprNode::App(..)));
    let ExprNode::Const(_, us) = env.exprs.get(d.ty) else {
        panic!()
    };
    assert_eq!(env.levels.list(us).len(), 3);
    assert!(env.levels.list_has_param(us));
    assert!(env.exprs.data(d.ty).has_level_param());
}

#[test]
fn key_order_whitespace_and_blank_lines_do_not_matter() {
    let a = export(SAMPLE);
    let mut b = String::from(META);
    b.push_str("\r\n\n");
    for l in SAMPLE {
        // Re-serialize each record with its top-level keys reversed and
        // extra whitespace, by swapping the two halves of id records.
        let l = if let Some(rest) = l.strip_prefix(r#"{"ie":"#) {
            let (id, payload) = rest.split_once(',').unwrap();
            format!("{{ {} , \"ie\" : {id} }}", &payload[..payload.len() - 1])
        } else {
            format!("  {l}  ")
        };
        b.push_str(&l);
        b.push_str("\r\n\n");
    }
    let (ea, eb) = (read_str(&a).unwrap(), read_str(&b).unwrap());
    assert_eq!(ea.counts(), eb.counts());
    assert_eq!(ea.exprs.len(), eb.exprs.len());
    assert_eq!(ea.decls, eb.decls);
}

#[test]
fn ids_may_be_sparse_and_out_of_order() {
    // From lean-kernel-arena's tests/other/{sparse-name-index,
    // level-index-out-of-order}.
    let env = read_str(&export(&[
        r#"{"in":2,"str":{"pre":0,"str":"foo"}}"#,
        r#"{"il":2,"succ":0}"#,
        r#"{"il":1,"succ":2}"#,
        r#"{"ie":4,"sort":1}"#,
        r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":2,"type":4}}"#,
        r#"{"in":1000000000000,"str":{"pre":2,"str":"bar"}}"#,
        r#"{"ie":0,"sort":2}"#,
        r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":1000000000000,"type":0}}"#,
    ]))
    .unwrap();
    let foo = env.find_dotted("foo").unwrap();
    let ExprNode::Sort(l) = env.exprs.get(foo.ty) else {
        panic!()
    };
    // `Sort 2`: succ (succ zero), whatever the export ids were.
    let LevelNode::Succ(l1) = env.levels.get(l) else {
        panic!()
    };
    assert_eq!(env.levels.get(l1), LevelNode::Succ(LevelId::ZERO));
    assert!(env.find_dotted("foo.bar").is_some());
}

#[test]
fn structurally_equal_records_share_a_node() {
    let env = read_str(&export(&[
        r#"{"ie":0,"sort":0}"#,
        r#"{"ie":1,"sort":0}"#,
        r#"{"ie":2,"natVal":"18446744073709551616"}"#,
        r#"{"ie":3,"natVal":"18446744073709551616"}"#,
        r#"{"ie":4,"natVal":"0018446744073709551615"}"#,
        r#"{"ie":5,"natVal":"18446744073709551615"}"#,
        r#"{"ie":6,"app":{"fn":0,"arg":2}}"#,
        r#"{"ie":7,"app":{"fn":1,"arg":3}}"#,
    ]))
    .unwrap();
    // sort, big literal, small literal, app.
    assert_eq!(env.exprs.len(), 4);
    assert_eq!(env.exprs.big_count(), 1);
}

#[test]
fn reads_from_a_stream() {
    let s = export(SAMPLE);
    let (env, stats) = read_buffered(s.as_bytes()).unwrap();
    assert_eq!(env.decls.len(), 16);
    assert_eq!(stats.lines, SAMPLE.len() as u64 + 1);
    assert_eq!(stats.bytes, s.len() as u64);
    assert_eq!(stats.shared_exprs, 1); // the mdata record
}

fn fail_bytes(bytes: &[u8]) -> ReadError {
    match read_buffered(bytes) {
        Ok(_) => panic!("accepted malformed input"),
        Err(e) => e,
    }
}

fn fail(lines: &[&str]) -> ReadError {
    fail_bytes(export(lines).as_bytes())
}

/// Assert an error's line (counting the meta line as 1), class and message.
#[track_caller]
fn assert_err(e: ReadError, line: u64, class: ErrorClass, needle: &str) {
    assert_eq!((e.line, e.class), (line, class), "{e}");
    assert!(e.msg.contains(needle), "{e:?} should mention {needle:?}");
    assert!(e.to_string().starts_with(&format!("line {line}: ")) || line == 0);
}

#[test]
fn structural_errors_name_their_line() {
    use ErrorClass::{Malformed, Rejected};
    let name = r#"{"in":1,"str":{"pre":0,"str":"a"}}"#;
    let sort = r#"{"ie":0,"sort":0}"#;
    let cases: &[(&[&str], u64, ErrorClass, &str)] = &[
        // Forward references and undefined ids.
        (
            &[r#"{"in":1,"str":{"pre":2,"str":"a"}}"#],
            2,
            Malformed,
            "undefined name id 2",
        ),
        (
            &[r#"{"il":1,"succ":5}"#],
            2,
            Malformed,
            "undefined level id 5",
        ),
        (
            &[sort, r#"{"ie":1,"app":{"fn":0,"arg":1}}"#],
            3,
            Malformed,
            "undefined expression id 1",
        ),
        (
            &[
                r#"{"ie":0,"sort":0}"#,
                r#"{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}"#,
            ],
            3,
            Malformed,
            "undefined name id 1",
        ),
        (
            &[
                name,
                r#"{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}"#,
            ],
            3,
            Malformed,
            "undefined expression id 0",
        ),
        (
            &[
                name,
                sort,
                r#"{"axiom":{"name":1,"levelParams":[7],"type":0,"isUnsafe":false}}"#,
            ],
            4,
            Malformed,
            "undefined name id 7",
        ),
        (
            &[sort, r#"{"ie":1,"const":{"name":0,"us":[3]}}"#],
            3,
            Malformed,
            "undefined level id 3",
        ),
        // Duplicate ids, including the implicit ones.
        (&[name, name], 3, Malformed, "name id 1 is defined twice"),
        (
            &[r#"{"in":0,"str":{"pre":0,"str":"a"}}"#],
            2,
            Malformed,
            "name id 0 is defined twice",
        ),
        (
            &[r#"{"il":0,"succ":0}"#],
            2,
            Malformed,
            "level id 0 is defined twice",
        ),
        (
            &[sort, r#"{"ie":0,"sort":0}"#],
            3,
            Malformed,
            "expression id 0 is defined twice",
        ),
        // Missing and ill-typed fields.
        (
            &[sort, r#"{"ie":1,"app":{"fn":0}}"#],
            3,
            Malformed,
            "expr.app: missing field 'arg'",
        ),
        (
            &[sort, r#"{"ie":1,"app":{"fn":0,"arg":"0"}}"#],
            3,
            Malformed,
            "field 'arg' must be a natural number",
        ),
        (
            &[sort, r#"{"ie":1,"lam":{"name":0,"type":0,"body":0}}"#],
            3,
            Malformed,
            "missing field 'binderInfo'",
        ),
        (
            &[
                sort,
                r#"{"ie":1,"lam":{"name":0,"type":0,"body":0,"binderInfo":"x"}}"#,
            ],
            3,
            Malformed,
            "unknown binder info 'x'",
        ),
        (
            &[
                sort,
                r#"{"ie":1,"letE":{"name":0,"type":0,"value":0,"body":0}}"#,
            ],
            3,
            Malformed,
            "missing field 'nondep'",
        ),
        (
            &[
                sort,
                r#"{"ie":1,"proj":{"typeName":0,"idx":4294967296,"struct":0}}"#,
            ],
            3,
            Malformed,
            "out of range",
        ),
        (
            &[r#"{"il":1,"max":[0]}"#],
            2,
            Malformed,
            "array of two level ids",
        ),
        (
            &[r#"{"ie":0,"natVal":"12x"}"#],
            2,
            Malformed,
            "decimal digits",
        ),
        (&[r#"{"ie":0,"natVal":12}"#], 2, Malformed, "decimal digits"),
        (
            &[r#"{"ie":0,"bvar":1048575}"#],
            2,
            Malformed,
            "bvar index 1048575 is too large",
        ),
        (
            &[r#"{"ie":0,"bvar":-1}"#],
            2,
            Malformed,
            "must be a natural number",
        ),
        (
            &[r#"{"ie":0,"bvar":1.5}"#],
            2,
            Malformed,
            "must be a natural number",
        ),
        (
            &[r#"{"ie":"0","bvar":0}"#],
            2,
            Malformed,
            "'ie' must be a natural number",
        ),
        (
            &[r#"{"ie":0,"mdata":{"expr":0,"data":{}}}"#],
            2,
            Malformed,
            "undefined expression id 0",
        ),
        (
            &[sort, r#"{"ie":1,"mdata":{"expr":0}}"#],
            3,
            Malformed,
            "missing field 'data'",
        ),
        (
            &[
                name,
                sort,
                r#"{"axiom":{"name":1,"levelParams":[],"type":0}}"#,
            ],
            4,
            Malformed,
            "axiom: missing field 'isUnsafe'",
        ),
        (
            &[
                name,
                sort,
                r#"{"def":{"name":1,"levelParams":[],"type":0,"value":0,"hints":"x","safety":"safe","all":[]}}"#,
            ],
            4,
            Malformed,
            "field 'hints'",
        ),
        (
            &[
                name,
                sort,
                r#"{"def":{"name":1,"levelParams":[],"type":0,"value":0,"hints":"abbrev","safety":"x","all":[]}}"#,
            ],
            4,
            Malformed,
            "unknown safety 'x'",
        ),
        (
            &[
                name,
                sort,
                r#"{"quot":{"name":1,"levelParams":[],"type":0,"kind":"x"}}"#,
            ],
            4,
            Malformed,
            "quot: unknown kind 'x'",
        ),
        (
            &[name, sort, r#"{"inductive":{"types":[],"ctors":[]}}"#],
            4,
            Malformed,
            "inductive: missing field 'recs'",
        ),
        (
            &[
                name,
                sort,
                r#"{"inductive":{"types":[{"name":1}],"ctors":[],"recs":[]}}"#,
            ],
            4,
            Malformed,
            "inductive.types: missing field 'levelParams'",
        ),
        // Unknown record kinds and shapes.
        (
            &[r#"{"foo":{}}"#],
            2,
            Malformed,
            "unknown record kind 'foo'",
        ),
        (
            &[r#"{"ie":0,"foo":0}"#],
            2,
            Malformed,
            "unknown expression record kind 'foo'",
        ),
        (
            &[r#"{"in":1,"foo":0}"#],
            2,
            Malformed,
            "unknown name record kind 'foo'",
        ),
        (
            &[r#"{"il":1,"foo":0}"#],
            2,
            Malformed,
            "unknown level record kind 'foo'",
        ),
        (
            &[r#"{"ie":0,"sort":0,"x":1}"#],
            2,
            Malformed,
            "exactly two fields",
        ),
        (
            &[r#"{"a":1,"b":2}"#],
            2,
            Malformed,
            "unrecognized record with keys",
        ),
        (&[r#"{}"#], 2, Malformed, "unrecognized record"),
        (&[META], 2, Malformed, "meta record after the first line"),
        // Bad JSON.
        (
            &[r#"{"ie":0,"sort":0} x"#],
            2,
            Malformed,
            "trailing characters",
        ),
        (&[r#"{"ie":0,"sort":0"#], 2, Malformed, "invalid JSON"),
        (&[r#"{"ie":0,"ie":1}"#], 2, Malformed, "duplicate key"),
        (&[r#"[1]"#], 2, Malformed, "expected a JSON object"),
        // A well-formed environment that declares a constant twice.
        (
            &[
                name,
                sort,
                r#"{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}"#,
                r#"{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}"#,
            ],
            5,
            Rejected,
            "constant a is declared twice",
        ),
    ];
    for (lines, line, class, needle) in cases {
        assert_err(fail(lines), *line, *class, needle);
    }
}

#[test]
fn meta_errors() {
    use ErrorClass::Malformed;
    assert_err(fail_bytes(b""), 0, Malformed, "empty input");
    assert_err(fail_bytes(b"\n\n"), 0, Malformed, "empty input");
    assert_err(
        fail_bytes(b"{\"ie\":0,\"sort\":0}\n"),
        1,
        Malformed,
        "expected the meta record",
    );
    assert_err(
        fail_bytes(b"{\"meta\":{\"format\":{\"version\":\"2.0.0\"}}}\n"),
        1,
        ErrorClass::Unsupported,
        "unsupported export format version 2.0.0",
    );
    assert_err(
        fail_bytes(b"{\"meta\":{}}\n"),
        1,
        Malformed,
        "missing field 'format'",
    );
    // Only the format version is required.
    let env = read_str("{\"meta\":{\"format\":{\"version\":\"3.0.0\"}}}\n").unwrap();
    assert_eq!(env.decls.len(), 0);
}

#[test]
fn invalid_utf8_is_an_error() {
    let mut s = export(&[r#"{"in":1,"str":{"pre":0,"str":"a"}}"#]).into_bytes();
    s.extend_from_slice(b"{\"in\":2,\"str\":{\"pre\":0,\"str\":\"\xff\"}}\n");
    assert_err(
        fail_bytes(&s),
        3,
        ErrorClass::Malformed,
        "invalid UTF-8 at column 31",
    );
}

/// Names with non-ASCII letters before, at and past the end of an
/// 8-byte word, given twice (the second time found, not added), and
/// invalid bytes after a word of ASCII.
#[test]
fn non_ascii_names_are_read_and_checked() {
    let words = [
        "\u{3b1}",
        "abcdefg\u{3b2}",
        "abcdefgh\u{3b3}x",
        "\u{2203}abcdefghijk",
    ];
    let mut lines = Vec::new();
    for (i, w) in words.iter().chain(&words).enumerate() {
        lines.push(format!(
            r#"{{"in":{},"str":{{"pre":0,"str":"{w}"}}}}"#,
            i + 1
        ));
    }
    let lines: Vec<&str> = lines.iter().map(String::as_str).collect();
    let env = read_str(&export(&lines)).unwrap();
    // Each name once (a name's second line makes the same name).
    assert_eq!(env.names.len(), 1 + words.len());
    for w in words {
        let name = env.names.find_dotted(w).expect("the name");
        assert_eq!(env.names.display(name).to_string(), w);
    }
    let mut s = export(&[r#"{"in":1,"str":{"pre":0,"str":"a"}}"#]).into_bytes();
    s.extend_from_slice(b"{\"in\":2,\"str\":{\"pre\":0,\"str\":\"abcdefghij\xce\"}}\n");
    assert_err(fail_bytes(&s), 3, ErrorClass::Malformed, "invalid UTF-8");
}

#[test]
fn deep_nesting_is_an_error_not_a_crash() {
    let deep = format!(
        "{{\"axiom\":{}{}}}",
        "[".repeat(100_000),
        "]".repeat(100_000)
    );
    assert_err(fail(&[&deep]), 2, ErrorClass::Malformed, "nesting too deep");
}

#[test]
fn errors_stop_at_the_first_bad_line() {
    // Many good lines, so the error arrives in a later batch.
    let mut lines: Vec<String> = vec![r#"{"ie":0,"sort":0}"#.into()];
    for i in 1..20_000 {
        lines.push(format!(r#"{{"ie":{i},"app":{{"fn":{},"arg":0}}}}"#, i - 1));
    }
    lines.push(r#"{"ie":20000,"app":{"fn":0,"arg":20001}}"#.into());
    lines.push(r#"{"bad"}"#.into());
    let refs: Vec<&str> = lines.iter().map(String::as_str).collect();
    assert_err(
        fail(&refs),
        20_002,
        ErrorClass::Malformed,
        "undefined expression id 20001",
    );
}

/// A regular file is read without hash-consing first; one that repeats a
/// name or a term is then read again with it, on any number of threads.
#[test]
fn files_that_repeat_records_are_read_again() {
    let text = export(&[
        r#"{"in":1,"str":{"pre":0,"str":"a"}}"#,
        r#"{"in":2,"str":{"pre":0,"str":"a"}}"#,
        r#"{"ie":0,"sort":0}"#,
        r#"{"ie":1,"sort":0}"#,
        r#"{"ie":2,"natVal":"18446744073709551616"}"#,
        r#"{"ie":3,"natVal":"18446744073709551616"}"#,
        r#"{"app":{"arg":2,"fn":0},"ie":4}"#,
        r#"{"app":{"arg":3,"fn":1},"ie":5}"#,
        r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":1,"type":4}}"#,
    ]);
    let dir = std::env::temp_dir().join(format!("nitrolean-repeat-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("repeat.ndjson");
    std::fs::write(&path, text).unwrap();
    for threads in [1, 3] {
        for lazy_proofs in [false, true] {
            let opts = nitrolean::reader::Options {
                lazy_proofs,
                threads,
            };
            let (env, _) = nitrolean::reader::read_file_with(&path, &opts).unwrap();
            assert_eq!(env.names.len(), 2, "threads={threads}");
            // sort, big literal, app.
            assert_eq!(env.exprs.len(), 3, "threads={threads}");
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

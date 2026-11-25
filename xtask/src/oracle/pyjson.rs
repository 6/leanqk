//! A JSON value whose objects keep their insertion order, written the way
//! Python's `json.dump(obj, f, indent=1)` writes it (ASCII only, `", "` and
//! `": "` separators, floats in their shortest round-trip form).

use std::fmt::Write;

#[derive(Clone, Debug, PartialEq)]
pub enum J {
    Null,
    Bool(bool),
    Int(i64),
    Float(f64),
    Str(String),
    List(Vec<J>),
    Obj(Vec<(String, J)>),
}

impl J {
    pub fn obj() -> J {
        J::Obj(Vec::new())
    }

    /// Sets `key` (in place if present, else at the end).
    pub fn set(&mut self, key: &str, v: impl Into<J>) {
        if let J::Obj(items) = self {
            let v = v.into();
            match items.iter_mut().find(|(k, _)| k == key) {
                Some(e) => e.1 = v,
                None => items.push((key.to_string(), v)),
            }
        }
    }

    pub fn get(&self, key: &str) -> Option<&J> {
        match self {
            J::Obj(items) => items.iter().find(|(k, _)| k == key).map(|(_, v)| v),
            _ => None,
        }
    }

    /// The string at `key`, or "" if there is none.
    pub fn str_of(&self, key: &str) -> &str {
        match self.get(key) {
            Some(J::Str(s)) => s,
            _ => "",
        }
    }

    /// Python's `json.dumps(self, indent=1)`.
    pub fn dumps_indent1(&self) -> String {
        let mut s = String::new();
        self.write(&mut s, 0);
        s
    }

    fn write(&self, s: &mut String, depth: usize) {
        match self {
            J::Null => s.push_str("null"),
            J::Bool(b) => s.push_str(if *b { "true" } else { "false" }),
            J::Int(i) => {
                let _ = write!(s, "{i}");
            }
            J::Float(f) => s.push_str(&py_float(*f)),
            J::Str(t) => py_str(s, t),
            J::List(v) if v.is_empty() => s.push_str("[]"),
            J::Obj(v) if v.is_empty() => s.push_str("{}"),
            J::List(v) => {
                s.push('[');
                for (i, x) in v.iter().enumerate() {
                    s.push_str(if i > 0 { ",\n" } else { "\n" });
                    s.push_str(&" ".repeat(depth + 1));
                    x.write(s, depth + 1);
                }
                s.push('\n');
                s.push_str(&" ".repeat(depth));
                s.push(']');
            }
            J::Obj(v) => {
                s.push('{');
                for (i, (k, x)) in v.iter().enumerate() {
                    s.push_str(if i > 0 { ",\n" } else { "\n" });
                    s.push_str(&" ".repeat(depth + 1));
                    py_str(s, k);
                    s.push_str(": ");
                    x.write(s, depth + 1);
                }
                s.push('\n');
                s.push_str(&" ".repeat(depth));
                s.push('}');
            }
        }
    }
}

impl From<&str> for J {
    fn from(s: &str) -> J {
        J::Str(s.to_string())
    }
}
impl From<String> for J {
    fn from(s: String) -> J {
        J::Str(s)
    }
}
impl From<bool> for J {
    fn from(b: bool) -> J {
        J::Bool(b)
    }
}
impl From<i64> for J {
    fn from(i: i64) -> J {
        J::Int(i)
    }
}
impl From<usize> for J {
    fn from(i: usize) -> J {
        J::Int(i as i64)
    }
}
impl From<u64> for J {
    fn from(i: u64) -> J {
        J::Int(i as i64)
    }
}
impl From<f64> for J {
    fn from(f: f64) -> J {
        J::Float(f)
    }
}
impl From<Option<String>> for J {
    fn from(o: Option<String>) -> J {
        o.map(J::Str).unwrap_or(J::Null)
    }
}

/// Python's `repr(float)`.
pub fn py_float(f: f64) -> String {
    if f.is_nan() {
        return "NaN".into();
    }
    if f.is_infinite() {
        return if f > 0.0 { "Infinity" } else { "-Infinity" }.into();
    }
    let a = f.abs();
    if a != 0.0 && !(1e-4..1e16).contains(&a) {
        let e = format!("{f:e}");
        let (m, x) = e.split_once('e').unwrap();
        let x: i32 = x.parse().unwrap();
        let sign = if x < 0 { '-' } else { '+' };
        return format!("{m}e{sign}{:02}", x.abs());
    }
    format!("{f:?}")
}

/// A JSON string with `ensure_ascii`: everything outside space..~ escaped.
fn py_str(s: &mut String, t: &str) {
    s.push('"');
    for c in t.chars() {
        match c {
            '"' => s.push_str("\\\""),
            '\\' => s.push_str("\\\\"),
            '\n' => s.push_str("\\n"),
            '\r' => s.push_str("\\r"),
            '\t' => s.push_str("\\t"),
            '\u{8}' => s.push_str("\\b"),
            '\u{c}' => s.push_str("\\f"),
            ' '..='~' => s.push(c),
            _ => {
                let mut buf = [0u16; 2];
                for u in c.encode_utf16(&mut buf) {
                    let _ = write!(s, "\\u{u:04x}");
                }
            }
        }
    }
    s.push('"');
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn like_python() {
        let mut o = J::obj();
        o.set("a", "x\u{ab}y\u{bb}\u{7f}\n");
        o.set(
            "n",
            J::List(vec![J::Float(5.37), J::Float(3.0), J::Int(-2)]),
        );
        o.set("e", J::List(vec![]));
        o.set("z", J::Null);
        assert_eq!(
            o.dumps_indent1(),
            "{\n \"a\": \"x\\u00aby\\u00bb\\u007f\\n\",\n \"n\": [\n  5.37,\n  3.0,\n  -2\n ],\n \"e\": [],\n \"z\": null\n}"
        );
        assert_eq!(py_float(1e16), "1e+16");
        assert_eq!(py_float(1.5e-5), "1.5e-05");
        assert_eq!(py_float(0.0), "0.0");
    }
}

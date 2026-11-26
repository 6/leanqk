//! Read a bounded prefix independently of the regular reader.

use std::fs::File;
use std::path::Path;
use std::time::{Duration, Instant};

use crate::env::Env;
use crate::olean::Mapped;

use super::{Lines, Options, ReadError, ReadStats, finish, io_error, read_open_file, state};

pub(crate) struct Overlap<T> {
    pub(crate) checked: Option<T>,
    pub(crate) preview_read: Duration,
    pub(crate) preview_check: Duration,
    pub(crate) full_read: Duration,
}

pub(crate) fn read_with_prefix<T: Send>(
    path: &Path,
    opts: &Options,
    bytes: Option<usize>,
    readers: usize,
    check: impl FnOnce(Env) -> Option<T> + Send,
) -> Result<(Env, ReadStats, Option<Overlap<T>>), ReadError> {
    const MIN_EXPORT_BYTES: u64 = 4 << 30;
    const MAX_PREFIX_BYTES: u64 = 1152 << 20;
    let f = File::open(path).map_err(|e| io_error(path, e))?;
    let mapped_prefix = f.metadata().ok().filter(|m| m.is_file()).and_then(|m| {
        let size = m.len();
        let bytes = match bytes {
            Some(bytes) => bytes,
            None if size >= MIN_EXPORT_BYTES => {
                (size.saturating_mul(17) / 100).min(MAX_PREFIX_BYTES) as usize
            }
            None => return None,
        };
        if bytes == 0 || bytes as u64 >= size {
            return None;
        }
        Mapped::new(&f).map(|map| (map, bytes))
    });
    let Some((map, bytes)) = mapped_prefix else {
        return read_open_file(f, opts).map(|(env, stats)| (env, stats, None));
    };

    std::thread::scope(|s| {
        let start = Instant::now();
        let parallel_opts = Options {
            threads: readers,
            ..*opts
        };
        let prefix = std::thread::Builder::new().spawn_scoped(s, move || {
            let env = read_prefix(&map, &parallel_opts, bytes);
            drop(map);
            let preview_read = start.elapsed();
            let checked = env.and_then(check);
            (checked, preview_read, start.elapsed() - preview_read)
        });
        let Ok(prefix) = prefix else {
            return read_open_file(f, opts).map(|(env, stats)| (env, stats, None));
        };
        let result = read_open_file(f, &parallel_opts);
        let full_read = start.elapsed();
        let overlap = prefix
            .join()
            .ok()
            .map(|(checked, preview_read, preview_check)| Overlap {
                checked,
                preview_read,
                preview_check,
                full_read,
            });
        result.map(|(env, stats)| (env, stats, overlap))
    })
}

fn read_prefix(map: &Mapped, opts: &Options, bytes: usize) -> Option<Env> {
    let data = map.bytes().get(..bytes)?;
    let end = data.iter().rposition(|&byte| byte == b'\n')? + 1;
    let data = &data[..end];
    let mut st = state(opts, end as u64, true);
    st.index_threads = Some(1);
    let result = finish(st, |st| {
        const STEP: usize = 16 << 20;
        let mut lines = Lines::default();
        let mut start = 0;
        while start < end {
            let limit = (start + STEP).min(end);
            let stop = super::memchr_from(data, limit - 1).map_or(end, |nl| nl + 1);
            st.lines(&mut lines, &data[start..stop])?;
            map.release(start, stop);
            start = stop;
        }
        st.end_lines(lines)
    })
    .ok()?;
    (result.dup.is_none() && !result.env.blocks.is_empty()).then_some(result.env)
}

//! Process resource statistics.

/// Peak resident set size of this process in bytes, where the platform
/// reports it (Linux: `VmHWM` in `/proc/self/status`).
pub fn peak_rss_bytes() -> Option<u64> {
    let s = std::fs::read_to_string("/proc/self/status").ok()?;
    let line = s.lines().find(|l| l.starts_with("VmHWM:"))?;
    let kb: u64 = line
        .trim_start_matches("VmHWM:")
        .trim()
        .trim_end_matches("kB")
        .trim()
        .parse()
        .ok()?;
    Some(kb * 1024)
}

/// Current resident set size of this process in bytes, where the platform
/// reports it (Linux: `/proc/self/statm`, in pages of the system's size,
/// which is not 4 KiB everywhere).
pub fn rss_bytes() -> Option<u64> {
    let s = std::fs::read_to_string("/proc/self/statm").ok()?;
    let pages: u64 = s.split_whitespace().nth(1)?.parse().ok()?;
    Some(pages * crate::slab::page_size() as u64)
}

/// The memory this process may use: the machine's, or its control group's
/// limit if lower (Linux only).
pub fn memory_limit_bytes() -> Option<u64> {
    let meminfo = std::fs::read_to_string("/proc/meminfo").ok()?;
    let total = meminfo
        .lines()
        .find_map(|l| l.strip_prefix("MemTotal:"))?
        .trim()
        .strip_suffix("kB")?
        .trim()
        .parse::<u64>()
        .ok()?
        * 1024;
    Some(cgroup_limit().map_or(total, |c| c.min(total)))
}

/// The memory limit of this process's control group (v2, or else v1).
fn cgroup_limit() -> Option<u64> {
    let read = |p: &str| -> Option<u64> { std::fs::read_to_string(p).ok()?.trim().parse().ok() };
    let groups = std::fs::read_to_string("/proc/self/cgroup").unwrap_or_default();
    if let Some(path) = groups.lines().find_map(|l| l.strip_prefix("0::")) {
        // Every level up to the root may limit it.
        let mut dir = std::path::PathBuf::from("/sys/fs/cgroup").join(path.trim_start_matches('/'));
        let mut min: Option<u64> = None;
        loop {
            if let Some(v) = read(&dir.join("memory.max").to_string_lossy()) {
                min = Some(min.map_or(v, |m| m.min(v)));
            }
            if dir.as_os_str() == "/sys/fs/cgroup" || !dir.pop() {
                break;
            }
        }
        if min.is_some() {
            return min;
        }
    }
    read("/sys/fs/cgroup/memory/memory.limit_in_bytes")
}

/// Format a byte count with a binary unit.
pub fn human_bytes(b: u64) -> String {
    const UNITS: [&str; 5] = ["B", "KiB", "MiB", "GiB", "TiB"];
    let mut v = b as f64;
    let mut u = 0;
    while v >= 1024.0 && u + 1 < UNITS.len() {
        v /= 1024.0;
        u += 1;
    }
    if u == 0 {
        format!("{b} B")
    } else {
        format!("{v:.1} {}", UNITS[u])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn formats() {
        assert_eq!(human_bytes(12), "12 B");
        assert_eq!(human_bytes(1536), "1.5 KiB");
        assert_eq!(human_bytes(3 << 30), "3.0 GiB");
    }
}

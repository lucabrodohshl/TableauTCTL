// ============================================================================
// tctl/utils.hpp — Utility functions
// ============================================================================

#ifndef CTL_UTILS_HPP
#define CTL_UTILS_HPP

#include <string>
#include <vector>

namespace tctl {

// ── File I/O ────────────────────────────────────────────────────────────────

/// Read a text file and return its content as a vector of lines.
/// Throws std::runtime_error if the file cannot be opened.
std::vector<std::string> read_lines(const std::string& path);

// ── String helpers ──────────────────────────────────────────────────────────

/// Trim leading and trailing whitespace from a string.
std::string trim(const std::string& s);

/// Strip an inline comment (everything from the first '#' onward).
/// Returns the portion before '#', trimmed.
std::string strip_comment(const std::string& line);

/// Return true if the line is empty or consists only of whitespace
/// (after comment stripping).
bool is_blank_or_comment(const std::string& line);

}  // namespace tctl

#endif  // CTL_UTILS_HPP

// ============================================================================
// utils.cpp — File I/O and string utilities
// ============================================================================

#include "tctl/utils.hpp"

#include <fstream>
#include <stdexcept>

namespace tctl {

// ── read_lines ──────────────────────────────────────────────────────────────

std::vector<std::string> read_lines(const std::string& path) {
    std::ifstream file(path);
    if (!file.is_open()) {
        throw std::runtime_error("cannot open file: " + path);
    }

    std::vector<std::string> lines;
    std::string line;
    while (std::getline(file, line)) {
        lines.push_back(std::move(line));
    }
    return lines;
}

// ── trim ────────────────────────────────────────────────────────────────────

std::string trim(const std::string& s) {
    auto start = s.find_first_not_of(" \t\r\n");
    if (start == std::string::npos) return "";
    auto end = s.find_last_not_of(" \t\r\n");
    return s.substr(start, end - start + 1);
}

// ── strip_comment ───────────────────────────────────────────────────────────

std::string strip_comment(const std::string& line) {
    auto pos = line.find('#');
    if (pos == std::string::npos) {
        return trim(line);
    }
    return trim(line.substr(0, pos));
}

// ── is_blank_or_comment ─────────────────────────────────────────────────────

bool is_blank_or_comment(const std::string& line) {
    return strip_comment(line).empty();
}

}  // namespace tctl

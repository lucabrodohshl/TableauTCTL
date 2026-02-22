// ============================================================================
// tctl/lexer.hpp — Tokeniser for the tctl input language
// ============================================================================
//
// The lexer converts a raw input string into a stream of tokens.  Every
// token carries its source position (line, column) so that error messages
// can point the user to the exact location of a problem.
//
// Recognised tokens:
//   Identifiers  [A-Za-z_][A-Za-z0-9_]*   (includes "true", "false", "EX",
//                                            "AX", "EF", "AF", "EG", "AG",
//                                            "E", "A", "U" as keywords)
//   Symbols      !  &  |  (  )  ->  <->
//   EOF          end-of-input sentinel
//
// Whitespace is skipped.  Inline comments starting with '#' discard the
// rest of the line.
//
// ============================================================================

#ifndef CTL_LEXER_HPP
#define CTL_LEXER_HPP

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

namespace tctl {

// ── SourcePos ───────────────────────────────────────────────────────────────
// 1-based line and column, used for error reporting.

struct SourcePos {
    std::uint32_t line   = 1;
    std::uint32_t column = 1;
};

// ── TokenKind ───────────────────────────────────────────────────────────────

enum class TokenKind : std::uint8_t {
    // Literals / identifiers
    Identifier,     // generic atom name
    IntLiteral,     // integer constant (digits, with optional -)
    KwTrue,         // "true"
    KwFalse,        // "false"

    // Temporal keywords
    KwEX,           // "EX"
    KwAX,           // "AX"
    KwEF,           // "EF"
    KwAF,           // "AF"
    KwEG,           // "EG"
    KwAG,           // "AG"
    KwE,            // bare "E" (for E(φ U ψ))
    KwA,            // bare "A" (for A(φ U ψ))
    KwU,            // "U"  (inside E/A until)
    KwR,            // "R"  (inside E/A release)

    // Boolean operators
    Bang,           // !
    Amp,            // &
    Pipe,           // |
    Arrow,          // ->
    DoubleArrow,    // <->

    // Arithmetic operators
    Plus,           // +
    Minus,          // -
    Star,           // *

    // Comparison operators
    LessEq,         // <=
    Less,           // <
    GreaterEq,      // >=
    Greater,        // >
    Equal,          // =

    // Delimiters
    LParen,         // (
    RParen,         // )
    LBracket,       // [
    RBracket,       // ]
    LBrace,         // {
    RBrace,         // }
    Comma,          // ,

    // Keywords for TCTL
    KwInf,          // inf (infinity for time bounds)

    // Sentinel
    Eof
};

/// Human-readable name for debugging.
const char* token_kind_name(TokenKind k) noexcept;

// ── Token ───────────────────────────────────────────────────────────────────

struct Token {
    TokenKind   kind = TokenKind::Eof;
    std::string text;
    SourcePos   pos;
};

// ── Lexer ───────────────────────────────────────────────────────────────────
// Stores the full input and lazily produces tokens via next().
// Errors are reported by throwing std::runtime_error with a formatted
// message that includes line and column.

class Lexer {
public:
    /// Construct a lexer over the given input.
    /// @param source  the full text to tokenise
    /// @param line    the starting line number (default 1)
    explicit Lexer(std::string_view source, std::uint32_t line = 1);

    /// Return the next token.  Repeated calls after EOF keep returning EOF.
    Token next();

    /// Peek at the next token without consuming it.
    const Token& peek();
    
    /// Peek at the second-next token (lookahead 2) without consuming.
    Token peek2();

    /// Current source position (of the next character to be read).
    SourcePos current_pos() const noexcept;

private:
    void skip_whitespace_and_comments();
    Token read_identifier_or_keyword();
    Token read_integer();
    Token make_token(TokenKind kind, std::string text, SourcePos pos);

    [[noreturn]] void error(const std::string& msg) const;

    std::string_view src_;
    std::size_t      idx_ = 0;
    SourcePos        pos_;
    bool             has_peeked_ = false;
    Token            peeked_;
};

// ── tokenise ────────────────────────────────────────────────────────────────
// Convenience: tokenise a complete string and return a vector of tokens
// (including the trailing Eof).

std::vector<Token> tokenise(std::string_view source, std::uint32_t line = 1);

}  // namespace tctl

#endif  // CTL_LEXER_HPP

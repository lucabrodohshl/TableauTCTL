// ============================================================================
// tctl/parser.hpp — Recursive-descent parser for tctl formulas
// ============================================================================
//
// Grammar (informal, with precedence already encoded):
//
//   formula     ::= iff_expr
//   iff_expr    ::= impl_expr ( '<->' impl_expr )*        (left-assoc)
//   impl_expr   ::= or_expr   ( '->'  impl_expr )?        (right-assoc)
//   or_expr     ::= and_expr  ( '|'   and_expr )*         (left-assoc)
//   and_expr    ::= unary     ( '&'   unary )*            (left-assoc)
//   unary       ::= '!' unary
//                  | 'EX' unary
//                  | 'AX' unary
//                  | 'EF' unary
//                  | 'AF' unary
//                  | 'EG' unary
//                  | 'AG' unary
//                  | primary
//   primary     ::= 'true' | 'false' | IDENTIFIER
//                  | 'E' '(' formula 'U' formula ')'
//                  | 'A' '(' formula 'U' formula ')'
//                  | '(' formula ')'
//
// Precedence (highest → lowest):
//   1. !, EX, AX, EF, AF, EG, AG   (unary prefix)
//   2. &                            (left-assoc)
//   3. |                            (left-assoc)
//   4. ->                           (right-assoc)
//   5. <->                          (left-assoc)
//
// ============================================================================

#ifndef CTL_PARSER_HPP
#define CTL_PARSER_HPP

#include "tctl/ast.hpp"
#include "tctl/lexer.hpp"

#include <string>
#include <string_view>

namespace tctl {

// ── ParseError ──────────────────────────────────────────────────────────────
// Carries the formatted error string for display.

struct ParseError {
    std::string message;  // already formatted with line/column
};

// ── Parser ──────────────────────────────────────────────────────────────────
// Takes a Lexer and a FormulaFactory reference.  Parses exactly one formula
// and returns its FormulaId.  Throws std::runtime_error on syntax errors
// with the format: <line>: ERROR: <msg> at column <n>

class Parser {
public:
    Parser(Lexer& lexer, FormulaFactory& factory);

    /// Parse a complete formula (expects Eof after).
    FormulaId parse();

    /// Parse a formula without requiring Eof — useful for sub-expressions.
    FormulaId parse_formula();

private:
    // ── Recursive-descent methods, one per precedence level ─────────────
    FormulaId parse_iff();
    FormulaId parse_implies();
    FormulaId parse_or();
    FormulaId parse_and();
    FormulaId parse_unary();
    FormulaId parse_primary();

    // ── TCTL: Time interval parsing ─────────────────────────────────────
    // Parses [a,b] or [a,inf) interval; validates a < b.
    // Returns {lower, upper} with strictness or throws on invalid interval.
    struct TimeInterval {
        TimeBound lower;
        TimeBound upper;
    };
    TimeInterval parse_time_interval();
    TimeInterval parse_relational_bound();  // Parse `<5`, `<=10`, etc.
    bool has_time_interval();    // Peeks to check if next token is '[' or '('
    bool has_relational_bound(); // Peeks to check if next token is a comparison

    // ── Arithmetic expression parsing ───────────────────────────────────
    FormulaId parse_int_expr();
    FormulaId parse_int_term();
    FormulaId parse_int_factor();
    bool is_comparison_op(TokenKind kind) const;
    bool is_int_start(TokenKind kind) const;

    // ── Helpers ─────────────────────────────────────────────────────────
    Token expect(TokenKind kind, const std::string& context);
    [[noreturn]] void error(const Token& tok, const std::string& msg);

    Lexer&          lex_;
    FormulaFactory& fac_;
};

// ── Convenience free function ───────────────────────────────────────────────
// Parse a single formula from a string.

FormulaId parse_formula(const std::string& input, FormulaFactory& factory,
                        std::uint32_t line = 1);

}  // namespace tctl

#endif  // CTL_PARSER_HPP

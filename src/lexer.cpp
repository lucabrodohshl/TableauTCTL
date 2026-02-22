// ============================================================================
// lexer.cpp — tctl tokeniser implementation
// ============================================================================

#include "tctl/lexer.hpp"

#include <cctype>
#include <stdexcept>

namespace tctl {

// ── token_kind_name ─────────────────────────────────────────────────────────

const char* token_kind_name(TokenKind k) noexcept {
    switch (k) {
        case TokenKind::Identifier:   return "identifier";
        case TokenKind::IntLiteral:   return "integer";
        case TokenKind::KwTrue:       return "true";
        case TokenKind::KwFalse:      return "false";
        case TokenKind::KwEX:         return "EX";
        case TokenKind::KwAX:         return "AX";
        case TokenKind::KwEF:         return "EF";
        case TokenKind::KwAF:         return "AF";
        case TokenKind::KwEG:         return "EG";
        case TokenKind::KwAG:         return "AG";
        case TokenKind::KwE:          return "E";
        case TokenKind::KwA:          return "A";
        case TokenKind::KwU:          return "U";
        case TokenKind::KwR:          return "R";
        case TokenKind::Bang:         return "!";
        case TokenKind::Amp:          return "&";
        case TokenKind::Pipe:         return "|";
        case TokenKind::Arrow:        return "->";
        case TokenKind::DoubleArrow:  return "<->";
        case TokenKind::Plus:         return "+";
        case TokenKind::Minus:        return "-";
        case TokenKind::Star:         return "*";
        case TokenKind::LessEq:       return "<=";
        case TokenKind::Less:         return "<";
        case TokenKind::GreaterEq:    return ">=";
        case TokenKind::Greater:      return ">";
        case TokenKind::Equal:        return "=";
        case TokenKind::LParen:       return "(";
        case TokenKind::RParen:       return ")";
        case TokenKind::LBracket:     return "[";
        case TokenKind::RBracket:     return "]";
        case TokenKind::LBrace:       return "{";
        case TokenKind::RBrace:       return "}";
        case TokenKind::Comma:        return ",";
        case TokenKind::KwInf:        return "inf";
        case TokenKind::Eof:          return "EOF";
    }
    return "?";
}

// ── Lexer ───────────────────────────────────────────────────────────────────

Lexer::Lexer(std::string_view source, std::uint32_t line)
    : src_(source), pos_{line, 1} {}

SourcePos Lexer::current_pos() const noexcept {
    return pos_;
}

Token Lexer::make_token(TokenKind kind, std::string text, SourcePos pos) {
    return Token{kind, std::move(text), pos};
}

void Lexer::error(const std::string& msg) const {
    // Format: <line>: ERROR: <message> at column <n>
    throw std::runtime_error(
        std::to_string(pos_.line) + ": ERROR: " + msg +
        " at column " + std::to_string(pos_.column));
}

// ── skip_whitespace_and_comments ────────────────────────────────────────────
// Skip spaces, tabs, and '#' comments (to end of line).

void Lexer::skip_whitespace_and_comments() {
    while (idx_ < src_.size()) {
        char c = src_[idx_];
        if (c == '#') {
            // Consume until end of string (we handle single lines).
            while (idx_ < src_.size() && src_[idx_] != '\n') {
                ++idx_;
                ++pos_.column;
            }
        } else if (c == '\n') {
            ++idx_;
            pos_.line++;
            pos_.column = 1;
        } else if (std::isspace(static_cast<unsigned char>(c))) {
            ++idx_;
            ++pos_.column;
        } else {
            break;
        }
    }
}

// ── read_identifier_or_keyword ──────────────────────────────────────────────
// Read [A-Za-z_][A-Za-z0-9_]* and classify as keyword or identifier.

Token Lexer::read_identifier_or_keyword() {
    SourcePos start = pos_;
    std::size_t begin = idx_;

    while (idx_ < src_.size() &&
           (std::isalnum(static_cast<unsigned char>(src_[idx_])) ||
            src_[idx_] == '_')) {
        ++idx_;
        ++pos_.column;
    }

    std::string text(src_.substr(begin, idx_ - begin));

    // ── keyword classification ──────────────────────────────────────────
    // Two-letter temporal keywords: EX, AX, EF, AF, EG, AG
    // One-letter temporal: E, A, U
    // Constants: true, false
    // Everything else is an atom identifier.

    TokenKind kind = TokenKind::Identifier;

    if (text == "true")       kind = TokenKind::KwTrue;
    else if (text == "false") kind = TokenKind::KwFalse;
    else if (text == "EX")    kind = TokenKind::KwEX;
    else if (text == "AX")    kind = TokenKind::KwAX;
    else if (text == "EF")    kind = TokenKind::KwEF;
    else if (text == "AF")    kind = TokenKind::KwAF;
    else if (text == "EG")    kind = TokenKind::KwEG;
    else if (text == "AG")    kind = TokenKind::KwAG;
    else if (text == "E")     kind = TokenKind::KwE;
    else if (text == "A")     kind = TokenKind::KwA;
    else if (text == "U")     kind = TokenKind::KwU;
    else if (text == "R")     kind = TokenKind::KwR;
    else if (text == "inf" || text == "INF" || text == "Inf") kind = TokenKind::KwInf;

    return make_token(kind, std::move(text), start);
}

// ── read_integer ────────────────────────────────────────────────────────────
// Read a sequence of digits (decimal integer).

Token Lexer::read_integer() {
    SourcePos start = pos_;
    std::size_t begin = idx_;

    while (idx_ < src_.size() && std::isdigit(static_cast<unsigned char>(src_[idx_]))) {
        ++idx_;
        ++pos_.column;
    }

    std::string text(src_.substr(begin, idx_ - begin));
    return make_token(TokenKind::IntLiteral, std::move(text), start);
}

// ── next ────────────────────────────────────────────────────────────────────

Token Lexer::next() {
    // If we already peeked, return the stored token.
    if (has_peeked_) {
        has_peeked_ = false;
        return std::move(peeked_);
    }

    skip_whitespace_and_comments();

    if (idx_ >= src_.size()) {
        return make_token(TokenKind::Eof, "", pos_);
    }

    SourcePos start = pos_;
    char c = src_[idx_];

    // ── single-character tokens ─────────────────────────────────────────
    if (c == '!') { ++idx_; ++pos_.column; return make_token(TokenKind::Bang,     "!", start); }
    if (c == '&') { ++idx_; ++pos_.column; return make_token(TokenKind::Amp,      "&", start); }
    if (c == '|') { ++idx_; ++pos_.column; return make_token(TokenKind::Pipe,     "|", start); }
    if (c == '(') { ++idx_; ++pos_.column; return make_token(TokenKind::LParen,   "(", start); }
    if (c == ')') { ++idx_; ++pos_.column; return make_token(TokenKind::RParen,   ")", start); }
    if (c == '[') { ++idx_; ++pos_.column; return make_token(TokenKind::LBracket, "[", start); }
    if (c == ']') { ++idx_; ++pos_.column; return make_token(TokenKind::RBracket, "]", start); }
    if (c == '{') { ++idx_; ++pos_.column; return make_token(TokenKind::LBrace,   "{", start); }
    if (c == '}') { ++idx_; ++pos_.column; return make_token(TokenKind::RBrace,   "}", start); }
    if (c == ',') { ++idx_; ++pos_.column; return make_token(TokenKind::Comma,    ",", start); }
    if (c == '+') { ++idx_; ++pos_.column; return make_token(TokenKind::Plus,     "+", start); }
    if (c == '*') { ++idx_; ++pos_.column; return make_token(TokenKind::Star,     "*", start); }
    if (c == '=') { ++idx_; ++pos_.column; return make_token(TokenKind::Equal,    "=", start); }

    // ── multi-character operators ───────────────────────────────────────
    // <->  must be checked before <= 
    if (c == '<') {
        if (idx_ + 2 < src_.size() && src_[idx_ + 1] == '-' && src_[idx_ + 2] == '>') {
            idx_ += 3; pos_.column += 3;
            return make_token(TokenKind::DoubleArrow, "<->", start);
        }
        if (idx_ + 1 < src_.size() && src_[idx_ + 1] == '=') {
            idx_ += 2; pos_.column += 2;
            return make_token(TokenKind::LessEq, "<=", start);
        }
        ++idx_; ++pos_.column;
        return make_token(TokenKind::Less, "<", start);
    }

    if (c == '>') {
        if (idx_ + 1 < src_.size() && src_[idx_ + 1] == '=') {
            idx_ += 2; pos_.column += 2;
            return make_token(TokenKind::GreaterEq, ">=", start);
        }
        ++idx_; ++pos_.column;
        return make_token(TokenKind::Greater, ">", start);
    }

    if (c == '-') {
        if (idx_ + 1 < src_.size() && src_[idx_ + 1] == '>') {
            idx_ += 2; pos_.column += 2;
            return make_token(TokenKind::Arrow, "->", start);
        }
        ++idx_; ++pos_.column;
        return make_token(TokenKind::Minus, "-", start);
    }

    // ── integer literals ────────────────────────────────────────────────
    if (std::isdigit(static_cast<unsigned char>(c))) {
        return read_integer();
    }

    // ── identifiers / keywords ──────────────────────────────────────────
    if (std::isalpha(static_cast<unsigned char>(c)) || c == '_') {
        return read_identifier_or_keyword();
    }

    error(std::string("unexpected character '") + c + "'");
}

// ── peek ────────────────────────────────────────────────────────────────────

const Token& Lexer::peek() {
    if (!has_peeked_) {
        peeked_ = next();
        has_peeked_ = true;
    }
    return peeked_;
}

// ── peek2 ───────────────────────────────────────────────────────────────────
// Lookahead 2 tokens. Returns the second token without consuming any.
// This is a bit hacky but necessary for distinguishing time intervals from parens.

Token Lexer::peek2() {
    // Save state
    auto saved_idx = idx_;
    auto saved_pos = pos_;
    auto saved_has_peeked = has_peeked_;
    auto saved_peeked = peeked_;
    
    // Consume first peeked token if any
    if (has_peeked_) {
        has_peeked_ = false;
    } else {
        next(); // Consume first token
    }
    
    // Get second token
    Token second = next();
    
    // Restore state
    idx_ = saved_idx;
    pos_ = saved_pos;
    has_peeked_ = saved_has_peeked;
    peeked_ = saved_peeked;
    
    return second;
}

// ── tokenise (convenience) ──────────────────────────────────────────────────

std::vector<Token> tokenise(std::string_view source, std::uint32_t line) {
    Lexer lex(source, line);
    std::vector<Token> toks;
    for (;;) {
        Token t = lex.next();
        toks.push_back(t);
        if (t.kind == TokenKind::Eof) break;
    }
    return toks;
}

}  // namespace tctl

var __assign = (this && this.__assign) || function () {
    __assign = Object.assign || function(t) {
        for (var s, i = 1, n = arguments.length; i < n; i++) {
            s = arguments[i];
            for (var p in s) if (Object.prototype.hasOwnProperty.call(s, p))
                t[p] = s[p];
        }
        return t;
    };
    return __assign.apply(this, arguments);
};
function sexpToString(sexp) {
    if (typeof sexp === "string") {
        return sexp;
    }
    if (typeof sexp === "number") {
        return sexp.toString();
    }
    return "(".concat(sexp.map(sexpToString).join(" "), ")");
}
function parseTrace(input) {
    // Split the input into lines
    input = input.trim();
    var tokens = input.split('\n');
    // As you go through the lines, find the trace markers, their depths, and their positions
    var markers = [];
    var position = 0;
    for (var i = 0; i < tokens.length; i++) {
        var line = tokens[i];
        if (line.startsWith(">")) {
            var _a = countDepth(line, '>'), depth = _a[0], epos = _a[1];
            markers.push({ typ: ">", depth: depth, spos: position, epos: position + epos - 1 });
        }
        else if (line.startsWith("<")) {
            var _b = countDepth(line, '<'), depth = _b[0], epos = _b[1];
            markers.push({ typ: "<", depth: depth, spos: position, epos: position + epos - 1 });
        }
        position += line.length + 1; // +1 for the newline character
    }
    var fullMarkers = [];
    // For each marker, parse the S-expression, which is between the marker and the next marker
    for (var i = 0; i < markers.length - 1; i++) {
        var marker = markers[i];
        var nextMarker = markers[i + 1];
        var sexp = input.slice(marker.epos, nextMarker === null || nextMarker === void 0 ? void 0 : nextMarker.spos).trim();
        if (sexp) {
            fullMarkers.push(__assign(__assign({}, marker), { sexp: parseSExpression(sexp) }));
        }
    }
    // Parse the last S-expression
    var lastMarker = markers[markers.length - 1];
    var lastSexp = input.slice(lastMarker.epos).trim();
    if (lastSexp) {
        fullMarkers.push(__assign(__assign({}, lastMarker), { sexp: parseSExpression(lastSexp) }));
    }
    var _c = createTraceFromMarkers(fullMarkers, 0, fullMarkers.length - 1), trace = _c[0], _ = _c[1];
    return trace;
}
function createTraceFromMarkers(markers, start, end) {
    if (markers[start].typ !== ">") {
        throw new Error("Expected start marker to be >");
    }
    var startMarker = markers[start];
    var nextMarker = markers[start + 1];
    var children = [];
    if (startMarker.depth === nextMarker.depth) {
        // This is a leaf trace
        return [{ start: startMarker.sexp, children: [], end: nextMarker.sexp, depth: startMarker.depth }, start + 2];
    }
    while (start < end) {
        if (markers[start + 1].typ === "<") {
            break;
        }
        var _a = createTraceFromMarkers(markers, start + 1, end), child = _a[0], next = _a[1];
        start = next - 1;
        children.push(child);
    }
    return [{ start: startMarker.sexp, children: children, end: markers[start + 1].sexp, depth: startMarker.depth }, start + 2];
}
/**
 * Parses the tokens into Trace objects recursively.
 * @param tokens - Array of lines from the trace log.
 * @param currentDepth - The current depth of recursion based on `> > ...>` symbols.
 * @param index - The current line index being parsed.
 * @returns - A tuple containing the parsed Trace and the next line index.
 */
function parseTraceTokens(tokens, currentDepth, index) {
    if (index === void 0) { index = 0; }
    var depth = countDepth(tokens[index], '>'); // Detect depth by counting `>`s
    // if (depth !== currentDepth) {
    //     throw new Error(`Unexpected depth at line ${index}: ${tokens[index]}`);
    // }
    // Parse the start S-expression after the '>' markers
    var startSexp = parseSExpressionFromTrace(tokens[index]);
    var trace = {
        start: startSexp,
        children: [],
        end: null,
        depth: currentDepth
    };
    index++;
    // Parse children traces recursively
    while (index < tokens.length) {
        if (tokens[index].startsWith('<')) {
            break; // End of this trace, return control to parent
        }
        var childDepth = countDepth(tokens[index], '>');
        if (childDepth > currentDepth) {
            var _a = parseTraceTokens(tokens, childDepth, index), childTrace = _a.trace, nextIndex = _a.nextIndex;
            trace.children.push(childTrace);
            index = nextIndex;
        }
        else {
            break; // Encountered a sibling or parent's end trace
        }
    }
    // Parse the end S-expression after the '<' markers
    if (index < tokens.length && tokens[index].startsWith('<')) {
        trace.end = parseSExpressionFromTrace(tokens[index]);
        index++;
    }
    return { trace: trace, nextIndex: index };
}
/**
 * Parse a single line from the trace and extract the S-expression.
 * Assumes the line starts with `> > ...>` or `< < ...<`.
 * @param line - The trace line.
 * @returns - The extracted S-expression.
 */
function parseSExpressionFromTrace(line) {
    var sExpressionPart = line.replace(/[><\s]+/g, ''); // Remove `>`, `<`, and spaces
    return parseSExpression(sExpressionPart);
}
/**
 * Counts the depth by the number of `>` or `<` symbols at the start of the line.
 * @param line - The trace line.
 * @param char - The character to count (`>` or `<`).
 * @returns - The depth of the trace.
 */
function countDepth(line, char) {
    var depth = line.trim().split("").findIndex(function (c) { return c !== char && c !== ' '; });
    var epos = depth;
    if (line[depth] === "[") {
        var end = line.indexOf("]");
        depth = +line.slice(depth + 1, end) + 1;
        epos = end + 1;
    }
    return [depth - 1, epos + 1];
}
/**
 * A simple S-expression parser, as implemented before.
 * @param input - The input string containing the S-expression.
 * @returns - The parsed S-expression.
 */
function parseSExpression(input) {
    var tokens = tokenize(input);
    var _a = parseTokens(tokens), expression = _a[0], _ = _a[1];
    return expression;
}
/**
 * Tokenizes the input S-expression string.
 * @param input - The input string containing the S-expression.
 * @returns - Array of tokenized strings.
 */
function tokenize(input) {
    var regex = /([()])|("(?:\\.|[^"\\])*")|[^\s()]+/g; // Match parentheses, strings, or atoms
    var tokens = input.match(regex);
    if (!tokens) {
        throw new Error("Failed to tokenize input.");
    }
    return tokens;
}
/**
 * Parses tokens recursively into nested S-expression structures.
 * @param tokens - The array of tokens to parse.
 * @param index - The current token index (used internally for recursion).
 * @returns - A tuple containing the parsed S-expression and the next token index.
 */
function parseTokens(tokens, index) {
    if (index === void 0) { index = 0; }
    var token = tokens[index];
    if (token === '(') {
        // Start of a new list
        var list = [];
        index++;
        while (tokens[index] !== ')') {
            var _a = parseTokens(tokens, index), expression = _a[0], nextIndex = _a[1];
            list.push(expression);
            index = nextIndex;
            if (index >= tokens.length) {
                throw new Error("Mismatched parentheses while parsing ".concat(tokens.join(' '), " at index ").concat(index));
            }
        }
        return [list, index + 1]; // Move past the closing ')'
    }
    else if (token === ')') {
        throw new Error("Unexpected closing parenthesis.");
    }
    else {
        // Atom (symbol, number, or string)
        return [parseAtom(token), index + 1];
    }
}
/**
 * Parses a single token as an atom (number, symbol, or string).
 * @param token - The token to parse.
 * @returns - The parsed atom (either a number, string, or symbol).
 */
function parseAtom(token) {
    if (token.match(/^".*"$/)) {
        // String
        return token.slice(1, -1); // Remove quotes
    }
    else if (!isNaN(Number(token))) {
        // Number
        return Number(token);
    }
    else {
        // Symbol
        return token;
    }
}
// Example usage
// const traceInput = `
// > > > >(wf-typ (EBound (EBound (Empty) (Top)) (TVar 0)) (TVar 1))
// > > > >(get-bound (EBound (EBound (Empty) (Top)) (TVar 0)) 1)
// > > > > >(tshift 0 (Top))
// < < < < < (Top)
// < < < < <(just (Top))
// > > > >(wf-typ (EBound (EBound (Empty) (Top)) (TVar 1)) (Arr (TVar 2) (TVar 2)))
// < < < < <(Top)
// `;
// const parsedTrace = parseTrace(traceInput);
// console.log(JSON.stringify(parsedTrace, null, 2));

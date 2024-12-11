type SExpression = string | number | SExpression[];

function sexpToString(sexp: SExpression): string {
    if (typeof sexp === "string") {
        return sexp;
    }
    if (typeof sexp === "number") {
        return sexp.toString();
    }

    return `(${sexp.map(sexpToString).join(" ")})`;
}
type Trace = {
    start: SExpression,
    children: Trace[],
    end: SExpression,
    depth: number
};


type TraceMarker = {
    typ: ">" | "<",
    depth: number,
    spos: number,
    epos: number,
}

type FullTraceMarker = {
    typ: ">" | "<",
    depth: number,
    spos: number,
    epos: number,
    sexp: SExpression
}

function parseTrace(input: string): Trace {
    // Split the input into lines
    input = input.trim();
    const tokens = input.split('\n');
    // As you go through the lines, find the trace markers, their depths, and their positions
    const markers: TraceMarker[] = [];
    let position = 0;

    for (let i = 0; i < tokens.length; i++) {
        const line = tokens[i];
        if (line.startsWith(">")) {
            const [depth, epos] = countDepth(line, '>');
            markers.push({ typ: ">", depth, spos: position, epos: position + epos - 1 });
        } else if (line.startsWith("<")) {
            const [depth, epos] = countDepth(line, '<');
            markers.push({ typ: "<", depth, spos: position, epos: position + epos - 1 });
        }
        position += line.length + 1; // +1 for the newline character
    }

    const fullMarkers: FullTraceMarker[] = [];

    // For each marker, parse the S-expression, which is between the marker and the next marker
    for (let i = 0; i < markers.length - 1; i++) {
        const marker = markers[i];
        const nextMarker = markers[i + 1];
        const sexp = input.slice(marker.epos, nextMarker?.spos).trim();
        if (sexp) {
            fullMarkers.push({ ...marker, sexp: parseSExpression(sexp) });
        }
    }
    // Parse the last S-expression
    const lastMarker = markers[markers.length - 1];
    const lastSexp = input.slice(lastMarker.epos).trim();
    if (lastSexp) {
        fullMarkers.push({ ...lastMarker, sexp: parseSExpression(lastSexp) });
    }
    const [trace, _] = createTraceFromMarkers(fullMarkers, 0, fullMarkers.length - 1);
    return trace;
}

function createTraceFromMarkers(markers: FullTraceMarker[], start: number, end: number): [Trace, number] {
    if (markers[start].typ !== ">") {
        throw new Error("Expected start marker to be >");
    }

    const startMarker = markers[start];
    const nextMarker = markers[start + 1];
    const children : Trace[] = [];
    if (startMarker.depth === nextMarker.depth) {
        // This is a leaf trace
        return [{ start: startMarker.sexp, children: [], end: nextMarker.sexp, depth: startMarker.depth }, start + 2];
    }



    while (start < end) {
        if (markers[start + 1].typ === "<")  {
            break;
        }
        const [child, next] = createTraceFromMarkers(markers, start + 1, end);
        start = next - 1;
        children.push(child);
    }

    return [{ start: startMarker.sexp, children, end: markers[start + 1].sexp, depth: startMarker.depth }, start + 2];
}

/**
 * Parses the tokens into Trace objects recursively.
 * @param tokens - Array of lines from the trace log.
 * @param currentDepth - The current depth of recursion based on `> > ...>` symbols.
 * @param index - The current line index being parsed.
 * @returns - A tuple containing the parsed Trace and the next line index.
 */
function parseTraceTokens(tokens: string[], currentDepth: number, index = 0): { trace: Trace, nextIndex: number } {
    const depth = countDepth(tokens[index], '>'); // Detect depth by counting `>`s
    // if (depth !== currentDepth) {
    //     throw new Error(`Unexpected depth at line ${index}: ${tokens[index]}`);
    // }

    // Parse the start S-expression after the '>' markers
    const startSexp = parseSExpressionFromTrace(tokens[index]);

    const trace: Trace = {
        start: startSexp,
        children: [],
        end: null as any,
        depth: currentDepth
    };

    index++;

    // Parse children traces recursively
    while (index < tokens.length) {
        if (tokens[index].startsWith('<')) {
            break; // End of this trace, return control to parent
        }

        const childDepth = countDepth(tokens[index], '>');
        if (childDepth > currentDepth) {
            const { trace: childTrace, nextIndex } = parseTraceTokens(tokens, childDepth, index);
            trace.children.push(childTrace);
            index = nextIndex;
        } else {
            break; // Encountered a sibling or parent's end trace
        }
    }

    // Parse the end S-expression after the '<' markers
    if (index < tokens.length && tokens[index].startsWith('<')) {
        trace.end = parseSExpressionFromTrace(tokens[index]);
        index++;
    }

    return { trace, nextIndex: index };
}

/**
 * Parse a single line from the trace and extract the S-expression.
 * Assumes the line starts with `> > ...>` or `< < ...<`.
 * @param line - The trace line.
 * @returns - The extracted S-expression.
 */
function parseSExpressionFromTrace(line: string): SExpression {
    const sExpressionPart = line.replace(/[><\s]+/g, ''); // Remove `>`, `<`, and spaces
    return parseSExpression(sExpressionPart);
}

/**
 * Counts the depth by the number of `>` or `<` symbols at the start of the line.
 * @param line - The trace line.
 * @param char - The character to count (`>` or `<`).
 * @returns - The depth of the trace.
 */
function countDepth(line: string, char: '>' | '<'): [number, number] {
    let depth = line.trim().split("").findIndex(c => c !== char && c !== ' ');
    let epos = depth;
    if (line[depth] === "[") {
        const end = line.indexOf("]");
        depth = +line.slice(depth + 1, end) + 1
        epos = end + 1;
    }
    return [depth - 1, epos + 1];
}

/**
 * A simple S-expression parser, as implemented before.
 * @param input - The input string containing the S-expression.
 * @returns - The parsed S-expression.
 */
function parseSExpression(input: string): SExpression {
    const tokens = tokenize(input);
    const [expression, _] = parseTokens(tokens);
    return expression;
}

/**
 * Tokenizes the input S-expression string.
 * @param input - The input string containing the S-expression.
 * @returns - Array of tokenized strings.
 */
function tokenize(input: string): string[] {
    const regex = /([()])|("(?:\\.|[^"\\])*")|[^\s()]+/g;  // Match parentheses, strings, or atoms
    const tokens = input.match(regex);
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
function parseTokens(tokens: string[], index = 0): [SExpression, number] {
    const token = tokens[index];

    if (token === '(') {
        // Start of a new list
        const list: SExpression[] = [];
        index++;
        while (tokens[index] !== ')') {
            const [expression, nextIndex] = parseTokens(tokens, index);
            list.push(expression);
            index = nextIndex;
            if (index >= tokens.length) {
                throw new Error(`Mismatched parentheses while parsing ${tokens.join(' ')} at index ${index}`);
            }
        }
        return [list, index + 1];  // Move past the closing ')'
    } else if (token === ')') {
        throw new Error("Unexpected closing parenthesis.");
    } else {
        // Atom (symbol, number, or string)
        return [parseAtom(token), index + 1];
    }
}

/**
 * Parses a single token as an atom (number, symbol, or string).
 * @param token - The token to parse.
 * @returns - The parsed atom (either a number, string, or symbol).
 */
function parseAtom(token: string): SExpression {
    if (token.match(/^".*"$/)) {
        // String
        return token.slice(1, -1);  // Remove quotes
    } else if (!isNaN(Number(token))) {
        // Number
        return Number(token);
    } else {
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

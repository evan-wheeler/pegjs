/* eslint-disable spaced-comment */
/* eslint-disable indent */
/* eslint-disable space-unary-ops */
/* eslint-disable template-curly-spacing */
/* eslint-disable padded-blocks */
/* eslint-disable quotes */
/* eslint-disable space-in-parens */
/* eslint-disable no-confusing-arrow */
/* eslint-disable computed-property-spacing */
/* eslint no-mixed-operators: 0, prefer-const: 0 */

"use strict";

const util = require("../../util");
const VERSION = require("../../../package.json").version;

function os_stringEscape(s) {
    return s
        .replace(/\t/g, "  ") // horizontal tab
        .replace(/"/g, '""') // quote
        .replace(/\n/g, '" + Str.LF + "') // line feed
        .replace(/\r/g, '" + Str.CR + "'); // carriage return
}

function os_regexpEscape(s) {
    return s
        .replace(/\t/g, "  ") // horizontal tab
        .replace(/"/g, '""') // quote
        .replace(/\n/g, '" + Str.LF + "') // line feed
        .replace(/\r/g, '" + Str.CR + "') // carriage return
        .replace(/@/g, "@@") // @
        .replace(/]/g, "@]") // closing bracket
        .replace(/%/g, "@%") // @
        .replace(/-/g, "@-"); // dash
}

// Generates parser OScript code.
function generateOS(ast, session, options) {
    const op = session.opcodes;

    /* Features that should be generated in the parser. */
    const features = options.features || {};
    function use(feature, use) {
        return feature in features
            ? !!features[feature]
            : use == null
            ? true
            : !!use;
    }

    /* These only indent non-empty lines to avoid trailing whitespace. */
    const lineMatchRE = /^([^\r\n]+?(?:[^\r\n]*?)?)$/gm;
    function indent2(code) {
        return code.replace(lineMatchRE, "  $1");
    }

    function quoteLiteral(lit) {
        return '"' + lit.replace(/"/g, '""') + '"';
    }

    function getSingleCharComparison(val, char) {
        const code = char.charCodeAt(0);
        const qt = char === `'` ? `"` : `'`;

        if (code >= 32 || code === 9) {
            return `${val} == ${qt}${char}${qt}`;
        }

        return `Str.Ascii( ${val} ) == ${char.charCodeAt(0)}`;
    }

    const l = i => ".fTable.c" + i; // |literals[i]| of the abstract machine
    const r = i => ".fTable.r" + i; // |classes[i]| of the abstract machine
    const e = i => ".fTable.e" + i; // |expectations[i]| of the abstract machine
    const f = i => "_fn" + i; // |actions[i]| of the abstract machine

    function generateTables() {
        function buildLiteral(literal) {
            return `"${os_stringEscape(literal)}"`;
        }

        function buildRegexp(cls) {
            return (
                'Pattern.CompileFind( "%[' +
                (cls.inverted ? "!" : "") +
                cls.value
                    .map(part =>
                        Array.isArray(part)
                            ? os_regexpEscape(part[0]) +
                              "-" +
                              os_regexpEscape(part[1])
                            : os_regexpEscape(part)
                    )
                    .join("") +
                ']"' +
                (cls.ignoreCase ? ", true)" : ")")
            );
        }

        function buildExpectation(e) {
            switch (e.type) {
                case "rule":
                    return `.OtherExpectation("${os_stringEscape(e.value)}")`;

                case "literal":
                    return (
                        '.LiteralExpectation("' +
                        os_stringEscape(e.value) +
                        '", ' +
                        e.ignoreCase +
                        ")"
                    );

                case "class": {
                    const parts = e.value.map(part =>
                        Array.isArray(part)
                            ? `{"${os_stringEscape(
                                  part[0]
                              )}", "${os_stringEscape(part[1])}"}`
                            : `"${os_stringEscape(part)}"`
                    );

                    return (
                        ".ClassExpectation({" +
                        parts.join(", ") +
                        "}, " +
                        e.inverted +
                        ", " +
                        e.ignoreCase +
                        ")"
                    );
                }

                case "any":
                    return ".AnyExpectation()";

                // istanbul ignore next
                default:
                    session.fatal(
                        `Unknown expectation type (${JSON.stringify(e)})`
                    );
            }
        }

        function buildFunc(f, name) {
            return [
                `function ${name}(${f.params.join(", ")})`,
                indent2(`${f.body}`),
                "end",
                ""
            ].join("\n");
        }

        return {
            values: ast.literals
                .map((c, i) => l(i) + " = " + buildLiteral(c))
                .concat(
                    "",
                    ast.classes.map((c, i) => r(i) + " = " + buildRegexp(c))
                )
                .concat(
                    "",
                    ast.expectations.map(
                        (c, i) => e(i) + " = " + buildExpectation(c)
                    )
                )
                .join("\n"),
            functions: ast.functions
                .map((c, i) => buildFunc(c, f(i)))
                .join("\n")
        };
    }

    // eslint-disable-next-line no-unused-vars
    function generateRuleHeader(ruleNameCode, ruleIndexCode) {
        return "";
    }

    // eslint-disable-next-line no-unused-vars
    function generateRuleFooter(ruleNameCode, resultCode) {
        const parts = [];

        parts.push(["", "return " + resultCode].join("\n"));

        return parts.join("\n");
    }

    function generateRuleFunction(rule) {
        const parts = [];
        const stackVars = [];

        function s(i) {
            // istanbul ignore next
            if (i < 0)
                session.fatal(
                    "Rule '" +
                        rule.name +
                        "': Var stack underflow: attempt to use var at index " +
                        i
                );

            return "s" + i;
        } // |stack[i]| of the abstract machine

        const stack = {
            sp: -1,
            maxSp: -1,

            push(exprCode) {
                const code = s(++this.sp) + " = " + exprCode;
                if (this.sp > this.maxSp) this.maxSp = this.sp;
                return code;
            },

            pop(n) {
                if (typeof n === "undefined") return s(this.sp--);

                const values = Array(n);

                for (let i = 0; i < n; i++) {
                    values[i] = s(this.sp - n + 1 + i);
                }

                this.sp -= n;
                return values;
            },

            top() {
                return s(this.sp);
            },

            index(i) {
                return s(this.sp - i);
            }
        };

        function compile(bc) {
            let ip = 0;
            const end = bc.length;
            const parts = [];
            let value;

            function compileCondition(cond, argCount) {
                const pos = ip;
                const baseLength = argCount + 3;
                const thenLength = bc[ip + baseLength - 2];
                const elseLength = bc[ip + baseLength - 1];
                const baseSp = stack.sp;
                let thenCode, elseCode, thenSp, elseSp;

                ip += baseLength;
                thenCode = compile(bc.slice(ip, ip + thenLength));
                thenSp = stack.sp;
                ip += thenLength;

                if (elseLength > 0) {
                    stack.sp = baseSp;
                    elseCode = compile(bc.slice(ip, ip + elseLength));
                    elseSp = stack.sp;
                    ip += elseLength;

                    // istanbul ignore if
                    if (thenSp !== elseSp) {
                        session.fatal(
                            "Rule '" +
                                rule.name +
                                "', position " +
                                pos +
                                ": " +
                                "Branches of a condition can't move the stack pointer differently " +
                                "(before: " +
                                baseSp +
                                ", after then: " +
                                thenSp +
                                ", after else: " +
                                elseSp +
                                ")."
                        );
                    }
                }

                parts.push("if " + cond);
                parts.push(indent2(thenCode));
                if (elseLength > 0) {
                    parts.push("else");
                    parts.push(indent2(elseCode));
                }
                parts.push("end");
            }

            function compileLoop(cond) {
                const pos = ip;
                const baseLength = 2;
                const bodyLength = bc[ip + baseLength - 1];
                const baseSp = stack.sp;
                let bodyCode, bodySp;

                ip += baseLength;
                bodyCode = compile(bc.slice(ip, ip + bodyLength));
                bodySp = stack.sp;
                ip += bodyLength;

                // istanbul ignore if
                if (bodySp !== baseSp) {
                    session.fatal(
                        "Rule '" +
                            rule.name +
                            "', position " +
                            pos +
                            ": " +
                            "Body of a loop can't move the stack pointer " +
                            "(before: " +
                            baseSp +
                            ", after: " +
                            bodySp +
                            ")."
                    );
                }

                parts.push("while (" + cond + ") ");
                parts.push(indent2(bodyCode));
                parts.push("end");
            }

            function compileCall() {
                const baseLength = 4;
                const paramsLength = bc[ip + baseLength - 1];

                const value =
                    f(bc[ip + 1]) +
                    "(" +
                    bc
                        .slice(ip + baseLength, ip + baseLength + paramsLength)
                        .map(p => stack.index(p))
                        .join(", ") +
                    ")";

                stack.pop(bc[ip + 2]);
                parts.push(stack.push(value));
                ip += baseLength + paramsLength;
            }

            while (ip < end) {
                switch (bc[ip]) {
                    case op.PUSH_EMPTY_STRING: // PUSH_EMPTY_STRING
                        parts.push(stack.push("''"));
                        ip++;
                        break;

                    case op.PUSH_CURR_POS: // PUSH_CURR_POS
                        parts.push(stack.push(".fCurPos"));
                        ip++;
                        break;

                    case op.PUSH_UNDEFINED: // PUSH_UNDEFINED
                        parts.push(stack.push("undefined"));
                        ip++;
                        break;

                    case op.PUSH_NULL: // PUSH_NULL
                        parts.push(stack.push("undefined"));
                        ip++;
                        break;

                    case op.PUSH_FAILED: // PUSH_FAILED
                        parts.push(stack.push(-1234567890 /*".fFAILED"*/));
                        ip++;
                        break;

                    case op.PUSH_EMPTY_ARRAY: // PUSH_EMPTY_ARRAY
                        parts.push(stack.push("{}"));
                        ip++;
                        break;

                    case op.POP: // POP
                        stack.pop();
                        ip++;
                        break;

                    case op.POP_CURR_POS: // POP_CURR_POS
                        parts.push(".fCurPos = " + stack.pop());
                        ip++;
                        break;

                    case op.POP_N: // POP_N n
                        stack.pop(bc[ip + 1]);
                        ip += 2;
                        break;

                    case op.NIP: // NIP
                        value = stack.pop();
                        stack.pop();
                        parts.push(stack.push(value));
                        ip++;
                        break;

                    case op.APPEND: // APPEND
                        value = stack.pop();
                        parts.push(
                            stack.top() +
                                " = { @" +
                                stack.top() +
                                ", " +
                                value +
                                " }"
                        );
                        ip++;
                        break;

                    case op.WRAP: // WRAP n
                        parts.push(
                            stack.push(
                                "{" + stack.pop(bc[ip + 1]).join(", ") + "}"
                            )
                        );
                        ip += 2;
                        break;

                    case op.TEXT: // TEXT
                        parts.push(
                            stack.push(
                                ".InputSubstring(" +
                                    stack.pop() +
                                    ", .fCurPos )"
                            )
                        );
                        ip++;
                        break;

                    case op.PLUCK: // PLUCK n, k, p1, ..., pK
                        const baseLength = 3;
                        const paramsLength = bc[ip + baseLength - 1];
                        const n = baseLength + paramsLength;
                        value = bc.slice(ip + baseLength, ip + n);
                        value =
                            paramsLength === 1
                                ? stack.index(value[0])
                                : `[ ${value
                                      .map(p => stack.index(p))
                                      .join(", ")} ]`;
                        stack.pop(bc[ip + 1]);
                        parts.push(stack.push(value));
                        ip += n;
                        break;

                    case op.IF: // IF t, f
                        compileCondition(stack.top(), 0);
                        break;

                    case op.IF_ERROR: // IF_ERROR t, f
                        compileCondition(stack.top() + " == -1234567890", 0);
                        break;

                    case op.IF_NOT_ERROR: // IF_NOT_ERROR t, f
                        compileCondition(stack.top() + " != -1234567890", 0);
                        break;

                    case op.WHILE_NOT_ERROR: // WHILE_NOT_ERROR b
                        compileLoop(stack.top() + " != -1234567890", 0);
                        break;

                    case op.MATCH_ANY: // MATCH_ANY a, f, ...
                        compileCondition("Length( .fInput ) > .fCurPos", 0);
                        break;

                    case op.MATCH_STRING: // MATCH_STRING s, a, f, ...
                        compileCondition(
                            ast.literals[bc[ip + 1]].length > 1
                                ? ".fInput[.fCurPos + 1:.fCurPos + " +
                                      ast.literals[bc[ip + 1]].length +
                                      "] == " +
                                      quoteLiteral(ast.literals[bc[ip + 1]])
                                : getSingleCharComparison(
                                      ".fInput[1+.fCurPos]",
                                      ast.literals[bc[ip + 1]].charAt(0)
                                  ),
                            1
                        );
                        break;

                    case op.MATCH_STRING_IC: // MATCH_STRING_IC s, a, f, ...
                        compileCondition(
                            "Str.Lower( .fInput[.fCurPos + 1:.fCurPos + " +
                                ast.literals[bc[ip + 1]].length +
                                "] ) == " +
                                l(bc[ip + 1]),
                            1
                        );
                        break;

                    case op.MATCH_CLASS: // MATCH_CLASS c, a, f, ...
                        compileCondition(
                            " IsDefined( Pattern.Find(.fInput[1+.fCurPos]," +
                                r(bc[ip + 1]) +
                                "))",
                            1
                        ); // InputCharAt(.fCurPos)
                        break;

                    case op.ACCEPT_N: // ACCEPT_N n
                        parts.push(
                            stack.push(
                                bc[ip + 1] > 1
                                    ? ".fInput[.fCurPos + 1:.fCurPos +" +
                                          bc[ip + 1] +
                                          "]"
                                    : ".fInput[ 1 + .fCurPos ]" // .InputCharAt( .fCurPos )
                            )
                        );
                        parts.push(
                            bc[ip + 1] > 1
                                ? ".fCurPos += " + bc[ip + 1]
                                : ".fCurPos += 1"
                        );
                        ip += 2;
                        break;

                    case op.ACCEPT_STRING: // ACCEPT_STRING s
                        parts.push(stack.push(l(bc[ip + 1])));
                        parts.push(
                            ast.literals[bc[ip + 1]].length > 1
                                ? ".fCurPos += " +
                                      ast.literals[bc[ip + 1]].length +
                                      ""
                                : ".fCurPos += 1"
                        );
                        ip += 2;
                        break;

                    case op.EXPECT: // EXPECT e
                        parts.push(".RuleExpects(" + e(bc[ip + 1]) + ")");
                        ip += 2;
                        break;

                    case op.LOAD_SAVED_POS: // LOAD_SAVED_POS p
                        parts.push(
                            ".fSavedPos = " + stack.index(bc[ip + 1]) + ""
                        );
                        ip += 2;
                        break;

                    case op.UPDATE_SAVED_POS: // UPDATE_SAVED_POS
                        parts.push(".fSavedPos = .fCurPos");
                        ip++;
                        break;

                    case op.CALL: // CALL f, n, pc, p1, p2, ..., pN
                        compileCall();
                        break;

                    case op.RULE: // RULE r
                        parts.push(
                            stack.push(
                                "Parse" + ast.rules[bc[ip + 1]].name + "()"
                            )
                        );
                        ip += 2;
                        break;

                    case op.SILENT_FAILS_ON: // SILENT_FAILS_ON
                        parts.push(".fSilentFails += 1");
                        ip++;
                        break;

                    case op.SILENT_FAILS_OFF: // SILENT_FAILS_OFF
                        parts.push(".fSilentFails -= 1");
                        ip++;
                        break;

                    case op.EXPECT_NS_BEGIN: // EXPECT_NS_BEGIN
                        parts.push(".ParseBegin()");
                        ip++;
                        break;

                    case op.EXPECT_NS_END: // EXPECT_NS_END invert
                        parts.push(".ParseEnd(" + (bc[ip + 1] !== 0) + ")");
                        ip += 2;
                        break;

                    // istanbul ignore next
                    default:
                        session.fatal(
                            "Rule '" +
                                rule.name +
                                "', position " +
                                ip +
                                ": " +
                                "Invalid opcode " +
                                bc[ip] +
                                "."
                        );
                }
            }

            return parts.join("\n");
        }

        const code = compile(rule.bytecode);

        parts.push("function Parse" + rule.name + "()");

        for (let i = 0; i <= stack.maxSp; i++) {
            stackVars[i] = s(i);
        }

        parts.push("  Dynamic " + stackVars.join(", "));

        parts.push(
            indent2(
                generateRuleHeader(
                    '"' + os_stringEscape(rule.name) + '"',
                    ast.indexOfRule(rule.name)
                )
            )
        );
        parts.push(indent2(code));
        parts.push(
            indent2(
                generateRuleFooter('"' + os_stringEscape(rule.name) + '"', s(0))
            )
        );

        parts.push("end");

        return parts.join("\n");
    }

    function generateToplevel() {
        const parts = [];

        const tables = generateTables();

        const startRuleFunction = "Parse" + options.allowedStartRules[0];

        parts.push("function Dynamic ParseSubclass()");
        parts.push("");
        parts.push("  if IsUndefined( .fTable )");
        parts.push("    .fTable = Assoc.CreateAssoc()");
        parts.push(indent2(indent2(tables.values)));
        parts.push("  end");
        parts.push("");
        parts.push("  return " + startRuleFunction + "()");
        parts.push("end");

        if (ast.initializer) {
            parts.push(ast.initializer.code);
            parts.push("");
        }

        ast.rules.forEach(rule => {
            parts.push(generateRuleFunction(rule));
            parts.push("");
        });

        parts.push(tables.functions);

        if (use("offset")) {
            parts.push(
                [
                    "",
                    "function Integer offset()",
                    "  return .fSavedPos",
                    "end"
                ].join("\n")
            );
        }

        if (use("range")) {
            parts.push(
                [
                    "",
                    "function List range()",
                    "  return {.fSavedPos, .fCurPos}",
                    "end"
                ].join("\n")
            );
        }

        if (use("location")) {
            parts.push(
                [
                    "",
                    "function location()",
                    "  return .ComputeLocation(.fSavedPos, .fCurPos)",
                    "end"
                ].join("\n")
            );
        }

        if (use("text")) {
            parts.push(
                ["", "function text()", "  return .text()", "end"].join("\n")
            );
        }

        return parts.join("\n");
    }

    function generateWrapper(toplevelCode) {
        return toplevelCode;
    }

    ast.code = generateWrapper(generateToplevel());
}

module.exports = generateOS;

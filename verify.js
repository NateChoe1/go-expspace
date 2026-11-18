/* helper functions for generating boolean formulas */
function X(idx) {
    return {
        type: "leaf",
        ref: "X",
        idx: idx,
    }
}

function Y(idx) {
    return {
        type: "leaf",
        ref: "Y",
        idx: idx,
    }
}

function KO(idx) {
    return {
        type: "leaf",
        ref: "koValues",
        idx: idx,
    }
}

function daisyChain(operation, arr) {
    ret = undefined;
    for (const elem of arr) {
        if (ret === undefined) {
            ret = elem;
            continue;
        }
        ret = operation(ret, elem);
    }
    return ret;
}

function AND(a, b) {
    if (a === undefined) {
        return b;
    }
    if (b === undefined) {
        return daisyChain(AND, a);
    }
    return {
        type: "and",
        a: a,
        b: b,
    }
}

function OR(a, b) {
    if (a === undefined) {
        return b;
    }
    if (b === undefined) {
        return daisyChain(OR, a);
    }
    return {
        type: "or",
        a: a,
        b: b,
    }
}

function NOT(f) {
    return {
        type: "not",
        child: f,
    }
}

/* moves all NOT gates to the leaf nodes */
function normalize(formula, invert = false) {
    switch (formula.type) {
        case "leaf":
            if (invert) {
                return NOT(formula);
            }
            return formula;
        case "and":
            if (invert) {
                return OR(normalize(formula.a, true), normalize(formula.b, true));
            }
            return AND(normalize(formula.a, false), normalize(formula.b, false));
        case "or":
            if (invert) {
                return AND(normalize(formula.a, true), normalize(formula.b, true));
            }
            return OR(normalize(formula.a, false), normalize(formula.b, false));
        case "not":
            if (invert) {
                return normalize(formula.child, false);
            }
            return normalize(formula.child, true);
    }
}

function evaluate(formula, assignments) {
    switch (formula.type) {
        case "leaf":
            return assignments[formula.ref][formula.idx];
        case "and":
            return evaluate(formula.a, assignments) && evaluate(formula.b, assignments);
        case "or":
            return evaluate(formula.a, assignments) || evaluate(formula.b, assignments);
        case "not":
            return !evaluate(formula.child, assignments);
    }
}

function stringToBoolArray(str) {
    ret = [];
    for (var i = 0; i < str.length; ++i) {
        if (str[i] == "0") {
            ret.push(false);
        } else if (str[i] == "1") {
            ret.push(true);
        }
    }
    return ret;
}

function countNodes(formula) {
    switch (formula.type) {
        case "leaf":
            return 1;
        case "and":
            return 1 + countNodes(formula.a) + countNodes(formula.b);
        case "or":
            return 1 + countNodes(formula.a) + countNodes(formula.b);
        case "not":
            return 1 + countNodes(formula.child);
        default:
            console.log(formula);
            throw "error";
    }
}

function compileG3(g3Assignments, formulaX, formulaY) {
    /* the values in the latch. initially it's black's turn. */
    var kos = [false, false, true];
    var gadgetMap = {
        latch: [0, 1, 2], /* A, B, C for the latch */
        blackVars: [],
        whiteVars: [],
    };

    var CLOCK_X1 = 0;
    var CLOCK_X2 = 1;
    var CLOCK_Y1 = 0;
    var CLOCK_Y2 = 1;
    var BLACK_X = [];
    var BLACK_Y = [];
    var WHITE_Y = [];
    var WHITE_X = [];

    /* add CLOCK vars */
    for (var i = 0; i < 4; ++i) {
        var varKos = []
        for (var j = 0; j < 6; ++j) {
            varKos.push(kos.length + j);
        }
        kos.push(false, false, false, true, true, true);
        if (i < 2) {
            gadgetMap.blackVars.push(varKos);
        } else {
            gadgetMap.whiteVars.push(varKos);
        }
    }

    function initializeVariables(reference, player, record) {
        for (const v of reference) {
            var varKos = [];
            for (var i = 0; i < 6; ++i) {
                varKos.push(kos.length + i);
            }
            if (v) {
                kos.push(false, false, false, true, true, true);
            } else {
                kos.push(true, true, true, false, false, false);
            }
            record.push(player.length);
            player.push(varKos);
        }
    }
    initializeVariables(g3Assignments.X, gadgetMap.blackVars, BLACK_X);
    initializeVariables(g3Assignments.Y, gadgetMap.blackVars, BLACK_Y);
    initializeVariables(g3Assignments.X, gadgetMap.whiteVars, WHITE_X);
    initializeVariables(g3Assignments.Y, gadgetMap.whiteVars, WHITE_Y);

    var BLACK_SENTE = KO(2);
    var WHITE_SENTE = AND(KO(0), KO(1));

    var BLACK_TRANSITIONING = undefined;
    var WHITE_TRANSITIONING = undefined;
    var BLACK_SLOW = OR(KO(0), KO(1));
    var WHITE_SLOW = WHITE_SENTE;
    for (const blackVar of gadgetMap.blackVars) {
        /* true if black has a forcing move on a black variable */
        var BLACK_TRANS_BLACK_local = OR([
            AND([KO(blackVar[0]), KO(blackVar[3]), KO(blackVar[4]), KO(blackVar[5])]),
            AND([KO(blackVar[0]), KO(blackVar[1]), KO(blackVar[4]), KO(blackVar[5])]),
            AND([KO(blackVar[0]), KO(blackVar[1]), KO(blackVar[2]), KO(blackVar[5])]),
        ]);

        /* false if white has a forcing move on a black variable (i.e. true if
         * white doesn't have a forcing move) */
        var WHITE_TRANS_BLACK_local = AND([
            OR([KO(blackVar[1]), KO(blackVar[2]), KO(blackVar[3])]),
            OR([KO(blackVar[2]), KO(blackVar[3]), KO(blackVar[4])]),
        ]);

        BLACK_TRANSITIONING = OR(BLACK_TRANSITIONING, BLACK_TRANS_BLACK_local);
        WHITE_TRANSITIONING = AND(WHITE_TRANSITIONING, WHITE_TRANS_BLACK_local);

        BLACK_SLOW = OR(BLACK_SLOW, AND(
            OR([KO(blackVar[0]), KO(blackVar[1]), KO(blackVar[2])]),
            OR([KO(blackVar[3]), KO(blackVar[4]), KO(blackVar[5])]),
        ));
    }

    for (const whiteVar of gadgetMap.whiteVars) {
        /* true if black has a forcing move on a white variable */
        var BLACK_TRANS_WHITE_local = OR([
            AND([KO(whiteVar[1]), KO(whiteVar[2]), KO(whiteVar[3])]),
            AND([KO(whiteVar[2]), KO(whiteVar[3]), KO(whiteVar[4])]),
        ]);

        /* false if white has a forcing move on a white variable (i.e. true if
         * white doesn't have a forcing move) */
        var WHITE_TRANS_WHITE_local = AND([
            OR([KO(whiteVar[0]), KO(whiteVar[3]), KO(whiteVar[4]), KO(whiteVar[5])]),
            OR([KO(whiteVar[0]), KO(whiteVar[1]), KO(whiteVar[4]), KO(whiteVar[5])]),
            OR([KO(whiteVar[0]), KO(whiteVar[1]), KO(whiteVar[2]), KO(whiteVar[5])]),
        ]);

        BLACK_TRANSITIONING = OR(BLACK_TRANSITIONING, BLACK_TRANS_WHITE_local);
        WHITE_TRANSITIONING = AND(WHITE_TRANSITIONING, WHITE_TRANS_WHITE_local);

        WHITE_SLOW = AND(WHITE_SLOW, OR(
            AND([KO(whiteVar[0]), KO(whiteVar[1]), KO(whiteVar[2])]),
            AND([KO(whiteVar[3]), KO(whiteVar[4]), KO(whiteVar[5])]),
        ));
    }

    BLACK_LATCHING = OR(AND(KO(0), KO(2)), AND(KO(1), KO(2)));
    WHITE_LATCHING = AND(OR(KO(0), KO(2)), OR(KO(1), KO(2)));

    function varTrue(idx) {
        return AND(KO(idx[3]), KO(idx[4]), KO(idx[5]));
    }
    function varFalse(idx) {
        return AND(KO(idx[0]), KO(idx[1]), KO(idx[2]));
    }
    function varsEqual(a, b) {
        return OR(
            AND([KO(a[0]), KO(a[1]), KO(a[2]), KO(b[0]), KO(b[1]), KO(b[2])]),
            AND([KO(a[3]), KO(a[4]), KO(a[5]), KO(b[3]), KO(b[4]), KO(b[5])]),
        );
    }
    function varsDiffer(a, b) {
        return OR(
            AND([KO(a[0]), KO(a[1]), KO(a[2]), KO(b[3]), KO(b[4]), KO(b[5])]),
            AND([KO(b[0]), KO(b[1]), KO(b[2]), KO(a[3]), KO(a[4]), KO(a[5])]),
        );
    }

    var X_MATCHES = undefined;
    var X_NO_MATCH = undefined;
    for (var i = 0; i < g3Assignments.X.length; ++i) {
        X_MATCHES = AND(X_MATCHES, varsEqual(
            gadgetMap.blackVars[BLACK_X[i]],
            gadgetMap.whiteVars[WHITE_X[i]],
        ));
        X_NO_MATCH = OR(X_NO_MATCH, varsDiffer(
            gadgetMap.blackVars[BLACK_X[i]],
            gadgetMap.whiteVars[WHITE_X[i]],
        ));
    }

    var Y_MATCHES = undefined;
    var Y_NO_MATCH = undefined;
    for (var i = 0; i < g3Assignments.Y.length; ++i) {
        Y_MATCHES = AND(Y_MATCHES, varsEqual(
            gadgetMap.blackVars[BLACK_Y[i]],
            gadgetMap.whiteVars[WHITE_Y[i]],
        ));
        Y_NO_MATCH = OR(Y_NO_MATCH, varsDiffer(
            gadgetMap.blackVars[BLACK_Y[i]],
            gadgetMap.whiteVars[WHITE_Y[i]],
        ));
    }

    function convertFormula(formula) {
        switch (formula.type) {
            case "leaf":
                if (formula.ref == "X") {
                    return varTrue(gadgetMap.blackVars[BLACK_X[formula.idx]]);
                } else {
                    return varTrue(gadgetMap.whiteVars[BLACK_Y[formula.idx]]);
                }
            case "and":
                return AND(convertFormula(formula.a), convertFormula(formula.b));
            case "or":
                return OR(convertFormula(formula.a), convertFormula(formula.b));
            case "not":
                if (formula.child.type != "leaf") {
                    throw new Error("Non normalized formula");
                }
                if (formula.child.ref == "X") {
                    return varFalse(gadgetMap.blackVars[BLACK_X[formula.child.idx]]);
                } else {
                    return varFalse(gadgetMap.whiteVars[BLACK_Y[formula.child.idx]]);
                }
        }
    }
    var BLACK_SAT = convertFormula(normalize(formulaX));
    var WHITE_UNSAT = convertFormula(normalize(formulaY, true));

    var WHITE_FAIL = AND([
        BLACK_SENTE,
        varsEqual(gadgetMap.blackVars[CLOCK_X1], gadgetMap.whiteVars[CLOCK_Y1]),
        OR([
            X_NO_MATCH,
            varsDiffer(gadgetMap.whiteVars[CLOCK_Y1], gadgetMap.whiteVars[CLOCK_Y2]),
            WHITE_UNSAT,
            AND(varFalse(gadgetMap.blackVars[CLOCK_X1]), Y_MATCHES),
            AND(varTrue(gadgetMap.blackVars[CLOCK_X1]), Y_NO_MATCH),
        ]),
    ]);

    var BLACK_FAIL = OR([
        BLACK_SENTE,
        varsEqual(gadgetMap.blackVars[CLOCK_X1], gadgetMap.whiteVars[CLOCK_Y1]),
        AND([
            Y_MATCHES,
            varsEqual(gadgetMap.blackVars[CLOCK_X1], gadgetMap.blackVars[CLOCK_X2]),
            BLACK_SAT,
            OR(varFalse(gadgetMap.whiteVars[CLOCK_Y1]), X_NO_MATCH),
            OR(varTrue(gadgetMap.whiteVars[CLOCK_Y1]), X_MATCHES),
        ]),
    ]);

    /* white is transitioning her variable */
    function T(vw) {
        idx = gadgetMap.whiteVars[vw];
        return AND(KO(idx[2]), KO(idx[3]));
    }

    /* false if black is transitioning his variable */
    function T_(vb) {
        idx = gadgetMap.blackVars[vb];
        return OR(KO(idx[2]), KO(idx[3]));
    }

    var WHITE_BAD_TRANSITIONING = AND(T(CLOCK_Y1),
            OR(Y_NO_MATCH, varsEqual(
                gadgetMap.whiteVars[CLOCK_Y2],
                gadgetMap.blackVars[CLOCK_X1],
            )));
    for (var i = 0; i < g3Assignments.Y.length; ++i) {
        var localBad = OR(
            varsDiffer(gadgetMap.blackVars[CLOCK_X1], gadgetMap.whiteVars[CLOCK_Y1]),
            varsEqual(gadgetMap.blackVars[CLOCK_X2], gadgetMap.whiteVars[CLOCK_Y2]),
        );
        for (var j = 0; j < g3Assignments.Y.length; ++j) {
            if (i == j) {
                continue;
            }
            localBad = OR(
                localBad,
                varsDiffer(gadgetMap.whiteVars[WHITE_Y[j]], gadgetMap.blackVars[BLACK_Y[j]]),
            );
        }
        WHITE_BAD_TRANSITIONING = OR(WHITE_BAD_TRANSITIONING, AND(T(WHITE_Y[i]), localBad));
    }
    var BAD_CLOCKY2 = OR([
        varsDiffer(gadgetMap.blackVars[CLOCK_X1], gadgetMap.whiteVars[CLOCK_Y1]),
        AND(varTrue(gadgetMap.blackVars[CLOCK_X1]), OR(
            Y_NO_MATCH,
            X_NO_MATCH,
        )),
        AND(varFalse(gadgetMap.blackVars[CLOCK_X1]), OR(
            Y_MATCHES,
            X_MATCHES,
        )),
    ]);
    WHITE_BAD_TRANSITIONING = OR(WHITE_BAD_TRANSITIONING, AND(T(CLOCK_Y2), BAD_CLOCKY2));
    for (var i = 0; i < g3Assignments.X.length; ++i) {
        var localBad = OR(
            varsDiffer(gadgetMap.whiteVars[CLOCK_Y1], gadgetMap.blackVars[CLOCK_X1]),
            varsDiffer(gadgetMap.whiteVars[CLOCK_Y2], gadgetMap.blackVars[CLOCK_X1]),
        );
        for (var j = 0; j < g3Assignments.X.length; ++j) {
            if (i == j) {
                continue;
            }
            localBad = OR(localBad, varsDiffer(
                gadgetMap.whiteVars[WHITE_X[j]],
                gadgetMap.blackVars[BLACK_X[j]],
            ));
        }
        WHITE_BAD_TRANSITIONING = OR(WHITE_BAD_TRANSITIONING, AND(
            T(WHITE_X[i]), localBad));
    }

    var BLACK_BAD_TRANSITIONING = OR(T_(CLOCK_X1),
        AND(X_MATCHES, varsEqual(
            gadgetMap.blackVars[CLOCK_X2],
            gadgetMap.whiteVars[CLOCK_Y1]
        )));
    for (var i = 0; i < g3Assignments.X.length; ++i) {
        var localFine = AND(
            varsDiffer(gadgetMap.whiteVars[CLOCK_Y1], gadgetMap.blackVars[CLOCK_X1]),
            varsEqual(gadgetMap.whiteVars[CLOCK_Y2], gadgetMap.blackVars[CLOCK_X1]),
        );
        for (var j = 0; j < g3Assignments.X.length; ++j) {
            if (i == j) {
                continue;
            }
            localFine = AND(localFine, varsEqual(
                gadgetMap.blackVars[BLACK_X[j]],
                gadgetMap.whiteVars[WHITE_X[j]],
            ));
        }
        BLACK_BAD_TRANSITIONING = AND(BLACK_BAD_TRANSITIONING, OR(T_(BLACK_X[i]), localFine));
    }
    var GOOD_CLOCKX2 = AND([
        varsEqual(gadgetMap.blackVars[CLOCK_X1], gadgetMap.whiteVars[CLOCK_Y1]),
        OR(varFalse(gadgetMap.whiteVars[CLOCK_Y1]), AND(
            Y_MATCHES,
            X_NO_MATCH,
        )),
        OR(varTrue(gadgetMap.whiteVars[CLOCK_Y1]), AND(
            Y_NO_MATCH,
            X_MATCHES,
        )),
    ]);
    BLACK_BAD_TRANSITIONING = AND(BLACK_BAD_TRANSITIONING, OR(T_(CLOCK_X2), GOOD_CLOCKX2));
    for (var i = 0; i < g3Assignments.Y.length; ++i) {
        var localFine = AND(
            varsDiffer(gadgetMap.blackVars[CLOCK_X1], gadgetMap.whiteVars[CLOCK_Y1]),
            varsDiffer(gadgetMap.blackVars[CLOCK_X2], gadgetMap.whiteVars[CLOCK_Y1]),
        );
        for (var j = 0; j < g3Assignments.Y.length; ++j) {
            if (i == j) {
                continue;
            }
            localFine = AND(localFine, varsEqual(
                gadgetMap.blackVars[BLACK_Y[j]],
                gadgetMap.whiteVars[WHITE_Y[j]],
            ));
        }
        BLACK_BAD_TRANSITIONING = AND(BLACK_BAD_TRANSITIONING, OR(
            T_(BLACK_Y[i]), localFine));
    }

    var F1 = OR([
        BLACK_TRANSITIONING,
        BLACK_LATCHING,
        WHITE_SLOW,
        WHITE_FAIL,
        WHITE_BAD_TRANSITIONING,
    ]);

    var F2 = AND([
        WHITE_TRANSITIONING,
        WHITE_LATCHING,
        BLACK_SLOW,
        BLACK_FAIL,
        BLACK_BAD_TRANSITIONING,
    ]);

    return {
        koValues: kos,
        f1: F1,
        f2: F2,
        gadgetMap: gadgetMap,
        clockX1: CLOCK_X1,
        clockX2: CLOCK_X2,
        clockY1: CLOCK_Y1,
        clockY2: CLOCK_Y2,
        blackX: BLACK_X,
        blackY: BLACK_Y,
        whiteX: WHITE_X,
        whiteY: WHITE_Y,
    };
}

/* sente is true on black's turn, false on white's turn */
function simulate(gameState, blackStrategy, whiteStrategy, sente, depth, logElem) {
    gameState.history.push(Array.from(gameState.koValues));

    var moves;
    if (sente) {
        moves = blackStrategy(gameState);
    } else {
        moves = whiteStrategy(gameState);
    }

    var ret = {};
    var winner = !sente;

moveLoop:
    for (const move of moves) {
        /* this move is illegal because we're trying to set a ko we already own */
        if (gameState.koValues[move] == sente) {
            continue;
        }

        gameState.koValues[move] = sente;

        /* this move is illegal by superko */
        for (const previousState of gameState.history) {
            var illegal = true;
            for (var i = 0; i < gameState.koValues.length; ++i) {
                if (previousState[i] != gameState.koValues[i]) {
                    illegal = false;
                    break;
                }
            }
            if (illegal) {
                gameState.koValues[move] = !sente;
                continue moveLoop;
            }
        }

        var f1Eval = evaluate(gameState.f1, gameState);
        var f2Eval = evaluate(gameState.f2, gameState);

        // we're playing as black and white has at least one formula set to
        // false, or we're playing as white and black has at least one formula
        if ((sente && !(f1Eval && f2Eval)) ||
            (!sente && (f1Eval || f2Eval))) {
            gameState.koValues[move] = !sente;
            continue;
        }

        logElem.innerText += '  ';
        for (var i = 0; i < depth; ++i) {
            logElem.innerText += '  ';
        }
        logElem.innerText += `${sente ? "black" : "white"}: ${move}\n`;

        var child = simulate(gameState, blackStrategy, whiteStrategy, !sente, depth+1, logElem);
        if (child.winner == sente) {
            winner = sente;
        }
        ret[move] = child;

        gameState.koValues[move] = !sente;
    }
    gameState.history.pop();

    ret.winner = winner;
    return ret;
}

function runGame() {
    var gameDescriptionRaw = document.getElementById("description").value;
    var gameDescriptionLines = gameDescriptionRaw.split('\n');

    var logElement = document.getElementById("log");
    logElement.innerText = "";

    var g3Assignments = {
        X: stringToBoolArray(gameDescriptionLines[0]),
        Y: stringToBoolArray(gameDescriptionLines[1]),
    };

    var formulaX = eval(gameDescriptionLines[2]);
    var formulaY = eval(gameDescriptionLines[3]);

    var compiled = compileG3(g3Assignments, formulaX, formulaY);
    logElement.innerText += "Finished compiling G3 to ko game\n";
    logElement.innerText += `F1 node count: ${countNodes(compiled.f1)}\n`;
    logElement.innerText += `F2 node count: ${countNodes(compiled.f2)}\n`;

    const blackStrategy = eval(`(${document.getElementById("blackStrategy").value})`);
    const whiteStrategy = eval(`(${document.getElementById("whiteStrategy").value})`);

    compiled.history = [];
    gameTree = simulate(compiled, blackStrategy, whiteStrategy, true, 0, logElement);
    logElement.innerText += `Simulation finished; winner: ${gameTree.winner ? "black" : "white"}\n`;
}

window.addEventListener("load", function() {
    document.getElementById("run").addEventListener("click", runGame);
});

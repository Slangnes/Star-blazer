/**
 * StarBlazer — Hexagonal Strategy Game
 * Core game logic: hex grid, royal/soldier/corvette/hopper/general tokens, placement rules,
 * one-field connectivity (stacked grid compatible), dynamic board rendering, panning/zooming, and drawer UI.
 */
(function () {
    'use strict';

    // ═══════════════════════════════════════════════════════════
    // Configuration
    // ═══════════════════════════════════════════════════════════
    const CONFIG = {
        GRID_RADIUS: 5,
        HEX_SIZE: 48,
        CHIP_SCALE: 0.75,
        SVG_NS: 'http://www.w3.org/2000/svg',
    };

    // ═══════════════════════════════════════════════════════════
    // Game State
    // ═══════════════════════════════════════════════════════════
    const state = {
        board: new Map(),                   // "q,r" → Array of [{ player: 1|2, type: 'chip'|'royal'|... }] (stacked)
        currentPlayer: 1,
        progression: {
            wins: 0,
            moves: 0,
            level: 1
        },
        totalPieces: 0,                     // pieces currently on board (total stack size sum)
        moveHistory: [],                    // for undo
        playerColors: { 1: '#1a1a1a', 2: '#d4b896' },
        playerNames: { 1: 'Player 1', 2: 'Player 2' },
        playerAvatars: { 1: null, 2: null },
        lobbyId: null,
        playerCounts: { 1: 0, 2: 0 },

        // Royal
        royals: { 1: null, 2: null },       // { q, r } or null
        royalPlaced: { 1: false, 2: false },
        playerTurnsTaken: { 1: 0, 2: 0 },   // individual turn count

        // Reserves
        soldierReserveCount: { 1: 3, 2: 3 },
        corvetteReserveCount: { 1: 2, 2: 2 },
        hopperReserveCount: { 1: 3, 2: 3 },
        generalReserveCount: { 1: 2, 2: 2 },

        selectedSoldier: null,              // { q, r } or null when moving
        selectedCorvette: null,             // { q, r } or null when moving
        selectedHopper: null,               // { q, r } or null when moving
        selectedGeneral: null,              // { q, r } or null when moving

        // Current action mode
        actionMode: 'place_soldier',        // 'place_royal' | 'place_soldier' | 'place_corvette' | 'place_hopper' | 'place_general' | 'move_royal' | 'move_soldier' | 'move_corvette' | 'move_hopper' | 'move_general'

        // End state
        gameOver: false,
        winner: null,
        playerAuto: { 1: false, 2: false },
        autoplayTimer: null,

        // Multiplayer P2P
        onlineRole: null,                   // 1 = Host, 2 = Guest, null = Offline/Local
        peer: null,
        conn: null,
        remoteActionInProgress: false,

        // Camera State
        isManualCamera: false,
        dragDistance: 0,
        isDragging: false,
        draggedDelta: { x: 0, y: 0 },
        wasJustDragging: false,
        lastPinchDist: null,
    };

    // ═══════════════════════════════════════════════════════════
    // DOM References
    // ═══════════════════════════════════════════════════════════
    const svgEl = document.getElementById('game-board');
    const cellElements = new Map(); // "q,r" → { group, bg, chip, crown, shield, helm, diamond, star, stackCount, preview }

    // ViewBox Animation State
    let currentViewBox = { x: -300, y: -250, w: 600, h: 500 };
    let targetViewBox = { x: -300, y: -250, w: 600, h: 500 };
    let viewBoxAnimationId = null;

    // ═══════════════════════════════════════════════════════════
    // Hex Math
    // ═══════════════════════════════════════════════════════════

    function axialToPixel(q, r) {
        const s = CONFIG.HEX_SIZE;
        return {
            x: s * Math.sqrt(3) * (q + r / 2),
            y: s * 1.5 * r,
        };
    }

    function hexPoints(cx, cy, size) {
        const pts = [];
        for (let i = 0; i < 6; i++) {
            const angle = (Math.PI / 3) * i - Math.PI / 6;
            pts.push(
                `${(cx + size * Math.cos(angle)).toFixed(2)},${(cy + size * Math.sin(angle)).toFixed(2)}`
            );
        }
        return pts.join(' ');
    }

    function getNeighbors(q, r) {
        return [
            [q + 1, r], [q - 1, r],
            [q, r + 1], [q, r - 1],
            [q + 1, r - 1], [q - 1, r + 1],
        ];
    }

    function isInsideGrid(q, r) {
        const R = CONFIG.GRID_RADIUS;
        return Math.abs(q) <= R && Math.abs(r) <= R && Math.abs(q + r) <= R;
    }

    // ═══════════════════════════════════════════════════════════
    // Stack-Agnostic Helpers
    // ═══════════════════════════════════════════════════════════

    function getOccupant(q, r) {
        const key = `${q},${r}`;
        const stack = state.board.get(key);
        if (stack && stack.length > 0) {
            return stack[stack.length - 1].player;
        }
        return undefined;
    }

    function getPieceTypeAt(q, r) {
        const key = `${q},${r}`;
        const stack = state.board.get(key);
        if (stack && stack.length > 0) {
            return stack[stack.length - 1].type;
        }
        return undefined;
    }

    function getPlacedPieces(player, type) {
        const coords = [];
        state.board.forEach((stack, key) => {
            if (stack && stack.length > 0) {
                const top = stack[stack.length - 1];
                if (top.player === player && top.type === type) {
                    const [q, r] = key.split(',').map(Number);
                    coords.push({ q, r });
                }
            }
        });
        return coords;
    }

    function isCellOccupied(q, r, liftedQ = null, liftedR = null) {
        const key = `${q},${r}`;
        const stack = state.board.get(key);
        if (!stack || stack.length === 0) return false;
        if (q === liftedQ && r === liftedR) {
            return stack.length > 1; // still occupied if another piece is underneath
        }
        return true;
    }

    function getMutualNeighbors(q1, r1, q2, r2) {
        const n1 = getNeighbors(q1, r1);
        const n2 = getNeighbors(q2, r2);
        const mutual = [];
        for (const [nq1, nr1] of n1) {
            for (const [nq2, nr2] of n2) {
                if (nq1 === nq2 && nr1 === nr2) {
                    mutual.push([nq1, nr1]);
                }
            }
        }
        return mutual;
    }

    function canSlide(q1, r1, q2, r2, liftedQ = null, liftedR = null) {
        const mutual = getMutualNeighbors(q1, r1, q2, r2);
        if (mutual.length < 2) return true;
        const cOccupied = isCellOccupied(mutual[0][0], mutual[0][1], liftedQ, liftedR);
        const dOccupied = isCellOccupied(mutual[1][0], mutual[1][1], liftedQ, liftedR);
        return !(cOccupied && dOccupied);
    }

    // ═══════════════════════════════════════════════════════════
    // Game Rules & Connectivity Checks
    // ═══════════════════════════════════════════════════════════

    /**
     * Can a piece be placed from reserve at (q, r)?
     * - First turn: forced at (0, 0)
     * - Opponent first turn: adjacent to Player 1's piece
     * - Subsequent turns: adjacent to own color AND NOT adjacent to opponent color (Field Rule)
     */
    function canPlace(q, r, player) {
        if (!isInsideGrid(q, r)) return false;
        if (state.board.has(`${q},${r}`)) return false; // Placement must be empty space
        if (state.totalPieces === 0) return q === 0 && r === 0;

        const neighbors = getNeighbors(q, r);
        const hasOwnPieces = state.playerCounts[player] > 0;

        if (!hasOwnPieces) {
            // First piece for this player: must touch any placed piece
            return neighbors.some(([nq, nr]) => state.board.has(`${nq},${nr}`));
        }

        let touchesOwn = false;
        let touchesOpponent = false;
        const opponent = player === 1 ? 2 : 1;

        for (const [nq, nr] of neighbors) {
            const key = `${nq},${nr}`;
            if (state.board.has(key)) {
                const occ = getOccupant(nq, nr);
                if (occ === player) touchesOwn = true;
                if (occ === opponent) touchesOpponent = true;
            }
        }

        return touchesOwn && !touchesOpponent;
    }

    /**
     * Verifies connectivity using BFS/DFS.
     * Handles stacked structures by checking if the coordinate grid remains fully connected
     * when the top piece at (fromQ, fromR) is temporarily lifted.
     */
    function isBoardConnectedAfterMoving(fromQ, fromR) {
        const key = `${fromQ},${fromR}`;
        const stack = state.board.get(key);
        if (!stack || stack.length === 0) return true;

        const topPiece = stack.pop();
        if (stack.length === 0) {
            state.board.delete(key);
        }

        const remainingOccupied = [];
        state.board.forEach((s, k) => {
            if (s && s.length > 0) {
                const [q, r] = k.split(',').map(Number);
                remainingOccupied.push({ q, r, key: k });
            }
        });

        let isConnected = true;
        if (remainingOccupied.length > 1) {
            const visited = new Set();
            const queue = [remainingOccupied[0]];
            visited.add(remainingOccupied[0].key);

            let count = 0;
            while (queue.length > 0) {
                const curr = queue.shift();
                count++;

                const neighbors = getNeighbors(curr.q, curr.r);
                for (const [nq, nr] of neighbors) {
                    const nKey = `${nq},${nr}`;
                    if (state.board.has(nKey) && !visited.has(nKey)) {
                        visited.add(nKey);
                        queue.push({ q: nq, r: nr, key: nKey });
                    }
                }
            }
            isConnected = (count === remainingOccupied.length);
        }

        // Restore stack
        if (stack.length === 0) {
            state.board.set(key, stack);
        }
        stack.push(topPiece);

        return isConnected;
    }

    /** Can the current player's royal move to (toQ, toR)? */
    function canMoveRoyalTo(toQ, toR) {
        const royal = state.royals[state.currentPlayer];
        if (!royal) return false;
        if (!isInsideGrid(toQ, toR)) return false;
        if (state.board.has(`${toQ},${toR}`)) return false; // Royal cannot stack

        // Must be adjacent to royal's current space
        const isAdj = getNeighbors(royal.q, royal.r).some(([nq, nr]) => nq === toQ && nr === toR);
        if (!isAdj) return false;

        // Connectivity check
        if (!isBoardConnectedAfterMoving(royal.q, royal.r)) return false;

        // Destination must touch at least one of the remaining pieces
        const otherPiecesCount = state.totalPieces - 1;
        if (otherPiecesCount > 0) {
            const touchesOther = getNeighbors(toQ, toR).some(([nq, nr]) => {
                const nKey = `${nq},${nr}`;
                return state.board.has(nKey) && (nq !== royal.q || nr !== royal.r);
            });
            if (!touchesOther) return false;
        }

        // Slide check
        if (!canSlide(royal.q, royal.r, toQ, toR, royal.q, royal.r)) return false;

        return true;
    }

    /** Can a soldier move from (fromQ, fromR) to (toQ, toR)? */
    function canMoveSoldierTo(fromQ, fromR, toQ, toR) {
        const targets = getSoldierMoveTargets(fromQ, fromR);
        return targets.some(t => t.q === toQ && t.r === toR);
    }

    /** Can a Corvette move from (fromQ, fromR) to (toQ, toR)? */
    function canMoveCorvetteTo(fromQ, fromR, toQ, toR) {
        if (!isInsideGrid(toQ, toR)) return false;

        // Must be adjacent
        const isAdj = getNeighbors(fromQ, fromR).some(([nq, nr]) => nq === toQ && nr === toR);
        if (!isAdj) return false;

        // Connectivity check
        if (!isBoardConnectedAfterMoving(fromQ, fromR)) return false;

        // If landing on an empty cell, verify it is connected to the remaining pieces
        const toStack = state.board.get(`${toQ},${toR}`);
        const isToEmpty = !toStack || toStack.length === 0;

        if (isToEmpty) {
            const fromStack = state.board.get(`${fromQ},${fromR}`);
            const willFromBeEmpty = !fromStack || fromStack.length <= 1;

            const touchesOther = getNeighbors(toQ, toR).some(([nq, nr]) => {
                const nKey = `${nq},${nr}`;
                if (state.board.has(nKey)) {
                    if (nq === fromQ && nr === fromR && willFromBeEmpty) return false;
                    return true;
                }
                return false;
            });

            if (!touchesOther) return false;
        }

        return true;
    }

    /** Can a Hopper move from (fromQ, fromR) to (toQ, toR)? */
    function canMoveHopperTo(fromQ, fromR, toQ, toR) {
        const targets = getHopperMoveTargets(fromQ, fromR);
        return targets.some(t => t.q === toQ && t.r === toR);
    }

    /** Can a General move from (fromQ, fromR) to (toQ, toR)? */
    function canMoveGeneralTo(fromQ, fromR, toQ, toR) {
        const targets = getGeneralMoveTargets(fromQ, fromR);
        return targets.some(t => t.q === toQ && t.r === toR);
    }

    /** Gets all valid perimeter move destinations for a Soldier */
    function getSoldierMoveTargets(sq, sr) {
        if (!isBoardConnectedAfterMoving(sq, sr)) return [];

        function isPerimeterCell(q, r) {
            if (!isInsideGrid(q, r)) return false;
            if (isCellOccupied(q, r, sq, sr)) return false; // Must be empty (lifted sq, sr)

            return getNeighbors(q, r).some(([nq, nr]) => {
                return isCellOccupied(nq, nr, sq, sr);
            });
        }

        const visited = new Set();
        const targets = [];
        const queue = [];

        // Seed initial neighbors
        getNeighbors(sq, sr).forEach(([nq, nr]) => {
            if (isPerimeterCell(nq, nr) && canSlide(sq, sr, nq, nr, sq, sr)) {
                const key = `${nq},${nr}`;
                visited.add(key);
                queue.push({ q: nq, r: nr });
                targets.push({ q: nq, r: nr });
            }
        });

        while (queue.length > 0) {
            const curr = queue.shift();
            getNeighbors(curr.q, curr.r).forEach(([nq, nr]) => {
                if (isPerimeterCell(nq, nr) && canSlide(curr.q, curr.r, nq, nr, sq, sr)) {
                    const key = `${nq},${nr}`;
                    if (!visited.has(key)) {
                        visited.add(key);
                        queue.push({ q: nq, r: nr });
                        targets.push({ q: nq, r: nr });
                    }
                }
            });
        }

        return targets;
    }

    /** Corvette moves 1 space, either crawling on top or dropping down */
    function getCorvetteMoveTargets(cq, cr) {
        const targets = [];
        getNeighbors(cq, cr).forEach(([nq, nr]) => {
            if (canMoveCorvetteTo(cq, cr, nq, nr)) {
                targets.push({ q: nq, r: nr });
            }
        });
        return targets;
    }

    /** Hopper jumps in a straight line over occupied cells, landing on the first empty space */
    function getHopperMoveTargets(hq, hr) {
        if (!isBoardConnectedAfterMoving(hq, hr)) return [];

        const targets = [];
        const dirs = [
            [1, 0], [-1, 0], [0, 1], [0, -1], [1, -1], [-1, 1]
        ];

        for (const [dq, dr] of dirs) {
            let k = 1;
            let nq = hq + dq;
            let nr = hr + dr;

            // Must have at least one occupied space in this direction to jump
            if (!state.board.has(`${nq},${nr}`)) continue;

            // Jump over occupied cells
            while (state.board.has(`${nq},${nr}`)) {
                k++;
                nq = hq + dq * k;
                nr = hr + dr * k;
            }

            if (isInsideGrid(nq, nr)) {
                targets.push({ q: nq, r: nr });
            }
        }
        return targets;
    }

    /** General slides along empty perimeter spaces up to max 3 steps */
    function getGeneralMoveTargets(gq, gr) {
        if (!isBoardConnectedAfterMoving(gq, gr)) return [];

        function isPerimeterCell(q, r) {
            if (!isInsideGrid(q, r)) return false;
            if (isCellOccupied(q, r, gq, gr)) return false; // Must be empty (lifted gq, gr)

            return getNeighbors(q, r).some(([nq, nr]) => {
                return isCellOccupied(nq, nr, gq, gr);
            });
        }

        const visited = new Set();
        const targets = [];
        const queue = [];

        // Seed initial neighbors
        getNeighbors(gq, gr).forEach(([nq, nr]) => {
            if (isPerimeterCell(nq, nr) && canSlide(gq, gr, nq, nr, gq, gr)) {
                const key = `${nq},${nr}`;
                visited.add(key);
                queue.push({ q: nq, r: nr, depth: 1 });
                targets.push({ q: nq, r: nr });
            }
        });

        while (queue.length > 0) {
            const curr = queue.shift();
            if (curr.depth >= 3) continue;

            getNeighbors(curr.q, curr.r).forEach(([nq, nr]) => {
                if (isPerimeterCell(nq, nr) && canSlide(curr.q, curr.r, nq, nr, gq, gr)) {
                    const key = `${nq},${nr}`;
                    if (!visited.has(key)) {
                        visited.add(key);
                        queue.push({ q: nq, r: nr, depth: curr.depth + 1 });
                        targets.push({ q: nq, r: nr });
                    }
                }
            });
        }

        return targets;
    }

    /** Is the player's royal completely surrounded (no escape)? */
    function isRoyalSurrounded(player) {
        const royal = state.royals[player];
        if (!royal) return false;
        return getNeighbors(royal.q, royal.r).every(([nq, nr]) => {
            if (!isInsideGrid(nq, nr)) return true;   // board edge = blocked

            // Blocked if occupied
            if (isCellOccupied(nq, nr)) return true;

            // Blocked if we cannot slide into it from royal's current position
            if (!canSlide(royal.q, royal.r, nq, nr, royal.q, royal.r)) return true;

            return false;
        });
    }

    function isRoyalAt(q, r) {
        for (const p of [1, 2]) {
            const royal = state.royals[p];
            if (royal && royal.q === q && royal.r === r) return true;
        }
        return false;
    }

    function isSoldierAt(q, r) {
        return getPieceTypeAt(q, r) === 'soldier';
    }

    function isCorvetteAt(q, r) {
        return getPieceTypeAt(q, r) === 'corvette';
    }

    function isHopperAt(q, r) {
        return getPieceTypeAt(q, r) === 'hopper';
    }

    function isGeneralAt(q, r) {
        return getPieceTypeAt(q, r) === 'general';
    }

    /** Available actions selector */
    function getAvailableActions() {
        if (state.gameOver) return [];

        const player = state.currentPlayer;
        const turns = state.playerTurnsTaken[player];
        const hasRoyal = state.royalPlaced[player];

        // Royal placement forced on individual turn 4
        if (!hasRoyal && turns < 4) {
            if (turns === 3) {
                return ['place_royal'];
            }
            const actions = ['place_royal'];
            if (state.soldierReserveCount[player] > 0) actions.push('place_soldier');
            if (state.corvetteReserveCount[player] > 0) actions.push('place_corvette');
            if (state.hopperReserveCount[player] > 0) actions.push('place_hopper');
            if (state.generalReserveCount[player] > 0) actions.push('place_general');
            return actions;
        }

        // Subsequent turns
        const actions = [];

        if (state.soldierReserveCount[player] > 0) actions.push('place_soldier');
        if (state.corvetteReserveCount[player] > 0) actions.push('place_corvette');
        if (state.hopperReserveCount[player] > 0) actions.push('place_hopper');
        if (state.generalReserveCount[player] > 0) actions.push('place_general');

        if (hasRoyal) {
            const royal = state.royals[player];
            const hasValidMove = getNeighbors(royal.q, royal.r).some(([nq, nr]) =>
                canMoveRoyalTo(nq, nr)
            );
            if (hasValidMove) actions.push('move_royal');
        }

        // Movement for Soldier, Corvette, Hopper, General
        if (getPlacedPieces(player, 'soldier').some(s => getSoldierMoveTargets(s.q, s.r).length > 0)) {
            actions.push('move_soldier');
        }
        if (getPlacedPieces(player, 'corvette').some(c => getCorvetteMoveTargets(c.q, c.r).length > 0)) {
            actions.push('move_corvette');
        }
        if (getPlacedPieces(player, 'hopper').some(h => getHopperMoveTargets(h.q, h.r).length > 0)) {
            actions.push('move_hopper');
        }
        if (getPlacedPieces(player, 'general').some(g => getGeneralMoveTargets(g.q, g.r).length > 0)) {
            actions.push('move_general');
        }

        return actions;
    }

    // ═══════════════════════════════════════════════════════════
    // SVG Helpers
    // ═══════════════════════════════════════════════════════════

    function createSvgElement(tag, attrs = {}) {
        const el = document.createElementNS(CONFIG.SVG_NS, tag);
        for (const [k, v] of Object.entries(attrs)) {
            el.setAttribute(k, v);
        }
        return el;
    }

    // ═══════════════════════════════════════════════════════════
    // Board Rendering & Animations
    // ═══════════════════════════════════════════════════════════

    function buildBoard() {
        const R = CONFIG.GRID_RADIUS;
        const size = CONFIG.HEX_SIZE;
        const chipSize = size * CONFIG.CHIP_SCALE;

        const cells = [];
        for (let q = -R; q <= R; q++) {
            for (let r = -R; r <= R; r++) {
                if (Math.abs(q + r) > R) continue;
                const { x, y } = axialToPixel(q, r);
                cells.push({ q, r, x, y });
            }
        }

        const defs = createSvgElement('defs');

        // Glow filter
        const glow = createSvgElement('filter', {
            id: 'hex-glow', x: '-50%', y: '-50%', width: '200%', height: '200%',
        });
        glow.appendChild(createSvgElement('feGaussianBlur', { stdDeviation: '4', result: 'blur' }));
        const merge = createSvgElement('feMerge');
        merge.appendChild(createSvgElement('feMergeNode', { in: 'blur' }));
        merge.appendChild(createSvgElement('feMergeNode', { in: 'SourceGraphic' }));
        glow.appendChild(merge);
        defs.appendChild(glow);

        // Chip shadow
        const shadow = createSvgElement('filter', {
            id: 'chip-shadow', x: '-20%', y: '-20%', width: '140%', height: '140%',
        });
        shadow.appendChild(createSvgElement('feDropShadow', {
            dx: '0', dy: '2', stdDeviation: '2',
            'flood-color': 'rgba(0,0,0,0.35)', 'flood-opacity': '1',
        }));
        defs.appendChild(shadow);

        // Royal glow
        const royalGlow = createSvgElement('filter', {
            id: 'royal-glow', x: '-50%', y: '-50%', width: '200%', height: '200%',
        });
        const rgBlur = createSvgElement('feGaussianBlur', { stdDeviation: '3', result: 'blur' });
        royalGlow.appendChild(rgBlur);
        const rgMerge = createSvgElement('feMerge');
        rgMerge.appendChild(createSvgElement('feMergeNode', { in: 'blur' }));
        rgMerge.appendChild(createSvgElement('feMergeNode', { in: 'SourceGraphic' }));
        royalGlow.appendChild(rgMerge);
        defs.appendChild(royalGlow);

        svgEl.appendChild(defs);

        cells.forEach(({ q, r, x, y }) => {
            const key = `${q},${r}`;
            const group = createSvgElement('g');
            group.classList.add('hex-cell');
            group.dataset.q = q;
            group.dataset.r = r;

            // Background hex
            const bg = createSvgElement('polygon', {
                points: hexPoints(x, y, size - 1),
                class: 'hex-bg',
            });
            group.appendChild(bg);

            // Chip (hidden initially)
            const chip = createSvgElement('polygon', {
                points: hexPoints(x, y, chipSize),
                class: 'hex-chip',
            });
            chip.style.display = 'none';
            chip.setAttribute('filter', 'url(#chip-shadow)');
            group.appendChild(chip);

            // Crown text (Royal)
            const crown = createSvgElement('text', {
                x: x.toFixed(2), y: y.toFixed(2), 'text-anchor': 'middle', dy: '0.38em', class: 'hex-crown',
            });
            crown.style.fontSize = `${Math.round(chipSize * 0.6)}px`;
            crown.textContent = '♛';
            crown.style.display = 'none';
            group.appendChild(crown);

            // Shield text (Soldier)
            const shield = createSvgElement('text', {
                x: x.toFixed(2), y: y.toFixed(2), 'text-anchor': 'middle', dy: '0.38em', class: 'hex-shield',
            });
            shield.style.fontSize = `${Math.round(chipSize * 0.52)}px`;
            shield.textContent = '🛡';
            shield.style.display = 'none';
            group.appendChild(shield);

            // Helm text (Corvette)
            const helm = createSvgElement('text', {
                x: x.toFixed(2), y: y.toFixed(2), 'text-anchor': 'middle', dy: '0.38em', class: 'hex-helm',
            });
            helm.style.fontSize = `${Math.round(chipSize * 0.52)}px`;
            helm.textContent = '⎈';
            helm.style.display = 'none';
            group.appendChild(helm);

            // Diamond text (Hopper)
            const diamond = createSvgElement('text', {
                x: x.toFixed(2), y: y.toFixed(2), 'text-anchor': 'middle', dy: '0.38em', class: 'hex-diamond',
            });
            diamond.style.fontSize = `${Math.round(chipSize * 0.55)}px`;
            diamond.textContent = '⬦';
            diamond.style.display = 'none';
            group.appendChild(diamond);

            // Star text (General)
            const star = createSvgElement('text', {
                x: x.toFixed(2), y: y.toFixed(2), 'text-anchor': 'middle', dy: '0.38em', class: 'hex-star',
            });
            star.style.fontSize = `${Math.round(chipSize * 0.55)}px`;
            star.textContent = '★';
            star.style.display = 'none';
            group.appendChild(star);

            // Stack count text badge
            const stackCount = createSvgElement('text', {
                x: (x + size * 0.42).toFixed(2),
                y: (y - size * 0.42).toFixed(2),
                'text-anchor': 'middle',
                class: 'hex-stack-count',
            });
            stackCount.style.fontSize = `${Math.round(size * 0.28)}px`;
            stackCount.style.display = 'none';
            group.appendChild(stackCount);

            // Preview ghost (hidden initially)
            const preview = createSvgElement('polygon', {
                points: hexPoints(x, y, chipSize),
                class: 'hex-preview',
            });
            preview.style.display = 'none';
            group.appendChild(preview);

            // Events
            group.addEventListener('pointerenter', () => handleHover(q, r, true));
            group.addEventListener('pointerleave', () => handleHover(q, r, false));
            group.addEventListener('click', () => handleClick(q, r));

            svgEl.appendChild(group);
            cellElements.set(key, { group, bg, chip, crown, shield, helm, diamond, star, stackCount, preview });
        });
    }

    /** Re-render a single cell to match current state. */
    function renderCell(q, r) {
        const key = `${q},${r}`;
        const cell = cellElements.get(key);
        if (!cell) return;

        const occupant = getOccupant(q, r);
        const type = getPieceTypeAt(q, r);
        const stack = state.board.get(key);

        cell.group.classList.remove('hex-cell--royal', 'hex-cell--soldier', 'hex-cell--corvette', 'hex-cell--hopper', 'hex-cell--general', 'hex-cell--placed');

        // Hide all piece indicators initially
        cell.crown.style.display = 'none';
        cell.shield.style.display = 'none';
        cell.helm.style.display = 'none';
        cell.diamond.style.display = 'none';
        cell.star.style.display = 'none';
        cell.stackCount.style.display = 'none';

        if (occupant !== undefined) {
            const color = state.playerColors[occupant];
            cell.chip.style.display = '';
            if (state.playerAvatars[occupant]) {
                cell.chip.style.fill = `url(#player${occupant}-avatar-pattern)`;
            } else {
                cell.chip.style.fill = color;
            }

            if (type === 'royal') {
                cell.chip.style.stroke = '#f59e0b';
                cell.chip.style.strokeWidth = '2';
                cell.chip.setAttribute('filter', 'url(#royal-glow)');
                cell.crown.style.display = '';
                cell.crown.style.fill = getCrownColor(color);
                cell.group.classList.add('hex-cell--royal', 'hex-cell--placed');
            } else if (type === 'soldier') {
                cell.chip.style.stroke = '#94a3b8';
                cell.chip.style.strokeWidth = '2.2';
                cell.chip.setAttribute('filter', 'url(#chip-shadow)');
                cell.shield.style.display = '';
                cell.shield.style.fill = getCrownColor(color);
                cell.group.classList.add('hex-cell--soldier', 'hex-cell--placed');
            } else if (type === 'corvette') {
                cell.chip.style.stroke = '#c084fc';
                cell.chip.style.strokeWidth = '2.2';
                cell.chip.setAttribute('filter', 'url(#chip-shadow)');
                cell.helm.style.display = '';
                cell.helm.style.fill = getCrownColor(color);
                cell.group.classList.add('hex-cell--corvette', 'hex-cell--placed');
            } else if (type === 'hopper') {
                cell.chip.style.stroke = '#2dd4bf';
                cell.chip.style.strokeWidth = '2.2';
                cell.chip.setAttribute('filter', 'url(#chip-shadow)');
                cell.diamond.style.display = '';
                cell.diamond.style.fill = getCrownColor(color);
                cell.group.classList.add('hex-cell--hopper', 'hex-cell--placed');
            } else if (type === 'general') {
                cell.chip.style.stroke = '#fb923c';
                cell.chip.style.strokeWidth = '2.2';
                cell.chip.setAttribute('filter', 'url(#chip-shadow)');
                cell.star.style.display = '';
                cell.star.style.fill = getCrownColor(color);
                cell.group.classList.add('hex-cell--general', 'hex-cell--placed');
            } else {
                cell.chip.style.stroke = chipStroke(color);
                cell.chip.style.strokeWidth = '1.5';
                cell.chip.setAttribute('filter', 'url(#chip-shadow)');
                cell.group.classList.add('hex-cell--placed');
            }

            // Draw stack indicator if multiple pieces are stacked underneath
            if (stack && stack.length > 1) {
                cell.stackCount.style.display = '';
                cell.stackCount.textContent = `+${stack.length - 1}`;
            }
        } else {
            cell.chip.style.display = 'none';
        }
    }

    function getCrownColor(hexColor) {
        const rv = parseInt(hexColor.slice(1, 3), 16);
        const g = parseInt(hexColor.slice(3, 5), 16);
        const b = parseInt(hexColor.slice(5, 7), 16);
        const lum = (0.299 * rv + 0.587 * g + 0.114 * b) / 255;
        return lum > 0.45 ? 'rgba(0,0,0,0.75)' : 'rgba(255,255,255,0.95)';
    }

    function chipStroke(hexColor) {
        const rv = parseInt(hexColor.slice(1, 3), 16);
        const g = parseInt(hexColor.slice(3, 5), 16);
        const b = parseInt(hexColor.slice(5, 7), 16);
        const lum = (0.299 * rv + 0.587 * g + 0.114 * b) / 255;
        return lum > 0.45 ? 'rgba(0,0,0,0.2)' : 'rgba(255,255,255,0.25)';
    }

    function animateChip(key) {
        const cell = cellElements.get(key);
        if (!cell) return;
        cell.chip.classList.remove('chip-enter');
        void cell.chip.offsetWidth;
        cell.chip.classList.add('chip-enter');
    }

    // Smooth ViewBox Animation
    function animateViewBox() {
        const lerp = (start, end, amt) => (1 - amt) * start + amt * end;
        const speed = 0.085;
        
        currentViewBox.x = lerp(currentViewBox.x, targetViewBox.x, speed);
        currentViewBox.y = lerp(currentViewBox.y, targetViewBox.y, speed);
        currentViewBox.w = lerp(currentViewBox.w, targetViewBox.w, speed);
        currentViewBox.h = lerp(currentViewBox.h, targetViewBox.h, speed);
        
        svgEl.setAttribute('viewBox', 
            `${currentViewBox.x.toFixed(1)} ${currentViewBox.y.toFixed(1)} ` +
            `${currentViewBox.w.toFixed(1)} ${currentViewBox.h.toFixed(1)}`
        );
        
        const dx = Math.abs(currentViewBox.x - targetViewBox.x);
        const dy = Math.abs(currentViewBox.y - targetViewBox.y);
        const dw = Math.abs(currentViewBox.w - targetViewBox.w);
        const dh = Math.abs(currentViewBox.h - targetViewBox.h);
        
        if (dx > 0.1 || dy > 0.1 || dw > 0.1 || dh > 0.1) {
            viewBoxAnimationId = requestAnimationFrame(animateViewBox);
        } else {
            viewBoxAnimationId = null;
        }
    }

    function updateTargetViewBox(visibleCoords) {
        if (state.isManualCamera) return; // Skip auto-fit if manual camera is active
        if (visibleCoords.length === 0) return;
        
        let minX = Infinity, maxX = -Infinity, minY = Infinity, maxY = -Infinity;
        const size = CONFIG.HEX_SIZE;
        
        visibleCoords.forEach(([q, r]) => {
            const { x, y } = axialToPixel(q, r);
            minX = Math.min(minX, x - size);
            maxX = Math.max(maxX, x + size);
            minY = Math.min(minY, y - size);
            maxY = Math.max(maxY, y + size);
        });
        
        const padX = size * 2.0;
        const padY = size * 2.0;
        
        targetViewBox = {
            x: minX - padX,
            y: minY - padY,
            w: (maxX - minX) + padX * 2,
            h: (maxY - minY) + padY * 2
        };
        
        if (!viewBoxAnimationId) {
            viewBoxAnimationId = requestAnimationFrame(animateViewBox);
        }
    }

    // Dynamic Board Visibility
    function updateCellVisibilities() {
        const visibleKeys = new Set();
        
        // Placed stack cells are always visible
        state.board.forEach((stack, key) => {
            if (stack && stack.length > 0) {
                visibleKeys.add(key);
            }
        });
        
        if (!state.gameOver) {
            const player = state.currentPlayer;
            const mode = state.actionMode;
            
            if (state.totalPieces === 0) {
                visibleKeys.add('0,0');
                const centerCell = cellElements.get('0,0');
                if (centerCell) {
                    centerCell.group.classList.add('hex-cell--start-pulse');
                }
            } else {
                const centerCell = cellElements.get('0,0');
                if (centerCell) {
                    centerCell.group.classList.remove('hex-cell--start-pulse');
                }
                if (mode.startsWith('place')) {
                    for (let q = -CONFIG.GRID_RADIUS; q <= CONFIG.GRID_RADIUS; q++) {
                        for (let r = -CONFIG.GRID_RADIUS; r <= CONFIG.GRID_RADIUS; r++) {
                            if (Math.abs(q + r) > CONFIG.GRID_RADIUS) continue;
                            if (canPlace(q, r, player)) {
                                visibleKeys.add(`${q},${r}`);
                            }
                        }
                    }
                } else if (mode === 'move_royal') {
                    const royal = state.royals[player];
                    if (royal) {
                        visibleKeys.add(`${royal.q},${royal.r}`);
                        getNeighbors(royal.q, royal.r).forEach(([nq, nr]) => {
                            if (canMoveRoyalTo(nq, nr)) visibleKeys.add(`${nq},${nr}`);
                        });
                    }
                } else if (mode === 'move_soldier') {
                    if (state.selectedSoldier) {
                        const soldier = state.selectedSoldier;
                        visibleKeys.add(`${soldier.q},${soldier.r}`);
                        getSoldierMoveTargets(soldier.q, soldier.r).forEach(({ q, r }) => {
                            visibleKeys.add(`${q},${r}`);
                        });
                    } else {
                        getPlacedPieces(player, 'soldier').forEach(({ q, r }) => {
                            visibleKeys.add(`${q},${r}`);
                        });
                    }
                } else if (mode === 'move_corvette') {
                    if (state.selectedCorvette) {
                        const corvette = state.selectedCorvette;
                        visibleKeys.add(`${corvette.q},${corvette.r}`);
                        getCorvetteMoveTargets(corvette.q, corvette.r).forEach(({ q, r }) => {
                            visibleKeys.add(`${q},${r}`);
                        });
                    } else {
                        getPlacedPieces(player, 'corvette').forEach(({ q, r }) => {
                            visibleKeys.add(`${q},${r}`);
                        });
                    }
                } else if (mode === 'move_hopper') {
                    if (state.selectedHopper) {
                        const hopper = state.selectedHopper;
                        visibleKeys.add(`${hopper.q},${hopper.r}`);
                        getHopperMoveTargets(hopper.q, hopper.r).forEach(({ q, r }) => {
                            visibleKeys.add(`${q},${r}`);
                        });
                    } else {
                        getPlacedPieces(player, 'hopper').forEach(({ q, r }) => {
                            visibleKeys.add(`${q},${r}`);
                        });
                    }
                } else if (mode === 'move_general') {
                    if (state.selectedGeneral) {
                        const general = state.selectedGeneral;
                        visibleKeys.add(`${general.q},${general.r}`);
                        getGeneralMoveTargets(general.q, general.r).forEach(({ q, r }) => {
                            visibleKeys.add(`${q},${r}`);
                        });
                    } else {
                        getPlacedPieces(player, 'general').forEach(({ q, r }) => {
                            visibleKeys.add(`${q},${r}`);
                        });
                    }
                }
            }
        }
        
        const visibleCoords = [];
        cellElements.forEach((cell, key) => {
            const isVisible = visibleKeys.has(key);
            cell.group.classList.toggle('hex-cell--visible', isVisible);
            if (isVisible) {
                const [q, r] = key.split(',').map(Number);
                visibleCoords.push([q, r]);
            }
        });
        
        updateTargetViewBox(visibleCoords);
    }

    // ═══════════════════════════════════════════════════════════
    // Action Mode Controls
    // ═══════════════════════════════════════════════════════════

    function setActionMode(mode) {
        if (state.gameOver) return;
        const available = getAvailableActions();
        if (!available.includes(mode)) mode = available[0] || 'place_soldier';
        state.actionMode = mode;
        
        // Reset selections if switching mode
        if (mode !== 'move_soldier') state.selectedSoldier = null;
        if (mode !== 'move_corvette') state.selectedCorvette = null;
        if (mode !== 'move_hopper') state.selectedHopper = null;
        if (mode !== 'move_general') state.selectedGeneral = null;

        clearHighlights();

        if (mode === 'move_royal') {
            highlightMoveTargets();
        } else if (mode === 'move_soldier') {
            highlightSoldierTargets();
        } else if (mode === 'move_corvette') {
            highlightCorvetteTargets();
        } else if (mode === 'move_hopper') {
            highlightHopperTargets();
        } else if (mode === 'move_general') {
            highlightGeneralTargets();
        }

        updateActionButtons();
        updateStatus();
        updateCellVisibilities();
    }

    function clearHighlights() {
        cellElements.forEach((cell) => {
            cell.group.classList.remove(
                'hex-cell--move-target',
                'hex-cell--royal-source',
                'hex-cell--valid'
            );
            cell.preview.style.display = 'none';
        });
    }

    function highlightMoveTargets() {
        const royal = state.royals[state.currentPlayer];
        if (!royal) return;

        const royalCell = cellElements.get(`${royal.q},${royal.r}`);
        if (royalCell) royalCell.group.classList.add('hex-cell--royal-source');

        getNeighbors(royal.q, royal.r).forEach(([nq, nr]) => {
            if (canMoveRoyalTo(nq, nr)) {
                const cell = cellElements.get(`${nq},${nr}`);
                if (cell) cell.group.classList.add('hex-cell--move-target');
            }
        });
    }

    function highlightSoldierTargets() {
        if (state.selectedSoldier) {
            const soldier = state.selectedSoldier;
            const sCell = cellElements.get(`${soldier.q},${soldier.r}`);
            if (sCell) sCell.group.classList.add('hex-cell--royal-source');

            getSoldierMoveTargets(soldier.q, soldier.r).forEach(({ q, r }) => {
                const cell = cellElements.get(`${q},${r}`);
                if (cell) cell.group.classList.add('hex-cell--move-target');
            });
        } else {
            getPlacedPieces(state.currentPlayer, 'soldier').forEach(({ q, r }) => {
                const cell = cellElements.get(`${q},${r}`);
                if (cell) cell.group.classList.add('hex-cell--move-target');
            });
        }
    }

    function highlightCorvetteTargets() {
        if (state.selectedCorvette) {
            const corvette = state.selectedCorvette;
            const cCell = cellElements.get(`${corvette.q},${corvette.r}`);
            if (cCell) cCell.group.classList.add('hex-cell--royal-source');

            getCorvetteMoveTargets(corvette.q, corvette.r).forEach(({ q, r }) => {
                const cell = cellElements.get(`${q},${r}`);
                if (cell) cell.group.classList.add('hex-cell--move-target');
            });
        } else {
            getPlacedPieces(state.currentPlayer, 'corvette').forEach(({ q, r }) => {
                const cell = cellElements.get(`${q},${r}`);
                if (cell) cell.group.classList.add('hex-cell--move-target');
            });
        }
    }

    function highlightHopperTargets() {
        if (state.selectedHopper) {
            const hopper = state.selectedHopper;
            const hCell = cellElements.get(`${hopper.q},${hopper.r}`);
            if (hCell) hCell.group.classList.add('hex-cell--royal-source');

            getHopperMoveTargets(hopper.q, hopper.r).forEach(({ q, r }) => {
                const cell = cellElements.get(`${q},${r}`);
                if (cell) cell.group.classList.add('hex-cell--move-target');
            });
        } else {
            getPlacedPieces(state.currentPlayer, 'hopper').forEach(({ q, r }) => {
                const cell = cellElements.get(`${q},${r}`);
                if (cell) cell.group.classList.add('hex-cell--move-target');
            });
        }
    }

    function highlightGeneralTargets() {
        if (state.selectedGeneral) {
            const general = state.selectedGeneral;
            const gCell = cellElements.get(`${general.q},${general.r}`);
            if (gCell) gCell.group.classList.add('hex-cell--royal-source');

            getGeneralMoveTargets(general.q, general.r).forEach(({ q, r }) => {
                const cell = cellElements.get(`${q},${r}`);
                if (cell) cell.group.classList.add('hex-cell--move-target');
            });
        } else {
            getPlacedPieces(state.currentPlayer, 'general').forEach(({ q, r }) => {
                const cell = cellElements.get(`${q},${r}`);
                if (cell) cell.group.classList.add('hex-cell--move-target');
            });
        }
    }

    // ═══════════════════════════════════════════════════════════
    // Event Handlers
    // ═══════════════════════════════════════════════════════════

    function handleHover(q, r, entering) {
        if (state.gameOver) return;
        const key = `${q},${r}`;
        const cell = cellElements.get(key);
        if (!cell) return;

        if (!entering) {
            cell.preview.style.display = 'none';
            cell.group.classList.remove('hex-cell--valid');
            return;
        }

        const mode = state.actionMode;
        const player = state.currentPlayer;
        const color = state.playerColors[player];

        if (mode.startsWith('place') && canPlace(q, r, player)) {
            cell.preview.style.display = '';
            cell.preview.style.fill = color;
            cell.preview.style.opacity = mode === 'place_royal' ? '0.45' : '0.3';
            cell.group.classList.add('hex-cell--valid');
        } else if (mode === 'move_royal' && canMoveRoyalTo(q, r)) {
            cell.preview.style.display = '';
            cell.preview.style.fill = color;
            cell.preview.style.opacity = '0.35';
            cell.group.classList.add('hex-cell--valid');
        } else if (mode === 'move_soldier' && state.selectedSoldier && canMoveSoldierTo(state.selectedSoldier.q, state.selectedSoldier.r, q, r)) {
            cell.preview.style.display = '';
            cell.preview.style.fill = color;
            cell.preview.style.opacity = '0.35';
            cell.group.classList.add('hex-cell--valid');
        } else if (mode === 'move_corvette' && state.selectedCorvette && canMoveCorvetteTo(state.selectedCorvette.q, state.selectedCorvette.r, q, r)) {
            cell.preview.style.display = '';
            cell.preview.style.fill = color;
            cell.preview.style.opacity = '0.35';
            cell.group.classList.add('hex-cell--valid');
        } else if (mode === 'move_hopper' && state.selectedHopper && canMoveHopperTo(state.selectedHopper.q, state.selectedHopper.r, q, r)) {
            cell.preview.style.display = '';
            cell.preview.style.fill = color;
            cell.preview.style.opacity = '0.35';
            cell.group.classList.add('hex-cell--valid');
        } else if (mode === 'move_general' && state.selectedGeneral && canMoveGeneralTo(state.selectedGeneral.q, state.selectedGeneral.r, q, r)) {
            cell.preview.style.display = '';
            cell.preview.style.fill = color;
            cell.preview.style.opacity = '0.35';
            cell.group.classList.add('hex-cell--valid');
        }
    }

    function handleClick(q, r) {
        if (state.gameOver) return;
        if (state.wasJustDragging) return;
        if (state.onlineRole !== null && state.currentPlayer !== state.onlineRole) return;
        stopCurrentPlayerAuto();

        const occupant = getOccupant(q, r);
        const type = getPieceTypeAt(q, r);

        // Click on player's own pieces to automatically select for movement
        if (occupant === state.currentPlayer) {
            const available = getAvailableActions();
            if (type === 'royal' && available.includes('move_royal')) {
                setActionMode('move_royal');
                return;
            } else if (type === 'soldier' && available.includes('move_soldier')) {
                state.selectedSoldier = { q, r };
                setActionMode('move_soldier');
                return;
            } else if (type === 'corvette' && available.includes('move_corvette')) {
                state.selectedCorvette = { q, r };
                setActionMode('move_corvette');
                return;
            } else if (type === 'hopper' && available.includes('move_hopper')) {
                state.selectedHopper = { q, r };
                setActionMode('move_hopper');
                return;
            } else if (type === 'general' && available.includes('move_general')) {
                state.selectedGeneral = { q, r };
                setActionMode('move_general');
                return;
            }
        }

        switch (state.actionMode) {
            case 'place_royal':    placeRoyal(q, r); break;
            case 'place_soldier':  placeSoldier(q, r); break;
            case 'place_corvette': placeCorvette(q, r); break;
            case 'place_hopper':   placeHopper(q, r); break;
            case 'place_general':  placeGeneral(q, r); break;
            case 'move_royal':     moveRoyal(q, r); break;
            case 'move_soldier':   moveSoldier(q, r); break;
            case 'move_corvette':  moveCorvette(q, r); break;
            case 'move_hopper':    moveHopper(q, r); break;
            case 'move_general':   moveGeneral(q, r); break;
        }
    }

    // ═══════════════════════════════════════════════════════════
    // Game Actions
    // ═══════════════════════════════════════════════════════════

    function pushToBoard(q, r, player, type) {
        const key = `${q},${r}`;
        if (!state.board.has(key)) {
            state.board.set(key, []);
        }
        state.board.get(key).push({ player, type });
        state.totalPieces++;
        state.playerCounts[player]++;
    }

    function popFromBoard(q, r) {
        const key = `${q},${r}`;
        const stack = state.board.get(key);
        if (stack && stack.length > 0) {
            const popped = stack.pop();
            state.totalPieces--;
            state.playerCounts[popped.player]--;
            if (stack.length === 0) {
                state.board.delete(key);
            }
            return popped;
        }
        return null;
    }


    function placeRoyal(q, r) {
        const player = state.currentPlayer;
        if (!canPlace(q, r, player)) return;

        if (state.onlineRole !== null && state.currentPlayer === state.onlineRole && !state.remoteActionInProgress) {
            sendNetworkMessage({ type: 'place', pieceType: 'royal', q, r });
        }

        pushToBoard(q, r, player, 'royal');
        state.royals[player] = { q, r };
        state.royalPlaced[player] = true;
        state.playerTurnsTaken[player]++;
        state.moveHistory.push({ type: 'place_royal', q, r, player });

        renderCell(q, r);
        animateChip(`${q},${r}`);
        endTurn();
    }

    function placeSoldier(q, r) {
        const player = state.currentPlayer;
        if (!canPlace(q, r, player) || state.soldierReserveCount[player] <= 0) return;

        if (state.onlineRole !== null && state.currentPlayer === state.onlineRole && !state.remoteActionInProgress) {
            sendNetworkMessage({ type: 'place', pieceType: 'soldier', q, r });
        }

        pushToBoard(q, r, player, 'soldier');
        state.soldierReserveCount[player]--;
        state.playerTurnsTaken[player]++;
        state.moveHistory.push({ type: 'place_soldier', q, r, player });

        renderCell(q, r);
        animateChip(`${q},${r}`);
        endTurn();
    }

    function placeCorvette(q, r) {
        const player = state.currentPlayer;
        if (!canPlace(q, r, player) || state.corvetteReserveCount[player] <= 0) return;

        if (state.onlineRole !== null && state.currentPlayer === state.onlineRole && !state.remoteActionInProgress) {
            sendNetworkMessage({ type: 'place', pieceType: 'corvette', q, r });
        }

        pushToBoard(q, r, player, 'corvette');
        state.corvetteReserveCount[player]--;
        state.playerTurnsTaken[player]++;
        state.moveHistory.push({ type: 'place_corvette', q, r, player });

        renderCell(q, r);
        animateChip(`${q},${r}`);
        endTurn();
    }

    function placeHopper(q, r) {
        const player = state.currentPlayer;
        if (!canPlace(q, r, player) || state.hopperReserveCount[player] <= 0) return;

        if (state.onlineRole !== null && state.currentPlayer === state.onlineRole && !state.remoteActionInProgress) {
            sendNetworkMessage({ type: 'place', pieceType: 'hopper', q, r });
        }

        pushToBoard(q, r, player, 'hopper');
        state.hopperReserveCount[player]--;
        state.playerTurnsTaken[player]++;
        state.moveHistory.push({ type: 'place_hopper', q, r, player });

        renderCell(q, r);
        animateChip(`${q},${r}`);
        endTurn();
    }

    function placeGeneral(q, r) {
        const player = state.currentPlayer;
        if (!canPlace(q, r, player) || state.generalReserveCount[player] <= 0) return;

        if (state.onlineRole !== null && state.currentPlayer === state.onlineRole && !state.remoteActionInProgress) {
            sendNetworkMessage({ type: 'place', pieceType: 'general', q, r });
        }

        pushToBoard(q, r, player, 'general');
        state.generalReserveCount[player]--;
        state.playerTurnsTaken[player]++;
        state.moveHistory.push({ type: 'place_general', q, r, player });

        renderCell(q, r);
        animateChip(`${q},${r}`);
        endTurn();
    }

    function moveRoyal(toQ, toR) {
        if (!canMoveRoyalTo(toQ, toR)) return;

        if (state.onlineRole !== null && state.currentPlayer === state.onlineRole && !state.remoteActionInProgress) {
            const royal = state.royals[state.currentPlayer];
            sendNetworkMessage({ type: 'move', pieceType: 'royal', fromQ: royal.q, fromR: royal.r, toQ, toR });
        }

        const player = state.currentPlayer;
        const royal = state.royals[player];
        const fromQ = royal.q, fromR = royal.r;

        popFromBoard(fromQ, fromR);
        pushToBoard(toQ, toR, player, 'royal');
        state.royals[player] = { q: toQ, r: toR };
        state.playerTurnsTaken[player]++;
        state.moveHistory.push({ type: 'move_royal', fromQ, fromR, toQ, toR, player });

        renderCell(fromQ, fromR);
        renderCell(toQ, toR);
        animateChip(`${toQ},${toR}`);
        endTurn();
    }

    function moveSoldier(toQ, toR) {
        const soldier = state.selectedSoldier;
        if (!soldier || !canMoveSoldierTo(soldier.q, soldier.r, toQ, toR)) return;

        if (state.onlineRole !== null && state.currentPlayer === state.onlineRole && !state.remoteActionInProgress) {
            sendNetworkMessage({ type: 'move', pieceType: 'soldier', fromQ: soldier.q, fromR: soldier.r, toQ, toR });
        }

        const player = state.currentPlayer;
        const fromQ = soldier.q, fromR = soldier.r;

        popFromBoard(fromQ, fromR);
        pushToBoard(toQ, toR, player, 'soldier');
        state.playerTurnsTaken[player]++;
        state.selectedSoldier = null;
        state.moveHistory.push({ type: 'move_soldier', fromQ, fromR, toQ, toR, player });

        renderCell(fromQ, fromR);
        renderCell(toQ, toR);
        animateChip(`${toQ},${toR}`);
        endTurn();
    }

    function moveCorvette(toQ, toR) {
        const corvette = state.selectedCorvette;
        if (!corvette || !canMoveCorvetteTo(corvette.q, corvette.r, toQ, toR)) return;

        if (state.onlineRole !== null && state.currentPlayer === state.onlineRole && !state.remoteActionInProgress) {
            sendNetworkMessage({ type: 'move', pieceType: 'corvette', fromQ: corvette.q, fromR: corvette.r, toQ, toR });
        }

        const player = state.currentPlayer;
        const fromQ = corvette.q, fromR = corvette.r;

        popFromBoard(fromQ, fromR);
        pushToBoard(toQ, toR, player, 'corvette');
        state.playerTurnsTaken[player]++;
        state.selectedCorvette = null;
        state.moveHistory.push({ type: 'move_corvette', fromQ, fromR, toQ, toR, player });

        renderCell(fromQ, fromR);
        renderCell(toQ, toR);
        animateChip(`${toQ},${toR}`);
        endTurn();
    }

    function moveHopper(toQ, toR) {
        const hopper = state.selectedHopper;
        if (!hopper || !canMoveHopperTo(hopper.q, hopper.r, toQ, toR)) return;

        if (state.onlineRole !== null && state.currentPlayer === state.onlineRole && !state.remoteActionInProgress) {
            sendNetworkMessage({ type: 'move', pieceType: 'hopper', fromQ: hopper.q, fromR: hopper.r, toQ, toR });
        }

        const player = state.currentPlayer;
        const fromQ = hopper.q, fromR = hopper.r;

        popFromBoard(fromQ, fromR);
        pushToBoard(toQ, toR, player, 'hopper');
        state.playerTurnsTaken[player]++;
        state.selectedHopper = null;
        state.moveHistory.push({ type: 'move_hopper', fromQ, fromR, toQ, toR, player });

        renderCell(fromQ, fromR);
        renderCell(toQ, toR);
        animateChip(`${toQ},${toR}`);
        endTurn();
    }

    function moveGeneral(toQ, toR) {
        const general = state.selectedGeneral;
        if (!general || !canMoveGeneralTo(general.q, general.r, toQ, toR)) return;

        if (state.onlineRole !== null && state.currentPlayer === state.onlineRole && !state.remoteActionInProgress) {
            sendNetworkMessage({ type: 'move', pieceType: 'general', fromQ: general.q, fromR: general.r, toQ, toR });
        }

        const player = state.currentPlayer;
        const fromQ = general.q, fromR = general.r;

        popFromBoard(fromQ, fromR);
        pushToBoard(toQ, toR, player, 'general');
        state.playerTurnsTaken[player]++;
        state.selectedGeneral = null;
        state.moveHistory.push({ type: 'move_general', fromQ, fromR, toQ, toR, player });

        renderCell(fromQ, fromR);
        renderCell(toQ, toR);
        animateChip(`${toQ},${toR}`);
        endTurn();
    }

    // ═══════════════════════════════════════════════════════════
    // Turn Logic
    // ═══════════════════════════════════════════════════════════

    function endTurn() {
        clearHighlights();

        // Increment moves played
        state.progression.moves += 1;
        localStorage.setItem('starblazer_moves', state.progression.moves);
        calculateLevel();
        updateProgressionUI();

        for (const p of [1, 2]) {
            if (state.royalPlaced[p] && isRoyalSurrounded(p)) {
                const winner = p === 1 ? 2 : 1;
                state.gameOver = true;
                state.winner = winner;
                
                // Increment wins
                state.progression.wins += 1;
                localStorage.setItem('starblazer_wins', state.progression.wins);
                calculateLevel();
                updateProgressionUI();

                showGameOver(winner, p);
                refreshUI();
                if (state.playerAuto[1] && state.playerAuto[2]) {
                    scheduleAutoplayMove(2000);
                }
                return;
            }
        }

        state.currentPlayer = state.currentPlayer === 1 ? 2 : 1;

        const available = getAvailableActions();
        state.actionMode = available[0] || 'place_soldier';

        refreshUI();

        if (state.actionMode === 'move_royal') {
            highlightMoveTargets();
        } else if (state.actionMode === 'move_soldier') {
            highlightSoldierTargets();
        } else if (state.actionMode === 'move_corvette') {
            highlightCorvetteTargets();
        } else if (state.actionMode === 'move_hopper') {
            highlightHopperTargets();
        } else if (state.actionMode === 'move_general') {
            highlightGeneralTargets();
        }

        if (state.playerAuto[state.currentPlayer]) {
            scheduleAutoplayMove(1000);
        }
    }

    // ═══════════════════════════════════════════════════════════
    // Reset & Undo
    // ═══════════════════════════════════════════════════════════

    function resetGame() {
        stopAllAutoplayTimers();

        if (state.onlineRole !== null && !state.remoteActionInProgress) {
            sendNetworkMessage({ type: 'reset' });
        }

        state.board.clear();
        state.totalPieces = 0;
        state.currentPlayer = 1;
        state.moveHistory = [];
        state.playerCounts = { 1: 0, 2: 0 };
        state.royals = { 1: null, 2: null };
        state.royalPlaced = { 1: false, 2: false };
        state.playerTurnsTaken = { 1: 0, 2: 0 };

        state.soldierReserveCount = { 1: 3, 2: 3 };
        state.corvetteReserveCount = { 1: 2, 2: 2 };
        state.hopperReserveCount = { 1: 3, 2: 3 };
        state.generalReserveCount = { 1: 2, 2: 2 };

        state.selectedSoldier = null;
        state.selectedCorvette = null;
        state.selectedHopper = null;
        state.selectedGeneral = null;

        state.actionMode = 'place_soldier';
        state.gameOver = false;
        state.winner = null;

        cellElements.forEach((cell) => {
            cell.chip.style.display = 'none';
            cell.crown.style.display = 'none';
            cell.shield.style.display = 'none';
            cell.helm.style.display = 'none';
            cell.diamond.style.display = 'none';
            cell.star.style.display = 'none';
            cell.stackCount.style.display = 'none';
            cell.preview.style.display = 'none';
            cell.group.classList.remove(
                'hex-cell--placed', 'hex-cell--royal', 'hex-cell--soldier',
                'hex-cell--corvette', 'hex-cell--hopper', 'hex-cell--general',
                'hex-cell--valid', 'hex-cell--move-target', 'hex-cell--royal-source'
            );
        });

        state.isManualCamera = false;
        const recenterBtn = document.getElementById('recenter-btn');
        if (recenterBtn) recenterBtn.classList.remove('active');

        hideGameOver();
        refreshUI();

        updatePlayerAutoUI(1);
        updatePlayerAutoUI(2);

        if (state.playerAuto[1]) {
            scheduleAutoplayMove(1000);
        }
    }

    function undoMove() {
        if (state.moveHistory.length === 0) return;

        if (state.onlineRole !== null && !state.remoteActionInProgress) {
            sendNetworkMessage({ type: 'undo' });
        }

        if (state.gameOver) {
            state.gameOver = false;
            state.winner = null;
            hideGameOver();
        }

        const last = state.moveHistory.pop();
        const player = last.player;

        if (last.type === 'place') {
            popFromBoard(last.q, last.r);
            state.playerTurnsTaken[player]--;
            state.currentPlayer = player;
            renderCell(last.q, last.r);

        } else if (last.type === 'place_royal') {
            popFromBoard(last.q, last.r);
            state.playerTurnsTaken[player]--;
            state.royals[player] = null;
            state.royalPlaced[player] = false;
            state.currentPlayer = player;
            renderCell(last.q, last.r);

        } else if (last.type === 'place_soldier') {
            popFromBoard(last.q, last.r);
            state.soldierReserveCount[player]++;
            state.playerTurnsTaken[player]--;
            state.currentPlayer = player;
            renderCell(last.q, last.r);

        } else if (last.type === 'place_corvette') {
            popFromBoard(last.q, last.r);
            state.corvetteReserveCount[player]++;
            state.playerTurnsTaken[player]--;
            state.currentPlayer = player;
            renderCell(last.q, last.r);

        } else if (last.type === 'place_hopper') {
            popFromBoard(last.q, last.r);
            state.hopperReserveCount[player]++;
            state.playerTurnsTaken[player]--;
            state.currentPlayer = player;
            renderCell(last.q, last.r);

        } else if (last.type === 'place_general') {
            popFromBoard(last.q, last.r);
            state.generalReserveCount[player]++;
            state.playerTurnsTaken[player]--;
            state.currentPlayer = player;
            renderCell(last.q, last.r);

        } else if (last.type === 'move_royal') {
            popFromBoard(last.toQ, last.toR);
            pushToBoard(last.fromQ, last.fromR, player, 'royal');
            state.royals[player] = { q: last.fromQ, r: last.fromR };
            state.playerTurnsTaken[player]--;
            state.currentPlayer = player;
            renderCell(last.toQ, last.toR);
            renderCell(last.fromQ, last.fromR);

        } else if (last.type === 'move_soldier') {
            popFromBoard(last.toQ, last.toR);
            pushToBoard(last.fromQ, last.fromR, player, 'soldier');
            state.playerTurnsTaken[player]--;
            state.currentPlayer = player;
            state.selectedSoldier = null;
            renderCell(last.toQ, last.toR);
            renderCell(last.fromQ, last.fromR);

        } else if (last.type === 'move_corvette') {
            popFromBoard(last.toQ, last.toR);
            pushToBoard(last.fromQ, last.fromR, player, 'corvette');
            state.playerTurnsTaken[player]--;
            state.currentPlayer = player;
            state.selectedCorvette = null;
            renderCell(last.toQ, last.toR);
            renderCell(last.fromQ, last.fromR);

        } else if (last.type === 'move_hopper') {
            popFromBoard(last.toQ, last.toR);
            pushToBoard(last.fromQ, last.fromR, player, 'hopper');
            state.playerTurnsTaken[player]--;
            state.currentPlayer = player;
            state.selectedHopper = null;
            renderCell(last.toQ, last.toR);
            renderCell(last.fromQ, last.fromR);

        } else if (last.type === 'move_general') {
            popFromBoard(last.toQ, last.toR);
            pushToBoard(last.fromQ, last.fromR, player, 'general');
            state.playerTurnsTaken[player]--;
            state.currentPlayer = player;
            state.selectedGeneral = null;
            renderCell(last.toQ, last.toR);
            renderCell(last.fromQ, last.fromR);
        }

        clearHighlights();

        const available = getAvailableActions();
        state.actionMode = available[0] || 'place_soldier';

        refreshUI();

        if (state.actionMode === 'move_royal') {
            highlightMoveTargets();
        } else if (state.actionMode === 'move_soldier') {
            highlightSoldierTargets();
        } else if (state.actionMode === 'move_corvette') {
            highlightCorvetteTargets();
        } else if (state.actionMode === 'move_hopper') {
            highlightHopperTargets();
        } else if (state.actionMode === 'move_general') {
            highlightGeneralTargets();
        }
        stopCurrentPlayerAuto();
    }

    // ═══════════════════════════════════════════════════════════
    // UI Updates
    // ═══════════════════════════════════════════════════════════

    function refreshUI() {
        // Active state
        document.getElementById('player1-card').classList.toggle('active', state.currentPlayer === 1 && !state.gameOver);
        document.getElementById('player2-card').classList.toggle('active', state.currentPlayer === 2 && !state.gameOver);

        // Previews
        document.getElementById('player1-chip').style.backgroundColor = state.playerColors[1];
        document.getElementById('player2-chip').style.backgroundColor = state.playerColors[2];

        updateRoyalStatus(1);
        updateRoyalStatus(2);

        const dotEl = document.getElementById('status-dot');
        if (!state.gameOver && dotEl) {
            dotEl.style.background = state.playerColors[state.currentPlayer];
        }

        updateActionButtons();
        updateStatus();
        updateCellVisibilities();

        updateMultiplayerCardsUI();

        if (state.onlineRole !== null) {
            document.getElementById('undo-btn').disabled = (state.moveHistory.length === 0) || (state.currentPlayer !== state.onlineRole);
        } else {
            document.getElementById('undo-btn').disabled = state.moveHistory.length === 0;
        }
    }

    function updateRoyalStatus(player) {
        const statusEl = document.getElementById(`player${player}-royal-status`);
        const labelEl = document.getElementById(`player${player}-royal-label`);

        statusEl.classList.remove('royal-placed', 'royal-required');

        if (state.royalPlaced[player]) {
            statusEl.classList.add('royal-placed');
            labelEl.textContent = 'Royal: On Board';
        } else if (state.currentPlayer === player && state.playerTurnsTaken[player] === 3) {
            statusEl.classList.add('royal-required');
            labelEl.textContent = 'Royal: Must Place!';
        } else {
            labelEl.textContent = 'Royal: Ready';
        }
    }

    function updateActionButtons() {
        const available = getAvailableActions();
        const activePiece = state.actionMode.replace('place_', '').replace('move_', '');
        const pieceTypes = ['royal', 'soldier', 'corvette', 'hopper', 'general'];

        // Disable interaction on drawers if it's not our turn in online play
        const isMyTurn = (state.onlineRole === null) || (state.currentPlayer === state.onlineRole);
        for (const p of [1, 2]) {
            const drawer = document.getElementById(`drawer-p${p}`);
            if (drawer) {
                const shouldDisable = !isMyTurn || state.currentPlayer !== p || state.gameOver;
                drawer.style.pointerEvents = shouldDisable ? 'none' : '';
                if (!isMyTurn && state.currentPlayer === p) {
                    drawer.style.opacity = '0.5';
                } else {
                    drawer.style.opacity = '';
                }
            }
        }

        for (const p of [1, 2]) {
            const isCurrent = (state.currentPlayer === p);

            // Update row active and forced states
            pieceTypes.forEach(type => {
                const rowEl = document.querySelector(`#drawer-p${p} .drawer-piece-row[data-piece="${type}"]`);
                if (rowEl) {
                    const isActiveRow = isCurrent && activePiece === type && !state.gameOver;
                    rowEl.classList.toggle('drawer-piece-row--active', isActiveRow);

                    if (type === 'royal') {
                        const isForced = isCurrent && available.length === 1 && available[0] === 'place_royal';
                        rowEl.classList.toggle('drawer-piece-row--forced', isForced);
                        const badge = document.getElementById(`p${p}-royal-required-badge`);
                        if (badge) badge.style.display = isForced ? '' : 'none';
                    }
                }
            });

            // Update Counts
            const soldierCount = document.getElementById(`p${p}-soldier-count`);
            if (soldierCount) soldierCount.textContent = state.soldierReserveCount[p];

            const corvetteCount = document.getElementById(`p${p}-corvette-count`);
            if (corvetteCount) corvetteCount.textContent = state.corvetteReserveCount[p];

            const hopperCount = document.getElementById(`p${p}-hopper-count`);
            if (hopperCount) hopperCount.textContent = state.hopperReserveCount[p];

            const generalCount = document.getElementById(`p${p}-general-count`);
            if (generalCount) generalCount.textContent = state.generalReserveCount[p];
        }
    }

    function updateStatus() {
        const statusEl = document.getElementById('game-status');
        if (!statusEl) return;

        if (state.gameOver) {
            statusEl.textContent = `Player ${state.winner} wins!`;
            return;
        }

        const name = `Player ${state.currentPlayer}`;
        const mode = state.actionMode;
        const available = getAvailableActions();
        const forced = available.length === 1 && available[0] === 'place_royal';

        const isFirstTurn = state.totalPieces === 0;

        if (mode === 'place_royal') {
            if (isFirstTurn) {
                statusEl.textContent = `${name}'s turn — place royal at the center cell`;
            } else if (forced) {
                statusEl.textContent = `${name} must place their royal!`;
            } else {
                statusEl.textContent = `${name}'s turn — place royal adjacent to a piece`;
            }
        } else if (mode === 'place_soldier') {
            statusEl.textContent = isFirstTurn
                ? `${name}'s turn — place soldier at the center cell`
                : `${name}'s turn — place soldier adjacent to a piece`;
        } else if (mode === 'place_corvette') {
            statusEl.textContent = isFirstTurn
                ? `${name}'s turn — place corvette at the center cell`
                : `${name}'s turn — place corvette adjacent to a piece`;
        } else if (mode === 'place_hopper') {
            statusEl.textContent = isFirstTurn
                ? `${name}'s turn — place hopper at the center cell`
                : `${name}'s turn — place hopper adjacent to a piece`;
        } else if (mode === 'place_general') {
            statusEl.textContent = isFirstTurn
                ? `${name}'s turn — place general at the center cell`
                : `${name}'s turn — place general adjacent to a piece`;
        } else if (mode === 'move_royal') {
            statusEl.textContent = `${name}'s turn — select where to move royal`;
        } else if (mode === 'move_soldier') {
            statusEl.textContent = state.selectedSoldier
                ? `${name}'s turn — move soldier on the perimeter`
                : `${name}'s turn — select which soldier to move`;
        } else if (mode === 'move_corvette') {
            statusEl.textContent = state.selectedCorvette
                ? `${name}'s turn — move corvette 1 space (can stack)`
                : `${name}'s turn — select which corvette to move`;
        } else if (mode === 'move_hopper') {
            statusEl.textContent = state.selectedHopper
                ? `${name}'s turn — jump hopper in a straight line`
                : `${name}'s turn — select which hopper to move`;
        } else if (mode === 'move_general') {
            statusEl.textContent = state.selectedGeneral
                ? `${name}'s turn — slide general along perimeter (max 3 spaces)`
                : `${name}'s turn — select which general to move`;
        }
    }

    function showGameOver(winner, loser) {
        document.getElementById('game-over-title').textContent = `Player ${winner} Wins!`;
        document.getElementById('game-over-desc').textContent =
            `Player ${loser}'s royal was surrounded.`;
        document.getElementById('game-over-overlay').classList.add('visible');
    }

    function hideGameOver() {
        document.getElementById('game-over-overlay').classList.remove('visible');
    }

    function updatePlayerColor(player, color) {
        state.playerColors[player] = color;
        document.documentElement.style.setProperty(`--p${player}-color`, color);

        state.board.forEach((stack, key) => {
            const [cq, cr] = key.split(',').map(Number);
            renderCell(cq, cr);
        });

        if (typeof updateLobbyImageWithColor === 'function') {
            updateLobbyImageWithColor(player, color);
        }

        refreshUI();
    }

    // ═══════════════════════════════════════════════════════════
    // Initialization
    // ═══════════════════════════════════════════════════════════

    function initThemeSelector() {
        const themeBtn = document.getElementById('theme-btn');
        const themeMenu = document.getElementById('theme-menu');
        const items = themeMenu.querySelectorAll('.theme-menu-item');

        themeBtn.addEventListener('click', (e) => {
            e.stopPropagation();
            themeMenu.classList.toggle('active');
        });

        document.addEventListener('click', () => {
            themeMenu.classList.remove('active');
        });

        items.forEach(item => {
            item.addEventListener('click', () => {
                const theme = item.dataset.theme;
                setTheme(theme);
            });
        });

        const savedTheme = localStorage.getItem('theme') || 'midnight';
        setTheme(savedTheme);
    }

    function setTheme(themeName) {
        const themes = ['midnight', 'alabaster', 'cyberpunk', 'forest', 'sunset'];
        themes.forEach(t => {
            document.body.classList.remove(`theme-${t}`);
            if (t === 'alabaster') {
                document.body.classList.remove('light-theme');
            }
        });

        if (themeName !== 'midnight') {
            document.body.classList.add(`theme-${themeName}`);
            if (themeName === 'alabaster') {
                document.body.classList.add('light-theme');
            }
        }

        localStorage.setItem('theme', themeName);

        const themeMenu = document.getElementById('theme-menu');
        const items = themeMenu.querySelectorAll('.theme-menu-item');
        items.forEach(item => {
            item.classList.toggle('theme-menu-item--active', item.dataset.theme === themeName);
        });
    }



    function initSwatches(player) {
        const container = document.getElementById(`player${player}-swatches`);
        const swatches = container.querySelectorAll('.swatch');
        const wrapper = document.getElementById(`player${player}-chip-wrapper`);

        swatches.forEach(swatch => {
            swatch.addEventListener('click', (e) => {
                e.stopPropagation();
                if (state.onlineRole !== null && player !== state.onlineRole) {
                    return;
                }
                stopCurrentPlayerAuto();
                const color = swatch.dataset.color;
                const otherPlayer = player === 1 ? 2 : 1;

                if (state.playerColors[otherPlayer] === color) {
                    const oldColor = state.playerColors[player];
                    updatePlayerColor(otherPlayer, oldColor);
                    updateSwatchUI(otherPlayer, oldColor);
                }

                updatePlayerColor(player, color);
                updateSwatchUI(player, color);

                if (state.onlineRole !== null && !state.remoteActionInProgress) {
                    sendNetworkMessage({ type: 'color', player, color });
                }

                if (wrapper) wrapper.classList.remove('open');
            });
        });
    }

    function updateSwatchUI(player, color) {
        const container = document.getElementById(`player${player}-swatches`);
        if (!container) return;
        const swatches = container.querySelectorAll('.swatch');
        swatches.forEach(swatch => {
            swatch.classList.toggle('swatch--active', swatch.dataset.color === color);
        });
    }

    function initColorPickerFan(player) {
        const wrapper = document.getElementById(`player${player}-chip-wrapper`);
        if (!wrapper) return;
        const chip = document.getElementById(`player${player}-chip`);
        
        chip.addEventListener('click', (e) => {
            e.stopPropagation();
            
            if (state.playerAvatars[player]) {
                const token = player === 1 ? currentInviteToken : currentAnswerToken;
                copyDataUrlToClipboard(state.playerAvatars[player], token);
            }

            wrapper.classList.toggle('open');
            
            const otherPlayer = player === 1 ? 2 : 1;
            const otherWrapper = document.getElementById(`player${otherPlayer}-chip-wrapper`);
            if (otherWrapper) otherWrapper.classList.remove('open');
        });
    }

    // ═══════════════════════════════════════════════════════════
    // Autoplay & Compact Row Default Click Helpers
    // ═══════════════════════════════════════════════════════════

    function togglePlayerAuto(player) {
        state.playerAuto[player] = !state.playerAuto[player];
        updatePlayerAutoUI(player);

        if (state.playerAuto[player] && state.currentPlayer === player && !state.gameOver) {
            scheduleAutoplayMove(1000);
        }
    }

    function updatePlayerAutoUI(player) {
        const btn = document.getElementById(`p${player}-type-btn`);
        if (!btn) return;
        const isAuto = state.playerAuto[player];
        btn.classList.toggle('player-type-btn--auto', isAuto);
        const iconEl = btn.querySelector('.player-type-icon');
        const labelEl = btn.querySelector('.player-type-label');
        if (isAuto) {
            if (iconEl) iconEl.textContent = '🤖';
            if (labelEl) labelEl.textContent = 'AI Player';
        } else {
            if (iconEl) iconEl.textContent = '👤';
            if (labelEl) labelEl.textContent = 'Human';
        }
    }

    function stopCurrentPlayerAuto() {
        const player = state.currentPlayer;
        if (state.playerAuto[player]) {
            state.playerAuto[player] = false;
            updatePlayerAutoUI(player);
        }
        if (state.autoplayTimer) {
            clearTimeout(state.autoplayTimer);
            state.autoplayTimer = null;
        }
    }

    function stopAllAutoplayTimers() {
        if (state.autoplayTimer) {
            clearTimeout(state.autoplayTimer);
            state.autoplayTimer = null;
        }
    }

    function scheduleAutoplayMove(delay) {
        if (state.autoplayTimer) clearTimeout(state.autoplayTimer);
        state.autoplayTimer = setTimeout(() => {
            if (state.playerAuto[state.currentPlayer]) {
                makeAutoplayMove();
            }
        }, delay);
    }

    function makeAutoplayMove() {
        if (state.gameOver) {
            if (state.playerAuto[1] && state.playerAuto[2]) {
                resetGame();
                scheduleAutoplayMove(1000);
            }
            return;
        }

        const player = state.currentPlayer;
        const available = getAvailableActions();

        if (available.length === 0) {
            endTurn();
            return;
        }

        const candidates = [];

        available.forEach(action => {
            if (action.startsWith('place_')) {
                const type = action.replace('place_', '');
                for (let q = -CONFIG.GRID_RADIUS; q <= CONFIG.GRID_RADIUS; q++) {
                    for (let r = -CONFIG.GRID_RADIUS; r <= CONFIG.GRID_RADIUS; r++) {
                        if (Math.abs(q + r) > CONFIG.GRID_RADIUS) continue;
                        if (canPlace(q, r, player)) {
                            candidates.push({
                                type: 'place',
                                action: action,
                                q: q,
                                r: r
                            });
                        }
                    }
                }
            } else if (action.startsWith('move_')) {
                const type = action.replace('move_', '');
                const pieces = getPlacedPieces(player, type);
                pieces.forEach(p => {
                    let targets = [];
                    if (type === 'royal') {
                        getNeighbors(p.q, p.r).forEach(([nq, nr]) => {
                            if (canMoveRoyalTo(nq, nr)) {
                                targets.push({ q: nq, r: nr });
                            }
                        });
                    } else if (type === 'soldier') {
                        targets = getSoldierMoveTargets(p.q, p.r);
                    } else if (type === 'corvette') {
                        targets = getCorvetteMoveTargets(p.q, p.r);
                    } else if (type === 'hopper') {
                        targets = getHopperMoveTargets(p.q, p.r);
                    } else if (type === 'general') {
                        targets = getGeneralMoveTargets(p.q, p.r);
                    }

                    targets.forEach(t => {
                        candidates.push({
                            type: 'move',
                            action: action,
                            from: { q: p.q, r: p.r },
                            to: { q: t.q, r: t.r }
                        });
                    });
                });
            }
        });

        if (candidates.length === 0) {
            endTurn();
            return;
        }

        const chosen = candidates[Math.floor(Math.random() * candidates.length)];

        if (chosen.type === 'place') {
            if (chosen.action === 'place_royal') placeRoyal(chosen.q, chosen.r);
            else if (chosen.action === 'place_soldier') placeSoldier(chosen.q, chosen.r);
            else if (chosen.action === 'place_corvette') placeCorvette(chosen.q, chosen.r);
            else if (chosen.action === 'place_hopper') placeHopper(chosen.q, chosen.r);
            else if (chosen.action === 'place_general') placeGeneral(chosen.q, chosen.r);
        } else if (chosen.type === 'move') {
            if (chosen.action === 'move_royal') {
                state.selectedSoldier = null;
                state.selectedCorvette = null;
                state.selectedHopper = null;
                state.selectedGeneral = null;
                moveRoyal(chosen.to.q, chosen.to.r);
            } else if (chosen.action === 'move_soldier') {
                state.selectedSoldier = chosen.from;
                moveSoldier(chosen.to.q, chosen.to.r);
            } else if (chosen.action === 'move_corvette') {
                state.selectedCorvette = chosen.from;
                moveCorvette(chosen.to.q, chosen.to.r);
            } else if (chosen.action === 'move_hopper') {
                state.selectedHopper = chosen.from;
                moveHopper(chosen.to.q, chosen.to.r);
            } else if (chosen.action === 'move_general') {
                state.selectedGeneral = chosen.from;
                moveGeneral(chosen.to.q, chosen.to.r);
            }
        }
    }

    function initDrawerRowClicks(player) {
        const rows = document.querySelectorAll(`#drawer-p${player} .drawer-piece-row`);
        rows.forEach(row => {
            row.addEventListener('click', (e) => {
                if (e.target.closest('.piece-fan-menu')) return;
                if (state.currentPlayer !== player || state.gameOver) return;

                // Lock clicks during opponent's turn in online play
                if (state.onlineRole !== null && state.currentPlayer !== state.onlineRole) return;

                stopCurrentPlayerAuto();

                const type = row.dataset.piece;
                const available = getAvailableActions();

                let canPlacePiece = false;
                if (type === 'royal') canPlacePiece = !state.royalPlaced[player];
                else if (type === 'soldier') canPlacePiece = state.soldierReserveCount[player] > 0;
                else if (type === 'corvette') canPlacePiece = state.corvetteReserveCount[player] > 0;
                else if (type === 'hopper') canPlacePiece = state.hopperReserveCount[player] > 0;
                else if (type === 'general') canPlacePiece = state.generalReserveCount[player] > 0;

                const placeAction = `place_${type}`;
                const moveAction = `move_${type}`;

                if (canPlacePiece && available.includes(placeAction)) {
                    setActionMode(placeAction);
                } else if (available.includes(moveAction)) {
                    setActionMode(moveAction);
                }
            });
        });
    }

    function init() {
        // Load progression stats
        state.progression = {
            wins: parseInt(localStorage.getItem('starblazer_wins') || '0', 10),
            moves: parseInt(localStorage.getItem('starblazer_moves') || '0', 10),
            level: 1
        };
        calculateLevel();

        buildBoard();

        // Handedness toggle listener
        const handBtn = document.getElementById('hand-toggle-btn');
        if (handBtn) {
            handBtn.addEventListener('click', () => {
                const gameLayout = document.querySelector('.game-layout');
                if (gameLayout) {
                    gameLayout.classList.toggle('left-handed');
                    const isLeft = gameLayout.classList.contains('left-handed');
                    localStorage.setItem('leftHanded', isLeft ? 'true' : 'false');
                }
            });
        }

        // Initialize camera controls and drag/zoom interactions
        initCameraControls();

        // Onboarding Welcome Modal logic
        const helpModal = document.getElementById('help-modal');
        const helpCloseBtn = document.getElementById('help-close-btn');
        const helpStartBtn = document.getElementById('help-start-btn');
        const howToPlayBtn = document.getElementById('how-to-play-btn');

        function openHelp() {
            if (helpModal) helpModal.style.display = '';
        }
        function closeHelp() {
            if (helpModal) helpModal.style.display = 'none';
            localStorage.setItem('starblazer_rules_read', 'true');
        }

        if (howToPlayBtn) {
            howToPlayBtn.addEventListener('click', (e) => {
                e.stopPropagation();
                openHelp();
            });
        }
        if (helpCloseBtn) helpCloseBtn.addEventListener('click', closeHelp);
        if (helpStartBtn) helpStartBtn.addEventListener('click', closeHelp);

        // Auto show on first visit
        if (!localStorage.getItem('starblazer_rules_read')) {
            setTimeout(openHelp, 800);
        }

        // Load handedness preference
        const isLeft = localStorage.getItem('leftHanded') === 'true';
        const gameLayout = document.querySelector('.game-layout');
        if (gameLayout && isLeft) {
            gameLayout.classList.add('left-handed');
        }

        // Controls
        // Controls
        const onlineBtn = document.getElementById('online-btn');
        if (onlineBtn) {
            onlineBtn.addEventListener('click', () => {
                if (state.onlineRole !== null) {
                    if (confirm('Disconnect from current game?')) {
                        resetToOffline();
                    }
                } else {
                    resetLobbyScreens();
                    updateProgressionUI();
                    document.getElementById('lobby-modal').style.display = '';
                }
            });
        }

        document.getElementById('reset-btn').addEventListener('click', () => {
            stopAllAutoplayTimers();
            resetGame();
        });
        document.getElementById('undo-btn').addEventListener('click', () => {
            stopCurrentPlayerAuto();
            undoMove();
        });
        document.getElementById('game-over-btn').addEventListener('click', () => {
            stopAllAutoplayTimers();
            resetGame();
        });

        // Player Type Toggles
        for (const p of [1, 2]) {
            const typeBtn = document.getElementById(`p${p}-type-btn`);
            if (typeBtn) {
                typeBtn.addEventListener('click', (e) => {
                    e.stopPropagation();
                    togglePlayerAuto(p);
                });
            }
        }

        initThemeSelector();

        // Close color pickers when clicking outside
        document.addEventListener('click', () => {
            for (const p of [1, 2]) {
                const wrapper = document.getElementById(`player${p}-chip-wrapper`);
                if (wrapper) wrapper.classList.remove('open');
            }
        });

        for (const p of [1, 2]) {
            initDrawerRowClicks(p);
            initSwatches(p);
            initColorPickerFan(p);
        }

        initLobbyEventListeners();
        initPlayerNames();

        // Keyboard shortcuts
        document.addEventListener('keydown', (e) => {
            if (e.ctrlKey && e.key === 'z') {
                stopCurrentPlayerAuto();
                e.preventDefault();
                undoMove();
            }
        });

        // Initialize viewBox center zoom
        targetViewBox = { x: -144, y: -144, w: 288, h: 288 };
        currentViewBox = { x: -300, y: -250, w: 600, h: 500 };
        animateViewBox();

        refreshUI();
        updateProgressionUI();

        // Copy canvas on click
        const hostWrapper = document.getElementById('host-avatar-wrapper');
        if (hostWrapper) {
            hostWrapper.addEventListener('click', (e) => {
                e.stopPropagation();
                const hostCanvas = document.getElementById('host-avatar-canvas');
                if (hostCanvas && currentInviteToken) {
                    copyCanvasToClipboard(hostCanvas, currentInviteToken);
                }
            });
        }
        const guestWrapper = document.getElementById('guest-avatar-wrapper');
        if (guestWrapper) {
            guestWrapper.addEventListener('click', (e) => {
                e.stopPropagation();
                const guestCanvas = document.getElementById('guest-avatar-canvas');
                if (guestCanvas && currentAnswerToken) {
                    copyCanvasToClipboard(guestCanvas, currentAnswerToken);
                }
            });
        }

        // Global paste listener
        document.addEventListener('paste', async (e) => {
            const lobbyModal = document.getElementById('lobby-modal');
            if (!lobbyModal || lobbyModal.style.display === 'none') return;

            const items = (e.clipboardData || window.clipboardData).items;
            for (const item of items) {
                if (item.type.indexOf('image') === 0) {
                    const file = item.getAsFile();
                    if (file) {
                        try {
                            showToast("Processing pasted image...");
                            const token = await decodeTokenFromImageFile(file);
                            if (token.startsWith("SB_OFFER:")) {
                                await initGuestWebRTC(token);
                            } else if (token.startsWith("SB_ANSWER:")) {
                                await handleGuestAnswer(token);
                            }
                        } catch (err) {
                            console.error("Paste image token decode failed:", err);
                        }
                    }
                } else if (item.kind === 'string' && item.type === 'text/plain') {
                    item.getAsString(async (text) => {
                        const code = text.trim();
                        if (code.startsWith("SB_OFFER:")) {
                            showToast("Pasted connection code!");
                            await initGuestWebRTC(code);
                        } else if (code.startsWith("SB_ANSWER:")) {
                            showToast("Pasted connection code!");
                            await handleGuestAnswer(code);
                        }
                    });
                }
            }
        });
    }

    // ═══════════════════════════════════════════════════════════
    // Camera Navigation: Pan & Zoom
    // ═══════════════════════════════════════════════════════════

    function initCameraControls() {
        const boardFrame = document.querySelector('.board-frame');
        const recenterBtn = document.getElementById('recenter-btn');
        const zoomInBtn = document.getElementById('zoom-in-btn');
        const zoomOutBtn = document.getElementById('zoom-out-btn');
        
        let isPointerDown = false;
        let startPointer = { x: 0, y: 0 };
        let startViewBox = { x: 0, y: 0 };
        let activeTouchPoints = new Map(); // For pinch zoom: pointerId -> clientX/Y

        function updateRecenterButton() {
            if (recenterBtn) {
                recenterBtn.classList.toggle('active', state.isManualCamera);
            }
        }

        function triggerManualCamera() {
            state.isManualCamera = true;
            updateRecenterButton();
        }

        // --- Recenter ---
        if (recenterBtn) {
            recenterBtn.addEventListener('click', (e) => {
                e.stopPropagation();
                state.isManualCamera = false;
                updateRecenterButton();
                updateCellVisibilities(); // Recalculate auto-viewbox and transition back
            });
        }

        // --- Zooming via Buttons ---
        function zoom(amount) {
            triggerManualCamera();
            const wChange = targetViewBox.w * amount;
            const hChange = targetViewBox.h * amount;
            
            targetViewBox.w += wChange;
            targetViewBox.h += hChange;
            
            // Adjust x and y to zoom relative to center
            targetViewBox.x -= wChange / 2;
            targetViewBox.y -= hChange / 2;

            if (!viewBoxAnimationId) {
                viewBoxAnimationId = requestAnimationFrame(animateViewBox);
            }
        }

        if (zoomInBtn) {
            zoomInBtn.addEventListener('click', (e) => {
                e.stopPropagation();
                zoom(-0.2); // Zoom in by 20%
            });
        }
        if (zoomOutBtn) {
            zoomOutBtn.addEventListener('click', (e) => {
                e.stopPropagation();
                zoom(0.25); // Zoom out by 25%
            });
        }

        // --- Wheel Zoom ---
        boardFrame.addEventListener('wheel', (e) => {
            e.preventDefault();
            triggerManualCamera();
            
            const zoomSpeed = 0.08;
            const factor = e.deltaY > 0 ? (1 + zoomSpeed) : (1 - zoomSpeed);
            
            // Zoom centered on the cursor position
            const rect = boardFrame.getBoundingClientRect();
            const mouseX = e.clientX - rect.left;
            const mouseY = e.clientY - rect.top;
            
            // Convert cursor position to percentages within the viewBox
            const px = mouseX / rect.width;
            const py = mouseY / rect.height;
            
            const oldW = targetViewBox.w;
            const oldH = targetViewBox.h;
            
            targetViewBox.w *= factor;
            targetViewBox.h *= factor;
            
            // Shift x and y so the point under the mouse cursor remains static
            targetViewBox.x += (oldW - targetViewBox.w) * px;
            targetViewBox.y += (oldH - targetViewBox.h) * py;

            // Enforce reasonable zoom limits
            const minW = 100;
            const maxW = 2000;
            if (targetViewBox.w < minW) {
                const ratio = minW / targetViewBox.w;
                targetViewBox.w = minW;
                targetViewBox.h = minW * (rect.height / rect.width || 1);
                targetViewBox.x += (targetViewBox.w * (1 - ratio)) * px;
                targetViewBox.y += (targetViewBox.h * (1 - ratio)) * py;
            } else if (targetViewBox.w > maxW) {
                const ratio = maxW / targetViewBox.w;
                targetViewBox.w = maxW;
                targetViewBox.h = maxW * (rect.height / rect.width || 1);
                targetViewBox.x += (targetViewBox.w * (1 - ratio)) * px;
                targetViewBox.y += (targetViewBox.h * (1 - ratio)) * py;
            }

            if (!viewBoxAnimationId) {
                viewBoxAnimationId = requestAnimationFrame(animateViewBox);
            }
        }, { passive: false });

        // --- Panning & Pinch-to-Zoom (Touch) ---
        boardFrame.addEventListener('pointerdown', (e) => {
            if (e.target.closest('.camera-controls')) return;
            if (e.target.closest('.player-panel')) return;

            activeTouchPoints.set(e.pointerId, { x: e.clientX, y: e.clientY });

            if (activeTouchPoints.size === 1) {
                isPointerDown = true;
                startPointer = { x: e.clientX, y: e.clientY };
                startViewBox = { x: targetViewBox.x, y: targetViewBox.y };
                state.dragDistance = 0;
                state.isDragging = false;
            } else if (activeTouchPoints.size === 2) {
                isPointerDown = false;
                state.isDragging = false;
                const pts = Array.from(activeTouchPoints.values());
                state.lastPinchDist = Math.hypot(pts[0].x - pts[1].x, pts[0].y - pts[1].y);
            }
        });

        window.addEventListener('pointermove', (e) => {
            if (!activeTouchPoints.has(e.pointerId)) return;
            activeTouchPoints.set(e.pointerId, { x: e.clientX, y: e.clientY });
            
            if (activeTouchPoints.size === 1 && isPointerDown) {
                const dx = e.clientX - startPointer.x;
                const dy = e.clientY - startPointer.y;
                const totalDist = Math.hypot(dx, dy);
                state.dragDistance = totalDist;

                if (totalDist > 6) {
                    state.isDragging = true;
                    triggerManualCamera();
                    
                    const rect = boardFrame.getBoundingClientRect();
                    const scaleX = targetViewBox.w / rect.width;
                    const scaleY = targetViewBox.h / rect.height;
                    
                    targetViewBox.x = startViewBox.x - dx * scaleX;
                    targetViewBox.y = startViewBox.y - dy * scaleY;
                    
                    if (!viewBoxAnimationId) {
                        viewBoxAnimationId = requestAnimationFrame(animateViewBox);
                    }
                }
            } else if (activeTouchPoints.size === 2) {
                triggerManualCamera();
                const pts = Array.from(activeTouchPoints.values());
                const dist = Math.hypot(pts[0].x - pts[1].x, pts[0].y - pts[1].y);
                
                if (state.lastPinchDist) {
                    const factor = state.lastPinchDist / dist;
                    const rect = boardFrame.getBoundingClientRect();
                    const midX = ((pts[0].x + pts[1].x) / 2) - rect.left;
                    const midY = ((pts[0].y + pts[1].y) / 2) - rect.top;
                    
                    const px = midX / rect.width;
                    const py = midY / rect.height;
                    
                    const oldW = targetViewBox.w;
                    const oldH = targetViewBox.h;
                    
                    targetViewBox.w *= factor;
                    targetViewBox.h *= factor;
                    
                    targetViewBox.x += (oldW - targetViewBox.w) * px;
                    targetViewBox.y += (oldH - targetViewBox.h) * py;
                    
                    const minW = 100;
                    const maxW = 2000;
                    if (targetViewBox.w < minW) {
                        targetViewBox.w = minW;
                        targetViewBox.h = minW * (rect.height / rect.width || 1);
                    } else if (targetViewBox.w > maxW) {
                        targetViewBox.w = maxW;
                        targetViewBox.h = maxW * (rect.height / rect.width || 1);
                    }
                    
                    if (!viewBoxAnimationId) {
                        viewBoxAnimationId = requestAnimationFrame(animateViewBox);
                    }
                }
                state.lastPinchDist = dist;
            }
        });

        const handlePointerUp = (e) => {
            if (!activeTouchPoints.has(e.pointerId)) return;
            activeTouchPoints.delete(e.pointerId);
            
            if (activeTouchPoints.size === 0) {
                if (state.isDragging) {
                    state.wasJustDragging = true;
                    setTimeout(() => { state.wasJustDragging = false; }, 50);
                }
                isPointerDown = false;
                state.isDragging = false;
            } else if (activeTouchPoints.size === 1) {
                isPointerDown = true;
                const remaining = Array.from(activeTouchPoints.values())[0];
                startPointer = { x: remaining.x, y: remaining.y };
                startViewBox = { x: targetViewBox.x, y: targetViewBox.y };
                state.lastPinchDist = null;
            }
        };

        window.addEventListener('pointerup', handlePointerUp);
        window.addEventListener('pointercancel', handlePointerUp);
    }

    // ═══════════════════════════════════════════════════════════
    // Multiplayer WebRTC PeerJS P2P Integration
    // ═══════════════════════════════════════════════════════════

    let toastTimer = null;
    let reconnectTimeout = null;
    let currentInviteToken = null;
    let currentAnswerToken = null;
    let hostInviteBlob = null;
    let guestAnswerBlob = null;

    const SEPARATOR_STR = "__STARBLAZER_DATA__";
    const encoder = new TextEncoder();
    const decoder = new TextDecoder();

    function generateLobbyId() {
        const chars = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789';
        let res = '';
        for (let i = 0; i < 8; i++) {
            res += chars.charAt(Math.floor(Math.random() * chars.length));
        }
        return res;
    }

    function createSeededRandom(seedString) {
        let hash = 0;
        for (let i = 0; i < seedString.length; i++) {
            hash = seedString.charCodeAt(i) + ((hash << 5) - hash);
        }
        return function() {
            let x = Math.sin(hash++) * 10000;
            return x - Math.floor(x);
        };
    }

    function drawSpaceBeaconAvatar(canvas, role, primaryColor, lobbyId) {
        const ctx = canvas.getContext('2d');
        const w = canvas.width;
        const h = canvas.height;
        
        // 1. Draw space background
        const grad = ctx.createRadialGradient(w/2, h/2, 10, w/2, h/2, w*0.7);
        grad.addColorStop(0, '#100a26');
        grad.addColorStop(1, '#05030f');
        ctx.fillStyle = grad;
        ctx.fillRect(0, 0, w, h);
        
        // 2. Draw stars (deterministic based on lobbyId)
        const seed = lobbyId || "starblazer";
        const random = createSeededRandom(seed);
        ctx.fillStyle = '#ffffff';
        for (let i = 0; i < 40; i++) {
            const sx = random() * w;
            const sy = random() * h;
            const size = random() * 2 + 0.5;
            const alpha = random() * 0.7 + 0.3;
            ctx.globalAlpha = alpha;
            ctx.beginPath();
            ctx.arc(sx, sy, size, 0, Math.PI * 2);
            ctx.fill();
        }
        ctx.globalAlpha = 1.0;
        
        // 3. Draw radar grid/circles
        ctx.strokeStyle = 'rgba(139, 92, 246, 0.15)';
        ctx.lineWidth = 1;
        ctx.beginPath();
        ctx.arc(w/2, h/2, w*0.35, 0, Math.PI * 2);
        ctx.stroke();
        ctx.beginPath();
        ctx.arc(w/2, h/2, w*0.2, 0, Math.PI * 2);
        ctx.stroke();
        
        // Crosshairs
        ctx.beginPath();
        ctx.moveTo(w/2 - w*0.4, h/2); ctx.lineTo(w/2 + w*0.4, h/2);
        ctx.moveTo(w/2, h/2 - h*0.4); ctx.lineTo(w/2, h/2 + h*0.4);
        ctx.stroke();
        
        // 4. Draw Transmission Waves / Telemetry Rings
        const waveColor = role === 1 ? 'rgba(56, 189, 248, 0.6)' : 'rgba(239, 68, 68, 0.6)';
        ctx.strokeStyle = waveColor;
        ctx.lineWidth = 2;
        ctx.setLineDash([4, 4]);
        
        if (role === 1) { // Host: Ripples emitting from nose (pointing up)
            const noseY = h/2 - 50;
            for (let r = 15; r < 60; r += 15) {
                ctx.beginPath();
                ctx.arc(w/2, noseY, r, Math.PI * 1.2, Math.PI * 1.8);
                ctx.stroke();
            }
        } else { // Guest: Ripples converging to nose (pointing down)
            const noseY = h/2 + 50;
            for (let r = 15; r < 60; r += 15) {
                ctx.beginPath();
                ctx.arc(w/2, noseY, r, Math.PI * 0.2, Math.PI * 0.8);
                ctx.stroke();
            }
        }
        ctx.setLineDash([]); // Reset dash
        
        // 5. Draw Spaceship
        ctx.save();
        ctx.translate(w/2, h/2);
        if (role === 2) {
            ctx.rotate(Math.PI); // Rotate 180 deg for Guest (pointing down)
        }

        // Deterministic spaceship components based on seed
        const wingType = Math.floor(random() * 3);
        const thrusterType = Math.floor(random() * 3);
        const fuselageType = Math.floor(random() * 3);
        const canopyColor = Math.floor(random() * 3);

        const lvl = state.progression.level || 1;

        // EXTRA LEVEL 4 PART: Quantum Warp Ring (glowing energy ellipse behind ship body)
        if (lvl >= 4) {
            ctx.save();
            ctx.strokeStyle = role === 1 ? '#38bdf8' : '#f43f5e';
            ctx.shadowColor = role === 1 ? '#38bdf8' : '#f43f5e';
            ctx.shadowBlur = 10;
            ctx.lineWidth = 4;
            ctx.beginPath();
            ctx.ellipse(0, 10, 28, 12, 0, 0, Math.PI * 2);
            ctx.stroke();
            ctx.restore();
        }

        // EXTRA LEVEL 2 PART: Laser Cannons (underneath wings)
        if (lvl >= 2) {
            ctx.fillStyle = '#475569';
            // Left Cannon
            ctx.fillRect(-35, -20, 4, 35);
            // Right Cannon
            ctx.fillRect(31, -20, 4, 35);
            // Cannon tips (glow matching transmission wave color)
            ctx.fillStyle = role === 1 ? '#38bdf8' : '#ef4444';
            ctx.fillRect(-35, -23, 4, 3);
            ctx.fillRect(31, -23, 4, 3);
        }
        
        // WINGS
        ctx.fillStyle = primaryColor;
        ctx.beginPath();
        if (wingType === 0) {
            // Delta wing style
            ctx.moveTo(0, -50);
            ctx.lineTo(-45, 18);
            ctx.lineTo(-15, 28);
            ctx.lineTo(15, 28);
            ctx.lineTo(45, 18);
        } else if (wingType === 1) {
            // Forward swept style
            ctx.moveTo(0, -50);
            ctx.lineTo(-38, -5);
            ctx.lineTo(-46, 22);
            ctx.lineTo(-15, 22);
            ctx.lineTo(15, 22);
            ctx.lineTo(46, 22);
            ctx.lineTo(38, -5);
        } else {
            // Solar curve style
            ctx.moveTo(0, -50);
            ctx.quadraticCurveTo(-45, -5, -42, 26);
            ctx.lineTo(-15, 22);
            ctx.lineTo(15, 22);
            ctx.lineTo(42, 26);
            ctx.quadraticCurveTo(45, -5, 0, -50);
        }
        ctx.closePath();
        ctx.fill();
        
        // FUSELAGE
        ctx.fillStyle = '#cbd5e1';
        ctx.beginPath();
        if (fuselageType === 0) {
            // Standard fuselage
            ctx.moveTo(0, -55);
            ctx.lineTo(-12, 10);
            ctx.lineTo(-10, 40);
            ctx.lineTo(10, 40);
            ctx.lineTo(12, 10);
        } else if (fuselageType === 1) {
            // Armored Hex fuselage
            ctx.moveTo(0, -58);
            ctx.lineTo(-14, -15);
            ctx.lineTo(-15, 25);
            ctx.lineTo(-8, 42);
            ctx.lineTo(8, 42);
            ctx.lineTo(15, 25);
            ctx.lineTo(14, -15);
        } else {
            // Sleek Arrow fuselage
            ctx.moveTo(0, -62);
            ctx.lineTo(-10, 0);
            ctx.lineTo(-11, 38);
            ctx.lineTo(0, 45);
            ctx.lineTo(11, 38);
            ctx.lineTo(10, 0);
        }
        ctx.closePath();
        ctx.fill();
        
        // EXTRA LEVEL 3 PART: Heavy Armored Plates
        if (lvl >= 3) {
            ctx.fillStyle = '#94a3b8';
            ctx.beginPath();
            ctx.moveTo(-18, 5); ctx.lineTo(-30, 20); ctx.lineTo(-14, 24); ctx.closePath(); ctx.fill();
            ctx.beginPath();
            ctx.moveTo(18, 5); ctx.lineTo(30, 20); ctx.lineTo(14, 24); ctx.closePath(); ctx.fill();
        }

        // Wing trim
        ctx.fillStyle = 'rgba(255, 255, 255, 0.35)';
        ctx.beginPath();
        ctx.moveTo(0, -20);
        ctx.lineTo(-30, 15);
        ctx.lineTo(-15, 20);
        ctx.closePath();
        ctx.fill();
        ctx.beginPath();
        ctx.moveTo(0, -20);
        ctx.lineTo(30, 15);
        ctx.lineTo(15, 20);
        ctx.closePath();
        ctx.fill();
        
        // COCKPIT
        const cockGrad = ctx.createLinearGradient(0, -35, 0, -5);
        if (canopyColor === 0) {
            cockGrad.addColorStop(0, '#06b6d4'); // Cyan
            cockGrad.addColorStop(1, '#0891b2');
        } else if (canopyColor === 1) {
            cockGrad.addColorStop(0, '#10b981'); // Green
            cockGrad.addColorStop(1, '#059669');
        } else {
            cockGrad.addColorStop(0, '#f59e0b'); // Amber/Gold
            cockGrad.addColorStop(1, '#d97706');
        }
        ctx.fillStyle = cockGrad;
        ctx.beginPath();
        ctx.moveTo(0, -35);
        ctx.lineTo(-6, -10);
        ctx.lineTo(-4, 0);
        ctx.lineTo(4, 0);
        ctx.lineTo(6, -10);
        ctx.closePath();
        ctx.fill();
        
        // ENGINES & FIRE
        ctx.fillStyle = role === 1 ? '#00d2ff' : '#ff4e00';
        if (thrusterType === 0) {
            // Center main engine flame
            ctx.beginPath();
            ctx.moveTo(-6, 40);
            ctx.lineTo(0, 68);
            ctx.lineTo(6, 40);
            ctx.closePath();
            ctx.fill();
        } else if (thrusterType === 1) {
            // Dual thrusters
            ctx.beginPath();
            ctx.moveTo(-15, 30); ctx.lineTo(-18, 55); ctx.lineTo(-10, 32); ctx.closePath(); ctx.fill();
            ctx.beginPath();
            ctx.moveTo(15, 30); ctx.lineTo(18, 55); ctx.lineTo(10, 32); ctx.closePath(); ctx.fill();
        } else {
            // Triple thruster cluster
            ctx.beginPath();
            ctx.moveTo(-15, 30); ctx.lineTo(-17, 52); ctx.lineTo(-11, 32); ctx.closePath(); ctx.fill();
            ctx.beginPath();
            ctx.moveTo(15, 30); ctx.lineTo(17, 52); ctx.lineTo(11, 32); ctx.closePath(); ctx.fill();
            ctx.beginPath();
            ctx.moveTo(-5, 40); ctx.lineTo(0, 64); ctx.lineTo(5, 40); ctx.closePath(); ctx.fill();
        }

        // EXTRA LEVEL 5 PART: Flagship antennae and emblem
        if (lvl >= 5) {
            ctx.strokeStyle = '#cbd5e1';
            ctx.lineWidth = 1.5;
            // Nose spike antenna
            ctx.beginPath(); ctx.moveTo(0, -55); ctx.lineTo(0, -78); ctx.stroke();
            // Sensor tip
            ctx.fillStyle = '#f59e0b';
            ctx.beginPath(); ctx.arc(0, -80, 2, 0, Math.PI * 2); ctx.fill();

            // Wing spike antennae
            ctx.beginPath(); ctx.moveTo(-40, 15); ctx.lineTo(-40, -5); ctx.stroke();
            ctx.beginPath(); ctx.moveTo(40, 15); ctx.lineTo(40, -5); ctx.stroke();
            
            // Faction emblem on nose
            ctx.fillStyle = '#f59e0b';
            ctx.beginPath();
            ctx.moveTo(0, 12); ctx.lineTo(-4, 20); ctx.lineTo(4, 20);
            ctx.closePath();
            ctx.fill();
        }
        
        ctx.restore();
        
        // 6. Draw HUD frame and text
        ctx.strokeStyle = 'rgba(139, 92, 246, 0.4)';
        ctx.lineWidth = 3;
        ctx.strokeRect(10, 10, w - 20, h - 20);
        
        // Frame brackets
        ctx.strokeStyle = '#8b5cf6';
        ctx.lineWidth = 5;
        const len = 20;
        ctx.beginPath(); ctx.moveTo(10, 10 + len); ctx.lineTo(10, 10); ctx.lineTo(10 + len, 10); ctx.stroke();
        ctx.beginPath(); ctx.moveTo(w - 10 - len, 10); ctx.lineTo(w - 10, 10); ctx.lineTo(w - 10, 10 + len); ctx.stroke();
        ctx.beginPath(); ctx.moveTo(10, h - 10 - len); ctx.lineTo(10, h - 10); ctx.lineTo(10 + len, h - 10); ctx.stroke();
        ctx.beginPath(); ctx.moveTo(w - 10 - len, h - 10); ctx.lineTo(w - 10, h - 10); ctx.lineTo(w - 10, h - 10 - len); ctx.stroke();
        
        ctx.fillStyle = '#a78bfa';
        ctx.font = '10px monospace';
        ctx.textAlign = 'center';
        ctx.fillText(role === 1 ? 'TRANSMITTING INVITE SIGNAL' : 'TRANSMITTING ANSWER SIGNAL', w/2, 25);
        
        ctx.fillStyle = '#a78bfa';
        ctx.fillText(`LOBBY: ${lobbyId}`, w/2, h - 20);
    }

    window.updateLobbyImageWithColor = function(player, color) {
        if (player === 1 && state.onlineRole === 1 && currentInviteToken) {
            const canvas = document.getElementById('host-avatar-canvas');
            if (canvas) {
                drawSpaceBeaconAvatar(canvas, 1, color, state.lobbyId);
                generateDownloadBlob(canvas, currentInviteToken, (blob) => {
                    hostInviteBlob = blob;
                });
            }
        } else if (player === 2 && state.onlineRole === 2 && currentAnswerToken) {
            const canvas = document.getElementById('guest-avatar-canvas');
            if (canvas) {
                drawSpaceBeaconAvatar(canvas, 2, color, state.lobbyId);
                generateDownloadBlob(canvas, currentAnswerToken, (blob) => {
                    guestAnswerBlob = blob;
                });
            }
        }
    };

    function generateDownloadBlob(canvas, token, callback) {
        canvas.toBlob(async (blob) => {
            if (!blob) return;
            try {
                const imageBuffer = await blob.arrayBuffer();
                const imageBytes = new Uint8Array(imageBuffer);
                const tokenWithSeparator = SEPARATOR_STR + token;
                const tokenBytes = encoder.encode(tokenWithSeparator);
                
                const combinedBytes = new Uint8Array(imageBytes.length + tokenBytes.length);
                combinedBytes.set(imageBytes, 0);
                combinedBytes.set(tokenBytes, imageBytes.length);
                
                const combinedBlob = new Blob([combinedBytes], { type: 'image/jpeg' });
                callback(combinedBlob);
            } catch (err) {
                console.error("Error creating combined blob:", err);
            }
        }, 'image/jpeg', 0.85);
    }

    function setPlayerAvatar(player, dataUrl) {
        state.playerAvatars[player] = dataUrl;

        const chipEl = document.getElementById(`player${player}-chip`);
        if (chipEl) {
            if (dataUrl) {
                chipEl.style.backgroundImage = `url(${dataUrl})`;
                chipEl.style.backgroundSize = 'cover';
                chipEl.style.backgroundColor = 'transparent';
                chipEl.style.border = '2px solid var(--accent)';
            } else {
                chipEl.style.backgroundImage = '';
                chipEl.style.backgroundColor = state.playerColors[player];
                chipEl.style.border = '';
            }
        }

        const defs = svgEl.querySelector('defs');
        if (defs) {
            const patternId = `player${player}-avatar-pattern`;
            let pattern = document.getElementById(patternId);
            if (dataUrl) {
                if (!pattern) {
                    pattern = document.createElementNS(CONFIG.SVG_NS, 'pattern');
                    pattern.setAttribute('id', patternId);
                    pattern.setAttribute('patternUnits', 'objectBoundingBox');
                    pattern.setAttribute('width', '1');
                    pattern.setAttribute('height', '1');
                    
                    const img = document.createElementNS(CONFIG.SVG_NS, 'image');
                    img.setAttribute('x', '0');
                    img.setAttribute('y', '0');
                    img.setAttribute('width', '100%');
                    img.setAttribute('height', '100%');
                    img.setAttribute('preserveAspectRatio', 'xMidYMid slice');
                    pattern.appendChild(img);
                    defs.appendChild(pattern);
                }
                const img = pattern.querySelector('image');
                if (img) {
                    img.setAttributeNS('http://www.w3.org/1999/xlink', 'href', dataUrl);
                }
            } else if (pattern) {
                pattern.remove();
            }
        }

        state.board.forEach((stack, key) => {
            const [cq, cr] = key.split(',').map(Number);
            renderCell(cq, cr);
        });

        if (state.onlineRole === player && state.conn && state.conn.open && !state.remoteActionInProgress) {
            sendNetworkMessage({ type: 'avatar', player, avatar: dataUrl });
        }
    }

    function updatePlayerName(player, name) {
        state.playerNames[player] = name;
        const el = document.querySelector(`#player${player}-card .player-name`);
        if (el) {
            el.textContent = name;
        }
    }

    function initPlayerNames() {
        for (const p of [1, 2]) {
            const el = document.querySelector(`#player${p}-card .player-name`);
            if (!el) continue;

            const handleNameSave = () => {
                let name = el.textContent.trim();
                if (!name) {
                    name = `Player ${p}`;
                    el.textContent = name;
                }
                if (state.playerNames[p] !== name) {
                    state.playerNames[p] = name;
                    // If online, send name update to peer
                    if (state.onlineRole === p && state.conn && state.conn.open && !state.remoteActionInProgress) {
                        sendNetworkMessage({ type: 'name_change', player: p, name });
                    }
                }
            };

            el.addEventListener('blur', handleNameSave);

            el.addEventListener('keydown', (e) => {
                if (e.key === 'Enter') {
                    e.preventDefault();
                    el.blur();
                }
            });
        }
    }

    function calculateLevel() {
        const wins = state.progression.wins;
        const moves = state.progression.moves;
        let lvl = 1;
        if (moves >= 100 || wins >= 5) lvl = 5;
        else if (moves >= 60 || wins >= 3) lvl = 4;
        else if (moves >= 30 || wins >= 2) lvl = 3;
        else if (moves >= 10 || wins >= 1) lvl = 2;
        
        state.progression.level = lvl;
        return lvl;
    }

    function updateProgressionUI() {
        const lvl = calculateLevel();
        const levelEl = document.getElementById('pilot-level');
        const movesEl = document.getElementById('pilot-moves');
        const winsEl = document.getElementById('pilot-wins');
        const nextUnlockEl = document.getElementById('pilot-next-unlock');
        
        if (levelEl) levelEl.textContent = lvl;
        if (movesEl) movesEl.textContent = state.progression.moves;
        if (winsEl) winsEl.textContent = state.progression.wins;
        
        if (nextUnlockEl) {
            if (lvl === 1) {
                nextUnlockEl.textContent = "Next: Laser Cannons 🔫 (10 moves / 1 win)";
            } else if (lvl === 2) {
                nextUnlockEl.textContent = "Next: Heavy Armor Plates 🛡 (30 moves / 2 wins)";
            } else if (lvl === 3) {
                nextUnlockEl.textContent = "Next: Quantum Warp Rings 🌀 (60 moves / 3 wins)";
            } else if (lvl === 4) {
                nextUnlockEl.textContent = "Next: Flagship Antennas 📡 (100 moves / 5 wins)";
            } else {
                nextUnlockEl.textContent = "Rank Maxed! 🏆 Elite Flagship unlocked!";
            }
        }
    }

    function convertToPngBlob(dataUrl) {
        return new Promise((resolve, reject) => {
            const img = new Image();
            img.onload = () => {
                const canvas = document.createElement('canvas');
                canvas.width = img.width;
                canvas.height = img.height;
                const ctx = canvas.getContext('2d');
                ctx.drawImage(img, 0, 0);
                canvas.toBlob((blob) => {
                    if (blob) resolve(blob);
                    else reject(new Error("Blob conversion failed"));
                }, 'image/png');
            };
            img.onerror = () => reject(new Error("Image load failed"));
            img.src = dataUrl;
        });
    }

    function copyCanvasToClipboard(canvas, token) {
        canvas.toBlob(async (blob) => {
            if (!blob) return;
            try {
                const clipboardItems = {
                    'image/png': blob
                };
                if (token) {
                    clipboardItems['text/plain'] = new Blob([token], { type: 'text/plain' });
                }
                await navigator.clipboard.write([new ClipboardItem(clipboardItems)]);
                showToast("Copied spaceship avatar and connection code to clipboard!");
            } catch (err) {
                console.error("Clipboard API failed:", err);
                if (token) {
                    navigator.clipboard.writeText(token).then(() => {
                        showToast("Copied connection code to clipboard!");
                    });
                } else {
                    showToast("Failed to copy avatar.");
                }
            }
        }, 'image/png');
    }

    async function copyDataUrlToClipboard(dataUrl, token) {
        try {
            const pngBlob = await convertToPngBlob(dataUrl);
            const clipboardItems = {
                'image/png': pngBlob
            };
            if (token) {
                clipboardItems['text/plain'] = new Blob([token], { type: 'text/plain' });
            }
            await navigator.clipboard.write([new ClipboardItem(clipboardItems)]);
            showToast("Copied avatar to clipboard!");
        } catch (err) {
            console.error("DataURL clipboard copy failed:", err);
            if (token) {
                navigator.clipboard.writeText(token).then(() => {
                    showToast("Copied connection code to clipboard!");
                });
            } else {
                showToast("Failed to copy avatar.");
            }
        }
    }

    function decodeTokenFromImageFile(file) {
        return new Promise((resolve, reject) => {
            const reader = new FileReader();
            reader.onload = function (e) {
                try {
                    const bytes = new Uint8Array(e.target.result);
                    const separatorBytes = encoder.encode(SEPARATOR_STR);
                    let foundIndex = -1;
                    
                    const searchStart = Math.max(0, bytes.length - 131072); // search last 128KB only
                    for (let i = bytes.length - separatorBytes.length; i >= searchStart; i--) {
                        let match = true;
                        for (let j = 0; j < separatorBytes.length; j++) {
                            if (bytes[i + j] !== separatorBytes[j]) {
                                match = false;
                                break;
                            }
                        }
                        if (match) {
                            foundIndex = i;
                            break;
                        }
                    }

                    if (foundIndex === -1) {
                        reject(new Error("This image does not contain a valid connection key. Make sure you uploaded the original file sent by your friend."));
                        return;
                    }

                    const tokenStartIndex = foundIndex + separatorBytes.length;
                    const tokenBytes = bytes.subarray(tokenStartIndex);
                    const token = decoder.decode(tokenBytes).trim();
                    resolve(token);
                } catch (err) {
                    reject(err);
                }
            };
            reader.onerror = () => reject(new Error("Failed to read file."));
            reader.readAsArrayBuffer(file);
        });
    }

    async function compressString(str) {
        try {
            const stream = new Blob([str]).stream();
            const compressedStream = stream.pipeThrough(new CompressionStream('gzip'));
            const response = new Response(compressedStream);
            const blob = await response.blob();
            const buffer = await blob.arrayBuffer();
            let binary = '';
            const bytes = new Uint8Array(buffer);
            for (let i = 0; i < bytes.byteLength; i++) {
                binary += String.fromCharCode(bytes[i]);
            }
            return "GZ:" + btoa(binary);
        } catch (e) {
            console.warn("CompressionStream not supported, using base64 fallback:", e);
            return "RAW:" + btoa(unescape(encodeURIComponent(str)));
        }
    }

    async function decompressString(token) {
        if (token.startsWith("GZ:")) {
            const base64Str = token.substring(3);
            const binary = atob(base64Str.trim());
            const bytes = new Uint8Array(binary.length);
            for (let i = 0; i < binary.length; i++) {
                bytes[i] = binary.charCodeAt(i);
            }
            const stream = new Blob([bytes]).stream();
            const decompressedStream = stream.pipeThrough(new DecompressionStream('gzip'));
            const response = new Response(decompressedStream);
            const blob = await response.blob();
            return await blob.text();
        } else if (token.startsWith("RAW:")) {
            const base64Str = token.substring(4);
            return decodeURIComponent(escape(atob(base64Str)));
        } else {
            try {
                return atob(token);
            } catch (e) {
                return token;
            }
        }
    }

    const rtcConfig = {
        iceServers: [
            { urls: 'stun:stun.l.google.com:19302' },
            { urls: 'stun:stun1.l.google.com:19302' },
            { urls: 'stun:stun2.l.google.com:19302' },
            { urls: 'stun:stun3.l.google.com:19302' },
            { urls: 'stun:stun4.l.google.com:19302' }
        ]
    };

    async function initHostWebRTC() {
        try {
            state.onlineRole = 1;
            state.lobbyId = generateLobbyId();
            
            cleanupWebRTC();

            console.log("Initializing Host WebRTC (Lobby ID:", state.lobbyId, ")...");
            
            document.getElementById('host-initial-container').style.display = 'none';
            document.getElementById('host-active-container').style.display = 'block';
            document.getElementById('host-qr-spinner').style.display = 'flex';
            document.getElementById('host-qr-spinner-text').textContent = 'Gathering network candidates...';
            
            // Hide guest side and divider
            const divider = document.getElementById('lobby-divider');
            if (divider) divider.style.display = 'none';
            const guestSide = document.getElementById('lobby-guest-side');
            if (guestSide) guestSide.style.display = 'none';
            
            // Draw and show host spaceship avatar instantly
            const canvas = document.getElementById('host-avatar-canvas');
            if (canvas) {
                drawSpaceBeaconAvatar(canvas, 1, state.playerColors[1], state.lobbyId);
            }
            document.getElementById('host-avatar-wrapper').style.display = 'block';
            
            document.getElementById('host-actions-row').style.display = 'none';
            document.getElementById('host-response-section').style.display = 'block';

            const pc = new RTCPeerConnection(rtcConfig);
            state.pc = pc;

            const dc = pc.createDataChannel("starblazer-data", { negotiated: false });
            state.conn = dc;
            setupDataChannelEvents(dc);

            pc.oniceconnectionstatechange = () => {
                console.log("ICE Connection State Change:", pc.iceConnectionState);
                if (pc.iceConnectionState === 'connected') {
                    showToast("Opponent connected! Game starting.");
                    updateLobbyUIForConnected();
                } else if (pc.iceConnectionState === 'disconnected' || pc.iceConnectionState === 'failed') {
                    showToast("Opponent disconnected. Reverting to local play.");
                    resetToOffline();
                }
            };

            const offer = await pc.createOffer();
            await pc.setLocalDescription(offer);

            // Wait for ICE candidates with a 3.5-second timeout to prevent freezes
            await new Promise((resolve) => {
                let resolved = false;
                const done = () => {
                    if (resolved) return;
                    resolved = true;
                    pc.removeEventListener('icegatheringstatechange', checkState);
                    pc.removeEventListener('icecandidate', checkCandidate);
                    clearTimeout(timeoutId);
                    resolve();
                };
                
                const timeoutId = setTimeout(done, 3500);
                
                const checkState = () => {
                    if (pc.iceGatheringState === 'complete') {
                        done();
                    }
                };
                const checkCandidate = (e) => {
                    if (!e.candidate) {
                        done();
                    }
                };
                
                if (pc.iceGatheringState === 'complete') {
                    done();
                } else {
                    pc.addEventListener('icegatheringstatechange', checkState);
                    pc.addEventListener('icecandidate', checkCandidate);
                }
            });

            // Package metadata into the compressed token
            const offerMetadata = {
                sdp: pc.localDescription.sdp,
                color: state.playerColors[1],
                name: state.playerNames[1],
                lobbyId: state.lobbyId
            };
            const compressed = await compressString(JSON.stringify(offerMetadata));
            const offerToken = "SB_OFFER:" + compressed;

            currentInviteToken = offerToken;

            // Render spaceship avatar
            if (canvas) {
                drawSpaceBeaconAvatar(canvas, 1, state.playerColors[1], state.lobbyId);
                generateDownloadBlob(canvas, offerToken, (blob) => {
                    hostInviteBlob = blob;
                });
            }

            document.getElementById('host-qr-spinner').style.display = 'none';
            document.getElementById('host-avatar-wrapper').style.display = 'block';
            document.getElementById('host-actions-row').style.display = 'flex';
            document.getElementById('host-response-section').style.display = 'block';
            document.getElementById('raw-code-out').value = offerToken;

        } catch (err) {
            console.error("Host initialization error:", err);
            showToast("Failed to initialize lobby: " + err.message);
            resetToOffline();
        }
    }

    async function initGuestWebRTC(offerToken) {
        try {
            state.onlineRole = 2;

            if (!offerToken.startsWith("SB_OFFER:")) {
                throw new Error("Invalid connection code. Make sure it is an Invite code.");
            }

            // Decompress and parse Host offer metadata
            const compressed = offerToken.replace("SB_OFFER:", "").trim();
            const decodedJSON = await decompressString(compressed);
            let offerMetadata;
            try {
                offerMetadata = JSON.parse(decodedJSON);
            } catch (e) {
                offerMetadata = { sdp: decodedJSON, color: state.playerColors[1], name: 'Host Player', lobbyId: 'SB-GUEST' };
            }

            state.lobbyId = offerMetadata.lobbyId || 'SB-LOBBY';
            updatePlayerColor(1, offerMetadata.color || '#1a1a1a');
            updateSwatchUI(1, offerMetadata.color || '#1a1a1a');
            updatePlayerName(1, offerMetadata.name || 'Player 1');

            cleanupWebRTC();

            console.log("Initializing Guest WebRTC for Lobby ID:", state.lobbyId);
            
            document.getElementById('guest-initial-container').style.display = 'none';
            document.getElementById('guest-active-container').style.display = 'block';
            document.getElementById('guest-qr-spinner').style.display = 'flex';
            
            // Hide host side and divider
            const divider = document.getElementById('lobby-divider');
            if (divider) divider.style.display = 'none';
            const hostSide = document.getElementById('lobby-host-side');
            if (hostSide) hostSide.style.display = 'none';
            
            const guestSpinnerText = document.getElementById('guest-qr-spinner-text');
            if (guestSpinnerText) {
                guestSpinnerText.textContent = 'Gathering network candidates...';
            }
            
            // Draw and show guest spaceship avatar instantly
            const canvas = document.getElementById('guest-avatar-canvas');
            if (canvas) {
                drawSpaceBeaconAvatar(canvas, 2, state.playerColors[2], state.lobbyId);
            }
            document.getElementById('guest-avatar-wrapper').style.display = 'block';
            document.getElementById('guest-actions-row').style.display = 'none';
            
            const guestStatus = document.getElementById('guest-status-text');
            if (guestStatus) {
                guestStatus.style.display = 'none';
            }

            const pc = new RTCPeerConnection(rtcConfig);
            state.pc = pc;

            pc.ondatachannel = (e) => {
                console.log("Received remote data channel!");
                state.conn = e.channel;
                setupDataChannelEvents(state.conn);
                showToast("Connected to player! Game starting.");
                updateLobbyUIForConnected();
            };

            pc.oniceconnectionstatechange = () => {
                console.log("ICE Connection State Change (Guest):", pc.iceConnectionState);
                if (pc.iceConnectionState === 'disconnected' || pc.iceConnectionState === 'failed') {
                    showToast("Opponent disconnected. Reverting to local play.");
                    resetToOffline();
                }
            };

            await pc.setRemoteDescription(new RTCSessionDescription({ type: 'offer', sdp: offerMetadata.sdp }));

            const answer = await pc.createAnswer();
            await pc.setLocalDescription(answer);

            // Wait for ICE candidates with a 3.5-second timeout to prevent freezes
            await new Promise((resolve) => {
                let resolved = false;
                const done = () => {
                    if (resolved) return;
                    resolved = true;
                    pc.removeEventListener('icegatheringstatechange', checkState);
                    pc.removeEventListener('icecandidate', checkCandidate);
                    clearTimeout(timeoutId);
                    resolve();
                };
                
                const timeoutId = setTimeout(done, 3500);
                
                const checkState = () => {
                    if (pc.iceGatheringState === 'complete') {
                        done();
                    }
                };
                const checkCandidate = (e) => {
                    if (!e.candidate) {
                        done();
                    }
                };
                
                if (pc.iceGatheringState === 'complete') {
                    done();
                } else {
                    pc.addEventListener('icegatheringstatechange', checkState);
                    pc.addEventListener('icecandidate', checkCandidate);
                }
            });

            // Package Guest metadata
            const answerMetadata = {
                sdp: pc.localDescription.sdp,
                color: state.playerColors[2],
                name: state.playerNames[2]
            };
            const compressedAnswer = await compressString(JSON.stringify(answerMetadata));
            const answerToken = "SB_ANSWER:" + compressedAnswer;

            currentAnswerToken = answerToken;

            // Render Guest spaceship avatar
            if (canvas) {
                drawSpaceBeaconAvatar(canvas, 2, state.playerColors[2], state.lobbyId);
                generateDownloadBlob(canvas, answerToken, (blob) => {
                    guestAnswerBlob = blob;
                });
            }

            document.getElementById('guest-qr-spinner').style.display = 'none';
            document.getElementById('guest-avatar-wrapper').style.display = 'block';
            document.getElementById('guest-actions-row').style.display = 'flex';
            document.getElementById('raw-code-out').value = answerToken;

            if (guestStatus) {
                guestStatus.style.display = 'block';
            }

        } catch (err) {
            console.error("Guest initialization error:", err);
            showToast("Failed to join lobby: " + err.message);
            resetToOffline();
        }
    }

    async function handleGuestAnswer(answerToken) {
        try {
            if (!state.pc) {
                throw new Error("Lobby is not initialized.");
            }
            if (!answerToken.startsWith("SB_ANSWER:")) {
                throw new Error("Invalid connection code. Make sure it is an Answer code.");
            }

            const compressed = answerToken.replace("SB_ANSWER:", "").trim();
            const decodedJSON = await decompressString(compressed);
            let answerMetadata;
            try {
                answerMetadata = JSON.parse(decodedJSON);
            } catch (e) {
                answerMetadata = { sdp: decodedJSON, color: state.playerColors[2], name: 'Guest Player' };
            }

            updatePlayerColor(2, answerMetadata.color || '#d4b896');
            updateSwatchUI(2, answerMetadata.color || '#d4b896');
            updatePlayerName(2, answerMetadata.name || 'Player 2');

            console.log("Setting remote description (Guest Answer)...");
            await state.pc.setRemoteDescription(new RTCSessionDescription({ type: 'answer', sdp: answerMetadata.sdp }));
            
            showToast("Connecting to peer...");
        } catch (err) {
            console.error("Error setting answer:", err);
            showToast("Failed to connect: " + err.message);
        }
    }

    function cleanupWebRTC() {
        if (state.conn) {
            state.conn.onopen = null;
            state.conn.onmessage = null;
            state.conn.onclose = null;
            state.conn.onerror = null;
            try {
                state.conn.close();
            } catch (e) {}
            state.conn = null;
        }
        if (state.pc) {
            state.pc.oniceconnectionstatechange = null;
            state.pc.ondatachannel = null;
            try {
                state.pc.close();
            } catch (e) {}
            state.pc = null;
        }
    }

    function setupDataChannelEvents(dc) {
        dc.onopen = () => {
            console.log("Data channel opened successfully!");
            state.playerAuto = { 1: false, 2: false };
            stopAllAutoplayTimers();
            
            if (state.onlineRole === 1) {
                setTimeout(() => {
                    sendStateSync();
                }, 500);
            }
            refreshUI();
        };

        dc.onmessage = (e) => {
            console.log("Received data channel message:", e.data);
            try {
                const data = JSON.parse(e.data);
                handleIncomingMessage(data);
            } catch (err) {
                console.error("Error parsing message:", err);
            }
        };

        dc.onclose = () => {
            console.log("Data channel closed.");
            showToast("Opponent disconnected. Reverting to local play.");
            resetToOffline();
        };

        dc.onerror = (err) => {
            console.error("Data channel error:", err);
            showToast("Connection lost. Reverting to local play.");
            resetToOffline();
        };
    }

    function resetLobbyScreens() {
        const setDisplay = (id, val) => {
            const el = document.getElementById(id);
            if (el) el.style.display = val;
        };
        const setText = (id, val) => {
            const el = document.getElementById(id);
            if (el) el.textContent = val;
        };
        const setValue = (id, val) => {
            const el = document.getElementById(id);
            if (el) el.value = val;
        };

        setDisplay('host-initial-container', 'block');
        setDisplay('host-active-container', 'none');
        setDisplay('guest-initial-container', 'block');
        setDisplay('guest-active-container', 'none');
        setDisplay('lobby-text-fallback', 'none');
        
        setDisplay('lobby-divider', 'block');
        setDisplay('lobby-host-side', 'flex');
        setDisplay('lobby-guest-side', 'flex');
        
        setDisplay('host-qr-spinner', 'flex');
        setText('host-qr-spinner-text', 'Gathering network candidates...');
        setDisplay('host-avatar-wrapper', 'none');
        setDisplay('host-actions-row', 'none');
        setDisplay('host-response-section', 'none');
        
        setDisplay('guest-qr-spinner', 'flex');
        setText('guest-qr-spinner-text', 'Preparing Answer Beacon...');
        setDisplay('guest-avatar-wrapper', 'none');
        setDisplay('guest-actions-row', 'none');
        setDisplay('guest-status-text', 'none');
        
        setText('host-dropzone-text', 'Drop Answer Beacon here or click to browse');
        setText('guest-dropzone-text', 'Drop Invite Beacon here or click to browse');
        
        setValue('raw-code-out', '');
        setValue('raw-code-in', '');
        setDisplay('text-inputs-container', 'none');

        currentInviteToken = null;
        currentAnswerToken = null;
        hostInviteBlob = null;
        guestAnswerBlob = null;
    }

    function initLobbyEventListeners() {
        document.getElementById('role-host-btn').addEventListener('click', () => {
            initHostWebRTC();
        });

        document.getElementById('lobby-close-btn').addEventListener('click', () => {
            resetToOffline();
        });

        document.getElementById('host-download-btn').addEventListener('click', () => {
            if (hostInviteBlob) {
                const link = document.createElement('a');
                link.download = `StarBlazer_Invite_${state.lobbyId || 'Lobby'}.jpg`;
                link.href = URL.createObjectURL(hostInviteBlob);
                link.click();
                URL.revokeObjectURL(link.href);
            }
        });

        document.getElementById('guest-download-btn').addEventListener('click', () => {
            if (guestAnswerBlob) {
                const link = document.createElement('a');
                link.download = `StarBlazer_Answer_${state.lobbyId || 'Lobby'}.jpg`;
                link.href = URL.createObjectURL(guestAnswerBlob);
                link.click();
                URL.revokeObjectURL(link.href);
            }
        });

        document.getElementById('host-avatar-use-btn').addEventListener('click', () => {
            const canvas = document.getElementById('host-avatar-canvas');
            if (canvas) {
                const dataUrl = canvas.toDataURL('image/jpeg', 0.85);
                setPlayerAvatar(1, dataUrl);
                showToast("Set as Player 1 avatar!");
            }
        });

        document.getElementById('guest-avatar-use-btn').addEventListener('click', () => {
            const canvas = document.getElementById('guest-avatar-canvas');
            if (canvas) {
                const dataUrl = canvas.toDataURL('image/jpeg', 0.85);
                setPlayerAvatar(2, dataUrl);
                showToast("Set as Player 2 avatar!");
            }
        });

        setupDropzone('host-dropzone', 'host-file-input', 'host-dropzone-text', async (file) => {
            try {
                const token = await decodeTokenFromImageFile(file);
                await handleGuestAnswer(token);
            } catch (err) {
                showToast(err.message);
            }
        });

        setupDropzone('guest-dropzone', 'guest-file-input', 'guest-dropzone-text', async (file) => {
            try {
                const token = await decodeTokenFromImageFile(file);
                await initGuestWebRTC(token);
            } catch (err) {
                showToast(err.message);
            }
        });

        document.getElementById('text-toggle-btn').addEventListener('click', () => {
            const container = document.getElementById('text-inputs-container');
            container.style.display = container.style.display === 'none' ? 'flex' : 'none';
        });

        document.getElementById('copy-raw-btn').addEventListener('click', () => {
            const textarea = document.getElementById('raw-code-out');
            navigator.clipboard.writeText(textarea.value).then(() => {
                const btn = document.getElementById('copy-raw-btn');
                btn.textContent = 'Copied!';
                setTimeout(() => btn.textContent = 'Copy Raw Code', 2000);
            }).catch(err => {
                showToast('Failed to copy code.');
            });
        });

        document.getElementById('submit-raw-btn').addEventListener('click', () => {
            const val = document.getElementById('raw-code-in').value.trim();
            if (!val) {
                showToast('Please paste a connection code first.');
                return;
            }
            if (val.startsWith("SB_OFFER:")) {
                initGuestWebRTC(val);
                document.getElementById('lobby-text-fallback').style.display = 'block';
            } else if (val.startsWith("SB_ANSWER:")) {
                handleGuestAnswer(val);
            } else {
                showToast('Invalid code format. Make sure it is an Invite or Answer code.');
            }
        });
    }

    function setupDropzone(dropzoneId, inputId, labelId, onFileSelected) {
        const dropzone = document.getElementById(dropzoneId);
        const input = document.getElementById(inputId);
        const label = document.getElementById(labelId);
        
        if (!dropzone || !input) return;

        dropzone.addEventListener('click', () => input.click());

        input.addEventListener('change', () => {
            if (input.files.length > 0) {
                const file = input.files[0];
                if (label) label.textContent = `Selected: ${file.name}`;
                onFileSelected(file);
            }
        });

        dropzone.addEventListener('dragover', (e) => {
            e.preventDefault();
            dropzone.classList.add('dragover');
        });

        dropzone.addEventListener('dragleave', () => {
            dropzone.classList.remove('dragover');
        });

        dropzone.addEventListener('drop', (e) => {
            e.preventDefault();
            dropzone.classList.remove('dragover');
            if (e.dataTransfer.files.length > 0) {
                const file = e.dataTransfer.files[0];
                if (label) label.textContent = `Dropped: ${file.name}`;
                onFileSelected(file);
            }
        });
    }

    function updateLobbyUIForConnected() {
        document.getElementById('lobby-modal').style.display = 'none';
        resetLobbyScreens();
    }

    function sendStateSync() {
        if (!state.conn) return;
        
        const boardData = Array.from(state.board.entries());
        const payload = {
            type: 'init',
            board: boardData,
            playerColors: state.playerColors,
            playerNames: state.playerNames,
            playerAvatars: state.playerAvatars,
            currentPlayer: state.currentPlayer,
            totalPieces: state.totalPieces,
            playerCounts: state.playerCounts,
            royals: state.royals,
            royalPlaced: state.royalPlaced,
            playerTurnsTaken: state.playerTurnsTaken,
            soldierReserveCount: state.soldierReserveCount,
            corvetteReserveCount: state.corvetteReserveCount,
            hopperReserveCount: state.hopperReserveCount,
            generalReserveCount: state.generalReserveCount,
            moveHistory: state.moveHistory,
            gameOver: state.gameOver,
            winner: state.winner
        };
        
        sendNetworkMessage(payload);
    }

    function applyStateSync(data) {
        state.remoteActionInProgress = true;
        
        state.board = new Map(data.board);
        state.playerColors = data.playerColors;
        
        if (data.playerNames) {
            state.playerNames = data.playerNames;
            updatePlayerName(1, state.playerNames[1]);
            updatePlayerName(2, state.playerNames[2]);
        }
        if (data.playerAvatars) {
            setPlayerAvatar(1, data.playerAvatars[1]);
            setPlayerAvatar(2, data.playerAvatars[2]);
        }
        
        state.currentPlayer = data.currentPlayer;
        state.totalPieces = data.totalPieces;
        state.playerCounts = data.playerCounts;
        state.royals = data.royals;
        state.royalPlaced = data.royalPlaced;
        state.playerTurnsTaken = data.playerTurnsTaken;
        state.soldierReserveCount = data.soldierReserveCount;
        state.corvetteReserveCount = data.corvetteReserveCount;
        state.hopperReserveCount = data.hopperReserveCount;
        state.generalReserveCount = data.generalReserveCount;
        state.moveHistory = data.moveHistory;
        state.gameOver = data.gameOver;
        state.winner = data.winner;
        
        document.documentElement.style.setProperty('--p1-color', state.playerColors[1]);
        document.documentElement.style.setProperty('--p2-color', state.playerColors[2]);
        
        updateSwatchUI(1, state.playerColors[1]);
        updateSwatchUI(2, state.playerColors[2]);
        
        // Re-draw cells
        cellElements.forEach((cell, key) => {
            const [cq, cr] = key.split(',').map(Number);
            renderCell(cq, cr);
        });
        
        state.selectedSoldier = null;
        state.selectedCorvette = null;
        state.selectedHopper = null;
        state.selectedGeneral = null;
        
        state.remoteActionInProgress = false;
        
        refreshUI();
        
        // Highlight active actions if any
        clearHighlights();
        const available = getAvailableActions();
        state.actionMode = available[0] || 'place_soldier';
        
        if (state.actionMode === 'move_royal') highlightMoveTargets();
        else if (state.actionMode === 'move_soldier') highlightSoldierTargets();
        else if (state.actionMode === 'move_corvette') highlightCorvetteTargets();
        else if (state.actionMode === 'move_hopper') highlightHopperTargets();
        else if (state.actionMode === 'move_general') highlightGeneralTargets();
    }

    function handleIncomingMessage(msg) {
        state.remoteActionInProgress = true;
        
        switch (msg.type) {
            case 'init':
                applyStateSync(msg);
                break;
            case 'place':
                executePlaceRemote(msg.pieceType, msg.q, msg.r);
                break;
            case 'move':
                executeMoveRemote(msg.pieceType, msg.fromQ, msg.fromR, msg.toQ, msg.toR);
                break;
            case 'undo':
                undoMove();
                break;
            case 'reset':
                resetGame();
                break;
            case 'color':
                executeColorRemote(msg.player, msg.color);
                break;
            case 'name_change':
                updatePlayerName(msg.player, msg.name);
                break;
            case 'avatar':
                setPlayerAvatar(msg.player, msg.avatar);
                break;
        }
        
        state.remoteActionInProgress = false;
        refreshUI();
    }

    function executePlaceRemote(pieceType, q, r) {
        if (pieceType === 'royal') placeRoyal(q, r);
        else if (pieceType === 'soldier') placeSoldier(q, r);
        else if (pieceType === 'corvette') placeCorvette(q, r);
        else if (pieceType === 'hopper') placeHopper(q, r);
        else if (pieceType === 'general') placeGeneral(q, r);
    }
    
    function executeMoveRemote(pieceType, fromQ, fromR, toQ, toR) {
        if (pieceType === 'royal') {
            moveRoyal(toQ, toR);
        } else if (pieceType === 'soldier') {
            state.selectedSoldier = { q: fromQ, r: fromR };
            moveSoldier(toQ, toR);
        } else if (pieceType === 'corvette') {
            state.selectedCorvette = { q: fromQ, r: fromR };
            moveCorvette(toQ, toR);
        } else if (pieceType === 'hopper') {
            state.selectedHopper = { q: fromQ, r: fromR };
            moveHopper(toQ, toR);
        } else if (pieceType === 'general') {
            state.selectedGeneral = { q: fromQ, r: fromR };
            moveGeneral(toQ, toR);
        }
    }

    function executeColorRemote(player, color) {
        state.remoteActionInProgress = true;
        const otherPlayer = player === 1 ? 2 : 1;
        if (state.playerColors[otherPlayer] === color) {
            const oldColor = state.playerColors[player];
            updatePlayerColor(otherPlayer, oldColor);
            updateSwatchUI(otherPlayer, oldColor);
        }
        updatePlayerColor(player, color);
        updateSwatchUI(player, color);
        state.remoteActionInProgress = false;
    }

    function sendNetworkMessage(msg) {
        if (state.conn && (state.conn.open || state.conn.readyState === 'open')) {
            const dataStr = typeof msg === 'object' ? JSON.stringify(msg) : msg;
            state.conn.send(dataStr);
        }
    }

    function resetToOffline() {
        state.onlineRole = null;
        cleanupWebRTC();
        
        document.getElementById('lobby-modal').style.display = 'none';
        resetLobbyScreens();
        
        const url = new URL(window.location);
        url.searchParams.delete('room');
        window.history.replaceState({}, document.title, url.pathname);
        
        document.getElementById('reset-btn').disabled = false;
        document.getElementById('undo-btn').disabled = false;
        
        state.isManualCamera = false;
        const recenterBtn = document.getElementById('recenter-btn');
        if (recenterBtn) recenterBtn.classList.remove('active');

        // Restore solid colors to chips
        const p1Chip = document.getElementById('player1-chip');
        if (p1Chip) {
            p1Chip.style.backgroundImage = '';
            p1Chip.style.backgroundColor = state.playerColors[1];
            p1Chip.style.border = '';
        }
        const p2Chip = document.getElementById('player2-chip');
        if (p2Chip) {
            p2Chip.style.backgroundImage = '';
            p2Chip.style.backgroundColor = state.playerColors[2];
            p2Chip.style.border = '';
        }
        
        state.playerAvatars = { 1: null, 2: null };
        
        // Remove patterns
        for (const p of [1, 2]) {
            const pattern = document.getElementById(`player${p}-avatar-pattern`);
            if (pattern) pattern.remove();
        }

        // Rerender cells
        state.board.forEach((stack, key) => {
            const [cq, cr] = key.split(',').map(Number);
            renderCell(cq, cr);
        });

        // Reset names to local values
        const name1 = document.querySelector('#player1-card .player-name');
        if (name1) name1.textContent = state.playerNames[1] || 'Player 1';
        const name2 = document.querySelector('#player2-card .player-name');
        if (name2) name2.textContent = state.playerNames[2] || 'Player 2';

        refreshUI();
    }

    function updateMultiplayerUI(status, text) {
        if (status === 'connected') {
            updateLobbyUIForConnected();
        }
    }

    function updateMultiplayerCardsUI() {
        const name1El = document.querySelector('#player1-card .player-name');
        const name2El = document.querySelector('#player2-card .player-name');

        for (const p of [1, 2]) {
            const btn = document.getElementById(`p${p}-type-btn`);
            if (!btn) continue;
            
            if (state.onlineRole !== null) {
                btn.disabled = true;
                btn.style.pointerEvents = 'none';
                
                const iconEl = btn.querySelector('.player-type-icon');
                const labelEl = btn.querySelector('.player-type-label');
                
                btn.classList.add('player-type-btn--auto');
                
                if (p === 1) {
                    if (iconEl) iconEl.textContent = state.onlineRole === 1 ? '👤' : '👥';
                    if (labelEl) labelEl.textContent = state.onlineRole === 1 ? 'Host (You)' : 'Host (Opponent)';
                } else {
                    if (iconEl) iconEl.textContent = state.onlineRole === 2 ? '👤' : '👥';
                    if (labelEl) labelEl.textContent = state.onlineRole === 2 ? 'Guest (You)' : 'Guest (Opponent)';
                }
            } else {
                btn.disabled = false;
                btn.style.pointerEvents = '';
                updatePlayerAutoUI(p);
            }
        }

        // Enforce contenteditable permissions based on role
        if (name1El && name2El) {
            if (state.onlineRole === 1) {
                name1El.contentEditable = "true";
                name2El.contentEditable = "false";
            } else if (state.onlineRole === 2) {
                name1El.contentEditable = "false";
                name2El.contentEditable = "true";
            } else {
                name1El.contentEditable = "true";
                name2El.contentEditable = "true";
            }
        }
    }

    function showToast(message) {
        const toast = document.getElementById('online-toast');
        const text = document.getElementById('online-toast-text');
        if (!toast || !text) return;
        text.textContent = message;
        toast.style.display = '';
        
        if (toastTimer) clearTimeout(toastTimer);
        toastTimer = setTimeout(() => {
            toast.style.display = 'none';
        }, 3000);
    }

    if (document.readyState === 'loading') {
        document.addEventListener('DOMContentLoaded', init);
    } else {
        init();
    }
})();

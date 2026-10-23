(() => {
  'use strict';

  /* ======================================================================
     1. 中国象棋规则核心
     主线程与 AI Worker 共用同一份实现，避免规则双写。
     ====================================================================== */
  function createEngineCore() {
    'use strict';

    const ROWS = 10;
    const COLS = 9;
    const MATE_SCORE = 1e8;
    const INF = 1e9;
    const TIMEOUT = { timeout: true };
    const VALUE = { k: 100000, r: 1000, c: 520, h: 460, a: 220, e: 220, p: 100 };
    const BACK_RANK = ['r', 'h', 'e', 'a', 'k', 'a', 'e', 'h', 'r'];
    const DIRS_ORTHO = [[1, 0], [-1, 0], [0, 1], [0, -1]];
    const DIRS_DIAG = [[1, 1], [1, -1], [-1, 1], [-1, -1]];

    const otherSide = side => side === 'red' ? 'green' : 'red';
    const inBounds = (r, c) => r >= 0 && r < ROWS && c >= 0 && c < COLS;
    const now = () => (typeof performance !== 'undefined' ? performance.now() : Date.now());

    function initialBoard() {
      const b = Array.from({ length: ROWS }, () => Array(COLS).fill(null));
      for (let c = 0; c < COLS; c++) {
        b[0][c] = { side: 'green', type: BACK_RANK[c] };
        b[9][c] = { side: 'red', type: BACK_RANK[c] };
      }
      b[2][1] = { side: 'green', type: 'c' };
      b[2][7] = { side: 'green', type: 'c' };
      b[7][1] = { side: 'red', type: 'c' };
      b[7][7] = { side: 'red', type: 'c' };
      for (const c of [0, 2, 4, 6, 8]) {
        b[3][c] = { side: 'green', type: 'p' };
        b[6][c] = { side: 'red', type: 'p' };
      }
      return b;
    }

    function cloneBoard(b) {
      return b.map(row => row.map(p => p ? { side: p.side, type: p.type } : null));
    }

    function palaceContains(side, r, c) {
      if (c < 3 || c > 5) return false;
      return side === 'red' ? r >= 7 && r <= 9 : r >= 0 && r <= 2;
    }

    function findKing(b, side) {
      for (let r = 0; r < ROWS; r++) {
        for (let c = 0; c < COLS; c++) {
          const p = b[r][c];
          if (p && p.side === side && p.type === 'k') return { r, c };
        }
      }
      return null;
    }

    function pseudoMoves(b, r, c) {
      const p = b[r] && b[r][c];
      if (!p) return [];
      const out = [];
      const add = (nr, nc) => {
        if (!inBounds(nr, nc)) return;
        const target = b[nr][nc];
        if (!target || target.side !== p.side) out.push({ r: nr, c: nc });
      };

      if (p.type === 'k') {
        for (const [dr, dc] of DIRS_ORTHO) {
          const nr = r + dr;
          const nc = c + dc;
          if (palaceContains(p.side, nr, nc)) add(nr, nc);
        }
      } else if (p.type === 'a') {
        for (const [dr, dc] of DIRS_DIAG) {
          const nr = r + dr;
          const nc = c + dc;
          if (palaceContains(p.side, nr, nc)) add(nr, nc);
        }
      } else if (p.type === 'e') {
        for (const [dr, dc] of DIRS_DIAG) {
          const nr = r + dr * 2;
          const nc = c + dc * 2;
          if (!inBounds(nr, nc)) continue;
          const ownSide = p.side === 'red' ? nr >= 5 : nr <= 4;
          if (!ownSide) continue;
          if (!b[r + dr][c + dc]) add(nr, nc);
        }
      } else if (p.type === 'h') {
        const legs = [
          [-2, -1, -1, 0], [-2, 1, -1, 0], [2, -1, 1, 0], [2, 1, 1, 0],
          [-1, -2, 0, -1], [1, -2, 0, -1], [-1, 2, 0, 1], [1, 2, 0, 1]
        ];
        for (const [dr, dc, lr, lc] of legs) {
          const nr = r + dr;
          const nc = c + dc;
          if (!inBounds(nr, nc)) continue;
          if (!b[r + lr][c + lc]) add(nr, nc);
        }
      } else if (p.type === 'r') {
        for (const [dr, dc] of DIRS_ORTHO) {
          let nr = r + dr;
          let nc = c + dc;
          while (inBounds(nr, nc)) {
            const target = b[nr][nc];
            if (!target) {
              out.push({ r: nr, c: nc });
            } else {
              if (target.side !== p.side) out.push({ r: nr, c: nc });
              break;
            }
            nr += dr;
            nc += dc;
          }
        }
      } else if (p.type === 'c') {
        for (const [dr, dc] of DIRS_ORTHO) {
          let nr = r + dr;
          let nc = c + dc;
          let screened = false;
          while (inBounds(nr, nc)) {
            const target = b[nr][nc];
            if (!screened) {
              if (!target) {
                out.push({ r: nr, c: nc });
              } else {
                screened = true;
              }
            } else if (target) {
              if (target.side !== p.side) out.push({ r: nr, c: nc });
              break;
            }
            nr += dr;
            nc += dc;
          }
        }
      } else if (p.type === 'p') {
        const forward = p.side === 'red' ? -1 : 1;
        add(r + forward, c);
        const crossed = p.side === 'red' ? r <= 4 : r >= 5;
        if (crossed) {
          add(r, c - 1);
          add(r, c + 1);
        }
      }
      return out;
    }

    /*
     * 直接判断“某方的帅/将是否正被攻击”。比遍历对方全部伪走法快，
     * 也完整覆盖车、炮、马、兵、将帅照面，以及理论上不会出现的士/象贴近局面。
     */
    function isAttacked(b, side) {
      const king = findKing(b, side);
      if (!king) return true;
      const enemy = otherSide(side);
      const kr = king.r;
      const kc = king.c;

      for (const [dr, dc] of DIRS_ORTHO) {
        let nr = kr + dr;
        let nc = kc + dc;
        let screens = 0;
        while (inBounds(nr, nc)) {
          const q = b[nr][nc];
          if (q) {
            if (screens === 0) {
              if (q.side === enemy && q.type === 'r') return true;
              screens = 1;
            } else {
              if (q.side === enemy && q.type === 'c') return true;
              break;
            }
          }
          nr += dr;
          nc += dc;
        }
      }

      const horseOffsets = [
        [-2, -1], [-2, 1], [2, -1], [2, 1],
        [-1, -2], [-1, 2], [1, -2], [1, 2]
      ];
      for (const [dr, dc] of horseOffsets) {
        const hr = kr + dr;
        const hc = kc + dc;
        if (!inBounds(hr, hc)) continue;
        const q = b[hr][hc];
        if (!q || q.side !== enemy || q.type !== 'h') continue;
        const legR = Math.abs(dc) === 2 ? hr : hr + (dr > 0 ? -1 : 1);
        const legC = Math.abs(dr) === 2 ? hc : hc + (dc > 0 ? -1 : 1);
        if (!b[legR][legC]) return true;
      }

      const pawnForward = enemy === 'red' ? -1 : 1;
      const pawnR = kr - pawnForward;
      if (inBounds(pawnR, kc)) {
        const q = b[pawnR][kc];
        if (q && q.side === enemy && q.type === 'p') return true;
      }
      const pawnCanSide = enemy === 'red' ? kr <= 4 : kr >= 5;
      if (pawnCanSide) {
        for (const dc of [-1, 1]) {
          const pc = kc + dc;
          if (!inBounds(kr, pc)) continue;
          const q = b[kr][pc];
          if (q && q.side === enemy && q.type === 'p') return true;
        }
      }

      for (const [dr, dc] of DIRS_DIAG) {
        const nr = kr + dr;
        const nc = kc + dc;
        if (!inBounds(nr, nc)) continue;
        const q = b[nr][nc];
        if (q && q.side === enemy && q.type === 'a' && palaceContains(enemy, nr, nc)) return true;

        const er = kr + dr * 2;
        const ec = kc + dc * 2;
        if (!inBounds(er, ec)) continue;
        const eq = b[er][ec];
        if (eq && eq.side === enemy && eq.type === 'e') {
          const ownSide = enemy === 'red' ? er >= 5 : er <= 4;
          if (ownSide && !b[kr + dr][kc + dc]) return true;
        }
      }

      for (const dr of [-1, 1]) {
        let nr = kr + dr;
        while (inBounds(nr, kc)) {
          const q = b[nr][kc];
          if (q) {
            if (q.side === enemy && q.type === 'k') return true;
            break;
          }
          nr += dr;
        }
      }

      for (const [dr, dc] of DIRS_ORTHO) {
        const nr = kr + dr;
        const nc = kc + dc;
        if (!inBounds(nr, nc)) continue;
        const q = b[nr][nc];
        if (q && q.side === enemy && q.type === 'k') return true;
      }

      return false;
    }

    function isInCheck(b, side) {
      return isAttacked(b, side);
    }

    function getLegalMoves(b, r, c, side) {
      const p = b[r] && b[r][c];
      if (!p || p.side !== side) return [];
      const out = [];
      for (const move of pseudoMoves(b, r, c)) {
        const target = b[move.r][move.c];
        if (target && target.type === 'k') continue;
        b[move.r][move.c] = p;
        b[r][c] = null;
        const safe = !isAttacked(b, side);
        b[r][c] = p;
        b[move.r][move.c] = target;
        if (safe) out.push(move);
      }
      return out;
    }

    function allLegalMoves(b, side) {
      const out = [];
      for (let r = 0; r < ROWS; r++) {
        for (let c = 0; c < COLS; c++) {
          const p = b[r][c];
          if (!p || p.side !== side) continue;
          for (const move of getLegalMoves(b, r, c, side)) {
            out.push({ fr: r, fc: c, tr: move.r, tc: move.c });
          }
        }
      }
      return out;
    }

    function makeMoveInternal(b, move) {
      const captured = b[move.tr][move.tc];
      b[move.tr][move.tc] = b[move.fr][move.fc];
      b[move.fr][move.fc] = null;
      return captured;
    }

    function unmakeMoveInternal(b, move, captured) {
      b[move.fr][move.fc] = b[move.tr][move.tc];
      b[move.tr][move.tc] = captured;
    }

    function evaluateBoard(b, perspective) {
      let red = 0;
      let green = 0;
      for (let r = 0; r < ROWS; r++) {
        for (let c = 0; c < COLS; c++) {
          const p = b[r][c];
          if (!p) continue;
          let v = VALUE[p.type] || 0;
          const advance = p.side === 'red' ? 6 - r : r - 3;
          const adv = Math.max(0, Math.min(6, advance));
          if (p.type === 'p') {
            v += adv * 10;
            if (adv >= 2) v += 50;
            if (adv >= 5) v += 35;
            if (c >= 3 && c <= 5) v += 12;
          } else if (p.type === 'h') {
            v += (4 - Math.abs(c - 4)) * 8 + adv * 3;
          } else if (p.type === 'c') {
            v += (4 - Math.abs(c - 4)) * 5 + adv * 2;
          } else if (p.type === 'r') {
            v += adv * 6;
          } else if (p.type === 'k') {
            v += c === 4 ? 0 : -8;
          }
          if (p.side === 'red') red += v;
          else green += v;
        }
      }
      const diff = red - green;
      return perspective === 'red' ? diff : -diff;
    }

    function moveOrderScore(b, move, preferredKey) {
      const key = `${move.fr}${move.fc}${move.tr}${move.tc}`;
      let score = key === preferredKey ? 500000 : 0;
      const target = b[move.tr][move.tc];
      if (target) {
        const mover = b[move.fr][move.fc];
        score += 100000 + (VALUE[target.type] || 0) * 8 - (mover ? (VALUE[mover.type] || 0) / 10 : 0);
      }
      return score;
    }

    function orderMoves(b, moves, preferredKey) {
      return moves.sort((a, b2) => moveOrderScore(b, b2, preferredKey) - moveOrderScore(b, a, preferredKey));
    }

    function checkDeadline(ctx) {
      if ((ctx.nodes & 511) === 0 && now() >= ctx.deadline) throw TIMEOUT;
      ctx.nodes++;
    }

    function negamax(b, side, depth, alpha, beta, ply, ctx) {
      checkDeadline(ctx);
      if (depth <= 0) return evaluateBoard(b, side);

      const moves = allLegalMoves(b, side);
      if (moves.length === 0) return -MATE_SCORE + ply;
      orderMoves(b, moves, null);

      let best = -INF;
      for (const move of moves) {
        const captured = makeMoveInternal(b, move);
        let score;
        try {
          score = -negamax(b, otherSide(side), depth - 1, -beta, -alpha, ply + 1, ctx);
        } finally {
          unmakeMoveInternal(b, move, captured);
        }
        if (score > best) best = score;
        if (score > alpha) alpha = score;
        if (alpha >= beta) break;
      }
      return best;
    }

    function searchRoot(b, side, depth, previousBest, deadline) {
      const ctx = { nodes: 0, deadline, started: now() };
      const moves = allLegalMoves(b, side);
      if (!moves.length) {
        return { move: null, score: -MATE_SCORE, nodes: 0, depth, elapsed: 0 };
      }
      const preferredKey = previousBest
        ? `${previousBest.fr}${previousBest.fc}${previousBest.tr}${previousBest.tc}`
        : null;
      orderMoves(b, moves, preferredKey);

      let alpha = -INF;
      const beta = INF;
      let bestMove = null;
      let bestScore = -INF;
      for (const move of moves) {
        if (now() >= deadline) throw TIMEOUT;
        const captured = makeMoveInternal(b, move);
        let score;
        try {
          score = -negamax(b, otherSide(side), depth - 1, -beta, -alpha, 1, ctx);
        } finally {
          unmakeMoveInternal(b, move, captured);
        }
        if (score > bestScore || (score === bestScore && Math.random() < 0.15)) {
          bestScore = score;
          bestMove = move;
        }
        if (score > alpha) alpha = score;
      }
      return {
        move: bestMove,
        score: bestScore,
        nodes: ctx.nodes,
        depth,
        elapsed: now() - ctx.started
      };
    }

    function chooseEasyMove(b, side, legal) {
      let best = legal[0];
      let bestScore = -INF;
      for (const move of legal) {
        const captured = makeMoveInternal(b, move);
        let score;
        try {
          score = -evaluateBoard(b, otherSide(side));
        } finally {
          unmakeMoveInternal(b, move, captured);
        }
        score += Math.random() * 160 - 80;
        if (Math.random() < 0.04) score -= 320;
        if (score > bestScore) {
          bestScore = score;
          best = move;
        }
      }
      if (Math.random() < 0.22) {
        return legal[Math.floor(Math.random() * legal.length)];
      }
      return best;
    }

    function chooseMove(board, side, level) {
      const started = now();
      const legal = allLegalMoves(board, side);
      if (!legal.length) {
        return { move: null, score: -MATE_SCORE, depth: 0, nodes: 0, elapsed: 0 };
      }

      const settings = level === 'hard'
        ? { maxDepth: 5, time: 1500 }
        : level === 'medium'
          ? { maxDepth: 3, time: 650 }
          : { maxDepth: 1, time: 220 };

      if (level === 'easy') {
        const move = chooseEasyMove(board, side, legal) || legal[0];
        return {
          move,
          score: 0,
          depth: 1,
          nodes: legal.length,
          elapsed: Math.round(now() - started)
        };
      }

      const deadline = started + settings.time;
      let best = legal[0];
      let bestScore = 0;
      let depthReached = 0;
      let totalNodes = 0;

      for (let depth = 1; depth <= settings.maxDepth; depth++) {
        if (now() >= deadline) break;
        try {
          const result = searchRoot(board, side, depth, best, deadline);
          totalNodes += result.nodes;
          if (result.move) {
            best = result.move;
            bestScore = result.score;
            depthReached = depth;
          }
          if (Math.abs(result.score) > MATE_SCORE / 2) break;
        } catch (error) {
          if (error !== TIMEOUT) throw error;
          break;
        }
      }

      return {
        move: best,
        score: bestScore,
        depth: depthReached,
        nodes: totalNodes,
        elapsed: Math.round(now() - started)
      };
    }

    function perft(b, side, depth) {
      if (depth <= 0) return 1;
      let total = 0;
      for (const move of allLegalMoves(b, side)) {
        const captured = makeMoveInternal(b, move);
        try {
          total += perft(b, otherSide(side), depth - 1);
        } finally {
          unmakeMoveInternal(b, move, captured);
        }
      }
      return total;
    }

    return {
      ROWS, COLS,
      initialBoard,
      cloneBoard,
      otherSide,
      pseudoMoves,
      isAttacked,
      isInCheck,
      findKing,
      getLegalMoves,
      allLegalMoves,
      makeMoveInternal,
      unmakeMoveInternal,
      evaluateBoard,
      chooseMove,
      perft
    };
  }

  const Engine = createEngineCore();

  /* ======================================================================
     2. 基础常量与状态
     ====================================================================== */
  const $ = id => document.getElementById(id);
  const LABELS = {
    red: { k: '帅', a: '仕', e: '相', h: '马', r: '车', c: '炮', p: '兵' },
    green: { k: '将', a: '士', e: '象', h: '马', r: '车', c: '炮', p: '卒' }
  };
  const SIDE_NAME = { red: '红方', green: '绿方' };
  const SIDE_GLYPH = { red: '帅', green: '将' };
  const SIDE_COLOR_NAME = { red: '红方 · 帅', green: '绿方 · 将' };
  const AI_LEVELS = {
    easy: { label: '简单', minDelay: 300 },
    medium: { label: '中等', minDelay: 420 },
    hard: { label: '困难', minDelay: 520 }
  };
  const RPS_HANDS = {
    rock: { label: '石头', glyph: '石' },
    scissors: { label: '剪刀', glyph: '剪' },
    paper: { label: '布', glyph: '布' }
  };
  const RPS_BEATS = { rock: 'scissors', scissors: 'paper', paper: 'rock' };
  const params = new URLSearchParams(window.location.search);

  const dom = {
    board: $('board'),
    pieceLayer: $('pieceLayer'),
    targetLayer: $('targetLayer'),
    lastMoveLayer: $('lastMoveLayer'),
    checkLayer: $('checkLayer'),
    modeChip: $('modeChip'),
    turnDot: $('turnDot'),
    turnLabel: $('turnLabel'),
    statusText: $('statusText'),
    topPlayerRow: $('topPlayerRow'),
    bottomPlayerRow: $('bottomPlayerRow'),
    topAvatar: $('topAvatar'),
    bottomAvatar: $('bottomAvatar'),
    topName: $('topName'),
    bottomName: $('bottomName'),
    topTag: $('topTag'),
    bottomTag: $('bottomTag'),
    modeLocalBtn: $('modeLocalBtn'),
    modeAiBtn: $('modeAiBtn'),
    modeRoomBtn: $('modeRoomBtn'),
    railInfoTitle: $('railInfoTitle'),
    railInfoText: $('railInfoText'),
    undoBtn: $('undoBtn'),
    restartBtn: $('restartBtn'),
    soundBtn: $('soundBtn'),
    soundLabel: $('soundLabel'),
    leaveRoomBtn: $('leaveRoomBtn'),
    moveList: $('moveList'),
    moveCount: $('moveCount'),
    toast: $('toast'),

    setupDialog: $('setupDialog'),
    setupCloseBtn: $('setupCloseBtn'),
    aiSetup: $('aiSetup'),
    roomSetup: $('roomSetup'),
    aiTitle: $('aiTitle'),
    roomTitle: $('roomTitle'),
    levelGroup: $('levelGroup'),
    aiSideGroup: $('aiSideGroup'),
    aiSummary: $('aiSummary'),
    startAiBtn: $('startAiBtn'),

    roomChoice: $('roomChoice'),
    createRoomTab: $('createRoomTab'),
    joinRoomTab: $('joinRoomTab'),
    createRoomPane: $('createRoomPane'),
    joinRoomPane: $('joinRoomPane'),
    createRoomBtn: $('createRoomBtn'),
    joinRoomBtn: $('joinRoomBtn'),
    roomCodeInput: $('roomCodeInput'),
    roomError: $('roomError'),
    roomLobby: $('roomLobby'),
    lobbyCode: $('lobbyCode'),
    hostBadge: $('hostBadge'),
    copyCodeBtn: $('copyCodeBtn'),
    lobbyStatus: $('lobbyStatus'),
    lobbyStatusText: $('lobbyStatusText'),
    roomSideGroup: $('roomSideGroup'),
    opponentSideText: $('opponentSideText'),
    sideConflictNote: $('sideConflictNote'),
    hostStartWrap: $('hostStartWrap'),
    startRoomBtn: $('startRoomBtn'),
    hostStartHint: $('hostStartHint'),
    guestWaitText: $('guestWaitText'),
    exitLobbyBtn: $('exitLobbyBtn'),

    rpsDialog: $('rpsDialog'),
    rpsSub: $('rpsSub'),
    rpsMyScore: $('rpsMyScore'),
    rpsOppScore: $('rpsOppScore'),
    rpsRound: $('rpsRound'),
    rpsChoices: $('rpsChoices'),
    rpsReveal: $('rpsReveal'),
    rpsMyHand: $('rpsMyHand'),
    rpsOppHand: $('rpsOppHand'),
    rpsResult: $('rpsResult'),
    rpsFooter: $('rpsFooter')
  };

  const initialSound = (() => {
    try {
      const saved = localStorage.getItem('xq-sound-v1');
      return saved === null ? true : saved === '1';
    } catch {
      return true;
    }
  })();

  const state = {
    mode: 'local',
    board: Engine.initialBoard(),
    turn: 'red',
    selected: null,
    history: [],
    moves: [],
    lastMove: null,
    gameOver: false,
    winner: null,
    endReason: '',
    inCheck: false,
    orientation: 'red',
    soundOn: initialSound,
    ai: freshAIState(),
    net: freshNetState()
  };

  const setupDraft = { level: 'medium', side: 'red' };
  const rps = {
    active: false,
    role: null,
    round: 1,
    hostWins: 0,
    guestWins: 0,
    hostChoice: null,
    guestChoice: null,
    side: null,
    phase: 'idle',
    final: false,
    timer: null
  };

  let toastTimer = null;
  let soundCount = 0;
  let audioContext = null;
  let aiWorkerUrl = null;
  const aiReady = (() => {
    try {
      const source = [
        "'use strict';",
        `const createEngineCore = ${createEngineCore.toString()};`,
        'const engine = createEngineCore();',
        "self.onmessage = function (event) {",
        '  try {',
        '    const data = event.data || {};',
        '    const result = engine.chooseMove(data.board, data.side, data.level);',
        '    self.postMessage({ ok: true, result: result });',
        '  } catch (error) {',
        '    self.postMessage({ ok: false, error: String(error && error.message || error) });',
        '  }',
        '};'
      ].join('\n');
      aiWorkerUrl = URL.createObjectURL(new Blob([source], { type: 'text/javascript' }));
      return typeof Worker !== 'undefined';
    } catch {
      return false;
    }
  })();

  function freshAIState() {
    return {
      level: 'medium',
      humanSide: 'red',
      thinking: false,
      requestId: 0,
      worker: null,
      timer: null,
      startTimer: null,
      fallbackTimer: null,
      anchors: []
    };
  }

  function freshNetState() {
    return {
      role: null,
      peer: null,
      conn: null,
      code: null,
      connected: false,
      phase: 'idle',
      gameId: 0,
      hostSide: null,
      guestSide: null,
      mySide: null,
      pendingMove: false,
      pendingTimer: null,
      joinTimer: null,
      handshakeTimer: null,
      generation: 0,
      closing: false
    };
  }

  /* ======================================================================
     3. 工具函数
     ====================================================================== */
  const otherSide = side => side === 'red' ? 'green' : 'red';
  const isSide = value => value === 'red' || value === 'green';
  const posText = pos => `${pos.c + 1}路${pos.r + 1}行`;

  function setStatus(text, tone = '') {
    dom.statusText.textContent = text;
    dom.statusText.className = `status-text${tone ? ` ${tone}` : ''}`;
  }

  function showToast(message, duration = 2600) {
    dom.toast.textContent = message;
    dom.toast.classList.add('show');
    if (toastTimer) clearTimeout(toastTimer);
    toastTimer = setTimeout(() => dom.toast.classList.remove('show'), duration);
  }

  function safeStorageSet(key, value) {
    try { localStorage.setItem(key, value); } catch { /* 忽略隐私模式限制 */ }
  }

  function showDialog(dialog) {
    if (!dialog) return;
    if (!dialog.open) {
      try { dialog.showModal(); } catch { dialog.setAttribute('open', ''); }
    }
  }

  function closeDialog(dialog) {
    if (dialog && dialog.open) dialog.close();
  }

  function isOnlineActive() {
    return state.mode === 'online' && Boolean(state.net.role) &&
      ['lobby', 'rps', 'playing'].includes(state.net.phase);
  }

  function currentSideName() {
    return SIDE_NAME[state.turn];
  }

  function playerInfo(side) {
    if (state.mode === 'ai') {
      const aiName = AI_LEVELS[state.ai.level].label;
      return {
        name: SIDE_NAME[side],
        tag: side === state.ai.humanSide ? '你' : `AI · ${aiName}`,
        isAI: side !== state.ai.humanSide
      };
    }
    if (state.mode === 'online') {
      return {
        name: SIDE_NAME[side],
        tag: side === state.net.mySide ? '你' : '对手',
        isAI: false
      };
    }
    return { name: SIDE_NAME[side], tag: '同屏玩家', isAI: false };
  }

  function displayPos(r, c) {
    return state.orientation === 'green' ? { r: 9 - r, c: 8 - c } : { r, c };
  }

  function logicalPos(r, c) {
    return state.orientation === 'green' ? { r: 9 - r, c: 8 - c } : { r, c };
  }

  function svgEl(tag, attrs = {}) {
    const el = document.createElementNS('http://www.w3.org/2000/svg', tag);
    for (const [key, value] of Object.entries(attrs)) el.setAttribute(key, String(value));
    return el;
  }

  function snapshotState() {
    return {
      board: Engine.cloneBoard(state.board),
      turn: state.turn,
      moves: state.moves.slice(),
      lastMove: state.lastMove
        ? { from: { ...state.lastMove.from }, to: { ...state.lastMove.to } }
        : null,
      gameOver: state.gameOver,
      winner: state.winner,
      endReason: state.endReason,
      inCheck: state.inCheck,
      orientation: state.orientation
    };
  }

  function restoreState(snapshot) {
    state.board = Engine.cloneBoard(snapshot.board);
    state.turn = snapshot.turn;
    state.moves = snapshot.moves.slice();
    state.lastMove = snapshot.lastMove
      ? { from: { ...snapshot.lastMove.from }, to: { ...snapshot.lastMove.to } }
      : null;
    state.gameOver = snapshot.gameOver;
    state.winner = snapshot.winner;
    state.endReason = snapshot.endReason;
    state.inCheck = snapshot.inCheck;
    state.orientation = snapshot.orientation;
    state.selected = null;
  }

  /* ======================================================================
     4. 音效
     ====================================================================== */
  function ensureAudioContext() {
    if (!state.soundOn) return null;
    try {
      if (!audioContext) {
        const AudioCtor = window.AudioContext || window.webkitAudioContext;
        if (!AudioCtor) return null;
        audioContext = new AudioCtor();
      }
      if (audioContext.state === 'suspended') audioContext.resume().catch(() => {});
      return audioContext;
    } catch {
      return null;
    }
  }

  function playMoveSound(captured = false) {
    if (!state.soundOn) return;
    const ctx = ensureAudioContext();
    if (!ctx) return;
    soundCount++;
    const t = ctx.currentTime;
    try {
      const master = ctx.createGain();
      master.gain.value = 0.28;
      master.connect(ctx.destination);

      const thump = ctx.createOscillator();
      const thumpGain = ctx.createGain();
      thump.type = 'triangle';
      thump.frequency.setValueAtTime(captured ? 235 : 275, t);
      thump.frequency.exponentialRampToValueAtTime(captured ? 82 : 105, t + 0.075);
      thumpGain.gain.setValueAtTime(0.0001, t);
      thumpGain.gain.exponentialRampToValueAtTime(0.6, t + 0.006);
      thumpGain.gain.exponentialRampToValueAtTime(0.0001, t + 0.14);
      thump.connect(thumpGain).connect(master);
      thump.start(t);
      thump.stop(t + 0.16);

      const length = Math.max(1, Math.floor(ctx.sampleRate * 0.032));
      const buffer = ctx.createBuffer(1, length, ctx.sampleRate);
      const data = buffer.getChannelData(0);
      for (let i = 0; i < length; i++) {
        const fade = Math.pow(1 - i / length, 3);
        data[i] = (Math.random() * 2 - 1) * fade;
      }
      const noise = ctx.createBufferSource();
      noise.buffer = buffer;
      const filter = ctx.createBiquadFilter();
      filter.type = 'bandpass';
      filter.frequency.value = captured ? 440 : 620;
      filter.Q.value = 0.75;
      const clickGain = ctx.createGain();
      clickGain.gain.value = captured ? 0.22 : 0.14;
      noise.connect(filter).connect(clickGain).connect(master);
      noise.start(t);
      noise.stop(t + 0.04);
    } catch {
      /* 音频失败不应影响对局 */
    }
  }

  function updateSoundButton() {
    dom.soundBtn.setAttribute('aria-pressed', String(state.soundOn));
    dom.soundLabel.textContent = state.soundOn ? '音效开' : '音效关';
  }

  function toggleSound() {
    state.soundOn = !state.soundOn;
    safeStorageSet('xq-sound-v1', state.soundOn ? '1' : '0');
    updateSoundButton();
    if (state.soundOn) playMoveSound(false);
    showToast(state.soundOn ? '落子音效已开启' : '落子音效已关闭');
  }

  /* ======================================================================
     5. 棋盘与信息渲染
     ====================================================================== */
  function canPlayNow() {
    if (state.gameOver) return false;
    if (state.mode === 'ai') {
      return !state.ai.thinking && state.turn === state.ai.humanSide;
    }
    if (state.mode === 'online') {
      return state.net.phase === 'playing' &&
        state.net.connected &&
        !state.net.pendingMove &&
        state.turn === state.net.mySide;
    }
    return true;
  }

  function drawSelectionAndTargets() {
    const targetLayer = dom.targetLayer;
    targetLayer.replaceChildren();
    if (!state.selected) return;
    const piece = state.board[state.selected.r] && state.board[state.selected.r][state.selected.c];
    if (!piece || piece.side !== state.turn || state.gameOver) return;
    const moves = Engine.getLegalMoves(state.board, state.selected.r, state.selected.c, state.turn);
    for (const move of moves) {
      const shown = displayPos(move.r, move.c);
      if (state.board[move.r][move.c]) {
        targetLayer.appendChild(svgEl('circle', {
          class: 'capture-ring',
          cx: 32 + shown.c * 57,
          cy: 32 + shown.r * 56,
          r: 26
        }));
      } else {
        targetLayer.appendChild(svgEl('circle', {
          class: 'target-dot',
          cx: 32 + shown.c * 57,
          cy: 32 + shown.r * 56,
          r: 4.8
        }));
      }
    }
  }

  function drawPieces() {
    const canPlay = canPlayNow();
    dom.pieceLayer.replaceChildren();
    for (let r = 0; r < Engine.ROWS; r++) {
      for (let c = 0; c < Engine.COLS; c++) {
        const piece = state.board[r][c];
        if (!piece) continue;
        const shown = displayPos(r, c);
        const isSelected = Boolean(state.selected && state.selected.r === r && state.selected.c === c);
        const playable = canPlay && piece.side === state.turn;
        const classes = ['piece', piece.side];
        if (isSelected) classes.push('selected');
        if (playable) classes.push('is-playable');
        const g = svgEl('g', { class: classes.join(' ') });
        const title = svgEl('title');
        title.textContent = `${SIDE_NAME[piece.side]}${LABELS[piece.side][piece.type]}`;
        g.appendChild(title);
        if (isSelected) {
          g.appendChild(svgEl('circle', {
            class: 'selection-ring',
            cx: 32 + shown.c * 57,
            cy: 32 + shown.r * 56,
            r: 28
          }));
        }
        g.appendChild(svgEl('circle', {
          class: 'base',
          cx: 32 + shown.c * 57,
          cy: 32 + shown.r * 56,
          r: 22.3
        }));
        const text = svgEl('text', {
          x: 32 + shown.c * 57,
          y: 32 + shown.r * 56 + 0.5
        });
        text.textContent = LABELS[piece.side][piece.type];
        g.appendChild(text);
        dom.pieceLayer.appendChild(g);
      }
    }
  }

  function drawLastMoveAndCheck() {
    dom.lastMoveLayer.replaceChildren();
    dom.checkLayer.replaceChildren();
    if (state.lastMove) {
      for (const pos of [state.lastMove.from, state.lastMove.to]) {
        const shown = displayPos(pos.r, pos.c);
        dom.lastMoveLayer.appendChild(svgEl('circle', {
          class: 'last-marker',
          cx: 32 + shown.c * 57,
          cy: 32 + shown.r * 56,
          r: 26.5
        }));
      }
    }
    if (state.inCheck && !state.gameOver) {
      const king = Engine.findKing(state.board, state.turn);
      if (king) {
        const shown = displayPos(king.r, king.c);
        dom.checkLayer.appendChild(svgEl('circle', {
          class: 'check-ring',
          cx: 32 + shown.c * 57,
          cy: 32 + shown.r * 56,
          r: 27
        }));
      }
    }
  }

  function renderBoard() {
    dom.board.classList.toggle('can-play', canPlayNow());
    drawLastMoveAndCheck();
    drawSelectionAndTargets();
    drawPieces();
  }

  function renderPlayerRows() {
    const topSide = otherSide(state.orientation);
    const bottomSide = state.orientation;
    const renderRow = (side, row, avatar, name, tag) => {
      const info = playerInfo(side);
      avatar.className = `player-avatar ${side}`;
      avatar.textContent = SIDE_GLYPH[side];
      name.textContent = info.name;
      tag.textContent = info.tag;
      row.classList.toggle('is-turn', !state.gameOver && state.turn === side);
    };
    renderRow(topSide, dom.topPlayerRow, dom.topAvatar, dom.topName, dom.topTag);
    renderRow(bottomSide, dom.bottomPlayerRow, dom.bottomAvatar, dom.bottomName, dom.bottomTag);
  }

  function renderModeAndRail() {
    const modeNames = { local: '自我对战', ai: 'AI 对决', online: '自定义房间' };
    for (const [mode, btn] of [['local', dom.modeLocalBtn], ['ai', dom.modeAiBtn], ['online', dom.modeRoomBtn]]) {
      const active = state.mode === mode;
      btn.classList.toggle('active', active);
      btn.setAttribute('aria-pressed', String(active));
    }

    if (state.mode === 'ai') {
      const level = AI_LEVELS[state.ai.level].label;
      dom.modeChip.textContent = `AI 对决 · ${level}`;
      dom.railInfoTitle.textContent = `人机对弈 · ${level}`;
      dom.railInfoText.textContent = `你执${SIDE_COLOR_NAME[state.ai.humanSide]}，AI 执${SIDE_COLOR_NAME[otherSide(state.ai.humanSide)]}。棋盘已按你的阵营转向。`;
    } else if (state.mode === 'online') {
      const code = state.net.code ? ` · ${state.net.code}` : '';
      dom.modeChip.textContent = `好友房间${code}`;
      if (state.net.phase === 'playing') {
        dom.railInfoTitle.textContent = `联机对局${code}`;
        dom.railInfoText.textContent = `你执${SIDE_COLOR_NAME[state.net.mySide] || '待定'}，对手执另一阵容。对局数据点对点直连。`;
      } else if (state.net.phase === 'rps') {
        dom.railInfoTitle.textContent = '选边对决';
        dom.railInfoText.textContent = '双方选择了同一阵容，正在用剪刀石头布决定选边权。';
      } else {
        dom.railInfoTitle.textContent = state.net.code ? `房间 ${state.net.code}` : '自定义房间';
        dom.railInfoText.textContent = state.net.connected
          ? '双方均已连接。打开「自定义房间」选择阵容，由房主开始对局。'
          : '等待双方连接，打开「自定义房间」可查看房间号与准备状态。';
      }
    } else {
      dom.modeChip.textContent = modeNames.local;
      dom.railInfoTitle.textContent = '自我对战';
      dom.railInfoText.textContent = '同一屏幕轮流落子。红方先行，将死或困毙即胜。';
    }
  }

  function renderStatus() {
    const isAiThinking = state.mode === 'ai' && state.ai.thinking;
    dom.turnDot.className = 'turn-dot';

    if (state.gameOver) {
      dom.turnDot.classList.add('over');
      dom.turnLabel.textContent = `${SIDE_NAME[state.winner]}胜`;
      const resultText = state.endReason === '困毙' ? '无棋可走，困毙判负' : '将死，对局结束';
      if (state.mode === 'online' && state.net.role === 'guest') {
        setStatus(`${resultText} · 等待房主重新开始`, 'good');
      } else {
        setStatus(`${resultText} · 点击重新开始再来一局`, 'good');
      }
    } else if (isAiThinking) {
      dom.turnDot.classList.add(state.turn === 'green' ? 'green' : 'red');
      dom.turnDot.classList.add('thinking');
      dom.turnLabel.textContent = `${currentSideName()}行棋`;
      setStatus('AI 正在计算落子…');
    } else if (state.mode === 'online' && state.net.phase !== 'playing') {
      dom.turnDot.classList.add('thinking');
      dom.turnLabel.textContent = state.net.phase === 'rps'
        ? '选边对决'
        : state.net.connected ? '等待开始' : '等待连接';
      setStatus(state.net.phase === 'rps'
        ? '剪刀石头布进行中…'
        : state.net.connected
          ? '房间已连接，打开「自定义房间」选择阵容'
          : '正在等待房间连接…');
    } else if (state.mode === 'online' && state.net.pendingMove) {
      dom.turnDot.classList.add(state.turn === 'green' ? 'green' : 'red');
      dom.turnLabel.textContent = `${currentSideName()}行棋`;
      setStatus('正在同步这一步落子…');
    } else {
      dom.turnDot.classList.add(state.turn === 'green' ? 'green' : 'red');
      dom.turnLabel.textContent = `${currentSideName()}行棋`;
      if (state.inCheck) {
        setStatus(`${currentSideName()}被将军！请解除将军`, 'alert');
      } else if (state.selected) {
        setStatus('已选中棋子，请选择落点');
      } else if (state.mode === 'ai') {
        setStatus(state.turn === state.ai.humanSide ? '轮到你落子' : '等待 AI 落子…');
      } else if (state.mode === 'online') {
        setStatus(state.turn === state.net.mySide ? '轮到你落子' : '等待对手落子…');
      } else {
        setStatus('点击棋子，再点击目标位置');
      }
    }

    const undoDisabled = state.mode === 'online' || !canUndo();
    dom.undoBtn.disabled = undoDisabled;
    dom.undoBtn.title = state.mode === 'online' ? '联机对局暂不支持悔棋' : '';
    const onlineControl = state.mode === 'online';
    dom.restartBtn.disabled = onlineControl && (!state.net.connected || state.net.role !== 'host' || state.net.phase !== 'playing');
    dom.restartBtn.title = onlineControl && state.net.role !== 'host' ? '联机对局由房主重新开始' : '';
    dom.leaveRoomBtn.hidden = !onlineControl;
    dom.soundBtn.setAttribute('aria-pressed', String(state.soundOn));
  }

  function renderMoves() {
    const frag = document.createDocumentFragment();
    const totalLines = Math.ceil(state.moves.length / 2);
    for (let i = 0; i < totalLines; i++) {
      const line = document.createElement('div');
      line.className = 'move-line';
      const index = document.createElement('span');
      index.className = 'move-index';
      index.textContent = `${i + 1}.`;
      line.appendChild(index);

      for (const move of [state.moves[i * 2], state.moves[i * 2 + 1]]) {
        const span = document.createElement('span');
        span.className = 'move-pill';
        if (!move) {
          span.classList.add('empty');
          span.textContent = '—';
        } else {
          const label = LABELS[move.side][move.type];
          span.classList.add(move.side);
          span.textContent = `${label} ${move.from.c + 1}-${move.from.r + 1} → ${move.to.c + 1}-${move.to.r + 1}${move.captured ? ' 吃' : ''}`;
          span.title = `${SIDE_NAME[move.side]}${label}：${posText(move.from)} → ${posText(move.to)}${move.captured ? '（吃子）' : ''}`;
        }
        line.appendChild(span);
      }
      frag.appendChild(line);
    }
    dom.moveList.replaceChildren(frag);
    dom.moveCount.textContent = `${state.moves.length} 手`;
    dom.moveList.scrollTop = dom.moveList.scrollHeight;
  }

  function render() {
    renderModeAndRail();
    renderPlayerRows();
    renderStatus();
    renderBoard();
    renderMoves();
    updateSoundButton();
  }

  /* ======================================================================
     6. 落子、悔棋与重开
     ====================================================================== */
  function resetBoardState(orientation = 'red') {
    state.board = Engine.initialBoard();
    state.turn = 'red';
    state.selected = null;
    state.history = [];
    state.moves = [];
    state.lastMove = null;
    state.gameOver = false;
    state.winner = null;
    state.endReason = '';
    state.inCheck = false;
    state.orientation = orientation;
  }

  function applyMove(from, to, options = {}) {
    const { recordHistory = false, sound = true } = options;
    const piece = state.board[from.r] && state.board[from.r][from.c];
    if (!piece || piece.side !== state.turn) return null;
    const legal = Engine.getLegalMoves(state.board, from.r, from.c, piece.side)
      .find(move => move.r === to.r && move.c === to.c);
    if (!legal) return null;

    if (recordHistory) state.history.push(snapshotState());
    const captured = state.board[to.r][to.c];
    state.board[to.r][to.c] = piece;
    state.board[from.r][from.c] = null;
    state.lastMove = { from: { ...from }, to: { ...to } };
    state.moves.push({
      side: piece.side,
      type: piece.type,
      from: { ...from },
      to: { ...to },
      captured: captured ? captured.type : null
    });
    state.turn = otherSide(piece.side);
    state.selected = null;
    state.inCheck = Engine.isInCheck(state.board, state.turn);
    const replies = Engine.allLegalMoves(state.board, state.turn);
    if (replies.length === 0) {
      state.gameOver = true;
      state.winner = piece.side;
      state.endReason = state.inCheck ? '将死' : '困毙';
    }
    if (sound) playMoveSound(Boolean(captured));
    render();
    return { piece, captured, gameOver: state.gameOver };
  }

  function selectedMoves() {
    if (!state.selected) return [];
    const p = state.board[state.selected.r] && state.board[state.selected.r][state.selected.c];
    if (!p || p.side !== state.turn) return [];
    return Engine.getLegalMoves(state.board, state.selected.r, state.selected.c, state.turn);
  }

  function handleBoardClick(r, c) {
    if (!canPlayNow()) return;
    const p = state.board[r][c];
    if (state.selected) {
      const legal = selectedMoves();
      if (legal.some(move => move.r === r && move.c === c)) {
        makeLocalMove(state.selected, { r, c });
        return;
      }
    }
    if (p && p.side === state.turn) {
      state.selected = { r, c };
    } else {
      state.selected = null;
    }
    renderBoard();
    renderStatus();
  }

  function makeLocalMove(from, to) {
    if (state.mode === 'online') {
      if (state.net.role === 'guest') {
        requestGuestMove(from, to);
      } else if (state.net.role === 'host') {
        const result = applyMove(from, to, { recordHistory: false });
        if (result) {
          netSend({ type: 'move', from, to, seq: state.moves.length, gameId: state.net.gameId });
        }
      }
      return;
    }

    const result = applyMove(from, to, { recordHistory: state.mode === 'local' });
    if (!result) return;

    if (state.mode === 'ai') {
      if (!state.gameOver) {
        if (state.turn === state.ai.humanSide) {
          pushAiAnchor();
        } else {
          scheduleAiMove();
        }
      }
      renderStatus();
    }
  }

  function localUndoEnabled() {
    if (state.mode === 'local') return state.history.length > 0;
    if (state.mode === 'ai') {
      const anchors = state.ai.anchors;
      if (!anchors.length) return false;
      const last = anchors[anchors.length - 1];
      return state.moves.length > last.moves.length || anchors.length > 1;
    }
    return false;
  }

  function canUndo() {
    return localUndoEnabled();
  }

  function undoMove() {
    if (state.mode === 'online') return;
    if (state.mode === 'local') {
      if (!state.history.length) return;
      const snapshot = state.history.pop();
      cancelAiWork();
      restoreState(snapshot);
      render();
      return;
    }
    if (state.mode === 'ai') {
      const anchors = state.ai.anchors;
      if (!anchors.length) return;
      const last = anchors[anchors.length - 1];
      cancelAiWork();
      if (state.moves.length > last.moves.length) {
        restoreState(last);
      } else if (anchors.length > 1) {
        anchors.pop();
        restoreState(anchors[anchors.length - 1]);
      } else {
        return;
      }
      render();
    }
  }

  function restartCurrentGame() {
    if (state.mode === 'online') {
      if (state.net.role !== 'host' || !state.net.connected || state.net.phase !== 'playing') return;
      if (!window.confirm('确定重新开始本局吗？双方棋盘将同时重置。')) return;
      state.net.gameId++;
      netSend({ type: 'restart', gameId: state.net.gameId });
      resetOnlineBoard();
      showToast('已重新开始对局');
      return;
    }

    if (state.mode === 'ai') {
      cancelAiWork();
      resetBoardState(state.ai.humanSide);
      state.ai.anchors = [];
      state.inCheck = false;
      render();
      if (state.turn !== state.ai.humanSide) {
        state.ai.startTimer = setTimeout(() => {
          state.ai.startTimer = null;
          if (state.mode === 'ai' && !state.gameOver) scheduleAiMove();
        }, 420);
      } else {
        pushAiAnchor();
      }
      render();
      return;
    }

    cancelAiWork();
    resetBoardState('red');
    render();
  }

  function pushAiAnchor() {
    if (state.mode !== 'ai' || state.gameOver) return;
    if (state.turn !== state.ai.humanSide) return;
    state.ai.anchors.push(snapshotState());
  }

  /* ======================================================================
     7. 自我对战与 AI 模式
     ====================================================================== */
  function cancelAiWork() {
    state.ai.requestId++;
    state.ai.thinking = false;
    if (state.ai.worker) {
      try { state.ai.worker.terminate(); } catch { /* ignore */ }
      state.ai.worker = null;
    }
    if (state.ai.timer) {
      clearTimeout(state.ai.timer);
      state.ai.timer = null;
    }
    if (state.ai.startTimer) {
      clearTimeout(state.ai.startTimer);
      state.ai.startTimer = null;
    }
    if (state.ai.fallbackTimer) {
      clearTimeout(state.ai.fallbackTimer);
      state.ai.fallbackTimer = null;
    }
  }

  function startLocalGame(showMessage = false) {
    cancelAiWork();
    leaveOnline({ silent: true, fallbackToLocal: false });
    state.mode = 'local';
    state.ai = freshAIState();
    resetBoardState('red');
    render();
    if (showMessage) showToast('已切换到自我对战');
  }

  function openAiSetup() {
    dom.aiSetup.hidden = false;
    dom.roomSetup.hidden = true;
    dom.setupDialog.setAttribute('aria-labelledby', 'aiTitle');
    updateAiSetup();
    showDialog(dom.setupDialog);
  }

  function updateAiSetup() {
    for (const btn of dom.levelGroup.querySelectorAll('[data-level]')) {
      btn.setAttribute('aria-pressed', String(btn.dataset.level === setupDraft.level));
    }
    for (const btn of dom.aiSideGroup.querySelectorAll('[data-side]')) {
      btn.setAttribute('aria-pressed', String(btn.dataset.side === setupDraft.side));
    }
    const level = AI_LEVELS[setupDraft.level].label;
    dom.aiSummary.textContent = `你执${SIDE_COLOR_NAME[setupDraft.side]}，AI 执${SIDE_COLOR_NAME[otherSide(setupDraft.side)]} · ${level}难度`;
  }

  function startAIGame(level, humanSide) {
    if (!AI_LEVELS[level] || !isSide(humanSide)) return;
    closeDialog(dom.setupDialog);
    cancelAiWork();
    leaveOnline({ silent: true, fallbackToLocal: false });
    state.mode = 'ai';
    state.ai = freshAIState();
    state.ai.level = level;
    state.ai.humanSide = humanSide;
    resetBoardState(humanSide);
    render();

    if (state.turn !== humanSide) {
      state.ai.startTimer = setTimeout(() => {
        state.ai.startTimer = null;
        if (state.mode === 'ai' && !state.gameOver) scheduleAiMove();
      }, 420);
    } else {
      pushAiAnchor();
    }
    render();
    showToast(`AI 对决开始 · ${AI_LEVELS[level].label}难度`);
  }

  function requestAiWorker(side, level, token, onResult) {
    const board = Engine.cloneBoard(state.board);
    const aiSide = side;
    const finish = result => {
      if (token !== state.ai.requestId) return;
      onResult(result);
    };

    const fallback = () => {
      if (token !== state.ai.requestId) return;
      let result = null;
      try {
        result = Engine.chooseMove(Engine.cloneBoard(board), aiSide, level);
      } catch {
        result = null;
      }
      finish(result);
    };

    if (aiReady && aiWorkerUrl) {
      let worker = null;
      try {
        worker = new Worker(aiWorkerUrl);
        state.ai.worker = worker;
        let settled = false;
        const settle = result => {
          if (settled) return;
          settled = true;
          if (state.ai.fallbackTimer) {
            clearTimeout(state.ai.fallbackTimer);
            state.ai.fallbackTimer = null;
          }
          try { worker.terminate(); } catch { /* ignore */ }
          if (state.ai.worker === worker) state.ai.worker = null;
          finish(result);
        };
        worker.onmessage = event => {
          const data = event.data || {};
          if (data.ok && data.result) {
            settle(data.result);
          } else {
            settled = true;
            try { worker.terminate(); } catch { /* ignore */ }
            if (state.ai.worker === worker) state.ai.worker = null;
            fallback();
          }
        };
        worker.onerror = () => {
          settled = true;
          try { worker.terminate(); } catch { /* ignore */ }
          if (state.ai.worker === worker) state.ai.worker = null;
          fallback();
        };
        state.ai.fallbackTimer = setTimeout(() => {
          if (settled) return;
          settled = true;
          try { worker.terminate(); } catch { /* ignore */ }
          if (state.ai.worker === worker) state.ai.worker = null;
          fallback();
        }, 4500);
        worker.postMessage({ board, side, level });
        return;
      } catch {
        if (worker) {
          try { worker.terminate(); } catch { /* ignore */ }
        }
        state.ai.worker = null;
      }
    }

    state.ai.fallbackTimer = setTimeout(() => {
      state.ai.fallbackTimer = null;
      fallback();
    }, 30);
  }

  function scheduleAiMove() {
    if (state.mode !== 'ai' || state.gameOver) {
      state.ai.thinking = false;
      return;
    }
    if (state.turn === state.ai.humanSide) {
      state.ai.thinking = false;
      render();
      return;
    }
    cancelAiWork();
    const token = state.ai.requestId;
    state.ai.thinking = true;
    state.selected = null;
    state.ai.anchors = state.ai.anchors || [];
    render();

    const side = state.turn;
    const level = state.ai.level;
    const started = performance.now();
    const minDelay = AI_LEVELS[level].minDelay;

    requestAiWorker(side, level, token, result => {
      if (token !== state.ai.requestId || state.mode !== 'ai' || state.gameOver || state.turn === state.ai.humanSide) {
        return;
      }
      const wait = Math.max(0, minDelay - (performance.now() - started));
      state.ai.timer = setTimeout(() => {
        state.ai.timer = null;
        if (token !== state.ai.requestId || state.mode !== 'ai' || state.gameOver) return;
        const legal = Engine.allLegalMoves(state.board, state.turn);
        if (!legal.length) return;
        let chosen = null;
        if (result && result.move) {
          chosen = legal.find(move =>
            move.fr === result.move.fr && move.fc === result.move.fc &&
            move.tr === result.move.tr && move.tc === result.move.tc
          );
        }
        if (!chosen) chosen = legal[Math.floor(Math.random() * legal.length)];
        state.ai.thinking = false;
        const applied = applyMove(
          { r: chosen.fr, c: chosen.fc },
          { r: chosen.tr, c: chosen.tc },
          { recordHistory: false }
        );
        if (!applied) {
          state.ai.thinking = false;
          render();
          return;
        }
        if (!state.gameOver && state.turn === state.ai.humanSide) pushAiAnchor();
        render();
      }, wait);
    });
  }

  /* ======================================================================
     8. 联机房间：连接与大厅
     ====================================================================== */
  function netSend(message) {
    const conn = state.net.conn;
    if (!conn || !conn.open) return false;
    try {
      conn.send(message);
      return true;
    } catch {
      return false;
    }
  }

  function generateRoomCode() {
    const values = new Uint32Array(1);
    if (window.crypto && crypto.getRandomValues) crypto.getRandomValues(values);
    else values[0] = Math.floor(Math.random() * 0xffffffff);
    return String(100000 + (values[0] % 900000));
  }

  function clearNetTimers() {
    const net = state.net;
    if (net.pendingTimer) clearTimeout(net.pendingTimer);
    if (net.joinTimer) clearTimeout(net.joinTimer);
    if (net.handshakeTimer) clearTimeout(net.handshakeTimer);
    net.pendingTimer = null;
    net.joinTimer = null;
    net.handshakeTimer = null;
  }

  function disposeOnline(notifyRemote = false) {
    const net = state.net;
    net.closing = true;
    clearNetTimers();
    if (notifyRemote && net.conn && net.conn.open) {
      try { net.conn.send({ type: 'leave' }); } catch { /* ignore */ }
    }
    try { if (net.conn) net.conn.close(); } catch { /* ignore */ }
    try { if (net.peer) net.peer.destroy(); } catch { /* ignore */ }
    state.net = freshNetState();
    closeRpsDialog(false);
    dom.leaveRoomBtn.hidden = true;
  }

  function enterOnlineLobby() {
    cancelAiWork();
    state.mode = 'online';
    if (state.net.phase !== 'lobby') state.net.phase = 'lobby';
    if (state.moves.length || state.gameOver) {
      resetBoardState('red');
    } else {
      state.board = Engine.initialBoard();
      state.turn = 'red';
      state.selected = null;
      state.gameOver = false;
    }
    render();
  }

  function leaveOnline(options = {}) {
    const { silent = false, fallbackToLocal = true, notifyRemote = true } = options;
    const wasOnline = state.mode === 'online' || state.net.role;
    if (!wasOnline && !state.net.peer) {
      if (fallbackToLocal) {
        state.mode = 'local';
        resetBoardState('red');
        render();
      }
      return;
    }
    cancelAiWork();
    disposeOnline(notifyRemote);
    closeDialog(dom.setupDialog);
    state.mode = 'local';
    if (fallbackToLocal) {
      resetBoardState('red');
      render();
      if (!silent) showToast('已退出房间');
    } else {
      render();
    }
  }

  function handleConnectionLost(message = '对方已离开，房间已关闭') {
    if (state.net.closing) return;
    const wasOnline = state.mode === 'online' || Boolean(state.net.role);
    disposeOnline(false);
    closeDialog(dom.setupDialog);
    if (wasOnline) {
      state.mode = 'local';
      resetBoardState('red');
      render();
      showToast(message, 4200);
    }
  }

  function showRoomError(message) {
    dom.roomError.textContent = message;
    dom.roomError.hidden = false;
  }

  function clearRoomError() {
    dom.roomError.textContent = '';
    dom.roomError.hidden = true;
  }

  function showRoomStage(stage) {
    const lobby = stage === 'lobby';
    dom.roomChoice.hidden = lobby;
    dom.roomLobby.hidden = !lobby;
  }

  function selectRoomTab(tab) {
    const create = tab === 'create';
    dom.createRoomTab.classList.toggle('active', create);
    dom.joinRoomTab.classList.toggle('active', !create);
    dom.createRoomTab.setAttribute('aria-selected', String(create));
    dom.joinRoomTab.setAttribute('aria-selected', String(!create));
    dom.createRoomPane.hidden = !create;
    dom.joinRoomPane.hidden = create;
    clearRoomError();
  }

  function openRoomSetup() {
    if (state.mode === 'online' && ['rps', 'playing'].includes(state.net.phase)) {
      showToast('联机对局进行中，可在棋盘下方退出房间');
      return;
    }
    dom.aiSetup.hidden = true;
    dom.roomSetup.hidden = false;
    dom.setupDialog.setAttribute('aria-labelledby', 'roomTitle');
    if (state.net.role) {
      showRoomStage('lobby');
      updateLobby();
    } else {
      showRoomStage('choice');
      selectRoomTab('create');
    }
    clearRoomError();
    showDialog(dom.setupDialog);
  }

  function createRoom() {
    if (typeof window.Peer !== 'function') {
      showRoomError('联机组件未加载，请刷新页面后重试。');
      return;
    }
    clearRoomError();
    if (state.net.peer) disposeOnline(false);
    const net = freshNetState();
    net.role = 'host';
    net.phase = 'creating';
    state.net = net;
    dom.hostBadge.textContent = '房主';
    dom.lobbyCode.textContent = '------';
    dom.roomCodeInput.value = '';
    showRoomStage('lobby');
    updateLobby('正在创建房间…', 'waiting');
    createHostPeer(0);
  }

  function createHostPeer(attempt) {
    const net = state.net;
    if (net.role !== 'host' || net.closing) return;
    const code = generateRoomCode();
    net.code = code;
    net.generation++;
    const generation = net.generation;
    net.phase = 'creating';
    dom.lobbyCode.textContent = code;
    updateLobby('正在连接联机服务…', 'waiting');

    let peer;
    try {
      peer = new Peer(`xq1-${code}`, { debug: 0 });
    } catch {
      showRoomError('无法初始化联机连接，请检查浏览器是否支持 WebRTC。');
      disposeOnline(false);
      showRoomStage('choice');
      selectRoomTab('create');
      return;
    }
    net.peer = peer;

    peer.on('open', () => {
      if (state.net !== net || generation !== net.generation || net.closing) {
        try { peer.destroy(); } catch { /* ignore */ }
        return;
      }
      net.phase = 'lobby';
      enterOnlineLobby();
      updateLobby('房间已创建，等待对方输入房间号加入。', 'waiting');
    });

    peer.on('connection', conn => {
      if (state.net !== net || generation !== net.generation || net.closing) {
        try { conn.close(); } catch { /* ignore */ }
        return;
      }
      if (net.conn) {
        try { conn.close(); } catch { /* ignore */ }
        return;
      }
      net.conn = conn;
      bindHostConnection(conn);
    });

    peer.on('error', error => {
      if (state.net !== net || generation !== net.generation || net.closing) return;
      if (error && error.type === 'unavailable-id' && attempt < 3) {
        try { peer.destroy(); } catch { /* ignore */ }
        if (net.peer === peer) net.peer = null;
        setTimeout(() => {
          if (state.net === net && net.role === 'host' && !net.closing) createHostPeer(attempt + 1);
        }, 180);
        return;
      }
      const preLobby = net.phase === 'creating';
      const message = error && error.type === 'network'
        ? '联机服务连接失败，请检查网络后重试。'
        : error && error.type === 'browser-incompatible'
          ? '当前浏览器不支持 WebRTC 联机。'
          : '房间创建失败，请稍后重试。';
      disposeOnline(false);
      state.mode = 'local';
      resetBoardState('red');
      render();
      if (preLobby) {
        openRoomSetup();
        showRoomStage('choice');
        selectRoomTab('create');
        showRoomError(message);
      } else {
        showToast(message, 4200);
      }
    });
  }

  function joinRoom() {
    if (typeof window.Peer !== 'function') {
      showRoomError('联机组件未加载，请刷新页面后重试。');
      return;
    }
    const code = dom.roomCodeInput.value.replace(/\D/g, '');
    if (code.length !== 6) {
      showRoomError('请输入完整的 6 位房间号。');
      dom.roomCodeInput.focus();
      return;
    }
    clearRoomError();
    if (state.net.peer) disposeOnline(false);
    const net = freshNetState();
    net.role = 'guest';
    net.phase = 'joining';
    net.code = code;
    state.net = net;
    dom.hostBadge.textContent = '访客';
    dom.lobbyCode.textContent = code;
    showRoomStage('lobby');
    updateLobby('正在连接房间…', 'waiting');

    let peer;
    try {
      peer = new Peer(undefined, { debug: 0 });
    } catch {
      showRoomError('无法初始化联机连接，请检查浏览器是否支持 WebRTC。');
      return;
    }
    net.peer = peer;

    net.joinTimer = setTimeout(() => {
      if (state.net === net && net.role === 'guest' && !net.connected) {
        failJoin('连接超时，请检查房间号与网络后重试。');
      }
    }, 18000);

    peer.on('open', () => {
      if (state.net !== net || net.closing || net.role !== 'guest') return;
      let conn;
      try {
        conn = peer.connect(`xq1-${code}`, { reliable: true, serialization: 'json' });
      } catch {
        failJoin('无法连接这个房间，请稍后重试。');
        return;
      }
      net.conn = conn;
      bindGuestConnection(conn);
    });

    peer.on('error', error => {
      if (state.net !== net || net.closing) return;
      if (error && error.type === 'peer-unavailable') {
        failJoin('未找到这个房间，请核对房间号。');
      } else if (!net.connected) {
        failJoin(error && error.type === 'network'
          ? '联机服务连接失败，请检查网络后重试。'
          : '加入房间失败，请稍后重试。');
      } else {
        handleConnectionLost('联机连接中断，房间已关闭');
      }
    });
  }

  function failJoin(message) {
    if (state.net.connected) {
      handleConnectionLost(message);
      return;
    }
    disposeOnline(false);
    state.mode = 'local';
    resetBoardState('red');
    render();
    openRoomSetup();
    showRoomStage('choice');
    selectRoomTab('join');
    dom.roomCodeInput.value = state.net.code || dom.roomCodeInput.value.replace(/\D/g, '').slice(0, 6);
    showRoomError(message);
  }

  function bindHostConnection(conn) {
    const net = state.net;
    conn.on('open', () => {
      if (state.net !== net || net.closing || net.role !== 'host') return;
      net.connected = true;
      net.phase = 'lobby';
      enterOnlineLobby();
      netSend({
        type: 'welcome',
        hostSide: net.hostSide,
        guestSide: net.guestSide
      });
      updateLobby('对方已加入，请选择阵容。', 'online');
      if (!dom.setupDialog.open) showToast('对方已加入房间，请打开「自定义房间」选择阵容', 4200);
    });
    conn.on('data', data => {
      if (state.net !== net || net.closing) return;
      const message = normalizeMessage(data);
      if (message) handleHostMessage(message);
    });
    conn.on('close', () => {
      if (state.net !== net || net.closing) return;
      handleConnectionLost('对方已离开，房间已关闭');
    });
    conn.on('error', () => {
      if (state.net !== net || net.closing) return;
      handleConnectionLost('连接异常，房间已关闭');
    });
    updateLobby('对方正在建立连接…', 'waiting');
  }

  function bindGuestConnection(conn) {
    const net = state.net;
    conn.on('open', () => {
      if (state.net !== net || net.closing || net.role !== 'guest') return;
      net.connected = true;
      net.phase = 'lobby';
      if (net.joinTimer) {
        clearTimeout(net.joinTimer);
        net.joinTimer = null;
      }
      enterOnlineLobby();
      netSend({ type: 'hello' });
      updateLobby('已连接，正在等待房主信息…', 'online');
      net.handshakeTimer = setTimeout(() => {
        if (state.net === net && net.connected && !net.closing && net.phase === 'lobby' && !net.hostSide) {
          failJoin('房间响应超时，请重新加入。');
        }
      }, 8000);
    });
    conn.on('data', data => {
      if (state.net !== net || net.closing) return;
      const message = normalizeMessage(data);
      if (message) handleGuestMessage(message);
    });
    conn.on('close', () => {
      if (state.net !== net || net.closing) return;
      handleConnectionLost('房主已离开，房间已关闭');
    });
    conn.on('error', () => {
      if (state.net !== net || net.closing) return;
      handleConnectionLost('连接异常，房间已关闭');
    });
  }

  function normalizeMessage(data) {
    if (!data) return null;
    if (typeof data === 'string') {
      try {
        const parsed = JSON.parse(data);
        return parsed && typeof parsed === 'object' ? parsed : null;
      } catch {
        return null;
      }
    }
    return typeof data === 'object' ? data : null;
  }

  function chooseRoomSide(side) {
    if (!isSide(side)) return;
    const net = state.net;
    if (!net.role || !net.connected || net.phase !== 'lobby') return;
    if (net.role === 'host') {
      net.hostSide = side;
      net.mySide = side;
      broadcastSideUpdate();
    } else {
      net.guestSide = side;
      net.mySide = side;
      netSend({ type: 'side', side });
    }
    updateLobby();
  }

  function broadcastSideUpdate() {
    netSend({
      type: 'sideUpdate',
      hostSide: state.net.hostSide,
      guestSide: state.net.guestSide
    });
  }

  function updateLobby(statusText = null, statusClass = null) {
    const net = state.net;
    dom.lobbyCode.textContent = net.code || '------';
    dom.hostBadge.textContent = net.role === 'host' ? '房主' : '访客';

    let status = statusText;
    let cls = statusClass;
    if (status === null) {
      if (net.phase === 'creating') {
        status = '正在创建房间…';
        cls = 'waiting';
      } else if (net.phase === 'joining') {
        status = '正在连接房间…';
        cls = 'waiting';
      } else if (net.connected) {
        status = '已连接，可以开始选择阵容。';
        cls = 'online';
      } else {
        status = '等待对方加入房间。';
        cls = 'waiting';
      }
    }
    dom.lobbyStatus.className = `room-status ${cls || ''}`.trim();
    dom.lobbyStatusText.textContent = status;

    const canChoose = net.connected && net.phase === 'lobby';
    for (const btn of dom.roomSideGroup.querySelectorAll('[data-room-side]')) {
      btn.disabled = !canChoose;
      btn.setAttribute('aria-pressed', String(btn.dataset.roomSide === net.mySide));
    }

    const opponentSide = net.role === 'host' ? net.guestSide : net.hostSide;
    if (!net.connected) {
      dom.opponentSideText.textContent = '等待对方加入后选择阵容。';
    } else if (opponentSide) {
      dom.opponentSideText.innerHTML = `对方选择：<strong>${SIDE_COLOR_NAME[opponentSide]}</strong>`;
    } else {
      dom.opponentSideText.textContent = '对方尚未选择阵容。';
    }

    const conflict = Boolean(net.hostSide && net.guestSide && net.hostSide === net.guestSide);
    dom.sideConflictNote.hidden = !conflict || !canChoose;

    const host = net.role === 'host';
    dom.hostStartWrap.hidden = !host;
    dom.guestWaitText.hidden = host;
    dom.startRoomBtn.disabled = !(host && canChoose && net.hostSide && net.guestSide);

    if (host) {
      if (!net.connected) {
        dom.hostStartHint.textContent = '等待对方加入并选择阵容。';
      } else if (!net.hostSide) {
        dom.hostStartHint.textContent = '请先选择你的阵容。';
      } else if (!net.guestSide) {
        dom.hostStartHint.textContent = '等待对方选择阵容。';
      } else if (conflict) {
        dom.hostStartHint.textContent = '双方阵营相同，开始后将进行剪刀石头布。';
      } else {
        dom.hostStartHint.textContent = '双方阵容已确定，可以开始对弈。';
      }
    }
    renderModeAndRail();
  }

  function handleHostMessage(message) {
    const net = state.net;
    switch (message.type) {
      case 'hello':
        break;
      case 'side':
        if (net.phase !== 'lobby' || !isSide(message.side)) break;
        net.guestSide = message.side;
        broadcastSideUpdate();
        updateLobby();
        break;
      case 'moveRequest':
        hostApplyGuestMove(message);
        break;
      case 'rpsPick':
        hostReceiveRpsPick(message);
        break;
      case 'leave':
        handleConnectionLost('对方已离开，房间已关闭');
        break;
      default:
        break;
    }
  }

  function handleGuestMessage(message) {
    const net = state.net;
    switch (message.type) {
      case 'welcome':
        if (net.handshakeTimer) {
          clearTimeout(net.handshakeTimer);
          net.handshakeTimer = null;
        }
        if (isSide(message.hostSide)) net.hostSide = message.hostSide;
        if (isSide(message.guestSide)) net.guestSide = message.guestSide;
        net.phase = 'lobby';
        updateLobby('已连接，请选择你的阵容。', 'online');
        break;
      case 'sideUpdate':
        if (isSide(message.hostSide)) net.hostSide = message.hostSide;
        if (isSide(message.guestSide)) net.guestSide = message.guestSide;
        updateLobby();
        break;
      case 'start':
        if (isSide(message.hostSide) && isSide(message.guestSide) && message.hostSide !== message.guestSide) {
          beginOnlineGame(message.hostSide, message.guestSide, message.gameId);
        }
        break;
      case 'move':
        receiveGuestMove(message);
        break;
      case 'moveRejected':
        clearPendingMove();
        render();
        showToast('落子未通过同步，请再试一次');
        break;
      case 'rpsStart':
        beginRpsGuest();
        break;
      case 'rpsReveal':
        guestReceiveRpsReveal(message);
        break;
      case 'rpsNext':
        guestReceiveRpsNext(message);
        break;
      case 'restart':
        if (net.phase === 'playing') {
          if (Number.isInteger(message.gameId)) net.gameId = message.gameId;
          resetOnlineBoard();
          showToast('房主重新开始了对局');
        }
        break;
      case 'leave':
        handleConnectionLost('对方已离开，房间已关闭');
        break;
      default:
        break;
    }
  }

  function hostApplyGuestMove(message) {
    const net = state.net;
    if (net.role !== 'host' || net.phase !== 'playing' || !net.connected) return;
    if (message.gameId !== net.gameId) return;
    if (state.turn !== net.guestSide || state.gameOver) {
      netSend({ type: 'moveRejected' });
      return;
    }
    const from = message.from;
    const to = message.to;
    if (!from || !to || !Number.isInteger(from.r) || !Number.isInteger(from.c) ||
        !Number.isInteger(to.r) || !Number.isInteger(to.c)) {
      netSend({ type: 'moveRejected' });
      return;
    }
    const result = applyMove(from, to, { recordHistory: false });
    if (!result) {
      netSend({ type: 'moveRejected' });
      return;
    }
    netSend({ type: 'move', from, to, seq: state.moves.length, gameId: net.gameId });
    render();
  }

  function requestGuestMove(from, to) {
    const net = state.net;
    if (net.role !== 'guest' || net.phase !== 'playing' || !net.connected || net.pendingMove) return;
    if (state.turn !== net.mySide || state.gameOver) return;
    const legal = Engine.getLegalMoves(state.board, from.r, from.c, state.turn)
      .some(move => move.r === to.r && move.c === to.c);
    if (!legal) return;
    net.pendingMove = true;
    state.selected = null;
    if (net.pendingTimer) clearTimeout(net.pendingTimer);
    net.pendingTimer = setTimeout(() => {
      if (state.net.pendingMove) {
        clearPendingMove();
        render();
        showToast('落子同步超时，请重试');
      }
    }, 6000);
    if (!netSend({ type: 'moveRequest', from, to, gameId: net.gameId })) {
      clearPendingMove();
      render();
      showToast('连接已中断，无法落子');
      return;
    }
    render();
  }

  function receiveGuestMove(message) {
    const net = state.net;
    if (net.role !== 'guest' || net.phase !== 'playing') return;
    if (message.gameId !== net.gameId) return;
    if (state.gameOver) return;
    const from = message.from;
    const to = message.to;
    if (!from || !to || !Number.isInteger(from.r) || !Number.isInteger(from.c) ||
        !Number.isInteger(to.r) || !Number.isInteger(to.c)) return;
    clearPendingMove();
    const result = applyMove(from, to, { recordHistory: false });
    if (!result) {
      showToast('同步异常，请重新进入房间');
    }
    render();
  }

  function clearPendingMove() {
    state.net.pendingMove = false;
    if (state.net.pendingTimer) {
      clearTimeout(state.net.pendingTimer);
      state.net.pendingTimer = null;
    }
  }

  function hostStartGame() {
    const net = state.net;
    if (net.role !== 'host' || !net.connected || net.phase !== 'lobby') return;
    if (!net.hostSide || !net.guestSide) return;
    if (net.hostSide === net.guestSide) {
      net.phase = 'rps';
      beginRpsHost();
      netSend({ type: 'rpsStart' });
    } else {
      const gameId = (net.gameId || 0) + 1;
      net.gameId = gameId;
      net.phase = 'playing';
      closeDialog(dom.setupDialog);
      netSend({
        type: 'start',
        hostSide: net.hostSide,
        guestSide: net.guestSide,
        gameId
      });
      beginOnlineGame(net.hostSide, net.guestSide, gameId);
    }
  }

  function beginOnlineGame(hostSide, guestSide, gameId) {
    const net = state.net;
    if (!isSide(hostSide) || !isSide(guestSide)) return;
    cancelAiWork();
    closeDialog(dom.setupDialog);
    closeRpsDialog(false);
    state.mode = 'online';
    net.phase = 'playing';
    net.hostSide = hostSide;
    net.guestSide = guestSide;
    net.mySide = net.role === 'host' ? hostSide : guestSide;
    net.gameId = Number.isInteger(gameId) ? gameId : (net.gameId || 0) + 1;
    net.pendingMove = false;
    clearPendingMove();
    resetBoardState(net.mySide);
    render();
    showToast(`对局开始 · 你执${SIDE_COLOR_NAME[net.mySide]}`);
  }

  function resetOnlineBoard() {
    const net = state.net;
    if (net.phase !== 'playing') return;
    clearPendingMove();
    cancelAiWork();
    resetBoardState(net.mySide || 'red');
    render();
  }

  function exitRoom() {
    if (!state.net.role) {
      closeDialog(dom.setupDialog);
      return;
    }
    leaveOnline({ fallbackToLocal: true, notifyRemote: true });
  }

  /* ======================================================================
     9. 剪刀石头布
     ====================================================================== */
  function updateRpsUi() {
    const myWins = rps.role === 'host' ? rps.hostWins : rps.guestWins;
    const oppWins = rps.role === 'host' ? rps.guestWins : rps.hostWins;
    dom.rpsMyScore.textContent = String(myWins);
    dom.rpsOppScore.textContent = String(oppWins);
    dom.rpsRound.textContent = `第 ${rps.round} 回合 · 率先赢下 2 回合`;

    const myChoice = rps.role === 'host' ? rps.hostChoice : rps.guestChoice;
    for (const btn of dom.rpsChoices.querySelectorAll('[data-rps-choice]')) {
      const picked = btn.dataset.rpsChoice === myChoice;
      btn.classList.toggle('picked', picked);
      btn.disabled = rps.phase !== 'pick' || Boolean(myChoice);
    }

    if (rps.phase === 'reveal') {
      dom.rpsReveal.hidden = false;
      const myHand = rps.role === 'host' ? rps.hostChoice : rps.guestChoice;
      const oppHand = rps.role === 'host' ? rps.guestChoice : rps.hostChoice;
      dom.rpsMyHand.textContent = myHand ? RPS_HANDS[myHand].label : '—';
      dom.rpsOppHand.textContent = oppHand ? RPS_HANDS[oppHand].label : '—';

      const myWonRound = myHand && oppHand && RPS_BEATS[myHand] === oppHand;
      const oppWonRound = myHand && oppHand && RPS_BEATS[oppHand] === myHand;
      let resultText;
      if (myWonRound) resultText = '你赢下本回合。';
      else if (oppWonRound) resultText = '对方赢下本回合。';
      else resultText = '本回合平局。';

      if (rps.final) {
        const myFinalSide = rps.role === 'host'
          ? (rps.hostWins > rps.guestWins ? rps.side : otherSide(rps.side))
          : (rps.guestWins > rps.hostWins ? rps.side : otherSide(rps.side));
        resultText += ` 你最终执${SIDE_COLOR_NAME[myFinalSide]}。`;
        dom.rpsFooter.textContent = '结果已确定，即将进入对局…';
      } else {
        dom.rpsFooter.textContent = '下一回合即将开始…';
      }
      dom.rpsResult.textContent = resultText;
    } else {
      dom.rpsReveal.hidden = true;
      const waiting = Boolean(myChoice);
      dom.rpsFooter.textContent = waiting ? '已出拳，等待对方…' : '请选择你的手势';
    }
    dom.rpsSub.textContent = rps.side
      ? `双方都选择了${SIDE_COLOR_NAME[rps.side]}。胜者执所选阵容，败者自动执另一阵容。`
      : '双方选择了同一阵容，赢家执所选阵容，输家自动执另一阵容。';
  }

  function beginRpsHost() {
    closeDialog(dom.setupDialog);
    const net = state.net;
    Object.assign(rps, {
      active: true,
      role: 'host',
      round: 1,
      hostWins: 0,
      guestWins: 0,
      hostChoice: null,
      guestChoice: null,
      side: net.hostSide,
      phase: 'pick',
      final: false,
      timer: null
    });
    net.phase = 'rps';
    updateRpsUi();
    showDialog(dom.rpsDialog);
    render();
  }

  function beginRpsGuest() {
    closeDialog(dom.setupDialog);
    const net = state.net;
    Object.assign(rps, {
      active: true,
      role: 'guest',
      round: 1,
      hostWins: 0,
      guestWins: 0,
      hostChoice: null,
      guestChoice: null,
      side: net.guestSide || net.hostSide,
      phase: 'pick',
      final: false,
      timer: null
    });
    net.phase = 'rps';
    updateRpsUi();
    showDialog(dom.rpsDialog);
    render();
  }

  function pickRps(choice) {
    if (!rps.active || rps.phase !== 'pick' || !RPS_HANDS[choice]) return;
    if (rps.role === 'host') {
      if (rps.hostChoice) return;
      rps.hostChoice = choice;
      updateRpsUi();
      hostResolveRps();
    } else {
      if (rps.guestChoice) return;
      rps.guestChoice = choice;
      netSend({ type: 'rpsPick', round: rps.round, choice });
      updateRpsUi();
    }
  }

  function hostReceiveRpsPick(message) {
    if (state.net.role !== 'host' || !rps.active || rps.phase !== 'pick') return;
    if (message.round !== rps.round || !RPS_HANDS[message.choice] || rps.guestChoice) return;
    rps.guestChoice = message.choice;
    hostResolveRps();
  }

  function hostResolveRps() {
    if (rps.role !== 'host' || rps.phase !== 'pick') return;
    if (!rps.hostChoice || !rps.guestChoice) return;
    const hostChoice = rps.hostChoice;
    const guestChoice = rps.guestChoice;
    const hostWon = RPS_BEATS[hostChoice] === guestChoice;
    const guestWon = RPS_BEATS[guestChoice] === hostChoice;
    if (hostWon) rps.hostWins++;
    if (guestWon) rps.guestWins++;
    rps.final = rps.hostWins >= 2 || rps.guestWins >= 2;
    rps.phase = 'reveal';
    updateRpsUi();

    netSend({
      type: 'rpsReveal',
      round: rps.round,
      hostChoice,
      guestChoice,
      hostWins: rps.hostWins,
      guestWins: rps.guestWins,
      final: rps.final
    });

    if (rps.timer) clearTimeout(rps.timer);
    rps.timer = setTimeout(() => {
      rps.timer = null;
      if (!rps.active || state.net.phase !== 'rps' || !state.net.connected) return;
      if (rps.final) {
        const winnerRole = rps.hostWins > rps.guestWins ? 'host' : 'guest';
        const chosenSide = rps.side;
        const hostSide = winnerRole === 'host' ? chosenSide : otherSide(chosenSide);
        const guestSide = otherSide(hostSide);
        const gameId = (state.net.gameId || 0) + 1;
        state.net.gameId = gameId;
        rps.active = false;
        closeRpsDialog(true);
        state.net.phase = 'playing';
        netSend({ type: 'start', hostSide, guestSide, gameId });
        beginOnlineGame(hostSide, guestSide, gameId);
      } else {
        rps.round++;
        rps.hostChoice = null;
        rps.guestChoice = null;
        rps.phase = 'pick';
        rps.final = false;
        updateRpsUi();
        netSend({ type: 'rpsNext', round: rps.round });
      }
    }, 2900);
  }

  function guestReceiveRpsReveal(message) {
    if (!rps.active || rps.role !== 'guest') return;
    if (message.round !== rps.round) return;
    if (!RPS_HANDS[message.hostChoice] || !RPS_HANDS[message.guestChoice]) return;
    rps.hostChoice = message.hostChoice;
    rps.guestChoice = message.guestChoice;
    rps.hostWins = Number(message.hostWins) || 0;
    rps.guestWins = Number(message.guestWins) || 0;
    rps.final = Boolean(message.final);
    rps.phase = 'reveal';
    updateRpsUi();
  }

  function guestReceiveRpsNext(message) {
    if (!rps.active || rps.role !== 'guest') return;
    if (!Number.isInteger(message.round) || message.round <= rps.round) return;
    rps.round = message.round;
    rps.hostChoice = null;
    rps.guestChoice = null;
    rps.phase = 'pick';
    rps.final = false;
    updateRpsUi();
  }

  function closeRpsDialog(keepActive = false) {
    if (rps.timer) {
      clearTimeout(rps.timer);
      rps.timer = null;
    }
    if (!keepActive) rps.active = false;
    if (dom.rpsDialog.open) dom.rpsDialog.close();
  }

  /* ======================================================================
     10. 事件绑定与初始化
     ====================================================================== */
  function bindEvents() {
    dom.board.addEventListener('click', event => {
      const rect = dom.board.getBoundingClientRect();
      if (!rect.width || !rect.height) return;
      const x = (event.clientX - rect.left) * 520 / rect.width;
      const y = (event.clientY - rect.top) * 568 / rect.height;
      let best = null;
      let bestDistance = Infinity;
      for (let r = 0; r < Engine.ROWS; r++) {
        for (let c = 0; c < Engine.COLS; c++) {
          const shown = displayPos(r, c);
          const distance = Math.hypot(x - (32 + shown.c * 57), y - (32 + shown.r * 56));
          if (distance < bestDistance) {
            bestDistance = distance;
            best = { r, c };
          }
        }
      }
      if (best && bestDistance <= 26) handleBoardClick(best.r, best.c);
    });

    dom.undoBtn.addEventListener('click', undoMove);
    dom.restartBtn.addEventListener('click', restartCurrentGame);
    dom.soundBtn.addEventListener('click', toggleSound);
    dom.leaveRoomBtn.addEventListener('click', exitRoom);
    dom.exitLobbyBtn.addEventListener('click', exitRoom);

    dom.modeLocalBtn.addEventListener('click', () => {
      if (state.mode === 'online') {
        if (isOnlineActive() && !window.confirm('离开当前房间？联机对局将结束。')) return;
        leaveOnline({ fallbackToLocal: false, silent: true });
      }
      startLocalGame(state.mode !== 'local');
    });

    dom.modeAiBtn.addEventListener('click', () => {
      if (state.mode === 'online') {
        if (isOnlineActive() && !window.confirm('离开当前房间？联机对局将结束。')) return;
        leaveOnline({ fallbackToLocal: true, silent: true });
      }
      openAiSetup();
    });

    dom.modeRoomBtn.addEventListener('click', () => {
      if (state.mode === 'online' && ['rps', 'playing'].includes(state.net.phase)) {
        showToast('联机对局进行中，可在棋盘下方退出房间');
        return;
      }
      openRoomSetup();
    });

    dom.setupCloseBtn.addEventListener('click', () => closeDialog(dom.setupDialog));

    dom.levelGroup.addEventListener('click', event => {
      const btn = event.target.closest('[data-level]');
      if (!btn) return;
      setupDraft.level = btn.dataset.level;
      updateAiSetup();
    });
    dom.aiSideGroup.addEventListener('click', event => {
      const btn = event.target.closest('[data-side]');
      if (!btn) return;
      setupDraft.side = btn.dataset.side;
      updateAiSetup();
    });
    dom.startAiBtn.addEventListener('click', () => startAIGame(setupDraft.level, setupDraft.side));

    dom.createRoomTab.addEventListener('click', () => selectRoomTab('create'));
    dom.joinRoomTab.addEventListener('click', () => selectRoomTab('join'));
    dom.createRoomBtn.addEventListener('click', createRoom);
    dom.joinRoomBtn.addEventListener('click', joinRoom);
    dom.roomCodeInput.addEventListener('input', () => {
      dom.roomCodeInput.value = dom.roomCodeInput.value.replace(/\D/g, '').slice(0, 6);
      clearRoomError();
    });
    dom.roomCodeInput.addEventListener('keydown', event => {
      if (event.key === 'Enter') joinRoom();
    });
    dom.roomSideGroup.addEventListener('click', event => {
      const btn = event.target.closest('[data-room-side]');
      if (!btn) return;
      chooseRoomSide(btn.dataset.roomSide);
    });
    dom.startRoomBtn.addEventListener('click', hostStartGame);
    dom.copyCodeBtn.addEventListener('click', async () => {
      const code = state.net.code;
      if (!code) return;
      try {
        await navigator.clipboard.writeText(code);
        showToast('房间号已复制');
      } catch {
        const input = document.createElement('input');
        input.value = code;
        document.body.appendChild(input);
        input.select();
        try { document.execCommand('copy'); showToast('房间号已复制'); }
        catch { showToast(`房间号：${code}`); }
        input.remove();
      }
    });

    dom.rpsChoices.addEventListener('click', event => {
      const btn = event.target.closest('[data-rps-choice]');
      if (btn) pickRps(btn.dataset.rpsChoice);
    });
    dom.rpsDialog.addEventListener('cancel', event => {
      if (rps.active) event.preventDefault();
    });

    window.addEventListener('beforeunload', () => {
      if (state.net.conn && state.net.conn.open) {
        try { state.net.conn.send({ type: 'leave' }); } catch { /* ignore */ }
      }
    });
  }

  function initialize() {
    bindEvents();
    document.addEventListener('pointerdown', () => ensureAudioContext(), { once: true, capture: true });
    state.mode = 'local';
    state.board = Engine.initialBoard();
    state.turn = 'red';
    render();
    updateSoundButton();
    updateAiSetup();
    selectRoomTab('create');
  }

  initialize();

  /* ======================================================================
     11. 自动化测试接口（仅在 ?test=1 时开放）
     ====================================================================== */
  if (params.has('test')) {
    window.__xqTest = {
      Engine,
      state,
      rps,
      getState: () => ({
        mode: state.mode,
        turn: state.turn,
        board: Engine.cloneBoard(state.board),
        moves: state.moves.map(move => ({ ...move, from: { ...move.from }, to: { ...move.to } })),
        gameOver: state.gameOver,
        winner: state.winner,
        inCheck: state.inCheck,
        selected: state.selected ? { ...state.selected } : null,
        orientation: state.orientation,
        net: {
          role: state.net.role,
          phase: state.net.phase,
          code: state.net.code,
          connected: state.net.connected,
          mySide: state.net.mySide,
          hostSide: state.net.hostSide,
          guestSide: state.net.guestSide,
          pendingMove: state.net.pendingMove,
          gameId: state.net.gameId
        }
      }),
      clickSquare: (r, c) => handleBoardClick(r, c),
      applyMove: (fr, fc, tr, tc) => {
        const result = applyMove({ r: fr, c: fc }, { r: tr, c: tc }, { recordHistory: true });
        return Boolean(result);
      },
      startAIGame,
      startLocalGame,
      startOnlineGame: beginOnlineGame,
      setPosition: (boardData, turn = 'red') => {
        cancelAiWork();
        state.mode = 'local';
        state.board = boardData.map(row => row.map(p => p ? { side: p.side, type: p.type } : null));
        state.turn = turn;
        state.selected = null;
        state.history = [];
        state.moves = [];
        state.lastMove = null;
        state.gameOver = false;
        state.winner = null;
        state.endReason = '';
        state.inCheck = Engine.isInCheck(state.board, turn);
        state.orientation = 'red';
        render();
      },
      getSoundCount: () => soundCount,
      playMoveSound,
      updateRpsUi,
      closeRpsDialog,
      chooseMove: (side = state.turn, level = 'medium') =>
        Engine.chooseMove(Engine.cloneBoard(state.board), side, level),
      perft: (depth, side = state.turn) => {
        const b = Engine.cloneBoard(state.board);
        return Engine.perft(b, side, depth);
      }
    };
  }
})();

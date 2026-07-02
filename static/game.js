// ============================================================
// CONFIG
// ============================================================
let latestArmyData = {};
const RENDER_BORDER_THRESHOLD = 1.5;
const DIFF_POLL_MS = 500;
const ARMY_POLL_MS = 400;
const money_POLL_MS = 400;
const MIN_ZOOM = 0.5;
const MAX_ZOOM = 10;
const ZOOM_SPEED = 0.1;

const loadingPromises = {};
const COLORS = {
    0: '#1a3a5c',
    1: '#e94560',
    2: '#00b4d8',
    3: '#53a548',
    4: '#f5a623',
    5: '#9b59b6'
};

// Building definitions
const BUILDING_DEFS = {
    city:    { cost: 3000, iron: 200,uranium:0, icon: '🏙️', desc: 'Increases army regen', width:1, height:1, imgSrc: "static/images/cityAlt1.png" },
    factory: { cost: 3000, iron: 300,uranium:0, icon: '🏭', desc: 'Boosts army cap & attack', width:1, height:1, imgSrc: "static/images/factoryAlt1.png" },
    port:    { cost: 4000, iron: 200,uranium:0, icon: '⚓', desc: 'Extends naval range', width:1, height:1, imgSrc: "static/images/port1.png" },
    iron_mine: { cost: 1000, iron: 0,uranium:0, icon: '⛏️', desc: 'Enables air units (soon)', width:1, height:1, imgSrc: "static/images/iron_mine.png" },
    uranium_mine: { cost: 10000, iron: 500,uranium:0, icon: '⛏️', desc: 'Enables air units (soon)', width:1, height:1, imgSrc: "static/images/uranium_mine.png" },
    launcher:{ cost: 1500, iron: 200,uranium:0, icon: '🚀', desc: 'Missile launcher', width:1, height:1, imgSrc: "static/images/silo1.png" }
};

const RESOURCE_DEFS = {
    iron: {imgSrc: "static/images/iron.png"},
    uranium: {imgSrc: "static/images/uranium.png"}
}

// ============================================================
// GLOBAL STATE
// ============================================================
let token = localStorage.getItem('token');
let playerName = localStorage.getItem('playerName') || 'Player';
let fullRefreshInterval = null;
let myCountry = null;
let ws = null;
let canvas = null;
let ctx = null;
let worldData = null;
let worldRadiation = new Map();
let colorsRgb = null;
let tempCanvas = null;
let tempCtx = null;
let imageDataCache = null;
let resizePending = false;
let renderPending = false;
let reconnectTimer = null;
let armyPollInterval = null;
let armyCh = false;
let moneyPollInterval = null;
let resourcePollInterval = null;
let diffPollInterval = null;

// Zoom / pan
let zoom = 1.0;
let panX = 0;
let panY = 0;
let isDragging = false;
let dragStartX = 0, dragStartY = 0;
let dragStartPanX = 0, dragStartPanY = 0;

// Coastal cache
let myCoastalTiles = new Set();

// Server-side fleets
let serverFleets = new Map();

// Explosions
let explosions = [];
let animationFrameId = null;

// Build menu
let selectedTile = null;

// Missiles
let missileTargeting = null;
let serverMissiles = new Map();

// Money
let latestMoneyData = {};

// Iron
let latestResourceData = {};

// ============================================================
// AUTH CHECK
// ============================================================
if (!token) window.location.href = '/';
let gameStatus = 'waiting'; // 'waiting' | 'active' | 'ended'
let gameStatusPollInterval = null;
let gameTimer = null;
let timeRemaining = 0;
let winner = null;
let finalScores = {};
let isAdmin = false;
const ADMIN_SECRET = 'ch1';

// ============================================================
// HELPERS
// ============================================================
function hexToRgb(hex) {
    const m = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex);
    return m ? { r: parseInt(m[1],16), g: parseInt(m[2],16), b: parseInt(m[3],16) } : { r:0,g:0,b:0 };
}

function buildColorCache() {
    colorsRgb = {};
    for (const [k, v] of Object.entries(COLORS)) colorsRgb[k] = hexToRgb(v);
}

function fetchNoStore(url, opts = {}) {
    return fetch(url, { ...opts, cache: 'no-store', headers: { ...(opts.headers||{}) } });
}

function setStatus(id, text) {
    const el = document.getElementById(id);
    if (el) el.textContent = text;
}

function clearReconnectTimer() {
    if (reconnectTimer) { clearTimeout(reconnectTimer); reconnectTimer = null; }
}

function requestRender() {
    if (renderPending) return;
    renderPending = true;
    requestAnimationFrame(() => {
        renderPending = false;
        if (worldData && canvas && ctx && armyCh) renderWorld();
    });
}

function startFullRefresh() {
    if (fullRefreshInterval) clearInterval(fullRefreshInterval);
    fullRefreshInterval = setInterval(async () => {
        if (!ws || ws.readyState !== WebSocket.OPEN) {
            try {
                const resp = await fetchNoStore(`/world?ts=${Date.now()}`);
                const data = await resp.json();
                worldData = data;
                worldRadiation.clear();
                if (data.radiation) {
                    for (const [rx, ry, owner, ticks] of data.radiation) {
                        worldRadiation.set(`${rx},${ry}`, { owner, ticks });
                    }
                }
                rebuildMyCoastalTiles();
                requestRender();
            } catch (e) {}
        }
    }, 5000);
}

// ============================================================
// COASTAL HELPERS
// ============================================================
function isCoastalTile(x, y) {
    if (!worldData || !worldData.terrain) return false;
    if (worldData.terrain[y][x] !== 1) return false;
    const neighbors = [[1,0],[-1,0],[0,1],[0,-1]];
    for (const [dx, dy] of neighbors) {
        const nx = x + dx, ny = y + dy;
        if (nx >= 0 && ny >= 0 && nx < worldData.width && ny < worldData.height) {
            if (worldData.terrain[ny][nx] === 0) return true;
        }
    }
    return false;
}

function isAdjacentToMyLand(x, y) {
    if (!worldData || myCountry === null) return false;
    const neighbors = [[1,0],[-1,0],[0,1],[0,-1]];
    for (const [dx, dy] of neighbors) {
        const nx = x + dx, ny = y + dy;
        if (nx >= 0 && ny >= 0 && nx < worldData.width && ny < worldData.height) {
            if (worldData.owners[ny][nx] === myCountry) return true;
        }
    }
    return false;
}

function updateMyCoastalTile(x, y) {
    if (!worldData || myCountry === null) return;
    if (worldData.owners[y]?.[x] === myCountry && isCoastalTile(x, y)) {
        myCoastalTiles.add(`${x},${y}`);
    } else {
        myCoastalTiles.delete(`${x},${y}`);
    }
    const neighbors = [[1,0],[-1,0],[0,1],[0,-1]];
    for (const [dx, dy] of neighbors) {
        const nx = x + dx, ny = y + dy;
        if (nx >= 0 && ny >= 0 && nx < worldData.width && ny < worldData.height) {
            if (worldData.owners[ny][nx] === myCountry && isCoastalTile(nx, ny)) {
                myCoastalTiles.add(`${nx},${ny}`);
            } else {
                myCoastalTiles.delete(`${nx},${ny}`);
            }
        }
    }
}

function rebuildMyCoastalTiles() {
    myCoastalTiles.clear();
    if (!worldData || myCountry === null) return;
    const { owners, width, height } = worldData;
    for (let y = 0; y < height; y++) {
        const row = owners[y];
        for (let x = 0; x < width; x++) {
            if (row[x] === myCountry && isCoastalTile(x, y)) {
                myCoastalTiles.add(`${x},${y}`);
            }
        }
    }
}

function findNearestFriendlyCoastal(targetX, targetY) {
    if (!worldData || myCountry === null) return null;
    let best = null, bestDist = Infinity;
    for (const key of myCoastalTiles) {
        const [cx, cy] = key.split(',').map(Number);
        const d = Math.hypot(cx - targetX, cy - targetY);
        if (d < bestDist) { bestDist = d; best = { x: cx, y: cy }; }
    }
    return best;
}

function findNearestBuildingOfType(tileX, tileY, buildingType, ownerId) {
    if (!worldData || !worldData.buildings) return null;
    let building = worldData.buildings.find(
        b => b.x === tileX && b.y === tileY && b.type === buildingType && b.owner === ownerId
    );
    if (building) return { x: building.x, y: building.y };
    for (let dy = -1; dy <= 1; dy++) {
        for (let dx = -1; dx <= 1; dx++) {
            if (dx === 0 && dy === 0) continue;
            building = worldData.buildings.find(
                b => b.x === tileX + dx && b.y === tileY + dy && b.type === buildingType && b.owner === ownerId
            );
            if (building) return { x: building.x, y: building.y };
        }
    }
    for (let dy = -2; dy <= 2; dy++) {
        for (let dx = -2; dx <= 2; dx++) {
            if (Math.abs(dx) <= 1 && Math.abs(dy) <= 1) continue;
            building = worldData.buildings.find(
                b => b.x === tileX + dx && b.y === tileY + dy && b.type === buildingType && b.owner === ownerId
            );
            if (building) return { x: building.x, y: building.y };
        }
    }
    return null;
}

// ============================================================
// EXPLOSION EFFECT
// ============================================================
class Explosion {
    constructor(x, y) {
        this.x = x; this.y = y;
        this.life = 0;
        this.maxLife = 25;
        this.alive = true;
    }
    update() { this.life++; if (this.life >= this.maxLife) this.alive = false; }
    draw(ctx, ox, oy, scale) {
        if (!this.alive) return;
        const sx = ox + this.x * scale, sy = oy + this.y * scale;
        const progress = this.life / this.maxLife;
        const radius = 15 * (1 - progress);
        const alpha = 1 - progress;
        const gradient = ctx.createRadialGradient(sx, sy, 0, sx, sy, radius);
        gradient.addColorStop(0, `rgba(255, 255, 200, ${alpha})`);
        gradient.addColorStop(0.5, `rgba(255, 150, 50, ${alpha * 0.7})`);
        gradient.addColorStop(1, 'rgba(255, 50, 0, 0)');
        ctx.fillStyle = gradient;
        ctx.fillRect(sx - radius, sy - radius, radius * 2, radius * 2);
    }
}

// ============================================================
// FLEET DRAWING
// ============================================================
function drawFleet(fleet, ox, oy, scale) {
    if (fleet.trail && fleet.trail.length > 1) {
        ctx.save();
        ctx.imageSmoothingEnabled = true;
        ctx.strokeStyle = 'rgba(255, 215, 0, 0.8)';
        ctx.lineWidth = Math.max(2, scale * 0.5);
        ctx.beginPath();
        ctx.moveTo(ox + fleet.trail[0].x * scale, oy + fleet.trail[0].y * scale);
        for (let i = 1; i < fleet.trail.length; i++) {
            ctx.lineTo(ox + fleet.trail[i].x * scale, oy + fleet.trail[i].y * scale);
        }
        ctx.stroke();
        ctx.restore();

        const blockSize = Math.max(1, Math.floor(scale * 0.3));
        ctx.imageSmoothingEnabled = false;
        for (let i = 0; i < fleet.trail.length; i++) {
            const pt = fleet.trail[i];
            const px = ox + pt.x * scale, py = oy + pt.y * scale;
            const alpha = i / fleet.trail.length;
            ctx.fillStyle = `rgba(255,215,0,${alpha * 0.9})`;
            ctx.fillRect(px - blockSize/2, py - blockSize/2, blockSize, blockSize);
        }
    }

    const bob = Math.sin(Date.now() * 0.005) * 2;
    const sx = ox + fleet.x * scale, sy = oy + fleet.y * scale;
    const size = Math.max(2, Math.floor(scale * 1));
    ctx.fillStyle = '#ffd700';
    ctx.fillRect(sx - size/2, sy - size/2, size, size);
    ctx.fillStyle = 'rgba(255,255,255,0.6)';
    ctx.fillRect(sx - size/4, sy - size/4, size/2, size/2);
    ctx.strokeStyle = 'rgba(255,255,255,0.9)';
    ctx.lineWidth = 1;
    ctx.strokeRect(sx - size/2, sy - size/2, size, size);
    ctx.imageSmoothingEnabled = true;
}

// ============================================================
// ANIMATION LOOP
// ============================================================
function startAnimationLoop() {
    if (animationFrameId) return;
    function animate() {
        let needs = false;
        explosions = explosions.filter(e => { e.update(); return e.alive; });
        if (explosions.length > 0 || serverFleets.size > 0 || serverMissiles.size > 0) needs = true;
        if (needs) requestRender();
        animationFrameId = requestAnimationFrame(animate);
    }
    animate();
}

// ============================================================
// SPAWN / ATTACK / BUILD
// ============================================================
async function spawnCountry(x, y) {
    if (!token) return;
    try {
        const resp = await fetchNoStore('/spawn', {
            method:'POST', headers:{'Content-Type':'application/json'},
            body: JSON.stringify({ token, x, y })
        });
        const data = await resp.json();
        if (!data.success) { alert(data.error); return; }
        myCountry = data.country;
        setStatus('player-country', myCountry);
        document.getElementById('spawn-overlay').style.display = 'none';
        fetchWorld(); fetchArmies(); fetchMoneys(); renderWorld();
    } catch(e) { alert('Connection error'); }
}

async function attackTarget(target) {
    if (!token) return;
    try {
        const resp = await fetchNoStore('/attack', {
            method:'POST', headers:{'Content-Type':'application/json'},
            body: JSON.stringify({ token, target })
        });
        const data = await resp.json();
        if (!data.success) { alert(data.error); return; }
        setStatus('target-status', `⚔️ Attacking Country ${target}`);
    } catch(e) {}
}

async function navalAttack(x, y) {
    if (!token) return;
    try {
        const resp = await fetchNoStore('/attack', {
            method:'POST', headers:{'Content-Type':'application/json'},
            body: JSON.stringify({ token, x, y })
        });
        const data = await resp.json();
        if (!data.success) { alert('Naval failed: '+data.error); return; }
        setStatus('target-status', '🚢 Fleet dispatched!');
    } catch(e) { alert('Connection error'); }
}

async function buildBuilding(x, y, type) {
    try {
        const resp = await fetchNoStore('/build', {
            method:'POST', headers:{'Content-Type':'application/json'},
            body: JSON.stringify({ token, x, y, type })
        });
        const data = await resp.json();
        if (data.success) {
            fetchWorld(); fetchArmies(); fetchMoneys();
            setStatus('target-status', `✅ Built ${type}!`);
        } else alert(data.error);
    } catch(e) { alert('Build failed'); }
}

function buildSelected(type) {
    if (!selectedTile) {
        setStatus("target-status", "Select one of your tiles first");
        return;
    }

    const myMoney = myCountry !== null && latestMoneyData[myCountry] ? latestMoneyData[myCountry].money : 0;
    const cost = BUILDING_DEFS[type]?.cost || 0;
    if (myMoney < cost) {
        setStatus('target-status', `❌ Not enough money! Need ${cost.toLocaleString()}💰`);
        return;
    }

    buildBuilding(selectedTile.x, selectedTile.y, type);
}

// ============================================================
// MISSILE LAUNCHING (NEW SEPARATE BUTTON SYSTEM)
// ============================================================
function launchMissileFromSelected(missileType) {
    if (!selectedTile) {
        setStatus('target-status', '❌ Select one of your tiles with a launcher first');
        return;
    }

    // Find a launcher on or near the selected tile
    const launcher = findNearestBuildingOfType(selectedTile.x, selectedTile.y, 'launcher', myCountry);
    
    if (!launcher) {
        setStatus('target-status', '❌ No launcher found! Build one first (🚀 button)');
        return;
    }

    // Start targeting mode
    console.log(launcher)
    startMissileTargeting(launcher.x, launcher.y, missileType);
}

function startMissileTargeting(fromX, fromY, missileType) {
    console.log('Starting missile targeting:', missileType, 'from', fromX, fromY);
    missileTargeting = { fromX, fromY, missileType };
    canvas.style.cursor = 'crosshair';
    
    const typeName = missileType === 'nuke' ? '☢️ NUKE' : '🚀 MISSILE';
    setStatus('target-status', `🎯 Click target for ${typeName} (Esc to cancel)`);
    
    // Auto-cancel after 15 seconds
    setTimeout(() => {
        if (missileTargeting) {
            missileTargeting = null;
            canvas.style.cursor = 'default';
            setStatus('target-status', '❌ Launch cancelled (timeout)');
        }
    }, 15000);
}

async function launchMissile(targetX, targetY) {
    if (!missileTargeting) return;
    
    const missileType = missileTargeting.missileType;
    missileTargeting = null;
    canvas.style.cursor = 'default';
    
    console.log('Launching missile:', missileType, 'to', targetX, targetY);

    try {
        const body = { 
            token: token, 
            x: targetX, 
            y: targetY, 
            missile_type: missileType
        };
        
        const resp = await fetchNoStore('/launch_missile', {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(body)
        });
        const data = await resp.json();
        
        if (data.success) {
            const typeName = missileType === 'nuke' ? '☢️ NUKE' : '🚀 MISSILE';
            setStatus('target-status', `${typeName} launched!`);
            fetchWorld();
        } else {
            alert('Launch failed: ' + (data.error || 'Unknown error'));
            setStatus('target-status', '❌ Launch failed');
        }
    } catch (e) {
        console.error('Launch error:', e);
        alert('Connection error');
        setStatus('target-status', '❌ Launch failed');
    }
}

function updateMissileButtons() {
    const convBtn = document.getElementById('conventional-btn');
    const nukeBtn = document.getElementById('nuke-btn');
    
    if (!convBtn || !nukeBtn) return;
    
    if (!selectedTile || myCountry === null) {
        convBtn.disabled = true;
        nukeBtn.disabled = true;
        return;
    }
    
    // Check if there's a launcher nearby
    const launcher = findNearestBuildingOfType(selectedTile.x, selectedTile.y, 'launcher', myCountry);
    const hasLauncher = launcher !== null;
    
    convBtn.disabled = !hasLauncher;
    nukeBtn.disabled = !hasLauncher;
    
    if (hasLauncher) {
        convBtn.classList.add('active');
        nukeBtn.classList.add('active');
        convBtn.title = 'Launch conventional missile';
        nukeBtn.title = 'Launch nuclear missile (destroys buildings!)';
    } else {
        convBtn.classList.remove('active');
        nukeBtn.classList.remove('active');
        convBtn.title = 'Need a launcher on this tile first';
        nukeBtn.title = 'Need a launcher on this tile first';
    }
}

// ============================================================
// BUILD BUTTON UPDATES
// ============================================================
function updateBuildButtons() {
    const buttons = document.querySelectorAll(".build-btn");
    const myMoney = myCountry !== null && latestMoneyData[myCountry] ? latestMoneyData[myCountry].money : 0;

    buttons.forEach(btn => {
        const onclick = btn.getAttribute('onclick');
        const match = onclick && onclick.match(/'([^']+)'/);
        const type = match ? match[1] : null;
        
        // Skip missile launch buttons (they're handled separately)
        if (!type || !BUILDING_DEFS[type]) return;

        const def = BUILDING_DEFS[type];
        const cost = def.cost;
        const ironCost = def.iron || 0;
        const uraniumCost = def.uranium || 0;
        
        const myResources = latestResourceData[myCountry] ? latestResourceData[myCountry].resources : {iron: 0, uranium: 0};
        const myIron = myResources.iron || 0;
        const myUranium = myResources.uranium || 0;

        // Check ALL resources
        const canAffordMoney = selectedTile && myMoney >= cost;
        const canAffordIron = selectedTile && myIron >= ironCost;
        const canAffordUranium = selectedTile && myUranium >= uraniumCost;
        const canAfford = canAffordMoney && canAffordIron && canAffordUranium;

        if (canAfford) {
            btn.disabled = false;
            btn.classList.add('active');
            btn.style.opacity = '1';
            
            // Build detailed tooltip
            let tooltip = `${def.desc} - `;
            tooltip += `${cost.toLocaleString()}💰`;
            if (ironCost > 0) tooltip += `, ${ironCost}⛏️`;
            if (uraniumCost > 0) tooltip += `, ${uraniumCost}☢️`;
            btn.title = tooltip;
        } else {
            btn.disabled = !selectedTile; // Only disable if no tile selected
            btn.classList.remove('active');
            btn.style.opacity = selectedTile ? '0.5' : '0.3';
            
            if (!selectedTile) {
                btn.title = 'Select a tile first';
            } else {
                // Show what's missing
                let missing = [];
                if (myMoney < cost) missing.push(`${(cost - myMoney).toLocaleString()}💰`);
                if (myIron < ironCost) missing.push(`${ironCost - myIron}⛏️`);
                if (myUranium < uraniumCost) missing.push(`${uraniumCost - myUranium}☢️`);
                
                btn.title = `Need: ${cost.toLocaleString()}💰, ${ironCost}⛏️, ${uraniumCost}☢️ | Missing: ${missing.join(', ')}`;
            }
        }
    });
    
    // Update missile buttons too
    updateMissileButtons();
}

// ============================================================
// ADMIN CONTROLS & GAME STATUS - SECURED VERSION
// ============================================================

function toggleAdminPanel() {
    const panel = document.getElementById('adminPanel');
    const toggleBtn = document.getElementById('adminToggle');
    
    if (!panel || !toggleBtn) return;
    
    // If panel is hidden or not displayed, check admin status first
    if (panel.style.display === 'none' || panel.style.display === '') {
        // Only show if user is already admin, otherwise prompt for password
        if (isAdmin) {
            panel.style.display = 'block';
            refreshGameStatus();
        } else {
            // Prompt for password
            const password = prompt('Enter admin password:');
            if (password !== null && password !== '') {
                adminLogin(password);
            }
        }
    } else {
        panel.style.display = 'none';
    }
}

async function adminLogin(password) {
    try {
        // First, check if the password is correct via the backend
        const resp = await fetch('/admin/login', {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({ 
                secret: password,
                token: token 
            })
        });
        const data = await resp.json();
        
        if (data.success) {
            isAdmin = true;
            document.getElementById('adminPanel').style.display = 'block';
            document.getElementById('adminToggle').style.display = 'block';
            document.getElementById('adminToggle').textContent = '👑 Admin';
            // Store admin status
            localStorage.setItem('isAdmin', 'true');
            alert('✅ Admin access granted!');
            refreshGameStatus();
        } else {
            alert('❌ Invalid admin password');
            document.getElementById('adminPanel').style.display = 'none';
            document.getElementById('adminToggle').style.display = 'none';
        }
    } catch (e) {
        console.error('Admin login failed:', e);
        alert('Connection error during admin login');
    }
}

async function adminStartGame() {
    if (!isAdmin) {
        alert('You are not authorized as admin');
        return;
    }
    
    try {
        const resp = await fetch('/admin/start', {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({ 
                secret: ADMIN_SECRET,
                token: token 
            })
        });
        const data = await resp.json();
        if (data.success) {
            setStatus('target-status', '✅ Game started by admin!');
            refreshGameStatus();
            document.getElementById('adminStartBtn').disabled = true;
            document.getElementById('adminEndBtn').disabled = false;
        } else {
            alert('Failed to start game: ' + data.error);
        }
    } catch (e) {
        alert('Connection error: ' + e.message);
    }
}

async function adminEndGame() {
    if (!isAdmin) {
        alert('You are not authorized as admin');
        return;
    }
    
    if (!confirm('Are you sure you want to end the game?')) return;
    
    try {
        const resp = await fetch('/admin/end', {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({ 
                secret: ADMIN_SECRET,
                token: token 
            })
        });
        const data = await resp.json();
        if (data.success) {
            setStatus('target-status', '⏹ Game ended by admin!');
            refreshGameStatus();
            document.getElementById('adminStartBtn').disabled = true;
            document.getElementById('adminEndBtn').disabled = true;
            if (data.winner) {
                winner = data.winner;
                finalScores = data.scores || {};
                displayEndGameResults();
            }
        } else {
            alert('Failed to end game: ' + data.error);
        }
    } catch (e) {
        alert('Connection error: ' + e.message);
    }
}

async function refreshGameStatus() {
    try {
        const resp = await fetch(`/game/status?ts=${Date.now()}`);
        const data = await resp.json();
        updateGameStatusDisplay(data);
        return data;
    } catch (e) {
        console.error('Failed to fetch game status:', e);
    }
}

function updateGameStatusDisplay(data) {
    if (!data) return;
    
    gameStatus = data.status;
    const statusText = document.getElementById('statusText');
    if (statusText) {
        statusText.textContent = data.status;
        statusText.style.color = 
            data.status === 'waiting' ? '#f1c40f' :
            data.status === 'active' ? '#2ecc71' :
            '#e74c3c';
    }
    
    const playerCount = document.getElementById('playerCount');
    if (playerCount) playerCount.textContent = data.players || 0;
    
    const activePlayerCount = document.getElementById('activePlayerCount');
    if (activePlayerCount) activePlayerCount.textContent = data.active_players || 0;
    
    const timeRemainingDisplay = document.getElementById('timeRemainingDisplay');
    const timeRemainingEl = document.getElementById('timeRemaining');
    
    if (data.status === 'active' && data.time_remaining !== undefined) {
        timeRemainingDisplay.style.display = 'block';
        timeRemaining = data.time_remaining;
        if (timeRemainingEl) timeRemainingEl.textContent = formatTime(data.time_remaining);
        
        if (gameTimer) clearInterval(gameTimer);
        gameTimer = setInterval(() => {
            timeRemaining--;
            if (timeRemainingEl && timeRemaining > 0) {
                timeRemainingEl.textContent = formatTime(timeRemaining);
            } else if (timeRemaining <= 0) {
                clearInterval(gameTimer);
                refreshGameStatus();
            }
        }, 1000);
    } else {
        timeRemainingDisplay.style.display = 'none';
        if (gameTimer) {
            clearInterval(gameTimer);
            gameTimer = null;
        }
    }
    
    const startBtn = document.getElementById('adminStartBtn');
    const endBtn = document.getElementById('adminEndBtn');
    
    if (startBtn) {
        startBtn.disabled = data.status !== 'waiting' || !isAdmin;
        startBtn.style.opacity = (data.status === 'waiting' && isAdmin) ? '1' : '0.5';
    }
    if (endBtn) {
        endBtn.disabled = data.status !== 'active' || !isAdmin;
        endBtn.style.opacity = (data.status === 'active' && isAdmin) ? '1' : '0.5';
    }
    
    if (data.status === 'ended') {
        winner = data.winner;
        finalScores = data.scores || {};
        displayEndGameResults();
    } else {
        document.getElementById('endGameResults').style.display = 'none';
    }
}

function formatTime(seconds) {
    const mins = Math.floor(seconds / 60);
    const secs = seconds % 60;
    return `${mins}:${secs.toString().padStart(2, '0')}`;
}

function displayEndGameResults() {
    const resultsDiv = document.getElementById('endGameResults');
    if (!resultsDiv) return;
    
    resultsDiv.style.display = 'block';
    
    const winnerDisplay = document.getElementById('winnerDisplay');
    if (winnerDisplay) {
        const winnerName = finalScores[winner]?.name || `Country ${winner}`;
        winnerDisplay.textContent = `Country ${winner} (${winnerName})`;
        winnerDisplay.style.color = '#ffd700';
    }
    
    const scoresDiv = document.getElementById('scoresDisplay');
    if (scoresDiv && finalScores) {
        const sorted = Object.entries(finalScores).sort((a, b) => b[1].score - a[1].score);
        scoresDiv.innerHTML = sorted.map(([cid, data]) => `
            <div style="padding: 4px 8px; margin: 2px 0; background: ${cid == winner ? '#2a2a3a' : 'transparent'}; 
                        border-left: ${cid == winner ? '3px solid #ffd700' : '3px solid transparent'};
                        border-radius: 2px;">
                <span style="font-weight: ${cid == winner ? 'bold' : 'normal'};">
                    ${cid == winner ? '👑 ' : ''}Country ${cid}: ${data.name || 'Unknown'}
                </span>
                <span style="float: right; margin-left: 10px;">
                    Score: ${data.score} | 
                    🏔️ ${data.territory} | 
                    ⚔️ ${data.army.toLocaleString()} | 
                    💰 ${data.money.toLocaleString()}
                </span>
            </div>
        `).join('');
    }
}

function startGameStatusPolling() {
    if (gameStatusPollInterval) clearInterval(gameStatusPollInterval);
    refreshGameStatus();
    gameStatusPollInterval = setInterval(() => {
        refreshGameStatus();
    }, 5000);
}

// Check admin access on page load - secured version
function checkAdminAccess() {
    // Hide admin elements by default
    const adminToggle = document.getElementById('adminToggle');
    const adminPanel = document.getElementById('adminPanel');
    
    if (adminToggle) adminToggle.style.display = 'none';
    if (adminPanel) adminPanel.style.display = 'none';
    
    // Check if user already has admin status from localStorage
    const savedAdmin = localStorage.getItem('isAdmin');
    if (savedAdmin === 'true') {
        // Verify with server
        verifyAdminStatus();
    }
    
    // Check URL parameter - but only show prompt, not auto-login
    const urlParams = new URLSearchParams(window.location.search);
    if (urlParams.has('admin')) {
        // Show a login prompt after a short delay
        setTimeout(() => {
            const password = prompt('Enter admin password:');
            if (password !== null && password !== '') {
                adminLogin(password);
            }
        }, 1000);
    }
}

async function verifyAdminStatus() {
    try {
        const resp = await fetch('/admin/check', {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({ token: token })
        });
        const data = await resp.json();
        
        if (data.success && data.is_admin) {
            isAdmin = true;
            document.getElementById('adminToggle').style.display = 'block';
            document.getElementById('adminToggle').textContent = '👑 Admin';
            // Don't auto-show panel, user must click the button
        } else {
            // Invalid admin status, clear it
            localStorage.removeItem('isAdmin');
            isAdmin = false;
            document.getElementById('adminToggle').style.display = 'none';
        }
    } catch (e) {
        console.error('Admin verification failed:', e);
        localStorage.removeItem('isAdmin');
        isAdmin = false;
        document.getElementById('adminToggle').style.display = 'none';
    }
}

// ============================================================
// ZOOM & PAN
// ============================================================
function handleWheel(e) {
    e.preventDefault();
    const rect = canvas.getBoundingClientRect();
    const mx = e.clientX - rect.left, my = e.clientY - rect.top;
    const zoomDelta = e.deltaY < 0 ? (1+ZOOM_SPEED) : (1-ZOOM_SPEED);
    const newZoom = Math.min(MAX_ZOOM, Math.max(MIN_ZOOM, zoom * zoomDelta));
    const ratio = newZoom / zoom;
    panX = mx - (mx - panX)*ratio;
    panY = my - (my - panY)*ratio;
    zoom = newZoom;
    requestRender();
}
function handleMouseDown(e) {
    if (e.button === 0) {
        isDragging = true;
        dragStartX = e.clientX; dragStartY = e.clientY;
        dragStartPanX = panX; dragStartPanY = panY;
        canvas.style.cursor = 'grabbing';
    }
}
function handleMouseMove(e) {
    if (isDragging) {
        panX = dragStartPanX + e.clientX - dragStartX;
        panY = dragStartPanY + e.clientY - dragStartY;
        requestRender();
    }
}
function handleMouseUp(e) {
    if (isDragging) {
        isDragging = false;
        canvas.style.cursor = missileTargeting ? 'crosshair' : 'default';
    }
}

function logout() {
    clearInterval(armyPollInterval); 
    clearInterval(diffPollInterval); 
    clearInterval(moneyPollInterval);
    clearInterval(resourcePollInterval);
    clearInterval(gameStatusPollInterval);
    if (gameTimer) clearInterval(gameTimer);
    clearReconnectTimer(); 
    if(animationFrameId) cancelAnimationFrame(animationFrameId);
    if(ws) try{ws.close();}catch(e){}
    localStorage.clear(); 
    window.location.href='/';
}

// ============================================================
// WORLD FETCH & RENDERING
// ============================================================
async function fetchWorld() {
    try {
        const resp = await fetchNoStore('/world');
        worldData = await resp.json();
        console.log(worldData);
        ensureBuffers();
        resizeCanvas();
        rebuildMyCoastalTiles();
        if (zoom === 1.0 && panX === 0 && panY === 0) resetView();
        requestRender();
    } catch(e) {}
}
function resetView() {
    if (!worldData || !canvas) return;
    zoom = Math.min(canvas.width/worldData.width, canvas.height/worldData.height) * 0.9;
    panX = (canvas.width - worldData.width*zoom)/2;
    panY = (canvas.height - worldData.height*zoom)/2;
}
function ensureBuffers() {
    if (!worldData) return;
    if (!tempCanvas) {
        tempCanvas = document.createElement('canvas');
        tempCtx = tempCanvas.getContext('2d', { willReadFrequently: true });
    }
    const { width, height } = worldData;
    if (tempCanvas.width !== width || tempCanvas.height !== height) {
        tempCanvas.width = width; tempCanvas.height = height;
        imageDataCache = tempCtx.createImageData(width, height);
    } else if (!imageDataCache) imageDataCache = tempCtx.createImageData(width, height);
}
function formatArmyLabel(value) {
    value = Number(value) || 0;
    if (value >= 1000000) return (value / 1000000).toFixed(1) + "M";
    if (value >= 1000) return (value / 1000).toFixed(1) + "K";
    return Math.round(value).toString();
}

function drawCountryArmyLabels() {
    if (!worldData) return;
    if (zoom < 1.0) return;
    
    const owners = worldData.owners;
    const width = worldData.width;
    const height = worldData.height;
    
    // Helper: Flood fill to find connected components
    function findConnectedComponents(ownerId) {
        const visited = new Set();
        const components = [];
        
        for (let y = 0; y < height; y++) {
            for (let x = 0; x < width; x++) {
                if (owners[y][x] !== ownerId) continue;
                const key = `${x},${y}`;
                if (visited.has(key)) continue;
                
                // BFS to find connected component
                const queue = [{x, y}];
                const component = [];
                visited.add(key);
                
                while (queue.length > 0) {
                    const current = queue.shift();
                    component.push(current);
                    
                    // Check 4 neighbors (up, down, left, right)
                    const neighbors = [
                        {x: current.x + 1, y: current.y},
                        {x: current.x - 1, y: current.y},
                        {x: current.x, y: current.y + 1},
                        {x: current.x, y: current.y - 1}
                    ];
                    
                    for (const neighbor of neighbors) {
                        const nKey = `${neighbor.x},${neighbor.y}`;
                        if (neighbor.x < 0 || neighbor.x >= width || 
                            neighbor.y < 0 || neighbor.y >= height) continue;
                        if (visited.has(nKey)) continue;
                        if (owners[neighbor.y][neighbor.x] !== ownerId) continue;
                        
                        visited.add(nKey);
                        queue.push(neighbor);
                    }
                }
                
                if (component.length > 0) {
                    components.push(component);
                }
            }
        }
        
        return components;
    }
    
    // Find the largest component for each country
    const countryCenters = {};
    const uniqueOwners = new Set();
    
    // Get all unique owners
    for (let y = 0; y < height; y++) {
        for (let x = 0; x < width; x++) {
            const owner = owners[y][x];
            if (owner > 0) uniqueOwners.add(owner);
        }
    }
    
    // Find largest component for each owner
    for (const ownerId of uniqueOwners) {
        const components = findConnectedComponents(ownerId);
        if (components.length === 0) continue;
        
        // Find the largest component
        let largest = components[0];
        for (const comp of components) {
            if (comp.length > largest.length) {
                largest = comp;
            }
        }
        
        // Calculate center of the largest component
        let sumX = 0, sumY = 0;
        for (const tile of largest) {
            sumX += tile.x;
            sumY += tile.y;
        }
        
        countryCenters[ownerId] = {
            cx: sumX / largest.length,
            cy: sumY / largest.length,
            componentSize: largest.length,
            totalTiles: components.reduce((sum, comp) => sum + comp.length, 0),
            components: components.length
        };
    }
    
    ctx.save();
    ctx.textAlign = "center";
    ctx.textBaseline = "middle";
    
    for (const ownerId in countryCenters) {
        const center = countryCenters[ownerId];
        const cx = center.cx;
        const cy = center.cy;
        const screenX = panX + cx * zoom;
        const screenY = panY + cy * zoom;
        
        // Skip if off screen
        if (screenX < -50 || screenX > canvas.width + 50 || 
            screenY < -50 || screenY > canvas.height + 50) continue;
        
        const army = latestArmyData?.[ownerId]?.army || 0;
        const label = formatArmyLabel(army);
        
        // Font size based on zoom and territory size
        const fontSize = Math.max(14, Math.min(36, zoom * 2.5));
        ctx.font = `bold ${fontSize}px Arial`;
        
        // Shadow for readability
        ctx.shadowColor = 'rgba(0, 0, 0, 0.9)';
        ctx.shadowBlur = 8;
        ctx.shadowOffsetX = 2;
        ctx.shadowOffsetY = 2;
        
        // Draw with country color
        const color = COLORS[ownerId] || '#ffffff';
        ctx.fillStyle = color;
        ctx.fillText(`⚔️ ${label}`, screenX, screenY);
        
        // Also draw outline for better visibility
        ctx.shadowBlur = 0;
        ctx.lineWidth = 3;
        ctx.strokeStyle = 'rgba(0, 0, 0, 0.8)';
        ctx.strokeText(`⚔️ ${label}`, screenX, screenY);
        ctx.fillStyle = color;
        ctx.fillText(`⚔️ ${label}`, screenX, screenY);
    }
    
    ctx.restore();
}
function renderWorld() {
    if (!worldData || !canvas || !ctx || !imageDataCache) return;
    const { owners, terrain, width, height } = worldData;
    const ox = panX, oy = panY, scale = zoom;
    const data = imageDataCache.data;
    const WATER = hexToRgb('#1a3a5c'), LAND = hexToRgb('#8a7a6a');
    for (let y = 0; y < height; y++) {
        const ownerRow = owners[y], terrainRow = terrain?.[y];
        for (let x = 0; x < width; x++) {
            const owner = ownerRow[x], idx = (y*width + x)*4;
            let c;
            if (owner === 0) {
                c = (terrainRow && terrainRow[x] === 1) ? LAND : WATER;
            } else {
                c = colorsRgb[String(owner)];
                if (!c) { c = hslToRgb(((owner*137.508)%360)/360, 0.7, 0.5); colorsRgb[String(owner)] = c; }
            }
            data[idx]=c.r; data[idx+1]=c.g; data[idx+2]=c.b; data[idx+3]=255;
        }
    }
    
    tempCtx.putImageData(imageDataCache, 0, 0);
    ctx.fillStyle = '#0a0a1a'; ctx.fillRect(0,0,canvas.width,canvas.height);
    ctx.save(); ctx.imageSmoothingEnabled = false;
    ctx.drawImage(tempCanvas, ox, oy, width*scale, height*scale);
    ctx.restore();
    if (scale >= RENDER_BORDER_THRESHOLD) drawBorders(ox, oy, scale);
    if(worldData.resources){
        for (const b of worldData.resources) drawResources(b, ox, oy, scale);
    }
    if (worldData.buildings) {
        for (const b of worldData.buildings) drawBuilding(b, ox, oy, scale);
    }


    for (const [mid, missile] of serverMissiles) drawMissile(missile, ox, oy, scale);
    for (const [fid, fleet] of serverFleets) drawFleet(fleet, ox, oy, scale);
    for (const exp of explosions) exp.draw(ctx, ox, oy, scale);
    drawCountryArmyLabels();
    drawZoomIndicator();

}

const imageCache = {};
function loadImage(src) {
    return new Promise((resolve, reject) => {
        const img = new Image();
        img.onload = () => resolve(img);
        img.onerror = reject;
        img.src = src;
    });
}
async function preloadBuildingImages() {
    const allDefs = { ...BUILDING_DEFS, ...RESOURCE_DEFS };
    
    const loadPromises = Object.values(allDefs)
        .filter(def => def.imgSrc)
        .map(async (def) => {
            if (!loadingPromises[def.imgSrc]) {
                loadingPromises[def.imgSrc] = loadImage(def.imgSrc)
                    .then(img => { imageCache[def.imgSrc] = img; return img; })
                    .catch(err => { console.error(err); return null; });
            }
            return loadingPromises[def.imgSrc];
        });
    await Promise.all(loadPromises);
    console.log('✅ All buildings preloaded!');
}

function drawMissile(missile, ox, oy, scale) {
    if (missile.trail && missile.trail.length > 1) {
        ctx.save();
        ctx.imageSmoothingEnabled = true;
        ctx.strokeStyle = missile.type === 'nuke' ? 'rgba(255, 50, 50, 0.7)' : 'rgba(255, 150, 50, 0.5)';
        ctx.lineWidth = missile.type === 'nuke' ? 3 : 2;
        ctx.shadowColor = missile.type === 'nuke' ? 'rgba(255, 0, 0, 0.8)' : 'rgba(255, 150, 0, 0.6)';
        ctx.shadowBlur = scale * 2;
        
        ctx.beginPath();
        ctx.moveTo(ox + missile.trail[0].x * scale, oy + missile.trail[0].y * scale);
        
        // Use cubic bezier curves for smooth path
        for (let i = 0; i < missile.trail.length - 1; i++) {
            const p0 = missile.trail[i];
            const p1 = missile.trail[Math.min(i + 1, missile.trail.length - 1)];
            
            // Calculate control points for smooth curve
            const cp1x = p0.x + (p1.x - p0.x) * 0.3;
            const cp1y = p0.y + (p1.y - p0.y) * 0.3;
            const cp2x = p1.x - (p1.x - p0.x) * 0.3;
            const cp2y = p1.y - (p1.y - p0.y) * 0.3;
            
            ctx.bezierCurveTo(
                ox + cp1x * scale, oy + cp1y * scale,
                ox + cp2x * scale, oy + cp2y * scale,
                ox + p1.x * scale, oy + p1.y * scale
            );
        }
        
        ctx.stroke();
        ctx.shadowBlur = 0;
        ctx.restore();
        
        // Draw trail dots (optional)
        const blockSize = Math.max(1, Math.floor(scale * 0.3));
        ctx.imageSmoothingEnabled = false;
        for (let i = 0; i < missile.trail.length; i++) {
            const pt = missile.trail[i];
            const px = ox + pt.x * scale, py = oy + pt.y * scale;
            const alpha = i / missile.trail.length;
            ctx.fillStyle = `rgba(255,215,0,${alpha * 0.9})`;
            ctx.fillRect(px - blockSize/2, py - blockSize/2, blockSize, blockSize);
        }
        
        // Draw missile head
        const sx = ox + missile.x * scale, sy = oy + missile.y * scale;
        const size = Math.max(4, Math.floor(scale * 1.5));
        ctx.fillStyle = missile.type === 'nuke' ? '#ff3333' : '#ff9933';
        ctx.fillRect(sx - size, sy - size/2, size * 2, size);
        ctx.fillStyle = missile.type === 'nuke' ? '#ff6666' : '#ffcc66';
        ctx.fillRect(sx - size/2, sy - size, size, size * 2);
    }
}

function drawBuilding(b, ox, oy, scale) {
    const def = BUILDING_DEFS[b.type];
    if (!def) return;
    const sx = ox + b.x * scale;
    const sy = oy + b.y * scale;
    const size = scale * 8;
    const offset = (scale - size) / 2;
    const img = imageCache[def.imgSrc];
    ctx.imageSmoothingEnabled = false;
    ctx.mozImageSmoothingEnabled = false;  // Firefox
    ctx.webkitImageSmoothingEnabled = false;  // Chrome/Safari
    ctx.msImageSmoothingEnabled = false; 
    if (img && img.complete && img.naturalWidth > 0) {
        ctx.save();
        ctx.globalCompositeOperation = 'source-over';
        ctx.imageSmoothingEnabled = true;
        ctx.imageSmoothingQuality = 'high';
        ctx.drawImage(img, sx + offset, sy + offset, size, size);
        ctx.restore();
    } else if (loadingPromises[def.imgSrc]) {
        ctx.save();
        ctx.fillStyle = '#444';
        ctx.fillRect(sx + offset, sy + offset, size, size);
        ctx.fillStyle = '#fff';
        ctx.font = `${size * 2}px sans-serif`;
        ctx.textAlign = 'center';
        ctx.textBaseline = 'middle';
        ctx.fillText('⏳', sx + scale/2, sy + scale/2);
        ctx.restore();
    } else {
        ctx.save();
        const colors = { city:'#4a90d9', factory:'#e67e22', port:'#2ecc71', airport:'#9b59b6', launcher:'#e74c3c', default:'#95a5a6' };
        ctx.fillStyle = colors[b.type] || colors.default;
        ctx.fillRect(sx + offset, sy + offset, size, size);
        ctx.fillStyle = '#fff';
        ctx.font = `${size * 0.6}px sans-serif`;
        ctx.textAlign = 'center';
        ctx.textBaseline = 'middle';
        const icons = { city:'🏙️', factory:'🏭', port:'⚓', airport:'🛫', launcher:'🚀' };
        ctx.fillText(icons[b.type] || '🏗️', sx + scale/2, sy + scale/2 + 2);
        ctx.restore();
    }
}

function drawResources(b, ox, oy, scale) {
    const def = RESOURCE_DEFS[b.type];
    if (!def) return;
    const sx = ox + b.x * scale;
    const sy = oy + b.y * scale;
    const size = scale * 8;
    const offset = (scale - size) / 2;
    const img = imageCache[def.imgSrc];
    ctx.imageSmoothingEnabled = false;
    ctx.mozImageSmoothingEnabled = false;  // Firefox
    ctx.webkitImageSmoothingEnabled = false;  // Chrome/Safari
    ctx.msImageSmoothingEnabled = false; 
    if (img && img.complete && img.naturalWidth > 0) {
        ctx.save();
        ctx.globalCompositeOperation = 'source-over';
        ctx.imageSmoothingEnabled = true;
        ctx.imageSmoothingQuality = 'high';
        ctx.drawImage(img, sx + offset, sy + offset, size, size);
        ctx.restore();
    } else if (loadingPromises[def.imgSrc]) {
        ctx.save();
        ctx.fillStyle = '#444';
        ctx.fillRect(sx + offset, sy + offset, size, size);
        ctx.fillStyle = '#fff';
        ctx.font = `${size * 2}px sans-serif`;
        ctx.textAlign = 'center';
        ctx.textBaseline = 'middle';
        ctx.fillText('⏳', sx + scale/2, sy + scale/2);
        ctx.restore();
    } else {
        ctx.save();
        const colors = { city:'#4a90d9', factory:'#e67e22', port:'#2ecc71', airport:'#9b59b6', launcher:'#e74c3c', default:'#95a5a6' };
        ctx.fillStyle = colors[b.type] || colors.default;
        ctx.fillRect(sx + offset, sy + offset, size, size);
        ctx.fillStyle = '#fff';
        ctx.font = `${size * 0.6}px sans-serif`;
        ctx.textAlign = 'center';
        ctx.textBaseline = 'middle';
        const icons = { city:'🏙️', factory:'🏭', port:'⚓', airport:'🛫', launcher:'🚀' };
        ctx.fillText(icons[b.type] || '🏗️', sx + scale/2, sy + scale/2 + 2);
        ctx.restore();
    }
}
function hslToRgb(h,s,l){ let r,g,b; if(s===0) r=g=b=l; else { const hue=(p,q,t)=>{ if(t<0)t+=1; if(t>1)t-=1; if(t<1/6)return p+(q-p)*6*t; if(t<1/2)return q; if(t<2/3)return p+(q-p)*(2/3-t)*6; return p; }; const q=l<0.5?l*(1+s):l+s-l*s, p=2*l-q; r=hue(p,q,h+1/3); g=hue(p,q,h); b=hue(p,q,h-1/3); } return {r:Math.round(r*255),g:Math.round(g*255),b:Math.round(b*255)}; }
function drawBorders(ox,oy,scale){ const {owners,width,height}=worldData; ctx.save(); ctx.lineWidth=Math.max(1,scale/6); ctx.strokeStyle='rgba(255,255,100,0.7)'; ctx.imageSmoothingEnabled=false; for(let y=0;y<height;y++){ for(let x=0;x<width;x++){ const o=owners[y][x]; if(o<=0)continue; if((x+1<width&&owners[y][x+1]!==o)||(x-1>=0&&owners[y][x-1]!==o)||(y+1<height&&owners[y+1][x]!==o)||(y-1>=0&&owners[y-1][x]!==o)){ ctx.strokeRect(ox+x*scale,oy+y*scale,scale,scale); } } } ctx.restore(); }
function drawZoomIndicator(){ ctx.fillStyle='rgba(0,0,0,0.7)'; ctx.fillRect(canvas.width-100,canvas.height-35,90,25); ctx.fillStyle='white'; ctx.font='12px monospace'; ctx.textAlign='right'; ctx.fillText(Math.round(zoom*100)+'%',canvas.width-20,canvas.height-17); }

// ============================================================
// CLICK HANDLER
// ============================================================
function handleClick(event) {
    if (isDragging) return;
    if (!worldData || !token) return;
    const rect = canvas.getBoundingClientRect();
    const worldX = ((event.clientX - rect.left) - panX) / zoom;
    const worldY = ((event.clientY - rect.top) - panY) / zoom;
    const x = Math.floor(worldX), y = Math.floor(worldY);
    
    if (x<0||y<0||x>=worldData.width||y>=worldData.height) return;
    
    // Missile targeting mode
    if (missileTargeting) {
        launchMissile(x, y);
        return;
    }
    
    const owner = worldData.owners[y][x];
    const isLand = worldData.terrain?.[y]?.[x] === 1;

    // Spawn
    if (myCountry === null) {
        if (!isLand) { setStatus('target-status','🌊 Water!'); return; }
        if (owner !== 0) { setStatus('target-status','❌ Occupied'); return; }
        spawnCountry(x,y); 
        fetchWorld();
        return;
    }

    // Select own tile
    if (owner === myCountry) {
        selectedTile = {x, y};
        setStatus('selected-info', `Tile (${x}, ${y})`);
        updateBuildButtons();
        updateMissileButtons();
        return;
    }

    if (!isLand) { setStatus('target-status','🌊 Water'); return; }

    const coastal = isCoastalTile(x,y);
    const adjacent = isAdjacentToMyLand(x,y);

    // Naval invasion
    if (coastal && !adjacent) {
        const from = findNearestFriendlyCoastal(x,y);
        if (from) {
            setStatus('target-status', owner===0 ? '🚢 Fleet to neutral island' : `🚢 Naval invading ${owner}`);
            navalAttack(x,y);
            return;
        } else { setStatus('target-status','🚢 No launch point'); return; }
    }

    // Normal land attack
    setStatus('target-status', owner===0 ? '🌲 Expanding' : `⚔️ Attacking ${owner}`);
    attackTarget(owner);
}

// ============================================================
// WEBSOCKET & POLLING
// ============================================================
function connectWebSocket() {
    clearReconnectTimer();
    const proto = location.protocol==='https:'?'wss:':'ws:';
    try { ws = new WebSocket(`${proto}//${location.host}/ws`); } catch(e) { scheduleReconnect(); return; }
    ws.onopen = () => setStatus('connection-status','🟢');
    ws.onmessage = e => { try { const d=JSON.parse(e.data); applyUpdates(d); } catch(ex){} };
    ws.onerror = () => setStatus('connection-status','🔴');
    ws.onclose = () => { setStatus('connection-status','🟡'); scheduleReconnect(); };
}
function scheduleReconnect() { if(!reconnectTimer) reconnectTimer=setTimeout(()=>{ reconnectTimer=null; connectWebSocket(); },3000); }
function applyUpdates(data) {
    if (!worldData) return;
    let changed = false;

    // Only log in development
    if (window.DEBUG) console.log(data);

    // Handle tile updates
    if (Array.isArray(data)) {
        for (const [x, y, owner] of data) {
            if (y < 0 || y >= worldData.owners.length || x < 0 || x >= worldData.owners[y].length) continue;
            const old = worldData.owners[y][x];
            if (old !== owner) {
                worldData.owners[y][x] = owner;
                changed = true;
                if (old === myCountry || owner === myCountry) updateMyCoastalTile(x, y);
            }
        }
        if (changed) requestRender();
        return;
    }

    // Handle tile updates (object format)
    if (data.tiles) {
        for (const [x, y, owner] of data.tiles) {
            if (y < 0 || y >= worldData.owners.length || x < 0 || x >= worldData.owners[y].length) continue;
            const old = worldData.owners[y][x];
            if (old !== owner) {
                worldData.owners[y][x] = owner;
                changed = true;
                if (old === myCountry || owner === myCountry) updateMyCoastalTile(x, y);
            }
        }
    }

    // Handle fleet updates
    if (data.fleets) {
        const seen = new Set();
        for (const [fid, owner, fx, fy] of data.fleets) {
            seen.add(fid);
            if (!serverFleets.has(fid)) {
                serverFleets.set(fid, { owner, x: fx, y: fy, trail: [] });
                changed = true;
            } else {
                const fleet = serverFleets.get(fid);
                if (Math.abs(fleet.x - fx) > 0.1 || Math.abs(fleet.y - fy) > 0.1) {
                    fleet.trail.push({ x: fleet.x, y: fleet.y, alpha: 1 });
                    if (fleet.trail.length > 200) {
                        fleet.trail.splice(0, fleet.trail.length - 200);
                    }
                    fleet.x = fx;
                    fleet.y = fy;
                    changed = true;
                }
            }
        }
        for (const [fid, fleet] of serverFleets) {
            if (!seen.has(fid)) {
                explosions.push(new Explosion(fleet.x, fleet.y));
                serverFleets.delete(fid);
                changed = true;
                if (fleet.owner === myCountry) rebuildMyCoastalTiles();
            }
        }
    }

    // Handle missile updates
    if (data.missiles) {
        const seen = new Set();
        for (const [mid, owner, mx, my, mtype] of data.missiles) {
            seen.add(mid);
            if (!serverMissiles.has(mid)) {
                serverMissiles.set(mid, { owner, x: mx, y: my, type: mtype, trail: [] });
                changed = true;
            } else {
                const m = serverMissiles.get(mid);
                if (Math.abs(m.x - mx) > 0.1 || Math.abs(m.y - my) > 0.1) {
                    m.trail.push({ x: m.x, y: m.y });
                    if (m.trail.length > 1000) {
                        m.trail.splice(0, m.trail.length - 1000);
                    }
                    m.x = mx;
                    m.y = my;
                    changed = true;
                }
            }
        }
        for (const [mid, missile] of serverMissiles) {
            if (!seen.has(mid)) {
                explosions.push(new Explosion(missile.x, missile.y));
                if (missile.type === 'nuke') {
                    for (let i = 0; i < 8; i++) {
                        const angle = (Math.PI * 2 * i) / 8;
                        const ex = missile.x + Math.cos(angle) * 3;
                        const ey = missile.y + Math.sin(angle) * 3;
                        explosions.push(new Explosion(ex, ey));
                    }
                    explosions.push(new Explosion(missile.x, missile.y));
                    explosions.push(new Explosion(missile.x, missile.y));
                }
                serverMissiles.delete(mid);
                changed = true;
                if (missile.owner === myCountry) rebuildMyCoastalTiles();
                clearTimeout(window._fetchWorldTimeout);
                window._fetchWorldTimeout = setTimeout(fetchWorld, 500);
            }
        }
    }

    if (data.buildings && data.buildings.length > 0) {
        if (!worldData.buildings) worldData.buildings = [];
        
        for (const building of data.buildings) {
            // Update or add building
            const existingIdx = worldData.buildings.findIndex(b => 
                b.x === building.x && b.y === building.y
            );
            
            if (existingIdx >= 0) {
                worldData.buildings[existingIdx] = building;
            } else {
                worldData.buildings.push(building);
            }
            changed = true;
        }
    }

    // Only render if something changed
    if (changed) {
        // Use throttled render
        if (!window._renderThrottle) {
            window._renderThrottle = true;
            requestRender();
            setTimeout(() => {
                window._renderThrottle = false;
            }, 50);
        }
    }
}

function startDiffPolling() {
    if (diffPollInterval) clearInterval(diffPollInterval);
    diffPollInterval = setInterval(async () => {
        try { const resp = await fetchNoStore(`/diff?ts=${Date.now()}`); const data = await resp.json(); applyUpdates(data); } catch(e) {}
    }, DIFF_POLL_MS);
}
function startArmyPolling() {
    if (armyPollInterval) clearInterval(armyPollInterval);
    fetchArmies(); armyPollInterval = setInterval(fetchArmies, ARMY_POLL_MS); 
}
function startMoneyPolling(){
    if (moneyPollInterval) clearInterval(moneyPollInterval);
    fetchMoneys(); moneyPollInterval = setInterval(fetchMoneys, money_POLL_MS);
}
function startResourcePolling(){
    if (resourcePollInterval) clearInterval(resourcePollInterval);
    fetchResources(); resourcePollInterval = setInterval(fetchResources, money_POLL_MS);
}
async function fetchArmies() {
    try {
        const resp = await fetchNoStore(`/armies?ts=${Date.now()}`);
        const data = await resp.json();
        latestArmyData = data;
        armyCh = true;
        updateArmyDisplay();
        requestRender();
        const list = document.getElementById('army-list');
        if (!list) return;
        const entries = Object.entries(data);
        if (entries.length===0) { list.innerHTML='<div style="color:#888;padding:10px;">No countries</div>'; return; }
        list.innerHTML = entries.sort((a,b)=>Number(a[0])-Number(b[0])).map(([id,d])=>{
            if(id != -99){
                const isMe = Number(id)===myCountry;
                const hue = (Number(id)*137.5)%360;
                const color = COLORS[id] || `hsl(${hue},70%,50%)`;
                return `<div class="country-row">
                    <span><span class="country-color" style="background:${color}"></span>${isMe?'★ ':''}Country ${id}${isMe?' (YOU)':''}</span>
                    <span>${Number(d.army).toLocaleString()} / ${Number(d.max_army).toLocaleString()}</span>
                </div>`;
            }
        }).join('');
    } catch(e) {}
}

async function fetchMoneys(){
    try {
        const resp = await fetchNoStore(`/moneys?ts=${Date.now()}`);
        const data = await resp.json();
        latestMoneyData = data;
        updateMoneyDisplay();
        updateBuildButtons();
        updateMissileButtons();
    } catch(e) {}
}
async function fetchResources(){
    try {
        const resp = await fetchNoStore(`/resources?ts=${Date.now()}`);
        const data = await resp.json();
        latestResourceData = data;
        updateResourceDisplay();
    } catch(e) {}
}
function updateArmyDisplay() {
    if (myCountry === null || !latestArmyData[myCountry]) {
        document.getElementById('army-current').textContent = '0';
        document.getElementById('army-max').textContent = '0';
        return;
    }
    const myArmy = latestArmyData[myCountry];
    document.getElementById('army-current').textContent = Math.floor(myArmy.army || 0).toLocaleString();
    document.getElementById('army-max').textContent = Math.floor(myArmy.max_army || 0).toLocaleString();
}

function updateMoneyDisplay() {
    if (myCountry === null || !latestMoneyData[myCountry]) {
        document.getElementById('money-current').textContent = '0';
    } else {
        const myMoney = latestMoneyData[myCountry].money || 0;
        document.getElementById('money-current').textContent = Math.floor(myMoney).toLocaleString();
    }
    updateBuildButtons();
    updateMissileButtons();
}
function updateResourceDisplay() {
    Object.keys(RESOURCE_DEFS).forEach(resourceType => {
        const value =
            latestResourceData?.[myCountry]?.resources?.[resourceType] || 0;

        document.getElementById(`${resourceType}-current`).textContent =
            Math.floor(value).toLocaleString();
    });

    updateBuildButtons();
    updateMissileButtons();
}

// ============================================================
// INIT
// ============================================================
function initGame() {
    canvas = document.getElementById('worldCanvas');
    ctx = canvas.getContext('2d', { alpha: false });
    buildColorCache();
    resizeCanvas();
    document.getElementById('player-name').textContent = playerName;
    document.getElementById('spawn-overlay').style.display = 'flex';

    window.addEventListener('resize', handleResize);
    canvas.addEventListener('click', handleClick);
    canvas.addEventListener('wheel', handleWheel, { passive: false });
    canvas.addEventListener('mousedown', handleMouseDown);
    canvas.addEventListener('mousemove', handleMouseMove);
    canvas.addEventListener('mouseup', handleMouseUp);
    canvas.addEventListener('mouseleave', handleMouseUp);
    canvas.addEventListener('contextmenu', e => e.preventDefault());
    
    // ESC key to cancel missile targeting
    document.addEventListener('keydown', e => {
        if (e.key === 'Escape' && missileTargeting) {
            missileTargeting = null;
            canvas.style.cursor = 'default';
            setStatus('target-status', '❌ Launch cancelled');
        }
    });

    connectWebSocket();
    fetchWorld();
    preloadBuildingImages();
    startArmyPolling();
    startMoneyPolling();
    startResourcePolling();
    startDiffPolling();
    startAnimationLoop();
    startFullRefresh();
    startGameStatusPolling();
    checkAdminAccess();
    updateBuildButtons();
    updateMissileButtons();
}

function handleResize() {
    if (resizePending) return;
    resizePending = true;
    requestAnimationFrame(() => { resizePending = false; resizeCanvas(); requestRender(); });
}
function resizeCanvas() {
    if (!canvas) return;
    canvas.width = window.innerWidth;
    canvas.height = window.innerHeight;
    if (worldData) ensureBuffers();
}

// ============================================================
// LOGOUT
// ============================================================
function logout() {
    clearInterval(armyPollInterval); 
    clearInterval(diffPollInterval); 
    clearInterval(moneyPollInterval);
    clearInterval(resourcePollInterval);
    clearInterval(gameStatusPollInterval);
    if (gameTimer) clearInterval(gameTimer);
    clearReconnectTimer(); 
    if(animationFrameId) cancelAnimationFrame(animationFrameId);
    if(ws) try{ws.close();}catch(e){}
    localStorage.clear(); 
    window.location.href='/';
}

// ============================================================
// STARTUP
// ============================================================
initGame();
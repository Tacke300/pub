import https from 'https';
import crypto from 'crypto';
import express from 'express';
import path from 'path';
import fs from 'fs';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const CONFIG_FILE = path.join(__dirname, 'config.json');
const STATE_FILE = path.join(__dirname, 'position_state.json');
const MAXLEV_FILE = path.join(__dirname, 'maxlev.json');
const FUNDING_FILE = path.join(__dirname, 'funding_cache.json');
const DATA_FILE = path.join(__dirname, 'data.json');

const DEFAULT_API_KEY = 'c1Y2O0kggVEggEaPvhFcYQHS5b1EsT2OWZb8zdY9C0jGqNROvXRZHTJjnQ7OG4Q'.trim();
const DEFAULT_SECRET_KEY = 'o6pZFHgEvbpD9NmFXp5ZVnYFMQ7EIkBiz88aTzvmC3SpT9nEf4fcDf0pEnFzoTc'.trim();

let userConfig = {
    apiKey: DEFAULT_API_KEY,
    secretKey: DEFAULT_SECRET_KEY,
    amountMode: 'percent',
    amountValue: 25,
    tpFixedPercent: 1,
    enableTrailing: false,
    tpTrailingPercent: 1,
    slPercent: 2,
    longOffsetMs: 1500,
    shortOffsetMs: 0,
    fundingThreshold: 0.3,
    tradeMode: 'both',
    sortMode: 'pnl',
    holdMinutes: 15,
    enableAlwaysPriceTrigger: false,
    alwaysPriceChangePct: 5
};

let blacklistMap = {};
let alwaysPriceLock = {};

function isBlacklisted(symbol) {
    const unlockTime = blacklistMap[symbol];
    if (!unlockTime) return false;
    if (Date.now() < unlockTime) return true;
    delete blacklistMap[symbol];
    return false;
}

function addToBlacklist(symbol) {
    blacklistMap[symbol] = Date.now() + 999999999999;
}

function unlockBlacklistWith15MinDelay(symbol) {
    blacklistMap[symbol] = Date.now() + 15 * 60 * 1000;
}

function saveDataPositionsToFile() {
    try {
        const dataObj = {
            currentMainPositions,
            currentBufferPositions
        };
        fs.writeFileSync(DATA_FILE, JSON.stringify(dataObj, null, 2), 'utf8');
    } catch (e) {}
}

function loadDataPositionsFromFile() {
    try {
        if (fs.existsSync(DATA_FILE)) {
            const raw = fs.readFileSync(DATA_FILE, 'utf8');
            const data = JSON.parse(raw);
            return {
                mainPositions: Array.isArray(data.currentMainPositions) ? data.currentMainPositions : (Array.isArray(data.mainPositions) ? data.mainPositions : []),
                bufferPositions: Array.isArray(data.currentBufferPositions) ? data.currentBufferPositions : (Array.isArray(data.bufferPositions) ? data.bufferPositions : [])
            };
        }
    } catch (e) {}
    return { mainPositions: [], bufferPositions: [] };
}

function getErrorMessage(error) {
    if (!error) return 'Không xác định';
    if (typeof error === 'string') return error;
    if (error.message) return error.message;
    if (error.msg) return error.msg;
    if (typeof error === 'object') {
        try {
            return JSON.stringify(error);
        } catch (e) {
            return String(error);
        }
    }
    return String(error);
}

function loadConfigFromFile() {
    try {
        if (fs.existsSync(CONFIG_FILE)) {
            const rawData = fs.readFileSync(CONFIG_FILE, 'utf8');
            const savedConfig = JSON.parse(rawData);
            userConfig = { ...userConfig, ...savedConfig };
        }
    } catch (error) {}
}

function saveConfigToFile() {
    try {
        fs.writeFileSync(CONFIG_FILE, JSON.stringify(userConfig, null, 2), 'utf8');
    } catch (error) {}
}

const BASE_HOST = 'fapi.binance.com';

let serverTimeOffset = 0;
let exchangeInfoCache = null;
let leverageCache = {};
let botRunning = false;
let botStartTime = null;

let currentMainPositions = [];
let currentBufferPositions = [];

let mainCheckInterval = null;
let bufferCheckInterval = null;
let schedulerTimeout = null;
let scheduledBufferTimeout = null;
let scheduledMainTimeout = null;
let antiLiquidationInterval = null;

let isOpeningPosition = false;
let lastOrderOpenTime = 0;

let consecutiveApiErrors = 0;
const MAX_CONSECUTIVE_API_ERRORS = 10;
const memoryLogs = [];
const MAX_LOG_SIZE = 1000;
const logCounts = {};
const LOG_COOLDOWN_MS = 60000;

const WEB_SERVER_PORT = 9998;

let globalStats = {
    totalSessions: 0,
    totalPnl: 0
};

let cachedFundingRates = [];
let lastFundingFetchTime = 0;
const FUNDING_CACHE_TTL = 30000;

let cachedDashboardData = null;
let lastDashboardFetchTime = 0;
const DASHBOARD_CACHE_TTL = 1500;

function formatTime(date = new Date()) {
    const utc7 = new Date(date.getTime() + (7 * 60 * 60 * 1000));
    const hours = String(utc7.getUTCHours()).padStart(2, '0');
    const minutes = String(utc7.getUTCMinutes()).padStart(2, '0');
    const seconds = String(utc7.getUTCSeconds()).padStart(2, '0');
    const ms = String(utc7.getUTCMilliseconds()).padStart(3, '0');
    return `${hours}:${minutes}:${seconds}.${ms}`;
}

function formatPrice(val) {
    if (val === null || val === undefined || isNaN(val)) return '0.00';
    const num = parseFloat(val);
    return parseFloat(num.toFixed(6)).toString();
}

function formatNumber(val) {
    if (val === null || val === undefined || isNaN(val)) return '0';
    return parseFloat(parseFloat(val).toFixed(6)).toString();
}

function formatQty(symbol, amount) {
    if (exchangeInfoCache && exchangeInfoCache[symbol] && exchangeInfoCache[symbol].quantityPrecision !== undefined) {
        return parseFloat(Math.abs(amount)).toFixed(exchangeInfoCache[symbol].quantityPrecision);
    }
    return Math.abs(amount).toString();
}

function formatDuration(startTimeMs) {
    if (!startTimeMs) return '00s';
    const elapsedSec = Math.floor((Date.now() - startTimeMs) / 1000);
    const mins = Math.floor(elapsedSec / 60);
    const secs = elapsedSec % 60;
    if (mins > 0) {
        return `${String(mins).padStart(2, '0')}m ${String(secs).padStart(2, '0')}s`;
    }
    return `${String(secs).padStart(2, '0')}s`;
}

function log(level, moduleName, message) {
    const timestamp = formatTime();
    const formattedLog = `[${timestamp}] [${level}] [${moduleName}] ${message}`;

    const plainTextMsg = formattedLog.replace(/<[^>]*>?/gm, '');
    const messageHash = crypto.createHash('md5').update(plainTextMsg).digest('hex');
    const now = Date.now();

    if (logCounts[messageHash]) {
        logCounts[messageHash].count++;
        if ((now - logCounts[messageHash].lastLoggedTime) < LOG_COOLDOWN_MS) {
            return;
        } else {
            logCounts[messageHash] = { count: 1, lastLoggedTime: new Date(now) };
        }
    } else {
        logCounts[messageHash] = { count: 1, lastLoggedTime: new Date(now) };
    }

    console.log(plainTextMsg);
    memoryLogs.push(formattedLog);
    if (memoryLogs.length > MAX_LOG_SIZE) memoryLogs.shift();
}

function saveStateToFile() {
    try {
        const stateData = {
            currentMainPositions,
            currentBufferPositions,
            botRunning,
            globalStats
        };
        fs.writeFileSync(STATE_FILE, JSON.stringify(stateData, null, 2), 'utf8');
    } catch (e) {}
}

function loadStateFromFile() {
    try {
        if (fs.existsSync(STATE_FILE)) {
            const raw = fs.readFileSync(STATE_FILE, 'utf8');
            const data = JSON.parse(raw);
            if (Array.isArray(data.currentMainPositions)) {
                currentMainPositions = data.currentMainPositions;
            } else if (data.currentMainPosition) {
                currentMainPositions = [data.currentMainPosition];
            } else {
                currentMainPositions = [];
            }

            if (Array.isArray(data.currentBufferPositions)) {
                currentBufferPositions = data.currentBufferPositions;
            } else if (data.currentBufferPosition) {
                currentBufferPositions = [data.currentBufferPosition];
            } else {
                currentBufferPositions = [];
            }

            if (data.botRunning !== undefined) botRunning = data.botRunning;
        }
    } catch (e) {}
}

class CriticalApiError extends Error {
    constructor(message) {
        super(message);
        this.name = 'CriticalApiError';
    }
}

function createSignature(queryString, apiSecret) {
    return crypto.createHmac('sha256', apiSecret).update(queryString).digest('hex');
}

async function makeHttpRequest(method, hostname, path, headers, postData = '') {
    return new Promise((resolve, reject) => {
        const options = { hostname, path, method, headers };
        const req = https.request(options, (res) => {
            let data = '';
            res.on('data', chunk => data += chunk);
            res.on('end', () => {
                if (res.statusCode >= 200 && res.statusCode < 300) {
                    resolve(data);
                } else {
                    let errorDetails = { code: res.statusCode, msg: res.statusMessage };
                    try { errorDetails = { ...errorDetails, ...JSON.parse(data) }; } catch (e) {}
                    reject(errorDetails);
                }
            });
        });
        req.on('error', e => reject({ code: 'NETWORK_ERROR', msg: e.message }));
        if (method === 'POST' && postData) req.write(postData);
        req.end();
    });
}

async function callSignedAPI(fullEndpointPath, method = 'GET', params = {}) {
    if (!userConfig.apiKey || !userConfig.secretKey) {
        throw new CriticalApiError("Thiếu API Key hoặc Secret Key.");
    }
    const timestamp = Date.now() + serverTimeOffset;
    let queryString = Object.keys(params).map(key => `${key}=${params[key]}`).join('&');
    queryString += (queryString ? '&' : '') + `timestamp=${timestamp}&recvWindow=5000`;
    const signature = createSignature(queryString, userConfig.secretKey);

    let requestPath, requestBody = '', headers = { 'X-MBX-APIKEY': userConfig.apiKey };

    if (method === 'GET' || method === 'DELETE') {
        requestPath = `${fullEndpointPath}?${queryString}&signature=${signature}`;
        headers['Content-Type'] = 'application/json';
    } else if (method === 'POST') {
        requestPath = fullEndpointPath;
        requestBody = `${queryString}&signature=${signature}`;
        headers['Content-Type'] = 'application/x-www-form-urlencoded';
    }

    try {
        const rawData = await makeHttpRequest(method, BASE_HOST, requestPath, headers, requestBody);
        consecutiveApiErrors = 0;
        return JSON.parse(rawData);
    } catch (error) {
        consecutiveApiErrors++;
        throw error;
    }
}

async function callPublicAPI(fullEndpointPath, params = {}) {
    const queryString = Object.keys(params).map(key => `${key}=${params[key]}`).join('&');
    const fullPath = `${fullEndpointPath}` + (queryString ? `?${queryString}` : '');
    try {
        const rawData = await makeHttpRequest('GET', BASE_HOST, fullPath, { 'Content-Type': 'application/json' });
        consecutiveApiErrors = 0;
        return JSON.parse(rawData);
    } catch (error) {
        consecutiveApiErrors++;
        throw error;
    }
}

async function syncServerTime() {
    try {
        const data = await callPublicAPI('/fapi/v1/time');
        serverTimeOffset = data.serverTime - Date.now();
    } catch (error) {
        throw error;
    }
}

function loadLeverageFromFile() {
    try {
        if (fs.existsSync(MAXLEV_FILE)) {
            const raw = fs.readFileSync(MAXLEV_FILE, 'utf8');
            const json = JSON.parse(raw);
            if (json.data && (Date.now() - (json.lastUpdated || 0)) < 8 * 3600 * 1000) {
                leverageCache = json.data;
                return true;
            }
        }
    } catch (e) {}
    return false;
}

function saveLeverageToFile() {
    try {
        const json = { lastUpdated: Date.now(), data: leverageCache };
        fs.writeFileSync(MAXLEV_FILE, JSON.stringify(json, null, 2), 'utf8');
    } catch (e) {}
}

async function updateAllLeverageCache(force = false) {
    try {
        if (!force && loadLeverageFromFile()) {
            return;
        }
        if (!userConfig.apiKey || !userConfig.secretKey) return;
        const response = await callSignedAPI('/fapi/v1/leverageBracket', 'GET');
        if (Array.isArray(response)) {
            response.forEach(item => {
                const brackets = item.brackets || [];
                brackets.sort((a, b) => b.initialLeverage - a.initialLeverage);
                leverageCache[item.symbol] = brackets.length > 0 ? brackets[0].initialLeverage : 20;
            });
            saveLeverageToFile();
        }
    } catch (error) {}
}

function getLeverageFromCache(symbol) {
    return leverageCache[symbol] || 20;
}

async function setLeverage(symbol, leverage) {
    try {
        await callSignedAPI('/fapi/v1/leverage', 'POST', { symbol, leverage });
        return true;
    } catch (error) { return false; }
}

async function ensureCrossMargin(symbol) {
    try {
        await callSignedAPI('/fapi/v1/marginType', 'POST', {
            symbol: symbol,
            marginType: 'CROSSED'
        });
    } catch (e) {}
}

async function getExchangeInfo() {
    if (exchangeInfoCache) return exchangeInfoCache;
    try {
        const data = await callPublicAPI('/fapi/v1/exchangeInfo');
        exchangeInfoCache = {};
        data.symbols.forEach(s => {
            if (s.status !== 'TRADING') return;
            exchangeInfoCache[s.symbol] = {
                minQty: parseFloat(s.filters.find(f => f.filterType === 'LOT_SIZE')?.minQty || 0),
                stepSize: parseFloat(s.filters.find(f => f.filterType === 'LOT_SIZE')?.stepSize || 0.001),
                minNotional: parseFloat(s.filters.find(f => f.filterType === 'MIN_NOTIONAL')?.notional || 5.0),
                pricePrecision: s.pricePrecision,
                quantityPrecision: s.quantityPrecision,
                tickSize: parseFloat(s.filters.find(f => f.filterType === 'PRICE_FILTER')?.tickSize || 0.001)
            };
        });
        return exchangeInfoCache;
    } catch (error) { throw error; }
}

async function getCurrentPrice(symbol) {
    try {
        const data = await callPublicAPI('/fapi/v1/ticker/price', { symbol });
        return parseFloat(data.price);
    } catch (error) {
        return null;
    }
}

async function aggressiveCleanup(symbol) {
    try {
        await callSignedAPI('/fapi/v1/allOpenOrders', 'DELETE', { symbol });
        const positions = await callSignedAPI('/fapi/v2/positionRisk', 'GET', { symbol });
        for (const pos of positions) {
            const amt = parseFloat(pos.positionAmt);
            if (Math.abs(amt) > 0) {
                const side = amt > 0 ? 'SELL' : 'BUY';
                await callSignedAPI('/fapi/v1/order', 'POST', {
                    symbol: symbol, side: side, positionSide: pos.positionSide, type: 'MARKET', quantity: formatQty(symbol, amt)
                });
            }
        }
    } catch (e) {}
}

function fetchAndLogRealizedPnL(symbol, positionSide, isTest = false) {
    const closeTime = Date.now();
    setTimeout(async () => {
        try {
            const trades = await callSignedAPI('/fapi/v1/userTrades', 'GET', { symbol, limit: 15 });
            const closeTrades = trades.filter(t => 
                t.time >= closeTime - 15000 && 
                t.realizedPnl !== "0" && 
                (t.positionSide === positionSide || t.positionSide === 'BOTH')
            );
            const totalPnl = closeTrades.reduce((sum, t) => sum + parseFloat(t.realizedPnl), 0);
            
            if (!isTest) {
                globalStats.totalPnl += totalPnl;
                saveStateToFile();
            }
            
            log('PNL', 'PNL', `💰 Kết quả giao dịch | Coin: ${symbol} | Position: ${positionSide} | PnL thực tế: ${totalPnl >= 0 ? '+' : ''}${totalPnl.toFixed(4)} USDT ${isTest ? '(TEST)' : ''}`);
        } catch (e) {}
    }, 5000);
}

function calculateValidQuantity(symbolInfo, currentPrice, initialMargin, leverage) {
    let exchangeMinNotional = symbolInfo ? (symbolInfo.minNotional || 5.0) : 5.0;
    let minQty = symbolInfo ? (symbolInfo.minQty || 0) : 0;
    let minQtyNotional = minQty * currentPrice;

    let requiredNotional = Math.max(5.5, exchangeMinNotional, minQtyNotional);
    let targetNotional = initialMargin * leverage;

    if (targetNotional < requiredNotional) {
        targetNotional = requiredNotional;
    }

    let qtyRaw = targetNotional / currentPrice;
    let step = symbolInfo ? (symbolInfo.stepSize || 0.001) : 0.001;
    let precision = (symbolInfo && symbolInfo.quantityPrecision !== undefined) ? symbolInfo.quantityPrecision : 3;

    let quantity = Math.ceil(qtyRaw / step) * step;

    if (quantity * currentPrice < requiredNotional) {
        quantity += step;
    }

    if (symbolInfo && symbolInfo.minQty && quantity < symbolInfo.minQty) {
        quantity = symbolInfo.minQty;
    }

    return parseFloat(quantity.toFixed(precision));
}

async function executeMarketOrderWithMinVolCheck(symbol, side, positionSide, quantity, currentPrice) {
    const orderSide = side === 'LONG' ? 'BUY' : 'SELL';
    try {
        return await callSignedAPI('/fapi/v1/order', 'POST', {
            symbol: symbol, side: orderSide, positionSide: positionSide, type: 'MARKET', quantity: quantity
        });
    } catch (error) {
        try {
            const exInfo = await callPublicAPI('/fapi/v1/exchangeInfo');
            const sInfo = exInfo.symbols.find(s => s.symbol === symbol);
            if (sInfo) {
                const minNotionalFilter = sInfo.filters.find(f => f.filterType === 'MIN_NOTIONAL');
                const lotSizeFilter = sInfo.filters.find(f => f.filterType === 'LOT_SIZE');
                const minNotional = parseFloat(minNotionalFilter?.notional || 5.0);
                const minQty = parseFloat(lotSizeFilter?.minQty || 0);
                const stepSize = parseFloat(lotSizeFilter?.stepSize || 0.001);
                
                let reqNotional = Math.max(5.5, minNotional, minQty * currentPrice);
                let newQtyRaw = reqNotional / currentPrice;
                let newQty = Math.ceil(newQtyRaw / stepSize) * stepSize;
                if (newQty < minQty) newQty = minQty;
                let formattedQty = parseFloat(newQty.toFixed(sInfo.quantityPrecision));

                return await callSignedAPI('/fapi/v1/order', 'POST', {
                    symbol: symbol, side: orderSide, positionSide: positionSide, type: 'MARKET', quantity: formattedQty
                });
            }
        } catch (retryErr) {}
        throw error;
    }
}

function loadFundingFromFile() {
    try {
        if (fs.existsSync(FUNDING_FILE)) {
            const raw = fs.readFileSync(FUNDING_FILE, 'utf8');
            const json = JSON.parse(raw);
            if (Array.isArray(json.data) && (Date.now() - (json.lastUpdated || 0)) < FUNDING_CACHE_TTL) {
                cachedFundingRates = json.data;
                lastFundingFetchTime = json.lastUpdated;
                return true;
            }
        }
    } catch (e) {}
    return false;
}

function saveFundingToFile() {
    try {
        const json = { lastUpdated: lastFundingFetchTime, data: cachedFundingRates };
        fs.writeFileSync(FUNDING_FILE, JSON.stringify(json, null, 2), 'utf8');
    } catch (e) {}
}

async function fetchFundingDataFromBinance(forceRefresh = false) {
    const now = Date.now();
    if (!forceRefresh && cachedFundingRates.length > 0 && (now - lastFundingFetchTime < FUNDING_CACHE_TTL)) {
        return cachedFundingRates;
    }
    if (!forceRefresh && loadFundingFromFile()) {
        return cachedFundingRates;
    }

    if (!exchangeInfoCache) await getExchangeInfo();
    const allFunding = await callPublicAPI('/fapi/v1/premiumIndex');
    
    let valid = allFunding.filter(item => 
        item.symbol.endsWith('USDT') && 
        exchangeInfoCache && exchangeInfoCache[item.symbol] && 
        item.nextFundingTime > now 
    );

    valid.forEach(item => {
        const lev = getLeverageFromCache(item.symbol);
        const fdValue = parseFloat(item.lastFundingRate);
        item.estPnl = lev * (Math.abs(fdValue) * 100); 
        item.fdType = fdValue >= 0 ? 'positive' : 'negative';
        item.lev = lev;
        item.timeToFunding = item.nextFundingTime - now;
    });

    valid.sort((a, b) => {
        const timeDiff = a.nextFundingTime - b.nextFundingTime;
        if (Math.abs(timeDiff) > 60000) { 
            return timeDiff; 
        }
        return b.estPnl - a.estPnl; 
    });

    cachedFundingRates = valid;
    lastFundingFetchTime = now;
    saveFundingToFile();
    return cachedFundingRates;
}

function getFilteredCandidates(allFunding, reqThreshold = null, targetFundingTime = null) {
    let valid = [...allFunding];

    valid = valid.filter(item => !isBlacklisted(item.symbol));

    valid = valid.filter(item => {
        const isOpenInMain = currentMainPositions.some(p => p.symbol === item.symbol);
        const isOpenInBuffer = currentBufferPositions.some(b => b.symbol === item.symbol);
        return !isOpenInMain && !isOpenInBuffer;
    });

    if (targetFundingTime !== null) {
        valid = valid.filter(item => Math.abs(item.nextFundingTime - targetFundingTime) <= 60000);
    }
    if (reqThreshold !== null) {
        valid = valid.filter(item => {
            const frPercent = Math.abs(parseFloat(item.lastFundingRate)) * 100;
            if (userConfig.sortMode === 'pnl') {
                return (item.estPnl || 0) >= reqThreshold;
            } else {
                return frPercent >= reqThreshold;
            }
        });
    }
    return valid;
}

async function executeAlwaysScan() {
    if (!botRunning || isOpeningPosition) return;

    try {
        const allFunding = await fetchFundingDataFromBinance(true);
        if (!allFunding || allFunding.length === 0) return;

        const candidates = getFilteredCandidates(allFunding, userConfig.fundingThreshold, null);

        const candidateSymbols = new Set(candidates.map(c => c.symbol));
        Object.keys(alwaysPriceLock).forEach(sym => {
            if (!candidateSymbols.has(sym)) {
                delete alwaysPriceLock[sym];
            }
        });

        if (candidates.length === 0) return;

        const best = candidates[0];

        if (currentMainPositions.some(p => p.symbol === best.symbol) || currentBufferPositions.some(b => b.symbol === best.symbol)) {
            return;
        }

        const leverage = best.lev;
        const isNegative = best.fdType === 'negative';
        const mainSide = isNegative ? 'SHORT' : 'LONG';

        const currentPrice = await getCurrentPrice(best.symbol);
        if (!currentPrice) return;

        if (userConfig.enableAlwaysPriceTrigger) {
            const reqChangePct = userConfig.alwaysPriceChangePct || 5;
            if (!alwaysPriceLock[best.symbol]) {
                alwaysPriceLock[best.symbol] = {
                    lockedPrice: currentPrice,
                    fdType: best.fdType,
                    lockTime: Date.now()
                };
                log('INFO', 'ALWAYS', `🔒 [ALWAYS] Đã khóa giá ${best.symbol}: ${formatPrice(currentPrice)} | FD: ${(parseFloat(best.lastFundingRate)*100).toFixed(4)}% | Chờ giá ${mainSide === 'LONG' ? 'tăng' : 'giảm'} thêm ${reqChangePct}%`);
                return;
            }

            const lockedPrice = alwaysPriceLock[best.symbol].lockedPrice;
            let isTriggered = false;

            if (mainSide === 'LONG') {
                const targetPrice = lockedPrice * (1 + reqChangePct / 100);
                if (currentPrice >= targetPrice) {
                    isTriggered = true;
                }
            } else {
                const targetPrice = lockedPrice * (1 - reqChangePct / 100);
                if (currentPrice <= targetPrice) {
                    isTriggered = true;
                }
            }

            if (!isTriggered) {
                return;
            }

            log('SUCCESS', 'ALWAYS', `⚡ [ALWAYS TRIGGER] ${best.symbol} giá đã ${mainSide === 'LONG' ? 'tăng' : 'giảm'} đạt ${reqChangePct}% từ mốc khóa ${formatPrice(lockedPrice)} -> Giá hiện tại: ${formatPrice(currentPrice)}`);
            delete alwaysPriceLock[best.symbol];
        }

        isOpeningPosition = true;
        log('SUCCESS', 'ALWAYS', `🎯 [ALWAYS MODE] Phát hiện ${best.symbol} | Funding Rate: ${(parseFloat(best.lastFundingRate) * 100).toFixed(4)}% | Est PnL: ${best.estPnl.toFixed(2)}% | Mở ngay vị thế ${mainSide}`);

        await setLeverage(best.symbol, leverage);
        await ensureCrossMargin(best.symbol);
        await aggressiveCleanup(best.symbol);

        const acc = await callSignedAPI('/fapi/v2/account', 'GET');
        const balance = parseFloat(acc.assets.find(a => a.asset === 'USDT')?.availableBalance || 0);

        const symbolInfo = exchangeInfoCache[best.symbol];

        let initialMargin = userConfig.amountMode === 'percent' ? balance * (userConfig.amountValue / 100) : userConfig.amountValue;
        let quantity = calculateValidQuantity(symbolInfo, currentPrice, initialMargin, leverage);

        await openMainPosition(best.symbol, quantity, best.nextFundingTime, mainSide, false, best.estPnl);
    } catch (e) {
        log('ERROR', 'ALWAYS', `✖ Lỗi quét vị thế Always Mode: ${getErrorMessage(e)}`);
        isOpeningPosition = false;
    }
}

async function armT2MinuteScheduler() {
    if (!botRunning) return;
    
    clearTimeout(schedulerTimeout);

    if (userConfig.tradeMode === 'always') {
        executeAlwaysScan().catch(e => {});
        schedulerTimeout = setTimeout(armT2MinuteScheduler, 10000);
        return;
    }
    
    try {
        const allFunding = await fetchFundingDataFromBinance(true);
        if (!allFunding || allFunding.length === 0) {
            schedulerTimeout = setTimeout(armT2MinuteScheduler, 30000);
            return;
        }

        const nearestFdTime = Math.min(...allFunding.map(item => item.nextFundingTime));
        const nowServer = Date.now() + serverTimeOffset;
        
        const t2TargetTime = nearestFdTime - 120000;
        const msToWait = t2TargetTime - nowServer;

        if (msToWait > 0) {
            schedulerTimeout = setTimeout(() => {
                executeT2MinuteSingleScan(nearestFdTime);
            }, msToWait);
        } else {
            executeT2MinuteSingleScan(nearestFdTime);
        }
    } catch (e) {
        schedulerTimeout = setTimeout(armT2MinuteScheduler, 15000);
    }
}

async function executeT2MinuteSingleScan(targetFundingTime) {
    if (!botRunning) return;
    
    try {
        isOpeningPosition = true;
        const allFunding = await fetchFundingDataFromBinance(true);
        const candidates = getFilteredCandidates(allFunding, userConfig.fundingThreshold, targetFundingTime);

        if (candidates.length === 0) {
            const timeStr = new Date(targetFundingTime + 7*3600000).toISOString().substr(11, 8);
            log('WARN', 'SCAN', `⚠️ Không có coin nào tới giờ Funding (${timeStr} UTC+7) đủ điều kiện threshold (>=${userConfig.fundingThreshold}%). Bỏ qua lượt này.`);
            isOpeningPosition = false;
            const timeToNextFd = targetFundingTime - (Date.now() + serverTimeOffset);
            schedulerTimeout = setTimeout(armT2MinuteScheduler, Math.max(timeToNextFd + 10000, 30000));
            return;
        }

        const best = candidates[0];

        if (currentMainPositions.some(p => p.symbol === best.symbol) || currentBufferPositions.some(b => b.symbol === best.symbol)) {
            log('WARN', 'SCAN', `⚠️ Coin ${best.symbol} đang có vị thế mở (Always/Before). Bỏ qua để tránh mở trùng.`);
            isOpeningPosition = false;
            return;
        }

        const leverage = best.lev;
        const nowServer = Date.now() + serverTimeOffset;
        const timeStr = new Date(targetFundingTime + 7*3600000).toISOString().substr(11, 8);

        log('SUCCESS', 'SCAN', `🎯 [CHỌN COIN] Symbol: ${best.symbol} | Funding Rate: ${(parseFloat(best.lastFundingRate) * 100).toFixed(4)}% | Đòn bẩy: ${leverage}x | Est PnL: ${best.estPnl.toFixed(2)}% | Funding Time: ${timeStr} UTC+7`);

        await setLeverage(best.symbol, leverage);
        await ensureCrossMargin(best.symbol);
        await aggressiveCleanup(best.symbol);

        const acc = await callSignedAPI('/fapi/v2/account', 'GET');
        const balance = parseFloat(acc.assets.find(a => a.asset === 'USDT')?.availableBalance || 0);

        const symbolInfo = exchangeInfoCache[best.symbol];
        const currentPrice = await getCurrentPrice(best.symbol);
        
        let initialMargin = userConfig.amountMode === 'percent' ? balance * (userConfig.amountValue / 100) : userConfig.amountValue;
        let quantity = calculateValidQuantity(symbolInfo, currentPrice, initialMargin, leverage);

        const isNegative = best.fdType === 'negative';
        const bufferSide = isNegative ? 'LONG' : 'SHORT';
        const mainSide = isNegative ? 'SHORT' : 'LONG';

        const longOffsetMs = userConfig.longOffsetMs !== undefined ? userConfig.longOffsetMs : 1500;
        const shortOffsetMs = userConfig.shortOffsetMs !== undefined ? userConfig.shortOffsetMs : 0;

        const delayLong = targetFundingTime - longOffsetMs - nowServer;
        const delayShort = targetFundingTime + shortOffsetMs - nowServer;

        const tradeMode = userConfig.tradeMode || 'both';

        clearTimeout(scheduledBufferTimeout);
        if (tradeMode === 'both' && delayLong > 0) {
            scheduledBufferTimeout = setTimeout(() => {
                if (botRunning) openBufferPosition(best.symbol, leverage, balance, bufferSide, false).catch(e => {});
            }, delayLong);
        }

        clearTimeout(scheduledMainTimeout);
        if ((tradeMode === 'both' || tradeMode === 'main') && delayShort >= 0) {
            scheduledMainTimeout = setTimeout(() => {
                if (botRunning) {
                    openMainPosition(best.symbol, quantity, targetFundingTime, mainSide, false, best.estPnl).catch(e => {});
                }
            }, delayShort);
        }

        const msAfterFunding = targetFundingTime + 30000 - Date.now();
        schedulerTimeout = setTimeout(armT2MinuteScheduler, Math.max(msAfterFunding, 60000));

    } catch (e) {
        log('ERROR', 'SCAN', `✖ Lỗi thực hiện chọn coin T-2m: ${getErrorMessage(e)}`);
        isOpeningPosition = false;
        schedulerTimeout = setTimeout(armT2MinuteScheduler, 15000);
    }
}

async function openBufferPosition(symbol, leverage, balance, side, isTest = false) {
    try {
        await ensureCrossMargin(symbol);
        const symbolInfo = exchangeInfoCache[symbol];
        const currentPrice = await getCurrentPrice(symbol);
        if(!currentPrice) throw new Error("Không thể lấy giá mở lệnh Buffer");
        
        let initialMargin = userConfig.amountMode === 'percent' 
            ? balance * (userConfig.amountValue / 100) 
            : userConfig.amountValue;
            
        let quantity = calculateValidQuantity(symbolInfo, currentPrice, initialMargin, leverage);

        await executeMarketOrderWithMinVolCheck(symbol, side, side, quantity, currentPrice);
        
        const slDistance = currentPrice * (userConfig.slPercent / 100);
        const slPrice = side === 'LONG' ? currentPrice - slDistance : currentPrice + slDistance;

        log('TRADE', 'BUFFER', `🚀 Mở vị thế Buffer | Coin: ${symbol} | Hướng: ${side} | Qty: ${formatNumber(quantity)} | Đòn bẩy: ${leverage}x | Entry: ${formatPrice(currentPrice)}`);

        addToBlacklist(symbol);

        const bufPos = { 
            symbol, side, quantity, entryPrice: currentPrice, slPrice, openTime: Date.now(), isTest,
            margin: (quantity * currentPrice) / leverage, leverage
        };
        currentBufferPositions.push(bufPos);
        
        saveDataPositionsToFile();
        saveStateToFile();
        
        if (!bufferCheckInterval) bufferCheckInterval = setInterval(manageBufferPositions, 1200);

    } catch (error) {
        log('ERROR', 'BUFFER', `✖ Lỗi mở lệnh Buffer ${side} ${symbol}: ${getErrorMessage(error)}`);
    }
}

let isClosingBuffer = false;
async function manageBufferPositions() {
    if (currentBufferPositions.length === 0 || isClosingBuffer) return;
    isClosingBuffer = true;
    try {
        for (let i = currentBufferPositions.length - 1; i >= 0; i--) {
            const buf = currentBufferPositions[i];
            const currentPrice = await getCurrentPrice(buf.symbol);
            if (!currentPrice) continue;
            
            const isLong = buf.side === 'LONG';
            let isSlHit = false;

            if (isLong && currentPrice <= buf.slPrice) isSlHit = true;
            if (!isLong && currentPrice >= buf.slPrice) isSlHit = true;

            if (isSlHit) {
                log('WARN', 'SL', `⚠ Kích hoạt Stop Loss Buffer | Coin: ${buf.symbol} | Entry: ${formatPrice(buf.entryPrice)} | Giá hiện tại: ${formatPrice(currentPrice)}`);
                await closeBufferInternal(buf, 'Chạm Stop Loss Buffer', buf.isTest);
            }
        }
    } catch (e) { 
    } finally {
        isClosingBuffer = false;
    }
}

async function closeBufferInternal(bufPos, reason = 'Thời gian', isTest = false) {
    if (!bufPos) return;
    const { symbol, side, openTime, entryPrice } = bufPos;
    const orderSide = side === 'LONG' ? 'SELL' : 'BUY';
    const duration = formatDuration(openTime);
    
    currentBufferPositions = currentBufferPositions.filter(b => b !== bufPos); 

    saveDataPositionsToFile();
    saveStateToFile();

    if (currentBufferPositions.length === 0 && bufferCheckInterval) { 
        clearInterval(bufferCheckInterval); 
        bufferCheckInterval = null; 
    }

    try {
        const positions = await callSignedAPI('/fapi/v2/positionRisk', 'GET', { symbol });
        const pos = positions.find(p => p.symbol === symbol && (p.positionSide === side || p.positionSide === 'BOTH'));
        const actualAmt = pos ? Math.abs(parseFloat(pos.positionAmt)) : 0;
        const markPrice = pos ? parseFloat(pos.markPrice) : entryPrice;

        if (actualAmt > 0) {
            await callSignedAPI('/fapi/v1/order', 'POST', {
                symbol: symbol, side: orderSide, positionSide: pos.positionSide, type: 'MARKET', quantity: formatQty(symbol, actualAmt)
            });
            log('SUCCESS', 'BUFFER', `🛑 Đóng vị thế Buffer | Coin: ${symbol} | Hướng: ${side} | Giá thoát: ${formatPrice(markPrice)} | Lý do: ${reason} | Thời gian giữ: ${duration}`);
            fetchAndLogRealizedPnL(symbol, side, isTest);
        }
    } catch (error) {
        log('WARN', 'BUFFER', `⚠ Lỗi đóng Buffer ${symbol}: ${getErrorMessage(error)}.`);
        await aggressiveCleanup(symbol);
    } finally {
        const remainingForSymbol = currentMainPositions.some(p => p.symbol === symbol) || currentBufferPositions.some(b => b.symbol === symbol);
        if (!remainingForSymbol) {
            unlockBlacklistWith15MinDelay(symbol);
        }
    }
}

let isClosingMain = false;
async function openMainPosition(symbol, quantity, nextFundingTime, side, isTest = false, estPnl = 0) {
    const bufPos = currentBufferPositions.find(b => b.symbol === symbol);
    if (bufPos) {
        await closeBufferInternal(bufPos, 'Chuyển giao Main', isTest); 
    }
    
    try {
        await ensureCrossMargin(symbol);
        const currentPrice = await getCurrentPrice(symbol);

        await executeMarketOrderWithMinVolCheck(symbol, side, side, quantity, currentPrice || 0);
        
        if (!isTest) {
            globalStats.totalSessions++;
        }
        
        let realEntryPrice = 0;
        let lev = getLeverageFromCache(symbol);

        await new Promise(r => setTimeout(r, 500));
        try {
            const positions = await callSignedAPI('/fapi/v2/positionRisk', 'GET', { symbol });
            const pos = positions.find(p => p.symbol === symbol && (p.positionSide === side || p.positionSide === 'BOTH'));
            if (pos && parseFloat(pos.positionAmt) !== 0) {
                realEntryPrice = parseFloat(pos.entryPrice);
                lev = parseInt(pos.leverage);
            }
        } catch (e) {}

        if (!realEntryPrice || realEntryPrice === 0) {
            realEntryPrice = currentPrice || 0;
        }

        const margin = (quantity * realEntryPrice) / (lev || 1);
        log('TRADE', 'MAIN', `🚀 Mở vị thế Main | Coin: ${symbol} | Hướng: ${side} | Qty: ${formatNumber(quantity)} | Đòn bẩy: ${lev}x | Margin: ${margin.toFixed(2)} USDT | Entry: ${formatPrice(realEntryPrice)}`);

        addToBlacklist(symbol);

        const mainPos = { 
            symbol, side, quantity, openTime: Date.now(), entryPrice: realEntryPrice, extremePrice: realEntryPrice, nextFundingTime, isTest,
            margin, leverage: lev
        };
        currentMainPositions.push(mainPos);
        
        saveDataPositionsToFile();
        saveStateToFile();

        if (!mainCheckInterval) mainCheckInterval = setInterval(manageMainPositions, 1200);

        lastOrderOpenTime = Date.now();
        setTimeout(() => { isOpeningPosition = false; }, 60000);

    } catch (error) {
        log('ERROR', 'MAIN', `✖ Lỗi mở lệnh MAIN ${side} ${symbol}: ${getErrorMessage(error)}`);
        isOpeningPosition = false;
        armT2MinuteScheduler();
    }
}

async function manageMainPositions() {
    if (currentMainPositions.length === 0 || isClosingMain) return;
    isClosingMain = true;
    try {
        const currentServerTime = Date.now() + serverTimeOffset;

        for (let i = currentMainPositions.length - 1; i >= 0; i--) {
            const pos = currentMainPositions[i];
            if (!pos) continue;
            const { symbol, side, entryPrice, nextFundingTime, openTime, isTest } = pos;
            const isLong = side === 'LONG';

            if (userConfig.tradeMode === 'always') {
                const elapsedMins = (Date.now() - openTime) / 60000;
                const maxHoldMins = userConfig.holdMinutes || 15;
                if (elapsedMins >= maxHoldMins) {
                    log('INFO', 'MAIN', `⏳ [ALWAYS MODE] Đã giữ lệnh ${elapsedMins.toFixed(1)}m >= ${maxHoldMins}m. Tự động đóng vị thế ngay lập tức!`);
                    await closeMainInternal(pos, `Hết thời gian Always (${maxHoldMins}m)`, isTest);
                    continue;
                }
            } else if (nextFundingTime && currentServerTime >= nextFundingTime) {
                log('INFO', 'MAIN', `⏳ Hết giờ Funding cho ${symbol}. Tự động đóng vị thế ngay lập tức!`);
                await closeMainInternal(pos, 'Hết giờ Funding', isTest);
                continue;
            }

            if (nextFundingTime && isTest) {
                const timeRemaining = nextFundingTime - currentServerTime;
                if (timeRemaining <= 1500 && timeRemaining > 0) {
                    log('INFO', 'MAIN', `⏳ [TEST] Còn <= 1500ms tới giờ Funding. Tự động đóng lệnh TEST!`);
                    await closeMainInternal(pos, 'Test Auto Close', true);
                    continue;
                }
            }
            
            const currentPrice = await getCurrentPrice(symbol);
            if (!currentPrice) continue;

            let stateUpdated = false;
            if (isLong) {
                if (!pos.extremePrice || currentPrice > pos.extremePrice) {
                    pos.extremePrice = currentPrice;
                    stateUpdated = true;
                }
            } else {
                if (!pos.extremePrice || currentPrice < pos.extremePrice) {
                    pos.extremePrice = currentPrice;
                    stateUpdated = true;
                }
            }
            if (stateUpdated) {
                saveDataPositionsToFile();
                saveStateToFile();
            }

            const extremePrice = pos.extremePrice || entryPrice;
            const tpFixedPct = userConfig.tpFixedPercent || 1;
            const enableTrailing = userConfig.enableTrailing || false;
            const tpTrailingPct = userConfig.tpTrailingPercent || 1;
            const slPct = userConfig.slPercent || 2;

            const maxGainPct = isLong ? 
                ((extremePrice - entryPrice) / entryPrice) * 100 : 
                ((entryPrice - extremePrice) / entryPrice) * 100;

            const fixedSL = isLong ? 
                entryPrice - (entryPrice * (slPct / 100)) : 
                entryPrice + (entryPrice * (slPct / 100));

            const tpFixedPrice = isLong ?
                entryPrice + (entryPrice * (tpFixedPct / 100)) :
                entryPrice - (entryPrice * (tpFixedPct / 100));

            let activeSL = fixedSL;
            let isSlPositive = false;
            let closeReason = 'Chạm Stop Loss';

            if (maxGainPct >= tpFixedPct) {
                isSlPositive = true;
                if (enableTrailing) {
                    if (isLong) {
                        const trailedSL = extremePrice - (entryPrice * (tpTrailingPct / 100));
                        activeSL = Math.max(tpFixedPrice, trailedSL);
                    } else {
                        const trailedSL = extremePrice + (entryPrice * (tpTrailingPct / 100));
                        activeSL = Math.min(tpFixedPrice, trailedSL);
                    }
                    closeReason = 'Chốt Lãi TP Trailing';
                } else {
                    activeSL = tpFixedPrice;
                    closeReason = 'Chốt Lãi TP Cứng';
                }
            }

            pos.dynamicSL = activeSL; 
            pos.isSlPositive = isSlPositive;

            let triggerClose = false;
            if (isLong && currentPrice <= activeSL) triggerClose = true;
            if (!isLong && currentPrice >= activeSL) triggerClose = true;

            if (triggerClose) {
                if (isSlPositive) {
                    log('SUCCESS', 'TP', `🎯 Kích hoạt ${closeReason} | Coin: ${symbol} | Entry: ${formatPrice(entryPrice)} | Giá chốt: ${formatPrice(activeSL)} | Giá hiện tại: ${formatPrice(currentPrice)}`);
                } else {
                    log('WARN', 'SL', `⚠ Kích hoạt Stop Loss | Coin: ${symbol} | Entry: ${formatPrice(entryPrice)} | Giá SL: ${formatPrice(activeSL)} | Giá hiện tại: ${formatPrice(currentPrice)}`);
                }
                await closeMainInternal(pos, closeReason, isTest);
            }
        }
    } catch (error) { 
        log('ERROR', 'MAIN_CHECK', `Lỗi kiểm tra vị thế Main: ${getErrorMessage(error)}`);
    } finally {
        isClosingMain = false;
    }
}

async function closeMainInternal(mainPos, reason = 'Thủ công', isTest = false) {
    if (!mainPos) return;
    const { symbol, side, openTime, entryPrice } = mainPos;
    const orderSide = side === 'LONG' ? 'SELL' : 'BUY';
    const duration = formatDuration(openTime);

    currentMainPositions = currentMainPositions.filter(p => p !== mainPos);
    
    saveDataPositionsToFile();
    saveStateToFile();

    try {
        const positions = await callSignedAPI('/fapi/v2/positionRisk', 'GET', { symbol });
        const pos = positions.find(p => p.symbol === symbol && (p.positionSide === side || p.positionSide === 'BOTH'));
        const actualAmt = pos ? Math.abs(parseFloat(pos.positionAmt)) : 0;
        const markPrice = pos ? parseFloat(pos.markPrice) : entryPrice;

        if (actualAmt > 0) {
            await callSignedAPI('/fapi/v1/order', 'POST', {
                symbol: symbol, side: orderSide, positionSide: pos ? pos.positionSide : side, type: 'MARKET', quantity: formatQty(symbol, actualAmt)
            });
            log('SUCCESS', 'MAIN', `🛑 Đóng vị thế Main | Coin: ${symbol} | Hướng: ${side} | Giá vào: ${formatPrice(entryPrice)} | Giá thoát: ${formatPrice(markPrice)} | Lý do: ${reason} | Thời gian giữ: ${duration}`);
            fetchAndLogRealizedPnL(symbol, side, isTest);
        }
    } catch (error) {
        log('ERROR', 'MAIN', `✖ Lỗi khi đóng MAIN ${symbol}: ${getErrorMessage(error)}.`);
        await aggressiveCleanup(symbol);
    } finally {
        cleanupAfterClose(symbol);
    }
}

function cleanupAfterClose(symbol) {
    saveDataPositionsToFile();
    saveStateToFile();

    const remainingForSymbol = currentMainPositions.some(p => p.symbol === symbol) || currentBufferPositions.some(b => b.symbol === symbol);
    if (!remainingForSymbol) {
        unlockBlacklistWith15MinDelay(symbol);
    }

    if (currentMainPositions.length === 0 && mainCheckInterval) { 
        clearInterval(mainCheckInterval); 
        mainCheckInterval = null; 
    }
    setTimeout(async () => {
        const stillRemaining = currentMainPositions.some(p => p.symbol === symbol) || currentBufferPositions.some(b => b.symbol === symbol);
        if (!stillRemaining) {
            await aggressiveCleanup(symbol);
        }
        if (botRunning) armT2MinuteScheduler();
    }, 10000);
}

function startAntiLiquidationMonitor() {
    if (antiLiquidationInterval) clearInterval(antiLiquidationInterval);
    antiLiquidationInterval = setInterval(async () => {
        if (!botRunning || isOpeningPosition) return;
        try {
            const acc = await callSignedAPI('/fapi/v2/account', 'GET');
            const totalWalletBalance = parseFloat(acc.totalWalletBalance || 0);
            const availableBalance = parseFloat(acc.availableBalance || 0);

            if (totalWalletBalance > 0 && availableBalance <= (totalWalletBalance * 0.15)) {
                log('WARN', 'POSITION', `🚨 BÁO ĐỘNG: Margin/Khả dụng còn lại <= 15% số dư tài khoản. KÍCH HOẠT CHỐNG THANH LÝ TOÀN BỘ SÀN!`);
                botRunning = false; 
                
                await callSignedAPI('/fapi/v1/allOpenOrders', 'DELETE'); 
                const positions = await callSignedAPI('/fapi/v2/positionRisk', 'GET');
                
                for (const p of positions) {
                    const amt = parseFloat(p.positionAmt);
                    if (Math.abs(amt) > 0) {
                        const side = amt > 0 ? 'SELL' : 'BUY';
                        await callSignedAPI('/fapi/v1/order', 'POST', {
                            symbol: p.symbol, side: side, positionSide: p.positionSide, type: 'MARKET', quantity: formatQty(p.symbol, Math.abs(amt))
                        });
                    }
                }
                currentMainPositions = [];
                currentBufferPositions = [];
                saveDataPositionsToFile();
                saveStateToFile();
                log('SUCCESS', 'POSITION', `🛑 Đã ĐÓNG TOÀN BỘ vị thế trên tài khoản. Bot tự động TẮT để bảo toàn vốn.`);
            }
        } catch(e) {}
    }, 20000);
}

async function restoreActivePositionsOnStartup() {
    loadStateFromFile();
    const dataSaved = loadDataPositionsFromFile();
    
    let candidateMains = dataSaved.mainPositions.length > 0 ? dataSaved.mainPositions : currentMainPositions;
    let candidateBuffers = dataSaved.bufferPositions.length > 0 ? dataSaved.bufferPositions : currentBufferPositions;

    if (!userConfig.apiKey || !userConfig.secretKey) return;
    try {
        await syncServerTime();
        await updateAllLeverageCache(); 
        await getExchangeInfo();
        const positions = await callSignedAPI('/fapi/v2/positionRisk', 'GET');
        
        const validMains = [];
        for (const mainPos of candidateMains) {
            const pos = positions.find(p => p.symbol === mainPos.symbol && (p.positionSide === mainPos.side || p.positionSide === 'BOTH'));
            if (pos) {
                const actualAmt = Math.abs(parseFloat(pos.positionAmt));
                if (actualAmt > 0 && (Math.abs(actualAmt - parseFloat(mainPos.quantity)) < 0.001 || Math.abs(actualAmt - parseFloat(mainPos.quantity)) / actualAmt < 0.02)) {
                    log('SUCCESS', 'SYNC', `✓ Khôi phục quản lý MAIN ${mainPos.side} ${mainPos.symbol} (Entry: ${mainPos.entryPrice})`);
                    validMains.push(mainPos);
                    addToBlacklist(mainPos.symbol);
                }
            }
        }
        currentMainPositions = validMains;

        const validBuffers = [];
        for (const bufPos of candidateBuffers) {
            const pos = positions.find(p => p.symbol === bufPos.symbol && (p.positionSide === bufPos.side || p.positionSide === 'BOTH'));
            if (pos) {
                const actualAmt = Math.abs(parseFloat(pos.positionAmt));
                if (actualAmt > 0 && (Math.abs(actualAmt - parseFloat(bufPos.quantity)) < 0.001 || Math.abs(actualAmt - parseFloat(bufPos.quantity)) / actualAmt < 0.02)) {
                    log('SUCCESS', 'SYNC', `✓ Khôi phục quản lý BUFFER ${bufPos.side} ${bufPos.symbol}`);
                    validBuffers.push(bufPos);
                    addToBlacklist(bufPos.symbol);
                }
            }
        }
        currentBufferPositions = validBuffers;

        saveDataPositionsToFile();
        saveStateToFile();

        if (currentMainPositions.length > 0) {
            botRunning = true;
            if (mainCheckInterval) clearInterval(mainCheckInterval);
            mainCheckInterval = setInterval(manageMainPositions, 1200);
        }

        if (currentBufferPositions.length > 0) {
            botRunning = true;
            if (bufferCheckInterval) clearInterval(bufferCheckInterval);
            bufferCheckInterval = setInterval(manageBufferPositions, 1200);
        }

        if (botRunning) {
            startAntiLiquidationMonitor();
            armT2MinuteScheduler();
        }
    } catch (e) {
        log('ERROR', 'SYNC', `✖ Lỗi khôi phục vị thế: ${getErrorMessage(e)}`);
    }
}

async function getDashboardDataCached() {
    if (!botRunning) return { running: false };
    const now = Date.now();

    if (isOpeningPosition || (cachedDashboardData && (now - lastDashboardFetchTime < DASHBOARD_CACHE_TTL))) {
        if (cachedDashboardData) return cachedDashboardData;
    }

    if (!userConfig.apiKey || !userConfig.secretKey) {
        return { running: true, error: "Thiếu API Key" };
    }

    try {
        const acc = await callSignedAPI('/fapi/v2/account', 'GET');
        
        const balance = parseFloat(acc.assets.find(a => a.asset === 'USDT')?.availableBalance || 0);
        const walletBalance = parseFloat(acc.totalWalletBalance || 0);
        const totalUnrealizedProfit = parseFloat(acc.totalUnrealizedProfit || 0);
        const totalWalletBalance = walletBalance + totalUnrealizedProfit; 

        const openOrdersInfo = await callSignedAPI('/fapi/v1/openOrders', 'GET');
        const allPositions = await callSignedAPI('/fapi/v2/positionRisk', 'GET');
        const openPositions = allPositions.filter(p => parseFloat(p.positionAmt) !== 0);
        
        let positionsRes = [];
        for (const p of openPositions) {
            const posAmt = parseFloat(p.positionAmt);
            const posAmtAbs = Math.abs(posAmt);
            const entryPrice = parseFloat(p.entryPrice);
            const markPrice = parseFloat(p.markPrice);
            const lev = parseInt(p.leverage);
            const margin = (posAmtAbs * entryPrice) / lev;
            const pnl = parseFloat(p.unRealizedProfit);
            
            const isLong = p.positionSide === 'LONG' || (p.positionSide === 'BOTH' && posAmt > 0);
            const sideStr = isLong ? 'LONG' : 'SHORT';
            
            const pctFromEntry = entryPrice > 0 ? (isLong ? ((markPrice - entryPrice) / entryPrice) * 100 : ((entryPrice - markPrice) / entryPrice) * 100) : 0;

            const isMatchMain = currentMainPositions.find(m => 
                m.symbol === p.symbol && 
                (m.side === p.positionSide || p.positionSide === 'BOTH')
            );

            const isMatchBuffer = currentBufferPositions.find(b => 
                b.symbol === p.symbol && 
                (b.side === p.positionSide || p.positionSide === 'BOTH')
            );

            if (!isMatchMain && !isMatchBuffer) {
                continue;
            }

            let deepest = markPrice;
            let openTime = Date.now();
            let posType = 'MAIN';
            let nextFundingTime = null;

            if (isMatchMain) {
                deepest = isMatchMain.extremePrice || markPrice;
                openTime = isMatchMain.openTime || Date.now();
                posType = isMatchMain.isTest ? 'TEST MAIN' : 'MAIN';
                nextFundingTime = isMatchMain.nextFundingTime || null;
            } else if (isMatchBuffer) {
                deepest = markPrice;
                openTime = isMatchBuffer.openTime || Date.now();
                posType = isMatchBuffer.isTest ? 'TEST BUFFER' : 'BUFFER';
            }

            const slPct = userConfig.slPercent || 2;
            const tpFixedPct = userConfig.tpFixedPercent || 1;
            const enableTrailing = userConfig.enableTrailing || false;
            const tpTrailingPct = userConfig.tpTrailingPercent || 1;
            const holdMins = userConfig.holdMinutes || 15;

            const slPrice = isLong ? 
                entryPrice - (entryPrice * (slPct / 100)) : 
                entryPrice + (entryPrice * (slPct / 100));
            const slPnlRoi = -slPct * lev;
            const slPnlAmount = margin * (slPnlRoi / 100);

            const tpFixedPrice = isLong ? 
                entryPrice + (entryPrice * (tpFixedPct / 100)) : 
                entryPrice - (entryPrice * (tpFixedPct / 100));
            const tpFixedPnlRoi = tpFixedPct * lev;
            const tpFixedPnlAmount = margin * (tpFixedPnlRoi / 100);

            let extremePrice = deepest || entryPrice;
            let maxGainPct = isLong ? 
                ((extremePrice - entryPrice) / entryPrice) * 100 : 
                ((entryPrice - extremePrice) / entryPrice) * 100;

            let isReached = maxGainPct >= tpFixedPct;
            
            let tpTrailingPrice = 0;
            let tpTrailingPnlRoi = 0;
            let tpTrailingPnlAmount = 0;

            if (enableTrailing) {
                if (!isReached) {
                    tpTrailingPrice = isLong ? 
                        entryPrice * (1 + (tpFixedPct + tpTrailingPct) / 100) : 
                        entryPrice * (1 - (tpFixedPct + tpTrailingPct) / 100);
                    tpTrailingPnlRoi = (tpFixedPct + tpTrailingPct) * lev;
                    tpTrailingPnlAmount = margin * (tpTrailingPnlRoi / 100);
                } else {
                    if (isLong) {
                        const trailedSL = extremePrice - (entryPrice * (tpTrailingPct / 100));
                        tpTrailingPrice = Math.max(tpFixedPrice, trailedSL);
                        tpTrailingPnlRoi = ((tpTrailingPrice - entryPrice) / entryPrice) * 100 * lev;
                    } else {
                        const trailedSL = extremePrice + (entryPrice * (tpTrailingPct / 100));
                        tpTrailingPrice = Math.min(tpFixedPrice, trailedSL);
                        tpTrailingPnlRoi = ((entryPrice - tpTrailingPrice) / entryPrice) * 100 * lev;
                    }
                    tpTrailingPnlAmount = margin * (tpTrailingPnlRoi / 100);
                }
            }

            let remainingMs = 0;
            if (userConfig.tradeMode === 'always') {
                const targetCloseTime = openTime + (holdMins * 60000);
                remainingMs = Math.max(0, targetCloseTime - Date.now());
            } else if (nextFundingTime) {
                remainingMs = Math.max(0, nextFundingTime - (Date.now() + serverTimeOffset));
            }

            positionsRes.push({
                coin: p.symbol,
                side: sideStr,
                size: formatNumber(posAmtAbs),
                leverage: lev,
                margin: margin,
                pnl: pnl,
                pctFromEntry: pctFromEntry,
                entryPrice: entryPrice,
                markPrice: markPrice,
                openTime: openTime,
                remainingMs: remainingMs,
                holdMinutes: holdMins,
                slPrice: slPrice,
                slPnlRoi: slPnlRoi,
                slPnlAmount: slPnlAmount,
                tpFixedPrice: tpFixedPrice,
                tpFixedPnlRoi: tpFixedPnlRoi,
                tpFixedPnlAmount: tpFixedPnlAmount,
                enableTrailing: enableTrailing,
                isReached: isReached,
                tpTrailingPct: tpTrailingPct,
                extremePrice: extremePrice,
                tpTrailingPrice: tpTrailingPrice,
                tpTrailingPnlRoi: tpTrailingPnlRoi,
                tpTrailingPnlAmount: tpTrailingPnlAmount,
                type: posType
            });
        }
        
        cachedDashboardData = {
            running: true, 
            balance, 
            totalWalletBalance, 
            openOrders: openOrdersInfo.length, 
            totalSessions: globalStats.totalSessions, 
            totalPnl: globalStats.totalPnl, 
            positions: positionsRes
        };
        lastDashboardFetchTime = now;
        return cachedDashboardData;
    } catch (e) { 
        return cachedDashboardData || { running: true, error: getErrorMessage(e) }; 
    }
}

function updateParamsFromQuery(query) {
    let isUpdated = false;
    if (query.apiKey !== undefined && query.apiKey.trim() !== '') { userConfig.apiKey = query.apiKey.trim(); isUpdated = true; }
    if (query.secretKey !== undefined && query.secretKey.trim() !== '') { userConfig.secretKey = query.secretKey.trim(); isUpdated = true; }
    if (query.amountMode) { userConfig.amountMode = query.amountMode; isUpdated = true; }
    if (query.amountValue !== undefined && !isNaN(parseFloat(query.amountValue))) { userConfig.amountValue = parseFloat(query.amountValue); isUpdated = true; }
    if (query.tpFixed !== undefined && !isNaN(parseFloat(query.tpFixed))) { userConfig.tpFixedPercent = parseFloat(query.tpFixed); isUpdated = true; } 
    if (query.tp !== undefined && query.tpFixed === undefined && !isNaN(parseFloat(query.tp))) { userConfig.tpFixedPercent = parseFloat(query.tp); isUpdated = true; }
    if (query.enableTrailing !== undefined) { userConfig.enableTrailing = query.enableTrailing === 'true' || query.enableTrailing === true; isUpdated = true; }
    if (query.tpTrailing !== undefined && !isNaN(parseFloat(query.tpTrailing))) { userConfig.tpTrailingPercent = parseFloat(query.tpTrailing); isUpdated = true; }
    if (query.sl !== undefined && !isNaN(parseFloat(query.sl))) { userConfig.slPercent = parseFloat(query.sl); isUpdated = true; }
    if (query.longMs !== undefined && query.longMs !== '') { userConfig.longOffsetMs = parseInt(query.longMs); isUpdated = true; }
    if (query.shortMs !== undefined && query.shortMs !== '') { userConfig.shortOffsetMs = parseInt(query.shortMs); isUpdated = true; }
    if (query.threshold !== undefined && query.threshold !== '') { userConfig.fundingThreshold = parseFloat(query.threshold); isUpdated = true; }
    if (query.tradeMode) { tradeMode: query.tradeMode; isUpdated = true; }
    if (query.sortMode) { userConfig.sortMode = query.sortMode; isUpdated = true; }
    if (query.holdMinutes !== undefined && query.holdMinutes !== '' && !isNaN(parseFloat(query.holdMinutes))) { userConfig.holdMinutes = parseFloat(query.holdMinutes); isUpdated = true; }
    if (query.enableAlwaysPriceTrigger !== undefined) { userConfig.enableAlwaysPriceTrigger = query.enableAlwaysPriceTrigger === 'true' || query.enableAlwaysPriceTrigger === true; isUpdated = true; }
    if (query.alwaysPriceChangePct !== undefined && !isNaN(parseFloat(query.alwaysPriceChangePct))) { userConfig.alwaysPriceChangePct = parseFloat(query.alwaysPriceChangePct); isUpdated = true; }
    return isUpdated;
}

async function startBotLogicInternal(query) {
    if (botRunning) return 'Bot đã đang chạy.';
    const isUpdated = updateParamsFromQuery(query);

    if (isUpdated) { saveConfigToFile(); }
    cachedDashboardData = null;
    try {
        await syncServerTime();
        await updateAllLeverageCache();
        await getExchangeInfo();
        botRunning = true; 
        botStartTime = new Date();
        saveStateToFile();
        startAntiLiquidationMonitor();
        armT2MinuteScheduler();
        return 'Bot Khởi Động Thành Công.';
    } catch (e) { return 'Lỗi Khởi Động: ' + getErrorMessage(e); }
}

function stopBotLogicInternal() {
    botRunning = false;
    cachedDashboardData = null;
    clearTimeout(schedulerTimeout);
    clearTimeout(scheduledBufferTimeout);
    clearTimeout(scheduledMainTimeout);
    if(mainCheckInterval) clearInterval(mainCheckInterval);
    if(bufferCheckInterval) clearInterval(bufferCheckInterval);
    if(antiLiquidationInterval) clearInterval(antiLiquidationInterval);
    saveStateToFile();
    return 'Bot Đã Dừng.';
}

loadConfigFromFile();
loadStateFromFile();

memoryLogs.length = 0;
globalStats.totalSessions = 0;
globalStats.totalPnl = 0;
saveStateToFile();

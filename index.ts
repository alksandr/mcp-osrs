#!/usr/bin/env node

import { Server } from "@modelcontextprotocol/sdk/server/index.js";
import { StdioServerTransport } from "@modelcontextprotocol/sdk/server/stdio.js";
import {
    CallToolRequestSchema,
    ListToolsRequestSchema,
} from "@modelcontextprotocol/sdk/types.js";
import { z } from 'zod';
import axios from 'axios';
import { zodToJsonSchema } from 'zod-to-json-schema';
import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';
import * as cheerio from 'cheerio';
import TurndownService from 'turndown';
import http from 'http';
import https from 'https';

/**
 * Represents a single drop table entry
 */
interface DropTableEntry {
    item: string;
    quantity: string;
    rarity: string;
    rarityPercent?: string;
}

/**
 * Represents a categorized drop table section
 */
interface DropTableSection {
    category: string;
    drops: DropTableEntry[];
}

/**
 * Represents a drop entry from osrsreboxed-db
 */
interface OsrsBoxDrop {
    id: number;
    name: string;
    members: boolean;
    quantity: string;
    noted: boolean;
    rarity: number;  // Decimal rarity e.g., 0.003333 = 1/300
    rolls: number;
}

/**
 * Represents a monster from osrsreboxed-db
 */
interface OsrsBoxMonster {
    id: number;
    name: string;
    combat_level: number;
    hitpoints: number;
    wiki_url: string;
    drops: OsrsBoxDrop[];
}

/**
 * Represents an item source entry for reverse lookups
 */
interface ItemSourceEntry {
    monsterId: number;
    monsterName: string;
    combatLevel: number;
    rarity: number;
    quantity: string;
    noted: boolean;
}

/**
 * Cache structure for osrsreboxed-db data
 */
interface OsrsBoxCache {
    monsters: Map<number, OsrsBoxMonster>;
    monsterNameIndex: Map<string, number[]>;  // lowercase name -> monster IDs
    itemDropIndex: Map<number, ItemSourceEntry[]>;  // item ID -> sources
    timestamp: number;
}

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const DATA_DIR = path.join(__dirname, 'data');

// File caching for improved performance
const fileCache: Map<string, { lines: string[], timestamp: number }> = new Map();
const idIndexCache: Map<string, Map<number, number>> = new Map();
const CACHE_TTL = 60 * 60 * 1000; // 1 hour cache TTL

// Wiki API response cache
const wikiCache: Map<string, { data: any, timestamp: number }> = new Map();
const WIKI_CACHE_TTL = 30 * 60 * 1000; // 30 minutes
const WIKI_CACHE_MAX_SIZE = 500;

// Cache statistics tracking
let fileCacheHits = 0;
let fileCacheMisses = 0;
let wikiCacheHits = 0;
let wikiCacheMisses = 0;

// osrsreboxed-db cache (in-memory + disk)
let osrsBoxCache: OsrsBoxCache | null = null;
const OSRSBOX_CACHE_TTL = 24 * 60 * 60 * 1000;  // 24 hours
const OSRSBOX_CACHE_FILE = 'osrsbox-monsters.json';
const OSRSBOX_GITHUB_URL = 'https://raw.githubusercontent.com/0xNeffarion/osrsreboxed-db/master/docs/monsters-complete.json';

// Environment variable for optional startup refresh of osrsbox data
const REFRESH_OSRSBOX_ON_STARTUP = process.env.OSRS_REFRESH_OSRSBOX === 'true';

/**
 * Get cached file lines or read from disk if cache is expired/missing
 * @param filePath Path to the file to read
 * @returns Array of lines from the file
 */
function getCachedFileLines(filePath: string): string[] {
    const now = Date.now();
    const cached = fileCache.get(filePath);

    // Check if we have a valid cached version
    if (cached && (now - cached.timestamp) < CACHE_TTL) {
        fileCacheHits++;
        return cached.lines;
    }

    // Cache miss - read file from disk
    fileCacheMisses++;

    if (!fs.existsSync(filePath)) {
        throw new Error(`File not found: ${filePath}`);
    }

    const content = fs.readFileSync(filePath, 'utf8');
    const lines = content.split('\n').map(line => line.replace(/\r$/, ''));

    // Cache the result
    fileCache.set(filePath, { lines, timestamp: now });

    // Invalidate the ID index cache for this file since content may have changed
    idIndexCache.delete(filePath);

    return lines;
}

/**
 * Build an ID index for fast ID lookups in a file
 * The index maps ID numbers to their line indices
 * @param filePath Path to the file
 * @returns Map of ID to line index
 */
function buildIdIndex(filePath: string): Map<number, number> {
    // Check if we have a cached index
    const cachedIndex = idIndexCache.get(filePath);
    if (cachedIndex) {
        // Verify the file cache is still valid (if file cache expired, index is invalid)
        const fileEntry = fileCache.get(filePath);
        if (fileEntry && (Date.now() - fileEntry.timestamp) < CACHE_TTL) {
            return cachedIndex;
        }
    }

    // Build the index from cached lines
    const lines = getCachedFileLines(filePath);
    const index = new Map<number, number>();

    for (let i = 0; i < lines.length; i++) {
        const line = lines[i];
        // Extract ID from the beginning of the line (common format: "123\tSomeName")
        const match = line.match(/^(\d+)/);
        if (match) {
            const id = parseInt(match[1], 10);
            if (!isNaN(id)) {
                index.set(id, i);
            }
        }
    }

    // Cache the index
    idIndexCache.set(filePath, index);

    return index;
}

/**
 * Generate a cache key from API action and parameters
 */
function getWikiCacheKey(action: string, params: Record<string, any>): string {
    const sortedParams = Object.keys(params)
        .sort()
        .map(key => `${key}=${params[key]}`)
        .join('&');
    return `${action}:${sortedParams}`;
}

/**
 * Get data from wiki cache if valid (not expired)
 */
function getFromWikiCache(key: string): any | null {
    const cached = wikiCache.get(key);
    if (!cached) {
        wikiCacheMisses++;
        return null;
    }

    const now = Date.now();
    if (now - cached.timestamp > WIKI_CACHE_TTL) {
        // Expired, remove from cache
        wikiCache.delete(key);
        wikiCacheMisses++;
        return null;
    }

    wikiCacheHits++;
    return cached.data;
}

/**
 * Store data in wiki cache, evicting oldest entries if at max size
 */
function setWikiCache(key: string, data: any): void {
    // If at max size, evict oldest entry (first entry in Map maintains insertion order)
    if (wikiCache.size >= WIKI_CACHE_MAX_SIZE) {
        const oldestKey = wikiCache.keys().next().value;
        if (oldestKey) {
            wikiCache.delete(oldestKey);
        }
    }

    wikiCache.set(key, {
        data,
        timestamp: Date.now()
    });
}

// Request deduplication - prevents duplicate in-flight requests
const pendingRequests = new Map<string, Promise<any>>();

async function fetchWithDedup<T>(key: string, fetcher: () => Promise<T>): Promise<T> {
    const existing = pendingRequests.get(key);
    if (existing) {
        return existing as Promise<T>;
    }

    const promise = fetcher().finally(() => {
        pendingRequests.delete(key);
    });

    pendingRequests.set(key, promise);
    return promise;
}

const responseToString = (response: any) => {
    const contentText = typeof response === 'string' ? response : JSON.stringify(response);
    return {
        content: [{ type: "text", text: contentText }]
    };
};

/**
 * Extract structured data from wiki infobox tables
 */
function extractInfobox(html: string): Record<string, any> | null {
    const $ = cheerio.load(html);
    const infobox: Record<string, any> = {};

    // Find infobox tables (various classes used by OSRS wiki)
    const infoboxTable = $('.infobox-monster, .infobox-item, .infobox-bonuses, .infobox').first();
    if (!infoboxTable.length) return null;

    // Extract all key-value pairs from rows
    infoboxTable.find('tr').each((_, row) => {
        const $row = $(row);
        const header = $row.find('th').text().trim().toLowerCase().replace(/\s+/g, '_');
        const value = $row.find('td').text().trim();
        if (header && value) {
            infobox[header] = value;
        }
    });

    return Object.keys(infobox).length > 0 ? infobox : null;
}

/**
 * Convert rarity string to percentage where possible
 * Examples: "1/128" -> "0.78%", "Always" -> "100%", "2 x 1/1,024" -> "0.195%"
 */
function rarityToPercent(rarity: string): string | undefined {
    const cleaned = rarity.toLowerCase().trim();

    // Handle "Always" case
    if (cleaned === 'always') {
        return '100%';
    }

    // Handle common rarity terms
    if (cleaned === 'common') return '~10-20%';
    if (cleaned === 'uncommon') return '~5-10%';
    if (cleaned === 'rare') return '~1-5%';
    if (cleaned === 'very rare') return '<1%';

    // Handle fraction format: "1/128" or "2 x 1/1,024" or "2 × 1/1,024"
    // First check for multiplier prefix like "2 x" or "2 ×"
    let multiplier = 1;
    const multiplierMatch = rarity.match(/^(\d+)\s*[x×]\s*/i);
    if (multiplierMatch) {
        multiplier = parseInt(multiplierMatch[1], 10);
    }

    // Find the fraction part
    const fractionMatch = rarity.match(/(\d+)\s*\/\s*([\d,]+)/);
    if (fractionMatch) {
        const numerator = parseInt(fractionMatch[1].replace(/,/g, ''), 10);
        const denominator = parseInt(fractionMatch[2].replace(/,/g, ''), 10);
        if (denominator > 0) {
            const percentage = (numerator / denominator) * multiplier * 100;
            // Format nicely based on size
            if (percentage >= 1) {
                return `${percentage.toFixed(2)}%`;
            } else if (percentage >= 0.01) {
                return `${percentage.toFixed(3)}%`;
            } else {
                return `${percentage.toFixed(4)}%`;
            }
        }
    }

    return undefined;
}

/**
 * Extract structured drop table data from wiki HTML
 * Parses OSRS Wiki drop tables which use wikitable class with Item, Quantity, Rarity columns
 */
function extractDropTable(html: string): DropTableSection[] {
    const $ = cheerio.load(html);
    const dropSections: DropTableSection[] = [];

    // Track current category based on headings
    let currentCategory = 'Drops';

    // Find all wikitables that appear to be drop tables
    // Drop tables typically have columns: Item, Quantity, Rarity, Price, High Alch
    $('table.wikitable').each((_, table) => {
        const $table = $(table);

        // Check if this looks like a drop table by examining headers
        const headers: string[] = [];
        $table.find('th').each((_, th) => {
            headers.push($(th).text().trim().toLowerCase());
        });

        // A drop table should have at minimum Item and Rarity columns
        const hasItemCol = headers.some(h => h.includes('item'));
        const hasRarityCol = headers.some(h => h.includes('rarity'));

        if (!hasItemCol || !hasRarityCol) {
            return; // Skip non-drop tables
        }

        // Find the best preceding heading by traversing siblings
        // Prefer higher-level headings (h2 > h3 > h4) as they represent main sections
        let currentElement = $table.prev();
        let bestHeading: { element: ReturnType<typeof $> | null, level: number } = { element: null, level: 5 };

        while (currentElement.length > 0) {
            // Check for headings and track the best one (lowest level number = highest priority)
            if (currentElement.is('h2')) {
                bestHeading = { element: currentElement, level: 2 };
                break; // h2 is authoritative, stop here
            } else if (currentElement.is('h3') && bestHeading.level > 3) {
                bestHeading = { element: currentElement, level: 3 };
            } else if (currentElement.is('h4') && bestHeading.level > 4) {
                bestHeading = { element: currentElement, level: 4 };
            }

            // If we hit another drop table, stop (category belongs to that table)
            if (currentElement.is('table.wikitable') && currentElement.find('th').toArray().some(th =>
                $(th).text().toLowerCase().includes('rarity'))) {
                break;
            }
            currentElement = currentElement.prev();
        }

        if (bestHeading.element && bestHeading.element.length) {
            const headingText = bestHeading.element.find('.mw-headline').text().trim() ||
                               bestHeading.element.text().replace(/\[edit\]/gi, '').trim();
            if (headingText) {
                currentCategory = headingText;
            }
        }

        // Find column indices from header row
        let itemColIdx = -1;
        let quantityColIdx = -1;
        let rarityColIdx = -1;

        $table.find('tr').first().find('th').each((idx, th) => {
            const text = $(th).text().trim().toLowerCase();
            if (text.includes('item') && itemColIdx === -1) itemColIdx = idx;
            if (text.includes('quantity') && quantityColIdx === -1) quantityColIdx = idx;
            if (text.includes('rarity') && rarityColIdx === -1) rarityColIdx = idx;
        });

        // If we couldn't find item column in first row, check for tables where first column
        // is an image and second column is the item name
        if (itemColIdx === -1) {
            // Common pattern: first th is blank or "Item" with image, item name is in .item-col
            const firstRow = $table.find('tr').first();
            firstRow.find('th').each((idx, th) => {
                const text = $(th).text().trim().toLowerCase();
                if (text === '' || text === 'item') {
                    // Check if next column is also item-related
                    const nextTh = firstRow.find('th').eq(idx + 1);
                    if (nextTh.length && nextTh.text().trim().toLowerCase().includes('item')) {
                        itemColIdx = idx + 1;
                    } else if (text === '' && idx === 0) {
                        // Image column, actual item is likely in second column
                        itemColIdx = 1;
                    }
                }
            });

            // Fallback: assume standard layout (image, item, quantity, rarity, price, alch)
            if (itemColIdx === -1) {
                itemColIdx = 1;
                quantityColIdx = 2;
                rarityColIdx = 3;
            }
        }

        const drops: DropTableEntry[] = [];

        // Parse each data row (skip header row)
        $table.find('tr').slice(1).each((_, row) => {
            const $row = $(row);
            const cells = $row.find('td');

            if (cells.length < 3) return; // Skip rows without enough columns

            // Extract item name - look for .item-col class first, then fall back to column index
            let itemName = '';
            const itemCell = $row.find('.item-col');
            if (itemCell.length) {
                // Get text from link if present, otherwise direct text
                const link = itemCell.find('a').first();
                itemName = link.length ? link.text().trim() : itemCell.text().trim();
            } else if (itemColIdx >= 0 && cells.eq(itemColIdx).length) {
                const cell = cells.eq(itemColIdx);
                const link = cell.find('a').first();
                itemName = link.length ? link.text().trim() : cell.text().trim();
            }

            // If no item name from item-col, try to find any anchor in the row as fallback
            if (!itemName) {
                const anyLink = $row.find('td a[href^="/w/"]').first();
                if (anyLink.length) {
                    itemName = anyLink.attr('title') || anyLink.text().trim();
                }
            }

            // Extract quantity
            let quantity = '';
            if (quantityColIdx >= 0 && cells.eq(quantityColIdx).length) {
                quantity = cells.eq(quantityColIdx).text().trim();
            } else {
                // Try to find by data-sort-value or just use the cell after item
                const qtyCell = cells.eq(itemColIdx + 1);
                if (qtyCell.length) {
                    quantity = qtyCell.text().trim();
                }
            }

            // Extract rarity
            let rarity = '';
            if (rarityColIdx >= 0 && cells.eq(rarityColIdx).length) {
                rarity = cells.eq(rarityColIdx).text().trim();
            } else {
                // Try cell after quantity
                const rarityCell = cells.eq(itemColIdx + 2);
                if (rarityCell.length) {
                    rarity = rarityCell.text().trim();
                }
            }

            // Clean up the values
            itemName = itemName.replace(/\s+/g, ' ').trim();
            quantity = quantity.replace(/\s+/g, ' ').trim();
            rarity = rarity.replace(/\s+/g, ' ').trim();

            // Skip if we don't have essential data
            if (!itemName || itemName === 'Nothing' || itemName === 'N/A') return;
            if (!rarity) return;

            const entry: DropTableEntry = {
                item: itemName,
                quantity: quantity || '1',
                rarity: rarity
            };

            // Try to convert rarity to percentage
            const percent = rarityToPercent(rarity);
            if (percent) {
                entry.rarityPercent = percent;
            }

            drops.push(entry);
        });

        // Only add section if we found drops
        if (drops.length > 0) {
            // Check if we already have this category
            const existingSection = dropSections.find(s => s.category === currentCategory);
            if (existingSection) {
                existingSection.drops.push(...drops);
            } else {
                dropSections.push({
                    category: currentCategory,
                    drops: drops
                });
            }
        }
    });

    return dropSections;
}

/**
 * Clean HTML and convert to markdown
 */
function cleanAndConvertHtml(html: string): string {
    const $ = cheerio.load(html);

    // Remove unwanted elements
    $('.navbox, .mbox, .hatnote, .toc, .mw-editsection, .reference, ' +
      '.references, .external, .noprint, script, style, .infobox').remove();

    // Remove "See also", "References", "External links" sections
    $('h2, h3').each((_, el) => {
        const text = $(el).text().toLowerCase();
        if (text.includes('see also') || text.includes('references') ||
            text.includes('external links') || text.includes('navigation')) {
            $(el).nextUntil('h2').remove();
            $(el).remove();
        }
    });

    // Convert to markdown
    const turndown = new TurndownService({
        headingStyle: 'atx',
        codeBlockStyle: 'fenced'
    });

    // Get main content area
    const content = $('.mw-parser-output').html() || $.html();
    const markdown = turndown.turndown(content);

    // Clean up excessive whitespace
    return markdown.replace(/\n{3,}/g, '\n\n').trim();
}

/**
 * Result from truncating content
 */
interface TruncateResult {
    content: string;
    truncated: boolean;
    originalLength: number;
    truncatedAtSection?: string;
}

/**
 * Truncate content to a maximum length, preferring to cut at section boundaries
 * @param content The markdown content to truncate
 * @param maxLength Maximum length in characters
 * @returns Truncation result with metadata
 */
function truncateContent(content: string, maxLength: number): TruncateResult {
    const originalLength = content.length;

    // If content is under the limit, return unchanged
    if (originalLength <= maxLength) {
        return {
            content,
            truncated: false,
            originalLength
        };
    }

    // Reserve space for truncation message
    const truncationMsg = '\n\n---\n*[Content truncated. Use sections parameter to request specific sections, or increase max_content_length.]*';
    const targetLength = maxLength - truncationMsg.length;

    if (targetLength <= 0) {
        return {
            content: truncationMsg.trim(),
            truncated: true,
            originalLength
        };
    }

    // Try to find a good cut point
    const searchRegion = content.substring(0, targetLength + 500); // Look a bit ahead for better cut points

    // Priority 1: Cut at a markdown heading (## or ###)
    const headingMatches = [...searchRegion.matchAll(/\n#{2,3}\s+([^\n]+)/g)];
    let cutPoint = -1;
    let truncatedAtSection: string | undefined;

    // Find the last heading that starts before our target length
    for (const match of headingMatches) {
        if (match.index !== undefined && match.index <= targetLength) {
            cutPoint = match.index;
            truncatedAtSection = match[1].trim();
        }
    }

    // Priority 2: Cut at a paragraph break (double newline)
    if (cutPoint === -1) {
        const lastParaBreak = content.lastIndexOf('\n\n', targetLength);
        if (lastParaBreak > targetLength * 0.5) { // Only use if we keep at least 50%
            cutPoint = lastParaBreak;
        }
    }

    // Priority 3: Hard cut at target length
    if (cutPoint === -1) {
        cutPoint = targetLength;
    }

    const truncatedContent = content.substring(0, cutPoint).trim() + truncationMsg;

    return {
        content: truncatedContent,
        truncated: true,
        originalLength,
        truncatedAtSection
    };
}

/**
 * Extract specific sections from markdown content by title
 * @param content The full markdown content
 * @param sectionTitles Array of section titles to extract (case-insensitive partial match)
 * @returns Filtered markdown content containing only matched sections
 */
function extractSections(content: string, sectionTitles: string[]): string {
    if (!sectionTitles || sectionTitles.length === 0) {
        return content;
    }

    // Normalize section titles for matching
    const normalizedTitles = sectionTitles.map(t => t.toLowerCase().trim());

    // Split content into sections based on markdown headings
    // Match ## and ### level headings
    const sectionRegex = /^(#{2,3})\s+(.+)$/gm;
    const sections: { title: string; level: number; start: number; content: string }[] = [];

    let match;
    const matches: { title: string; level: number; start: number }[] = [];

    while ((match = sectionRegex.exec(content)) !== null) {
        matches.push({
            title: match[2].trim(),
            level: match[1].length,
            start: match.index
        });
    }

    // Extract content for each section
    for (let i = 0; i < matches.length; i++) {
        const current = matches[i];
        const nextStart = i < matches.length - 1 ? matches[i + 1].start : content.length;
        const sectionContent = content.substring(current.start, nextStart).trim();

        sections.push({
            ...current,
            content: sectionContent
        });
    }

    // Filter to matching sections
    const matchedSections = sections.filter(section => {
        const sectionTitleLower = section.title.toLowerCase();
        return normalizedTitles.some(t => sectionTitleLower.includes(t) || t.includes(sectionTitleLower));
    });

    if (matchedSections.length === 0) {
        return `*[No sections matching: ${sectionTitles.join(', ')}]*\n\nAvailable sections:\n${sections.map(s => `- ${s.title}`).join('\n')}`;
    }

    // Combine matched sections
    return matchedSections.map(s => s.content).join('\n\n');
}

// HTTP agents with keep-alive for connection reuse
const httpAgent = new http.Agent({ keepAlive: true, maxSockets: 10 });
const httpsAgent = new https.Agent({ keepAlive: true, maxSockets: 10 });

const osrsApiClient = axios.create({
    baseURL: 'https://oldschool.runescape.wiki/api.php',
    params: {
        format: 'json'
    },
    httpsAgent: httpsAgent,
    timeout: 15000
});

// Grand Exchange price API client
const geApiClient = axios.create({
    baseURL: 'https://prices.runescape.wiki/api/v1/osrs',
    headers: {
        'User-Agent': 'mcp-osrs/1.0 (https://github.com/jayarrowz/mcp-osrs)'
    },
    httpsAgent: httpsAgent,
    timeout: 15000
});

// GE cache with 5-minute TTL (prices update frequently)
const GE_CACHE_TTL = 5 * 60 * 1000;
let gePriceCache: { data: any; timestamp: number } | null = null;

/**
 * Get GE price data, using cache if valid
 */
async function getGEPrices(): Promise<any> {
    const now = Date.now();
    if (gePriceCache && (now - gePriceCache.timestamp) < GE_CACHE_TTL) {
        return gePriceCache.data;
    }

    const response = await geApiClient.get('/latest');
    gePriceCache = { data: response.data, timestamp: now };
    return response.data;
}

// Environment variable for optional startup refresh of sound IDs
const REFRESH_SOUNDIDS_ON_STARTUP = process.env.OSRS_REFRESH_SOUNDIDS === 'true';

/**
 * Represents a sound ID entry from the wiki
 */
interface SoundIdEntry {
    id: number;
    name: string;
}

/**
 * Result from updating sound IDs from wiki
 */
interface UpdateSoundIdsResult {
    success: boolean;
    entriesFound: number;
    entriesWritten?: number;
    idRange?: { min: number; max: number };
    dryRun: boolean;
    filePath?: string;
    error?: string;
}

/**
 * Parse sound ID tables from OSRS Wiki HTML
 * @param html Raw HTML from the wiki page
 * @returns Array of sound ID entries
 */
function parseSoundIdTables(html: string): SoundIdEntry[] {
    const $ = cheerio.load(html);
    const entries: SoundIdEntry[] = [];
    const seenIds = new Set<number>();

    // Find all wikitables on the page
    $('table.wikitable').each((_, table) => {
        const $table = $(table);

        // Get headers from the first row
        const headers: string[] = [];
        $table.find('tr').first().find('th').each((_, th) => {
            headers.push($(th).text().trim().toLowerCase());
        });

        // Must have 'id' and 'sound' columns
        const idColIdx = headers.findIndex(h => h === 'id');
        const soundColIdx = headers.findIndex(h => h === 'sound');

        if (idColIdx === -1 || soundColIdx === -1) {
            return; // Skip non-sound-ID tables
        }

        // Parse each data row
        $table.find('tr').slice(1).each((_, row) => {
            const cells = $(row).find('td');
            if (cells.length < 2) return;

            // Extract ID
            const idText = cells.eq(idColIdx).text().trim();
            const id = parseInt(idText, 10);
            if (isNaN(id)) return;

            // Skip duplicates
            if (seenIds.has(id)) return;

            // Extract sound name
            let soundName = cells.eq(soundColIdx).text().trim();

            // Clean up sound name (normalize whitespace to underscores)
            soundName = soundName.replace(/\s+/g, '_');

            if (!soundName) return;

            seenIds.add(id);
            entries.push({ id, name: soundName });
        });
    });

    // Sort by ID for consistent file output
    entries.sort((a, b) => a.id - b.id);

    return entries;
}

/**
 * Fetch and parse OSRS Wiki sound IDs, optionally write to file
 * @param dryRun If true, parse only without writing
 * @returns Update result statistics
 */
async function updateSoundIdsFromWiki(dryRun: boolean = false): Promise<UpdateSoundIdsResult> {
    const wikiPageTitle = 'List_of_sound_IDs';

    // Fetch the wiki page HTML
    const response = await osrsApiClient.get('', {
        params: {
            action: 'parse',
            page: wikiPageTitle,
            prop: 'text',
            formatversion: 2
        }
    });

    const html = response.data?.parse?.text;
    if (!html) {
        throw new Error('Failed to fetch wiki page content');
    }

    // Parse the tables
    const entries = parseSoundIdTables(html);

    if (entries.length === 0) {
        throw new Error('No sound ID entries found in wiki page');
    }

    // Validate we have enough entries (prevents partial data from overwriting good data)
    if (entries.length < 1000) {
        throw new Error(
            `Only ${entries.length} entries found, expected 10,000+. ` +
            `Wiki page structure may have changed.`
        );
    }

    const result: UpdateSoundIdsResult = {
        success: true,
        entriesFound: entries.length,
        idRange: {
            min: entries[0].id,
            max: entries[entries.length - 1].id
        },
        dryRun
    };

    if (!dryRun) {
        // Build file content
        const fileContent = entries
            .map(entry => `${entry.id}\t${entry.name}`)
            .join('\n');

        // Write to file
        const filePath = path.join(DATA_DIR, 'soundids.txt');
        fs.writeFileSync(filePath, fileContent, 'utf8');

        // Invalidate caches
        fileCache.delete(filePath);
        idIndexCache.delete(filePath);

        result.entriesWritten = entries.length;
        result.filePath = filePath;
    }

    return result;
}

/**
 * Convert decimal rarity to human-readable fraction string
 * @param rarity Decimal rarity (e.g., 0.003333)
 * @returns Fraction string (e.g., "1/300") or "Always" for 1.0
 */
function rarityToFraction(rarity: number): string {
    if (rarity >= 1) return 'Always';
    if (rarity <= 0) return 'Never';

    // Calculate denominator
    const denominator = Math.round(1 / rarity);
    return `1/${denominator.toLocaleString()}`;
}

/**
 * Build indexes from raw monster data
 */
function buildOsrsBoxIndexes(monsters: OsrsBoxMonster[]): OsrsBoxCache {
    const monsterMap = new Map<number, OsrsBoxMonster>();
    const nameIndex = new Map<string, number[]>();
    const itemDropIndex = new Map<number, ItemSourceEntry[]>();

    for (const monster of monsters) {
        // Add to ID map
        monsterMap.set(monster.id, monster);

        // Add to name index (lowercase for case-insensitive search)
        const nameLower = monster.name.toLowerCase();
        const existing = nameIndex.get(nameLower) || [];
        existing.push(monster.id);
        nameIndex.set(nameLower, existing);

        // Build inverted item drop index
        if (monster.drops) {
            for (const drop of monster.drops) {
                const sources = itemDropIndex.get(drop.id) || [];
                sources.push({
                    monsterId: monster.id,
                    monsterName: monster.name,
                    combatLevel: monster.combat_level,
                    rarity: drop.rarity,
                    quantity: drop.quantity,
                    noted: drop.noted
                });
                itemDropIndex.set(drop.id, sources);
            }
        }
    }

    return {
        monsters: monsterMap,
        monsterNameIndex: nameIndex,
        itemDropIndex: itemDropIndex,
        timestamp: Date.now()
    };
}

/**
 * Fetch osrsreboxed-db data from GitHub
 * @param saveToDisk Whether to save data to disk cache
 * @returns Update result with statistics
 */
async function fetchOsrsBoxData(saveToDisk: boolean = true): Promise<{
    success: boolean;
    monsterCount: number;
    totalDrops: number;
    uniqueItems: number;
    dryRun: boolean;
    filePath?: string;
    error?: string;
}> {
    const response = await axios.get(OSRSBOX_GITHUB_URL);
    const rawData = response.data;

    // The data is an object with monster IDs as keys
    const monsters: OsrsBoxMonster[] = Object.values(rawData);

    if (monsters.length === 0) {
        throw new Error('No monsters found in osrsreboxed-db data');
    }

    // Validate minimum expected count
    if (monsters.length < 1000) {
        throw new Error(
            `Only ${monsters.length} monsters found, expected 2800+. ` +
            `Data structure may have changed.`
        );
    }

    // Count total drops and unique items
    let totalDrops = 0;
    const uniqueItemIds = new Set<number>();

    for (const monster of monsters) {
        if (monster.drops) {
            totalDrops += monster.drops.length;
            for (const drop of monster.drops) {
                uniqueItemIds.add(drop.id);
            }
        }
    }

    const result = {
        success: true,
        monsterCount: monsters.length,
        totalDrops,
        uniqueItems: uniqueItemIds.size,
        dryRun: !saveToDisk
    };

    if (saveToDisk) {
        const filePath = path.join(DATA_DIR, OSRSBOX_CACHE_FILE);
        fs.writeFileSync(filePath, JSON.stringify(rawData), 'utf8');
        (result as any).filePath = filePath;

        // Rebuild in-memory cache
        osrsBoxCache = buildOsrsBoxIndexes(monsters);
    }

    return result;
}

/**
 * Load osrsreboxed-db data from disk cache
 * @returns Whether data was loaded successfully
 */
function loadOsrsBoxFromDisk(): boolean {
    const filePath = path.join(DATA_DIR, OSRSBOX_CACHE_FILE);

    if (!fs.existsSync(filePath)) {
        return false;
    }

    try {
        const stats = fs.statSync(filePath);
        const age = Date.now() - stats.mtimeMs;

        // Check if cache is expired
        if (age > OSRSBOX_CACHE_TTL) {
            return false;
        }

        const content = fs.readFileSync(filePath, 'utf8');
        const rawData = JSON.parse(content);
        const monsters: OsrsBoxMonster[] = Object.values(rawData);

        osrsBoxCache = buildOsrsBoxIndexes(monsters);
        return true;
    } catch (error) {
        console.error('[mcp-osrs] Failed to load osrsbox cache from disk:', error);
        return false;
    }
}

/**
 * Get osrsreboxed-db cache, loading from disk or fetching from GitHub if needed
 * @param forceRefresh Force a refresh from GitHub
 * @returns The cache object or null if unavailable
 */
async function getOsrsBoxCache(forceRefresh: boolean = false): Promise<OsrsBoxCache | null> {
    // Check if we have valid memory cache
    if (!forceRefresh && osrsBoxCache) {
        const age = Date.now() - osrsBoxCache.timestamp;
        if (age < OSRSBOX_CACHE_TTL) {
            return osrsBoxCache;
        }
    }

    // Try to load from disk cache
    if (!forceRefresh && loadOsrsBoxFromDisk()) {
        return osrsBoxCache;
    }

    // Fetch from GitHub
    try {
        await fetchOsrsBoxData(true);
        return osrsBoxCache;
    } catch (error) {
        console.error('[mcp-osrs] Failed to fetch osrsbox data:', error);
        return null;
    }
}

const OsrsWikiSearchSchema = z.object({
    search: z.string().describe("The term to search for on the OSRS Wiki"),
    limit: z.number().int().min(1).max(50).optional().describe("Number of results to return (1-50)"),
    offset: z.number().int().min(0).optional().describe("Offset for pagination (0-based)")
});

const OsrsWikiGetPageInfoSchema = z.object({
    titles: z.string().describe("Comma-separated list of page titles to get info for (e.g., Dragon_scimitar,Abyssal_whip)")
});

const OsrsWikiParsePageSchema = z.object({
    page: z.string().describe("The exact title of the wiki page to parse (e.g., 'Dragon scimitar', 'Abyssal whip'). Case-sensitive."),
    max_content_length: z.number().int().min(1000).max(100000).optional().default(25000)
        .describe("Maximum length of markdown content in characters (1000-100000, default 25000). Content exceeding this limit will be truncated."),
    sections: z.array(z.string()).optional()
        .describe("Filter to specific section titles only. Case-insensitive partial matching. Example: ['Strategy', 'Equipment'] to get only those sections.")
});

const FileSearchSchema = z.object({
    query: z.string().describe("The term to search for in the file"),
    page: z.number().int().min(1).optional().default(1).describe("Page number for pagination"),
    pageSize: z.number().int().min(1).max(100).optional().default(10).describe("Number of results per page")
});

const GenericFileSearchSchema = z.object({
    filename: z.string().describe("The filename to search in the data directory (e.g., 'varptypes.txt')"),
    query: z.string().describe("The term to search for in the file"),
    page: z.number().int().min(1).optional().default(1).describe("Page number for pagination"),
    pageSize: z.number().int().min(1).max(100).optional().default(10).describe("Number of results per page")
});

const FileDetailsSchema = z.object({
    filename: z.string().describe("The filename to get details for in the data directory")
});

const ListDataFilesSchema = z.object({
    fileType: z.string().optional().describe("Optional filter for file type (e.g., 'txt')")
});

const GetByIdSchema = z.object({
    id: z.number().int().min(0).describe("The numeric ID to look up")
});

const UpdateSoundIdsSchema = z.object({
    dryRun: z.boolean().optional().default(false)
        .describe("If true, parse and return stats without writing to file")
});

// Phase 2 Schemas
const BulkLookupSchema = z.object({
    ids: z.array(z.number().int().min(0)).max(100)
        .describe("Array of IDs to look up (max 100)")
});

const ExactMatchSchema = z.object({
    name: z.string().describe("Exact name to match (case-insensitive)")
});

const GEPriceSchema = z.object({
    itemId: z.number().int().min(0).describe("Item ID to get price for")
});

const GEPriceBulkSchema = z.object({
    itemIds: z.array(z.number().int().min(0)).max(100)
        .describe("Array of item IDs to get prices for (max 100)")
});

// Phase 3 Schemas
const CacheStatsSchema = z.object({});

const HiscoresSchema = z.object({
    username: z.string().describe("Player username"),
    gameMode: z.enum(['normal', 'ironman', 'hardcore', 'ultimate'])
        .optional().default('normal')
        .describe("Game mode for hiscores lookup")
});

const RegexSearchSchema = z.object({
    pattern: z.string().describe("Regex pattern to match against entry names"),
    filename: z.string().describe("Data file to search (e.g., 'objtypes.txt')"),
    flags: z.string().optional().default("i").describe("Regex flags (default: 'i' for case-insensitive)"),
    page: z.number().int().min(1).optional().default(1).describe("Page number"),
    pageSize: z.number().int().min(1).max(100).optional().default(10).describe("Results per page")
});

// Hiscores skill names in order
const HISCORE_SKILLS = [
    'Overall', 'Attack', 'Defence', 'Strength', 'Hitpoints', 'Ranged',
    'Prayer', 'Magic', 'Cooking', 'Woodcutting', 'Fletching', 'Fishing',
    'Firemaking', 'Crafting', 'Smithing', 'Mining', 'Herblore', 'Agility',
    'Thieving', 'Slayer', 'Farming', 'Runecraft', 'Hunter', 'Construction'
];

// Phase 4 Schemas
const RangeQuerySchema = z.object({
    filename: z.string().describe("Data file to query (e.g., 'objtypes.txt')"),
    startId: z.number().int().min(0).describe("Starting ID (inclusive)"),
    endId: z.number().int().min(0).describe("Ending ID (inclusive)"),
    limit: z.number().int().min(1).max(1000).optional().default(100)
        .describe("Maximum results to return (default 100, max 1000)")
});

const WikiImagesSchema = z.object({
    page: z.string().describe("The exact title of the wiki page (e.g., 'Abyssal whip', 'Zulrah')")
});

// Drop Table Tool Schemas
const WikiGetDropsSchema = z.object({
    pages: z.union([
        z.string(),
        z.array(z.string())
    ]).describe("Page title(s) to get drops from. Can be a single page name or array of names."),
    include_categories: z.boolean().optional().default(true)
        .describe("Include category names in output (default: true)")
});

const UpdateOsrsBoxSchema = z.object({
    dryRun: z.boolean().optional().default(false)
        .describe("If true, fetch and return stats without writing to disk")
});

const MonsterDropsSchema = z.object({
    monster_id: z.number().int().min(0).describe("Monster ID to get drops for"),
    include_ge_prices: z.boolean().optional().default(false)
        .describe("Include current GE prices for dropped items")
});

const MonsterDropsByNameSchema = z.object({
    monster_name: z.string().describe("Monster name to search for (case-insensitive)"),
    include_ge_prices: z.boolean().optional().default(false)
        .describe("Include current GE prices for dropped items"),
    page: z.number().int().min(1).optional().default(1)
        .describe("Page number for pagination"),
    pageSize: z.number().int().min(1).max(50).optional().default(10)
        .describe("Number of monsters per page (max 50)")
});

const ItemSourcesSchema = z.object({
    item_id: z.number().int().min(0).optional()
        .describe("Item ID to find sources for"),
    item_name: z.string().optional()
        .describe("Item name to find sources for (partial match, case-insensitive)"),
    min_rarity: z.number().min(0).max(1).optional()
        .describe("Minimum rarity threshold (0.0-1.0, e.g., 0.01 = 1%)"),
    limit: z.number().int().min(1).max(500).optional().default(50)
        .describe("Maximum results to return (default 50, max 500)")
}).refine(data => data.item_id !== undefined || data.item_name !== undefined, {
    message: "Either item_id or item_name must be provided"
});

function convertZodToJsonSchema(schema: z.ZodType<any>) {
  const jsonSchema = zodToJsonSchema(schema);
  delete jsonSchema.$schema;
  delete jsonSchema.definitions;
  return {
    ...jsonSchema
  };
}

const server = new Server(
    {
        name: "mcp-osrs",
        version: "0.1.0" 
    },
    {
        capabilities: {
            tools: {}
        }
    }
);

/**
 * Search through a file for matching lines (uses caching for performance)
 * @param filePath Path to the file to search
 * @param searchTerm Term to search for
 * @param page Page number for pagination
 * @param pageSize Number of results per page
 * @returns Object containing results and pagination info
 */
function searchFile(filePath: string, searchTerm: string, page: number = 1, pageSize: number = 10): any {
    // Replace spaces with underscores
    searchTerm = searchTerm.replaceAll(" ", "_");

    // Use cached file lines
    const lines = getCachedFileLines(filePath);
    const searchTermLower = searchTerm.toLowerCase();

    const results: {line: string, lineNumber: number}[] = [];

    for (let i = 0; i < lines.length; i++) {
        const line = lines[i];
        if (line.toLowerCase().includes(searchTermLower)) {
            results.push({ line, lineNumber: i + 1 }); // lineNumber is 1-based
        }
    }

    const totalResults = results.length;
    const totalPages = Math.ceil(totalResults / pageSize);
    const startIndex = (page - 1) * pageSize;
    const endIndex = startIndex + pageSize;
    const paginatedResults = results.slice(startIndex, endIndex);

    // Process the results to extract key-value pairs if possible
    const formattedResults = paginatedResults.map(result => {
        // Try to format as key-value pair (common for ID data files)
        const parts = result.line.split(/\s+/);
        if (parts.length >= 2) {
            const id = parts[0];
            const value = parts.slice(1).join(' ');
            return {
                ...result,
                id,
                value,
                formatted: `${id}\t${value}`
            };
        }
        return result;
    });

    return {
        results: formattedResults,
        pagination: {
            page,
            pageSize,
            totalResults,
            totalPages,
            hasNextPage: page < totalPages,
            hasPreviousPage: page > 1
        }
    };
}

/**
 * Find an entry by exact name match (case-insensitive)
 * @param filePath Path to the file to search
 * @param name Exact name to match
 * @returns Object with the entry or null if not found
 */
function findByExactName(filePath: string, name: string): any {
    const lines = getCachedFileLines(filePath);
    const searchName = name.toLowerCase().replace(/ /g, '_');

    for (let i = 0; i < lines.length; i++) {
        const line = lines[i];
        if (!line.trim()) continue;

        const parts = line.split(/\t/);
        if (parts.length >= 2) {
            const entryName = parts[1].toLowerCase();
            if (entryName === searchName) {
                return {
                    id: parseInt(parts[0], 10),
                    name: parts[1],
                    lineNumber: i + 1,
                    raw: line
                };
            }
        }
    }
    return null;
}

/**
 * Search file using regex pattern matching
 * @param filePath Path to the file to search
 * @param pattern Regex pattern to match
 * @param flags Regex flags
 * @param page Page number for pagination
 * @param pageSize Results per page
 * @returns Search results with pagination
 */
function searchFileRegex(filePath: string, pattern: string, flags: string, page: number, pageSize: number): any {
    const lines = getCachedFileLines(filePath);

    let regex: RegExp;
    try {
        regex = new RegExp(pattern, flags);
    } catch (e) {
        throw new Error(`Invalid regex pattern: ${pattern}`);
    }

    const results: { line: string; lineNumber: number }[] = [];

    for (let i = 0; i < lines.length; i++) {
        const line = lines[i];
        if (regex.test(line)) {
            results.push({ line, lineNumber: i + 1 });
        }
    }

    const totalResults = results.length;
    const totalPages = Math.ceil(totalResults / pageSize);
    const startIndex = (page - 1) * pageSize;
    const paginatedResults = results.slice(startIndex, startIndex + pageSize);

    const formattedResults = paginatedResults.map(result => {
        const parts = result.line.split(/\t/);
        if (parts.length >= 2) {
            return {
                ...result,
                id: parseInt(parts[0], 10),
                name: parts[1]
            };
        }
        return result;
    });

    return {
        pattern,
        results: formattedResults,
        pagination: { page, pageSize, totalResults, totalPages }
    };
}

/**
 * Extract image URLs from wiki HTML
 * @param html The HTML content of the wiki page
 * @returns Object containing image URLs (detail, inventory, chathead)
 */
function extractWikiImages(html: string): Record<string, string> {
    const $ = cheerio.load(html);
    const images: Record<string, string> = {};

    // Find infobox image (usually the main item/NPC image)
    const infoboxImage = $('.infobox-image img, .infobox img').first();
    if (infoboxImage.length) {
        const src = infoboxImage.attr('src');
        if (src) {
            images.detail = src.startsWith('//') ? `https:${src}` : src;
        }
    }

    // Find inventory image (items have this)
    const invImage = $('img[alt*="inventory" i], img[src*="inventory" i]').first();
    if (invImage.length) {
        const src = invImage.attr('src');
        if (src) {
            images.inventory = src.startsWith('//') ? `https:${src}` : src;
        }
    }

    // Find chathead image (NPCs have this)
    const chatheadImage = $('img[alt*="chathead" i], img[src*="chathead" i]').first();
    if (chatheadImage.length) {
        const src = chatheadImage.attr('src');
        if (src) {
            images.chathead = src.startsWith('//') ? `https:${src}` : src;
        }
    }

    return images;
}

/**
 * Check if a file exists in the data directory
 * @param filename The filename to check
 * @returns Boolean indicating if the file exists
 */
function fileExists(filename: string): boolean {
    const filePath = path.join(DATA_DIR, filename);
    return fs.existsSync(filePath);
}

/**
 * Get data file details
 * @param filename The filename to get details for
 * @returns Object with file details
 */
function getFileDetails(filename: string): any {
    try {
        const filePath = path.join(DATA_DIR, filename);
        if (!fs.existsSync(filePath)) {
            return { exists: false };
        }

        const stats = fs.statSync(filePath);
        const lineCount = getFileLineCount(filePath);

        return {
            exists: true,
            size: stats.size,
            lineCount,
            created: stats.birthtime,
            lastModified: stats.mtime
        };
    } catch (error) {
        console.error(`Error getting file details for ${filename}:`, error);
        return { exists: false, error: 'Error getting file details' };
    }
}

/**
 * Get the number of lines in a file (uses caching for performance)
 * @param filePath Path to the file
 * @returns Number of lines in the file
 */
function getFileLineCount(filePath: string): number {
    try {
        const lines = getCachedFileLines(filePath);
        return lines.length;
    } catch (error) {
        console.error(`Error counting lines in ${filePath}:`, error);
        return 0;
    }
}

/**
 * List all data files in the data directory
 * @param fileType Optional filter for file type
 * @returns Array of file names
 */
function listDataFiles(fileType?: string): string[] {
    try {
        const files = fs.readdirSync(DATA_DIR);

        if (fileType) {
            return files.filter(file => file.endsWith(`.${fileType}`));
        }

        return files;
    } catch (error) {
        console.error("Error listing data files:", error);
        return [];
    }
}

/**
 * Get an entry by its numeric ID from a data file (uses caching for performance)
 * @param filePath Path to the file to search
 * @param id The numeric ID to look up
 * @returns Object with the entry or null if not found
 */
function getEntryById(filePath: string, id: number): any {
    // Build or get cached ID index for O(1) lookups
    const idIndex = buildIdIndex(filePath);
    const lineIndex = idIndex.get(id);

    if (lineIndex === undefined) {
        return null;
    }

    // Get the line from cached file content
    const lines = getCachedFileLines(filePath);
    const line = lines[lineIndex];

    if (!line) {
        return null;
    }

    // Parse the line
    const parts = line.split(/\t/);
    const name = parts.length >= 2 ? parts.slice(1).join('\t') : '';

    return {
        id: id,
        name: name,
        lineNumber: lineIndex + 1, // Convert 0-based index to 1-based line number
        raw: line
    };
}

server.setRequestHandler(ListToolsRequestSchema, async () => {
    return {
        tools: [
            {
                name: "osrs_wiki_search",
                description: "Search the OSRS Wiki for pages matching a search term.",
                inputSchema: convertZodToJsonSchema(OsrsWikiSearchSchema),
            },
            {
                name: "osrs_wiki_get_page_info",
                description: "Get information about specific pages on the OSRS Wiki.",
                inputSchema: convertZodToJsonSchema(OsrsWikiGetPageInfoSchema),
            },
            {
                name: "osrs_wiki_parse_page",
                description: "Get parsed content of an OSRS Wiki page. Returns structured JSON with infobox data (stats, combat info), drop tables with item/quantity/rarity, table of contents, and content as markdown. Content is truncated to max_content_length (default 25000 chars) to prevent oversized responses. Use 'sections' parameter to filter to specific sections only (e.g., ['Strategy', 'Equipment']). Response includes 'contentMeta' with truncation info.",
                inputSchema: convertZodToJsonSchema(OsrsWikiParsePageSchema),
            },
            {
                name: "search_varptypes",
                description: "Search the varptypes.txt file for player variables (varps) that store player state and progress.",
                inputSchema: convertZodToJsonSchema(FileSearchSchema),
            },
            {
                name: "search_varbittypes",
                description: "Search the varbittypes.txt file for variable bits (varbits) that store individual bits from varps.",
                inputSchema: convertZodToJsonSchema(FileSearchSchema),
            },
            {
                name: "search_iftypes",
                description: "Search the iftypes.txt file for interface definitions used in the game's UI.",
                inputSchema: convertZodToJsonSchema(FileSearchSchema),
            },
            {
                name: "search_invtypes",
                description: "Search the invtypes.txt file for inventory type definitions in the game.",
                inputSchema: convertZodToJsonSchema(FileSearchSchema),
            },
            {
                name: "search_loctypes",
                description: "Search the loctypes.txt file for location/object type definitions in the game world.",
                inputSchema: convertZodToJsonSchema(FileSearchSchema),
            },
            {
                name: "search_npctypes",
                description: "Search the npctypes.txt file for NPC (non-player character) definitions.",
                inputSchema: convertZodToJsonSchema(FileSearchSchema),
            },
            {
                name: "search_objtypes",
                description: "Search the objtypes.txt file for object/item definitions in the game.",
                inputSchema: convertZodToJsonSchema(FileSearchSchema),
            },
            {
                name: "search_rowtypes",
                description: "Search the rowtypes.txt file for row definitions used in various interfaces.",
                inputSchema: convertZodToJsonSchema(FileSearchSchema),
            },
            {
                name: "search_seqtypes",
                description: "Search the seqtypes.txt file for animation sequence definitions.",
                inputSchema: convertZodToJsonSchema(FileSearchSchema),
            },
            {
                name: "search_soundtypes",
                description: "Search the soundtypes.txt file for sound effect definitions in the game.",
                inputSchema: convertZodToJsonSchema(FileSearchSchema),
            },
            {
                name: "search_spottypes",
                description: "Search the spottypes.txt file for spot animation (graphical effect) definitions.",
                inputSchema: convertZodToJsonSchema(FileSearchSchema),
            },
            {
                name: "search_spritetypes",
                description: "Search the spritetypes.txt file for sprite image definitions used in the interface.",
                inputSchema: convertZodToJsonSchema(FileSearchSchema),
            },
            {
                name: "search_tabletypes",
                description: "Search the tabletypes.txt file for interface tab definitions.",
                inputSchema: convertZodToJsonSchema(FileSearchSchema),
            },
            {
                name: "search_data_file",
                description: "Search any file in the data directory for matching entries. Available files typically include: varptypes, varbittypes, iftypes, invtypes, loctypes, npctypes, objtypes, rowtypes, seqtypes, soundtypes, spottypes, spritetypes, tabletypes, soundids. Additional files like enumtypes, structtypes, paramtypes may also be available if added to the data directory.",
                inputSchema: convertZodToJsonSchema(GenericFileSearchSchema),
            },
            {
                name: "get_file_details",
                description: "Get details about a file in the data directory.",
                inputSchema: convertZodToJsonSchema(FileDetailsSchema),
            },
            {
                name: "list_data_files",
                description: "List available data files in the data directory.",
                inputSchema: convertZodToJsonSchema(ListDataFilesSchema),
            },
            {
                name: "get_npctype_by_id",
                description: "Get NPC definition by ID from npctypes.txt. Returns the NPC name and details for the given numeric ID.",
                inputSchema: convertZodToJsonSchema(GetByIdSchema),
            },
            {
                name: "get_objtype_by_id",
                description: "Get item/object definition by ID from objtypes.txt. Returns the item name and details for the given numeric ID.",
                inputSchema: convertZodToJsonSchema(GetByIdSchema),
            },
            {
                name: "get_seqtype_by_id",
                description: "Get animation sequence by ID from seqtypes.txt. Returns the animation name and details for the given numeric ID.",
                inputSchema: convertZodToJsonSchema(GetByIdSchema),
            },
            {
                name: "get_spottype_by_id",
                description: "Get spot animation (graphical effect) by ID from spottypes.txt. Returns the spotanim name and details for the given numeric ID.",
                inputSchema: convertZodToJsonSchema(GetByIdSchema),
            },
            {
                name: "get_loctype_by_id",
                description: "Get location/object definition by ID from loctypes.txt. Returns the location name and details for the given numeric ID.",
                inputSchema: convertZodToJsonSchema(GetByIdSchema),
            },
            {
                name: "search_soundids",
                description: "Search the soundids.txt file for sound effect IDs from the OSRS Wiki. Contains 10,000+ sound effect entries. Use update_soundids_from_wiki to download/update the data.",
                inputSchema: convertZodToJsonSchema(FileSearchSchema),
            },
            {
                name: "get_soundid_by_id",
                description: "Get sound effect by ID from soundids.txt. Returns the sound name for the given numeric ID.",
                inputSchema: convertZodToJsonSchema(GetByIdSchema),
            },
            {
                name: "update_soundids_from_wiki",
                description: "Update soundids.txt by fetching and parsing the OSRS Wiki 'List of sound IDs' page. Use dryRun=true to preview without writing. Downloads ~10,000 sound entries.",
                inputSchema: convertZodToJsonSchema(UpdateSoundIdsSchema),
            },
            {
                name: "get_varptype_by_id",
                description: "Get player variable definition by ID from varptypes.txt. Returns the varp name for the given numeric ID.",
                inputSchema: convertZodToJsonSchema(GetByIdSchema),
            },
            {
                name: "get_varbittype_by_id",
                description: "Get variable bit definition by ID from varbittypes.txt. Returns the varbit name for the given numeric ID.",
                inputSchema: convertZodToJsonSchema(GetByIdSchema),
            },
            {
                name: "get_iftype_by_id",
                description: "Get interface definition by ID from iftypes.txt. Returns the interface name for the given numeric ID.",
                inputSchema: convertZodToJsonSchema(GetByIdSchema),
            },
            {
                name: "get_invtype_by_id",
                description: "Get inventory type by ID from invtypes.txt. Returns the inventory name for the given numeric ID.",
                inputSchema: convertZodToJsonSchema(GetByIdSchema),
            },
            {
                name: "get_rowtype_by_id",
                description: "Get row definition by ID from rowtypes.txt. Returns the row name for the given numeric ID.",
                inputSchema: convertZodToJsonSchema(GetByIdSchema),
            },
            {
                name: "get_soundtype_by_id",
                description: "Get sound type by ID from soundtypes.txt. Returns the sound name for the given numeric ID.",
                inputSchema: convertZodToJsonSchema(GetByIdSchema),
            },
            {
                name: "get_spritetype_by_id",
                description: "Get sprite definition by ID from spritetypes.txt. Returns the sprite name for the given numeric ID.",
                inputSchema: convertZodToJsonSchema(GetByIdSchema),
            },
            {
                name: "get_tabletype_by_id",
                description: "Get table definition by ID from tabletypes.txt. Returns the table name for the given numeric ID.",
                inputSchema: convertZodToJsonSchema(GetByIdSchema),
            },
            // Phase 2: Bulk ID lookup tools
            {
                name: "get_npctypes_by_ids",
                description: "Get multiple NPC definitions by IDs from npctypes.txt. Returns results array and notFound array.",
                inputSchema: convertZodToJsonSchema(BulkLookupSchema),
            },
            {
                name: "get_objtypes_by_ids",
                description: "Get multiple item/object definitions by IDs from objtypes.txt. Returns results array and notFound array.",
                inputSchema: convertZodToJsonSchema(BulkLookupSchema),
            },
            {
                name: "get_seqtypes_by_ids",
                description: "Get multiple animation sequences by IDs from seqtypes.txt. Returns results array and notFound array.",
                inputSchema: convertZodToJsonSchema(BulkLookupSchema),
            },
            {
                name: "get_spottypes_by_ids",
                description: "Get multiple spot animations by IDs from spottypes.txt. Returns results array and notFound array.",
                inputSchema: convertZodToJsonSchema(BulkLookupSchema),
            },
            {
                name: "get_loctypes_by_ids",
                description: "Get multiple location definitions by IDs from loctypes.txt. Returns results array and notFound array.",
                inputSchema: convertZodToJsonSchema(BulkLookupSchema),
            },
            {
                name: "get_varptypes_by_ids",
                description: "Get multiple player variables by IDs from varptypes.txt. Returns results array and notFound array.",
                inputSchema: convertZodToJsonSchema(BulkLookupSchema),
            },
            {
                name: "get_varbittypes_by_ids",
                description: "Get multiple variable bits by IDs from varbittypes.txt. Returns results array and notFound array.",
                inputSchema: convertZodToJsonSchema(BulkLookupSchema),
            },
            {
                name: "get_iftypes_by_ids",
                description: "Get multiple interface definitions by IDs from iftypes.txt. Returns results array and notFound array.",
                inputSchema: convertZodToJsonSchema(BulkLookupSchema),
            },
            {
                name: "get_invtypes_by_ids",
                description: "Get multiple inventory types by IDs from invtypes.txt. Returns results array and notFound array.",
                inputSchema: convertZodToJsonSchema(BulkLookupSchema),
            },
            {
                name: "get_rowtypes_by_ids",
                description: "Get multiple row definitions by IDs from rowtypes.txt. Returns results array and notFound array.",
                inputSchema: convertZodToJsonSchema(BulkLookupSchema),
            },
            {
                name: "get_soundtypes_by_ids",
                description: "Get multiple sound types by IDs from soundtypes.txt. Returns results array and notFound array.",
                inputSchema: convertZodToJsonSchema(BulkLookupSchema),
            },
            {
                name: "get_spritetypes_by_ids",
                description: "Get multiple sprite definitions by IDs from spritetypes.txt. Returns results array and notFound array.",
                inputSchema: convertZodToJsonSchema(BulkLookupSchema),
            },
            {
                name: "get_tabletypes_by_ids",
                description: "Get multiple table definitions by IDs from tabletypes.txt. Returns results array and notFound array.",
                inputSchema: convertZodToJsonSchema(BulkLookupSchema),
            },
            {
                name: "get_soundids_by_ids",
                description: "Get multiple sound effects by IDs from soundids.txt. Returns results array and notFound array.",
                inputSchema: convertZodToJsonSchema(BulkLookupSchema),
            },
            // Phase 2: Exact match tools
            {
                name: "find_objtype_by_name",
                description: "Find an item/object by exact name (case-insensitive) from objtypes.txt. Spaces are converted to underscores.",
                inputSchema: convertZodToJsonSchema(ExactMatchSchema),
            },
            {
                name: "find_npctype_by_name",
                description: "Find an NPC by exact name (case-insensitive) from npctypes.txt. Spaces are converted to underscores.",
                inputSchema: convertZodToJsonSchema(ExactMatchSchema),
            },
            {
                name: "find_loctype_by_name",
                description: "Find a location/object by exact name (case-insensitive) from loctypes.txt. Spaces are converted to underscores.",
                inputSchema: convertZodToJsonSchema(ExactMatchSchema),
            },
            {
                name: "find_seqtype_by_name",
                description: "Find an animation sequence by exact name (case-insensitive) from seqtypes.txt. Spaces are converted to underscores.",
                inputSchema: convertZodToJsonSchema(ExactMatchSchema),
            },
            {
                name: "find_spottype_by_name",
                description: "Find a spot animation by exact name (case-insensitive) from spottypes.txt. Spaces are converted to underscores.",
                inputSchema: convertZodToJsonSchema(ExactMatchSchema),
            },
            {
                name: "find_varptype_by_name",
                description: "Find a player variable by exact name (case-insensitive) from varptypes.txt. Spaces are converted to underscores.",
                inputSchema: convertZodToJsonSchema(ExactMatchSchema),
            },
            {
                name: "find_varbittype_by_name",
                description: "Find a variable bit by exact name (case-insensitive) from varbittypes.txt. Spaces are converted to underscores.",
                inputSchema: convertZodToJsonSchema(ExactMatchSchema),
            },
            {
                name: "find_iftype_by_name",
                description: "Find an interface by exact name (case-insensitive) from iftypes.txt. Spaces are converted to underscores.",
                inputSchema: convertZodToJsonSchema(ExactMatchSchema),
            },
            {
                name: "find_invtype_by_name",
                description: "Find an inventory type by exact name (case-insensitive) from invtypes.txt. Spaces are converted to underscores.",
                inputSchema: convertZodToJsonSchema(ExactMatchSchema),
            },
            {
                name: "find_rowtype_by_name",
                description: "Find a row definition by exact name (case-insensitive) from rowtypes.txt. Spaces are converted to underscores.",
                inputSchema: convertZodToJsonSchema(ExactMatchSchema),
            },
            {
                name: "find_soundtype_by_name",
                description: "Find a sound type by exact name (case-insensitive) from soundtypes.txt. Spaces are converted to underscores.",
                inputSchema: convertZodToJsonSchema(ExactMatchSchema),
            },
            {
                name: "find_spritetype_by_name",
                description: "Find a sprite by exact name (case-insensitive) from spritetypes.txt. Spaces are converted to underscores.",
                inputSchema: convertZodToJsonSchema(ExactMatchSchema),
            },
            {
                name: "find_tabletype_by_name",
                description: "Find a table definition by exact name (case-insensitive) from tabletypes.txt. Spaces are converted to underscores.",
                inputSchema: convertZodToJsonSchema(ExactMatchSchema),
            },
            // Phase 2: GE price tools
            {
                name: "osrs_ge_price",
                description: "Get Grand Exchange price for an item by ID. Returns high/low prices and timestamps.",
                inputSchema: convertZodToJsonSchema(GEPriceSchema),
            },
            {
                name: "osrs_ge_prices",
                description: "Get Grand Exchange prices for multiple items by IDs. Returns results array and notFound array.",
                inputSchema: convertZodToJsonSchema(GEPriceBulkSchema),
            },
            // Phase 3: Polish tools
            {
                name: "get_cache_stats",
                description: "Get cache statistics for debugging and monitoring. Shows file cache and wiki cache hit rates.",
                inputSchema: convertZodToJsonSchema(CacheStatsSchema),
            },
            {
                name: "osrs_hiscores",
                description: "Look up a player's stats and rankings from the OSRS hiscores. Supports normal, ironman, hardcore, and ultimate game modes.",
                inputSchema: convertZodToJsonSchema(HiscoresSchema),
            },
            {
                name: "search_regex",
                description: "Search a data file using regex pattern matching. Useful for finding items matching patterns like 'dragon_.*_ornament'.",
                inputSchema: convertZodToJsonSchema(RegexSearchSchema),
            },
            // Phase 4 Tools
            {
                name: "get_id_range",
                description: "Get all entries within an ID range from a data file. Useful for exploring ID ranges to find related items/NPCs/objects.",
                inputSchema: convertZodToJsonSchema(RangeQuerySchema),
            },
            {
                name: "osrs_wiki_images",
                description: "Extract image URLs (detail, inventory sprite, chathead) from an OSRS Wiki page. Useful for getting item/NPC images.",
                inputSchema: convertZodToJsonSchema(WikiImagesSchema),
            },
            // Drop Table Tools
            {
                name: "osrs_wiki_get_drops",
                description: "Get ONLY drop tables from wiki pages. Lightweight alternative to osrs_wiki_parse_page when you only need drops. Supports multiple pages in one call.",
                inputSchema: convertZodToJsonSchema(WikiGetDropsSchema),
            },
            {
                name: "update_osrsbox_data",
                description: "Update local cache of osrsreboxed-db monster data from GitHub. Downloads ~50MB of structured drop data with numeric rarity values. Use dryRun=true to preview without saving.",
                inputSchema: convertZodToJsonSchema(UpdateOsrsBoxSchema),
            },
            {
                name: "osrs_get_monster_drops",
                description: "Get drops for a monster by ID from osrsreboxed-db. Returns structured data with numeric rarity values (decimal, e.g., 0.003333 = 1/300).",
                inputSchema: convertZodToJsonSchema(MonsterDropsSchema),
            },
            {
                name: "osrs_search_monster_drops",
                description: "Search for monsters by name and get their drops from osrsreboxed-db. Returns all monsters matching the name with their drops.",
                inputSchema: convertZodToJsonSchema(MonsterDropsByNameSchema),
            },
            {
                name: "osrs_get_item_sources",
                description: "Reverse drop lookup: find all monsters that drop a specific item. Specify item_id OR item_name. Returns sources sorted by rarity (best first).",
                inputSchema: convertZodToJsonSchema(ItemSourcesSchema),
            },
        ]
    };
});

server.setRequestHandler(CallToolRequestSchema, async (request) => {
    const { name, arguments: args } = request.params;

    try {
        switch (name) {
            case "osrs_wiki_search": {
                const { search, limit = 10, offset = 0 } = OsrsWikiSearchSchema.parse(args);
                const searchParams = {
                    action: 'query',
                    list: 'search',
                    srsearch: search,
                    srlimit: limit,
                    sroffset: offset,
                    srprop: 'snippet|titlesnippet|sectiontitle'
                };
                const searchCacheKey = getWikiCacheKey('wiki_search', searchParams);
                const cachedSearchData = getFromWikiCache(searchCacheKey);
                if (cachedSearchData) {
                    return responseToString(cachedSearchData);
                }
                const searchResponse = await fetchWithDedup(searchCacheKey, () =>
                    osrsApiClient.get('', { params: searchParams })
                );
                // Strip HTML tags from snippets
                if (searchResponse.data?.query?.search) {
                    searchResponse.data.query.search = searchResponse.data.query.search.map((result: any) => ({
                        ...result,
                        snippet: result.snippet?.replace(/<\/?span[^>]*>/g, '') || '',
                        titlesnippet: result.titlesnippet?.replace(/<\/?span[^>]*>/g, '') || ''
                    }));
                }
                setWikiCache(searchCacheKey, searchResponse.data);
                return responseToString(searchResponse.data);
            }

            case "osrs_wiki_get_page_info": {
                const { titles } = OsrsWikiGetPageInfoSchema.parse(args);
                const pageInfoParams = {
                    action: 'query',
                    prop: 'info',
                    titles: titles
                };
                const pageInfoCacheKey = getWikiCacheKey('wiki_page_info', pageInfoParams);
                const cachedPageInfoData = getFromWikiCache(pageInfoCacheKey);
                if (cachedPageInfoData) {
                    return responseToString(cachedPageInfoData);
                }
                const pageInfoResponse = await fetchWithDedup(pageInfoCacheKey, () =>
                    osrsApiClient.get('', { params: pageInfoParams })
                );
                setWikiCache(pageInfoCacheKey, pageInfoResponse.data);
                return responseToString(pageInfoResponse.data);
            }

            case "osrs_wiki_parse_page": {
                const { page, max_content_length, sections: requestedSections } = OsrsWikiParsePageSchema.parse(args);
                const parseParams = {
                    action: 'parse',
                    page: page,
                    prop: 'text|sections',
                    formatversion: 2
                };

                // Include new parameters in cache key for proper caching
                const cacheParams = {
                    ...parseParams,
                    max_content_length,
                    sections: requestedSections?.join(',') || ''
                };
                const parseCacheKey = getWikiCacheKey('wiki_parse_page', cacheParams);
                const cachedParseData = getFromWikiCache(parseCacheKey);
                if (cachedParseData) {
                    return responseToString(cachedParseData);
                }

                const parseResponse = await fetchWithDedup(parseCacheKey, () =>
                    osrsApiClient.get('', { params: parseParams })
                );

                const rawHtml = parseResponse.data?.parse?.text;
                if (!rawHtml) {
                    return responseToString({ error: 'Page content not found.' });
                }

                const infobox = extractInfobox(rawHtml);
                const dropTable = extractDropTable(rawHtml);
                let content = cleanAndConvertHtml(rawHtml);
                const sections = parseResponse.data?.parse?.sections?.map((s: any) => ({
                    level: s.level,
                    title: s.line,
                    anchor: s.anchor
                })) || [];

                // Apply section filtering if requested
                if (requestedSections && requestedSections.length > 0) {
                    content = extractSections(content, requestedSections);
                }

                // Apply content truncation
                const truncateResult = truncateContent(content, max_content_length);

                const parseResult: Record<string, any> = {
                    page: page,
                    infobox: infobox,
                    dropTable: dropTable.length > 0 ? dropTable : null,
                    sections: sections,
                    content: truncateResult.content,
                    contentMeta: {
                        originalLength: truncateResult.originalLength,
                        truncated: truncateResult.truncated,
                        ...(truncateResult.truncatedAtSection && { truncatedAtSection: truncateResult.truncatedAtSection }),
                        ...(requestedSections && requestedSections.length > 0 && { filteredSections: requestedSections })
                    }
                };
                setWikiCache(parseCacheKey, parseResult);
                return responseToString(parseResult);
            }

            case "search_varptypes":
            case "search_varbittypes":
            case "search_iftypes":
            case "search_invtypes":
            case "search_loctypes":
            case "search_npctypes":
            case "search_objtypes":
            case "search_rowtypes":
            case "search_seqtypes":
            case "search_soundtypes":
            case "search_spottypes":
            case "search_spritetypes":
            case "search_tabletypes":
                const { query, page: filePage = 1, pageSize: filePageSize = 10 } = FileSearchSchema.parse(args);
                const filename = `${name.replace('search_', '')}.txt`;
                const filePath = path.join(DATA_DIR, filename);
                
                if (!fileExists(filename)) {
                    return responseToString({ error: `${filename} not found in data directory` });
                }
                
                const fileResults = await searchFile(filePath, query, filePage, filePageSize);
                return responseToString(fileResults);

            case "search_data_file":
                const { filename: genericFilename, query: searchQuery, page: genericFilePage = 1, pageSize: genericFilePageSize = 10 } = GenericFileSearchSchema.parse(args);
                
                // Security check to prevent directory traversal
                if (genericFilename.includes('..') || genericFilename.includes('/') || genericFilename.includes('\\')) {
                    throw new Error('Invalid filename');
                }
                
                if (!fileExists(genericFilename)) {
                    return responseToString({ error: `${genericFilename} not found in data directory` });
                }
                
                const genericFilePath = path.join(DATA_DIR, genericFilename);
                const genericFileResults = await searchFile(genericFilePath, searchQuery, genericFilePage, genericFilePageSize);
                return responseToString(genericFileResults);

            case "get_file_details":
                const { filename: detailsFilename } = FileDetailsSchema.parse(args);
                
                // Security check to prevent directory traversal
                if (detailsFilename.includes('..') || detailsFilename.includes('/') || detailsFilename.includes('\\')) {
                    throw new Error('Invalid filename');
                }
                
                const details = getFileDetails(detailsFilename);
                return responseToString(details);

            case "list_data_files":
                const { fileType } = ListDataFilesSchema.parse(args);
                const files = listDataFiles(fileType);
                return responseToString({ files, path: DATA_DIR });

            case "get_npctype_by_id": {
                const { id } = GetByIdSchema.parse(args);
                const npcFilePath = path.join(DATA_DIR, 'npctypes.txt');
                if (!fileExists('npctypes.txt')) {
                    return responseToString({ error: 'npctypes.txt not found in data directory' });
                }
                const npcEntry = await getEntryById(npcFilePath, id);
                if (npcEntry === null) {
                    return responseToString({ error: `NPC with ID ${id} not found` });
                }
                return responseToString(npcEntry);
            }

            case "get_objtype_by_id": {
                const { id } = GetByIdSchema.parse(args);
                const objFilePath = path.join(DATA_DIR, 'objtypes.txt');
                if (!fileExists('objtypes.txt')) {
                    return responseToString({ error: 'objtypes.txt not found in data directory' });
                }
                const objEntry = await getEntryById(objFilePath, id);
                if (objEntry === null) {
                    return responseToString({ error: `Object/Item with ID ${id} not found` });
                }
                return responseToString(objEntry);
            }

            case "get_seqtype_by_id": {
                const { id } = GetByIdSchema.parse(args);
                const seqFilePath = path.join(DATA_DIR, 'seqtypes.txt');
                if (!fileExists('seqtypes.txt')) {
                    return responseToString({ error: 'seqtypes.txt not found in data directory' });
                }
                const seqEntry = await getEntryById(seqFilePath, id);
                if (seqEntry === null) {
                    return responseToString({ error: `Animation sequence with ID ${id} not found` });
                }
                return responseToString(seqEntry);
            }

            case "get_spottype_by_id": {
                const { id } = GetByIdSchema.parse(args);
                const spotFilePath = path.join(DATA_DIR, 'spottypes.txt');
                if (!fileExists('spottypes.txt')) {
                    return responseToString({ error: 'spottypes.txt not found in data directory' });
                }
                const spotEntry = await getEntryById(spotFilePath, id);
                if (spotEntry === null) {
                    return responseToString({ error: `Spot animation with ID ${id} not found` });
                }
                return responseToString(spotEntry);
            }

            case "get_loctype_by_id": {
                const { id } = GetByIdSchema.parse(args);
                const locFilePath = path.join(DATA_DIR, 'loctypes.txt');
                if (!fileExists('loctypes.txt')) {
                    return responseToString({ error: 'loctypes.txt not found in data directory' });
                }
                const locEntry = await getEntryById(locFilePath, id);
                if (locEntry === null) {
                    return responseToString({ error: `Location with ID ${id} not found` });
                }
                return responseToString(locEntry);
            }

            case "search_soundids": {
                const { query, page: soundPage = 1, pageSize: soundPageSize = 10 } = FileSearchSchema.parse(args);
                const soundIdsFilePath = path.join(DATA_DIR, 'soundids.txt');
                if (!fileExists('soundids.txt')) {
                    return responseToString({
                        error: 'soundids.txt not found in data directory. Use update_soundids_from_wiki to download.'
                    });
                }
                const soundResults = searchFile(soundIdsFilePath, query, soundPage, soundPageSize);
                return responseToString(soundResults);
            }

            case "get_soundid_by_id": {
                const { id } = GetByIdSchema.parse(args);
                const soundIdFilePath = path.join(DATA_DIR, 'soundids.txt');
                if (!fileExists('soundids.txt')) {
                    return responseToString({
                        error: 'soundids.txt not found in data directory. Use update_soundids_from_wiki to download.'
                    });
                }
                const soundEntry = getEntryById(soundIdFilePath, id);
                if (soundEntry === null) {
                    return responseToString({ error: `Sound ID ${id} not found` });
                }
                return responseToString(soundEntry);
            }

            case "update_soundids_from_wiki": {
                const { dryRun = false } = UpdateSoundIdsSchema.parse(args);
                try {
                    const result = await updateSoundIdsFromWiki(dryRun);
                    return responseToString(result);
                } catch (error) {
                    const err = error as Error;
                    return responseToString({
                        error: `Failed to update sound IDs: ${err.message}`
                    });
                }
            }

            case "get_varptype_by_id": {
                const { id } = GetByIdSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'varptypes.txt');
                if (!fileExists('varptypes.txt')) {
                    return responseToString({ error: 'varptypes.txt not found in data directory' });
                }
                const entry = getEntryById(filePath, id);
                if (entry === null) {
                    return responseToString({ error: `Varp with ID ${id} not found` });
                }
                return responseToString(entry);
            }

            case "get_varbittype_by_id": {
                const { id } = GetByIdSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'varbittypes.txt');
                if (!fileExists('varbittypes.txt')) {
                    return responseToString({ error: 'varbittypes.txt not found in data directory' });
                }
                const entry = getEntryById(filePath, id);
                if (entry === null) {
                    return responseToString({ error: `Varbit with ID ${id} not found` });
                }
                return responseToString(entry);
            }

            case "get_iftype_by_id": {
                const { id } = GetByIdSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'iftypes.txt');
                if (!fileExists('iftypes.txt')) {
                    return responseToString({ error: 'iftypes.txt not found in data directory' });
                }
                const entry = getEntryById(filePath, id);
                if (entry === null) {
                    return responseToString({ error: `Interface with ID ${id} not found` });
                }
                return responseToString(entry);
            }

            case "get_invtype_by_id": {
                const { id } = GetByIdSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'invtypes.txt');
                if (!fileExists('invtypes.txt')) {
                    return responseToString({ error: 'invtypes.txt not found in data directory' });
                }
                const entry = getEntryById(filePath, id);
                if (entry === null) {
                    return responseToString({ error: `Inventory with ID ${id} not found` });
                }
                return responseToString(entry);
            }

            case "get_rowtype_by_id": {
                const { id } = GetByIdSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'rowtypes.txt');
                if (!fileExists('rowtypes.txt')) {
                    return responseToString({ error: 'rowtypes.txt not found in data directory' });
                }
                const entry = getEntryById(filePath, id);
                if (entry === null) {
                    return responseToString({ error: `Row with ID ${id} not found` });
                }
                return responseToString(entry);
            }

            case "get_soundtype_by_id": {
                const { id } = GetByIdSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'soundtypes.txt');
                if (!fileExists('soundtypes.txt')) {
                    return responseToString({ error: 'soundtypes.txt not found in data directory' });
                }
                const entry = getEntryById(filePath, id);
                if (entry === null) {
                    return responseToString({ error: `Sound type with ID ${id} not found` });
                }
                return responseToString(entry);
            }

            case "get_spritetype_by_id": {
                const { id } = GetByIdSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'spritetypes.txt');
                if (!fileExists('spritetypes.txt')) {
                    return responseToString({ error: 'spritetypes.txt not found in data directory' });
                }
                const entry = getEntryById(filePath, id);
                if (entry === null) {
                    return responseToString({ error: `Sprite with ID ${id} not found` });
                }
                return responseToString(entry);
            }

            case "get_tabletype_by_id": {
                const { id } = GetByIdSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'tabletypes.txt');
                if (!fileExists('tabletypes.txt')) {
                    return responseToString({ error: 'tabletypes.txt not found in data directory' });
                }
                const entry = getEntryById(filePath, id);
                if (entry === null) {
                    return responseToString({ error: `Table with ID ${id} not found` });
                }
                return responseToString(entry);
            }

            // Phase 2: Bulk ID lookup handlers
            case "get_npctypes_by_ids": {
                const { ids } = BulkLookupSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'npctypes.txt');
                if (!fileExists('npctypes.txt')) {
                    return responseToString({ error: 'npctypes.txt not found' });
                }
                const results: any[] = [];
                const notFound: number[] = [];
                for (const id of ids) {
                    const entry = getEntryById(filePath, id);
                    if (entry === null) {
                        notFound.push(id);
                    } else {
                        results.push(entry);
                    }
                }
                return responseToString({ results, notFound });
            }

            case "get_objtypes_by_ids": {
                const { ids } = BulkLookupSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'objtypes.txt');
                if (!fileExists('objtypes.txt')) {
                    return responseToString({ error: 'objtypes.txt not found' });
                }
                const results: any[] = [];
                const notFound: number[] = [];
                for (const id of ids) {
                    const entry = getEntryById(filePath, id);
                    if (entry === null) {
                        notFound.push(id);
                    } else {
                        results.push(entry);
                    }
                }
                return responseToString({ results, notFound });
            }

            case "get_seqtypes_by_ids": {
                const { ids } = BulkLookupSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'seqtypes.txt');
                if (!fileExists('seqtypes.txt')) {
                    return responseToString({ error: 'seqtypes.txt not found' });
                }
                const results: any[] = [];
                const notFound: number[] = [];
                for (const id of ids) {
                    const entry = getEntryById(filePath, id);
                    if (entry === null) {
                        notFound.push(id);
                    } else {
                        results.push(entry);
                    }
                }
                return responseToString({ results, notFound });
            }

            case "get_spottypes_by_ids": {
                const { ids } = BulkLookupSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'spottypes.txt');
                if (!fileExists('spottypes.txt')) {
                    return responseToString({ error: 'spottypes.txt not found' });
                }
                const results: any[] = [];
                const notFound: number[] = [];
                for (const id of ids) {
                    const entry = getEntryById(filePath, id);
                    if (entry === null) {
                        notFound.push(id);
                    } else {
                        results.push(entry);
                    }
                }
                return responseToString({ results, notFound });
            }

            case "get_loctypes_by_ids": {
                const { ids } = BulkLookupSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'loctypes.txt');
                if (!fileExists('loctypes.txt')) {
                    return responseToString({ error: 'loctypes.txt not found' });
                }
                const results: any[] = [];
                const notFound: number[] = [];
                for (const id of ids) {
                    const entry = getEntryById(filePath, id);
                    if (entry === null) {
                        notFound.push(id);
                    } else {
                        results.push(entry);
                    }
                }
                return responseToString({ results, notFound });
            }

            case "get_varptypes_by_ids": {
                const { ids } = BulkLookupSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'varptypes.txt');
                if (!fileExists('varptypes.txt')) {
                    return responseToString({ error: 'varptypes.txt not found' });
                }
                const results: any[] = [];
                const notFound: number[] = [];
                for (const id of ids) {
                    const entry = getEntryById(filePath, id);
                    if (entry === null) {
                        notFound.push(id);
                    } else {
                        results.push(entry);
                    }
                }
                return responseToString({ results, notFound });
            }

            case "get_varbittypes_by_ids": {
                const { ids } = BulkLookupSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'varbittypes.txt');
                if (!fileExists('varbittypes.txt')) {
                    return responseToString({ error: 'varbittypes.txt not found' });
                }
                const results: any[] = [];
                const notFound: number[] = [];
                for (const id of ids) {
                    const entry = getEntryById(filePath, id);
                    if (entry === null) {
                        notFound.push(id);
                    } else {
                        results.push(entry);
                    }
                }
                return responseToString({ results, notFound });
            }

            case "get_iftypes_by_ids": {
                const { ids } = BulkLookupSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'iftypes.txt');
                if (!fileExists('iftypes.txt')) {
                    return responseToString({ error: 'iftypes.txt not found' });
                }
                const results: any[] = [];
                const notFound: number[] = [];
                for (const id of ids) {
                    const entry = getEntryById(filePath, id);
                    if (entry === null) {
                        notFound.push(id);
                    } else {
                        results.push(entry);
                    }
                }
                return responseToString({ results, notFound });
            }

            case "get_invtypes_by_ids": {
                const { ids } = BulkLookupSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'invtypes.txt');
                if (!fileExists('invtypes.txt')) {
                    return responseToString({ error: 'invtypes.txt not found' });
                }
                const results: any[] = [];
                const notFound: number[] = [];
                for (const id of ids) {
                    const entry = getEntryById(filePath, id);
                    if (entry === null) {
                        notFound.push(id);
                    } else {
                        results.push(entry);
                    }
                }
                return responseToString({ results, notFound });
            }

            case "get_rowtypes_by_ids": {
                const { ids } = BulkLookupSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'rowtypes.txt');
                if (!fileExists('rowtypes.txt')) {
                    return responseToString({ error: 'rowtypes.txt not found' });
                }
                const results: any[] = [];
                const notFound: number[] = [];
                for (const id of ids) {
                    const entry = getEntryById(filePath, id);
                    if (entry === null) {
                        notFound.push(id);
                    } else {
                        results.push(entry);
                    }
                }
                return responseToString({ results, notFound });
            }

            case "get_soundtypes_by_ids": {
                const { ids } = BulkLookupSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'soundtypes.txt');
                if (!fileExists('soundtypes.txt')) {
                    return responseToString({ error: 'soundtypes.txt not found' });
                }
                const results: any[] = [];
                const notFound: number[] = [];
                for (const id of ids) {
                    const entry = getEntryById(filePath, id);
                    if (entry === null) {
                        notFound.push(id);
                    } else {
                        results.push(entry);
                    }
                }
                return responseToString({ results, notFound });
            }

            case "get_spritetypes_by_ids": {
                const { ids } = BulkLookupSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'spritetypes.txt');
                if (!fileExists('spritetypes.txt')) {
                    return responseToString({ error: 'spritetypes.txt not found' });
                }
                const results: any[] = [];
                const notFound: number[] = [];
                for (const id of ids) {
                    const entry = getEntryById(filePath, id);
                    if (entry === null) {
                        notFound.push(id);
                    } else {
                        results.push(entry);
                    }
                }
                return responseToString({ results, notFound });
            }

            case "get_tabletypes_by_ids": {
                const { ids } = BulkLookupSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'tabletypes.txt');
                if (!fileExists('tabletypes.txt')) {
                    return responseToString({ error: 'tabletypes.txt not found' });
                }
                const results: any[] = [];
                const notFound: number[] = [];
                for (const id of ids) {
                    const entry = getEntryById(filePath, id);
                    if (entry === null) {
                        notFound.push(id);
                    } else {
                        results.push(entry);
                    }
                }
                return responseToString({ results, notFound });
            }

            case "get_soundids_by_ids": {
                const { ids } = BulkLookupSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'soundids.txt');
                if (!fileExists('soundids.txt')) {
                    return responseToString({ error: 'soundids.txt not found. Use update_soundids_from_wiki to download.' });
                }
                const results: any[] = [];
                const notFound: number[] = [];
                for (const id of ids) {
                    const entry = getEntryById(filePath, id);
                    if (entry === null) {
                        notFound.push(id);
                    } else {
                        results.push(entry);
                    }
                }
                return responseToString({ results, notFound });
            }

            // Phase 2: Exact match handlers
            case "find_objtype_by_name": {
                const { name: searchName } = ExactMatchSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'objtypes.txt');
                if (!fileExists('objtypes.txt')) {
                    return responseToString({ error: 'objtypes.txt not found' });
                }
                const entry = findByExactName(filePath, searchName);
                if (entry === null) {
                    return responseToString({ error: `Object with name "${searchName}" not found` });
                }
                return responseToString(entry);
            }

            case "find_npctype_by_name": {
                const { name: searchName } = ExactMatchSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'npctypes.txt');
                if (!fileExists('npctypes.txt')) {
                    return responseToString({ error: 'npctypes.txt not found' });
                }
                const entry = findByExactName(filePath, searchName);
                if (entry === null) {
                    return responseToString({ error: `NPC with name "${searchName}" not found` });
                }
                return responseToString(entry);
            }

            case "find_loctype_by_name": {
                const { name: searchName } = ExactMatchSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'loctypes.txt');
                if (!fileExists('loctypes.txt')) {
                    return responseToString({ error: 'loctypes.txt not found' });
                }
                const entry = findByExactName(filePath, searchName);
                if (entry === null) {
                    return responseToString({ error: `Location with name "${searchName}" not found` });
                }
                return responseToString(entry);
            }

            case "find_seqtype_by_name": {
                const { name: searchName } = ExactMatchSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'seqtypes.txt');
                if (!fileExists('seqtypes.txt')) {
                    return responseToString({ error: 'seqtypes.txt not found' });
                }
                const entry = findByExactName(filePath, searchName);
                if (entry === null) {
                    return responseToString({ error: `Animation sequence with name "${searchName}" not found` });
                }
                return responseToString(entry);
            }

            case "find_spottype_by_name": {
                const { name: searchName } = ExactMatchSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'spottypes.txt');
                if (!fileExists('spottypes.txt')) {
                    return responseToString({ error: 'spottypes.txt not found' });
                }
                const entry = findByExactName(filePath, searchName);
                if (entry === null) {
                    return responseToString({ error: `Spot animation with name "${searchName}" not found` });
                }
                return responseToString(entry);
            }

            case "find_varptype_by_name": {
                const { name: searchName } = ExactMatchSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'varptypes.txt');
                if (!fileExists('varptypes.txt')) {
                    return responseToString({ error: 'varptypes.txt not found' });
                }
                const entry = findByExactName(filePath, searchName);
                if (entry === null) {
                    return responseToString({ error: `Player variable with name "${searchName}" not found` });
                }
                return responseToString(entry);
            }

            case "find_varbittype_by_name": {
                const { name: searchName } = ExactMatchSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'varbittypes.txt');
                if (!fileExists('varbittypes.txt')) {
                    return responseToString({ error: 'varbittypes.txt not found' });
                }
                const entry = findByExactName(filePath, searchName);
                if (entry === null) {
                    return responseToString({ error: `Variable bit with name "${searchName}" not found` });
                }
                return responseToString(entry);
            }

            case "find_iftype_by_name": {
                const { name: searchName } = ExactMatchSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'iftypes.txt');
                if (!fileExists('iftypes.txt')) {
                    return responseToString({ error: 'iftypes.txt not found' });
                }
                const entry = findByExactName(filePath, searchName);
                if (entry === null) {
                    return responseToString({ error: `Interface with name "${searchName}" not found` });
                }
                return responseToString(entry);
            }

            case "find_invtype_by_name": {
                const { name: searchName } = ExactMatchSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'invtypes.txt');
                if (!fileExists('invtypes.txt')) {
                    return responseToString({ error: 'invtypes.txt not found' });
                }
                const entry = findByExactName(filePath, searchName);
                if (entry === null) {
                    return responseToString({ error: `Inventory type with name "${searchName}" not found` });
                }
                return responseToString(entry);
            }

            case "find_rowtype_by_name": {
                const { name: searchName } = ExactMatchSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'rowtypes.txt');
                if (!fileExists('rowtypes.txt')) {
                    return responseToString({ error: 'rowtypes.txt not found' });
                }
                const entry = findByExactName(filePath, searchName);
                if (entry === null) {
                    return responseToString({ error: `Row definition with name "${searchName}" not found` });
                }
                return responseToString(entry);
            }

            case "find_soundtype_by_name": {
                const { name: searchName } = ExactMatchSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'soundtypes.txt');
                if (!fileExists('soundtypes.txt')) {
                    return responseToString({ error: 'soundtypes.txt not found' });
                }
                const entry = findByExactName(filePath, searchName);
                if (entry === null) {
                    return responseToString({ error: `Sound type with name "${searchName}" not found` });
                }
                return responseToString(entry);
            }

            case "find_spritetype_by_name": {
                const { name: searchName } = ExactMatchSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'spritetypes.txt');
                if (!fileExists('spritetypes.txt')) {
                    return responseToString({ error: 'spritetypes.txt not found' });
                }
                const entry = findByExactName(filePath, searchName);
                if (entry === null) {
                    return responseToString({ error: `Sprite with name "${searchName}" not found` });
                }
                return responseToString(entry);
            }

            case "find_tabletype_by_name": {
                const { name: searchName } = ExactMatchSchema.parse(args);
                const filePath = path.join(DATA_DIR, 'tabletypes.txt');
                if (!fileExists('tabletypes.txt')) {
                    return responseToString({ error: 'tabletypes.txt not found' });
                }
                const entry = findByExactName(filePath, searchName);
                if (entry === null) {
                    return responseToString({ error: `Table definition with name "${searchName}" not found` });
                }
                return responseToString(entry);
            }

            // Phase 2: GE price handlers
            case "osrs_ge_price": {
                const { itemId } = GEPriceSchema.parse(args);
                const priceData = await getGEPrices();
                const itemPrice = priceData.data?.[itemId.toString()];
                if (!itemPrice) {
                    return responseToString({ error: `No GE price data for item ID ${itemId}` });
                }
                return responseToString({
                    itemId,
                    high: itemPrice.high,
                    highTime: itemPrice.highTime,
                    low: itemPrice.low,
                    lowTime: itemPrice.lowTime
                });
            }

            case "osrs_ge_prices": {
                const { itemIds } = GEPriceBulkSchema.parse(args);
                const priceData = await getGEPrices();
                const results: any[] = [];
                const notFound: number[] = [];
                for (const itemId of itemIds) {
                    const itemPrice = priceData.data?.[itemId.toString()];
                    if (itemPrice) {
                        results.push({
                            itemId,
                            high: itemPrice.high,
                            highTime: itemPrice.highTime,
                            low: itemPrice.low,
                            lowTime: itemPrice.lowTime
                        });
                    } else {
                        notFound.push(itemId);
                    }
                }
                return responseToString({ results, notFound });
            }

            // Phase 3: Polish tool handlers
            case "get_cache_stats": {
                const totalFileRequests = fileCacheHits + fileCacheMisses;
                const totalWikiRequests = wikiCacheHits + wikiCacheMisses;

                return responseToString({
                    fileCache: {
                        entries: fileCache.size,
                        hits: fileCacheHits,
                        misses: fileCacheMisses,
                        hitRate: totalFileRequests > 0
                            ? `${((fileCacheHits / totalFileRequests) * 100).toFixed(1)}%`
                            : "N/A",
                        ttlMinutes: CACHE_TTL / 60000
                    },
                    wikiCache: {
                        entries: wikiCache.size,
                        hits: wikiCacheHits,
                        misses: wikiCacheMisses,
                        hitRate: totalWikiRequests > 0
                            ? `${((wikiCacheHits / totalWikiRequests) * 100).toFixed(1)}%`
                            : "N/A",
                        maxSize: WIKI_CACHE_MAX_SIZE,
                        ttlMinutes: WIKI_CACHE_TTL / 60000
                    },
                    geCache: {
                        cached: gePriceCache !== null,
                        ttlMinutes: GE_CACHE_TTL / 60000
                    }
                });
            }

            case "osrs_hiscores": {
                const { username, gameMode = 'normal' } = HiscoresSchema.parse(args);

                const gameModeUrls: Record<string, string> = {
                    'normal': 'hiscore_oldschool',
                    'ironman': 'hiscore_oldschool_ironman',
                    'hardcore': 'hiscore_oldschool_hardcore_ironman',
                    'ultimate': 'hiscore_oldschool_ultimate'
                };

                const url = `https://secure.runescape.com/m=${gameModeUrls[gameMode]}/index_lite.json?player=${encodeURIComponent(username)}`;

                try {
                    const response = await axios.get(url);
                    const data = response.data;

                    // Parse skills from response
                    const skills: Record<string, { rank: number; level: number; xp: number }> = {};
                    if (data.skills) {
                        for (let i = 0; i < HISCORE_SKILLS.length && i < data.skills.length; i++) {
                            const skill = data.skills[i];
                            skills[HISCORE_SKILLS[i]] = {
                                rank: skill.rank,
                                level: skill.level,
                                xp: skill.xp
                            };
                        }
                    }

                    return responseToString({
                        username,
                        gameMode,
                        skills
                    });
                } catch (error) {
                    const err = error as any;
                    if (err.response?.status === 404) {
                        return responseToString({ error: `Player "${username}" not found on ${gameMode} hiscores` });
                    }
                    throw error;
                }
            }

            case "search_regex": {
                const { pattern, filename, flags = 'i', page = 1, pageSize = 10 } = RegexSearchSchema.parse(args);

                // Security check
                if (filename.includes('..') || filename.includes('/') || filename.includes('\\')) {
                    throw new Error('Invalid filename');
                }

                if (!fileExists(filename)) {
                    return responseToString({ error: `${filename} not found in data directory` });
                }

                const filePath = path.join(DATA_DIR, filename);
                const results = searchFileRegex(filePath, pattern, flags, page, pageSize);
                return responseToString(results);
            }

            // Phase 4 Handlers
            case "get_id_range": {
                const { filename, startId, endId, limit = 100 } = RangeQuerySchema.parse(args);

                // Security check
                if (filename.includes('..') || filename.includes('/') || filename.includes('\\')) {
                    throw new Error('Invalid filename');
                }

                if (!fileExists(filename)) {
                    return responseToString({ error: `${filename} not found in data directory` });
                }

                if (startId > endId) {
                    return responseToString({ error: 'startId must be <= endId' });
                }

                const filePath = path.join(DATA_DIR, filename);
                const idIndex = buildIdIndex(filePath);
                const lines = getCachedFileLines(filePath);
                const results: any[] = [];

                for (let id = startId; id <= endId && results.length < limit; id++) {
                    const lineIndex = idIndex.get(id);
                    if (lineIndex !== undefined) {
                        const line = lines[lineIndex];
                        const parts = line.split(/\t/);
                        results.push({
                            id,
                            name: parts.length >= 2 ? parts[1] : '',
                            lineNumber: lineIndex + 1
                        });
                    }
                }

                return responseToString({
                    filename,
                    startId,
                    endId,
                    limit,
                    count: results.length,
                    results
                });
            }

            case "osrs_wiki_images": {
                const { page } = WikiImagesSchema.parse(args);
                const parseParams = {
                    action: 'parse',
                    page: page,
                    prop: 'text',
                    formatversion: 2
                };

                const cacheKey = getWikiCacheKey('wiki_images', { page });
                const cached = getFromWikiCache(cacheKey);
                if (cached) {
                    return responseToString(cached);
                }

                const response = await fetchWithDedup(cacheKey, () =>
                    osrsApiClient.get('', { params: parseParams })
                );
                const html = response.data?.parse?.text;

                if (!html) {
                    return responseToString({ error: 'Page not found or has no content' });
                }

                const images = extractWikiImages(html);
                const result = { page, images };

                setWikiCache(cacheKey, result);
                return responseToString(result);
            }

            // Drop Table Tool Handlers
            case "osrs_wiki_get_drops": {
                const { pages, include_categories = true } = WikiGetDropsSchema.parse(args);
                const pageList = Array.isArray(pages) ? pages : [pages];
                const results: Record<string, any> = {};

                for (const pageName of pageList) {
                    // Check cache first
                    const cacheKey = getWikiCacheKey('wiki_drops', { page: pageName });
                    const cached = getFromWikiCache(cacheKey);

                    if (cached) {
                        results[pageName] = cached;
                        continue;
                    }

                    // Fetch wiki page
                    const parseParams = {
                        action: 'parse',
                        page: pageName,
                        prop: 'text',
                        formatversion: 2
                    };

                    try {
                        const response = await fetchWithDedup(cacheKey, () =>
                            osrsApiClient.get('', { params: parseParams })
                        );
                        const html = response.data?.parse?.text;

                        if (!html) {
                            results[pageName] = { error: 'Page not found' };
                            continue;
                        }

                        const dropTable = extractDropTable(html);

                        // Format output based on include_categories
                        let pageResult;
                        if (include_categories) {
                            pageResult = dropTable;
                        } else {
                            // Flatten all drops without categories
                            const allDrops = dropTable.flatMap(section => section.drops);
                            pageResult = allDrops;
                        }

                        setWikiCache(cacheKey, pageResult);
                        results[pageName] = pageResult;
                    } catch (error) {
                        const err = error as Error;
                        results[pageName] = { error: err.message };
                    }
                }

                // If single page was requested, return just that result
                if (pageList.length === 1) {
                    return responseToString(results[pageList[0]]);
                }
                return responseToString(results);
            }

            case "update_osrsbox_data": {
                const { dryRun = false } = UpdateOsrsBoxSchema.parse(args);
                try {
                    const result = await fetchOsrsBoxData(!dryRun);
                    return responseToString(result);
                } catch (error) {
                    const err = error as Error;
                    return responseToString({
                        error: `Failed to update osrsbox data: ${err.message}`
                    });
                }
            }

            case "osrs_get_monster_drops": {
                const { monster_id, include_ge_prices = false } = MonsterDropsSchema.parse(args);

                const cache = await getOsrsBoxCache();
                if (!cache) {
                    return responseToString({
                        error: 'osrsreboxed-db data not available. Use update_osrsbox_data to download.'
                    });
                }

                const monster = cache.monsters.get(monster_id);
                if (!monster) {
                    return responseToString({ error: `Monster ID ${monster_id} not found` });
                }

                // Format drops with rarity strings
                const formattedDrops = monster.drops?.map(drop => ({
                    id: drop.id,
                    name: drop.name,
                    quantity: drop.quantity,
                    rarity: drop.rarity,
                    rarity_fraction: rarityToFraction(drop.rarity),
                    rarity_percent: `${(drop.rarity * 100).toFixed(4)}%`,
                    noted: drop.noted,
                    members: drop.members
                })) || [];

                let result: any = {
                    id: monster.id,
                    name: monster.name,
                    combat_level: monster.combat_level,
                    hitpoints: monster.hitpoints,
                    wiki_url: monster.wiki_url,
                    drops: formattedDrops
                };

                // Add GE prices if requested
                if (include_ge_prices && formattedDrops.length > 0) {
                    try {
                        const priceData = await getGEPrices();
                        result.drops = formattedDrops.map(drop => {
                            const itemPrice = priceData.data?.[drop.id.toString()];
                            return {
                                ...drop,
                                ge_price: itemPrice ? {
                                    high: itemPrice.high,
                                    low: itemPrice.low
                                } : null
                            };
                        });
                    } catch (error) {
                        // Continue without prices if GE API fails
                    }
                }

                return responseToString(result);
            }

            case "osrs_search_monster_drops": {
                const { monster_name, include_ge_prices = false, page = 1, pageSize = 10 } = MonsterDropsByNameSchema.parse(args);

                const cache = await getOsrsBoxCache();
                if (!cache) {
                    return responseToString({
                        error: 'osrsreboxed-db data not available. Use update_osrsbox_data to download.'
                    });
                }

                const searchLower = monster_name.toLowerCase();
                const matchingMonsters: OsrsBoxMonster[] = [];

                // Search through name index for partial matches
                for (const [name, ids] of cache.monsterNameIndex) {
                    if (name.includes(searchLower)) {
                        for (const id of ids) {
                            const monster = cache.monsters.get(id);
                            if (monster) {
                                matchingMonsters.push(monster);
                            }
                        }
                    }
                }

                if (matchingMonsters.length === 0) {
                    return responseToString({ error: `No monsters found matching "${monster_name}"` });
                }

                // Pagination
                const totalResults = matchingMonsters.length;
                const totalPages = Math.ceil(totalResults / pageSize);
                const startIndex = (page - 1) * pageSize;
                const paginatedMonsters = matchingMonsters.slice(startIndex, startIndex + pageSize);

                // Format results
                const results = paginatedMonsters.map(monster => {
                    const formattedDrops = monster.drops?.map(drop => ({
                        id: drop.id,
                        name: drop.name,
                        quantity: drop.quantity,
                        rarity: drop.rarity,
                        rarity_fraction: rarityToFraction(drop.rarity),
                        rarity_percent: `${(drop.rarity * 100).toFixed(4)}%`,
                        noted: drop.noted
                    })) || [];

                    return {
                        id: monster.id,
                        name: monster.name,
                        combat_level: monster.combat_level,
                        hitpoints: monster.hitpoints,
                        wiki_url: monster.wiki_url,
                        drop_count: formattedDrops.length,
                        drops: formattedDrops
                    };
                });

                // Add GE prices if requested
                if (include_ge_prices) {
                    try {
                        const priceData = await getGEPrices();
                        for (const result of results) {
                            result.drops = result.drops.map((drop: any) => {
                                const itemPrice = priceData.data?.[drop.id.toString()];
                                return {
                                    ...drop,
                                    ge_price: itemPrice ? {
                                        high: itemPrice.high,
                                        low: itemPrice.low
                                    } : null
                                };
                            });
                        }
                    } catch (error) {
                        // Continue without prices
                    }
                }

                return responseToString({
                    query: monster_name,
                    totalResults,
                    pagination: {
                        page,
                        pageSize,
                        totalPages,
                        hasNextPage: page < totalPages,
                        hasPreviousPage: page > 1
                    },
                    monsters: results
                });
            }

            case "osrs_get_item_sources": {
                const { item_id, item_name, min_rarity, limit = 50 } = ItemSourcesSchema.parse(args);

                const cache = await getOsrsBoxCache();
                if (!cache) {
                    return responseToString({
                        error: 'osrsreboxed-db data not available. Use update_osrsbox_data to download.'
                    });
                }

                let sources: ItemSourceEntry[] = [];
                let matchedItemId: number | null = null;
                let matchedItemName: string | null = null;

                if (item_id !== undefined) {
                    // Direct ID lookup (O(1))
                    sources = cache.itemDropIndex.get(item_id) || [];
                    matchedItemId = item_id;

                    // Try to get item name from objtypes
                    const objFilePath = path.join(DATA_DIR, 'objtypes.txt');
                    if (fileExists('objtypes.txt')) {
                        const entry = getEntryById(objFilePath, item_id);
                        if (entry) {
                            matchedItemName = entry.name;
                        }
                    }
                } else if (item_name) {
                    // Search by name - find matching item IDs first
                    const searchLower = item_name.toLowerCase();
                    const matchedItems: { id: number; name: string }[] = [];

                    // Search through all item drop entries
                    for (const [itemId, itemSources] of cache.itemDropIndex) {
                        if (itemSources.length > 0) {
                            // Get item name from first source's drop list
                            const monster = cache.monsters.get(itemSources[0].monsterId);
                            if (monster?.drops) {
                                const drop = monster.drops.find(d => d.id === itemId);
                                if (drop && drop.name.toLowerCase().includes(searchLower)) {
                                    matchedItems.push({ id: itemId, name: drop.name });
                                }
                            }
                        }
                    }

                    if (matchedItems.length === 0) {
                        return responseToString({ error: `No items found matching "${item_name}"` });
                    }

                    // If multiple items match, show them
                    if (matchedItems.length > 1) {
                        return responseToString({
                            message: `Multiple items match "${item_name}". Use item_id for specific item.`,
                            matches: matchedItems.slice(0, 20)
                        });
                    }

                    // Single match
                    matchedItemId = matchedItems[0].id;
                    matchedItemName = matchedItems[0].name;
                    sources = cache.itemDropIndex.get(matchedItemId) || [];
                }

                // Apply rarity filter
                if (min_rarity !== undefined) {
                    sources = sources.filter(s => s.rarity >= min_rarity);
                }

                // Sort by rarity (best/highest first)
                sources.sort((a, b) => b.rarity - a.rarity);

                // Apply limit
                sources = sources.slice(0, limit);

                // Format output
                const formattedSources = sources.map(source => ({
                    monster_id: source.monsterId,
                    monster_name: source.monsterName,
                    combat_level: source.combatLevel,
                    quantity: source.quantity,
                    noted: source.noted,
                    rarity: source.rarity,
                    rarity_fraction: rarityToFraction(source.rarity),
                    rarity_percent: `${(source.rarity * 100).toFixed(4)}%`
                }));

                return responseToString({
                    item_id: matchedItemId,
                    item_name: matchedItemName,
                    source_count: formattedSources.length,
                    sources: formattedSources
                });
            }

            default:
                throw new Error(`Unknown tool: ${name}`);
        }

    } catch (error) {
        if (error instanceof z.ZodError) {
            throw new Error(
                `Invalid arguments: ${error.errors
                    .map((e) => `${e.path.join(".")}: ${e.message}`)
                    .join(", ")}`
            );
        }

        const err = error as any;
        if (axios.isAxiosError(err)) {
             console.error("Axios Error Details:", {
                message: err.message,
                url: err.config?.url,
                method: err.config?.method,
                params: err.config?.params,
                data: err.config?.data,
                responseStatus: err.response?.status,
                responseData: err.response?.data,
                stack: err.stack
            });
             throw new Error(`Error executing tool ${name}: ${err.message}${err.response?.data ? ` - Wiki Response: ${JSON.stringify(err.response.data)}` : ''}`);
        } else {
            console.error("Error details:", {
                message: err.message,
                stack: err.stack,
                name: err.name,
                fullError: JSON.stringify(err, Object.getOwnPropertyNames(err), 2)
            });
            throw new Error(`Error executing tool ${name}: ${err.message}`);
        }
    }
});

// Files to pre-warm on startup (most commonly used)
const PREWARM_FILES = ['objtypes.txt', 'npctypes.txt', 'loctypes.txt', 'seqtypes.txt'];

async function prewarmFileCache(): Promise<void> {
    console.error('[mcp-osrs] Pre-warming file caches...');
    let loaded = 0;

    for (const filename of PREWARM_FILES) {
        const filePath = path.join(DATA_DIR, filename);
        try {
            if (fs.existsSync(filePath)) {
                getCachedFileLines(filePath);
                buildIdIndex(filePath);
                loaded++;
            }
        } catch (error) {
            // Non-fatal: continue with other files
        }
    }

    console.error(`[mcp-osrs] Pre-warmed ${loaded} file caches`);
}

async function main() {
    try {
        // Pre-warm file caches for commonly used data files
        await prewarmFileCache();

        // Optional startup refresh of sound IDs from wiki
        if (REFRESH_SOUNDIDS_ON_STARTUP) {
            try {
                console.error('[mcp-osrs] Refreshing sound IDs from wiki...');
                const result = await updateSoundIdsFromWiki(false);
                console.error(`[mcp-osrs] Sound IDs updated: ${result.entriesWritten} entries`);
            } catch (error) {
                const err = error as Error;
                console.error(`[mcp-osrs] Failed to refresh sound IDs: ${err.message}`);
                // Non-fatal: continue startup even if refresh fails
            }
        }

        // Optional startup refresh of osrsreboxed-db data
        if (REFRESH_OSRSBOX_ON_STARTUP) {
            try {
                console.error('[mcp-osrs] Refreshing osrsreboxed-db from GitHub...');
                const result = await fetchOsrsBoxData(true);
                console.error(`[mcp-osrs] osrsreboxed-db updated: ${result.monsterCount} monsters, ${result.totalDrops} drops`);
            } catch (error) {
                const err = error as Error;
                console.error(`[mcp-osrs] Failed to refresh osrsreboxed-db: ${err.message}`);
                // Non-fatal: continue startup even if refresh fails
            }
        }

        const transport = new StdioServerTransport();
        await server.connect(transport);
    } catch (error) {
        console.error("Error during startup:", error);
        process.exit(1);
    }
}

main().catch((error) => {
    console.error("Fatal error in main():", error);
    process.exit(1);
});

// Export for testing
export { searchFile, rarityToPercent, extractDropTable, getEntryById, findByExactName, getCachedFileLines };

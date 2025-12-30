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
        return cached.lines;
    }

    // Read file and cache it
    if (!fs.existsSync(filePath)) {
        throw new Error(`File not found: ${filePath}`);
    }

    const content = fs.readFileSync(filePath, 'utf8');
    const lines = content.split('\n');

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
    if (!cached) return null;

    const now = Date.now();
    if (now - cached.timestamp > WIKI_CACHE_TTL) {
        // Expired, remove from cache
        wikiCache.delete(key);
        return null;
    }

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

        // Try to find the category from a preceding h3/h2/h4 heading
        const precedingHeading = $table.prevAll('h2, h3, h4').first();
        if (precedingHeading.length) {
            // Extract just the text, removing any edit links
            const headingText = precedingHeading.find('.mw-headline').text().trim() ||
                               precedingHeading.text().replace(/\[edit\]/gi, '').trim();
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

const osrsApiClient = axios.create({
    baseURL: 'https://oldschool.runescape.wiki/api.php',
    params: {
        format: 'json'
    }
});

const OsrsWikiSearchSchema = z.object({
    search: z.string().describe("The term to search for on the OSRS Wiki"),
    limit: z.number().int().min(1).max(50).optional().describe("Number of results to return (1-50)"),
    offset: z.number().int().min(0).optional().describe("Offset for pagination (0-based)")
});

const OsrsWikiGetPageInfoSchema = z.object({
    titles: z.string().describe("Comma-separated list of page titles to get info for (e.g., Dragon_scimitar,Abyssal_whip)")
});

const OsrsWikiParsePageSchema = z.object({
    page: z.string().describe("The exact title of the wiki page to parse (e.g., 'Dragon scimitar', 'Abyssal whip'). Case-sensitive.")
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
                description: "Get parsed content of an OSRS Wiki page. Returns structured JSON with infobox data (stats, combat info), drop tables with item/quantity/rarity, table of contents, and content as markdown.",
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
                description: "Search any file in the data directory for matching entries.",
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
                const searchResponse = await osrsApiClient.get('', { params: searchParams });
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
                const pageInfoResponse = await osrsApiClient.get('', { params: pageInfoParams });
                setWikiCache(pageInfoCacheKey, pageInfoResponse.data);
                return responseToString(pageInfoResponse.data);
            }

            case "osrs_wiki_parse_page": {
                const { page } = OsrsWikiParsePageSchema.parse(args);
                const parseParams = {
                    action: 'parse',
                    page: page,
                    prop: 'text|sections',
                    formatversion: 2
                };
                const parseCacheKey = getWikiCacheKey('wiki_parse_page', parseParams);
                const cachedParseData = getFromWikiCache(parseCacheKey);
                if (cachedParseData) {
                    return responseToString(cachedParseData);
                }

                const parseResponse = await osrsApiClient.get('', { params: parseParams });

                const rawHtml = parseResponse.data?.parse?.text;
                if (!rawHtml) {
                    return responseToString({ error: 'Page content not found.' });
                }

                const infobox = extractInfobox(rawHtml);
                const dropTable = extractDropTable(rawHtml);
                const content = cleanAndConvertHtml(rawHtml);
                const sections = parseResponse.data?.parse?.sections?.map((s: any) => ({
                    level: s.level,
                    title: s.line,
                    anchor: s.anchor
                })) || [];

                const parseResult = {
                    page: page,
                    infobox: infobox,
                    dropTable: dropTable.length > 0 ? dropTable : null,
                    sections: sections,
                    content: content
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

async function main() {
    try {
        //console.log("Starting MCP OSRS Server...");
        const transport = new StdioServerTransport();
        await server.connect(transport);
        //console.log("MCP OSRS Server running on stdio");
    } catch (error) {
        console.error("Error during startup:", error);
        process.exit(1);
    }
}

main().catch((error) => {
    console.error("Fatal error in main():", error);
    process.exit(1);
});

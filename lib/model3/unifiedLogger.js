"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const wyclif_1 = require("wyclif");
/** This provides a singleton class to provide easy access to the logger */
class UnifiedLogger {
    constructor() { }
    /** Gets the logger instance */
    static getInstance() {
        if (!UnifiedLogger.instance) {
            UnifiedLogger.instance = (0, wyclif_1.Log)('agent');
            UnifiedLogger.instance.info('\n\nLogger created!\nRunning new Simulation\n');
        }
        return UnifiedLogger.instance;
    }
}
exports.default = UnifiedLogger;

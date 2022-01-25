"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const wyclif_1 = require("wyclif");
/** This provides a singleton class to provide easy access to the logger */
class UnifiedLogger {
    constructor() { }
    /** Gets the logger instance */
    static getInstance() {
        if (!UnifiedLogger.instance) {
            UnifiedLogger.instance = new wyclif_1.Log('agent');
        }
        return UnifiedLogger.instance;
    }
}
exports.default = UnifiedLogger;

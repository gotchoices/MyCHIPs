"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const wyclif_1 = require("wyclif");
/** This provides a singleton class to provide easy access to the logger */
class UnifiedLogger {
    constructor() { }
    /** Sets a passed-in logger instance */
    static setInstance(log) {
        UnifiedLogger.instance = log;
    }
    static getInstance() {
        if (!UnifiedLogger.instance) {
            UnifiedLogger.instance = (0, wyclif_1.Log)('model-3');
            UnifiedLogger.instance.info('\n\nLogger created!\nRunning new Simulation\n');
        }
        return UnifiedLogger.instance;
    }
}
exports.default = UnifiedLogger;

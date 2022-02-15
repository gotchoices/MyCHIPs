import { Log } from 'wyclif'

/** This provides a singleton class to provide easy access to the logger */
class UnifiedLogger {
  private static instance: WyclifLogger

  private constructor() {}

  /** Gets the logger instance */
  public static getInstance(): WyclifLogger {
    if (!UnifiedLogger.instance) {
      UnifiedLogger.instance = Log('agent')
    }
    return UnifiedLogger.instance
  }
}

export default UnifiedLogger

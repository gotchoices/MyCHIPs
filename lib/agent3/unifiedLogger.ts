import { Log } from 'wyclif'

/** This provides a singleton class to provide easy access to the logger */
class UnifiedLogger {
  private static instance: WyclifLogger

  private constructor() {}

  /** Gets the logger instance */
  public static getInstance(): WyclifLogger {
    if (!UnifiedLogger.instance) {
      UnifiedLogger.instance = Log('agent')
      UnifiedLogger.instance.info(
        '\n\nLogger created!\nRunning new Simulation\n'
      )
    }
    return UnifiedLogger.instance
  }
}

export default UnifiedLogger

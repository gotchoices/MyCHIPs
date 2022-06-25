import { Log } from 'wyclif'

/** This provides a singleton class to provide easy access to the logger */
class UnifiedLogger {
  private static instance: WyclifLogger

  private constructor() {}

  /** Sets a passed-in logger instance */
  public static setInstance(log): void {
    UnifiedLogger.instance = log
  }

  public static getInstance(): WyclifLogger {
    if (!UnifiedLogger.instance) {
      UnifiedLogger.instance = Log('model-3')
      UnifiedLogger.instance.info(
        '\n\nLogger created!\nRunning new Simulation\n'
      )
    }
    return UnifiedLogger.instance
  }
}

export default UnifiedLogger

/** Kyle's custom logger that outputs data to simulation logging windows */
declare interface WyclifLogger {
  error(...args: string[] | unknown[]): void
  warn(...args: string[]): void
  info(...args: string[]): void
  debug(...args: any[]): void
  verbose(...args: string[] | number[]): void
  silly(...args: string[]): void
  trace(...args: string[]): void
}

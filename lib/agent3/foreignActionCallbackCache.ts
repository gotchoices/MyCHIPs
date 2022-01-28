
class ForeignActionCallbackCache {
    private static instance: ForeignActionCallbackCache

    private callbacksMap: { [x: string]: (...args: any) => any }

    private constructor() {
        this.callbacksMap = {}
    }

    public static getInstance() {
        if (!ForeignActionCallbackCache.instance) {
            ForeignActionCallbackCache.instance = new ForeignActionCallbackCache()
        }
        return ForeignActionCallbackCache.instance
    }

    public addCallback(tag: string, callback: (...args: any) => any) {
        this.callbacksMap[tag] = callback
    }

    public getCallback(tag: string): (...args: any) => any {
        if (this.callbacksMap[tag]) {
            return this.callbacksMap[tag]
        } else {
            return ()=>{}   // Maybe throw an error, but I don't really care enough right now...
        }
    }

    public deleteCallback(tag: string) {
        delete this.callbacksMap[tag]
    }
}
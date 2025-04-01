# MyCHIPs Error Handling Strategy  Apr 1, 2025

This document outlines a comprehensive strategy for improving error handling and socket cleanup throughout the MyCHIPs server codebase to prevent unexpected crashes and ensure reliable operation.

## Problem Statement

The MyCHIPs server crashed with an unhandled 'error' event related to socket connections:

```
(node:901664) Warning: An error event has already been emitted on the socket. Please use the destroy method on the socket while handling a 'clientError' event.
(Use `node --trace-warnings ...` to show where the warning was created)
node:events:495
      throw er; // Unhandled 'error' event
      ^

Error: read ECONNRESET
    at TCP.onStreamRead (node:internal/stream_base_commons:217:20)
Emitted 'error' event on Socket instance at:
    at Socket.onerror (node:internal/streams/readable:828:14)
    at Socket.emit (node:events:517:28)
    at emitErrorNT (node:internal/streams/destroy:151:8)
    at emitErrorCloseNT (node:internal/streams/destroy:116:3)
    at process.processTicksAndRejections (node:internal/process/task_queues:82:21) {
  errno: -104,
  code: 'ECONNRESET',
  syscall: 'read'
}
```

This suggests:
1. An `ECONNRESET` error occurred when reading from a socket
2. The error event was emitted on a socket that already had an error 
3. The socket wasn't properly destroyed, leading to a second error event that crashed the server

## Error Handling Strategy

### Principles

1. **Defense in Depth**: Implement error handling at multiple levels
2. **Graceful Degradation**: Errors in one component should not crash the entire application
3. **Comprehensive Logging**: Log errors with context for diagnosis
4. **Resilience**: Recover from transient errors where possible

### Implementation Approaches

1. **Try/Catch Blocks**: Wrap critical operations in try/catch
2. **Promise Error Handling**: Ensure all promises have `.catch()` handlers
3. **Event Listeners**: Add error listeners to all event emitters
4. **Default Error Handlers**: Implement fallback handlers for unexpected errors

## Socket Cleanup Strategy

### Principles

1. **Selective Handling**: Only explicitly destroy sockets when necessary, allowing the system to handle most cleanup
2. **Resource Management**: Track active connections for monitoring and debugging
3. **Timeout Management**: Implement proper timeouts to prevent resource leaks
4. **Error Propagation Control**: Prevent errors from propagating unhandled

### Implementation Approaches

1. **Nuanced Error Handling**: Categorize socket errors and only destroy when truly necessary
   - Fatal/unrecoverable errors: May require explicit socket.destroy()
   - Transient errors: Log and allow the system to recover
   - Data/protocol errors: Handle at application level without socket destruction

2. **Connection Monitoring**: Track socket lifecycle for diagnostics without aggressive intervention
   - Monitor socket state for debugging and metrics
   - Allow natural socket lifecycle to complete in most cases

3. **Resource Protection**: Focus on preventing resource exhaustion
   - Implement timeouts to prevent indefinitely hanging connections
   - Add connection limits to prevent resource overload

4. **Graceful Degradation**: Implement patterns for maintaining service during partial failures
   - Allow independent failure of socket connections without cascading effects
   - Provide fallback mechanisms when appropriate

## Implementation Checklist

### Error Handling Improvements

- [x] **bin/mychips.js**
  - [x] Add process-level uncaught exception handler
  - [x] Add unhandled promise rejection handler
  - [ ] Wrap key initialization blocks in try/catch

- [x] **lib/peer2peer.js**
  - [x] Add try/catch to peerTransmit method
  - [x] Improve error handling in db.query callbacks
  - [x] Add proper error handling to the poll method
  - [ ] Enhance stateError method to handle more error types

- [x] **lib/peernoise.js**
  - [x] Add try/catch to send method
  - [x] Improve error handling in socket connection callbacks
  - [x] Add error handling to packet parsing methods
  - [x] Enhance error handling in encryption/decryption operations

- [x] **lib/noisewrap.js**
  - [x] Return appropriate error objects instead of just logging
  - [ ] Add try/catch blocks to all methods that don't already have them

- [ ] **All Socket-Related Code**
  - [x] Ensure all event handlers have error handling
  - [ ] Add timeout handling to all network operations

### Socket Cleanup Improvements

- [ ] **lib/peernoise.js - PeerConnection Class**
  - [ ] Improve error handler to log context and categorize errors:
    ```javascript
    s.on('error', e => {
      this.log.error('Socket error:', this.agent, e.message, e.code)
      // Only destroy for specific unrecoverable errors
      if (e.code === 'EPROTOTYPE' || e.code === 'ERR_STREAM_WRITE_AFTER_END') {
        if (this.socket && !this.socket.destroyed) {
          try {
            this.socket.destroy();
          } catch (err) {
            this.log.error('Error during socket cleanup:', err.message);
          }
        }
      }
    })
    ```
  - [ ] Enhance error categorization in socket error handlers
  - [ ] Update `socketEnd()` method to better handle state tracking
  - [ ] Ensure initFraming properly handles frame stream errors

- [ ] **lib/peernoise.js - Main Class**
  - [ ] Improve the `close()` method to gracefully shut down connections
  - [ ] Add diagnostic logging for connections during shutdown
  - [ ] Add connection state tracking without aggressive intervention

- [ ] **General Socket Management**
  - [ ] Implement socket state monitoring for diagnostics
  - [ ] Add monitoring for connection lifecycle events
  - [ ] Review and set appropriate timeouts to prevent resource exhaustion

## Implementation Progress

### Completed
1. **Error Handling - Phase 1**:
   - Added process-level uncaught exception and promise rejection handlers
   - Implemented comprehensive error handling in major components:
     - peer2peer.js: peerTransmit and poll methods
     - peernoise.js: send, fromInitiator, decrypt, and initiate methods 
     - noisewrap.js: proper error propagation from encrypt/decrypt operations
   - Added error handling to critical network message processing
   - Ensured errors are properly logged with context for easier debugging

### Remaining
1. **Socket Cleanup - Phase 1**:
   - Improve error categorization in socket handlers
   - Enhance error logging with socket state information
   - Only destroy sockets for specific unrecoverable error types

2. **Error Handling - Phase 2**:
   - Wrap key initialization blocks in try/catch
   - Add try/catch blocks to remaining methods in noisewrap.js
   - Enhance stateError method to handle more error types

3. **Socket Monitoring - Phase 2**:
   - Implement diagnostic tracking of socket states
   - Add logging for connection lifecycle events
   - Review and optimize connection timeouts

4. **Final Improvements**:
   - Add adaptive timeout handling based on connection patterns
   - Implement graceful degradation for partial failures
   - Add system monitoring for connection health

## Testing Strategy

1. Create test cases that simulate network errors:
   - Connection reset by peer
   - Connection timeout
   - Socket hang up
   - DNS resolution failure

2. Implement stress tests that:
   - Create and destroy many connections rapidly
   - Force error conditions during active communication
   - Simulate slow/partial network failures

3. Add logging to verify proper cleanup:
   - Track socket creation and destruction
   - Monitor for resource leaks
   - Verify error handling paths

## Conclusion

We have made significant progress in enhancing the error handling capabilities of the MyCHIPs server. The first phase of improvements has been implemented, focusing on:

1. Adding process-level error handlers to prevent server crashes
2. Implementing comprehensive error handling in critical network communication code
3. Ensuring proper error propagation and logging throughout the system

These changes have substantially improved the stability of the server by preventing unhandled errors from causing crashes. With the error handling foundation in place, we can now take a more nuanced approach to socket management:

1. Instead of aggressively destroying sockets on all errors, we'll allow most socket cleanup to occur naturally
2. We'll enhance error categorization to handle specific error types appropriately 
3. We'll focus on monitoring and diagnostics rather than intervention for most socket issues
4. We'll only explicitly destroy sockets for specific unrecoverable error conditions

This balanced approach will provide the benefits of proper error handling while allowing the Node.js runtime and operating system to handle most socket lifecycle management, which is their natural responsibility. The result will be a more resilient server that properly logs errors while continuing to run even when network disruptions occur.

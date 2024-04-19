export class KeyNotFoundError extends Error {
  constructor(message) {
    super(message);
    this.name = 'KeyNotFound';
  }
}

/**
  * Error if different public keys found when signing tallies/chits
  */
export class DifferentSigningKeyError extends Error {
  constructor(message) {
    super(message);
    this.name = 'DifferentSigningKeyError'
  }
}


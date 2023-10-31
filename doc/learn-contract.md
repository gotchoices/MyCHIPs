<div style="display: flex; justify-content: space-between;">
  <a href="README.md#contents">Back to Index</a>
  <a href="learn-lift.md">Next</a>
</div>

## Tally Contracts

### General
A CHIP is, at its heart, a credit agreement between two parties.
In other words, it is a debt contract--payable by one party and receivable to the other.

So one job of MyCHIPs is to organize and document these contracts.
It will do so just as you might imagine with any legally binding agreement.
That way, if both parties share a legal jurisdiction, their agreements could be 
enforced by that jurisdiction.  This is in addition to the expected negative 
consequence of tarnished reputation that will naturally result in the trading 
community as a result of defaulting on a contract.

The contact directory contains examples of contracts and their components.
Normally, a contract would be comprised of multiple components.
The idea is, you mix and match various clauses together to build up a complete
contract agreement that is acceptable to both parties.
Ideally, there would be a relatively small universe of "standard" contracts 
people recognize and get comfortable with.

Contracts can be incorporated into other contracts by referring to the contract's
resource ID (RID), which is an encoded hash of the contents of the contract.
This way the contract itself doesn't actually have to get repeated inline.
But the terms, or effect of the contract, are still invoked by reference.

### Contract Format
A contract is represented as a JSON object with the following properties:

  - host: mychips.org (or any valid web address)  
    The web address of some computer that can serve up an authoritative copy
    of the contract document.  That system must answer queries for the
    document given nothing but its RID.
    
    Most users are likely to feel most comfortable using a tally contract 
    written by someone they can trust.  The system should discourage users from 
    entering into a tally using a contract they are not familiar with.

  - name: Chip_Definition  
    A symbolic name for the contract.  This is independent of the language the
    contract is written in.  Think of it more like a file name.  It should 
    uniquely refer to a particular document (which may have multiple versions
    and/or languages) within the namespace of the particular host.

  - version:	1  
    An integer indicating the revision of the contract.  The number 1 indicates
    this is the first publicly released version.

  - language:	eng  
    Use the standard, 3-letter abbreviation for the language the contract is
    rendered in.  It is very possible to have the same contract and version
    available in multiple languages.  In fact, it might be possible to include
    the same contract in two different languages as part of a single tally.

  - top: true/null
    If present and true, this indicates that the document is suitable for
    inclusion directly in a MyCHIPs tally.  Otherwise, it is intended to be
    referenced by some higher document and included as a sub-section.
  
  - rid: Resource_ID  
    This contains a SHA-256 hash of the rest of the object so it must be 
    treated differently from all the other properties.  When computing the hash, 
    the rid property is removed, the object is serialized using a deterministic 
    algorithm, and then run through the SHA256 hash routine.  The hash is
    encoded using base64url format and then added back into the document object.

  - published:  
    A date indicating when this contract version was published by the author.
    This must be in ISO format YYYY-MM-DD where the month is a two digit 
    number, and not a word in any particular language.  The day should also
    be a two digit number.  This exact format is important so hashes
    generated in different contexts (in the database or in a JS frontend) will 
    properly match.

  - title:  
    A concise title, in the target language, for the contract.  This will be
    used as a header for the contract or section when the document is rendered.

  - text:  
    An optional pragraph of text which will form a recital paragraph for the
    contract or section.  This consists of one or more sentences, terminated by 
    a regular punctuation mark, and being separated by a single space.  There 
    should be no line feeds or other superfluous characters in the paragraph.
    It will be parsed as HTML, so extra white space would be ignored anyway.
    The text may include a few HTML formatting tags which are limited to 
    <b>bold,</b> <i>italicized,</i> <u>underlined,</u> and a custom tag <x-r>
    used to create cross-references.
  
  - tag:  
    An optional character string that can be used to target cross references
    from other sections, to this one.

  - sections:  
    An array of JSON objects which constitute the sub-sections of this document 
    or section.  Each object contains a subset of the properties described here 
    as follows:

    - title:
    - tag:
    - text:
    - sections:
    - source:  
      If present, this indicates that some other document should be included 
      at this point.  The exact format of the field is expected to be defined and 
      understood by the application (MyCHIPs) so the general code in Wylib will
      just accept whatever form is entered and leave it up to an external
      handler to deal with.

### Contract URI
    As mentioned, contract documents (as well as other resources) that are
    referenced for inclusion in a tallies or tally contract will be specified by
    a URI.  In the case of MyCHIPs, the contract must be available at all times via 
    an http fetch from the issuer's site.  The contract url specifies the format for
    fetching these resources:
    
    For purposes of inclusion in a Wylib structured document, the URI will be
    specified simply as:
```
       AcLuufjjd8f...FPIUuiDFJ
```
    to reference a contract document from the same author as the enclosing document, or:
```
       example.com/AcLuufjjd8f...FPIUuiDFJ
```
    to explicitly specify the author host name where the document can be found.

    If an actual http fetch is required, this URI must be translated to something
    a MyCHIPs server will respond to, such as:
```    
    	https://mychips.org/doc/AcLuufjjd8f...FPIUuiDFJ
    	https://mychips.org/?type=doc&rid=AcLuufjjd8f...FPIUuiDFJ
```

### Tally Agreement Layout
The tally itself is an agreement between two parties.
For clarity, we will refer to it at this top level as the "Tally Agreement."

By inclusion or reference, the Tally Agreement should contain enough data to
clearly explain the commitments each of the parties is making to each other.

When a tally agreement is printed out, it should contain at least the following:

```
This Tally Agreement is made by and between the Parties:

  Vendor: <Name of stock entity in the tally>
  Vendor ID Type: email, domain, usa, etc.
  Vendor ID: <email_address>, <domain_name>, <Tax ID Number>, etc.
  Vendor Public: <Stock entity's public trading key>

and:
  Client: <Name of the foil entity in the tally>
  Client ID Type: email, domain, usa, etc.
  Client ID: <email_address>, <domain_name>, <Tax ID Number>, etc.
  Client Public: <Foil entity's public trading key>

which Agreement is made according to the following terms and conditions:

  Stock Credit Terms:				(see doc/Tallies)
    <Enumerated list of Stock's credit terms>
  Foil Credit Terms:				(see doc/Tallies)
    <Enumerated list of Foil's credit terms>

and according to the definitions, terms, and conditions specified in the
following contract which is incorporated herein and made a part of this
Agreement:

  Contract: <publisher.domain/Tally_Contract-version-language>
  Contract Hash: <Contract digest>

this Agreement being made binding, as of:
  Tally Date: <Date the tally was signed>

by the digital signatures of the parties as follows:
  Tally Hash: <Tally digest>
  Stock Signature: <Stock's signature of tally hash>
  Foil Signature: <Foil's signature of tally hash>

<QR Code containing Tally JSON>
```

The Tally Contract itself whould then be structured something like this:
```
  Recitals
  Tally_Definition		Roles of the parties
  Chip_Definition		
  Duties_Rights			Recourse / Governing law
  Representations
  Defaults
  Credit Terms			Definition of specific terms
  Sending_Value
  Free
  Ethics
```

<div style="display: flex; justify-content: space-between;">
  <a href="README.md#contents">Back to Index</a>
  <a href="learn-lift.md">Next</a>
</div>

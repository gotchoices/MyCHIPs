# MyCHIPs Trading Contract Visualization Tool
July 2020

## Project Background:
MyCHIPs is a system for trading value using a network of private credit 
contracts.  These contracts are very real--just as a written contract you might
draft and execute with a business partner or a contractor.

The primary difference is, MyCHIPs contracts are not regularly rendered to
paper or signed using pen and ink.  Rather, they are stored in a digital
JSON format that focuses on content rather than presentation.

The content of a contract is condensed down using a SHA256 hash and then
encorporated into a trading tally which itself gets similarly hashed and then
cryptographically signed by the parties to the agreement.  The result is a
signed, legally enforceable contract that can be later rendered to paper or
electronic media should contract proof or enforcement become necessary.


The current proof-of-concept release of MyCHIPs relies on the
[Wylib](http://github.com/gotchoices/wylib) library for generating and viewing
contract documents.  The particular module is
[here](http://github.com/gotchoices/wylib/src/strdoc.vue).

## Objectives:
The goal of this project is to enhance the existing Wylib structured document
tool so it is ready for production use in MyCHIPs or other related projects.

## Strategy:
- Analyze/understand existing strdoc code
- Coordinate with backend report generation code project
- Coordinate with mobile user app
- Evaluate what additional functionality will be needed
- Enhance strdoc code
- Generate needed unit testing, where applicable
- Document system and changes

## Outcomes:
- MyCHIPs Admin UI can readily create/edit/modify contract documents
- MyCHIPs Admin UI can render/print contract documents
- Strdoc works properly in Admin report windows 
  (local domain or separate browser report window)
- Users can browse rendered contract documents via MyCHIPs http portal
- Strdoc menu functions work properly
- Editing menu functions are more intuitive

## Technical Considerations:
The existing strdoc is implemented in VueJS.

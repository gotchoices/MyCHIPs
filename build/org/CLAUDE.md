# MyCHIPs Website Build System Guide

This document provides essential information about the MyCHIPs website build system, structure, and process for future reference.

## Build System Overview

The website uses m4 macro processing to generate HTML files:

- **Source files**: `.m4` extension
- **Output files**: `.html` extension
- **Build script**: `./make` automates the build process
- **Publish script**: `./publish` handles deployment using the `MYCHIPS_ORG_WEB_DEPLOY` environment variable

To build a specific page:
```bash
./make pagename.html
```

To build all default pages:
```bash
./make
```

## Key Components

1. **template** - Standard HTML template with placeholders
2. **all.m4** - Contains common macros used across multiple pages
3. **Individual .m4 files** - Define content for specific pages using macros

## Important Macros

- **TITLE** - Defines the page title (appears in h1)
- **SUBTITLE** - Defines the page subtitle (appears in h2)
- **CONTENT** - Defines the main content section
- **LINK_BLOCK** - Creates a grid box item with icon, title, link, and description
- **GETAPP** - Common component for app download instructions

## Macro Definition Format

```m4
define(MACRO_NAME,`
  HTML content here with $1, $2, etc. for parameters
')
```

## Spacing Adjustments

Several spacing adjustments have been made to improve the visual design:
- Reduced gap between "Learn More" title and grid (margin-top: 20px)
- Reduced padding inside grid boxes (30px 20px)
- Adjusted spacing around privacy policy link (pt-2 pb-0)

## CPI Update Script

The `updateCPI` script handles fetching and updating the Consumer Price Index data. Important notes:

- Runs as a cron job
- Error handling has been improved to log errors to stderr
- Important changes to address:
  - No validation for markValue before using in calculations
  - No timeout mechanism for API calls
  - Nested callbacks that could be refactored for better maintainability

## Structure and Content Patterns

### Page Sections
1. Introduction/description
2. App download links
3. "Learn More" grid of resources
4. "News & Presentations" chronological list
5. Privacy Policy link
6. Footer

### News Items
- Displayed in chronological order (newest first)
- Include date in title with consistent "Month Year" format
- Ensure consistent button styling based on content type

## Potential Future Improvements

1. **Macro Consistency**
   - Create additional shared macros for common text patterns
   - Standardize macro usage across all pages
   - Consider centralizing URL definitions

2. **Error Handling in updateCPI**
   - Add timeout/retry mechanism for API calls
   - Add validation for markValue before calculations
   - Consider refactoring to use async/await

3. **SEO Optimization**
   - Add meta descriptions and keywords
   - Add structured data for search engines
   - Improve accessibility attributes

4. **Build Process**
   - Add better documentation for content editors
   - Consider more robust temporary file cleanup
   - Add support for automated validation

## Common Tasks

### Adding a New Presentation

To add a new presentation to the News section:

1. Edit index.m4
2. Add a new card using the same format as existing presentations
3. Place it in the appropriate chronological position (newest first)
4. Follow the date format "Month Year"
5. Run `./make index.html` to rebuild the page

### Creating a New Page

1. Create a new .m4 file (e.g., newpage.m4)
2. Define the TITLE, SUBTITLE, and CONTENT macros
3. Run `./make newpage.html` to build the page
4. Add the page to the default build list in the make script if needed

### Deploying Changes

After making and testing changes locally:

```bash
./publish
```

This deploys the website to the location specified in the `MYCHIPS_ORG_WEB_DEPLOY` environment variable.
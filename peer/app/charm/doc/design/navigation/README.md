# Navigation Documentation

This directory contains all navigation-related specifications and documentation for the MyCHIPs mobile app.

## 📁 Directory Structure

- **`sitemap.md`** - Complete navigation tree and screen hierarchy
- **`global-specs.md`** - Global navigation specifications (tabs, breadcrumbs, etc.)
- **`deep-links.md`** - URL routing and deep link patterns
- **`flows/`** - User flow diagrams for complex navigation sequences

## 🚀 Workflow Guidelines

### When Adding a New Screen

**ALWAYS** update navigation documentation when creating screens:

1. **Update Navigation Tree** (`sitemap.md`)
   - Place the screen in the correct tab section
   - Define its relationship to parent/child screens
   - Specify modal vs. navigation transitions

2. **Create Screen Specification** (`../specs/screen-name.md`)
   - Include navigation context (breadcrumbs, tab state, etc.)
   - Reference global navigation patterns from `global-specs.md`

3. **Update Master Index** (`../index.md`)
   - Add screen to appropriate section
   - Link to both screen XML and navigation placement

4. **Test Navigation Flow**
   - Verify all paths to/from the screen make sense
   - Check tab state consistency
   - Validate breadcrumb paths

### When Modifying Navigation Structure

1. **Update Global Specs** (`global-specs.md`)
   - Document changes to tab bar, breadcrumbs, or universal patterns
   - Update component specifications

2. **Update XSLT Components** (`../components/transforms/master.xsl`)
   - Ensure navigation components match specifications
   - Test component rendering

3. **Audit Existing Screens**
   - Check all screens for compliance with new navigation patterns
   - Update screens that need navigation changes

4. **Update Documentation**
   - Refresh `sitemap.md` with new structure
   - Update `deep-links.md` for routing changes

## 📋 Navigation Consistency Checklist

Before finalizing any screen design:

- [ ] Screen placed correctly in navigation tree
- [ ] Tab state specified (which tab is active)
- [ ] Breadcrumb path defined (if applicable)
- [ ] Back button behavior documented
- [ ] Deep link pattern established
- [ ] Modal vs. navigation transition specified
- [ ] Global navigation components used consistently

## 🔗 Related Documentation

- **Screen Specifications**: `../specs/` - Screen-specific design requirements
- **Component Library**: `../components/transforms/master.xsl` - Reusable navigation components
- **User Stories**: `../stories/` - Navigation flows within user journeys
- **Master Index**: `../index.md` - Complete design documentation

---

*Keep navigation documentation updated to ensure consistent user experience and accurate AI code generation.*

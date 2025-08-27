<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0" 
                xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
                xmlns:ui="http://mychips.io/ui"
                xmlns="http://www.w3.org/2000/svg">
                
    <xsl:output method="xml" indent="yes"/>
    
    <!-- Root app-screen transforms to SVG -->
    <xsl:template match="ui:app-screen">
        <svg width="{@width}" height="{@height}" xmlns="http://www.w3.org/2000/svg">
            <!-- Screen Background -->
            <rect width="{@width}" height="{@height}" fill="#F2F2F7"/>
            
            <!-- Process all child elements -->
            <xsl:apply-templates/>
        </svg>
    </xsl:template>
    
    <!-- App Header Component -->
    <xsl:template match="ui:app-header">
        <g data-component="app-header">
            <!-- Status bar -->
            <rect width="375" height="44" fill="#F8F8F8"/>
            <text x="20" y="30" font-family="SF Pro, Arial" font-size="14" font-weight="600" fill="#000000">9:41</text>
            <text x="340" y="30" font-family="SF Pro, Arial" font-size="14" font-weight="400" text-anchor="end" fill="#000000">100%</text>
            
            <!-- Navigation bar -->
            <rect y="44" width="375" height="56" fill="white" stroke="#E5E5EA" stroke-width="1"/>
            <text x="187.5" y="80" font-family="SF Pro, Arial" font-size="17" font-weight="600" text-anchor="middle" fill="#000000">
                <xsl:value-of select="@data-title"/>
            </text>
            
            <!-- Back button -->
            <path d="M25 72 L20 77 L25 82" fill="none" stroke="#007AFF" stroke-width="2"/>
            <text x="35" y="81" font-family="SF Pro, Arial" font-size="17" fill="#007AFF">Back</text>
        </g>
    </xsl:template>
    
    <!-- Balance Card Component -->
    <xsl:template match="ui:balance-card">
        <g data-component="balance-card">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <rect width="340" height="120" fill="#34C759" stroke="#30A047" stroke-width="1" rx="16"/>
            
            <!-- Gradient definition -->
            <defs>
                <linearGradient id="balanceGradient" x1="0%" y1="0%" x2="100%" y2="100%">
                    <stop offset="0%" style="stop-color:#40D865;stop-opacity:0.3" />
                    <stop offset="100%" style="stop-color:#28A745;stop-opacity:0.1" />
                </linearGradient>
            </defs>
            <rect width="340" height="120" fill="url(#balanceGradient)" rx="16"/>
            
            <text x="20" y="30" font-family="SF Pro, Arial" font-size="14" font-weight="500" fill="white" opacity="0.8">
                <xsl:value-of select="@data-label"/>
            </text>
            <text x="20" y="55" font-family="SF Pro, Arial" font-size="32" font-weight="700" fill="white">
                <xsl:value-of select="@data-amount"/>
            </text>
            <text x="20" y="80" font-family="SF Pro, Arial" font-size="14" font-weight="400" fill="white" opacity="0.7">
                <xsl:value-of select="@data-description"/>
            </text>
            
            <!-- Currency icon -->
            <circle cx="290" cy="40" r="20" fill="white" opacity="0.2"/>
            <text x="290" y="46" font-family="SF Pro, Arial" font-size="14" font-weight="700" text-anchor="middle" fill="white">₡</text>
        </g>
    </xsl:template>
    
    <!-- Section Header Component -->
    <xsl:template match="ui:section-header">
        <text font-family="SF Pro, Arial" font-size="22" font-weight="700" fill="#000000">
            <xsl:if test="@x"><xsl:attribute name="x"><xsl:value-of select="@x"/></xsl:attribute></xsl:if>
            <xsl:if test="@y"><xsl:attribute name="y"><xsl:value-of select="@y"/></xsl:attribute></xsl:if>
            <xsl:value-of select="@data-title"/>
        </text>
    </xsl:template>
    
    <!-- Quick Actions Row -->
    <xsl:template match="ui:quick-actions-row">
        <g data-component="quick-actions-row">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            <xsl:apply-templates/>
        </g>
    </xsl:template>
    
    <!-- Quick Action Card -->
    <xsl:template match="ui:quick-action-card">
        <g data-component="quick-action-card">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <rect width="100" height="80" fill="white" stroke="#E5E5EA" stroke-width="1" rx="12"/>
            <circle cx="50" cy="35" r="16" fill="{@data-icon-color}"/>
            <text x="50" y="41" font-family="SF Pro, Arial" font-size="16" font-weight="600" text-anchor="middle" fill="white">
                <xsl:value-of select="@data-icon"/>
            </text>
            <text x="50" y="65" font-family="SF Pro, Arial" font-size="13" font-weight="500" text-anchor="middle" fill="#000000">
                <xsl:value-of select="@data-label"/>
            </text>
        </g>
    </xsl:template>
    
    <!-- Transaction List -->
    <xsl:template match="ui:transaction-list">
        <g data-component="transaction-list">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            <xsl:apply-templates/>
        </g>
    </xsl:template>
    
    <!-- Transaction Item -->
    <xsl:template match="ui:transaction-item">
        <g data-component="transaction-item">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <rect width="340" height="70" fill="white" stroke="#F2F2F7" stroke-width="1"/>
            
            <!-- Avatar/Icon circle -->
            <circle cx="35" cy="35" r="20" fill="{@data-avatar-color}"/>
            <text x="35" y="41" font-family="SF Pro, Arial" font-size="16" font-weight="600" text-anchor="middle" fill="white">
                <xsl:value-of select="@data-icon"/>
            </text>
            
            <!-- Transaction details -->
            <text x="70" y="25" font-family="SF Pro, Arial" font-size="17" font-weight="600" fill="#000000">
                <xsl:value-of select="@data-name"/>
            </text>
            <text x="70" y="45" font-family="SF Pro, Arial" font-size="15" fill="#8E8E93">
                <xsl:value-of select="@data-description"/>
            </text>
            <text x="70" y="60" font-family="SF Pro, Arial" font-size="13" fill="#8E8E93">
                <xsl:value-of select="@data-time"/>
            </text>
            
            <!-- Amount -->
            <text x="320" y="30" font-family="SF Pro, Arial" font-size="17" font-weight="600" text-anchor="end" fill="{@data-amount-color}">
                <xsl:value-of select="@data-amount"/>
            </text>
            
            <!-- Chevron -->
            <path d="M315 30 L320 35 L315 40" fill="none" stroke="#C7C7CC" stroke-width="2"/>
        </g>
    </xsl:template>
    
    <!-- Action Button Secondary -->
    <xsl:template match="ui:action-button-secondary">
        <g data-component="action-button-secondary">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <rect width="{@width}" height="{@height}" fill="none" stroke="#007AFF" stroke-width="2" rx="22"/>
            <text x="{@width div 2}" y="{@height div 2 + 6}" font-family="SF Pro, Arial" font-size="17" font-weight="500" text-anchor="middle" fill="#007AFF">
                <xsl:value-of select="@data-label"/>
            </text>
        </g>
    </xsl:template>
    
    <!-- Breadcrumb Bar Component -->
    <xsl:template match="ui:breadcrumb-bar">
        <g data-component="breadcrumb-bar">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <!-- Background (optional) -->
            <rect width="335" height="44" fill="transparent"/>
            
            <!-- Process breadcrumb items -->
            <xsl:apply-templates/>
        </g>
    </xsl:template>
    
    <!-- Breadcrumb Item -->
    <xsl:template match="ui:breadcrumb-item">
        <g data-component="breadcrumb-item">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <xsl:variable name="is-current" select="@data-current = 'true'"/>
            <xsl:variable name="text-color">
                <xsl:choose>
                    <xsl:when test="$is-current">#000000</xsl:when>
                    <xsl:otherwise>#007AFF</xsl:otherwise>
                </xsl:choose>
            </xsl:variable>
            <xsl:variable name="font-weight">
                <xsl:choose>
                    <xsl:when test="$is-current">600</xsl:when>
                    <xsl:otherwise>400</xsl:otherwise>
                </xsl:choose>
            </xsl:variable>
            
            <!-- Breadcrumb text -->
            <text x="0" y="28" font-family="SF Pro, Arial" font-size="14" font-weight="{$font-weight}" fill="{$text-color}">
                <xsl:value-of select="@data-label"/>
            </text>
            
            <!-- Separator (if not current/last item) -->
            <xsl:if test="not($is-current)">
                <text x="{string-length(@data-label) * 8 + 8}" y="28" font-family="SF Pro, Arial" font-size="14" fill="#8E8E93"> > </text>
            </xsl:if>
        </g>
    </xsl:template>
    
    <!-- Bottom Tab Bar -->
    <xsl:template match="ui:bottom-tab-bar">
        <g data-component="bottom-tab-bar">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <!-- Background -->
            <rect width="375" height="83" fill="white" stroke="#E5E5EA" stroke-width="1"/>
            
            <!-- Process tab items -->
            <xsl:apply-templates/>
        </g>
    </xsl:template>
    
    <!-- Tab Item -->
    <xsl:template match="ui:tab-item">
        <g data-component="tab-item">
            <!-- Calculate position based on x attribute (5-tab layout: 75px each, centers at 37.5, 112.5, 187.5, 262.5, 337.5) -->
            <xsl:variable name="x-pos">
                <xsl:choose>
                    <xsl:when test="@x"><xsl:value-of select="@x"/></xsl:when>
                    <xsl:otherwise>37.5</xsl:otherwise> <!-- Default to first tab position -->
                </xsl:choose>
            </xsl:variable>
            
            <!-- Icon background color (use data attribute or default based on active state) -->
            <xsl:variable name="icon-color">
                <xsl:choose>
                    <xsl:when test="@data-icon-color"><xsl:value-of select="@data-icon-color"/></xsl:when>
                    <xsl:when test="@data-active = 'true'">#007AFF</xsl:when>
                    <xsl:otherwise>#8E8E93</xsl:otherwise>
                </xsl:choose>
            </xsl:variable>
            
            <!-- Text color (use data attribute or default based on active state) -->
            <xsl:variable name="text-color">
                <xsl:choose>
                    <xsl:when test="@data-text-color"><xsl:value-of select="@data-text-color"/></xsl:when>
                    <xsl:when test="@data-active = 'true'">#007AFF</xsl:when>
                    <xsl:otherwise>#8E8E93</xsl:otherwise>
                </xsl:choose>
            </xsl:variable>
            
            <!-- Font weight (use data attribute or default based on active state) -->
            <xsl:variable name="font-weight">
                <xsl:choose>
                    <xsl:when test="@data-font-weight"><xsl:value-of select="@data-font-weight"/></xsl:when>
                    <xsl:when test="@data-active = 'true'">600</xsl:when>
                    <xsl:otherwise>500</xsl:otherwise>
                </xsl:choose>
            </xsl:variable>
            
            <!-- Icon -->
            <circle cx="{$x-pos}" cy="25" r="12" fill="{$icon-color}"/>
            <text x="{$x-pos}" y="30" font-family="SF Pro, Arial" font-size="12" text-anchor="middle" fill="white">
                <xsl:value-of select="@data-icon"/>
            </text>
            
            <!-- Label -->
            <text x="{$x-pos}" y="50" font-family="SF Pro, Arial" font-size="10" text-anchor="middle" fill="{$text-color}" font-weight="{$font-weight}">
                <xsl:value-of select="@data-label"/>
            </text>
        </g>
    </xsl:template>
    
    <!-- Welcome Hero Component -->
    <xsl:template match="ui:welcome-hero">
        <g data-component="welcome-hero">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <!-- Hero background -->
            <rect width="335" height="180" fill="#007AFF" rx="20"/>
            <rect width="335" height="180" fill="url(#heroGradient)" rx="20"/>
            
            <!-- Gradient definition -->
            <defs>
                <linearGradient id="heroGradient" x1="0%" y1="0%" x2="100%" y2="100%">
                    <stop offset="0%" style="stop-color:#40A9FF;stop-opacity:0.3"/>
                    <stop offset="100%" style="stop-color:#1890FF;stop-opacity:0.1"/>
                </linearGradient>
            </defs>
            
            <!-- Content -->
            <text x="167.5" y="40" font-family="SF Pro, Arial" font-size="28" font-weight="700" text-anchor="middle" fill="white">
                <xsl:value-of select="@data-title"/>
            </text>
            <text x="167.5" y="70" font-family="SF Pro, Arial" font-size="16" font-weight="500" text-anchor="middle" fill="white" opacity="0.9">
                <xsl:value-of select="@data-subtitle"/>
            </text>
            <text x="167.5" y="120" font-family="SF Pro, Arial" font-size="14" font-weight="400" text-anchor="middle" fill="white" opacity="0.8">
                <xsl:value-of select="@data-description"/>
            </text>
        </g>
    </xsl:template>
    
    <!-- Feature List Component -->
    <xsl:template match="ui:feature-list">
        <g data-component="feature-list">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            <xsl:apply-templates/>
        </g>
    </xsl:template>
    
    <!-- Feature Item Component -->
    <xsl:template match="ui:feature-item">
        <g data-component="feature-item">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <!-- Icon circle -->
            <circle cx="30" cy="30" r="20" fill="#F0F9FF" stroke="#007AFF" stroke-width="2"/>
            <text x="30" y="36" font-family="SF Pro, Arial" font-size="16" text-anchor="middle" fill="#007AFF">
                <xsl:value-of select="@data-icon"/>
            </text>
            
            <!-- Content -->
            <text x="70" y="25" font-family="SF Pro, Arial" font-size="17" font-weight="600" fill="#000000">
                <xsl:value-of select="@data-title"/>
            </text>
            <text x="70" y="45" font-family="SF Pro, Arial" font-size="14" fill="#8E8E93">
                <xsl:value-of select="@data-description"/>
            </text>
        </g>
    </xsl:template>
    
    <!-- Button Primary Component -->
    <xsl:template match="ui:button-primary">
        <g data-component="button-primary">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <rect width="{@width}" height="{@height}" fill="#007AFF" rx="25"/>
            <text x="{@width div 2}" y="{@height div 2 + 6}" font-family="SF Pro, Arial" font-size="17" font-weight="600" text-anchor="middle" fill="white">
                <xsl:value-of select="@data-label"/>
            </text>
        </g>
    </xsl:template>
    
    <!-- Button Text Component -->
    <xsl:template match="ui:button-text">
        <g data-component="button-text">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <text x="{@width div 2}" y="{@height div 2 + 6}" font-family="SF Pro, Arial" font-size="17" font-weight="500" text-anchor="middle" fill="#007AFF">
                <xsl:value-of select="@data-label"/>
            </text>
        </g>
    </xsl:template>
    
    <!-- App Footer Component -->
    <xsl:template match="ui:app-footer">
        <g data-component="app-footer">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <text x="187.5" y="30" font-family="SF Pro, Arial" font-size="12" text-anchor="middle" fill="#8E8E93">
                <xsl:value-of select="@data-version"/>
            </text>
        </g>
    </xsl:template>
    
    <!-- Progress Bar Component -->
    <xsl:template match="ui:progress-bar">
        <g data-component="progress-bar">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <!-- Background -->
            <rect width="335" height="6" fill="#E5E5EA" rx="3"/>
            
            <!-- Progress -->
            <xsl:variable name="progress" select="(@data-current div @data-total) * 335"/>
            <rect width="{$progress}" height="6" fill="#007AFF" rx="3"/>
            
            <!-- Label -->
            <text x="167.5" y="25" font-family="SF Pro, Arial" font-size="13" text-anchor="middle" fill="#8E8E93">
                <xsl:value-of select="@data-label"/>
            </text>
        </g>
    </xsl:template>
    
    <!-- Form Section Component -->
    <xsl:template match="ui:form-section">
        <g data-component="form-section">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            <xsl:apply-templates/>
        </g>
    </xsl:template>
    
    <!-- Input Field Component -->
    <xsl:template match="ui:input-field">
        <g data-component="input-field">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <!-- Label -->
            <text x="0" y="15" font-family="SF Pro, Arial" font-size="14" font-weight="500" fill="#000000">
                <xsl:value-of select="@data-label"/>
                <xsl:if test="@data-required = 'true'">
                    <tspan fill="#FF3B30"> *</tspan>
                </xsl:if>
            </text>
            
            <!-- Input field -->
            <rect y="25" width="335" height="44" fill="white" stroke="#D1D1D6" stroke-width="1" rx="8"/>
            
            <!-- Placeholder text -->
            <text x="12" y="52" font-family="SF Pro, Arial" font-size="16" fill="#C7C7CC">
                <xsl:value-of select="@data-placeholder"/>
            </text>
        </g>
    </xsl:template>
    
    <!-- Info Card Component -->
    <xsl:template match="ui:info-card">
        <g data-component="info-card">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <!-- Background -->
            <rect width="335" height="80" fill="#F0F9FF" stroke="#B3D8FF" stroke-width="1" rx="12"/>
            
            <!-- Icon -->
            <text x="20" y="35" font-family="SF Pro, Arial" font-size="18" fill="#007AFF">
                <xsl:value-of select="@data-icon"/>
            </text>
            
            <!-- Content -->
            <text x="50" y="25" font-family="SF Pro, Arial" font-size="15" font-weight="600" fill="#000000">
                <xsl:value-of select="@data-title"/>
            </text>
            <text x="50" y="45" font-family="SF Pro, Arial" font-size="13" fill="#666666">
                <xsl:value-of select="@data-description"/>
            </text>
        </g>
    </xsl:template>
    
    <!-- Balance Summary Component -->
    <xsl:template match="ui:balance-summary">
        <g data-component="balance-summary">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <!-- Background -->
            <rect width="335" height="120" fill="white" stroke="#E5E5EA" stroke-width="1" rx="16"/>
            
            <!-- CHIP Balance -->
            <text x="20" y="35" font-family="SF Pro, Arial" font-size="14" font-weight="500" fill="#8E8E93">CHIP Balance</text>
            <text x="20" y="60" font-family="SF Pro, Arial" font-size="28" font-weight="700" fill="#000000">
                <xsl:value-of select="@data-chip-balance"/>
            </text>
            
            <!-- Local Balance -->
            <text x="20" y="85" font-family="SF Pro, Arial" font-size="16" font-weight="500" fill="#666666">
                <xsl:value-of select="@data-local-balance"/>
            </text>
            
            <!-- Description -->
            <text x="20" y="105" font-family="SF Pro, Arial" font-size="13" fill="#8E8E93">
                <xsl:value-of select="@data-description"/>
            </text>
        </g>
    </xsl:template>
    
    <!-- Context Help Component -->
    <xsl:template match="ui:context-help">
        <g data-component="context-help">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <!-- Help icon -->
            <circle cx="12" cy="12" r="12" fill="#007AFF"/>
            <text x="12" y="17" font-family="SF Pro, Arial" font-size="14" font-weight="600" text-anchor="middle" fill="white">?</text>
        </g>
    </xsl:template>
    
    <!-- Getting Started List Component -->
    <xsl:template match="ui:getting-started-list">
        <g data-component="getting-started-list">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            <xsl:apply-templates/>
        </g>
    </xsl:template>
    
    <!-- Getting Started Item Component -->
    <xsl:template match="ui:getting-started-item">
        <g data-component="getting-started-item">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <!-- Background -->
            <rect width="335" height="60" fill="white" stroke="#E5E5EA" stroke-width="1" rx="12"/>
            
            <!-- Icon -->
            <text x="25" y="38" font-family="SF Pro, Arial" font-size="20" text-anchor="middle">
                <xsl:value-of select="@data-icon"/>
            </text>
            
            <!-- Content -->
            <text x="60" y="25" font-family="SF Pro, Arial" font-size="16" font-weight="600" fill="#000000">
                <xsl:value-of select="@data-title"/>
            </text>
            <text x="60" y="45" font-family="SF Pro, Arial" font-size="14" fill="#8E8E93">
                <xsl:value-of select="@data-description"/>
            </text>
            
            <!-- Status indicator -->
            <xsl:variable name="status-color">
                <xsl:choose>
                    <xsl:when test="@data-status = 'pending'">#FF9500</xsl:when>
                    <xsl:when test="@data-status = 'optional'">#8E8E93</xsl:when>
                    <xsl:when test="@data-status = 'ready'">#34C759</xsl:when>
                    <xsl:otherwise>#8E8E93</xsl:otherwise>
                </xsl:choose>
            </xsl:variable>
            <circle cx="305" cy="30" r="6" fill="{$status-color}"/>
            
            <!-- Chevron -->
            <path d="M315 25 L320 30 L315 35" fill="none" stroke="#C7C7CC" stroke-width="2"/>
        </g>
    </xsl:template>
    
    <!-- Empty State Component -->
    <xsl:template match="ui:empty-state">
        <g data-component="empty-state">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <!-- Icon -->
            <text x="167.5" y="50" font-family="SF Pro, Arial" font-size="48" text-anchor="middle" opacity="0.5">
                <xsl:value-of select="@data-icon"/>
            </text>
            
            <!-- Title -->
            <text x="167.5" y="85" font-family="SF Pro, Arial" font-size="18" font-weight="600" text-anchor="middle" fill="#000000">
                <xsl:value-of select="@data-title"/>
            </text>
            
            <!-- Description -->
            <text x="167.5" y="110" font-family="SF Pro, Arial" font-size="14" text-anchor="middle" fill="#8E8E93">
                <xsl:value-of select="@data-description"/>
            </text>
        </g>
    </xsl:template>
    
    <!-- Search Bar Component -->
    <xsl:template match="ui:search-bar">
        <g data-component="search-bar">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <!-- Background -->
            <rect width="335" height="36" fill="#F2F2F7" rx="18"/>
            
            <!-- Search icon -->
            <text x="15" y="24" font-family="SF Pro, Arial" font-size="14" fill="#8E8E93">🔍</text>
            
            <!-- Placeholder text -->
            <text x="40" y="24" font-family="SF Pro, Arial" font-size="16" fill="#8E8E93">
                <xsl:value-of select="@data-placeholder"/>
            </text>
        </g>
    </xsl:template>
    
    <!-- Filter Chips Component -->
    <xsl:template match="ui:filter-chips">
        <g data-component="filter-chips">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            <xsl:apply-templates/>
        </g>
    </xsl:template>
    
    <!-- Filter Chip Component -->
    <xsl:template match="ui:filter-chip">
        <g data-component="filter-chip">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <xsl:variable name="bg-color">
                <xsl:choose>
                    <xsl:when test="@data-active = 'true'">#007AFF</xsl:when>
                    <xsl:otherwise>#F2F2F7</xsl:otherwise>
                </xsl:choose>
            </xsl:variable>
            
            <xsl:variable name="text-color">
                <xsl:choose>
                    <xsl:when test="@data-active = 'true'">white</xsl:when>
                    <xsl:otherwise>#000000</xsl:otherwise>
                </xsl:choose>
            </xsl:variable>
            
            <!-- Background -->
            <rect width="40" height="28" fill="{$bg-color}" rx="14"/>
            
            <!-- Label -->
            <text x="20" y="19" font-family="SF Pro, Arial" font-size="13" font-weight="500" text-anchor="middle" fill="{$text-color}">
                <xsl:value-of select="@data-label"/>
            </text>
        </g>
    </xsl:template>
    
    <!-- Info Banner Component -->
    <xsl:template match="ui:info-banner">
        <g data-component="info-banner">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <!-- Background -->
            <rect width="335" height="44" fill="#F0F9FF" stroke="#B3D8FF" stroke-width="1" rx="8"/>
            
            <!-- Icon -->
            <text x="15" y="27" font-family="SF Pro, Arial" font-size="16" fill="#007AFF">ℹ️</text>
            
            <!-- Message -->
            <text x="40" y="27" font-family="SF Pro, Arial" font-size="14" fill="#000000">
                <xsl:value-of select="@data-message"/>
            </text>
        </g>
    </xsl:template>
    
    <!-- Vendor List Component -->
    <xsl:template match="ui:vendor-list">
        <g data-component="vendor-list">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            <xsl:apply-templates/>
        </g>
    </xsl:template>
    
    <!-- Vendor Item Component -->
    <xsl:template match="ui:vendor-item">
        <g data-component="vendor-item">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <!-- Background -->
            <rect width="335" height="85" fill="white" stroke="#E5E5EA" stroke-width="1" rx="12"/>
            
            <!-- Logo -->
            <circle cx="30" cy="42.5" r="18" fill="#F2F2F7"/>
            <text x="30" y="48" font-family="SF Pro, Arial" font-size="16" text-anchor="middle">
                <xsl:value-of select="@data-logo"/>
            </text>
            
            <!-- Content -->
            <text x="60" y="25" font-family="SF Pro, Arial" font-size="16" font-weight="600" fill="#000000">
                <xsl:value-of select="@data-name"/>
            </text>
            <text x="60" y="43" font-family="SF Pro, Arial" font-size="13" fill="#8E8E93">
                <xsl:value-of select="@data-category"/>
            </text>
            <text x="60" y="62" font-family="SF Pro, Arial" font-size="12" fill="#666666">
                <xsl:value-of select="@data-description"/>
            </text>
            
            <!-- Rating and distance -->
            <text x="270" y="25" font-family="SF Pro, Arial" font-size="13" fill="#FF9500" text-anchor="end">
                ★ <xsl:value-of select="@data-rating"/>
            </text>
            <text x="270" y="43" font-family="SF Pro, Arial" font-size="12" fill="#8E8E93" text-anchor="end">
                <xsl:value-of select="@data-distance"/>
            </text>
            
            <!-- Acceptance indicators -->
            <xsl:if test="@data-accepts-chips = 'true'">
                <rect x="275" y="50" width="25" height="15" fill="#34C759" rx="7.5"/>
                <text x="287.5" y="60" font-family="SF Pro, Arial" font-size="8" font-weight="600" text-anchor="middle" fill="white">₡</text>
            </xsl:if>
            
            <xsl:if test="@data-accepts-tallies = 'true'">
                <rect x="305" y="50" width="25" height="15" fill="#007AFF" rx="7.5"/>
                <text x="317.5" y="60" font-family="SF Pro, Arial" font-size="8" font-weight="600" text-anchor="middle" fill="white">T</text>
            </xsl:if>
        </g>
    </xsl:template>
    
    <!-- Button Secondary Component -->
    <xsl:template match="ui:button-secondary">
        <g data-component="button-secondary">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <rect width="{@width}" height="{@height}" fill="none" stroke="#007AFF" stroke-width="2" rx="22"/>
            <text x="{@width div 2}" y="{@height div 2 + 6}" font-family="SF Pro, Arial" font-size="15" font-weight="500" text-anchor="middle" fill="#007AFF">
                <xsl:value-of select="@data-label"/>
            </text>
        </g>
    </xsl:template>
    
    <!-- Credit Limit Input Component -->
    <xsl:template match="ui:credit-limit-input">
        <g data-component="credit-limit-input">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <!-- Label -->
            <text x="0" y="15" font-family="SF Pro, Arial" font-size="14" font-weight="500" fill="#000000">
                <xsl:value-of select="@data-label"/>
            </text>
            
            <!-- CHIP Amount Input -->
            <rect y="25" width="160" height="44" fill="white" stroke="#D1D1D6" stroke-width="1" rx="8"/>
            <text x="12" y="52" font-family="SF Pro, Arial" font-size="18" font-weight="600" fill="#000000">
                <xsl:value-of select="@data-chip-amount"/>
            </text>
            
            <!-- USD Equivalent -->
            <text x="175" y="47" font-family="SF Pro, Arial" font-size="16" fill="#8E8E93">
                <xsl:value-of select="@data-usd-amount"/>
            </text>
        </g>
    </xsl:template>
    
    <!-- Credit Limit Pair Component -->
    <xsl:template match="ui:credit-limit-pair">
        <g data-component="credit-limit-pair">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            <xsl:apply-templates/>
        </g>
    </xsl:template>
    
    <!-- Identity Display Component -->
    <xsl:template match="ui:identity-display">
        <g data-component="identity-display">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            <xsl:apply-templates/>
        </g>
    </xsl:template>
    
    <!-- Identity Field Component -->
    <xsl:template match="ui:identity-field">
        <g data-component="identity-field">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <!-- Label -->
            <text x="0" y="15" font-family="SF Pro, Arial" font-size="14" font-weight="500" fill="#000000">
                <xsl:value-of select="@data-label"/>
                <xsl:if test="@data-optional = 'true'">
                    <tspan fill="#8E8E93"> (optional)</tspan>
                </xsl:if>
            </text>
            
            <!-- Value or Empty State -->
            <xsl:choose>
                <xsl:when test="@data-value != ''">
                    <text x="0" y="35" font-family="SF Pro, Arial" font-size="16" fill="#000000">
                        <xsl:value-of select="@data-value"/>
                    </text>
                    <xsl:if test="@data-verified = 'true'">
                        <text x="200" y="35" font-family="SF Pro, Arial" font-size="14" fill="#34C759">✓ Verified</text>
                    </xsl:if>
                </xsl:when>
                <xsl:otherwise>
                    <text x="0" y="35" font-family="SF Pro, Arial" font-size="16" fill="#C7C7CC">Not provided</text>
                </xsl:otherwise>
            </xsl:choose>
        </g>
    </xsl:template>
    
    <!-- QR Code Display Component -->
    <xsl:template match="ui:qr-code-display">
        <g data-component="qr-code-display">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <!-- QR Code Background -->
            <rect x="67.5" y="20" width="200" height="200" fill="white" stroke="#E5E5EA" stroke-width="1" rx="12"/>
            
            <!-- QR Code Placeholder -->
            <rect x="87.5" y="40" width="160" height="160" fill="#000000"/>
            <rect x="97.5" y="50" width="140" height="140" fill="white"/>
            <text x="167.5" y="130" font-family="SF Pro, Arial" font-size="24" text-anchor="middle" fill="#000000">QR</text>
            
            <!-- Title and Subtitle -->
            <text x="167.5" y="250" font-family="SF Pro, Arial" font-size="18" font-weight="600" text-anchor="middle" fill="#000000">
                <xsl:value-of select="@data-title"/>
            </text>
            <text x="167.5" y="270" font-family="SF Pro, Arial" font-size="14" text-anchor="middle" fill="#8E8E93">
                <xsl:value-of select="@data-subtitle"/>
            </text>
            
            <!-- Expiration -->
            <text x="167.5" y="295" font-family="SF Pro, Arial" font-size="12" text-anchor="middle" fill="#FF9500">
                <xsl:value-of select="@data-expiration"/>
            </text>
        </g>
    </xsl:template>
    
    <!-- Share Actions Component -->
    <xsl:template match="ui:share-actions">
        <g data-component="share-actions">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            <xsl:apply-templates/>
        </g>
    </xsl:template>
    
    <!-- Share Button Component -->
    <xsl:template match="ui:share-button">
        <g data-component="share-button">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <!-- Background -->
            <rect width="90" height="70" fill="white" stroke="#E5E5EA" stroke-width="1" rx="12"/>
            
            <!-- Icon -->
            <text x="45" y="30" font-family="SF Pro, Arial" font-size="24" text-anchor="middle">
                <xsl:value-of select="@data-icon"/>
            </text>
            
            <!-- Label -->
            <text x="45" y="55" font-family="SF Pro, Arial" font-size="13" font-weight="500" text-anchor="middle" fill="#000000">
                <xsl:value-of select="@data-label"/>
            </text>
        </g>
    </xsl:template>
    
    <!-- Text Area Component -->
    <xsl:template match="ui:text-area">
        <g data-component="text-area">
            <xsl:if test="@x and @y">
                <xsl:attribute name="transform">translate(<xsl:value-of select="@x"/>, <xsl:value-of select="@y"/>)</xsl:attribute>
            </xsl:if>
            
            <!-- Label -->
            <text x="0" y="15" font-family="SF Pro, Arial" font-size="14" font-weight="500" fill="#000000">
                <xsl:value-of select="@data-label"/>
            </text>
            
            <!-- Text area -->
            <rect y="25" width="{@width}" height="{@height}" fill="white" stroke="#D1D1D6" stroke-width="1" rx="8"/>
            
            <!-- Content or placeholder -->
            <xsl:choose>
                <xsl:when test="@data-value != ''">
                    <text x="12" y="45" font-family="SF Pro, Arial" font-size="16" fill="#000000">
                        <xsl:value-of select="@data-value"/>
                    </text>
                </xsl:when>
                <xsl:otherwise>
                    <text x="12" y="45" font-family="SF Pro, Arial" font-size="16" fill="#C7C7CC">
                        <xsl:value-of select="@data-placeholder"/>
                    </text>
                </xsl:otherwise>
            </xsl:choose>
        </g>
    </xsl:template>
    
</xsl:stylesheet>

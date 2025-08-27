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
            <xsl:variable name="slot" select="@slot"/>
            <xsl:variable name="x-pos">
                <xsl:choose>
                    <xsl:when test="$slot = '1'">52.5</xsl:when>
                    <xsl:when test="$slot = '2'">131.25</xsl:when>
                    <xsl:when test="$slot = '3'">210</xsl:when>
                    <xsl:when test="$slot = '4'">288.75</xsl:when>
                    <xsl:when test="$slot = '5'">337.5</xsl:when>
                </xsl:choose>
            </xsl:variable>
            
            <xsl:variable name="color">
                <xsl:choose>
                    <xsl:when test="@data-active = 'true'">#007AFF</xsl:when>
                    <xsl:otherwise>#8E8E93</xsl:otherwise>
                </xsl:choose>
            </xsl:variable>
            
            <!-- Icon -->
            <circle cx="{$x-pos}" cy="25" r="12" fill="{$color}"/>
            <text x="{$x-pos}" y="30" font-family="SF Pro, Arial" font-size="12" text-anchor="middle" fill="white">
                <xsl:value-of select="@data-icon"/>
            </text>
            
            <!-- Label -->
            <text x="{$x-pos}" y="50" font-family="SF Pro, Arial" font-size="10" text-anchor="middle" fill="{$color}">
                <xsl:attribute name="font-weight">
                    <xsl:choose>
                        <xsl:when test="@data-active = 'true'">600</xsl:when>
                        <xsl:otherwise>500</xsl:otherwise>
                    </xsl:choose>
                </xsl:attribute>
                <xsl:value-of select="@data-label"/>
            </text>
        </g>
    </xsl:template>
    
</xsl:stylesheet>

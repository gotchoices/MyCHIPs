#!/bin/bash

# MyCHIPs Design Build System
# Transforms semantic XML screen definitions to visual SVG wireframes

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Configuration
SOURCE_DIR="screens"
OUTPUT_DIR="images"
TRANSFORM_DIR="components/transforms"
MASTER_TRANSFORM="$TRANSFORM_DIR/master.xsl"

# Ensure output directory exists
mkdir -p "$OUTPUT_DIR"

# Function to print colored output
print_status() {
    echo -e "${BLUE}[BUILD]${NC} $1"
}

print_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

print_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

print_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Function to check dependencies
check_dependencies() {
    print_status "Checking build dependencies..."
    
    if ! command -v xsltproc &> /dev/null; then
        print_error "xsltproc is required but not installed"
        print_status "Install with: brew install libxslt (macOS) or apt-get install xsltproc (Linux)"
        exit 1
    fi
    
    if [ ! -f "$MASTER_TRANSFORM" ]; then
        print_error "Master transform file not found: $MASTER_TRANSFORM"
        exit 1
    fi
    
    print_success "Dependencies OK"
}

# Function to build a single XML file
build_file() {
    local source_file="$1"
    local relative_path="${source_file#$SOURCE_DIR/}"
    local output_file="$OUTPUT_DIR/${relative_path%.xml}.svg"
    local output_dir=$(dirname "$output_file")
    
    # Create output directory if it doesn't exist
    mkdir -p "$output_dir"
    
    print_status "Building: $relative_path"
    
    # Transform XML to SVG
    if xsltproc "$MASTER_TRANSFORM" "$source_file" > "$output_file" 2>/dev/null; then
        print_success "Generated: ${output_file#$OUTPUT_DIR/}"
    else
        print_error "Failed to build: $relative_path"
        return 1
    fi
}

# Function to build all files in a directory
build_directory() {
    local target_dir="$1"
    local source_path="$SOURCE_DIR/$target_dir"
    
    if [ ! -d "$source_path" ]; then
        print_error "Directory not found: $source_path"
        return 1
    fi
    
    print_status "Building directory: $target_dir"
    
    # Find all XML files in the directory
    local xml_files=$(find "$source_path" -name "*.xml" -type f)
    local file_count=$(echo "$xml_files" | wc -l)
    
    if [ -z "$xml_files" ]; then
        print_warning "No XML files found in $target_dir"
        return 0
    fi
    
    print_status "Found $file_count XML files in $target_dir"
    
    # Build each file
    local success_count=0
    while IFS= read -r file; do
        if build_file "$file"; then
            ((success_count++))
        fi
    done <<< "$xml_files"
    
    print_success "Built $success_count/$file_count files in $target_dir"
}

# Function to build all files
build_all() {
    print_status "Building all screens..."
    
    # Find all XML files recursively
    local xml_files=$(find "$SOURCE_DIR" -name "*.xml" -type f)
    local total_files=$(echo "$xml_files" | wc -l)
    
    if [ -z "$xml_files" ]; then
        print_warning "No XML files found in $SOURCE_DIR"
        return 0
    fi
    
    print_status "Found $total_files XML files total"
    
    # Build each file
    local success_count=0
    local start_time=$(date +%s)
    
    while IFS= read -r file; do
        if build_file "$file"; then
            ((success_count++))
        fi
    done <<< "$xml_files"
    
    local end_time=$(date +%s)
    local duration=$((end_time - start_time))
    
    print_success "Build complete: $success_count/$total_files files in ${duration}s"
}

# Function to watch for changes (if fswatch is available)
watch_mode() {
    if ! command -v fswatch &> /dev/null; then
        print_error "fswatch is required for watch mode"
        print_status "Install with: brew install fswatch (macOS)"
        exit 1
    fi
    
    print_status "Watching for changes in $SOURCE_DIR..."
    print_status "Press Ctrl+C to stop"
    
    fswatch -o "$SOURCE_DIR" "$TRANSFORM_DIR" | while read num_changes; do
        print_status "Changes detected, rebuilding..."
        build_all
    done
}

# Function to clean build outputs
clean() {
    print_status "Cleaning build outputs..."
    
    if [ -d "$OUTPUT_DIR" ]; then
        rm -rf "$OUTPUT_DIR"
        print_success "Removed $OUTPUT_DIR"
    fi
    
    mkdir -p "$OUTPUT_DIR"
    print_success "Clean complete"
}

# Function to show help
show_help() {
    cat << EOF
MyCHIPs Design Build System

USAGE:
    ./build.sh [command] [options]

COMMANDS:
    all                 Build all XML files to SVG (default)
    <directory>         Build specific directory (e.g., wallet, auth)
    clean               Remove all build outputs
    watch               Watch for changes and rebuild automatically
    help                Show this help message

EXAMPLES:
    ./build.sh                  # Build everything
    ./build.sh wallet           # Build only wallet screens
    ./build.sh auth             # Build only auth screens
    ./build.sh clean            # Clean all outputs
    ./build.sh watch            # Watch mode

DIRECTORIES:
    Source:  $SOURCE_DIR
    Output:  $OUTPUT_DIR
    Transforms: $TRANSFORM_DIR

EOF
}

# Main script logic
main() {
    local command="${1:-all}"
    
    case "$command" in
        "help"|"-h"|"--help")
            show_help
            exit 0
            ;;
        "clean")
            clean
            exit 0
            ;;
        "watch")
            check_dependencies
            watch_mode
            ;;
        "all"|"")
            check_dependencies
            build_all
            ;;
        *)
            # Assume it's a directory name
            check_dependencies
            build_directory "$command"
            ;;
    esac
}

# Run main function with all arguments
main "$@"

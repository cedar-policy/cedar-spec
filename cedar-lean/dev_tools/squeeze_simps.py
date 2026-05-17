import re
import sys
import subprocess
import os
import shutil
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor, as_completed
import threading

def print_step(step_num, total_steps, message):
    """Print a formatted step message."""
    print(f"\n[{step_num}/{total_steps}] {message}")
    print("=" * 80)

def print_success(message):
    """Print a success message."""
    print(f"✓ {message}")

def print_info(message):
    """Print an info message."""
    print(f"ℹ {message}")

def print_warning(message):
    """Print a warning message."""
    print(f"⚠ {message}")

def get_indentation(line):
    return len(line) - len(line.lstrip())

def create_backup_filename(original_path, simp_index):
    """Create backup filename by adding _tmp_<index> before the file extension."""
    path_parts = os.path.splitext(original_path)
    return f"{path_parts[0]}_tmp_{simp_index}{path_parts[1]}"

def create_backup_file(original_path, simp_index):
    """Create a backup copy of the original file with _tmp_<index> suffix."""
    backup_path = create_backup_filename(original_path, simp_index)
    try:
        shutil.copy2(original_path, backup_path)
        print_success(f"Created backup file: {backup_path}")
        return backup_path
    except Exception as e:
        print(f"❌ Error creating backup file: {e}")
        return None

def copy_backup_to_original(backup_path, original_path):
    """Copy the backup file back to the original location."""
    try:
        shutil.copy2(backup_path, original_path)
        print_success(f"Successfully copied changes from backup to original file")
        return True
    except Exception as e:
        print(f"❌ Error copying backup to original: {e}")
        return False

def cleanup_backup_file(backup_path):
    try:
        if os.path.exists(backup_path):
            os.remove(backup_path)
            print_info(f"Cleaned up backup file: {backup_path}")
    except Exception as e:
        print_warning(f"Could not remove backup file {backup_path}: {e}")

def is_simp_terminal(lines, line_index):
    """Check if a simp call is terminal (last in its block)."""
    if line_index >= len(lines) - 1:
        return True
    
    current_indent = get_indentation(lines[line_index])
    next_indent = get_indentation(lines[line_index + 1])
    
    # If next line has less indentation, this simp is terminal
    if next_indent < current_indent:
        return True
    
    # If indentation is the same but both start with a dot, the simp is terminal
    if current_indent == next_indent:
        current_line_stripped = lines[line_index].lstrip()
        next_line_stripped = lines[line_index + 1].lstrip()
        if current_line_stripped.startswith('.') and next_line_stripped.startswith('.'):
            return True
    
    return False

def find_suggestion_from_build_output(build_output, target_line_num):
    """Find simp suggestion from build output for a specific line number."""

    print("here", flush=True)
    print(build_output, flush=True)
    # Check if this suggestion is for our target line
    line_pattern = f':{target_line_num}:'
    if line_pattern not in build_output:
        return None
    
    # Look for "Try this: simp only" or "Try this: dsimp only"
    simp_match = re.search(r'Try this: (d?simp only)', build_output)
    if not simp_match:
        return None
    
    simp_command = simp_match.group(1)
    
    start_pos = simp_match.end()
    remaining_text = build_output[start_pos:]
    
    # Look for square brackets containing comma-separated lemmas
    bracket_match = re.search(r'\s*\[([^\]]*)\]', remaining_text)
    if bracket_match:
        text_between = remaining_text[:bracket_match.start()]
        # the bracket starts on the same line
        if '\n' not in text_between:
            lemmas = bracket_match.group(1).strip()
            lemmas = re.sub(r'\s+', ' ', lemmas)
            
            after_bracket_pos = bracket_match.end()
            rest_of_text = remaining_text[after_bracket_pos:]
            
            newline_pos = rest_of_text.find('\n')
            # trailing text, for example "at h"
            if newline_pos != -1:
                trailing_text = rest_of_text[:newline_pos].strip()
            else:
                trailing_text = rest_of_text.strip()
            
            if trailing_text:
                return f"{simp_command} [{lemmas}] {trailing_text}"
            else:
                return f"{simp_command} [{lemmas}]"
    
    # No brackets, return "simp only" or "dsimp only"
    return simp_command

def apply_suggestion_to_line(lines, line_index, suggestion, original_line):
    """Apply a simp suggestion to a specific line, preserving content before 'simp' or 'dsimp'."""
    if suggestion:
        # Find everything before 'simp' or 'dsimp' in the original line
        # Use word boundaries to match complete words
        simp_match = re.search(r'(.*?)(dsimp|simp)', original_line)
        if simp_match:
            prefix = simp_match.group(1)
            lines[line_index] = f"{prefix}{suggestion}\n"
            print_success(f"Applied suggestion to line {line_index + 1}")
            return True
        else:
            # Error out if 'simp' or 'dsimp' not found - this should never happen
            raise ValueError(f"Error: 'simp' or 'dsimp' not found in line {line_index + 1}: {original_line.strip()}")
    else:
        # Error out completely if no suggestion found
        raise ValueError(f"❌ FATAL ERROR: No suggestion found for line {line_index + 1}. Aborting entire process.")

def find_simp_positions(lines):
    """Find all simp positions that should be processed (excluding terminal ones)."""
    simp_positions = []
    for i, line in enumerate(lines):
        # Check for simp or dsimp, but exclude simp?, dsimp?, simp only, dsimp only
        if (('simp' in line or 'dsimp' in line) and 
            not 'simp?' in line and not 'dsimp?' in line and 
            not 'simp only' in line and not 'dsimp only' in line):
            if is_simp_terminal(lines, i):
                print_info(f"Line {i+1}: Skipping simp/dsimp (last in block)")
                continue
            simp_positions.append(i)
    return simp_positions

def process_single_simp(lines, pos, backup_file_path):
    """Process a single simp call: replace with simp?, get suggestion, apply it."""
    # Store original line for restoration if needed
    original_line = lines[pos]
    
    # Replace simp or dsimp with simp? or dsimp? in the backup file
    if 'dsimp' in lines[pos]:
        lines[pos] = lines[pos].replace('dsimp', 'dsimp?')
    else:
        lines[pos] = lines[pos].replace('simp', 'simp?')
    
    # Write the modified content back to the backup file
    with open(backup_file_path, 'w') as f:
        f.writelines(lines)

    # Run lake build to get suggestions for this specific backup file
    build_success, build_output = run_lake_build(backup_file_path)                                             
    
    if not build_success:
        print(f"❌ Build failed after modifying line {pos + 1}.")
        return False
    
    # Find suggestion from build output
    current_line_num = pos + 1  # Convert to 1-based indexing
    suggestion = find_suggestion_from_build_output(build_output, current_line_num)
    
    if suggestion:
        print_info(f"Found suggestion for line {current_line_num}: {suggestion}")
    
    # Apply the suggestion
    apply_suggestion_to_line(lines, pos, suggestion, original_line)
    
    # Write the modified content back to the backup file
    with open(backup_file_path, 'w') as f:
        f.writelines(lines)

    # Verify the change didn't break the build for this specific backup file
    build_success, _ = run_lake_build(backup_file_path)
    if not build_success:
        print(f"❌ Build failed after applying suggestion to line {pos + 1}.")
        return False
    
    return True

def run_lake_build(target_file):
    """Run lake build on the target file and return (success, output)."""
    try:
        # Get the full absolute path of the target file
        full_target_path = os.path.abspath(target_file)
        
        # Build only the specific target file
        print_info(f"Running lake build for file: {full_target_path}")
        result = subprocess.run(['lake', 'build', full_target_path], 
                              capture_output=True, 
                              text=True)
        
        build_output = result.stdout + result.stderr
        
        # Check if build was successful
        if result.returncode == 0:
            print_success("Lake build completed successfully")
            return True, build_output
        else:
            print_warning("Lake build failed with return code: " + str(result.returncode))
            return False, build_output
            
    except subprocess.CalledProcessError as e:
        print_warning(f"Lake build failed with error code: {e.returncode}")
        return False, e.output
    except Exception as e:
        print(f"❌ Error during lake build: {e}")
        return False, ""

def process_simp_call_with_backup(file_path, pos_idx, pos, file_lock):
    """Process a single simp call with its own backup file."""
    print(f"\n📍 Processing simp call {pos_idx + 1} (line {pos + 1})")
    
    # Create fresh backup file for this simp call
    backup_path = create_backup_file(file_path, pos_idx)
    if not backup_path:
        print(f"❌ Failed to create backup file for simp call {pos_idx + 1}")
        return False, f"Failed to create backup file for simp call {pos_idx + 1}"
    
    try:
        # Read fresh copy of lines for this simp call
        with open(backup_path, 'r') as f:
            lines = f.readlines()
        
        # Process this single simp call
        success = process_single_simp(lines, pos, backup_path)
        
        if success:
            # Apply the change to the original file with file lock
            try:
                with file_lock:
                    with open(file_path, 'r') as f:
                        current_lines = f.readlines()
                    current_lines[pos] = lines[pos]
                    with open(file_path, 'w') as f:
                        f.writelines(current_lines)
                
                print_success(f"Successfully processed and applied simp call {pos_idx + 1}")
                cleanup_backup_file(backup_path)
                return True, None
                
            except Exception as e:
                error_msg = f"Error applying change to original file: {e}"
                print(f"❌ {error_msg}")
                cleanup_backup_file(backup_path)
                return False, error_msg
        else:
            error_msg = f"Failed to process simp call {pos_idx + 1}"
            print_warning(error_msg)
            cleanup_backup_file(backup_path)
            return False, error_msg
        
    except ValueError as e:
        # Handle fatal errors (like no suggestion found)
        error_msg = str(e)
        print(f"{error_msg}")
        cleanup_backup_file(backup_path)
        return False, error_msg
    except Exception as e:
        error_msg = f"Unexpected error processing simp call {pos_idx + 1}: {e}"
        print(f"❌ {error_msg}")
        cleanup_backup_file(backup_path)
        return False, error_msg

def process_lean_file(file_path):
    print(f"\n🔧 Starting Lean file processing at {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"📁 Processing file: {file_path}")
    print("=" * 80)

    script_dir = os.path.dirname(os.path.abspath(__file__))

    # Step 1: Read the original file
    print_step(1, 3, "Reading Lean file")
    try:
        with open(file_path, 'r') as f:
            original_lines = f.readlines()
        print_success(f"Successfully read {len(original_lines)} lines from file")
    except Exception as e:
        print(f"❌ Error reading file: {e}")
        return

    # Step 2: Process simp calls one by one with fresh backup files
    print_step(2, 3, "Processing simp calls with individual backup files")
    
    # Find all simp positions using helper function
    simp_positions = find_simp_positions(original_lines)
    print_success(f"Found {len(simp_positions)} simp calls to process")

    if len(simp_positions) == 0:
        print_info("No simp calls to process.")
        return

    # Keep track of successful changes for summary
    successful_count = 0
    failed_count = 0
    errors = []

    # Create a file lock for thread-safe file operations
    file_lock = threading.Lock()

    NUM_THREADS = min(len(simp_positions), 4)
    # Process simp calls in parallel using ThreadPoolExecutor
    print_info(f"Starting parallel processing with up to {NUM_THREADS} threads")
    
    with ThreadPoolExecutor(max_workers=NUM_THREADS) as executor:
        # Submit all tasks
        future_to_pos = {
            executor.submit(process_simp_call_with_backup, file_path, pos_idx, pos, file_lock): (pos_idx, pos)
            for pos_idx, pos in enumerate(simp_positions)
        }
        
        # Process completed tasks as they finish
        for future in as_completed(future_to_pos):
            pos_idx, pos = future_to_pos[future]
            try:
                success, error_msg = future.result()
                if success:
                    successful_count += 1
                else:
                    failed_count += 1
                    if error_msg and "FATAL ERROR" in error_msg:
                        # Handle fatal errors by stopping all processing
                        print(f"❌ {error_msg}")
                        print("❌ FATAL ERROR encountered. Stopping all processing.")
                        # Cancel remaining futures
                        for remaining_future in future_to_pos:
                            if not remaining_future.done():
                                remaining_future.cancel()
                        sys.exit(1)
                    elif error_msg:
                        errors.append(f"Simp call {pos_idx + 1}: {error_msg}")
            except Exception as e:
                failed_count += 1
                error_msg = f"Simp call {pos_idx + 1}: Unexpected exception: {e}"
                errors.append(error_msg)
                print(f"❌ {error_msg}")

    # Print any non-fatal errors
    if errors:
        print_warning("Non-fatal errors encountered:")
        for error in errors:
            print(f"  - {error}")

    # Step 3: Final summary
    print_step(3, 3, "Processing completed")
    print_success("All changes have been applied to the original file")

    print("\n✨ Processing completed successfully!")
    print(f"📊 Summary:")
    print(f"   - Total simp calls found: {len(simp_positions)}")
    print(f"   - Successfully processed: {successful_count}")
    print(f"   - Failed: {len(simp_positions) - successful_count}")
    print("=" * 80)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("❌ Error: Missing file path")
        print("Usage: python script.py <lean_file_path>")
        sys.exit(1)
    
    process_lean_file(sys.argv[1])

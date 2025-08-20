import re
import sys
import subprocess
import os
import shutil
from datetime import datetime

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
    """Create backup filename by adding _1_<index> before the file extension."""
    path_parts = os.path.splitext(original_path)
    return f"{path_parts[0]}_1_{simp_index}{path_parts[1]}"

def create_backup_file(original_path, simp_index):
    """Create a backup copy of the original file with _1_<index> suffix."""
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
    """Remove the backup file."""
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
    
    return next_indent < current_indent

def find_suggestion_from_build_output(build_output, target_line_num):
    """Find simp suggestion from build output for a specific line number."""
    lines_iter = iter(build_output.split('\n'))
    for line in lines_iter:
        if 'Try this: simp only' in line:
            # Extract line number from build output
            line_num_match = re.search(r':(\d+):', line)
            if line_num_match:
                build_line_num = int(line_num_match.group(1))
                # Only use suggestion if it matches our target line
                if build_line_num == target_line_num:
                    # Extract the suggestion from the current line only
                    suggestion_match = re.search(r'Try this: (simp only.*?)(?:\s*$)', line)
                    if suggestion_match:
                        suggestion = suggestion_match.group(1).strip()
                        
                        # If it's just "simp only" with no lemmas, return it as is
                        if suggestion == "simp only":
                            return "simp only"
                        
                        # Otherwise, return the full suggestion
                        return suggestion
    return None

def apply_suggestion_to_line(lines, line_index, suggestion, original_line):
    """Apply a simp suggestion to a specific line, preserving content before 'simp'."""
    if suggestion:
        # Find everything before 'simp' in the original line
        simp_match = re.search(r'(.*)simp', original_line)
        if simp_match:
            prefix = simp_match.group(1)
            lines[line_index] = f"{prefix}{suggestion}\n"
            print_success(f"Applied suggestion to line {line_index + 1}")
            return True
        else:
            # Error out if 'simp' not found - this should never happen
            raise ValueError(f"Error: 'simp' not found in line {line_index + 1}: {original_line.strip()}")
    else:
        # Error out completely if no suggestion found
        raise ValueError(f"❌ FATAL ERROR: No suggestion found for line {line_index + 1}. Aborting entire process.")

def find_simp_positions(lines):
    """Find all simp positions that should be processed (excluding terminal ones)."""
    simp_positions = []
    for i, line in enumerate(lines):
        if 'simp' in line and not 'simp?' in line and not 'simp only' in line:
            if is_simp_terminal(lines, i):
                print_info(f"Line {i+1}: Skipping simp (last in block)")
                continue
            simp_positions.append(i)
    return simp_positions

def process_single_simp(lines, pos, backup_file_path):
    """Process a single simp call: replace with simp?, get suggestion, apply it."""
    # Store original line for restoration if needed
    original_line = lines[pos]
    
    # Replace simp with simp? in the backup file
    lines[pos] = lines[pos].replace('simp', 'simp?')
    
    # Write the modified content back to the backup file
    with open(backup_file_path, 'w') as f:
        f.writelines(lines)

    # Run lake build to get suggestions for this specific backup file
    build_success, build_output = run_lake_build(backup_file_path)
    
    if not build_success:
        print(f"❌ Build failed after modifying line {pos + 1}. Restoring original line.")
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
    
    # Process each simp call individually with its own backup file
    for pos_idx, pos in enumerate(simp_positions):
        print(f"\n📍 Processing simp call {pos_idx + 1}/{len(simp_positions)} (line {pos + 1})")
        
        # Create fresh backup file for this simp call
        backup_path = create_backup_file(file_path, pos_idx)
        if not backup_path:
            print(f"❌ Failed to create backup file for simp call {pos_idx + 1}")
            print("❌ FATAL ERROR: Cannot continue without backup file. Aborting.")
            sys.exit(1)
        
        try:
            # Read fresh copy of lines for this simp call
            with open(backup_path, 'r') as f:
                lines = f.readlines()
            
            # Process this single simp call
            success = process_single_simp(lines, pos, backup_path)
            
            if success:
                # Apply the change to the original file immediately
                try:
                    # Read current state of original file
                    with open(file_path, 'r') as f:
                        current_lines = f.readlines()
                    
                    # Apply the successful change
                    current_lines[pos] = lines[pos]
                    
                    # Write back to original file
                    with open(file_path, 'w') as f:
                        f.writelines(current_lines)
                    
                    successful_count += 1
                    print_success(f"Successfully processed and applied simp call {pos_idx + 1}")
                    
                except Exception as e:
                    print(f"❌ Error applying change to original file: {e}")
                    cleanup_backup_file(backup_path)
                    print("❌ FATAL ERROR: Failed to apply change to original file. Aborting.")
                    sys.exit(1)
            else:
                print_warning(f"Failed to process simp call {pos_idx + 1}")
                cleanup_backup_file(backup_path)
                print("❌ FATAL ERROR: Simp processing failed. Aborting entire process.")
                sys.exit(1)
            
            # Clean up backup file after successful processing
            cleanup_backup_file(backup_path)
            
        except ValueError as e:
            # Handle fatal errors (like no suggestion found)
            print(f"{e}")
            cleanup_backup_file(backup_path)
            sys.exit(1)
        except Exception as e:
            print(f"❌ Unexpected error processing simp call {pos_idx + 1}: {e}")
            cleanup_backup_file(backup_path)
            print("❌ FATAL ERROR: Unexpected error occurred. Aborting entire process.")
            sys.exit(1)

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

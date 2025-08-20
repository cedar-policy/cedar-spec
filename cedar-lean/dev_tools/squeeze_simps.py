import re
import sys
import subprocess
import os
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
                    # Get the initial part of the suggestion
                    suggestion_parts = [re.search(r'Try this: (simp only[^"]*)', line).group(1)]
                    
                    # Look ahead for continuation lines
                    try:
                        next_line = next(lines_iter)
                        while next_line.strip() and not next_line.lstrip().startswith(('⚠', 'ℹ', '✓', 'info:', 'warning:')):
                            suggestion_parts.append(next_line.strip())
                            next_line = next(lines_iter)
                    except StopIteration:
                        pass

                    return ' '.join(suggestion_parts)
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
        print_warning(f"No suggestion found for line {line_index + 1}")
        # Restore original line if no suggestion found
        lines[line_index] = original_line
        return False

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

def process_single_simp(lines, pos, file_path, script_dir):
    """Process a single simp call: replace with simp?, get suggestion, apply it."""
    # Store original line for restoration if needed
    original_line = lines[pos]
    
    # Replace simp with simp? in the actual file
    lines[pos] = lines[pos].replace('simp', 'simp?')
    
    # Write the modified content back to the file
    with open(file_path, 'w') as f:
        f.writelines(lines)

    # Run lake build to get suggestions
    build_success, build_output = run_lake_build(script_dir)
    
    if not build_success:
        print(f"❌ Build failed after modifying line {pos + 1}. Restoring original file.")
        lines[pos] = original_line
        with open(file_path, 'w') as f:
            f.writelines(lines)
        return False
    
    # Find suggestion from build output
    current_line_num = pos + 1  # Convert to 1-based indexing
    suggestion = find_suggestion_from_build_output(build_output, current_line_num)
    
    if suggestion:
        print_info(f"Found suggestion for line {current_line_num}: {suggestion}")
    
    # Apply the suggestion
    apply_suggestion_to_line(lines, pos, suggestion, original_line)
    
    # Write the modified content back to the file
    with open(file_path, 'w') as f:
        f.writelines(lines)

    # Verify the change didn't break the build
    build_success, _ = run_lake_build(script_dir)
    if not build_success:
        print(f"❌ Build failed after applying suggestion to line {pos + 1}. Restoring original file.")
        lines[pos] = original_line
        with open(file_path, 'w') as f:
            f.writelines(lines)
        return False
    
    return True

def run_lake_build(script_dir):
    """Run lake build and return (success, output)."""
    try:
        print_info("Running lake build command...")
        # Run lake build in the parent directory of the script
        parent_dir = os.path.dirname(script_dir)
        result = subprocess.run(['lake', 'build'], 
                              capture_output=True, 
                              text=True, 
                              cwd=parent_dir)
        build_output = result.stdout + result.stderr
        
        # Check if build was successful
        if result.returncode == 0:
            if "Build completed successfully" in build_output:
                print_success("Lake build completed successfully")
                return True, build_output
            else:
                print_warning("Lake build output doesn't indicate success")
                return False, build_output
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

    # Step 1: Read the file
    print_step(1, 3, "Reading Lean file")
    try:
        with open(file_path, 'r') as f:
            lines = f.readlines()
        print_success(f"Successfully read {len(lines)} lines from file")
    except Exception as e:
        print(f"❌ Error reading file: {e}")
        return

    # Step 2: Process simp calls one by one
    print_step(2, 3, "Processing simp calls")
    
    # Find all simp positions using helper function
    simp_positions = find_simp_positions(lines)
    print_success(f"Found {len(simp_positions)} simp calls to process")

    # Process each simp call individually using helper function
    for pos_idx, pos in enumerate(simp_positions):
        print(f"\n📍 Processing simp call {pos_idx + 1}/{len(simp_positions)} (line {pos + 1})")
        
        success = process_single_simp(lines, pos, file_path, script_dir)
        if not success:
            return

    # Step 3: Final save (though file should already be up to date)
    print_step(3, 3, "Finalizing changes")
    print_success("All changes have been applied")

    print("\n✨ Processing completed successfully!")
    print(f"📊 Summary:")
    print(f"   - Total simp calls processed: {len(simp_positions)}")
    print("=" * 80)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("❌ Error: Missing file path")
        print("Usage: python script.py <lean_file_path>")
        sys.exit(1)
    
    process_lean_file(sys.argv[1])

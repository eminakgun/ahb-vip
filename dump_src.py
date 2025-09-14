import os
import re

def discover_test_files(project_root):
    """
    Discover all test files in the tests directory and return them in dependency order.
    Base tests should come before derived tests.
    """
    test_dir = os.path.join(project_root, "tests")
    if not os.path.exists(test_dir):
        print(f"Warning: Tests directory not found at {test_dir}")
        return []
    
    test_files = []
    
    # Get all .sv files in the tests directory
    try:
        for root, dirs, files in os.walk(test_dir):
            for file in files:
                if file.endswith('.sv') or file.endswith('.svh'):
                    # Get relative path from project root
                    full_path = os.path.join(root, file)
                    rel_path = os.path.relpath(full_path, project_root)
                    test_files.append(rel_path)
    except Exception as e:
        print(f"Error discovering test files: {e}")
        return []
    
    # Sort test files by dependency order
    sorted_test_files = sort_test_files_by_dependency(test_files)
    
    print(f"Discovered {len(sorted_test_files)} test files:")
    for test_file in sorted_test_files:
        print(f"  - {test_file}")
    
    return sorted_test_files

def sort_test_files_by_dependency(test_files):
    """
    Sort test files by dependency order. Base classes should come first.
    """
    # Define priority order for common test file patterns
    priority_patterns = [
        ("base_test", 0),           # Base test class first
        ("test_base", 0),           # Alternative base test naming
        ("common", 1),              # Common utilities
        ("lib", 1),                 # Library files
        ("pkg", 1),                 # Package files
        ("sequence", 2),            # Sequence files
        ("env", 3),                 # Environment files
        ("test", 4),                # Regular test files
    ]
    
    def get_file_priority(filename):
        """Get priority for a test file based on naming patterns."""
        basename = os.path.basename(filename).lower()
        
        # Check for specific priority patterns
        for pattern, priority in priority_patterns:
            if pattern in basename:
                return priority
                
        # Default priority for unmatched files
        return 5
    
    def get_file_secondary_sort(filename):
        """Secondary sort criteria: alphabetical by filename."""
        return os.path.basename(filename).lower()
    
    # Sort by priority first, then alphabetically
    sorted_files = sorted(test_files, key=lambda x: (get_file_priority(x), get_file_secondary_sort(x)))
    
    return sorted_files

def dump_source_code(output_filename="ahb_vip_all.sv"):
    project_root = os.getcwd()

    # Files that belong inside the ahb_pkg and should be flattened
    package_files_to_flatten = {
        "ahb_types.svh": "src/ahb_types.svh",
        "ahb_config.svh": "src/ahb_config.svh",
        "ahb_sequence_item.svh": "src/ahb_sequence_item.svh",
        "ahb_burst_transaction.svh": "src/ahb_burst_transaction.svh",
        "ahb_single_write_sequence.svh": "src/ahb_single_write_sequence.svh",
        "ahb_single_read_sequence.svh": "src/ahb_single_read_sequence.svh",
        "ahb_write_read_verify_sequence.svh": "src/ahb_write_read_verify_sequence.svh",
        "ahb_incr4_write_read_sequence.svh": "src/ahb_incr4_write_read_sequence.svh",
        "ahb_sequencer.svh": "src/ahb_sequencer.svh",
        "ahb_driver.svh": "src/ahb_driver.svh",
        "ahb_monitor.svh": "src/ahb_monitor.svh",
        "ahb_coverage.svh": "src/ahb_coverage.svh",
        "ahb_agent.svh": "src/ahb_agent.svh",
        "ahb_scoreboard.svh": "src/ahb_scoreboard.svh",
        "ahb_env.svh": "src/ahb_env.svh",
    }

    # Read ahb_pkg.sv content
    ahb_pkg_path = os.path.join(project_root, "src/ahb_pkg.sv")
    ahb_pkg_content = ""
    try:
        with open(ahb_pkg_path, "r") as f:
            ahb_pkg_content = f.read()
    except Exception as e:
        print(f"Error reading ahb_pkg.sv: {e}")
        return

    # Assemble the new ahb_pkg content by flattening includes
    new_ahb_pkg_lines = []
    for line in ahb_pkg_content.splitlines():
        stripped_line = line.strip()
        if stripped_line.startswith("`include "):
            included_filename = stripped_line.split("`include ")[1].strip().replace("\"", "")
            if included_filename in package_files_to_flatten:
                full_path_to_include = os.path.join(project_root, package_files_to_flatten[included_filename])
                try:
                    with open(full_path_to_include, "r") as included_file:
                        content_to_add = included_file.read()
                        # Remove class/interface/package declarations and includes/imports from internal files
                        # as they will be wrapped by the main package
                        lines_to_add = content_to_add.splitlines()
                        filtered_lines_to_add = []
                        skip_until_end = None
                        
                        for sub_line in lines_to_add:
                            stripped_sub = sub_line.strip()
                            
                            # Handle skipping until end keyword
                            if skip_until_end:
                                if stripped_sub.startswith(skip_until_end):
                                    skip_until_end = None
                                continue
                            
                            # Skip unwanted declarations
                            if (stripped_sub.startswith("interface ") or
                                stripped_sub.startswith("package ") or
                                stripped_sub.startswith("`include") or
                                (stripped_sub.startswith("import ") and "uvm_pkg" not in stripped_sub)):
                                # For interface/package/module declarations, skip until end
                                if stripped_sub.startswith("interface "):
                                    skip_until_end = "endinterface"
                                elif stripped_sub.startswith("package "):
                                    skip_until_end = "endpackage"
                                elif stripped_sub.startswith("module "):
                                    skip_until_end = "endmodule"
                                continue
                            
                            filtered_lines_to_add.append(sub_line)
                        
                        if filtered_lines_to_add:
                            new_ahb_pkg_lines.append(f"  // --- Content from {included_filename} ---")
                            new_ahb_pkg_lines.extend(filtered_lines_to_add)
                            new_ahb_pkg_lines.append(f"  // --- End of {included_filename} ---")
                            new_ahb_pkg_lines.append("") # Add newline between internal files
                except Exception as e:
                    print(f"Error reading included file {full_path_to_include}: {e}")
            else:
                # Keep other `include statements (e.g., uvm_macros.svh)
                new_ahb_pkg_lines.append(line)
        else:
            # Keep all other lines (package declaration, import uvm_pkg::*, endpackage, etc.)
            new_ahb_pkg_lines.append(line)

    final_ahb_pkg_content = "\n".join(new_ahb_pkg_lines)

    # Discover test files
    test_files = discover_test_files(project_root)
    
    # Define the final order of files to dump
    final_dump_order = ["src/ahb_if.sv", "src/ahb_pkg.sv"]  # Interface and package first
    
    # Add all discovered test files
    final_dump_order.extend(test_files)
    
    # Add testbench top if it exists
    tb_candidates = ["tb_top.sv", "testbench_top.sv", "tb.sv", "top.sv"]
    tb_found = False
    for tb_name in tb_candidates:
        if os.path.exists(os.path.join(project_root, tb_name)):
            final_dump_order.append(tb_name)
            tb_found = True
            break
    
    if not tb_found:
        print("Warning: No testbench top file found")

    print(f"\nFile compilation order:")
    for i, file_path in enumerate(final_dump_order, 1):
        print(f"  {i:2d}. {file_path}")

    with open(output_filename, "w") as outfile:
        # Write header
        outfile.write("// ========================================\n")
        outfile.write("// Flattened SystemVerilog AHB VIP Package\n")
        outfile.write("// Generated automatically - do not edit\n")
        outfile.write("// ========================================\n\n")
        
        for relative_path in final_dump_order:
            if relative_path == "src/ahb_pkg.sv":
                outfile.write(f"// --- Start of file: {relative_path} (flattened) ---" + "\n")
                outfile.write(final_ahb_pkg_content)
                outfile.write(f"// --- End of file: {relative_path} (flattened) ---" + "\n\n")
            else:
                full_path = os.path.join(project_root, relative_path)
                if not os.path.exists(full_path):
                    print(f"Warning: File not found - {full_path}. Skipping." + "\n")
                    continue

                outfile.write(f"// --- Start of file: {relative_path} ---" + "\n")
                try:
                    with open(full_path, "r") as infile:
                        content = infile.read()
                        outfile.write(content)
                        outfile.write("\n") # Ensure a newline between files
                except Exception as e:
                    print(f"Error reading file {full_path}: {e}" + "\n")
                outfile.write(f"// --- End of file: {relative_path} ---" + "\n\n")

    print(f"Successfully dumped all source codes into {output_filename}" + "\n")

if __name__ == "__main__":
    dump_source_code()
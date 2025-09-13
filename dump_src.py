import os

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
        "ahb_agent.svh": "src/ahb_agent.svh",
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
                        for sub_line in lines_to_add:
                            if not (sub_line.strip().startswith("interface") or
                                    sub_line.strip().startswith("package") or
                                    sub_line.strip().startswith("`include") or
                                    sub_line.strip().startswith("import")):
                                filtered_lines_to_add.append(sub_line)
                        new_ahb_pkg_lines.append("\n".join(filtered_lines_to_add))
                        new_ahb_pkg_lines.append("\n") # Add newline between internal files
                except Exception as e:
                    print(f"Error reading included file {full_path_to_include}: {e}")
            else:
                # Keep other `include statements (e.g., uvm_macros.svh)
                new_ahb_pkg_lines.append(line)
        else:
            # Keep all other lines (package declaration, import uvm_pkg::*, endpackage, etc.)
            new_ahb_pkg_lines.append(line)

    final_ahb_pkg_content = "\n".join(new_ahb_pkg_lines)

    # Define the final order of files to dump
    final_dump_order = [
        "src/ahb_if.sv", # Interface first
        "src/ahb_pkg.sv", # Then the flattened package
        "tests/base_test.sv", # Testbench
        "tb_top.sv", # Finally the top-level testbench module
    ]

    with open(output_filename, "w") as outfile:
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

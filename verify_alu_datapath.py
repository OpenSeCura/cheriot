#!/usr/bin/env python3
"""
Formal Architectural Invariant Verifier for CHERIoT ALU Datapath Specification (AluLatest.v)
Written from scratch to verify all 6 formal architectural invariants.
"""

import re
import sys

def parse_alu_spec(file_path):
    with open(file_path, "r") as f:
        content = f.read()

    # Section 1: 1. INSTRUCTION GROUPS
    sec1_match = re.search(r"1\.\s+INSTRUCTION GROUPS\s*[-=]*\n(.*?)-------------------------------------------------------------------------------", content, re.DOTALL)
    # Section 2: 2. FUNCTIONAL UNIT/RESOURCE MAPPING (stops strictly at comment end `*)`)
    sec2_match = re.search(r"2\.\s+FUNCTIONAL UNIT/RESOURCE MAPPING\s*[-=]*\n(.*?)\*\)", content, re.DOTALL)

    if not sec1_match or not sec2_match:
        print("ERROR: Could not locate Section 1 or Section 2 in AluLatest.v")
        sys.exit(1)

    sec1_text = sec1_match.group(1)
    sec2_text = sec2_match.group(1)

    # -------------------------------------------------------------------------
    # Parse Section 1: Extract InstGroups
    # -------------------------------------------------------------------------
    section1_groups = set()
    raw_sec1_blocks = re.split(r"\n\n+", sec1_text)
    for block in raw_sec1_blocks:
        lines = [line.strip() for line in block.split("\n") if line.strip()]
        if not lines:
            continue
        header = lines[0]
        if header.startswith("Immediate") or header.startswith("Miscellaneous") or header.startswith("-") or header.startswith("*") or ":" in header:
            continue
        
        # Handle slash-separated headers like AuiCgp/AuiPcc
        sub_headers = [h.strip() for h in header.split("/") if h.strip()]
        for h in sub_headers:
            if re.match(r"^[A-Z][A-Za-z0-9_]*$", h) and h not in ["Immediate", "Miscellaneous"]:
                section1_groups.add(h)

    # -------------------------------------------------------------------------
    # Parse Section 2: Functional Units & Writeback MUXes
    # -------------------------------------------------------------------------
    s2_blocks = []
    current_b = []
    for line in sec2_text.split("\n"):
        if line.strip() and not line.startswith(" ") and ":" in line and not line.strip().startswith("-"):
            if current_b:
                s2_blocks.append("\n".join(current_b))
                current_b = []
        current_b.append(line)
    if current_b:
        s2_blocks.append("\n".join(current_b))

    wb_destinations = {"Reg.addr", "Reg.tag", "Reg.ecap", "NewPcc.tag", "NewPcc.ecap", "NewPcc.addr",
                       "NewSpecial.tag", "NewSpecial.ecap", "NewSpecial.addr", "Exception",
                       "LoadPostProcess", "BranchTaken", "NewInterruptStatus"}

    unit_ports = {}
    unit_options = {}
    s2_groups_found = set()
    s2_all_blocks = []

    for block in s2_blocks:
        lines = block.split("\n")
        header = lines[0].split(":")[0].strip()
        if not header:
            continue

        s2_all_blocks.append(block)
        unit_ports[header] = {}
        unit_options[header] = []

        is_wb = header in wb_destinations or any(header.startswith(p) for p in ["Reg.", "NewPcc.", "NewSpecial."])

        if is_wb:
            full_rest = block[block.find(":") + 1:].strip()
            unit_ports[header]["out"] = []
            matches = re.findall(r"([^(),]+?)\s*\(([^)]+)\)", full_rest)
            
            if matches:
                explicit_grps = set()
                parsed_matches = []
                for src_expr, paren_content in matches:
                    src_clean = re.sub(r"\bIF\s+!?Compressed\b", "", src_expr, flags=re.IGNORECASE).strip(", ")
                    grps = extract_groups_from_paren(paren_content, section1_groups)
                    s2_groups_found.update(grps)
                    
                    if "all" in paren_content:
                        s2_groups_found.update(section1_groups)
                        parsed_matches.append((src_clean, "all", section1_groups))
                    elif "others" in paren_content:
                        parsed_matches.append((src_clean, "others", grps))
                    else:
                        explicit_grps.update(grps)
                        parsed_matches.append((src_clean, "explicit", grps))

                others_grps = section1_groups - explicit_grps
                for src_clean, mtype, grps in parsed_matches:
                    if mtype == "all":
                        eff_grps = section1_groups
                    elif mtype == "others":
                        eff_grps = others_grps | grps
                        s2_groups_found.update(eff_grps)
                    else:
                        eff_grps = grps

                    if eff_grps:
                        unit_ports[header]["out"].append((src_clean, eff_grps))

                # Check for sub-unit references inside paren_content (specifically ANDed with ComparatorGeneral.cond)
                for src_expr, paren_content in matches:
                    if "ComparatorGeneral" in paren_content:
                        cg_grps = set()
                        for part in paren_content.split(","):
                            if "ComparatorGeneral" in part:
                                cg_grps.update(extract_groups_from_paren(part, section1_groups))
                        if cg_grps:
                            unit_ports[header]["out"].append(("ComparatorGeneral.cond", cg_grps))
            elif full_rest.strip():
                src_clean = full_rest.strip()
                if header == "BranchTaken" and "ComparatorGeneral" in src_clean:
                    eff_grps = {"Branch"}
                    s2_groups_found.update(eff_grps)
                    unit_ports[header]["out"].append((src_clean, eff_grps))
                else:
                    unit_ports[header]["out"].append((src_clean, set()))
        else:
            # Functional Unit block
            field_lines = []
            last_was_option = False
            for line in lines[1:]:
                line_str = line.strip()
                if not line_str:
                    continue
                if line_str.startswith("-"):
                    unit_options[header].append(line_str)
                    last_was_option = True
                    continue
                if ":" in line_str and line.startswith("  ") and not line.startswith("    "):
                    field_lines.append(line_str)
                    last_was_option = False
                elif last_was_option and unit_options[header]:
                    unit_options[header][-1] += " " + line_str
                elif field_lines:
                    field_lines[-1] += " " + line_str

            for line in field_lines:
                port_name = line.split(":")[0].strip()
                if port_name in ["Outputs", "Can cause exceptions", "Functional Units"]:
                    continue

                rest = line[line.find(":") + 1:].strip()
                if port_name not in unit_ports[header]:
                    unit_ports[header][port_name] = []

                matches = re.findall(r"([^(),]+?)\s*\(([^)]+)\)", rest)
                explicit_grps = set()
                parsed_matches = []
                for src_expr, paren_content in matches:
                    src_clean = re.sub(r"\bIF\s+!?Compressed\b", "", src_expr, flags=re.IGNORECASE).strip(", ")
                    grps = extract_groups_from_paren(paren_content, section1_groups)
                    s2_groups_found.update(grps)

                    if "all" in paren_content:
                        s2_groups_found.update(section1_groups)
                        parsed_matches.append((src_clean, "all", section1_groups))
                    elif "others" in paren_content:
                        parsed_matches.append((src_clean, "others", grps))
                    else:
                        explicit_grps.update(grps)
                        parsed_matches.append((src_clean, "explicit", grps))

                others_grps = section1_groups - explicit_grps
                for src_clean, mtype, grps in parsed_matches:
                    if mtype == "all":
                        eff_grps = section1_groups
                    elif mtype == "others":
                        eff_grps = others_grps | grps
                        s2_groups_found.update(eff_grps)
                    else:
                        eff_grps = grps

                    if eff_grps:
                        unit_ports[header][port_name].append((src_clean, eff_grps))

    return section1_groups, s2_groups_found, unit_ports, unit_options, wb_destinations, s2_all_blocks

def extract_groups_from_paren(paren_text, valid_groups):
    found = set()
    tokens = re.findall(r"\b[A-Za-z0-9_]+\b", paren_text)
    for t in tokens:
        if t in valid_groups:
            found.add(t)
    return found

# =============================================================================
# MAIN VERIFICATION FUNCTION
# =============================================================================
def main():
    spec_path = "AluLatest.v"
    section1_groups, s2_groups_found, unit_ports, unit_options, wb_destinations, s2_all_blocks = parse_alu_spec(spec_path)

    print("=" * 80)
    print(" FORMAL ARCHITECTURAL INVARIANT VERIFIER FOR CHERIOT ALU DATAPATH (AluLatest.v)")
    print("=" * 80)

    # -------------------------------------------------------------------------
    # INVARIANT 1: Bi-directional Completeness
    # -------------------------------------------------------------------------
    print("\n" + "-" * 80)
    print("INVARIANT 1: BI-DIRECTIONAL COMPLETENESS")
    print("  a) Every InstGroup defined in Section 1 MUST be covered in Section 2.")
    print("  b) Every InstGroup referenced in Section 2 MUST be defined in Section 1.")
    print("-" * 80)

    inv1_failed = False
    missing_in_s2 = section1_groups - s2_groups_found
    if missing_in_s2:
        print(f"  [FAIL] InstGroups defined in Section 1 but missing in Section 2: {sorted(list(missing_in_s2))}")
        inv1_failed = True
    
    extra_in_s2 = s2_groups_found - section1_groups
    if extra_in_s2:
        print(f"  [FAIL] InstGroups in Section 2 not defined in Section 1: {sorted(list(extra_in_s2))}")
        inv1_failed = True

    if not inv1_failed:
        print(f"  [PASS] All {len(section1_groups)} instruction groups match 100% bi-directionally between Section 1 and Section 2.")

    # -------------------------------------------------------------------------
    # INVARIANT 2: Path Reachability to Writeback MUXes
    # -------------------------------------------------------------------------
    print("\n" + "-" * 80)
    print("INVARIANT 2: PATH REACHABILITY TO WRITEBACK MUXES")
    print("  Every instruction group MUST have a valid dataflow path terminating at a writeback MUX.")
    print("-" * 80)

    inv2_failed = False
    for g in sorted(list(section1_groups)):
        active_units = set()
        wb_reached = set()

        for unit_name, ports in unit_ports.items():
            is_wb = unit_name in wb_destinations or any(unit_name.startswith(p) for p in ["Reg.", "NewPcc.", "NewSpecial."])
            for port_name, src_tuples in ports.items():
                for src_expr, grps in src_tuples:
                    if g in grps:
                        if is_wb:
                            wb_reached.add(unit_name)
                        else:
                            active_units.add(unit_name)

        if not wb_reached:
            print(f"  [FAIL] InstGroup '{g}' has NO reachability path to any writeback MUX!")
            inv2_failed = True
        else:
            units_str = f"[{', '.join(sorted(list(active_units)))}]" if active_units else "[None (Direct pass-through)]"
            wb_str = f"[{', '.join(sorted(list(wb_reached)))}]"
            print(f"  [PASS] {g:<14} -> Active Units: {units_str}")
            print(f"                       -> Terminates at: {wb_str}")

    if not inv2_failed:
        print("\n  [PASS] 100% of instruction groups successfully establish valid paths to writeback MUXes.")

    # -------------------------------------------------------------------------
    # INVARIANT 3: Strict Signal Typing & Syntax Validation
    # -------------------------------------------------------------------------
    print("\n" + "-" * 80)
    print("INVARIANT 3: STRICT SIGNAL TYPING (Syntax Validation)")
    print("  Parenthesis content MUST contain only valid InstGroups, 'all', 'others', or allowed qualifiers.")
    print("  Option lines (- ...) permit '(when INST1/INST2/...)'.")
    print("  Outputs: fields permit documentation comments in parenthesis.")
    print("-" * 80)

    inv3_failed = False
    valid_elements = section1_groups | {"others", "all"}

    for block in s2_all_blocks:
        header = block.split(":")[0].strip()
        lines = block.split("\n")

        in_outputs_field = False
        for line in lines[1:]:
            line_str = line.strip()
            if not line_str:
                continue

            if line.startswith("  ") and not line.startswith("    ") and ":" in line_str:
                field_name = line_str.split(":")[0].strip()
                if field_name in ["Outputs", "Can cause exceptions", "Functional Units"]:
                    in_outputs_field = True
                else:
                    in_outputs_field = False

            if in_outputs_field or line_str.startswith("-") or (line.startswith("    ") and not ":" in line_str):
                continue
            else:
                matches = re.findall(r"\(([^)]+)\)", line_str)
                for paren_content in matches:
                    p_clean = re.sub(r"\bIF\s+!?Compressed\b", "", paren_content, flags=re.IGNORECASE)
                    p_clean = re.sub(r"\bBranch\s*&\s*!?ComparatorGeneral\.cond\b", "", p_clean, flags=re.IGNORECASE)
                    p_clean = re.sub(r"&\s*!?isImm\b", "", p_clean, flags=re.IGNORECASE).strip()

                    tokens = [t.strip() for t in p_clean.split(",") if t.strip()]
                    for t in tokens:
                        if t not in valid_elements and not t.isdigit():
                            print(f"  [FAIL] Unit '{header}' entry contains invalid selector component '{t}' in '({paren_content})'")
                            inv3_failed = True

    if not inv3_failed:
        print("  [PASS] All multiplexer table entries and unit option specifiers strictly conform to syntax rules.")

    # -------------------------------------------------------------------------
    # INVARIANT 4: Upstream Input Port Completeness
    # -------------------------------------------------------------------------
    print("\n" + "-" * 80)
    print("INVARIANT 4: UPSTREAM INPUT PORT COMPLETENESS")
    print("  If unit B consumes unit A for group G, unit A MUST have input selectors for group G on ALL its input ports.")
    print("-" * 80)

    inv4_failed = False
    functional_units = {u for u in unit_ports if u not in wb_destinations and not any(u.startswith(p) for p in ["Reg.", "NewPcc.", "NewSpecial."])}

    for unit_b, ports_b in unit_ports.items():
        for port_b, src_list in ports_b.items():
            for src_expr, grps_b in src_list:
                unit_a = src_expr.split(".")[0].strip()
                if unit_a in functional_units:
                    ports_a = unit_ports[unit_a]
                    for g in grps_b:
                        for port_a, src_list_a in ports_a.items():
                            driven = any(g in grps_a for _, grps_a in src_list_a)
                            if not driven:
                                print(f"  [FAIL] Unit '{unit_b}' consumes '{unit_a}' for Group '{g}', but '{unit_a}' input port '{port_a}' has NO selector for Group '{g}'!")
                                inv4_failed = True

    if not inv4_failed:
        print("  [PASS] All functional unit dependencies are 100% complete across all input ports.")

    # -------------------------------------------------------------------------
    # INVARIANT 5: Intra-Unit Port Coverage Completeness
    # -------------------------------------------------------------------------
    print("\n" + "-" * 80)
    print("INVARIANT 5: INTRA-UNIT PORT COVERAGE COMPLETENESS")
    print("  If group G selects an input to unit A, G MUST select an input for EVERY required input port of unit A.")
    print("-" * 80)

    inv5_failed = False
    for unit_name in functional_units:
        ports = unit_ports[unit_name]
        if not ports:
            continue
        driven_groups = set()
        for port_name, src_list in ports.items():
            for _, grps in src_list:
                driven_groups.update(grps)

        for g in driven_groups:
            for port_name, src_list in ports.items():
                driven = any(g in grps for _, grps in src_list)
                if not driven:
                    print(f"  [FAIL] InstGroup '{g}' drives Unit '{unit_name}', but input port '{port_name}' has NO selector for InstGroup '{g}'!")
                    inv5_failed = True

    if not inv5_failed:
        print("  [PASS] Every active unit port is 100% fully driven across all inputs for each selected instruction group.")

    # -------------------------------------------------------------------------
    # INVARIANT 6: Downstream Consumption Completeness
    # -------------------------------------------------------------------------
    print("\n" + "-" * 80)
    print("INVARIANT 6: DOWNSTREAM CONSUMPTION COMPLETENESS")
    print("  If group G selects inputs for unit A, unit A MUST be consumed downstream under group G.")
    print("-" * 80)

    inv6_failed = False
    for unit_a in functional_units:
        ports_a = unit_ports[unit_a]
        if not ports_a:
            continue
        driven_groups = set()
        for port_name, src_list in ports_a.items():
            for _, grps in src_list:
                driven_groups.update(grps)

        for g in driven_groups:
            consumed = False
            for unit_b, ports_b in unit_ports.items():
                if unit_b == unit_a:
                    continue
                for port_b, src_list_b in ports_b.items():
                    for src_expr, grps_b in src_list_b:
                        if src_expr.split(".")[0].strip() == unit_a and g in grps_b:
                            consumed = True
                            break
                    if consumed:
                        break
                if consumed:
                    break

            if not consumed:
                print(f"  [FAIL] InstGroup '{g}' drives Unit '{unit_a}', but Unit '{unit_a}' output is NEVER consumed under InstGroup '{g}' in any downstream unit or writeback MUX!")
                inv6_failed = True

    if not inv6_failed:
        print("  [PASS] All functional unit outputs are 100% consumed downstream for every active instruction group.")

    # -------------------------------------------------------------------------
    # SUMMARY
    # -------------------------------------------------------------------------
    all_failed = inv1_failed or inv2_failed or inv3_failed or inv4_failed or inv5_failed or inv6_failed

    print("\n" + "=" * 80)
    if not all_failed:
        print(" [+] SUMMARY: ALL 6 FORMAL ARCHITECTURAL INVARIANTS SATISFIED 100%")
    else:
        print(" [-] SUMMARY: VERIFICATION FAILED - ONE OR MORE INVARIANTS VIOLATED")
    print("=" * 80)

if __name__ == "__main__":
    main()

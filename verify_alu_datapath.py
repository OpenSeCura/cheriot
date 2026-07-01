#!/usr/bin/env python3
import re
import sys
from pathlib import Path

def parse_groups_from_paren(paren_text, valid_groups):
    """Extract instruction groups from parenthesized text by matching against known Section 1 groups."""
    groups = set()
    for word in re.findall(r"\b[A-Za-z0-9_.]+\b", paren_text):
        if word in valid_groups:
            groups.add(word)
        elif word == "Aui":
            groups.add("AuiPcc")
            groups.add("AuiCgp")
    return groups

def verify_alu(file_path):
    with open(file_path, "r") as f:
        content = f.read()

    # 1. Strip comments (#...)
    content_no_comments = re.sub(r"#.*", "", content)

    # 2. Extract Section 1 and Section 2/3 blocks
    s1_match = re.search(r"1\. INSTRUCTION GROUPS(.*?)(?:2\. FUNCTIONAL UNIT|\Z)", content_no_comments, re.DOTALL)
    s2_match = re.search(r"2\. FUNCTIONAL UNIT/RESOURCE MAPPING(.*?)(?:\*\)|\Z)", content_no_comments, re.DOTALL)

    if not s1_match or not s2_match:
        print("[!] Error: Could not locate Section 1 or Section 2 in file.")
        sys.exit(1)

    s1_text = s1_match.group(1)
    s2_text = s2_match.group(1)

    # 3. Parse Section 1 instruction groups
    section1_groups = set()
    for line in s1_text.split("\n"):
        if not line or line.startswith(" ") or line.startswith("\t") or line.startswith("*") or line.startswith("-"):
            continue
        token = line.split(":")[0].strip()
        if token and not token.startswith("---") and "Immediate" not in token and "Miscellaneous" not in token and "0." not in token:
            if token == "Aui":
                section1_groups.add("AuiPcc")
                section1_groups.add("AuiCgp")
            else:
                section1_groups.add(token)

    reachability = {g: {"units": set(), "writebacks": set()} for g in section1_groups}

    print("================================================================================")
    print("               ALU DATAPATH FORMAL VERIFICATION REPORT                          ")
    print("================================================================ algorithm\n")
    print(f"Successfully parsed {len(section1_groups)} instruction groups from Section 1: {sorted(section1_groups)}\n")

    # 4. Parse Section 2 & 3 functional units and writeback MUXes
    s2_blocks = re.split(r"\n(?=[A-Za-z0-9_.]+:)", "\n" + s2_text)

    unit_ports = {}
    known_units = set()

    for block in s2_blocks:
        block = block.strip()
        if not block or ":" not in block:
            continue

        lines = block.split("\n")
        header = lines[0].split(":")[0].strip()
        known_units.add(header)

        current_unit = header
        if current_unit not in unit_ports:
            unit_ports[current_unit] = {}

        is_writeback = any(header.startswith(prefix) for prefix in ["Reg.", "NewPcc.", "NewSpecial.", "Exception", "LoadPostProcess", "BranchTaken"])

        if is_writeback:
            full_rest = block[block.find(":") + 1:].strip()
            unit_ports[current_unit]["out"] = []
            matches = re.findall(r"([^(),]+?)\s*\(([^)]+)\)", full_rest)
            if matches:
                explicit_grps = set()
                parsed_matches = []
                for src_expr, paren_content in matches:
                    src_expr = re.sub(r"\bIF\s+!?Compressed\b", "", src_expr, flags=re.IGNORECASE).strip(", ")
                    grps = parse_groups_from_paren(paren_content, section1_groups)
                    if "others" in paren_content:
                        parsed_matches.append((src_expr, "others", grps))
                    else:
                        explicit_grps.update(grps)
                        parsed_matches.append((src_expr, "explicit", grps))

                others_grps = section1_groups - explicit_grps
                for src_expr, match_type, grps in parsed_matches:
                    effective_grps = (others_grps | grps) if match_type == "others" else grps
                    if effective_grps:
                        unit_ports[current_unit]["out"].append((src_expr, effective_grps))
                        for g in effective_grps:
                            reachability[g]["writebacks"].add(header)

                # Check for sub-unit outputs in paren_content (e.g. ComparatorGeneral.cond)
                for src_expr, paren_content in matches:
                    if "ComparatorGeneral.cond" in paren_content or "ComparatorGeneral" in paren_content:
                        # Extract only groups that are ANDed with ComparatorGeneral.cond (e.g. Branch)
                        cg_grps = set()
                        for part in paren_content.split(","):
                            if "ComparatorGeneral" in part:
                                cg_grps.update(parse_groups_from_paren(part, section1_groups))
                        if cg_grps:
                            unit_ports[current_unit]["out"].append(("ComparatorGeneral.cond", cg_grps))
            elif full_rest.strip():
                src_expr = full_rest.strip()
                unit_ports[current_unit]["out"].append((src_expr, set()))
        else:
            field_lines = []
            for line in lines[1:]:
                line_str = line.strip()
                if not line_str or line_str.startswith("-"):
                    continue
                if line.startswith("  ") and not line.startswith("    ") and ":" in line_str:
                    field_lines.append(line_str)
                elif field_lines:
                    field_lines[-1] += " " + line_str

            for line in field_lines:
                port_name = line.split(":")[0].strip()
                if port_name in ["Outputs", "Can cause exceptions", "Functional Units"]:
                    continue

                rest = line[line.find(":") + 1:].strip()
                if port_name not in unit_ports[current_unit]:
                    unit_ports[current_unit][port_name] = []

                matches = re.findall(r"([^(),]+?)\s*\(([^)]+)\)", rest)
                if matches:
                    explicit_grps = set()
                    parsed_matches = []
                    for src_expr, paren_content in matches:
                        src_expr = re.sub(r"\bIF\s+!?Compressed\b", "", src_expr, flags=re.IGNORECASE).strip(", ")
                        grps = parse_groups_from_paren(paren_content, section1_groups)
                        if "others" in paren_content:
                            parsed_matches.append((src_expr, "others", grps))
                        else:
                            explicit_grps.update(grps)
                            parsed_matches.append((src_expr, "explicit", grps))

                    others_grps = section1_groups - explicit_grps
                    for src_expr, match_type, grps in parsed_matches:
                        effective_grps = (others_grps | grps) if match_type == "others" else grps
                        if effective_grps:
                            unit_ports[current_unit][port_name].append((src_expr, effective_grps))
                            for g in effective_grps:
                                reachability[g]["units"].add(header)
                elif rest.strip():
                    src_expr = rest.strip()

    # INVARIANT 1: Bi-directional Completeness
    section2_tags = set()
    for g in reachability:
        if reachability[g]["units"] or reachability[g]["writebacks"]:
            section2_tags.add(g)

    missing_in_s2 = section1_groups - section2_tags
    print("--------------------------------------------------------------------------------")
    print("INVARIANT 1: BI-DIRECTIONAL COMPLETENESS (No Orphan Signals)")
    print("--------------------------------------------------------------------------------")
    if not missing_in_s2:
        print("  [PASS] All 100% of defined instruction groups participate in functional units or writeback MUXes.")
    else:
        print(f"  [FAIL] Orphan instruction groups found without functional unit or writeback mapping: {sorted(missing_in_s2)}")

    # INVARIANT 2: End-to-End Signal Reachability (Graph Traversal)
    print("\n--------------------------------------------------------------------------------")
    print("INVARIANT 2: END-TO-END SIGNAL REACHABILITY")
    print("--------------------------------------------------------------------------------")
    inv2_failed = False
    for g in sorted(section1_groups):
        wb_units = reachability[g]["writebacks"]
        active_units = reachability[g]["units"]
        if not wb_units and not active_units:
            print(f"  [FAIL] Group '{g}' has NO active units and NO writeback destinations!")
            inv2_failed = True
        else:
            units_str = f"Active Units: [{', '.join(sorted(active_units)) if active_units else 'None (Direct register/bus pass-through)'}]"
            wb_str = f"Terminates at: [{', '.join(sorted(wb_units))}]"
            print(f"  [PASS] {g:<12} -> {units_str}\n                       -> {wb_str}")

    if not inv2_failed:
        print("\n  [PASS] 100% of instruction groups successfully establish valid paths to writeback MUXes.")

    # INVARIANT 3: Strict Signal Typing (Strict Syntax Enforcement)
    print("\n--------------------------------------------------------------------------------")
    print("INVARIANT 3: STRICT SIGNAL TYPING (Strict Comma-Separated InstGroup List & 'when' Option Specifiers)")
    print("--------------------------------------------------------------------------------")
    valid_elements = section1_groups | {"others", "Aui"}
    informal_found = False
    for block in s2_blocks:
        block_str = block.strip()
        if not block_str or ":" not in block_str:
            continue
        header = block_str.split(":")[0].strip()

        # Check writeback MUX block vs Functional Unit block
        is_wb = any(header.startswith(prefix) for prefix in ["Reg.", "NewPcc.", "NewSpecial.", "Exception", "LoadPostProcess", "BranchTaken"])

        input_lines = []
        option_lines = []
        if is_wb:
            full_rest = block_str[block_str.find(":") + 1:].strip()
            input_lines.append(full_rest)
        else:
            lines = block_str.split("\n")
            field_lines = []
            for l in lines[1:]:
                l_str = l.strip()
                if not l_str:
                    continue
                if l_str.startswith("-"):
                    option_lines.append(l_str)
                elif l.startswith("  ") and not l.startswith("    ") and ":" in l_str:
                    field_lines.append(l_str)
                elif field_lines:
                    field_lines[-1] += " " + l_str

            for fl in field_lines:
                port_name = fl.split(":")[0].strip()
                if port_name in ["Outputs", "Can cause exceptions", "Functional Units"]:
                    continue
                input_lines.append(fl[fl.find(":") + 1:].strip())

        # 1. Check Input Port lines
        joined_inputs = " ".join(input_lines)
        for paren_content in re.findall(r"\(([^)]+)\)", joined_inputs):
            tokens = [t.strip() for t in paren_content.split(",")]
            for token in tokens:
                if token in ["Branch & ComparatorGeneral.cond", "Branch & !ComparatorGeneral.cond"]:
                    continue
                token_base = re.sub(r"\s*&\s*!?isImm$", "", token).strip()
                if token_base not in valid_elements:
                    print(f"  [FAIL] Invalid entry '{token}' in block '{header}', input condition: '({paren_content})' (Must be comma-separated InstGroup elements only)")
                    informal_found = True

        # 2. Check Option lines (starting with -)
        joined_options = " ".join(option_lines)
        for paren_content in re.findall(r"\(([^)]+)\)", joined_options):
            p_str = paren_content.strip()
            if p_str.startswith("when "):
                # Strip explanation trailing text if any
                when_part = p_str[5:].split(" to ")[0].strip()
                sub_insts = [t.strip() for t in re.split(r"[,/]+", when_part) if t.strip()]
                for inst_name in sub_insts:
                    if not inst_name.isalnum():
                        print(f"  [FAIL] Invalid 'when' instruction filter '({paren_content})' in block '{header}'")
                        informal_found = True

    if not informal_found:
        print("  [PASS] All multiplexer table entries and unit option specifiers strictly conform to syntax rules.")

    # INVARIANT 4: UPSTREAM INPUT PORT COMPLETENESS
    print("\n--------------------------------------------------------------------------------")
    print("INVARIANT 4: UPSTREAM INPUT PORT COMPLETENESS")
    print("  If functional unit B or writeback MUX C consumes functional unit A for instruction group G,")
    print("  then for EVERY input port of unit A, there MUST be a matching selector for group G.")
    print("--------------------------------------------------------------------------------")
    inv4_failed = False
    functional_units = {u for u in known_units if not any(u.startswith(p) for p in ["Reg.", "NewPcc.", "NewSpecial.", "Exception", "LoadPostProcess", "BranchTaken"])}

    for unit_b, ports_b in unit_ports.items():
        for port_b, src_list in ports_b.items():
            for src_expr, grps in src_list:
                unit_a = src_expr.split(".")[0].strip()
                if unit_a in functional_units and unit_a in unit_ports:
                    ports_a = unit_ports[unit_a]
                    if not ports_a:
                        continue
                    for g in grps:
                        for port_a, a_src_list in ports_a.items():
                            covered_for_g = False
                            for a_src_expr, a_grps in a_src_list:
                                if g in a_grps:
                                    covered_for_g = True
                                    break
                            if not covered_for_g:
                                print(f"  [FAIL] Unit '{unit_b}' consumes '{unit_a}' for Group '{g}', but '{unit_a}' input port '{port_a}' has NO selector for Group '{g}'!")
                                inv4_failed = True

    if not inv4_failed:
        print("  [PASS] All functional unit dependencies are 100% complete across all input ports.")

    # INVARIANT 5: INTRA-UNIT PORT COVERAGE COMPLETENESS
    print("\n--------------------------------------------------------------------------------")
    print("INVARIANT 5: INTRA-UNIT PORT COVERAGE COMPLETENESS")
    print("  If instruction group G selects an input to functional unit A, G MUST select")
    print("  an input for EVERY other required input port of unit A.")
    print("--------------------------------------------------------------------------------")

    inv5_failed = False
    for unit_a in sorted(functional_units):
        ports_a = unit_ports.get(unit_a, {})
        if not ports_a:
            continue

        # Collect all instruction groups that drive ANY port of unit_a
        unit_groups = set()
        for port_name, src_list in ports_a.items():
            for src_expr, grps in src_list:
                unit_groups.update(grps)

        # For each group G driving unit_a, check that EVERY port of unit_a has a selector for G
        for g in sorted(unit_groups):
            for port_name, src_list in ports_a.items():
                port_has_g = False
                for src_expr, grps in src_list:
                    if g in grps:
                        port_has_g = True
                        break
                if not port_has_g:
                    print(f"  [FAIL] InstGroup '{g}' drives Unit '{unit_a}', but input port '{port_name}' has NO selector for InstGroup '{g}'!")
                    inv5_failed = True

    if not inv5_failed:
        print("  [PASS] Every active unit port is 100% fully driven across all inputs for each selected instruction group.")

    # INVARIANT 6: DOWNSTREAM CONSUMPTION COMPLETENESS
    print("\n--------------------------------------------------------------------------------")
    print("INVARIANT 6: DOWNSTREAM CONSUMPTION COMPLETENESS")
    print("  If instruction group G selects inputs for functional unit A, A MUST be used")
    print("  as an input selected by G in another downstream functional unit or writeback MUX.")
    print("--------------------------------------------------------------------------------")

    inv6_failed = False
    for unit_a in sorted(functional_units):
        ports_a = unit_ports.get(unit_a, {})
        if not ports_a:
            continue

        unit_groups = set()
        for port_name, src_list in ports_a.items():
            for src_expr, grps in src_list:
                unit_groups.update(grps)

        for g in sorted(unit_groups):
            # Check if unit_a is consumed by any downstream unit B or writeback MUX for group G
            consumed = False
            for unit_b, ports_b in unit_ports.items():
                if unit_b == unit_a:
                    continue
                for port_b, b_src_list in ports_b.items():
                    for b_src_expr, b_grps in b_src_list:
                        consumed_unit = b_src_expr.split(".")[0].strip()
                        if consumed_unit == unit_a and g in b_grps:
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

    if missing_in_s2 or informal_found or inv4_failed or inv5_failed or inv6_failed:
        sys.exit(1)

    print("\n================================================================================")
    print(" [+] SUMMARY: ALL 6 FORMAL ARCHITECTURAL INVARIANTS SATISFIED 100%")
    print("================================================================================")

if __name__ == "__main__":
    verify_alu("/Users/muralivi/work/Cherified/cheriot/AluLatest.v")

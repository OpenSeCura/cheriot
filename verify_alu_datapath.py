#!/usr/bin/env python3
"""
Formal Architectural Invariant Verifier for CHERIoT ALU Datapath Specification (AluLatest.v)
Written to verify the 6 formal architectural invariants.
"""

import re
import sys

def parse_outputs_tree(s):
    tokens = [t.strip() for t in re.findall(r'\(|\)|\{|\}|,|OR|[a-zA-Z0-9_.]+', s) if t.strip()]
    pos = 0

    def parse_expr():
        return parse_comma_list()

    def parse_comma_list():
        nonlocal pos
        nodes = []
        nodes.append(parse_or_list())
        while pos < len(tokens) and tokens[pos] == ',':
            pos += 1
            nodes.append(parse_or_list())
        if len(nodes) == 1:
            return nodes[0]
        return {"tuple": nodes}

    def parse_or_list():
        nonlocal pos
        nodes = []
        nodes.append(parse_term())
        while pos < len(tokens) and tokens[pos] == 'OR':
            pos += 1
            nodes.append(parse_term())
        if len(nodes) == 1:
            return nodes[0]
        return {"options": nodes}

    def parse_term():
        nonlocal pos
        if pos >= len(tokens):
            return None
        
        t = tokens[pos]
        if t == '(':
            pos += 1
            node = parse_expr()
            if pos < len(tokens) and tokens[pos] == ')':
                pos += 1
            return node
        else:
            ident = t
            pos += 1
            if pos < len(tokens) and tokens[pos] == '{':
                pos += 1
                inner = parse_expr()
                if pos < len(tokens) and tokens[pos] == '}':
                    pos += 1
                return {"struct": ident, "fields": inner}
            return ident

    return parse_expr() if tokens else None

def get_all_fields_from_tree(node):
    fields = set()
    if isinstance(node, str):
        fields.add(node)
    elif isinstance(node, dict):
        if "tuple" in node:
            for item in node["tuple"]:
                fields.update(get_all_fields_from_tree(item))
        elif "options" in node:
            for item in node["options"]:
                fields.update(get_all_fields_from_tree(item))
        elif "struct" in node:
            fields.add(node["struct"])
            if "fields" in node and node["fields"]:
                fields.update(get_all_fields_from_tree(node["fields"]))
    elif isinstance(node, list):
        for item in node:
            fields.update(get_all_fields_from_tree(item))
    return fields


def parse_alu_latest(file_path):
    with open(file_path, "r") as f:
        content = f.read()

    sec1_match = re.search(r"1\.\s+INSTRUCTION GROUPS\s*[-=]*\n(.*?)-------------------------------------------------------------------------------", content, re.DOTALL)
    # Section 2 ends strictly at the end of the top comment `*)`
    sec2_match = re.search(r"2\.\s+FUNCTIONAL UNIT/RESOURCE MAPPING\s*[-=]*\n(.*?)\*\)", content, re.DOTALL)

    if not sec1_match or not sec2_match:
        print("ERROR: Could not locate Section 1 or Section 2 in Alu.v")
        sys.exit(1)

    sec1_text = sec1_match.group(1)
    sec2_text = sec2_match.group(1)

    # 1. SECTION 1: Extract InstGroup elements
    section1_groups = set()
    raw_sec1_blocks = re.split(r"\n\n+", sec1_text)
    for block in raw_sec1_blocks:
        lines = [line.strip() for line in block.split("\n") if line.strip()]
        if not lines:
            continue
        header = lines[0]
        if header.startswith("Immediate") or header.startswith("Miscellaneous") or header.startswith("-") or header.startswith("*") or ":" in header:
            continue
        sub_headers = [h.strip() for h in header.split("/") if h.strip()]
        for h in sub_headers:
            if re.match(r"^[A-Z][A-Za-z0-9_]*$", h) and h not in ["Immediate", "Miscellaneous"]:
                section1_groups.add(h)

    def extract_groups_from_paren(paren_text):
        found = set()
        p_clean = re.sub(r"\bIF\s+!?Compressed\b", "", paren_text, flags=re.IGNORECASE)
        p_clean = re.sub(r"&\s*!?isImm\b", "", p_clean, flags=re.IGNORECASE)
        p_clean = re.sub(r"\bwhen\s+[A-Z0-9_/.]+\b", "", p_clean, flags=re.IGNORECASE).strip()
        tokens = [t.strip() for t in p_clean.split(",") if t.strip()]
        for t in tokens:
            if t == "all":
                found.update(section1_groups)
            elif t == "others":
                pass
            elif t in section1_groups:
                found.add(t)
        return found

    units = {}
    writebacks = {}
    s2_groups_found = set()
    raw_selector_tokens = []

    blocks = re.split(r"\n\n+", sec2_text.strip())
    
    for block in blocks:
        lines = block.split("\n")
        header_line = lines[0].strip()
        
        if header_line.endswith(":"):
            header_raw = header_line[:-1].strip()
            unit_name = header_raw.split("(")[0].strip()
            is_mux = "(Mux)" in header_raw

            units[unit_name] = {
                "is_mux": is_mux,
                "outputs": [],
                "output_fields": set(),
                "ports": {}
            }

            port_lines = []
            curr_p = []
            outputs_str = ""
            in_outputs = False
            for line in lines[1:]:
                l_str = line.strip()
                if not l_str or l_str.startswith("-"):
                    continue
                if l_str.startswith("Outputs:"):
                    in_outputs = True
                    outputs_str += " " + l_str[len("Outputs:"):].strip()
                    continue
                
                if ":" in l_str and not l_str.startswith("(") and re.match(r"^[a-zA-Z0-9_.]+\s*:", l_str):
                    in_outputs = False
                    if curr_p:
                        port_lines.append(" ".join(curr_p))
                        curr_p = []
                
                if in_outputs:
                    outputs_str += " " + l_str
                else:
                    curr_p.append(l_str)
            if curr_p:
                port_lines.append(" ".join(curr_p))

            if outputs_str.strip():
                parsed_tree = parse_outputs_tree(outputs_str)
                units[unit_name]["outputs"] = parsed_tree
                units[unit_name]["output_fields"] = get_all_fields_from_tree(parsed_tree)

            for p_str in port_lines:
                if ":" not in p_str:
                    continue
                port_name = p_str.split(":")[0].strip()
                rest = p_str[p_str.find(":") + 1:].strip()
                units[unit_name]["ports"][port_name] = []

                matches = re.findall(r"([^(),]+?)\s*\(([^)]+)\)", rest)
                if matches:
                    explicit_grps = set()
                    parsed = []
                    for src_expr, paren in matches:
                        src_clean = re.sub(r"^.*?,\s*", "", src_expr).strip()
                        raw_selector_tokens.append((paren, rest))
                        grps = extract_groups_from_paren(paren)
                        s2_groups_found.update(grps)
                        if "all" in paren:
                            parsed.append((src_clean, "all", section1_groups))
                        elif "others" in paren:
                            parsed.append((src_clean, "others", grps))
                        else:
                            explicit_grps.update(grps)
                            parsed.append((src_clean, "explicit", grps))

                    others_grps = section1_groups - explicit_grps
                    for src_clean, mtype, grps in parsed:
                        if mtype == "all":
                            eff = section1_groups
                        elif mtype == "others":
                            eff = others_grps | grps
                        else:
                            eff = grps
                        units[unit_name]["ports"][port_name].append((src_clean, eff))
                elif rest:
                    units[unit_name]["ports"][port_name].append((rest, section1_groups))

        else:
            wb_joined_blocks = []
            curr_wb = []
            for l in lines:
                l_str = l.strip()
                if not l_str:
                    continue
                
                is_new_wb = (":" in l_str) or (l_str in units)
                if is_new_wb:
                    if curr_wb:
                        wb_joined_blocks.append(" ".join(curr_wb))
                        curr_wb = []
                curr_wb.append(l_str)
            if curr_wb:
                wb_joined_blocks.append(" ".join(curr_wb))

            for line_str in wb_joined_blocks:
                if ":" in line_str:
                    wb_name = line_str.split(":")[0].strip()
                    rest = line_str[line_str.find(":") + 1:].strip()
                    writebacks[wb_name] = []

                    matches = re.findall(r"([^(),]+?)\s*\(([^)]+)\)", rest)
                    if matches:
                        explicit_grps = set()
                        parsed = []
                        for src_expr, paren in matches:
                            src_clean = re.sub(r"^.*?,\s*", "", src_expr).strip()
                            raw_selector_tokens.append((paren, rest))
                            grps = extract_groups_from_paren(paren)
                            s2_groups_found.update(grps)
                            if "all" in paren:
                                parsed.append((src_clean, "all", section1_groups))
                            elif "others" in paren:
                                parsed.append((src_clean, "others", grps))
                            else:
                                explicit_grps.update(grps)
                                parsed.append((src_clean, "explicit", grps))

                        others_grps = section1_groups - explicit_grps
                        for src_clean, mtype, grps in parsed:
                            if mtype == "all":
                                eff = section1_groups
                            elif mtype == "others":
                                eff = others_grps | grps
                            else:
                                eff = grps
                            writebacks[wb_name].append((src_clean, eff))
                    elif rest:
                        writebacks[wb_name].append((rest, section1_groups))
                elif line_str in units:
                    sink_unit = line_str
                    driven_grps = set()
                    for _, src_list in units[sink_unit]["ports"].items():
                        for _, grps in src_list:
                            driven_grps.update(grps)
                    writebacks[sink_unit] = [(sink_unit, driven_grps)]
    return section1_groups, s2_groups_found, units, writebacks, raw_selector_tokens

def run_invariant_checks():
    spec_path = "Alu.v"
    section1_groups, s2_groups_found, units, writebacks, raw_selector_tokens = parse_alu_latest(spec_path)

    print("=" * 80)
    print(" FORMAL ARCHITECTURAL INVARIANT VERIFIER (Alu.v)")
    print("=" * 80)

    print("\n" + "-" * 80)
    print("INVARIANT 1:")
    print("  Every element in InstGroup defined in the instruction classification must be used by a functional unit or writeback, and every element of InstGroup used in the functional unit or writeback must have an instruction classification.")
    print("-" * 80)
    inv1_failed = False
    missing = section1_groups - s2_groups_found
    if missing:
        print(f"  [FAIL] InstGroups in classification but missing in mapping: {sorted(list(missing))}")
        inv1_failed = True
    extra = s2_groups_found - section1_groups
    if extra:
        print(f"  [FAIL] InstGroups in mapping but missing in classification: {sorted(list(extra))}")
        inv1_failed = True
    if not inv1_failed:
        print(f"  [PASS] Every element in InstGroup defined in the instruction classification is used by a functional unit or writeback, and vice-versa.")

    print("\n" + "-" * 80)
    print("INVARIANT 2:")
    print("  Every element in InstGroup must have a valid dataflow path through the functional units ending in at least one writeback destination.")
    print("-" * 80)
    inv2_failed = False
    for g in sorted(list(section1_groups)):
        reached_wb = set()
        for wb_name, src_list in writebacks.items():
            for src_expr, grps in src_list:
                if g in grps:
                    reached_wb.add(wb_name)
        if not reached_wb:
            print(f"  [FAIL] InstGroup '{g}' has NO dataflow path to any writeback destination!")
            inv2_failed = True
    if not inv2_failed:
        print("  [PASS] Every element in InstGroup has a valid dataflow path through the functional units ending in at least one writeback destination.")

    print("\n" + "-" * 80)
    print("INVARIANT 3:")
    print("  Every selector tag in parenthesis must be a valid element in InstGroup, all, others, or an explicit condition modifier (isImm, !isImm, IF Compressed, IF !Compressed, or when <sub-opcode>).")
    print("-" * 80)
    inv3_failed = False
    valid_elements = section1_groups | {"others", "all"}
    for paren, context_line in raw_selector_tokens:
        p_clean = re.sub(r"\bIF\s+!?Compressed\b", "", paren, flags=re.IGNORECASE)
        p_clean = re.sub(r"&\s*!?isImm\b", "", p_clean, flags=re.IGNORECASE)
        p_clean = re.sub(r"\bwhen\s+[A-Z0-9_/.]+\b", "", p_clean, flags=re.IGNORECASE).strip()
        tokens = [t.strip() for t in p_clean.split(",") if t.strip()]
        for t in tokens:
            if t not in valid_elements and not t.isdigit():
                print(f"  [FAIL] Entry contains invalid selector component '{t}' in '({paren})' on line: {context_line}")
                inv3_failed = True
    if not inv3_failed:
        print("  [PASS] All selector tags strictly conform to syntax rules.")

    print("\n" + "-" * 80)
    print("INVARIANT 4:")
    print("  If unit B consumes unit A for an element in InstGroup, unit A must have valid input selectors on one of its input ports for that element.")
    print("-" * 80)
    inv4_failed = False
    for u_name_b, u_info_b in units.items():
        for p_name_b, src_list_b in u_info_b["ports"].items():
            for src_expr, grps_b in src_list_b:
                unit_a = src_expr.split(".")[0].strip()
                if unit_a in units:
                    u_info_a = units[unit_a]
                    for g in grps_b:
                        driven_on_any_port = False
                        for p_name_a, src_list_a in u_info_a["ports"].items():
                            if any(g in grps_a for _, grps_a in src_list_a):
                                driven_on_any_port = True
                                break
                        if not driven_on_any_port:
                            print(f"  [FAIL] Unit '{u_name_b}' consumes '{unit_a}' for Group '{g}', but '{unit_a}' has NO input selector for Group '{g}' on any port!")
                            inv4_failed = True
    if not inv4_failed:
        print("  [PASS] If unit B consumes unit A for an element in InstGroup, unit A has valid input selectors on one of its input ports for that element.")

    print("\n" + "-" * 80)
    print("INVARIANT 5:")
    print("  If an element in InstGroup drives inputs into unit A, unit A's output must be consumed by a unit or writeback for that element.")
    print("-" * 80)
    inv5_failed = False
    for u_name_a, u_info_a in units.items():
        driven_groups = set()
        for p_name_a, src_list_a in u_info_a["ports"].items():
            for _, grps in src_list_a:
                driven_groups.update(grps)

        for g in driven_groups:
            consumed = False
            for u_name_b, u_info_b in units.items():
                if u_name_b == u_name_a:
                    continue
                for p_name_b, src_list_b in u_info_b["ports"].items():
                    for src_expr, grps_b in src_list_b:
                        if src_expr.split(".")[0].strip() == u_name_a and g in grps_b:
                            consumed = True
                            break
                    if consumed:
                        break
                if consumed:
                    break
            if not consumed:
                for wb_name, src_list_wb in writebacks.items():
                    for src_expr, grps_wb in src_list_wb:
                        if (src_expr.split(".")[0].strip() == u_name_a or wb_name == u_name_a) and g in grps_wb:
                            consumed = True
                            break
                    if consumed:
                        break
            if not consumed:
                print(f"  [FAIL] InstGroup '{g}' drives Unit '{u_name_a}', but Unit '{u_name_a}' output is NEVER consumed under InstGroup '{g}'!")
                inv5_failed = True
    if not inv5_failed:
        print("  [PASS] If an element in InstGroup drives inputs into unit A, unit A's output is consumed by a unit or writeback for that element.")

    print("\n" + "-" * 80)
    print("INVARIANT 6:")
    print("  If an element in InstGroup drives an input port of a non Mux unit A, that element must provide inputs for all required ports of non Mux unit A.")
    print("-" * 80)
    inv6_failed = False
    for u_name, u_info in units.items():
        if u_info["is_mux"]:
            continue
        ports = u_info["ports"]
        if not ports:
            continue
        driven_groups = set()
        for p_name, src_list in ports.items():
            for _, grps in src_list:
                driven_groups.update(grps)

        for g in driven_groups:
            for p_name, src_list in ports.items():
                driven = any(g in grps for _, grps in src_list)
                if not driven:
                    print(f"  [FAIL] InstGroup '{g}' drives non-Mux Unit '{u_name}', but input port '{p_name}' has NO selector for InstGroup '{g}'!")
                    inv6_failed = True
    if not inv6_failed:
        print("  [PASS] Every active non-Mux unit port is 100% fully driven across all inputs for each selected instruction group.")

    # INVARIANT 7
    print("\n" + "-" * 80)
    print("INVARIANT 7:")
    print("  If a unit or writeback consumes a sub-field 'Unit.field', 'field' must be declared in the Outputs of 'Unit'.")
    print("-" * 80)
    inv7_failed = False

    def check_field_references(context_name, src_expr):
        nonlocal inv7_failed
        dot_matches = re.findall(r"\b([a-zA-Z0-9_]+)\.([a-zA-Z0-9_]+)\b", src_expr)
        for unit_a, field_a in dot_matches:
            if unit_a in units:
                declared = units[unit_a]["output_fields"]
                if not declared:
                    print(f"  [FAIL] {context_name} consumes '{unit_a}.{field_a}', but Unit '{unit_a}' declares NO Outputs!")
                    inv7_failed = True
                elif field_a not in declared:
                    print(f"  [FAIL] {context_name} consumes '{unit_a}.{field_a}', but '{field_a}' is NOT in Outputs of Unit '{unit_a}'! (Declared: {sorted(list(declared))})")
                    inv7_failed = True

    for u_name_b, u_info_b in units.items():
        for p_name_b, src_list_b in u_info_b["ports"].items():
            for src_expr, _ in src_list_b:
                check_field_references(f"Unit '{u_name_b}' port '{p_name_b}'", src_expr)

    for wb_name, src_list_wb in writebacks.items():
        for src_expr, _ in src_list_wb:
            check_field_references(f"Writeback '{wb_name}'", src_expr)

    if not inv7_failed:
        print("  [PASS] Every referenced 'Unit.field' is a valid declared output of 'Unit'.")

    all_failed = inv1_failed or inv2_failed or inv3_failed or inv4_failed or inv5_failed or inv6_failed or inv7_failed
    print("\n" + "=" * 80)
    if all_failed:
        print(" [-] SUMMARY: VERIFICATION FAILED - ONE OR MORE INVARIANTS VIOLATED")
        sys.exit(1)
    else:
        print(" [+] SUMMARY: ALL 7 ARCHITECTURAL INVARIANTS VERIFIED SUCCESSFULLY (100% PASS)")
        sys.exit(0)

if __name__ == "__main__":
    run_invariant_checks()

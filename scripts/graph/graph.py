import pydot
import re
import json

dot = pydot.graph_from_dot_file("../../.verus-log/crate-call-graph-full-initial.dot")

r = {}

for n in dot[0].get_nodes():
    if n.get_label() is None:
        continue

    l = n.get_label()

    if not l.startswith("\"Fun"):
        continue

    if not re.match(".*(std|core|clone|verus_builtin)", l) is None:
        continue

    ancestors = [e.get_target() for e in dot[0].get_edges() if e.get_source() == n.get_name()]

    fn_name = l.split("\\n")[1][:-1]

    r.update([[fn_name, len(ancestors)]])

    print(f"{l}: {len(ancestors)} {ancestors}")

enc = json.JSONEncoder()
print(enc.encode(r))

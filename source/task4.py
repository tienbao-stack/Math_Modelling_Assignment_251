from queue import Queue
import os
import time
import xml.etree.ElementTree as et
from collections import defaultdict, namedtuple
# BDD
import pyeda.inter as pyeda
# ILP
import pulp
import task1_2
import task3


# ---------------------------
# detect deadlock combining BDD & ILP 
# ---------------------------
def _enumerate_bdd_markings(R, net):
    """
    Trả về danh sách marking (list[dict]) theo cùng thứ tự places sorted(net.places.keys()).
    Sử dụng R.satisfy_all() nếu có, fallback bằng satisfy_one + blocking clause nếu cần.
    """
    places_list = sorted(net.places.keys())
    n = len(places_list)
    curr_vars = pyeda.bddvars('curr', n)

    markings = []
    try:
        gen = R.satisfy_all()
        for ass in gen:
            mark = {}
            for i, v in enumerate(curr_vars):
                val = ass.get(v, 0)
                mark[places_list[i]] = 1 if val else 0
            markings.append(mark)
        return markings
    except Exception:
        R_copy = R
        while True:
            one = R_copy.satisfy_one()
            if one is None:
                break
            mark = {}
            for i, v in enumerate(curr_vars):
                val = one.get(v, 0)
                mark[places_list[i]] = 1 if val else 0
            markings.append(mark)
            block = None
            for i, v in enumerate(curr_vars):
                lit = v if mark[places_list[i]] == 1 else ~v
                block = lit if block is None else (block & lit)
            if block is None:
                break
            R_copy = R_copy & ~block
        return markings

# ----------------------------
# ILP + BDD deadlock detection
# - Build BDD reachable R and enumerate markings M = {m1,...,mK}
# - Build ILP with binary selection z_k for each marking
# - For each transition t, compute e_tk = 1 if marking k enables t (considering same enable rules as BDD)
# - Introduce y_t (binary) indicating enabled in selected marking
# - Constraints:
#     sum_k z_k == 1
#     for each t: y_t <= sum_k e_tk * z_k
#                for each k with e_tk==1: y_t >= z_k
#     deadlock constraint: sum_t y_t == 0
# - If feasible => found dead reachable marking
# ----------------------------
#def detect_deadlock_ilp_bdd(net, timeout_seconds=None, verbose=False):

def detect_deadlock_bdd_ilp(net: PetriNet, timeout_seconds: int = None, verbose: bool = False):
    """
    Kết hợp BDD (tập reachable) và ILP:
      - Lấy R = bdd(net)
      - Liệt kê tất cả marking reachable (theo R)
      - Dùng ILP chọn 1 marking reachable sao cho không có transition nào enabled
    Trả về (found: bool, marking: dict|None)
    """
    R, count = bbd(net)
    if verbose:
        print(f"[BDD] satisfy_count = {count}")

    markings = _enumerate_bdd_markings(R, net)
    if verbose:
        print(f"[BDD] Enumerated {len(markings)} markings")

    if len(markings) == 0:
        return False, None

    inp = {}
    outp = {}
    inp_w = {}
    outp_w = {}
    for s, t, w in net.arcs:
        if s in net.places:
            inp.setdefault(t, []).append(s)
            inp_w[(s, t)] = w
        elif s in net.transitions:
            outp.setdefault(s, []).append(t)
            outp_w[(s, t)] = w

    K = len(markings)
    e_tk = {t: [0]*K for t in net.transitions}
    for k, m in enumerate(markings):
        for t in net.transitions:
            tran_in = inp.get(t, [])
            tran_out = outp.get(t, [])
            fire = all(m[p] >= inp_w.get((p, t), 1) for p in tran_in)
            fire = fire and all(m[p] == 0 for p in tran_out if p not in tran_in)
            e_tk[t][k] = 1 if fire else 0

    prob = pulp.LpProblem("deadlock_detection", pulp.LpMinimize)
    prob += 0 

    z = [pulp.LpVariable(f"z_{k}", lowBound=0, upBound=1, cat='Binary') for k in range(K)]
    prob += pulp.lpSum(z) == 1

    y = {t: pulp.LpVariable(f"y_{t}", lowBound=0, upBound=1, cat='Binary') for t in net.transitions}

    for t in net.transitions:
        prob += y[t] <= pulp.lpSum(e_tk[t][k] * z[k] for k in range(K))
        for k in range(K):
            if e_tk[t][k] == 1:
                prob += y[t] >= z[k]

    prob += pulp.lpSum(y[t] for t in net.transitions) == 0

    solver = pulp.PULP_CBC_CMD(msg=(1 if verbose else 0), timeLimit=timeout_seconds) if timeout_seconds else pulp.PULP_CBC_CMD(msg=(1 if verbose else 0))
    res = prob.solve(solver)
    status = pulp.LpStatus[prob.status]
    if verbose:
        print(f"[ILP] status = {status}")

    if status in ("Optimal", "Feasible"):
        chosen = None
        for k in range(K):
            val = pulp.value(z[k])
            if val is not None and val > 0.5:
                chosen = k
                break
        if chosen is None:
            vals = [pulp.value(var) for var in z]
            chosen = max(range(K), key=lambda i: 0 if vals[i] is None else vals[i])
        return True, markings[chosen]
    else:
        return False, None


# ----------------------------
# Test harness 
# ----------------------------
test1_pnml = """<?xml version="1.0"?><pnml><net id="n1" type="http://www.pnml.org/version-2009/grammar/pnmlcoremodel">
<page id="p1"><place id="p1"><initialMarking><text>1</text></initialMarking></place>
<place id="p2"><initialMarking><text>0</text></initialMarking></place>
<transition id="t1"><name><text>t1</text></name></transition>
<arc id="a1" source="p1" target="t1"></arc><arc id="a2" source="t1" target="p2"></arc>
</page></net></pnml>"""

test2_pnml = """<?xml version="1.0"?><pnml><net id="n1" type="http://www.pnml.org/version-2009/grammar/pnmlcoremodel">
<page id="p1"><place id="p1"><initialMarking><text>1</text></initialMarking></place>
<place id="p2"><initialMarking><text>1</text></initialMarking></place>
<transition id="t1"><name><text>t1</text></name></transition>
<arc id="a1" source="p1" target="t1"></arc><arc id="a2" source="t1" target="p2"></arc>
</page></net></pnml>"""

test3_pnml = """<?xml version="1.0"?><pnml><net id="n1" type="http://www.pnml.org/version-2009/grammar/pnmlcoremodel">
<page id="p1"><place id="p1"><initialMarking><text>1</text></initialMarking></place>
<place id="p2"><initialMarking><text>0</text></initialMarking></place>
<place id="p3"><initialMarking><text>0</text></initialMarking></place>
<transition id="t1"><name><text>t1</text></name></transition>
<transition id="t2"><name><text>t2</text></name></transition>
<arc id="a1" source="p1" target="t1"></arc><arc id="a2" source="t1" target="p2"></arc>
<arc id="a3" source="p1" target="t2"></arc><arc id="a4" source="t2" target="p3"></arc>
</page></net></pnml>"""

test4_pnml = """<?xml version="1.0"?><pnml><net id="n1" type="http://www.pnml.org/version-2009/grammar/pnmlcoremodel">
<page id="p1"><place id="p1"><initialMarking><text>1</text></initialMarking></place>
<place id="p2"><initialMarking><text>0</text></initialMarking></place>
<transition id="t1"><name><text>t1</text></name></transition>
<transition id="t2"><name><text>t2</text></name></transition>
<arc id="a1" source="p1" target="t1"></arc><arc id="a2" source="t1" target="p2"></arc>
<arc id="a3" source="p2" target="t2"></arc><arc id="a4" source="t2" target="p1"></arc>
</page></net></pnml>"""

test5_pnml = """<?xml version="1.0"?><pnml><net id="n1" type="http://www.pnml.org/version-2009/grammar/pnmlcoremodel">
<page id="p1"><place id="p1"><initialMarking><text>1</text></initialMarking></place>
<transition id="t1"><name><text>t1</text></name></transition>
<arc id="a1" source="p1" target="t1"></arc><arc id="a2" source="t1" target="p1"></arc>
</page></net></pnml>"""

def run_test_Task4(name, pnml_content, expected_dead):
    filename = f"./{name}.pnml"
    with open(filename, "w") as f:
        f.write(pnml_content)
    try:
        net = read_pnmlFile(filename)
        expl = all_reachable_marking(net)
        print(f"\n--- Test {name} ---")
        print(f"Explicit reachable ({len(expl)}): {expl}")

        start = time.time()
        found, marking = detect_deadlock_bdd_ilp(net, verbose=False) 
        took = time.time() - start
        if found:
            print(f"--> BẾ TẮC TÌM THẤY (time {took:.4f}s): {marking}")
        else:
            print(f"--> KHÔNG BẾ TẮC (time {took:.4f}s)")
        assert found == expected_dead, f"Expected dead={expected_dead}, got {found}"
    finally:
        if os.path.exists(filename):
            os.remove(filename)


if __name__ == "__main__":
    print("===============================")
    print(" TEST Task 4 ")
    print("===============================")

    tests = [
        ("test1_simple", test1_pnml, False),   
        ("test2_1safe",  test2_pnml, True),   
        ("test4_cycle",  test4_pnml, False),
        ("test5_selfloop", test5_pnml, False), 
    ]
    passed = 0
    failed = 0
    for name, content, expect in tests:
        try:
            run_test_Task4(name, content, expect)
            print("PASS")
            passed += 1
        except AssertionError as e:
            print("FAIL:", e)
            failed += 1
    print(f"\nSUMMARY: passed={passed} failed={failed}")

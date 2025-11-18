import xml.etree.ElementTree as et
# from collections import deque
from queue import Queue
import pyeda.inter as pyeda
import os
import time
import task1_2

def bbd(net: PetriNet):
    places_id = {j: i for i, j in enumerate(sorted(net.places.keys()))}
    n = len(places_id)

    curr = pyeda.bddvars('curr', n)
    next = pyeda.bddvars('next', n)

    R = curr[0] | ~curr[0]
    
    for i in net.places:
        id = places_id[i]
        val = net.places[i]
        if int(val) == 1:
            R &= curr[id]
        else:
            R &= ~curr[id]

    inVar = {tran: [] for tran in net.transitions}
    outVar = {tran: [] for tran in net.transitions}

    for s, t, w in net.arcs:
        if s in net.places and t in net.transitions:
            inVar.setdefault(t, []).append(s)
        elif s in net.transitions and t in net.places:
            outVar.setdefault(s, []).append(t)

    T = curr[0] & ~curr[0]

    for i in net.transitions:
        T_temp = curr[0] | ~curr[0]
        inVar_id = {places_id[j] for j in inVar.get(i, [])}
        outVar_id = {places_id[j] for j in outVar.get(i, [])}

        for j in inVar_id:
            T_temp &= curr[j]

        for j in outVar_id:
            if j not in inVar_id:
                T_temp &= ~curr[j]

        for j in range(n):
            inInVar = j in inVar_id
            inOutVar = j in outVar_id

            if inInVar and not inOutVar:
                T_temp &= ~next[j]
            elif not inInVar and inOutVar:
                T_temp &= next[j]
            elif inInVar and inOutVar:
                T_temp &= next[j]
            elif not inInVar and not inOutVar:
                T_temp &= (next[j] & curr[j]) | (~next[j] & ~curr[j])

        T |= T_temp
    
    
    trans = {j: i for i, j in zip(curr, next)}

    while True:
        R_curr = R

        R_img = (R & T).smoothing(curr)

        R_next = R_img.compose(trans)
            
        R = R | R_next

        if R == R_curr:
            break
    
    return R, R.satisfy_count()

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

def run_test(test_name, pnml_content, expected_count):
    print(f"\n--- ⚡ Đang chạy: {test_name} ---")
    
    test_filename = f"./{test_name}.pnml"
    try:
        with open(test_filename, "w") as f:
            f.write(pnml_content)
    except Exception as e:
        print(f"LỖI: Không thể tạo file test: {e}")
        return False

    try:
        net = read_pnmlFile(test_filename)
        
        start_time = time.time()
        explicit_markings = all_reachable_marking(net)
        explicit_time = time.time() - start_time
        explicit_count = len(explicit_markings)
        
        start_time = time.time()
        R_bdd, bdd_count = bbd(net)
        bdd_time = time.time() - start_time
        
        print(f"Task 2 (Tường minh): {explicit_count} trạng thái (Time: {explicit_time:.6f}s)")
        print(f"Task 3 (BDD):         {bdd_count} trạng thái (Time: {bdd_time:.6f}s)")
        
        if explicit_count == bdd_count and bdd_count == expected_count:
            print(f"✅ PASSED: Kết quả khớp ({expected_count})")
            return True
        else:
            print(f"❌ FAILED: Không khớp! Task 2={explicit_count}, Task 3={bdd_count}, Dự kiến={expected_count}")
            return False

    except Exception as e:
        print(f"❌ FAILED: Lỗi nghiêm trọng khi chạy test '{test_name}': {e}")
        import traceback
        traceback.print_exc()
        return False
    finally:
        if os.path.exists(test_filename):
            os.remove(test_filename)

if __name__ == "__main__":
    
    print("===============================")
    print(" TEST Task 3 ")
    print("===============================")
    
    tests = [
        ("test1_simple", test1_pnml, 2),
        ("test2_1safe",  test2_pnml, 1),
        ("test3_branch", test3_pnml, 3),
        ("test4_cycle",  test4_pnml, 2),
        ("test5_selfloop", test5_pnml, 1)
    ]
    
    pass_count = 0
    fail_count = 0
    
    for name, content, count in tests:
        if run_test(name, content, count):
            pass_count += 1
        else:
            fail_count += 1
            
    print("\n===============================")
    print(" KẾT QUẢ TEST SUITE ")
    print("===============================")
    print(f"✅ PASSED: {pass_count}")
    print(f"❌ FAILED: {fail_count}")

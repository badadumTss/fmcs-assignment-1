import pynusmv
import sys
import pprint

def spec_to_bdd(model, spec):
    """Return the set of states of `model` satisfying `spec`, as a BDD.

    """
    bddspec = pynusmv.mc.eval_ctl_spec(model, spec)
    return bddspec

def research(fsm, bddspec):
    #seguo algoritmo
    reach = fsm.init
    new = fsm.init
    seq = []
    while fsm.count_states(new) > 0:
        notResp = new.diff(bddspec)
        if fsm.count_states(notResp) > 0: #se qualcosa non rispetta
            return fsm.pick_one_state(notResp), seq
        seq.append(new)
        new = (fsm.post(new)).diff(reach)
        reach = reach + new
    return None, seq

def not_satisfies(fsm, state, spec):
    return state not in fsm.pick_all_states(spec)

def dfs(fsm, s, spec, reach):
    reach.append(s)
    if not_satisfies(fsm, s, spec):
        return reach, [s.get_str_values()]
    for inp in fsm.pick_all_inputs(s):
        for t in fsm.pick_all_states(fsm.post(s, inp)):
            if t not in reach:
                reach, exe = dfs(fsm, t, spec, reach)
                if bool(len(exe)):
                    exe.insert(0, inp.get_str_values())
                    exe.insert(0, s.get_str_values())
                    return reach, exe
    return reach, []

def reachable(fsm, spec):
    reach = []
    exe = []
    for s in fsm.pick_all_states(fsm.init):
        if s not in reach:
            reach, exe = dfs(fsm, s, spec, reach)
            if bool(len(exe)):
                return exe
    return [] # empty path

def check_explain_inv_spec(spec):
    """Return whether the loaded SMV model satisfies or not the invariant
    `spec`, that is, whether all reachable states of the model
    satisfies `spec` or not. Return also an explanation for why the
    model does not satisfy `spec``, if it is the case, or `None`
    otherwise.

    The result is a tuple where the first element is a boolean telling
    whether `spec` is satisfied, and the second element is either
    `None` if the first element is `True``, or an execution of the SMV
    model violating `spec` otherwise.

    The execution is a tuple of alternating states and inputs,
    starting and ennding with a state. States and inputs are
    represented by dictionaries where keys are state and inputs
    variable of the loaded SMV model, and values are their value.

    """
    fsm = pynusmv.glob.prop_database().master.bddFsm
    bddspec = spec_to_bdd(fsm, spec)
    node, sequence = research(fsm, bddspec) #ricerca per vedere se rispetta
    #funzione che costruisce l'albero e controllo su res
    if node is not None:
        return False, reachable(fsm, bddspec)
    else:
        return True, None

if len(sys.argv) != 2:
    print("Usage: ", sys.argv[0], " filename.smv")
    sys.exit(1)

# init 
pynusmv.init.init_nusmv()
filename = sys.argv[1]
# load file
pynusmv.glob.load_from_file(filename)
# compute model, goes to state of the library
pynusmv.glob.compute_model()
invtype = pynusmv.prop.propTypes['Invariant']
# check all the property in the library status, if one is $invtype,
for prop in pynusmv.glob.prop_database():
    spec = prop.expr
    # then
    if prop.type == invtype:
        print("Property", spec, "is an INVARSPEC.")
        res, trace = check_explain_inv_spec(spec)
        if res == True:
            print("Invariant is respected")
        else:
            print("Invariant is not respected")
            print(trace)
    else:
        print("Property", spec, "is not an INVARSPEC, skipped.")

pynusmv.init.deinit_nusmv()

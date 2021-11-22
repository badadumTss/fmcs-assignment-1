import pynusmv
import sys
import pprint

def spec_to_bdd(model, spec):
    """Return the set of states of `model` satisfying `spec`, as a BDD.

    """
    bddspec = pynusmv.mc.eval_ctl_spec(model, spec)
    return bddspec

def print_states(fsm, bdd):
    for state in fsm.pick_all_states(bdd):
        print(state.get_str_values())

def reachable(fsm, prop):	# transition system and property to verify
    """
    :fsm model
    :prop property bdd encoded
    """
    trans = fsm.trans
    new = fsm.init
    reached = fsm.init
    while (new.size > 0):
        if new & prop:
            print_states(fsm, new)
            print_states(fsm, prop)
            return True
        new = ((trans.post(new)) - reached)
        reached = (reached + new)
    return False

def check_explain_ltl_spec(spec):
    """Returns weather or not the loaded model satisfies the `ltlspec` for
    all possible inputs. If not, returns a trace that rapresents a
    possible input that breaks the invariant

    """
    # reverse property
    prop1 = pynusmv.prop.not_(spec)          # reversing the invariant,
                                             # this way we can check
                                             # weather a node sarisfies
                                             # the inverse and
                                             # therefore does not
                                             # respect the invariant
    
    fsm = pynusmv.glob.prop_database().master.bddFsm # complete model
    prop = spec_to_bdd(fsm, prop1)
    
    # check with symbolic bds search if some node verifies the inverse
    # of the property
    return not reachable(fsm, prop)
    
    # if some state reach the inverse of the invariant, explain (the
    # invariant is violated)
	

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
    # res, trace = pynusmv.mc.check_explain_ltl_spec(ltlspec)
    return check_explain_ltl_spec(spec)

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
        print(check_explain_inv_spec(spec))
	# if res == True:
	#     print("Invariant is respected")
	# else:
	#     print("Invariant is not respected")
	#     pprint.PrettyPrinter(indent=2).pprint(trace)
    else:
        print("Property", spec, "is not an INVARSPEC, skipped.")

pynusmv.init.deinit_nusmv()

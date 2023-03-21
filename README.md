# tla-common
TLA+ building block specifications for distributed systems.

## Organization:

If the module contains a specification, its folder will contain:

- The module itself: *"module name".tla*
  
- A *model.tla* module that will extend the module above and add anything needed for model checking:
  - invariants
  - constraints
  - temporal properties
  
- A model.cfg that sets redefinitions and/or the items from the model.tla module to check

## Common Modules:

The Common folder contains any modules that are shared by others, but are not specifications. The *Bounds.tla* module is a special case that is used by *model.tla* models to allow TLC to compute finite behaviors for infinite sets (such as Nat, Seq).
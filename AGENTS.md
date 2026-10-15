# Repository guidance

- Implement in C, C++, and assembly. Use GNU C23 and GNU C++26 modes explicitly.
- Treat OS resources, effects, ownership, and synchronization as first-class
  parts of the program model across every language/backend.
- Keep implementation status accurate. Design documents do not establish an
  implemented API or supported backend.
- Document target limitations and failure behavior; never silently lower an
  operation to a weaker semantic contract.
- Tests must check independently defined behavior and catch plausible defects.
  Do not repeat implementation logic, assert fixture assignments, or mock away
  the behavior under test. Skip new tests without meaningful evidence.
- Run checks appropriate to the change. Keep bootstrap compiler checks distinct
  from future runtime, eDSL, ABI, and memory-model validation.

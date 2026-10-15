# Repository guidance

- Implement the eDSLs, semantics, proof infrastructure, and validators in Lean 4.
  C (GNU23), C++ (GNU++26), LLVM IR, and assembly are modeled/generated domains.
  Native fixtures and necessary runtime shims may use C/C++/assembly.
- Keep Lean pinned, build with warnings as errors, and audit theorem dependencies.
  Do not introduce proof holes, project axioms, or unchecked solver results into
  claims advertised as proved. List environmental assumptions in theorem contracts.
- Treat OS resources, effects, ownership, and synchronization as first-class
  parts of the program model across every language/backend.
- Keep implementation status accurate. Design documents do not establish an
  implemented API or supported backend.
- Prioritize direct verification of exact final machine code against independent
  contracts. Source/IR semantics provide optional preservation guarantees and
  proof hints, not mandatory frontends for every binary-verification input.
- Keep security findings private. Proof failure, timeout, and unsupported code
  do not establish a defect; record evidence and triage before reporting.
- Document target limitations and failure behavior; never silently lower an
  operation to a weaker semantic contract.
- Tests must check independently defined behavior and catch plausible defects.
  Do not repeat implementation logic, assert fixture assignments, or mock away
  the behavior under test. Skip new tests without meaningful evidence.
- Run checks appropriate to the change. Keep bootstrap compiler checks distinct
  from future runtime, eDSL, ABI, and memory-model validation.

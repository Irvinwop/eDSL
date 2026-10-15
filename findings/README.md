# Findings queue

The repository is private during development. [index.json](index.json) is the
initial machine-readable queue, using format version 1. It currently contains
no findings. The [workflow](../docs/findings.md) defines evidence requirements,
states and the reporting boundary.

The queue is a record, not an implemented scanner or reporter. Future entries
must reference checked evidence; a timeout or unsupported construct does not
establish unsafe behavior. Raw payloads/reproducers belong in controlled storage
such as the ignored `private/` directory, not ordinary logs.

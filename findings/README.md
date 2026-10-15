# Findings queue

The repository is public. [index.example.json](index.example.json) documents
the empty format; it is not a live findings database. Actual records belong in
the ignored `index.json`, `records/` or `private/` paths and are never committed.
The [workflow](../docs/findings.md) defines evidence requirements and states.

No scanner or reporter is implemented. Local entries must reference checked
evidence; a timeout or unsupported construct does not
establish unsafe behavior. Raw payloads/reproducers belong in controlled storage
such as the ignored `private/` directory, not ordinary logs.

# Benchmarking Tests


We present a collection of known, used, examples from MPST/Actor community to highlight our language's efficacy.

This list was inspired:

> Nicolas Lagaillardie, Rumyana Neykova, Nobuko Yoshida: Stay Safe
> Under Panic: Affine Rust Programming with Multiparty Session Types
> (Artifact). Dagstuhl Artifacts Ser. 8(2): 09:1-09:16 (2022)


| Name                 | Ps | DMs | Choices | Rs | Protocol | Session    | Execution    | Pass/Fail | Notes   |
|----------------------|----|-----|---------|----|----------|------------|--------------|-----------|---------|
| Calculator           | 2  | 3   | 1x3,1x2 | 0  | yes      | yes(all)   | no           | Pass      | See [0] |
| Two Buyer            | 3  | 6   | 1x2     | 0  | yes      | yes(all)   | yes (bob)    | Pass      | See [1] |
| Simple Voter         | 2  | 3   | 2x2     | 0  | yes      | yes(both)  | yes (client) | Pass      |         |
| Fibonacci            | 2  | 1   | 1x2     | 1  | yes      | yes (both) | yes (client) | Pass      |         |
| Streaming            | 4  | 3   | 0       | 1  | yes      | no         | yes          | Pass      |         |
| Buyer Seller         | 2  | 3   | 1x3     | 1  | yes      | yes(both)  | yes (client) | Pass      |         |
| SMTP                 | 2  | 9   | 8x2,1x3 | 3  | yes      | no         | no           | Pass      | See [0] |
| Simple Travel Agency | 3  | 6   | 1x3     | 1  | yes      | no         | no           | Fail      | See [2] |
| Online Wallet        | 3  | 4   | 2x2     | 1  | yes      | no         | no           | Fail      | See [2] |
| oAuth2               | 3  | 3   | 1       | 0  | yes      | no         | no           | Fail      | See [2] |
| Negotiation          | 3  | 9   | 2x2     | 2  | yes      | no         | no           | Fail      | See [2] |
|                      |    |     |         |    |          |            |              |           |         |

Notes

0. A basic calculator has been specified, a more extensive calculator
   *could* be written but what we have is sufficient. Ditto for SMTP
1. The other two-buyer examples are not worth exploring.
2. Failing examples are a result of the language's lack of support for
   full merge.

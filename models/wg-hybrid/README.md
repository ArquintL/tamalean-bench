# Artifacts for Usenix'25 paper "A Tale of Two Worlds, a Formal Story of WireGuard Hybridization"

This repository contains all required software to reproduce results from paper "A Tale of Two Worlds, a Story of WireGuard Hybridization".

## Licence

GNU General Public License v3[^0].


## Architecture

Folder *artifacts_evaluation* concerns the symbolic evaluation of WireGuard (with fix for anonymity based on psk), PQ-WireGuard, PQ-WireGuard⋆ and Hybrid-WireGuard with the help of SAPIC+, ProVerif, Tamarin and DeepSec. The second folder *artifacts_implementation* concerns the Rust implementation of WireGuard, PQ-WireGuard⋆ and Hybrid-WireGuard. Each folder contains a README.md file that explains how to install all the dependencies (SAPIC+, ProVerif, Tamarin, DeepSec used for symbolic evaluation, Python package sympy used for the CNF computations on the one hand, and Rust on the other hand). Our target is to ensure reproducibility of our results on a fresh Ubuntu Server 24.04.2 LTS.

## References

[^0]: https://www.gnu.org/licenses/gpl-3.0.html
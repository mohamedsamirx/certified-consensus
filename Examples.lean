import CertifiedConsensus

/-!
# `#certify_epipolar` examples

The command evaluates the matrix **at elaboration time**, reads the
correspondences from disk, and refuses to compile if any check fails.
-/

open CertifiedConsensus

-- Exact certificate: every residual is exactly zero.
#certify_epipolar
  !![0, 0, 1/10; 0, 0, -1/2; 1/2, 1/10, 0]
  from "data/stereo_points.txt"

-- Noisy certificate: the same rank-two matrix, with an explicit tolerance.
#certify_epipolar
  !![0, 0, 1/10; 0, 0, -1/2; 1/2, 1/10, 0]
  from "data/noisy_points.txt" tol 3/500

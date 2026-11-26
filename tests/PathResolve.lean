import CertifiedConsensus.Command

-- Relative to this file's directory (`tests/`), not the process working directory.
#certify_epipolar !![0, 0, 1/10; 0, 0, -1/2; 1/2, 1/10, 0]
  from "../data/stereo_points.txt"

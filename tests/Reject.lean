import CertifiedConsensus.Command

-- Expected to fail: the identity matrix has rank three, so the certificate is invalid.
#certify_epipolar !![1, 0, 0; 0, 1, 0; 0, 0, 1]
  from "../data/stereo_points.txt"

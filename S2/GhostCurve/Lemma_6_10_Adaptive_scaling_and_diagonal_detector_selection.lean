module

public import S2.GhostCurve.detectorIndex

/- Lemma 6.10 (Adaptive scaling and diagonal detector selection)

With zero-based indexing, `Lorentz.detectorScale` is the adaptive scale using
the weight `(i + 1) ^ 2`, while `Lorentz.detectorIndex` selects the scheduled
detector point.  The following canonical declarations give the scale bound,
the lower bound on the selected index, and the scaled negative-coordinate
bound by half of `DetectorTriple.rightRadius i`. -/
#check Lorentz.detectorScale
#check Lorentz.quadraticSize_le_detectorScale
#check Lorentz.detectorIndex
#check Lorentz.le_detectorIndex
#check Lorentz.scaled_norm_detectorIndex_lt

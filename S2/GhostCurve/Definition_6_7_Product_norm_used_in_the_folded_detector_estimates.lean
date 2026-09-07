module

import S2.Infra.zSize

/- Definition 6.7 (Product norm used in the folded detector estimates):
on `C0Seq × L1Seq`, use the coordinate-sum size, equivalently the canonical
`WithLp 1` product norm. -/
#check C0Seq.zSize
#check C0Seq.zSize_apply
#check C0Seq.zSize_eq_norm_toLp

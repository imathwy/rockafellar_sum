module

public import ReasLib.Analysis.C0Seq.RemoteBall

@[expose] public section

open scoped ZeroAtInfty

/- Definition 6.1 (Local test ball and remote convex ball) (1): the local test ball `U` is
`C0Seq.localOpenUnitBall = Metric.ball 0 1`. -/
#check (C0Seq.localOpenUnitBall : Set C₀(ℕ, ℝ))

/- Definition 6.1 (Local test ball and remote convex ball) (2): the point `4e₁`, using
Lean coordinate `0` for the source's first coordinate. -/
#check (C0Seq.farPoint : C₀(ℕ, ℝ))
#check (C0Seq.farPoint_apply :
  ∀ n : ℕ, C0Seq.farPoint n = if n = 0 then 4 else 0)
#check (C0Seq.norm_farPoint : ‖C0Seq.farPoint‖ = 4)

/- Definition 6.1 (Local test ball and remote convex ball) (3): the radius-one ball
centered at `farPoint`. -/
#check (C0Seq.remoteBall : Set C₀(ℕ, ℝ))
#check (C0Seq.mem_remoteBall :
  ∀ x : C₀(ℕ, ℝ), x ∈ C0Seq.remoteBall ↔ dist x C0Seq.farPoint < 1)

/- Definition 6.1 (Local test ball and remote convex ball) (4): the local test ball and
the remote ball are disjoint. -/
#check (C0Seq.localOpenUnitBall_disjoint_remoteBall :
  Disjoint C0Seq.localOpenUnitBall C0Seq.remoteBall)

/- Definition 6.1 (Local test ball and remote convex ball) (5): the remote ball is convex. -/
#check (C0Seq.convex_remoteBall : Convex ℝ C0Seq.remoteBall)

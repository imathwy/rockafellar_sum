/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.Pairing
import ReasLib.FunctionalAnalysis.SequenceSpace.C0.Proportionality

/-!
# Two-coordinate determinant vectors

This module defines determinant vectors supported on two coordinates and their
evaluation, support, norm, and pairing API.
-/

@[expose] public section

noncomputable section

namespace L1Seq

/-- The two-coordinate determinant vector associated to `d`, with coefficient `d p`
at coordinate `q` and coefficient `-d q` at coordinate `p`. -/
def twoDet (d : C0Seq) (p q : ℕ) : L1Seq :=
  lp.single 1 q (d p) - lp.single 1 p (d q)

/-- Evaluation of a two-coordinate determinant vector at an arbitrary coordinate. -/
theorem twoDet_apply (d : C0Seq) (p q n : ℕ) :
    twoDet d p q n = (if q = n then d p else 0) - (if p = n then d q else 0) := by
  -- Expose the two singleton coordinates, then orient their equality tests as stated.
  simp only [twoDet, lp.coeFn_sub, Pi.sub_apply, lp.single_apply, Pi.single_apply]
  simp only [eq_comm]

/-- A two-coordinate determinant vector is supported on its two selected coordinates. -/
theorem support_twoDet_subset (d : C0Seq) (p q : ℕ) :
    Function.support (fun n ↦ twoDet d p q n) ⊆ ({p, q} : Set ℕ) := by
  -- A coordinate outside the selected pair vanishes by the evaluation formula.
  intro n hn
  by_contra hnpq
  have hnp : n ≠ p := by
    intro h
    exact hnpq (Or.inl h)
  have hnq : n ≠ q := by
    intro h
    exact hnpq (Or.inr h)
  have hzero : twoDet d p q n = 0 := by
    rw [twoDet_apply]
    have hpn : p ≠ n := Ne.symm hnp
    have hqn : q ≠ n := Ne.symm hnq
    simp [hpn, hqn]
  exact (Function.mem_support.mp hn) hzero

/-- Every two-coordinate determinant vector has finite coordinate support. -/
theorem twoDet_hasFiniteSupport (d : C0Seq) (p q : ℕ) :
    (fun n ↦ twoDet d p q n).HasFiniteSupport := by
  -- Bound the support by the finite two-element set from the preceding theorem.
  rw [Function.HasFiniteSupport]
  apply (Set.finite_singleton q).insert p |>.subset
  exact support_twoDet_subset d p q

/-- A two-coordinate determinant vector associated to a unit vector has norm at most two. -/
theorem norm_twoDet_le_two_of_norm_eq_one (d : C0Seq) (h_norm : ‖d‖ = 1)
    (p q : ℕ) (_ : p < q) : ‖twoDet d p q‖ ≤ 2 := by
  -- The unit norm bounds each of the two coefficients appearing in `twoDet`.
  have hp : |d p| ≤ 1 := by
    have hp' := C0Seq.abs_apply_le_norm d p
    rw [h_norm] at hp'
    exact hp'
  have hq : |d q| ≤ 1 := by
    have hq' := C0Seq.abs_apply_le_norm d q
    rw [h_norm] at hq'
    exact hq'
  -- Record the exponent side condition once, then normalize both singleton norms.
  have h_one_pos : 0 < (1 : ENNReal) := by
    norm_num
  have hnorm_q :
      ‖lp.single (E := fun _ : ℕ => ℝ) 1 q (d p)‖ = |d p| := by
    rw [lp.norm_single (E := fun _ : ℕ => ℝ) (p := (1 : ENNReal)) h_one_pos]
    exact Real.norm_eq_abs (d p)
  have hnorm_p :
      ‖lp.single (E := fun _ : ℕ => ℝ) 1 p (d q)‖ = |d q| := by
    rw [lp.norm_single (E := fun _ : ℕ => ℝ) (p := (1 : ENNReal)) h_one_pos]
    exact Real.norm_eq_abs (d q)
  -- Apply the triangle inequality and finish with the two coordinate bounds.
  calc
    ‖twoDet d p q‖ ≤
        ‖lp.single (E := fun _ : ℕ => ℝ) 1 q (d p)‖ +
          ‖lp.single (E := fun _ : ℕ => ℝ) 1 p (d q)‖ := by
      unfold twoDet
      exact norm_sub_le _ _
    _ = |d p| + |d q| := by rw [hnorm_q, hnorm_p]
    _ ≤ 2 := by linarith

end L1Seq

namespace C0Seq

/-- Pairing against a two-coordinate determinant vector evaluates the corresponding
two-by-two determinant. -/
theorem pairingL_twoDet (x d : C0Seq) (p q : ℕ) :
    pairingL x (L1Seq.twoDet d p q) = d p * x q - d q * x p := by
  -- Collapse the pairing with a singleton vector to its unique nonzero summand.
  have hsingle (i : ℕ) (c : ℝ) :
      pairingL x (lp.single (E := fun _ : ℕ => ℝ) 1 i c) = x i * c := by
    rw [pairingL_apply, tsum_eq_single i]
    · rw [lp.single_apply_self, mul_comm]
    · intro m hm
      simp only [lp.single_apply, Pi.single_apply, if_neg hm, mul_zero]
  -- Linearity reduces the determinant vector to the two singleton evaluations.
  unfold L1Seq.twoDet
  rw [map_sub, hsingle, hsingle]
  ring

/-- A sequence pairs to zero with each of its two-coordinate determinant vectors. -/
theorem pairingL_twoDet_self (d : C0Seq) (p q : ℕ) (_ : p < q) :
    pairingL d (L1Seq.twoDet d p q) = 0 := by
  -- The pairing formula becomes an alternating determinant with identical rows.
  rw [pairingL_twoDet]
  ring

/-- If `r` is not a real scalar multiple of a nonzero sequence `d`, then some
ordered pair of coordinates gives a nonzero pairing with the corresponding
two-coordinate determinant vector. -/
theorem exists_pairingL_twoDet_ne_zero (d r : C0Seq) (hd : d ≠ 0) (hr : r ∉ ℝ ∙ d) :
    ∃ p q : ℕ, p < q ∧ pairingL r (L1Seq.twoDet d p q) ≠ 0 := by
  -- If every pairing vanished, every ordered two-coordinate determinant would vanish.
  by_contra h
  have h_all : ∀ p q : ℕ, p < q →
      pairingL r (L1Seq.twoDet d p q) = 0 := by
    intro p q hpq
    by_contra hne
    exact h ⟨p, q, hpq, hne⟩
  have h_det : ∀ p q : ℕ, p < q → d p * r q - d q * r p = 0 := by
    intro p q hpq
    have hzero := h_all p q hpq
    rw [pairingL_twoDet] at hzero
    exact hzero
  -- Determinant vanishing forces proportionality, contradicting exclusion from the span.
  obtain ⟨s, hrs⟩ := eq_smul_of_all_twoDet_eq_zero d r hd h_det
  apply hr
  rw [hrs]
  exact Submodule.smul_mem _ s (Submodule.mem_span_singleton_self d)

end C0Seq

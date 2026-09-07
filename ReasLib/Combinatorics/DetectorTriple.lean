/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Data.Countable.Basic

/-!
# Detector triples

This module defines the finite-sign detector-triple data and its coordinate
and schedule API.
-/

public section

/-- A detector triple encoded by its zero-based lower coordinate, the gap after that
coordinate, and an integer unit representing one of the signs `±1`. -/
@[expose] def DetectorTriple : Type := ℕ × (ℕ × ℤˣ)

namespace DetectorTriple

/-- The zero-based lower coordinate of a detector triple. -/
def p (t : DetectorTriple) : ℕ := t.1

/-- The zero-based upper coordinate of a detector triple. -/
def q (t : DetectorTriple) : ℕ := t.1 + t.2.1 + 1

/-- The integer sign of a detector triple. -/
def sign (t : DetectorTriple) : ℤ := t.2.2

/-- Construct a detector triple from zero-based coordinates `p < q` and an integer unit. -/
def ofIndices (p q : ℕ) (_ : p < q) (σ : ℤˣ) : DetectorTriple :=
  (p, q - p - 1, σ)

/-- The lower coordinate of a detector triple is strictly below its upper coordinate. -/
theorem p_lt_q (t : DetectorTriple) : p t < q t := by
  -- Reassociate the upper coordinate so the positive successor gap is explicit.
  rw [p, q, add_assoc]
  exact lt_add_of_pos_right _ (Nat.zero_lt_succ _)

/-- The integer sign of a detector triple is `1` or `-1`. -/
theorem sign_eq_one_or_neg_one (t : DetectorTriple) : sign t = 1 ∨ sign t = -1 := by
  -- Classify the stored integer unit, then transport each case through its value coercion.
  rcases Int.units_eq_one_or t.2.2 with h | h
  · left
    simp only [sign, h, Units.val_one]
  · right
    simp only [sign, h, Units.val_neg, Units.val_one]

/-- `ofIndices` preserves the lower coordinate. -/
theorem p_ofIndices (p q : ℕ) (hpq : p < q) (σ : ℤˣ) :
    (ofIndices p q hpq σ).p = p := by
  -- The lower coordinate is the first projection of the constructor.
  rfl

/-- `ofIndices` preserves the upper coordinate. -/
theorem q_ofIndices (p q : ℕ) (hpq : p < q) (σ : ℤˣ) :
    (ofIndices p q hpq σ).q = q := by
  -- Strict ordering supplies exactly the bound needed to cancel truncated subtraction.
  have hp1q : p + 1 ≤ q := by
    exact hpq
  -- Normalize the encoded gap and commute the final successor into the cancellable prefix.
  unfold ofIndices DetectorTriple.q
  rw [tsub_tsub]
  calc
    p + (q - (p + 1)) + 1 = (p + 1) + (q - (p + 1)) := by
      simp only [add_assoc, add_comm, add_left_comm]
    _ = q := add_tsub_cancel_of_le hp1q

/-- `ofIndices` preserves the integer value of the sign. -/
theorem sign_ofIndices (p q : ℕ) (hpq : p < q) (σ : ℤˣ) :
    (ofIndices p q hpq σ).sign = σ := by
  -- The sign is the final projection of the constructor, followed by its value coercion.
  rfl

/-- Detector triples form a countable type. -/
instance instCountable : Countable DetectorTriple :=
  inferInstanceAs (Countable (ℕ × (ℕ × ℤˣ)))

/-- The detector-triple type is inhabited. -/
instance instNonempty : Nonempty DetectorTriple := ⟨(0, 0, 1)⟩

end DetectorTriple

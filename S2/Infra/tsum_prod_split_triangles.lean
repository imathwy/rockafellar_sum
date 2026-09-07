/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.InfiniteSum.NatTriangle

/-!
# Product-Series Rearrangement

This module exposes Fubini and symmetry identities for summable double series.
-/

universe u

section

variable {E : Type u} [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
  [CompleteSpace E] [T0Space E]

/- Infrastructure C.1 (Absolutely summable double-series rearrangement) (1).
The canonical Fubini theorem rewrites a summable product-indexed series as an iterated sum. -/
#check (Summable.tsum_prod :
  ∀ {f : ℕ × ℕ → E}, Summable f →
    ∑' p, f p = ∑' n, ∑' m, f (n, m))

/- Infrastructure C.1 (Absolutely summable double-series rearrangement) (2).
The canonical API interchanges iterated sums and transports summability and sums across a swap. -/
#check (Summable.tsum_comm :
  ∀ {f : ℕ → ℕ → E}, Summable (Function.uncurry f) →
    (∑' m, ∑' n, f n m) = ∑' n, ∑' m, f n m)
#check (Summable.prod_symm :
  ∀ {f : ℕ × ℕ → E}, Summable f → Summable (fun p : ℕ × ℕ ↦ f p.swap))
#check (Equiv.tsum_eq :
  ∀ (e : ℕ ≃ ℕ) (f : ℕ → E), (∑' n, f (e n)) = ∑' n, f n)

/- Infrastructure C.1 (Absolutely summable double-series rearrangement) (3).
An absolutely summable real double series decomposes into its diagonal, strict-upper,
and strict-lower triangular parts. -/
#check (Summable.tsum_prod_split_triangles_of_norm :
  ∀ {f : ℕ × ℕ → ℝ}, Summable (fun p ↦ ‖f p‖) →
    ∑' p, f p =
      (∑' n, f (n, n)) +
        (∑' n, ∑' m, if n < m then f (n, m) else 0) +
          ∑' n, ∑' m, if m < n then f (n, m) else 0)

#check (Summable.of_norm :
  ∀ {f : ℕ × ℕ → ℝ}, Summable (fun p ↦ ‖f p‖) → Summable f)

#check (Summable.tsum_prod_split_triangles :
  ∀ {f : ℕ × ℕ → E}, Summable f →
    ∑' p, f p =
      (∑' n, f (n, n)) +
        (∑' n, ∑' m, if n < m then f (n, m) else 0) +
          ∑' n, ∑' m, if m < n then f (n, m) else 0)

#check (Summable.tsum_lower_eq_upper_of_symm :
  ∀ {f : ℕ × ℕ → E}, Summable f →
    (∀ n m, f (n, m) = f (m, n)) →
      (∑' n, ∑' m, if m < n then f (n, m) else 0) =
        ∑' n, ∑' m, if n < m then f (n, m) else 0)

#check (Summable.tsum_prod_eq_diag_add_two_upper_of_symm :
  ∀ {f : ℕ × ℕ → E}, Summable f →
    (∀ n m, f (n, m) = f (m, n)) →
      ∑' p, f p =
        (∑' n, f (n, n)) +
          2 • (∑' n, ∑' m, if n < m then f (n, m) else 0))

end

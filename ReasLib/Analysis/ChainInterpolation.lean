/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.AffineInterpolation

/-!
# Lipschitz chain interpolation

This module glues affine interpolants along ordered chains and their limiting
endpoint.
-/

public section

open Filter Topology

universe u

namespace AffineMap

/-- Lipschitz bounds with the same constant on two adjacent real intervals glue across
their common endpoint. -/
private lemma lipschitzOnWith_Icc_union_adjacent
    {Y : Type*} [PseudoMetricSpace Y] (K : NNReal) {p q r : ℝ} {f : ℝ → Y}
    (hpq : p ≤ q) (hqr : q ≤ r)
    (hleft : LipschitzOnWith K f (Set.Icc p q))
    (hright : LipschitzOnWith K f (Set.Icc q r)) :
    LipschitzOnWith K f (Set.Icc p r) := by
  -- First prove the estimate for an ordered pair of arguments.
  have hordered : ∀ {s v : ℝ}, s ∈ Set.Icc p r → v ∈ Set.Icc p r → s ≤ v →
      dist (f s) (f v) ≤ (K : ℝ) * dist s v := by
    intro s v hs hv hsv
    by_cases hvq : v ≤ q
    · exact hleft.dist_le_mul s ⟨hs.1, hsv.trans hvq⟩ v ⟨hs.1.trans hsv, hvq⟩
    have hqv : q ≤ v := (not_le.mp hvq).le
    by_cases hqs : q ≤ s
    · exact hright.dist_le_mul s ⟨hqs, hsv.trans hv.2⟩ v ⟨hqs.trans hsv, hv.2⟩
    have hsq : s ≤ q := (not_le.mp hqs).le
    have hleft_bound := hleft.dist_le_mul s ⟨hs.1, hsq⟩ q ⟨hpq, le_rfl⟩
    have hright_bound := hright.dist_le_mul q ⟨le_rfl, hqr⟩ v ⟨hqv, hv.2⟩
    calc
      dist (f s) (f v) ≤ dist (f s) (f q) + dist (f q) (f v) := dist_triangle _ _ _
      _ ≤ (K : ℝ) * dist s q + (K : ℝ) * dist q v :=
        add_le_add hleft_bound hright_bound
      _ = (K : ℝ) * dist s v := by
        simp only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hsq),
          abs_of_nonpos (sub_nonpos.mpr hqv), abs_of_nonpos (sub_nonpos.mpr hsv)]
        ring
  -- Symmetry reduces the remaining ordering of the pair to the preceding estimate.
  refine LipschitzOnWith.of_dist_le_mul fun s hs v hv ↦ ?_
  rcases le_total s v with hsv | hvs
  · exact hordered hs hv hsv
  · simpa only [dist_comm] using hordered hv hs hvs

/-- Uniform Lipschitz bounds on increasing finite prefix intervals extend to their
limiting closed interval. -/
private lemma lipschitzOnWith_Icc_limit_of_prefix
    {Y : Type*} [PseudoMetricSpace Y] (K : NNReal) (a : ℝ) (t : ℕ → ℝ) (f : ℝ → Y)
    (h_lower : ∀ n, t 0 ≤ t n) (h_below : ∀ n, t n < a)
    (ht : Tendsto t atTop (𝓝 a))
    (hf : Tendsto (fun n ↦ f (t n)) atTop (𝓝 (f a)))
    (hprefix : ∀ n, LipschitzOnWith K f (Set.Icc (t 0) (t n))) :
    LipschitzOnWith K f (Set.Icc (t 0) a) := by
  -- Treat ordered pairs, separating the limiting endpoint from interior points.
  have hordered : ∀ {s v : ℝ}, s ∈ Set.Icc (t 0) a → v ∈ Set.Icc (t 0) a → s ≤ v →
      dist (f s) (f v) ≤ (K : ℝ) * dist s v := by
    intro s v hs hv hsv
    by_cases hva : v = a
    · subst v
      by_cases hsa : s = a
      · subst s
        simp only [dist_self, mul_zero, le_refl]
      have hsa_lt : s < a := lt_of_le_of_ne hs.2 hsa
      -- Approximate `a` by knots lying to the right of the fixed interior point.
      refine le_of_tendsto (tendsto_const_nhds.dist hf) ?_
      filter_upwards [ht.eventually_const_le hsa_lt] with n hst
      have hbound := (hprefix n).dist_le_mul s ⟨hs.1, hst⟩ (t n) ⟨h_lower n, le_rfl⟩
      have hdist : dist s (t n) ≤ dist s a := by
        simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst),
          abs_of_nonpos (sub_nonpos.mpr hs.2), neg_sub] using
            sub_le_sub_right (h_below n).le s
      exact hbound.trans (mul_le_mul_of_nonneg_left hdist K.coe_nonneg)
    have hva_lt : v < a := lt_of_le_of_ne hv.2 hva
    -- An interior ordered pair lies in one sufficiently long finite prefix.
    obtain ⟨n, hvn⟩ := (ht.eventually_const_le hva_lt).exists
    exact (hprefix n).dist_le_mul s ⟨hs.1, hsv.trans hvn⟩ v ⟨hv.1, hvn⟩
  -- Reverse pairs are handled by symmetry of distance.
  refine LipschitzOnWith.of_dist_le_mul fun s hs v hv ↦ ?_
  rcases le_total s v with hsv | hvs
  · exact hordered hs hv hsv
  · simpa only [dist_comm] using hordered hv hs hvs

/-- Uniform Lipschitz bounds on decreasing finite prefix intervals extend to their
limiting closed interval. -/
private lemma lipschitzOnWith_Icc_limit_of_antitone_prefix
    {Y : Type*} [PseudoMetricSpace Y] (K : NNReal) (a : ℝ) (t : ℕ → ℝ) (f : ℝ → Y)
    (h_upper : ∀ n, t n ≤ t 0) (h_above : ∀ n, a < t n)
    (ht : Tendsto t atTop (𝓝 a))
    (hf : Tendsto (fun n ↦ f (t n)) atTop (𝓝 (f a)))
    (hprefix : ∀ n, LipschitzOnWith K f (Set.Icc (t n) (t 0))) :
    LipschitzOnWith K f (Set.Icc a (t 0)) := by
  -- Treat ordered pairs, separating the limiting endpoint from interior points.
  have hordered : ∀ {s v : ℝ}, s ∈ Set.Icc a (t 0) → v ∈ Set.Icc a (t 0) → s ≤ v →
      dist (f s) (f v) ≤ (K : ℝ) * dist s v := by
    intro s v hs hv hsv
    by_cases hsa : s = a
    · subst s
      by_cases hva : v = a
      · subst v
        simp only [dist_self, mul_zero, le_refl]
      have hva_gt : a < v := lt_of_le_of_ne hv.1 (Ne.symm hva)
      -- Approximate `a` by knots lying to the left of the fixed interior point.
      refine le_of_tendsto (hf.dist tendsto_const_nhds) ?_
      filter_upwards [ht.eventually_le_const hva_gt] with n htv
      have hbound := (hprefix n).dist_le_mul (t n) ⟨le_rfl, h_upper n⟩ v ⟨htv, hv.2⟩
      have hdist : dist (t n) v ≤ dist a v := by
        simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr htv),
          abs_of_nonpos (sub_nonpos.mpr hv.1), neg_sub] using
            sub_le_sub_left (h_above n).le v
      exact hbound.trans (mul_le_mul_of_nonneg_left hdist K.coe_nonneg)
    have hsa_gt : a < s := lt_of_le_of_ne hs.1 (Ne.symm hsa)
    -- An interior ordered pair lies in one sufficiently long finite prefix.
    obtain ⟨n, hns⟩ := (ht.eventually_le_const hsa_gt).exists
    exact (hprefix n).dist_le_mul s ⟨hns, hs.2⟩ v ⟨hns.trans hsv, hv.2⟩
  -- Reverse pairs are handled by symmetry of distance.
  refine LipschitzOnWith.of_dist_le_mul fun s hs v hv ↦ ?_
  rcases le_total s v with hsv | hvs
  · exact hordered hs hv hsv
  · simpa only [dist_comm] using hordered hv hs hvs

/-- Adjacent affine interpolants along an increasing chain converging to `a` glue to a
`K`-Lipschitz map on `Set.Icc (t 0) a`. -/
theorem lipschitzOnWith_chainInterpolation_of_strictMono
    {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (K : NNReal) (a : ℝ) (t : ℕ → ℝ) (x : ℕ → E) (x0 : E) (f : ℝ → E)
    (h_mono : StrictMono t) (h_below : ∀ n, t n < a)
    (ht : Tendsto t atTop (𝓝 a)) (hx : Tendsto x atTop (𝓝 x0))
    (h_step : ∀ n, ‖x (n + 1) - x n‖ ≤ (K : ℝ) * |t (n + 1) - t n|)
    (h_endpoint : f a = x0)
    (h_interpolation : ∀ n, Set.EqOn f
      (fun s ↦ AffineMap.lineMap (x n) (x (n + 1))
        ((s - t n) / (t (n + 1) - t n)))
      (Set.Icc (t n) (t (n + 1)))) :
    LipschitzOnWith K f (Set.Icc (t 0) a) := by
  -- Each finite prefix is Lipschitz, by induction and adjacent-interval gluing.
  have hprefix : ∀ n, LipschitzOnWith K f (Set.Icc (t 0) (t n)) := by
    intro n
    induction n with
    | zero =>
        refine LipschitzOnWith.of_dist_le_mul fun s hs v hv ↦ ?_
        have hsv : s = v := le_antisymm (hs.2.trans hv.1) (hv.2.trans hs.1)
        subst v
        simp only [dist_self, mul_zero, le_refl]
    | succ n ih =>
        have htn : t n < t (n + 1) := h_mono (Nat.lt_succ_self n)
        have hsegment : LipschitzOnWith K f (Set.Icc (t n) (t (n + 1))) := by
          have hline := lipschitzOnWith_lineMap_interval htn
            (by simpa only [abs_of_pos (sub_pos.mpr htn)] using h_step n)
          refine LipschitzOnWith.of_dist_le_mul fun s hs v hv ↦ ?_
          rw [h_interpolation n hs, h_interpolation n hv]
          exact hline.dist_le_mul s hs v hv
        simpa only [Nat.succ_eq_add_one] using
          lipschitzOnWith_Icc_union_adjacent K
            (h_mono.monotone (Nat.zero_le n)) htn.le ih hsegment
  -- The interpolation hypotheses identify the values of `f` at every knot.
  have hknot : ∀ n, f (t n) = x n := by
    intro n
    have htn : t n < t (n + 1) := h_mono (Nat.lt_succ_self n)
    simpa only [sub_self, zero_div, lineMap_apply_zero] using
      h_interpolation n ⟨le_rfl, htn.le⟩
  have hf : Tendsto (fun n ↦ f (t n)) atTop (𝓝 (f a)) := by
    rw [h_endpoint]
    exact hx.congr' (Eventually.of_forall fun n ↦ (hknot n).symm)
  -- Pass the common prefix estimate to the accumulation endpoint.
  exact lipschitzOnWith_Icc_limit_of_prefix K a t f
    (fun n ↦ h_mono.monotone (Nat.zero_le n)) h_below ht hf hprefix

/-- Adjacent affine interpolants along a decreasing chain converging to `a` glue to a
`K`-Lipschitz map on `Set.Icc a (t 0)`. -/
theorem lipschitzOnWith_chainInterpolation_of_strictAnti
    {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (K : NNReal) (a : ℝ) (t : ℕ → ℝ) (x : ℕ → E) (x0 : E) (f : ℝ → E)
    (h_anti : StrictAnti t) (h_above : ∀ n, a < t n)
    (ht : Tendsto t atTop (𝓝 a)) (hx : Tendsto x atTop (𝓝 x0))
    (h_step : ∀ n, ‖x (n + 1) - x n‖ ≤ (K : ℝ) * |t (n + 1) - t n|)
    (h_endpoint : f a = x0)
    (h_interpolation : ∀ n, Set.EqOn f
      (fun s ↦ AffineMap.lineMap (x (n + 1)) (x n)
        ((s - t (n + 1)) / (t n - t (n + 1))))
      (Set.Icc (t (n + 1)) (t n))) :
    LipschitzOnWith K f (Set.Icc a (t 0)) := by
  -- Each finite reversed prefix is Lipschitz, by induction and adjacent gluing.
  have hprefix : ∀ n, LipschitzOnWith K f (Set.Icc (t n) (t 0)) := by
    intro n
    induction n with
    | zero =>
        refine LipschitzOnWith.of_dist_le_mul fun s hs v hv ↦ ?_
        have hsv : s = v := le_antisymm (hs.2.trans hv.1) (hv.2.trans hs.1)
        subst v
        simp only [dist_self, mul_zero, le_refl]
    | succ n ih =>
        have htn : t (n + 1) < t n := h_anti (Nat.lt_succ_self n)
        have hendpoint_bound :
            ‖x n - x (n + 1)‖ ≤ (K : ℝ) * (t n - t (n + 1)) := by
          calc
            ‖x n - x (n + 1)‖ = ‖x (n + 1) - x n‖ := norm_sub_rev _ _
            _ ≤ (K : ℝ) * |t (n + 1) - t n| := h_step n
            _ = (K : ℝ) * (t n - t (n + 1)) := by
              rw [abs_of_nonpos (sub_nonpos.mpr htn.le)]
              ring
        have hsegment : LipschitzOnWith K f (Set.Icc (t (n + 1)) (t n)) := by
          have hline := lipschitzOnWith_lineMap_interval htn hendpoint_bound
          refine LipschitzOnWith.of_dist_le_mul fun s hs v hv ↦ ?_
          rw [h_interpolation n hs, h_interpolation n hv]
          exact hline.dist_le_mul s hs v hv
        simpa only [Nat.succ_eq_add_one] using
          lipschitzOnWith_Icc_union_adjacent K htn.le
            (h_anti.antitone (Nat.zero_le n)) hsegment ih
  -- The interpolation hypotheses identify the values of `f` at every knot.
  have hknot : ∀ n, f (t n) = x n := by
    intro n
    have htn : t (n + 1) < t n := h_anti (Nat.lt_succ_self n)
    have hright := h_interpolation n ⟨htn.le, le_rfl⟩
    have hratio : (t n - t (n + 1)) / (t n - t (n + 1)) = (1 : ℝ) :=
      div_self (sub_ne_zero.mpr htn.ne')
    simpa only [hratio, lineMap_apply_one] using hright
  have hf : Tendsto (fun n ↦ f (t n)) atTop (𝓝 (f a)) := by
    rw [h_endpoint]
    exact hx.congr' (Eventually.of_forall fun n ↦ (hknot n).symm)
  -- Pass the common reversed-prefix estimate to the accumulation endpoint.
  exact lipschitzOnWith_Icc_limit_of_antitone_prefix K a t f
    (fun n ↦ h_anti.antitone (Nat.zero_le n)) h_above ht hf hprefix

end AffineMap

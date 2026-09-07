/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.Normed.LorentzCone

/-!
# Lorentz Cone Convexity

This module exposes convexity and affine-segment properties of Lorentz cones.
-/

@[expose] public section

universe u

section

variable (H0 : Type u) [SeminormedAddCommGroup H0] [NormedSpace ℝ H0]

/- Infrastructure E.5 (Convexity of the Lorentz future and past cones) (1):
the future Lorentz cone is convex. -/
#check (Lorentz.convex_futureCone H0 : Convex ℝ (Lorentz.futureCone H0))

/- Infrastructure E.5 (Convexity of the Lorentz future and past cones) (2):
the past Lorentz cone is convex. -/
#check (Lorentz.convex_pastCone H0 : Convex ℝ (Lorentz.pastCone H0))

variable {xFuture yFuture : ℝ × H0}
  (hxFuture : xFuture ∈ Lorentz.futureCone H0) (hyFuture : yFuture ∈ Lorentz.futureCone H0)

/- Infrastructure E.5 (Convexity of the Lorentz future and past cones) (3):
affine interpolation between points of the future cone remains in that cone. -/
#check ((Lorentz.convex_futureCone H0).mapsTo_lineMap hxFuture hyFuture :
  Set.MapsTo (AffineMap.lineMap xFuture yFuture) (Set.Icc (0 : ℝ) 1)
    (Lorentz.futureCone H0))

variable {xPast yPast : ℝ × H0}
  (hxPast : xPast ∈ Lorentz.pastCone H0) (hyPast : yPast ∈ Lorentz.pastCone H0)

/- Infrastructure E.5 (Convexity of the Lorentz future and past cones) (4):
affine interpolation between points of the past cone remains in that cone. -/
#check ((Lorentz.convex_pastCone H0).mapsTo_lineMap hxPast hyPast :
  Set.MapsTo (AffineMap.lineMap xPast yPast) (Set.Icc (0 : ℝ) 1)
    (Lorentz.pastCone H0))

variable {tFuture : ℝ} (htFuture : tFuture ∈ Set.Icc (0 : ℝ) 1)

/- Infrastructure E.5 (Convexity of the Lorentz future and past cones) (5):
affine interpolation in the future cone has nonnegative Lorentz energy. -/
#check (Lorentz.energy_lineMap_nonneg_of_mem_futureCone hxFuture hyFuture htFuture :
  0 ≤ Lorentz.energy (AffineMap.lineMap xFuture yFuture tFuture))

variable {tPast : ℝ} (htPast : tPast ∈ Set.Icc (0 : ℝ) 1)

/- Infrastructure E.5 (Convexity of the Lorentz future and past cones) (6):
affine interpolation in the past cone has nonnegative Lorentz energy. -/
#check (Lorentz.energy_lineMap_nonneg_of_mem_pastCone hxPast hyPast htPast :
  0 ≤ Lorentz.energy (AffineMap.lineMap xPast yPast tPast))

end

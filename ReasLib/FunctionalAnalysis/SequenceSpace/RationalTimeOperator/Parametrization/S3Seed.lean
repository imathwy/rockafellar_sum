/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.DualPairing.PolarCarrier
public import ReasLib.FunctionalAnalysis.DualPairing.MaximalExtension
public import ReasLib.Analysis.Normed.LorentzCone.SeedMonotone
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzSeed
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.ScaledDetector
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.SeedBase
public import ReasLib.Analysis.Normed.LorentzCone.ScaledDivergence
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.SeedSchedule
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.SeedComparisons
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.SeedAssembly
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.SeedWitnesses
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.SeedCounterexample
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.UnitDifferenceDetector

/-!
# S3 Lorentz seed infrastructure

This aggregate exposes the seed construction, its polar and local energy
properties, the concrete witnesses, and the final normal-cone sum counterexample.
-/

module

public import S2.Infra.paperTranspose
public import ReasLib.FunctionalAnalysis.StrongDual.Ext

public section

universe u v

namespace ContinuousLinearMap

/- Infrastructure C.3 (Transpose evaluation and composition simp package) (1):
the paper transpose evaluates by precomposition. -/
#check (ContinuousLinearMap.paperTranspose_apply :
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : L1Seq →L[ℝ] E) (φ : StrongDual ℝ E) (a : L1Seq),
    T.paperTranspose φ a = φ (T a))

/- Infrastructure C.3 (Transpose evaluation and composition simp package) (2):
the paper transpose preserves addition. -/
#check (ContinuousLinearMap.paperTranspose_add :
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S T : L1Seq →L[ℝ] E),
    (S + T).paperTranspose = S.paperTranspose + T.paperTranspose)

/- Infrastructure C.3 (Transpose evaluation and composition simp package) (3):
the paper transpose reverses composition by precomposition on the strong dual. -/
#check (ContinuousLinearMap.paperTranspose_comp :
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : L1Seq →L[ℝ] E) (U : E →L[ℝ] F),
    (U.comp T).paperTranspose =
      T.paperTranspose.comp (ContinuousLinearMap.precomp ℝ U))

/- Infrastructure C.3 (Transpose evaluation and composition simp package) (4):
the paper transpose commutes with real scalar multiplication. -/
#check (ContinuousLinearMap.paperTranspose_smul :
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (T : L1Seq →L[ℝ] E),
    (c • T).paperTranspose = c • T.paperTranspose)

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Infrastructure C.3 (Transpose evaluation and composition simp package) (5):
paper transposes, and more generally maps into the strong dual of `L1Seq`, are equal when
all their values agree on every primal vector. -/
#check (ContinuousLinearMap.strongDual_ext
    (𝕜 := ℝ) (X := StrongDual ℝ E) (Y := L1Seq) :
  ∀ (S T : StrongDual ℝ E →L[ℝ] StrongDual ℝ L1Seq),
    (∀ φ : StrongDual ℝ E, ∀ a : L1Seq, S φ a = T φ a) → S = T)

end

end ContinuousLinearMap

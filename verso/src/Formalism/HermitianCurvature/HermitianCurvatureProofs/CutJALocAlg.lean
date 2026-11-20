import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnBesselFold

open Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Take `⟨c, hc1, hc2⟩` from `hF`. Use `⟨c, hc1, fun u w hu hw hl g hg => ?_⟩` and prove the remaining obligations. Establish `h1` using `Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg`. Conclude with `(mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le h1 h) (norm_nonneg _)).trans (hc2 u w hu hw hl g hg)`.
-/
theorem inCC_antiA {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {A A' : ℝ} {m : ℕ}
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (h : A' ≤ A) (hF : B.InCC A m F) : B.InCC A' m F := by
  obtain ⟨c, hc1, hc2⟩ := hF
  refine ⟨c, hc1, fun u w hu hw hl g hg => ?_⟩
  have h1 := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
  exact (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le h1 h) (norm_nonneg _)).trans
    (hc2 u w hu hw hl g hg)

section loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

/- English proof (translation)
Introduce `m` and use `inCC_antiA (by linarith) (hF m)`.
-/
theorem cCg_antiA {S : C.HidaSetting E Wp Wq} {v : Fin S.f} {A A' Bg : ℝ} {F : GFn S v} (h : A' ≤ A)
    (hF : CCg S v A Bg F) : CCg S v A' Bg F :=
  fun m => inCC_antiA (by linarith) (hF m)

/- English proof (translation)
Use `⟨hJ.1, fun δ hδ => ?_⟩` and prove the remaining obligations. Take `⟨F, h1, h2, h3⟩` from `hJ.2 δ hδ`. Conclude with `⟨F, h1, cCg_antiA h h2, h3⟩`.
-/
theorem locCC_antiA {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {v : Fin S.f} {A A' Bg : ℝ} {J : GFn S v} (h : A' ≤ A) (hJ : LocCC S T v A Bg J) : LocCC S T v A' Bg J := by
  refine ⟨hJ.1, fun δ hδ => ?_⟩
  obtain ⟨F, h1, h2, h3⟩ := hJ.2 δ hδ
  exact ⟨F, h1, cCg_antiA h h2, h3⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨hFF, fun _ _ => ⟨F, hF, fun m => inCC_antiA (sub_le_self _ (mul_nonneg hBg (Nat.cast_nonneg m))) (hA m), fun _ _ _ => rfl⟩⟩`.
-/
theorem locCC_JF {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {v : Fin S.f} {A Bg : ℝ} {F : GFn S v} (hF : B.CkOn ⊤ (B.GV S.G.k S.G.r) F) (hA : ∀ m : ℕ, B.InCC A m F)
    (hFF : B.JF (T v).base F ∈ smoothFormsPositiveCone S T v) (hBg : 0 ≤ Bg) : LocCC S T v A Bg (B.JF (T v).base F) :=
  ⟨hFF, fun _ _ => ⟨F, hF, fun m => inCC_antiA (sub_le_self _ (mul_nonneg hBg (Nat.cast_nonneg m))) (hA m),
    fun _ _ _ => rfl⟩⟩

/- English proof (translation)
Use `⟨Formalism.FourierDecayAlt.P.Qx8.FFl_smul hJ.1 c, fun δ hδ => ?_⟩` and prove the remaining obligations. Take `⟨F, h1, h2, h3⟩` from `hJ.2 δ hδ`. Use `⟨c • F, Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' c h1, fun m => ?_, fun x hx hG => ?_⟩` and prove the remaining obligations. Take `⟨c0, hc0⟩` from `h2 m`. Conclude with `⟨‖c‖ * c0, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul c hc0⟩`.

Rewrite using `[Formalism.FourierDecayAlt.P.CutMP.En.JF_smul', Pi.smul_apply, h3 x hx hG]`.
-/
theorem locCC_smul {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {v : Fin S.f} {A Bg : ℝ} (c : ℂ) {J : GFn S v} (hJ : LocCC S T v A Bg J) : LocCC S T v A Bg (c • J) := by
  refine ⟨Formalism.FourierDecayAlt.P.Qx8.FFl_smul hJ.1 c, fun δ hδ => ?_⟩
  obtain ⟨F, h1, h2, h3⟩ := hJ.2 δ hδ
  refine ⟨c • F, Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' c h1, fun m => ?_, fun x hx hG => ?_⟩
  · obtain ⟨c0, hc0⟩ := h2 m
    exact ⟨‖c‖ * c0, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul c hc0⟩
  · rw [Formalism.FourierDecayAlt.P.CutMP.En.JF_smul', Pi.smul_apply, h3 x hx hG]

end loc

end Formalism.FourierDecayAlt.P.CutMP.JA

end

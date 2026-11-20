import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadingMinorIntegrality

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LatA

open Alg

variable {D : D7} (X : HidaSetting D)

local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E

/- English proof (translation)
Establish `h` using `(I : Submodule (𝓞 D.host.E) D.host.E).smul_mem o hx`. Rewrite `h` using `[Algebra.smul_def]`. Conclude with `h`.
-/
theorem fi_smul_mem {I : FI} {x : D.host.E} (hx : x ∈ I) (o : 𝓞 D.host.E) : (o : D.host.E) * x ∈ I := by
  have h := (I : Submodule (𝓞 D.host.E) D.host.E).smul_mem o hx
  rw [Algebra.smul_def] at h
  exact h

/- English proof (translation)
Unfold `latSpanS at hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨b, t, ht, rfl⟩` from `hz`. Use `⟨fun a => ?_, fun a => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_smul, hfe, smul_eq_mul] split_ifs with hab`. Substitute `hab` using the available equality. Simplify using `using ht`. Rewrite using `[mul_zero]`. Conclude with `Submodule.zero_mem (aaD D a : Submodule (𝓞 D.host.E) D.host.E)`.

Rewrite using `[map_smul, X.ee, smul_zero]`. Rewrite using `[pW_smul, pW_e, smul_zero]`. Consider the case `zero => exact ⟨fun a => by rw [map_zero]; exact Submodule.zero_mem (aaD D a : Submodule (𝓞 D.host.E) D.host.E), fun a => by simp, by simpa using pW_smul X 0 0⟩`. Consider the case `add z w _ _ hz hw`. Use `⟨fun a => ?_, fun a => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add]`. Conclude with `Submodule.add_mem (aaD D a : Submodule (𝓞 D.host.E) D.host.E) (hz.1 a) (hw.1 a)`. Rewrite using `[map_add, hz.2.1 a, hw.2.1 a, add_zero]`. Rewrite using `[pW_add, hz.2.2, hw.2.2, add_zero]`. Consider the case `smul o z _ hz`.

Rewrite using `[← algebraMap_smul D.host.E o z]`. Use `⟨fun a => ?_, fun a => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul]`. Conclude with `fi_smul_mem (hz.1 a) o`. Rewrite using `[map_smul, hz.2.1 a, smul_zero]`.

Rewrite using `[pW_smul, hz.2.2, smul_zero]`.
-/
theorem coef_span_e (y : (VS D).V) (hy : y ∈ latSpanS (fun a => aaD D a) X.eX) :
    (∀ a, (VS D).hT (X.fY a) y ∈ aaD D a) ∧ (∀ a, (VS D).hT (X.eX a) y = 0) ∧ pW X y = 0 := by
  unfold latSpanS at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, t, ht, rfl⟩ := hz
    refine ⟨fun a => ?_, fun a => ?_, ?_⟩
    · rw [map_smul, hfe, smul_eq_mul]
      split_ifs with hab
      · subst hab
        simpa using ht
      · rw [mul_zero]
        exact Submodule.zero_mem (aaD D a : Submodule (𝓞 D.host.E) D.host.E)
    · rw [map_smul, X.ee, smul_zero]
    · rw [pW_smul, pW_e, smul_zero]
  | zero => exact ⟨fun a => by rw [map_zero]; exact Submodule.zero_mem (aaD D a : Submodule (𝓞 D.host.E) D.host.E), fun a => by simp, by simpa using pW_smul X 0 0⟩
  | add z w _ _ hz hw =>
    refine ⟨fun a => ?_, fun a => ?_, ?_⟩
    · rw [map_add]
      exact Submodule.add_mem (aaD D a : Submodule (𝓞 D.host.E) D.host.E) (hz.1 a) (hw.1 a)
    · rw [map_add, hz.2.1 a, hw.2.1 a, add_zero]
    · rw [pW_add, hz.2.2, hw.2.2, add_zero]
  | smul o z _ hz =>
    rw [← algebraMap_smul D.host.E o z]
    refine ⟨fun a => ?_, fun a => ?_, ?_⟩
    · rw [map_smul, smul_eq_mul]
      exact fi_smul_mem (hz.1 a) o
    · rw [map_smul, hz.2.1 a, smul_zero]
    · rw [pW_smul, hz.2.2, smul_zero]

/- English proof (translation)
Unfold `pW`. Simplify using `[X.ff, X.ef, ite_smul, Finset.sum_ite_eq']`.
-/
theorem pW_f (b : Fin D.R.rS) : pW X (X.fY b) = 0 := by
  unfold pW
  simp [X.ff, X.ef, ite_smul, Finset.sum_ite_eq']

/- English proof (translation)
Unfold `latSpanS at hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨b, t, ht, rfl⟩` from `hz`. Use `⟨fun a => ?_, fun a => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_smul, X.ff, smul_zero]`. Rewrite using `[map_smul, X.ef, smul_eq_mul] split_ifs with hab`. Substitute `hab` using the available equality. Simplify using `using ht`. Rewrite using `[mul_zero]`.

Conclude with `Submodule.zero_mem (((aaD D a)⁻¹ : FI) : Submodule (𝓞 D.host.E) D.host.E)`. Rewrite using `[pW_smul, pW_f, smul_zero]`. Consider the case `zero => exact ⟨fun a => by simp, fun a => by rw [map_zero]; exact Submodule.zero_mem (((aaD D a)⁻¹ : FI) : Submodule (𝓞 D.host.E) D.host.E), by simpa using pW_smul X 0 0⟩`. Consider the case `add z w _ _ hz hw`. Use `⟨fun a => ?_, fun a => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, hz.1 a, hw.1 a, add_zero]`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem (((aaD D a)⁻¹ : FI) : Submodule (𝓞 D.host.E) D.host.E) (hz.2.1 a) (hw.2.1 a)`. Rewrite using `[pW_add, hz.2.2, hw.2.2, add_zero]`. Consider the case `smul o z _ hz`.

Rewrite using `[← algebraMap_smul D.host.E o z]`. Use `⟨fun a => ?_, fun a => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, hz.1 a, smul_zero]`. Rewrite using `[map_smul, smul_eq_mul]`. Conclude with `fi_smul_mem (hz.2.1 a) o`.

Rewrite using `[pW_smul, hz.2.2, smul_zero]`.
-/
theorem coef_span_f (y : (VS D).V) (hy : y ∈ latSpanS (fun a => (aaD D a)⁻¹) X.fY) :
    (∀ a, (VS D).hT (X.fY a) y = 0) ∧ (∀ a, (VS D).hT (X.eX a) y ∈ (aaD D a)⁻¹) ∧ pW X y = 0 := by
  unfold latSpanS at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, t, ht, rfl⟩ := hz
    refine ⟨fun a => ?_, fun a => ?_, ?_⟩
    · rw [map_smul, X.ff, smul_zero]
    · rw [map_smul, X.ef, smul_eq_mul]
      split_ifs with hab
      · subst hab
        simpa using ht
      · rw [mul_zero]
        exact Submodule.zero_mem (((aaD D a)⁻¹ : FI) : Submodule (𝓞 D.host.E) D.host.E)
    · rw [pW_smul, pW_f, smul_zero]
  | zero => exact ⟨fun a => by simp, fun a => by rw [map_zero]; exact Submodule.zero_mem (((aaD D a)⁻¹ : FI) : Submodule (𝓞 D.host.E) D.host.E), by simpa using pW_smul X 0 0⟩
  | add z w _ _ hz hw =>
    refine ⟨fun a => ?_, fun a => ?_, ?_⟩
    · rw [map_add, hz.1 a, hw.1 a, add_zero]
    · rw [map_add]
      exact Submodule.add_mem (((aaD D a)⁻¹ : FI) : Submodule (𝓞 D.host.E) D.host.E) (hz.2.1 a) (hw.2.1 a)
    · rw [pW_add, hz.2.2, hw.2.2, add_zero]
  | smul o z _ hz =>
    rw [← algebraMap_smul D.host.E o z]
    refine ⟨fun a => ?_, fun a => ?_, ?_⟩
    · rw [map_smul, hz.1 a, smul_zero]
    · rw [map_smul, smul_eq_mul]
      exact fi_smul_mem (hz.2.1 a) o
    · rw [pW_smul, hz.2.2, smul_zero]

/- English proof (translation)
Rewrite using `[X.Lam_split]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨y, hy, f, hf, rfl⟩` from `Submodule.mem_sup.mp hx`. Take `⟨e, he, w, hw, rfl⟩` from `Submodule.mem_sup.mp hy`.

Take `⟨he1, he2, he3⟩` from `coef_span_e X e he`. Take `⟨hf1, hf2, hf3⟩` from `coef_span_f X f hf`. Establish `hwp` using `X.Lb_perp w hw`. Establish `hwW : InW X w` using `fun c => hwp c`. Use `⟨fun a => ?_, fun a => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, map_add, (hwp a).2, hf1 a, add_zero, add_zero]`. Conclude with `he1 a`. Rewrite using `[map_add, map_add, (hwp a).1, he2 a, zero_add, zero_add]`. Conclude with `hf2 a`. Rewrite using `[pW_add, pW_add, he3, hf3, pW_of_inW X hwW, zero_add, add_zero]`.

Conclude with `hw`. Introduce and unpack `⟨h1, h2, h3⟩`. Rewrite using `[decomp X x, add_right_comm]`. Use `Submodule.add_mem_sup (Submodule.add_mem_sup ?_ h3) ?_` and prove the remaining obligations. Unfold `latSpanS`.

Conclude with `Submodule.sum_mem _ fun d _ => Submodule.subset_span ⟨d, _, h1 d, rfl⟩`. Unfold `latSpanS`. Conclude with `Submodule.sum_mem _ fun d _ => Submodule.subset_span ⟨d, _, h2 d, rfl⟩`.
-/
theorem mem_hermitianStandardLattice_iff_pairing_integral (x : (VS D).V) : x ∈ (VS D).L0 ↔
    (∀ a, (VS D).hT (X.fY a) x ∈ aaD D a) ∧ (∀ a, (VS D).hT (X.eX a) x ∈ (aaD D a)⁻¹) ∧ pW X x ∈ X.Lb := by
  rw [X.Lam_split]
  constructor
  · intro hx
    obtain ⟨y, hy, f, hf, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨e, he, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨he1, he2, he3⟩ := coef_span_e X e he
    obtain ⟨hf1, hf2, hf3⟩ := coef_span_f X f hf
    have hwp := X.Lb_perp w hw
    have hwW : InW X w := fun c => hwp c
    refine ⟨fun a => ?_, fun a => ?_, ?_⟩
    · rw [map_add, map_add, (hwp a).2, hf1 a, add_zero, add_zero]
      exact he1 a
    · rw [map_add, map_add, (hwp a).1, he2 a, zero_add, zero_add]
      exact hf2 a
    · rw [pW_add, pW_add, he3, hf3, pW_of_inW X hwW, zero_add, add_zero]
      exact hw
  · rintro ⟨h1, h2, h3⟩
    rw [decomp X x, add_right_comm]
    refine Submodule.add_mem_sup (Submodule.add_mem_sup ?_ h3) ?_
    · unfold latSpanS
      exact Submodule.sum_mem _ fun d _ => Submodule.subset_span ⟨d, _, h1 d, rfl⟩
    · unfold latSpanS
      exact Submodule.sum_mem _ fun d _ => Submodule.subset_span ⟨d, _, h2 d, rfl⟩

end LatA

end Formalism.L2.SG.Pf.NcReal.JX.NOf

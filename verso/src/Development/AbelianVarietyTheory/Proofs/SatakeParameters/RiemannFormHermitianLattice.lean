import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SurjectiveOfLocallySurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraEqRangeExteriorPower
open KaehlerDifferential GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

/- English proof (translation)
Rewrite using `[SemiHom.coe_mOm, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp_apply, SemiHom.mDR_ι, SemiHom.m1_D]`.
-/
theorem mOm_ιMulti_D_algebraMap (k K A : Type) [Field k] [Field K] [Algebra k K] [CommRing A]
    [Algebra k A] [Algebra A K] [IsScalarTower k A K] (q : ℕ) (w : Fin q → A) :
    ((semiHom_algebraMap k A K).mOm q (exteriorPower.ιMulti A q fun j => D k A (w j)) : DR k K) =
      ExteriorAlgebra.ιMulti K q fun j => D k K (algebraMap A K (w j)) := by
  rw [SemiHom.coe_mOm, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
    ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp only [Function.comp_apply, SemiHom.mDR_ι, SemiHom.m1_D]

/- English proof (translation)
Use `haveI : IsDomain A := (IsFractionRing.injective A K).isDomain (algebraMap A K)`. Use `haveI : Algebra.FormallyEtale A K := .of_isLocalization (nonZeroDivisors A)`. Establish `hE : IsLocalizedModule (nonZeroDivisors A) (formLin k A K q)` using `(isLocalizedModule_iff_isBaseChange _ K _).2 (isBaseChange_formLin k A K q)`. Use `haveI : Module.Projective A (⋀[A]^q Ω[A⁄k]) := by`. Take `⟨s, hs⟩` from `Module.projective_def'.1 (inferInstance : Module.Projective A Ω[A⁄k])`.

Conclude with `Module.Projective.of_split (exteriorPower.map q s) (exteriorPower.map q (Finsupp.linearCombination A id)) (by rw [← exteriorPower.map_comp, hs, exteriorPower.map_id])`. Use `haveI : Module.Flat A (⋀[A]^q Ω[A⁄k]) := inferInstance`. Use `haveI : Module.IsTorsionFree A (⋀[A]^q Ω[A⁄k]) := Module.Flat.isTorsionFree`. Establish `hinj : Function.Injective (formLin k A K q)`. Introduce `x y hxy`.

Take `⟨c, hc⟩` from `IsLocalizedModule.exists_of_eq (S := nonZeroDivisors A) hxy`. Conclude with `(Module.IsTorsionFree.isSMulRegular (M := ⋀[A]^q Ω[A⁄k]) (isRegular_of_ne_zero (nonZeroDivisors.coe_ne_zero c))) hc`. Establish `hsm : ∀ (a : A) (z : Om k A q), ((semiHom_algebraMap k A K).mOm q (a • z) : DR k K) = algebraMap A K a • ((semiHom_algebraMap k A K).mOm q z : DR k K)` using `fun a z => by`. Rewrite using `[SemiHom.mOm_smul]`. Both sides reduce to the same expression.

Use `⟨hinj, fun y => ⟨fun hy => ?_, ?_⟩⟩` and prove the remaining obligations. Set `S : Submodule k (DR k K)` to `{ carrier := {y | ∃ z : Om k A q, ((semiHom_algebraMap k A K).mOm q z : DR k K) = y} add_mem' := by`. Introduce and unpack `_ _ ⟨a, rfl⟩ ⟨b, rfl⟩`. Conclude with `⟨a + b, by rw [map_add]; rfl⟩`. Use the proof step `zero_mem' := ⟨0, by rw [map_zero]; rfl⟩`.

Use the proof step `smul_mem' := by`. Introduce and unpack `c _ ⟨a, rfl⟩`. Use `⟨algebraMap k A c • a, ?_⟩` and prove the remaining obligations. Rewrite using `[hsm, ← IsScalarTower.algebraMap_apply, algebraMap_smul] }`. Establish `: omB k K B q ≤ S`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨b, hb, v, hv, rfl⟩`. Take `⟨a, rfl⟩` from `(hB b).1 hb`. Use `choose w hw using fun j => (hB (v j)).1 (hv j)`. Use `⟨a • exteriorPower.ιMulti A q (fun j => D k A (w j)), ?_⟩` and prove the remaining obligations.

Rewrite using `[hsm, mOm_ιMulti_D_algebraMap]`. Simplify using `only [hw]`. Conclude with `this hy`. Introduce and unpack `⟨z, rfl⟩`. Establish `htop` using `exteriorPower.ιMulti_span_of_span A q Ω[A⁄k] (span_range_derivation k A)`.

Establish `hz : z ∈ Submodule.span A (⇑(exteriorPower.ιMulti A q) '' {a | Set.range a ⊆ Set.range (D k A)})`. Rewrite using `[htop]`. Conclude with `Submodule.mem_top`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`.

Take `⟨a, ha, rfl⟩` from `hz`. Use `choose w hw using fun j => ha ⟨j, rfl⟩`. Establish `ha' : a = fun j => D k A (w j)` using `funext fun j => (hw j).symm`. Substitute `ha'` using the available equality. Rewrite using `[mOm_ιMulti_D_algebraMap]`.

Conclude with `ιMulti_D_mem_omB_regForms B q fun j => ⟨algebraMap A K (w j), (hB _).2 ⟨w j, rfl⟩⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add _ _ _ _ h1 h2 => rw [map_add]`. Conclude with `add_mem h1 h2`.

Consider the case `smul a z _ h => rw [hsm]`. Conclude with `smul_mem_omB_regForms B q ((hB _).2 ⟨a, rfl⟩) h`.
-/
theorem mOm_injective_and_omB (k K A : Type) [Field k] [Field K] [Algebra k K] [CommRing A]
    [Algebra k A] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K] [Algebra.Smooth k A]
    (B : Subalgebra k K) (hB : ∀ y, y ∈ B ↔ ∃ f : A, algebraMap A K f = y) (q : ℕ) :
    Function.Injective ((semiHom_algebraMap k A K).mOm q) ∧
      ∀ y : DR k K, y ∈ omB k K B q ↔
        ∃ z : Om k A q, ((semiHom_algebraMap k A K).mOm q z : DR k K) = y := by
  haveI : IsDomain A := (IsFractionRing.injective A K).isDomain (algebraMap A K)
  haveI : Algebra.FormallyEtale A K := .of_isLocalization (nonZeroDivisors A)
  have hE : IsLocalizedModule (nonZeroDivisors A) (formLin k A K q) :=
    (isLocalizedModule_iff_isBaseChange _ K _).2 (isBaseChange_formLin k A K q)
  haveI : Module.Projective A (⋀[A]^q Ω[A⁄k]) := by
    obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective A Ω[A⁄k])
    exact Module.Projective.of_split (exteriorPower.map q s)
      (exteriorPower.map q (Finsupp.linearCombination A id))
      (by rw [← exteriorPower.map_comp, hs, exteriorPower.map_id])
  haveI : Module.Flat A (⋀[A]^q Ω[A⁄k]) := inferInstance
  haveI : Module.IsTorsionFree A (⋀[A]^q Ω[A⁄k]) := Module.Flat.isTorsionFree
  have hinj : Function.Injective (formLin k A K q) := by
    intro x y hxy
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors A) hxy
    exact (Module.IsTorsionFree.isSMulRegular (M := ⋀[A]^q Ω[A⁄k])
      (isRegular_of_ne_zero (nonZeroDivisors.coe_ne_zero c))) hc
  have hsm : ∀ (a : A) (z : Om k A q), ((semiHom_algebraMap k A K).mOm q (a • z) : DR k K) =
      algebraMap A K a • ((semiHom_algebraMap k A K).mOm q z : DR k K) := fun a z => by
    rw [SemiHom.mOm_smul]; rfl
  refine ⟨hinj, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · let S : Submodule k (DR k K) :=
      { carrier := {y | ∃ z : Om k A q, ((semiHom_algebraMap k A K).mOm q z : DR k K) = y}
        add_mem' := by
          rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
          exact ⟨a + b, by rw [map_add]; rfl⟩
        zero_mem' := ⟨0, by rw [map_zero]; rfl⟩
        smul_mem' := by
          rintro c _ ⟨a, rfl⟩
          refine ⟨algebraMap k A c • a, ?_⟩
          rw [hsm, ← IsScalarTower.algebraMap_apply, algebraMap_smul] }
    have : omB k K B q ≤ S := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, hb, v, hv, rfl⟩
      obtain ⟨a, rfl⟩ := (hB b).1 hb
      choose w hw using fun j => (hB (v j)).1 (hv j)
      refine ⟨a • exteriorPower.ιMulti A q (fun j => D k A (w j)), ?_⟩
      rw [hsm, mOm_ιMulti_D_algebraMap]
      simp only [hw]
    exact this hy
  · rintro ⟨z, rfl⟩
    have htop := exteriorPower.ιMulti_span_of_span A q Ω[A⁄k] (span_range_derivation k A)
    have hz : z ∈ Submodule.span A
        (⇑(exteriorPower.ιMulti A q) '' {a | Set.range a ⊆ Set.range (D k A)}) := by
      rw [htop]; exact Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, rfl⟩ := hz
      choose w hw using fun j => ha ⟨j, rfl⟩
      have ha' : a = fun j => D k A (w j) := funext fun j => (hw j).symm
      subst ha'
      rw [mOm_ιMulti_D_algebraMap]
      exact ιMulti_D_mem_omB_regForms B q fun j => ⟨algebraMap A K (w j), (hB _).2 ⟨w j, rfl⟩⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | smul a z _ h => rw [hsm]; exact smul_mem_omB_regForms B q ((hB _).2 ⟨a, rfl⟩) h

end GlobalTheory.PD

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.VdmSplit

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap
open GlobalTheory.PsCo.Pc1 (Mat)

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `n ε H _ _ σ D E hσ hD Y _ hY hG hK`. Set `Z : Submodule ℂ (TensorProduct ℂ D (Fock n))` to `Y ⊓ LinearMap.ker (dD ε E)`. Establish `hZY : Z ≤ Y` using `inf_le_left`. Use `haveI hZf : FiniteDimensional ℂ Z := Submodule.finiteDimensional_of_le hZY`. Establish `hZK : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Z, wK hD hk y ∈ Z`.

Introduce `k hk y hy`. Use `⟨hK k hk y hy.1, ?_⟩` and prove the remaining obligations. Establish `h0 : dD ε E y = 0` using `hy.2`. Use `show dD ε E (wK hD hk y) = 0`. Rewrite using `[← wK_D hσ hD hk, h0, map_zero]`.

Establish `hZG : ∀ y ∈ Z, gradT y ∈ Z`. Introduce `y hy`. Use `⟨hG y hy.1, ?_⟩` and prove the remaining obligations. Establish `h0 : dD ε E y = 0` using `hy.2`. Use `show dD ε E (gradT y) = 0`.

Use `gradT_D (ε := ε) E y` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`. Conclude with `neg_eq_zero.1 this.symm`. Set `Γ : TSub Z →ₗ[ℂ] TSub Z` to `((gradT.restrict hZG : Z →ₗ[ℂ] Z) : TSub Z →ₗ[ℂ] TSub Z)`. Use `⟨Z, hZf, hZK, Γ, hZY, fun y hy => hy.2, fun k hk => ?_⟩` and prove the remaining obligations.

Establish `hU : IsInfUnitary ε E` using `isInfUnitary_of_isDerivedOn hσ hD`. Set `Dl : TSub Y →ₗ[ℂ] TSub Y` to `(((dD ε E).restrict hY : Y →ₗ[ℂ] Y) : TSub Y →ₗ[ℂ] TSub Y)`. Set `Γy : TSub Y →ₗ[ℂ] TSub Y` to `((gradT.restrict hG : Y →ₗ[ℂ] Y) : TSub Y →ₗ[ℂ] TSub Y)`. Set `B : TSub Y →ₗ[ℂ] TSub Y` to `(((wK hD hk).restrict (hK k hk) : Y →ₗ[ℂ] Y) : TSub Y →ₗ[ℂ] TSub Y)`. Take `⟨hker, htr⟩` from `str_eq_str_ker Dl Γy B (fun x y => by rw [tsub_inner, tsub_inner]; exact tform_D hU _ _) (fun x => Subtype.ext (gradT_D E _)) (fun x => Subtype.ext (wK_D hσ hD hk _))`.

Establish `h1 : LinearMap.trace ℂ Y ((gradT ∘ₗ wK hD hk).restrict (fun y hy => hG _ (hK k hk y hy))) = LinearMap.trace ℂ (TSub Y) (Γy ∘ₗ B)` using `rfl`. Rewrite using `[h1, htr]`. Establish `hmemZ : ∀ x : LinearMap.ker Dl, tsubVal Y (x : TSub Y) ∈ Z`. Introduce `x`. Establish `hx : Dl (x : TSub Y) = 0` using `x.2`.

Conclude with `⟨tsubVal_mem (x : TSub Y), congrArg (tsubVal Y) hx⟩`. Set `f : LinearMap.ker Dl →ₗ[ℂ] TSub Z` to `{ toFun := fun x => ((⟨tsubVal Y (x : TSub Y), hmemZ x⟩ : Z) : TSub Z) map_add' := fun x y => rfl map_smul' := fun c x => rfl }`. Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`.

Establish `: tsubVal Y (x : TSub Y) = tsubVal Y (y : TSub Y)` using `congrArg (tsubVal Z) hxy`. Conclude with `Subtype.ext (tsubVal_injective this)`. Introduce `z`. Establish `hzY : tsubVal Z z ∈ Y` using `hZY (tsubVal_mem z)`. Set `x : TSub Y` to `((⟨tsubVal Z z, hzY⟩ : Y) : TSub Y)`.

Establish `hx : x ∈ LinearMap.ker Dl`. Rewrite using `[LinearMap.mem_ker]`. Apply `tsubVal_injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `(tsubVal_mem z).2`.

Conclude with `⟨⟨x, hx⟩, rfl⟩`. Set `e` to `LinearEquiv.ofBijective f hf`. Rewrite using `[← LinearMap.trace_conj' _ e]`. Use `congr 1`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `z`. Rewrite using `[LinearEquiv.conj_apply_apply]`. Apply `tsubVal_injective` to reduce the goal to its premises. Take `⟨x, rfl⟩` from `e.surjective z`. Rewrite using `[LinearEquiv.symm_apply_apply]`.

Use `show tsubVal Z (f ((Γy ∘ₗ B).restrict hker x)) = tsubVal Z (Γ (tOp hD hZK k (f x)))`. Establish `hΓ : ∀ w : TSub Z, tsubVal Z (Γ w) = gradT (tsubVal Z w)` using `fun w => rfl`. Rewrite using `[hΓ, tOp_apply hD hZK hk]`. Both sides reduce to the same expression.
-/
theorem supertrace_carriedBy_diracKernel : StrKer := by
  intro n ε H _ _ σ D E hσ hD Y _ hY hG hK
  classical
  let Z : Submodule ℂ (TensorProduct ℂ D (Fock n)) := Y ⊓ LinearMap.ker (dD ε E)
  have hZY : Z ≤ Y := inf_le_left
  haveI hZf : FiniteDimensional ℂ Z := Submodule.finiteDimensional_of_le hZY
  have hZK : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Z, wK hD hk y ∈ Z := by
    intro k hk y hy
    refine ⟨hK k hk y hy.1, ?_⟩
    have h0 : dD ε E y = 0 := hy.2
    show dD ε E (wK hD hk y) = 0
    rw [← wK_D hσ hD hk, h0, map_zero]
  have hZG : ∀ y ∈ Z, gradT y ∈ Z := by
    intro y hy
    refine ⟨hG y hy.1, ?_⟩
    have h0 : dD ε E y = 0 := hy.2
    show dD ε E (gradT y) = 0
    have := gradT_D (ε := ε) E y
    rw [h0, map_zero] at this
    exact neg_eq_zero.1 this.symm
  let Γ : TSub Z →ₗ[ℂ] TSub Z := ((gradT.restrict hZG : Z →ₗ[ℂ] Z) : TSub Z →ₗ[ℂ] TSub Z)
  refine ⟨Z, hZf, hZK, Γ, hZY, fun y hy => hy.2, fun k hk => ?_⟩
  have hU : IsInfUnitary ε E := isInfUnitary_of_isDerivedOn hσ hD
  let Dl : TSub Y →ₗ[ℂ] TSub Y := (((dD ε E).restrict hY : Y →ₗ[ℂ] Y) : TSub Y →ₗ[ℂ] TSub Y)
  let Γy : TSub Y →ₗ[ℂ] TSub Y := ((gradT.restrict hG : Y →ₗ[ℂ] Y) : TSub Y →ₗ[ℂ] TSub Y)
  let B : TSub Y →ₗ[ℂ] TSub Y := (((wK hD hk).restrict (hK k hk) : Y →ₗ[ℂ] Y) : TSub Y →ₗ[ℂ] TSub Y)
  obtain ⟨hker, htr⟩ := str_eq_str_ker Dl Γy B
    (fun x y => by rw [tsub_inner, tsub_inner]; exact tform_D hU _ _)
    (fun x => Subtype.ext (gradT_D E _)) (fun x => Subtype.ext (wK_D hσ hD hk _))
  have h1 : LinearMap.trace ℂ Y ((gradT ∘ₗ wK hD hk).restrict (fun y hy => hG _ (hK k hk y hy))) =
      LinearMap.trace ℂ (TSub Y) (Γy ∘ₗ B) := rfl
  rw [h1, htr]
  have hmemZ : ∀ x : LinearMap.ker Dl, tsubVal Y (x : TSub Y) ∈ Z := by
    intro x
    have hx : Dl (x : TSub Y) = 0 := x.2
    exact ⟨tsubVal_mem (x : TSub Y), congrArg (tsubVal Y) hx⟩
  let f : LinearMap.ker Dl →ₗ[ℂ] TSub Z :=
    { toFun := fun x => ((⟨tsubVal Y (x : TSub Y), hmemZ x⟩ : Z) : TSub Z)
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have : tsubVal Y (x : TSub Y) = tsubVal Y (y : TSub Y) := congrArg (tsubVal Z) hxy
      exact Subtype.ext (tsubVal_injective this)
    · intro z
      have hzY : tsubVal Z z ∈ Y := hZY (tsubVal_mem z)
      let x : TSub Y := ((⟨tsubVal Z z, hzY⟩ : Y) : TSub Y)
      have hx : x ∈ LinearMap.ker Dl := by
        rw [LinearMap.mem_ker]
        apply tsubVal_injective
        rw [map_zero]
        exact (tsubVal_mem z).2
      exact ⟨⟨x, hx⟩, rfl⟩
  let e := LinearEquiv.ofBijective f hf
  rw [← LinearMap.trace_conj' _ e]
  congr 1
  apply LinearMap.ext
  intro z
  rw [LinearEquiv.conj_apply_apply]
  apply tsubVal_injective
  obtain ⟨x, rfl⟩ := e.surjective z
  rw [LinearEquiv.symm_apply_apply]
  show tsubVal Z (f ((Γy ∘ₗ B).restrict hker x)) = tsubVal Z (Γ (tOp hD hZK k (f x)))
  have hΓ : ∀ w : TSub Z, tsubVal Z (Γ w) = gradT (tsubVal Z w) := fun w => rfl
  rw [hΓ, tOp_apply hD hZK hk]
  rfl

end GlobalTheory.PsCo.PcEF

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineClassRestrictDecompositionGroupStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasWeightNegOfCyclotomicPowOnInertiaStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineCocycleCoboundaryOfNegativeWeightStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix

namespace GlobalTheory.Ord2

/- English proof (translation)
Introduce `hP l _ Ω _ _ _ e S A W hN z hz hbk`. Establish `hcol : ∀ s x, Loc.colRep W s x = mat W s *ᵥ x` using `fun s x => by`. Simplify using `[Loc.colRep, Matrix.toLin'_apply]`. Use `⟨fun w hw => ?_, ?_⟩` and prove the remaining obligations. Take `⟨B, hB, x, hx⟩` from `hbk.away w hw`.

Conclude with `⟨B, hB, x, fun s hs => by rw [hx s hs, hcol]⟩`. Take `⟨ι, hιc, hιD, hιS, hιI, hιcyc, hιZ⟩` from `GlobalTheory.T.crystallineClass_restrict_decompositionGroup l Ω W A hN.atL z hz hbk`. Establish `hup : ∀ σ, mat W (ι σ) 1 0 = 0` using `fun σ => hN.upper _ (hιD σ)`. Set `k0 : GQ l →* Qbar l` to `{ toFun := fun σ => mat W (ι σ) 1 1 map_one' := by simp [mat] map_mul' := fun σ τ => by`. Establish `h` using `hup σ`.

Simplify using `only [mat] at h`. Simplify using `only [mat, map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h, zero_mul, zero_add] }`. Set `κ : GQ l →* (Qbar l)ˣ` to `k0.toHomUnits`. Establish `hκ : ∀ σ, (κ σ : Qbar l) = mat W (ι σ) 1 1` using `fun σ => rfl`. Establish `hκc : Continuous fun σ => (κ σ : Qbar l)` using `((Units.continuous_val.comp (hN.cont.comp hιc)).matrix_elem 1 1)`.

Set `f : (Fin 2 → Qbar l) →ₗ[ℚ_[l]] Qbar l` to `LinearMap.proj (R := ℚ_[l]) (φ := fun _ : Fin 2 => Qbar l) 1`. Establish `hf : ∀ σ x, f (((Loc.colRep W).comp ι) σ x) = Loc.chRep κ σ (f x)` using `fun σ x => by`. Establish `h` using `hup σ`. Simplify using `only [mat] at h`. Simplify using `[f, Loc.chRep, hcol, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hκ, mat, h]`.

Establish `hc` using `Loc.z1fCoef (MonoidHom.id (GQ l)) _ _ f (continuous_apply 1) hf _ hιZ`. Take `⟨c, hcO⟩` from `hN.int`. Take `⟨m, hm1, hm⟩` from `hN.wt`. Establish `hw : Loc.HasWeight (MonoidHom.id (GQ l)) κ (-(e : ℤ))`. Use `GlobalTheory.T.hasWeight_neg_of_cyclotomic_pow_on_inertia l κ hκc e (2 * m) (by omega) fun σ hσ => ?_` and prove the remaining obligations.

Establish `hs` using `hιI σ hσ`. Establish `h0` using `hm _ hs`. Establish `hd : (dt W (ι σ) : Qbar l) ^ 2 = 1`. Use `congrArg (fun u : G ℚ Ω →* (Qbar l)ˣ => ((u (ι σ) : (Qbar l)ˣ) : Qbar l)) hN.det2` as an intermediate fact. Simplify using `using this`.

Establish `hdet : (dt W (ι σ) : Qbar l) = mat W (ι σ) 0 0 * mat W (ι σ) 1 1`. Establish `h` using `hup σ`. Simplify using `only [mat] at h`. Simplify using `[dt, Matrix.det_fin_two, mat, h]`. Establish `hcy : (Loc.cycA l l (Qbar l) σ : Qbar l) = eps l (ι σ)`.

Simplify using `only [Loc.cycA, eps, cycBar, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, hιcyc, RingHom.coe_comp, Function.comp_apply]`. Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]`. Both sides reduce to the same expression. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_zpow_eq_zpow_val, zpow_natCast, Units.val_one, hκ, hcy]`.

Rewrite `hd` using `[hdet]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨x, hx⟩` from `GlobalTheory.T.crystallineCocycle_coboundary_of_negative_weight hP l κ hκc c (fun σ => hcO _ 1 1) (-(e : ℤ)) (by have := hN.e_pos; omega) hw _ hc`. Use `⟨x, fun s hs => ?_⟩` and prove the remaining obligations. Take `⟨σ, rfl⟩` from `hιS s hs`.

Use `hx σ` as an intermediate fact. Simplify `this` using `[f, hκ]`.
-/
theorem bk_unr_gr : Loc.LocalPublishedTheorems → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ z ∈ Z1 (Loc.colRep W), IsBK l (Loc.colRep W) z → Unr W z ∧ Gr W A z := by
  intro hP l _ Ω _ _ _ e S A W hN z hz hbk
  have hcol : ∀ s x, Loc.colRep W s x = mat W s *ᵥ x := fun s x => by
    simp [Loc.colRep, Matrix.toLin'_apply]
  refine ⟨fun w hw => ?_, ?_⟩
  · obtain ⟨B, hB, x, hx⟩ := hbk.away w hw
    exact ⟨B, hB, x, fun s hs => by rw [hx s hs, hcol]⟩
  obtain ⟨ι, hιc, hιD, hιS, hιI, hιcyc, hιZ⟩ := GlobalTheory.T.crystallineClass_restrict_decompositionGroup l Ω W A hN.atL z hz hbk
  have hup : ∀ σ, mat W (ι σ) 1 0 = 0 := fun σ => hN.upper _ (hιD σ)
  let k0 : GQ l →* Qbar l :=
    { toFun := fun σ => mat W (ι σ) 1 1
      map_one' := by simp [mat]
      map_mul' := fun σ τ => by
        have h := hup σ
        simp only [mat] at h
        simp only [mat, map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h, zero_mul, zero_add] }
  let κ : GQ l →* (Qbar l)ˣ := k0.toHomUnits
  have hκ : ∀ σ, (κ σ : Qbar l) = mat W (ι σ) 1 1 := fun σ => rfl
  have hκc : Continuous fun σ => (κ σ : Qbar l) :=
    ((Units.continuous_val.comp (hN.cont.comp hιc)).matrix_elem 1 1)
  let f : (Fin 2 → Qbar l) →ₗ[ℚ_[l]] Qbar l := LinearMap.proj (R := ℚ_[l]) (φ := fun _ : Fin 2 => Qbar l) 1
  have hf : ∀ σ x, f (((Loc.colRep W).comp ι) σ x) = Loc.chRep κ σ (f x) := fun σ x => by
    have h := hup σ
    simp only [mat] at h
    simp [f, Loc.chRep, hcol, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hκ, mat, h]
  have hc := Loc.z1fCoef (MonoidHom.id (GQ l)) _ _ f (continuous_apply 1) hf _ hιZ
  obtain ⟨c, hcO⟩ := hN.int
  obtain ⟨m, hm1, hm⟩ := hN.wt
  have hw : Loc.HasWeight (MonoidHom.id (GQ l)) κ (-(e : ℤ)) := by
    refine GlobalTheory.T.hasWeight_neg_of_cyclotomic_pow_on_inertia l κ hκc e (2 * m) (by omega) fun σ hσ => ?_
    have hs := hιI σ hσ
    have h0 := hm _ hs
    have hd : (dt W (ι σ) : Qbar l) ^ 2 = 1 := by
      have := congrArg (fun u : G ℚ Ω →* (Qbar l)ˣ => ((u (ι σ) : (Qbar l)ˣ) : Qbar l)) hN.det2
      simpa using this
    have hdet : (dt W (ι σ) : Qbar l) = mat W (ι σ) 0 0 * mat W (ι σ) 1 1 := by
      have h := hup σ
      simp only [mat] at h
      simp [dt, Matrix.det_fin_two, mat, h]
    have hcy : (Loc.cycA l l (Qbar l) σ : Qbar l) = eps l (ι σ) := by
      simp only [Loc.cycA, eps, cycBar, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, hιcyc, RingHom.coe_comp, Function.comp_apply]
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]
      rfl
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_zpow_eq_zpow_val, zpow_natCast, Units.val_one, hκ, hcy]
    rw [hdet] at hd
    calc (mat W (ι σ) 1 1 * eps l (ι σ) ^ e) ^ (2 * m) = (mat W (ι σ) 1 1) ^ (2 * m) * (eps l (ι σ) ^ (e * m)) ^ 2 := by ring
      _ = ((mat W (ι σ) 0 0 * mat W (ι σ) 1 1) ^ 2) ^ m := by rw [← h0]; ring
      _ = 1 := by rw [hd, one_pow]
  obtain ⟨x, hx⟩ := GlobalTheory.T.crystallineCocycle_coboundary_of_negative_weight hP l κ hκc c (fun σ => hcO _ 1 1) (-(e : ℤ)) (by have := hN.e_pos; omega) hw _ hc
  refine ⟨x, fun s hs => ?_⟩
  obtain ⟨σ, rfl⟩ := hιS s hs
  have := hx σ
  simpa [f, hκ] using this

end GlobalTheory.Ord2

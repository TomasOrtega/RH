import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesEvalOfPowMem
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CohenStructureFiniteOverNormalCompleteSubring

set_option autoImplicit false
open IsLocalRing

namespace GlobalTheory.PlaceInt

section
variable {V : Type} [CommRing V] [IsLocalRing V]

/- English proof (translation)
Simplify using `only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]`.
-/
theorem mem_maximalIdeal_mvPowerSeries_iff {τ : Type} (f : MvPowerSeries τ V) :
    f ∈ maximalIdeal (MvPowerSeries τ V) ↔ MvPowerSeries.constantCoeff f ∈ maximalIdeal V := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]

variable [IsNoetherianRing V] [IsAdicComplete (maximalIdeal V) V]

/- English proof (translation)
Take `⟨n, ⟨e⟩⟩` from `Finite.exists_equiv_fin τ`. Establish `ha : MvPowerSeries.HasSubst (fun i : Fin n => (MvPowerSeries.X (e.symm i) : MvPowerSeries τ V))` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)`. Establish `hb : MvPowerSeries.HasSubst (fun t : τ => (MvPowerSeries.X (e t) : MvPowerSeries (Fin n) V))` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)`. Establish `hba : ∀ f : MvPowerSeries (Fin n) V, MvPowerSeries.substAlgHom (R` using `V) hb (MvPowerSeries.substAlgHom (R := V) ha f) = f := by`. Introduce `f`.

Rewrite using `[MvPowerSeries.substAlgHom_comp_substAlgHom_apply]`. Establish `hX : (fun i : Fin n => MvPowerSeries.substAlgHom (R` using `V) hb (MvPowerSeries.X (e.symm i) : MvPowerSeries τ V)) = MvPowerSeries.X := by`. Use function extensionality and compare the values at `i`. Rewrite using `[MvPowerSeries.substAlgHom_X, Equiv.apply_symm_apply]`. Rewrite using `[MvPowerSeries.substAlgHom_apply, hX, MvPowerSeries.subst_self, id]`.

Establish `hab : ∀ g : MvPowerSeries τ V, MvPowerSeries.substAlgHom (R` using `V) ha (MvPowerSeries.substAlgHom (R := V) hb g) = g := by`. Introduce `g`. Rewrite using `[MvPowerSeries.substAlgHom_comp_substAlgHom_apply]`. Establish `hX : (fun t : τ => MvPowerSeries.substAlgHom (R` using `V) ha (MvPowerSeries.X (e t) : MvPowerSeries (Fin n) V)) = MvPowerSeries.X := by`. Use function extensionality and compare the values at `t`.

Rewrite using `[MvPowerSeries.substAlgHom_X, Equiv.symm_apply_apply]`. Rewrite using `[MvPowerSeries.substAlgHom_apply, hX, MvPowerSeries.subst_self, id]`. Set `E : MvPowerSeries (Fin n) V ≃+* MvPowerSeries τ V` to `{ toFun := MvPowerSeries.substAlgHom (R := V) ha invFun := MvPowerSeries.substAlgHom (R := V) hb left_inv := hba right_inv := hab map_mul' := map_mul _ map_add' := map_add _ }`. Use `GlobalTheory.CohenStructure.isAdicComplete_mvPowerSeries V n` as an intermediate fact. Conclude with `GlobalTheory.CohenStructure.isAdicComplete_of_ringEquiv E`.
-/
theorem isAdicComplete_mvPowerSeries_finite (τ : Type) [Finite τ] :
    IsAdicComplete (maximalIdeal (MvPowerSeries τ V)) (MvPowerSeries τ V) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin τ

  have ha : MvPowerSeries.HasSubst
      (fun i : Fin n => (MvPowerSeries.X (e.symm i) : MvPowerSeries τ V)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hb : MvPowerSeries.HasSubst
      (fun t : τ => (MvPowerSeries.X (e t) : MvPowerSeries (Fin n) V)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hba : ∀ f : MvPowerSeries (Fin n) V,
      MvPowerSeries.substAlgHom (R := V) hb (MvPowerSeries.substAlgHom (R := V) ha f) = f := by
    intro f
    rw [MvPowerSeries.substAlgHom_comp_substAlgHom_apply]
    have hX : (fun i : Fin n => MvPowerSeries.substAlgHom (R := V) hb
        (MvPowerSeries.X (e.symm i) : MvPowerSeries τ V)) = MvPowerSeries.X := by
      funext i
      rw [MvPowerSeries.substAlgHom_X, Equiv.apply_symm_apply]
    rw [MvPowerSeries.substAlgHom_apply, hX, MvPowerSeries.subst_self, id]
  have hab : ∀ g : MvPowerSeries τ V,
      MvPowerSeries.substAlgHom (R := V) ha (MvPowerSeries.substAlgHom (R := V) hb g) = g := by
    intro g
    rw [MvPowerSeries.substAlgHom_comp_substAlgHom_apply]
    have hX : (fun t : τ => MvPowerSeries.substAlgHom (R := V) ha
        (MvPowerSeries.X (e t) : MvPowerSeries (Fin n) V)) = MvPowerSeries.X := by
      funext t
      rw [MvPowerSeries.substAlgHom_X, Equiv.symm_apply_apply]
    rw [MvPowerSeries.substAlgHom_apply, hX, MvPowerSeries.subst_self, id]
  let E : MvPowerSeries (Fin n) V ≃+* MvPowerSeries τ V :=
    { toFun := MvPowerSeries.substAlgHom (R := V) ha
      invFun := MvPowerSeries.substAlgHom (R := V) hb
      left_inv := hba
      right_inv := hab
      map_mul' := map_mul _
      map_add' := map_add _ }
  have := GlobalTheory.CohenStructure.isAdicComplete_mvPowerSeries V n
  exact GlobalTheory.CohenStructure.isAdicComplete_of_ringEquiv E

variable {σ τ : Type} [Finite σ] [Finite τ]

/- English proof (translation)
Use `isAdicComplete_mvPowerSeries_finite (V := V) τ` as an intermediate fact. Use `(GlobalTheory.mvPowerSeries_eval_of_pow_mem (MvPowerSeries τ V) (maximalIdeal _) σ a (fun j => ⟨1, ?_⟩)).1 inferInstance V` and prove the remaining obligations. Rewrite using `[pow_one, mem_maximalIdeal_mvPowerSeries_iff]`. Conclude with `ha j`.
-/
theorem exists_algHom_evC (a : σ → MvPowerSeries τ V)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V) :
    ∃ ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, ∀ j, ψ (MvPowerSeries.X j) = a j := by
  have := isAdicComplete_mvPowerSeries_finite (V := V) τ
  refine (GlobalTheory.mvPowerSeries_eval_of_pow_mem (MvPowerSeries τ V) (maximalIdeal _) σ a
    (fun j => ⟨1, ?_⟩)).1 inferInstance V
  rw [pow_one, mem_maximalIdeal_mvPowerSeries_iff]
  exact ha j

/- English proof (translation)
Use `isAdicComplete_mvPowerSeries_finite (V := V) τ` as an intermediate fact. Establish `key` using `(GlobalTheory.mvPowerSeries_eval_of_pow_mem (MvPowerSeries τ V) (maximalIdeal _) σ a (fun j => ⟨1, by rw [pow_one, mem_maximalIdeal_mvPowerSeries_iff]; exact ha j⟩)).2 inferInstance V ψ.toRingHom ψ'.toRingHom (fun t => by show ψ (MvPowerSeries.C t) = ψ' (MvPowerSeries.C t)`. Establish `hC : (MvPowerSeries.C t : MvPowerSeries σ V) = algebraMap V (MvPowerSeries σ V) t`. Rewrite using `[MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]`. Rewrite using `[hC, ψ.commutes, ψ'.commutes]) h h'`.

Conclude with `AlgHom.ext fun f => RingHom.congr_fun key f`.
-/
private theorem mvPowerSeries_algHom_ext_of_X_eq (a : σ → MvPowerSeries τ V)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V)
    (ψ ψ' : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V) (h : ∀ j, ψ (MvPowerSeries.X j) = a j)
    (h' : ∀ j, ψ' (MvPowerSeries.X j) = a j) : ψ = ψ' := by
  have := isAdicComplete_mvPowerSeries_finite (V := V) τ
  have key := (GlobalTheory.mvPowerSeries_eval_of_pow_mem (MvPowerSeries τ V) (maximalIdeal _) σ a
    (fun j => ⟨1, by rw [pow_one, mem_maximalIdeal_mvPowerSeries_iff]; exact ha j⟩)).2
    inferInstance V ψ.toRingHom ψ'.toRingHom
    (fun t => by
      show ψ (MvPowerSeries.C t) = ψ' (MvPowerSeries.C t)
      have hC : (MvPowerSeries.C t : MvPowerSeries σ V) = algebraMap V (MvPowerSeries σ V) t := by
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rw [hC, ψ.commutes, ψ'.commutes]) h h'
  exact AlgHom.ext fun f => RingHom.congr_fun key f

/- English proof (translation)
Establish `h : ∃ φ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, ∀ j, φ (MvPowerSeries.X j) = a j` using `⟨ψ, hψ⟩`. Rewrite using `[evC, dif_pos h, mvPowerSeries_algHom_ext_of_X_eq a ha h.choose ψ h.choose_spec hψ]`.
-/
theorem evC_eq_algHom (a : σ → MvPowerSeries τ V)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V)
    (ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V) (hψ : ∀ j, ψ (MvPowerSeries.X j) = a j)
    (f : MvPowerSeries σ V) : evC a f = ψ f := by
  have h : ∃ φ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, ∀ j, φ (MvPowerSeries.X j) = a j :=
    ⟨ψ, hψ⟩
  rw [evC, dif_pos h, mvPowerSeries_algHom_ext_of_X_eq a ha h.choose ψ h.choose_spec hψ]

/- English proof (translation)
Take `⟨ψ, hψ⟩` from `exists_algHom_evC a ha`. Rewrite using `[evC_eq_algHom a ha ψ hψ f]`. Set `χ₁ : MvPowerSeries σ V →+* ResidueField V` to `(residue V).comp (MvPowerSeries.constantCoeff.comp ψ.toRingHom)`. Set `χ₂ : MvPowerSeries σ V →+* ResidueField V` to `(residue V).comp MvPowerSeries.constantCoeff`. Establish `hC : ∀ t : V, ψ (MvPowerSeries.C t) = MvPowerSeries.C t` using `fun t => by`.

Use `ψ.commutes t` as an intermediate fact. Rewrite `this` using `[MvPowerSeries.algebraMap_apply, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]`. Then use the resulting hypothesis. Establish `key` using `(GlobalTheory.mvPowerSeries_eval_of_pow_mem (ResidueField V) ⊥ σ (fun _ => 0) (fun _ => ⟨1, by simp⟩)).2 inferInstance V χ₁ χ₂ (fun t => by simp [χ₁, χ₂, hC]) (fun j => by`. Simplify using `only [χ₁, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hψ]`. Conclude with `(residue_eq_zero_iff _).2 (ha j))`.

Use the proof step `(fun j => by simp [χ₂])`. Establish `hf'` using `RingHom.congr_fun key f`. Simplify using `only [χ₁, χ₂, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf'`. Rewrite using `[← residue_eq_zero_iff, hf']`. Conclude with `(residue_eq_zero_iff _).2 hf`.
-/
theorem constantCoeff_evC_mem (a : σ → MvPowerSeries τ V)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V) (f : MvPowerSeries σ V)
    (hf : MvPowerSeries.constantCoeff f ∈ maximalIdeal V) :
    MvPowerSeries.constantCoeff (evC a f) ∈ maximalIdeal V := by
  obtain ⟨ψ, hψ⟩ := exists_algHom_evC a ha
  rw [evC_eq_algHom a ha ψ hψ f]

  let χ₁ : MvPowerSeries σ V →+* ResidueField V :=
    (residue V).comp (MvPowerSeries.constantCoeff.comp ψ.toRingHom)
  let χ₂ : MvPowerSeries σ V →+* ResidueField V := (residue V).comp MvPowerSeries.constantCoeff
  have hC : ∀ t : V, ψ (MvPowerSeries.C t) = MvPowerSeries.C t := fun t => by
    have := ψ.commutes t
    rwa [MvPowerSeries.algebraMap_apply, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply] at this
  have key := (GlobalTheory.mvPowerSeries_eval_of_pow_mem (ResidueField V) ⊥ σ (fun _ => 0)
    (fun _ => ⟨1, by simp⟩)).2 inferInstance V χ₁ χ₂
    (fun t => by simp [χ₁, χ₂, hC])
    (fun j => by
      simp only [χ₁, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hψ]
      exact (residue_eq_zero_iff _).2 (ha j))
    (fun j => by simp [χ₂])
  have hf' := RingHom.congr_fun key f
  simp only [χ₁, χ₂, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf'
  rw [← residue_eq_zero_iff, hf']
  exact (residue_eq_zero_iff _).2 hf

end

/- English proof (translation)
Introduce `V _ _ _ _ _ σ τ ρ _ _ _ a ha`. Use `⟨?_, fun f hf => constantCoeff_evC_mem a ha f hf, ?_, ?_⟩` and prove the remaining obligations. Take `⟨ψ, hψ⟩` from `exists_algHom_evC a ha`. Conclude with `⟨ψ, hψ, fun f => evC_eq_algHom a ha ψ hψ f⟩`. Introduce `h0 f`.

Establish `hs : MvPowerSeries.HasSubst a` using `MvPowerSeries.hasSubst_of_constantCoeff_zero h0`. Rewrite using `[evC_eq_algHom a ha (MvPowerSeries.substAlgHom (R := V) hs) (fun j => MvPowerSeries.substAlgHom_X hs j) f]`. Conclude with `MvPowerSeries.substAlgHom_apply hs f`. Introduce `b hb f`. Take `⟨ψa, hψa⟩` from `exists_algHom_evC a ha`.

Take `⟨ψb, hψb⟩` from `exists_algHom_evC b hb`. Establish `hc : ∀ j, MvPowerSeries.constantCoeff (evC b (a j)) ∈ maximalIdeal V` using `fun j => constantCoeff_evC_mem b hb (a j) (ha j)`. Rewrite using `[evC_eq_algHom (fun j => evC b (a j)) hc (ψb.comp ψa) (fun j => by rw [AlgHom.comp_apply, hψa, evC_eq_algHom b hb ψb hψb]) f, evC_eq_algHom a ha ψa hψa, evC_eq_algHom b hb ψb hψb, AlgHom.comp_apply]`.
-/
theorem evC_spec : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (σ τ ρ : Type) [Finite σ] [Finite τ] [Finite ρ] (a : σ → MvPowerSeries τ V), (∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V) → (∃ ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, (∀ j, ψ (MvPowerSeries.X j) = a j) ∧ ∀ f, evC a f = ψ f) ∧ (∀ f, MvPowerSeries.constantCoeff f ∈ maximalIdeal V → MvPowerSeries.constantCoeff (evC a f) ∈ maximalIdeal V) ∧ ((∀ j, MvPowerSeries.constantCoeff (a j) = 0) → ∀ f, evC a f = MvPowerSeries.subst a f) ∧ ∀ b : τ → MvPowerSeries ρ V, (∀ j, MvPowerSeries.constantCoeff (b j) ∈ maximalIdeal V) → ∀ f, evC b (evC a f) = evC (fun j => evC b (a j)) f := by
  intro V _ _ _ _ _ σ τ ρ _ _ _ a ha
  refine ⟨?_, fun f hf => constantCoeff_evC_mem a ha f hf, ?_, ?_⟩
  · obtain ⟨ψ, hψ⟩ := exists_algHom_evC a ha
    exact ⟨ψ, hψ, fun f => evC_eq_algHom a ha ψ hψ f⟩
  · intro h0 f
    have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero h0
    rw [evC_eq_algHom a ha (MvPowerSeries.substAlgHom (R := V) hs)
      (fun j => MvPowerSeries.substAlgHom_X hs j) f]
    exact MvPowerSeries.substAlgHom_apply hs f
  · intro b hb f
    obtain ⟨ψa, hψa⟩ := exists_algHom_evC a ha
    obtain ⟨ψb, hψb⟩ := exists_algHom_evC b hb
    have hc : ∀ j, MvPowerSeries.constantCoeff (evC b (a j)) ∈ maximalIdeal V :=
      fun j => constantCoeff_evC_mem b hb (a j) (ha j)

    rw [evC_eq_algHom (fun j => evC b (a j)) hc (ψb.comp ψa)
      (fun j => by rw [AlgHom.comp_apply, hψa, evC_eq_algHom b hb ψb hψb]) f,
      evC_eq_algHom a ha ψa hψa, evC_eq_algHom b hb ψb hψb, AlgHom.comp_apply]

end GlobalTheory.PlaceInt

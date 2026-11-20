import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsWeaklyRegularMvPowerSeriesOfFiniteColengthStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FlatMvPowerSeriesOfIsNoetherianRingStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FlatQuotientWeaklyRegularStatement

open IsLocalRing TensorProduct

namespace GlobalTheory.FiniteColength

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `r hr`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker]`. Express the relevant statement in the definitionally equal form `MvPowerSeries.map (residue T) (MvPowerSeries.C r) = 0`.

Rewrite using `[MvPowerSeries.map_C, (residue_eq_zero_iff r).2 hr, map_zero]`. Introduce `g hg`. Use `GlobalTheory.FormalIsogeny.mem_map_C_of_coeff_mem (IsNoetherian.noetherian _) fun d => ?_` and prove the remaining obligations. Rewrite using `[← residue_eq_zero_iff, ← MvPowerSeries.coeff_map, RingHom.mem_ker.1 hg, map_zero]`.
-/
theorem map_maximalIdeal_eq_ker_map_residue (T : Type) [CommRing T] [IsLocalRing T]
    [IsNoetherianRing T] (σ : Type) :
    (maximalIdeal T).map (algebraMap T (MvPowerSeries σ T)) =
      RingHom.ker (MvPowerSeries.map (σ := σ) (residue T)) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change MvPowerSeries.map (residue T) (MvPowerSeries.C r) = 0
    rw [MvPowerSeries.map_C, (residue_eq_zero_iff r).2 hr, map_zero]
  · intro g hg
    refine GlobalTheory.FormalIsogeny.mem_map_C_of_coeff_mem (IsNoetherian.noetherian _) fun d => ?_
    rw [← residue_eq_zero_iff, ← MvPowerSeries.coeff_map, RingHom.mem_ker.1 hg, map_zero]

/- English proof (translation)
Introduce `T _ _ _ hc σ _ n e f h0 hM`. Establish `hfin : Module.Finite T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f))` using `(GlobalTheory.FormalIsogeny.finiteReduction_iff.2 hM).finite_quotient`. Use `⟨?_, hfin⟩` and prove the remaining obligations. Use `haveI : Module.Flat T (MvPowerSeries σ T) := GlobalTheory.T.module_flat_mvPowerSeries_of_isNoetherianRing T σ`. Use `haveI : IsLocalHom (algebraMap T (MvPowerSeries σ T)) := ⟨fun r hr => by`.

Use `MvPowerSeries.isUnit_iff_constantCoeff.1 hr` as an intermediate fact. Conclude with `this⟩`. Establish `hreg` using `GlobalTheory.T.isWeaklyRegular_mvPowerSeries_of_finite_colength (ResidueField T) σ n e (fun s => MvPowerSeries.map (residue T) (f (e.symm s))) (fun s => by rw [MvPowerSeries.constantCoeff_map, h0, map_zero]) (by`. Establish `: (Set.range fun s => MvPowerSeries.map (σ` using `σ) (residue T) (f (e.symm s))) = Set.range fun j => MvPowerSeries.map (σ := σ) (residue T) (f j) := e.symm.surjective.range_comp fun j => MvPowerSeries.map (σ := σ) (residue T) (f j)`. Rewrite using `[this]`.

Conclude with `hM)`. Simplify using `only [Equiv.symm_apply_apply] at hreg`. Set `φ : (MvPowerSeries σ T ⧸ (maximalIdeal T).map (algebraMap T (MvPowerSeries σ T))) ≃+* MvPowerSeries σ (ResidueField T)` to `(Ideal.quotEquivOfEq (map_maximalIdeal_eq_ker_map_residue T σ)).trans (RingHom.quotientKerEquivOfSurjective (GlobalTheory.FormalIsogeny.map_surjective_of_surjective (σ := σ) (residue_surjective (R := T))))`. Establish `hφ : ∀ g, φ (Ideal.Quotient.mk _ g) = MvPowerSeries.map (residue T) g` using `fun g => rfl`. Establish `hreg' : RingTheory.Sequence.IsWeaklyRegular (MvPowerSeries σ T ⧸ (maximalIdeal T).map (algebraMap T (MvPowerSeries σ T))) (List.ofFn f)`.

Use `(AddEquiv.isWeaklyRegular_congr (e := φ.toAddEquiv) ?_).2 hreg` and prove the remaining obligations. Establish `: (List.ofFn fun i => MvPowerSeries.map (σ` using `σ) (residue T) (f i)) = (List.ofFn f).map (MvPowerSeries.map (σ := σ) (residue T)) := by`. Rewrite using `[List.map_ofFn]`. Both sides reduce to the same expression. Rewrite using `[this, List.forall₂_map_right_iff, List.forall₂_same]`.

Introduce `r _ x`. Express the relevant statement in the definitionally equal form `φ (Ideal.Quotient.mk _ r * x) = _ * φ x`. Rewrite using `[map_mul, hφ]`. Establish `hflat` using `GlobalTheory.T.flat_quotient_weakly_regular T (MvPowerSeries σ T) (List.ofFn f) (fun r hr => by`. Take `⟨j, rfl⟩` from `(List.mem_ofFn' _ _).1 hr`.

Rewrite using `[mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, h0]`. Conclude with `not_isUnit_zero) hreg'`. Establish `hI : Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f)`. Unfold `Ideal.ofList`. Use `congr 1`.

Use extensionality with `r`. Conclude with `List.mem_ofFn' _ _`. Rewrite `hflat` using `[hI]`. Conclude with `Module.free_of_flat_of_isLocalRing`.
-/
theorem free_finite_quotient : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T], IsAdicComplete (maximalIdeal T) T → ∀ (σ : Type) [Finite σ] (n : ℕ) (e : Fin n ≃ σ) (f : Fin n → MvPowerSeries σ T), (∀ j, MvPowerSeries.constantCoeff (f j) = 0) → (∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ (ResidueField T))) ^ M ≤ Ideal.span (Set.range fun j => MvPowerSeries.map (residue T) (f j))) → Module.Free T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f)) ∧ Module.Finite T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f)) := by
  intro T _ _ _ hc σ _ n e f h0 hM
  have hfin : Module.Finite T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f)) :=
    (GlobalTheory.FormalIsogeny.finiteReduction_iff.2 hM).finite_quotient
  refine ⟨?_, hfin⟩
  haveI : Module.Flat T (MvPowerSeries σ T) := GlobalTheory.T.module_flat_mvPowerSeries_of_isNoetherianRing T σ
  haveI : IsLocalHom (algebraMap T (MvPowerSeries σ T)) := ⟨fun r hr => by
    have := MvPowerSeries.isUnit_iff_constantCoeff.1 hr
    exact this⟩
  have hreg := GlobalTheory.T.isWeaklyRegular_mvPowerSeries_of_finite_colength (ResidueField T) σ n e
    (fun s => MvPowerSeries.map (residue T) (f (e.symm s)))
    (fun s => by rw [MvPowerSeries.constantCoeff_map, h0, map_zero])
    (by
      have : (Set.range fun s => MvPowerSeries.map (σ := σ) (residue T) (f (e.symm s))) =
          Set.range fun j => MvPowerSeries.map (σ := σ) (residue T) (f j) :=
        e.symm.surjective.range_comp fun j => MvPowerSeries.map (σ := σ) (residue T) (f j)
      rw [this]; exact hM)
  simp only [Equiv.symm_apply_apply] at hreg
  let φ : (MvPowerSeries σ T ⧸ (maximalIdeal T).map (algebraMap T (MvPowerSeries σ T))) ≃+*
      MvPowerSeries σ (ResidueField T) :=
    (Ideal.quotEquivOfEq (map_maximalIdeal_eq_ker_map_residue T σ)).trans
      (RingHom.quotientKerEquivOfSurjective
        (GlobalTheory.FormalIsogeny.map_surjective_of_surjective (σ := σ) (residue_surjective (R := T))))
  have hφ : ∀ g, φ (Ideal.Quotient.mk _ g) = MvPowerSeries.map (residue T) g := fun g => rfl
  have hreg' : RingTheory.Sequence.IsWeaklyRegular
      (MvPowerSeries σ T ⧸ (maximalIdeal T).map (algebraMap T (MvPowerSeries σ T)))
      (List.ofFn f) := by
    refine (AddEquiv.isWeaklyRegular_congr (e := φ.toAddEquiv) ?_).2 hreg
    have : (List.ofFn fun i => MvPowerSeries.map (σ := σ) (residue T) (f i)) =
        (List.ofFn f).map (MvPowerSeries.map (σ := σ) (residue T)) := by
      rw [List.map_ofFn]; rfl
    rw [this, List.forall₂_map_right_iff, List.forall₂_same]
    intro r _ x
    change φ (Ideal.Quotient.mk _ r * x) = _ * φ x
    rw [map_mul, hφ]
  have hflat := GlobalTheory.T.flat_quotient_weakly_regular T (MvPowerSeries σ T) (List.ofFn f) (fun r hr => by
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hr
    rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, h0]
    exact not_isUnit_zero) hreg'
  have hI : Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f) := by
    unfold Ideal.ofList
    congr 1
    ext r
    exact List.mem_ofFn' _ _
  rw [hI] at hflat
  exact Module.free_of_flat_of_isLocalRing

end GlobalTheory.FiniteColength

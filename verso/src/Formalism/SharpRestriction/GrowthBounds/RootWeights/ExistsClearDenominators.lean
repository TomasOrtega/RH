import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightProjectionDiagonalApplyEqSmul
import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantProjectionExtremalFormula
import Lemmata.GeneralBFactLeftAltForm.MQ

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section lat
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_left_alt_form.goal1 .. | (apply Bl.general_b_fact_left_alt_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_alt_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_alt_form.goal1 <;> assumption) | (intros; apply @Bl.genera …`.
-/
theorem exists_clear_denominators_alt (M : Submodule O W) (y : W) (hy : y ∈ MQ (K := KK O) M) : ∃ a : O, a ≠ 0 ∧ a • y ∈ M := by
  first | exact Bl.general_b_fact_left_alt_form.goal1 .. | (apply Bl.general_b_fact_left_alt_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_alt_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_alt_form.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left_alt_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_alt_form.goal1 <;> first | assumption | infer_instance)

def latticeInter (M : Submodule O W) (L : Submodule (KK O) W) : Submodule O L :=
  M.comap (L.subtype.restrictScalars O)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_latticeInter_iff (M : Submodule O W) (L : Submodule (KK O) W) (x : L) : x ∈ latticeInter M L ↔ (x : W) ∈ M := Iff.rfl

/- English proof (translation)
Establish `hN : IsNoetherian O M` using `isNoetherian_of_fg_of_noetherian M hfg`. Use `Submodule.fg_of_fg_map_injective (L.subtype.restrictScalars O) (fun x y h => Subtype.ext h) ?_` and prove the remaining obligations. Use `(isNoetherian_submodule.1 hN) _ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `hx`.

Use `span_eq_top := by`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Take `⟨a, ha, hax⟩` from `exists_clear_denominators_alt M (x : W) (by rw [hMQ]; trivial)`. Establish `ha1 : algebraMap O (KK O) a ≠ 0`.

Simplify using `using (IsFractionRing.injective O (KK O)).ne ha`. Establish `h1 : a • x ∈ latticeInter M L` using `hax`. Establish `h2 : x = (algebraMap O (KK O) a)⁻¹ • (a • x)`. Rewrite using `[← algebraMap_smul (KK O) a x, smul_smul, inv_mul_cancel₀ ha1, one_smul]`. Rewrite using `[h2]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span h1)`.
-/
theorem latticeInter_isLattice (M : Submodule O W) (hfg : M.FG) (hMQ : MQ (K := KK O) M = ⊤) (L : Submodule (KK O) W) :
    Submodule.IsLattice (KK O) (latticeInter M L) where
  fg := by
    have hN : IsNoetherian O M := isNoetherian_of_fg_of_noetherian M hfg
    refine Submodule.fg_of_fg_map_injective (L.subtype.restrictScalars O) (fun x y h => Subtype.ext h) ?_
    refine (isNoetherian_submodule.1 hN) _ ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  span_eq_top := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, ha, hax⟩ := exists_clear_denominators_alt M (x : W) (by rw [hMQ]; trivial)
    have ha1 : algebraMap O (KK O) a ≠ 0 := by
      simpa using (IsFractionRing.injective O (KK O)).ne ha
    have h1 : a • x ∈ latticeInter M L := hax
    have h2 : x = (algebraMap O (KK O) a)⁻¹ • (a • x) := by
      rw [← algebraMap_smul (KK O) a x, smul_smul, inv_mul_cancel₀ ha1, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

end lat

/- English proof (translation)
Introduce `O _ _ _ W _ _ _ _ _ M hfg hMQ L`. Use `haveI := latticeInter_isLattice M hfg hMQ L`. Use `haveI : Module.Finite O (latticeInter M L) := Module.Finite.iff_fg.2 (Submodule.IsLattice.fg (A := KK O))`. Set `bO` to `Module.finBasis O (latticeInter M L)`. Use `⟨_, bO.extendOfIsLattice (KK O), fun i => ?_, fun x hx i => ?_⟩` and prove the remaining obligations.

Rewrite using `[Module.Basis.extendOfIsLattice_apply]`. Conclude with `(bO i).2`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : Fin _ → O, x = ∑ j, (algebraMap O (KK O) (c j)) • (bO.extendOfIsLattice (KK O)) j := by`. Use `⟨fun j => bO.repr ⟨x, hx⟩ j, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg (fun z : latticeInter M L => (z : L)) (bO.sum_repr ⟨x, hx⟩)`.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h2`. Use `h2.symm.trans (Finset.sum_congr rfl fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[Module.Basis.extendOfIsLattice_apply, algebraMap_smul]`. Use `⟨c i, ?_⟩` and prove the remaining obligations. Rewrite using `[hc, map_sum]`.

Simplify using `only [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
theorem lattice_adapted_basis_exists : LatticeAdaptedBasisExists := by
  intro O _ _ _ W _ _ _ _ _ M hfg hMQ L
  haveI := latticeInter_isLattice M hfg hMQ L
  haveI : Module.Finite O (latticeInter M L) := Module.Finite.iff_fg.2 (Submodule.IsLattice.fg (A := KK O))
  let bO := Module.finBasis O (latticeInter M L)
  refine ⟨_, bO.extendOfIsLattice (KK O), fun i => ?_, fun x hx i => ?_⟩
  · rw [Module.Basis.extendOfIsLattice_apply]
    exact (bO i).2
  · obtain ⟨c, hc⟩ : ∃ c : Fin _ → O, x = ∑ j, (algebraMap O (KK O) (c j)) • (bO.extendOfIsLattice (KK O)) j := by
      refine ⟨fun j => bO.repr ⟨x, hx⟩ j, ?_⟩
      have h2 := congrArg (fun z : latticeInter M L => (z : L)) (bO.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h2
      refine h2.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [Module.Basis.extendOfIsLattice_apply, algebraMap_smul]
    refine ⟨c i, ?_⟩
    rw [hc, map_sum]
    simp only [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Formalism.MainNotions.G.GLWeightTheory

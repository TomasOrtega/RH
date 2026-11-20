import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Finset

namespace GlobalTheory.CompanionTheory.DSHighestOfKType

open Formalism.REAL (GlRel KHighest IsWeight)
open PI.UpqRep (CDom root)

variable {n : ℕ}

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem height_root (a b : Fin n) : ∑ i : Fin n, ((i : ℕ) : ℝ) * root a b i = ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ) := by
  simp [root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

/- English proof (translation)
Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem not_cdom_add_root (ε : Fin n → Bool) (μ : Fin n → ℝ) {a b : Fin n} (hab : a < b) :
    ¬ CDom ε (μ + root a b) μ := by
  rintro ⟨c, hc, h⟩
  have h1 : ∑ i : Fin n, ((i : ℕ) : ℝ) * (μ - (μ + root a b)) i = ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) := by
    have : ∀ i : Fin n, ((i : ℕ) : ℝ) * (μ - (μ + root a b)) i = -(((i : ℕ) : ℝ) * root a b i) := by
      intro i; simp
    simp only [this, Finset.sum_neg_distrib, height_root]; ring
  have h2 : ∑ i : Fin n, ((i : ℕ) : ℝ) * (∑ x, ∑ y, (c x y : ℝ) • root x y) i
      = ∑ x, ∑ y, (c x y : ℝ) * (((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)) := by
    simp only [← height_root, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have h3 : ∑ x, ∑ y, (c x y : ℝ) * (((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)) ≤ 0 := by
    refine Finset.sum_nonpos fun x _ => Finset.sum_nonpos fun y _ => ?_
    by_cases h0 : c x y = 0
    · simp [h0]
    · have hxy : ((x : ℕ) : ℝ) < ((y : ℕ) : ℝ) := by exact_mod_cast (hc x y h0).1
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
  have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  rw [h, h2] at h1
  linarith

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Apply the first step, then apply the next step to every resulting obligation. Substitute using the available equality. Substitute using the available equality. Simplify using the standard rewrite rules. Substitute using the available equality.

Simplify using the standard rewrite rules. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem isWeight_apply {V : Type} [AddCommGroup V] [Module ℂ V] {E : Fin n → Fin n → Module.End ℂ V}
    (hE : GlRel E) {μ : Fin n → ℝ} {v : V} (hv : IsWeight E μ v) (a b : Fin n) :
    IsWeight E (μ + root a b) (E a b v) := by
  intro c
  have h := LinearMap.congr_fun (hE c c a b) v
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hv c, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  by_cases h1 : c = a <;> by_cases h2 : b = c
  · subst h1; subst h2; simp [root]
  · subst h1; simp [root, h2, Ne.symm h2, add_smul, add_comm]
  · subst h2; simp [root, h1, add_smul, add_comm]
  · simp [root, h1, h2, Ne.symm h2]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem hwOfType : CompanionTheory.D.DSIC.StabLink → CompanionTheory.D.DSIC.WtLink → CompanionTheory.D.DSIC.HWofType := by
  intro hS hW n ε H _ _ σ S E hσ hm μ T hT hTS
  obtain ⟨hfin, hst, -, ⟨v, hvT, hv0, hvw⟩, hdom⟩ := hT
  have hmap : (T.comap S.subtype).map S.subtype = T := by
    rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr hTS
  have hfinU : FiniteDimensional ℂ (T.comap S.subtype) :=
    (Submodule.comapSubtypeEquivOfLe hTS).symm.finiteDimensional
  have hU := (hS n ε H σ S E hσ hm _ hfinU).2 (by rw [hmap]; exact hst)
  have hw : IsWeight E μ (⟨v, hTS hvT⟩ : S) := (hW n ε H σ S E hσ hm μ _).2 hvw
  refine ⟨⟨v, hTS hvT⟩, fun h => hv0 (congrArg Subtype.val h), hvT, hw, fun a b hab hε => ?_⟩
  by_contra hne
  have hmem := hU a b hε ⟨v, hTS hvT⟩ hvT
  have hw' := (hW n ε H σ S E hσ hm _ _).1 (isWeight_apply hm.gl hw a b)
  exact not_cdom_add_root ε μ hab (hdom _ _ hmem (fun h => hne (Subtype.ext h)) hw')

end GlobalTheory.CompanionTheory.DSHighestOfKType

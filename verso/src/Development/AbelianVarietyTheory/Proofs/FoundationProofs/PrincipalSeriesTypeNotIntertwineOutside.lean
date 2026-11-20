import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTrivialOnUnitsModConductorUnitCharacterValuePr
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterRankOnePerturbationStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRankOneCornerPrincipalSeriesCongruenceStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

/- English proof (translation)
Introduce `k _ _ _ _ n ψ hord y hy hny`. Establish `hbad : ∃ a b : Fin n, a < b ∧ ¬ Triv (ψ a / ψ b) (y.val a b)`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hny ⟨hy, fun i j hij => h i j hij⟩`.

Set `S : Finset (Fin n)` to `Finset.univ.filter (fun a => ∃ b, a < b ∧ ¬ Triv (ψ a / ψ b) (y.val a b))`. Establish `hS : S.Nonempty`. Take `⟨a, b, hab, h⟩` from `hbad`. Conclude with `⟨a, by simp [S]; exact ⟨b, hab, h⟩⟩`. Use `set a := S.min' hS with ha_def`.

Establish `haS : a ∈ S` using `S.min'_mem hS`. Establish `hamin : ∀ i ∈ S, a ≤ i` using `fun i hi => S.min'_le i hi`. Set `T : Finset (Fin n)` to `Finset.univ.filter (fun b => a < b ∧ ¬ Triv (ψ a / ψ b) (y.val a b))`. Establish `hT : T.Nonempty`. Use `haS` as an intermediate fact.

Simplify using `only [S, Finset.mem_filter, Finset.mem_univ, true_and] at this`. Take `⟨b, hb⟩` from `this`. Conclude with `⟨b, by simp [T]; exact hb⟩`. Use `set b := T.max' hT with hb_def`. Establish `hbT : b ∈ T` using `T.max'_mem hT`.

Simplify using `only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hbT`. Take `⟨hab, hbad_ab⟩` from `hbT`. Establish `hbmax : ∀ j, b < j → Triv (ψ a / ψ j) (y.val a j)`. Introduce `j hj`. Assume the negation of the conclusion as `hc`.

Establish `: j ∈ T` using `by simp [T]; exact ⟨lt_trans hab hj, hc⟩`. Conclude with `absurd (T.le_max' j this) (not_le.mpr hj)`. Take `⟨j, hj, u, s, hu, hs, hsu, hne, hθj, hKO, hval⟩` from `GlobalTheory.T.exists_rankOne_corner_principalSeriesCongruence k n ψ hord y hy a b hab hbad_ab hbmax`. Establish `hprops` using `GlobalTheory.PsType.triv_ev_props k`. Use `⟨j, hj, ⟨hKO, ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `i i' hii'`. Rewrite using `[hval]`. Distinguish the cases in `hi' : i' = a`. Substitute `hi'` using the available equality. Simplify using `only [Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.single_eq_same, mul_one, if_neg (ne_of_lt hii'), zero_add]`.

Establish `hiS : i ∉ S` using `fun h => absurd (hamin i h) (not_le.mpr hii')`. Establish `hib : Triv (ψ i / ψ b) (y.val i b)`. Assume the negation of the conclusion as `hc`. Conclude with `hiS (by simp [S]; exact ⟨b, lt_trans hii' hab, hc⟩)`. Establish `h2 : Triv (ψ i / ψ a) (y.val i b)` using `hord i i a b le_rfl hii'.le hab.le _ hib`.

Use `hprops.1 _ _ _ ?_ h2` and prove the remaining obligations. Rewrite using `[map_mul]`. Use `first`. Consider the case `exact mul_le_of_le_one_left' hs`. Consider the case `exact (mul_le_mul' hs le_rfl).trans_eq (one_mul _)`.

Consider the case `exact mul_le_of_le_one_left (zero_le _) hs`. Simplify using `only [Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.single_eq_of_ne hi', mul_zero, if_neg (ne_of_lt hii'), add_zero]`. Conclude with `hprops.2.2.1 _`. Establish `hθ : theta ψ (y * j * y⁻¹) = (ψ a u : ℂ)`. Use `GlobalTheory.T.principalSeriesTypeCharacter_rankOne_perturbation k n ψ (y * j * y⁻¹) (fun i => s * y.val i b) (Pi.single a 1) a u hu hval ?_` and prove the remaining obligations.

Introduce `i`. Distinguish the cases in `hi : i = a`. Substitute `hi` using the available equality. Simplify using `[hsu]`. Simplify using `[Pi.single_eq_of_ne hi, hi]`.

Rewrite using `[hθj, hθ]`. Introduce `h`. Conclude with `hne (Units.ext h).symm`.
-/
theorem not_intertwine : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ y ∈ KO k (Fin n), y ∉ grp ψ → ∃ j ∈ grp ψ, y * j * y⁻¹ ∈ grp ψ ∧ theta ψ j ≠ theta ψ (y * j * y⁻¹) := by
  intro k _ _ _ _ n ψ hord y hy hny
  classical

  have hbad : ∃ a b : Fin n, a < b ∧ ¬ Triv (ψ a / ψ b) (y.val a b) := by
    by_contra h
    push_neg at h
    exact hny ⟨hy, fun i j hij => h i j hij⟩
  let S : Finset (Fin n) := Finset.univ.filter (fun a => ∃ b, a < b ∧ ¬ Triv (ψ a / ψ b) (y.val a b))
  have hS : S.Nonempty := by
    obtain ⟨a, b, hab, h⟩ := hbad
    exact ⟨a, by simp [S]; exact ⟨b, hab, h⟩⟩
  set a := S.min' hS with ha_def
  have haS : a ∈ S := S.min'_mem hS
  have hamin : ∀ i ∈ S, a ≤ i := fun i hi => S.min'_le i hi
  let T : Finset (Fin n) := Finset.univ.filter (fun b => a < b ∧ ¬ Triv (ψ a / ψ b) (y.val a b))
  have hT : T.Nonempty := by
    have := haS
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at this
    obtain ⟨b, hb⟩ := this
    exact ⟨b, by simp [T]; exact hb⟩
  set b := T.max' hT with hb_def
  have hbT : b ∈ T := T.max'_mem hT
  simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hbT
  obtain ⟨hab, hbad_ab⟩ := hbT
  have hbmax : ∀ j, b < j → Triv (ψ a / ψ j) (y.val a j) := by
    intro j hj
    by_contra hc
    have : j ∈ T := by simp [T]; exact ⟨lt_trans hab hj, hc⟩
    exact absurd (T.le_max' j this) (not_le.mpr hj)
  obtain ⟨j, hj, u, s, hu, hs, hsu, hne, hθj, hKO, hval⟩ :=
    GlobalTheory.T.exists_rankOne_corner_principalSeriesCongruence k n ψ hord y hy a b hab hbad_ab hbmax
  have hprops := GlobalTheory.PsType.triv_ev_props k
  refine ⟨j, hj, ⟨hKO, ?_⟩, ?_⟩
  · intro i i' hii'
    rw [hval]
    by_cases hi' : i' = a
    · subst hi'
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.single_eq_same, mul_one,
        if_neg (ne_of_lt hii'), zero_add]

      have hiS : i ∉ S := fun h => absurd (hamin i h) (not_le.mpr hii')
      have hib : Triv (ψ i / ψ b) (y.val i b) := by
        by_contra hc
        exact hiS (by simp [S]; exact ⟨b, lt_trans hii' hab, hc⟩)
      have h2 : Triv (ψ i / ψ a) (y.val i b) := hord i i a b le_rfl hii'.le hab.le _ hib
      refine hprops.1 _ _ _ ?_ h2
      rw [map_mul]
      first
        | exact mul_le_of_le_one_left' hs
        | exact (mul_le_mul' hs le_rfl).trans_eq (one_mul _)
        | exact mul_le_of_le_one_left (zero_le _) hs
    · simp only [Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.single_eq_of_ne hi', mul_zero,
        if_neg (ne_of_lt hii'), add_zero]
      exact hprops.2.2.1 _
  · have hθ : theta ψ (y * j * y⁻¹) = (ψ a u : ℂ) := by
      refine GlobalTheory.T.principalSeriesTypeCharacter_rankOne_perturbation k n ψ (y * j * y⁻¹) (fun i => s * y.val i b) (Pi.single a 1) a u hu hval ?_
      intro i
      by_cases hi : i = a
      · subst hi; simp [hsu]
      · simp [Pi.single_eq_of_ne hi, hi]
    rw [hθj, hθ]
    intro h
    exact hne (Units.ext h).symm

end GlobalTheory.PsType

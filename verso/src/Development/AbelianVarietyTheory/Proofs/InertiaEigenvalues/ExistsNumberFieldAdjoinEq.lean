import Mathlib
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCoh
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory.PadicNumberFieldGen

open Polynomial IntermediateField

/- English proof (translation)
Establish `hint : ∀ z : PadicAlgCl l, IsIntegral ℚ_[l] z` using `fun z => (Algebra.IsAlgebraic.isAlgebraic z).isIntegral`. Establish `fmon : (minpoly ℚ_[l] α).Monic` using `minpoly.monic (hint α)`. Establish `fa0 : (minpoly ℚ_[l] α).aeval α = 0` using `minpoly.aeval _ _`. Establish `hfin : ({x' | IsConjRoot ℚ_[l] α x' ∧ α ≠ x'} : Set (PadicAlgCl l)).Finite`. Use `((minpoly ℚ_[l] α).rootSet_finite (PadicAlgCl l)).subset fun x' hx' => ?_` and prove the remaining obligations.

Conclude with `(isConjRoot_iff_mem_minpoly_rootSet (hint α)).1 hx'.1`. Establish `hop : IsOpen (⋂ x' ∈ ({x' | IsConjRoot ℚ_[l] α x' ∧ α ≠ x'} : Set (PadicAlgCl l)), {y : PadicAlgCl l | ‖α - y‖ < ‖α - x'‖})` using `hfin.isOpen_biInter fun x' _ => isOpen_lt (by fun_prop) continuous_const`. Establish `hmem : α ∈ (⋂ x' ∈ ({x' | IsConjRoot ℚ_[l] α x' ∧ α ≠ x'} : Set (PadicAlgCl l)), {y : PadicAlgCl l | ‖α - y‖ < ‖α - x'‖})`. Simplify using `only [Set.mem_iInter, Set.mem_setOf_eq, sub_self, norm_zero, norm_pos_iff, sub_ne_zero]`. Conclude with `fun x' h => h.2`.

Take `⟨δ, δpos, hball⟩` from `Metric.isOpen_iff.1 hop α hmem`. Establish `hn : (minpoly ℚ_[l] α).natDegree ≠ 0` using `(minpoly.natDegree_pos (hint α)).ne'`. Establish `hε : (δ / (max ‖α‖ 1)) ^ (minpoly ℚ_[l] α).natDegree / ((minpoly ℚ_[l] α).natDegree + 1) > 0` using `by positivity`. Take `⟨g, gmon, gdeg, gcoeff⟩` from `exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt (Padic.denseRange_ratCast l) fmon hε`. Take `⟨β, hb, hab⟩` from `exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt (L := PadicAlgCl l) hε fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff (IsAlgClosed.splits _)`.

Establish `hab : ‖α - β‖ < δ`. Rewrite `hab` using `[← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul, ← Real.rpow_mul (div_pos δpos (by positivity)).le, mul_inv_cancel₀]`. Simplify `hab` using `[mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖α‖ 1) > 0).ne']`. Simplify using `[hn]`. Check the signs of the components of the expression.

Establish `hβU` using `hball (show β ∈ Metric.ball α δ by rw [Metric.mem_ball, dist_comm, dist_eq_norm]; exact hab)`. Establish `hgβ : aeval β g = 0`. Rewrite `hb` using `[Polynomial.mem_aroots]`. Simplify `hb.2` using `[Polynomial.aeval_map_algebraMap]`. Use `⟨β, g, gmon, gdeg.symm, hgβ, ?_⟩` and prove the remaining obligations.

Use `IsKrasner.krasner (minpoly.irreducible (hint α)).separable (IsAlgClosed.splits _) (hint β) fun x' h1 h2 => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_iInter, Set.mem_setOf_eq] at hβU`. Conclude with `hβU x' ⟨h1, h2⟩`.
-/
theorem exists_rat_root_mem_adjoin (l : ℕ) [Fact l.Prime] (α : PadicAlgCl l) :
    ∃ β : PadicAlgCl l, ∃ g : ℚ[X], g.Monic ∧ g.natDegree = (minpoly ℚ_[l] α).natDegree ∧
      aeval β g = 0 ∧ α ∈ ℚ_[l]⟮β⟯ := by
  have hint : ∀ z : PadicAlgCl l, IsIntegral ℚ_[l] z := fun z =>
    (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  have fmon : (minpoly ℚ_[l] α).Monic := minpoly.monic (hint α)
  have fa0 : (minpoly ℚ_[l] α).aeval α = 0 := minpoly.aeval _ _
  have hfin : ({x' | IsConjRoot ℚ_[l] α x' ∧ α ≠ x'} : Set (PadicAlgCl l)).Finite := by
    refine ((minpoly ℚ_[l] α).rootSet_finite (PadicAlgCl l)).subset fun x' hx' => ?_
    exact (isConjRoot_iff_mem_minpoly_rootSet (hint α)).1 hx'.1
  have hop : IsOpen (⋂ x' ∈ ({x' | IsConjRoot ℚ_[l] α x' ∧ α ≠ x'} : Set (PadicAlgCl l)),
      {y : PadicAlgCl l | ‖α - y‖ < ‖α - x'‖}) :=
    hfin.isOpen_biInter fun x' _ => isOpen_lt (by fun_prop) continuous_const
  have hmem : α ∈ (⋂ x' ∈ ({x' | IsConjRoot ℚ_[l] α x' ∧ α ≠ x'} : Set (PadicAlgCl l)),
      {y : PadicAlgCl l | ‖α - y‖ < ‖α - x'‖}) := by
    simp only [Set.mem_iInter, Set.mem_setOf_eq, sub_self, norm_zero, norm_pos_iff, sub_ne_zero]
    exact fun x' h => h.2
  obtain ⟨δ, δpos, hball⟩ := Metric.isOpen_iff.1 hop α hmem
  have hn : (minpoly ℚ_[l] α).natDegree ≠ 0 := (minpoly.natDegree_pos (hint α)).ne'
  have hε : (δ / (max ‖α‖ 1)) ^ (minpoly ℚ_[l] α).natDegree /
      ((minpoly ℚ_[l] α).natDegree + 1) > 0 := by positivity
  obtain ⟨g, gmon, gdeg, gcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt
      (Padic.denseRange_ratCast l) fmon hε
  obtain ⟨β, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt (L := PadicAlgCl l)
      hε fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff (IsAlgClosed.splits _)
  have hab : ‖α - β‖ < δ := by
    rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
        ← Real.rpow_mul (div_pos δpos (by positivity)).le, mul_inv_cancel₀] at hab
    · simpa [mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖α‖ 1) > 0).ne'] using hab
    · simp [hn]
    · positivity
  have hβU := hball (show β ∈ Metric.ball α δ by rw [Metric.mem_ball, dist_comm, dist_eq_norm]; exact hab)
  have hgβ : aeval β g = 0 := by
    rw [Polynomial.mem_aroots] at hb
    simpa [Polynomial.aeval_map_algebraMap] using hb.2
  refine ⟨β, g, gmon, gdeg.symm, hgβ, ?_⟩
  refine IsKrasner.krasner (minpoly.irreducible (hint α)).separable (IsAlgClosed.splits _)
    (hint β) fun x' h1 h2 => ?_
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hβU
  exact hβU x' ⟨h1, h2⟩

end GlobalTheory.PadicNumberFieldGen

namespace GlobalTheory.PadicNumberFieldGen

open Polynomial IntermediateField

/- English proof (translation)
Introduce `l _ K hK`. Take `⟨α, hα⟩` from `Field.exists_primitive_element ℚ_[l] K`. Establish `hKα : K = ℚ_[l]⟮(α : PadicAlgCl l)⟯`. Rewrite using `[← IntermediateField.lift_adjoin_simple, hα, IntermediateField.lift_top]`. Take `⟨β, g, gmon, gdeg, hgβ, hαβ⟩` from `exists_rat_root_mem_adjoin l (α : PadicAlgCl l)`.

Establish `hβQ : IsIntegral ℚ β` using `⟨g, gmon, hgβ⟩`. Use `haveI : FiniteDimensional ℚ ℚ⟮β⟯ := IntermediateField.adjoin.finiteDimensional hβQ`. Use `haveI : NumberField ℚ⟮β⟯ := ⟨⟩`. Use `⟨ℚ⟮β⟯, inferInstance, inferInstance, (ℚ⟮β⟯).val.toRingHom, ?_⟩` and prove the remaining obligations. Establish `hrange : Set.range (ℚ⟮β⟯).val.toRingHom = (ℚ⟮β⟯ : Set (PadicAlgCl l))`.

Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[hrange]`. Establish `hint : ∀ z : PadicAlgCl l, IsIntegral ℚ_[l] z` using `fun z => (Algebra.IsAlgebraic.isAlgebraic z).isIntegral`. Establish `h1 : IntermediateField.adjoin ℚ_[l] (ℚ⟮β⟯ : Set (PadicAlgCl l)) = ℚ_[l]⟮β⟯`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce `x hx`. Establish `hle : ℚ⟮β⟯ ≤ (ℚ_[l]⟮β⟯).restrictScalars ℚ`. Rewrite using `[IntermediateField.adjoin_simple_le_iff]`.

Conclude with `IntermediateField.mem_adjoin_simple_self ℚ_[l] β`. Conclude with `hle hx`. Apply `IntermediateField.adjoin.mono` to reduce the goal to its premises. Rewrite using `[Set.singleton_subset_iff]`. Conclude with `IntermediateField.mem_adjoin_simple_self ℚ β`.

Rewrite using `[h1, hKα]`. Use `symm`. Use `haveI : FiniteDimensional ℚ_[l] ℚ_[l]⟮β⟯ := IntermediateField.adjoin.finiteDimensional (hint β)`. Use `IntermediateField.eq_of_le_of_finrank_le (IntermediateField.adjoin_simple_le_iff.2 hαβ) ?_` and prove the remaining obligations. Rewrite using `[IntermediateField.adjoin.finrank (hint β), IntermediateField.adjoin.finrank (hint _), ← gdeg]`.

Establish `hg0 : g.map (algebraMap ℚ ℚ_[l]) ≠ 0` using `(gmon.map _).ne_zero`. Establish `hdvd : minpoly ℚ_[l] β ∣ g.map (algebraMap ℚ ℚ_[l])` using `minpoly.dvd _ _ (by rw [Polynomial.aeval_map_algebraMap]; exact hgβ)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_numberField_adjoin_eq : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] K → ∃ (F : Type) (_ : Field F) (_ : NumberField F) (c : F →+* PadicAlgCl l), IntermediateField.adjoin ℚ_[l] (Set.range c) = K := by
  intro l _ K hK
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ_[l] K
  have hKα : K = ℚ_[l]⟮(α : PadicAlgCl l)⟯ := by
    rw [← IntermediateField.lift_adjoin_simple, hα, IntermediateField.lift_top]
  obtain ⟨β, g, gmon, gdeg, hgβ, hαβ⟩ := exists_rat_root_mem_adjoin l (α : PadicAlgCl l)
  have hβQ : IsIntegral ℚ β := ⟨g, gmon, hgβ⟩
  haveI : FiniteDimensional ℚ ℚ⟮β⟯ := IntermediateField.adjoin.finiteDimensional hβQ
  haveI : NumberField ℚ⟮β⟯ := ⟨⟩
  refine ⟨ℚ⟮β⟯, inferInstance, inferInstance, (ℚ⟮β⟯).val.toRingHom, ?_⟩
  have hrange : Set.range (ℚ⟮β⟯).val.toRingHom = (ℚ⟮β⟯ : Set (PadicAlgCl l)) := by
    ext x; simp
  rw [hrange]
  have hint : ∀ z : PadicAlgCl l, IsIntegral ℚ_[l] z := fun z =>
    (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  have h1 : IntermediateField.adjoin ℚ_[l] (ℚ⟮β⟯ : Set (PadicAlgCl l)) = ℚ_[l]⟮β⟯ := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      have hle : ℚ⟮β⟯ ≤ (ℚ_[l]⟮β⟯).restrictScalars ℚ := by
        rw [IntermediateField.adjoin_simple_le_iff]
        exact IntermediateField.mem_adjoin_simple_self ℚ_[l] β
      exact hle hx
    · apply IntermediateField.adjoin.mono
      rw [Set.singleton_subset_iff]
      exact IntermediateField.mem_adjoin_simple_self ℚ β
  rw [h1, hKα]
  symm
  haveI : FiniteDimensional ℚ_[l] ℚ_[l]⟮β⟯ := IntermediateField.adjoin.finiteDimensional (hint β)
  refine IntermediateField.eq_of_le_of_finrank_le
    (IntermediateField.adjoin_simple_le_iff.2 hαβ) ?_
  rw [IntermediateField.adjoin.finrank (hint β), IntermediateField.adjoin.finrank (hint _), ← gdeg]
  have hg0 : g.map (algebraMap ℚ ℚ_[l]) ≠ 0 := (gmon.map _).ne_zero
  have hdvd : minpoly ℚ_[l] β ∣ g.map (algebraMap ℚ ℚ_[l]) :=
    minpoly.dvd _ _ (by rw [Polynomial.aeval_map_algebraMap]; exact hgβ)
  calc (minpoly ℚ_[l] β).natDegree ≤ (g.map (algebraMap ℚ ℚ_[l])).natDegree :=
        Polynomial.natDegree_le_of_dvd hdvd hg0
    _ = g.natDegree := g.natDegree_map _

end GlobalTheory.PadicNumberFieldGen

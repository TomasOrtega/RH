import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL.PrimOrth

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem neg_mem_nilRad {A : Submodule F V} {h : Module.End F V} (hh : h ∈ nilRad A) : -h ∈ nilRad A :=
  ⟨fun x => by simpa using hh.1 x, fun x hx => by simpa using hh.2 x hx⟩

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem add_preserves {A : Submodule F V} {g h : Module.End F V} (hh : h ∈ nilRad A)
    (hg : ∀ x ∈ A, g x ∈ A) : ∀ x ∈ A, (g + h) x ∈ A :=
  fun x hx => A.add_mem (hg x hx) (hh.1 x)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem add_preserves_iff {A : Submodule F V} {g h : Module.End F V} (hh : h ∈ nilRad A) :
    (∀ x ∈ A, (g + h) x ∈ A) ↔ ∀ x ∈ A, g x ∈ A := by
  refine ⟨fun H => ?_, add_preserves hh⟩
  have := add_preserves (neg_mem_nilRad hh) H
  simpa using this

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem isUnit_add [FiniteDimensional F V] {A : Submodule F V} {g h : Module.End F V} (hh : h ∈ nilRad A)
    (hg : ∀ x ∈ A, g x ∈ A) (hu : IsUnit g) : IsUnit (g + h) := by
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot] at hu
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hinj : Function.Injective (g.restrict hg) := by
    intro a b hab
    exact Subtype.ext (hu (congrArg Subtype.val hab))
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  have hx' : g x + h x = 0 := hx
  have hgx : g x ∈ A := by
    rw [eq_neg_of_add_eq_zero_left hx']
    exact A.neg_mem (hh.1 x)
  obtain ⟨w, hw⟩ := hsurj ⟨g x, hgx⟩
  have hwx : (w : V) = x := hu (congrArg Subtype.val hw)
  have hxA : x ∈ A := hwx ▸ w.2
  rw [hh.2 x hxA, add_zero] at hx'
  exact hu (by rw [hx', map_zero])

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem isUnit_add_iff [FiniteDimensional F V] {A : Submodule F V} {g h : Module.End F V} (hh : h ∈ nilRad A)
    (hg : ∀ x ∈ A, g x ∈ A) : IsUnit (g + h) ↔ IsUnit g := by
  refine ⟨fun H => ?_, isUnit_add hh hg⟩
  have := isUnit_add (neg_mem_nilRad hh) (add_preserves hh hg) H
  simpa using this

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem sum_mul_eq_zero [Fintype (Module.End F V)] {φ : Module.End F V → ℂ} (hφ : IsPrimitive φ)
    {A : Submodule F V} (h0 : A ≠ ⊥) (h1 : A ≠ ⊤) (f : Module.End F V → ℂ)
    (hf : ∀ g, ∀ h ∈ nilRad A, f (g + h) = f g) (hf0 : ∀ g, ¬ (∀ x ∈ A, g x ∈ A) → f g = 0) :
    ∑ g, φ g * f g = 0 := by
  classical
  have hfin : (nilRad A).Finite := Set.toFinite _
  have hne : (hfin.toFinset.card : ℂ) ≠ 0 := by
    have : hfin.toFinset.Nonempty := ⟨0, by
      rw [Set.Finite.mem_toFinset]
      exact ⟨fun x => by simp, fun x _ => by simp⟩⟩
    exact_mod_cast this.card_pos.ne'
  have key : ∑ h ∈ hfin.toFinset, ∑ g, φ g * f g = 0 := by
    have : ∀ h ∈ hfin.toFinset, ∑ g, φ g * f g = ∑ g, φ (g + h) * f g := by
      intro h hh
      rw [Set.Finite.mem_toFinset] at hh
      rw [← Equiv.sum_comp (Equiv.addRight h)]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [Equiv.coe_addRight, hf g h hh]
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [← Finset.sum_mul]
    by_cases hg : ∀ x ∈ A, g x ∈ A
    · have := hφ A h0 h1 g hg
      rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at this
      rw [this, zero_mul]
    · rw [hf0 g hg, mul_zero]
  rw [Finset.sum_const, nsmul_eq_mul] at key
  exact (mul_eq_zero.mp key).resolve_left hne

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem psi_bot {s : F[X] → ℂ} (hs : IsAdditive s) (U : Type) [AddCommGroup U] [Module F U]
    [FiniteDimensional F U] [Subsingleton U] (g : Module.End F U) : psi s U g = 0 := by
  have h1 : s 1 = 0 := by
    have := hs 1 1 monic_one monic_one
    simpa using this
  have hc : LinearMap.charpoly g = 1 := by
    have hm := LinearMap.charpoly_monic g
    rw [← hm.natDegree_eq_zero, LinearMap.charpoly_natDegree]
    exact Module.finrank_zero_of_subsingleton
  haveI : IsEmpty {W : Submodule F U // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W} :=
    ⟨fun W => W.2.1 (Subsingleton.elim _ _)⟩
  rw [psi_eq, hc, h1, finsum_of_isEmpty, sub_zero]

open Classical in

/- English proof (translation)
Equip the data with the indicated structure. Equip the data with the indicated structure. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Substitute using the available equality. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem ipGL_psi_eq (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (s : F[X] → ℂ) (hs : IsAdditive s) (φ : Module.End F V → ℂ)
    (hφ : IsPrimitive φ) : ipGL φ (psi s V) = ipGL φ (fun g => s (LinearMap.charpoly g)) := by
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F V) := Finite.of_injective _ (DFunLike.coe_injective (F := V →ₗ[F] V))
  haveI : Finite (Submodule F V) := Finite.of_injective _ (SetLike.coe_injective (A := Submodule F V))
  letI := Fintype.ofFinite (Module.End F V)
  letI := Fintype.ofFinite (Submodule F V)
  let R : Submodule F V → Module.End F V → ℂ := fun W g =>
    if h : W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W then psi s W (g.restrict h.2) else 0
  have hR : ∀ g, psi s V g = s (LinearMap.charpoly g) - ∑ W, R W g := by
    intro g
    rw [psi_eq, finsum_eq_sum_of_fintype]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun W : Submodule F V => W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W)]
    rw [Finset.sum_eq_zero (s := Finset.univ.filter fun W : Submodule F V => ¬ (W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W)), add_zero,
      Finset.sum_subtype (p := fun W : Submodule F V => W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W) _ (by simp)]
    · refine Finset.sum_congr rfl fun W _ => ?_
      simp only [R, dif_pos W.2]
    · intro W hW
      simp only [R, dif_neg (Finset.mem_filter.mp hW).2]
  have hW : ∀ W, ∑ g, φ g * (if IsUnit g then star (R W g) else 0) = 0 := by
    intro W
    by_cases h1 : W = ⊤
    · refine Finset.sum_eq_zero fun g _ => ?_
      have : R W g = 0 := dif_neg (fun h => h.1 h1)
      simp [this]
    by_cases h0 : W = ⊥
    · refine Finset.sum_eq_zero fun g _ => ?_
      have : R W g = 0 := by
        subst h0
        simp only [R]
        split_ifs
        · exact psi_bot hs _ _
        · rfl
      simp [this]
    refine sum_mul_eq_zero hφ h0 h1 _ ?_ ?_
    · intro g h hh
      by_cases hg : ∀ x ∈ W, g x ∈ W
      · have e : R W (g + h) = R W g := by
          simp only [R]
          rw [dif_pos ⟨h1, add_preserves hh hg⟩, dif_pos ⟨h1, hg⟩]
          congr 1
          ext x
          simp [LinearMap.restrict_apply, hh.2 x x.2]
        simp only [e, isUnit_add_iff hh hg]
      · have e1 : R W g = 0 := dif_neg (fun H => hg H.2)
        have e2 : R W (g + h) = 0 := dif_neg (fun H => hg ((add_preserves_iff hh).mp H.2))
        simp [e1, e2]
    · intro g hg
      have e1 : R W g = 0 := dif_neg (fun H => hg H.2)
      simp [e1]
  have hsum : ∀ ψ : Module.End F V → ℂ,
      ipGL φ ψ = ∑ g, φ g * (if IsUnit g then star (ψ g) else 0) := by
    intro ψ
    rw [ipGL, finsum_mem_def, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hg : IsUnit g
    · simp [Set.indicator, hg]
    · simp [Set.indicator, hg]
  rw [hsum, hsum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  have h2 : ∑ W, ∑ g, φ g * (if IsUnit g then star (R W g) else 0) = 0 :=
    Finset.sum_eq_zero fun W _ => hW W
  rw [Finset.sum_comm, ← neg_eq_zero, ← Finset.sum_neg_distrib] at h2
  rw [← h2]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases hg : IsUnit g
  · simp only [if_pos hg, hR g, star_sub, star_sum, ← Finset.mul_sum]
    ring
  · simp [hg]

end GlobalTheory.CuspGL.PrimOrth

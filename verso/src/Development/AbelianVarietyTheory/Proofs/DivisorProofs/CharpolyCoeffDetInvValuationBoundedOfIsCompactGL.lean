import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CptBound

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Take `⟨c, hc⟩` from `HeightOneSpectrum.valuedAdicCompletion_surjective E w (WithZero.exp m)`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Rewrite `hc` using `[map_zero]`. Conclude with `WithZero.exp_ne_zero hc.symm`.

Establish `: {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} = {y | Valued.v.restrict y ≤ Valued.v.restrict c}`. Use extensionality with `y`. Simplify using `only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]`. Rewrite using `[this]`. Conclude with `Valued.isOpen_closedBall _ (by simp [hc0])`.
-/
theorem isOpen_le_exp (w : Pl E) (m : ℤ) :
    IsOpen {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w (WithZero.exp m)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} =
      {y | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isOpen_closedBall _ (by simp [hc0])

/- English proof (translation)
Establish `hcov : S ⊆ ⋃ m : ℕ, {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp (m : ℤ)}`. Introduce `x _`. Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq]`. Break down `eq_or_ne (Valued.v x) 0 with h | h` into its components or cases. Conclude with `⟨0, by rw [h]; exact zero_le'⟩`.

Use `⟨(WithZero.log (Valued.v x)).toNat, ?_⟩ conv_lhs => rw [← WithZero.exp_log h]` and prove the remaining obligations. Rewrite using `[WithZero.exp_le_exp]`. Conclude with `Int.self_le_toNat _`. Establish `hdir : Directed (· ⊆ ·) (fun m : ℕ => {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp (m : ℤ)})` using `Monotone.directed_le fun a b hab y (hy : _ ≤ _) => (show _ ≤ _ from hy.trans (WithZero.exp_le_exp.2 (by exact_mod_cast hab)))`. Take `⟨m, hm⟩` from `hS.elim_directed_cover _ (fun m => isOpen_le_exp w _) hcov hdir`.

Conclude with `⟨_, fun x hx => hm hx⟩`.
-/
theorem exists_bound_of_isCompact (w : Pl E) {S : Set (w.adicCompletion E)} (hS : IsCompact S) :
    ∃ γ : WithZero (Multiplicative ℤ), ∀ x ∈ S, Valued.v x ≤ γ := by
  have hcov : S ⊆ ⋃ m : ℕ, {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp (m : ℤ)} := by
    intro x _
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    rcases eq_or_ne (Valued.v x) 0 with h | h
    · exact ⟨0, by rw [h]; exact zero_le'⟩
    · refine ⟨(WithZero.log (Valued.v x)).toNat, ?_⟩
      conv_lhs => rw [← WithZero.exp_log h]
      rw [WithZero.exp_le_exp]
      exact Int.self_le_toNat _
  have hdir : Directed (· ⊆ ·) (fun m : ℕ => {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp (m : ℤ)}) :=
    Monotone.directed_le fun a b hab y (hy : _ ≤ _) =>
      (show _ ≤ _ from hy.trans (WithZero.exp_le_exp.2 (by exact_mod_cast hab)))
  obtain ⟨m, hm⟩ := hS.elim_directed_cover _ (fun m => isOpen_le_exp w _) hcov hdir
  exact ⟨_, fun x hx => hm hx⟩

/- English proof (translation)
Rewrite using `[MvPolynomial.eval_map]`. Establish `h` using `Matrix.charpoly.univ_map_eval₂Hom (Fin n) (Int.castRingHom R) (fun ij : Fin n × Fin n => M ij.1 ij.2)`. Establish `hM : Matrix.of (Function.curry fun ij : Fin n × Fin n => M ij.1 ij.2) = M`. Use extensionality with `i j`. Both sides reduce to the same expression.

Rewrite `h` using `[hM]`. Rewrite using `[← h, Polynomial.coeff_map]`. Both sides reduce to the same expression.
-/
theorem charpoly_coeff_eq {R : Type} [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    M.charpoly.coeff k = MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
      (MvPolynomial.map (Int.castRingHom R) ((Matrix.charpoly.univ ℤ (Fin n)).coeff k)) := by
  rw [MvPolynomial.eval_map]
  have h := Matrix.charpoly.univ_map_eval₂Hom (Fin n) (Int.castRingHom R) (fun ij : Fin n × Fin n => M ij.1 ij.2)
  have hM : Matrix.of (Function.curry fun ij : Fin n × Fin n => M ij.1 ij.2) = M := by
    ext i j; rfl
  rw [hM] at h
  rw [← h, Polynomial.coeff_map]
  rfl

end GlobalTheory.CptBound

namespace GlobalTheory.BCT

open GlobalTheory.CptBound

/- English proof (translation)
Introduce `E _ _ _ n w C hC`. Establish `hent : Continuous fun y : GLw n w => fun ij : Fin n × Fin n => y.val ij.1 ij.2` using `continuous_pi fun ij => Units.continuous_val.matrix_elem ij.1 ij.2`. Establish `hco : ∀ k, Continuous fun y : GLw n w => y.val.charpoly.coeff k`. Introduce `k`. Establish `e : (fun y : GLw n w => y.val.charpoly.coeff k) = fun y : GLw n w => MvPolynomial.eval (fun ij : Fin n × Fin n => y.val ij.1 ij.2) (MvPolynomial.map (Int.castRingHom (w.adicCompletion E)) ((Matrix.charpoly.univ ℤ (Fin n)).coeff k))`.

Use function extensionality and compare the values at `fun y => charpoly_coeff_eq n y.val k`. Rewrite using `[e]`. Conclude with `(MvPolynomial.continuous_eval _).comp hent`. Establish `hdet : Continuous fun y : GLw n w => (y⁻¹ : GLw n w).val.det` using `Units.continuous_coe_inv.matrix_det`. Use `set S : Set (w.adicCompletion E) := (⋃ k ∈ Finset.range (n + 1), (fun y : GLw n w => y.val.charpoly.coeff k) '' C) ∪ ((fun y : GLw n w => (y⁻¹ : GLw n w).val.det) '' C) with hS`.

Establish `hSc : IsCompact S` using `((Finset.range (n + 1)).isCompact_biUnion fun k _ => hC.image (hco k)).union (hC.image hdet)`. Take `⟨γ, hγ⟩` from `exists_bound_of_isCompact w hSc`. Use `⟨γ, fun y hy => ⟨fun k => ?_, hγ _ (Or.inr ⟨y, hy, rfl⟩)⟩⟩` and prove the remaining obligations. Distinguish the cases in `hk : k < n + 1`. Conclude with `hγ _ (Or.inl (Set.mem_biUnion (Finset.mem_range.2 hk) ⟨y, hy, rfl⟩))`.

Rewrite using `[Polynomial.coeff_eq_zero_of_natDegree_lt (by`. Rewrite using `[Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`. Use the proof step `omega), map_zero]`. Conclude with `zero_le'`.
-/
theorem charpoly_det_bounded_of_isCompact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (C : Set (GLw n w)), IsCompact C → ∃ γ : WithZero (Multiplicative ℤ), ∀ y ∈ C,
      (∀ k, Valued.v (y.val.charpoly.coeff k) ≤ γ) ∧ Valued.v (y⁻¹ : GLw n w).val.det ≤ γ := by
  intro E _ _ _ n w C hC
  have hent : Continuous fun y : GLw n w => fun ij : Fin n × Fin n => y.val ij.1 ij.2 :=
    continuous_pi fun ij => Units.continuous_val.matrix_elem ij.1 ij.2
  have hco : ∀ k, Continuous fun y : GLw n w => y.val.charpoly.coeff k := by
    intro k
    have e : (fun y : GLw n w => y.val.charpoly.coeff k) = fun y : GLw n w =>
        MvPolynomial.eval (fun ij : Fin n × Fin n => y.val ij.1 ij.2)
          (MvPolynomial.map (Int.castRingHom (w.adicCompletion E)) ((Matrix.charpoly.univ ℤ (Fin n)).coeff k)) :=
      funext fun y => charpoly_coeff_eq n y.val k
    rw [e]
    exact (MvPolynomial.continuous_eval _).comp hent
  have hdet : Continuous fun y : GLw n w => (y⁻¹ : GLw n w).val.det :=
    Units.continuous_coe_inv.matrix_det
  set S : Set (w.adicCompletion E) :=
    (⋃ k ∈ Finset.range (n + 1), (fun y : GLw n w => y.val.charpoly.coeff k) '' C) ∪
      ((fun y : GLw n w => (y⁻¹ : GLw n w).val.det) '' C) with hS
  have hSc : IsCompact S :=
    ((Finset.range (n + 1)).isCompact_biUnion fun k _ => hC.image (hco k)).union (hC.image hdet)
  obtain ⟨γ, hγ⟩ := exists_bound_of_isCompact w hSc
  refine ⟨γ, fun y hy => ⟨fun k => ?_, hγ _ (Or.inr ⟨y, hy, rfl⟩)⟩⟩
  by_cases hk : k < n + 1
  · exact hγ _ (Or.inl (Set.mem_biUnion (Finset.mem_range.2 hk) ⟨y, hy, rfl⟩))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; omega), map_zero]
    exact zero_le'

end GlobalTheory.BCT

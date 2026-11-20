import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.Arith
import Mathlib

namespace PositivityTheory.KB.SpectralGap

/- English proof (translation)
Establish `hmem : g ∈ Kg L N π r ↔ ∃ γ, dg L N π r * (mt L N) g = (mo L N) γ * dg L N π r` using `Iff.rfl`. Rewrite using `[hmem]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨γ, hγ⟩ i j`. Use `⟨(γ : Matrix (Fin N) (Fin N) _) i j, ?_⟩` and prove the remaining obligations.

Establish `h` using `congrFun (congrFun hγ i) j`. Simplify `h` using `[dg, mt, mo, Matrix.diagonal_mul, Matrix.mul_diagonal]`. Introduce `h choose z hz using h`. Establish `hD : (dg L N π r).det ≠ 0`. Simplify using `only [dg, Matrix.det_diagonal]`.

Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `i _`. Apply the tactic sequence `split_ifs <;> simp [hπ]`. Establish `hmat : dg L N π r * (g : Matrix (Fin N) (Fin N) L) = (Matrix.of z).map (algebraMap (NumberField.RingOfIntegers L) L) * dg L N π r`. Use extensionality with `i j`.

Simplify using `only [dg, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply, Matrix.of_apply]`. Conclude with `hz i j`. Establish `hdet : (Matrix.of z).det = 1`. Establish `h1` using `congrArg Matrix.det hmat`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_mul, g.prop, mul_one]`.

Establish `h2 : algebraMap (NumberField.RingOfIntegers L) L (Matrix.of z).det = algebraMap (NumberField.RingOfIntegers L) L 1`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, map_one]`. Conclude with `(mul_eq_right₀ hD).mp h1.symm`. Conclude with `(FaithfulSMul.algebraMap_injective _ L) h2`. Use `⟨⟨Matrix.of z, hdet⟩, ?_⟩` and prove the remaining obligations.

Use `hmat using 2` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression. Use extensionality with `i j`. Both sides reduce to the same expression.
-/
private theorem mem_Kg_iff_scaled_entries_integral {L : Type} [Field L] [NumberField L] {N : ℕ}
    (π : NumberField.RingOfIntegers L) (hπ : (π : L) ≠ 0) (r : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin N) L) :
    g ∈ Kg L N π r ↔ ∀ i j : Fin N, ∃ z : NumberField.RingOfIntegers L,
      (if (i : ℕ) < r then (π : L) else 1) * (g : Matrix (Fin N) (Fin N) L) i j =
        (z : L) * (if (j : ℕ) < r then (π : L) else 1) := by
  have hmem : g ∈ Kg L N π r ↔ ∃ γ, dg L N π r * (mt L N) g = (mo L N) γ * dg L N π r := Iff.rfl
  rw [hmem]
  constructor
  · rintro ⟨γ, hγ⟩ i j
    refine ⟨(γ : Matrix (Fin N) (Fin N) _) i j, ?_⟩
    have h := congrFun (congrFun hγ i) j
    simpa [dg, mt, mo, Matrix.diagonal_mul, Matrix.mul_diagonal] using h
  · intro h
    choose z hz using h
    have hD : (dg L N π r).det ≠ 0 := by
      simp only [dg, Matrix.det_diagonal]
      rw [Finset.prod_ne_zero_iff]
      intro i _
      split_ifs <;> simp [hπ]
    have hmat : dg L N π r * (g : Matrix (Fin N) (Fin N) L) =
        (Matrix.of z).map (algebraMap (NumberField.RingOfIntegers L) L) * dg L N π r := by
      ext i j
      simp only [dg, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply, Matrix.of_apply]
      exact hz i j
    have hdet : (Matrix.of z).det = 1 := by
      have h1 := congrArg Matrix.det hmat
      rw [Matrix.det_mul, Matrix.det_mul, g.prop, mul_one] at h1
      have h2 : algebraMap (NumberField.RingOfIntegers L) L (Matrix.of z).det = algebraMap (NumberField.RingOfIntegers L) L 1 := by
        rw [RingHom.map_det, RingHom.mapMatrix_apply, map_one]
        exact (mul_eq_right₀ hD).mp h1.symm
      exact (FaithfulSMul.algebraMap_injective _ L) h2
    refine ⟨⟨Matrix.of z, hdet⟩, ?_⟩
    convert hmat using 2
    · rfl
    · ext i j
      rfl

/- English proof (translation)
Establish `hD : (dg L N π r).det ≠ 0`. Simplify using `only [dg, Matrix.det_diagonal]`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `i _`. Apply the tactic sequence `split_ifs <;> simp [hπ]`.

Establish `hU : IsUnit (dg L N π r).det` using `isUnit_iff_ne_zero.mpr hD`. Establish `hconj : ∀ ξ : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L), ∃ e : Matrix.SpecialLinearGroup (Fin N) L, dg L N π r * (mt L N) e = (mo L N) ξ * dg L N π r`. Introduce `ξ`. Establish `hdet : ((dg L N π r)⁻¹ * (mo L N) ξ * dg L N π r).det = 1`. Rewrite using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv]`.

Establish `: ((mo L N) ξ).det = 1` using `by show ((ξ : Matrix (Fin N) (Fin N) _).map (algebraMap (NumberField.RingOfIntegers L) L)).det = 1`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det, ξ.prop, map_one]`. Rewrite using `[this, mul_one, Ring.inverse_mul_cancel _ hU]`. Use `⟨⟨_, hdet⟩, ?_⟩` and prove the remaining obligations. Use `show dg L N π r * ((dg L N π r)⁻¹ * (mo L N) ξ * dg L N π r) = _`.

Rewrite using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hU]`. Introduce `g hg hgE g' hg' hg'E`. Take `⟨γ, hγ⟩` from `hg`. Take `⟨γ', hγ'⟩` from `hg'`. Establish `hγS : γ ∉ S` using `fun h => hgE ((hES g γ hγ).mpr h)`.

Establish `hγ'S : γ' ∉ S` using `fun h => hg'E ((hES g' γ' hγ').mpr h)`. Take `⟨ξ, hξ, η, hη, hδ⟩` from `hS γ γ' hγS hγ'S`. Take `⟨e, he⟩` from `hconj ξ`. Take `⟨e', he'⟩` from `hconj η`. Use `⟨e, (hES e ξ he).mpr hξ, e', (hES e' η he').mpr hη, ?_⟩` and prove the remaining obligations.

Establish `key : dg L N π r * (mt L N) (e * g * e') = (mo L N) γ' * dg L N π r`. Rewrite using `[hδ, map_mul, map_mul, map_mul, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hinj : (mt L N) g' = (mt L N) (e * g * e')`. Use `congrArg (fun M => (dg L N π r)⁻¹ * M) (hγ'.trans key.symm)` as an intermediate fact.

Simplify `this` using `only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]`. Conclude with `Matrix.SpecialLinearGroup.ext _ _ (fun i j => congrFun (congrFun hinj i) j)`.
-/
private theorem twoTr_Kg_of_double_coset_set_of_iff {L : Type} [Field L] [NumberField L] {N : ℕ}
    (π : NumberField.RingOfIntegers L) (hπ : (π : L) ≠ 0) (r : ℕ)
    (E : Subgroup (Matrix.SpecialLinearGroup (Fin N) L))
    (S : Set (Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L)))
    (hS : ∀ γ δ, γ ∉ S → δ ∉ S → ∃ ξ ∈ S, ∃ η ∈ S, δ = ξ * γ * η)
    (hES : ∀ g γ, dg L N π r * (mt L N) g = (mo L N) γ * dg L N π r → (g ∈ E ↔ γ ∈ S)) :
    TwoTr E (Kg L N π r) := by
  have hD : (dg L N π r).det ≠ 0 := by
    simp only [dg, Matrix.det_diagonal]
    rw [Finset.prod_ne_zero_iff]
    intro i _
    split_ifs <;> simp [hπ]
  have hU : IsUnit (dg L N π r).det := isUnit_iff_ne_zero.mpr hD
  have hconj : ∀ ξ : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L),
      ∃ e : Matrix.SpecialLinearGroup (Fin N) L,
        dg L N π r * (mt L N) e = (mo L N) ξ * dg L N π r := by
    intro ξ
    have hdet : ((dg L N π r)⁻¹ * (mo L N) ξ * dg L N π r).det = 1 := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv]
      have : ((mo L N) ξ).det = 1 := by
        show ((ξ : Matrix (Fin N) (Fin N) _).map (algebraMap (NumberField.RingOfIntegers L) L)).det = 1
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, ξ.prop, map_one]
      rw [this, mul_one, Ring.inverse_mul_cancel _ hU]
    refine ⟨⟨_, hdet⟩, ?_⟩
    show dg L N π r * ((dg L N π r)⁻¹ * (mo L N) ξ * dg L N π r) = _
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hU]
  intro g hg hgE g' hg' hg'E
  obtain ⟨γ, hγ⟩ := hg
  obtain ⟨γ', hγ'⟩ := hg'
  have hγS : γ ∉ S := fun h => hgE ((hES g γ hγ).mpr h)
  have hγ'S : γ' ∉ S := fun h => hg'E ((hES g' γ' hγ').mpr h)
  obtain ⟨ξ, hξ, η, hη, hδ⟩ := hS γ γ' hγS hγ'S
  obtain ⟨e, he⟩ := hconj ξ
  obtain ⟨e', he'⟩ := hconj η
  refine ⟨e, (hES e ξ he).mpr hξ, e', (hES e' η he').mpr hη, ?_⟩
  have key : dg L N π r * (mt L N) (e * g * e') = (mo L N) γ' * dg L N π r := by
    rw [hδ, map_mul, map_mul, map_mul, map_mul]
    calc dg L N π r * ((mt L N) e * (mt L N) g * (mt L N) e')
        = (dg L N π r * (mt L N) e) * (mt L N) g * (mt L N) e' := by simp only [Matrix.mul_assoc]
      _ = (mo L N) ξ * (dg L N π r * (mt L N) g) * (mt L N) e' := by rw [he]; simp only [Matrix.mul_assoc]
      _ = (mo L N) ξ * (mo L N) γ * (dg L N π r * (mt L N) e') := by rw [hγ]; simp only [Matrix.mul_assoc]
      _ = (mo L N) ξ * (mo L N) γ * (mo L N) η * dg L N π r := by rw [he']; simp only [Matrix.mul_assoc]
  have hinj : (mt L N) g' = (mt L N) (e * g * e') := by
    have := congrArg (fun M => (dg L N π r)⁻¹ * M) (hγ'.trans key.symm)
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul] using this
  exact Matrix.SpecialLinearGroup.ext _ _ (fun i j => congrFun (congrFun hinj i) j)

/- English proof (translation)
Rewrite using `[mem_Kg_iff_scaled_entries_integral π hπ s g]`. Establish `hent : ∀ i j : Fin N, (if (i : ℕ) < r then (π : L) else 1) * (g : Matrix (Fin N) (Fin N) L) i j = (((γ : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i j : NumberField.RingOfIntegers L) : L) * (if (j : ℕ) < r then (π : L) else 1)`. Introduce `i j`. Use `congrFun (congrFun h i) j` as an intermediate fact. Simplify `this` using `[dg, mt, mo, Matrix.diagonal_mul, Matrix.mul_diagonal]`.

Establish `hne : ∀ i : Fin N, (if (i : ℕ) < r then (π : L) else 1) ≠ 0`. Apply the tactic sequence `intro i; split_ifs <;> simp [hπ]`. Apply `forall_congr'` to reduce the goal to its premises. Introduce `i`. Apply `forall_congr'` to reduce the goal to its premises.

Introduce `j`. Apply `exists_congr` to reduce the goal to its premises. Introduce `z`. Prove the components needed by the constructor for the conclusion. Introduce `hz`.

Combine the equalities or inequalities in the displayed calculation. Introduce `hz`. Apply `mul_right_cancel₀ (hne i)` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem scaled_integral_entry_eq_swap_scales {L : Type} [Field L] [NumberField L] {N : ℕ}
    (π : NumberField.RingOfIntegers L) (hπ : (π : L) ≠ 0) (r s : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin N) L)
    (γ : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L))
    (h : dg L N π r * (mt L N) g = (mo L N) γ * dg L N π r) :
    g ∈ Kg L N π s ↔ ∀ i j : Fin N, ∃ z : NumberField.RingOfIntegers L,
      (if (i : ℕ) < s then (π : L) else 1) * (if (j : ℕ) < r then (π : L) else 1) *
        (((γ : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i j : NumberField.RingOfIntegers L) : L) =
      (z : L) * (if (j : ℕ) < s then (π : L) else 1) * (if (i : ℕ) < r then (π : L) else 1) := by
  rw [mem_Kg_iff_scaled_entries_integral π hπ s g]
  have hent : ∀ i j : Fin N, (if (i : ℕ) < r then (π : L) else 1) * (g : Matrix (Fin N) (Fin N) L) i j =
      (((γ : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i j : NumberField.RingOfIntegers L) : L) * (if (j : ℕ) < r then (π : L) else 1) := by
    intro i j
    have := congrFun (congrFun h i) j
    simpa [dg, mt, mo, Matrix.diagonal_mul, Matrix.mul_diagonal] using this
  have hne : ∀ i : Fin N, (if (i : ℕ) < r then (π : L) else 1) ≠ 0 := by
    intro i; split_ifs <;> simp [hπ]
  apply forall_congr'; intro i; apply forall_congr'; intro j
  apply exists_congr; intro z
  constructor
  · intro hz
    calc _ = (if (i : ℕ) < s then (π : L) else 1) * ((((γ : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i j : NumberField.RingOfIntegers L) : L) *
          (if (j : ℕ) < r then (π : L) else 1)) := by ring
      _ = (if (i : ℕ) < s then (π : L) else 1) * ((if (i : ℕ) < r then (π : L) else 1) *
          (g : Matrix (Fin N) (Fin N) L) i j) := by rw [hent]
      _ = ((if (i : ℕ) < s then (π : L) else 1) * (g : Matrix (Fin N) (Fin N) L) i j) *
          (if (i : ℕ) < r then (π : L) else 1) := by ring
      _ = _ := by rw [hz]
  · intro hz
    apply mul_right_cancel₀ (hne i)
    calc _ = (if (i : ℕ) < s then (π : L) else 1) * ((if (i : ℕ) < r then (π : L) else 1) *
          (g : Matrix (Fin N) (Fin N) L) i j) := by ring
      _ = (if (i : ℕ) < s then (π : L) else 1) * ((((γ : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i j : NumberField.RingOfIntegers L) : L) *
          (if (j : ℕ) < r then (π : L) else 1)) := by rw [hent]
      _ = _ := by rw [← hz]; ring

/- English proof (translation)
Establish `hg0 : g ∈ Kg L N π 0` using `⟨γ, h⟩`. Establish `hik : ∀ i : Fin N, (i : ℕ) < 1 ↔ i = k` using `fun i => by`. Rewrite using `[Nat.lt_one_iff, ← hk, Fin.val_inj]`. Rewrite using `[Subgroup.mem_inf, scaled_integral_entry_eq_swap_scales π hπ 0 1 g γ h]`. Simplify using `only [Nat.not_lt_zero, if_false, mul_one, hik, Set.mem_setOf_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, H⟩ i hi`. Take `⟨z, hz⟩` from `H i k`. Simplify using `only [hi, if_false, if_true, one_mul] at hz`. Use `⟨z, ?_⟩` and prove the remaining obligations.

Apply `FaithfulSMul.algebraMap_injective (NumberField.RingOfIntegers L) L` to reduce the goal to its premises. Simplify using `only [map_mul]`. Conclude with `hz.trans (mul_comm _ _)`. Introduce `H`. Use `⟨hg0, fun i j => ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `by_cases hi : i = k <;> by_cases hj : j = k`. Conclude with `⟨(γ : Matrix (Fin N) (Fin N) _) i j, by simp [hi, hj, mul_comm]⟩`. Conclude with `⟨π * (γ : Matrix (Fin N) (Fin N) _) i j, by simp [hi, hj]⟩`. Take `⟨z, hz⟩` from `H i hi`. Use `⟨z, ?_⟩` and prove the remaining obligations.

Substitute `hj` using the available equality. Simplify using `only [hi, if_false, if_true, one_mul]`. Rewrite using `[hz]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `⟨(γ : Matrix (Fin N) (Fin N) _) i j, by simp [hi, hj]⟩`.
-/
private theorem mem_Kg_zero_inf_Kg_one_iff_col_dvd_pi {L : Type} [Field L] [NumberField L] {N : ℕ}
    (π : NumberField.RingOfIntegers L) (hπ : (π : L) ≠ 0) (k : Fin N) (hk : (k : ℕ) = 0)
    (g : Matrix.SpecialLinearGroup (Fin N) L)
    (γ : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L))
    (h : dg L N π 0 * (mt L N) g = (mo L N) γ * dg L N π 0) :
    g ∈ Kg L N π 0 ⊓ Kg L N π 1 ↔
      γ ∈ {x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L) |
        ∀ i, i ≠ k → π ∣ (x : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i k} := by
  have hg0 : g ∈ Kg L N π 0 := ⟨γ, h⟩
  have hik : ∀ i : Fin N, (i : ℕ) < 1 ↔ i = k := fun i => by
    rw [Nat.lt_one_iff, ← hk, Fin.val_inj]
  rw [Subgroup.mem_inf, scaled_integral_entry_eq_swap_scales π hπ 0 1 g γ h]
  simp only [Nat.not_lt_zero, if_false, mul_one, hik, Set.mem_setOf_eq]
  constructor
  · rintro ⟨-, H⟩ i hi
    obtain ⟨z, hz⟩ := H i k
    simp only [hi, if_false, if_true, one_mul] at hz
    refine ⟨z, ?_⟩
    apply FaithfulSMul.algebraMap_injective (NumberField.RingOfIntegers L) L
    simp only [map_mul]
    exact hz.trans (mul_comm _ _)
  · intro H
    refine ⟨hg0, fun i j => ?_⟩
    by_cases hi : i = k <;> by_cases hj : j = k
    · exact ⟨(γ : Matrix (Fin N) (Fin N) _) i j, by simp [hi, hj, mul_comm]⟩
    · exact ⟨π * (γ : Matrix (Fin N) (Fin N) _) i j, by simp [hi, hj]⟩
    · obtain ⟨z, hz⟩ := H i hi
      refine ⟨z, ?_⟩
      subst hj
      simp only [hi, if_false, if_true, one_mul]
      rw [hz]; push_cast; ring
    · exact ⟨(γ : Matrix (Fin N) (Fin N) _) i j, by simp [hi, hj]⟩

/- English proof (translation)
Establish `hgr : g ∈ Kg L N π 1` using `⟨γ, h⟩`. Establish `h1 : ∀ i : Fin N, (i : ℕ) < 1 ↔ i = k0` using `fun i => by`. Rewrite using `[Nat.lt_one_iff, ← hk0, Fin.val_inj]`. Establish `h2 : ∀ i : Fin N, (i : ℕ) < 2 ↔ i = k0 ∨ i = k1` using `fun i => by`. Rewrite using `[← Fin.val_inj, ← Fin.val_inj, hk0, hk1]`.

Use linear arithmetic over natural numbers and integers. Establish `hne : k0 ≠ k1` using `fun e => by rw [← Fin.val_inj, hk0, hk1] at e; omega`. Rewrite using `[Subgroup.mem_inf, scaled_integral_entry_eq_swap_scales π hπ 1 2 g γ h]`. Simplify using `only [h1, h2, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨-, H⟩ i hi`. Take `⟨z, hz⟩` from `H i k1`. Use `⟨z, ?_⟩` and prove the remaining obligations. Apply `FaithfulSMul.algebraMap_injective (NumberField.RingOfIntegers L) L` to reduce the goal to its premises. Simplify using `only [map_mul]`.

Distinguish the cases in `hi0 : i = k0`. Substitute `hi0` using the available equality. Simplify using `only [true_or, if_true, or_true, hne.symm, if_false, mul_one] at hz`. Apply `mul_left_cancel₀ hπ` to reduce the goal to its premises. Take the linear combination `hz`.

Simplify using `only [hi0, hi, or_self, if_false, or_true, if_true, hne.symm, one_mul, mul_one] at hz`. Take the linear combination `hz`. Introduce `H`. Use `⟨hgr, fun i j => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `by_cases hi0 : i = k0 <;> by_cases hi1 : i = k1 <;> by_cases hj0 : j = k0 <;> by_cases hj1 : j = k1`.

Apply the tactic sequence `all_goals first`. Consider the case `(exfalso; exact hne (hi0.symm.trans hi1))`. Consider the case `(exfalso; exact hne (hj0.symm.trans hj1))`. Consider the case `skip`. Apply the tactic sequence `all_goals simp only [hi0, hi1, hj0, hj1, hne, hne.symm, true_or, or_true, or_self, if_true, if_false, one_mul, mul_one]`.

Apply the tactic sequence `all_goals first`. Consider the case `(refine ⟨((γ : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i j), ?_⟩; subst_vars; push_cast; ring; done)`. Consider the case `(refine ⟨π * ((γ : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i j), ?_⟩; subst_vars; push_cast; ring; done)`. Consider the case `(obtain ⟨w, hw⟩ := H i ‹_›`. Use `⟨w, ?_⟩` and prove the remaining obligations.

Use `subst_vars`. Rewrite using `[hw]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `done)`.
-/
private theorem mem_Kg_one_inf_Kg_two_iff_col_dvd_pi_of_dg_one {L : Type} [Field L] [NumberField L] {N : ℕ}
    (π : NumberField.RingOfIntegers L) (hπ : (π : L) ≠ 0) (k0 k1 : Fin N) (hk0 : (k0 : ℕ) = 0)
    (hk1 : (k1 : ℕ) = 1)
    (g : Matrix.SpecialLinearGroup (Fin N) L)
    (γ : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L))
    (h : dg L N π 1 * (mt L N) g = (mo L N) γ * dg L N π 1) :
    g ∈ Kg L N π 1 ⊓ Kg L N π 2 ↔
      γ ∈ {x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L) |
        ∀ i, i ≠ k1 → π ∣ (x : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i k1} := by
  have hgr : g ∈ Kg L N π 1 := ⟨γ, h⟩
  have h1 : ∀ i : Fin N, (i : ℕ) < 1 ↔ i = k0 := fun i => by
    rw [Nat.lt_one_iff, ← hk0, Fin.val_inj]
  have h2 : ∀ i : Fin N, (i : ℕ) < 2 ↔ i = k0 ∨ i = k1 := fun i => by
    rw [← Fin.val_inj, ← Fin.val_inj, hk0, hk1]; omega
  have hne : k0 ≠ k1 := fun e => by rw [← Fin.val_inj, hk0, hk1] at e; omega
  rw [Subgroup.mem_inf, scaled_integral_entry_eq_swap_scales π hπ 1 2 g γ h]
  simp only [h1, h2, Set.mem_setOf_eq]
  constructor
  · rintro ⟨-, H⟩ i hi
    obtain ⟨z, hz⟩ := H i k1
    refine ⟨z, ?_⟩
    apply FaithfulSMul.algebraMap_injective (NumberField.RingOfIntegers L) L
    simp only [map_mul]
    by_cases hi0 : i = k0
    · subst hi0
      simp only [true_or, if_true, or_true, hne.symm, if_false, mul_one] at hz
      apply mul_left_cancel₀ hπ
      linear_combination hz
    · simp only [hi0, hi, or_self, if_false, or_true, if_true, hne.symm, one_mul, mul_one] at hz
      linear_combination hz
  · intro H
    refine ⟨hgr, fun i j => ?_⟩
    by_cases hi0 : i = k0 <;> by_cases hi1 : i = k1 <;> by_cases hj0 : j = k0 <;> by_cases hj1 : j = k1
    all_goals first
      | (exfalso; exact hne (hi0.symm.trans hi1))
      | (exfalso; exact hne (hj0.symm.trans hj1))
      | skip
    all_goals simp only [hi0, hi1, hj0, hj1, hne, hne.symm, true_or, or_true, or_self, if_true, if_false,
      one_mul, mul_one]
    all_goals first
      | (refine ⟨((γ : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i j), ?_⟩; subst_vars; push_cast; ring; done)
      | (refine ⟨π * ((γ : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i j), ?_⟩; subst_vars; push_cast; ring; done)
      | (obtain ⟨w, hw⟩ := H i ‹_›
         refine ⟨w, ?_⟩; subst_vars; rw [hw]; push_cast; ring; done)

/- English proof (translation)
Establish `hgr : g ∈ Kg L N π 2` using `⟨γ, h⟩`. Establish `h1 : ∀ i : Fin N, (i : ℕ) < 1 ↔ i = k0` using `fun i => by`. Rewrite using `[Nat.lt_one_iff, ← hk0, Fin.val_inj]`. Establish `h2 : ∀ i : Fin N, (i : ℕ) < 2 ↔ i = k0 ∨ i = k1` using `fun i => by`. Rewrite using `[← Fin.val_inj, ← Fin.val_inj, hk0, hk1]`.

Use linear arithmetic over natural numbers and integers. Establish `hne : k0 ≠ k1` using `fun e => by rw [← Fin.val_inj, hk0, hk1] at e; omega`. Rewrite using `[Subgroup.mem_inf, scaled_integral_entry_eq_swap_scales π hπ 2 1 g γ h]`. Simplify using `only [h1, h2, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨H, -⟩ j hj`. Take `⟨z, hz⟩` from `H k1 j`. Use `⟨z, ?_⟩` and prove the remaining obligations. Apply `FaithfulSMul.algebraMap_injective (NumberField.RingOfIntegers L) L` to reduce the goal to its premises. Simplify using `only [map_mul]`.

Distinguish the cases in `hj0 : j = k0`. Substitute `hj0` using the available equality. Simplify using `only [true_or, if_true, or_true, hne.symm, if_false, mul_one, one_mul] at hz`. Apply `mul_left_cancel₀ hπ` to reduce the goal to its premises. Take the linear combination `hz`.

Simplify using `only [hj0, hj, or_self, if_false, or_true, if_true, hne.symm, one_mul, mul_one] at hz`. Take the linear combination `hz`. Introduce `H`. Use `⟨fun i j => ?_, hgr⟩` and prove the remaining obligations. Apply the tactic sequence `by_cases hi0 : i = k0 <;> by_cases hi1 : i = k1 <;> by_cases hj0 : j = k0 <;> by_cases hj1 : j = k1`.

Apply the tactic sequence `all_goals first`. Consider the case `(exfalso; exact hne (hi0.symm.trans hi1))`. Consider the case `(exfalso; exact hne (hj0.symm.trans hj1))`. Consider the case `skip`. Apply the tactic sequence `all_goals simp only [hi0, hi1, hj0, hj1, hne, hne.symm, true_or, or_true, or_self, if_true, if_false, one_mul, mul_one]`.

Apply the tactic sequence `all_goals first`. Consider the case `(refine ⟨((γ : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i j), ?_⟩; subst_vars; push_cast; ring; done)`. Consider the case `(refine ⟨π * ((γ : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i j), ?_⟩; subst_vars; push_cast; ring; done)`. Consider the case `(obtain ⟨w, hw⟩ := H j ‹_›`. Use `⟨w, ?_⟩` and prove the remaining obligations.

Use `subst_vars`. Rewrite using `[hw]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `done)`.
-/
private theorem mem_Kg_one_inf_Kg_two_iff_transpose_dvd_pi_of_dg_two {L : Type} [Field L] [NumberField L] {N : ℕ}
    (π : NumberField.RingOfIntegers L) (hπ : (π : L) ≠ 0) (k0 k1 : Fin N) (hk0 : (k0 : ℕ) = 0)
    (hk1 : (k1 : ℕ) = 1)
    (g : Matrix.SpecialLinearGroup (Fin N) L)
    (γ : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L))
    (h : dg L N π 2 * (mt L N) g = (mo L N) γ * dg L N π 2) :
    g ∈ Kg L N π 1 ⊓ Kg L N π 2 ↔
      γ ∈ {x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L) |
        ∀ j, j ≠ k1 → π ∣ (x : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) k1 j} := by
  have hgr : g ∈ Kg L N π 2 := ⟨γ, h⟩
  have h1 : ∀ i : Fin N, (i : ℕ) < 1 ↔ i = k0 := fun i => by
    rw [Nat.lt_one_iff, ← hk0, Fin.val_inj]
  have h2 : ∀ i : Fin N, (i : ℕ) < 2 ↔ i = k0 ∨ i = k1 := fun i => by
    rw [← Fin.val_inj, ← Fin.val_inj, hk0, hk1]; omega
  have hne : k0 ≠ k1 := fun e => by rw [← Fin.val_inj, hk0, hk1] at e; omega
  rw [Subgroup.mem_inf, scaled_integral_entry_eq_swap_scales π hπ 2 1 g γ h]
  simp only [h1, h2, Set.mem_setOf_eq]
  constructor
  · rintro ⟨H, -⟩ j hj
    obtain ⟨z, hz⟩ := H k1 j
    refine ⟨z, ?_⟩
    apply FaithfulSMul.algebraMap_injective (NumberField.RingOfIntegers L) L
    simp only [map_mul]
    by_cases hj0 : j = k0
    · subst hj0
      simp only [true_or, if_true, or_true, hne.symm, if_false, mul_one, one_mul] at hz
      apply mul_left_cancel₀ hπ
      linear_combination hz
    · simp only [hj0, hj, or_self, if_false, or_true, if_true, hne.symm, one_mul, mul_one] at hz
      linear_combination hz
  · intro H
    refine ⟨fun i j => ?_, hgr⟩
    by_cases hi0 : i = k0 <;> by_cases hi1 : i = k1 <;> by_cases hj0 : j = k0 <;> by_cases hj1 : j = k1
    all_goals first
      | (exfalso; exact hne (hi0.symm.trans hi1))
      | (exfalso; exact hne (hj0.symm.trans hj1))
      | skip
    all_goals simp only [hi0, hi1, hj0, hj1, hne, hne.symm, true_or, or_true, or_self, if_true, if_false,
      one_mul, mul_one]
    all_goals first
      | (refine ⟨((γ : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i j), ?_⟩; subst_vars; push_cast; ring; done)
      | (refine ⟨π * ((γ : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i j), ?_⟩; subst_vars; push_cast; ring; done)
      | (obtain ⟨w, hw⟩ := H j ‹_›
         refine ⟨w, ?_⟩; subst_vars; rw [hw]; push_cast; ring; done)

/- English proof (translation)
Use `haveI : (H.subgroupOf A).FiniteIndex := ⟨hfin⟩`. Rewrite using `[Subgroup.index]`. Use `choose s hs using (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk I))`. Set `φ : R ⧸ I → A ⧸ H.subgroupOf A` to `fun q => (QuotientGroup.mk (⟨f (s q), hf _⟩ : A))`. Apply `Nat.card_le_card_of_injective φ` to reduce the goal to its premises.

Introduce `q₁ q₂ hq`. Establish `h` using `QuotientGroup.eq.mp hq`. Rewrite `h` using `[Subgroup.mem_subgroupOf]`. Establish `h' : s q₂ - s q₁ ∈ I` using `hinj _ _ (by simpa using h)`. Rewrite using `[← hs q₁, ← hs q₂]`.

Conclude with `(Ideal.Quotient.eq.mpr h').symm`.
-/
private theorem card_quotient_le_index_of_injective_mod {G R : Type} [Group G] [CommRing R] (I : Ideal R)
    (A H : Subgroup G) (hfin : (H.subgroupOf A).index ≠ 0) (f : R → G) (hf : ∀ x, f x ∈ A)
    (hinj : ∀ x y, (f x)⁻¹ * f y ∈ H → y - x ∈ I) :
    Nat.card (R ⧸ I) ≤ (H.subgroupOf A).index := by
  haveI : (H.subgroupOf A).FiniteIndex := ⟨hfin⟩
  rw [Subgroup.index]
  choose s hs using (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk I))
  let φ : R ⧸ I → A ⧸ H.subgroupOf A := fun q => (QuotientGroup.mk (⟨f (s q), hf _⟩ : A))
  apply Nat.card_le_card_of_injective φ
  intro q₁ q₂ hq
  have h := QuotientGroup.eq.mp hq
  rw [Subgroup.mem_subgroupOf] at h
  have h' : s q₂ - s q₁ ∈ I := hinj _ _ (by simpa using h)
  rw [← hs q₁, ← hs q₂]
  exact (Ideal.Quotient.eq.mpr h').symm

/- English proof (translation)
Use `(mem_Kg_iff_scaled_entries_integral π hπ r _).mpr ?_` and prove the remaining obligations. Introduce `p q`. Simplify using `only [Matrix.SpecialLinearGroup.coe_mk]`. Use `⟨Matrix.transvection a b x p q, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single, Matrix.of_apply]`.

Distinguish the cases in `hpq : p = q`. Substitute `hpq` using the available equality. Establish `: ¬ (a = p ∧ b = p)` using `fun h => hab (h.1.trans h.2.symm)`. Simplify using `[this]`. Distinguish the cases in `h : a = p ∧ b = q`.

Take `⟨rfl, rfl⟩` from `h`. Simplify using `only [hab, if_false, if_true, and_self, zero_add]`. Use `push_cast`. Distinguish the cases in `ha : (a : ℕ) < r`. Simplify using `[ha, hr.mp ha, mul_comm]`.

Establish `hb : ¬ (b : ℕ) < r` using `fun h => ha (hr.mpr h)`. Simplify using `[ha, hb]`. Simplify using `[hpq, h]`.
-/
private theorem transvection_mem_Kg_of_same_side {L : Type} [Field L] [NumberField L] {N : ℕ}
    (π : NumberField.RingOfIntegers L) (hπ : (π : L) ≠ 0) (r : ℕ) (a b : Fin N) (hab : a ≠ b)
    (hr : (a : ℕ) < r ↔ (b : ℕ) < r) (x : NumberField.RingOfIntegers L) :
    (show Matrix.SpecialLinearGroup (Fin N) L from ⟨Matrix.transvection a b (x : L), Matrix.det_transvection_of_ne a b hab _⟩) ∈ Kg L N π r := by
  refine (mem_Kg_iff_scaled_entries_integral π hπ r _).mpr ?_
  intro p q
  simp only [Matrix.SpecialLinearGroup.coe_mk]
  refine ⟨Matrix.transvection a b x p q, ?_⟩
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single, Matrix.of_apply]
  by_cases hpq : p = q
  · subst hpq
    have : ¬ (a = p ∧ b = p) := fun h => hab (h.1.trans h.2.symm)
    simp [this]
  · by_cases h : a = p ∧ b = q
    · obtain ⟨rfl, rfl⟩ := h
      simp only [hab, if_false, if_true, and_self, zero_add]
      push_cast
      by_cases ha : (a : ℕ) < r
      · simp [ha, hr.mp ha, mul_comm]
      · have hb : ¬ (b : ℕ) < r := fun h => ha (hr.mpr h)
        simp [ha, hb]
    · simp [hpq, h]

/- English proof (translation)
Take `⟨z, hz⟩` from `(mem_Kg_iff_scaled_entries_integral π hπ r _).mp hx a b`. Simplify using `[Matrix.transvection, Matrix.single, ha, hb, hab] at hz`. Use `⟨z, ?_⟩` and prove the remaining obligations. Apply `FaithfulSMul.algebraMap_injective (NumberField.RingOfIntegers L) L` to reduce the goal to its premises. Simplify using `only [map_mul]`.

Take the linear combination `hz`.
-/
private theorem pi_dvd_of_transvection_mem_Kg_cross {L : Type} [Field L] [NumberField L] {N : ℕ}
    (π : NumberField.RingOfIntegers L) (hπ : (π : L) ≠ 0) (r : ℕ) (a b : Fin N) (hab : a ≠ b)
    (ha : ¬ (a : ℕ) < r) (hb : (b : ℕ) < r) (x : NumberField.RingOfIntegers L)
    (hx : (show Matrix.SpecialLinearGroup (Fin N) L from ⟨Matrix.transvection a b (x : L), Matrix.det_transvection_of_ne a b hab _⟩) ∈ Kg L N π r) : π ∣ x := by
  obtain ⟨z, hz⟩ := (mem_Kg_iff_scaled_entries_integral π hπ r _).mp hx a b
  simp [Matrix.transvection, Matrix.single, ha, hb, hab] at hz
  refine ⟨z, ?_⟩
  apply FaithfulSMul.algebraMap_injective (NumberField.RingOfIntegers L) L
  simp only [map_mul]
  linear_combination hz

/- English proof (translation)
Establish `hab : a ≠ b` using `fun e => by rw [← Fin.val_inj, ha, hb] at e; omega`. Establish `hHA : Kg L N π 0 ⊓ Kg L N π 1 ⊓ Kg L N π 2 ≤ Kg L N π 0 ⊓ Kg L N π 1` using `inf_le_left`. Establish `hA0 : Kg L N π 0 ⊓ Kg L N π 1 ≤ Kg L N π 0` using `fun g hg => hg.1`. Establish `hfinA : ((Kg L N π 0 ⊓ Kg L N π 1 ⊓ Kg L N π 2).subgroupOf (Kg L N π 0 ⊓ Kg L N π 1)).index ≠ 0`. Use `Subgroup.relIndex_mul_relIndex _ _ _ hHA hA0` as an intermediate fact.

Introduce `h0`. Apply `hfin` to reduce the goal to its premises. Rewrite `this` using `[Subgroup.relIndex]`. Rewrite using `[← Subgroup.relIndex, ← this, Subgroup.relIndex, h0, zero_mul]`. Use `le_trans ?_ (card_quotient_le_index_of_injective_mod (Ideal.span {π}) _ _ hfinA (fun x : NumberField.RingOfIntegers L => (show Matrix.SpecialLinearGroup (Fin N) L from ⟨Matrix.transvection a b (x : L), Matrix.det_transvection_of_ne a b hab _⟩)) ?_ ?_)` and prove the remaining obligations.

Rewrite `hn` using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Conclude with `hn`. Introduce `x`. Conclude with `⟨transvection_mem_Kg_of_same_side π hπ 0 a b hab (by omega) x, transvection_mem_Kg_of_same_side π hπ 1 a b hab (by omega) x⟩`. Introduce `x y hxy`.

Establish `heq : ((show Matrix.SpecialLinearGroup (Fin N) L from ⟨Matrix.transvection a b (x : L), Matrix.det_transvection_of_ne a b hab _⟩))⁻¹ * (show Matrix.SpecialLinearGroup (Fin N) L from ⟨Matrix.transvection a b (y : L), Matrix.det_transvection_of_ne a b hab _⟩) = (show Matrix.Special …`. Rewrite using `[inv_mul_eq_iff_eq_mul]`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show Matrix.transvection a b (y : L) = Matrix.transvection a b (x : L) * Matrix.transvection a b (((y - x : NumberField.RingOfIntegers L)) : L)`. Rewrite using `[Matrix.transvection_mul_transvection_same (h := hab)]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hxy` using `[heq]`. Rewrite using `[Ideal.mem_span_singleton]`.

Conclude with `pi_dvd_of_transvection_mem_Kg_cross π hπ 2 a b hab (by omega) (by omega) _ (hxy.2)`.
-/
private theorem twentyfive_le_index_Kg_triple_in_Kg_zero_one {L : Type} [Field L] [NumberField L] {N : ℕ}
    (π : NumberField.RingOfIntegers L) (hπ : (π : L) ≠ 0) (a b : Fin N) (ha : (a : ℕ) = 2) (hb : (b : ℕ) = 1)
    (hn : 25 ≤ Ideal.absNorm (Ideal.span {π}))
    (hfin : ((Kg L N π 0 ⊓ Kg L N π 1 ⊓ Kg L N π 2).subgroupOf (Kg L N π 0)).index ≠ 0) :
    25 ≤ ((Kg L N π 0 ⊓ Kg L N π 1 ⊓ Kg L N π 2).subgroupOf (Kg L N π 0 ⊓ Kg L N π 1)).index := by
  have hab : a ≠ b := fun e => by rw [← Fin.val_inj, ha, hb] at e; omega
  have hHA : Kg L N π 0 ⊓ Kg L N π 1 ⊓ Kg L N π 2 ≤ Kg L N π 0 ⊓ Kg L N π 1 := inf_le_left
  have hA0 : Kg L N π 0 ⊓ Kg L N π 1 ≤ Kg L N π 0 := fun g hg => hg.1
  have hfinA : ((Kg L N π 0 ⊓ Kg L N π 1 ⊓ Kg L N π 2).subgroupOf (Kg L N π 0 ⊓ Kg L N π 1)).index ≠ 0 := by
    have := Subgroup.relIndex_mul_relIndex _ _ _ hHA hA0
    intro h0
    apply hfin
    rw [Subgroup.relIndex] at this
    rw [← Subgroup.relIndex, ← this, Subgroup.relIndex, h0, zero_mul]
  refine le_trans ?_ (card_quotient_le_index_of_injective_mod (Ideal.span {π}) _ _ hfinA
    (fun x : NumberField.RingOfIntegers L => (show Matrix.SpecialLinearGroup (Fin N) L from ⟨Matrix.transvection a b (x : L), Matrix.det_transvection_of_ne a b hab _⟩)) ?_ ?_)
  · rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hn
    exact hn
  · intro x
    exact ⟨transvection_mem_Kg_of_same_side π hπ 0 a b hab (by omega) x, transvection_mem_Kg_of_same_side π hπ 1 a b hab (by omega) x⟩
  · intro x y hxy
    have heq : ((show Matrix.SpecialLinearGroup (Fin N) L from ⟨Matrix.transvection a b (x : L), Matrix.det_transvection_of_ne a b hab _⟩))⁻¹ * (show Matrix.SpecialLinearGroup (Fin N) L from ⟨Matrix.transvection a b (y : L), Matrix.det_transvection_of_ne a b hab _⟩) =
        (show Matrix.SpecialLinearGroup (Fin N) L from ⟨Matrix.transvection a b ((y - x : NumberField.RingOfIntegers L) : L), Matrix.det_transvection_of_ne a b hab _⟩) := by
      rw [inv_mul_eq_iff_eq_mul]
      apply Subtype.ext
      show Matrix.transvection a b (y : L) = Matrix.transvection a b (x : L) *
        Matrix.transvection a b (((y - x : NumberField.RingOfIntegers L)) : L)
      rw [Matrix.transvection_mul_transvection_same (h := hab)]
      congr 1
      push_cast; ring
    rw [heq] at hxy
    rw [Ideal.mem_span_singleton]
    exact pi_dvd_of_transvection_mem_Kg_cross π hπ 2 a b hab (by omega) (by omega) _ (hxy.2)

/- English proof (translation)
Establish `hab : a ≠ b` using `fun e => by rw [← Fin.val_inj, ha, hb] at e; omega`. Establish `hHA : Kg L N π 0 ⊓ Kg L N π 1 ⊓ Kg L N π 2 ≤ Kg L N π 0 ⊓ Kg L N π 2` using `fun g hg => ⟨hg.1.1, hg.2⟩`. Establish `hA0 : Kg L N π 0 ⊓ Kg L N π 2 ≤ Kg L N π 0` using `fun g hg => hg.1`. Establish `hfinA : ((Kg L N π 0 ⊓ Kg L N π 1 ⊓ Kg L N π 2).subgroupOf (Kg L N π 0 ⊓ Kg L N π 2)).index ≠ 0`. Use `Subgroup.relIndex_mul_relIndex _ _ _ hHA hA0` as an intermediate fact.

Introduce `h0`. Apply `hfin` to reduce the goal to its premises. Rewrite `this` using `[Subgroup.relIndex]`. Rewrite using `[← Subgroup.relIndex, ← this, Subgroup.relIndex, h0, zero_mul]`. Use `le_trans ?_ (card_quotient_le_index_of_injective_mod (Ideal.span {π}) _ _ hfinA (fun x : NumberField.RingOfIntegers L => (show Matrix.SpecialLinearGroup (Fin N) L from ⟨Matrix.transvection a b (x : L), Matrix.det_transvection_of_ne a b hab _⟩)) ?_ ?_)` and prove the remaining obligations.

Rewrite `hn` using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Conclude with `hn`. Introduce `x`. Conclude with `⟨transvection_mem_Kg_of_same_side π hπ 0 a b hab (by omega) x, transvection_mem_Kg_of_same_side π hπ 2 a b hab (by omega) x⟩`. Introduce `x y hxy`.

Establish `heq : ((show Matrix.SpecialLinearGroup (Fin N) L from ⟨Matrix.transvection a b (x : L), Matrix.det_transvection_of_ne a b hab _⟩))⁻¹ * (show Matrix.SpecialLinearGroup (Fin N) L from ⟨Matrix.transvection a b (y : L), Matrix.det_transvection_of_ne a b hab _⟩) = (show Matrix.Special …`. Rewrite using `[inv_mul_eq_iff_eq_mul]`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show Matrix.transvection a b (y : L) = Matrix.transvection a b (x : L) * Matrix.transvection a b (((y - x : NumberField.RingOfIntegers L)) : L)`. Rewrite using `[Matrix.transvection_mul_transvection_same (h := hab)]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hxy` using `[heq]`. Rewrite using `[Ideal.mem_span_singleton]`.

Conclude with `pi_dvd_of_transvection_mem_Kg_cross π hπ 1 a b hab (by omega) (by omega) _ (hxy.1.2)`.
-/
private theorem twentyfive_le_index_Kg_triple_in_Kg_zero_two {L : Type} [Field L] [NumberField L] {N : ℕ}
    (π : NumberField.RingOfIntegers L) (hπ : (π : L) ≠ 0) (a b : Fin N) (ha : (a : ℕ) = 1) (hb : (b : ℕ) = 0)
    (hn : 25 ≤ Ideal.absNorm (Ideal.span {π}))
    (hfin : ((Kg L N π 0 ⊓ Kg L N π 1 ⊓ Kg L N π 2).subgroupOf (Kg L N π 0)).index ≠ 0) :
    25 ≤ ((Kg L N π 0 ⊓ Kg L N π 1 ⊓ Kg L N π 2).subgroupOf (Kg L N π 0 ⊓ Kg L N π 2)).index := by
  have hab : a ≠ b := fun e => by rw [← Fin.val_inj, ha, hb] at e; omega
  have hHA : Kg L N π 0 ⊓ Kg L N π 1 ⊓ Kg L N π 2 ≤ Kg L N π 0 ⊓ Kg L N π 2 := fun g hg => ⟨hg.1.1, hg.2⟩
  have hA0 : Kg L N π 0 ⊓ Kg L N π 2 ≤ Kg L N π 0 := fun g hg => hg.1
  have hfinA : ((Kg L N π 0 ⊓ Kg L N π 1 ⊓ Kg L N π 2).subgroupOf (Kg L N π 0 ⊓ Kg L N π 2)).index ≠ 0 := by
    have := Subgroup.relIndex_mul_relIndex _ _ _ hHA hA0
    intro h0
    apply hfin
    rw [Subgroup.relIndex] at this
    rw [← Subgroup.relIndex, ← this, Subgroup.relIndex, h0, zero_mul]
  refine le_trans ?_ (card_quotient_le_index_of_injective_mod (Ideal.span {π}) _ _ hfinA
    (fun x : NumberField.RingOfIntegers L => (show Matrix.SpecialLinearGroup (Fin N) L from ⟨Matrix.transvection a b (x : L), Matrix.det_transvection_of_ne a b hab _⟩)) ?_ ?_)
  · rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hn
    exact hn
  · intro x
    exact ⟨transvection_mem_Kg_of_same_side π hπ 0 a b hab (by omega) x, transvection_mem_Kg_of_same_side π hπ 2 a b hab (by omega) x⟩
  · intro x y hxy
    have heq : ((show Matrix.SpecialLinearGroup (Fin N) L from ⟨Matrix.transvection a b (x : L), Matrix.det_transvection_of_ne a b hab _⟩))⁻¹ * (show Matrix.SpecialLinearGroup (Fin N) L from ⟨Matrix.transvection a b (y : L), Matrix.det_transvection_of_ne a b hab _⟩) =
        (show Matrix.SpecialLinearGroup (Fin N) L from ⟨Matrix.transvection a b ((y - x : NumberField.RingOfIntegers L) : L), Matrix.det_transvection_of_ne a b hab _⟩) := by
      rw [inv_mul_eq_iff_eq_mul]
      apply Subtype.ext
      show Matrix.transvection a b (y : L) = Matrix.transvection a b (x : L) *
        Matrix.transvection a b (((y - x : NumberField.RingOfIntegers L)) : L)
      rw [Matrix.transvection_mul_transvection_same (h := hab)]
      congr 1
      push_cast; ring
    rw [heq] at hxy
    rw [Ideal.mem_span_singleton]
    exact pi_dvd_of_transvection_mem_Kg_cross π hπ 1 a b hab (by omega) (by omega) _ (hxy.1.2)

/- English proof (translation)
Establish `hv : Matrix.mulVec M (fun j => X j k - b / a * (if j = k then 1 else 0)) = 0`. Use function extensionality and compare the values at `i`. Establish `h1 : (M * X) i k = Y i k` using `by rw [hXY]`. Rewrite `h1` using `[Matrix.mul_apply]`. Simplify using `only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.zero_apply]`.

Rewrite using `[h1, hYk, hMk]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h0` using `Matrix.eq_zero_of_mulVec_eq_zero hM hv`. Introduce `i hi`.

Use `congrFun h0 i` as an intermediate fact. Simplify `this` using `[hi]`.
-/
private theorem col_entry_eq_zero_of_mul_cols_proportional {F : Type} [Field F] {N : ℕ}
    (M X Y : Matrix (Fin N) (Fin N) F) (hM : M.det ≠ 0) (hXY : M * X = Y) (k : Fin N)
    (w : Fin N → F) (a b : F) (ha : a ≠ 0) (hMk : ∀ i, M i k = a * w i)
    (hYk : ∀ i, Y i k = b * w i) : ∀ i, i ≠ k → X i k = 0 := by
  have hv : Matrix.mulVec M (fun j => X j k - b / a * (if j = k then 1 else 0)) = 0 := by
    funext i
    have h1 : (M * X) i k = Y i k := by rw [hXY]
    rw [Matrix.mul_apply] at h1
    simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.zero_apply]
    rw [h1, hYk, hMk]
    field_simp
    ring
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero hM hv
  intro i hi
  have := congrFun h0 i
  simpa [hi] using this

/- English proof (translation)
Establish `hdet : ((A : Matrix (Fin N) (Fin N) R).map q).det ≠ 0`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det, A.prop, map_one]`. Conclude with `one_ne_zero`. Establish `hmul : (A : Matrix (Fin N) (Fin N) R).map q * ((A⁻¹ * B : Matrix.SpecialLinearGroup (Fin N) R) : Matrix (Fin N) (Fin N) R).map q = (B : Matrix (Fin N) (Fin N) R).map q`. Rewrite using `[← Matrix.map_mul]`.

Use `congr 1`. Rewrite using `[← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]`. Introduce `i hi`. Use `col_entry_eq_zero_of_mul_cols_proportional _ _ _ hdet hmul k w a b ha (fun i => by simpa using hA i) (fun i => by simpa using hB i) i hi` as an intermediate fact. Simplify using `using this`.
-/
private theorem sl_inv_mul_col_entry_zero_of_cols_proportional {R : Type} [CommRing R] {F : Type} [Field F] (q : R →+* F) {N : ℕ}
    (A B : Matrix.SpecialLinearGroup (Fin N) R) (k : Fin N) (w : Fin N → F) (a b : F) (ha : a ≠ 0)
    (hA : ∀ i, q ((A : Matrix (Fin N) (Fin N) R) i k) = a * w i)
    (hB : ∀ i, q ((B : Matrix (Fin N) (Fin N) R) i k) = b * w i) :
    ∀ i, i ≠ k → q (((A⁻¹ * B : Matrix.SpecialLinearGroup (Fin N) R) : Matrix (Fin N) (Fin N) R) i k) = 0 := by
  have hdet : ((A : Matrix (Fin N) (Fin N) R).map q).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, A.prop, map_one]
    exact one_ne_zero
  have hmul : (A : Matrix (Fin N) (Fin N) R).map q *
      ((A⁻¹ * B : Matrix.SpecialLinearGroup (Fin N) R) : Matrix (Fin N) (Fin N) R).map q =
      (B : Matrix (Fin N) (Fin N) R).map q := by
    rw [← Matrix.map_mul]
    congr 1
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  intro i hi
  have := col_entry_eq_zero_of_mul_cols_proportional _ _ _ hdet hmul k w a b ha (fun i => by simpa using hA i) (fun i => by simpa using hB i) i hi
  simpa using this

/- English proof (translation)
Introduce `h0`. Establish `hdet : ((X : Matrix (Fin N) (Fin N) R).map q).det = 0`. Apply `Matrix.det_eq_zero_of_column_eq_zero k` to reduce the goal to its premises. Introduce `i`. Distinguish the cases in `hi : i = k`.

Substitute `hi` using the available equality. Simplify using `using h0`. Simplify using `using hX i hi`. Rewrite `hdet` using `[← RingHom.mapMatrix_apply, ← RingHom.map_det, X.prop, map_one]`. Conclude with `one_ne_zero hdet`.
-/
private theorem sl_diag_entry_ne_zero_of_col_off_diag_zero {R : Type} [CommRing R] {F : Type} [Field F] (q : R →+* F) {N : ℕ}
    (X : Matrix.SpecialLinearGroup (Fin N) R) (k : Fin N)
    (hX : ∀ i, i ≠ k → q ((X : Matrix (Fin N) (Fin N) R) i k) = 0) :
    q ((X : Matrix (Fin N) (Fin N) R) k k) ≠ 0 := by
  intro h0
  have hdet : ((X : Matrix (Fin N) (Fin N) R).map q).det = 0 := by
    apply Matrix.det_eq_zero_of_column_eq_zero k
    intro i
    by_cases hi : i = k
    · subst hi
      simpa using h0
    · simpa using hX i hi
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, X.prop, map_one] at hdet
  exact one_ne_zero hdet

/- English proof (translation)
Introduce `i hi`. Rewrite using `[Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, map_sum]`. Rewrite using `[Finset.sum_eq_single k]`. Rewrite using `[map_mul, hX i hi, zero_mul]`. Introduce `j _ hj`.

Rewrite using `[map_mul, hY j hj, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ k) h`.
-/
private theorem sl_mul_col_off_diag_zero_of_both {R : Type} [CommRing R] {F : Type} [Field F] (q : R →+* F) {N : ℕ}
    (X Y : Matrix.SpecialLinearGroup (Fin N) R) (k : Fin N)
    (hX : ∀ i, i ≠ k → q ((X : Matrix (Fin N) (Fin N) R) i k) = 0)
    (hY : ∀ i, i ≠ k → q ((Y : Matrix (Fin N) (Fin N) R) i k) = 0) :
    ∀ i, i ≠ k → q (((X * Y : Matrix.SpecialLinearGroup (Fin N) R) : Matrix (Fin N) (Fin N) R) i k) = 0 := by
  intro i hi
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, map_sum]
  rw [Finset.sum_eq_single k]
  · rw [map_mul, hX i hi, zero_mul]
  · intro j _ hj
    rw [map_mul, hY j hj, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

/- English proof (translation)
Take `⟨p, hpk, hp⟩` from `hγ`. Distinguish the cases in `hm : q ((γ : Matrix (Fin N) (Fin N) R) m k) = 0`. Establish `hmp : m ≠ p`. Introduce and unpack `rfl`. Conclude with `hp hm`.

Set `ε : Matrix.SpecialLinearGroup (Fin N) R` to `⟨Matrix.transvection m p 1, Matrix.det_transvection_of_ne m p hmp 1⟩`. Establish `hε : (ε : Matrix (Fin N) (Fin N) R) = Matrix.transvection m p 1` using `rfl`. Use `⟨ε, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Establish `hki : k ≠ p` using `fun h => hpk h.symm`.

Rewrite using `[hε]`. Simplify using `[Matrix.transvection, Matrix.one_apply_ne hi, Matrix.single_apply, hki.symm, Ne.symm hki]`. Rewrite using `[Matrix.SpecialLinearGroup.coe_mul, hε]`. Simplify using `only [Matrix.transvection_mul_apply_same, one_mul, map_add, hm, zero_add]`. Conclude with `hp`.

Use `⟨1, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Simplify using `[Matrix.one_apply_ne hi]`. Simplify using `using hm`.
-/
private theorem exists_col_fixing_mul_entry_ne_zero {R : Type} [CommRing R] {F : Type} [Field F] (q : R →+* F) {N : ℕ}
    (k m : Fin N) (γ : Matrix.SpecialLinearGroup (Fin N) R)
    (hγ : ∃ p, p ≠ k ∧ q ((γ : Matrix (Fin N) (Fin N) R) p k) ≠ 0) :
    ∃ ε : Matrix.SpecialLinearGroup (Fin N) R,
      (∀ i, i ≠ k → q ((ε : Matrix (Fin N) (Fin N) R) i k) = 0) ∧
      q (((ε * γ : Matrix.SpecialLinearGroup (Fin N) R) : Matrix (Fin N) (Fin N) R) m k) ≠ 0 := by
  obtain ⟨p, hpk, hp⟩ := hγ
  by_cases hm : q ((γ : Matrix (Fin N) (Fin N) R) m k) = 0
  · have hmp : m ≠ p := by
      rintro rfl
      exact hp hm
    let ε : Matrix.SpecialLinearGroup (Fin N) R :=
      ⟨Matrix.transvection m p 1, Matrix.det_transvection_of_ne m p hmp 1⟩
    have hε : (ε : Matrix (Fin N) (Fin N) R) = Matrix.transvection m p 1 := rfl
    refine ⟨ε, ?_, ?_⟩
    · intro i hi
      have hki : k ≠ p := fun h => hpk h.symm
      rw [hε]
      simp [Matrix.transvection, Matrix.one_apply_ne hi, Matrix.single_apply, hki.symm, Ne.symm hki]
    · rw [Matrix.SpecialLinearGroup.coe_mul, hε]
      simp only [Matrix.transvection_mul_apply_same, one_mul, map_add, hm, zero_add]
      exact hp
  · refine ⟨1, ?_, ?_⟩
    · intro i hi
      simp [Matrix.one_apply_ne hi]
    · simpa using hm

/- English proof (translation)
Take `⟨t, ht⟩` from `hq (q ((w : Matrix (Fin N) (Fin N) R) m k))⁻¹`. Use `set c : Fin N → R := fun i => if i = m then 0 else -(t * (w : Matrix (Fin N) (Fin N) R) i k) with hc`. Use `set e : Fin N → R := fun j => if j = m then 1 else 0 with he`. Set `E : Matrix (Fin N) (Fin N) R` to `1 + Matrix.replicateCol Unit c * Matrix.replicateRow Unit e`. Establish `hdet : E.det = 1`.

Rewrite using `[Matrix.det_one_add_replicateCol_mul_replicateRow]`. Simplify using `only [hc, he, dotProduct]`. Rewrite using `[add_eq_left]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `x _`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hent : ∀ i j, E i j = (1 : Matrix (Fin N) (Fin N) R) i j + c i * e j`. Introduce `i j`. Simplify using `[E, Matrix.mul_apply]`. Set `ε : Matrix.SpecialLinearGroup (Fin N) R` to `⟨E, hdet⟩`.

Establish `hε : (ε : Matrix (Fin N) (Fin N) R) = E` using `rfl`. Use `⟨ε, ?_, q ((w : Matrix (Fin N) (Fin N) R) m k), hw, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Rewrite using `[hε, hent]`. Simplify using `[Matrix.one_apply_ne hi, he, hkm]`.

Introduce `i`. Rewrite using `[Matrix.SpecialLinearGroup.coe_mul, hε]`. Establish `h2 : (E * (w : Matrix (Fin N) (Fin N) R)) i k = (w : Matrix (Fin N) (Fin N) R) i k + c i * (w : Matrix (Fin N) (Fin N) R) m k`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [hent, add_mul, Finset.sum_add_distrib, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, he, mul_ite, mul_one, mul_zero]`.

Simplify using the standard rewrite rules. Rewrite using `[h2]`. Distinguish the cases in `him : i = m`. Substitute `him` using the available equality. Simplify using `[hc]`.

Simplify using `only [hc, him, if_false, mul_zero, map_add, map_mul, map_neg, ht]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem exists_col_fixing_mul_col_eq_smul_single {R : Type} [CommRing R] {F : Type} [Field F] (q : R →+* F)
    (hq : Function.Surjective q) {N : ℕ}
    (k m : Fin N) (hkm : k ≠ m) (w : Matrix.SpecialLinearGroup (Fin N) R)
    (hw : q ((w : Matrix (Fin N) (Fin N) R) m k) ≠ 0) :
    ∃ ε : Matrix.SpecialLinearGroup (Fin N) R,
      (∀ i, i ≠ k → q ((ε : Matrix (Fin N) (Fin N) R) i k) = 0) ∧
      ∃ u : F, u ≠ 0 ∧ ∀ i, q (((ε * w : Matrix.SpecialLinearGroup (Fin N) R) : Matrix (Fin N) (Fin N) R) i k) =
        u * (if i = m then 1 else 0) := by
  obtain ⟨t, ht⟩ := hq (q ((w : Matrix (Fin N) (Fin N) R) m k))⁻¹
  set c : Fin N → R := fun i => if i = m then 0 else -(t * (w : Matrix (Fin N) (Fin N) R) i k) with hc
  set e : Fin N → R := fun j => if j = m then 1 else 0 with he
  let E : Matrix (Fin N) (Fin N) R := 1 + Matrix.replicateCol Unit c * Matrix.replicateRow Unit e
  have hdet : E.det = 1 := by
    rw [Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp only [hc, he, dotProduct]
    rw [add_eq_left]
    apply Finset.sum_eq_zero
    intro x _
    split_ifs <;> simp
  have hent : ∀ i j, E i j = (1 : Matrix (Fin N) (Fin N) R) i j + c i * e j := by
    intro i j
    simp [E, Matrix.mul_apply]
  let ε : Matrix.SpecialLinearGroup (Fin N) R := ⟨E, hdet⟩
  have hε : (ε : Matrix (Fin N) (Fin N) R) = E := rfl
  refine ⟨ε, ?_, q ((w : Matrix (Fin N) (Fin N) R) m k), hw, ?_⟩
  · intro i hi
    rw [hε, hent]
    simp [Matrix.one_apply_ne hi, he, hkm]
  · intro i
    rw [Matrix.SpecialLinearGroup.coe_mul, hε]
    have h2 : (E * (w : Matrix (Fin N) (Fin N) R)) i k =
        (w : Matrix (Fin N) (Fin N) R) i k + c i * (w : Matrix (Fin N) (Fin N) R) m k := by
      rw [Matrix.mul_apply]
      simp only [hent, add_mul, Finset.sum_add_distrib, Matrix.one_apply, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, he, mul_ite, mul_one, mul_zero]
      simp
    rw [h2]
    by_cases him : i = m
    · subst him
      simp [hc]
    · simp only [hc, him, if_false, mul_zero, map_add, map_mul, map_neg, ht]
      field_simp
      ring

/- English proof (translation)
Establish `hπ0 : π ≠ 0` using `hπ.ne_zero`. Use `haveI hP : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ0).mpr hπ`. Use `haveI : (Ideal.span {π}).IsMaximal := Ideal.IsPrime.isMaximal hP (by rwa [Ne, Ideal.span_singleton_eq_bot])`. Use `letI : Field (NumberField.RingOfIntegers L ⧸ Ideal.span {π}) := Ideal.Quotient.field _`. Use `set q := Ideal.Quotient.mk (Ideal.span {π}) with hq`.

Establish `hdvd : ∀ x, π ∣ x ↔ q x = 0` using `fun x => by`. Rewrite using `[hq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`. Establish `hsurj : Function.Surjective q` using `Ideal.Quotient.mk_surjective`. Establish `hmemS : ∀ x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L), x ∈ {x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L) | ∀ i, i ≠ k → π ∣ (x : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i k} ↔ ∀ i, i ≠ k → q ((x : Matrix (Fin N) (Fin …`. Introduce `x`.

Simplify using `only [Set.mem_setOf_eq, hdvd]`. Establish `step : ∀ γ : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L), γ ∉ {x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L) | ∀ i, i ≠ k → π ∣ (x : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i k} → ∃ ε : Matrix.SpecialLinearGroup (Fin N) ( …`. Introduce `γ hγ`. Rewrite `hγ` using `[hmemS]`. Use `push_neg at hγ`.

Take `⟨ε1, h1S, h1m⟩` from `exists_col_fixing_mul_entry_ne_zero q k m γ hγ`. Take `⟨ε2, h2S, u, hu, hu'⟩` from `exists_col_fixing_mul_col_eq_smul_single q hsurj k m hkm (ε1 * γ) h1m`. Use `⟨ε2 * ε1, sl_mul_col_off_diag_zero_of_both q ε2 ε1 k h2S h1S, u, hu, ?_⟩` and prove the remaining obligations. Introduce `i`. Rewrite using `[mul_assoc]`.

Conclude with `hu' i`. Introduce `γ δ hγ hδ`. Take `⟨A, hAS, u, hu, hAu⟩` from `step γ hγ`. Take `⟨B, hBS, u', hu', hBu⟩` from `step δ hδ`. Establish `hcol : ∀ X : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L), (∀ i, i ≠ k → q ((X : Matrix (Fin N) (Fin N) _) i k) = 0) → ∀ i, q ((X : Matrix (Fin N) (Fin N) _) i k) = q ((X : Matrix (Fin N) (Fin N) _) k k) * (if i = k then 1 else 0)`.

Introduce `X hX i`. Distinguish the cases in `hi : i = k`. Substitute `hi` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hi, hX i hi]`.

Use `⟨B⁻¹ * A, ?_, (A * γ)⁻¹ * (B * δ), ?_, by group⟩` and prove the remaining obligations. Rewrite using `[hmemS]`. Conclude with `sl_inv_mul_col_entry_zero_of_cols_proportional q B A k _ _ _ (sl_diag_entry_ne_zero_of_col_off_diag_zero q B k hBS) (hcol B hBS) (hcol A hAS)`. Rewrite using `[hmemS]`. Conclude with `sl_inv_mul_col_entry_zero_of_cols_proportional q (A * γ) (B * δ) k _ u u' hu hAu hBu`.
-/
private theorem arith_holds_lemma_3 {L : Type} [Field L] [NumberField L] {N : ℕ}
    (π : NumberField.RingOfIntegers L) (hπ : Prime π) (k m : Fin N) (hkm : k ≠ m) :
    ∀ γ δ : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L),
      γ ∉ {x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L) |
        ∀ i, i ≠ k → π ∣ (x : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i k} →
      δ ∉ {x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L) |
        ∀ i, i ≠ k → π ∣ (x : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i k} →
      ∃ ξ ∈ {x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L) |
        ∀ i, i ≠ k → π ∣ (x : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i k},
      ∃ η ∈ {x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L) |
        ∀ i, i ≠ k → π ∣ (x : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i k},
      δ = ξ * γ * η := by
  have hπ0 : π ≠ 0 := hπ.ne_zero
  haveI hP : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ0).mpr hπ
  haveI : (Ideal.span {π}).IsMaximal :=
    Ideal.IsPrime.isMaximal hP (by rwa [Ne, Ideal.span_singleton_eq_bot])
  letI : Field (NumberField.RingOfIntegers L ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  set q := Ideal.Quotient.mk (Ideal.span {π}) with hq
  have hdvd : ∀ x, π ∣ x ↔ q x = 0 := fun x => by
    rw [hq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have hsurj : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hmemS : ∀ x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L),
      x ∈ {x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L) |
        ∀ i, i ≠ k → π ∣ (x : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i k} ↔
      ∀ i, i ≠ k → q ((x : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i k) = 0 := by
    intro x
    simp only [Set.mem_setOf_eq, hdvd]
  have step : ∀ γ : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L),
      γ ∉ {x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L) |
        ∀ i, i ≠ k → π ∣ (x : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i k} →
      ∃ ε : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L),
        (∀ i, i ≠ k → q ((ε : Matrix (Fin N) (Fin N) _) i k) = 0) ∧
        ∃ u, u ≠ 0 ∧ ∀ i, q (((ε * γ : Matrix.SpecialLinearGroup (Fin N) _) : Matrix (Fin N) (Fin N) _) i k) =
          u * (if i = m then 1 else 0) := by
    intro γ hγ
    rw [hmemS] at hγ
    push_neg at hγ
    obtain ⟨ε1, h1S, h1m⟩ := exists_col_fixing_mul_entry_ne_zero q k m γ hγ
    obtain ⟨ε2, h2S, u, hu, hu'⟩ := exists_col_fixing_mul_col_eq_smul_single q hsurj k m hkm (ε1 * γ) h1m
    refine ⟨ε2 * ε1, sl_mul_col_off_diag_zero_of_both q ε2 ε1 k h2S h1S, u, hu, ?_⟩
    intro i
    rw [mul_assoc]
    exact hu' i
  intro γ δ hγ hδ
  obtain ⟨A, hAS, u, hu, hAu⟩ := step γ hγ
  obtain ⟨B, hBS, u', hu', hBu⟩ := step δ hδ
  have hcol : ∀ X : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L),
      (∀ i, i ≠ k → q ((X : Matrix (Fin N) (Fin N) _) i k) = 0) →
      ∀ i, q ((X : Matrix (Fin N) (Fin N) _) i k) =
        q ((X : Matrix (Fin N) (Fin N) _) k k) * (if i = k then 1 else 0) := by
    intro X hX i
    by_cases hi : i = k
    · subst hi
      simp
    · simp [hi, hX i hi]
  refine ⟨B⁻¹ * A, ?_, (A * γ)⁻¹ * (B * δ), ?_, by group⟩
  · rw [hmemS]
    exact sl_inv_mul_col_entry_zero_of_cols_proportional q B A k _ _ _ (sl_diag_entry_ne_zero_of_col_off_diag_zero q B k hBS) (hcol B hBS) (hcol A hAS)
  · rw [hmemS]
    exact sl_inv_mul_col_entry_zero_of_cols_proportional q (A * γ) (B * δ) k _ u u' hu hAu hBu

/- English proof (translation)
Set `T : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L) → Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L)` to `fun x => ⟨Matrix.transpose (x : Matrix (Fin N) (Fin N) _), by rw [Matrix.det_transpose]; exact x.prop⟩`. Establish `hT : ∀ x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L), ((T x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L)) : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) = Matrix.transpose (x : Matrix (Fin N) (Fin N) (NumberField.RingOfIntege …` using `fun x => rfl`. Introduce `γ δ hγ hδ`. Establish `hγ' : T γ ∉ {x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L) | ∀ i, i ≠ k → π ∣ (x : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i k}`. Simplify `hγ` using `[hT]`.

Establish `hδ' : T δ ∉ {x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L) | ∀ i, i ≠ k → π ∣ (x : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i k}`. Simplify `hδ` using `[hT]`. Take `⟨ξ, hξ, η, hη, h⟩` from `arith_holds_lemma_3 π hπ k m hkm (T γ) (T δ) hγ' hδ'`. Use `⟨T η, by simpa [hT] using hη, T ξ, by simpa [hT] using hξ, ?_⟩` and prove the remaining obligations. Apply `Matrix.SpecialLinearGroup.ext` to reduce the goal to its premises.

Introduce `i j`. Establish `h2` using `congrArg (fun x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L) => (Matrix.transpose (x : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L))) i j) h`. Simplify using `only [Matrix.SpecialLinearGroup.coe_mul, hT, Matrix.transpose_mul, Matrix.transpose_transpose] at h2`. Rewrite using `[h2, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hT, hT, Matrix.mul_assoc]`.
-/
private theorem arith_holds_lemma_4 {L : Type} [Field L] [NumberField L] {N : ℕ}
    (π : NumberField.RingOfIntegers L) (hπ : Prime π) (k m : Fin N) (hkm : k ≠ m) :
    ∀ γ δ : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L),
      γ ∉ {x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L) |
        ∀ j, j ≠ k → π ∣ (x : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) k j} →
      δ ∉ {x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L) |
        ∀ j, j ≠ k → π ∣ (x : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) k j} →
      ∃ ξ ∈ {x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L) |
        ∀ j, j ≠ k → π ∣ (x : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) k j},
      ∃ η ∈ {x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L) |
        ∀ j, j ≠ k → π ∣ (x : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) k j},
      δ = ξ * γ * η := by
  let T : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L) →
      Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L) :=
    fun x => ⟨Matrix.transpose (x : Matrix (Fin N) (Fin N) _), by rw [Matrix.det_transpose]; exact x.prop⟩
  have hT : ∀ x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L),
      ((T x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L)) :
        Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) =
      Matrix.transpose (x : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) := fun x => rfl
  intro γ δ hγ hδ
  have hγ' : T γ ∉ {x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L) |
      ∀ i, i ≠ k → π ∣ (x : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i k} := by
    simpa [hT] using hγ
  have hδ' : T δ ∉ {x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L) |
      ∀ i, i ≠ k → π ∣ (x : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L)) i k} := by
    simpa [hT] using hδ
  obtain ⟨ξ, hξ, η, hη, h⟩ := arith_holds_lemma_3 π hπ k m hkm (T γ) (T δ) hγ' hδ'
  refine ⟨T η, by simpa [hT] using hη, T ξ, by simpa [hT] using hξ, ?_⟩
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have h2 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin N) (NumberField.RingOfIntegers L) =>
    (Matrix.transpose (x : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L))) i j) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, hT, Matrix.transpose_mul, Matrix.transpose_transpose] at h2
  rw [h2, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hT, hT, Matrix.mul_assoc]

/- English proof (translation)
Set `ψ : Set.range (fun x : K => φ x) → K ⧸ H.subgroupOf K` to `fun s => QuotientGroup.mk (Classical.choose s.2)`. Establish `hψ : Function.Surjective ψ`. Introduce `q`. Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H x`.

Use `⟨⟨φ x, x, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hc` using `Classical.choose_spec (show ∃ y : K, φ y = φ x from ⟨x, rfl⟩)`. Use `show QuotientGroup.mk _ = QuotientGroup.mk x`. Rewrite using `[QuotientGroup.eq]`. Rewrite using `[Subgroup.mem_subgroupOf]`.

Simplify using `using h _ (Classical.choose (show ∃ y : K, φ y = φ x from ⟨x, rfl⟩)).2 _ x.2 hc`. Use `haveI : Finite (K ⧸ H.subgroupOf K) := Finite.of_surjective ψ hψ`. Conclude with `Subgroup.index_ne_zero_of_finite`.
-/
private theorem index_subgroupOf_ne_zero_of_finite_separating_map {G : Type} [Group G] (K H : Subgroup G) {S : Type} [Finite S]
    (φ : G → S) (h : ∀ a ∈ K, ∀ b ∈ K, φ a = φ b → a⁻¹ * b ∈ H) :
    (H.subgroupOf K).index ≠ 0 := by
  let ψ : Set.range (fun x : K => φ x) → K ⧸ H.subgroupOf K :=
    fun s => QuotientGroup.mk (Classical.choose s.2)
  have hψ : Function.Surjective ψ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      refine ⟨⟨φ x, x, rfl⟩, ?_⟩
      have hc := Classical.choose_spec (show ∃ y : K, φ y = φ x from ⟨x, rfl⟩)
      show QuotientGroup.mk _ = QuotientGroup.mk x
      rw [QuotientGroup.eq]
      rw [Subgroup.mem_subgroupOf]
      simpa using h _ (Classical.choose (show ∃ y : K, φ y = φ x from ⟨x, rfl⟩)).2 _ x.2 hc
  haveI : Finite (K ⧸ H.subgroupOf K) := Finite.of_surjective ψ hψ
  exact Subgroup.index_ne_zero_of_finite

/- English proof (translation)
Use `set ι := algebraMap (NumberField.RingOfIntegers L) L with hι`. Use `set D := dg L N π r with hDdef`. Establish `hD : D.det ≠ 0`. Simplify using `only [hDdef, dg, Matrix.det_diagonal]`. Rewrite using `[Finset.prod_ne_zero_iff]`.

Introduce `i _`. Apply the tactic sequence `split_ifs <;> simp [hπ]`. Establish `hU : IsUnit D.det` using `isUnit_iff_ne_zero.mpr hD`. Establish `hdetA : (A.map ι).det = 1`. Establish `h1` using `congrArg Matrix.det hA`.

Rewrite `h1` using `[Matrix.det_mul, Matrix.det_mul, a.prop, mul_one]`. Conclude with `(mul_eq_right₀ hD).mp h1.symm`. Use `choose Dm hDm using hAB`. Use `set M := Matrix.adjugate A * Matrix.of Dm with hM`. Establish `hB' : B.map ι = A.map ι + (ι π) ^ 2 • (Matrix.of Dm).map ι`.

Use extensionality with `i j`. Use `hDm i j` as an intermediate fact. Simplify using `only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]`. Rewrite using `[← map_pow, ← map_mul, ← this, map_sub]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hMmap : M.map ι = Matrix.adjugate (A.map ι) * (Matrix.of Dm).map ι`. Rewrite using `[hM, Matrix.map_mul, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, RingHom.map_adjugate]`. Establish `hc : (a : Matrix (Fin N) (Fin N) L) * ((a⁻¹ * b : Matrix.SpecialLinearGroup (Fin N) L) : Matrix (Fin N) (Fin N) L) = b`. Rewrite using `[← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]`. Establish `hDc : D * ((a⁻¹ * b : Matrix.SpecialLinearGroup (Fin N) L) : Matrix (Fin N) (Fin N) L) = (1 + (ι π) ^ 2 • M.map ι) * D`.

Establish `hadj : Matrix.adjugate (A.map ι) * A.map ι = 1`. Rewrite using `[Matrix.adjugate_mul, hdetA, one_smul]`. Establish `e1 : A.map ι * (D * ((a⁻¹ * b : Matrix.SpecialLinearGroup (Fin N) L) : Matrix (Fin N) (Fin N) L)) = B.map ι * D`. Rewrite using `[← Matrix.mul_assoc, ← hA, Matrix.mul_assoc, hc, hB]`. Establish `e2 : A.map ι * ((1 + (ι π) ^ 2 • M.map ι) * D) = B.map ι * D`.

Rewrite using `[hMmap, hB', ← Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.mul_adjugate, hdetA, one_smul, Matrix.one_mul]`. Use `congrArg (fun X => Matrix.adjugate (A.map ι) * X) (e1.trans e2.symm)` as an intermediate fact. Simplify `this` using `only [← Matrix.mul_assoc, hadj, Matrix.one_mul]`. Rewrite using `[mem_Kg_iff_scaled_entries_integral π hπ s]`. Introduce `i j`.

Use `⟨(if i = j then 1 else 0) + M i j * (if (i : ℕ) < r then 1 else π) * (if (j : ℕ) < s then 1 else π) * (if (j : ℕ) < r then π else 1) * (if (i : ℕ) < s then π else 1), ?_⟩` and prove the remaining obligations. Establish `hij` using `congrFun (congrFun hDc i) j`. Simplify using `only [hDdef, dg, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at hij`. Apply the tactic sequence `have hdi : (if (i : ℕ) < r then (π : L) else 1) ≠ 0 := by split_ifs <;> simp [hπ]`. Apply `mul_left_cancel₀ hdi` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hij]`. Distinguish the cases in `hij' : i = j`. Apply the tactic sequence `subst hij' split_ifs <;> push_cast <;> ring`. Apply the tactic sequence `simp only [hij', if_false] split_ifs <;> push_cast <;> ring`.
-/
private theorem inv_mul_mem_Kg_of_lifts_congr_pi_sq {L : Type} [Field L] [NumberField L] {N : ℕ}
    (π : NumberField.RingOfIntegers L) (hπ : (π : L) ≠ 0) (r s : ℕ)
    (a b : Matrix.SpecialLinearGroup (Fin N) L)
    (A B : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L))
    (hA : dg L N π r * (a : Matrix (Fin N) (Fin N) L) =
      A.map (algebraMap (NumberField.RingOfIntegers L) L) * dg L N π r)
    (hB : dg L N π r * (b : Matrix (Fin N) (Fin N) L) =
      B.map (algebraMap (NumberField.RingOfIntegers L) L) * dg L N π r)
    (hAB : ∀ i j, π ^ 2 ∣ B i j - A i j) : a⁻¹ * b ∈ Kg L N π s := by
  set ι := algebraMap (NumberField.RingOfIntegers L) L with hι
  set D := dg L N π r with hDdef
  have hD : D.det ≠ 0 := by
    simp only [hDdef, dg, Matrix.det_diagonal]
    rw [Finset.prod_ne_zero_iff]
    intro i _
    split_ifs <;> simp [hπ]
  have hU : IsUnit D.det := isUnit_iff_ne_zero.mpr hD
  have hdetA : (A.map ι).det = 1 := by
    have h1 := congrArg Matrix.det hA
    rw [Matrix.det_mul, Matrix.det_mul, a.prop, mul_one] at h1
    exact (mul_eq_right₀ hD).mp h1.symm
  choose Dm hDm using hAB
  set M := Matrix.adjugate A * Matrix.of Dm with hM
  have hB' : B.map ι = A.map ι + (ι π) ^ 2 • (Matrix.of Dm).map ι := by
    ext i j
    have := hDm i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← map_pow, ← map_mul, ← this, map_sub]
    ring
  have hMmap : M.map ι = Matrix.adjugate (A.map ι) * (Matrix.of Dm).map ι := by
    rw [hM, Matrix.map_mul, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply,
      ← RingHom.mapMatrix_apply, RingHom.map_adjugate]
  have hc : (a : Matrix (Fin N) (Fin N) L) * ((a⁻¹ * b : Matrix.SpecialLinearGroup (Fin N) L) : Matrix (Fin N) (Fin N) L) = b := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  have hDc : D * ((a⁻¹ * b : Matrix.SpecialLinearGroup (Fin N) L) : Matrix (Fin N) (Fin N) L) =
      (1 + (ι π) ^ 2 • M.map ι) * D := by
    have hadj : Matrix.adjugate (A.map ι) * A.map ι = 1 := by
      rw [Matrix.adjugate_mul, hdetA, one_smul]
    have e1 : A.map ι * (D * ((a⁻¹ * b : Matrix.SpecialLinearGroup (Fin N) L) : Matrix (Fin N) (Fin N) L)) =
        B.map ι * D := by
      rw [← Matrix.mul_assoc, ← hA, Matrix.mul_assoc, hc, hB]
    have e2 : A.map ι * ((1 + (ι π) ^ 2 • M.map ι) * D) = B.map ι * D := by
      rw [hMmap, hB', ← Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
        ← Matrix.mul_assoc, Matrix.mul_adjugate, hdetA, one_smul, Matrix.one_mul]
    have := congrArg (fun X => Matrix.adjugate (A.map ι) * X) (e1.trans e2.symm)
    simpa only [← Matrix.mul_assoc, hadj, Matrix.one_mul] using this
  rw [mem_Kg_iff_scaled_entries_integral π hπ s]
  intro i j
  refine ⟨(if i = j then 1 else 0) + M i j * (if (i : ℕ) < r then 1 else π) *
    (if (j : ℕ) < s then 1 else π) * (if (j : ℕ) < r then π else 1) * (if (i : ℕ) < s then π else 1), ?_⟩
  have hij := congrFun (congrFun hDc i) j
  simp only [hDdef, dg, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply, Matrix.one_apply,
    Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at hij
  have hdi : (if (i : ℕ) < r then (π : L) else 1) ≠ 0 := by split_ifs <;> simp [hπ]
  apply mul_left_cancel₀ hdi
  calc (if (i : ℕ) < r then (π : L) else 1) * ((if (i : ℕ) < s then (π : L) else 1) *
        ((a⁻¹ * b : Matrix.SpecialLinearGroup (Fin N) L) : Matrix (Fin N) (Fin N) L) i j)
      = (if (i : ℕ) < s then (π : L) else 1) * ((if (i : ℕ) < r then (π : L) else 1) *
        ((a⁻¹ * b : Matrix.SpecialLinearGroup (Fin N) L) : Matrix (Fin N) (Fin N) L) i j) := by ring
    _ = _ := by
      rw [hij]
      by_cases hij' : i = j
      · subst hij'
        split_ifs <;> push_cast <;> ring
      · simp only [hij', if_false]
        split_ifs <;> push_cast <;> ring

/- English proof (translation)
Establish `hπ0 : (π : L) ≠ 0`. Introduce `h`. Conclude with `hπ.ne_zero (FaithfulSMul.algebraMap_injective _ L (by rw [map_zero]; exact h))`. Use `set I : Ideal (NumberField.RingOfIntegers L) := Ideal.span {π ^ 2} with hIdef`. Establish `hI : I ≠ ⊥`.

Rewrite using `[hIdef, Ne, Ideal.span_singleton_eq_bot]`. Conclude with `pow_ne_zero _ hπ.ne_zero`. Use `haveI : Finite (NumberField.RingOfIntegers L ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI`. Set `φ : Matrix.SpecialLinearGroup (Fin N) L → Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L ⧸ I)` to `fun g i j => if h : ∃ z : NumberField.RingOfIntegers L, (if (i : ℕ) < r then (π : L) else 1) * (g : Matrix (Fin N) (Fin N) L) i j = (z : L) * (if (j : ℕ) < r then (π : L) else 1) then Ideal.Quotient.mk I (Classical.choose h) else 0`. Apply `index_subgroupOf_ne_zero_of_finite_separating_map _ _ φ` to reduce the goal to its premises.

Introduce `a ha b hb hab`. Rewrite `ha`, `hb` using `[mem_Kg_iff_scaled_entries_integral π hπ0 r]`. Establish `key : ∀ s, a⁻¹ * b ∈ Kg L N π s`. Introduce `s`. Use `inv_mul_mem_Kg_of_lifts_congr_pi_sq π hπ0 r s a b (Matrix.of fun i j => Classical.choose (ha i j)) (Matrix.of fun i j => Classical.choose (hb i j)) ?_ ?_ ?_` and prove the remaining obligations.

Use extensionality with `i j`. Simplify `Classical.choose_spec (ha i j)` using `[dg, Matrix.diagonal_mul, Matrix.mul_diagonal]`. Use extensionality with `i j`. Simplify `Classical.choose_spec (hb i j)` using `[dg, Matrix.diagonal_mul, Matrix.mul_diagonal]`. Introduce `i j`.

Use `congrFun (congrFun hab i) j` as an intermediate fact. Simplify using `only [φ, dif_pos (ha i j), dif_pos (hb i j)] at this`. Rewrite `this` using `[Ideal.Quotient.eq, hIdef, Ideal.mem_span_singleton]`. Simplify using `using dvd_sub_comm.mp this`. Conclude with `⟨⟨key 0, key 1⟩, key 2⟩`.
-/
private theorem index_Kg_triple_subgroupOf_Kg_ne_zero {L : Type} [Field L] [NumberField L]
    (π : NumberField.RingOfIntegers L) (hπ : Prime π) (N r : ℕ) :
    ((Kg L N π 0 ⊓ Kg L N π 1 ⊓ Kg L N π 2).subgroupOf (Kg L N π r)).index ≠ 0 := by
  have hπ0 : (π : L) ≠ 0 := by
    intro h
    exact hπ.ne_zero (FaithfulSMul.algebraMap_injective _ L (by rw [map_zero]; exact h))
  set I : Ideal (NumberField.RingOfIntegers L) := Ideal.span {π ^ 2} with hIdef
  have hI : I ≠ ⊥ := by
    rw [hIdef, Ne, Ideal.span_singleton_eq_bot]
    exact pow_ne_zero _ hπ.ne_zero
  haveI : Finite (NumberField.RingOfIntegers L ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  classical
  let φ : Matrix.SpecialLinearGroup (Fin N) L →
      Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers L ⧸ I) :=
    fun g i j => if h : ∃ z : NumberField.RingOfIntegers L,
      (if (i : ℕ) < r then (π : L) else 1) * (g : Matrix (Fin N) (Fin N) L) i j =
        (z : L) * (if (j : ℕ) < r then (π : L) else 1) then
      Ideal.Quotient.mk I (Classical.choose h) else 0
  apply index_subgroupOf_ne_zero_of_finite_separating_map _ _ φ
  intro a ha b hb hab
  rw [mem_Kg_iff_scaled_entries_integral π hπ0 r] at ha hb
  have key : ∀ s, a⁻¹ * b ∈ Kg L N π s := by
    intro s
    refine inv_mul_mem_Kg_of_lifts_congr_pi_sq π hπ0 r s a b (Matrix.of fun i j => Classical.choose (ha i j))
      (Matrix.of fun i j => Classical.choose (hb i j)) ?_ ?_ ?_
    · ext i j
      simpa [dg, Matrix.diagonal_mul, Matrix.mul_diagonal] using Classical.choose_spec (ha i j)
    · ext i j
      simpa [dg, Matrix.diagonal_mul, Matrix.mul_diagonal] using Classical.choose_spec (hb i j)
    · intro i j
      have := congrFun (congrFun hab i) j
      simp only [φ, dif_pos (ha i j), dif_pos (hb i j)] at this
      rw [Ideal.Quotient.eq, hIdef, Ideal.mem_span_singleton] at this
      simpa using dvd_sub_comm.mp this
  exact ⟨⟨key 0, key 1⟩, key 2⟩

/- English proof (translation)
Introduce `L _ _ π hπ hn N hN`. Establish `hπ0 : (π : L) ≠ 0`. Introduce `h`. Apply `hπ.ne_zero` to reduce the goal to its premises. Apply `FaithfulSMul.algebraMap_injective (NumberField.RingOfIntegers L) L` to reduce the goal to its premises.

Simplify using `using h`. Establish `hf0` using `index_Kg_triple_subgroupOf_Kg_ne_zero π hπ N 0`. Establish `h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩` using `by simp [Fin.ext_iff]`. Conclude with `{ fin₀ := hf0 fin₁ := index_Kg_triple_subgroupOf_Kg_ne_zero π hπ N 1 fin₂ := index_Kg_triple_subgroupOf_Kg_ne_zero π hπ N 2 two₀ := twoTr_Kg_of_double_coset_set_of_iff π hπ0 0 _ _ (arith_holds_lemma_3 π hπ ⟨0, by omega⟩ ⟨1, by omega⟩ h01) (fun g γ h => mem_Kg_zero_inf_Kg_one_iff_ …`.
-/
theorem arith_holds : Arith := by
  intro L _ _ π hπ hn N hN
  have hπ0 : (π : L) ≠ 0 := by
    intro h
    apply hπ.ne_zero
    apply FaithfulSMul.algebraMap_injective (NumberField.RingOfIntegers L) L
    simpa using h
  have hf0 := index_Kg_triple_subgroupOf_Kg_ne_zero π hπ N 0
  have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  exact
    { fin₀ := hf0
      fin₁ := index_Kg_triple_subgroupOf_Kg_ne_zero π hπ N 1
      fin₂ := index_Kg_triple_subgroupOf_Kg_ne_zero π hπ N 2
      two₀ := twoTr_Kg_of_double_coset_set_of_iff π hπ0 0 _ _ (arith_holds_lemma_3 π hπ ⟨0, by omega⟩ ⟨1, by omega⟩ h01)
        (fun g γ h => mem_Kg_zero_inf_Kg_one_iff_col_dvd_pi π hπ0 ⟨0, by omega⟩ rfl g γ h)
      two₁ := twoTr_Kg_of_double_coset_set_of_iff π hπ0 1 _ _ (arith_holds_lemma_3 π hπ ⟨1, by omega⟩ ⟨0, by omega⟩ h01.symm)
        (fun g γ h => mem_Kg_one_inf_Kg_two_iff_col_dvd_pi_of_dg_one π hπ0 ⟨0, by omega⟩ ⟨1, by omega⟩ rfl rfl g γ h)
      two₂ := twoTr_Kg_of_double_coset_set_of_iff π hπ0 2 _ _ (arith_holds_lemma_4 π hπ ⟨1, by omega⟩ ⟨0, by omega⟩ h01.symm)
        (fun g γ h => mem_Kg_one_inf_Kg_two_iff_transpose_dvd_pi_of_dg_two π hπ0 ⟨0, by omega⟩ ⟨1, by omega⟩ rfl rfl g γ h)
      big₀₂ := twentyfive_le_index_Kg_triple_in_Kg_zero_two π hπ0 ⟨1, by omega⟩ ⟨0, by omega⟩ rfl rfl hn hf0
      big₀₁ := twentyfive_le_index_Kg_triple_in_Kg_zero_one π hπ0 ⟨2, by omega⟩ ⟨1, by omega⟩ rfl rfl hn hf0 }

end PositivityTheory.KB.SpectralGap

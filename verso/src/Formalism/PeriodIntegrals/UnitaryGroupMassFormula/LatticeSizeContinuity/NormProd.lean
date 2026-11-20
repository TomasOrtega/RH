import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.LatSizeContOfSteps

noncomputable section

open NumberField

namespace PI.UnitaryGroupMassFormula.LSC.NormProd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hc.deg2]; norm_num)`. Establish `hfix : ∀ r : F, starRingAut (algebraMap F E r) = algebraMap F E r` using `fun r => (hc.fixed _).mpr ⟨r, rfl⟩`. Set `σ : E ≃ₐ[F] E` to `AlgEquiv.ofRingEquiv (f := starRingAut) hfix`. Establish `hσ : ∀ a, σ a = star a` using `fun _ => rfl`. Establish `hne : (1 : E ≃ₐ[F] E) ≠ σ`.

Introduce `h`. Establish `hall : ∀ a : E, a ∈ (algebraMap F E).range` using `fun a => by`. Rewrite using `[← hc.fixed, ← hσ, ← h]`. Both sides reduce to the same expression. Establish `hbot : (⊥ : Subalgebra F E) = ⊤`.

Use extensionality with `a`. Simplify `hall a` using `[Algebra.mem_bot]`. Establish `h1` using `Subalgebra.bot_eq_top_iff_finrank_eq_one.mp hbot`. Rewrite `h1` using `[hc.deg2]`. Evaluate the numerical expressions using `at h1`.

Establish `hle : Fintype.card (E ≃ₐ[F] E) ≤ 2`. Rewrite using `[← hc.deg2]`. Conclude with `(Fintype.card_le_of_injective (fun e : E ≃ₐ[F] E => (e : E →ₐ[F] E)) (fun a b h => AlgEquiv.coe_algHom_injective h)).trans AlgHom.card_le`. Establish `hge : 2 ≤ Fintype.card (E ≃ₐ[F] E)`. Rewrite using `[← Finset.card_pair hne]`.

Conclude with `Finset.card_le_univ _`. Establish `hcard : Fintype.card (E ≃ₐ[F] E) = Module.finrank F E`. Rewrite using `[hc.deg2]`. Use linear arithmetic over natural numbers and integers. Use `haveI : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E (by rw [Nat.card_eq_fintype_card]; exact hcard)`.

Establish `huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, σ}` using `(Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by rw [Finset.card_univ, Finset.card_pair hne]; omega)).symm`. Rewrite using `[Algebra.norm_eq_prod_automorphisms, huniv, Finset.prod_pair hne]`. Both sides reduce to the same expression.
-/
theorem algebraMap_norm_eq (hc : Formalism.BasicNotions.CMData F E) (m : E) :
    algebraMap F E (Algebra.norm F m) = m * star m := by
  classical
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hc.deg2]; norm_num)
  have hfix : ∀ r : F, starRingAut (algebraMap F E r) = algebraMap F E r := fun r =>
    (hc.fixed _).mpr ⟨r, rfl⟩
  let σ : E ≃ₐ[F] E := AlgEquiv.ofRingEquiv (f := starRingAut) hfix
  have hσ : ∀ a, σ a = star a := fun _ => rfl
  have hne : (1 : E ≃ₐ[F] E) ≠ σ := by
    intro h
    have hall : ∀ a : E, a ∈ (algebraMap F E).range := fun a => by
      rw [← hc.fixed, ← hσ, ← h]; rfl
    have hbot : (⊥ : Subalgebra F E) = ⊤ := by
      ext a; simpa [Algebra.mem_bot] using hall a
    have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp hbot
    rw [hc.deg2] at h1; norm_num at h1
  have hle : Fintype.card (E ≃ₐ[F] E) ≤ 2 := by
    rw [← hc.deg2]
    exact (Fintype.card_le_of_injective (fun e : E ≃ₐ[F] E => (e : E →ₐ[F] E))
      (fun a b h => AlgEquiv.coe_algHom_injective h)).trans AlgHom.card_le
  have hge : 2 ≤ Fintype.card (E ≃ₐ[F] E) := by
    rw [← Finset.card_pair hne]; exact Finset.card_le_univ _
  have hcard : Fintype.card (E ≃ₐ[F] E) = Module.finrank F E := by
    rw [hc.deg2]; omega
  haveI : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E (by rw [Nat.card_eq_fintype_card]; exact hcard)
  have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, σ} :=
    (Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      (by rw [Finset.card_univ, Finset.card_pair hne]; omega)).symm
  rw [Algebra.norm_eq_prod_automorphisms, huniv, Finset.prod_pair hne]
  rfl

end PI.UnitaryGroupMassFormula.LSC.NormProd

namespace PI.UnitaryGroupMassFormula.LSC

open PI.UnitaryGroupMassFormula.LSC.NormProd

/- English proof (translation)
Introduce `I m`. Use `letI := I.fF`. Use `letI := I.nF`. Use `letI := I.fE`. Use `letI := I.nE`.

Use `letI := I.sE`. Use `letI := I.aFE`. Establish `hc` using `I.cm`. Use `set N := Algebra.norm I.F m with hN`. Establish `hv : ∀ v : InfinitePlace I.F, ‖I.φ v m‖ ^ 2 = v N`.

Introduce `v`. Establish `h1 : I.φ v (m * star m) = v.embedding N`. Rewrite using `[← algebraMap_norm_eq hc m, I.φ_over]`. Rewrite `h1` using `[map_mul, hc.cmUnram.2.1, Complex.mul_conj]`. Rewrite using `[← InfinitePlace.norm_embedding_eq, ← h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]`.

Repeatedly rewrite using `[hv]`. Establish `hmult : ∀ v : InfinitePlace I.F, v.mult = 1` using `fun v => InfinitePlace.mult_isReal ⟨v, hc.totReal.isReal v⟩`. Use `InfinitePlace.prod_eq_abs_norm N` as an intermediate fact. Simplify using `only [hmult, pow_one] at this`. Rewrite using `[this, hN, Algebra.norm_norm, Rat.cast_abs]`.
-/
theorem norm_product_formula : NormProd := by
  intro I m
  letI := I.fF; letI := I.nF; letI := I.fE; letI := I.nE; letI := I.sE; letI := I.aFE
  have hc := I.cm
  set N := Algebra.norm I.F m with hN
  have hv : ∀ v : InfinitePlace I.F, ‖I.φ v m‖ ^ 2 = v N := by
    intro v
    have h1 : I.φ v (m * star m) = v.embedding N := by
      rw [← algebraMap_norm_eq hc m, I.φ_over]
    rw [map_mul, hc.cmUnram.2.1, Complex.mul_conj] at h1
    rw [← InfinitePlace.norm_embedding_eq, ← h1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
  simp_rw [hv]
  have hmult : ∀ v : InfinitePlace I.F, v.mult = 1 := fun v =>
    InfinitePlace.mult_isReal ⟨v, hc.totReal.isReal v⟩
  have := InfinitePlace.prod_eq_abs_norm N
  simp only [hmult, pow_one] at this
  rw [this, hN, Algebra.norm_norm, Rat.cast_abs]

end PI.UnitaryGroupMassFormula.LSC

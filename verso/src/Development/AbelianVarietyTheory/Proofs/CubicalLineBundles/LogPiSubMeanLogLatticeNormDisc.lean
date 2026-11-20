import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogCovolumeEqMeanClassGroup

open NumberField
open scoped nonZeroDivisors UpperHalfPlane

namespace GlobalTheory

/- English proof (translation)
Take `⟨𝔞, ω, h𝔞, hω⟩` from `hτ`. Use `set J := FractionalIdeal.mk0 K 𝔟 with hJ`. Establish `hcl : ClassGroup.mk K (𝔞⁻¹ * J) = 1`. Rewrite using `[map_mul, map_inv, h𝔞, hJ, ClassGroup.mk_mk0, inv_mul_cancel]`. Take `⟨x₀, hx₀⟩` from `(ClassGroup.mk_eq_one_iff.1 hcl).principal`.

Establish `hJx : ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀ * (𝔞 : FractionalIdeal (𝓞 K)⁰ K)`. Establish `h1 : ((𝔞⁻¹ * J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀`. Apply `FractionalIdeal.coeToSubmodule_injective` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[FractionalIdeal.coe_spanSingleton]`.

Conclude with `hx₀`. Establish `h2 : J = 𝔞 * (𝔞⁻¹ * J)` using `(mul_inv_cancel_left 𝔞 J).symm`. Use `conv_lhs => rw [h2]`. Rewrite using `[Units.val_mul, h1, mul_comm]`. Establish `hmemJ : ∀ y : K, (∃ b ∈ (𝔟 : Ideal (𝓞 K)), (b : K) = y) ↔ ∃ y' ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K), y = x₀ * y'`.

Introduce `y`. Rewrite using `[← FractionalIdeal.mem_singleton_mul, ← hJx, hJ, FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal]`. Establish `hmem : ∀ z, z ∈ P.lattice ↔ ∃ m n : ℤ, σ x₀ * ω * (m * (τ : ℂ) + n) = z`. Introduce `z`. Rewrite using `[hP]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, rfl⟩`. Take `⟨y', hy', hby⟩` from `(hmemJ _).1 ⟨b, hb, rfl⟩`. Take `⟨m, n, hmn⟩` from `(hω (σ y')).1 ⟨y', hy', rfl⟩`. Conclude with `⟨m, n, by rw [hby, map_mul, ← hmn]; ring⟩`.

Introduce and unpack `⟨m, n, rfl⟩`. Take `⟨y', hy', hy'eq⟩` from `(hω (ω * (m * (τ : ℂ) + n))).2 ⟨m, n, rfl⟩`. Take `⟨b, hb, hbeq⟩` from `(hmemJ (x₀ * y')).2 ⟨y', hy', rfl⟩`. Conclude with `⟨b, hb, by rw [hbeq, map_mul, hy'eq]; ring⟩`. Use `⟨σ x₀ * ω, ?_, hmem⟩` and prove the remaining obligations.

Introduce `ha`. Take `⟨m, n, hmn⟩` from `(hmem P.ω₁).1 P.ω₁_mem_lattice`. Rewrite `hmn` using `[ha, zero_mul]`. Conclude with `P.indep.ne_zero 0 (by simpa using hmn.symm)`.
-/
theorem IsIdealClassPoint.exists_lattice_eq {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ}
    {𝔟 : (Ideal (𝓞 K))⁰} {τ : ℍ} (hτ : IsIdealClassPoint σ (ClassGroup.mk0 𝔟) τ)
    {P : PeriodPair} (hP : ∀ z, z ∈ P.lattice ↔ ∃ a ∈ (𝔟 : Ideal (𝓞 K)), z = σ (a : K)) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ x, x ∈ P.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x := by
  classical
  obtain ⟨𝔞, ω, h𝔞, hω⟩ := hτ
  set J := FractionalIdeal.mk0 K 𝔟 with hJ
  have hcl : ClassGroup.mk K (𝔞⁻¹ * J) = 1 := by
    rw [map_mul, map_inv, h𝔞, hJ, ClassGroup.mk_mk0, inv_mul_cancel]
  obtain ⟨x₀, hx₀⟩ := (ClassGroup.mk_eq_one_iff.1 hcl).principal

  have hJx : ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀ * (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
    have h1 : ((𝔞⁻¹ * J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀ := by
      apply FractionalIdeal.coeToSubmodule_injective
      dsimp only
      rw [FractionalIdeal.coe_spanSingleton]
      exact hx₀
    have h2 : J = 𝔞 * (𝔞⁻¹ * J) := (mul_inv_cancel_left 𝔞 J).symm
    conv_lhs => rw [h2]
    rw [Units.val_mul, h1, mul_comm]
  have hmemJ : ∀ y : K, (∃ b ∈ (𝔟 : Ideal (𝓞 K)), (b : K) = y) ↔
      ∃ y' ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K), y = x₀ * y' := by
    intro y
    rw [← FractionalIdeal.mem_singleton_mul, ← hJx, hJ, FractionalIdeal.coe_mk0,
      FractionalIdeal.mem_coeIdeal]
  have hmem : ∀ z, z ∈ P.lattice ↔ ∃ m n : ℤ, σ x₀ * ω * (m * (τ : ℂ) + n) = z := by
    intro z
    rw [hP]
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨y', hy', hby⟩ := (hmemJ _).1 ⟨b, hb, rfl⟩
      obtain ⟨m, n, hmn⟩ := (hω (σ y')).1 ⟨y', hy', rfl⟩
      exact ⟨m, n, by rw [hby, map_mul, ← hmn]; ring⟩
    · rintro ⟨m, n, rfl⟩
      obtain ⟨y', hy', hy'eq⟩ := (hω (ω * (m * (τ : ℂ) + n))).2 ⟨m, n, rfl⟩
      obtain ⟨b, hb, hbeq⟩ := (hmemJ (x₀ * y')).2 ⟨y', hy', rfl⟩
      exact ⟨b, hb, by rw [hbeq, map_mul, hy'eq]; ring⟩
  refine ⟨σ x₀ * ω, ?_, hmem⟩
  intro ha
  obtain ⟨m, n, hmn⟩ := (hmem P.ω₁).1 P.ω₁_mem_lattice
  rw [ha, zero_mul] at hmn
  exact P.indep.ne_zero 0 (by simpa using hmn.symm)

/- English proof (translation)
Introduce `K _ _ hK σ₀ h₀ 𝔟 Lc h𝔟 hL σ τ hτ`. Establish `key : ∀ C, Real.log Real.pi - Real.log (|((Lc C).ω₁ * starRingEnd ℂ (Lc C).ω₂).im| ^ 6 * ‖(Lc C).g₂ ^ 3 - 27 * (Lc C).g₃ ^ 2‖) / 6 = -Real.log (4 * Real.pi * (τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4)`. Introduce `C`. Establish `hτC : IsIdealClassPoint σ (ClassGroup.mk0 (𝔟 C)) (τ C)`. Rewrite using `[h𝔟 C]`.

Conclude with `hτ C`. Break down `embedding_eq_or_eq_conjugate hK h₀ σ with rfl | rfl` into its components or cases. Take `⟨a, ha, h⟩` from `hτC.exists_lattice_eq (hL C)`. Conclude with `log_pi_sub_log_latticeNormDisc ha h`. Establish `hP : ∀ z, z ∈ (conjPeriods (Lc C)).lattice ↔ ∃ a ∈ (𝔟 C : Ideal (𝓞 K)), z = ComplexEmbedding.conjugate σ₀ (a : K)`.

Introduce `z`. Rewrite using `[mem_conjPeriods_lattice, hL]`. Use `exists_congr fun a => and_congr_right fun _ => ?_` and prove the remaining obligations. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Rewrite using `[← h, Complex.conj_conj]`. Introduce `h`. Rewrite using `[h, Complex.conj_conj]`. Take `⟨a, ha, h⟩` from `hτC.exists_lattice_eq hP`.

Establish `e` using `log_pi_sub_log_latticeNormDisc ha h`. Rewrite `e` using `[← latticeNormDisc_eq, latticeNormDisc_conjPeriods, latticeNormDisc_eq]`. Conclude with `e`. Establish `hh : (Fintype.card (ClassGroup (𝓞 K)) : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Repeatedly rewrite using `[← key]`.

Rewrite using `[Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_div]`. Simplify using `only [NumberField.classNumber]`. Clear the denominators using the available nonvanishing facts.
-/
theorem log_pi_sub_mean_log_latticeNormDisc :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (σ₀ : K →+* ℂ), ¬ ComplexEmbedding.IsReal σ₀ → ∀ (𝔟 : ClassGroup (𝓞 K) → nonZeroDivisors (Ideal (𝓞 K))), ∀ (Lc : ClassGroup (𝓞 K) → PeriodPair), (∀ C, ClassGroup.mk0 (𝔟 C) = C) → (∀ C z, z ∈ (Lc C).lattice ↔ ∃ a ∈ (𝔟 C : Ideal (𝓞 K)), z = σ₀ (a : K)) → ∀ (σ : K →+* ℂ) (τ : ClassGroup (𝓞 K) → ℍ), (∀ C, IsIdealClassPoint σ C (τ C)) → Real.log Real.pi - (∑ C, Real.log (|((Lc C).ω₁ * starRingEnd ℂ (Lc C).ω₂).im| ^ 6 * ‖(Lc C).g₂ ^ 3 - 27 * (Lc C).g₃ ^ 2‖)) / (6 * Fintype.card (ClassGroup (𝓞 K))) = (∑ C, -Real.log (4 * Real.pi * (τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4)) / classNumber K := by
  intro K _ _ hK σ₀ h₀ 𝔟 Lc h𝔟 hL σ τ hτ
  classical

  have key : ∀ C, Real.log Real.pi - Real.log (|((Lc C).ω₁ * starRingEnd ℂ (Lc C).ω₂).im| ^ 6 *
      ‖(Lc C).g₂ ^ 3 - 27 * (Lc C).g₃ ^ 2‖) / 6 =
      -Real.log (4 * Real.pi * (τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4) := by
    intro C
    have hτC : IsIdealClassPoint σ (ClassGroup.mk0 (𝔟 C)) (τ C) := by
      rw [h𝔟 C]
      exact hτ C
    rcases embedding_eq_or_eq_conjugate hK h₀ σ with rfl | rfl
    · obtain ⟨a, ha, h⟩ := hτC.exists_lattice_eq (hL C)
      exact log_pi_sub_log_latticeNormDisc ha h
    · have hP : ∀ z, z ∈ (conjPeriods (Lc C)).lattice ↔
          ∃ a ∈ (𝔟 C : Ideal (𝓞 K)), z = ComplexEmbedding.conjugate σ₀ (a : K) := by
        intro z
        rw [mem_conjPeriods_lattice, hL]
        refine exists_congr fun a => and_congr_right fun _ => ?_
        rw [ComplexEmbedding.conjugate_coe_eq]
        constructor
        · intro h
          rw [← h, Complex.conj_conj]
        · intro h
          rw [h, Complex.conj_conj]
      obtain ⟨a, ha, h⟩ := hτC.exists_lattice_eq hP
      have e := log_pi_sub_log_latticeNormDisc ha h
      rw [← latticeNormDisc_eq, latticeNormDisc_conjPeriods, latticeNormDisc_eq] at e
      exact e
  have hh : (Fintype.card (ClassGroup (𝓞 K)) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp_rw [← key]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_div]
  simp only [NumberField.classNumber]
  field_simp

end GlobalTheory

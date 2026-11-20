import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitLatticeLevelTraceDenominatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumRealEmbeddingsEqTraceTotallyRealStatement

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
/- English proof (translation)
Take `⟨h1, h2⟩` from `h`. Establish `mem : ∀ v : Fin 2 → F, v ∈ _root_.GlobalTheory.HilbFam.split A B x ↔ v 0 ∈ (B : FractionalIdeal (𝓞 F)⁰ F) ∧ v 1 - v 0 * x ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM A` using `fun v ↦ Iff.rfl`. Establish `std : ∀ v : Fin 2 → F, v ∈ _root_.GlobalTheory.HilbFam.stdLat F ↔ ∀ i, v i ∈ (1 : Submodule (𝓞 F) F)`. Introduce `v`. Simplify using `[_root_.GlobalTheory.HilbFam.stdLat, Submodule.mem_pi]`.

Establish `one_mem : (1 : F) ∈ (1 : Submodule (𝓞 F) F)` using `Submodule.mem_one.2 ⟨1, map_one _⟩`. Establish `zero_mem' : (0 : F) ∈ (1 : Submodule (𝓞 F) F)` using `Submodule.zero_mem _`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `b hb`. Establish `hv : ![b, b * x] ∈ _root_.GlobalTheory.HilbFam.split A B x` using `(mem _).2 ⟨by simpa using hb, by`.

Simplify using `using FractionalIdeal.mem_coe.1 (Submodule.zero_mem _)⟩`. Use `((std _).1 (h2 hv)) 0` as an intermediate fact. Simplify using `only [Matrix.cons_val_zero] at this`. Take `⟨y, hy⟩` from `Submodule.mem_one.1 this`. Conclude with `(FractionalIdeal.mem_one_iff _).2 ⟨y, hy⟩`.

Apply the tactic sequence `have hv := h1 ![0, 1] ((std _).2 (by intro i; fin_cases i <;> simpa))`. Use `((mem _).1 hv).2` as an intermediate fact. Simplify `this` using `[Algebra.smul_def]`. Apply the tactic sequence `have hv := h1 ![1, 0] ((std _).2 (by intro i; fin_cases i <;> simpa))`. Use `FractionalIdeal.mem_coe.1 (Submodule.neg_mem _ (FractionalIdeal.mem_coe.2 ((mem _).1 hv).2))` as an intermediate fact.

Simplify `this` using `[Algebra.smul_def]`.
-/
private lemma le_one_and_mem_latM_of_hasLevel {F : Type} [Field F] [NumberField F] {N : ℕ}
    {A B : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} {x : F}
    (h : _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.split A B x)) :
    ((B : FractionalIdeal (𝓞 F)⁰ F) ≤ 1) ∧ (N : F) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM A ∧
      (N : F) * x ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM A := by
  obtain ⟨h1, h2⟩ := h
  have mem : ∀ v : Fin 2 → F, v ∈ _root_.GlobalTheory.HilbFam.split A B x ↔
      v 0 ∈ (B : FractionalIdeal (𝓞 F)⁰ F) ∧ v 1 - v 0 * x ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM A :=
    fun v ↦ Iff.rfl
  have std : ∀ v : Fin 2 → F, v ∈ _root_.GlobalTheory.HilbFam.stdLat F ↔
      ∀ i, v i ∈ (1 : Submodule (𝓞 F) F) := by
    intro v; simp [_root_.GlobalTheory.HilbFam.stdLat, Submodule.mem_pi]
  have one_mem : (1 : F) ∈ (1 : Submodule (𝓞 F) F) := Submodule.mem_one.2 ⟨1, map_one _⟩
  have zero_mem' : (0 : F) ∈ (1 : Submodule (𝓞 F) F) := Submodule.zero_mem _
  refine ⟨?_, ?_, ?_⟩
  · intro b hb
    have hv : ![b, b * x] ∈ _root_.GlobalTheory.HilbFam.split A B x :=
      (mem _).2 ⟨by simpa using hb, by
        simpa using FractionalIdeal.mem_coe.1 (Submodule.zero_mem _)⟩
    have := ((std _).1 (h2 hv)) 0
    simp only [Matrix.cons_val_zero] at this
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 this
    exact (FractionalIdeal.mem_one_iff _).2 ⟨y, hy⟩
  · have hv := h1 ![0, 1] ((std _).2 (by intro i; fin_cases i <;> simpa))
    have := ((mem _).1 hv).2
    simpa [Algebra.smul_def] using this
  · have hv := h1 ![1, 0] ((std _).2 (by intro i; fin_cases i <;> simpa))
    have := FractionalIdeal.mem_coe.1
      (Submodule.neg_mem _ (FractionalIdeal.mem_coe.2 ((mem _).1 hv).2))
    simpa [Algebra.smul_def] using this

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
/- English proof (translation)
Take `⟨-, -, hsupp, -⟩` from `ha`. Take `⟨hmem, hpos⟩` from `hsupp ξ hξ0 hξ`. Use `⟨?_, hpos⟩` and prove the remaining obligations. Establish `hB` using `(le_one_and_mem_latM_of_hasLevel hN).1`. Establish `hle : ((A * B : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) : FractionalIdeal (𝓞 F)⁰ F) ≤ A`.

Rewrite using `[Units.val_mul]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hle hmem`.
-/
private lemma mem_and_totally_pos_of_coeff_ne_zero {F : Type} [Field F] [NumberField F]
    {k N : ℕ} {A B : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} {a₀ : ℂ} {a : F → ℂ} {x : F}
    (ha : _root_.GlobalTheory.HilbFam.IsCoef k A B a₀ a)
    (hN : _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.split A B x)) {ξ : F}
    (hξ0 : ξ ≠ 0) (hξ : a ξ ≠ 0) :
    ξ ∈ (A : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, 0 < i ξ := by
  obtain ⟨-, -, hsupp, -⟩ := ha
  obtain ⟨hmem, hpos⟩ := hsupp ξ hξ0 hξ
  refine ⟨?_, hpos⟩
  have hB := (le_one_and_mem_latM_of_hasLevel hN).1
  have hle : ((A * B : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) : FractionalIdeal (𝓞 F)⁰ F) ≤ A := by
    rw [Units.val_mul]
    calc (A : FractionalIdeal (𝓞 F)⁰ F) * B ≤ A * 1 := by gcongr
      _ = A := mul_one _
  exact hle hmem

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
/- English proof (translation)
Apply `Complex.ofReal_injective` to reduce the goal to its premises. Use `push_cast`. Conclude with `_root_.GlobalTheory.HilbFam.sum_realEmb_eq_trace F y`.
-/
private lemma sum_realEmbeddings_eq_trace {F : Type} [Field F] [NumberField F]
    [IsTotallyReal F] (y : F) :
    ∑ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, i y = ((Algebra.trace ℚ F y : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  exact _root_.GlobalTheory.HilbFam.sum_realEmb_eq_trace F y

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
/- English proof (translation)
Rewrite `hy` using `[_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual, FractionalIdeal.mem_dual A.ne_zero]`. Take `⟨c, hc⟩` from `hy ξ hξ`. Conclude with `⟨c, by simpa [Algebra.traceForm_apply] using hc.symm⟩`.
-/
private lemma trace_mul_int_of_mem_latM {F : Type} [Field F] [NumberField F]
    {A : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} {y ξ : F} (hy : y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM A)
    (hξ : ξ ∈ (A : FractionalIdeal (𝓞 F)⁰ F)) : ∃ c : ℤ, Algebra.trace ℚ F (y * ξ) = c := by
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual, FractionalIdeal.mem_dual A.ne_zero] at hy
  obtain ⟨c, hc⟩ := hy ξ hξ
  exact ⟨c, by simpa [Algebra.traceForm_apply] using hc.symm⟩

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
/- English proof (translation)
Establish `hNF : (N : F) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞` using `(le_one_and_mem_latM_of_hasLevel hlev).2.1`. Establish `hpos : ∀ ξ, a ξ ≠ 0 → ξ ≠ 0 → ξ ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, 0 < i ξ` using `fun ξ hξ hξ0 ↦ mem_and_totally_pos_of_coeff_ne_zero ha hlev hξ0 hξ`. Establish `hbound : ∀ ξ : F, (∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, 0 < i ξ) → ∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, i ξ ≤ ((Algebra.trace ℚ F ξ : ℚ) : ℝ)`. Introduce `ξ hξ i`. Rewrite using `[← sum_realEmbeddings_eq_trace]`.

Conclude with `Finset.single_le_sum (fun j _ ↦ (hξ j).le) (Finset.mem_univ i)`. Establish `htr_nonneg : ∀ ξ : F, (∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, 0 < i ξ) → 0 ≤ Algebra.trace ℚ F ξ`. Introduce `ξ hξ`. Establish `: (0 : ℝ) ≤ ((Algebra.trace ℚ F ξ : ℚ) : ℝ)`. Rewrite using `[← sum_realEmbeddings_eq_trace]`.

Conclude with `Finset.sum_nonneg fun j _ ↦ (hξ j).le`. Conclude with `this` after adjusting the coercions. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `ξ hξ`. Distinguish the cases in `hξ0 : ξ = 0`.

Conclude with `⟨0, by simp [hξ0]⟩`. Take `⟨hmem, hξpos⟩` from `hpos ξ hξ hξ0`. Take `⟨c, hc⟩` from `trace_mul_int_of_mem_latM hNF hmem`. Establish `hc' : (N : ℚ) * Algebra.trace ℚ F ξ = c`. Rewrite using `[← hc, ← nsmul_eq_mul, ← map_nsmul, nsmul_eq_mul]`.

Establish `hc0 : 0 ≤ c`. Establish `: (0 : ℚ) ≤ c` using `hc' ▸ mul_nonneg (Nat.cast_nonneg _) (htr_nonneg ξ hξpos)`. Conclude with `this` after adjusting the coercions. Conclude with `⟨c.toNat, by rw [hc']; exact_mod_cast (Int.toNat_of_nonneg hc0).symm⟩`. Introduce `n`.

Take `⟨d, hd0, hd⟩` from `(𝔞 : FractionalIdeal (𝓞 F)⁰ F).isFractional`. Use `set D : F := algebraMap (𝓞 F) F d with hD`. Establish `hD0 : D ≠ 0`. Rewrite using `[hD]`. Conclude with `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd0`.

Use `set M : ℝ := (∑ φ : F →+* ℂ, ‖φ D‖) * ((n : ℝ) / N) with hM`. Establish `hfin` using `NumberField.Embeddings.finite_of_norm_le F ℂ M`. Use `(hfin.image fun z ↦ z / D).subset ?_` and prove the remaining obligations. Introduce and unpack `ξ ⟨hξ, htr⟩`. Use `⟨D * ξ, ⟨?_, ?_⟩, by field_simp⟩` and prove the remaining obligations.

Distinguish the cases in `hξ0 : ξ = 0`. Simplify `isIntegral_zero` using `[hξ0]`. Take `⟨r, hr⟩` from `hd ξ (hpos ξ hξ hξ0).1`. Establish `hDξ : D * ξ = algebraMap (𝓞 F) F r` using `by rw [hr, Algebra.smul_def]`. Rewrite using `[hDξ]`.

Conclude with `NumberField.RingOfIntegers.isIntegral_coe r`. Introduce `φ`. Establish `hMnn : 0 ≤ M` using `by rw [hM]; positivity`. Rewrite using `[map_mul, norm_mul]`. Distinguish the cases in `hξ0 : ξ = 0`.

Simplify `hMnn` using `[hξ0]`. Establish `hξpos` using `(hpos ξ hξ hξ0).2`. Establish `hφ` using `IsTotallyReal.complexEmbedding_isReal φ`. Establish `htrq : Algebra.trace ℚ F ξ = n / N`. Rewrite using `[eq_div_iff (by exact_mod_cast hN.ne')]`.

Rewrite using `[mul_comm]`. Conclude with `htr`. Establish `hφξ : ‖φ ξ‖ ≤ (n : ℝ) / N`. Rewrite using `[← ComplexEmbedding.IsReal.coe_embedding_apply hφ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hξpos _)]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hφD : ‖φ D‖ ≤ ∑ ψ : F →+* ℂ, ‖ψ D‖` using `Finset.single_le_sum (fun ψ _ ↦ norm_nonneg (ψ D)) (Finset.mem_univ φ)`. Rewrite using `[hM]`. Conclude with `mul_le_mul hφD hφξ (norm_nonneg _) (Finset.sum_nonneg fun ψ _ ↦ norm_nonneg _)`.
-/
private lemma coeff_support_trace_natCast_and_finite {F : Type} [Field F] [NumberField F]
    [IsTotallyReal F] {k : ℕ} {𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} {a₀ : ℂ} {a : F → ℂ} {x : F}
    {N : ℕ} (hN : 0 < N) (ha : _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a)
    (hlev : _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x)) :
    (∀ ξ, a ξ ≠ 0 → ∃ n : ℕ, (N : ℚ) * Algebra.trace ℚ F ξ = n) ∧
      ∀ n : ℕ, {ξ : F | a ξ ≠ 0 ∧ (N : ℚ) * Algebra.trace ℚ F ξ = n}.Finite := by
  have hNF : (N : F) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 := (le_one_and_mem_latM_of_hasLevel hlev).2.1
  have hpos : ∀ ξ, a ξ ≠ 0 → ξ ≠ 0 → ξ ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ∧
      ∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, 0 < i ξ := fun ξ hξ hξ0 ↦
    mem_and_totally_pos_of_coeff_ne_zero ha hlev hξ0 hξ

  have hbound : ∀ ξ : F, (∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, 0 < i ξ) →
      ∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, i ξ ≤ ((Algebra.trace ℚ F ξ : ℚ) : ℝ) := by
    intro ξ hξ i
    rw [← sum_realEmbeddings_eq_trace]
    exact Finset.single_le_sum (fun j _ ↦ (hξ j).le) (Finset.mem_univ i)
  have htr_nonneg : ∀ ξ : F, (∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, 0 < i ξ) →
      0 ≤ Algebra.trace ℚ F ξ := by
    intro ξ hξ
    have : (0 : ℝ) ≤ ((Algebra.trace ℚ F ξ : ℚ) : ℝ) := by
      rw [← sum_realEmbeddings_eq_trace]
      exact Finset.sum_nonneg fun j _ ↦ (hξ j).le
    exact_mod_cast this
  refine ⟨?_, ?_⟩
  · intro ξ hξ
    by_cases hξ0 : ξ = 0
    · exact ⟨0, by simp [hξ0]⟩
    obtain ⟨hmem, hξpos⟩ := hpos ξ hξ hξ0
    obtain ⟨c, hc⟩ := trace_mul_int_of_mem_latM hNF hmem
    have hc' : (N : ℚ) * Algebra.trace ℚ F ξ = c := by
      rw [← hc, ← nsmul_eq_mul, ← map_nsmul, nsmul_eq_mul]
    have hc0 : 0 ≤ c := by
      have : (0 : ℚ) ≤ c := hc' ▸ mul_nonneg (Nat.cast_nonneg _) (htr_nonneg ξ hξpos)
      exact_mod_cast this
    exact ⟨c.toNat, by rw [hc']; exact_mod_cast (Int.toNat_of_nonneg hc0).symm⟩
  · intro n
    obtain ⟨d, hd0, hd⟩ := (𝔞 : FractionalIdeal (𝓞 F)⁰ F).isFractional
    set D : F := algebraMap (𝓞 F) F d with hD
    have hD0 : D ≠ 0 := by
      rw [hD]
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd0
    set M : ℝ := (∑ φ : F →+* ℂ, ‖φ D‖) * ((n : ℝ) / N) with hM
    have hfin := NumberField.Embeddings.finite_of_norm_le F ℂ M
    refine (hfin.image fun z ↦ z / D).subset ?_
    rintro ξ ⟨hξ, htr⟩
    refine ⟨D * ξ, ⟨?_, ?_⟩, by field_simp⟩
    · by_cases hξ0 : ξ = 0
      · simpa [hξ0] using isIntegral_zero
      obtain ⟨r, hr⟩ := hd ξ (hpos ξ hξ hξ0).1
      have hDξ : D * ξ = algebraMap (𝓞 F) F r := by rw [hr, Algebra.smul_def]
      rw [hDξ]
      exact NumberField.RingOfIntegers.isIntegral_coe r
    · intro φ
      have hMnn : 0 ≤ M := by rw [hM]; positivity
      rw [map_mul, norm_mul]
      by_cases hξ0 : ξ = 0
      · simpa [hξ0] using hMnn
      have hξpos := (hpos ξ hξ hξ0).2
      have hφ := IsTotallyReal.complexEmbedding_isReal φ
      have htrq : Algebra.trace ℚ F ξ = n / N := by
        rw [eq_div_iff (by exact_mod_cast hN.ne')]
        rw [mul_comm]; exact htr
      have hφξ : ‖φ ξ‖ ≤ (n : ℝ) / N := by
        rw [← ComplexEmbedding.IsReal.coe_embedding_apply hφ, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (hξpos _)]
        calc ComplexEmbedding.IsReal.embedding hφ ξ ≤ ((Algebra.trace ℚ F ξ : ℚ) : ℝ) :=
              hbound ξ hξpos _
          _ = (n : ℝ) / N := by rw [htrq]; push_cast; ring
      have hφD : ‖φ D‖ ≤ ∑ ψ : F →+* ℂ, ‖ψ D‖ :=
        Finset.single_le_sum (fun ψ _ ↦ norm_nonneg (ψ D)) (Finset.mem_univ φ)
      rw [hM]
      exact mul_le_mul hφD hφξ (norm_nonneg _) (Finset.sum_nonneg fun ψ _ ↦ norm_nonneg _)

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in

/- English proof (translation)
The claim follows from `fun _ _ _ _ _ _ _ _ _ _ _ hN ha hlev ↦ coeff_support_trace_natCast_and_finite hN ha hlev`.
-/
theorem _root_.GlobalTheory.HilbFam.coef_support_trace : ∀ (F : Type) [Field F] [NumberField F]
    [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F)
    (N : ℕ), 0 < N → _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a →
    _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) →
    (∀ ξ, a ξ ≠ 0 → ∃ n : ℕ, (N : ℚ) * Algebra.trace ℚ F ξ = n) ∧
      ∀ n : ℕ, {ξ : F | a ξ ≠ 0 ∧ (N : ℚ) * Algebra.trace ℚ F ξ = n}.Finite :=
  fun _ _ _ _ _ _ _ _ _ _ _ hN ha hlev ↦ coeff_support_trace_natCast_and_finite hN ha hlev

end GlobalTheory.HilbFam

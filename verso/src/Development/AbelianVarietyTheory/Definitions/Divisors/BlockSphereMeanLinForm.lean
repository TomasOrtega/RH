import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsHomogeneousOfEquivariant
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality

set_option autoImplicit false
noncomputable section
open MvPolynomial NumberField
namespace GlobalTheory.ChowHt.Model

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `s hs b`. Rewrite `hs` using `[support_X, Finset.mem_singleton]`. Substitute `hs` using the available equality. Use `fin_cases b`.

Simplify using `[Fin.sum_univ_two, Finsupp.single_apply]`. Rewrite using `[map_X]`. Conclude with `X_prime.irreducible`. Introduce `u`. Rewrite using `[aeval_X]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨![1, 0], by simp, ?_, ?_⟩` and prove the remaining obligations. Introduce `g hg`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.1 hg`.

Simplify using the standard rewrite rules. Introduce `i fin_cases i`. Simplify `h` using `[Fin.sum_univ_two]`. Introduce and unpack `⟨y, hy, hI, hu⟩`. Establish `h1 : y 1 = 0` using `by simpa using hI (X 1) (Ideal.subset_span rfl)`.

Establish `h0 : y 0 ≠ 0`. Apply the tactic sequence `intro h0; apply hy; funext j; fin_cases j <;> simp [h0, h1]`. Use `hu 0` as an intermediate fact. Simplify using `[Fin.sum_univ_two, h1, h0] at this`. Conclude with `this`.
-/
theorem isChowForm_point (k : Type) [Field k] :
    IsChowForm (Ideal.span {(X 1 : MvPolynomial (Fin 2) k)}) 0 1 (X (0, 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs b
    rw [support_X, Finset.mem_singleton] at hs
    subst hs
    fin_cases b
    simp [Fin.sum_univ_two, Finsupp.single_apply]
  · rw [map_X]; exact X_prime.irreducible
  · intro u
    rw [aeval_X]
    constructor
    · intro h
      refine ⟨![1, 0], by simp, ?_, ?_⟩
      · intro g hg
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hg
        simp
      · intro i
        fin_cases i
        simpa [Fin.sum_univ_two] using h
    · rintro ⟨y, hy, hI, hu⟩
      have h1 : y 1 = 0 := by simpa using hI (X 1) (Ideal.subset_span rfl)
      have h0 : y 0 ≠ 0 := by
        intro h0; apply hy; funext j; fin_cases j <;> simp [h0, h1]
      have := hu 0
      simp [Fin.sum_univ_two, h1, h0] at this
      exact this

def linForm {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) : MvPolynomial (Fin 1 × Fin N) R :=
  ∑ j, C (c j) * X (0, j)

/- English proof (translation)
Simplify using `only [linSubst, linForm, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.
-/
theorem linSubst_linForm {R : Type} [CommRing R] {N n : ℕ} (M : Matrix (Fin N) (Fin n) R)
    (c : Fin N → R) : linSubst M (linForm c) = linForm (fun k => ∑ j, M j k * c j) := by
  simp only [linSubst, linForm, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

set_option autoImplicit false in
open MvPolynomial NumberField in
/- English proof (translation)
Simplify using `only [_root_.GlobalTheory.ChowHt.Model.linForm, coeff_sum, coeff_C_mul, coeff_X']`. Establish `key : ∀ j : Fin N, (Finsupp.single ((0 : Fin 1), j) 1 = Finsupp.single ((0 : Fin 1), k) 1) ↔ j = k`. Introduce `j`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `Finsupp.single_left_injective (one_ne_zero) h` as an intermediate fact. Simplify using `using this`. Introduce and unpack `rfl`. Both sides reduce to the same expression. Simplify using `[key]`.
-/
theorem _root_.GlobalTheory.ChowHt.Model.coeff_linForm {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R)
    (k : Fin N) :
    (_root_.GlobalTheory.ChowHt.Model.linForm c).coeff (Finsupp.single (0, k) 1) = c k := by
  classical
  simp only [_root_.GlobalTheory.ChowHt.Model.linForm, coeff_sum, coeff_C_mul, coeff_X']
  have key : ∀ j : Fin N,
      (Finsupp.single ((0 : Fin 1), j) 1 = Finsupp.single ((0 : Fin 1), k) 1) ↔ j = k := by
    intro j
    constructor
    · intro h
      have := Finsupp.single_left_injective (one_ne_zero) h
      simpa using this
    · rintro rfl; rfl
  simp [key]

/- English proof (translation)
Establish `hb : BddAbove (Set.range fun k => v (c k))` using `(Set.finite_range _).bddAbove`. Establish `hn : 0 ≤ ⨆ k, v (c k)` using `Real.iSup_nonneg fun k => apply_nonneg _ _`. Unfold `ReciprocityTheory.MultiplicativeHeights.gaussAbs`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← Real.coe_toNNReal _ hn, NNReal.coe_le_coe]`.

Use `Finset.sup_le fun s hs => Real.toNNReal_le_toNNReal ?_` and prove the remaining obligations. Distinguish the cases in `h : ∃ k, s = Finsupp.single (0, k) 1`. Take `⟨k, rfl⟩` from `h`. Rewrite using `[coeff_linForm]`. Conclude with `le_ciSup hb k`.

It suffices to derive a contradiction. Rewrite `hs` using `[mem_support_iff]`. Apply `hs` to reduce the goal to its premises. Simplify using `only [linForm, coeff_sum, coeff_C_mul, coeff_X']`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[if_neg, mul_zero]`. Introduce `h'`. Conclude with `h ⟨j, h'.symm⟩`. Use `Real.iSup_le (fun k => ?_) (NNReal.coe_nonneg _)` and prove the remaining obligations. Distinguish the cases in `h : c k = 0`.

Simplify using `[h]`. Establish `hm : Finsupp.single ((0 : Fin 1), k) 1 ∈ (linForm c).support`. Rewrite using `[mem_support_iff, coeff_linForm]`. Conclude with `h`. Use `Finset.le_sup (f := fun s => (v ((linForm c).coeff s)).toNNReal) hm` as an intermediate fact.

Simplify using `only [coeff_linForm] at this`. Establish `h2` using `NNReal.coe_le_coe.2 this`. Rewrite `h2` using `[Real.coe_toNNReal _ (apply_nonneg _ _)]`. Then use the resulting hypothesis.
-/
theorem gaussAbs_linForm {F : Type} [Field F] [NumberField F] {N : ℕ} (v : FinitePlace F)
    (c : Fin N → F) : ReciprocityTheory.MultiplicativeHeights.gaussAbs v (linForm c) = ⨆ k, v (c k) := by
  classical
  have hb : BddAbove (Set.range fun k => v (c k)) := (Set.finite_range _).bddAbove
  have hn : 0 ≤ ⨆ k, v (c k) := Real.iSup_nonneg fun k => apply_nonneg _ _
  unfold ReciprocityTheory.MultiplicativeHeights.gaussAbs
  apply le_antisymm
  · rw [← Real.coe_toNNReal _ hn, NNReal.coe_le_coe]
    refine Finset.sup_le fun s hs => Real.toNNReal_le_toNNReal ?_
    by_cases h : ∃ k, s = Finsupp.single (0, k) 1
    · obtain ⟨k, rfl⟩ := h
      rw [coeff_linForm]; exact le_ciSup hb k
    · exfalso
      rw [mem_support_iff] at hs
      apply hs
      simp only [linForm, coeff_sum, coeff_C_mul, coeff_X']
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg, mul_zero]
      intro h'; exact h ⟨j, h'.symm⟩
  · refine Real.iSup_le (fun k => ?_) (NNReal.coe_nonneg _)
    by_cases h : c k = 0
    · simp [h]
    · have hm : Finsupp.single ((0 : Fin 1), k) 1 ∈ (linForm c).support := by
        rw [mem_support_iff, coeff_linForm]; exact h
      have := Finset.le_sup (f := fun s => (v ((linForm c).coeff s)).toNNReal) hm
      simp only [coeff_linForm] at this
      have h2 := NNReal.coe_le_coe.2 this
      rwa [Real.coe_toNNReal _ (apply_nonneg _ _)] at h2

/- English proof (translation)
Establish `h` using `(ReciprocityTheory.MultiplicativeHeights.Closed.sphereLinLog N (WithLp.toLp 2 c) (by simpa using hc)).2`. Rewrite `h` using `[EuclideanSpace.norm_eq]`. Simplify using `only at h`. Rewrite using `[← h]`. Unfold `ReciprocityTheory.MultiplicativeHeights.blockSphereMean ReciprocityTheory.MultiplicativeHeights.blockSphereProb`.

Rewrite using `[← (MeasureTheory.measurePreserving_funUnique (ReciprocityTheory.MultiplicativeHeights.sphereProb N) (Fin 1)).integral_comp']`. Use `MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Simplify using `[linForm, ReciprocityTheory.MultiplicativeHeights.blockPoint]`.
-/
theorem blockSphereMean_linForm {N : ℕ} (c : Fin N → ℂ) (hc : c ≠ 0) :
    ReciprocityTheory.MultiplicativeHeights.blockSphereMean 1 N (linForm c) =
      Real.log (Real.sqrt (∑ i, ‖c i‖ ^ 2)) - (harmonic (N - 1) : ℝ) / 2 := by
  have h := (ReciprocityTheory.MultiplicativeHeights.Closed.sphereLinLog N (WithLp.toLp 2 c) (by simpa using hc)).2
  rw [EuclideanSpace.norm_eq] at h
  simp only at h
  rw [← h]
  unfold ReciprocityTheory.MultiplicativeHeights.blockSphereMean ReciprocityTheory.MultiplicativeHeights.blockSphereProb
  rw [← (MeasureTheory.measurePreserving_funUnique (ReciprocityTheory.MultiplicativeHeights.sphereProb N) (Fin 1)).integral_comp']
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp [linForm, ReciprocityTheory.MultiplicativeHeights.blockPoint]

/- English proof (translation)
Unfold `formHeight pointHeight`. Use `congr 2`. Simplify using `[linSubst_linForm, gaussAbs_linForm]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Establish `hm : MvPolynomial.map σ (linForm y) = linForm (fun j => σ (y j))`.

Simplify using `[linForm]`. Establish `hσ : σ.comp (algebraMap F F) = σ` using `by ext; simp`. Rewrite using `[hm, linSubst_linForm, blockSphereMean_linForm, hσ]`. Simplify using the standard rewrite rules. Introduce `h`.

Apply `hy` to reduce the goal to its premises. Establish `: Matrix.vecMul (fun j => σ (y j)) (A σ) = 0`. Use function extensionality and compare the values at `k`. Use `congrFun h k` as an intermediate fact. Simplify `this` using `[Matrix.vecMul, dotProduct, mul_comm]`.

Establish `h2` using `Matrix.eq_zero_of_vecMul_eq_zero (hA σ) this`. Use function extensionality and compare the values at `j`. Simplify using `using congrFun h2 j`.
-/
theorem formHeight_linForm {F : Type} [Field F] [NumberField F] {N n : ℕ}
    (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ σ, (A σ).det ≠ 0) (y : Fin N → F) (hy : y ≠ 0) :
    formHeight 1 w A (linForm y) = pointHeight w A y := by
  unfold formHeight pointHeight
  congr 2
  · simp [linSubst_linForm, gaussAbs_linForm]
  · refine Finset.sum_congr rfl fun σ _ => ?_
    have hm : MvPolynomial.map σ (linForm y) = linForm (fun j => σ (y j)) := by
      simp [linForm]
    have hσ : σ.comp (algebraMap F F) = σ := by ext; simp
    rw [hm, linSubst_linForm, blockSphereMean_linForm, hσ]
    · simp
    · intro h
      apply hy
      have : Matrix.vecMul (fun j => σ (y j)) (A σ) = 0 := by
        funext k
        have := congrFun h k
        simpa [Matrix.vecMul, dotProduct, mul_comm] using this
      have h2 := Matrix.eq_zero_of_vecMul_eq_zero (hA σ) this
      funext j
      simpa using congrFun h2 j

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `s hs b`. Rewrite `hs` using `[Matrix.det_fin_two]`. Simplify using `only [Matrix.of_apply, X, monomial_mul, mul_one] at hs`. Establish `h1` using `support_sub _ _ _ hs`.

Rewrite `h1` using `[Finset.mem_union]`. Apply the tactic sequence `rcases h1 with h | h <;>`. Use `support_monomial_subset h` as an intermediate fact. Rewrite `this` using `[Finset.mem_singleton]`. Substitute `this` using the available equality.

Apply the tactic sequence `fin_cases b <;> simp [Fin.sum_univ_two, Finsupp.single_apply]`. Use `GlobalTheory.BorelAlg.irreducible_det' (R := AlgebraicClosure k) (k := 2) (by norm_num) id Function.injective_id` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[RingHom.map_det]`. Use `congr 1`.

Use extensionality with `i j`. Simplify using the standard rewrite rules. Introduce `u`. Establish `: MvPolynomial.aeval u (Matrix.of fun i j : Fin 2 => (X (i, j) : MvPolynomial (Fin 2 × Fin 2) k)).det = (Matrix.of fun i j : Fin 2 => u (i, j)).det`. Simplify using `[Matrix.det_fin_two]`.

Rewrite using `[this, ← Matrix.exists_mulVec_eq_zero_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, h⟩`. Use `⟨y, hy, fun g hg => by simp [Ideal.mem_bot.1 hg], fun i => ?_⟩` and prove the remaining obligations. Simplify `congrFun h i` using `[Matrix.mulVec, dotProduct]`.

Introduce and unpack `⟨y, hy, -, h⟩`. Use `⟨y, hy, funext fun i => ?_⟩` and prove the remaining obligations. Simplify `h i` using `[Matrix.mulVec, dotProduct]`.
-/
theorem isChowForm_line (k : Type) [Field k] :
    IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) k)) 1 1
      (Matrix.of fun i j : Fin 2 => (X (i, j) : MvPolynomial (Fin 2 × Fin 2) k)).det := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro s hs b
    rw [Matrix.det_fin_two] at hs
    simp only [Matrix.of_apply, X, monomial_mul, mul_one] at hs
    have h1 := support_sub _ _ _ hs
    rw [Finset.mem_union] at h1
    rcases h1 with h | h <;>
    · have := support_monomial_subset h
      rw [Finset.mem_singleton] at this
      subst this
      fin_cases b <;> simp [Fin.sum_univ_two, Finsupp.single_apply]
  · have := GlobalTheory.BorelAlg.irreducible_det' (R := AlgebraicClosure k) (k := 2) (by norm_num) id
      Function.injective_id
    convert this using 1
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp
  · intro u
    have : MvPolynomial.aeval u
        (Matrix.of fun i j : Fin 2 => (X (i, j) : MvPolynomial (Fin 2 × Fin 2) k)).det =
        (Matrix.of fun i j : Fin 2 => u (i, j)).det := by
      simp [Matrix.det_fin_two]
    rw [this, ← Matrix.exists_mulVec_eq_zero_iff]
    constructor
    · rintro ⟨y, hy, h⟩
      refine ⟨y, hy, fun g hg => by simp [Ideal.mem_bot.1 hg], fun i => ?_⟩
      simpa [Matrix.mulVec, dotProduct] using congrFun h i
    · rintro ⟨y, hy, -, h⟩
      refine ⟨y, hy, funext fun i => ?_⟩
      simpa [Matrix.mulVec, dotProduct] using h i

/- English proof (translation)
Introduce `h`. Establish `hz : ∀ u : Fin (D + 1) × Fin N → AlgebraicClosure k, MvPolynomial.aeval u f ≠ 0`. Introduce `u hu`. Take `⟨y, -, hI, -⟩` from `(h.zero_iff u).1 hu`. Simplify using `using hI 1 trivial`.

Apply `h.irred.not_isUnit` to reduce the goal to its premises. Rewrite using `[← Ideal.span_singleton_eq_top]`. Assume the negation of the conclusion as `hne`. Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal _ hne`. Take `⟨x, rfl⟩` from `(MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton).1 hM`.

Use `hle (Ideal.subset_span rfl)` as an intermediate fact. Rewrite `this` using `[MvPolynomial.mem_vanishingIdeal_singleton_iff]`. Apply `hz x` to reduce the goal to its premises. Simplify `this` using `[MvPolynomial.aeval_map_algebraMap]`.
-/
theorem not_isChowForm_top {k : Type} [Field k] {N D δ : ℕ}
    (f : MvPolynomial (Fin (D + 1) × Fin N) k) : ¬ IsChowForm (⊤ : Ideal (MvPolynomial (Fin N) k)) D δ f := by
  intro h
  have hz : ∀ u : Fin (D + 1) × Fin N → AlgebraicClosure k, MvPolynomial.aeval u f ≠ 0 := by
    intro u hu
    obtain ⟨y, -, hI, -⟩ := (h.zero_iff u).1 hu
    simpa using hI 1 trivial
  apply h.irred.not_isUnit
  rw [← Ideal.span_singleton_eq_top]
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨x, rfl⟩ := (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton).1 hM
  have := hle (Ideal.subset_span rfl)
  rw [MvPolynomial.mem_vanishingIdeal_singleton_iff] at this
  apply hz x
  simpa [MvPolynomial.aeval_map_algebraMap] using this

end GlobalTheory.ChowHt.Model

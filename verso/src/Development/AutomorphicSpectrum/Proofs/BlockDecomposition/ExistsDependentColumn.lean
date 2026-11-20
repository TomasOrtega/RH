import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFieldIdemOne
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr.Coeff

variable {A : Type} [CommRing A]

/- English proof (translation)
Take `⟨y, rfl⟩` from `Ideal.mem_span_singleton'.1 hx`. Take the linear combination `(-y) * hf`.
-/
theorem mul_eq_zero_of_mem {f : A} (hf : f * f = f) {x : A}
    (hx : x ∈ Ideal.span ({1 - f} : Set A)) : f * x = 0 := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  linear_combination (-y) * hf

/- English proof (translation)
The claim follows from `Ideal.mem_span_singleton'.2 ⟨x, by linear_combination (-1 : A) * hx⟩`.
-/
theorem mem_of_mul_eq_zero {f x : A} (hx : f * x = 0) :
    x ∈ Ideal.span ({1 - f} : Set A) :=
  Ideal.mem_span_singleton'.2 ⟨x, by linear_combination (-1 : A) * hx⟩

/- English proof (translation)
Use `Ideal.isMaximal_iff.2 ⟨fun h => hf.ne ?_, fun J x hJ hx hxJ => ?_⟩` and prove the remaining obligations. Simplify using `using mul_eq_zero_of_mem hf.idem h`. Establish `hne : f * x ≠ 0` using `fun h => hx (mem_of_mul_eq_zero h)`. Take `⟨y, hy⟩` from `hf.inv x hne`. Establish `h1 : (1 - f) ∈ J` using `hJ (Ideal.subset_span rfl)`.

Establish `h2 : x * (f * y) ∈ J` using `J.mul_mem_right _ hxJ`. Establish `: (1 : A) = (1 - f) + x * (f * y)` using `by linear_combination (-1 : A) * hy`. Rewrite using `[this]`. Conclude with `J.add_mem h1 h2`.
-/
theorem isMaximal_span {f : A} (hf : IsFieldIdem f) :
    (Ideal.span ({1 - f} : Set A)).IsMaximal := by
  refine Ideal.isMaximal_iff.2 ⟨fun h => hf.ne ?_, fun J x hJ hx hxJ => ?_⟩
  · simpa using mul_eq_zero_of_mem hf.idem h
  · have hne : f * x ≠ 0 := fun h => hx (mem_of_mul_eq_zero h)
    obtain ⟨y, hy⟩ := hf.inv x hne
    have h1 : (1 - f) ∈ J := hJ (Ideal.subset_span rfl)
    have h2 : x * (f * y) ∈ J := J.mul_mem_right _ hxJ
    have : (1 : A) = (1 - f) + x * (f * y) := by linear_combination (-1 : A) * hy
    rw [this]
    exact J.add_mem h1 h2

/- English proof (translation)
Use `set w : Matrix (Fin a) (Fin t) K := v.map π with hw`. Distinguish the cases in `hli : LinearIndependent K w.col`. Use `left`. Establish `hinj : Function.Injective w.mulVecLin` using `Matrix.mulVec_injective_iff.2 hli`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective w.mulVecLin (LinearMap.ker_eq_bot.2 hinj)`.

Use `set N : Matrix (Fin t) (Fin a) K := LinearMap.toMatrix' g with hN`. Establish `hNw : N * w = 1`. Establish `: LinearMap.toMatrix' (g ∘ₗ w.mulVecLin) = N * w`. Rewrite using `[LinearMap.toMatrix'_comp, hN]`. Use `congr 1`.

Rewrite using `[← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']`. Rewrite using `[← this, hg, LinearMap.toMatrix'_id]`. Use `choose l hl using hs`. Use `⟨Matrix.of fun p q => l (N p q), ?_⟩` and prove the remaining obligations. Establish `hmap : ((Matrix.of fun p q => l (N p q) : Fx A t a) * v).map π = 1`.

Rewrite using `[Matrix.map_mul, ← hNw]`. Use `congr 1`. Use extensionality with `p q`. Simplify using `[hl]`. Use extensionality with `p q`.

Establish `hpq` using `congrFun (congrFun hmap p) q`. Establish `hz : π (((Matrix.of fun p q => l (N p q) : Fx A t a) * v) p q - (1 : Fx A t t) p q) = 0`. Rewrite using `[map_sub, sub_eq_zero]`. Establish `hpq' : π (((Matrix.of fun p q => l (N p q) : Fx A t a) * v) p q) = (1 : Matrix (Fin t) (Fin t) K) p q` using `hpq`. Rewrite using `[hpq']`.

Distinguish the cases in `h : p = q`. Substitute `h` using the available equality. Rewrite using `[Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]`. Rewrite using `[Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]`. Use `h0 _ hz` as an intermediate fact.

Simplify using `only [Matrix.smul_apply, smul_eq_mul]`. Take the linear combination `this`. Use `right`. Take `⟨g, hg, i, hi⟩` from `Fintype.not_linearIndependent_iff.1 hli`. Use `set b : Fin t → K := fun k => if k = i then 0 else -(g k / g i) with hb`.

Use `choose l hl using hs`. Use `⟨i, fun k => f * l (b k), ?_, fun k => ?_, fun p => ?_⟩` and prove the remaining obligations. Establish `: π (l (b i)) = 0` using `by simp [hl, hb]`. Conclude with `h0 _ this`. Rewrite using `[← mul_assoc, hf]`.

Establish `hrow : ∑ k, g k * w p k = 0`. Use `congrFun hg p` as an intermediate fact. Simplify `this` using `[Matrix.col_apply, Finset.sum_apply]`. Establish `hz : π (v p i - ∑ k, l (b k) * v p k) = 0`. Establish `hw' : ∀ k, π (v p k) = w p k` using `fun k => rfl`.

Rewrite using `[map_sub, map_sum]`. Simplify using `only [map_mul, hl, hw']`. Establish `hsum : ∑ k, b k * w p k = w p i`. Establish `hsplit : ∀ k, b k * w p k = -(g i)⁻¹ * (g k * w p k) + (if k = i then w p i else 0)`. Introduce `k`.

Distinguish the cases in `h : k = i`. Substitute `h` using the available equality. Simplify using `only [hb, if_true]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [hb, if_neg h]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_add_distrib, ← Finset.mul_sum, hrow]`. Simplify using the standard rewrite rules.

Rewrite using `[hsum, sub_self]`. Use `h0 _ hz` as an intermediate fact. Rewrite `this` using `[mul_sub, Finset.mul_sum, sub_eq_zero]`. Rewrite using `[this]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`.
-/
theorem alt_of_field {K : Type} [Field K] (π : A →+* K) (hs : Function.Surjective π) {f : A}
    (hf : f * f = f) (h1 : π f = 1) (h0 : ∀ x, π x = 0 → f * x = 0) {a t : ℕ} (v : Fx A a t) :
    (∃ M : Fx A t a, f • (M * v) = f • (1 : Fx A t t)) ∨
      ∃ (i : Fin t) (c : Fin t → A), c i = 0 ∧ (∀ k, f * c k = c k) ∧
        ∀ p, f * v p i = ∑ k, c k * v p k := by
  classical
  set w : Matrix (Fin a) (Fin t) K := v.map π with hw
  by_cases hli : LinearIndependent K w.col
  · left
    have hinj : Function.Injective w.mulVecLin := Matrix.mulVec_injective_iff.2 hli
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective w.mulVecLin
      (LinearMap.ker_eq_bot.2 hinj)
    set N : Matrix (Fin t) (Fin a) K := LinearMap.toMatrix' g with hN
    have hNw : N * w = 1 := by
      have : LinearMap.toMatrix' (g ∘ₗ w.mulVecLin) = N * w := by
        rw [LinearMap.toMatrix'_comp, hN]
        congr 1
        rw [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
      rw [← this, hg, LinearMap.toMatrix'_id]
    choose l hl using hs
    refine ⟨Matrix.of fun p q => l (N p q), ?_⟩
    have hmap : ((Matrix.of fun p q => l (N p q) : Fx A t a) * v).map π = 1 := by
      rw [Matrix.map_mul, ← hNw]
      congr 1
      ext p q
      simp [hl]
    ext p q
    have hpq := congrFun (congrFun hmap p) q
    have hz : π (((Matrix.of fun p q => l (N p q) : Fx A t a) * v) p q - (1 : Fx A t t) p q) = 0 := by
      rw [map_sub, sub_eq_zero]
      have hpq' : π (((Matrix.of fun p q => l (N p q) : Fx A t a) * v) p q) = (1 : Matrix (Fin t) (Fin t) K) p q := hpq
      rw [hpq']
      by_cases h : p = q
      · subst h
        rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
      · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]
    have := h0 _ hz
    simp only [Matrix.smul_apply, smul_eq_mul]
    linear_combination this
  · right
    obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hli
    set b : Fin t → K := fun k => if k = i then 0 else -(g k / g i) with hb
    choose l hl using hs
    refine ⟨i, fun k => f * l (b k), ?_, fun k => ?_, fun p => ?_⟩
    · have : π (l (b i)) = 0 := by simp [hl, hb]
      exact h0 _ this
    · rw [← mul_assoc, hf]
    · have hrow : ∑ k, g k * w p k = 0 := by
        have := congrFun hg p
        simpa [Matrix.col_apply, Finset.sum_apply] using this
      have hz : π (v p i - ∑ k, l (b k) * v p k) = 0 := by
        have hw' : ∀ k, π (v p k) = w p k := fun k => rfl
        rw [map_sub, map_sum]
        simp only [map_mul, hl, hw']
        have hsum : ∑ k, b k * w p k = w p i := by
          have hsplit : ∀ k, b k * w p k = -(g i)⁻¹ * (g k * w p k) +
              (if k = i then w p i else 0) := by
            intro k
            by_cases h : k = i
            · subst h
              simp only [hb, if_true]
              field_simp
              ring
            · simp only [hb, if_neg h]
              field_simp
              ring
          rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_add_distrib,
            ← Finset.mul_sum, hrow]
          simp
        rw [hsum, sub_self]
      have := h0 _ hz
      rw [mul_sub, Finset.mul_sum, sub_eq_zero] at this
      rw [this]
      exact Finset.sum_congr rfl fun k _ => by ring

/- English proof (translation)
Establish `key : ∀ j, (∃ M : Fx A t a, f j • (M * v) = f j • (1 : Fx A t t)) ∨ ∃ (i : Fin t) (c : Fin t → A), c i = 0 ∧ (∀ k, f j * c k = c k) ∧ ∀ p, f j * v p i = ∑ k, c k * v p k`. Introduce `j`. Establish `hj` using `hd.field j`. Use `haveI := isMaximal_span hj`. Use `letI : Field (A ⧸ Ideal.span ({1 - f j} : Set A)) := Ideal.Quotient.field _`.

Use `alt_of_field (Ideal.Quotient.mk (Ideal.span ({1 - f j} : Set A))) Ideal.Quotient.mk_surjective hj.idem ?_ ?_ v` and prove the remaining obligations. Rewrite using `[← map_one (Ideal.Quotient.mk (Ideal.span ({1 - f j} : Set A)))]`. Use `Ideal.Quotient.eq.2 ?_` and prove the remaining obligations. Establish `: f j - 1 = (-1 : A) * (1 - f j)` using `by ring`. Rewrite using `[this]`.

Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)`. Introduce `x hx`. Conclude with `mul_eq_zero_of_mem hj.idem (Ideal.Quotient.eq_zero_iff_mem.1 hx)`. Assume the negation of the conclusion as `hno`. Establish `hall : ∀ j, ∃ M : Fx A t a, f j • (M * v) = f j • (1 : Fx A t t)` using `fun j => (key j).resolve_right fun ⟨i, c, h⟩ => hno ⟨j, i, c, h⟩`.

Use `choose M hM using hall`. Use `hv ⟨∑ j, f j • M j, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.sum_mul, ← hd.sum, Finset.sum_smul]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [Matrix.smul_mul, hM j]`.
-/
theorem exists_dependent_column {A : Type} [CommRing A] {ι : Type} [Fintype ι] (e : A) (f : ι → A)
    (hd : IsFieldDec e f) {a t : ℕ} (v : Fx A a t)
    (hv : ¬ ∃ M : Fx A t a, M * v = e • (1 : Fx A t t)) :
    ∃ (j : ι) (i : Fin t) (c : Fin t → A), c i = 0 ∧ (∀ k, f j * c k = c k) ∧
      ∀ p, f j * v p i = ∑ k, c k * v p k := by
  classical
  have key : ∀ j, (∃ M : Fx A t a, f j • (M * v) = f j • (1 : Fx A t t)) ∨
      ∃ (i : Fin t) (c : Fin t → A), c i = 0 ∧ (∀ k, f j * c k = c k) ∧
        ∀ p, f j * v p i = ∑ k, c k * v p k := by
    intro j
    have hj := hd.field j
    haveI := isMaximal_span hj
    letI : Field (A ⧸ Ideal.span ({1 - f j} : Set A)) := Ideal.Quotient.field _
    refine alt_of_field (Ideal.Quotient.mk (Ideal.span ({1 - f j} : Set A)))
      Ideal.Quotient.mk_surjective hj.idem ?_ ?_ v
    · rw [← map_one (Ideal.Quotient.mk (Ideal.span ({1 - f j} : Set A)))]
      refine Ideal.Quotient.eq.2 ?_
      have : f j - 1 = (-1 : A) * (1 - f j) := by ring
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    · intro x hx
      exact mul_eq_zero_of_mem hj.idem (Ideal.Quotient.eq_zero_iff_mem.1 hx)
  by_contra hno
  have hall : ∀ j, ∃ M : Fx A t a, f j • (M * v) = f j • (1 : Fx A t t) := fun j =>
    (key j).resolve_right fun ⟨i, c, h⟩ => hno ⟨j, i, c, h⟩
  choose M hM using hall
  refine hv ⟨∑ j, f j • M j, ?_⟩
  rw [Matrix.sum_mul, ← hd.sum, Finset.sum_smul]
  exact Finset.sum_congr rfl fun j _ => by rw [Matrix.smul_mul, hM j]

end GlobalTheory.CompanionTheory.NullFr.Coeff

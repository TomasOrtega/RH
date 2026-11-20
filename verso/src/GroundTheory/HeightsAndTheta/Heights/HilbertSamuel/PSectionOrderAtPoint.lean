import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionOrderAtPoint
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLocalRep
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

namespace SectionOrderAtPoint

section Core

universe v

variable {R : Type*} [CommRing R]

def mulIdeal (W I : Ideal R) (f : R) : (R ⧸ (W ⊔ I)) →ₗ[R] (R ⧸ (W ⊔ Ideal.span {f} * I)) :=
  Submodule.mapQ _ _ (LinearMap.mulLeft R f) fun x hx => by
    have h : Ideal.span {f} * (W ⊔ I) ≤ W ⊔ Ideal.span {f} * I := by
      rw [Ideal.mul_sup]
      exact sup_le_sup_right Ideal.mul_le_right _
    exact h (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self f) hx)

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`. Introduce `x hx`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite `hx` using `[LinearMap.mem_ker, mulIdeal, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]`. Rewrite using `[Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]`.

Take `⟨v, hv, w, hw, hvw⟩` from `Submodule.mem_sup.mp hx`. Take `⟨i, hi, rfl⟩` from `Ideal.mem_span_singleton_mul.mp hw`. Simplify using `only [LinearMap.mulLeft_apply] at hvw`. Establish `h1 : f * (x - i) ∈ W`. Establish `: f * (x - i) = v` using `by linear_combination -hvw`.

Rewrite using `[this]`. Conclude with `hv`. Establish `h2 : x - i ∈ W` using `(hW.mem_or_mem h1).resolve_left hf`. Establish `: x = (x - i) + i` using `by ring`. Rewrite using `[this]`.

Conclude with `Submodule.add_mem _ (Submodule.mem_sup_left h2) (Submodule.mem_sup_right hi)`.
-/
theorem mulIdeal_injective {W : Ideal R} (hW : W.IsPrime) (I : Ideal R) {f : R} (hf : f ∉ W) :
    Function.Injective (mulIdeal W I f) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearMap.mem_ker, mulIdeal, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  obtain ⟨v, hv, w, hw, hvw⟩ := Submodule.mem_sup.mp hx
  obtain ⟨i, hi, rfl⟩ := Ideal.mem_span_singleton_mul.mp hw
  simp only [LinearMap.mulLeft_apply] at hvw
  have h1 : f * (x - i) ∈ W := by
    have : f * (x - i) = v := by linear_combination -hvw
    rw [this]; exact hv
  have h2 : x - i ∈ W := (hW.mem_or_mem h1).resolve_left hf
  have : x = (x - i) + i := by ring
  rw [this]
  exact Submodule.add_mem _ (Submodule.mem_sup_left h2) (Submodule.mem_sup_right hi)

/- English proof (translation)
The claim follows from `sup_le_sup_left Ideal.mul_le_left W`.
-/
theorem sup_mul_le (W I : Ideal R) (f : R) : W ⊔ Ideal.span {f} * I ≤ W ⊔ Ideal.span {f} :=
  sup_le_sup_left Ideal.mul_le_left W

/- English proof (translation)
Introduce `y`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Express the relevant statement in the definitionally equal form `(Submodule.Quotient.mk y : R ⧸ (W ⊔ Ideal.span {f})) = 0 ↔ _`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Take `⟨v, hv, w, hw, hvw⟩` from `Submodule.mem_sup.mp hy`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hw`. Use `⟨Submodule.Quotient.mk c, ?_⟩` and prove the remaining obligations. Rewrite using `[mulIdeal, Submodule.mapQ_apply, Submodule.Quotient.eq]`.

Simplify using `only [LinearMap.mulLeft_apply]`. Establish `: f * c - y = -v` using `by linear_combination hvw`. Rewrite using `[this]`. Conclude with `Submodule.neg_mem _ (Submodule.mem_sup_left hv)`. Introduce and unpack `⟨x, hx⟩`.

Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite `hx` using `[mulIdeal, Submodule.mapQ_apply, Submodule.Quotient.eq']`. Simplify using `only [LinearMap.mulLeft_apply] at hx`. Establish `hy : y = f * x + (-(f * x) + y)` using `by ring`. Rewrite using `[hy]`.

Conclude with `Submodule.add_mem _ (Submodule.mem_sup_right (Ideal.mul_mem_right x _ (Ideal.mem_span_singleton_self f))) (sup_mul_le W I f hx)`.
-/
theorem mulIdeal_exact (W I : Ideal R) (f : R) :
    Function.Exact (mulIdeal W I f) (Submodule.factor (sup_mul_le W I f)) := by
  intro y
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  change (Submodule.Quotient.mk y : R ⧸ (W ⊔ Ideal.span {f})) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hy
    obtain ⟨v, hv, w, hw, hvw⟩ := Submodule.mem_sup.mp hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hw
    refine ⟨Submodule.Quotient.mk c, ?_⟩
    rw [mulIdeal, Submodule.mapQ_apply, Submodule.Quotient.eq]
    simp only [LinearMap.mulLeft_apply]
    have : f * c - y = -v := by linear_combination hvw
    rw [this]
    exact Submodule.neg_mem _ (Submodule.mem_sup_left hv)
  · rintro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [mulIdeal, Submodule.mapQ_apply, Submodule.Quotient.eq'] at hx
    simp only [LinearMap.mulLeft_apply] at hx
    have hy : y = f * x + (-(f * x) + y) := by ring
    rw [hy]
    exact Submodule.add_mem _
      (Submodule.mem_sup_right (Ideal.mul_mem_right x _ (Ideal.mem_span_singleton_self f)))
      (sup_mul_le W I f hx)

/- English proof (translation)
Rewrite using `[locLen_add (LinearMap.ker g).subtype g (Submodule.injective_subtype _) hg (LinearMap.exact_subtype_ker_map g) p]`. Conclude with `le_add_self`.
-/
theorem locLen_le_of_surjective {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (g : M →ₗ[R] N) (hg : Function.Surjective g) (p : PrimeSpectrum R) :
    locLen N p ≤ locLen M p := by
  rw [locLen_add (LinearMap.ker g).subtype g (Submodule.injective_subtype _) hg
    (LinearMap.exact_subtype_ker_map g) p]
  exact le_add_self

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Rewrite using `[pow_zero, locLen_quot_eq_zero p fun h1 => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)]`. Conclude with `ENat.zero_ne_top`. Consider the case `succ k ih`.

Rewrite using `[pow_succ', locLen_mul hW hb]`. Conclude with `WithTop.add_ne_top.mpr ⟨ih, h⟩`.
-/
theorem locLen_pow_ne_top {W : Ideal R} (hW : W.IsPrime) {b : R} (hb : b ∉ W) (p : PrimeSpectrum R)
    (h : locLen (R ⧸ (W ⊔ Ideal.span {b})) p ≠ ⊤) (k : ℕ) :
    locLen (R ⧸ (W ⊔ Ideal.span {b ^ k})) p ≠ ⊤ := by
  induction k with
  | zero =>
    rw [pow_zero, locLen_quot_eq_zero p fun h1 => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)]
    exact ENat.zero_ne_top
  | succ k ih =>
    rw [pow_succ', locLen_mul hW hb]
    exact WithTop.add_ne_top.mpr ⟨ih, h⟩

def powIdeal (a b : R) (n : ℕ) : Ideal R :=
  Ideal.span (Set.range fun i : Fin (n + 1) => a ^ (i : ℕ) * b ^ (n - i))

/- English proof (translation)
The claim follows from `Ideal.subset_span ⟨0, by simp⟩`.
-/
theorem pow_mem_powIdeal (a b : R) (n : ℕ) : b ^ n ∈ powIdeal a b n :=
  Ideal.subset_span ⟨0, by simp⟩

/- English proof (translation)
Rewrite using `[Ideal.span_singleton_mul_le_iff]`. Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨⟨i, hi⟩, rfl⟩` from `hx`.

Distinguish the cases in `hin : i < n`. Use `Submodule.mem_sup_right (Ideal.mem_span_singleton_mul.mpr ⟨a ^ (i + 1) * b ^ (n - (i + 1)), Ideal.subset_span ⟨⟨i + 1, by omega⟩, rfl⟩, ?_⟩)` and prove the remaining obligations. Establish `: n - i = (n - (i + 1)) + 1` using `by omega`. Simplify using `only [this, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hi' : i = n` using `by omega`. Substitute `hi'` using the available equality. Establish `hsum : ∑ j ∈ Finset.range (i + 1), c j * a ^ j * b ^ (i + 1 - j) ∈ Ideal.span {b} * powIdeal a b i`. Use `Ideal.sum_mem _ fun j hj => ?_` and prove the remaining obligations. Establish `hj' : j < i + 1` using `Finset.mem_range.mp hj`.

Use `Ideal.mem_span_singleton_mul.mpr ⟨c j * (a ^ j * b ^ (i - j)), Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨j, hj'⟩, rfl⟩), ?_⟩` and prove the remaining obligations. Establish `: i + 1 - j = (i - j) + 1` using `by omega`. Rewrite using `[this, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Establish `: a * (a ^ i * b ^ (i - i)) = (a ^ (i + 1) + ∑ j ∈ Finset.range (i + 1), c j * a ^ j * b ^ (i + 1 - j)) - ∑ j ∈ Finset.range (i + 1), c j * a ^ j * b ^ (i + 1 - j)`.

Simplify using `only [Nat.sub_self, pow_zero, mul_one, add_sub_cancel_right, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Submodule.sub_mem _ (Submodule.mem_sup_left hrel) (Submodule.mem_sup_right hsum)`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [mul_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul r x _ hx`. Rewrite using `[smul_eq_mul, mul_left_comm]`. Conclude with `Ideal.mul_mem_left _ r hx`.
-/
theorem mul_powIdeal_le {W : Ideal R} {a b : R} {n : ℕ} (c : ℕ → R)
    (hrel : a ^ (n + 1) + ∑ j ∈ Finset.range (n + 1), c j * a ^ j * b ^ (n + 1 - j) ∈ W) :
    Ideal.span {a} * powIdeal a b n ≤ W ⊔ Ideal.span {b} * powIdeal a b n := by
  rw [Ideal.span_singleton_mul_le_iff]
  intro z hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨i, hi⟩, rfl⟩ := hx
    by_cases hin : i < n
    · refine Submodule.mem_sup_right (Ideal.mem_span_singleton_mul.mpr
        ⟨a ^ (i + 1) * b ^ (n - (i + 1)), Ideal.subset_span ⟨⟨i + 1, by omega⟩, rfl⟩, ?_⟩)
      have : n - i = (n - (i + 1)) + 1 := by omega
      simp only [this, pow_succ]
      ring
    · have hi' : i = n := by omega
      subst hi'
      have hsum : ∑ j ∈ Finset.range (i + 1), c j * a ^ j * b ^ (i + 1 - j) ∈
          Ideal.span {b} * powIdeal a b i := by
        refine Ideal.sum_mem _ fun j hj => ?_
        have hj' : j < i + 1 := Finset.mem_range.mp hj
        refine Ideal.mem_span_singleton_mul.mpr ⟨c j * (a ^ j * b ^ (i - j)),
          Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨j, hj'⟩, rfl⟩), ?_⟩
        have : i + 1 - j = (i - j) + 1 := by omega
        rw [this, pow_succ]
        ring
      have : a * (a ^ i * b ^ (i - i)) =
          (a ^ (i + 1) + ∑ j ∈ Finset.range (i + 1), c j * a ^ j * b ^ (i + 1 - j)) -
            ∑ j ∈ Finset.range (i + 1), c j * a ^ j * b ^ (i + 1 - j) := by
        simp only [Nat.sub_self, pow_zero, mul_one, add_sub_cancel_right, pow_succ]
        ring
      rw [this]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left hrel) (Submodule.mem_sup_right hsum)
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    rw [smul_eq_mul, mul_left_comm]
    exact Ideal.mul_mem_left _ r hx

/- English proof (translation)
Use `set I := powIdeal a b n`. Establish `hA` using `locLen_add (mulIdeal W I a) (Submodule.factor (sup_mul_le W I a)) (mulIdeal_injective hW I ha) (Submodule.factor_surjective _) (mulIdeal_exact W I a) p`. Establish `hB` using `locLen_add (mulIdeal W I b) (Submodule.factor (sup_mul_le W I b)) (mulIdeal_injective hW I hb) (Submodule.factor_surjective _) (mulIdeal_exact W I b) p`. Establish `hle : W ⊔ Ideal.span {a} * I ≤ W ⊔ Ideal.span {b} * I` using `sup_le le_sup_left (mul_powIdeal_le c hrel)`. Establish `h1` using `locLen_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle) p`.

Establish `hI : W ⊔ Ideal.span {b ^ n} ≤ W ⊔ I` using `sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr (pow_mem_powIdeal a b n)) W`. Establish `h2` using `locLen_le_of_surjective (Submodule.factor hI) (Submodule.factor_surjective hI) p`. Establish `hIfin : locLen (R ⧸ (W ⊔ I)) p ≠ ⊤` using `ne_top_of_le_ne_top (locLen_pow_ne_top hW hb p hfin n) h2`. Rewrite `h1` using `[hA, hB]`. Conclude with `(ENat.add_le_add_iff_left hIfin).mp h1`.
-/
theorem locLen_le_of_monic {W : Ideal R} (hW : W.IsPrime) {a b : R} (ha : a ∉ W) (hb : b ∉ W)
    (p : PrimeSpectrum R) {n : ℕ} (c : ℕ → R)
    (hrel : a ^ (n + 1) + ∑ j ∈ Finset.range (n + 1), c j * a ^ j * b ^ (n + 1 - j) ∈ W)
    (hfin : locLen (R ⧸ (W ⊔ Ideal.span {b})) p ≠ ⊤) :
    locLen (R ⧸ (W ⊔ Ideal.span {b})) p ≤ locLen (R ⧸ (W ⊔ Ideal.span {a})) p := by
  set I := powIdeal a b n
  have hA := locLen_add (mulIdeal W I a) (Submodule.factor (sup_mul_le W I a))
    (mulIdeal_injective hW I ha) (Submodule.factor_surjective _) (mulIdeal_exact W I a) p
  have hB := locLen_add (mulIdeal W I b) (Submodule.factor (sup_mul_le W I b))
    (mulIdeal_injective hW I hb) (Submodule.factor_surjective _) (mulIdeal_exact W I b) p
  have hle : W ⊔ Ideal.span {a} * I ≤ W ⊔ Ideal.span {b} * I :=
    sup_le le_sup_left (mul_powIdeal_le c hrel)
  have h1 := locLen_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle) p
  have hI : W ⊔ Ideal.span {b ^ n} ≤ W ⊔ I :=
    sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr (pow_mem_powIdeal a b n)) W
  have h2 := locLen_le_of_surjective (Submodule.factor hI) (Submodule.factor_surjective hI) p
  have hIfin : locLen (R ⧸ (W ⊔ I)) p ≠ ⊤ :=
    ne_top_of_le_ne_top (locLen_pow_ne_top hW hb p hfin n) h2
  rw [hA, hB] at h1
  exact (ENat.add_le_add_iff_left hIfin).mp h1

/- English proof (translation)
Establish `huW : u ∉ W` using `fun h => hu (hWp h)`. Consider the cases of `n with`. Consider the case `zero`. Simplify using `only [pow_zero, mul_one, Finset.range_zero, Finset.sum_empty, add_zero] at hrel`. Conclude with `absurd hrel huW`.

Consider the case `succ m`. Establish `hua : u * a ∉ W` using `fun h => (hW.mem_or_mem h).elim huW ha`. Establish `hrel' : (u * a) ^ (m + 1) + ∑ j ∈ Finset.range (m + 1), (c j * u ^ (m - j)) * (u * a) ^ j * b ^ (m + 1 - j) ∈ W`. Establish `e : (u * a) ^ (m + 1) + ∑ j ∈ Finset.range (m + 1), (c j * u ^ (m - j)) * (u * a) ^ j * b ^ (m + 1 - j) = u ^ m * (u * a ^ (m + 1) + ∑ j ∈ Finset.range (m + 1), c j * a ^ j * b ^ (m + 1 - j))`. Rewrite using `[mul_add, Finset.mul_sum]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Establish `hj' : j ≤ m` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)`. Rewrite using `[show u ^ m = u ^ (m - j) * u ^ j by rw [← pow_add, Nat.sub_add_cancel hj']]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `W.mul_mem_left _ hrel`. Establish `key` using `locLen_le_of_monic hW hua hb p _ hrel' hfin`. Rewrite `key` using `[locLen_mul hW huW a, locLen_quot_eq_zero p hu, add_zero]`. Then use the resulting hypothesis.
-/
theorem locLen_le_of_rel {W : Ideal R} (hW : W.IsPrime) {a b u : R} (ha : a ∉ W) (hb : b ∉ W)
    (p : PrimeSpectrum R) (hWp : W ≤ p.asIdeal) (hu : u ∉ p.asIdeal) {n : ℕ} (c : ℕ → R)
    (hrel : u * a ^ n + ∑ j ∈ Finset.range n, c j * a ^ j * b ^ (n - j) ∈ W)
    (hfin : locLen (R ⧸ (W ⊔ Ideal.span {b})) p ≠ ⊤) :
    locLen (R ⧸ (W ⊔ Ideal.span {b})) p ≤ locLen (R ⧸ (W ⊔ Ideal.span {a})) p := by
  have huW : u ∉ W := fun h => hu (hWp h)
  cases n with
  | zero =>
    simp only [pow_zero, mul_one, Finset.range_zero, Finset.sum_empty, add_zero] at hrel
    exact absurd hrel huW
  | succ m =>
    have hua : u * a ∉ W := fun h => (hW.mem_or_mem h).elim huW ha
    have hrel' : (u * a) ^ (m + 1) + ∑ j ∈ Finset.range (m + 1),
        (c j * u ^ (m - j)) * (u * a) ^ j * b ^ (m + 1 - j) ∈ W := by
      have e : (u * a) ^ (m + 1) + ∑ j ∈ Finset.range (m + 1),
          (c j * u ^ (m - j)) * (u * a) ^ j * b ^ (m + 1 - j) =
          u ^ m * (u * a ^ (m + 1) + ∑ j ∈ Finset.range (m + 1), c j * a ^ j * b ^ (m + 1 - j)) := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        · ring
        · refine Finset.sum_congr rfl fun j hj => ?_
          have hj' : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          rw [show u ^ m = u ^ (m - j) * u ^ j by rw [← pow_add, Nat.sub_add_cancel hj']]
          ring
      rw [e]
      exact W.mul_mem_left _ hrel
    have key := locLen_le_of_monic hW hua hb p _ hrel' hfin
    rwa [locLen_mul hW huW a, locLen_quot_eq_zero p hu, add_zero] at key

/- English proof (translation)
Establish `hsum : ∑ j ∈ Finset.range n, c j * a ^ j * b ^ (n - j) ∈ V`. Use `V.sum_mem fun j hj => ?_` and prove the remaining obligations. Establish `: n - j = (n - j - 1) + 1` using `by have := Finset.mem_range.mp hj; omega`. Rewrite using `[this, pow_succ, ← mul_assoc]`. Conclude with `V.mul_mem_left _ hb`.

Establish `h` using `(Submodule.add_mem_iff_left _ hsum).mp hrel`. Conclude with `hV.mem_of_pow_mem n ((hV.mem_or_mem h).resolve_left hu)`.
-/
theorem mem_of_rel {V : Ideal R} (hV : V.IsPrime) {a b u : R} (hb : b ∈ V) (hu : u ∉ V) {n : ℕ}
    (c : ℕ → R) (hrel : u * a ^ n + ∑ j ∈ Finset.range n, c j * a ^ j * b ^ (n - j) ∈ V) : a ∈ V := by
  have hsum : ∑ j ∈ Finset.range n, c j * a ^ j * b ^ (n - j) ∈ V := by
    refine V.sum_mem fun j hj => ?_
    have : n - j = (n - j - 1) + 1 := by have := Finset.mem_range.mp hj; omega
    rw [this, pow_succ, ← mul_assoc]
    exact V.mul_mem_left _ hb
  have h := (Submodule.add_mem_iff_left _ hsum).mp hrel
  exact hV.mem_of_pow_mem n ((hV.mem_or_mem h).resolve_left hu)

end Core

section Relation

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [Fintype K] in
/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using LocalRep.isMultiHomog_C (ι := ι) 1`. Consider the case `succ m ih`. Rewrite using `[pow_succ, succ_nsmul]`. Conclude with `LocalRep.isMultiHomog_mul ih hf`.
-/
theorem isMultiHomog_pow' {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d) (m : ℕ) :
    IsMultiHomog (f ^ m) (m • d) := by
  induction m with
  | zero => simpa using LocalRep.isMultiHomog_C (ι := ι) 1
  | succ m ih =>
    rw [pow_succ, succ_nsmul]
    exact LocalRep.isMultiHomog_mul ih hf

omit [Fintype K] in
/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using LowerBoundFree.isMultiHomog_zero (ι := ι) d`. Consider the case `insert b s hb ih`. Rewrite using `[Finset.sum_insert hb]`. Conclude with `LocalRep.isMultiHomog_add (hf b (Finset.mem_insert_self b s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))`.
-/
theorem isMultiHomog_sum' {β : Type*} (s : Finset β) (f : β → MRing ι) {d : K → ℕ}
    (hf : ∀ j ∈ s, IsMultiHomog (f j) d) : IsMultiHomog (∑ j ∈ s, f j) d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LowerBoundFree.isMultiHomog_zero (ι := ι) d
  | insert b s hb ih =>
    rw [Finset.sum_insert hb]
    exact LocalRep.isMultiHomog_add (hf b (Finset.mem_insert_self b s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/- English proof (translation)
Take `⟨p, hpm, hp⟩` from `ht`. Use `set n := p.natDegree`. Rewrite `hp` using `[hpm.as_sum]`. Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C] at hp`. Use `choose Nf Rf hRf hRe using fun i : ℕ => LocalRep.exists_form_of_mem_chartRingZ y c hyc (p.coeff i).2`.

Use `set N : K → ℕ := ∑ i ∈ Finset.range n, Nf i`. Establish `hN : ∀ i ∈ Finset.range n, ∀ k, Nf i k ≤ N k`. Introduce `i hi k`. Simplify using `only [N, Finset.sum_apply]`. Conclude with `Finset.single_le_sum (f := fun j => Nf j k) (fun _ _ => Nat.zero_le _) hi`.

Use `set P : (K → ℕ) → MRing ι := fun f => ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ f k`. Use `⟨N, n, fun i => Rf i * P (N - Nf i), ?_⟩` and prove the remaining obligations. Use `LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero y (d := N + n • δ) ?_ ?_` and prove the remaining obligations. Use `LocalRep.isMultiHomog_add (LocalRep.isMultiHomog_mul (LocalRep.isMultiHomog_chartMono c N) (isMultiHomog_pow' hA n)) (isMultiHomog_sum' _ _ fun j hj => ?_)` and prove the remaining obligations. Establish `h1` using `LocalRep.isMultiHomog_mul (LocalRep.isMultiHomog_mul (LocalRep.isMultiHomog_mul (hRf j) (LocalRep.isMultiHomog_chartMono c (N - Nf j))) (isMultiHomog_pow' hA j)) (isMultiHomog_pow' hB (n - j))`.

Use `h1 using 1` and compare the differences between its conclusion and the goal. Establish `hj' : j ≤ n` using `(Finset.mem_range.mp hj).le`. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Use `hN j hj k` as an intermediate fact.

Establish `e1 : n * δ k = j * δ k + (n - j) * δ k`. Rewrite using `[← add_mul, Nat.add_sub_cancel' hj']`. Use linear arithmetic over natural numbers and integers. Establish `hsum : ∀ j ∈ Finset.range n, aeval y (Rf j * P (N - Nf j) * A ^ j * B ^ (n - j)) = (∏ k, y ⟨k, c k⟩ ^ N k) * aeval y B ^ n * ((algebraMap (chartRingZ y c) Ω) (p.coeff j) * t ^ j)`. Introduce `j hj`.

Establish `hj' : j ≤ n` using `(Finset.mem_range.mp hj).le`. Establish `hc : (algebraMap (chartRingZ y c) Ω) (p.coeff j) = ((p.coeff j : chartRingZ y c) : Ω)`. Both sides reduce to the same expression. Simplify using `only [P, map_mul, map_pow, map_prod, aeval_X, hRe j, ← htB, hc]`. Establish `e2 : (∏ k, y ⟨k, c k⟩ ^ Nf j k) * ∏ k, y ⟨k, c k⟩ ^ (N - Nf j) k = ∏ k, y ⟨k, c k⟩ ^ N k`.

Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← pow_add, Pi.sub_apply, Nat.add_sub_cancel' (hN j hj k)]`. Establish `e3 : aeval y B ^ n = aeval y B ^ j * aeval y B ^ (n - j)`. Rewrite using `[← pow_add, Nat.add_sub_cancel' hj']`.

Rewrite using `[e3, ← e2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hp' : t ^ n + ∑ i ∈ Finset.range n, (algebraMap (chartRingZ y c) Ω) (p.coeff i) * t ^ i = 0` using `hp`. Rewrite using `[map_add, map_sum, Finset.sum_congr rfl hsum, ← Finset.mul_sum]`. Simplify using `only [map_mul, map_pow, map_prod, aeval_X, ← htB]`.

Rewrite using `[mul_pow]`. Take the linear combination `((∏ k, y ⟨k, c k⟩ ^ N k) * aeval y B ^ n) * hp'`.
-/
theorem exists_rel (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) {t : Ω}
    (ht : IsIntegral (chartRingZ y c) t) {A B : MRing ι} {δ : K → ℕ} (hA : IsMultiHomog A δ)
    (hB : IsMultiHomog B δ) (htB : t * aeval y B = aeval y A) :
    ∃ (N : K → ℕ) (n : ℕ) (c' : ℕ → MRing ι),
      (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ N k) * A ^ n +
        ∑ j ∈ Finset.range n, c' j * A ^ j * B ^ (n - j) ∈ mCoordIdeal y := by
  classical
  obtain ⟨p, hpm, hp⟩ := ht
  set n := p.natDegree
  rw [hpm.as_sum] at hp
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at hp
  choose Nf Rf hRf hRe using fun i : ℕ =>
    LocalRep.exists_form_of_mem_chartRingZ y c hyc (p.coeff i).2
  set N : K → ℕ := ∑ i ∈ Finset.range n, Nf i
  have hN : ∀ i ∈ Finset.range n, ∀ k, Nf i k ≤ N k := by
    intro i hi k
    simp only [N, Finset.sum_apply]
    exact Finset.single_le_sum (f := fun j => Nf j k) (fun _ _ => Nat.zero_le _) hi
  set P : (K → ℕ) → MRing ι := fun f => ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ f k
  refine ⟨N, n, fun i => Rf i * P (N - Nf i), ?_⟩
  refine LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero y (d := N + n • δ) ?_ ?_
  · refine LocalRep.isMultiHomog_add
      (LocalRep.isMultiHomog_mul (LocalRep.isMultiHomog_chartMono c N) (isMultiHomog_pow' hA n))
      (isMultiHomog_sum' _ _ fun j hj => ?_)
    have h1 := LocalRep.isMultiHomog_mul (LocalRep.isMultiHomog_mul (LocalRep.isMultiHomog_mul
      (hRf j) (LocalRep.isMultiHomog_chartMono c (N - Nf j))) (isMultiHomog_pow' hA j))
      (isMultiHomog_pow' hB (n - j))
    convert h1 using 1
    have hj' : j ≤ n := (Finset.mem_range.mp hj).le
    funext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have := hN j hj k
    have e1 : n * δ k = j * δ k + (n - j) * δ k := by
      rw [← add_mul, Nat.add_sub_cancel' hj']
    omega
  · have hsum : ∀ j ∈ Finset.range n,
        aeval y (Rf j * P (N - Nf j) * A ^ j * B ^ (n - j)) =
          (∏ k, y ⟨k, c k⟩ ^ N k) * aeval y B ^ n *
            ((algebraMap (chartRingZ y c) Ω) (p.coeff j) * t ^ j) := by
      intro j hj
      have hj' : j ≤ n := (Finset.mem_range.mp hj).le
      have hc : (algebraMap (chartRingZ y c) Ω) (p.coeff j) = ((p.coeff j : chartRingZ y c) : Ω) :=
        rfl
      simp only [P, map_mul, map_pow, map_prod, aeval_X, hRe j, ← htB, hc]
      have e2 : (∏ k, y ⟨k, c k⟩ ^ Nf j k) * ∏ k, y ⟨k, c k⟩ ^ (N - Nf j) k =
          ∏ k, y ⟨k, c k⟩ ^ N k := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [← pow_add, Pi.sub_apply, Nat.add_sub_cancel' (hN j hj k)]
      have e3 : aeval y B ^ n = aeval y B ^ j * aeval y B ^ (n - j) := by
        rw [← pow_add, Nat.add_sub_cancel' hj']
      rw [e3, ← e2]
      ring
    have hp' : t ^ n + ∑ i ∈ Finset.range n, (algebraMap (chartRingZ y c) Ω) (p.coeff i) * t ^ i = 0 :=
      hp
    rw [map_add, map_sum, Finset.sum_congr rfl hsum, ← Finset.mul_sum]
    simp only [map_mul, map_pow, map_prod, aeval_X, ← htB]
    rw [mul_pow]
    linear_combination ((∏ k, y ⟨k, c k⟩ ^ N k) * aeval y B ^ n) * hp'

end Relation

end SectionOrderAtPoint

/- English proof (translation)
Introduce `K _ ι _ Ω _ y a τ s W G H dg dh hW hyW hs hG hH hdeg heval hGW hHW V hV`. Establish `hWp : W.IsPrime` using `hW.2.1.1`. Take `⟨hVmin, hVrel⟩` from `hV`. Establish `hVp : V.IsPrime` using `hVmin.1.1`. Establish `hWV : W ≤ V` using `le_sup_left.trans hVmin.1.2`.

Establish `hHV : H ∈ V` using `hVmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self H))`. Use `choose c hc using hVrel`. Establish `hyc : ∀ k, y ⟨k, c k⟩ ≠ 0`. Introduce `k h0`. Use `hc k (hWV (hyW ?_))` and prove the remaining obligations.

Conclude with `LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero y (LocalRep.isMultiHomog_X k (c k)) (by simp [h0])`. Establish `hmono : ∀ f : K → ℕ, (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ f k) ∉ V`. Introduce `f h`. Take `⟨k, -, hk⟩` from `(hVp.prod_mem_iff).mp h`. Conclude with `hc k (hVp.mem_of_pow_mem _ hk)`.

Use `set ep : K → ℕ := fun k => ((τ : ℤ) * a k).toNat`. Use `set em : K → ℕ := fun k => (-((τ : ℤ) * a k)).toNat`. Establish `hdeg' : em + dg = ep + dh`. Use function extensionality and compare the values at `k`. Use `hdeg k` as an intermediate fact.

Simplify using `only [Pi.add_apply, ep, em]`. Use linear arithmetic over natural numbers and integers. Use `set A : MRing ι := (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ em k) * G`. Use `set B : MRing ι := (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ ep k) * H`. Establish `hA : IsMultiHomog A (em + dg)` using `LocalRep.isMultiHomog_mul (LocalRep.isMultiHomog_chartMono c em) hG`.

Establish `hB : IsMultiHomog B (em + dg)` using `hdeg' ▸ LocalRep.isMultiHomog_mul (LocalRep.isMultiHomog_chartMono c ep) hH`. Use `set t := s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k))`. Establish `ht : IsIntegral (chartRingZ y c) t` using `hs c hyc`. Establish `hexp : ∀ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) * y ⟨k, c k⟩ ^ ep k = y ⟨k, c k⟩ ^ em k`. Introduce `k`.

Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k)]`. Use `congr 1`. Simplify using `only [ep, em]`. Use linear arithmetic over natural numbers and integers. Establish `htB : t * aeval y B = aeval y A`.

Simplify using `only [t, A, B, map_mul, map_prod, map_pow, aeval_X, heval]`. Rewrite using `[show ∀ u v x : Ω, s * u * (v * x) = (u * v) * (s * x) by intros; ring, ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun k _ => hexp k]`. Take `⟨N, n, c', hQ⟩` from `SectionOrderAtPoint.exists_rel y c hyc ht hA hB htB`. Establish `hQW` using `hyW hQ`. Establish `hAW : A ∉ W` using `fun h => (hWp.mem_or_mem h).elim (fun h => hmono em (hWV h)) hGW`.

Establish `hBW : B ∉ W` using `fun h => (hWp.mem_or_mem h).elim (fun h => hmono ep (hWV h)) hHW`. Establish `hBV : B ∈ V` using `V.mul_mem_left _ hHV`. Establish `hAV : A ∈ V` using `SectionOrderAtPoint.mem_of_rel hVp hBV (hmono N) c' (hWV hQW)`. Establish `hGV : G ∈ V` using `(hVp.mem_or_mem hAV).resolve_left (hmono em)`. Establish `hVG : V ∈ (W ⊔ Ideal.span {G}).minimalPrimes`.

Use `⟨⟨hVp, sup_le hWV ((Ideal.span_singleton_le_iff_mem _).mpr hGV)⟩, fun Q hQ hQV => ?_⟩` and prove the remaining obligations. Conclude with `(eq_of_le_of_mem_minimalPrimes hWp hVmin hQ.1 (le_sup_left.trans hQ.2) (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self G))) hGW hQV).ge`. Use `⟨⟨hVG, fun k => ⟨c k, hc k⟩⟩, ?_⟩` and prove the remaining obligations. Set `pV : PrimeSpectrum (MRing ι)` to `⟨V, hVp⟩`. Establish `hHfin : locLen (MRing ι ⧸ (W ⊔ Ideal.span {H})) pV ≠ ⊤` using `locLen_ne_top hVmin`.

Establish `hGfin : locLen (MRing ι ⧸ (W ⊔ Ideal.span {G})) pV ≠ ⊤` using `locLen_ne_top hVG`. Establish `eA : locLen (MRing ι ⧸ (W ⊔ Ideal.span {A})) pV = locLen (MRing ι ⧸ (W ⊔ Ideal.span {G})) pV`. Rewrite using `[locLen_mul hWp (fun h => hmono em (hWV h)) G, locLen_quot_eq_zero pV (hmono em), add_zero]`. Establish `eB : locLen (MRing ι ⧸ (W ⊔ Ideal.span {B})) pV = locLen (MRing ι ⧸ (W ⊔ Ideal.span {H})) pV`. Rewrite using `[locLen_mul hWp (fun h => hmono ep (hWV h)) H, locLen_quot_eq_zero pV (hmono ep), add_zero]`.

Establish `key` using `SectionOrderAtPoint.locLen_le_of_rel hWp hAW hBW pV hWV (hmono N) c' hQW (eB ▸ hHfin)`. Rewrite `key` using `[eA, eB]`. Use `ENat.toNat_le_toNat key hGfin` as an intermediate fact. Simplify `this` using `[multAt, hVp, locLen]`.
-/
theorem SectionOrderAtPoint.proof : SectionOrderAtPoint.Statement := by
  intro K _ ι _ Ω _ y a τ s W G H dg dh hW hyW hs hG hH hdeg heval hGW hHW V hV
  classical
  have hWp : W.IsPrime := hW.2.1.1
  obtain ⟨hVmin, hVrel⟩ := hV
  have hVp : V.IsPrime := hVmin.1.1
  have hWV : W ≤ V := le_sup_left.trans hVmin.1.2
  have hHV : H ∈ V := hVmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self H))
  choose c hc using hVrel
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    refine hc k (hWV (hyW ?_))
    exact LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero y (LocalRep.isMultiHomog_X k (c k))
      (by simp [h0])
  have hmono : ∀ f : K → ℕ, (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ f k) ∉ V := by
    intro f h
    obtain ⟨k, -, hk⟩ := (hVp.prod_mem_iff).mp h
    exact hc k (hVp.mem_of_pow_mem _ hk)
  set ep : K → ℕ := fun k => ((τ : ℤ) * a k).toNat
  set em : K → ℕ := fun k => (-((τ : ℤ) * a k)).toNat
  have hdeg' : em + dg = ep + dh := by
    funext k
    have := hdeg k
    simp only [Pi.add_apply, ep, em]
    omega
  set A : MRing ι := (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ em k) * G
  set B : MRing ι := (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ ep k) * H
  have hA : IsMultiHomog A (em + dg) :=
    LocalRep.isMultiHomog_mul (LocalRep.isMultiHomog_chartMono c em) hG
  have hB : IsMultiHomog B (em + dg) :=
    hdeg' ▸ LocalRep.isMultiHomog_mul (LocalRep.isMultiHomog_chartMono c ep) hH
  set t := s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k))
  have ht : IsIntegral (chartRingZ y c) t := hs c hyc
  have hexp : ∀ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) * y ⟨k, c k⟩ ^ ep k = y ⟨k, c k⟩ ^ em k := by
    intro k
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k)]
    congr 1
    simp only [ep, em]
    omega
  have htB : t * aeval y B = aeval y A := by
    simp only [t, A, B, map_mul, map_prod, map_pow, aeval_X, heval]
    rw [show ∀ u v x : Ω, s * u * (v * x) = (u * v) * (s * x) by intros; ring,
      ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun k _ => hexp k]
  obtain ⟨N, n, c', hQ⟩ := SectionOrderAtPoint.exists_rel y c hyc ht hA hB htB
  have hQW := hyW hQ
  have hAW : A ∉ W := fun h => (hWp.mem_or_mem h).elim (fun h => hmono em (hWV h)) hGW
  have hBW : B ∉ W := fun h => (hWp.mem_or_mem h).elim (fun h => hmono ep (hWV h)) hHW
  have hBV : B ∈ V := V.mul_mem_left _ hHV
  have hAV : A ∈ V := SectionOrderAtPoint.mem_of_rel hVp hBV (hmono N) c' (hWV hQW)
  have hGV : G ∈ V := (hVp.mem_or_mem hAV).resolve_left (hmono em)
  have hVG : V ∈ (W ⊔ Ideal.span {G}).minimalPrimes := by
    refine ⟨⟨hVp, sup_le hWV ((Ideal.span_singleton_le_iff_mem _).mpr hGV)⟩, fun Q hQ hQV => ?_⟩
    exact (eq_of_le_of_mem_minimalPrimes hWp hVmin hQ.1 (le_sup_left.trans hQ.2)
      (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self G))) hGW hQV).ge
  refine ⟨⟨hVG, fun k => ⟨c k, hc k⟩⟩, ?_⟩
  let pV : PrimeSpectrum (MRing ι) := ⟨V, hVp⟩
  have hHfin : locLen (MRing ι ⧸ (W ⊔ Ideal.span {H})) pV ≠ ⊤ := locLen_ne_top hVmin
  have hGfin : locLen (MRing ι ⧸ (W ⊔ Ideal.span {G})) pV ≠ ⊤ := locLen_ne_top hVG
  have eA : locLen (MRing ι ⧸ (W ⊔ Ideal.span {A})) pV =
      locLen (MRing ι ⧸ (W ⊔ Ideal.span {G})) pV := by
    rw [locLen_mul hWp (fun h => hmono em (hWV h)) G, locLen_quot_eq_zero pV (hmono em), add_zero]
  have eB : locLen (MRing ι ⧸ (W ⊔ Ideal.span {B})) pV =
      locLen (MRing ι ⧸ (W ⊔ Ideal.span {H})) pV := by
    rw [locLen_mul hWp (fun h => hmono ep (hWV h)) H, locLen_quot_eq_zero pV (hmono ep), add_zero]
  have key := SectionOrderAtPoint.locLen_le_of_rel hWp hAW hBW pV hWV (hmono N) c' hQW
    (eB ▸ hHfin)
  rw [eA, eB] at key
  have := ENat.toNat_le_toNat key hGfin
  simpa [multAt, hVp, locLen] using this

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

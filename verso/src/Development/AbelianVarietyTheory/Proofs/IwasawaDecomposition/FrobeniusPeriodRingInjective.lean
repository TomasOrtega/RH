import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineThetaEqZeroIffFontaineXiElementDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompatibleRootsOfUnityAndTiltPadic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AinfIsDomainAndAinfInvPInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineXiPowSaturatedQuotientCompleteStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCanonicalAcrisToBdRPlusStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalAcrisToBdRPlusUniqueEquivariantApproxStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisToBdRPlusInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveBcrisToBdRStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisMembershipSpanIffStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSpanPairPowSucc

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.FrobInj

section Pair
variable {R : Type} [CommRing R] (p w : R)

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.SpanPairPowSucc.mem_span_pair_pow_succ`. Consider the case `exact _root_.GlobalTheory.SpanPairPowSucc.mem_span_pair_pow_succ`. Consider the case `(apply _root_.GlobalTheory.SpanPairPowSucc.mem_span_pair_pow_succ <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.SpanPairPowSucc.mem_span_pair_pow_succ <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.SpanPairPowSucc.mem_span_pair_pow_succ <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.SpanPairPowSucc.mem_span_pair_pow_succ ..)`.
-/
theorem mem_pow_succ (k : ℕ) (x : R) (hx : x ∈ Ideal.span {p, w} ^ (k + 1)) :
    ∃ c G, G ∈ Ideal.span {p, w} ^ k ∧ x = w ^ (k + 1) * c + p * G := by
  first
  | exact @_root_.GlobalTheory.SpanPairPowSucc.mem_span_pair_pow_succ
  | exact _root_.GlobalTheory.SpanPairPowSucc.mem_span_pair_pow_succ
  | (apply _root_.GlobalTheory.SpanPairPowSucc.mem_span_pair_pow_succ <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpanPairPowSucc.mem_span_pair_pow_succ <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpanPairPowSucc.mem_span_pair_pow_succ <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpanPairPowSucc.mem_span_pair_pow_succ ..)

/- English proof (translation)
The claim follows from `Ideal.pow_mem_pow (Ideal.subset_span (by simp)) k`.
-/
theorem pow_mem (k : ℕ) : w ^ k ∈ Ideal.span {p, w} ^ k :=
  Ideal.pow_mem_pow (Ideal.subset_span (by simp)) k

/- English proof (translation)
The claim follows from `Ideal.pow_mem_pow (Ideal.subset_span (by simp)) k`.
-/
theorem pow_mem' (k : ℕ) : p ^ k ∈ Ideal.span {p, w} ^ k :=
  Ideal.pow_mem_pow (Ideal.subset_span (by simp)) k

variable {p w} (hp : ∀ x : R, p * x = 0 → x = 0) (hw : ∀ b : R, p ∣ w * b → p ∣ b)

include hw in
/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using h`. Consider the case `succ k ih => exact ih (hw _ (by rwa [← mul_assoc, ← pow_succ']))`.
-/
theorem dvd_of_pow (k : ℕ) (b : R) (h : p ∣ w ^ k * b) : p ∣ b := by
  induction k with
  | zero => simpa using h
  | succ k ih => exact ih (hw _ (by rwa [← mul_assoc, ← pow_succ']))

include hp hw in
/- English proof (translation)
Take `⟨c, G, hG, e⟩` from `mem_pow_succ p w k _ hx`. Take `⟨d, rfl⟩` from `dvd_of_pow hw (k + 1) c ⟨x - G, by linear_combination -e⟩`. Establish `: x = w ^ k * (w * d) + G` using `sub_eq_zero.1 (hp _ (by linear_combination e))`. Rewrite using `[this]`. Conclude with `add_mem (Ideal.mul_mem_right _ _ (pow_mem p w k)) hG`.
-/
theorem sat (k : ℕ) (x : R) (hx : p * x ∈ Ideal.span {p, w} ^ (k + 1)) : x ∈ Ideal.span {p, w} ^ k := by
  obtain ⟨c, G, hG, e⟩ := mem_pow_succ p w k _ hx
  obtain ⟨d, rfl⟩ := dvd_of_pow hw (k + 1) c ⟨x - G, by linear_combination -e⟩
  have : x = w ^ k * (w * d) + G := sub_eq_zero.1 (hp _ (by linear_combination e))
  rw [this]
  exact add_mem (Ideal.mul_mem_right _ _ (pow_mem p w k)) hG

include hp hw in

/- English proof (translation)
Proceed by induction on `N generalizing b with`. Consider the case `zero => intro i hi`. Use linear arithmetic over natural numbers and integers. Consider the case `succ N ih`. Establish `e0 : b * w ^ (l * (N + 1)) + F (N + 1) = (b * w ^ l + a N) * w ^ (l * N) + p * F N`.

Rewrite using `[hF]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[e0, show N + 1 + r = N + r + 1 by ring]`. Distinguish the cases in `hc : N + r + 1 ≤ l * N`. Establish `h1 : (b * w ^ l + a N) * w ^ (l * N) ∈ Ideal.span {p, w} ^ (N + r + 1)` using `Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hc (pow_mem p w _))`.

Establish `h2` using `sat hp hw _ _ ((Ideal.add_mem_iff_right _ h1).1 h)`. Introduce `i hi hl`. Break down `Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl` into its components or cases. Conclude with `ih 0 (by simpa using h2) i hi hl`. Establish `: l = 0`.

Rewrite `hl` using `[Nat.mul_succ]`. Use linear arithmetic over natural numbers and integers. Substitute `this` using the available equality. Use linear arithmetic over natural numbers and integers. Take `⟨e, he⟩` from `Nat.exists_eq_add_of_le (not_le.1 hc).le`.

Take `⟨c, G, hG, e1⟩` from `mem_pow_succ p w _ _ h`. Rewrite `e1` using `[he, pow_add]`. Take `⟨d, hd⟩` from `dvd_of_pow hw (l * N) (b * w ^ l + a N - w ^ e * c) ⟨G - F N, by linear_combination e1⟩`. Establish `h2 : d * w ^ (l * N) + F N = G` using `sub_eq_zero.1 (hp _ (by linear_combination e1 - w ^ (l * N) * hd))`. Introduce `i hi hl`.

Break down `Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl` into its components or cases. Conclude with `ih d (h2 ▸ hG) i hi hl`. Take `⟨e', rfl⟩ : ∃ e', e = l + e'` from `Nat.exists_eq_add_of_le (by`. Rewrite `hl` using `[Nat.mul_succ]`. Use the proof step `omega)`.

Conclude with `Ideal.mem_span_pair.2 ⟨d, w ^ e' * c - b, by linear_combination -hd⟩`.
-/
theorem coeff_mem (l r : ℕ) (a F : ℕ → R) (hF : ∀ N, F (N + 1) = a N * w ^ (l * N) + p * F N)
    (N : ℕ) (b : R) (h : b * w ^ (l * N) + F N ∈ Ideal.span {p, w} ^ (N + r)) :
    ∀ i < N, l * (i + 1) ≤ i + r + 1 → a i ∈ Ideal.span {p, w ^ l} := by
  induction N generalizing b with
  | zero => intro i hi; omega
  | succ N ih =>
    have e0 : b * w ^ (l * (N + 1)) + F (N + 1) = (b * w ^ l + a N) * w ^ (l * N) + p * F N := by
      rw [hF]; ring
    rw [e0, show N + 1 + r = N + r + 1 by ring] at h
    by_cases hc : N + r + 1 ≤ l * N
    · have h1 : (b * w ^ l + a N) * w ^ (l * N) ∈ Ideal.span {p, w} ^ (N + r + 1) :=
        Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hc (pow_mem p w _))
      have h2 := sat hp hw _ _ ((Ideal.add_mem_iff_right _ h1).1 h)
      intro i hi hl
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact ih 0 (by simpa using h2) i hi hl
      · have : l = 0 := by
          rw [Nat.mul_succ] at hl
          omega
        subst this
        omega
    · obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (not_le.1 hc).le
      obtain ⟨c, G, hG, e1⟩ := mem_pow_succ p w _ _ h
      rw [he, pow_add] at e1
      obtain ⟨d, hd⟩ := dvd_of_pow hw (l * N) (b * w ^ l + a N - w ^ e * c)
        ⟨G - F N, by linear_combination e1⟩
      have h2 : d * w ^ (l * N) + F N = G :=
        sub_eq_zero.1 (hp _ (by linear_combination e1 - w ^ (l * N) * hd))
      intro i hi hl
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact ih d (h2 ▸ hG) i hi hl
      · obtain ⟨e', rfl⟩ : ∃ e', e = l + e' := Nat.exists_eq_add_of_le (by
          rw [Nat.mul_succ] at hl
          omega)
        exact Ideal.mem_span_pair.2 ⟨d, w ^ e' * c - b, by linear_combination -hd⟩

end Pair

section Loc
variable {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {p w : R} {q : K}
  (hq : algebraMap R K p * q = 1)

include hq in
/- English proof (translation)
Proceed by induction on `hv using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Rewrite using `[Set.mem_singleton_iff.1 hx]`. Conclude with `⟨1, w, by simpa using pow_mem p w 1, by linear_combination (algebraMap R K w) * hq⟩`. Consider the case `algebraMap r => exact ⟨0, r, by simp, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨N, c, hc, e⟩` from `hx`. Take `⟨N', c', hc', e'⟩` from `hy`. Use `⟨N + N', c * p ^ N' + p ^ N * c', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_add]`.

Conclude with `add_mem (Ideal.mul_mem_mul hc (pow_mem' p w N')) (Ideal.mul_mem_mul (pow_mem' p w N) hc')`. Simplify using `only [map_add, map_mul, map_pow, ← e, ← e']`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul x y _ _ hx hy`. Take `⟨N, c, hc, e⟩` from `hx`.

Take `⟨N', c', hc', e'⟩` from `hy`. Use `⟨N + N', c * c', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_add]`. Conclude with `Ideal.mul_mem_mul hc hc'`. Simplify using `only [map_mul, ← e, ← e']`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem clear_den (v : K) (hv : v ∈ Algebra.adjoin R {algebraMap R K w * q}) :
    ∃ N : ℕ, ∃ c ∈ Ideal.span {p, w} ^ N, algebraMap R K p ^ N * v = algebraMap R K c := by
  induction hv using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.1 hx]
    exact ⟨1, w, by simpa using pow_mem p w 1, by linear_combination (algebraMap R K w) * hq⟩
  | algebraMap r => exact ⟨0, r, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, c, hc, e⟩ := hx
    obtain ⟨N', c', hc', e'⟩ := hy
    refine ⟨N + N', c * p ^ N' + p ^ N * c', ?_, ?_⟩
    · rw [pow_add]
      exact add_mem (Ideal.mul_mem_mul hc (pow_mem' p w N')) (Ideal.mul_mem_mul (pow_mem' p w N) hc')
    · simp only [map_add, map_mul, map_pow, ← e, ← e']; ring
  | mul x y _ _ hx hy =>
    obtain ⟨N, c, hc, e⟩ := hx
    obtain ⟨N', c', hc', e'⟩ := hy
    refine ⟨N + N', c * c', ?_, ?_⟩
    · rw [pow_add]
      exact Ideal.mul_mem_mul hc hc'
    · simp only [map_mul, ← e, ← e']; ring

variable (hp : ∀ x : R, p * x = 0 → x = 0) (hw : ∀ b : R, p ∣ w * b → p ∣ b)
  (hinj : Function.Injective (algebraMap R K)) (l : ℕ) (φ : R →+* R) (hφ : Function.Bijective φ)
  (hφp : φ p = p) (hφw : φ w = w ^ l) (ψ : K →+* K) (hψ : ∀ a, ψ (algebraMap R K a) = algebraMap R K (φ a))

include hq hp hw hinj hφ hφp hφw hψ in
/- English proof (translation)
Use `set P := algebraMap R K p with hP`. Establish `hψq : ψ q = q`. Use `congrArg ψ hq` as an intermediate fact. Rewrite `this` using `[map_mul, hP, hψ, hφp, map_one, ← hP]`. Take the linear combination `q * this - ψ q * hq`.

Set `F : ℕ → R` to `fun N => Nat.rec 0 (fun N x => φ (h.coeff N) * w ^ (l * N) + p * x) N`. Establish `hF : ∀ N, F (N + 1) = φ (h.coeff N) * w ^ (l * N) + p * F N` using `fun N => rfl`. Establish `hFK : ∀ N, algebraMap R K (F N) * P = P ^ N * ψ (∑ j ∈ Finset.range N, h.coeff j • (algebraMap R K w * q) ^ j)`. Introduce `N`. Proceed by induction on `N with`.

Consider the case `zero => simp [F]`. Consider the case `succ N ih`. Establish `: P ^ N * q ^ N = 1` using `by rw [← mul_pow, hq, one_pow]`. Rewrite using `[hF, Finset.sum_range_succ, map_add ψ, Algebra.smul_def, map_mul ψ, map_pow ψ, map_mul ψ, hψ, hψ, hψq, hφw, map_add, map_mul, map_mul, map_pow, map_pow, ← hP, mul_pow, ← pow_mul]`. Take the linear combination `P * ih - P * algebraMap R K (φ (h.coeff N)) * algebraMap R K w ^ (l * N) * this`.

Take `⟨N0, c, hc, ec⟩` from `clear_den hq v hv`. Establish `h1` using `hFK (N0 + (h.natDegree + i + 1))`. Rewrite `h1` using `[← Polynomial.aeval_eq_sum_range' (by omega), e]`. Establish `h2 : F (N0 + (h.natDegree + i + 1)) = c * p ^ (h.natDegree + i + 1 + l * (i + 1))`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[map_mul, map_pow, ← ec, ← hP]`. Take the linear combination `q * h1 - (algebraMap R K (F (N0 + (h.natDegree + i + 1))) - P ^ N0 * v * P ^ (h.natDegree + i + 1 + l * (i + 1))) * hq`. Establish `h3` using `coeff_mem hp hw l (l * (i + 1)) (fun j => φ (h.coeff j)) F hF (N0 + (h.natDegree + i + 1)) 0 (by`. Rewrite using `[zero_mul, zero_add, h2, add_assoc, pow_add _ N0]`. Conclude with `Ideal.mul_mem_mul hc (pow_mem' p w _)) i (by omega) (by omega)`.

Take `⟨α, β, h4⟩` from `Ideal.mem_span_pair.1 h3`. Take `⟨α, rfl⟩` from `hφ.2 α`. Take `⟨β, rfl⟩` from `hφ.2 β`. Conclude with `Ideal.mem_span_pair.2 ⟨α, β, hφ.1 (by rw [map_add, map_mul, map_mul, hφp, hφw, h4])⟩`.
-/
theorem coeff_mem_of_frob (h : Polynomial R) (i : ℕ) (v : K) (hv : v ∈ Algebra.adjoin R {algebraMap R K w * q})
    (e : ψ (Polynomial.aeval (algebraMap R K w * q) h) = algebraMap R K p ^ (l * (i + 1) + 1) * v) :
    h.coeff i ∈ Ideal.span {p, w} := by
  set P := algebraMap R K p with hP
  have hψq : ψ q = q := by
    have := congrArg ψ hq
    rw [map_mul, hP, hψ, hφp, map_one, ← hP] at this
    linear_combination q * this - ψ q * hq
  let F : ℕ → R := fun N => Nat.rec 0 (fun N x => φ (h.coeff N) * w ^ (l * N) + p * x) N
  have hF : ∀ N, F (N + 1) = φ (h.coeff N) * w ^ (l * N) + p * F N := fun N => rfl
  have hFK : ∀ N, algebraMap R K (F N) * P =
      P ^ N * ψ (∑ j ∈ Finset.range N, h.coeff j • (algebraMap R K w * q) ^ j) := by
    intro N
    induction N with
    | zero => simp [F]
    | succ N ih =>
      have : P ^ N * q ^ N = 1 := by rw [← mul_pow, hq, one_pow]
      rw [hF, Finset.sum_range_succ, map_add ψ, Algebra.smul_def, map_mul ψ, map_pow ψ, map_mul ψ, hψ, hψ, hψq,
        hφw, map_add, map_mul, map_mul, map_pow, map_pow, ← hP, mul_pow, ← pow_mul]
      linear_combination P * ih - P * algebraMap R K (φ (h.coeff N)) * algebraMap R K w ^ (l * N) * this
  obtain ⟨N0, c, hc, ec⟩ := clear_den hq v hv
  have h1 := hFK (N0 + (h.natDegree + i + 1))
  rw [← Polynomial.aeval_eq_sum_range' (by omega), e] at h1
  have h2 : F (N0 + (h.natDegree + i + 1)) = c * p ^ (h.natDegree + i + 1 + l * (i + 1)) := by
    apply hinj
    rw [map_mul, map_pow, ← ec, ← hP]
    linear_combination q * h1 - (algebraMap R K (F (N0 + (h.natDegree + i + 1))) -
      P ^ N0 * v * P ^ (h.natDegree + i + 1 + l * (i + 1))) * hq
  have h3 := coeff_mem hp hw l (l * (i + 1)) (fun j => φ (h.coeff j)) F hF (N0 + (h.natDegree + i + 1)) 0
    (by
      rw [zero_mul, zero_add, h2, add_assoc, pow_add _ N0]
      exact Ideal.mul_mem_mul hc (pow_mem' p w _)) i (by omega) (by omega)
  obtain ⟨α, β, h4⟩ := Ideal.mem_span_pair.1 h3
  obtain ⟨α, rfl⟩ := hφ.2 α
  obtain ⟨β, rfl⟩ := hφ.2 β
  exact Ideal.mem_span_pair.2 ⟨α, β, hφ.1 (by rw [map_add, map_mul, map_mul, hφp, hφw, h4])⟩

include hq hp hw hinj hφ hφp hφw hψ in
/- English proof (translation)
Establish `hZ : algebraMap R K w * q ∈ Algebra.adjoin R {algebraMap R K w * q}` using `Algebra.subset_adjoin rfl`. Establish `ht'` using `ht`. Rewrite `ht'` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨f, rfl⟩` from `ht'`. Establish `hf : ∀ i, f.coeff i ∈ Ideal.span {p, w}`.

Introduce `i`. Take `⟨u, hu, v, hv, e⟩` from `H (l * (i + 1) + 1)`. Rewrite `hu` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨g, rfl⟩` from `hu`. Use `coeff_mem_of_frob hq hp hw hinj l φ hφ hφp hφw ψ hψ (f + Polynomial.C p * g) i v hv (by rw [← e]; simp)` as an intermediate fact.

Rewrite `this` using `[Polynomial.coeff_add, Polynomial.coeff_C_mul]`. Conclude with `(Ideal.add_mem_iff_left _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))).1 this`. Express the relevant statement in the definitionally equal form `∃ m ∈ _, Polynomial.aeval _ f = _`. Rewrite using `[Polynomial.aeval_eq_sum_range]`. Use `Finset.sum_induction _ (fun t => ∃ m ∈ Algebra.adjoin R {algebraMap R K w * q}, t = algebraMap R K p * m) ?_ ⟨0, zero_mem _, by simp⟩ ?_` and prove the remaining obligations.

Introduce and unpack `_ _ ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩`. Conclude with `⟨m + m', add_mem hm hm', by ring⟩`. Introduce `i _`. Take `⟨α, β, h4⟩` from `Ideal.mem_span_pair.1 (hf i)`. Use `⟨(algebraMap R K α + algebraMap R K β * (algebraMap R K w * q)) * (algebraMap R K w * q) ^ i, mul_mem (add_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (Subalgebra.algebraMap_mem _ _) hZ)) (_root_.pow_mem hZ i), ?_⟩` and prove the remaining obligations.

Rewrite using `[Algebra.smul_def, ← h4, map_add, map_mul, map_mul]`. Take the linear combination `-(algebraMap R K β * algebraMap R K w * (algebraMap R K w * q) ^ i) * hq`.
-/
theorem dvd_of_frob (t : K) (ht : t ∈ Algebra.adjoin R {algebraMap R K w * q})
    (H : ∀ r : ℕ, ∃ u ∈ Algebra.adjoin R {algebraMap R K w * q}, ∃ v ∈ Algebra.adjoin R {algebraMap R K w * q},
      ψ (t + algebraMap R K p * u) = algebraMap R K p ^ r * v) :
    ∃ m ∈ Algebra.adjoin R {algebraMap R K w * q}, t = algebraMap R K p * m := by
  have hZ : algebraMap R K w * q ∈ Algebra.adjoin R {algebraMap R K w * q} := Algebra.subset_adjoin rfl
  have ht' := ht
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ht'
  obtain ⟨f, rfl⟩ := ht'
  have hf : ∀ i, f.coeff i ∈ Ideal.span {p, w} := by
    intro i
    obtain ⟨u, hu, v, hv, e⟩ := H (l * (i + 1) + 1)
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hu
    obtain ⟨g, rfl⟩ := hu
    have := coeff_mem_of_frob hq hp hw hinj l φ hφ hφp hφw ψ hψ (f + Polynomial.C p * g) i v hv
      (by rw [← e]; simp)
    rw [Polynomial.coeff_add, Polynomial.coeff_C_mul] at this
    exact (Ideal.add_mem_iff_left _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))).1 this
  change ∃ m ∈ _, Polynomial.aeval _ f = _
  rw [Polynomial.aeval_eq_sum_range]
  refine Finset.sum_induction _ (fun t => ∃ m ∈ Algebra.adjoin R {algebraMap R K w * q},
    t = algebraMap R K p * m) ?_ ⟨0, zero_mem _, by simp⟩ ?_
  · rintro _ _ ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
    exact ⟨m + m', add_mem hm hm', by ring⟩
  · intro i _
    obtain ⟨α, β, h4⟩ := Ideal.mem_span_pair.1 (hf i)
    refine ⟨(algebraMap R K α + algebraMap R K β * (algebraMap R K w * q)) * (algebraMap R K w * q) ^ i,
      mul_mem (add_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (Subalgebra.algebraMap_mem _ _) hZ))
        (_root_.pow_mem hZ i), ?_⟩
    rw [Algebra.smul_def, ← h4, map_add, map_mul, map_mul]
    linear_combination -(algebraMap R K β * algebraMap R K w * (algebraMap R K w * q) ^ i) * hq

include hq hp hw hinj hφ hφp hφw hψ in
/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact ⟨t, ht, by simp⟩`. Consider the case `succ k ih`. Take `⟨t', ht', rfl⟩` from `ih fun r => by`. Take `⟨u, hu, v, hv, e⟩` from `H r`.

Conclude with `⟨algebraMap R K p * u, mul_mem (Subalgebra.algebraMap_mem _ _) hu, v, hv, by rw [← e, pow_succ, mul_assoc]⟩`. Take `⟨m, hm, rfl⟩` from `dvd_of_frob hq hp hw hinj l φ hφ hφp hφw ψ hψ t' ht' fun r => by`. Take `⟨u, hu, v, hv, e⟩` from `H (k + r)`. Use `⟨u, hu, v, hv, ?_⟩` and prove the remaining obligations. Establish `: algebraMap R K p ^ k * q ^ k = 1` using `by rw [← mul_pow, hq, one_pow]`.

Simplify using `only [map_add, map_mul, map_pow, hψ, hφp] at e ⊢`. Take the linear combination `q ^ k * e - (ψ t' + algebraMap R K p * ψ u - algebraMap R K p ^ r * v) * this`. Conclude with `⟨m, hm, by ring⟩`.
-/
theorem pow_dvd_of_frob (k : ℕ) (t : K) (ht : t ∈ Algebra.adjoin R {algebraMap R K w * q})
    (H : ∀ r : ℕ, ∃ u ∈ Algebra.adjoin R {algebraMap R K w * q}, ∃ v ∈ Algebra.adjoin R {algebraMap R K w * q},
      ψ (t + algebraMap R K p ^ k * u) = algebraMap R K p ^ r * v) :
    ∃ m ∈ Algebra.adjoin R {algebraMap R K w * q}, t = algebraMap R K p ^ k * m := by
  induction k with
  | zero => exact ⟨t, ht, by simp⟩
  | succ k ih =>
    obtain ⟨t', ht', rfl⟩ := ih fun r => by
      obtain ⟨u, hu, v, hv, e⟩ := H r
      exact ⟨algebraMap R K p * u, mul_mem (Subalgebra.algebraMap_mem _ _) hu, v, hv,
        by rw [← e, pow_succ, mul_assoc]⟩
    obtain ⟨m, hm, rfl⟩ := dvd_of_frob hq hp hw hinj l φ hφ hφp hφw ψ hψ t' ht' fun r => by
      obtain ⟨u, hu, v, hv, e⟩ := H (k + r)
      refine ⟨u, hu, v, hv, ?_⟩
      have : algebraMap R K p ^ k * q ^ k = 1 := by rw [← mul_pow, hq, one_pow]
      simp only [map_add, map_mul, map_pow, hψ, hφp] at e ⊢
      linear_combination q ^ k * e - (ψ t' + algebraMap R K p * ψ u - algebraMap R K p ^ r * v) * this
    exact ⟨m, hm, by ring⟩

include hq in

/- English proof (translation)
Proceed by induction on `n generalizing m with`. Consider the case `zero => exact ⟨0, m, by simp⟩`. Consider the case `succ n ih`. Rewrite `hm` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨f, rfl⟩` from `hm`.

Take `⟨a, z, e⟩` from `ih (Polynomial.aeval (algebraMap R K x * q) f.divX) (Polynomial.aeval_mem_adjoin_singleton _ _)`. Use `⟨p ^ (n + 1) * f.coeff 0 + x * a, z, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (Polynomial.aeval (algebraMap R K x * q)) (Polynomial.divX_mul_X_add f)`. Express the relevant statement in the definitionally equal form `_ * Polynomial.aeval _ f = _`. Rewrite using `[← h]`.

Simplify using `only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]`. Take the linear combination `algebraMap R K x * e + algebraMap R K x * algebraMap R K p ^ n * Polynomial.aeval (algebraMap R K x * q) f.divX * hq`.
-/
theorem bounded_mod (x : R) (n : ℕ) (m : K) (hm : m ∈ Algebra.adjoin R {algebraMap R K x * q}) :
    ∃ (a : R) (z : K), algebraMap R K p ^ n * m = algebraMap R K a + algebraMap R K x ^ n * z := by
  induction n generalizing m with
  | zero => exact ⟨0, m, by simp⟩
  | succ n ih =>
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hm
    obtain ⟨f, rfl⟩ := hm
    obtain ⟨a, z, e⟩ := ih (Polynomial.aeval (algebraMap R K x * q) f.divX)
      (Polynomial.aeval_mem_adjoin_singleton _ _)
    refine ⟨p ^ (n + 1) * f.coeff 0 + x * a, z, ?_⟩
    have h := congrArg (Polynomial.aeval (algebraMap R K x * q)) (Polynomial.divX_mul_X_add f)
    change _ * Polynomial.aeval _ f = _
    rw [← h]
    simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    linear_combination algebraMap R K x * e + algebraMap R K x * algebraMap R K p ^ n *
      Polynomial.aeval (algebraMap R K x * q) f.divX * hq

/- English proof (translation)
Establish `h1 : P ^ n * q ^ n = 1` using `by rw [← mul_pow, hP, one_pow]`. Establish `key : y = algebraMap R K c * (algebraMap R K a * (algebraMap R K x * q)) ^ n`. Apply `hf.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[← mul_assoc, hc, hy, map_mul, mul_pow, mul_pow, mul_pow]`. Take the linear combination `-(algebraMap R K x ^ n * algebraMap R K a ^ n) * h1`.

Rewrite using `[key]`. Establish `hZ : algebraMap R K x * q ∈ Algebra.adjoin R {algebraMap R K x * q}` using `Algebra.subset_adjoin rfl`. Use `Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ c) (Subalgebra.pow_mem _ ?_ n)` and prove the remaining obligations. Conclude with `Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a) hZ`.
-/
theorem dividedPower_mem {P f y : K} (hP : P * q = 1) (x a c : R) (n : ℕ) (hf : IsUnit f)
    (hc : f * algebraMap R K c = P ^ n) (hy : f * y = algebraMap R K (x * a) ^ n) :
    y ∈ Algebra.adjoin R {algebraMap R K x * q} := by
  have h1 : P ^ n * q ^ n = 1 := by rw [← mul_pow, hP, one_pow]
  have key : y = algebraMap R K c * (algebraMap R K a * (algebraMap R K x * q)) ^ n := by
    apply hf.mul_left_cancel
    rw [← mul_assoc, hc, hy, map_mul, mul_pow, mul_pow, mul_pow]
    linear_combination -(algebraMap R K x ^ n * algebraMap R K a ^ n) * h1
  rw [key]
  have hZ : algebraMap R K x * q ∈ Algebra.adjoin R {algebraMap R K x * q} := Algebra.subset_adjoin rfl
  refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ c) (Subalgebra.pow_mem _ ?_ n)
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a) hZ

end Loc

end GlobalTheory.FrobInj

namespace GlobalTheory.MemLoc.PhiInj

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Take `⟨ζ, ε, h0, -, h1, h⟩` from `exists_zeta_eps l`. Use `⟨ε, ?_, ?_⟩` and prove the remaining obligations. Use `h 0` as an intermediate fact. Rewrite `this` using `[h0, map_one]`. Conclude with `Subtype.ext this`.

Introduce `hh`. Use `h 1` as an intermediate fact. Apply `h1` to reduce the goal to its premises. Apply `(algebraMap (Om l) ℂ_[l]).injective` to reduce the goal to its premises. Rewrite using `[← this, map_one]`.

Conclude with `congrArg Subtype.val hh`.
-/
theorem exists_eps : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, ε, h0, -, h1, h⟩ := exists_zeta_eps l
  refine ⟨ε, ?_, ?_⟩
  · have := h 0
    rw [h0, map_one] at this
    exact Subtype.ext this
  · intro hh
    have := h 1
    apply h1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← this, map_one]
    exact congrArg Subtype.val hh

/- English proof (translation)
Establish `h : (Per.φA l : Per.Ainf l → Per.Ainf l) = WittVector.map (frobenius (Per.Fl l) l)`. Use function extensionality and compare the values at `w`. Apply `WittVector.ext` to reduce the goal to its premises. Introduce `n`. Rewrite using `[GlobalTheory.RingIface.phiA_coeff, WittVector.map_coeff, frobenius_def]`.

Rewrite using `[h]`. Conclude with `⟨WittVector.map_injective _ (frobeniusEquiv (Per.Fl l) l).injective, WittVector.map_surjective _ (frobeniusEquiv (Per.Fl l) l).surjective⟩`.
-/
theorem φA_bijective : Function.Bijective (Per.φA l) := by
  have h : (Per.φA l : Per.Ainf l → Per.Ainf l) = WittVector.map (frobenius (Per.Fl l) l) := by
    funext w
    apply WittVector.ext
    intro n
    rw [GlobalTheory.RingIface.phiA_coeff, WittVector.map_coeff, frobenius_def]
  rw [h]
  exact ⟨WittVector.map_injective _ (frobeniusEquiv (Per.Fl l) l).injective,
    WittVector.map_surjective _ (frobeniusEquiv (Per.Fl l) l).surjective⟩

/- English proof (translation)
Establish `h0` using `WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff (p := l) x 0`. Establish `hI : (Finset.Iic 0 : Finset ℕ) = {0}`. Use extensionality with `i`. Simplify using the standard rewrite rules. Rewrite `h0` using `[hI, Finset.sum_singleton]`.

Take `⟨u, hu⟩ : (l : Per.Ainf l) ∣ x - Per.tm (x.coeff 0)` from `by simpa using h0`. Use `⟨Per.tm (x.coeff 0), u, by rw [← hu]; ring, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.RingIface.phiA_teich, map_pow]`.
-/
theorem exists_teich (x : Per.Ainf l) : ∃ w u : Per.Ainf l, x = w + (l : Per.Ainf l) * u ∧ Per.φA l w = w ^ l := by
  have h0 := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff (p := l) x 0
  have hI : (Finset.Iic 0 : Finset ℕ) = {0} := by
    ext i
    simp
  rw [hI, Finset.sum_singleton] at h0
  obtain ⟨u, hu⟩ : (l : Per.Ainf l) ∣ x - Per.tm (x.coeff 0) := by simpa using h0
  refine ⟨Per.tm (x.coeff 0), u, by rw [← hu]; ring, ?_⟩
  rw [GlobalTheory.RingIface.phiA_teich, map_pow]

/- English proof (translation)
Establish `H : Submodule.span (Per.Ainf l) {y : Per.AinfP l | ∃ n : ℕ, ((n.factorial : ℕ) : Per.AinfP l) * y = algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ^ n} ≤ Subalgebra.toSubmodule (Algebra.adjoin (Per.Ainf l) {algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) * q})`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `y ⟨n, hn⟩`. Take `⟨c, hc⟩` from `GlobalTheory.RingBasics.exists_pow_div_factorial l n`. Establish `h` using `congrArg (fun z => algebraMap (Per.Ainf l) (Per.AinfP l) (Per.zA l z)) hc`.

Simplify using `only [map_mul, map_natCast, map_pow] at h`. Establish `h' : ((n.factorial : ℕ) : Per.AinfP l) * algebraMap (Per.Ainf l) (Per.AinfP l) (Per.zA l c) = (l : Per.AinfP l) ^ n` using `h`. Conclude with `GlobalTheory.FrobInj.dividedPower_mem hq (xi e) 1 (Per.zA l c) n (GlobalTheory.RingBasics.isUnit_nat l n.factorial n.factorial_ne_zero) h' (by rw [mul_one]; exact hn)`. Conclude with `H ((GlobalTheory.T.acris_membership_span_iff l e he s).1 s.2)`.
-/
theorem acris0_le {e : Per.Fl l} (he : IsEps e) {q : Per.AinfP l} (hq : (l : Per.AinfP l) * q = 1)
    (s : Per.Acris0 l) :
    (s : Per.AinfP l) ∈ Algebra.adjoin (Per.Ainf l) {algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) * q} := by
  have H : Submodule.span (Per.Ainf l) {y : Per.AinfP l | ∃ n : ℕ,
        ((n.factorial : ℕ) : Per.AinfP l) * y = algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ^ n} ≤
      Subalgebra.toSubmodule
        (Algebra.adjoin (Per.Ainf l) {algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) * q}) := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨n, hn⟩
    obtain ⟨c, hc⟩ := GlobalTheory.RingBasics.exists_pow_div_factorial l n
    have h := congrArg (fun z => algebraMap (Per.Ainf l) (Per.AinfP l) (Per.zA l z)) hc
    simp only [map_mul, map_natCast, map_pow] at h
    have h' : ((n.factorial : ℕ) : Per.AinfP l) * algebraMap (Per.Ainf l) (Per.AinfP l) (Per.zA l c) =
        (l : Per.AinfP l) ^ n := h
    exact GlobalTheory.FrobInj.dividedPower_mem hq (xi e) 1 (Per.zA l c) n
      (GlobalTheory.RingBasics.isUnit_nat l n.factorial n.factorial_ne_zero) h' (by rw [mul_one]; exact hn)
  exact H ((GlobalTheory.T.acris_membership_span_iff l e he s).1 s.2)

noncomputable def phi0 : Per.Acris0 l →+* Per.Acris0 l :=
  (Per.extP (Per.φA l)).restrict _ _ (GlobalTheory.CrisMaps.frob_extends l).mem

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_phi0 (s : Per.Acris0 l) : (phi0 l s : Per.AinfP l) = Per.extP (Per.φA l) s := rfl

/- English proof (translation)
The claim follows from `(GlobalTheory.CrisMaps.phiA_extends l).env s`.
-/
theorem phiA_of (s : Per.Acris0 l) : phiA l (algebraMap (Per.Acris0 l) (Per.Acris l) s) =
    algebraMap (Per.Acris0 l) (Per.Acris l) (phi0 l s) :=
  (GlobalTheory.CrisMaps.phiA_extends l).env s

/- English proof (translation)
The claim follows from `GlobalTheory.RingIface.ev_alg l n x`.
-/
theorem ev_alg (n : ℕ) (x : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) x) = Ideal.Quotient.mk _ x :=
  GlobalTheory.RingIface.ev_alg l n x

/- English proof (translation)
The claim follows from `GlobalTheory.RingIface.ev_ext l y 0 h`.
-/
theorem eq_zero_of_ev (y : Per.BdRp l) (h : ∀ n, Per.ev l n y = Per.ev l n 0) : y = 0 :=
  GlobalTheory.RingIface.ev_ext l y 0 h

/- English proof (translation)
The claim follows from `GlobalTheory.RingIface.alg_mem_kerP l hx`.
-/
theorem mem_kerP (x : Per.Ainf l) (hx : Per.θ l x = 0) :
    algebraMap (Per.Ainf l) (Per.AinfP l) x ∈ Per.kerP l :=
  GlobalTheory.RingIface.alg_mem_kerP l hx

/- English proof (translation)
The claim follows from `GlobalTheory.CrisMaps.φB_phiA l x`.
-/
theorem φB_alg (x : Per.Acris l) : Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) x) =
    algebraMap (Per.Acris l) (Per.Bcris l) (phiA l x) :=
  GlobalTheory.CrisMaps.φB_phiA l x

section
set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

/- English proof (translation)
Take `⟨hd, -, hinj⟩` from `ainf_isDomain_and_injective l`. Take `⟨-, -, hdense, hdvd⟩` from `acris_basic l`. Take `⟨w, u, hw, hφw⟩` from `exists_teich l (xi e)`. Establish `hq' : algebraMap (Per.Ainf l) (Per.AinfP l) (l : Per.Ainf l) * q = 1` using `by rwa [map_natCast]`. Establish `hp : ∀ a : Per.Ainf l, (l : Per.Ainf l) * a = 0 → a = 0`.

Introduce `a ha`. Apply `hinj` to reduce the goal to its premises. Use `congrArg (algebraMap (Per.Ainf l) (Per.AinfP l)) ha` as an intermediate fact. Rewrite `this` using `[map_mul, map_zero]`. Rewrite using `[map_zero]`.

Take the linear combination `q * this - algebraMap (Per.Ainf l) (Per.AinfP l) a * hq'`. Establish `hsat : ∀ a : Per.Ainf l, xi e ∣ (l : Per.Ainf l) * a → xi e ∣ a`. Simplify using `using (GlobalTheory.T.fontaineXi_pow_saturated_quotient_complete l e he 1).1`. Establish `hx0 : xi e ≠ 0`. Introduce `h`.

Establish `h1` using `(theta_eq_zero_iff_xi_dvd l e he (mu e)).1 (by`. Rewrite using `[mu, map_sub, map_one, WittVector.fontaineTheta_teichmuller, he.1, sub_self])`. Rewrite `h1` using `[h, zero_dvd_iff, mu, sub_eq_zero]`. Establish `h2 : e = 1` using `by simpa using congrArg (fun y : Per.Ainf l => y.coeff 0) h1`. Apply `he.2` to reduce the goal to its premises.

Rewrite using `[h2, map_one, map_one]`. Establish `hreg : ∀ b : Per.Ainf l, (l : Per.Ainf l) ∣ w * b → (l : Per.Ainf l) ∣ b`. Introduce and unpack `b ⟨c, hc⟩`. Take `⟨d, hd⟩` from `hsat (c + u * b) ⟨b, by linear_combination -hc - b * hw⟩`. Conclude with `⟨d, mul_left_cancel₀ hx0 (by linear_combination hc + b * hw + (l : Per.Ainf l) * hd)⟩`.

Establish `hZ : algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) * q = algebraMap (Per.Ainf l) (Per.AinfP l) w * q + algebraMap (Per.Ainf l) (Per.AinfP l) u`. Rewrite using `[hw, map_add, map_mul]`. Take the linear combination `algebraMap (Per.Ainf l) (Per.AinfP l) u * hq'`. Establish `hM : Algebra.adjoin (Per.Ainf l) {algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) * q} = Algebra.adjoin (Per.Ainf l) {algebraMap (Per.Ainf l) (Per.AinfP l) w * q}`. Use `le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_le ?_)` and prove the remaining obligations.

Introduce and unpack `_ rfl`. Rewrite using `[hZ]`. Conclude with `add_mem (Algebra.subset_adjoin rfl) (Subalgebra.algebraMap_mem _ _)`. Introduce and unpack `_ rfl`. Rewrite using `[← sub_eq_iff_eq_add.2 hZ]`.

Conclude with `sub_mem (Algebra.subset_adjoin rfl) (Subalgebra.algebraMap_mem _ _)`. Establish `hle` using `acris0_le l he hq`. Rewrite `hle`, the goal using `[hM]`. Use `GlobalTheory.FrobInj.pow_dvd_of_frob hq' hp hreg hinj l (Per.φA l) (φA_bijective l) (map_natCast _ _) hφw (Per.extP (Per.φA l)) (GlobalTheory.RingBasics.awayMap_algebraMap₂ _) k s (hle s) (fun r => by` as an intermediate fact. Take `⟨s', z', rfl⟩` from `hdense z r`.

Establish `h1 : (l : Per.Acris l) ^ r ∣ algebraMap (Per.Acris0 l) (Per.Acris l) (phi0 l (s + (l : Per.Acris0 l) ^ k * s'))`. Use `⟨-((l : Per.Acris l) ^ k * phiA l z'), ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[hs]`. Rewrite using `[← phiA_of]`. Simplify using `only [map_add, map_mul, map_pow, map_natCast] at hx ⊢`.

Take the linear combination `hx`. Take `⟨v, hv⟩` from `(hdvd _ _).1 h1`. Use `⟨s', hle s', v, hle v, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg Subtype.val hv`. Rewrite `h2` using `[coe_phi0]`.

Rewrite using `[map_natCast]`. Simplify using `using h2)`. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.
-/
theorem approx_mem {e : Per.Fl l} (he : IsEps e) {q : Per.AinfP l} (hq : (l : Per.AinfP l) * q = 1)
    (x : Per.Acris l) (hx : phiA l x = 0) (k : ℕ) (s : Per.Acris0 l) (z : Per.Acris l)
    (hs : x = algebraMap (Per.Acris0 l) (Per.Acris l) s + (l : Per.Acris l) ^ k * z) :
    ∃ m ∈ Algebra.adjoin (Per.Ainf l) {algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) * q},
      (s : Per.AinfP l) = (l : Per.AinfP l) ^ k * m := by
  obtain ⟨hd, -, hinj⟩ := ainf_isDomain_and_injective l
  obtain ⟨-, -, hdense, hdvd⟩ := acris_basic l
  obtain ⟨w, u, hw, hφw⟩ := exists_teich l (xi e)
  have hq' : algebraMap (Per.Ainf l) (Per.AinfP l) (l : Per.Ainf l) * q = 1 := by rwa [map_natCast]
  have hp : ∀ a : Per.Ainf l, (l : Per.Ainf l) * a = 0 → a = 0 := by
    intro a ha
    apply hinj
    have := congrArg (algebraMap (Per.Ainf l) (Per.AinfP l)) ha
    rw [map_mul, map_zero] at this
    rw [map_zero]
    linear_combination q * this - algebraMap (Per.Ainf l) (Per.AinfP l) a * hq'
  have hsat : ∀ a : Per.Ainf l, xi e ∣ (l : Per.Ainf l) * a → xi e ∣ a := by
    simpa using (GlobalTheory.T.fontaineXi_pow_saturated_quotient_complete l e he 1).1
  have hx0 : xi e ≠ 0 := by
    intro h
    have h1 := (theta_eq_zero_iff_xi_dvd l e he (mu e)).1 (by
      rw [mu, map_sub, map_one, WittVector.fontaineTheta_teichmuller, he.1, sub_self])
    rw [h, zero_dvd_iff, mu, sub_eq_zero] at h1
    have h2 : e = 1 := by simpa using congrArg (fun y : Per.Ainf l => y.coeff 0) h1
    apply he.2
    rw [h2, map_one, map_one]
  have hreg : ∀ b : Per.Ainf l, (l : Per.Ainf l) ∣ w * b → (l : Per.Ainf l) ∣ b := by
    rintro b ⟨c, hc⟩
    obtain ⟨d, hd⟩ := hsat (c + u * b) ⟨b, by linear_combination -hc - b * hw⟩
    exact ⟨d, mul_left_cancel₀ hx0 (by linear_combination hc + b * hw + (l : Per.Ainf l) * hd)⟩
  have hZ : algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) * q =
      algebraMap (Per.Ainf l) (Per.AinfP l) w * q + algebraMap (Per.Ainf l) (Per.AinfP l) u := by
    rw [hw, map_add, map_mul]
    linear_combination algebraMap (Per.Ainf l) (Per.AinfP l) u * hq'
  have hM : Algebra.adjoin (Per.Ainf l) {algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) * q} =
      Algebra.adjoin (Per.Ainf l) {algebraMap (Per.Ainf l) (Per.AinfP l) w * q} := by
    refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_le ?_)
    · rintro _ rfl
      rw [hZ]
      exact add_mem (Algebra.subset_adjoin rfl) (Subalgebra.algebraMap_mem _ _)
    · rintro _ rfl
      rw [← sub_eq_iff_eq_add.2 hZ]
      exact sub_mem (Algebra.subset_adjoin rfl) (Subalgebra.algebraMap_mem _ _)
  have hle := acris0_le l he hq
  rw [hM] at hle ⊢
  have := GlobalTheory.FrobInj.pow_dvd_of_frob hq' hp hreg hinj l (Per.φA l) (φA_bijective l) (map_natCast _ _) hφw
    (Per.extP (Per.φA l)) (GlobalTheory.RingBasics.awayMap_algebraMap₂ _) k s (hle s) (fun r => by
      obtain ⟨s', z', rfl⟩ := hdense z r
      have h1 : (l : Per.Acris l) ^ r ∣
          algebraMap (Per.Acris0 l) (Per.Acris l) (phi0 l (s + (l : Per.Acris0 l) ^ k * s')) := by
        refine ⟨-((l : Per.Acris l) ^ k * phiA l z'), ?_⟩
        rw [hs] at hx
        rw [← phiA_of]
        simp only [map_add, map_mul, map_pow, map_natCast] at hx ⊢
        linear_combination hx
      obtain ⟨v, hv⟩ := (hdvd _ _).1 h1
      refine ⟨s', hle s', v, hle v, ?_⟩
      have h2 := congrArg Subtype.val hv
      rw [coe_phi0] at h2
      rw [map_natCast]
      simpa using h2)
  rwa [map_natCast] at this

/- English proof (translation)
Take `⟨e, he⟩` from `exists_eps l`. Take `⟨q, hq⟩` from `(GlobalTheory.RingBasics.isUnit_l l).exists_right_inv`. Establish `hq' : algebraMap (Per.Ainf l) (Per.AinfP l) (l : Per.Ainf l) * q = 1` using `by rwa [map_natCast]`. Take `⟨j, hj⟩` from `GlobalTheory.T.exists_canonical_acris_to_bdRPlus l`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `x hx`. Apply `GlobalTheory.T.acrisToBdRPlus_injective l j hj` to reduce the goal to its premises. Rewrite using `[map_zero]`. Use `eq_zero_of_ev l _ fun n => (GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l j hj).2.2 n x 0 fun r => ?_` and prove the remaining obligations. Take `⟨s, z, hs⟩` from `(acris_basic l).2.2.1 x (r + n)`.

Take `⟨m, hm, e1⟩` from `approx_mem l he hq x hx (r + n) s z hs`. Take `⟨a, y, e2⟩` from `GlobalTheory.FrobInj.bounded_mod hq' (xi e) n m hm`. Use `⟨s, (l : Per.Acris l) ^ n * z, -a, by rw [hs]; ring, ?_⟩` and prove the remaining obligations. Establish `e3 : ((l : Per.BdRp l) ^ r * aDp l (-a)) = algebraMap (Per.AinfP l) (Per.BdRp l) ((l : Per.AinfP l) ^ r * algebraMap (Per.Ainf l) (Per.AinfP l) (-a))`. Rewrite using `[map_mul, map_pow, map_natCast]`.

Both sides reduce to the same expression. Rewrite using `[e3, zero_sub, ← map_neg, ev_alg, ev_alg, Ideal.Quotient.eq]`. Establish `e4 : -(s : Per.AinfP l) - (l : Per.AinfP l) ^ r * algebraMap (Per.Ainf l) (Per.AinfP l) (-a) = algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ^ n * (-((l : Per.AinfP l) ^ r * y))`. Rewrite `e2` using `[map_natCast]`. Rewrite using `[e1, map_neg]`.

Take the linear combination `-(l : Per.AinfP l) ^ r * e2`. Rewrite using `[e4]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (mem_kerP l _ ((theta_eq_zero_iff_xi_dvd l e he _).2 dvd_rfl)) n)`.
-/
theorem phiA_injective : Function.Injective (phiA l) := by
  obtain ⟨e, he⟩ := exists_eps l
  obtain ⟨q, hq⟩ := (GlobalTheory.RingBasics.isUnit_l l).exists_right_inv
  have hq' : algebraMap (Per.Ainf l) (Per.AinfP l) (l : Per.Ainf l) * q = 1 := by rwa [map_natCast]
  obtain ⟨j, hj⟩ := GlobalTheory.T.exists_canonical_acris_to_bdRPlus l
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply GlobalTheory.T.acrisToBdRPlus_injective l j hj
  rw [map_zero]
  refine eq_zero_of_ev l _ fun n => (GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l j hj).2.2 n x 0 fun r => ?_
  obtain ⟨s, z, hs⟩ := (acris_basic l).2.2.1 x (r + n)
  obtain ⟨m, hm, e1⟩ := approx_mem l he hq x hx (r + n) s z hs
  obtain ⟨a, y, e2⟩ := GlobalTheory.FrobInj.bounded_mod hq' (xi e) n m hm
  refine ⟨s, (l : Per.Acris l) ^ n * z, -a, by rw [hs]; ring, ?_⟩
  have e3 : ((l : Per.BdRp l) ^ r * aDp l (-a)) = algebraMap (Per.AinfP l) (Per.BdRp l)
      ((l : Per.AinfP l) ^ r * algebraMap (Per.Ainf l) (Per.AinfP l) (-a)) := by
    rw [map_mul, map_pow, map_natCast]
    rfl
  rw [e3, zero_sub, ← map_neg, ev_alg, ev_alg, Ideal.Quotient.eq]
  have e4 : -(s : Per.AinfP l) - (l : Per.AinfP l) ^ r * algebraMap (Per.Ainf l) (Per.AinfP l) (-a) =
      algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ^ n * (-((l : Per.AinfP l) ^ r * y)) := by
    rw [map_natCast] at e2
    rw [e1, map_neg]
    linear_combination -(l : Per.AinfP l) ^ r * e2
  rw [e4]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow
    (mem_kerP l _ ((theta_eq_zero_iff_xi_dvd l e he _).2 dvd_rfl)) n)

/- English proof (translation)
Take `⟨j, hj⟩` from `GlobalTheory.T.exists_canonical_acris_to_bdRPlus l`. Take `⟨ι, hι, -⟩` from `GlobalTheory.T.exists_injective_bcris_to_bdR l j hj`. Introduce `x y h`. Apply `GlobalTheory.T.acrisToBdRPlus_injective l j hj` to reduce the goal to its premises. Apply `(GlobalTheory.T.bdRPlus_isDomain_bdR_isField l).2.1` to reduce the goal to its premises.

Rewrite using `[← hι, ← hι, h]`.
-/
theorem algebraMap_acris_bcris_injective : Function.Injective (algebraMap (Per.Acris l) (Per.Bcris l)) := by
  obtain ⟨j, hj⟩ := GlobalTheory.T.exists_canonical_acris_to_bdRPlus l
  obtain ⟨ι, hι, -⟩ := GlobalTheory.T.exists_injective_bcris_to_bdR l j hj
  intro x y h
  apply GlobalTheory.T.acrisToBdRPlus_injective l j hj
  apply (GlobalTheory.T.bdRPlus_isDomain_bdR_isField l).2.1
  rw [← hι, ← hι, h]

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `b hb`. Take `⟨e, he, hne⟩` from `GlobalTheory.CrisLoc.exists_root_ne_one l`. Take `⟨n, x, h⟩` from `GlobalTheory.CrisLoc.exists_mul_pow_eq l e he hne b`. Establish `h1` using `congrArg (Per.φB l) h`.

Rewrite `h1` using `[map_mul, hb, zero_mul, φB_alg, ← map_zero (algebraMap (Per.Acris l) (Per.Bcris l)), ← map_zero (phiA l)]`. Establish `h2` using `phiA_injective l (algebraMap_acris_bcris_injective l h1)`. Rewrite `h` using `[← h2, map_zero]`. Conclude with `((GlobalTheory.CrisLoc.unit_of_root l e he hne).pow n).mul_left_eq_zero.1 h`.
-/
theorem φB_inj : Function.Injective (Per.φB l) := by
  rw [injective_iff_map_eq_zero]
  intro b hb
  obtain ⟨e, he, hne⟩ := GlobalTheory.CrisLoc.exists_root_ne_one l
  obtain ⟨n, x, h⟩ := GlobalTheory.CrisLoc.exists_mul_pow_eq l e he hne b
  have h1 := congrArg (Per.φB l) h
  rw [map_mul, hb, zero_mul, φB_alg, ← map_zero (algebraMap (Per.Acris l) (Per.Bcris l)),
    ← map_zero (phiA l)] at h1
  have h2 := phiA_injective l (algebraMap_acris_bcris_injective l h1)
  rw [← h2, map_zero] at h
  exact ((GlobalTheory.CrisLoc.unit_of_root l e he hne).pow n).mul_left_eq_zero.1 h

end

end GlobalTheory.MemLoc.PhiInj

/- English proof (translation)
Introduce `l _` and use `GlobalTheory.MemLoc.PhiInj.φB_inj l`.
-/
theorem GlobalTheory.MemLoc.phiB_injective : ∀ (l : ℕ) [Fact l.Prime], Function.Injective (Per.φB l) :=
  fun l _ => GlobalTheory.MemLoc.PhiInj.φB_inj l

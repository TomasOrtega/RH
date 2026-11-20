import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import GroundTheory.HeightsAndTheta.Heights.Intersections.UniquenessDegreeFormOfIntersectionForm
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

open Classical in

def killBlocks (S : Set K) : MRing ι →ₐ[ℤ] MRing ι :=
  aeval fun p => if p.1 ∈ S then 0 else X p

omit [Fintype K] [∀ k, Fintype (ι k)] in
open Classical in

/- English proof (translation)
Rewrite using `[killBlocks, aeval_X]`.
-/
theorem killBlocks_X (S : Set K) (p : Σ k, ι k) :
    killBlocks S (X p : MRing ι) = if p.1 ∈ S then 0 else X p := by
  rw [killBlocks, aeval_X]

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Rewrite using `[killBlocks, aeval_monomial, monomial_eq, algebraMap_eq]`. Use `congr 1`. Use `Finsupp.prod_congr fun p hp => ?_` and prove the remaining obligations. Rewrite using `[if_neg (h p hp)]`.
-/
theorem killBlocks_monomial_of_forall (S : Set K) (m : (Σ k, ι k) →₀ ℕ) (c : ℤ)
    (h : ∀ p ∈ m.support, p.1 ∉ S) : killBlocks S (monomial m c : MRing ι) = monomial m c := by
  rw [killBlocks, aeval_monomial, monomial_eq, algebraMap_eq]
  congr 1
  refine Finsupp.prod_congr fun p hp => ?_
  rw [if_neg (h p hp)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Rewrite using `[killBlocks, aeval_monomial, Finsupp.prod]`. Use `mul_eq_zero_of_right _ (Finset.prod_eq_zero hp ?_)` and prove the remaining obligations. Rewrite using `[if_pos hS, zero_pow (Finsupp.mem_support_iff.mp hp)]`.
-/
theorem killBlocks_monomial_of_mem (S : Set K) (m : (Σ k, ι k) →₀ ℕ) (c : ℤ) (p : Σ k, ι k)
    (hp : p ∈ m.support) (hS : p.1 ∈ S) : killBlocks S (monomial m c : MRing ι) = 0 := by
  rw [killBlocks, aeval_monomial, Finsupp.prod]
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hp ?_)
  rw [if_pos hS, zero_pow (Finsupp.mem_support_iff.mp hp)]

/- English proof (translation)
Distinguish the cases in `ha : ∀ k ∈ S, a k = 0`. Use `left`. Rewrite using `[f.as_sum, map_sum]`. Use `Finset.sum_congr rfl fun m hm => killBlocks_monomial_of_forall S m _ ?_` and prove the remaining obligations. Introduce and unpack `⟨k, i⟩ hp hkS`.

Establish `h1` using `hf m hm k`. Rewrite `h1` using `[ha k hkS]`. Establish `h2 : m ⟨k, i⟩ ≤ ∑ j, m ⟨k, j⟩` using `Finset.single_le_sum (f := fun j => m ⟨k, j⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)`. Conclude with `Finsupp.mem_support_iff.mp hp (by omega)`. Use `right push Not at ha`.

Take `⟨k, hkS, hak⟩` from `ha`. Rewrite using `[f.as_sum, map_sum]`. Use `Finset.sum_eq_zero fun m hm => ?_` and prove the remaining obligations. Establish `h1` using `hf m hm k`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, m ⟨k, i⟩ ≠ 0 := by`.

Assume the negation of the conclusion as `h0`. Use `push Not at h0`. Establish `: ∑ j, m ⟨k, j⟩ = 0` using `Finset.sum_eq_zero fun j _ => h0 j`. Use linear arithmetic over natural numbers and integers. Conclude with `killBlocks_monomial_of_mem S m _ ⟨k, i⟩ (Finsupp.mem_support_iff.mpr hi) hkS`.
-/
theorem killBlocks_of_isMultiHomog (S : Set K) {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    killBlocks S f = f ∨ killBlocks S f = 0 := by
  by_cases ha : ∀ k ∈ S, a k = 0
  · left
    rw [f.as_sum, map_sum]
    refine Finset.sum_congr rfl fun m hm => killBlocks_monomial_of_forall S m _ ?_
    rintro ⟨k, i⟩ hp hkS
    have h1 := hf m hm k
    rw [ha k hkS] at h1
    have h2 : m ⟨k, i⟩ ≤ ∑ j, m ⟨k, j⟩ :=
      Finset.single_le_sum (f := fun j => m ⟨k, j⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact Finsupp.mem_support_iff.mp hp (by omega)
  · right
    push Not at ha
    obtain ⟨k, hkS, hak⟩ := ha
    rw [f.as_sum, map_sum]
    refine Finset.sum_eq_zero fun m hm => ?_
    have h1 := hf m hm k
    obtain ⟨i, hi⟩ : ∃ i, m ⟨k, i⟩ ≠ 0 := by
      by_contra h0
      push Not at h0
      have : ∑ j, m ⟨k, j⟩ = 0 := Finset.sum_eq_zero fun j _ => h0 j
      omega
    exact killBlocks_monomial_of_mem S m _ ⟨k, i⟩ (Finsupp.mem_support_iff.mpr hi) hkS

/- English proof (translation)
Take `⟨T, hT, rfl⟩` from `hP`. Use `Ideal.span_le.mpr fun f hf => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `hT f hf`. Rewrite using `[SetLike.mem_coe, Ideal.mem_comap]`. Apply the tactic sequence `rcases killBlocks_of_isMultiHomog S ha with h | h <;> rw [h]`.

Conclude with `Ideal.subset_span hf`. Conclude with `Ideal.zero_mem _`.
-/
theorem le_comap_killBlocks {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (S : Set K) :
    P ≤ P.comap (killBlocks S) := by
  obtain ⟨T, hT, rfl⟩ := hP
  refine Ideal.span_le.mpr fun f hf => ?_
  obtain ⟨a, ha⟩ := hT f hf
  rw [SetLike.mem_coe, Ideal.mem_comap]
  rcases killBlocks_of_isMultiHomog S ha with h | h <;> rw [h]
  · exact Ideal.subset_span hf
  · exact Ideal.zero_mem _

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Use `MvPolynomial.algHom_ext fun p => ?_` and prove the remaining obligations. Rewrite using `[AlgHom.comp_apply, killBlocks_X, killBlocks_X]`. Distinguish the cases in `hp : p.1 ∈ S`. Rewrite using `[if_pos hp, map_zero, if_pos (h hp)]`. Rewrite using `[if_neg hp, killBlocks_X]`.
-/
theorem killBlocks_comp {S S' : Set K} (h : S ⊆ S') :
    (killBlocks S').comp (killBlocks S) = (killBlocks S' : MRing ι →ₐ[ℤ] MRing ι) := by
  refine MvPolynomial.algHom_ext fun p => ?_
  rw [AlgHom.comp_apply, killBlocks_X, killBlocks_X]
  by_cases hp : p.1 ∈ S
  · rw [if_pos hp, map_zero, if_pos (h hp)]
  · rw [if_neg hp, killBlocks_X]

/- English proof (translation)
Introduce `f hf`. Rewrite `hf`, the goal using `[Ideal.mem_comap]`. Establish `e : killBlocks S' f = killBlocks S' (killBlocks S f)`. Rewrite using `[← AlgHom.comp_apply, killBlocks_comp h]`. Rewrite using `[e]`.

Conclude with `le_comap_killBlocks hP S' hf`.
-/
theorem comap_killBlocks_mono {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {S S' : Set K}
    (h : S ⊆ S') : P.comap (killBlocks S) ≤ P.comap (killBlocks S') := by
  intro f hf
  rw [Ideal.mem_comap] at hf ⊢
  have e : killBlocks S' f = killBlocks S' (killBlocks S f) := by
    rw [← AlgHom.comp_apply, killBlocks_comp h]
  rw [e]
  exact le_comap_killBlocks hP S' hf

/- English proof (translation)
Introduce `K _ ι _ P hP`. Take `⟨_, ⟨hPp, hPh, hPr⟩, hhor, hdim⟩` from `hP`. Use `hPp` as an intermediate fact. Use `set m := Fintype.card K with hm`. Set `e : K ≃ Fin m` to `Fintype.equivFin K`.

Set `S : ℕ → Set K` to `fun n => {k | (e k : ℕ) < n}`. Set `Q : ℕ → Ideal (MRing ι)` to `fun n => P.comap (killBlocks (S n))`. Set `Q2 : Ideal (MRing ι)` to `RingHom.ker ((Int.castRingHom (ZMod 2)).comp (constantCoeff : MRing ι →+* ℤ))`. Establish `hQp : ∀ n, (Q n).IsPrime` using `fun n => Ideal.IsPrime.comap _`. Establish `hQ2p : Q2.IsPrime` using `RingHom.ker_isPrime _`.

Establish `hstep : ∀ n, n < m → Q n < Q (n + 1)`. Introduce `n hn`. Take `⟨i, hi⟩` from `hPr (e.symm ⟨n, hn⟩)`. Use `SetLike.lt_iff_le_and_exists.mpr ⟨comap_killBlocks_mono hPh fun k hk => Nat.lt_succ_of_lt hk, X ⟨e.symm ⟨n, hn⟩, i⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show killBlocks _ _ ∈ P`.

Rewrite using `[killBlocks_X, if_pos (by simp [S])]`. Conclude with `P.zero_mem`. Introduce `h2`. Express the relevant statement in the definitionally equal form `killBlocks _ _ ∈ P at h2`. Rewrite `h2` using `[killBlocks_X, if_neg (by simp [S])]`.

Conclude with `hi h2`. Establish `hall : ∀ f : MRing ι, killBlocks (S m) f = C (constantCoeff f)`. Introduce `f`. Establish `: killBlocks (S m) = aeval (0 : (Σ k, ι k) → MRing ι)`. Use `MvPolynomial.algHom_ext fun p => ?_` and prove the remaining obligations.

Rewrite using `[killBlocks_X, if_pos (by simp [S]), aeval_X]`. Both sides reduce to the same expression. Rewrite using `[this, aeval_zero, algebraMap_eq]`. Establish `hQm : ∀ f, f ∈ Q m ↔ constantCoeff f = 0`. Introduce `f`.

Express the relevant statement in the definitionally equal form `killBlocks (S m) f ∈ P ↔ _`. Rewrite using `[hall]`. Express the relevant statement in the definitionally equal form `constantCoeff f ∈ P.comap (C : ℤ →+* MRing ι) ↔ _`. Rewrite using `[hhor, Ideal.mem_bot]`. Establish `hstep2 : Q m < Q2`.

Use `SetLike.lt_iff_le_and_exists.mpr ⟨fun f hf => ?_, C 2, ?_, fun h2 => ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.mem_ker, RingHom.comp_apply, (hQm f).mp hf, map_zero]`. Rewrite using `[RingHom.mem_ker, RingHom.comp_apply, constantCoeff_C]`. Both sides reduce to the same expression. Use `(hQm _).mp h2` as an intermediate fact.

Rewrite `this` using `[constantCoeff_C]`. Evaluate the numerical expressions using `at this`. Set `T : ℕ → Ideal (MRing ι)` to `fun n => if n ≤ m then Q n else Q2`. Establish `hTp : ∀ n, (T n).IsPrime`. Introduce `n`.

Simplify using `only [T]`. Use `split_ifs`. Use `exacts [hQp n, hQ2p]`. Establish `hPT : ∀ n, P ≤ T n`. Introduce `n`.

Simplify using `only [T]`. Use `split_ifs`. Conclude with `le_comap_killBlocks hPh _`. Conclude with `(le_comap_killBlocks hPh _).trans hstep2.le`. Establish `hTlt : ∀ n, n ≤ m → T n < T (n + 1)`.

Introduce `n hn`. Simplify using `only [T]`. Rewrite using `[if_pos hn]`. Break down `hn.lt_or_eq with h | h` into its components or cases. Rewrite using `[if_pos (Nat.succ_le_of_lt h)]`.

Conclude with `hstep n h`. Rewrite using `[if_neg (by omega), h]`. Conclude with `hstep2`. Set `g : Fin (m + 2) → PrimeSpectrum.zeroLocus (R` to `MRing ι) (P : Set (MRing ι)) := fun j => ⟨⟨T j, hTp j⟩, hPT j⟩`. Establish `hg : StrictMono g`.

Use `Fin.strictMono_iff_lt_succ.mpr fun i => ?_` and prove the remaining obligations. Conclude with `hTlt i (Nat.lt_succ_iff.mp i.isLt)`. Establish `hlen` using `Order.LTSeries.length_le_krullDim (LTSeries.mk (m + 1) g hg)`. Rewrite `hlen` using `[← ringKrullDim_quotient, hdim]`. Establish `h3 : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ ((0 + m : ℕ) : WithBot ℕ∞)` using `hlen`.

Establish `h4 : m + 1 ≤ 0 + m` using `by exact_mod_cast h3`. Use linear arithmetic over natural numbers and integers.
-/
theorem arithVarZero : ReciprocityTheory.ChartRestriction.G.AI.I2.ArithVarZeroStatement := by
  intro K _ ι _ P hP
  obtain ⟨_, ⟨hPp, hPh, hPr⟩, hhor, hdim⟩ := hP
  have := hPp
  set m := Fintype.card K with hm
  let e : K ≃ Fin m := Fintype.equivFin K
  let S : ℕ → Set K := fun n => {k | (e k : ℕ) < n}
  let Q : ℕ → Ideal (MRing ι) := fun n => P.comap (killBlocks (S n))
  let Q2 : Ideal (MRing ι) :=
    RingHom.ker ((Int.castRingHom (ZMod 2)).comp (constantCoeff : MRing ι →+* ℤ))
  have hQp : ∀ n, (Q n).IsPrime := fun n => Ideal.IsPrime.comap _
  have hQ2p : Q2.IsPrime := RingHom.ker_isPrime _
  have hstep : ∀ n, n < m → Q n < Q (n + 1) := by
    intro n hn
    obtain ⟨i, hi⟩ := hPr (e.symm ⟨n, hn⟩)
    refine SetLike.lt_iff_le_and_exists.mpr
      ⟨comap_killBlocks_mono hPh fun k hk => Nat.lt_succ_of_lt hk, X ⟨e.symm ⟨n, hn⟩, i⟩, ?_, ?_⟩
    · show killBlocks _ _ ∈ P
      rw [killBlocks_X, if_pos (by simp [S])]
      exact P.zero_mem
    · intro h2
      change killBlocks _ _ ∈ P at h2
      rw [killBlocks_X, if_neg (by simp [S])] at h2
      exact hi h2
  have hall : ∀ f : MRing ι, killBlocks (S m) f = C (constantCoeff f) := by
    intro f
    have : killBlocks (S m) = aeval (0 : (Σ k, ι k) → MRing ι) := by
      refine MvPolynomial.algHom_ext fun p => ?_
      rw [killBlocks_X, if_pos (by simp [S]), aeval_X]
      rfl
    rw [this, aeval_zero, algebraMap_eq]
  have hQm : ∀ f, f ∈ Q m ↔ constantCoeff f = 0 := by
    intro f
    change killBlocks (S m) f ∈ P ↔ _
    rw [hall]
    change constantCoeff f ∈ P.comap (C : ℤ →+* MRing ι) ↔ _
    rw [hhor, Ideal.mem_bot]
  have hstep2 : Q m < Q2 := by
    refine SetLike.lt_iff_le_and_exists.mpr ⟨fun f hf => ?_, C 2, ?_, fun h2 => ?_⟩
    · rw [RingHom.mem_ker, RingHom.comp_apply, (hQm f).mp hf, map_zero]
    · rw [RingHom.mem_ker, RingHom.comp_apply, constantCoeff_C]
      rfl
    · have := (hQm _).mp h2
      rw [constantCoeff_C] at this
      norm_num at this
  let T : ℕ → Ideal (MRing ι) := fun n => if n ≤ m then Q n else Q2
  have hTp : ∀ n, (T n).IsPrime := by
    intro n
    dsimp only [T]
    split_ifs
    exacts [hQp n, hQ2p]
  have hPT : ∀ n, P ≤ T n := by
    intro n
    dsimp only [T]
    split_ifs
    · exact le_comap_killBlocks hPh _
    · exact (le_comap_killBlocks hPh _).trans hstep2.le
  have hTlt : ∀ n, n ≤ m → T n < T (n + 1) := by
    intro n hn
    dsimp only [T]
    rw [if_pos hn]
    rcases hn.lt_or_eq with h | h
    · rw [if_pos (Nat.succ_le_of_lt h)]
      exact hstep n h
    · rw [if_neg (by omega), h]
      exact hstep2
  let g : Fin (m + 2) → PrimeSpectrum.zeroLocus (R := MRing ι) (P : Set (MRing ι)) :=
    fun j => ⟨⟨T j, hTp j⟩, hPT j⟩
  have hg : StrictMono g := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    exact hTlt i (Nat.lt_succ_iff.mp i.isLt)
  have hlen := Order.LTSeries.length_le_krullDim (LTSeries.mk (m + 1) g hg)
  rw [← ringKrullDim_quotient, hdim] at hlen
  have h3 : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ ((0 + m : ℕ) : WithBot ℕ∞) := hlen
  have h4 : m + 1 ≤ 0 + m := by exact_mod_cast h3
  omega

end GroundTheory.Heights₂.Heights.Inter

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

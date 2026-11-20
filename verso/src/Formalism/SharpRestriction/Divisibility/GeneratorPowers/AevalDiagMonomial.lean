import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PairEvaluation

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1

open MvPolynomial Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation

variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

/- English proof (translation)
The claim follows from `mem_pow_idealOfVars_iff n p`.
-/
private theorem memIo_lemma {σ : Type} (n : ℕ) (p : MvPolynomial σ S) :
    p ∈ Io S σ ^ n ↔ ∀ x ∈ p.support, n ≤ Finsupp.degree x :=
  mem_pow_idealOfVars_iff n p

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `h` using `(memIo_lemma (n + 1) p).1 hp 0 (MvPolynomial.mem_support_iff.2 hne)`. Simplify using `[Finsupp.degree] at h`.
-/
private theorem ccmem_lemma_2 {σ : Type} {n : ℕ} {p : MvPolynomial σ S} (hp : p ∈ Io S σ ^ (n + 1)) :
    coeff 0 p = 0 := by
  by_contra hne
  have h := (memIo_lemma (n + 1) p).1 hp 0 (MvPolynomial.mem_support_iff.2 hne)
  simp [Finsupp.degree] at h

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp only [aeval_C, algebraMap_eq, constantCoeff_C]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p i hp => simp only [map_mul, aeval_X, constantCoeff_X, hg, mul_zero]`.
-/
private theorem ccaeval_lemma_3 {σ τ : Type} (g : σ → MvPolynomial τ S) (hg : ∀ i, constantCoeff (g i) = 0)
    (p : MvPolynomial σ S) : constantCoeff (aeval g p) = constantCoeff p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, algebraMap_eq, constantCoeff_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, aeval_X, constantCoeff_X, hg, mul_zero]

/- English proof (translation)
Rewrite using `[memIo_lemma]`. Introduce `x hx`. Assume the negation of the conclusion as `hlt`. Establish `h0 : Finsupp.degree x = 0` using `by omega`. Establish `hs : ∑ j ∈ x.support, x j = 0` using `h0`.

Establish `hx0 : x = 0`. Use extensionality with `i`. Assume the negation of the conclusion as `hi`. Conclude with `hi ((Finset.sum_eq_zero_iff.1 hs) i (Finsupp.mem_support_iff.2 hi))`. Substitute `hx0` using the available equality.

Conclude with `(MvPolynomial.mem_support_iff.1 hx) hp`.
-/
private theorem memcc_lemma_19 {σ : Type} {p : MvPolynomial σ S} (hp : constantCoeff p = 0) :
    p ∈ Io S σ ^ 1 := by
  rw [memIo_lemma]
  intro x hx
  by_contra hlt
  have h0 : Finsupp.degree x = 0 := by omega
  have hs : ∑ j ∈ x.support, x j = 0 := h0
  have hx0 : x = 0 := by
    ext i
    by_contra hi
    exact hi ((Finset.sum_eq_zero_iff.1 hs) i (Finsupp.mem_support_iff.2 hi))
  subst hx0
  exact (MvPolynomial.mem_support_iff.1 hx) hp

/- English proof (translation)
Rewrite `hp`, the goal using `[memIo_lemma]`. Introduce `x hx`. Use `hp x hx` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private theorem weak_lemma_24 {σ : Type} {m n : ℕ} (h : m ≤ n) {p : MvPolynomial σ S}
    (hp : p ∈ Io S σ ^ n) : p ∈ Io S σ ^ m := by
  rw [memIo_lemma] at hp ⊢
  intro x hx
  have := hp x hx
  omega

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp only [aeval_C, sub_self, Submodule.zero_mem]`. Consider the case `add p q hp hq`. Rewrite using `[map_add, map_add, add_sub_add_comm]`. Conclude with `Ideal.add_mem _ hp hq`.

Consider the case `mul_X p i hp`. Rewrite using `[map_mul, map_mul, aeval_X, aeval_X]`. Establish `e : aeval g p * g i - aeval g' p * g' i = aeval g p * (g i - g' i) + (aeval g p - aeval g' p) * g' i` using `by ring`. Rewrite using `[e]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hgg i)) (Ideal.mul_mem_right _ _ hp)`.
-/
private theorem base_lemma_17 {σ τ : Type} (g g' : σ → MvPolynomial τ S)
    (hgg : ∀ i, g i - g' i ∈ Io S τ ^ 2) (p : MvPolynomial σ S) :
    aeval g p - aeval g' p ∈ Io S τ ^ 2 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, sub_self, Submodule.zero_mem]
  | add p q hp hq =>
    rw [map_add, map_add, add_sub_add_comm]
    exact Ideal.add_mem _ hp hq
  | mul_X p i hp =>
    rw [map_mul, map_mul, aeval_X, aeval_X]
    have e : aeval g p * g i - aeval g' p * g' i =
        aeval g p * (g i - g' i) + (aeval g p - aeval g' p) * g' i := by ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hgg i)) (Ideal.mul_mem_right _ _ hp)

/- English proof (translation)
Establish `hcg : ∀ i, constantCoeff (g i) = 0` using `fun i => ccmem_lemma_2 (n := 0) (hg i)`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `p _`. Use `⟨by simp, weak_lemma_24 (by norm_num) (base_lemma_17 g g' hgg p)⟩` and prove the remaining obligations.

Consider the case `succ n ih`. Introduce `p hp`. Rewrite `hp` using `[pow_succ]`. Use `Submodule.mul_induction_on hp ?_ ?_` and prove the remaining obligations. Introduce `a ha b hb`.

Take `⟨h1, h2⟩` from `ih a ha`. Establish `hb0 : coeff 0 b = 0` using `ccmem_lemma_2 (n := 0) (p := b) (by rwa [zero_add, pow_one])`. Establish `hb1 : aeval g b ∈ Io S τ ^ 1`. Apply `memcc_lemma_19` to reduce the goal to its premises. Rewrite using `[ccaeval_lemma_3 g hcg]`.

Conclude with `hb0`. Establish `hb2 : aeval g b - aeval g' b ∈ Io S τ ^ 2` using `base_lemma_17 g g' hgg b`. Establish `hb3 : aeval g' b ∈ Io S τ ^ 1`. Establish `h` using `Ideal.sub_mem _ hb1 (weak_lemma_24 (by norm_num) hb2)`. Simplify using `using h`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[map_mul, pow_succ]`. Conclude with `Ideal.mul_mem_mul h1 (by rwa [pow_one] at hb1)`. Rewrite using `[map_mul, map_mul]`. Establish `e : aeval g a * aeval g b - aeval g' a * aeval g' b = aeval g a * (aeval g b - aeval g' b) + (aeval g a - aeval g' a) * aeval g' b` using `by ring`.

Rewrite using `[e]`. Establish `k1` using `Ideal.mul_mem_mul h1 hb2`. Establish `k2` using `Ideal.mul_mem_mul h2 hb3`. Rewrite `k1`, `k2` using `[← pow_add]`. Establish `e1 : n + 2 = n + 1 + 1` using `by omega`.

Rewrite `k1` using `[e1]`. Conclude with `Ideal.add_mem _ k1 k2`. Introduce `x y hx hy`. Take `⟨hx1, hx2⟩` from `hx`. Take `⟨hy1, hy2⟩` from `hy`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[map_add]`. Conclude with `Ideal.add_mem _ hx1 hy1`. Rewrite using `[map_add, map_add, add_sub_add_comm]`. Conclude with `Ideal.add_mem _ hx2 hy2`.
-/
private theorem subst_lemma_18 {σ τ : Type} (g g' : σ → MvPolynomial τ S) (hg : ∀ i, g i ∈ Io S τ ^ 1)
    (hgg : ∀ i, g i - g' i ∈ Io S τ ^ 2) (n : ℕ) :
    ∀ p ∈ Io S σ ^ n, aeval g p ∈ Io S τ ^ n ∧ aeval g p - aeval g' p ∈ Io S τ ^ (n + 1) := by
  have hcg : ∀ i, constantCoeff (g i) = 0 := fun i => ccmem_lemma_2 (n := 0) (hg i)
  induction n with
  | zero =>
    intro p _
    refine ⟨by simp, weak_lemma_24 (by norm_num) (base_lemma_17 g g' hgg p)⟩
  | succ n ih =>
    intro p hp
    rw [pow_succ] at hp
    refine Submodule.mul_induction_on hp ?_ ?_
    · intro a ha b hb
      obtain ⟨h1, h2⟩ := ih a ha
      have hb0 : coeff 0 b = 0 := ccmem_lemma_2 (n := 0) (p := b) (by rwa [zero_add, pow_one])
      have hb1 : aeval g b ∈ Io S τ ^ 1 := by
        apply memcc_lemma_19
        rw [ccaeval_lemma_3 g hcg]
        exact hb0
      have hb2 : aeval g b - aeval g' b ∈ Io S τ ^ 2 := base_lemma_17 g g' hgg b
      have hb3 : aeval g' b ∈ Io S τ ^ 1 := by
        have h := Ideal.sub_mem _ hb1 (weak_lemma_24 (by norm_num) hb2)
        simpa using h
      constructor
      · rw [map_mul, pow_succ]
        exact Ideal.mul_mem_mul h1 (by rwa [pow_one] at hb1)
      · rw [map_mul, map_mul]
        have e : aeval g a * aeval g b - aeval g' a * aeval g' b =
            aeval g a * (aeval g b - aeval g' b) + (aeval g a - aeval g' a) * aeval g' b := by ring
        rw [e]
        have k1 := Ideal.mul_mem_mul h1 hb2
        have k2 := Ideal.mul_mem_mul h2 hb3
        rw [← pow_add] at k1 k2
        have e1 : n + 2 = n + 1 + 1 := by omega
        rw [e1] at k1
        exact Ideal.add_mem _ k1 k2
    · intro x y hx hy
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨hy1, hy2⟩ := hy
      constructor
      · rw [map_add]
        exact Ideal.add_mem _ hx1 hy1
      · rw [map_add, map_add, add_sub_add_comm]
        exact Ideal.add_mem _ hx2 hy2

/- English proof (translation)
Use `subst_lemma_18 _ _ ?_ ?_ n p hp` and prove the remaining obligations. Introduce and unpack `⟨k, i⟩ fin_cases k`. Simplify using `using hu i`. Simplify using `using hv i`. Introduce and unpack `⟨k, i⟩ fin_cases k`.

Simplify using `using huu i`. Simplify using `using hvv i`.
-/
private theorem ev2sub_lemma_25 {τ : Type} (u v u' v' : Fin d → MvPolynomial τ S)
    (hu : ∀ i, u i ∈ Io S τ ^ 1) (hv : ∀ i, v i ∈ Io S τ ^ 1)
    (huu : ∀ i, u i - u' i ∈ Io S τ ^ 2) (hvv : ∀ i, v i - v' i ∈ Io S τ ^ 2)
    (n : ℕ) (p : MvPolynomial (Fin 2 × Fin d) S) (hp : p ∈ Io S (Fin 2 × Fin d) ^ n) :
    ev2 p u v ∈ Io S τ ^ n ∧ ev2 p u v - ev2 p u' v' ∈ Io S τ ^ (n + 1) := by
  refine subst_lemma_18 _ _ ?_ ?_ n p hp
  · rintro ⟨k, i⟩
    fin_cases k
    · simpa using hu i
    · simpa using hv i
  · rintro ⟨k, i⟩
    fin_cases k
    · simpa using huu i
    · simpa using hvv i

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply]`. Use `show (e.sum fun i c => c • (1 : σ → ℕ) i) = ∑ i ∈ e.support, e i`. Simplify using `[Finsupp.sum]`.
-/
private theorem wtdeg_lemma_20 {σ : Type} (e : σ →₀ ℕ) : Finsupp.weight 1 e = Finsupp.degree e := by
  rw [Finsupp.weight_apply]
  show (e.sum fun i c => c • (1 : σ → ℕ) i) = ∑ i ∈ e.support, e i
  simp [Finsupp.sum]

/- English proof (translation)
Introduce `e he`. Rewrite `he` using `[coeff_X']`. Use `split_ifs at he with h`. Rewrite using `[← h]`. Simplify using `[Finsupp.weight_apply, Finsupp.sum_single_index]`.

Conclude with `absurd rfl he`.
-/
private theorem hX_lemma_22 {σ : Type} (i : σ) : (X i : MvPolynomial σ S).IsHomogeneous 1 := by
  classical
  intro e he
  rw [coeff_X'] at he
  split_ifs at he with h
  · rw [← h]
    simp [Finsupp.weight_apply, Finsupp.sum_single_index]
  · exact absurd rfl he

/- English proof (translation)
Establish `h` using `hp.eval₂ C g (fun r => isHomogeneous_C _ r) hg`. Rewrite `h` using `[one_mul]`. Rewrite using `[aeval_def, algebraMap_eq]`. Conclude with `h`.
-/
private theorem homog_lemma_21 {σ τ : Type} {p : MvPolynomial σ S} {j : ℕ} (hp : p.IsHomogeneous j)
    (g : σ → MvPolynomial τ S) (hg : ∀ i, (g i).IsHomogeneous 1) : (aeval g p).IsHomogeneous j := by
  have h := hp.eval₂ C g (fun r => isHomogeneous_C _ r) hg
  rw [one_mul] at h
  rw [aeval_def, algebraMap_eq]
  exact h

/- English proof (translation)
Apply `homog_lemma_21 hp` to reduce the goal to its premises. Introduce and unpack `⟨k, i⟩`. Use `fin_cases k`. Simplify using `using hu i`. Simplify using `using hv i`.
-/
private theorem ev2homog_lemma_23 {τ : Type} {p : MvPolynomial (Fin 2 × Fin d) S} {j : ℕ}
    (hp : p.IsHomogeneous j) (u v : Fin d → MvPolynomial τ S) (hu : ∀ i, (u i).IsHomogeneous 1)
    (hv : ∀ i, (v i).IsHomogeneous 1) : (ev2 p u v).IsHomogeneous j := by
  apply homog_lemma_21 hp
  rintro ⟨k, i⟩
  fin_cases k
  · simpa using hu i
  · simpa using hv i

/- English proof (translation)
Use extensionality with `e`. Rewrite using `[coeff_zero]`. Assume the negation of the conclusion as `he`. Establish `h1 : Finsupp.weight 1 e = j` using `hh he`. Establish `h2` using `(memIo_lemma (j + 1) p).1 hp e (MvPolynomial.mem_support_iff.2 he)`.

Rewrite `h1` using `[wtdeg_lemma_20]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem zeroOf_lemma_26 {τ : Type} {p : MvPolynomial τ S} {j : ℕ} (hh : p.IsHomogeneous j)
    (hp : p ∈ Io S τ ^ (j + 1)) : p = 0 := by
  ext e
  rw [coeff_zero]
  by_contra he
  have h1 : Finsupp.weight 1 e = j := hh he
  have h2 := (memIo_lemma (j + 1) p).1 hp e (MvPolynomial.mem_support_iff.2 he)
  rw [wtdeg_lemma_20] at h1
  omega

/- English proof (translation)
Establish `hxJ : ∀ (k : Fin 3) (i : Fin d), xs S d k i ∈ Io S (Fin 3 × Fin d) ^ 1` using `fun k i => memcc_lemma_19 (by simp [xs])`. Establish `hyJ : ∀ (k : Fin 2) (i : Fin d), xs S d k i ∈ Io S (Fin 2 × Fin d) ^ 1` using `fun k i => memcc_lemma_19 (by simp [xs])`. Establish `haJ : ∀ i, xs S d (0 : Fin 3) i + xs S d 1 i ∈ Io S (Fin 3 × Fin d) ^ 1` using `fun i => Ideal.add_mem _ (hxJ 0 i) (hxJ 1 i)`. Establish `hfJ : ∀ i, fF i ∈ Io S (Fin 3 × Fin d) ^ 1`. Introduce `i`.

Establish `h` using `Ideal.add_mem _ (weak_lemma_24 (by norm_num) (hF i)) (haJ i)`. Simplify using `using h`. Establish `hR : P - 1 - homogeneousComponent j (P - 1) ∈ Io S (Fin 2 × Fin d) ^ (j + 1)`. Establish `hP'` using `hP`. Rewrite `hP'`, the goal using `[memIo_lemma]`.

Introduce `x hx`. Rewrite `hx` using `[MvPolynomial.mem_support_iff, coeff_sub, coeff_homogeneousComponent]`. Use `split_ifs at hx with hxj`. Simplify using `at hx`. Establish `hxQ : x ∈ (P - 1).support`.

Rewrite using `[MvPolynomial.mem_support_iff]`. Simplify using `using hx`. Use `hP' x hxQ` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hQj` using `homogeneousComponent_isHomogeneous j (P - 1)`.

Establish `hXh : ∀ (k : Fin 3) (i : Fin d), (xs S d k i).IsHomogeneous 1` using `fun k i => hX_lemma_22 _`. Establish `hYh : ∀ (k : Fin 2) (i : Fin d), (xs S d k i).IsHomogeneous 1` using `fun k i => hX_lemma_22 _`. Establish `z2 : ∀ (w : Fin d → MvPolynomial (Fin 3 × Fin d) S) (i : Fin d), w i - w i ∈ Io S (Fin 3 × Fin d) ^ 2`. Introduce `w i`. Simplify using the standard rewrite rules.

Establish `y2 : ∀ (w : Fin d → MvPolynomial (Fin 2 × Fin d) S) (i : Fin d), w i - w i ∈ Io S (Fin 2 × Fin d) ^ 2`. Introduce `w i`. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Establish `m1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈ Io S (Fin 3 × Fin d) ^ (j + 1)` using `weak_lemma_24 (by omega) hph1`.

Establish `m2` using `(ev2sub_lemma_25 fF (xs S d (2 : Fin 3)) (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d (2 : Fin 3)) hfJ (hxJ 2) hF (z2 _) j (P - 1) hP).2`. Establish `m3` using `(ev2sub_lemma_25 (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d (2 : Fin 3)) (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d (2 : Fin 3)) haJ (hxJ 2) (z2 _) (z2 _) (j + 1) _ hR).1`. Establish `m4` using `(ev2sub_lemma_25 (xs S d (0 : Fin 3)) (xs S d (2 : Fin 3)) (xs S d (0 : Fin 3)) (xs S d (2 : Fin 3)) (hxJ 0) (hxJ 2) (z2 _) (z2 _) (j + 1) _ hR).1`. Establish `m5` using `(ev2sub_lemma_25 (xs S d (1 : Fin 3)) (xs S d (2 : Fin 3)) (xs S d (1 : Fin 3)) (xs S d (2 : Fin 3)) (hxJ 1) (hxJ 2) (z2 _) (z2 _) (j + 1) _ hR).1`. Establish `t4` using `(ev2sub_lemma_25 (xs S d (0 : Fin 3)) (xs S d (2 : Fin 3)) (xs S d (0 : Fin 3)) (xs S d (2 : Fin 3)) (hxJ 0) (hxJ 2) (z2 _) (z2 _) j _ hP).1`.

Establish `t5` using `(ev2sub_lemma_25 (xs S d (1 : Fin 3)) (xs S d (2 : Fin 3)) (xs S d (1 : Fin 3)) (xs S d (2 : Fin 3)) (hxJ 1) (hxJ 2) (z2 _) (z2 _) j _ hP).1`. Establish `m6 : ev2 (P - 1) (xs S d 0) (xs S d 2) * ev2 (P - 1) (xs S d 1) (xs S d 2) ∈ Io S (Fin 3 × Fin d) ^ (j + 1)`. Establish `h` using `Ideal.mul_mem_mul t4 t5`. Rewrite `h` using `[← pow_add]`. Conclude with `weak_lemma_24 (by omega) h`.

Establish `hE : ev2 (homogeneousComponent j (P - 1)) (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) - ev2 (homogeneousComponent j (P - 1)) (xs S d 0) (xs S d 2) - ev2 (homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 2) = 0`. Apply `zeroOf_lemma_26` to reduce the goal to its premises. Conclude with `((ev2homog_lemma_23 hQj _ _ (fun i => (hXh 0 i).add (hXh 1 i)) (hXh 2)).sub (ev2homog_lemma_23 hQj _ _ (hXh 0) (hXh 2))).sub (ev2homog_lemma_23 hQj _ _ (hXh 1) (hXh 2))`. Establish `hid : ev2 (homogeneousComponent j (P - 1)) (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) - ev2 (homogeneousComponent j (P - 1)) (xs S d 0) (xs S d 2) - ev2 (homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 2) = (ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 …`. Simplify using `only [ev2, map_sub, map_one]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hid]`. Conclude with `Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.sub_mem _ (Ideal.sub_mem _ m1 m2) m3) m4) m5) m6`. Take the linear combination `hE`. Establish `s1 : ev2 P (xs S d 1) (xs S d 0) - P ∈ Io S (Fin 2 × Fin d) ^ (j + 1)` using `weak_lemma_24 (by omega) hsym`.

Establish `s2` using `(ev2sub_lemma_25 (xs S d (1 : Fin 2)) (xs S d (0 : Fin 2)) (xs S d (1 : Fin 2)) (xs S d (0 : Fin 2)) (hyJ 1) (hyJ 0) (y2 _) (y2 _) (j + 1) _ hR).1`. Establish `hE : ev2 (homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 0) - homogeneousComponent j (P - 1) = 0`. Apply `zeroOf_lemma_26` to reduce the goal to its premises. Conclude with `(ev2homog_lemma_23 hQj _ _ (hYh 1) (hYh 0)).sub hQj`. Establish `hid : ev2 (homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 0) - homogeneousComponent j (P - 1) = (ev2 P (xs S d 1) (xs S d 0) - P) - ev2 (P - 1 - homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 0) + (P - 1 - homogeneousComponent j (P - 1))`.

Simplify using `only [ev2, map_sub, map_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hid]`. Conclude with `Ideal.add_mem _ (Ideal.sub_mem _ s1 s2) hR`. Take the linear combination `hE`.
-/
theorem lead_biadd {P : MvPolynomial (Fin 2 × Fin d) S} {m j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m)
    (fF : Fin d → MvPolynomial (Fin 3 × Fin d) S)
    (hF : ∀ i, fF i - (xs S d 0 i + xs S d 1 i) ∈ Io S (Fin 3 × Fin d) ^ 2)
    (hph1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
      Io S (Fin 3 × Fin d) ^ (m + 1))
    (hsym : ev2 P (xs S d 1) (xs S d 0) - P ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (hP : P - 1 ∈ Io S (Fin 2 × Fin d) ^ j) :
    ev2 (homogeneousComponent j (P - 1)) (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) =
        ev2 (homogeneousComponent j (P - 1)) (xs S d 0) (xs S d 2) +
          ev2 (homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 2) ∧
      ev2 (homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 0) = homogeneousComponent j (P - 1) := by
  have hxJ : ∀ (k : Fin 3) (i : Fin d), xs S d k i ∈ Io S (Fin 3 × Fin d) ^ 1 :=
    fun k i => memcc_lemma_19 (by simp [xs])
  have hyJ : ∀ (k : Fin 2) (i : Fin d), xs S d k i ∈ Io S (Fin 2 × Fin d) ^ 1 :=
    fun k i => memcc_lemma_19 (by simp [xs])
  have haJ : ∀ i, xs S d (0 : Fin 3) i + xs S d 1 i ∈ Io S (Fin 3 × Fin d) ^ 1 :=
    fun i => Ideal.add_mem _ (hxJ 0 i) (hxJ 1 i)
  have hfJ : ∀ i, fF i ∈ Io S (Fin 3 × Fin d) ^ 1 := by
    intro i
    have h := Ideal.add_mem _ (weak_lemma_24 (by norm_num) (hF i)) (haJ i)
    simpa using h
  have hR : P - 1 - homogeneousComponent j (P - 1) ∈ Io S (Fin 2 × Fin d) ^ (j + 1) := by
    have hP' := hP
    rw [memIo_lemma] at hP' ⊢
    intro x hx
    rw [MvPolynomial.mem_support_iff, coeff_sub, coeff_homogeneousComponent] at hx
    split_ifs at hx with hxj
    · simp at hx
    · have hxQ : x ∈ (P - 1).support := by
        rw [MvPolynomial.mem_support_iff]
        simpa using hx
      have := hP' x hxQ
      omega
  have hQj := homogeneousComponent_isHomogeneous j (P - 1)
  have hXh : ∀ (k : Fin 3) (i : Fin d), (xs S d k i).IsHomogeneous 1 := fun k i => hX_lemma_22 _
  have hYh : ∀ (k : Fin 2) (i : Fin d), (xs S d k i).IsHomogeneous 1 := fun k i => hX_lemma_22 _
  have z2 : ∀ (w : Fin d → MvPolynomial (Fin 3 × Fin d) S) (i : Fin d), w i - w i ∈ Io S (Fin 3 × Fin d) ^ 2 := by
    intro w i
    simp
  have y2 : ∀ (w : Fin d → MvPolynomial (Fin 2 × Fin d) S) (i : Fin d), w i - w i ∈ Io S (Fin 2 × Fin d) ^ 2 := by
    intro w i
    simp
  constructor
  · have m1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
        Io S (Fin 3 × Fin d) ^ (j + 1) := weak_lemma_24 (by omega) hph1
    have m2 := (ev2sub_lemma_25 fF (xs S d (2 : Fin 3)) (fun i => xs S d (0 : Fin 3) i + xs S d 1 i)
      (xs S d (2 : Fin 3)) hfJ (hxJ 2) hF (z2 _) j (P - 1) hP).2
    have m3 := (ev2sub_lemma_25 (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d (2 : Fin 3))
      (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d (2 : Fin 3)) haJ (hxJ 2) (z2 _) (z2 _) (j + 1) _ hR).1
    have m4 := (ev2sub_lemma_25 (xs S d (0 : Fin 3)) (xs S d (2 : Fin 3)) (xs S d (0 : Fin 3)) (xs S d (2 : Fin 3))
      (hxJ 0) (hxJ 2) (z2 _) (z2 _) (j + 1) _ hR).1
    have m5 := (ev2sub_lemma_25 (xs S d (1 : Fin 3)) (xs S d (2 : Fin 3)) (xs S d (1 : Fin 3)) (xs S d (2 : Fin 3))
      (hxJ 1) (hxJ 2) (z2 _) (z2 _) (j + 1) _ hR).1
    have t4 := (ev2sub_lemma_25 (xs S d (0 : Fin 3)) (xs S d (2 : Fin 3)) (xs S d (0 : Fin 3)) (xs S d (2 : Fin 3))
      (hxJ 0) (hxJ 2) (z2 _) (z2 _) j _ hP).1
    have t5 := (ev2sub_lemma_25 (xs S d (1 : Fin 3)) (xs S d (2 : Fin 3)) (xs S d (1 : Fin 3)) (xs S d (2 : Fin 3))
      (hxJ 1) (hxJ 2) (z2 _) (z2 _) j _ hP).1
    have m6 : ev2 (P - 1) (xs S d 0) (xs S d 2) * ev2 (P - 1) (xs S d 1) (xs S d 2) ∈
        Io S (Fin 3 × Fin d) ^ (j + 1) := by
      have h := Ideal.mul_mem_mul t4 t5
      rw [← pow_add] at h
      exact weak_lemma_24 (by omega) h
    have hE : ev2 (homogeneousComponent j (P - 1)) (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) -
        ev2 (homogeneousComponent j (P - 1)) (xs S d 0) (xs S d 2) -
        ev2 (homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 2) = 0 := by
      apply zeroOf_lemma_26
      · exact ((ev2homog_lemma_23 hQj _ _ (fun i => (hXh 0 i).add (hXh 1 i)) (hXh 2)).sub
          (ev2homog_lemma_23 hQj _ _ (hXh 0) (hXh 2))).sub (ev2homog_lemma_23 hQj _ _ (hXh 1) (hXh 2))
      · have hid : ev2 (homogeneousComponent j (P - 1)) (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) -
            ev2 (homogeneousComponent j (P - 1)) (xs S d 0) (xs S d 2) -
            ev2 (homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 2) =
            (ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2)) -
            (ev2 (P - 1) fF (xs S d 2) - ev2 (P - 1) (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2)) -
            ev2 (P - 1 - homogeneousComponent j (P - 1)) (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) +
            ev2 (P - 1 - homogeneousComponent j (P - 1)) (xs S d 0) (xs S d 2) +
            ev2 (P - 1 - homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 2) +
            ev2 (P - 1) (xs S d 0) (xs S d 2) * ev2 (P - 1) (xs S d 1) (xs S d 2) := by
          simp only [ev2, map_sub, map_one]
          ring
        rw [hid]
        exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _
          (Ideal.sub_mem _ (Ideal.sub_mem _ m1 m2) m3) m4) m5) m6
    linear_combination hE
  · have s1 : ev2 P (xs S d 1) (xs S d 0) - P ∈ Io S (Fin 2 × Fin d) ^ (j + 1) := weak_lemma_24 (by omega) hsym
    have s2 := (ev2sub_lemma_25 (xs S d (1 : Fin 2)) (xs S d (0 : Fin 2)) (xs S d (1 : Fin 2)) (xs S d (0 : Fin 2))
      (hyJ 1) (hyJ 0) (y2 _) (y2 _) (j + 1) _ hR).1
    have hE : ev2 (homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 0) - homogeneousComponent j (P - 1) = 0 := by
      apply zeroOf_lemma_26
      · exact (ev2homog_lemma_23 hQj _ _ (hYh 1) (hYh 0)).sub hQj
      · have hid : ev2 (homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 0) - homogeneousComponent j (P - 1) =
            (ev2 P (xs S d 1) (xs S d 0) - P) -
            ev2 (P - 1 - homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 0) +
            (P - 1 - homogeneousComponent j (P - 1)) := by
          simp only [ev2, map_sub, map_one]
          ring
        rw [hid]
        exact Ideal.add_mem _ (Ideal.sub_mem _ s1 s2) hR
    linear_combination hE

/- English proof (translation)
Rewrite using `[aeval_monomial, algebraMap_eq, monomial_eq, C_mul]`. Simplify using `only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem monoDiag_lemma_4 {σ : Type} (s : σ → S) (e : σ →₀ ℕ) (a : S) :
    aeval (fun p => C (s p) * X p) (monomial e a) = monomial e ((e.prod fun p k => s p ^ k) * a) := by
  rw [aeval_monomial, algebraMap_eq, monomial_eq, C_mul]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  ring

/- English proof (translation)
Use `conv_lhs => rw [h.as_sum]`. Rewrite using `[map_sum, coeff_sum]`. Simplify using `only [monoDiag_lemma_4, coeff_monomial]`. Rewrite using `[Finset.sum_eq_single e]`. Rewrite using `[if_pos rfl]`.

Introduce `b _ hb`. Rewrite using `[if_neg hb]`. Introduce `he`. Simplify using `only [MvPolynomial.mem_support_iff, not_not] at he`. Rewrite using `[if_pos rfl, he, mul_zero]`.
-/
private theorem coeffDiag_lemma_5 {σ : Type} (s : σ → S) (h : MvPolynomial σ S) (e : σ →₀ ℕ) :
    coeff e (aeval (fun p => C (s p) * X p) h) = (e.prod fun p k => s p ^ k) * coeff e h := by
  classical
  conv_lhs => rw [h.as_sum]
  rw [map_sum, coeff_sum]
  simp only [monoDiag_lemma_4, coeff_monomial]
  rw [Finset.sum_eq_single e]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb]
  · intro he
    simp only [MvPolynomial.mem_support_iff, not_not] at he
    rw [if_pos rfl, he, mul_zero]

/- English proof (translation)
Establish `hq : ((2 : ℚ) ^ a - 2) ≠ 0`. Introduce `h0`. Establish `h1 : ((2 ^ a : ℕ) : ℚ) = ((2 : ℕ) : ℚ)`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h2 : 2 ^ a = 2 ^ 1`. Rewrite using `[pow_one]`. Conclude with `h1` after adjusting the coercions. Conclude with `ha (Nat.pow_right_injective (le_refl 2) h2)`. Establish `h3 : algebraMap ℚ S ((2 : ℚ) ^ a - 2) * c = 0`.

Rewrite using `[map_sub, map_pow, map_ofNat]`. Take the linear combination `h`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[inv_mul_cancel₀ hq, map_one, one_mul]`. Use `_ = algebraMap ℚ S (((2 : ℚ) ^ a - 2)⁻¹) * (algebraMap ℚ S ((2 : ℚ) ^ a - 2) * c) := by`.

Rewrite using `[map_mul, mul_assoc]`. Use `_ = 0 := by rw [h3, mul_zero]`.
-/
private theorem cancel_lemma_6 {a : ℕ} (ha : a ≠ 1) {c : S} (h : (2 : S) ^ a * c = 2 * c) : c = 0 := by
  have hq : ((2 : ℚ) ^ a - 2) ≠ 0 := by
    intro h0
    have h1 : ((2 ^ a : ℕ) : ℚ) = ((2 : ℕ) : ℚ) := by
      push_cast
      linarith
    have h2 : 2 ^ a = 2 ^ 1 := by
      rw [pow_one]
      exact_mod_cast h1
    exact ha (Nat.pow_right_injective (le_refl 2) h2)
  have h3 : algebraMap ℚ S ((2 : ℚ) ^ a - 2) * c = 0 := by
    rw [map_sub, map_pow, map_ofNat]
    linear_combination h
  calc c = algebraMap ℚ S (((2 : ℚ) ^ a - 2)⁻¹ * ((2 : ℚ) ^ a - 2)) * c := by
        rw [inv_mul_cancel₀ hq, map_one, one_mul]
    _ = algebraMap ℚ S (((2 : ℚ) ^ a - 2)⁻¹) * (algebraMap ℚ S ((2 : ℚ) ^ a - 2) * c) := by
        rw [map_mul, mul_assoc]
    _ = 0 := by rw [h3, mul_zero]

/- English proof (translation)
Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, Fin.prod_univ_two]`. Apply the tactic sequence `fin_cases k <;> simp [Finset.prod_pow_eq_pow_sum]`.
-/
private theorem prod_ite_pow_eq_two_pow_sum (k : Fin 2) (e : Fin 2 × Fin d →₀ ℕ) :
    (e.prod fun p n => (if p.1 = k then (2 : S) else 1) ^ n) = 2 ^ (∑ i, e (k, i)) := by
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, Fin.prod_univ_two]
  fin_cases k <;> simp [Finset.prod_pow_eq_pow_sum]

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp only [aeval_C, algebraMap_eq]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p i hp => simp only [map_mul, aeval_X, hp]`.
-/
private theorem comp_lemma_9 {σ τ υ : Type} (g : σ → MvPolynomial τ S) (r : τ → MvPolynomial υ S)
    (p : MvPolynomial σ S) : aeval r (aeval g p) = aeval (fun i => aeval r (g i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, aeval_X, hp]

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp only [aeval_C, algebraMap_eq]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p i hp => simp only [map_mul, aeval_X, hp]`.
-/
private theorem aevalX_lemma_10 {σ : Type} (p : MvPolynomial σ S) : aeval X p = p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, aeval_X, hp]

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]`. Simplify using `[Fintype.sum_prod_type, Fin.sum_univ_two]`.
-/
private theorem wt_lemma_11 (e : Fin 2 × Fin d →₀ ℕ) :
    Finsupp.weight 1 e = (∑ i, e (0, i)) + ∑ i, e (1, i) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two]

/- English proof (translation)
Take `⟨r, hr⟩ : ∃ r : Fin 3 × Fin d → MvPolynomial (Fin 2 × Fin d) S, ∀ q, r q = if q.1 = 2 then X (1, q.2) else X (0, q.2)` from `⟨_, fun _ => rfl⟩`. Establish `H` using `congrArg (aeval r) hA1`. Establish `e1 : aeval r (ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2)) = aeval (fun p : Fin 2 × Fin d => C (if p.1 = 0 then (2 : S) else 1) * X p) h`. Rewrite using `[ev2, comp_lemma_9]`. Use `congrArg (fun f => aeval f h) ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `⟨k, i⟩`. Apply the tactic sequence `fin_cases k <;> simp [xs, hr]`. Rewrite using `[← two_mul]`. Use `congr 1`. Establish `e2 : ∀ k : Fin 3, k ≠ 2 → aeval r (ev2 h (xs S d k) (xs S d 2)) = h`.

Introduce `k hk`. Rewrite using `[ev2, comp_lemma_9]`. Use `conv_rhs => rw [← aevalX_lemma_10 h]`. Use `congrArg (fun f => aeval f h) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `⟨l, i⟩`.

Apply the tactic sequence `fin_cases l <;> simp [xs, hr, hk]`. Rewrite `H` using `[e1, map_add, e2 0 (by decide), e2 1 (by decide)]`. Conclude with `H`.
-/
private theorem aeval_double_fst_of_additive {h : MvPolynomial (Fin 2 × Fin d) S}
    (hA1 : ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) =
      ev2 h (xs S d 0) (xs S d 2) + ev2 h (xs S d 1) (xs S d 2)) :
    aeval (fun p : Fin 2 × Fin d => C (if p.1 = 0 then (2 : S) else 1) * X p) h = h + h := by
  obtain ⟨r, hr⟩ : ∃ r : Fin 3 × Fin d → MvPolynomial (Fin 2 × Fin d) S,
      ∀ q, r q = if q.1 = 2 then X (1, q.2) else X (0, q.2) := ⟨_, fun _ => rfl⟩
  have H := congrArg (aeval r) hA1
  have e1 : aeval r (ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2)) =
      aeval (fun p : Fin 2 × Fin d => C (if p.1 = 0 then (2 : S) else 1) * X p) h := by
    rw [ev2, comp_lemma_9]
    refine congrArg (fun f => aeval f h) ?_
    funext ⟨k, i⟩
    fin_cases k <;> simp [xs, hr]
    rw [← two_mul]
    congr 1
  have e2 : ∀ k : Fin 3, k ≠ 2 → aeval r (ev2 h (xs S d k) (xs S d 2)) = h := by
    intro k hk
    rw [ev2, comp_lemma_9]
    conv_rhs => rw [← aevalX_lemma_10 h]
    refine congrArg (fun f => aeval f h) ?_
    funext ⟨l, i⟩
    fin_cases l <;> simp [xs, hr, hk]
  rw [e1, map_add, e2 0 (by decide), e2 1 (by decide)] at H
  exact H

/- English proof (translation)
Take `⟨G, hG⟩ : ∃ G : Fin 2 × Fin d → MvPolynomial (Fin 2 × Fin d) S, ∀ q, G q = if q.1 = 0 then C (2 : S) * X (1, q.2) else X (0, q.2)` from `⟨_, fun _ => rfl⟩`. Establish `e1 : aeval (fun p : Fin 2 × Fin d => C (if p.1 = 1 then (2 : S) else 1) * X p) (ev2 h (xs S d (1 : Fin 2)) (xs S d 0)) = aeval G h`. Rewrite using `[ev2, comp_lemma_9]`. Use `congrArg (fun f => aeval f h) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `⟨k, i⟩`.

Apply the tactic sequence `fin_cases k <;> simp [xs, hG]`. Establish `e2 : ev2 (aeval (fun p : Fin 2 × Fin d => C (if p.1 = 0 then (2 : S) else 1) * X p) h) (xs S d (1 : Fin 2)) (xs S d 0) = aeval G h`. Rewrite using `[ev2, comp_lemma_9]`. Use `congrArg (fun f => aeval f h) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `⟨k, i⟩`.

Apply the tactic sequence `fin_cases k <;> simp [xs, hG]`. Establish `e3 : ev2 (h + h) (xs S d (1 : Fin 2)) (xs S d 0) = h + h`. Unfold `ev2 at hs ⊢`. Rewrite using `[map_add, hs]`. Rewrite `e1` using `[hs]`.

Rewrite using `[e1, ← e2, h0, e3]`.
-/
private theorem aeval_double_snd_of_symm {h : MvPolynomial (Fin 2 × Fin d) S}
    (h0 : aeval (fun p : Fin 2 × Fin d => C (if p.1 = 0 then (2 : S) else 1) * X p) h = h + h)
    (hs : ev2 h (xs S d (1 : Fin 2)) (xs S d 0) = h) :
    aeval (fun p : Fin 2 × Fin d => C (if p.1 = 1 then (2 : S) else 1) * X p) h = h + h := by
  obtain ⟨G, hG⟩ : ∃ G : Fin 2 × Fin d → MvPolynomial (Fin 2 × Fin d) S,
      ∀ q, G q = if q.1 = 0 then C (2 : S) * X (1, q.2) else X (0, q.2) := ⟨_, fun _ => rfl⟩
  have e1 : aeval (fun p : Fin 2 × Fin d => C (if p.1 = 1 then (2 : S) else 1) * X p)
      (ev2 h (xs S d (1 : Fin 2)) (xs S d 0)) = aeval G h := by
    rw [ev2, comp_lemma_9]
    refine congrArg (fun f => aeval f h) ?_
    funext ⟨k, i⟩
    fin_cases k <;> simp [xs, hG]
  have e2 : ev2 (aeval (fun p : Fin 2 × Fin d => C (if p.1 = 0 then (2 : S) else 1) * X p) h)
      (xs S d (1 : Fin 2)) (xs S d 0) = aeval G h := by
    rw [ev2, comp_lemma_9]
    refine congrArg (fun f => aeval f h) ?_
    funext ⟨k, i⟩
    fin_cases k <;> simp [xs, hG]
  have e3 : ev2 (h + h) (xs S d (1 : Fin 2)) (xs S d 0) = h + h := by
    unfold ev2 at hs ⊢
    rw [map_add, hs]
  rw [hs] at e1
  rw [e1, ← e2, h0, e3]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Apply `he` to reduce the goal to its premises. Apply `cancel_lemma_6 hne` to reduce the goal to its premises. Establish `H` using `congrArg (coeff e) hk`. Rewrite `H` using `[coeffDiag_lemma_5, prod_ite_pow_eq_two_pow_sum, coeff_add]`.

Rewrite using `[H, two_mul]`.
-/
private theorem row_degree_eq_one_of_aeval_double {h : MvPolynomial (Fin 2 × Fin d) S} (k : Fin 2)
    (hk : aeval (fun p : Fin 2 × Fin d => C (if p.1 = k then (2 : S) else 1) * X p) h = h + h)
    (e : Fin 2 × Fin d →₀ ℕ) (he : coeff e h ≠ 0) : ∑ i, e (k, i) = 1 := by
  by_contra hne
  apply he
  apply cancel_lemma_6 hne
  have H := congrArg (coeff e) hk
  rw [coeffDiag_lemma_5, prod_ite_pow_eq_two_pow_sum, coeff_add] at H
  rw [H, two_mul]

/- English proof (translation)
Use extensionality with `e`. Rewrite using `[coeff_zero]`. Assume the negation of the conclusion as `he`. Establish `h0` using `row_degree_eq_one_of_aeval_double 0 (aeval_double_fst_of_additive hA1) e he`. Establish `h1` using `row_degree_eq_one_of_aeval_double 1 (aeval_double_snd_of_symm (aeval_double_fst_of_additive hA1) hs) e he`.

Establish `hw : Finsupp.weight 1 e = j` using `hh he`. Rewrite `hw` using `[wt_lemma_11, h0, h1]`. Use linear arithmetic over natural numbers and integers.
-/
theorem zero_of_biadd {h : MvPolynomial (Fin 2 × Fin d) S} {j : ℕ} (hh : h.IsHomogeneous j) (hj2 : j ≠ 2)
    (hA1 : ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) =
      ev2 h (xs S d 0) (xs S d 2) + ev2 h (xs S d 1) (xs S d 2))
    (hs : ev2 h (xs S d 1) (xs S d 0) = h) : h = 0 := by
  ext e
  rw [coeff_zero]
  by_contra he
  have h0 := row_degree_eq_one_of_aeval_double 0 (aeval_double_fst_of_additive hA1) e he
  have h1 := row_degree_eq_one_of_aeval_double 1 (aeval_double_snd_of_symm (aeval_double_fst_of_additive hA1) hs) e he
  have hw : Finsupp.weight 1 e = j := hh he
  rw [wt_lemma_11, h0, h1] at hw
  omega

/- English proof (translation)
Take `⟨hA, hs⟩` from `lead_biadd hj1 hjm fF hF hph1 hsym hP`. Establish `h0` using `zero_of_biadd (homogeneousComponent_isHomogeneous j (P - 1)) hj2 hA hs`. Rewrite `hP`, the goal using `[memIo_lemma]`. Introduce `x hx`. Establish `hle` using `hP x hx`.

Break down `Nat.lt_or_ge j (Finsupp.degree x) with hlt | hge` into its components or cases. Use linear arithmetic over natural numbers and integers. It suffices to derive a contradiction. Establish `hxj : Finsupp.degree x = j` using `le_antisymm hge hle`. Establish `hcx` using `congrArg (coeff x) h0`.

Rewrite `hcx` using `[coeff_homogeneousComponent, if_pos hxj, coeff_zero]`. Conclude with `(MvPolynomial.mem_support_iff.1 hx) hcx`.
-/
theorem stepNo2 {P : MvPolynomial (Fin 2 × Fin d) S} {m j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m) (hj2 : j ≠ 2)
    (fF : Fin d → MvPolynomial (Fin 3 × Fin d) S)
    (hF : ∀ i, fF i - (xs S d 0 i + xs S d 1 i) ∈ Io S (Fin 3 × Fin d) ^ 2)
    (hph1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
      Io S (Fin 3 × Fin d) ^ (m + 1))
    (hsym : ev2 P (xs S d 1) (xs S d 0) - P ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (hP : P - 1 ∈ Io S (Fin 2 × Fin d) ^ j) : P - 1 ∈ Io S (Fin 2 × Fin d) ^ (j + 1) := by
  obtain ⟨hA, hs⟩ := lead_biadd hj1 hjm fF hF hph1 hsym hP
  have h0 := zero_of_biadd (homogeneousComponent_isHomogeneous j (P - 1)) hj2 hA hs
  rw [memIo_lemma] at hP ⊢
  intro x hx
  have hle := hP x hx
  rcases Nat.lt_or_ge j (Finsupp.degree x) with hlt | hge
  · omega
  · exfalso
    have hxj : Finsupp.degree x = j := le_antisymm hge hle
    have hcx := congrArg (coeff x) h0
    rw [coeff_homogeneousComponent, if_pos hxj, coeff_zero] at hcx
    exact (MvPolynomial.mem_support_iff.1 hx) hcx

/- English proof (translation)
Establish `key : ∀ k, 3 + k ≤ m + 1 → P - 1 ∈ Io S (Fin 2 × Fin d) ^ (3 + k)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `_`.

Simplify using `using h3`. Consider the case `succ k ih`. Introduce `hk`. Establish `h` using `stepNo2 (j := 3 + k) (by omega) (by omega) (by omega) fF hF hph1 hsym (ih (by omega))`. Establish `e : 3 + (k + 1) = 3 + k + 1` using `by omega`.

Rewrite using `[e]`. Conclude with `h`. Distinguish the cases in `hm : m + 1 ≤ 3`. Rewrite `h3`, the goal using `[memIo_lemma]`. Introduce `x hx`.

Use `h3 x hx` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h` using `key (m + 1 - 3) (by omega)`. Establish `e : 3 + (m + 1 - 3) = m + 1` using `by omega`. Rewrite `h` using `[e]`.

Conclude with `h`.
-/
theorem eq_one_of_cube {P : MvPolynomial (Fin 2 × Fin d) S} {m : ℕ}
    (fF : Fin d → MvPolynomial (Fin 3 × Fin d) S)
    (hF : ∀ i, fF i - (xs S d 0 i + xs S d 1 i) ∈ Io S (Fin 3 × Fin d) ^ 2)
    (hph1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
      Io S (Fin 3 × Fin d) ^ (m + 1))
    (hsym : ev2 P (xs S d 1) (xs S d 0) - P ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (h3 : P - 1 ∈ Io S (Fin 2 × Fin d) ^ 3) : P - 1 ∈ Io S (Fin 2 × Fin d) ^ (m + 1) := by
  have key : ∀ k, 3 + k ≤ m + 1 → P - 1 ∈ Io S (Fin 2 × Fin d) ^ (3 + k) := by
    intro k
    induction k with
    | zero =>
      intro _
      simpa using h3
    | succ k ih =>
      intro hk
      have h := stepNo2 (j := 3 + k) (by omega) (by omega) (by omega) fF hF hph1 hsym (ih (by omega))
      have e : 3 + (k + 1) = 3 + k + 1 := by omega
      rw [e]
      exact h
  by_cases hm : m + 1 ≤ 3
  · rw [memIo_lemma] at h3 ⊢
    intro x hx
    have := h3 x hx
    omega
  · have h := key (m + 1 - 3) (by omega)
    have e : 3 + (m + 1 - 3) = m + 1 := by omega
    rw [e] at h
    exact h

/- English proof (translation)
Establish `hx : ∀ (k : Fin 3) (i : Fin d), constantCoeff (xs S d k i) = 0`. Introduce `k i`. Simplify using `[xs]`. Establish `hfF : ∀ i, constantCoeff (fF i) = 0`. Introduce `i`.

Establish `h2 : coeff 0 (fF i - (xs S d 0 i + xs S d 1 i)) = 0` using `ccmem_lemma_2 (n := 1) (hF i)`. Rewrite `h2` using `[coeff_sub, coeff_add]`. Establish `h0 : coeff 0 (xs S d 0 i) = 0` using `hx 0 i`. Establish `h1 : coeff 0 (xs S d 1 i) = 0` using `hx 1 i`. Rewrite `h2` using `[h0, h1, add_zero, sub_zero]`.

Conclude with `h2`. Establish `key : ∀ u v : Fin d → MvPolynomial (Fin 3 × Fin d) S, (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → constantCoeff (ev2 P u v) = coeff 0 P`. Introduce `u v hu hv`. Rewrite using `[ev2, ccaeval_lemma_3]`. Both sides reduce to the same expression.

Introduce and unpack `⟨k, i⟩ fin_cases k`. Simplify using `using hu i`. Simplify using `using hv i`. Establish `h1 : constantCoeff (ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2)) = 0` using `ccmem_lemma_2 hph1`. Rewrite `h1` using `[map_sub, map_mul, key _ _ hfF (hx 2), key _ _ (hx 0) (hx 2), key _ _ (hx 1) (hx 2)]`.

Establish `h2 : coeff 0 P * (1 - coeff 0 P) = 0` using `by linear_combination h1`. Take `⟨v, hv⟩` from `hu.exists_left_inv`. Establish `h3 : 1 - coeff 0 P = 0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[memIo_lemma]`.

Introduce `x hx`. Assume the negation of the conclusion as `hlt`. Establish `h0 : Finsupp.degree x = 0` using `by omega`. Establish `hs : ∑ j ∈ x.support, x j = 0` using `h0`. Establish `hx0 : x = 0`.

Use extensionality with `i`. Assume the negation of the conclusion as `hi`. Conclude with `hi ((Finset.sum_eq_zero_iff.1 hs) i (Finsupp.mem_support_iff.2 hi))`. Substitute `hx0` using the available equality. Apply `MvPolynomial.mem_support_iff.1 hx` to reduce the goal to its premises.

Rewrite using `[coeff_sub, coeff_zero_one]`. Take the linear combination `-h3`.
-/
theorem const_one {P : MvPolynomial (Fin 2 × Fin d) S} {m : ℕ}
    (fF : Fin d → MvPolynomial (Fin 3 × Fin d) S)
    (hF : ∀ i, fF i - (xs S d 0 i + xs S d 1 i) ∈ Io S (Fin 3 × Fin d) ^ 2)
    (hph1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
      Io S (Fin 3 × Fin d) ^ (m + 1))
    (hu : IsUnit (coeff 0 P)) : P - 1 ∈ Io S (Fin 2 × Fin d) ^ 1 := by
  have hx : ∀ (k : Fin 3) (i : Fin d), constantCoeff (xs S d k i) = 0 := by
    intro k i
    simp [xs]
  have hfF : ∀ i, constantCoeff (fF i) = 0 := by
    intro i
    have h2 : coeff 0 (fF i - (xs S d 0 i + xs S d 1 i)) = 0 := ccmem_lemma_2 (n := 1) (hF i)
    rw [coeff_sub, coeff_add] at h2
    have h0 : coeff 0 (xs S d 0 i) = 0 := hx 0 i
    have h1 : coeff 0 (xs S d 1 i) = 0 := hx 1 i
    rw [h0, h1, add_zero, sub_zero] at h2
    exact h2
  have key : ∀ u v : Fin d → MvPolynomial (Fin 3 × Fin d) S, (∀ i, constantCoeff (u i) = 0) →
      (∀ i, constantCoeff (v i) = 0) → constantCoeff (ev2 P u v) = coeff 0 P := by
    intro u v hu hv
    rw [ev2, ccaeval_lemma_3]
    · rfl
    · rintro ⟨k, i⟩
      fin_cases k
      · simpa using hu i
      · simpa using hv i
  have h1 : constantCoeff (ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2)) = 0 :=
    ccmem_lemma_2 hph1
  rw [map_sub, map_mul, key _ _ hfF (hx 2), key _ _ (hx 0) (hx 2), key _ _ (hx 1) (hx 2)] at h1
  have h2 : coeff 0 P * (1 - coeff 0 P) = 0 := by linear_combination h1
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have h3 : 1 - coeff 0 P = 0 := by
    calc 1 - coeff 0 P = (v * coeff 0 P) * (1 - coeff 0 P) := by rw [hv, one_mul]
      _ = v * (coeff 0 P * (1 - coeff 0 P)) := by ring
      _ = 0 := by rw [h2, mul_zero]
  rw [memIo_lemma]
  intro x hx
  by_contra hlt
  have h0 : Finsupp.degree x = 0 := by omega
  have hs : ∑ j ∈ x.support, x j = 0 := h0
  have hx0 : x = 0 := by
    ext i
    by_contra hi
    exact hi ((Finset.sum_eq_zero_iff.1 hs) i (Finsupp.mem_support_iff.2 hi))
  subst hx0
  apply MvPolynomial.mem_support_iff.1 hx
  rw [coeff_sub, coeff_zero_one]
  linear_combination -h3

/- English proof (translation)
Rewrite using `[aeval_monomial, algebraMap_eq, monomial_eq, C_mul]`. Simplify using `only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aeval_diag_monomial {σ : Type} (s : σ → S) (e : σ →₀ ℕ) (a : S) :
    aeval (fun p => C (s p) * X p) (monomial e a) = monomial e ((e.prod fun p k => s p ^ k) * a) := by
  rw [aeval_monomial, algebraMap_eq, monomial_eq, C_mul]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  ring

/- English proof (translation)
Use `conv_lhs => rw [h.as_sum]`. Rewrite using `[map_sum, coeff_sum]`. Simplify using `only [aeval_diag_monomial, coeff_monomial]`. Rewrite using `[Finset.sum_eq_single e]`. Rewrite using `[if_pos rfl]`.

Introduce `b _ hb`. Rewrite using `[if_neg hb]`. Introduce `he`. Simplify using `only [MvPolynomial.mem_support_iff, not_not] at he`. Rewrite using `[if_pos rfl, he, mul_zero]`.
-/
theorem coeff_aeval_diag {σ : Type} (s : σ → S) (h : MvPolynomial σ S) (e : σ →₀ ℕ) :
    coeff e (aeval (fun p => C (s p) * X p) h) = (e.prod fun p k => s p ^ k) * coeff e h := by
  classical
  conv_lhs => rw [h.as_sum]
  rw [map_sum, coeff_sum]
  simp only [aeval_diag_monomial, coeff_monomial]
  rw [Finset.sum_eq_single e]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb]
  · intro he
    simp only [MvPolynomial.mem_support_iff, not_not] at he
    rw [if_pos rfl, he, mul_zero]

/- English proof (translation)
Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, Fin.prod_univ_two]`. Apply the tactic sequence `fin_cases k <;> simp [Finset.prod_pow_eq_pow_sum]`.
-/
theorem prod_position (k : Fin 2) (e : Fin 2 × Fin d →₀ ℕ) :
    (e.prod fun p n => (if p.1 = k then (2 : S) else 1) ^ n) = 2 ^ (∑ i, e (k, i)) := by
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, Fin.prod_univ_two]
  fin_cases k <;> simp [Finset.prod_pow_eq_pow_sum]

/- English proof (translation)
Rewrite using `[X, X, monomial_mul, C_mul_monomial, coeff_monomial, mul_one, mul_one]`.
-/
private theorem coeffXX_lemma_15 (c : S) (a b : Fin 2 × Fin d) (e : Fin 2 × Fin d →₀ ℕ) :
    coeff e (C c * (X a * X b)) = if Finsupp.single a 1 + Finsupp.single b 1 = e then c else 0 := by
  rw [X, X, monomial_mul, C_mul_monomial, coeff_monomial, mul_one, mul_one]

/- English proof (translation)
Establish `hsplit` using `Finset.add_sum_erase Finset.univ f (Finset.mem_univ i0)`. Rewrite `hsplit` using `[hs]`. Establish `hi0 : f i0 = 1` using `by omega`. Establish `hrest : ∑ x ∈ Finset.univ.erase i0, f x = 0` using `by omega`. Use `split_ifs with hi`.

Rewrite using `[hi, hi0]`. Conclude with `(Finset.sum_eq_zero_iff.1 hrest) i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩)`.
-/
private theorem one_lemma_16 (f : Fin d → ℕ) (hs : ∑ i, f i = 1) (i0 : Fin d) (h0 : f i0 ≠ 0) (i : Fin d) :
    f i = if i = i0 then 1 else 0 := by
  have hsplit := Finset.add_sum_erase Finset.univ f (Finset.mem_univ i0)
  rw [hs] at hsplit
  have hi0 : f i0 = 1 := by omega
  have hrest : ∑ x ∈ Finset.univ.erase i0, f x = 0 := by omega
  split_ifs with hi
  · rw [hi, hi0]
  · exact (Finset.sum_eq_zero_iff.1 hrest) i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩)

/- English proof (translation)
Establish `h0` using `aeval_double_fst_of_additive hA1`. Establish `h1` using `aeval_double_snd_of_symm h0 hs`. Use extensionality with `e`. Simplify using `only [coeff_sum, coeffXX_lemma_15]`. Distinguish the cases in `hz : coeff e h = 0`.

Rewrite using `[hz]`. Use `symm`. Use `Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun l _ => ?_))` and prove the remaining obligations. Apply the tactic sequence `split_ifs with heq <;> simp only [heq, hz]`. Establish `hs0` using `row_degree_eq_one_of_aeval_double 0 h0 e hz`.

Establish `hs1` using `row_degree_eq_one_of_aeval_double 1 h1 e hz`. Establish `hne0 : ∑ i, e (0, i) ≠ 0`. Rewrite using `[hs0]`. Conclude with `one_ne_zero`. Establish `hne1 : ∑ i, e (1, i) ≠ 0`.

Rewrite using `[hs1]`. Conclude with `one_ne_zero`. Take `⟨i0, -, hi0⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hne0`. Take `⟨l0, -, hl0⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hne1`. Establish `hE : e = Finsupp.single ((0 : Fin 2), i0) 1 + Finsupp.single ((1 : Fin 2), l0) 1`.

Use extensionality with `⟨k, i⟩`. Use `revert k`. Rewrite using `[Fin.forall_fin_two]`. Prove the components needed by the constructor for the conclusion. Establish `hu` using `one_lemma_16 (fun i => e (0, i)) hs0 i0 hi0 i`.

Rewrite using `[hu]`. Distinguish the cases in `hii : i = i0`. Substitute `hii` using the available equality. Simplify using `[Finsupp.single_apply]`. Simplify using `[Finsupp.single_apply, hii, Ne.symm hii]`.

Establish `hu` using `one_lemma_16 (fun i => e (1, i)) hs1 l0 hl0 i`. Rewrite using `[hu]`. Distinguish the cases in `hii : i = l0`. Substitute `hii` using the available equality. Simplify using `[Finsupp.single_apply]`.

Simplify using `[Finsupp.single_apply, hii, Ne.symm hii]`. Substitute `hE` using the available equality. Rewrite using `[Finset.sum_eq_single i0, Finset.sum_eq_single l0, if_pos rfl]`. Introduce `l _ hl`. Rewrite using `[if_neg]`.

Introduce `heq`. Use `congrArg (fun f => f ((1 : Fin 2), l)) heq` as an intermediate fact. Simplify using `[Finsupp.single_apply, Ne.symm hl] at this`. Introduce `h'`. Conclude with `absurd (Finset.mem_univ _) h'`.

Introduce `i _ hi`. Use `Finset.sum_eq_zero (fun l _ => ?_)` and prove the remaining obligations. Rewrite using `[if_neg]`. Introduce `heq`. Use `congrArg (fun f => f ((0 : Fin 2), i)) heq` as an intermediate fact.

Simplify using `[Finsupp.single_apply, Ne.symm hi] at this`. Introduce `h'`. Conclude with `absurd (Finset.mem_univ _) h'`.
-/
theorem bilin_of_biadd {h : MvPolynomial (Fin 2 × Fin d) S}
    (hA1 : ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) =
      ev2 h (xs S d 0) (xs S d 2) + ev2 h (xs S d 1) (xs S d 2))
    (hs : ev2 h (xs S d 1) (xs S d 0) = h) :
    h = ∑ i, ∑ l, C (coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), l) 1) h) *
      (X ((0 : Fin 2), i) * X ((1 : Fin 2), l)) := by
  have h0 := aeval_double_fst_of_additive hA1
  have h1 := aeval_double_snd_of_symm h0 hs
  ext e
  simp only [coeff_sum, coeffXX_lemma_15]
  by_cases hz : coeff e h = 0
  · rw [hz]
    symm
    refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun l _ => ?_))
    split_ifs with heq <;> simp only [heq, hz]
  · have hs0 := row_degree_eq_one_of_aeval_double 0 h0 e hz
    have hs1 := row_degree_eq_one_of_aeval_double 1 h1 e hz
    have hne0 : ∑ i, e (0, i) ≠ 0 := by
      rw [hs0]
      exact one_ne_zero
    have hne1 : ∑ i, e (1, i) ≠ 0 := by
      rw [hs1]
      exact one_ne_zero
    obtain ⟨i0, -, hi0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne0
    obtain ⟨l0, -, hl0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne1
    have hE : e = Finsupp.single ((0 : Fin 2), i0) 1 + Finsupp.single ((1 : Fin 2), l0) 1 := by
      ext ⟨k, i⟩
      revert k
      rw [Fin.forall_fin_two]
      constructor
      · have hu := one_lemma_16 (fun i => e (0, i)) hs0 i0 hi0 i
        rw [hu]
        by_cases hii : i = i0
        · subst hii
          simp [Finsupp.single_apply]
        · simp [Finsupp.single_apply, hii, Ne.symm hii]
      · have hu := one_lemma_16 (fun i => e (1, i)) hs1 l0 hl0 i
        rw [hu]
        by_cases hii : i = l0
        · subst hii
          simp [Finsupp.single_apply]
        · simp [Finsupp.single_apply, hii, Ne.symm hii]
    subst hE
    rw [Finset.sum_eq_single i0, Finset.sum_eq_single l0, if_pos rfl]
    · intro l _ hl
      rw [if_neg]
      intro heq
      have := congrArg (fun f => f ((1 : Fin 2), l)) heq
      simp [Finsupp.single_apply, Ne.symm hl] at this
    · intro h'
      exact absurd (Finset.mem_univ _) h'
    · intro i _ hi
      refine Finset.sum_eq_zero (fun l _ => ?_)
      rw [if_neg]
      intro heq
      have := congrArg (fun f => f ((0 : Fin 2), i)) heq
      simp [Finsupp.single_apply, Ne.symm hi] at this
    · intro h'
      exact absurd (Finset.mem_univ _) h'

end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1

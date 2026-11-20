import Formalism.MahlerMeasure.MahlerMeasureProofs.RemoveS
import Formalism.MahlerMeasure.MahlerMeasureProofs.LevelDecomp
import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.ScalSum

namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset

section
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ)

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[pow_succ' a m, mul_assoc, ← ih, pow_succ']`. Use `show LinearMap.mulLeft k a ((LinearMap.mulLeft k a ^ m) f) = _`.

Rewrite using `[LinearMap.mulLeft_apply]`.
-/
theorem mulLeft_pow_apply (a f : MvPolynomial σ k) (m : ℕ) :
    ((LinearMap.mulLeft k a) ^ m) f = a ^ m * f := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ' a m, mul_assoc, ← ih, pow_succ']
    show LinearMap.mulLeft k a ((LinearMap.mulLeft k a ^ m) f) = _
    rw [LinearMap.mulLeft_apply]

/- English proof (translation)
Rewrite using `[Derivation.leibniz, h, smul_zero, add_zero, smul_eq_mul]`.
-/
private lemma pderiv_mul_of_pderiv_eq_zero (i : σ) (q f : MvPolynomial σ k) (h : pderiv i q = 0) :
    pderiv i (q * f) = q * pderiv i f := by
  rw [Derivation.leibniz, h, smul_zero, add_zero, smul_eq_mul]

/- English proof (translation)
Establish `key : ∀ g : MvPolynomial σ k, tieF w e g = ∑ c, pderiv (w c) (pderiv (e c) g)`. Introduce `g`. Simplify using `[tieF]`. Rewrite using `[key, key, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[pderiv_mul_of_pderiv_eq_zero _ _ _ (he c), pderiv_mul_of_pderiv_eq_zero _ _ _ (hw c)]`.
-/
theorem tieF_mul_free (q f : MvPolynomial σ k) (hw : ∀ c, pderiv (w c) q = 0) (he : ∀ c, pderiv (e c) q = 0) :
    tieF w e (q * f) = q * tieF w e f := by
  have key : ∀ g : MvPolynomial σ k, tieF w e g = ∑ c, pderiv (w c) (pderiv (e c) g) := by
    intro g
    simp [tieF]
  rw [key, key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pderiv_mul_of_pderiv_eq_zero _ _ _ (he c), pderiv_mul_of_pderiv_eq_zero _ _ _ (hw c)]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[pow_succ']`. Use `show tieF w e ((tieF w e ^ m) (q * f)) = q * tieF w e ((tieF w e ^ m) f)`.

Rewrite using `[ih, tieF_mul_free w e q _ hw he]`.
-/
theorem tieF_pow_mul_free (q f : MvPolynomial σ k) (hw : ∀ c, pderiv (w c) q = 0)
    (he : ∀ c, pderiv (e c) q = 0) (m : ℕ) :
    (tieF w e ^ m) (q * f) = q * (tieF w e ^ m) f := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ']
    show tieF w e ((tieF w e ^ m) (q * f)) = q * tieF w e ((tieF w e ^ m) f)
    rw [ih, tieF_mul_free w e q _ hw he]

noncomputable def ehP : MvPolynomial σ k := X zv * X sv + ∑ c, X (w c) * X (e c)

/- English proof (translation)
Rewrite using `[Derivation.leibniz_pow]`. Simplify using `[pderiv_X, Pi.single_apply, Ne.symm h]`.
-/
private lemma pderiv_X_pow_of_ne' (i j : σ) (h : i ≠ j) (n : ℕ) : pderiv i (X j ^ n : MvPolynomial σ k) = 0 := by
  classical
  rw [Derivation.leibniz_pow]
  simp [pderiv_X, Pi.single_apply, Ne.symm h]

/- English proof (translation)
Establish `hE : ∀ (m : ℕ) (y : MvPolynomial σ k), (M.tieEh w e zv sv ^ m) y = ehP w e zv sv ^ m * y`. Introduce `m y`. Unfold `M.tieEh`. Conclude with `mulLeft_pow_apply _ _ m`. Unfold `M.tieP`.

Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[tieF_pow_mul_free w e _ x (fun c => pderiv_X_pow_of_ne' _ _ (hz c).1 z) (fun c => pderiv_X_pow_of_ne' _ _ (hz c).2 z) m, hE]`.
-/
theorem harmonicProjection_expand (hz : ∀ c, w c ≠ zv ∧ e c ≠ zv) (o n z : ℕ) (x : MvPolynomial σ k) :
    M.tieP w e zv sv o n z x = ∑ m ∈ range (o + 1),
      (((-1 : k) ^ m) / (((m.factorial : k) ^ 2) * ((o + n + r + z - 1).choose m : k))) •
        (ehP w e zv sv ^ m * (X zv ^ z * (tieF w e ^ m) x)) := by
  have hE : ∀ (m : ℕ) (y : MvPolynomial σ k),
      (M.tieEh w e zv sv ^ m) y = ehP w e zv sv ^ m * y := by
    intro m y
    unfold M.tieEh
    exact mulLeft_pow_apply _ _ m
  unfold M.tieP
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  rw [tieF_pow_mul_free w e _ x (fun c => pderiv_X_pow_of_ne' _ _ (hz c).1 z)
    (fun c => pderiv_X_pow_of_ne' _ _ (hz c).2 z) m, hE]

/- English proof (translation)
Establish `hp : pderiv i p = ∑ s ∈ p.support, pderiv i (monomial s (coeff s p))` using `by conv_lhs => rw [p.as_sum]`. Rewrite using `[map_sum]`. Rewrite `ht` using `[MvPolynomial.mem_support_iff, hp, MvPolynomial.coeff_sum]`. Take `⟨s, hs, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero ht`. Rewrite `hne` using `[pderiv_monomial, MvPolynomial.coeff_monomial]`.

Use `split_ifs at hne with hst`. Establish `hsi : s i ≠ 0`. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Rewrite using `[h0]`.

Simplify using the standard rewrite rules. Establish `hts : t + Finsupp.single i 1 = s`. Rewrite using `[← hst]`. Use extensionality with `j`. Rewrite using `[Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]`.

Use `split_ifs with h`. Substitute `h` using the available equality. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Rewrite using `[hts]`.

Conclude with `hs`. Conclude with `absurd rfl hne`.
-/
private lemma add_single_mem_support_of_mem_support_pderiv (i : σ) (p : MvPolynomial σ k) (t : σ →₀ ℕ) (ht : t ∈ (pderiv i p).support) :
    t + Finsupp.single i 1 ∈ p.support := by
  classical
  have hp : pderiv i p = ∑ s ∈ p.support, pderiv i (monomial s (coeff s p)) := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
  rw [MvPolynomial.mem_support_iff, hp, MvPolynomial.coeff_sum] at ht
  obtain ⟨s, hs, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht
  rw [pderiv_monomial, MvPolynomial.coeff_monomial] at hne
  split_ifs at hne with hst
  · have hsi : s i ≠ 0 := by
      intro h0
      apply hne
      rw [h0]
      simp
    have hts : t + Finsupp.single i 1 = s := by
      rw [← hst]
      ext j
      rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs with h
      · subst h
        omega
      · omega
    rw [hts]
    exact hs
  · exact absurd rfl hne

/- English proof (translation)
Establish `hsupp : ∀ (y : MvPolynomial σ k) (t : σ →₀ ℕ), t ∈ (tieF w e y).support → ∃ c, t + Finsupp.single (w c) 1 + Finsupp.single (e c) 1 ∈ y.support`. Introduce `y t ht`. Establish `key : tieF w e y = ∑ c, pderiv (w c) (pderiv (e c) y)` using `by simp [tieF]`. Rewrite `ht` using `[key]`. Take `⟨c, -, hc⟩` from `Finset.mem_biUnion.mp (MvPolynomial.support_sum ht)`.

Conclude with `⟨c, add_single_mem_support_of_mem_support_pderiv _ _ _ (add_single_mem_support_of_mem_support_pderiv _ _ _ hc)⟩`. Establish `hW1 : ∀ (t : σ →₀ ℕ) (c : Fin r), (∑ d, (t + Finsupp.single (w c) 1 + Finsupp.single (e c) 1 : σ →₀ ℕ) (w d)) = (∑ d, t (w d)) + 1`. Introduce `t c`. Establish `h1 : ∀ d, (e c = w d) ↔ False` using `fun d => ⟨fun h => hwe d c h.symm, False.elim⟩`. Simplify using `[Finsupp.single_apply, hw.eq_iff, Finset.sum_add_distrib, h1]`.

Establish `hE1 : ∀ (t : σ →₀ ℕ) (c : Fin r), (∑ d, (t + Finsupp.single (w c) 1 + Finsupp.single (e c) 1 : σ →₀ ℕ) (e d)) = (∑ d, t (e d)) + 1`. Introduce `t c`. Establish `h1 : ∀ d, (w c = e d) ↔ False` using `fun d => ⟨fun h => hwe c d h, False.elim⟩`. Simplify using `[Finsupp.single_apply, he.eq_iff, Finset.sum_add_distrib, h1]`. Establish `claim : ∀ (j : ℕ) (t : σ →₀ ℕ), t ∈ ((tieF w e ^ j) x).support → (∑ d, t (w d)) + j = o ∧ (∑ d, t (e d)) + j = n`.

Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `t ht`. Establish `ht' : t ∈ x.support` using `by simpa using ht`.

Simplify using `using hx t ht'`. Consider the case `succ j ih`. Introduce `t ht`. Establish `ht' : t ∈ (tieF w e ((tieF w e ^ j) x)).support`. Rewrite `ht` using `[pow_succ']`.

Conclude with `ht`. Take `⟨c, hc⟩` from `hsupp _ t ht'`. Take `⟨h1, h2⟩` from `ih _ hc`. Rewrite `h1` using `[hW1]`. Rewrite `h2` using `[hE1]`.

Apply the tactic sequence `constructor <;> omega`. Introduce `m hm`. Assume the negation of the conclusion as `hne`. Take `⟨t, ht⟩` from `MvPolynomial.ne_zero_iff.mp hne`. Take `⟨h1, h2⟩` from `claim m t (MvPolynomial.mem_support_iff.mpr ht)`.

Use linear arithmetic over natural numbers and integers.
-/
theorem tieF_pow_apply_eq_zero_of_min_lt [CharZero k] (hw : Function.Injective w) (he : Function.Injective e)
    (hwe : ∀ c d, w c ≠ e d) {o n : ℕ} {x : MvPolynomial σ k} (hx : BiHom w e o n x) :
    ∀ m, min o n < m → (tieF w e ^ m) x = 0 := by
  classical
  have hsupp : ∀ (y : MvPolynomial σ k) (t : σ →₀ ℕ), t ∈ (tieF w e y).support →
      ∃ c, t + Finsupp.single (w c) 1 + Finsupp.single (e c) 1 ∈ y.support := by
    intro y t ht
    have key : tieF w e y = ∑ c, pderiv (w c) (pderiv (e c) y) := by simp [tieF]
    rw [key] at ht
    obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum ht)
    exact ⟨c, add_single_mem_support_of_mem_support_pderiv _ _ _ (add_single_mem_support_of_mem_support_pderiv _ _ _ hc)⟩
  have hW1 : ∀ (t : σ →₀ ℕ) (c : Fin r),
      (∑ d, (t + Finsupp.single (w c) 1 + Finsupp.single (e c) 1 : σ →₀ ℕ) (w d)) = (∑ d, t (w d)) + 1 := by
    intro t c
    have h1 : ∀ d, (e c = w d) ↔ False := fun d => ⟨fun h => hwe d c h.symm, False.elim⟩
    simp [Finsupp.single_apply, hw.eq_iff, Finset.sum_add_distrib, h1]
  have hE1 : ∀ (t : σ →₀ ℕ) (c : Fin r),
      (∑ d, (t + Finsupp.single (w c) 1 + Finsupp.single (e c) 1 : σ →₀ ℕ) (e d)) = (∑ d, t (e d)) + 1 := by
    intro t c
    have h1 : ∀ d, (w c = e d) ↔ False := fun d => ⟨fun h => hwe c d h, False.elim⟩
    simp [Finsupp.single_apply, he.eq_iff, Finset.sum_add_distrib, h1]
  have claim : ∀ (j : ℕ) (t : σ →₀ ℕ), t ∈ ((tieF w e ^ j) x).support →
      (∑ d, t (w d)) + j = o ∧ (∑ d, t (e d)) + j = n := by
    intro j
    induction j with
    | zero =>
      intro t ht
      have ht' : t ∈ x.support := by simpa using ht
      simpa using hx t ht'
    | succ j ih =>
      intro t ht
      have ht' : t ∈ (tieF w e ((tieF w e ^ j) x)).support := by
        rw [pow_succ'] at ht
        exact ht
      obtain ⟨c, hc⟩ := hsupp _ t ht'
      obtain ⟨h1, h2⟩ := ih _ hc
      rw [hW1] at h1
      rw [hE1] at h2
      constructor <;> omega
  intro m hm
  by_contra hne
  obtain ⟨t, ht⟩ := MvPolynomial.ne_zero_iff.mp hne
  obtain ⟨h1, h2⟩ := claim m t (MvPolynomial.mem_support_iff.mpr ht)
  omega

/- English proof (translation)
Rewrite using `[eq_div_iff (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero b)))]`. Establish `h` using `Nat.add_choose_mul_factorial_mul_factorial a b`. Rewrite `h` using `[mul_assoc]`. Conclude with `h` after adjusting the coercions.
-/
private lemma cast_choose_add_eq_factorial_div_of_charZero [CharZero k] (a b : ℕ) :
    (((a + b).choose b : ℕ) : k) = ((a + b).factorial : k) / ((a.factorial : k) * (b.factorial : k)) := by
  rw [eq_div_iff (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero b)))]
  have h := Nat.add_choose_mul_factorial_mul_factorial a b
  rw [mul_assoc] at h
  exact_mod_cast h

/- English proof (translation)
Take `⟨c, hc⟩ : ∃ c : ℕ → k, ∀ l, c l = (-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((N - 2 * l - 1).choose (j - l) : k)) * ((l.factorial : k) ^ 2 * ((N - l).choose l : k))⁻¹` from `⟨_, fun _ => rfl⟩`. Take `⟨W, hW⟩ : ∃ W : ℕ → k, ∀ l, W l = if l ≤ j then c l * (((l : ℕ) : k) * ((N - l - j : ℕ) : k)) / ((j : k) * ((N - 2 * l : ℕ) : k)) else 0` from `⟨_, fun _ => rfl⟩`. Establish `key : ∀ l ∈ range (j + 1), c l = W l - W (l + 1)`. Introduce `l hl`. Establish `hl' : l ≤ j` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)`.

Break down `Nat.eq_or_lt_of_le hl' with hlj | hlj` into its components or cases. Establish `hne : (((l : ℕ) : k) * ((N - 2 * l : ℕ) : k)) ≠ 0` using `mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega))`. Rewrite using `[hW, hW, ← hlj, if_pos le_rfl, if_neg (by omega), sub_zero, show N - l - l = N - 2 * l by omega, mul_div_assoc, div_self hne, mul_one]`. Take `⟨u, hu⟩ : ∃ u, j = l + 1 + u` from `⟨j - l - 1, by omega⟩`. Take `⟨v, hv⟩ : ∃ v, N = 2 * j + 1 + v` from `⟨N - 2 * j - 1, by omega⟩`.

Rewrite using `[hW, hW, if_pos hl', if_pos (by omega), hc, hc]`. Rewrite using `[show N - l - j = u + 2 + v by omega, show N - 2 * l - 1 = u + 1 + v + (u + 1) by omega, show N - 2 * l = 2 * u + 3 + v by omega, show N - l = 2 * u + 3 + v + l by omega, show j - l = u + 1 by omega, show N - (l + 1) - j = u + 1 + v by omega, show N - 2 * (l + 1) - 1 = u + v + u …`. Rewrite using `[cast_choose_add_eq_factorial_div_of_charZero (u + 1 + v) (u + 1), cast_choose_add_eq_factorial_div_of_charZero (2 * u + 3 + v) l, cast_choose_add_eq_factorial_div_of_charZero (u + v) u, cast_choose_add_eq_factorial_div_of_charZero (2 * u + 1 + v) (l + 1), hu]`. Establish `F1 : ((u + 1).factorial : k) = ((u + 1 : ℕ) : k) * (u.factorial : k)`. Rewrite using `[Nat.factorial_succ]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `F2 : ((u + 1 + v).factorial : k) = ((u + 1 + v : ℕ) : k) * ((u + v).factorial : k)`. Rewrite using `[show u + 1 + v = u + v + 1 by ring, Nat.factorial_succ]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `F3 : ((u + 1 + v + (u + 1)).factorial : k) = ((u + v + u + 2 : ℕ) : k) * ((u + v + u + 1 : ℕ) : k) * ((u + v + u).factorial : k)`. Rewrite using `[show u + 1 + v + (u + 1) = u + v + u + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `F4 : ((2 * u + 3 + v + l).factorial : k) = ((2 * u + 3 + v + l : ℕ) : k) * ((2 * u + 1 + v + (l + 1)).factorial : k)`. Rewrite using `[show 2 * u + 3 + v + l = 2 * u + 1 + v + (l + 1) + 1 by ring, Nat.factorial_succ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `F5 : ((2 * u + 3 + v).factorial : k) = ((u + v + u + 3 : ℕ) : k) * ((u + v + u + 2 : ℕ) : k) * ((u + v + u + 1 : ℕ) : k) * ((u + v + u).factorial : k)`.

Rewrite using `[show 2 * u + 3 + v = u + v + u + 1 + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `F6 : ((l + 1).factorial : k) = ((l + 1 : ℕ) : k) * (l.factorial : k)`. Rewrite using `[Nat.factorial_succ]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `F7 : ((2 * u + 1 + v).factorial : k) = ((u + v + u + 1 : ℕ) : k) * ((u + v + u).factorial : k)`. Rewrite using `[show 2 * u + 1 + v = u + v + u + 1 by ring, Nat.factorial_succ]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[F3, F4, F5, F7, F2, F1, F6]`. Use `clear hW hc W c hl hl' hlj hu hv hj hN F1 F2 F3 F4 F5 F6 F7`. Establish `nB1 : ((u.factorial : ℕ) : k) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)`. Generalize the expression as in `hB1 : ((u.factorial : ℕ) : k) = B1 at nB1 ⊢`.

Establish `nB2 : (((u + v).factorial : ℕ) : k) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)`. Generalize the expression as in `hB2 : (((u + v).factorial : ℕ) : k) = B2 at nB2 ⊢`. Establish `nB3 : (((u + v + u).factorial : ℕ) : k) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)`. Generalize the expression as in `hB3 : (((u + v + u).factorial : ℕ) : k) = B3 at nB3 ⊢`. Establish `nB4 : ((l.factorial : ℕ) : k) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)`.

Generalize the expression as in `hB4 : ((l.factorial : ℕ) : k) = B4 at nB4 ⊢`. Establish `nB5 : (((2 * u + 1 + v + (l + 1)).factorial : ℕ) : k) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)`. Generalize the expression as in `hB5 : (((2 * u + 1 + v + (l + 1)).factorial : ℕ) : k) = B5 at nB5 ⊢`. Establish `nL1 : ((u + 1 : ℕ) : k) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`. Generalize the expression as in `hL1 : ((u + 1 : ℕ) : k) = L1 at nL1 ⊢`.

Establish `nL2 : ((u + 1 + v : ℕ) : k) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`. Generalize the expression as in `hL2 : ((u + 1 + v : ℕ) : k) = L2 at nL2 ⊢`. Establish `nL3 : ((u + v + u + 2 : ℕ) : k) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`. Generalize the expression as in `hL3 : ((u + v + u + 2 : ℕ) : k) = L3 at nL3 ⊢`. Establish `nL4 : ((u + v + u + 1 : ℕ) : k) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`.

Generalize the expression as in `hL4 : ((u + v + u + 1 : ℕ) : k) = L4 at nL4 ⊢`. Establish `nL5 : ((2 * u + 3 + v + l : ℕ) : k) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`. Generalize the expression as in `hL5 : ((2 * u + 3 + v + l : ℕ) : k) = L5 at nL5 ⊢`. Establish `nL6 : ((u + v + u + 3 : ℕ) : k) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`. Generalize the expression as in `hL6 : ((u + v + u + 3 : ℕ) : k) = L6 at nL6 ⊢`.

Establish `nL7 : ((l + 1 : ℕ) : k) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`. Generalize the expression as in `hL7 : ((l + 1 : ℕ) : k) = L7 at nL7 ⊢`. Establish `nL8 : ((l + 1 + u : ℕ) : k) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`. Generalize the expression as in `hL8 : ((l + 1 + u : ℕ) : k) = L8 at nL8 ⊢`. Establish `nL9 : ((2 * u + 3 + v : ℕ) : k) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`.

Generalize the expression as in `hL9 : ((2 * u + 3 + v : ℕ) : k) = liftZP_newton at nL9 ⊢`. Establish `nL10 : ((2 * u + 1 + v : ℕ) : k) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`. Generalize the expression as in `hL10 : ((2 * u + 1 + v : ℕ) : k) = ParameterUpperBound at nL10 ⊢`. Clear denominators, using `[nB1, nB2, nB3, nB4, nB5, nL1, nL2, nL3, nL4, nL5, nL6, nL7, nL8, nL9, nL10]` for the nonvanishing conditions. Substitute `hB1 hB2 hB3 hB4 hB5 hL1 hL2 hL3 hL4 hL5 hL6 hL7 hL8 hL9 hL10` using the available equality.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [← hc]`. Rewrite using `[Finset.sum_congr rfl key, Finset.sum_range_sub', hW, hW, if_pos (Nat.zero_le _), if_neg (by omega)]`. Simplify using the standard rewrite rules.
-/
private lemma factorial_choose_signed_sum_eq_zero [CharZero k] (N j : ℕ) (hj : 1 ≤ j) (hN : 2 * j + 1 ≤ N) :
    ∑ l ∈ range (j + 1), (-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((N - 2 * l - 1).choose (j - l) : k)) *
      ((l.factorial : k) ^ 2 * ((N - l).choose l : k))⁻¹ = 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → k, ∀ l, c l = (-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 *
      ((N - 2 * l - 1).choose (j - l) : k)) * ((l.factorial : k) ^ 2 * ((N - l).choose l : k))⁻¹ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℕ → k, ∀ l, W l = if l ≤ j then c l * (((l : ℕ) : k) * ((N - l - j : ℕ) : k)) /
      ((j : k) * ((N - 2 * l : ℕ) : k)) else 0 := ⟨_, fun _ => rfl⟩
  have key : ∀ l ∈ range (j + 1), c l = W l - W (l + 1) := by
    intro l hl
    have hl' : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    rcases Nat.eq_or_lt_of_le hl' with hlj | hlj
    · have hne : (((l : ℕ) : k) * ((N - 2 * l : ℕ) : k)) ≠ 0 :=
        mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega))
      rw [hW, hW, ← hlj, if_pos le_rfl, if_neg (by omega), sub_zero, show N - l - l = N - 2 * l by omega,
        mul_div_assoc, div_self hne, mul_one]
    · obtain ⟨u, hu⟩ : ∃ u, j = l + 1 + u := ⟨j - l - 1, by omega⟩
      obtain ⟨v, hv⟩ : ∃ v, N = 2 * j + 1 + v := ⟨N - 2 * j - 1, by omega⟩
      rw [hW, hW, if_pos hl', if_pos (by omega), hc, hc]
      rw [show N - l - j = u + 2 + v by omega, show N - 2 * l - 1 = u + 1 + v + (u + 1) by omega,
        show N - 2 * l = 2 * u + 3 + v by omega, show N - l = 2 * u + 3 + v + l by omega,
        show j - l = u + 1 by omega,
        show N - (l + 1) - j = u + 1 + v by omega, show N - 2 * (l + 1) - 1 = u + v + u by omega,
        show N - 2 * (l + 1) = 2 * u + 1 + v by omega, show N - (l + 1) = 2 * u + 1 + v + (l + 1) by omega,
        show j - (l + 1) = u by omega]
      rw [cast_choose_add_eq_factorial_div_of_charZero (u + 1 + v) (u + 1), cast_choose_add_eq_factorial_div_of_charZero (2 * u + 3 + v) l,
        cast_choose_add_eq_factorial_div_of_charZero (u + v) u, cast_choose_add_eq_factorial_div_of_charZero (2 * u + 1 + v) (l + 1), hu]
      have F1 : ((u + 1).factorial : k) = ((u + 1 : ℕ) : k) * (u.factorial : k) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have F2 : ((u + 1 + v).factorial : k) = ((u + 1 + v : ℕ) : k) * ((u + v).factorial : k) := by
        rw [show u + 1 + v = u + v + 1 by ring, Nat.factorial_succ]
        push_cast
        ring
      have F3 : ((u + 1 + v + (u + 1)).factorial : k) =
          ((u + v + u + 2 : ℕ) : k) * ((u + v + u + 1 : ℕ) : k) * ((u + v + u).factorial : k) := by
        rw [show u + 1 + v + (u + 1) = u + v + u + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
        push_cast
        ring
      have F4 : ((2 * u + 3 + v + l).factorial : k) =
          ((2 * u + 3 + v + l : ℕ) : k) * ((2 * u + 1 + v + (l + 1)).factorial : k) := by
        rw [show 2 * u + 3 + v + l = 2 * u + 1 + v + (l + 1) + 1 by ring, Nat.factorial_succ]
        push_cast
        ring
      have F5 : ((2 * u + 3 + v).factorial : k) = ((u + v + u + 3 : ℕ) : k) * ((u + v + u + 2 : ℕ) : k) *
          ((u + v + u + 1 : ℕ) : k) * ((u + v + u).factorial : k) := by
        rw [show 2 * u + 3 + v = u + v + u + 1 + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
          Nat.factorial_succ]
        push_cast
        ring
      have F6 : ((l + 1).factorial : k) = ((l + 1 : ℕ) : k) * (l.factorial : k) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have F7 : ((2 * u + 1 + v).factorial : k) = ((u + v + u + 1 : ℕ) : k) * ((u + v + u).factorial : k) := by
        rw [show 2 * u + 1 + v = u + v + u + 1 by ring, Nat.factorial_succ]
        push_cast
        ring
      rw [F3, F4, F5, F7, F2, F1, F6]
      clear hW hc W c hl hl' hlj hu hv hj hN F1 F2 F3 F4 F5 F6 F7
      have nB1 : ((u.factorial : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      generalize hB1 : ((u.factorial : ℕ) : k) = B1 at nB1 ⊢
      have nB2 : (((u + v).factorial : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      generalize hB2 : (((u + v).factorial : ℕ) : k) = B2 at nB2 ⊢
      have nB3 : (((u + v + u).factorial : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      generalize hB3 : (((u + v + u).factorial : ℕ) : k) = B3 at nB3 ⊢
      have nB4 : ((l.factorial : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      generalize hB4 : ((l.factorial : ℕ) : k) = B4 at nB4 ⊢
      have nB5 : (((2 * u + 1 + v + (l + 1)).factorial : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      generalize hB5 : (((2 * u + 1 + v + (l + 1)).factorial : ℕ) : k) = B5 at nB5 ⊢
      have nL1 : ((u + 1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL1 : ((u + 1 : ℕ) : k) = L1 at nL1 ⊢
      have nL2 : ((u + 1 + v : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL2 : ((u + 1 + v : ℕ) : k) = L2 at nL2 ⊢
      have nL3 : ((u + v + u + 2 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL3 : ((u + v + u + 2 : ℕ) : k) = L3 at nL3 ⊢
      have nL4 : ((u + v + u + 1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL4 : ((u + v + u + 1 : ℕ) : k) = L4 at nL4 ⊢
      have nL5 : ((2 * u + 3 + v + l : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL5 : ((2 * u + 3 + v + l : ℕ) : k) = L5 at nL5 ⊢
      have nL6 : ((u + v + u + 3 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL6 : ((u + v + u + 3 : ℕ) : k) = L6 at nL6 ⊢
      have nL7 : ((l + 1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL7 : ((l + 1 : ℕ) : k) = L7 at nL7 ⊢
      have nL8 : ((l + 1 + u : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL8 : ((l + 1 + u : ℕ) : k) = L8 at nL8 ⊢
      have nL9 : ((2 * u + 3 + v : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL9 : ((2 * u + 3 + v : ℕ) : k) = liftZP_newton at nL9 ⊢
      have nL10 : ((2 * u + 1 + v : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL10 : ((2 * u + 1 + v : ℕ) : k) = ParameterUpperBound at nL10 ⊢
      field_simp [nB1, nB2, nB3, nB4, nB5, nL1, nL2, nL3, nL4, nL5, nL6, nL7, nL8, nL9, nL10]
      subst hB1 hB2 hB3 hB4 hB5 hL1 hL2 hL3 hL4 hL5 hL6 hL7 hL8 hL9 hL10
      push_cast
      ring
  simp only [← hc]
  rw [Finset.sum_congr rfl key, Finset.sum_range_sub', hW, hW, if_pos (Nat.zero_le _), if_neg (by omega)]
  simp

/- English proof (translation)
Establish `hT : ∀ l m : ℕ, (tieF w e ^ m) ((tieF w e ^ l) x) = (tieF w e ^ (l + m)) x`. Introduce `l m`. Rewrite using `[add_comm, pow_add]`. Both sides reduce to the same expression. Establish `hterm : ∀ l ∈ range (min o n + 1), ehP w e zv sv ^ l * M.tieP w e zv sv (o - l) (n - l) z (((((l.factorial : k)) ^ 2 * ((o + n + r + z - l).choose l : k)))⁻¹ • (tieF w e ^ l) x) = ∑ m ∈ range (min o n - l + 1), ((-1 : k) ^ m / (((m).factorial : k) ^ 2 * ((o - l + (n - l) + r + z …`.

Introduce `l hl`. Establish `hlL : l ≤ min o n` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)`. Establish `hsub : range (min o n - l + 1) ⊆ range (o - l + 1)`. Introduce `m hm`. Simplify using `only [Finset.mem_range] at hm ⊢`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[harmonicProjection_expand w e zv sv hz, Finset.mul_sum, ← Finset.sum_subset hsub]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smul, hT]`. Simplify using `only [MvPolynomial.smul_eq_C_mul, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `m _ hm`. Simplify using `only [Finset.mem_range, not_lt] at hm`. Establish `h0 : (tieF w e ^ (l + m)) x = 0` using `hv (l + m) (by omega)`. Simplify using `[LinearMap.map_smul, hT, h0]`.

Establish `hre : ∀ l ∈ range (min o n + 1), ∑ m ∈ range (min o n - l + 1), ((-1 : k) ^ m / (((m).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (m) : k)) * (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (l + m) * (X zv ^ z * (tieF w e ^ (l + …`. Introduce `l hl`. Establish `hlL : l ≤ min o n` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)`. Rewrite using `[Finset.sum_Ico_eq_sum_range, show min o n + 1 - l = min o n - l + 1 by omega]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[Nat.add_sub_cancel_left]`. Establish `hcomm : ∑ l ∈ range (min o n + 1), ∑ j ∈ Ico l (min o n + 1), ((-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (j - l) : k)) * (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (j) * (X zv ^ z * (tieF w …` using `Finset.sum_comm' (fun l j => by simp only [Finset.mem_range, Finset.mem_Ico]; omega)`. Establish `hid : ∀ j ∈ range (min o n + 1), ∑ l ∈ range (j + 1), ((-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (j - l) : k)) * (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (j) * (X zv ^ z * (tieF w e ^ (j)) …`. Introduce `j hj`. Establish `hjL : j ≤ min o n` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)`.

Rewrite using `[← Finset.sum_smul]`. Break down `Nat.eq_zero_or_pos j with h0 | hpos` into its components or cases. Substitute `h0` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg (by omega)]`.

Establish `hc2 : ∑ l ∈ range (j + 1), ((-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (j - l) : k)) * (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) = 0`. Use `Eq.trans ?_ (factorial_choose_signed_sum_eq_zero (o + n + r + z) j hpos (by omega))` and prove the remaining obligations. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations. Establish `hlj : l ≤ j` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)`. Rewrite using `[show o - l + (n - l) + r + z - 1 = o + n + r + z - 2 * l - 1 by omega]`.

Rewrite using `[hc2, zero_smul]`. Rewrite using `[Finset.sum_congr rfl hterm, Finset.sum_congr rfl hre, hcomm, Finset.sum_congr rfl hid]`. Simplify using the standard rewrite rules.
-/
theorem decomp [CharZero k] (hr : 1 ≤ r) (hz : ∀ c, w c ≠ zv ∧ e c ≠ zv) (o n z : ℕ) (x : MvPolynomial σ k)
    (hv : ∀ m, min o n < m → (tieF w e ^ m) x = 0) :
    X zv ^ z * x = ∑ l ∈ range (min o n + 1), ehP w e zv sv ^ l *
      M.tieP w e zv sv (o - l) (n - l) z
        (((((l.factorial : k)) ^ 2 * ((o + n + r + z - l).choose l : k)))⁻¹ • (tieF w e ^ l) x) := by
  classical
  have hT : ∀ l m : ℕ, (tieF w e ^ m) ((tieF w e ^ l) x) = (tieF w e ^ (l + m)) x := by
    intro l m
    rw [add_comm, pow_add]
    rfl
  have hterm : ∀ l ∈ range (min o n + 1), ehP w e zv sv ^ l *
      M.tieP w e zv sv (o - l) (n - l) z
        (((((l.factorial : k)) ^ 2 * ((o + n + r + z - l).choose l : k)))⁻¹ • (tieF w e ^ l) x) =
      ∑ m ∈ range (min o n - l + 1), ((-1 : k) ^ m / (((m).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (m) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (l + m) * (X zv ^ z * (tieF w e ^ (l + m)) x)) := by
    intro l hl
    have hlL : l ≤ min o n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hsub : range (min o n - l + 1) ⊆ range (o - l + 1) := by
      intro m hm
      simp only [Finset.mem_range] at hm ⊢
      omega
    rw [harmonicProjection_expand w e zv sv hz, Finset.mul_sum, ← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [LinearMap.map_smul, hT]
      simp only [MvPolynomial.smul_eq_C_mul, map_mul]
      ring
    · intro m _ hm
      simp only [Finset.mem_range, not_lt] at hm
      have h0 : (tieF w e ^ (l + m)) x = 0 := hv (l + m) (by omega)
      simp [LinearMap.map_smul, hT, h0]
  have hre : ∀ l ∈ range (min o n + 1),
      ∑ m ∈ range (min o n - l + 1), ((-1 : k) ^ m / (((m).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (m) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (l + m) * (X zv ^ z * (tieF w e ^ (l + m)) x)) =
      ∑ j ∈ Ico l (min o n + 1), ((-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (j - l) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (j) * (X zv ^ z * (tieF w e ^ (j)) x)) := by
    intro l hl
    have hlL : l ≤ min o n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    rw [Finset.sum_Ico_eq_sum_range, show min o n + 1 - l = min o n - l + 1 by omega]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Nat.add_sub_cancel_left]
  have hcomm : ∑ l ∈ range (min o n + 1), ∑ j ∈ Ico l (min o n + 1), ((-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (j - l) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (j) * (X zv ^ z * (tieF w e ^ (j)) x)) =
      ∑ j ∈ range (min o n + 1), ∑ l ∈ range (j + 1), ((-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (j - l) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (j) * (X zv ^ z * (tieF w e ^ (j)) x)) :=
    Finset.sum_comm' (fun l j => by simp only [Finset.mem_range, Finset.mem_Ico]; omega)
  have hid : ∀ j ∈ range (min o n + 1),
      ∑ l ∈ range (j + 1), ((-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (j - l) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (j) * (X zv ^ z * (tieF w e ^ (j)) x)) = if j = 0 then X zv ^ z * x else 0 := by
    intro j hj
    have hjL : j ≤ min o n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [← Finset.sum_smul]
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      simp
    · rw [if_neg (by omega)]
      have hc2 : ∑ l ∈ range (j + 1), ((-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (j - l) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) = 0 := by
        refine Eq.trans ?_ (factorial_choose_signed_sum_eq_zero (o + n + r + z) j hpos (by omega))
        refine Finset.sum_congr rfl fun l hl => ?_
        have hlj : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
        rw [show o - l + (n - l) + r + z - 1 = o + n + r + z - 2 * l - 1 by omega]
      rw [hc2, zero_smul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_congr rfl hre, hcomm, Finset.sum_congr rfl hid]
  simp

end

end Formalism.InvariantFactorPaths.KP.LL

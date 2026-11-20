import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DecompBlock0
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ProdZpowEqZpowSum

namespace ReciprocityTheory.ChartRestriction.G.T0

open MvPolynomial

section Comp

variable {K : Type} [Field K] {D N : ℕ}

def degB (b : Fin (D + 1)) (s : TVar D N →₀ ℕ) : ℕ := ∑ j, s (b, j)

noncomputable def compB (b : Fin (D + 1)) (k : ℕ) (p : MvPolynomial (TVar D N) K) :
    MvPolynomial (TVar D N) K :=
  ∑ s ∈ p.support.filter (fun s => degB b s = k), monomial s (coeff s p)

/- English proof (translation)
Unfold `compB`. Rewrite using `[coeff_sum]`. Simplify using `only [coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq']`. Distinguish the cases in `h : degB b t = k`.

Rewrite using `[if_pos h]`. Distinguish the cases in `ht : t ∈ p.support`. Establish `hm : t ∈ p.support.filter (fun s => degB b s = k)` using `Finset.mem_filter.mpr ⟨ht, h⟩`. Rewrite using `[if_pos hm]`. Establish `hn : t ∉ p.support.filter (fun s => degB b s = k)` using `fun h' => ht (Finset.mem_filter.mp h').1`.

Rewrite using `[if_neg hn]`. Conclude with `(by simpa using ht : coeff t p = 0).symm`. Establish `hn : t ∉ p.support.filter (fun s => degB b s = k)` using `fun h' => h (Finset.mem_filter.mp h').2`. Rewrite using `[if_neg h, if_neg hn]`.
-/
theorem coeff_compB (b : Fin (D + 1)) (k : ℕ) (p : MvPolynomial (TVar D N) K) (t : TVar D N →₀ ℕ) :
    coeff t (compB b k p) = if degB b t = k then coeff t p else 0 := by
  unfold compB
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases h : degB b t = k
  · rw [if_pos h]
    by_cases ht : t ∈ p.support
    · have hm : t ∈ p.support.filter (fun s => degB b s = k) := Finset.mem_filter.mpr ⟨ht, h⟩
      rw [if_pos hm]
    · have hn : t ∉ p.support.filter (fun s => degB b s = k) := fun h' => ht (Finset.mem_filter.mp h').1
      rw [if_neg hn]
      exact (by simpa using ht : coeff t p = 0).symm
  · have hn : t ∉ p.support.filter (fun s => degB b s = k) := fun h' => h (Finset.mem_filter.mp h').2
    rw [if_neg h, if_neg hn]

/- English proof (translation)
Rewrite `ht` using `[mem_support_iff, coeff_compB]`. Distinguish the cases in `h : degB b t = k`. Rewrite `ht` using `[if_pos h]`. Conclude with `⟨mem_support_iff.mpr ht, h⟩`. Rewrite `ht` using `[if_neg h]`.

Conclude with `absurd rfl ht`.
-/
theorem mem_support_compB {b : Fin (D + 1)} {k : ℕ} {p : MvPolynomial (TVar D N) K}
    {t : TVar D N →₀ ℕ} (ht : t ∈ (compB b k p).support) : t ∈ p.support ∧ degB b t = k := by
  rw [mem_support_iff, coeff_compB] at ht
  by_cases h : degB b t = k
  · rw [if_pos h] at ht
    exact ⟨mem_support_iff.mpr ht, h⟩
  · rw [if_neg h] at ht
    exact absurd rfl ht

/- English proof (translation)
Rewrite using `[Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single b]`. Simplify using `[degB]`. Introduce `i _ hi`. Simplify using `[hi]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ b) h`.
-/
private lemma sum_filter_block_eq_degB {D N : ℕ} (b : Fin (D + 1)) (s : TVar D N →₀ ℕ) :
    ∑ v ∈ Finset.univ.filter (fun v : TVar D N => v.1 = b), s v = degB b s := by
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single b]
  · simp [degB]
  · intro i _ hi
    simp [hi]
  · intro h
    exact absurd (Finset.mem_univ b) h

/- English proof (translation)
Use `conv_lhs => rw [p.as_sum]`. Rewrite using `[map_sum]`. Simplify using `only [sigP, scaleEquiv_monomial, sum_filter_block_eq_degB]`. Simplify using `only [compB, Finset.mul_sum]`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (fun s hs => Finset.mem_range.mpr (hM s hs))]`.

Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations. Rewrite using `[(Finset.mem_filter.mp hs).2]`.
-/
theorem scaleBlock_eq_sum (b : Fin (D + 1)) (u : Kˣ) (p : MvPolynomial (TVar D N) K) (M : ℕ)
    (hM : ∀ s ∈ p.support, degB b s < M) :
    sigP b u p = ∑ k ∈ Finset.range M, C ((u : K) ^ k) * compB b k p := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  simp only [sigP, scaleEquiv_monomial, sum_filter_block_eq_degB]
  simp only [compB, Finset.mul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (fun s hs => Finset.mem_range.mpr (hM s hs))]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun s hs => ?_
  rw [(Finset.mem_filter.mp hs).2]

end Comp

section Pres

variable {K : Type} [Field K] [CharZero K] {D N : ℕ}

/- English proof (translation)
Use `first`. Consider the case `exact IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _`. Consider the case `simp [sigF, IsFractionRing.ringEquivOfRingEquiv_algebraMap]`.
-/
theorem sigF_alg (b : Fin (D + 1)) (u : Kˣ) (g : KTp K D N) :
    sigF (K := K) (D := D) (N := N) b u (algebraMap (KTp K D N) (KTf K D N) g) =
      algebraMap (KTp K D N) (KTf K D N) (sigP b u g) := by
  first
  | exact IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _
  | simp [sigF, IsFractionRing.ringEquivOfRingEquiv_algebraMap]

/- English proof (translation)
Take `⟨M, hMp, hMq⟩ : ∃ M, (∀ s ∈ p.support, degB b s < M) ∧ (∀ s ∈ q.support, degB b s < M)` from `⟨(p.support ∪ q.support).sup (degB b) + 1, fun s hs => Nat.lt_succ_of_le (Finset.le_sup (f := degB b) (Finset.mem_union_left _ hs)), fun s hs => Nat.lt_succ_of_le (Finset.le_sup (f := degB b) (Finset.mem_union_right _ hs))⟩`. Establish `hroot : ∀ u : Kˣ, ∑ k ∈ Finset.range M, (algebraMap (KTp K D N) (KTf K D N) (compB b k p) - z * algebraMap (KTp K D N) (KTf K D N) (compB b k q)) * (algebraMap (KTp K D N) (KTf K D N) (C (u : K))) ^ k = 0`. Introduce `u`. Establish `h1` using `congrArg (sigF (K := K) (D := D) (N := N) b u) hpq`. Rewrite `h1` using `[map_mul, sigF_alg, sigF_alg, hz u, scaleBlock_eq_sum b u p M hMp, scaleBlock_eq_sum b u q M hMq, map_sum, map_sum, Finset.mul_sum]`.

Establish `h2` using `sub_eq_zero.mpr h1`. Rewrite `h2` using `[← Finset.sum_sub_distrib]`. Use `Eq.trans (Finset.sum_congr rfl fun k _ => ?_) h2` and prove the remaining obligations. Simplify using `only [map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hQ : (∑ k ∈ Finset.range M, Polynomial.monomial k (algebraMap (KTp K D N) (KTf K D N) (compB b k p) - z * algebraMap (KTp K D N) (KTf K D N) (compB b k q))) = 0`. Apply `Polynomial.eq_zero_of_infinite_isRoot` to reduce the goal to its premises. Use `Set.infinite_of_injective_forall_mem (f := fun n : ℕ => algebraMap (KTp K D N) (KTf K D N) (C ((n : K) + 1))) ?_ ?_` and prove the remaining obligations. Introduce `n m hnm`. Establish `h2` using `IsFractionRing.injective (KTp K D N) (KTf K D N) hnm`.

Establish `h3` using `MvPolynomial.C_injective (TVar D N) K h2`. Conclude with `add_right_cancel h3` after adjusting the coercions. Introduce `n`. Establish `hu` using `hroot (Units.mk0 ((n : K) + 1) (Nat.cast_add_one_ne_zero n))`. Rewrite `hu` using `[Units.val_mk0]`.

Use `show Polynomial.eval _ _ = 0`. Rewrite using `[Polynomial.eval_finset_sum]`. Simplify using `only [Polynomial.eval_monomial]`. Conclude with `hu`. Establish `hcoef : ∀ k < M, algebraMap (KTp K D N) (KTf K D N) (compB b k p) - z * algebraMap (KTp K D N) (KTf K D N) (compB b k q) = 0`.

Introduce `k hk`. Establish `h4` using `congrArg (fun P => Polynomial.coeff P k) hQ`. Simplify using `only [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at h4`. Use `first`. Consider the case `rwa [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hk)] at h4`.

Consider the case `rwa [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hk)] at h4`. Establish `hqs : q = ∑ k ∈ Finset.range M, compB b k q`. Use extensionality with `t`. Rewrite using `[MvPolynomial.coeff_sum]`. Simplify using `only [coeff_compB]`.

Rewrite using `[Finset.sum_ite_eq]`. Use `split_ifs with h`. Both sides reduce to the same expression. Assume the negation of the conclusion as `hne`. Conclude with `h (Finset.mem_range.mpr (hMq t (MvPolynomial.mem_support_iff.mpr hne)))`.

Choose the witnesses or unpack the hypotheses as in `⟨k, hk, hqk⟩ : ∃ k ∈ Finset.range M, compB b k q ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `hq` to reduce the goal to its premises. Rewrite using `[hqs]`.

Conclude with `Finset.sum_eq_zero hc`. Conclude with `⟨k, hqk, sub_eq_zero.mp (hcoef k (Finset.mem_range.mp hk))⟩`.
-/
theorem one_block (b : Fin (D + 1)) (z : KTf K D N)
    (hz : ∀ u : Kˣ, sigF (K := K) (D := D) (N := N) b u z = z)
    (p q : KTp K D N) (hq : q ≠ 0)
    (hpq : algebraMap (KTp K D N) (KTf K D N) p = z * algebraMap (KTp K D N) (KTf K D N) q) :
    ∃ k, compB b k q ≠ 0 ∧ algebraMap (KTp K D N) (KTf K D N) (compB b k p) =
      z * algebraMap (KTp K D N) (KTf K D N) (compB b k q) := by
  obtain ⟨M, hMp, hMq⟩ : ∃ M, (∀ s ∈ p.support, degB b s < M) ∧ (∀ s ∈ q.support, degB b s < M) :=
    ⟨(p.support ∪ q.support).sup (degB b) + 1,
      fun s hs => Nat.lt_succ_of_le (Finset.le_sup (f := degB b) (Finset.mem_union_left _ hs)),
      fun s hs => Nat.lt_succ_of_le (Finset.le_sup (f := degB b) (Finset.mem_union_right _ hs))⟩
  have hroot : ∀ u : Kˣ, ∑ k ∈ Finset.range M,
      (algebraMap (KTp K D N) (KTf K D N) (compB b k p) - z * algebraMap (KTp K D N) (KTf K D N) (compB b k q)) * (algebraMap (KTp K D N) (KTf K D N) (C (u : K))) ^ k = 0 := by
    intro u
    have h1 := congrArg (sigF (K := K) (D := D) (N := N) b u) hpq
    rw [map_mul, sigF_alg, sigF_alg, hz u, scaleBlock_eq_sum b u p M hMp, scaleBlock_eq_sum b u q M hMq,
      map_sum, map_sum, Finset.mul_sum] at h1
    have h2 := sub_eq_zero.mpr h1
    rw [← Finset.sum_sub_distrib] at h2
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) h2
    simp only [map_mul, map_pow]
    ring
  have hQ : (∑ k ∈ Finset.range M, Polynomial.monomial k
      (algebraMap (KTp K D N) (KTf K D N) (compB b k p) - z * algebraMap (KTp K D N) (KTf K D N) (compB b k q))) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => algebraMap (KTp K D N) (KTf K D N) (C ((n : K) + 1))) ?_ ?_
    · intro n m hnm
      have h2 := IsFractionRing.injective (KTp K D N) (KTf K D N) hnm
      have h3 := MvPolynomial.C_injective (TVar D N) K h2
      exact_mod_cast add_right_cancel h3
    · intro n
      have hu := hroot (Units.mk0 ((n : K) + 1) (Nat.cast_add_one_ne_zero n))
      rw [Units.val_mk0] at hu
      show Polynomial.eval _ _ = 0
      rw [Polynomial.eval_finset_sum]
      simp only [Polynomial.eval_monomial]
      exact hu
  have hcoef : ∀ k < M, algebraMap (KTp K D N) (KTf K D N) (compB b k p) - z * algebraMap (KTp K D N) (KTf K D N) (compB b k q) = 0 := by
    intro k hk
    have h4 := congrArg (fun P => Polynomial.coeff P k) hQ
    simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at h4
    first
    | rwa [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hk)] at h4
    | rwa [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hk)] at h4
  have hqs : q = ∑ k ∈ Finset.range M, compB b k q := by
    ext t
    rw [MvPolynomial.coeff_sum]
    simp only [coeff_compB]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · by_contra hne
      exact h (Finset.mem_range.mpr (hMq t (MvPolynomial.mem_support_iff.mpr hne)))
  obtain ⟨k, hk, hqk⟩ : ∃ k ∈ Finset.range M, compB b k q ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hq
    rw [hqs]
    exact Finset.sum_eq_zero hc
  exact ⟨k, hqk, sub_eq_zero.mp (hcoef k (Finset.mem_range.mp hk))⟩

/- English proof (translation)
Rewrite using `[aeval_monomial]`. Use `split_ifs with h`. Establish `h' : ∑ j, s (0, j) = 0` using `h`. Establish `hz : ∀ v ∈ s.support, v.1 ≠ 0`. Introduce `v hv h0`.

Establish `hsum : s (0, v.2) = 0` using `Finset.sum_eq_zero_iff.mp h' v.2 (Finset.mem_univ _)`. Establish `hv' : v = (0, v.2)` using `Prod.ext h0 rfl`. Rewrite `hv` using `[Finsupp.mem_support_iff, hv']`. Conclude with `hv hsum`. Rewrite using `[Finsupp.prod_congr (g2 := fun i k => (X i : KTp K D N) ^ k) (fun i hi => by simp [hz i hi]), MvPolynomial.algebraMap_eq, ← monomial_eq]`.

Establish `h' : ∃ j, s (0, j) ≠ 0`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `h (Finset.sum_eq_zero fun j _ => hc j)`. Take `⟨j, hj⟩` from `h'`.

Rewrite using `[Finsupp.prod, Finset.prod_eq_zero (i := ((0 : Fin (D + 1)), j)) (Finsupp.mem_support_iff.mpr hj) (by simp [hj]), mul_zero]`.
-/
private lemma aeval_block_zero_monomial (s : TVar D N →₀ ℕ) (a : K) :
    (aeval (fun v : TVar D N => if v.1 = 0 then C ((0 : Fin (N + 1) → K) v.2) else X v) :
      KTp K D N →ₐ[K] KTp K D N) (monomial s a) =
      if degB 0 s = 0 then monomial s a else 0 := by
  rw [aeval_monomial]
  split_ifs with h
  · have h' : ∑ j, s (0, j) = 0 := h
    have hz : ∀ v ∈ s.support, v.1 ≠ 0 := by
      intro v hv h0
      have hsum : s (0, v.2) = 0 := Finset.sum_eq_zero_iff.mp h' v.2 (Finset.mem_univ _)
      have hv' : v = (0, v.2) := Prod.ext h0 rfl
      rw [Finsupp.mem_support_iff, hv'] at hv
      exact hv hsum
    rw [Finsupp.prod_congr (g2 := fun i k => (X i : KTp K D N) ^ k) (fun i hi => by simp [hz i hi]),
      MvPolynomial.algebraMap_eq, ← monomial_eq]
  · have h' : ∃ j, s (0, j) ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact h (Finset.sum_eq_zero fun j _ => hc j)
    obtain ⟨j, hj⟩ := h'
    rw [Finsupp.prod, Finset.prod_eq_zero (i := ((0 : Fin (D + 1)), j))
      (Finsupp.mem_support_iff.mpr hj) (by simp [hj]), mul_zero]

/- English proof (translation)
Establish `h0` using `hP 0`. Establish `hc : (aeval (fun v : TVar D N => if v.1 = 0 then C ((0 : Fin (N + 1) → K) v.2) else X v) : KTp K D N →ₐ[K] KTp K D N) P = compB 0 0 P` using `by conv_lhs => rw [P.as_sum]`. Rewrite using `[map_sum]`. Simplify using `only [aeval_block_zero_monomial]`. Unfold `compB`.

Rewrite using `[Finset.sum_filter]`. Establish `hPc : P = compB 0 0 P` using `h0.symm.trans hc`. Introduce `s hs`. Rewrite `hs` using `[hPc]`. Conclude with `(mem_support_compB hs).2`.
-/
theorem support_free_of_block_subst_invariant (P : KTp K D N)
    (hP : ∀ x : Fin (N + 1) → K, (aeval (fun v : TVar D N =>
      if v.1 = 0 then C (x v.2) else X v) : KTp K D N →ₐ[K] KTp K D N) P = P) :
    ∀ s ∈ P.support, degB 0 s = 0 := by
  have h0 := hP 0
  have hc : (aeval (fun v : TVar D N => if v.1 = 0 then C ((0 : Fin (N + 1) → K) v.2) else X v) :
      KTp K D N →ₐ[K] KTp K D N) P = compB 0 0 P := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    simp only [aeval_block_zero_monomial]
    unfold compB
    rw [Finset.sum_filter]
  have hPc : P = compB 0 0 P := h0.symm.trans hc
  intro s hs
  rw [hPc] at hs
  exact (mem_support_compB hs).2

/- English proof (translation)
Establish `key : ∀ S : Finset (Fin (D + 1)), ∃ a b : KTp K D N, b ≠ 0 ∧ algebraMap (KTp K D N) (KTf K D N) a = z * algebraMap (KTp K D N) (KTf K D N) b ∧ (∀ s ∈ a.support, degB 0 s = 0) ∧ (∀ s ∈ b.support, degB 0 s = 0) ∧ ∃ m : Fin (D + 1) → ℕ, ∀ i ∈ S, (∀ s ∈ a.support, degB i s = m i) ∧ ( …`. Introduce `S`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨p, q, hq, hpq, hp0, hq0, 0, by simp⟩`. Consider the case `insert i S hi ih`.

Take `⟨a, b, hb, hab, ha0, hb0, m, hm⟩` from `ih`. Take `⟨k, hk0, hk⟩` from `one_block i z (hz i) a b hb hab`. Use `⟨compB i k a, compB i k b, hk0, hk, fun s hs => ha0 s (mem_support_compB hs).1, fun s hs => hb0 s (mem_support_compB hs).1, Function.update m i k, ?_⟩` and prove the remaining obligations. Introduce `i' hi'`. Break down `Finset.mem_insert.mp hi' with rfl | hi'` into its components or cases.

Simplify using `only [Function.update_self]`. Conclude with `⟨fun s hs => (mem_support_compB hs).2, fun s hs => (mem_support_compB hs).2⟩`. Establish `hne : i' ≠ i` using `fun h => hi (h ▸ hi')`. Rewrite using `[Function.update_of_ne hne]`. Conclude with `⟨fun s hs => (hm i' hi').1 s (mem_support_compB hs).1, fun s hs => (hm i' hi').2 s (mem_support_compB hs).1⟩`.

Take `⟨a, b, hb, hab, ha0, hb0, m, hm⟩` from `key Finset.univ`. Use `⟨a, b, hb, hab, fun i => if i = 0 then 0 else m i, by simp, ?_, ?_⟩` and prove the remaining obligations. Introduce `s hs i`. Distinguish the cases in `hi : i = 0`. Substitute `hi` using the available equality.

Simplify `ha0 s hs` using `[degB]`. Simplify `(hm i (Finset.mem_univ i)).1 s hs` using `[hi, degB]`. Introduce `s hs i`. Distinguish the cases in `hi : i = 0`. Substitute `hi` using the available equality.

Simplify `hb0 s hs` using `[degB]`. Simplify `(hm i (Finset.mem_univ i)).2 s hs` using `[hi, degB]`.
-/
theorem multi_pres (z : KTf K D N)
    (hz : ∀ (b : Fin (D + 1)) (u : Kˣ), sigF (K := K) (D := D) (N := N) b u z = z)
    (p q : KTp K D N) (hq : q ≠ 0)
    (hpq : algebraMap (KTp K D N) (KTf K D N) p = z * algebraMap (KTp K D N) (KTf K D N) q)
    (hp0 : ∀ s ∈ p.support, degB 0 s = 0) (hq0 : ∀ s ∈ q.support, degB 0 s = 0) :
    ∃ a b : KTp K D N, b ≠ 0 ∧
      algebraMap (KTp K D N) (KTf K D N) a = z * algebraMap (KTp K D N) (KTf K D N) b ∧
      ∃ m : Fin (D + 1) → ℕ, m 0 = 0 ∧ ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m a ∧
        ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m b := by
  classical
  have key : ∀ S : Finset (Fin (D + 1)), ∃ a b : KTp K D N, b ≠ 0 ∧
      algebraMap (KTp K D N) (KTf K D N) a = z * algebraMap (KTp K D N) (KTf K D N) b ∧
      (∀ s ∈ a.support, degB 0 s = 0) ∧ (∀ s ∈ b.support, degB 0 s = 0) ∧
      ∃ m : Fin (D + 1) → ℕ, ∀ i ∈ S,
        (∀ s ∈ a.support, degB i s = m i) ∧ (∀ s ∈ b.support, degB i s = m i) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨p, q, hq, hpq, hp0, hq0, 0, by simp⟩
    | insert i S hi ih =>
      obtain ⟨a, b, hb, hab, ha0, hb0, m, hm⟩ := ih
      obtain ⟨k, hk0, hk⟩ := one_block i z (hz i) a b hb hab
      refine ⟨compB i k a, compB i k b, hk0, hk, fun s hs => ha0 s (mem_support_compB hs).1,
        fun s hs => hb0 s (mem_support_compB hs).1, Function.update m i k, ?_⟩
      intro i' hi'
      rcases Finset.mem_insert.mp hi' with rfl | hi'
      · simp only [Function.update_self]
        exact ⟨fun s hs => (mem_support_compB hs).2, fun s hs => (mem_support_compB hs).2⟩
      · have hne : i' ≠ i := fun h => hi (h ▸ hi')
        rw [Function.update_of_ne hne]
        exact ⟨fun s hs => (hm i' hi').1 s (mem_support_compB hs).1,
          fun s hs => (hm i' hi').2 s (mem_support_compB hs).1⟩
  obtain ⟨a, b, hb, hab, ha0, hb0, m, hm⟩ := key Finset.univ
  refine ⟨a, b, hb, hab, fun i => if i = 0 then 0 else m i, by simp, ?_, ?_⟩
  · intro s hs i
    by_cases hi : i = 0
    · subst hi
      simpa [degB] using ha0 s hs
    · simpa [hi, degB] using (hm i (Finset.mem_univ i)).1 s hs
  · intro s hs i
    by_cases hi : i = 0
    · subst hi
      simpa [degB] using hb0 s hs
    · simpa [hi, degB] using (hm i (Finset.mem_univ i)).2 s hs

end Pres

end ReciprocityTheory.ChartRestriction.G.T0

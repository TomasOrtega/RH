import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeO
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeP
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPC

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

/- English proof (translation)
Establish `hPp : P.IsPrime` using `hP.2.1.1`. Use `choose i hi using hP.2.1.2.2`. Use `set m : MRing ι := ∏ k, X ⟨k, i k⟩ with hmdef`. Establish `hm : m ∉ P` using `fun h' => by`. Take `⟨k, -, hk⟩` from `(Ideal.IsPrime.prod_mem_iff (hp := hPp)).mp h'`.

Conclude with `hi k hk`. Establish `hv : u * m ∉ P` using `fun h' => (hPp.mem_or_mem h').elim hu hm`. Establish `hvan : map (Int.castRingHom ℂ) (u * m) * H ∈ (pC P).radical`. Rewrite using `[← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ), MvPolynomial.mem_vanishingIdeal_iff]`. Introduce `x hx`.

Express the relevant statement in the definitionally equal form `eval x _ = 0`. Rewrite `hx` using `[MvPolynomial.mem_zeroLocus_iff]`. Distinguish the cases in `hb : ∀ k, x ⟨k, i k⟩ ≠ 0`. Establish `hxm : x ∈ mcPts P`. Rewrite using `[mcPts_eq_pC]`.

Conclude with `⟨fun k => ⟨i k, hb k⟩, fun f hf => hx f hf⟩`. Rewrite using `[map_mul, map_mul, map_mul, mul_right_comm, h x hxm, zero_mul]`. Use `push Not at hb`. Take `⟨k, hk⟩` from `hb`. Establish `: eval x (map (Int.castRingHom ℂ) m) = 0`.

Rewrite using `[hmdef, map_prod, map_prod]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])`. Rewrite using `[map_mul, map_mul, map_mul, this, mul_zero, zero_mul]`. Establish `hHrad : H ∈ (pC P).radical`. Rewrite using `[← Ideal.sInf_minimalPrimes]`.

Use `Submodule.mem_sInf.mpr fun Q hQ => ?_` and prove the remaining obligations. Establish `hQp : Ideal.IsPrime Q` using `hQ.1.1`. Establish `hle : (pC P).radical ≤ Q` using `(Ideal.IsPrime.radical_le_iff hQp).mpr hQ.1.2`. Establish `hvQ : map (Int.castRingHom ℂ) (u * m) ∉ Q` using `fun h' => by`. Apply `hv` to reduce the goal to its premises.

Rewrite using `[← hM K ι P e hP Q hQ]`. Conclude with `h'`. Conclude with `(hQp.mem_or_mem (hle hvan)).resolve_left hvQ`. Introduce `z hz`. Rewrite `hHrad` using `[← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ), MvPolynomial.mem_vanishingIdeal_iff]`.

Use `hHrad z (by` as an intermediate fact. Rewrite using `[MvPolynomial.mem_zeroLocus_iff]`. Introduce `p hp`. Conclude with `(by rw [mcPts_eq_pC] at hz; exact hz.2 p hp))`. Conclude with `this`.
-/
theorem eval_eq_zero_of_mul (hM : PCMinContractStatement) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ} (hP : IsArithVar P (e + 1)) {u : MRing ι}
    (hu : u ∉ P) {H : MRingOver ℂ ι}
    (h : ∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) u) * eval z H = 0) :
    ∀ z ∈ mcPts P, eval z H = 0 := by
  classical
  have hPp : P.IsPrime := hP.2.1.1
  choose i hi using hP.2.1.2.2
  set m : MRing ι := ∏ k, X ⟨k, i k⟩ with hmdef
  have hm : m ∉ P := fun h' => by
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hPp)).mp h'
    exact hi k hk
  have hv : u * m ∉ P := fun h' => (hPp.mem_or_mem h').elim hu hm
  have hvan : map (Int.castRingHom ℂ) (u * m) * H ∈ (pC P).radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ),
      MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    change eval x _ = 0
    rw [MvPolynomial.mem_zeroLocus_iff] at hx
    by_cases hb : ∀ k, x ⟨k, i k⟩ ≠ 0
    · have hxm : x ∈ mcPts P := by
        rw [mcPts_eq_pC]
        exact ⟨fun k => ⟨i k, hb k⟩, fun f hf => hx f hf⟩
      rw [map_mul, map_mul, map_mul, mul_right_comm, h x hxm, zero_mul]
    · push Not at hb
      obtain ⟨k, hk⟩ := hb
      have : eval x (map (Int.castRingHom ℂ) m) = 0 := by
        rw [hmdef, map_prod, map_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])
      rw [map_mul, map_mul, map_mul, this, mul_zero, zero_mul]
  have hHrad : H ∈ (pC P).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    refine Submodule.mem_sInf.mpr fun Q hQ => ?_
    have hQp : Ideal.IsPrime Q := hQ.1.1
    have hle : (pC P).radical ≤ Q := (Ideal.IsPrime.radical_le_iff hQp).mpr hQ.1.2
    have hvQ : map (Int.castRingHom ℂ) (u * m) ∉ Q := fun h' => by
      apply hv
      rw [← hM K ι P e hP Q hQ]
      exact h'
    exact (hQp.mem_or_mem (hle hvan)).resolve_left hvQ
  intro z hz
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ),
    MvPolynomial.mem_vanishingIdeal_iff] at hHrad
  have := hHrad z (by
    rw [MvPolynomial.mem_zeroLocus_iff]
    intro p hp
    exact (by rw [mcPts_eq_pC] at hz; exact hz.2 p hp))
  exact this

/- English proof (translation)
Establish `hscale : ∀ (m : ℕ) (t : ℂ) (v : Fin n → ℂ), eval (fun i => t * v i) (homogeneousComponent m c) = t ^ m * eval v (homogeneousComponent m c)`. Introduce `m t v`. Rewrite using `[homogeneousComponent_apply, map_sum, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Rewrite `hd` using `[Finset.mem_filter]`.

Establish `hdeg : ∑ i ∈ d.support, d i = m` using `by first`. Consider the case `exact hd.2`. Consider the case `(rw [← hd.2]; rfl)`. Consider the case `simpa [Finsupp.degree] using hd.2`. Simplify using `only [eval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hcomp : ∀ m, ∀ v ∈ T, eval v (homogeneousComponent m c) = 0`. Introduce `m v hv`. Set `Q : Polynomial ℂ` to `∑ k ∈ Finset.range (c.totalDegree + 1), Polynomial.C (eval v (homogeneousComponent k c)) * Polynomial.X ^ k`. Establish `hQ : ∀ t : ℂ, t ≠ 0 → Q.eval t = 0`.

Introduce `t ht`. Establish `h0` using `hcT _ (hT v hv t ht)`. Rewrite `h0` using `[← sum_homogeneousComponent c, map_sum]`. Simplify using `only [Q, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]`. Rewrite using `[← h0]`.

Conclude with `Finset.sum_congr rfl fun k _ => by rw [hscale]; ring`. Establish `hQ0 : Q = 0`. Apply `Polynomial.eq_zero_of_infinite_isRoot` to reduce the goal to its premises. Apply `Set.Infinite.mono (s := {t : ℂ | t ≠ 0})` to reduce the goal to its premises. Introduce `t ht`.

Conclude with `hQ t ht`. Conclude with `(Set.finite_singleton (0 : ℂ)).infinite_compl`. Distinguish the cases in `hm : m ≤ c.totalDegree`. Establish `h1` using `congrArg (fun p => Polynomial.coeff p m) hQ0`. Simplify `h1` using `[Q, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, (by omega : m < c.totalDegree + 1)]`.

Rewrite using `[homogeneousComponent_eq_zero m c (by omega), map_zero]`. Choose the witnesses or unpack the hypotheses as in `⟨m, -, hm⟩ : ∃ m ∈ Finset.range (c.totalDegree + 1), homogeneousComponent m c ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hc` to reduce the goal to its premises.

Rewrite using `[← sum_homogeneousComponent c]`. Conclude with `Finset.sum_eq_zero hcon`. Conclude with `⟨m, hm, homogeneousComponent_isHomogeneous m c, fun v hv => hcomp m v hv⟩`.
-/
theorem exists_homog_of_cone {n : ℕ} {c : MvPolynomial (Fin n) ℂ} (hc : c ≠ 0)
    {T : Set (Fin n → ℂ)} (hT : ∀ v ∈ T, ∀ t : ℂ, t ≠ 0 → (fun i => t * v i) ∈ T)
    (hcT : ∀ v ∈ T, eval v c = 0) :
    ∃ m, homogeneousComponent m c ≠ 0 ∧ (homogeneousComponent m c).IsHomogeneous m ∧
      ∀ v ∈ T, eval v (homogeneousComponent m c) = 0 := by
  have hscale : ∀ (m : ℕ) (t : ℂ) (v : Fin n → ℂ),
      eval (fun i => t * v i) (homogeneousComponent m c) = t ^ m * eval v (homogeneousComponent m c) := by
    intro m t v
    rw [homogeneousComponent_apply, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_filter] at hd
    have hdeg : ∑ i ∈ d.support, d i = m := by
      first
      | exact hd.2
      | (rw [← hd.2]; rfl)
      | simpa [Finsupp.degree] using hd.2
    simp only [eval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, hdeg]
    ring
  have hcomp : ∀ m, ∀ v ∈ T, eval v (homogeneousComponent m c) = 0 := by
    intro m v hv
    let Q : Polynomial ℂ := ∑ k ∈ Finset.range (c.totalDegree + 1),
      Polynomial.C (eval v (homogeneousComponent k c)) * Polynomial.X ^ k
    have hQ : ∀ t : ℂ, t ≠ 0 → Q.eval t = 0 := by
      intro t ht
      have h0 := hcT _ (hT v hv t ht)
      rw [← sum_homogeneousComponent c, map_sum] at h0
      simp only [Q, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      rw [← h0]
      exact Finset.sum_congr rfl fun k _ => by rw [hscale]; ring
    have hQ0 : Q = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply Set.Infinite.mono (s := {t : ℂ | t ≠ 0})
      · intro t ht
        exact hQ t ht
      · exact (Set.finite_singleton (0 : ℂ)).infinite_compl
    by_cases hm : m ≤ c.totalDegree
    · have h1 := congrArg (fun p => Polynomial.coeff p m) hQ0
      simpa [Q, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow,
        (by omega : m < c.totalDegree + 1)] using h1
    · rw [homogeneousComponent_eq_zero m c (by omega), map_zero]
  obtain ⟨m, -, hm⟩ : ∃ m ∈ Finset.range (c.totalDegree + 1), homogeneousComponent m c ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hc
    rw [← sum_homogeneousComponent c]
    exact Finset.sum_eq_zero hcon
  exact ⟨m, hm, homogeneousComponent_isHomogeneous m c, fun v hv => hcomp m v hv⟩

/- English proof (translation)
Introduce `K _ ι _ P e Ψ f a hP hΨ hf hfP`. Establish `hPp : P.IsPrime` using `hP.2.1.1`. Establish `hPh : IsMultiHomogIdeal P` using `hP.2.1.2.1`. Take `⟨k1⟩` from `hP.1`. Use `choose i hi using hP.2.1.2.2`.

Use `set d := ∑ k, a k with hd`. Use `set g : MRing ι := ∏ k, X ⟨k, i k⟩ ^ (d - a k) with hgdef`. Use `set f' : MRing ι := f * g with hf'def`. Establish `hgP : g ∉ P` using `fun h' => by`. Take `⟨k, -, hk⟩` from `(Ideal.IsPrime.prod_mem_iff (hp := hPp)).mp h'`.

Conclude with `hi k (hPp.mem_of_pow_mem _ hk)`. Establish `hf'P : f' ∉ P` using `fun h' => (hPp.mem_or_mem h').elim hfP hgP`. Establish `hf'h : IsWeightedHomogeneous (blkW ι) (map (Int.castRingHom ℂ) f') (fun _ => d)`. Establish `h1 : IsWeightedHomogeneous (blkW ι) (map (Int.castRingHom ℂ) f) a` using `isWeightedHomogeneous_map_of_isMultiHomog hf`. Establish `h2 : IsWeightedHomogeneous (blkW ι) (map (Int.castRingHom ℂ) g) (∑ k, (d - a k) • blkW ι ⟨k, i k⟩)`.

Rewrite using `[hgdef, map_prod]`. Use `IsWeightedHomogeneous.prod _ _ _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, map_X]`. Conclude with `(isWeightedHomogeneous_X ℂ _ _).pow _`. Establish `hw : a + ∑ k, (d - a k) • blkW ι ⟨k, i k⟩ = fun _ => d`.

Use function extensionality and compare the values at `k'`. Establish `hle : a k' ≤ d` using `Finset.single_le_sum (fun k _ => Nat.zero_le (a k)) (Finset.mem_univ k')`. Simplify using `only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, blkW, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hf'def, map_mul, ← hw]`.

Conclude with `h1.mul h2`. Take `⟨F, -, hF⟩` from `diag_of_homog d hf'h`. Take `⟨n, c, hcn, hrelF⟩` from `exists_monic_rel Ψ P hPh hΨ F`. Establish `hex : ∃ k, c k ≠ 0` using `⟨n, by rw [hcn]; exact one_ne_zero⟩`. Use `set k0 := Nat.find hex with hk0def`.

Establish `hk0 : c k0 ≠ 0` using `Nat.find_spec hex`. Establish `hlt : ∀ j < k0, c j = 0` using `fun j hj => by`. Assume the negation of the conclusion as `h`. Conclude with `Nat.find_min hex hj h`. Establish `hk0n : k0 ≤ n` using `Nat.find_min' hex (by rw [hcn]; exact one_ne_zero)`.

Use `set S := (Finset.range (n + 1)).filter (fun j => k0 ≤ j) with hSdef`. Use `set H : MRingOver ℂ ι := ∑ j ∈ S, bind₁ (psiPoly Ψ) (c j) * (map (Int.castRingHom ℂ) f') ^ (j - k0) with hHdef`. Establish `hbind : ∀ (z : (Σ k, ι k) → ℂ) (q : MvPolynomial (Fin (e + 1)) ℂ), eval z (bind₁ (psiPoly Ψ) q) = eval (Ψ (segre z)) q`. Introduce `z q`. Proceed by induction on `q using MvPolynomial.induction_on with`.

Consider the case `C a => simp`. Consider the case `add p q hp hq => rw [map_add, map_add, hp, hq, map_add]`. Consider the case `mul_X p j hp => rw [map_mul, map_mul, hp, bind₁_X_right, eval_psiPoly, map_mul, eval_X]`. Establish `hevalH : ∀ z, eval z H = ∑ j ∈ S, eval (Ψ (segre z)) (c j) * eval (segre z) F ^ (j - k0)`. Introduce `z`.

Rewrite using `[hHdef, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, hbind, hF]`. Establish `hmul : ∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) (f' ^ k0)) * eval z H = 0`. Introduce `z hz`.

Rewrite using `[hevalH, map_pow, map_pow, hF, Finset.mul_sum, ← hrelF z hz]`. Rewrite using `[hSdef, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : k0 ≤ j`. Rewrite using `[if_pos hj]`.

Rewrite using `[show j = k0 + (j - k0) from (Nat.add_sub_cancel' hj).symm]`. Rewrite using `[Nat.add_sub_cancel_left, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hj, hlt j (not_le.mp hj), map_zero, zero_mul]`. Establish `hH` using `eval_eq_zero_of_mul hM hP (u := f' ^ k0) (fun h' => hf'P (hPp.mem_of_pow_mem _ h')) hmul`.

Use `set T : Set (Fin (e + 1) → ℂ) := {v | ∃ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) f) = 0 ∧ Ψ (segre z) = v} with hTdef`. Establish `hcT : ∀ v ∈ T, eval v (c k0) = 0`. Introduce and unpack `_ ⟨z, hz, hfz, rfl⟩`. Establish `h0` using `hH z hz`. Establish `hF0 : eval (segre z) F = 0`.

Rewrite using `[← hF, hf'def, map_mul, map_mul, hfz, zero_mul]`. Rewrite `h0` using `[hevalH, hF0]`. Rewrite `h0` using `[Finset.sum_eq_single k0]`. Simplify using `using h0`. Introduce `j hj hjk`.

Establish `: 0 < j - k0`. Use `(Finset.mem_filter.mp hj).2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[zero_pow this.ne', mul_zero]`. Introduce `h`.

Conclude with `absurd (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), le_rfl⟩) h`. Establish `hT : ∀ v ∈ T, ∀ t : ℂ, t ≠ 0 → (fun j => t * v j) ∈ T`. Introduce and unpack `_ ⟨z, hz, hfz, rfl⟩ t ht`. Use `set cc : K → ℂ := Function.update (fun _ => (1 : ℂ)) k1 t with hccdef`. Establish `hcc : ∀ k, cc k ≠ 0`.

Introduce `k`. Distinguish the cases in `hk : k = k1`. Substitute `hk` using the available equality. Simplify using `[hccdef, ht]`. Simplify using `[hccdef, Function.update_of_ne hk]`.

Establish `hpc : ∏ k, cc k = t`. Simplify using `[hccdef, Finset.prod_update_of_mem (Finset.mem_univ k1)]`. Use `⟨fun p => cc p.1 * z p, mcPts_smul hPh cc hcc hz, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[eval_smul_homog f a hf cc z, hfz, mul_zero]`. Rewrite using `[segre_smul, map_smul, hpc]`.

Both sides reduce to the same expression. Take `⟨m, hm0, hmh, hmT⟩` from `exists_homog_of_cone hk0 hT hcT`. Conclude with `⟨homogeneousComponent m (c k0), m, hm0, hmh, fun z hz hfz => hmT _ ⟨z, hz, hfz, rfl⟩⟩`.
-/
theorem normPoly_of (hM : PCMinContractStatement) : NormPolyStatement := by
  intro K _ ι _ P e Ψ f a hP hΨ hf hfP
  classical
  have hPp : P.IsPrime := hP.2.1.1
  have hPh : IsMultiHomogIdeal P := hP.2.1.2.1
  obtain ⟨k1⟩ := hP.1
  choose i hi using hP.2.1.2.2
  set d := ∑ k, a k with hd
  set g : MRing ι := ∏ k, X ⟨k, i k⟩ ^ (d - a k) with hgdef
  set f' : MRing ι := f * g with hf'def
  have hgP : g ∉ P := fun h' => by
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hPp)).mp h'
    exact hi k (hPp.mem_of_pow_mem _ hk)
  have hf'P : f' ∉ P := fun h' => (hPp.mem_or_mem h').elim hfP hgP
  have hf'h : IsWeightedHomogeneous (blkW ι) (map (Int.castRingHom ℂ) f') (fun _ => d) := by
    have h1 : IsWeightedHomogeneous (blkW ι) (map (Int.castRingHom ℂ) f) a :=
      isWeightedHomogeneous_map_of_isMultiHomog hf
    have h2 : IsWeightedHomogeneous (blkW ι) (map (Int.castRingHom ℂ) g)
        (∑ k, (d - a k) • blkW ι ⟨k, i k⟩) := by
      rw [hgdef, map_prod]
      refine IsWeightedHomogeneous.prod _ _ _ fun k _ => ?_
      rw [map_pow, map_X]
      exact (isWeightedHomogeneous_X ℂ _ _).pow _
    have hw : a + ∑ k, (d - a k) • blkW ι ⟨k, i k⟩ = fun _ => d := by
      funext k'
      have hle : a k' ≤ d := Finset.single_le_sum (fun k _ => Nat.zero_le (a k))
        (Finset.mem_univ k')
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, blkW, Pi.single_apply,
        smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      omega
    rw [hf'def, map_mul, ← hw]
    exact h1.mul h2
  obtain ⟨F, -, hF⟩ := diag_of_homog d hf'h
  obtain ⟨n, c, hcn, hrelF⟩ := exists_monic_rel Ψ P hPh hΨ F
  have hex : ∃ k, c k ≠ 0 := ⟨n, by rw [hcn]; exact one_ne_zero⟩
  set k0 := Nat.find hex with hk0def
  have hk0 : c k0 ≠ 0 := Nat.find_spec hex
  have hlt : ∀ j < k0, c j = 0 := fun j hj => by
    by_contra h
    exact Nat.find_min hex hj h
  have hk0n : k0 ≤ n := Nat.find_min' hex (by rw [hcn]; exact one_ne_zero)
  set S := (Finset.range (n + 1)).filter (fun j => k0 ≤ j) with hSdef
  set H : MRingOver ℂ ι := ∑ j ∈ S,
    bind₁ (psiPoly Ψ) (c j) * (map (Int.castRingHom ℂ) f') ^ (j - k0) with hHdef
  have hbind : ∀ (z : (Σ k, ι k) → ℂ) (q : MvPolynomial (Fin (e + 1)) ℂ),
      eval z (bind₁ (psiPoly Ψ) q) = eval (Ψ (segre z)) q := by
    intro z q
    induction q using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
    | mul_X p j hp => rw [map_mul, map_mul, hp, bind₁_X_right, eval_psiPoly, map_mul, eval_X]
  have hevalH : ∀ z, eval z H = ∑ j ∈ S, eval (Ψ (segre z)) (c j) * eval (segre z) F ^ (j - k0) := by
    intro z
    rw [hHdef, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, hbind, hF]
  have hmul : ∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) (f' ^ k0)) * eval z H = 0 := by
    intro z hz
    rw [hevalH, map_pow, map_pow, hF, Finset.mul_sum, ← hrelF z hz]
    rw [hSdef, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : k0 ≤ j
    · rw [if_pos hj]
      rw [show j = k0 + (j - k0) from (Nat.add_sub_cancel' hj).symm]
      rw [Nat.add_sub_cancel_left, pow_add]
      ring
    · rw [if_neg hj, hlt j (not_le.mp hj), map_zero, zero_mul]
  have hH := eval_eq_zero_of_mul hM hP (u := f' ^ k0) (fun h' => hf'P (hPp.mem_of_pow_mem _ h'))
    hmul
  set T : Set (Fin (e + 1) → ℂ) :=
    {v | ∃ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) f) = 0 ∧ Ψ (segre z) = v} with hTdef
  have hcT : ∀ v ∈ T, eval v (c k0) = 0 := by
    rintro _ ⟨z, hz, hfz, rfl⟩
    have h0 := hH z hz
    have hF0 : eval (segre z) F = 0 := by
      rw [← hF, hf'def, map_mul, map_mul, hfz, zero_mul]
    rw [hevalH, hF0] at h0
    rw [Finset.sum_eq_single k0] at h0
    · simpa using h0
    · intro j hj hjk
      have : 0 < j - k0 := by
        have := (Finset.mem_filter.mp hj).2
        omega
      rw [zero_pow this.ne', mul_zero]
    · intro h
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), le_rfl⟩) h
  have hT : ∀ v ∈ T, ∀ t : ℂ, t ≠ 0 → (fun j => t * v j) ∈ T := by
    rintro _ ⟨z, hz, hfz, rfl⟩ t ht
    set cc : K → ℂ := Function.update (fun _ => (1 : ℂ)) k1 t with hccdef
    have hcc : ∀ k, cc k ≠ 0 := by
      intro k
      by_cases hk : k = k1
      · subst hk; simp [hccdef, ht]
      · simp [hccdef, Function.update_of_ne hk]
    have hpc : ∏ k, cc k = t := by
      simp [hccdef, Finset.prod_update_of_mem (Finset.mem_univ k1)]
    refine ⟨fun p => cc p.1 * z p, mcPts_smul hPh cc hcc hz, ?_, ?_⟩
    · rw [eval_smul_homog f a hf cc z, hfz, mul_zero]
    · rw [segre_smul, map_smul, hpc]
      rfl
  obtain ⟨m, hm0, hmh, hmT⟩ := exists_homog_of_cone hk0 hT hcT
  exact ⟨homogeneousComponent m (c k0), m, hm0, hmh, fun z hz hfz => hmT _ ⟨z, hz, hfz, rfl⟩⟩

end ReciprocityTheory.ChartRestriction.G.Geo

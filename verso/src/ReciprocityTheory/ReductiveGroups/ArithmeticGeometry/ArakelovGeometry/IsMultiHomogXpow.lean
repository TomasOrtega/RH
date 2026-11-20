import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.NotRelevantOfDimZero

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def xpow (i : ∀ k, ι k) (e : K → ℕ) : MRing ι := ∏ k, (X ⟨k, i k⟩ : MRing ι) ^ (e k)

/- English proof (translation)
Introduce `m hm k`. Take `⟨a, ha, b, hb, rfl⟩` from `Finset.mem_add.mp (MvPolynomial.support_mul f g hm)`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib, hf a ha k, hg b hb k, Pi.add_apply]`.
-/
private theorem isMultiHomog_mul_lemma {f g : MRing ι} {c c' : K → ℕ} (hf : IsMultiHomog f c)
    (hg : IsMultiHomog g c') : IsMultiHomog (f * g) (c + c') := by
  classical
  intro m hm k
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf a ha k, hg b hb k, Pi.add_apply]

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_one]`. Use `split_ifs at hm with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Conclude with `absurd rfl hm`.
-/
private theorem isMultiHomog_one_arakelov_geometry : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
  split_ifs at hm with h
  · subst h
    simp
  · exact absurd rfl hm

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Simplify using `only [pow_zero, zero_smul]`. Conclude with `isMultiHomog_one_arakelov_geometry`. Consider the case `succ n ih`.

Rewrite using `[pow_succ, succ_nsmul]`. Conclude with `isMultiHomog_mul_lemma ih hf`.
-/
theorem isMultiHomog_pow {f : MRing ι} {c : K → ℕ} (hf : IsMultiHomog f c) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • c) := by
  induction n with
  | zero =>
    simp only [pow_zero, zero_smul]
    exact isMultiHomog_one_arakelov_geometry
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact isMultiHomog_mul_lemma ih hf

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using isMultiHomog_one_arakelov_geometry`. Consider the case `@insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `isMultiHomog_mul_lemma (h a) ih`.
-/
theorem isMultiHomog_prod (s : Finset K) (g : K → MRing ι) (c : K → K → ℕ)
    (h : ∀ k, IsMultiHomog (g k) (c k)) : IsMultiHomog (∏ k ∈ s, g k) (∑ k ∈ s, c k) := by
  induction s using Finset.induction_on with
  | empty => simpa using isMultiHomog_one_arakelov_geometry
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact isMultiHomog_mul_lemma (h a) ih

/- English proof (translation)
Establish `hX : ∀ k, IsMultiHomog (X ⟨k, i k⟩ : MRing ι) (Pi.single k 1)`. Introduce `k m hm k'`. Rewrite `hm` using `[MvPolynomial.support_X, Finset.mem_singleton]`. Substitute `hm` using the available equality. Distinguish the cases in `hk : k' = k`.

Substitute `hk` using the available equality. Rewrite using `[Finset.sum_eq_single (i k')]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[Finsupp.single_apply, Sigma.mk.inj_iff, Ne.symm hj]`.

Simplify using the standard rewrite rules. Simplify using `[Finsupp.single_apply, Sigma.mk.inj_iff, hk, Ne.symm hk]`. Establish `h` using `isMultiHomog_prod Finset.univ (fun k => (X ⟨k, i k⟩ : MRing ι) ^ e k) (fun k => e k • Pi.single k 1) (fun k => isMultiHomog_pow (hX k) (e k))`. Establish `he : (∑ k, e k • Pi.single k 1 : K → ℕ) = e`. Use extensionality with `k'`.

Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite `h` using `[he]`. Conclude with `h`.
-/
theorem isMultiHomog_xpow (i : ∀ k, ι k) (e : K → ℕ) : IsMultiHomog (xpow i e) e := by
  classical
  have hX : ∀ k, IsMultiHomog (X ⟨k, i k⟩ : MRing ι) (Pi.single k 1) := by
    intro k m hm k'
    rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
    subst hm
    by_cases hk : k' = k
    · subst hk
      rw [Finset.sum_eq_single (i k')]
      · simp
      · intro j _ hj
        simp [Finsupp.single_apply, Sigma.mk.inj_iff, Ne.symm hj]
      · simp
    · simp [Finsupp.single_apply, Sigma.mk.inj_iff, hk, Ne.symm hk]
  have h := isMultiHomog_prod Finset.univ (fun k => (X ⟨k, i k⟩ : MRing ι) ^ e k)
    (fun k => e k • Pi.single k 1) (fun k => isMultiHomog_pow (hX k) (e k))
  have he : (∑ k, e k • Pi.single k 1 : K → ℕ) = e := by
    ext k'
    simp [Finset.sum_apply, Pi.single_apply]
  rw [he] at h
  exact h

def dehomI (W : Ideal (MRing ι)) (i : ∀ k, ι k) : Ideal (MRing ι) :=
  W ⊔ Ideal.span (Set.range fun k => (X ⟨k, i k⟩ : MRing ι) - 1)

/- English proof (translation)
Unfold `xpow`. Rewrite using `[map_prod]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `k _`. Establish `hk : Ideal.Quotient.mk (dehomI W i) (X ⟨k, i k⟩) = 1`.

Rewrite using `[← sub_eq_zero, ← map_one (Ideal.Quotient.mk (dehomI W i)), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)`. Rewrite using `[map_pow, hk, one_pow]`.
-/
theorem mk_xpow (W : Ideal (MRing ι)) (i : ∀ k, ι k) (e : K → ℕ) :
    Ideal.Quotient.mk (dehomI W i) (xpow i e) = 1 := by
  unfold xpow
  rw [map_prod]
  apply Finset.prod_eq_one
  intro k _
  have hk : Ideal.Quotient.mk (dehomI W i) (X ⟨k, i k⟩) = 1 := by
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk (dehomI W i)), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
  rw [map_pow, hk, one_pow]

/- English proof (translation)
Use `haveI : W.IsPrime := hWp`. Take `⟨F, _, q, hq⟩ : ∃ (F : Type) (_ : Field F) (q : MRing ι →+* F), ∀ f, q f = 0 ↔ f ∈ W` from `⟨FractionRing (MRing ι ⧸ W), inferInstance, (algebraMap (MRing ι ⧸ W) _).comp (Ideal.Quotient.mk W), fun f => by`. Rewrite using `[RingHom.comp_apply, show (0 : FractionRing (MRing ι ⧸ W)) = algebraMap (MRing ι ⧸ W) _ 0 from (map_zero _).symm, (IsFractionRing.injective (MRing ι ⧸ W) _).eq_iff, Ideal.Quotient.eq_zero_iff_mem]⟩`. Establish `hc : ∀ k, q (X ⟨k, i k⟩) ≠ 0` using `fun k h => hi k ((hq _).1 h)`. Take `⟨Θ, hΘ⟩ : ∃ Θ : MRing ι →+* F, Θ = MvPolynomial.eval₂Hom (Int.castRingHom F) (fun p => q (X p) / q (X ⟨p.1, i p.1⟩))` from `⟨_, rfl⟩`.

Establish `hqm : ∀ (m : ((k : K) × ι k) →₀ ℕ) (c : ℤ), q (monomial m c) = (c : F) * ∏ p ∈ m.support, q (X p) ^ m p`. Introduce `m c`. Rewrite using `[MvPolynomial.monomial_eq, map_mul]`. Simplify using `only [Finsupp.prod, map_prod, map_pow]`. Use `congr 1`.

Conclude with `eq_intCast (q.comp MvPolynomial.C) c`. Establish `hΘm : ∀ (m : ((k : K) × ι k) →₀ ℕ) (c : ℤ), Θ (monomial m c) = (c : F) * ∏ p ∈ m.support, (q (X p) / q (X ⟨p.1, i p.1⟩)) ^ m p`. Introduce `m c`. Rewrite using `[hΘ, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial, eq_intCast]`. Both sides reduce to the same expression.

Establish `key : ∀ (f : MRing ι) (d : K → ℕ), IsMultiHomog f d → Θ f * ∏ k, q (X ⟨k, i k⟩) ^ d k = q f`. Introduce `f d hf`. Establish `hC : ∏ k, q (X ⟨k, i k⟩) ^ d k ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)`. Use `conv_lhs => rw [f.as_sum]`. Use `conv_rhs => rw [f.as_sum]`.

Rewrite using `[map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hcm : ∏ p ∈ m.support, q (X ⟨p.1, i p.1⟩) ^ m p = ∏ k, q (X ⟨k, i k⟩) ^ d k`. Rewrite using `[Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp => by`. Rewrite `hp` using `[Finsupp.mem_support_iff, not_not]`.

Rewrite using `[hp, pow_zero]), Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hf m hm k]`. Rewrite using `[hΘm, hqm]`.

Simplify using `only [div_pow]`. Rewrite using `[Finset.prod_div_distrib, hcm, mul_assoc, div_mul_cancel₀ _ hC]`. Establish `hW : W ≤ RingHom.ker Θ`. Take `⟨S, hS, hWS⟩` from `hWm`. Introduce `w hw`.

Establish `hw' : w ∈ Ideal.span S` using `hWS ▸ hw`. Use `(Ideal.span_le.mpr ?_) hw'` and prove the remaining obligations. Introduce `f hf`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker]`. Take `⟨d, hd⟩` from `hS f hf`.

Establish `h1` using `key f d hd`. Establish `h2 : q f = 0` using `(hq f).2 (by rw [hWS]; exact Ideal.subset_span hf)`. Rewrite `h1` using `[h2]`. Conclude with `(mul_eq_zero.mp h1).resolve_right (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k))`. Establish `hJ : ∀ k, Θ ((X ⟨k, i k⟩ : MRing ι) - 1) = 0`.

Introduce `k`. Rewrite using `[map_sub, map_one, hΘ, MvPolynomial.eval₂Hom_X', div_self (hc k), sub_self]`. Establish `hle : W ⊔ Ideal.span (Set.range fun k => (X ⟨k, i k⟩ : MRing ι) - 1) ≤ RingHom.ker Θ` using `sup_le hW (Ideal.span_le.mpr (by`. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `RingHom.mem_ker.mpr (hJ k)))`.

Establish `hΘs : Θ s = 0` using `RingHom.mem_ker.mp (hle hsI)`. Establish `h` using `key s a hs`. Rewrite `h` using `[hΘs, zero_mul]`. Conclude with `(hq s).1 h.symm`.
-/
theorem mem_of_mem_dehomI {W : Ideal (MRing ι)} (hWp : W.IsPrime) (hWm : IsMultiHomogIdeal W)
    {i : ∀ k, ι k} (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι) ∉ W) {a : K → ℕ} {s : MRing ι}
    (hs : IsMultiHomog s a) (hsI : s ∈ dehomI W i) : s ∈ W := by
  classical
  haveI : W.IsPrime := hWp
  obtain ⟨F, _, q, hq⟩ : ∃ (F : Type) (_ : Field F) (q : MRing ι →+* F), ∀ f, q f = 0 ↔ f ∈ W :=
    ⟨FractionRing (MRing ι ⧸ W), inferInstance, (algebraMap (MRing ι ⧸ W) _).comp (Ideal.Quotient.mk W),
      fun f => by
        rw [RingHom.comp_apply, show (0 : FractionRing (MRing ι ⧸ W)) = algebraMap (MRing ι ⧸ W) _ 0 from
          (map_zero _).symm, (IsFractionRing.injective (MRing ι ⧸ W) _).eq_iff,
          Ideal.Quotient.eq_zero_iff_mem]⟩
  have hc : ∀ k, q (X ⟨k, i k⟩) ≠ 0 := fun k h => hi k ((hq _).1 h)
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : MRing ι →+* F,
      Θ = MvPolynomial.eval₂Hom (Int.castRingHom F) (fun p => q (X p) / q (X ⟨p.1, i p.1⟩)) := ⟨_, rfl⟩

  have hqm : ∀ (m : ((k : K) × ι k) →₀ ℕ) (c : ℤ),
      q (monomial m c) = (c : F) * ∏ p ∈ m.support, q (X p) ^ m p := by
    intro m c
    rw [MvPolynomial.monomial_eq, map_mul]
    simp only [Finsupp.prod, map_prod, map_pow]
    congr 1
    exact eq_intCast (q.comp MvPolynomial.C) c
  have hΘm : ∀ (m : ((k : K) × ι k) →₀ ℕ) (c : ℤ),
      Θ (monomial m c) = (c : F) * ∏ p ∈ m.support, (q (X p) / q (X ⟨p.1, i p.1⟩)) ^ m p := by
    intro m c
    rw [hΘ, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial, eq_intCast]
    rfl

  have key : ∀ (f : MRing ι) (d : K → ℕ), IsMultiHomog f d →
      Θ f * ∏ k, q (X ⟨k, i k⟩) ^ d k = q f := by
    intro f d hf
    have hC : ∏ k, q (X ⟨k, i k⟩) ^ d k ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
    conv_lhs => rw [f.as_sum]
    conv_rhs => rw [f.as_sum]
    rw [map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hcm : ∏ p ∈ m.support, q (X ⟨p.1, i p.1⟩) ^ m p = ∏ k, q (X ⟨k, i k⟩) ^ d k := by
      rw [Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp => by
        rw [Finsupp.mem_support_iff, not_not] at hp
        rw [hp, pow_zero]), Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      dsimp only
      rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
    rw [hΘm, hqm]
    simp only [div_pow]
    rw [Finset.prod_div_distrib, hcm, mul_assoc, div_mul_cancel₀ _ hC]
  have hW : W ≤ RingHom.ker Θ := by
    obtain ⟨S, hS, hWS⟩ := hWm
    intro w hw
    have hw' : w ∈ Ideal.span S := hWS ▸ hw
    refine (Ideal.span_le.mpr ?_) hw'
    intro f hf
    rw [SetLike.mem_coe, RingHom.mem_ker]
    obtain ⟨d, hd⟩ := hS f hf
    have h1 := key f d hd
    have h2 : q f = 0 := (hq f).2 (by rw [hWS]; exact Ideal.subset_span hf)
    rw [h2] at h1
    exact (mul_eq_zero.mp h1).resolve_right
      (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k))
  have hJ : ∀ k, Θ ((X ⟨k, i k⟩ : MRing ι) - 1) = 0 := by
    intro k
    rw [map_sub, map_one, hΘ, MvPolynomial.eval₂Hom_X', div_self (hc k), sub_self]
  have hle : W ⊔ Ideal.span (Set.range fun k => (X ⟨k, i k⟩ : MRing ι) - 1) ≤ RingHom.ker Θ :=
    sup_le hW (Ideal.span_le.mpr (by
      rintro _ ⟨k, rfl⟩
      exact RingHom.mem_ker.mpr (hJ k)))
  have hΘs : Θ s = 0 := RingHom.mem_ker.mp (hle hsI)
  have h := key s a hs
  rw [hΘs, zero_mul] at h
  exact (hq s).1 h.symm

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

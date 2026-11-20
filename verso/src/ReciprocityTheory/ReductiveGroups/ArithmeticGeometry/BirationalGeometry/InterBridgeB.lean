import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

/- English proof (translation)
Rewrite using `[MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum, MvPolynomial.support_map_of_injective _ (RingHom.injective_int (Int.castRingHom ℂ))]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hc : ∏ p : (Σ k, ι k), c p.1 ^ m p = ∏ k, c k ^ a k`. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Use `show ∏ y, c k ^ m ⟨k, y⟩ = c k ^ a k`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hf m hm k]`. Repeatedly rewrite using `[mul_pow, Finset.prod_mul_distrib, hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_smul_homog (f : MRing ι) (a : K → ℕ) (hf : IsMultiHomog f a) (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * z p) (map (Int.castRingHom ℂ) f) =
      (∏ k, c k ^ a k) * eval z (map (Int.castRingHom ℂ) f) := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum,
    MvPolynomial.support_map_of_injective _ (RingHom.injective_int (Int.castRingHom ℂ))]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hc : ∏ p : (Σ k, ι k), c p.1 ^ m p = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, c k ^ m ⟨k, y⟩ = c k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
  simp_rw [mul_pow, Finset.prod_mul_distrib, hc]
  ring

/- English proof (translation)
Take `⟨S0, hS0, rfl⟩` from `hJ`. Use `⟨fun k => ?_, fun f hf => ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `hz.1 k`. Conclude with `⟨i, mul_ne_zero (hc k) hi⟩`. Establish `hle : Ideal.span S0 ≤ RingHom.ker ((MvPolynomial.eval (fun p => c p.1 * z p)).comp (MvPolynomial.map (Int.castRingHom ℂ)))`.

Rewrite using `[Ideal.span_le]`. Introduce `s hs`. Take `⟨a, ha⟩` from `hS0 s hs`. Simplify using `only [SetLike.mem_coe, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply]`. Rewrite using `[eval_smul_homog s a ha c z, hz.2 s (Ideal.subset_span hs), mul_zero]`.

Use `hle hf` as an intermediate fact. Simplify using `using this`.
-/
theorem mcPts_smul {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) (c : K → ℂ)
    (hc : ∀ k, c k ≠ 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts J) :
    (fun p => c p.1 * z p) ∈ mcPts J := by
  obtain ⟨S0, hS0, rfl⟩ := hJ
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, mul_ne_zero (hc k) hi⟩
  · have hle : Ideal.span S0 ≤ RingHom.ker ((MvPolynomial.eval (fun p => c p.1 * z p)).comp
        (MvPolynomial.map (Int.castRingHom ℂ))) := by
      rw [Ideal.span_le]
      intro s hs
      obtain ⟨a, ha⟩ := hS0 s hs
      simp only [SetLike.mem_coe, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply]
      rw [eval_smul_homog s a ha c z, hz.2 s (Ideal.subset_span hs), mul_zero]
    have := hle hf
    simpa using this

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `h`. Conclude with `mcPts_smul hJ c hc hz'`.
-/
theorem mem_mcPts_of_sameOrbit {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J)
    {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (hz' : z' ∈ mcPts J) : z ∈ mcPts J := by
  obtain ⟨c, hc, rfl⟩ := h
  exact mcPts_smul hJ c hc hz'

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [segre, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]`.
-/
theorem segre_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    segre (fun p => c p.1 * z p) = (∏ k, c k) • segre z := by
  funext i
  simp only [segre, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

/- English proof (translation)
Unfold `segre`. Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]`. Use `congr 1`. Simplify using the standard rewrite rules. Use `Finset.prod_congr rfl fun l hl => ?_` and prove the remaining obligations.

Simplify using `[Finset.ne_of_mem_erase hl]`.
-/
theorem segre_update [DecidableEq K] (z : (Σ k, ι k) → ℂ) (p : (k : K) → ι k) (k : K) (i : ι k) :
    segre z (Function.update p k i) = z ⟨k, i⟩ * ∏ l ∈ Finset.univ.erase k, z ⟨l, p l⟩ := by
  unfold segre
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun l hl => ?_
    simp [Finset.ne_of_mem_erase hl]

/- English proof (translation)
Use `choose p0 hp0 using hz'`. Establish `hz0 : ∀ k, z ⟨k, p0 k⟩ ≠ 0`. Establish `hs : segre z p0 ≠ 0`. Rewrite using `[h, Pi.smul_apply, smul_eq_mul]`. Conclude with `mul_ne_zero hμ (Finset.prod_ne_zero_iff.mpr fun k _ => hp0 k)`.

Introduce `k hk`. Conclude with `hs (Finset.prod_eq_zero (Finset.mem_univ k) hk)`. Establish `hR : ∀ k, ∏ l ∈ Finset.univ.erase k, z ⟨l, p0 l⟩ ≠ 0` using `fun k => Finset.prod_ne_zero_iff.mpr fun l _ => hz0 l`. Establish `hR' : ∀ k, ∏ l ∈ Finset.univ.erase k, z' ⟨l, p0 l⟩ ≠ 0` using `fun k => Finset.prod_ne_zero_iff.mpr fun l _ => hp0 l`. Use `⟨fun k => μ * (∏ l ∈ Finset.univ.erase k, z' ⟨l, p0 l⟩) / ∏ l ∈ Finset.univ.erase k, z ⟨l, p0 l⟩, fun k => div_ne_zero (mul_ne_zero hμ (hR' k)) (hR k), ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `q`. Take `⟨k, i⟩` from `q`. Establish `e` using `congrFun h (Function.update p0 k i)`. Rewrite `e` using `[Pi.smul_apply, smul_eq_mul, segre_update, segre_update]`. Use `show z ⟨k, i⟩ = μ * (∏ l ∈ Finset.univ.erase k, z' ⟨l, p0 l⟩) / (∏ l ∈ Finset.univ.erase k, z ⟨l, p0 l⟩) * z' ⟨k, i⟩`.

Clear denominators, using `[hR k]` for the nonvanishing conditions. Take the linear combination `e`.
-/
theorem sameOrbit_of_segre {z z' : (Σ k, ι k) → ℂ} (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (μ : ℂ)
    (hμ : μ ≠ 0) (h : segre z = μ • segre z') : SameOrbit z z' := by
  classical
  choose p0 hp0 using hz'
  have hz0 : ∀ k, z ⟨k, p0 k⟩ ≠ 0 := by
    have hs : segre z p0 ≠ 0 := by
      rw [h, Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero hμ (Finset.prod_ne_zero_iff.mpr fun k _ => hp0 k)
    intro k hk
    exact hs (Finset.prod_eq_zero (Finset.mem_univ k) hk)
  have hR : ∀ k, ∏ l ∈ Finset.univ.erase k, z ⟨l, p0 l⟩ ≠ 0 :=
    fun k => Finset.prod_ne_zero_iff.mpr fun l _ => hz0 l
  have hR' : ∀ k, ∏ l ∈ Finset.univ.erase k, z' ⟨l, p0 l⟩ ≠ 0 :=
    fun k => Finset.prod_ne_zero_iff.mpr fun l _ => hp0 l
  refine ⟨fun k => μ * (∏ l ∈ Finset.univ.erase k, z' ⟨l, p0 l⟩) / ∏ l ∈ Finset.univ.erase k, z ⟨l, p0 l⟩,
    fun k => div_ne_zero (mul_ne_zero hμ (hR' k)) (hR k), ?_⟩
  funext q
  obtain ⟨k, i⟩ := q
  have e := congrFun h (Function.update p0 k i)
  rw [Pi.smul_apply, smul_eq_mul, segre_update, segre_update] at e
  show z ⟨k, i⟩ = μ * (∏ l ∈ Finset.univ.erase k, z' ⟨l, p0 l⟩) / (∏ l ∈ Finset.univ.erase k, z ⟨l, p0 l⟩) * z' ⟨k, i⟩
  field_simp [hR k]
  linear_combination e

end ReciprocityTheory.ChartRestriction.G.Geo

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartPrimePowerInverse
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

/- English proof (translation)
Rewrite using `[aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.sum_mul]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hc : (∏ i : (Σ k, ι k), t i.1 ^ d i) = ∏ k, t k ^ a k`. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Use `show ∏ x, t k ^ d ⟨k, x⟩ = _`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hf d hd k]`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aeval_mul_blockScale_of_isMultiHomog {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {Ω : Type*} [CommRing Ω] {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (t : K → Ω)
    (y : (Σ k, ι k) → Ω) :
    aeval (fun p => y p * t p.1) f = aeval y f * ∏ k, t k ^ a k := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hc : (∏ i : (Σ k, ι k), t i.1 ^ d i) = ∏ k, t k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ x, t k ^ d ⟨k, x⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf d hd k]
  simp only [mul_pow, Finset.prod_mul_distrib, hc]
  ring

/- English proof (translation)
Establish `h0 : mConeMap y f = 0` using `hf`. Establish `hcomp : ((aeval t).restrictScalars ℤ).comp (mConeMap y) = aeval (fun p => y p * t p.1)` using `MvPolynomial.algHom_ext fun p => by simp [mConeMap]`. Rewrite using `[← hcomp, AlgHom.comp_apply, h0, map_zero]`.
-/
theorem aeval_mul_blockScale_eq_zero_of_mem_mCoordIdeal {K : Type*} [Fintype K] {ι : K → Type*}
    [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω] {y : (Σ k, ι k) → Ω} {f : MRing ι}
    (hf : f ∈ mCoordIdeal y) (t : K → Ω) : aeval (fun p => y p * t p.1) f = 0 := by
  have h0 : mConeMap y f = 0 := hf
  have hcomp : ((aeval t).restrictScalars ℤ).comp (mConeMap y) = aeval (fun p => y p * t p.1) :=
    MvPolynomial.algHom_ext fun p => by simp [mConeMap]
  rw [← hcomp, AlgHom.comp_apply, h0, map_zero]

/- English proof (translation)
Introduce `K _ ι _ Ω _ _ y D e L hhom hL p hp j hj`. Take `⟨N, hN⟩` from `PullConeNull.proof K ι Ω y D L hL`. Establish `hp0 : (p : Ω) ≠ 0` using `Nat.cast_ne_zero.mpr hp.ne_zero`. Establish `key : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ a : ℕ, (p : Ω) ^ a * (∏ k, y ⟨k, c k⟩ ^ e k) / aeval y (L j) ∈ Subring.closure (Set.range (fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩) ∪ Set.range (fun i => aeval y (L i) / aeval y (L j)) ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹})`. Introduce `c hc`.

Use `set R := Subring.closure (Set.range (fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩) ∪ Set.range (fun i => aeval y (L i) / aeval y (L j)) ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹}) with hR`. Use `set Y := ∏ k, y ⟨k, c k⟩ ^ e k with hYdef`. Establish `hY : Y ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)`. Establish `hpR : ∀ n : ℕ, (p : Ω) ^ n ∈ R` using `fun n => R.pow_mem (natCast_mem R p) n`. Set `G : Subalgebra ℚ Ω` to `{ carrier := {x | ∃ a : ℕ, (p : Ω) ^ a * x ∈ R} mul_mem' := by`.

Introduce and unpack `x z ⟨a, ha⟩ ⟨b, hb⟩`. Use `⟨a + b, ?_⟩` and prove the remaining obligations. Establish `: (p : Ω) ^ (a + b) * (x * z) = ((p : Ω) ^ a * x) * ((p : Ω) ^ b * z)` using `by ring`. Rewrite using `[this]`. Conclude with `R.mul_mem ha hb`.

Use the proof step `add_mem' := by`. Introduce and unpack `x z ⟨a, ha⟩ ⟨b, hb⟩`. Use `⟨a + b, ?_⟩` and prove the remaining obligations. Establish `: (p : Ω) ^ (a + b) * (x + z) = (p : Ω) ^ b * ((p : Ω) ^ a * x) + (p : Ω) ^ a * ((p : Ω) ^ b * z)`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `R.add_mem (R.mul_mem (hpR b) ha) (R.mul_mem (hpR a) hb)`. Use the proof step `algebraMap_mem' := by`. Introduce `q`. Take `⟨b, d', hd', hden⟩` from `Nat.exists_eq_pow_mul_and_not_dvd q.den_nz p hp.one_lt.ne'`.

Use `⟨b, ?_⟩` and prove the remaining obligations. Establish `hden' : (q.den : Ω) = (p : Ω) ^ b * (d' : Ω)` using `by exact_mod_cast hden`. Establish `hd0 : (d' : Ω) ≠ 0`. Introduce `h0`. Establish `: (q.den : Ω) ≠ 0` using `Nat.cast_ne_zero.mpr q.den_nz`.

Rewrite `this` using `[hden', h0, mul_zero]`. Conclude with `this rfl`. Establish `: (p : Ω) ^ b * algebraMap ℚ Ω q = (q.num : Ω) * (d' : Ω)⁻¹`. Rewrite using `[eq_ratCast, Rat.cast_def, hden']`. Clear the denominators using the available nonvanishing facts.

Use `show (p : Ω) ^ b * algebraMap ℚ Ω q ∈ R`. Rewrite using `[this]`. Conclude with `R.mul_mem (intCast_mem R _) (Subring.subset_closure (Or.inr ⟨d', hd', rfl⟩)) }`. Establish `hmemG : ∀ x ∈ R, x ∈ G` using `fun x hx => ⟨0, by simpa using hx⟩`. Set `r : (Σ k, ι k) → Ω` to `fun q => y q / y ⟨q.1, c q.1⟩`.

Set `χ : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] Ω` to `aeval r`. Set `t : K → Ω` to `fun k => (y ⟨k, c k⟩)⁻¹`. Establish `hχG : ∀ g, χ g ∈ G`. Introduce `g`. Proceed by induction on `g using MvPolynomial.induction_on with`.

Consider the case `C q => simpa [χ] using G.algebraMap_mem q`. Consider the case `add f g hf hg => simpa using G.add_mem hf hg`. Consider the case `mul_X f q hf`. Simplify `G.mul_mem hf (hmemG _ (Subring.subset_closure (Or.inl (Or.inl ⟨q, rfl⟩))))` using `[χ]`. Establish `hχmap : ∀ f : MRing ι, χ (map (Int.castRingHom ℚ) f) = aeval (fun q => y q * t q.1) f`.

Introduce `f`. Rewrite using `[← algebraMap_int_eq, aeval_map_algebraMap]`. Simplify using `only [r, t, div_eq_mul_inv]`. Set `J : Ideal (MvPolynomial (Σ k, ι k) ℚ)` to `{ carrier := {f | χ f * (Y / aeval y (L j)) ∈ G} add_mem' := by`. Introduce `f g hf hg`.

Simplify `G.add_mem hf hg` using `[add_mul]`. Use the proof step `zero_mem' := by simp`. Use the proof step `smul_mem' := by`. Introduce `g f hf`. Simplify `G.mul_mem (hχG g) hf }` using `[smul_eq_mul, mul_assoc]`.

Establish `hIJ : coneNullIdeal y L ≤ J`. Use `Ideal.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `f (⟨f, hf, rfl⟩ | ⟨i, rfl⟩)`. Use `show χ _ * _ ∈ G`. Rewrite using `[hχmap, aeval_mul_blockScale_eq_zero_of_mem_mCoordIdeal hf t, zero_mul]`.

Conclude with `G.zero_mem`. Use `show χ _ * _ ∈ G`. Rewrite using `[hχmap, aeval_mul_blockScale_of_isMultiHomog (hhom i) t]`. Establish `: aeval y (L i) * (∏ k, t k ^ e k) * (Y / aeval y (L j)) = aeval y (L i) / aeval y (L j)`. Establish `hprod : (∏ k, t k ^ e k) = Y⁻¹`.

Rewrite using `[hYdef, ← Finset.prod_inv_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => inv_pow _ _`. Rewrite using `[hprod]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`.

Conclude with `hmemG _ (Subring.subset_closure (Or.inl (Or.inr ⟨i, rfl⟩)))`. Establish `h1` using `hIJ (hN c)`. Establish `hone : χ ((∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℚ)) ^ N) = 1`. Simplify using `[χ, r, div_self (hc _)]`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : Y / aeval y (L j) ∈ G := by`.

Establish `: χ ((∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℚ)) ^ N) * (Y / aeval y (L j)) ∈ G` using `h1`. Rewrite `this` using `[hone, one_mul]`. Then use the resulting hypothesis. Conclude with `⟨a, by rw [mul_div_assoc]; exact ha⟩`. Use `choose! a ha using key`. Use `⟨Finset.univ.sup a, fun c hc => ?_⟩` and prove the remaining obligations.

Establish `hle : a c ≤ Finset.univ.sup a` using `Finset.le_sup (Finset.mem_univ c)`. Establish `e1 : (p : Ω) ^ Finset.univ.sup a * (∏ k, y ⟨k, c k⟩ ^ e k) / aeval y (L j) = (p : Ω) ^ (Finset.univ.sup a - a c) * ((p : Ω) ^ a c * (∏ k, y ⟨k, c k⟩ ^ e k) / aeval y (L j))`. Rewrite using `[← Nat.sub_add_cancel hle, pow_add, Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`.

Conclude with `Subring.mul_mem _ (Subring.pow_mem _ (natCast_mem _ p) _) (ha c hc)`.
-/
theorem ChartPrimePowerInverse.proof : ChartPrimePowerInverse.Statement := by
  classical
  intro K _ ι _ Ω _ _ y D e L hhom hL p hp j hj
  obtain ⟨N, hN⟩ := PullConeNull.proof K ι Ω y D L hL
  have hp0 : (p : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have key : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ a : ℕ,
      (p : Ω) ^ a * (∏ k, y ⟨k, c k⟩ ^ e k) / aeval y (L j) ∈
        Subring.closure (Set.range (fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩) ∪
          Set.range (fun i => aeval y (L i) / aeval y (L j)) ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹}) := by
    intro c hc
    set R := Subring.closure (Set.range (fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩) ∪
          Set.range (fun i => aeval y (L i) / aeval y (L j)) ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹}) with hR
    set Y := ∏ k, y ⟨k, c k⟩ ^ e k with hYdef
    have hY : Y ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
    have hpR : ∀ n : ℕ, (p : Ω) ^ n ∈ R := fun n => R.pow_mem (natCast_mem R p) n

    let G : Subalgebra ℚ Ω :=
      { carrier := {x | ∃ a : ℕ, (p : Ω) ^ a * x ∈ R}
        mul_mem' := by
          rintro x z ⟨a, ha⟩ ⟨b, hb⟩
          refine ⟨a + b, ?_⟩
          have : (p : Ω) ^ (a + b) * (x * z) = ((p : Ω) ^ a * x) * ((p : Ω) ^ b * z) := by ring
          rw [this]
          exact R.mul_mem ha hb
        add_mem' := by
          rintro x z ⟨a, ha⟩ ⟨b, hb⟩
          refine ⟨a + b, ?_⟩
          have : (p : Ω) ^ (a + b) * (x + z) = (p : Ω) ^ b * ((p : Ω) ^ a * x) + (p : Ω) ^ a * ((p : Ω) ^ b * z) := by
            ring
          rw [this]
          exact R.add_mem (R.mul_mem (hpR b) ha) (R.mul_mem (hpR a) hb)
        algebraMap_mem' := by
          intro q
          obtain ⟨b, d', hd', hden⟩ := Nat.exists_eq_pow_mul_and_not_dvd q.den_nz p hp.one_lt.ne'
          refine ⟨b, ?_⟩
          have hden' : (q.den : Ω) = (p : Ω) ^ b * (d' : Ω) := by exact_mod_cast hden
          have hd0 : (d' : Ω) ≠ 0 := by
            intro h0
            have : (q.den : Ω) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
            rw [hden', h0, mul_zero] at this
            exact this rfl
          have : (p : Ω) ^ b * algebraMap ℚ Ω q = (q.num : Ω) * (d' : Ω)⁻¹ := by
            rw [eq_ratCast, Rat.cast_def, hden']
            field_simp
          show (p : Ω) ^ b * algebraMap ℚ Ω q ∈ R
          rw [this]
          exact R.mul_mem (intCast_mem R _) (Subring.subset_closure (Or.inr ⟨d', hd', rfl⟩)) }
    have hmemG : ∀ x ∈ R, x ∈ G := fun x hx => ⟨0, by simpa using hx⟩
    let r : (Σ k, ι k) → Ω := fun q => y q / y ⟨q.1, c q.1⟩
    let χ : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] Ω := aeval r
    let t : K → Ω := fun k => (y ⟨k, c k⟩)⁻¹
    have hχG : ∀ g, χ g ∈ G := by
      intro g
      induction g using MvPolynomial.induction_on with
      | C q => simpa [χ] using G.algebraMap_mem q
      | add f g hf hg => simpa using G.add_mem hf hg
      | mul_X f q hf =>
        simpa [χ] using G.mul_mem hf (hmemG _ (Subring.subset_closure (Or.inl (Or.inl ⟨q, rfl⟩))))
    have hχmap : ∀ f : MRing ι,
        χ (map (Int.castRingHom ℚ) f) = aeval (fun q => y q * t q.1) f := by
      intro f
      rw [← algebraMap_int_eq, aeval_map_algebraMap]
      simp only [r, t, div_eq_mul_inv]

    let J : Ideal (MvPolynomial (Σ k, ι k) ℚ) :=
      { carrier := {f | χ f * (Y / aeval y (L j)) ∈ G}
        add_mem' := by
          intro f g hf hg
          simpa [add_mul] using G.add_mem hf hg
        zero_mem' := by simp
        smul_mem' := by
          intro g f hf
          simpa [smul_eq_mul, mul_assoc] using G.mul_mem (hχG g) hf }
    have hIJ : coneNullIdeal y L ≤ J := by
      refine Ideal.span_le.mpr ?_
      rintro f (⟨f, hf, rfl⟩ | ⟨i, rfl⟩)
      · show χ _ * _ ∈ G
        rw [hχmap, aeval_mul_blockScale_eq_zero_of_mem_mCoordIdeal hf t, zero_mul]
        exact G.zero_mem
      · show χ _ * _ ∈ G
        rw [hχmap, aeval_mul_blockScale_of_isMultiHomog (hhom i) t]
        have : aeval y (L i) * (∏ k, t k ^ e k) * (Y / aeval y (L j)) =
            aeval y (L i) / aeval y (L j) := by
          have hprod : (∏ k, t k ^ e k) = Y⁻¹ := by
            rw [hYdef, ← Finset.prod_inv_distrib]
            exact Finset.prod_congr rfl fun k _ => inv_pow _ _
          rw [hprod]
          field_simp
        rw [this]
        exact hmemG _ (Subring.subset_closure (Or.inl (Or.inr ⟨i, rfl⟩)))
    have h1 := hIJ (hN c)
    have hone : χ ((∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℚ)) ^ N) = 1 := by
      simp [χ, r, div_self (hc _)]
    obtain ⟨a, ha⟩ : Y / aeval y (L j) ∈ G := by
      have : χ ((∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℚ)) ^ N) * (Y / aeval y (L j)) ∈ G := h1
      rwa [hone, one_mul] at this
    exact ⟨a, by rw [mul_div_assoc]; exact ha⟩
  choose! a ha using key
  refine ⟨Finset.univ.sup a, fun c hc => ?_⟩
  have hle : a c ≤ Finset.univ.sup a := Finset.le_sup (Finset.mem_univ c)
  have e1 : (p : Ω) ^ Finset.univ.sup a * (∏ k, y ⟨k, c k⟩ ^ e k) / aeval y (L j) =
      (p : Ω) ^ (Finset.univ.sup a - a c) * ((p : Ω) ^ a c * (∏ k, y ⟨k, c k⟩ ^ e k) / aeval y (L j)) := by
    rw [← Nat.sub_add_cancel hle, pow_add, Nat.add_sub_cancel]
    ring
  rw [e1]
  exact Subring.mul_mem _ (Subring.pow_mem _ (natCast_mem _ p) _) (ha c hc)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

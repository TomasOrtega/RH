import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsValuativeCentre
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartDehomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Graded

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]
  {κ : Type*} [CommRing κ]

def blockSpecial (ρ : MRing ι F →+* κ) : MRing ι F →+* MvPolynomial K κ :=
  eval₂Hom (C.comp (ρ.comp C)) fun v => C (ρ (X v)) * X v.1

/- English proof (translation)
Establish `hT : (monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (blockWeight ι) d)) (1 : κ)) = d.prod fun v n => (X v.1 : MvPolynomial K κ) ^ n`. Rewrite using `[← prod_pow_blockWeight, monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`. Both sides reduce to the same expression. Rewrite using `[hT, blockSpecial, coe_eval₂Hom, eval₂_monomial, monomial_eq, map_mul, map_mul, map_finsuppProd, map_finsuppProd]`. Simplify using `only [RingHom.comp_apply, mul_pow, map_pow]`.

Rewrite using `[Finsupp.prod_mul, mul_assoc]`.
-/
theorem blockSpecial_monomial (ρ : MRing ι F →+* κ) (d : (Σ k, ι k) →₀ ℕ) (a : F) :
    blockSpecial ρ (monomial d a) = C (ρ (monomial d a)) *
      monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (blockWeight ι) d)) 1 := by
  have hT : (monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (blockWeight ι) d)) (1 : κ)) =
      d.prod fun v n => (X v.1 : MvPolynomial K κ) ^ n := by
    rw [← prod_pow_blockWeight, monomial_eq, C_1, one_mul,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rfl
  rw [hT, blockSpecial, coe_eval₂Hom, eval₂_monomial, monomial_eq, map_mul, map_mul,
    map_finsuppProd, map_finsuppProd]
  simp only [RingHom.comp_apply, mul_pow, map_pow]
  rw [Finsupp.prod_mul, mul_assoc]

/- English proof (translation)
Use `conv_lhs => rw [f.as_sum]`. Rewrite using `[weightedHomogeneousComponent_apply, map_sum, coeff_sum, map_sum, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[blockSpecial_monomial, coeff_C_mul, coeff_monomial]`. Establish `hiff : Finsupp.equivFunOnFinite.symm (Finsupp.weight (blockWeight ι) d) = e ↔ Finsupp.weight (blockWeight ι) d = ⇑e`.

Rewrite using `[Equiv.symm_apply_eq]`. Both sides reduce to the same expression. Distinguish the cases in `h : Finsupp.weight (blockWeight ι) d = ⇑e`. Rewrite using `[if_pos (hiff.mpr h), if_pos h, mul_one]`. Rewrite using `[if_neg (fun h' => h (hiff.mp h')), if_neg h, mul_zero]`.
-/
theorem coeff_blockSpecial (ρ : MRing ι F →+* κ) (f : MRing ι F) (e : K →₀ ℕ) :
    coeff e (blockSpecial ρ f) = ρ (weightedHomogeneousComponent (blockWeight ι) (⇑e) f) := by
  classical
  conv_lhs => rw [f.as_sum]
  rw [weightedHomogeneousComponent_apply, map_sum, coeff_sum, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [blockSpecial_monomial, coeff_C_mul, coeff_monomial]
  have hiff : Finsupp.equivFunOnFinite.symm (Finsupp.weight (blockWeight ι) d) = e ↔
      Finsupp.weight (blockWeight ι) d = ⇑e := by
    rw [Equiv.symm_apply_eq]; rfl
  by_cases h : Finsupp.weight (blockWeight ι) d = ⇑e
  · rw [if_pos (hiff.mpr h), if_pos h, mul_one]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, mul_zero]

end Graded

/- English proof (translation)
Introduce `F _ K _ _ ι _ P hP`. Use `hP.isPrime` as an intermediate fact. Introduce `R hF`. Use `set L := FractionRing (MRing ι F ⧸ P)`. Set `φ : MRing ι F →+* L` to `(algebraMap (MRing ι F ⧸ P) L).comp (Ideal.Quotient.mk P)`.

Establish `hφ : ∀ p, φ p = 0 ↔ p ∈ P` using `fun p => by`. Simplify using `only [φ, RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`. Establish `hmax : ∀ k, ∃ i, (X ⟨k, i⟩ : MRing ι F) ∉ P ∧ ∀ j, R.valuation (φ (X ⟨k, j⟩)) ≤ R.valuation (φ (X ⟨k, i⟩))`. Introduce `k`. Take `⟨i₀, hi₀⟩` from `hP.relevant k`.

Take `⟨i, hi, hmx⟩` from `Finset.exists_max_image (Finset.univ.filter fun j => (X ⟨k, j⟩ : MRing ι F) ∉ P) (fun j => R.valuation (φ (X ⟨k, j⟩))) ⟨i₀, by simp [hi₀]⟩`. Use `⟨i, (Finset.mem_filter.mp hi).2, fun j => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hj : (X ⟨k, j⟩ : MRing ι F) ∈ P`. Rewrite using `[(hφ _).mpr hj, map_zero]`. Conclude with `zero_le`.

Conclude with `hmx j (by simp [hj])`. Use `choose c hcP hcmax using hmax`. Establish `hchart : ∀ p, chartMap P c p ∈ R`. Introduce `p`. Proceed by induction on `p using MvPolynomial.induction_on with`.

Consider the case `C a => rw [chartMap, aeval_C]`. Conclude with `hF a`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `add_mem hp hq`. Consider the case `mul_X p v hp`.

Rewrite using `[map_mul]`. Use `mul_mem hp ?_` and prove the remaining obligations. Rewrite using `[chartMap, aeval_X, ← R.valuation_le_one_iff, map_div₀]`. Establish `h0 : R.valuation (φ (X ⟨v.1, c v.1⟩)) ≠ 0`. Rewrite using `[Ne, Valuation.zero_iff, hφ]`.

Conclude with `hcP v.1`. Conclude with `(div_le_one₀ (zero_lt_iff.mpr h0)).mpr (hcmax v.1 v.2)`. Set `χ : MRing ι F →+* R` to `(chartMap P c).toRingHom.codRestrict R hchart`. Establish `hχ : ∀ p, (χ p : L) = chartMap P c p` using `fun p => rfl`. Set `ρ : MRing ι F →+* IsLocalRing.ResidueField R` to `(IsLocalRing.residue R).comp χ`.

Set `θ : MRing ι F →+* MvPolynomial K (IsLocalRing.ResidueField R)` to `blockSpecial ρ`. Establish `hdeh : ∀ f b, IsMultiHomog f b → chartMap P c f = φ f / φ (chartMonomial c b)` using `fun f b hf => MChartDehomog.proof F K ι P c hcP f b hf`. Establish `hmon : ∀ b, φ (chartMonomial c b) ≠ 0` using `fun b => by`. Simplify using `only [chartMonomial, map_prod, map_pow]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (fun h => hcP k ((hφ _).mp h))`.

Establish `hy : ∀ f, f ∈ RingHom.ker θ ↔ ∀ b : K → ℕ, ρ (weightedHomogeneousComponent (blockWeight ι) b f) = 0`. Introduce `f`. Rewrite using `[RingHom.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `h b`.

Use `congrArg (coeff (Finsupp.equivFunOnFinite.symm b)) h` as an intermediate fact. Rewrite `this` using `[coeff_blockSpecial, coeff_zero, Finsupp.coe_equivFunOnFinite_symm]`. Then use the resulting hypothesis. Introduce `h`. Use extensionality with `e`. Rewrite using `[coeff_blockSpecial, coeff_zero, h]`.

Establish `hyform : ∀ f b, IsMultiHomog f b → (f ∈ RingHom.ker θ ↔ ρ f = 0)`. Introduce `f b hf`. Rewrite using `[hy]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `h b` as an intermediate fact. Rewrite `this` using `[IsWeightedHomogeneous.weightedHomogeneousComponent_same hf]`. Then use the resulting hypothesis. Introduce `h b'`. Distinguish the cases in `hb : b' = b`. Rewrite using `[hb, IsWeightedHomogeneous.weightedHomogeneousComponent_same hf]`.

Conclude with `h`. Rewrite using `[IsWeightedHomogeneous.weightedHomogeneousComponent_ne b' hf hb, map_zero]`. Use `⟨RingHom.ker θ, ⟨RingHom.ker_isPrime θ, ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `f hf b`. Rewrite `hf`, the goal using `[hy]`.

Introduce `b'`. Establish `hb` using `weightedHomogeneousComponent_isWeightedHomogeneous (w := blockWeight ι) b f`. Distinguish the cases in `hbb : b' = b`. Rewrite using `[hbb, IsWeightedHomogeneous.weightedHomogeneousComponent_same hb]`. Conclude with `hf b`.

Rewrite using `[IsWeightedHomogeneous.weightedHomogeneousComponent_ne b' hb hbb, map_zero]`. Introduce `k`. Use `⟨c k, fun h => ?_⟩` and prove the remaining obligations. Establish `hX` using `isWeightedHomogeneous_X F (blockWeight ι) (⟨k, c k⟩ : Σ k, ι k)`. Rewrite `h` using `[hyform _ _ hX]`.

Establish `h1 : χ (X ⟨k, c k⟩) = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hχ, chartMap, aeval_X]`. Conclude with `div_self (fun h' => hcP k ((hφ _).mp h'))`. Simplify using `only [ρ, RingHom.comp_apply, h1, map_one] at h`.

Conclude with `one_ne_zero h`. Introduce `f hf`. Rewrite using `[hy]`. Introduce `b`. Establish `hb` using `weightedHomogeneousComponent_isWeightedHomogeneous (w := blockWeight ι) b f`.

Establish `h0 : χ (weightedHomogeneousComponent (blockWeight ι) b f) = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hχ, hdeh _ _ hb, (hφ _).mpr (hP.multiHomog f hf b), zero_div]`. Both sides reduce to the same expression. Simplify using `only [ρ, RingHom.comp_apply, h0, map_zero]`.

Introduce `b f g hf hg hgy`. Express the relevant statement in the definitionally equal form `φ f / φ g ∈ R ∧ (f ∈ RingHom.ker θ ↔ φ f / φ g ∈ R.nonunits)`. Establish `hgu : IsUnit (χ g)`. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit]`. Conclude with `fun h => hgy ((hyform g b hg).mpr h)`.

Establish `hg0 : (χ g : L) ≠ 0` using `fun h => hgu.ne_zero (Subtype.ext h)`. Establish `hquot : φ f / φ g = ((χ f * ↑hgu.unit⁻¹ : R) : L)`. Establish `e1 : φ f / φ g = (χ f : L) / (χ g : L)`. Rewrite using `[hχ, hχ, hdeh f b hf, hdeh g b hg, div_div_div_cancel_right₀ (hmon b)]`. Establish `e2 : (χ g : L) * ((↑hgu.unit⁻¹ : R) : L) = 1`.

Rewrite using `[← Subring.coe_mul, IsUnit.mul_val_inv]`. Both sides reduce to the same expression. Rewrite using `[e1, div_eq_iff hg0, Subring.coe_mul, mul_assoc, mul_comm _ (χ g : L), e2, mul_one]`. Rewrite using `[hquot, ValuationSubring.coe_mem_nonunits_iff, ← IsLocalRing.residue_eq_zero_iff, map_mul, hyform f b hf]`. Use `⟨Subtype.mem _, ?_⟩` and prove the remaining obligations.

Establish `hu : IsLocalRing.residue R (↑hgu.unit⁻¹ : R) ≠ 0` using `(IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (Units.isUnit _)`. Simplify using `only [ρ, RingHom.comp_apply, mul_eq_zero]`. Conclude with `⟨Or.inl, fun h => h.resolve_right hu⟩`.
-/
theorem ValuativeCentre.proof : ValuativeCentre.Statement.{u} := by
  intro F _ K _ _ ι _ P hP
  have := hP.isPrime
  intro R hF
  set L := FractionRing (MRing ι F ⧸ P)
  let φ : MRing ι F →+* L := (algebraMap (MRing ι F ⧸ P) L).comp (Ideal.Quotient.mk P)
  have hφ : ∀ p, φ p = 0 ↔ p ∈ P := fun p => by
    simp only [φ, RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

  have hmax : ∀ k, ∃ i, (X ⟨k, i⟩ : MRing ι F) ∉ P ∧
      ∀ j, R.valuation (φ (X ⟨k, j⟩)) ≤ R.valuation (φ (X ⟨k, i⟩)) := by
    intro k
    classical
    obtain ⟨i₀, hi₀⟩ := hP.relevant k
    obtain ⟨i, hi, hmx⟩ := Finset.exists_max_image
      (Finset.univ.filter fun j => (X ⟨k, j⟩ : MRing ι F) ∉ P)
      (fun j => R.valuation (φ (X ⟨k, j⟩))) ⟨i₀, by simp [hi₀]⟩
    refine ⟨i, (Finset.mem_filter.mp hi).2, fun j => ?_⟩
    by_cases hj : (X ⟨k, j⟩ : MRing ι F) ∈ P
    · rw [(hφ _).mpr hj, map_zero]; exact zero_le
    · exact hmx j (by simp [hj])
  choose c hcP hcmax using hmax

  have hchart : ∀ p, chartMap P c p ∈ R := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => rw [chartMap, aeval_C]; exact hF a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p v hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      rw [chartMap, aeval_X, ← R.valuation_le_one_iff, map_div₀]
      have h0 : R.valuation (φ (X ⟨v.1, c v.1⟩)) ≠ 0 := by
        rw [Ne, Valuation.zero_iff, hφ]; exact hcP v.1
      exact (div_le_one₀ (zero_lt_iff.mpr h0)).mpr (hcmax v.1 v.2)
  let χ : MRing ι F →+* R := (chartMap P c).toRingHom.codRestrict R hchart
  have hχ : ∀ p, (χ p : L) = chartMap P c p := fun p => rfl
  let ρ : MRing ι F →+* IsLocalRing.ResidueField R := (IsLocalRing.residue R).comp χ
  let θ : MRing ι F →+* MvPolynomial K (IsLocalRing.ResidueField R) := blockSpecial ρ
  have hdeh : ∀ f b, IsMultiHomog f b → chartMap P c f = φ f / φ (chartMonomial c b) :=
    fun f b hf => MChartDehomog.proof F K ι P c hcP f b hf
  have hmon : ∀ b, φ (chartMonomial c b) ≠ 0 := fun b => by
    simp only [chartMonomial, map_prod, map_pow]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (fun h => hcP k ((hφ _).mp h))

  have hy : ∀ f, f ∈ RingHom.ker θ ↔
      ∀ b : K → ℕ, ρ (weightedHomogeneousComponent (blockWeight ι) b f) = 0 := by
    intro f
    rw [RingHom.mem_ker]
    constructor
    · intro h b
      have := congrArg (coeff (Finsupp.equivFunOnFinite.symm b)) h
      rwa [coeff_blockSpecial, coeff_zero, Finsupp.coe_equivFunOnFinite_symm] at this
    · intro h
      ext e
      rw [coeff_blockSpecial, coeff_zero, h]
  have hyform : ∀ f b, IsMultiHomog f b → (f ∈ RingHom.ker θ ↔ ρ f = 0) := by
    intro f b hf
    rw [hy]
    constructor
    · intro h
      have := h b
      rwa [IsWeightedHomogeneous.weightedHomogeneousComponent_same hf] at this
    · intro h b'
      by_cases hb : b' = b
      · rw [hb, IsWeightedHomogeneous.weightedHomogeneousComponent_same hf]; exact h
      · rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne b' hf hb, map_zero]
  refine ⟨RingHom.ker θ, ⟨RingHom.ker_isPrime θ, ?_, ?_⟩, ?_, ?_⟩
  ·
    intro f hf b
    rw [hy] at hf ⊢
    intro b'
    have hb := weightedHomogeneousComponent_isWeightedHomogeneous (w := blockWeight ι) b f
    by_cases hbb : b' = b
    · rw [hbb, IsWeightedHomogeneous.weightedHomogeneousComponent_same hb]; exact hf b
    · rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne b' hb hbb, map_zero]
  ·
    intro k
    refine ⟨c k, fun h => ?_⟩
    have hX := isWeightedHomogeneous_X F (blockWeight ι) (⟨k, c k⟩ : Σ k, ι k)
    rw [hyform _ _ hX] at h
    have h1 : χ (X ⟨k, c k⟩) = 1 := by
      apply Subtype.ext
      rw [hχ, chartMap, aeval_X]
      exact div_self (fun h' => hcP k ((hφ _).mp h'))
    simp only [ρ, RingHom.comp_apply, h1, map_one] at h
    exact one_ne_zero h
  ·
    intro f hf
    rw [hy]
    intro b
    have hb := weightedHomogeneousComponent_isWeightedHomogeneous (w := blockWeight ι) b f
    have h0 : χ (weightedHomogeneousComponent (blockWeight ι) b f) = 0 := by
      apply Subtype.ext
      rw [hχ, hdeh _ _ hb, (hφ _).mpr (hP.multiHomog f hf b), zero_div]
      rfl
    simp only [ρ, RingHom.comp_apply, h0, map_zero]
  ·
    intro b f g hf hg hgy
    change φ f / φ g ∈ R ∧ (f ∈ RingHom.ker θ ↔ φ f / φ g ∈ R.nonunits)
    have hgu : IsUnit (χ g) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
      exact fun h => hgy ((hyform g b hg).mpr h)
    have hg0 : (χ g : L) ≠ 0 := fun h => hgu.ne_zero (Subtype.ext h)
    have hquot : φ f / φ g = ((χ f * ↑hgu.unit⁻¹ : R) : L) := by
      have e1 : φ f / φ g = (χ f : L) / (χ g : L) := by
        rw [hχ, hχ, hdeh f b hf, hdeh g b hg, div_div_div_cancel_right₀ (hmon b)]
      have e2 : (χ g : L) * ((↑hgu.unit⁻¹ : R) : L) = 1 := by
        rw [← Subring.coe_mul, IsUnit.mul_val_inv]; rfl
      rw [e1, div_eq_iff hg0, Subring.coe_mul, mul_assoc, mul_comm _ (χ g : L), e2, mul_one]
    rw [hquot, ValuationSubring.coe_mem_nonunits_iff, ← IsLocalRing.residue_eq_zero_iff, map_mul,
      hyform f b hf]
    refine ⟨Subtype.mem _, ?_⟩
    have hu : IsLocalRing.residue R (↑hgu.unit⁻¹ : R) ≠ 0 :=
      (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (Units.isUnit _)
    simp only [ρ, RingHom.comp_apply, mul_eq_zero]
    exact ⟨Or.inl, fun h => h.resolve_right hu⟩

end

end GroundTheory.Heights₂.Heights.FieldNumbers

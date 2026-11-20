import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.FfHasInfChar

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def ffg_IsSq {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  Nontrivial H ∧ IsURepOn (UJset ε) σ' ∧ IsIrredOn (UJset ε) σ' ∧ IsSqIntOn ε σ'

def ffg_Equiv {n : ℕ} {H' H : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ε : Fin n → Bool) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H'))
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∃ U : H' ≃ₗᵢ[ℂ] H, ∀ g ∈ UJset ε, ∀ v : H', U (σ' g v) = σ g (U v)

def QOrth : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool),
    (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), ffg_IsSq ε σ' → ∃ d : ℝ, IsFdeg (Formalism.REAL.muG ε) σ' d) ∧
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H'))
      (H'' : Type) [NormedAddCommGroup H''] [InnerProductSpace ℂ H''] [CompleteSpace H'']
      (σ'' : Matrix (Fin n) (Fin n) ℂ → (H'' →L[ℂ] H'')), ffg_IsSq ε σ' → ffg_IsSq ε σ'' → ¬ ffg_Equiv ε σ' σ'' →
      ∀ (a b : H') (a' b' : H''), ∫ g, coefOn σ' a b g * star (coefOn σ'' a' b' g) ∂(Formalism.REAL.muG ε) = 0

def FCharOther (χ : ∀ n : ℕ, (Fin n → ℝ) → ℕ → ℂ) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ →
    IsOrthProjOnto E (lowKSub ε lam σ) →
    ∀ Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H), ff_Sph ε σ Ψ → ff_Compr ε E Ψ → ff_Eig ε (χ n lam) Ψ → ff_DSSum ε Ψ →
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (π' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), ffg_IsSq ε π' → ∀ (x y : H) (a b : H'),
      ∫ g, ⟪x, Ψ (umat g) y⟫_ℂ * star (coefOn π' a b g) ∂(Formalism.REAL.muG ε) ≠ 0 → ff_HasInfChar ε π' (χ n lam)

def FKTypeOther : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ →
    IsOrthProjOnto E (lowKSub ε lam σ) →
    ∀ Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H), ff_Sph ε σ Ψ → ff_Compr ε E Ψ → ff_DSSum ε Ψ →
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (π' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), ffg_IsSq ε π' → ∀ (x y : H) (a b : H'),
      ∫ g, ⟪x, Ψ (umat g) y⟫_ℂ * star (coefOn π' a b g) ∂(Formalism.REAL.muG ε) ≠ 0 →
      ∃ S : Submodule ℂ H', IsKTypeOf ε π' (Formalism.QuantumDeterminants.lowK ε lam) S

section SlopeTestRemainingChoices

variable {n : ℕ} {ε : Fin n → Bool}

/- English proof (translation)
Take `⟨U, hU⟩` from `h`. Use `⟨U.symm, fun g hg v => ?_⟩` and prove the remaining obligations. Apply `U.injective` to reduce the goal to its premises. Rewrite using `[U.apply_symm_apply, hU g hg, U.apply_symm_apply]`.
-/
theorem ffg_equiv_symm {H' H : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h : ffg_Equiv ε σ' σ) : ffg_Equiv ε σ σ' := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U.symm, fun g hg v => ?_⟩
  apply U.injective
  rw [U.apply_symm_apply, hU g hg, U.apply_symm_apply]

/- English proof (translation)
Establish `hu : Continuous (fun g : Formalism.REAL.UJ ε => umat g)` using `Units.continuous_val.comp continuous_subtype_val`. Establish `hm : ∀ g : Formalism.REAL.UJ ε, umat g ∈ UJset ε` using `fun g => g.2`. Conclude with `continuous_const.inner ((hσ.2.2 v).comp_continuous hu hm)`.
-/
theorem ffg_coef_cont {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (v w : H) :
    Continuous (coefOn (ε := ε) σ v w) := by
  have hu : Continuous (fun g : Formalism.REAL.UJ ε => umat g) :=
    Units.continuous_val.comp continuous_subtype_val
  have hm : ∀ g : Formalism.REAL.UJ ε, umat g ∈ UJset ε := fun g => g.2
  exact continuous_const.inner ((hσ.2.2 v).comp_continuous hu hm)

/- English proof (translation)
Use `first`. Consider the case `exact hu.integrable_mul hv.star`. Consider the case `exact MemLp.integrable_mul hu hv.star`. Consider the case `exact hu.integrable_mul hv.star (by norm_num)`.
-/
theorem ffg_int_mul {u v : Formalism.REAL.UJ ε → ℂ} (hu : MemLp u 2 (Formalism.REAL.muG ε)) (hv : MemLp v 2 (Formalism.REAL.muG ε)) :
    Integrable (fun g => u g * star (v g)) (Formalism.REAL.muG ε) := by
  first
  | exact hu.integrable_mul hv.star
  | exact MemLp.integrable_mul hu hv.star
  | exact hu.integrable_mul hv.star (by norm_num)

def ffg_CoefOf {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (φ : Formalism.REAL.UJ ε → ℂ) : Prop :=
  ∃ v w : H, φ = coefOn σ v w

def ffg_Other {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (φ : Formalism.REAL.UJ ε → ℂ) : Prop :=
  ∃ (H' : Type) (_ : NormedAddCommGroup H') (_ : InnerProductSpace ℂ H') (_ : CompleteSpace H')
    (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (v w : H'),
    ffg_IsSq ε σ' ∧ ¬ ffg_Equiv ε σ' σ ∧ φ = coefOn σ' v w

/- English proof (translation)
Take `⟨H', i1, i2, i3, σ', v, w, hnt, hU, hI, hS, rfl⟩` from `hφ`. Distinguish the cases in `he : ffg_Equiv ε σ' σ`. Use `left`. Take `⟨U, hU'⟩` from `he`. Use `⟨U v, U w, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `g`. Simplify using `only [coefOn]`. Rewrite using `[← hU' (umat g) g.2 v, LinearIsometryEquiv.inner_map_map]`. Use `right`. Conclude with `⟨H', i1, i2, i3, σ', v, w, ⟨hnt, hU, hI, hS⟩, he, rfl⟩`.
-/
theorem ffg_split {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {φ : Formalism.REAL.UJ ε → ℂ} (hφ : IsDSCoef ε φ) :
    ffg_CoefOf ε σ φ ∨ ffg_Other ε σ φ := by
  obtain ⟨H', i1, i2, i3, σ', v, w, hnt, hU, hI, hS, rfl⟩ := hφ
  by_cases he : ffg_Equiv ε σ' σ
  · left
    obtain ⟨U, hU'⟩ := he
    refine ⟨U v, U w, ?_⟩
    funext g
    simp only [coefOn]
    rw [← hU' (umat g) g.2 v, LinearIsometryEquiv.inner_map_map]
  · right
    exact ⟨H', i1, i2, i3, σ', v, w, ⟨hnt, hU, hI, hS⟩, he, rfl⟩

/- English proof (translation)
Take `⟨H', i1, i2, i3, σ', v, w, hnt, hU, hI, hS, rfl⟩` from `hφ`. Conclude with `hS v w`.
-/
theorem ffg_ds_memLp {φ : Formalism.REAL.UJ ε → ℂ} (hφ : IsDSCoef ε φ) : MemLp φ 2 (Formalism.REAL.muG ε) := by
  obtain ⟨H', i1, i2, i3, σ', v, w, hnt, hU, hI, hS, rfl⟩ := hφ
  exact hS v w

/- English proof (translation)
Take `⟨H', i1, i2, i3, σ', v, w, hnt, hU, hI, hS, rfl⟩` from `hφ`. Conclude with `ffg_coef_cont hU v w`.
-/
theorem ffg_ds_cont {φ : Formalism.REAL.UJ ε → ℂ} (hφ : IsDSCoef ε φ) : Continuous φ := by
  obtain ⟨H', i1, i2, i3, σ', v, w, hnt, hU, hI, hS, rfl⟩ := hφ
  exact ffg_coef_cont hU v w

/- English proof (translation)
Establish `heq : ∀ g, h g * star (h g) = ((‖h g‖ ^ 2 : ℝ) : ℂ)` using `fun g => by`. Rewrite using `[show star (h g) = (starRingEnd ℂ) (h g) from rfl, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Establish `hint : Integrable (fun g => h g * star (h g)) (Formalism.REAL.muG ε)` using `ffg_int_mul h2 h2`. Establish `hint' : Integrable (fun g => ‖h g‖ ^ 2) (Formalism.REAL.muG ε)`. Use `hint.norm.congr (ae_of_all _ fun g => ?_)` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[heq g, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]`. Establish `hre : ∫ g, ‖h g‖ ^ 2 ∂(Formalism.REAL.muG ε) = 0`. Rewrite `h0` using `[heq]`. Rewrite `h0` using `[integral_complex_ofReal]`.

Conclude with `h0` after adjusting the coercions. Establish `hnn : 0 ≤ᵐ[Formalism.REAL.muG ε] fun g => ‖h g‖ ^ 2` using `ae_of_all _ fun g => by positivity`. Establish `hae` using `(integral_eq_zero_iff_of_nonneg_ae hnn hint').1 hre`. Use `haveI : (Formalism.REAL.muG ε).IsOpenPosMeasure := by first`. Consider the case `infer_instance`.

Consider the case `(unfold Formalism.REAL.muG; infer_instance)`. Establish `hz : (fun g => ‖h g‖ ^ 2) = 0` using `((hc.norm.pow 2).ae_eq_iff_eq (Formalism.REAL.muG ε) continuous_zero).1 hae`. Use function extensionality and compare the values at `g`. Use `congrFun hz g` as an intermediate fact. Simplify using `using this`.
-/
theorem ffg_zero_of_int {h : Formalism.REAL.UJ ε → ℂ} (hc : Continuous h) (h2 : MemLp h 2 (Formalism.REAL.muG ε))
    (h0 : ∫ g, h g * star (h g) ∂(Formalism.REAL.muG ε) = 0) : h = 0 := by
  have heq : ∀ g, h g * star (h g) = ((‖h g‖ ^ 2 : ℝ) : ℂ) := fun g => by
    rw [show star (h g) = (starRingEnd ℂ) (h g) from rfl, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hint : Integrable (fun g => h g * star (h g)) (Formalism.REAL.muG ε) := ffg_int_mul h2 h2
  have hint' : Integrable (fun g => ‖h g‖ ^ 2) (Formalism.REAL.muG ε) := by
    refine hint.norm.congr (ae_of_all _ fun g => ?_)
    simp only
    rw [heq g, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hre : ∫ g, ‖h g‖ ^ 2 ∂(Formalism.REAL.muG ε) = 0 := by
    simp_rw [heq] at h0
    rw [integral_complex_ofReal] at h0
    exact_mod_cast h0
  have hnn : 0 ≤ᵐ[Formalism.REAL.muG ε] fun g => ‖h g‖ ^ 2 := ae_of_all _ fun g => by positivity
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hint').1 hre
  haveI : (Formalism.REAL.muG ε).IsOpenPosMeasure := by
    first
    | infer_instance
    | (unfold Formalism.REAL.muG; infer_instance)
  have hz : (fun g => ‖h g‖ ^ 2) = 0 :=
    ((hc.norm.pow 2).ae_eq_iff_eq (Formalism.REAL.muG ε) continuous_zero).1 hae
  funext g
  have := congrFun hz g
  simpa using this

end SlopeTestRemainingChoices

/- English proof (translation)
Take `⟨U, hU⟩` from `h₁`. Take `⟨V, hV⟩` from `h₂`. Use `⟨U.trans V, fun g hg v => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply, hU g hg, hV g hg]`.
-/
private theorem ffg_Equiv_trans {n : ℕ} {ε : Fin n → Bool} {H₁ H₂ H₃ : Type}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)}
    {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)} {σ₃ : Matrix (Fin n) (Fin n) ℂ → (H₃ →L[ℂ] H₃)}
    (h₁ : ffg_Equiv ε σ₁ σ₂) (h₂ : ffg_Equiv ε σ₂ σ₃) : ffg_Equiv ε σ₁ σ₃ := by
  obtain ⟨U, hU⟩ := h₁
  obtain ⟨V, hV⟩ := h₂
  refine ⟨U.trans V, fun g hg v => ?_⟩
  rw [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply, hU g hg, hV g hg]

/- English proof (translation)
Introduce `n ε lam H _ _ _ σ E hHC hDS hE Ψ hSph hCompr hEig hDSS x y`. Take `⟨N, φ, hφ, hψ⟩` from `hDSS x y`. Establish `hL2 : ∀ i, MemLp (φ i) 2 (Formalism.REAL.muG ε)` using `fun i => ffg_ds_memLp (hφ i)`. Establish `hC : ∀ i, Continuous (φ i)` using `fun i => ffg_ds_cont (hφ i)`. Establish `hψf : (fun g => ⟪x, Ψ (umat g) y⟫_ℂ) = fun g => ∑ i, φ i g` using `funext hψ`.

Establish `hψL2 : MemLp (fun g => ⟪x, Ψ (umat g) y⟫_ℂ) 2 (Formalism.REAL.muG ε)`. Rewrite using `[hψf]`. Conclude with `memLp_finset_sum _ fun i _ => hL2 i`. Establish `F2 : ∀ j, ffg_Other ε σ (φ j) → ∫ g, ⟪x, Ψ (umat g) y⟫_ℂ * star (φ j g) ∂(Formalism.REAL.muG ε) = 0`. Introduce `j hO`.

Take `⟨H', iA, iB, iC, σ', a, b, hsq, hne, hj⟩` from `hO`. Rewrite using `[hj]`. Assume the negation of the conclusion as `h0`. Apply `hne` to reduce the goal to its premises. Establish `hsq'` using `hsq`.

Take `⟨hnt, hU, hI, hS⟩` from `hsq'`. Conclude with `q2 n ε lam hHC H σ hDS H' σ' hnt hU hI hS (q3 n ε lam H σ E hHC hDS hE Ψ hSph hCompr hEig hDSS H' σ' hsq x y a b h0) (q4 n ε lam H σ E hHC hDS hE Ψ hSph hCompr hDSS H' σ' hsq x y a b h0)`. Establish `F3 : ∀ i, ¬ ffg_Other ε σ (φ i) → ∀ j, ffg_Other ε σ (φ j) → ∫ g, φ i g * star (φ j g) ∂(Formalism.REAL.muG ε) = 0`. Introduce `i hA j hO`. Take `⟨Hj, jA, jB, jC, σj, a, b, hsqj, hnej, hj⟩` from `hO`.

Take `⟨Hi, kA, kB, kC, σi, c, d, hnt, hU, hI, hS, hi⟩` from `hφ i`. Establish `hEq : ffg_Equiv ε σi σ`. Assume the negation of the conclusion as `hne`. Conclude with `hA ⟨Hi, kA, kB, kC, σi, c, d, ⟨hnt, hU, hI, hS⟩, hne, hi⟩`. Establish `hne' : ¬ ffg_Equiv ε σi σj` using `fun h' => hnej (ffg_Equiv_trans (ffg_equiv_symm h') hEq)`.

Rewrite using `[hi, hj]`. Conclude with `(q1 n ε).2 Hi σi Hj σj ⟨hnt, hU, hI, hS⟩ hsqj hne' c d a b`. Take `⟨s, hs⟩ : ∃ s : Finset (Fin N), s = Finset.univ.filter (fun j => ffg_Other ε σ (φ j))` from `⟨_, rfl⟩`. Take `⟨t, ht⟩ : ∃ t : Finset (Fin N), t = Finset.univ.filter (fun j => ¬ ffg_Other ε σ (φ j))` from `⟨_, rfl⟩`. Establish `hsplit : ∀ g, ⟪x, Ψ (umat g) y⟫_ℂ = ∑ i ∈ t, φ i g + ∑ j ∈ s, φ j g` using `fun g => by`.

Rewrite using `[hψ g, hs, ht, add_comm]`. Conclude with `(Finset.sum_filter_add_sum_filter_not _ _ _).symm`. Take `⟨h, hh⟩ : ∃ h : Formalism.REAL.UJ ε → ℂ, h = fun g => ∑ j ∈ s, φ j g` from `⟨_, rfl⟩`. Establish `hh' : ∀ g, h g = ∑ j ∈ s, φ j g` using `fun g => by simp only [hh]`. Establish `hhL2 : MemLp h 2 (Formalism.REAL.muG ε)` using `by rw [hh]; exact memLp_finset_sum _ fun j _ => hL2 j`.

Establish `hhC : Continuous h` using `by rw [hh]; exact continuous_finset_sum _ fun j _ => hC j`. Establish `key : ∀ j ∈ s, ∫ g, h g * star (φ j g) ∂(Formalism.REAL.muG ε) = 0`. Introduce `j hj`. Establish `hOj : ffg_Other ε σ (φ j)` using `by rw [hs] at hj; exact (Finset.mem_filter.1 hj).2`. Establish `e1 : ∀ g, h g * star (φ j g) = ⟪x, Ψ (umat g) y⟫_ℂ * star (φ j g) - ∑ i ∈ t, φ i g * star (φ j g)` using `fun g => by`.

Rewrite using `[hh' g, hsplit g, ← Finset.sum_mul]`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[e1]`. Establish `I1 : Integrable (fun g => ⟪x, Ψ (umat g) y⟫_ℂ * star (φ j g)) (Formalism.REAL.muG ε)` using `ffg_int_mul hψL2 (hL2 j)`. Establish `I2 : ∀ i ∈ t, Integrable (fun g => φ i g * star (φ j g)) (Formalism.REAL.muG ε)` using `fun i _ => ffg_int_mul (hL2 i) (hL2 j)`.

Rewrite using `[integral_sub I1 (integrable_finset_sum t I2), integral_finset_sum t I2, F2 j hOj, Finset.sum_eq_zero fun i hi => F3 i (by rw [ht] at hi; exact (Finset.mem_filter.1 hi).2) j hOj, sub_zero]`. Establish `hzero : ∫ g, h g * star (h g) ∂(Formalism.REAL.muG ε) = 0`. Establish `e2 : ∀ g, h g * star (h g) = ∑ j ∈ s, h g * star (φ j g)` using `fun g => by`. Rewrite using `[← Finset.mul_sum, ← star_sum, ← hh' g]`. Repeatedly rewrite using `[e2]`.

Rewrite using `[integral_finset_sum _ fun j _ => ffg_int_mul hhL2 (hL2 j)]`. Conclude with `Finset.sum_eq_zero key`. Establish `h0 : h = 0` using `ffg_zero_of_int hhC hhL2 hzero`. Establish `hpt : ∀ g, ⟪x, Ψ (umat g) y⟫_ℂ = ∑ i ∈ t, φ i g` using `fun g => by`. Establish `h1 : ∑ j ∈ s, φ j g = 0` using `by rw [← hh' g, h0, Pi.zero_apply]`.

Rewrite using `[hsplit g, h1, add_zero]`. Establish `F1 : ∀ i, ¬ ffg_Other ε σ (φ i) → ∃ v w : H, φ i = coefOn σ v w` using `fun i hA => (ffg_split σ (hφ i)).resolve_right hA`. Use `⟨N, fun i => if hA : ¬ ffg_Other ε σ (φ i) then (F1 i hA).choose else 0, fun i => if hA : ¬ ffg_Other ε σ (φ i) then (F1 i hA).choose_spec.choose else 0, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[hpt g, ht, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hA : ¬ ffg_Other ε σ (φ i)`. Simplify using `only [if_pos hA, dif_pos hA]`. Conclude with `congrFun (F1 i hA).choose_spec.choose_spec g`. Simplify using `[if_neg hA, dif_neg hA, coefOn]`.
-/
theorem ff_ident_of (χ : ∀ n : ℕ, (Fin n → ℝ) → ℕ → ℂ) (q1 : QOrth) (q2 : QClass χ) (q3 : FCharOther χ)
    (q4 : FKTypeOther) : FIdent χ := by
  intro n ε lam H _ _ _ σ E hHC hDS hE Ψ hSph hCompr hEig hDSS x y
  classical
  obtain ⟨N, φ, hφ, hψ⟩ := hDSS x y
  have hL2 : ∀ i, MemLp (φ i) 2 (Formalism.REAL.muG ε) := fun i => ffg_ds_memLp (hφ i)
  have hC : ∀ i, Continuous (φ i) := fun i => ffg_ds_cont (hφ i)
  have hψf : (fun g => ⟪x, Ψ (umat g) y⟫_ℂ) = fun g => ∑ i, φ i g := funext hψ
  have hψL2 : MemLp (fun g => ⟪x, Ψ (umat g) y⟫_ℂ) 2 (Formalism.REAL.muG ε) := by
    rw [hψf]; exact memLp_finset_sum _ fun i _ => hL2 i
  have F2 : ∀ j, ffg_Other ε σ (φ j) →
      ∫ g, ⟪x, Ψ (umat g) y⟫_ℂ * star (φ j g) ∂(Formalism.REAL.muG ε) = 0 := by
    intro j hO
    obtain ⟨H', iA, iB, iC, σ', a, b, hsq, hne, hj⟩ := hO
    rw [hj]
    by_contra h0
    apply hne
    have hsq' := hsq
    obtain ⟨hnt, hU, hI, hS⟩ := hsq'
    exact q2 n ε lam hHC H σ hDS H' σ' hnt hU hI hS
      (q3 n ε lam H σ E hHC hDS hE Ψ hSph hCompr hEig hDSS H' σ' hsq x y a b h0)
      (q4 n ε lam H σ E hHC hDS hE Ψ hSph hCompr hDSS H' σ' hsq x y a b h0)
  have F3 : ∀ i, ¬ ffg_Other ε σ (φ i) → ∀ j, ffg_Other ε σ (φ j) →
      ∫ g, φ i g * star (φ j g) ∂(Formalism.REAL.muG ε) = 0 := by
    intro i hA j hO
    obtain ⟨Hj, jA, jB, jC, σj, a, b, hsqj, hnej, hj⟩ := hO
    obtain ⟨Hi, kA, kB, kC, σi, c, d, hnt, hU, hI, hS, hi⟩ := hφ i
    have hEq : ffg_Equiv ε σi σ := by
      by_contra hne
      exact hA ⟨Hi, kA, kB, kC, σi, c, d, ⟨hnt, hU, hI, hS⟩, hne, hi⟩
    have hne' : ¬ ffg_Equiv ε σi σj := fun h' => hnej (ffg_Equiv_trans (ffg_equiv_symm h') hEq)
    rw [hi, hj]
    exact (q1 n ε).2 Hi σi Hj σj ⟨hnt, hU, hI, hS⟩ hsqj hne' c d a b
  obtain ⟨s, hs⟩ : ∃ s : Finset (Fin N), s = Finset.univ.filter (fun j => ffg_Other ε σ (φ j)) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : Finset (Fin N), t = Finset.univ.filter (fun j => ¬ ffg_Other ε σ (φ j)) := ⟨_, rfl⟩
  have hsplit : ∀ g, ⟪x, Ψ (umat g) y⟫_ℂ = ∑ i ∈ t, φ i g + ∑ j ∈ s, φ j g := fun g => by
    rw [hψ g, hs, ht, add_comm]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  obtain ⟨h, hh⟩ : ∃ h : Formalism.REAL.UJ ε → ℂ, h = fun g => ∑ j ∈ s, φ j g := ⟨_, rfl⟩
  have hh' : ∀ g, h g = ∑ j ∈ s, φ j g := fun g => by simp only [hh]
  have hhL2 : MemLp h 2 (Formalism.REAL.muG ε) := by rw [hh]; exact memLp_finset_sum _ fun j _ => hL2 j
  have hhC : Continuous h := by rw [hh]; exact continuous_finset_sum _ fun j _ => hC j
  have key : ∀ j ∈ s, ∫ g, h g * star (φ j g) ∂(Formalism.REAL.muG ε) = 0 := by
    intro j hj
    have hOj : ffg_Other ε σ (φ j) := by rw [hs] at hj; exact (Finset.mem_filter.1 hj).2
    have e1 : ∀ g, h g * star (φ j g) =
        ⟪x, Ψ (umat g) y⟫_ℂ * star (φ j g) - ∑ i ∈ t, φ i g * star (φ j g) := fun g => by
      rw [hh' g, hsplit g, ← Finset.sum_mul]; ring
    simp_rw [e1]
    have I1 : Integrable (fun g => ⟪x, Ψ (umat g) y⟫_ℂ * star (φ j g)) (Formalism.REAL.muG ε) :=
      ffg_int_mul hψL2 (hL2 j)
    have I2 : ∀ i ∈ t, Integrable (fun g => φ i g * star (φ j g)) (Formalism.REAL.muG ε) :=
      fun i _ => ffg_int_mul (hL2 i) (hL2 j)
    rw [integral_sub I1 (integrable_finset_sum t I2), integral_finset_sum t I2, F2 j hOj,
      Finset.sum_eq_zero fun i hi => F3 i (by rw [ht] at hi; exact (Finset.mem_filter.1 hi).2) j hOj, sub_zero]
  have hzero : ∫ g, h g * star (h g) ∂(Formalism.REAL.muG ε) = 0 := by
    have e2 : ∀ g, h g * star (h g) = ∑ j ∈ s, h g * star (φ j g) := fun g => by
      rw [← Finset.mul_sum, ← star_sum, ← hh' g]
    simp_rw [e2]
    rw [integral_finset_sum _ fun j _ => ffg_int_mul hhL2 (hL2 j)]
    exact Finset.sum_eq_zero key
  have h0 : h = 0 := ffg_zero_of_int hhC hhL2 hzero
  have hpt : ∀ g, ⟪x, Ψ (umat g) y⟫_ℂ = ∑ i ∈ t, φ i g := fun g => by
    have h1 : ∑ j ∈ s, φ j g = 0 := by rw [← hh' g, h0, Pi.zero_apply]
    rw [hsplit g, h1, add_zero]
  have F1 : ∀ i, ¬ ffg_Other ε σ (φ i) → ∃ v w : H, φ i = coefOn σ v w := fun i hA =>
    (ffg_split σ (hφ i)).resolve_right hA
  refine ⟨N, fun i => if hA : ¬ ffg_Other ε σ (φ i) then (F1 i hA).choose else 0,
    fun i => if hA : ¬ ffg_Other ε σ (φ i) then (F1 i hA).choose_spec.choose else 0, fun g => ?_⟩
  rw [hpt g, ht, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hA : ¬ ffg_Other ε σ (φ i)
  · simp only [if_pos hA, dif_pos hA]
    exact congrFun (F1 i hA).choose_spec.choose_spec g
  · simp [if_neg hA, dif_neg hA, coefOn]

end Formalism.MainNotions.LeviCoordinates

end

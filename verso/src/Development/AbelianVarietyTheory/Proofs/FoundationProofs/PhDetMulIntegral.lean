import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPosHermFormV
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralGaussianUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergReproducingKernelSumSpecStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryFiniteGaussSumPhaseRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralUnfoldFundamentalDomainStatement
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

noncomputable section

namespace GlobalTheory.UnitaryTheta.Graph

section Alg

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def term (H : Sesq V) (a : V ≃ₗ[ℂ] V) (α : V → ℂ) (x z : V) : ℂ :=
  α x * kerTerm H x (a z) z * cexp (-(π : ℂ) * H z z)

/- English proof (translation)
Establish `h1 : H z (a.symm x) = H (a z) x` using `by rw [← ha, LinearEquiv.apply_symm_apply]`. Rewrite using `[term, kerTerm, hy, mul_assoc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]`. Use `congr 2`. Simplify using `only [map_add, map_sub, map_neg, LinearMap.add_apply, LinearMap.sub_apply, h1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem term_eq (H : Sesq V) (a : V ≃ₗ[ℂ] V) (ha : ∀ z w, H (a z) (a w) = H z w) (α : V → ℂ) (x y z : V)
    (hy : y - a y = x) :
    term H a α x z = α x * cexp (-(π : ℂ) * H x x / 2) *
      cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z (-(a.symm x))) := by
  have h1 : H z (a.symm x) = H (a z) x := by rw [← ha, LinearEquiv.apply_symm_apply]
  rw [term, kerTerm, hy, mul_assoc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  simp only [map_add, map_sub, map_neg, LinearMap.add_apply, LinearMap.sub_apply, h1]
  ring

/- English proof (translation)
Establish `h1 : H y (a.symm x) = H y x - H x x`. Rewrite using `[← ha, LinearEquiv.apply_symm_apply]`. Establish `: a y = y - x` using `by rw [← hy]; abel`. Rewrite using `[this]`. Simplify using the standard rewrite rules.

Establish `h2 : H x x = H y x + conj (H y x)`. Rewrite using `[← hH.1, ← hy]`. Simplify using `only [map_sub, LinearMap.sub_apply, ha]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← Complex.exp_add]`.

Use `congr 1`. Rewrite using `[map_neg, h1, h2, Complex.im_eq_sub_conj]`. Use `Complex.I_ne_zero` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem value_eq (H : Sesq V) (hH : IsPosHerm H) (a : V ≃ₗ[ℂ] V) (ha : ∀ z w, H (a z) (a w) = H z w) (x y : V)
    (hy : y - a y = x) :
    cexp (-(π : ℂ) * H x x / 2) * cexp (π * H y (-(a.symm x))) =
      cexp (-((π : ℂ) * I) * ((H y x).im : ℂ)) := by
  have h1 : H y (a.symm x) = H y x - H x x := by
    rw [← ha, LinearEquiv.apply_symm_apply]
    have : a y = y - x := by rw [← hy]; abel
    rw [this]; simp
  have h2 : H x x = H y x + conj (H y x) := by
    rw [← hH.1, ← hy]
    simp only [map_sub, LinearMap.sub_apply, ha]
    ring
  rw [← Complex.exp_add]
  congr 1
  rw [map_neg, h1, h2, Complex.im_eq_sub_conj]
  have := Complex.I_ne_zero
  field_simp
  ring

/- English proof (translation)
Establish `hx' : x - (y - a y) ∈ Λ` using `Λ.sub_mem hx (Λ.sub_mem hy hay)`. Establish `e1` using `hα.2.2 _ hx' _ hy`. Establish `e2` using `hα.2.2 _ hx _ hay`. Establish `e0 : x - (y - a y) + y = x + a y` using `by abel`. Rewrite `e1` using `[e0, e2, hαy]`.

Apply the tactic sequence `have hne : α y ≠ 0 := by rcases hα.1 y hy with h | h <;> simp [h]`. Establish `e3 : α (x - (y - a y)) = α x * cexp (-((π : ℂ) * I) * ((H x (a y)).im : ℂ) + ((π : ℂ) * I) * ((H (x - (y - a y)) y).im : ℂ))`. Establish `h` using `Complex.exp_ne_zero (-((π : ℂ) * I) * ((H (x - (y - a y)) y).im : ℂ))`. Apply `mul_right_cancel₀ h` to reduce the goal to its premises. Apply `mul_right_cancel₀ hne` to reduce the goal to its premises.

Rewrite using `[mul_assoc (α x), ← Complex.exp_add]`. Establish `: -((π : ℂ) * I) * ((H x (a y)).im : ℂ) + ((π : ℂ) * I) * ((H (x - (y - a y)) y).im : ℂ) + -((π : ℂ) * I) * ((H (x - (y - a y)) y).im : ℂ) = -((π : ℂ) * I) * ((H x (a y)).im : ℂ)` using `by ring`. Rewrite using `[this]`. Take the linear combination `-e1`. Take `⟨m, hm⟩` from `hα.2.1 x hx _ hay`.

Establish `hm' : ((H x (a y)).im : ℂ) = m` using `by exact_mod_cast hm`. Rewrite using `[term, term, e3, kerTerm, kerTerm]`. Simplify using `only [mul_assoc, ← Complex.exp_add]`. Use `congr 1`. Rewrite using `[Complex.exp_eq_exp_iff_exists_int]`.

Use `⟨-m, ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[← hm']`. Simplify using `only [Complex.im_eq_sub_conj, ← hH.1]`. Simplify using `only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, ha]`.

Use `Complex.I_ne_zero` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem term_shift (H : Sesq V) (hH : IsPosHerm H) (a : V ≃ₗ[ℂ] V) (ha : ∀ z w, H (a z) (a w) = H z w)
    (Λ : AddSubgroup V) (α : V → ℂ) (hα : IsSemichar H Λ α) (x y z : V) (hx : x ∈ Λ) (hy : y ∈ Λ)
    (hay : a y ∈ Λ) (hαy : α (a y) = α y) :
    term H a α (x - (y - a y)) z = term H a α x (z + y) := by
  have hx' : x - (y - a y) ∈ Λ := Λ.sub_mem hx (Λ.sub_mem hy hay)
  have e1 := hα.2.2 _ hx' _ hy
  have e2 := hα.2.2 _ hx _ hay
  have e0 : x - (y - a y) + y = x + a y := by abel
  rw [e0, e2, hαy] at e1
  have hne : α y ≠ 0 := by rcases hα.1 y hy with h | h <;> simp [h]
  have e3 : α (x - (y - a y)) = α x * cexp (-((π : ℂ) * I) * ((H x (a y)).im : ℂ)
      + ((π : ℂ) * I) * ((H (x - (y - a y)) y).im : ℂ)) := by
    have h := Complex.exp_ne_zero (-((π : ℂ) * I) * ((H (x - (y - a y)) y).im : ℂ))
    apply mul_right_cancel₀ h
    apply mul_right_cancel₀ hne
    rw [mul_assoc (α x), ← Complex.exp_add]
    have : -((π : ℂ) * I) * ((H x (a y)).im : ℂ)
      + ((π : ℂ) * I) * ((H (x - (y - a y)) y).im : ℂ) + -((π : ℂ) * I) * ((H (x - (y - a y)) y).im : ℂ) =
        -((π : ℂ) * I) * ((H x (a y)).im : ℂ) := by ring
    rw [this]
    linear_combination -e1
  obtain ⟨m, hm⟩ := hα.2.1 x hx _ hay
  have hm' : ((H x (a y)).im : ℂ) = m := by exact_mod_cast hm
  rw [term, term, e3, kerTerm, kerTerm]
  simp only [mul_assoc, ← Complex.exp_add]
  congr 1
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-m, ?_⟩
  push_cast
  rw [← hm']
  simp only [Complex.im_eq_sub_conj, ← hH.1]
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, ha]
  have := Complex.I_ne_zero
  field_simp
  ring

end Alg

/- English proof (translation)
Assemble the required witnesses or components as `⟨2, two_pos, by rw [Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]⟩`.
-/
theorem ph_real (κ : ℝ) : GlobalTheory.Phase.Ph (κ : ℂ) :=
  ⟨2, two_pos, by rw [Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]⟩

/- English proof (translation)
Introduce `V _ _ _ _ _ μ _ H hH a ha hdet Λ Λ' _ hfg hle hfi haΛ α hα hαa Fd hFd`. Use `haveI : ProperSpace V := FiniteDimensional.proper ℂ V`. Use `haveI : Countable Λ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance`. Use `haveI : Countable Λ' := (AddSubgroup.inclusion_injective hle).countable`. Take `⟨κ, -, hg⟩` from `GlobalTheory.T.integral_cexp_herm_gaussian_eq_div_det V μ H hH a ha hdet`.

Set `E` to `LinearMap.equivOfDetNeZero _ hdet`. Establish `hE : ∀ x, E x = x - a x` using `fun x => rfl`. Set `B : V →ₗ[ℂ] V` to `E.symm`. Establish `hB1 : ∀ x, B x - a (B x) = x` using `fun x => by rw [← hE]; exact E.apply_symm_apply x`. Establish `hB2 : ∀ x, B (x - a x) = x` using `fun x => by rw [← hE]; exact E.symm_apply_apply x`.

Take `⟨M, _, s, hs, huniq, hph⟩` from `GlobalTheory.T.unitary_finite_gaussSum_phase_rootOfUnity V H hH a ha B hB1 hB2 Λ Λ' hfg hle hfi haΛ α hα hαa`. Establish `hint : ∀ x, Integrable (term H a α x) μ` using `fun x => by`. Establish `: term H a α x = _` using `funext fun z => term_eq H a ha α x (B x) z (hB1 x)`. Rewrite using `[this]`. Conclude with `(hg (B x) _).1.const_mul _`.

Establish `hval : ∀ x, ∫ z, term H a α x z ∂μ = κ / LinearMap.det (1 - (a : V →ₗ[ℂ] V)) * (α x * cexp (-((π : ℂ) * I) * ((H (B x) x).im : ℂ)))` using `fun x => by`. Simplify using `only [fun z => term_eq H a ha α x (B x) z (hB1 x)]`. Rewrite using `[integral_const_mul, (hg (B x) _).2, ← value_eq H hH a ha x (B x) (hB1 x)]`. Expand and normalize the polynomial expressions, which then agree. Set `f : M × Λ' → Λ` to `fun p => ⟨s p.1 - ((p.2 : V) - a p.2), Λ.sub_mem (hs _) (Λ.sub_mem (hle p.2.2) (haΛ _ p.2.2))⟩`.

Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion. Introduce `p q hpq`. Conclude with `(huniq _ (f p).2).unique rfl (congrArg Subtype.val hpq)`. Introduce `x`.

Take `⟨p, hp, -⟩` from `huniq x x.2`. Conclude with `⟨p, Subtype.ext hp.symm⟩`. Establish `hsum : ∀ z, kerSum H Λ α z (a z) * cexp (-(π : ℂ) * H z z) = ∑ m, ∑' y : Λ', term H a α (s m) (z + y)` using `fun z => by`. Establish `h1 : Summable (fun x : Λ => term H a α x z)` using `((GlobalTheory.T.heisenbergReproducingKernelSum_spec V H hH Λ α hα).1 (a z) z).mul_right _`. Establish `h2` using `(Equiv.ofBijective f hf).summable_iff.2 h1`.

Rewrite using `[kerSum, ← tsum_mul_right]`. Express the relevant statement in the definitionally equal form `∑' x : Λ, term H a α x z = _`. Rewrite using `[← (Equiv.ofBijective f hf).tsum_eq]`. Use `(h2.tsum_prod).trans ?_` and prove the remaining obligations. Rewrite using `[tsum_fintype]`.

Use `Finset.sum_congr rfl fun m _ => tsum_congr fun y => ?_` and prove the remaining obligations. Conclude with `term_shift H hH a ha Λ α hα (s m) y z (hs m) (hle y.2) (haΛ _ y.2) (hαa _ y.2)`. Establish `hu` using `fun m => GlobalTheory.T.setIntegral_tsum_translate_eq_integral V μ Λ' Fd hFd _ (hint (s m))`. Simplify using `only [hsum]`. Rewrite using `[integral_finset_sum _ (fun m _ => (hu m).1)]`.

Simplify using `only [fun m => (hu m).2, hval]`. Rewrite using `[← Finset.mul_sum, ← mul_assoc, mul_div_cancel₀ _ hdet]`. Conclude with `(ph_real κ).mul hph`.
-/
theorem ph_det_mul_integral : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ (a : V ≃ₗ[ℂ] V), (∀ z w, H (a z) (a w) = H z w) → LinearMap.det (1 - (a : V →ₗ[ℂ] V)) ≠ 0 → ∀ (Λ Λ' : AddSubgroup V) [DiscreteTopology Λ], Λ.FG → Λ' ≤ Λ → (Λ'.addSubgroupOf Λ).FiniteIndex → (∀ y ∈ Λ', a y ∈ Λ) → ∀ α : V → ℂ, IsSemichar H Λ α → (∀ y ∈ Λ', α (a y) = α y) → ∀ Fd : Set V, IsAddFundamentalDomain Λ' Fd μ → GlobalTheory.Phase.Ph (LinearMap.det (1 - (a : V →ₗ[ℂ] V)) * ∫ z in Fd, kerSum H Λ α z (a z) * cexp (-(π : ℂ) * H z z) ∂μ) := by
  intro V _ _ _ _ _ μ _ H hH a ha hdet Λ Λ' _ hfg hle hfi haΛ α hα hαa Fd hFd
  haveI : ProperSpace V := FiniteDimensional.proper ℂ V
  haveI : Countable Λ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : Countable Λ' := (AddSubgroup.inclusion_injective hle).countable
  obtain ⟨κ, -, hg⟩ := GlobalTheory.T.integral_cexp_herm_gaussian_eq_div_det V μ H hH a ha hdet
  let E := LinearMap.equivOfDetNeZero _ hdet
  have hE : ∀ x, E x = x - a x := fun x => rfl
  let B : V →ₗ[ℂ] V := E.symm
  have hB1 : ∀ x, B x - a (B x) = x := fun x => by rw [← hE]; exact E.apply_symm_apply x
  have hB2 : ∀ x, B (x - a x) = x := fun x => by rw [← hE]; exact E.symm_apply_apply x
  obtain ⟨M, _, s, hs, huniq, hph⟩ := GlobalTheory.T.unitary_finite_gaussSum_phase_rootOfUnity V H hH a ha B hB1 hB2 Λ Λ' hfg hle hfi haΛ α hα hαa
  have hint : ∀ x, Integrable (term H a α x) μ := fun x => by
    have : term H a α x = _ := funext fun z => term_eq H a ha α x (B x) z (hB1 x)
    rw [this]
    exact (hg (B x) _).1.const_mul _
  have hval : ∀ x, ∫ z, term H a α x z ∂μ = κ / LinearMap.det (1 - (a : V →ₗ[ℂ] V)) *
      (α x * cexp (-((π : ℂ) * I) * ((H (B x) x).im : ℂ))) := fun x => by
    simp only [fun z => term_eq H a ha α x (B x) z (hB1 x)]
    rw [integral_const_mul, (hg (B x) _).2, ← value_eq H hH a ha x (B x) (hB1 x)]
    ring
  let f : M × Λ' → Λ := fun p => ⟨s p.1 - ((p.2 : V) - a p.2),
    Λ.sub_mem (hs _) (Λ.sub_mem (hle p.2.2) (haΛ _ p.2.2))⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p q hpq
      exact (huniq _ (f p).2).unique rfl (congrArg Subtype.val hpq)
    · intro x
      obtain ⟨p, hp, -⟩ := huniq x x.2
      exact ⟨p, Subtype.ext hp.symm⟩
  have hsum : ∀ z, kerSum H Λ α z (a z) * cexp (-(π : ℂ) * H z z) =
      ∑ m, ∑' y : Λ', term H a α (s m) (z + y) := fun z => by
    have h1 : Summable (fun x : Λ => term H a α x z) :=
      ((GlobalTheory.T.heisenbergReproducingKernelSum_spec V H hH Λ α hα).1 (a z) z).mul_right _
    have h2 := (Equiv.ofBijective f hf).summable_iff.2 h1
    rw [kerSum, ← tsum_mul_right]
    change ∑' x : Λ, term H a α x z = _
    rw [← (Equiv.ofBijective f hf).tsum_eq]
    refine (h2.tsum_prod).trans ?_
    rw [tsum_fintype]
    refine Finset.sum_congr rfl fun m _ => tsum_congr fun y => ?_
    exact term_shift H hH a ha Λ α hα (s m) y z (hs m) (hle y.2) (haΛ _ y.2) (hαa _ y.2)
  have hu := fun m => GlobalTheory.T.setIntegral_tsum_translate_eq_integral V μ Λ' Fd hFd _ (hint (s m))
  simp only [hsum]
  rw [integral_finset_sum _ (fun m _ => (hu m).1)]
  simp only [fun m => (hu m).2, hval]
  rw [← Finset.mul_sum, ← mul_assoc, mul_div_cancel₀ _ hdet]
  exact (ph_real κ).mul hph

end GlobalTheory.UnitaryTheta.Graph

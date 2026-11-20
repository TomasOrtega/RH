import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.HermitianMetricLogNormFormulaStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramDetNeZeroLocalBasisCofiniteStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChowlaSelbergPeriodStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogNormsExtDegreeAdelicStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.SumEmbeddingsBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionCmValueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionCmHeightStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionCmNumberFieldStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM

/- English proof (translation)
Establish `h` using `GlobalTheory.T.sum_embeddings_base_change M k ℂ f F`. Establish `hM : (Module.finrank ℚ M : ℝ) ≠ 0` using `Nat.cast_ne_zero.mpr Module.finrank_pos.ne'`. Establish `hk : (Module.finrank ℚ k : ℝ) ≠ 0` using `Nat.cast_ne_zero.mpr Module.finrank_pos.ne'`. Rewrite using `[div_eq_div_iff hk hM]`. Take the linear combination `h`.
-/
theorem flatDegree_mean_ext {M k : Type} [Field M] [NumberField M] [Field k] [NumberField k] (f : M →+* k)
    (F : (M →+* ℂ) → ℝ) :
    (∑ s : k →+* ℂ, F (s.comp f)) / Module.finrank ℚ k = (∑ s, F s) / Module.finrank ℚ M := by
  have h := GlobalTheory.T.sum_embeddings_base_change M k ℂ f F
  have hM : (Module.finrank ℚ M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hk : (Module.finrank ℚ k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  rw [div_eq_div_iff hk hM]
  linear_combination h

/- English proof (translation)
Set `c : E →+* E` to `RingHomClass.toRingHom (IsCMField.complexConj E)`. Set `σ : (E →+* A) ≃ (E →+* A)` to `{ toFun := fun j => j.comp c invFun := fun j => j.comp c left_inv := fun j => RingHom.ext fun x => congrArg j (IsCMField.complexConj_apply_apply E x) right_inv := fun j => RingHom.ext fun x => congrArg j (IsCMField.complexConj_apply_apply E x) }`. Conclude with `Equiv.sum_comp σ (fun j => F (j t))`.
-/
theorem flatDegree_sum_conj {E A : Type} [Field E] [NumberField E] [IsCMField E] [Field A] [CharZero A]
    (F : A → ℝ) (t : E) :
    ∑ j : E →+* A, F (j (IsCMField.complexConj E t)) = ∑ j : E →+* A, F (j t) := by
  let c : E →+* E := RingHomClass.toRingHom (IsCMField.complexConj E)
  let σ : (E →+* A) ≃ (E →+* A) :=
    { toFun := fun j => j.comp c
      invFun := fun j => j.comp c
      left_inv := fun j => RingHom.ext fun x => congrArg j (IsCMField.complexConj_apply_apply E x)
      right_inv := fun j => RingHom.ext fun x => congrArg j (IsCMField.complexConj_apply_apply E x) }
  exact Equiv.sum_comp σ (fun j => F (j t))

/- English proof (translation)
Establish `hrd : 0 < rootDiscr E`. Unfold `NumberField.rootDiscr`. Apply `Real.rpow_pos_of_pos` to reduce the goal to its premises. Conclude with `abs_pos.mpr (NumberField.discr_ne_zero E)` after adjusting the coercions. Establish `hd : 0 < √(d : ℝ)` using `Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d))`.

Establish `hL : deriv χ.LFunction 1 / χ.LFunction 1 = ((Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √d) : ℝ) : ℂ) - x`. Rewrite using `[hx]`. Expand and normalize the polynomial expressions, which then agree. Unfold `GlobalTheory.CM.logOm`. Rewrite using `[hL]`.

Simplify using `only [Complex.sub_re, Complex.ofReal_re]`. Rewrite using `[Real.log_div (by positivity) hrd.ne', Real.log_div (by positivity) hd.ne']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem flatDegree_logOm_re (E : Type) [Field E] [NumberField E] {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) {x : ℝ}
    (hx : (x : ℂ) = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √d) : ℝ) -
      deriv χ.LFunction 1 / χ.LFunction 1) :
    (logOm E χ).re = x - Real.log (rootDiscr E) + Real.log (Real.sqrt d) := by
  have hrd : 0 < rootDiscr E := by
    unfold NumberField.rootDiscr
    apply Real.rpow_pos_of_pos
    exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero E)
  have hd : 0 < √(d : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d))
  have hL : deriv χ.LFunction 1 / χ.LFunction 1 =
      ((Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √d) : ℝ) : ℂ) - x := by
    rw [hx]; ring
  unfold GlobalTheory.CM.logOm
  rw [hL]
  simp only [Complex.sub_re, Complex.ofReal_re]
  rw [Real.log_div (by positivity) hrd.ne', Real.log_div (by positivity) hd.ne']
  ring

/- English proof (translation)
Unfold `FlatDegree`. Introduce `E _ _ _ H D l Xo c g ty FU i U τ φ _ N _ χ hχ hty hrt hflat hN`. Take `⟨mem, line, ⟨e, ρ, hli, hcm⟩⟩` from `hflat`. Take `⟨hNinf, hNfin⟩` from `hN`. Establish `hsq : ∀ b : Bool, sgnRt H b ^ 2 = -(H.d : ℂ)`.

Introduce `b`. Apply the tactic sequence `cases b <;> simp [sgnRt, neg_sq, H.sqrt_neg_disc_sq]`. Use `choose Z x hz hper hxv using fun b => GlobalTheory.T.chowla_selberg_period E H χ hχ (sgnRt H b) (hsq b)`. Establish `hx : x false = x true` using `Complex.ofReal_injective ((hxv false).trans (hxv true).symm)`. Use `haveI := (Z true).nf`.

Use `haveI := (Z false).nf`. Take `⟨n₁, hn₁, hm₁⟩` from `hper true`. Take `⟨n₀, hn₀, hm₀⟩` from `hper false`. Take `⟨k, hkfd, r, hc, hM, hr0, hrz⟩` from `GlobalTheory.T.frame_function_cm_value E H D l Xo c g ty FU i Z U τ φ e ρ hty hrt mem line hli hcm`. Use `haveI := hkfd`.

Use `haveI : NumberField k := ⟨⟩`. Use `choose t ht1 ht2 ht3 using fun ℓ : Nat.Primes => GlobalTheory.T.frame_function_cm_height E H D l Xo c g ty FU i Z U τ φ e ρ k hc hM r ℓ hty hrt mem line hli hcm hr0 hrz`. Establish `hgram` using `GlobalTheory.T.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) (Fin D.p ⊕ Fin D.q) e (by rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, (FU.sig i).1, (FU.sig i).2]) hli`. Establish `hrt2 : ((H.rt : E)) ^ 2 = -(H.d : E)`. Establish `h` using `congrArg (algebraMap (NumberField.RingOfIntegers E) E) H.rt_sq`.

Rewrite `h` using `[map_pow, map_neg, map_natCast]`. Conclude with `h`. Establish `hmean₁` using `flatDegree_mean_ext (IntermediateField.inclusion (hM true)).toRingHom (fun σ => Real.log (n₁ σ))`. Establish `hmean₀` using `flatDegree_mean_ext (IntermediateField.inclusion (hM false)).toRingHom (fun σ => Real.log (n₀ σ))`. Establish `hfinite : {ℓ : Nat.Primes | ∃ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖ ≠ 0}.Finite`.

Apply `hgram.2.subset` to reduce the goal to its premises. Introduce `ℓ hℓ hloc`. Take `⟨j, hj⟩` from `hℓ`. Conclude with `hj (ht2 ℓ hloc j)`. Establish `key` using `GlobalTheory.T.hermitian_metric_log_norm_formula (↥k) E (RingHom.comp (IntermediateField.inclusion hc : ↥c.F →+* ↥k) (GlobalTheory.CompanionTheory.Ar.Fl.tauE c τ)) (N.ext (IntermediateField.inclusion hc).toRingHom) r (GlobalTheory.CompanionTheory.Ar.Fl.gramE (FU.Di i) e).det (H.r …`.

Take `⟨hAd, hdeg⟩` from `key`. Take `⟨hdeg', hAd'⟩` from `GlobalTheory.CompanionTheory.Ar.Fl.logNorms_ext_deg_isAdelic (↥c.F) (↥k) (IntermediateField.inclusion hc).toRingHom N`. Use `⟨hAd'.mp hAd, ?_⟩` and prove the remaining obligations. Rewrite using `[← hdeg', hdeg, flatDegree_logOm_re E χ (hxv true)]`.
-/
theorem flatDegree : FlatDegree := by
  unfold FlatDegree
  intro E _ _ _ H D l Xo c g ty FU i U τ φ _ N _ χ hχ hty hrt hflat hN
  obtain ⟨mem, line, ⟨e, ρ, hli, hcm⟩⟩ := hflat
  obtain ⟨hNinf, hNfin⟩ := hN
  have hsq : ∀ b : Bool, sgnRt H b ^ 2 = -(H.d : ℂ) := by
    intro b
    cases b <;> simp [sgnRt, neg_sq, H.sqrt_neg_disc_sq]
  choose Z x hz hper hxv using fun b => GlobalTheory.T.chowla_selberg_period E H χ hχ (sgnRt H b) (hsq b)
  have hx : x false = x true := Complex.ofReal_injective ((hxv false).trans (hxv true).symm)
  haveI := (Z true).nf
  haveI := (Z false).nf
  obtain ⟨n₁, hn₁, hm₁⟩ := hper true
  obtain ⟨n₀, hn₀, hm₀⟩ := hper false
  obtain ⟨k, hkfd, r, hc, hM, hr0, hrz⟩ :=
    GlobalTheory.T.frame_function_cm_value E H D l Xo c g ty FU i Z U τ φ e ρ hty hrt mem line hli hcm
  haveI := hkfd
  haveI : NumberField k := ⟨⟩
  choose t ht1 ht2 ht3 using fun ℓ : Nat.Primes =>
    GlobalTheory.T.frame_function_cm_height E H D l Xo c g ty FU i Z U τ φ e ρ k hc hM r ℓ hty hrt mem line hli hcm hr0 hrz
  have hgram := GlobalTheory.T.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) (Fin D.p ⊕ Fin D.q) e
    (by rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, (FU.sig i).1, (FU.sig i).2]) hli
  have hrt2 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have h := congrArg (algebraMap (NumberField.RingOfIntegers E) E) H.rt_sq
    rw [map_pow, map_neg, map_natCast] at h
    exact h
  have hmean₁ := flatDegree_mean_ext (IntermediateField.inclusion (hM true)).toRingHom
    (fun σ => Real.log (n₁ σ))
  have hmean₀ := flatDegree_mean_ext (IntermediateField.inclusion (hM false)).toRingHom
    (fun σ => Real.log (n₀ σ))
  have hfinite : {ℓ : Nat.Primes | ∃ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖ ≠ 0}.Finite := by
    apply hgram.2.subset
    intro ℓ hℓ hloc
    obtain ⟨j, hj⟩ := hℓ
    exact hj (ht2 ℓ hloc j)
  have key := GlobalTheory.T.hermitian_metric_log_norm_formula (↥k) E (RingHom.comp (IntermediateField.inclusion hc : ↥c.F →+* ↥k) (GlobalTheory.CompanionTheory.Ar.Fl.tauE c τ))
    (N.ext (IntermediateField.inclusion hc).toRingHom) r (GlobalTheory.CompanionTheory.Ar.Fl.gramE (FU.Di i) e).det
    (H.rt : E) D.p D.q H.d
    (fun s => n₁ (s.comp (IntermediateField.inclusion (hM true)).toRingHom))
    (fun s => n₀ (s.comp (IntermediateField.inclusion (hM false)).toRingHom))
    (x true) t (fun ℓ => IsCMField.complexConj E (t ℓ))
    hr0 hgram.1 (Nat.Prime.pos H.d_prime) hrt2
    (by rw [neg_div, hmean₁, ← hm₁]; rfl)
    (by rw [neg_div, hmean₀, ← hx, ← hm₀]; rfl)
    (fun s => GlobalTheory.T.frame_function_cm_number_field E H D l Xo c g ty FU i Z U τ φ e ρ k hc hM r s
      (n₁ (s.comp (IntermediateField.inclusion (hM true)).toRingHom))
      (n₀ (s.comp (IntermediateField.inclusion (hM false)).toRingHom))
      (N.inf (s.comp (IntermediateField.inclusion hc).toRingHom))
      hty hrt mem line hli hcm hr0 hrz
      (hn₁ _).1 (hn₀ _).1 (((hn₁ _).2 _).mpr rfl) (((hn₀ _).2 _).mpr rfl)
      (hNinf _))
    (fun ℓ => flatDegree_sum_conj (fun z : ℂ_[ℓ] => Real.log ‖z‖) (t ℓ))
    (fun ℓ j => ht1 ℓ j) hfinite
    (fun ℓ j => ht3 ℓ j _ (hNfin ℓ (j.comp (IntermediateField.inclusion hc).toRingHom)))
  obtain ⟨hAd, hdeg⟩ := key
  obtain ⟨hdeg', hAd'⟩ := GlobalTheory.CompanionTheory.Ar.Fl.logNorms_ext_deg_isAdelic (↥c.F) (↥k)
    (IntermediateField.inclusion hc).toRingHom N
  refine ⟨hAd'.mp hAd, ?_⟩
  rw [← hdeg', hdeg, flatDegree_logOm_re E χ (hxv true)]

end GlobalTheory.CompanionTheory.Ar.Fl

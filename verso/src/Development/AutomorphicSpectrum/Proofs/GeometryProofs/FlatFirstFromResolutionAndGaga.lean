import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionAnalyticNormStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InfNormConjugateInvariantStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitAnalyticFunctionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUniformisationOfAbelianSchemeLaws
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditionalStatement
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodEigenFrame
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateRootZero

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FlatFirstTheorem

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.ComplexConjugateRootEqNeg.rt0_conj_neg_ne_zero H`.
-/
theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 :=
  _root_.UpperTheory.Reformulated.B.ComplexConjugateRootEqNeg.rt0_conj_neg_ne_zero H

/- English proof (translation)
Establish `h : (σ (tauIn c τ H.rt)) ^ 2 = H.rt0 ^ 2`. Rewrite using `[← map_pow, ← map_pow, H.rt_sq, H.sqrt_neg_disc_sq]`. Simplify using the standard rewrite rules. Conclude with `sq_eq_sq_iff_eq_or_eq_neg.1 h`.
-/
theorem tauIn_rt_eq (τ : E →+* ℂ) (σ : c.F →+* ℂ) :
    σ (tauIn c τ H.rt) = H.rt0 ∨ σ (tauIn c τ H.rt) = -H.rt0 := by
  have h : (σ (tauIn c τ H.rt)) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, ← map_pow, H.rt_sq, H.sqrt_neg_disc_sq]; simp
  exact sq_eq_sq_iff_eq_or_eq_neg.1 h

/- English proof (translation)
Establish `hs : under y ≫ Xo.s = spMap (σ.comp (IntermediateField.inclusion c.le).toRingHom)`. Rewrite using `[under, Category.assoc, pullback.condition, ← Category.assoc, hf.1, ← Spec.map_comp]`. Both sides reduce to the same expression. Take `⟨i, P, hP, hu⟩` from `FU.onto _ hs`. Take `⟨V, hV, hli, -⟩` from `exists_directions_of_isEigFrame E H D l Xo _ g ty FU i P (under y) (σ.comp (tauIn c τ)) (σ.comp (τ.codRestrict c.F.toSubfield (c.conj τ))) D.p v hP hu.symm (fun a => rfl) hf.2.2.1`.

Take `⟨Hm, hH, hpos, him⟩` from `hP.2.2.2.2`. Establish `hG` using `(hodgeGram_iff_period E H D l Xo _ g ty FU i P Hm hP hH him (under y) hu.symm D.p v V Γ (fun a => (hV a (V a)).2 rfl)).1 hΓ`. Set `M : Matrix (Fin D.p) (Fin g) ℂ` to `Matrix.of V`. Establish `hΓM : Γ = (Real.pi : ℂ) • (M * Hm * M.conjTranspose)`. Use extensionality with `a b`.

Rewrite using `[hG a b, Matrix.smul_apply, smul_eq_mul]`. Use `congr 1`. Simplify using `only [hermForm, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, M, Matrix.of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring` and prove the remaining obligations.

Introduce `hdet`. Take `⟨x, hx0, hx⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hdet`. Use `set z := Matrix.vecMul (star x) M with hz`. Establish `hq : dotProduct (star x) (Γ.mulVec x) = (Real.pi : ℂ) * hermForm Hm z z`. Rewrite using `[hΓM, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hermForm, hz, Matrix.star_vecMul, star_star, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]`.

Rewrite `hq` using `[hx, dotProduct_zero]`. Establish `hz0 : z = 0`. Assume the negation of the conclusion as `hne`. Use `hpos z hne` as an intermediate fact. Establish `h2 : (hermForm Hm z z) = 0`.

Break down `mul_eq_zero.1 hq.symm with h | h` into its components or cases. Conclude with `absurd h (by exact_mod_cast Real.pi_ne_zero)`. Conclude with `h`. Rewrite `this` using `[h2]`. Simplify using `at this`.

Establish `hinj : Function.Injective M.vecMul` using `Matrix.vecMul_injective_iff.2 hli`. Establish `: star x = 0` using `hinj (show Matrix.vecMul (star x) M = Matrix.vecMul 0 M by rw [← hz, hz0, Matrix.zero_vecMul])`. Conclude with `hx0 (by simpa using this)`.
-/
theorem gram_det_ne_zero {τ : E →+* ℂ} {σ : c.F →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty)
    {y : Sp ℂ ⟶ Xo.XF c} {v : Vecs y D.p} {w : Vecs y D.q} {Γ : Matrix (Fin D.p) (Fin D.p) ℂ}
    (hf : IsFramed Set.univ τ σ y v w) (hΓ : IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) v Γ) :
    Γ.det ≠ 0 := by
  have hs : under y ≫ Xo.s = spMap (σ.comp (IntermediateField.inclusion c.le).toRingHom) := by
    rw [under, Category.assoc, pullback.condition, ← Category.assoc, hf.1, ← Spec.map_comp]; rfl
  obtain ⟨i, P, hP, hu⟩ := FU.onto _ hs
  obtain ⟨V, hV, hli, -⟩ := exists_directions_of_isEigFrame E H D l Xo _ g ty FU i P (under y)
    (σ.comp (tauIn c τ)) (σ.comp (τ.codRestrict c.F.toSubfield (c.conj τ))) D.p v hP hu.symm (fun a => rfl)
    hf.2.2.1
  obtain ⟨Hm, hH, hpos, him⟩ := hP.2.2.2.2
  have hG := (hodgeGram_iff_period E H D l Xo _ g ty FU i P Hm hP hH him (under y) hu.symm D.p v V Γ
    (fun a => (hV a (V a)).2 rfl)).1 hΓ
  let M : Matrix (Fin D.p) (Fin g) ℂ := Matrix.of V
  have hΓM : Γ = (Real.pi : ℂ) • (M * Hm * M.conjTranspose) := by
    ext a b
    rw [hG a b, Matrix.smul_apply, smul_eq_mul]
    congr 1
    simp only [hermForm, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, M,
      Matrix.of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  intro hdet
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  set z := Matrix.vecMul (star x) M with hz
  have hq : dotProduct (star x) (Γ.mulVec x) = (Real.pi : ℂ) * hermForm Hm z z := by
    rw [hΓM, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hermForm, hz, Matrix.star_vecMul, star_star,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  rw [hx, dotProduct_zero] at hq
  have hz0 : z = 0 := by
    by_contra hne
    have := hpos z hne
    have h2 : (hermForm Hm z z) = 0 := by
      rcases mul_eq_zero.1 hq.symm with h | h
      · exact absurd h (by exact_mod_cast Real.pi_ne_zero)
      · exact h
    rw [h2] at this; simp at this
  have hinj : Function.Injective M.vecMul := Matrix.vecMul_injective_iff.2 hli
  have : star x = 0 := hinj (show Matrix.vecMul (star x) M = Matrix.vecMul 0 M by rw [← hz, hz0, Matrix.zero_vecMul])
  exact hx0 (by simpa using this)

/- English proof (translation)
Take `⟨g, ty, hty⟩` from `GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q`. Establish `hK : (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0`. Establish `e : (IntermediateField.inclusion c.le) (baseKA l).ρ = tauIn c τ H.rt` using `Subtype.ext (show H.rt0 = τ (H.rt : E) from hτ.symm)`. Use `show σ ((IntermediateField.inclusion c.le) (baseKA l).ρ) = H.rt0`. Rewrite using `[e, hσ]`.

Take `⟨FU⟩` from `GlobalTheory.familyUnif_of_laws GlobalTheory.T.abelianScheme_laws_unconditional.1 E H D l Xo _ g ty hr hK hty`. Take `⟨Φ, hΦ, -⟩` from `GlobalTheory.T.exists_unit_analytic_function E H D l Xo c τ (σ.comp (τ.codRestrict c.F.toSubfield (c.conj τ))) σ g ty FU hty hσ (fun a => rfl)`. Take `⟨κ, hκ0, hκ⟩` from `GlobalTheory.T.frame_function_analytic_norm hR hG E H D l Xo c O β Y U Z τ σ Φ φ hβ hr hτ hσ hZ hΦ hl hm`. Use `⟨Real.log ‖κ‖, fun y v w Γ Δ hf h1 h2 => ?_⟩` and prove the remaining obligations. Establish `hf' : IsFramed Set.univ τ σ y v w` using `⟨hf.1, Set.subset_univ _, hf.2.2⟩`.

Establish `hΓ : ‖Γ.det‖ ≠ 0` using `norm_ne_zero_iff.2 (gram_det_ne_zero FU hf' h1)`. Establish `hΦ0 : ‖Φ y v w‖ ≠ 0` using `norm_ne_zero_iff.2 (hΦ.ne y v w hf')`. Establish `hn` using `congrArg Real.log (hΦ.norm y v w Γ Δ hf' h1 h2)`. Rewrite `hn` using `[Real.log_mul (pow_ne_zero 2 hΦ0) hΓ, Real.log_pow]`. Rewrite using `[hκ y v w hf, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hκ0) hΦ0]`.

Move the coercions through the operations in `at hn`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_infNorm_of_rt (hR : Geo.ResK.ResKStatement) (hG : GagaSections) {O : Type} [CommRing O]
    {β : O →+* c.F} {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) {τ : E →+* ℂ} {φ : FrameFn Xo c}
    (hβ : Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    (hr : 1 ≤ D.p + D.q) (hτ : τ (H.rt : E) = H.rt0) (hZ : Z.IsGeom) (hl : IsLineFn U τ φ)
    (hm : FlatOnModel Z τ φ) (σ : c.F →+* ℂ) (hσ : σ (tauIn c τ H.rt) = H.rt0) :
    ∃ t : ℝ, HasInfNorm U τ φ σ t := by
  obtain ⟨g, ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  have hK : (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 := by
    have e : (IntermediateField.inclusion c.le) (baseKA l).ρ = tauIn c τ H.rt :=
      Subtype.ext (show H.rt0 = τ (H.rt : E) from hτ.symm)
    show σ ((IntermediateField.inclusion c.le) (baseKA l).ρ) = H.rt0
    rw [e, hσ]
  obtain ⟨FU⟩ := GlobalTheory.familyUnif_of_laws GlobalTheory.T.abelianScheme_laws_unconditional.1 E H D l Xo _ g ty hr hK hty
  obtain ⟨Φ, hΦ, -⟩ := GlobalTheory.T.exists_unit_analytic_function E H D l Xo c τ (σ.comp (τ.codRestrict c.F.toSubfield (c.conj τ))) σ g ty FU
    hty hσ (fun a => rfl)
  obtain ⟨κ, hκ0, hκ⟩ := GlobalTheory.T.frame_function_analytic_norm hR hG E H D l Xo c O β Y U Z τ σ Φ φ hβ hr hτ hσ hZ hΦ hl hm
  refine ⟨Real.log ‖κ‖, fun y v w Γ Δ hf h1 h2 => ?_⟩
  have hf' : IsFramed Set.univ τ σ y v w := ⟨hf.1, Set.subset_univ _, hf.2.2⟩
  have hΓ : ‖Γ.det‖ ≠ 0 := norm_ne_zero_iff.2 (gram_det_ne_zero FU hf' h1)
  have hΦ0 : ‖Φ y v w‖ ≠ 0 := norm_ne_zero_iff.2 (hΦ.ne y v w hf')
  have hn := congrArg Real.log (hΦ.norm y v w Γ Δ hf' h1 h2)
  rw [Real.log_mul (pow_ne_zero 2 hΦ0) hΓ, Real.log_pow] at hn
  rw [hκ y v w hf, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hκ0) hΦ0]
  push_cast at hn
  linarith

/- English proof (translation)
Introduce `hR hG E _ _ _ H D l Xo c O _ β Y U Z τ φ hβ hr hτ hZ hl hm`. Establish `key : ∀ s : c.F →+* ℂ, ∃ t, HasInfNorm U τ φ s t`. Introduce `s`. Break down `tauIn_rt_eq (c := c) (H := H) τ s with h | h` into its components or cases. Conclude with `exists_infNorm_of_rt hR hG Z hβ hr hτ hZ hl hm s h`.

Take `⟨t, ht⟩` from `exists_infNorm_of_rt hR hG Z hβ hr hτ hZ hl hm ((starRingEnd ℂ).comp s) (by rw [RingHom.comp_apply, h, map_neg, rt0_conj_neg_ne_zero, neg_neg])`. Use `⟨t, ?_⟩` and prove the remaining obligations. Use `GlobalTheory.T.inf_norm_conjugate_invariant E H D l Xo c U τ φ _ t hl ht` as an intermediate fact. Rewrite `this` using `[show (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s from RingHom.ext fun x => by simp]`. Then use the resulting hypothesis. Use `⟨fun s => ?_, fun g ty FU i hty hmem => ?_⟩` and prove the remaining obligations.

Take `⟨t, ht⟩` from `key s`. Conclude with `⟨t, ht, GlobalTheory.T.inf_norm_conjugate_invariant E H D l Xo c U τ φ s t hl ht⟩`. Take `⟨Φ, hΦ, hfl⟩` from `GlobalTheory.T.exists_unit_analytic_function E H D l Xo c τ τ (algebraMap c.F ℂ) g ty FU hty hτ (fun a => rfl)`. Take `⟨κ, -, hκ⟩` from `GlobalTheory.T.frame_function_analytic_norm hR hG E H D l Xo c O β Y U Z τ (algebraMap c.F ℂ) Φ φ hβ hr hτ hτ hZ hΦ hl hm`. Take `⟨e, ρ, -, he, hρ⟩` from `hfl i`.

Use `⟨hmem, hl, e, κ * ρ, he, ?_⟩` and prove the remaining obligations. Introduce `P y v w V W C Fm B h1 h2 h3 h4 h5 h6 h7 h8`. Rewrite using `[hκ y v w h3, _root_.mul_assoc, hρ P y v w V W C Fm B h1 h2 ⟨h3.1, Set.subset_univ _, h3.2.2⟩ h4 h5 h6 h7 h8]`.
-/
theorem flat_first_of_resolution_gaga : Geo.ResK.ResKStatement → GagaSections → FlatLineGeneratorComponent := by
  intro hR hG E _ _ _ H D l Xo c O _ β Y U Z τ φ hβ hr hτ hZ hl hm
  have key : ∀ s : c.F →+* ℂ, ∃ t, HasInfNorm U τ φ s t := by
    intro s
    rcases tauIn_rt_eq (c := c) (H := H) τ s with h | h
    · exact exists_infNorm_of_rt hR hG Z hβ hr hτ hZ hl hm s h
    · obtain ⟨t, ht⟩ := exists_infNorm_of_rt hR hG Z hβ hr hτ hZ hl hm ((starRingEnd ℂ).comp s)
        (by rw [RingHom.comp_apply, h, map_neg, rt0_conj_neg_ne_zero, neg_neg])
      refine ⟨t, ?_⟩
      have := GlobalTheory.T.inf_norm_conjugate_invariant E H D l Xo c U τ φ _ t hl ht
      rwa [show (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s from RingHom.ext fun x => by simp] at this
  refine ⟨fun s => ?_, fun g ty FU i hty hmem => ?_⟩
  · obtain ⟨t, ht⟩ := key s
    exact ⟨t, ht, GlobalTheory.T.inf_norm_conjugate_invariant E H D l Xo c U τ φ s t hl ht⟩
  · obtain ⟨Φ, hΦ, hfl⟩ := GlobalTheory.T.exists_unit_analytic_function E H D l Xo c τ τ (algebraMap c.F ℂ) g ty FU hty hτ (fun a => rfl)
    obtain ⟨κ, -, hκ⟩ := GlobalTheory.T.frame_function_analytic_norm hR hG E H D l Xo c O β Y U Z τ (algebraMap c.F ℂ) Φ φ hβ hr hτ hτ hZ hΦ hl hm
    obtain ⟨e, ρ, -, he, hρ⟩ := hfl i
    refine ⟨hmem, hl, e, κ * ρ, he, ?_⟩
    intro P y v w V W C Fm B h1 h2 h3 h4 h5 h6 h7 h8
    rw [hκ y v w h3, _root_.mul_assoc, hρ P y v w V W C Fm B h1 h2 ⟨h3.1, Set.subset_univ _, h3.2.2⟩ h4 h5 h6 h7 h8]

end GlobalTheory.CompanionTheory.Ar.Flat.FlatFirstTheorem

import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCmPeriodEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.ExistsExtensionEmbeddingAlgClosedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPureFrameOpenStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorsBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPeriodProductStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveZNeZeroStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsTransitionMatrixGramStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramDetNeZeroLocalBasisCofiniteStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PureTypeLatticesOrthogonalStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsAlt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.InfPlace

/- English proof (translation)
Establish `hΓ' : Γ = ((r : ℂ) * ((ε : ℤ) : ℂ) * σ rt) • (σ.mapMatrix M)`. Use extensionality with `k k'`. Simplify using `only [hΓ, Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdet : Γ.det = ((r : ℂ) * ((ε : ℤ) : ℂ) * σ rt) ^ n * σ M.det`.

Rewrite using `[hΓ', Matrix.det_smul, Fintype.card_fin, RingHom.map_det]`. Establish `hε : ‖((ε : ℤ) : ℂ)‖ = 1`. Apply the tactic sequence `rcases Int.units_eq_one_or ε with h | h <;> simp [h]`. Establish `hs : ‖σ rt‖ ^ 2 = d`. Establish `h1 : σ rt ^ 2 = -(d : ℂ)`.

Rewrite using `[← map_pow, hrt]`. Simplify using the standard rewrite rules. Establish `h2` using `congrArg norm h1`. Simplify `h2` using `[norm_pow]`. Establish `hd' : (0 : ℝ) < d` using `by exact_mod_cast hd`.

Establish `hs0 : ‖σ rt‖ ≠ 0`. Introduce `h`. Rewrite `hs` using `[h]`. Establish `h0 : (d : ℝ) = 0` using `by simpa using hs.symm`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hlog : Real.log ‖σ rt‖ = Real.log d / 2`. Establish `h3` using `congrArg Real.log hs`. Rewrite `h3` using `[Real.log_pow]`. Move the coercions through the operations in `at h3`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hσM : σ M.det ≠ 0` using `(map_ne_zero σ).2 hM`. Establish `hpos : ‖((r : ℂ) * ((ε : ℤ) : ℂ) * σ rt) ^ n‖ ≠ 0`. Rewrite using `[norm_pow, norm_mul, norm_mul, hε, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, _root_.mul_one]`. Conclude with `pow_ne_zero _ (mul_ne_zero hr.ne' hs0)`. Rewrite using `[hdet, norm_mul, Real.log_mul hpos (norm_ne_zero_iff.2 hσM), norm_pow, norm_mul, norm_mul, hε, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, _root_.mul_one, Real.log_pow, Real.log_mul hr.ne' hs0, hlog]`.
-/
theorem log_norm_det_scaled {E : Type} [Field E] (σ : E →+* ℂ) (rt : E) (d : ℕ) (hd : 0 < d)
    (hrt : rt ^ 2 = -(d : E)) (r : ℝ) (hr : 0 < r) (ε : ℤˣ) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) E) (hM : M.det ≠ 0) (Γ : Matrix (Fin n) (Fin n) ℂ)
    (hΓ : ∀ k k', Γ k k' = (r : ℂ) * ((ε : ℤ) : ℂ) * σ (rt * M k k')) :
    Real.log ‖Γ.det‖ = (n : ℝ) * (Real.log r + Real.log d / 2) + Real.log ‖σ M.det‖ := by
  have hΓ' : Γ = ((r : ℂ) * ((ε : ℤ) : ℂ) * σ rt) • (σ.mapMatrix M) := by
    ext k k'
    simp only [hΓ, Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul, map_mul]
    ring
  have hdet : Γ.det = ((r : ℂ) * ((ε : ℤ) : ℂ) * σ rt) ^ n * σ M.det := by
    rw [hΓ', Matrix.det_smul, Fintype.card_fin, RingHom.map_det]
  have hε : ‖((ε : ℤ) : ℂ)‖ = 1 := by
    rcases Int.units_eq_one_or ε with h | h <;> simp [h]
  have hs : ‖σ rt‖ ^ 2 = d := by
    have h1 : σ rt ^ 2 = -(d : ℂ) := by
      rw [← map_pow, hrt]
      simp
    have h2 := congrArg norm h1
    simpa [norm_pow] using h2
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hs0 : ‖σ rt‖ ≠ 0 := by
    intro h
    rw [h] at hs
    have h0 : (d : ℝ) = 0 := by simpa using hs.symm
    linarith
  have hlog : Real.log ‖σ rt‖ = Real.log d / 2 := by
    have h3 := congrArg Real.log hs
    rw [Real.log_pow] at h3
    push_cast at h3
    linarith
  have hσM : σ M.det ≠ 0 := (map_ne_zero σ).2 hM
  have hpos : ‖((r : ℂ) * ((ε : ℤ) : ℂ) * σ rt) ^ n‖ ≠ 0 := by
    rw [norm_pow, norm_mul, norm_mul, hε, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, _root_.mul_one]
    exact pow_ne_zero _ (mul_ne_zero hr.ne' hs0)
  rw [hdet, norm_mul, Real.log_mul hpos (norm_ne_zero_iff.2 hσM), norm_pow, norm_mul, norm_mul, hε,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, _root_.mul_one, Real.log_pow,
    Real.log_mul hr.ne' hs0, hlog]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.ConjEqNegOfSqEqNegNat₂.main hd hz`.
-/
theorem conj_eq_neg_of_sq {d : ℕ} (hd : 0 < d) {z : ℂ} (hz : z ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ z = -z :=
  _root_.UpperTheory.Reformulated.B.ConjEqNegOfSqEqNegNat₂.main hd hz

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c g ty FU i Z U τ φ e ρ k _ hc hM r s n n' t hty hτ hU hline he hconst hr hrz hn hn' hLt hLf hinf`. Take `⟨P, hP, x, hx, X, v, w, hkK, hloc, hfr⟩` from `GlobalTheory.T.exists_cm_period_embedding E H D l Xo c g ty FU i Z τ ⟨2, Nat.prime_two⟩ k inferInstance hty hτ`. Establish `hxli : LinearIndependent (𝓞 E) x` using `hloc.1`. Establish `hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q`. Simplify using `[(FU.sig i).1, (FU.sig i).2]`.

Take `⟨T, hT, hgram, hTdet, -⟩` from `GlobalTheory.T.exists_transition_matrix_gram E H (FU.Di i) _ x e hcard he`. Establish `hTne` using `hTdet hxli`. Establish `hGe` using `(GlobalTheory.T.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) _ e hcard he).1`. Take `⟨hfram, hval⟩` from `GlobalTheory.T.cm_pack_pure_frame_open E H D l Xo c g ty FU i Z P hP X x hx U τ φ e ρ T v w hty hτ hU hline he hconst hxli hT hfr`. Take `⟨s', hs'⟩` from `GlobalTheory.T.exists_extension_embedding_alg_closed k X.K ℂ (IntermediateField.inclusion hkK).toRingHom s`.

Establish `hs'a : ∀ a : k, s' (IntermediateField.inclusion hkK a) = s a` using `fun a => DFunLike.congr_fun hs' a`. Establish `hβ : s'.comp X.β = s.comp (IntermediateField.inclusion hc).toRingHom`. Use extensionality with `a`. Conclude with `hs'a (IntermediateField.inclusion hc a)`. Establish `hMs : ∀ b, s'.comp (IntermediateField.inclusion (X.hM b)).toRingHom = s.comp (IntermediateField.inclusion (hM b)).toRingHom`.

Introduce `b`. Use extensionality with `a`. Conclude with `hs'a (IntermediateField.inclusion (hM b) a)`. Set `y' : Sp ℂ ⟶ Xo.XF c` to `spMap s' ≫ X.y`. Establish `hy' : under y' = spMap s' ≫ under X.y` using `Category.assoc _ _ _`.

Take `⟨⟨v', hv'⟩, hvI⟩` from `GlobalTheory.T.tangent_vectors_base_change E H Xo.X Xo.univ.t X.K ℂ s' (under X.y) (under y') (X.β.comp (tauIn c τ)) D.p v hy'`. Take `⟨⟨w', hw'⟩, hwI⟩` from `GlobalTheory.T.tangent_vectors_base_change E H Xo.X Xo.univ.t X.K ℂ s' (under X.y) (under y') (X.β.comp (tauIn c (ComplexEmbedding.conjugate τ))) D.q w hy'`. Establish `hfram' : IsFramed U τ (s.comp (IntermediateField.inclusion hc).toRingHom) y' v' w'`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hβ]`.

Simplify using `only [y', Category.assoc, hfram.1]`. Simplify using `[spMap, ← Spec.map_comp, CommRingCat.ofHom_comp]`. Introduce and unpack `_ ⟨u, rfl⟩`. Apply `hfram.2.1` to reduce the goal to its premises. Conclude with `⟨(spMap s') u, by simp [y']⟩`.

Rewrite using `[← hβ, RingHom.comp_assoc]`. Conclude with `(hvI v' hv').1 hfram.2.2.1`. Rewrite using `[← hβ, RingHom.comp_assoc]`. Conclude with `(hwI w' hw').1 hfram.2.2.2`. Establish `hconjτ : ComplexEmbedding.conjugate τ (H.rt : E) = sgnRt H false`.

Simplify using `only [sgnRt, ComplexEmbedding.conjugate_coe_eq, hτ]`. Conclude with `conj_eq_neg_of_sq H.d_prime.pos H.sqrt_neg_disc_sq`. Establish `hΓ` using `GlobalTheory.T.cm_pack_period_product E H D l Xo c g ty FU i Z P hP X true τ D.p (fun a => ⟨x (.inl a), hx.1 a⟩) v s' y' v' n (by simpa [sgnRt] using hτ) hfr.1 rfl hv' (by rw [hMs]; exact hLt)`. Establish `hΔ` using `GlobalTheory.T.cm_pack_period_product E H D l Xo c g ty FU i Z P hP X false (ComplexEmbedding.conjugate τ) D.q (fun a => ⟨x (.inr a), hx.2 a⟩) w s' y' w' n' hconjτ hfr.2 rfl hw' (by rw [hMs]; exact hLf)`. Establish `hmain` using `hinf y' v' w' _ _ hfram' hΓ hΔ`.

Rewrite `hmain` using `[hline.nat X.K ℂ s' X.β X.y v w y' v' w' hfram rfl hv' hw']`. Establish `hblock : gramE (FU.Di i) x = Matrix.fromBlocks (gramE (FU.Di i) (x ∘ Sum.inl)) 0 0 (gramE (FU.Di i) (x ∘ Sum.inr))`. Use extensionality with `a b`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b`. Both sides reduce to the same expression.

Conclude with `(GlobalTheory.T.pure_type_lattices_orthogonal E H (FU.Di i) g ty P hP _ _ (hx.1 a) (hx.2 b)).1`. Conclude with `(GlobalTheory.T.pure_type_lattices_orthogonal E H (FU.Di i) g ty P hP _ _ (hx.1 b) (hx.2 a)).2`. Both sides reduce to the same expression. Establish `hdet1 : (gramE (FU.Di i) x).det = (gramE (FU.Di i) (x ∘ Sum.inl)).det * (gramE (FU.Di i) (x ∘ Sum.inr)).det`. Rewrite using `[hblock, Matrix.det_fromBlocks_zero₁₂]`.

Establish `hdet2 : (gramE (FU.Di i) x).det = T.det * (gramE (FU.Di i) e).det * IsCMField.complexConj E T.det`. Establish `hc' : (T.map (IsCMField.complexConj E)).det = IsCMField.complexConj E T.det` using `(RingHom.map_det (IsCMField.complexConj E : E →+* E) T).symm`. Rewrite using `[hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc']`. Establish `hconjne : IsCMField.complexConj E T.det ≠ 0`. Simplify using `using hTne`.

Establish `hG : (gramE (FU.Di i) (x ∘ Sum.inl)).det * (gramE (FU.Di i) (x ∘ Sum.inr)).det ≠ 0`. Rewrite using `[← hdet1, hdet2]`. Conclude with `mul_ne_zero (mul_ne_zero hTne hGe) hconjne`. Establish `hG1` using `left_ne_zero_of_mul hG`. Establish `hG2` using `right_ne_zero_of_mul hG`.

Set `σ : E →+* ℂ` to `s'.comp (X.β.comp (tauE c τ))`. Set `σ' : E →+* ℂ` to `s'.comp (X.β.comp (tauE c (ComplexEmbedding.conjugate τ)))`. Establish `hσ' : ∀ a, ‖σ' a‖ = ‖σ a‖`. Introduce `a`. Establish `h1 : tauE c (ComplexEmbedding.conjugate τ) a = tauE c τ (IsCMField.complexConj E a)`.

Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `ComplexEmbedding.conjugate τ a = τ (IsCMField.complexConj E a)`. Rewrite using `[IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]`. Establish `h2 : σ' a = σ (IsCMField.complexConj E a)`. Simplify using `only [σ', σ, RingHom.comp_apply, h1]`.

Rewrite using `[h2, IsCMField.complexEmbedding_complexConj, RCLike.norm_conj]`. Establish `hrt : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E)`. Use `congrArg (algebraMap (𝓞 E) E) H.rt_sq` as an intermediate fact. Simplify using `using this`. Establish `hlΓ` using `log_norm_det_scaled σ (H.rt : E) H.d H.d_prime.pos hrt n hn (X.ε true) (gramE (FU.Di i) (x ∘ Sum.inl)) hG1 (Matrix.of fun a a' => (n : ℂ) * ((X.ε true : ℤ) : ℂ) * s' (X.β (tauE c τ ((H.rt : E) * sesq (FU.Di i) (x (.inl a)) (x (.inl a')))))) (fun _ _ => rfl)`.

Establish `hlΔ` using `log_norm_det_scaled σ' (H.rt : E) H.d H.d_prime.pos hrt n' hn' (X.ε false) (gramE (FU.Di i) (x ∘ Sum.inr)) hG2 (Matrix.of fun a a' => (n' : ℂ) * ((X.ε false : ℤ) : ℂ) * s' (X.β (tauE c (ComplexEmbedding.conjugate τ) ((H.rt : E) * sesq (FU.Di i) (x (.inr a)) (x (.inr a')))))) (fun …`. Rewrite `hlΔ` using `[hσ']`. Establish `hz` using `GlobalTheory.T.curve_z_ne_zero E H _ (Z true)`. Establish `hval2 : ((φ X.K X.y v w : X.K) : ℂ) * τ T.det = (r : ℂ) * τ (gramE (FU.Di i) (x ∘ Sum.inr)).det`. Apply `mul_right_cancel₀ (pow_ne_zero D.p hz)` to reduce the goal to its premises.

Rewrite using `[hval, ← hrz]`. Expand and normalize the polynomial expressions, which then agree. Establish `hK : (φ X.K X.y v w) * X.β (tauE c τ T.det) = IntermediateField.inclusion hkK r * X.β (tauE c τ (gramE (FU.Di i) (x ∘ Sum.inr)).det)` using `Subtype.ext hval2`. Establish `hS : s' (φ X.K X.y v w) * σ T.det = s r * σ (gramE (FU.Di i) (x ∘ Sum.inr)).det`. Use `congrArg s' hK` as an intermediate fact.

Rewrite `this` using `[map_mul, map_mul, hs'a]`. Conclude with `this`. Establish `hφ0 : s' (φ X.K X.y v w) ≠ 0` using `(map_ne_zero s').2 (hline.ne X.K X.β X.y v w hfram)`. Establish `hσT : σ T.det ≠ 0` using `(map_ne_zero σ).2 hTne`. Establish `hσG2 : σ (gramE (FU.Di i) (x ∘ Sum.inr)).det ≠ 0` using `(map_ne_zero σ).2 hG2`.

Establish `hσG1 : σ (gramE (FU.Di i) (x ∘ Sum.inl)).det ≠ 0` using `(map_ne_zero σ).2 hG1`. Establish `hσGe : σ (gramE (FU.Di i) e).det ≠ 0` using `(map_ne_zero σ).2 hGe`. Establish `hsr : s r ≠ 0` using `(map_ne_zero s).2 hr`. Establish `hl1 : Real.log ‖s' (φ X.K X.y v w)‖ + Real.log ‖σ T.det‖ = Real.log ‖s r‖ + Real.log ‖σ (gramE (FU.Di i) (x ∘ Sum.inr)).det‖`. Rewrite using `[← Real.log_mul (norm_ne_zero_iff.2 hφ0) (norm_ne_zero_iff.2 hσT), ← Real.log_mul (norm_ne_zero_iff.2 hsr) (norm_ne_zero_iff.2 hσG2), ← norm_mul, ← norm_mul, hS]`.

Establish `hl2 : Real.log ‖σ (gramE (FU.Di i) (x ∘ Sum.inl)).det‖ + Real.log ‖σ (gramE (FU.Di i) (x ∘ Sum.inr)).det‖ = 2 * Real.log ‖σ T.det‖ + Real.log ‖σ (gramE (FU.Di i) e).det‖`. Establish `h1` using `congrArg σ (hdet1.symm.trans hdet2)`. Rewrite `h1` using `[map_mul, map_mul, map_mul, IsCMField.complexEmbedding_complexConj]`. Establish `h2` using `congrArg norm h1`. Rewrite `h2` using `[norm_mul, norm_mul, norm_mul, RCLike.norm_conj]`.

Establish `h3` using `congrArg Real.log h2`. Rewrite `h3` using `[Real.log_mul (norm_ne_zero_iff.2 hσG1) (norm_ne_zero_iff.2 hσG2), Real.log_mul (mul_ne_zero (norm_ne_zero_iff.2 hσT) (norm_ne_zero_iff.2 hσGe)) (norm_ne_zero_iff.2 hσT), Real.log_mul (norm_ne_zero_iff.2 hσT) (norm_ne_zero_iff.2 hσGe)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlast : s ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) (gramE (FU.Di i) e).det) = σ (gramE (FU.Di i) e).det` using `(DFunLike.congr_fun hβ (tauE c τ (gramE (FU.Di i) e).det)).symm`. Rewrite using `[hlast]`.

Rewrite `hmain` using `[hlΓ, hlΔ]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hasInfNorm_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) (k : IntermediateField ℚ ℂ) [NumberField k] (hc : c.F ≤ k) (hM : ∀ b, (Z b).M ≤ k) (r : k) (s : k →+* ℂ) (n n' t : ℝ), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) → IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ → r ≠ 0 → (r : ℂ) * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q → 0 < n → 0 < n' → IsLieNormSq (Z true).C.P (Z true).C.v ((s.comp (IntermediateField.inclusion (hM true)).toRingHom).comp (algebraMap (𝓞 (Z true).M) (Z true).M)) n → IsLieNormSq (Z false).C.P (Z false).C.v ((s.comp (IntermediateField.inclusion (hM false)).toRingHom).comp (algebraMap (𝓞 (Z false).M) (Z false).M)) n' → HasInfNorm U τ φ (s.comp (IntermediateField.inclusion hc).toRingHom) t → t = Real.log ‖s r‖ + ((D.p : ℝ) / 2 * (Real.log n + Real.log H.d / 2) - (D.q : ℝ) / 2 * (Real.log n' + Real.log H.d / 2)) + Real.log ‖s ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) (gramE (FU.Di i) e).det)‖ / 2 := by
  intro E _ _ _ H D l Xo c g ty FU i Z U τ φ e ρ k _ hc hM r s n n' t hty hτ hU hline he hconst hr hrz hn hn' hLt hLf hinf
  classical
  obtain ⟨P, hP, x, hx, X, v, w, hkK, hloc, hfr⟩ :=
    GlobalTheory.T.exists_cm_period_embedding E H D l Xo c g ty FU i Z τ ⟨2, Nat.prime_two⟩ k inferInstance hty hτ
  have hxli : LinearIndependent (𝓞 E) x := hloc.1
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    simp [(FU.sig i).1, (FU.sig i).2]
  obtain ⟨T, hT, hgram, hTdet, -⟩ := GlobalTheory.T.exists_transition_matrix_gram E H (FU.Di i) _ x e hcard he
  have hTne := hTdet hxli
  have hGe := (GlobalTheory.T.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) _ e hcard he).1
  obtain ⟨hfram, hval⟩ := GlobalTheory.T.cm_pack_pure_frame_open E H D l Xo c g ty FU i Z P hP X x hx U τ φ e ρ T v w hty hτ hU hline he
    hconst hxli hT hfr
  obtain ⟨s', hs'⟩ := GlobalTheory.T.exists_extension_embedding_alg_closed k X.K ℂ (IntermediateField.inclusion hkK).toRingHom s
  have hs'a : ∀ a : k, s' (IntermediateField.inclusion hkK a) = s a := fun a => DFunLike.congr_fun hs' a
  have hβ : s'.comp X.β = s.comp (IntermediateField.inclusion hc).toRingHom := by
    ext a
    exact hs'a (IntermediateField.inclusion hc a)
  have hMs : ∀ b, s'.comp (IntermediateField.inclusion (X.hM b)).toRingHom =
      s.comp (IntermediateField.inclusion (hM b)).toRingHom := by
    intro b
    ext a
    exact hs'a (IntermediateField.inclusion (hM b) a)

  let y' : Sp ℂ ⟶ Xo.XF c := spMap s' ≫ X.y
  have hy' : under y' = spMap s' ≫ under X.y := Category.assoc _ _ _
  obtain ⟨⟨v', hv'⟩, hvI⟩ := GlobalTheory.T.tangent_vectors_base_change E H Xo.X Xo.univ.t X.K ℂ s' (under X.y) (under y')
    (X.β.comp (tauIn c τ)) D.p v hy'
  obtain ⟨⟨w', hw'⟩, hwI⟩ := GlobalTheory.T.tangent_vectors_base_change E H Xo.X Xo.univ.t X.K ℂ s' (under X.y) (under y')
    (X.β.comp (tauIn c (ComplexEmbedding.conjugate τ))) D.q w hy'
  have hfram' : IsFramed U τ (s.comp (IntermediateField.inclusion hc).toRingHom) y' v' w' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hβ]
      simp only [y', Category.assoc, hfram.1]
      simp [spMap, ← Spec.map_comp, CommRingCat.ofHom_comp]
    · rintro _ ⟨u, rfl⟩
      apply hfram.2.1
      exact ⟨(spMap s') u, by simp [y']⟩
    · rw [← hβ, RingHom.comp_assoc]
      exact (hvI v' hv').1 hfram.2.2.1
    · rw [← hβ, RingHom.comp_assoc]
      exact (hwI w' hw').1 hfram.2.2.2
  have hconjτ : ComplexEmbedding.conjugate τ (H.rt : E) = sgnRt H false := by
    simp only [sgnRt, ComplexEmbedding.conjugate_coe_eq, hτ]
    exact conj_eq_neg_of_sq H.d_prime.pos H.sqrt_neg_disc_sq
  have hΓ := GlobalTheory.T.cm_pack_period_product E H D l Xo c g ty FU i Z P hP X true τ D.p (fun a => ⟨x (.inl a), hx.1 a⟩) v s' y' v' n
    (by simpa [sgnRt] using hτ) hfr.1 rfl hv' (by rw [hMs]; exact hLt)
  have hΔ := GlobalTheory.T.cm_pack_period_product E H D l Xo c g ty FU i Z P hP X false (ComplexEmbedding.conjugate τ) D.q
    (fun a => ⟨x (.inr a), hx.2 a⟩) w s' y' w' n' hconjτ hfr.2 rfl hw' (by rw [hMs]; exact hLf)
  have hmain := hinf y' v' w' _ _ hfram' hΓ hΔ
  rw [hline.nat X.K ℂ s' X.β X.y v w y' v' w' hfram rfl hv' hw'] at hmain

  have hblock : gramE (FU.Di i) x =
      Matrix.fromBlocks (gramE (FU.Di i) (x ∘ Sum.inl)) 0 0 (gramE (FU.Di i) (x ∘ Sum.inr)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    · rfl
    · exact (GlobalTheory.T.pure_type_lattices_orthogonal E H (FU.Di i) g ty P hP _ _ (hx.1 a) (hx.2 b)).1
    · exact (GlobalTheory.T.pure_type_lattices_orthogonal E H (FU.Di i) g ty P hP _ _ (hx.1 b) (hx.2 a)).2
    · rfl
  have hdet1 : (gramE (FU.Di i) x).det =
      (gramE (FU.Di i) (x ∘ Sum.inl)).det * (gramE (FU.Di i) (x ∘ Sum.inr)).det := by
    rw [hblock, Matrix.det_fromBlocks_zero₁₂]
  have hdet2 : (gramE (FU.Di i) x).det =
      T.det * (gramE (FU.Di i) e).det * IsCMField.complexConj E T.det := by
    have hc' : (T.map (IsCMField.complexConj E)).det = IsCMField.complexConj E T.det :=
      (RingHom.map_det (IsCMField.complexConj E : E →+* E) T).symm
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc']
  have hconjne : IsCMField.complexConj E T.det ≠ 0 := by
    simpa using hTne
  have hG : (gramE (FU.Di i) (x ∘ Sum.inl)).det * (gramE (FU.Di i) (x ∘ Sum.inr)).det ≠ 0 := by
    rw [← hdet1, hdet2]
    exact mul_ne_zero (mul_ne_zero hTne hGe) hconjne
  have hG1 := left_ne_zero_of_mul hG
  have hG2 := right_ne_zero_of_mul hG

  let σ : E →+* ℂ := s'.comp (X.β.comp (tauE c τ))
  let σ' : E →+* ℂ := s'.comp (X.β.comp (tauE c (ComplexEmbedding.conjugate τ)))
  have hσ' : ∀ a, ‖σ' a‖ = ‖σ a‖ := by
    intro a
    have h1 : tauE c (ComplexEmbedding.conjugate τ) a = tauE c τ (IsCMField.complexConj E a) := by
      apply Subtype.ext
      change ComplexEmbedding.conjugate τ a = τ (IsCMField.complexConj E a)
      rw [IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
    have h2 : σ' a = σ (IsCMField.complexConj E a) := by
      simp only [σ', σ, RingHom.comp_apply, h1]
    rw [h2, IsCMField.complexEmbedding_complexConj, RCLike.norm_conj]
  have hrt : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have hlΓ := log_norm_det_scaled σ (H.rt : E) H.d H.d_prime.pos hrt n hn (X.ε true)
    (gramE (FU.Di i) (x ∘ Sum.inl)) hG1
    (Matrix.of fun a a' => (n : ℂ) * ((X.ε true : ℤ) : ℂ) *
      s' (X.β (tauE c τ ((H.rt : E) * sesq (FU.Di i) (x (.inl a)) (x (.inl a')))))) (fun _ _ => rfl)
  have hlΔ := log_norm_det_scaled σ' (H.rt : E) H.d H.d_prime.pos hrt n' hn' (X.ε false)
    (gramE (FU.Di i) (x ∘ Sum.inr)) hG2
    (Matrix.of fun a a' => (n' : ℂ) * ((X.ε false : ℤ) : ℂ) *
      s' (X.β (tauE c (ComplexEmbedding.conjugate τ) ((H.rt : E) * sesq (FU.Di i) (x (.inr a)) (x (.inr a')))))) (fun _ _ => rfl)
  rw [hσ'] at hlΔ

  have hz := GlobalTheory.T.curve_z_ne_zero E H _ (Z true)
  have hval2 : ((φ X.K X.y v w : X.K) : ℂ) * τ T.det = (r : ℂ) * τ (gramE (FU.Di i) (x ∘ Sum.inr)).det := by
    apply mul_right_cancel₀ (pow_ne_zero D.p hz)
    rw [hval, ← hrz]
    ring
  have hK : (φ X.K X.y v w) * X.β (tauE c τ T.det) =
      IntermediateField.inclusion hkK r * X.β (tauE c τ (gramE (FU.Di i) (x ∘ Sum.inr)).det) :=
    Subtype.ext hval2
  have hS : s' (φ X.K X.y v w) * σ T.det = s r * σ (gramE (FU.Di i) (x ∘ Sum.inr)).det := by
    have := congrArg s' hK
    rw [map_mul, map_mul, hs'a] at this
    exact this
  have hφ0 : s' (φ X.K X.y v w) ≠ 0 := (map_ne_zero s').2 (hline.ne X.K X.β X.y v w hfram)
  have hσT : σ T.det ≠ 0 := (map_ne_zero σ).2 hTne
  have hσG2 : σ (gramE (FU.Di i) (x ∘ Sum.inr)).det ≠ 0 := (map_ne_zero σ).2 hG2
  have hσG1 : σ (gramE (FU.Di i) (x ∘ Sum.inl)).det ≠ 0 := (map_ne_zero σ).2 hG1
  have hσGe : σ (gramE (FU.Di i) e).det ≠ 0 := (map_ne_zero σ).2 hGe
  have hsr : s r ≠ 0 := (map_ne_zero s).2 hr
  have hl1 : Real.log ‖s' (φ X.K X.y v w)‖ + Real.log ‖σ T.det‖ =
      Real.log ‖s r‖ + Real.log ‖σ (gramE (FU.Di i) (x ∘ Sum.inr)).det‖ := by
    rw [← Real.log_mul (norm_ne_zero_iff.2 hφ0) (norm_ne_zero_iff.2 hσT),
      ← Real.log_mul (norm_ne_zero_iff.2 hsr) (norm_ne_zero_iff.2 hσG2), ← norm_mul, ← norm_mul, hS]
  have hl2 : Real.log ‖σ (gramE (FU.Di i) (x ∘ Sum.inl)).det‖ + Real.log ‖σ (gramE (FU.Di i) (x ∘ Sum.inr)).det‖ =
      2 * Real.log ‖σ T.det‖ + Real.log ‖σ (gramE (FU.Di i) e).det‖ := by
    have h1 := congrArg σ (hdet1.symm.trans hdet2)
    rw [map_mul, map_mul, map_mul, IsCMField.complexEmbedding_complexConj] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_mul, norm_mul, RCLike.norm_conj] at h2
    have h3 := congrArg Real.log h2
    rw [Real.log_mul (norm_ne_zero_iff.2 hσG1) (norm_ne_zero_iff.2 hσG2),
      Real.log_mul (mul_ne_zero (norm_ne_zero_iff.2 hσT) (norm_ne_zero_iff.2 hσGe)) (norm_ne_zero_iff.2 hσT),
      Real.log_mul (norm_ne_zero_iff.2 hσT) (norm_ne_zero_iff.2 hσGe)] at h3
    linarith
  have hlast : s ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) (gramE (FU.Di i) e).det) =
      σ (gramE (FU.Di i) e).det :=
    (DFunLike.congr_fun hβ (tauE c τ (gramE (FU.Di i) e).det)).symm
  rw [hlast]
  rw [hlΓ, hlΔ] at hmain
  linarith

end GlobalTheory.CompanionTheory.Ar.Fl.InfPlace

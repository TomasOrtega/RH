import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittCharacterConjugateInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinEvaluationTripleTorusStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.ConeSmallLaw

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

instance borelIdele : BorelSpace (AE F E)ˣ := ⟨rfl⟩

/- English proof (translation)
Simplify using `only [thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]`.
-/
theorem thetaSum_smul' {κ : Type} (c : ℂ) (Φ : (κ → AF F) → ℂ) :
    thetaSum F (c • Φ) = c * thetaSum F Φ := by
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]

/- English proof (translation)
Simplify using `only [Model.I, theta, map_smul, thetaSum_smul']`. Conclude with `integral_const_mul c _`.
-/
theorem I_smul {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) (c : ℂ)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (h : UA σ W.J) : M.I om (c • Φ) h = c * M.I om Φ h := by
  simp only [Model.I, theta, map_smul, thetaSum_smul']
  exact integral_const_mul c _

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vecMulVec_mul_transpose {R : Type} [CommRing R] {n d : ℕ} (y : Fin n → R) (x : Fin d → R)
    (N : Matrix (Fin d) (Fin d) R) : Matrix.vecMulVec y x * Nᵀ = Matrix.vecMulVec y (N *ᵥ x) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/- English proof (translation)
Establish `: (cA σ).comp (cA σ) = AlgHom.id (AF F) (AE F E)`. Apply `Algebra.TensorProduct.ext'` to reduce the goal to its premises. Introduce `r s`. Simplify using `[cA, GlobalTheory.ThK.Inhab.conj_conj h]`. Conclude with `AlgHom.congr_fun this x`.
-/
theorem cA_cA (h : IsCMExt F E σ) (x : AE F E) : cA σ (cA σ x) = x := by
  have : (cA σ).comp (cA σ) = AlgHom.id (AF F) (AE F E) := by
    apply Algebra.TensorProduct.ext'
    intro r s
    simp [cA, GlobalTheory.ThK.Inhab.conj_conj h]
  exact AlgHom.congr_fun this x

/- English proof (translation)
Establish `: Units.map (cA σ).toMonoidHom x = GlobalTheory.Doubling.conjUnit σ x`. Use `ext`. Simplify using `only [Units.coe_map, MonoidHom.coe_coe]`. Both sides reduce to the same expression. Rewrite using `[this, GlobalTheory.Doubling.absE_conjUnit]`.
-/
theorem absE_cA (x : (AE F E)ˣ) : absE F E (Units.map (cA σ).toMonoidHom x) = absE F E x := by
  have : Units.map (cA σ).toMonoidHom x = GlobalTheory.Doubling.conjUnit σ x := by
    ext
    simp only [Units.coe_map, MonoidHom.coe_coe]
    rfl
  rw [this, GlobalTheory.Doubling.absE_conjUnit]

end GlobalTheory.ConeSmallLaw

namespace GlobalTheory.ConeSmallLaw

/- English proof (translation)
Establish `h1 : mat m *ᵥ incV F H'.x = t.1 • incV F H'.x` using `hL.1`. Simplify using `only [actAB, shiftB, OneMemClass.coe_one, Units.val_one, Matrix.one_mul, Matrix.smul_mul]`. Rewrite using `[vecMulVec_mul_transpose, show ((m : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) = mat m from rfl, h1, Matrix.vecMulVec_smul, smul_smul]`. Use `congr 1`. Establish `e1 : (t : AE F E) = cA σ ((Units.map (cA σ).toMonoidHom t : (AE F E)ˣ) : AE F E)`.

Simplify using `[cA_cA hcm]`. Rewrite using `[Units.val_mul, map_mul, mul_assoc, e1, ← map_mul, Units.inv_mul, map_one, mul_one]`.
-/
theorem act_shiftB {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hcm : IsCMExt F E σ) {n n₁ d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁} (H : Plane E n n₁)
    (H' : Plane E d d₁) (t : (AE F E)ˣ) (m : UA σ W.J) (hL : IsLevi (W₁ := W₁) H' t 1 m) (l : (AE F E)ˣ) :
    actAB (cA σ) ((1 : UA σ X.J), m) (shiftB σ H H' (l * (Units.map (cA σ).toMonoidHom t)⁻¹)) = shiftB σ H H' l := by
  have h1 : mat m *ᵥ incV F H'.x = t.1 • incV F H'.x := hL.1
  simp only [actAB, shiftB, OneMemClass.coe_one, Units.val_one, Matrix.one_mul, Matrix.smul_mul]
  rw [vecMulVec_mul_transpose, show ((m : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) = mat m from rfl, h1,
    Matrix.vecMulVec_smul, smul_smul]
  congr 1
  have e1 : (t : AE F E) = cA σ ((Units.map (cA σ).toMonoidHom t : (AE F E)ˣ) : AE F E) := by
    simp [cA_cA hcm]
  rw [Units.val_mul, map_mul, mul_assoc, e1, ← map_mul, Units.inv_mul, map_one, mul_one]

/- English proof (translation)
Establish `hspl` using `T.weil'.isUSplitting`. Establish `hΨ' : om' (k, h) Ψ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2)))` using `hspl.pres _ _ hΨ`. Establish `h1 : om' (k, m * h) Ψ = om' (1, m) (om' (k, h) Ψ)`. Rewrite using `[← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]`. Establish `h2 : G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (1, m) (om' (k, h) Ψ)) = om' (1, m) (G.M'.co.rho B.ψ (shiftB σ H H' (l * (Units.map (cA σ).toMonoidHom t)⁻¹)) (om' (k, h) Ψ))`.

Rewrite using `[hspl.impl (1, m) _ _ hΨ']`. Use `congr 1`. Conclude with `(act_shiftB T.base.cm H H' t m hL l).symm`. Establish `hρ` using `GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ T.base.std (shiftB σ H H' (l * (Units.map (cA σ).toMonoidHom t)⁻¹)) _ hΨ'`. Rewrite using `[h1, h2, GlobalTheory.T.eisenstein_evaluation_triple_torus hKP F E σ B a b G G₁ H H' cfg e' he' X om om' om₁ om₁' T T₁ t m hL _ hρ, I_smul]`.
-/
theorem integrand_levi (hKP : GlobalTheory.ThK.KP) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : Base F E} {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b}
    {H : Plane E (b + 2) b} {H' : Plane E (a + (b + 2)) (a + b)} (cfg : CfgB B G G₁ H H') {e'}
    (he' : IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e') {X om om' om₁ om₁'} (T : IsTriple B G X om om')
    (T₁ : IsTriple B G₁ X om₁ om₁') (t : (AE F E)ˣ) (m : UA σ G.W.J) (hL : IsLevi (W₁ := G₁.W) H' t 1 m)
    (k : UA σ G.V'.J) (h : UA σ G.W.J) (Ψ : (Fin (b + 2) × Fin (a + (b + 2)) → AF F) → ℂ)
    (hΨ : Ψ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2)))) (l : (AE F E)ˣ) :
    G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k, m * h) Ψ))) 1 =
      ((X.α t : ℂ) * (((absE F E t : ℝ) ^ ((b : ℝ) / 2) : ℝ) : ℂ)) *
        G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' (l * (Units.map (cA σ).toMonoidHom t)⁻¹)) (om' (k, h) Ψ))) 1 := by
  have hspl := T.weil'.isUSplitting
  have hΨ' : om' (k, h) Ψ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))) := hspl.pres _ _ hΨ
  have h1 : om' (k, m * h) Ψ = om' (1, m) (om' (k, h) Ψ) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have h2 : G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (1, m) (om' (k, h) Ψ)) =
      om' (1, m) (G.M'.co.rho B.ψ (shiftB σ H H' (l * (Units.map (cA σ).toMonoidHom t)⁻¹)) (om' (k, h) Ψ)) := by
    rw [hspl.impl (1, m) _ _ hΨ']
    congr 1
    exact (act_shiftB T.base.cm H H' t m hL l).symm
  have hρ := GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ T.base.std
    (shiftB σ H H' (l * (Units.map (cA σ).toMonoidHom t)⁻¹)) _ hΨ'
  rw [h1, h2, GlobalTheory.T.eisenstein_evaluation_triple_torus hKP F E σ B a b G G₁ H H' cfg e' he' X om om' om₁ om₁' T T₁ t m hL _ hρ, I_smul]

/- English proof (translation)
Take `⟨k, hk⟩` from `hG.even`. Establish `h1` using `hG.lt`. Establish `h2 : 2 * ((a - (b + 2)) / 2 + 1) + b = a` using `by omega`. Establish `h3 : (2 * (((a - (b + 2)) / 2 + 1 : ℕ) : ℝ) + b : ℝ) = a` using `by exact_mod_cast h2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exp_add {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {a b : ℕ} {G : Geo σ a (b + 2)} (hG : G.IsGood B) :
    (b : ℝ) / 2 + (((a - (b + 2)) / 2 + 1 : ℕ) : ℝ) = (a : ℝ) / 2 := by
  obtain ⟨k, hk⟩ := hG.even
  have h1 := hG.lt
  have h2 : 2 * ((a - (b + 2)) / 2 + 1) + b = a := by omega
  have h3 : (2 * (((a - (b + 2)) / 2 + 1 : ℕ) : ℝ) + b : ℝ) = a := by exact_mod_cast h2
  linarith

/- English proof (translation)
Rewrite using `[inv_pow, mul_inv, inv_inv, inv_div]`. Clear the denominators using the available nonvanishing facts.
-/
theorem scalar_id (A Bt R P : ℂ) (hA : A ≠ 0) (hB : Bt ≠ 0) (hR : R ≠ 0) (N : ℕ) :
    A * P * (A / Bt * (R⁻¹) ^ N)⁻¹ = Bt * (P * R ^ N) := by
  rw [inv_pow, mul_inv, inv_inv, inv_div]
  field_simp

/- English proof (translation)
Establish `h` using `map_mul (absE F E) l l⁻¹`. Rewrite `h` using `[mul_inv_cancel, map_one]`. Establish `: absE F E l ≠ 0` using `left_ne_zero_of_mul_eq_one h.symm`. Conclude with `pos_iff_ne_zero.mpr this` after adjusting the coercions.
-/
theorem absE_pos {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (l : (AE F E)ˣ) :
    (0 : ℝ) < absE F E l := by
  have h := map_mul (absE F E) l l⁻¹
  rw [mul_inv_cancel, map_one] at h
  have : absE F E l ≠ 0 := left_ne_zero_of_mul_eq_one h.symm
  exact_mod_cast pos_iff_ne_zero.mpr this

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B a b G G₁ H H' cfg e' he' K μK μ hK hμK hμ X om om' om₁ om₁' T T₁ Φ' hΦ' t m hL h`. Establish `hS : Φ' ∈ schA F (Fin (b + 2) × Fin (a + (b + 2)))`. Use `Submodule.span_le.mpr ?_ hΦ'` and prove the remaining obligations. Introduce and unpack `_ ⟨f, φ, hφ, hv, -, rfl⟩`. Use `GlobalTheory.TensUniq.pure_mem_schA f φ hφ ?_` and prove the remaining obligations.

Use `filter_upwards [hv, T.geo.hM'.std] with v h1 h2`. Rewrite using `[h1, h2]`. Take `⟨u, hu⟩ : ∃ u : (AE F E)ˣ, u = (Units.map (cA σ).toMonoidHom t)⁻¹` from `⟨_, rfl⟩`. Take `⟨N, hN⟩ : ∃ N : ℕ, N = (a - (b + 2)) / 2 + 1` from `⟨_, rfl⟩`. Rewrite using `[← hN]`.

Establish `hν0 : ∀ l : (AE F E)ˣ, (X.ν l : ℂ) ≠ 0` using `fun l => Circle.coe_ne_zero _`. Establish `habs0 : ∀ l : (AE F E)ˣ, ((absE F E l : ℝ) : ℂ) ≠ 0` using `fun l => Complex.ofReal_ne_zero.mpr (absE_pos l).ne'`. Establish `hin : ∀ k : K, (∫ l, G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, m * h) Φ'))) 1 * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ (N : ℂ) ∂μ) = ((X.α t : ℂ) * (((absE F E t : ℝ) ^ ((b : ℝ) / 2) : ℝ) : ℂ)) * ((X.ν u : ℂ) * ((absE F E u : ℝ) : ℂ) ^ N)⁻¹ * ∫ l, G₁.M'.I om₁ …`. Introduce `k`. Rewrite using `[← integral_mul_right_eq_self (μ := μ) (fun l => G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ'))) 1 * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ (N : ℂ)) u, ← integral_const_mul]`.

Use `integral_congr_ae (Eventually.of_forall fun l => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[integrand_levi hKP cfg he' T T₁ t m hL k.1 h Φ' hS l, ← hu]`. Establish `h1` using `hν0 u`. Establish `h2` using `habs0 u`.

Simplify using `only [Complex.cpow_natCast, map_mul, Circle.coe_mul, NNReal.coe_mul, Complex.ofReal_mul, mul_pow]`. Clear the denominators using the available nonvanishing facts. Establish `hα` using `GlobalTheory.chrX_conj_inv F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' T) t`. Establish `hβ` using `GlobalTheory.chrX_conj_inv F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.Inhab.pairV T) t`. Establish `hνu : X.ν u = X.α t / X.β t`.

Rewrite using `[hu, map_inv, Chars.ν, MonoidHom.div_apply, hα, hβ, inv_div_inv, inv_div]`. Establish `habsu : ((absE F E u : ℝ) : ℂ) = (((absE F E t : ℝ) : ℂ))⁻¹`. Rewrite using `[hu, map_inv, absE_cA, NNReal.coe_inv, Complex.ofReal_inv]`. Establish `hr` using `absE_pos t`. Use `show GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (N : ℂ) (m * h) = _`.

Unfold `GlobalTheory.ConeSmall.coneI`. Rewrite using `[integral_congr_ae (Eventually.of_forall hin), integral_const_mul]`. Use `congr 1`. Rewrite using `[show (((absE F E t : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ) = (((absE F E t : ℝ) ^ ((b : ℝ) / 2) : ℝ) : ℂ) * ((absE F E t : ℝ) : ℂ) ^ N by`. Rewrite using `[← exp_add T.geo, ← hN, Real.rpow_add hr, Real.rpow_natCast, Complex.ofReal_mul, Complex.ofReal_pow]]`.

Rewrite using `[hνu, habsu, Circle.coe_div]`. Conclude with `scalar_id _ _ _ _ (Circle.coe_ne_zero _) (Circle.coe_ne_zero _) (habs0 t) N`.
-/
theorem coneI_law : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ' ∈ G.M'.So B.ψ B.τ₁,
        HasLaw G₁.W H' X.β ((a : ℝ) / 2) (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (((a - (b + 2)) / 2 + 1 : ℕ) : ℂ)) := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' cfg e' he' K μK μ hK hμK hμ X om om' om₁ om₁' T T₁ Φ' hΦ' t m hL h
  classical
  have hS : Φ' ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))) := by
    refine Submodule.span_le.mpr ?_ hΦ'
    rintro _ ⟨f, φ, hφ, hv, -, rfl⟩
    refine GlobalTheory.TensUniq.pure_mem_schA f φ hφ ?_
    filter_upwards [hv, T.geo.hM'.std] with v h1 h2
    rw [h1, h2]
  obtain ⟨u, hu⟩ : ∃ u : (AE F E)ˣ, u = (Units.map (cA σ).toMonoidHom t)⁻¹ := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = (a - (b + 2)) / 2 + 1 := ⟨_, rfl⟩
  rw [← hN]
  have hν0 : ∀ l : (AE F E)ˣ, (X.ν l : ℂ) ≠ 0 := fun l => Circle.coe_ne_zero _
  have habs0 : ∀ l : (AE F E)ˣ, ((absE F E l : ℝ) : ℂ) ≠ 0 := fun l =>
    Complex.ofReal_ne_zero.mpr (absE_pos l).ne'
  have hin : ∀ k : K, (∫ l, G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, m * h) Φ'))) 1 *
        (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ (N : ℂ) ∂μ) =
      ((X.α t : ℂ) * (((absE F E t : ℝ) ^ ((b : ℝ) / 2) : ℝ) : ℂ)) *
        ((X.ν u : ℂ) * ((absE F E u : ℝ) : ℂ) ^ N)⁻¹ *
        ∫ l, G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ'))) 1 *
          (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ (N : ℂ) ∂μ := by
    intro k
    rw [← integral_mul_right_eq_self (μ := μ) (fun l => G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l)
      (om' (k.1, h) Φ'))) 1 * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ (N : ℂ)) u, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun l => ?_)
    simp only
    rw [integrand_levi hKP cfg he' T T₁ t m hL k.1 h Φ' hS l, ← hu]
    have h1 := hν0 u
    have h2 := habs0 u
    simp only [Complex.cpow_natCast, map_mul, Circle.coe_mul, NNReal.coe_mul, Complex.ofReal_mul, mul_pow]
    field_simp
  have hα := GlobalTheory.chrX_conj_inv F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' T) t
  have hβ := GlobalTheory.chrX_conj_inv F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.Inhab.pairV T) t
  have hνu : X.ν u = X.α t / X.β t := by
    rw [hu, map_inv, Chars.ν, MonoidHom.div_apply, hα, hβ, inv_div_inv, inv_div]
  have habsu : ((absE F E u : ℝ) : ℂ) = (((absE F E t : ℝ) : ℂ))⁻¹ := by
    rw [hu, map_inv, absE_cA, NNReal.coe_inv, Complex.ofReal_inv]
  have hr := absE_pos t
  show GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (N : ℂ) (m * h) = _
  unfold GlobalTheory.ConeSmall.coneI
  rw [integral_congr_ae (Eventually.of_forall hin), integral_const_mul]
  congr 1
  rw [show (((absE F E t : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ) =
      (((absE F E t : ℝ) ^ ((b : ℝ) / 2) : ℝ) : ℂ) * ((absE F E t : ℝ) : ℂ) ^ N by
    rw [← exp_add T.geo, ← hN, Real.rpow_add hr, Real.rpow_natCast, Complex.ofReal_mul, Complex.ofReal_pow]]
  rw [hνu, habsu, Circle.coe_div]
  exact scalar_id _ _ _ _ (Circle.coe_ne_zero _) (Circle.coe_ne_zero _) (habs0 t) N

end GlobalTheory.ConeSmallLaw

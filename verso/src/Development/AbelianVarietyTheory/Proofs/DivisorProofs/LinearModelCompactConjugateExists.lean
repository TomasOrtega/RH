import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalGoodPlaceEquivariant
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ShapeUXBas

/- English proof (translation)
Introduce `hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v t b c ι hι`. It suffices to establish `H : ∀ g ∈ UAt σ X (evFin F v), ∃ κ₀ : ℂ, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = κ₀ • fun Y => ι φ (((locMat t b g)⁻¹ : GL (Fin n) (Fv F v)).val * Y) by classical`. Use `⟨fun g => if hg : g ∈ UAt σ X (evFin F v) then (H g hg).choose else 0, fun g hg => ?_⟩` and prove the remaining obligations. Simplify using `only [dif_pos hg]`. Conclude with `(H g hg).choose_spec`.

Introduce `g hg`. Establish `hcm : IsCMExt F E σ` using `hP.base.cm`. Establish `hstd` using `hP.base.std`. Establish `hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v)` using `GlobalTheory.SchrSB.continuous_psiAt _ hstd.1 v`. Establish `hψ1 : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1` using `GlobalTheory.PsiNontriv.psiAt_ne_one _ hstd v`.

Establish `hSplit` using `GlobalTheory.WeilM.IsUWeilPair.isUSplitting hP.weil`. Establish `hAE` using `(GlobalTheory.T.theta_action_exists hPr) F E σ B n d X W M χX χW om r s r' s' hP v`. Establish `h1W : (1 : UA σ W.J) ∈ UAt σ W (evFin F v)`. Introduce `u _`. Simplify using `[mat]`.

Establish `hex : ∀ φ : (Fin n × Fin d → Fv F v) → ℂ, ∃ φ₁ : (Fin n × Fin d → Fv F v) → ℂ, φ ∈ SB (Fin n × Fin d → Fv F v) → φ₁ ∈ SB (Fin n × Fin d → Fv F v) ∧ Acts (evFin F v) (om (g, 1)) φ φ₁`. Introduce `φ`. Distinguish the cases in `hφ : φ ∈ SB (Fin n × Fin d → Fv F v)`. Take `⟨φ₁, h, -⟩` from `hAE.1 g hg 1 h1W φ hφ`. Conclude with `⟨φ₁, fun _ => h⟩`.

Conclude with `⟨0, fun h => absurd h hφ⟩`. Use `choose A hA using hex`. Establish `huniq : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ → φ₁ = A φ` using `fun φ hφ φ₁ hφ₁ h => (hAE.1 g hg 1 h1W φ hφ).unique ⟨hφ₁, h⟩ (hA φ hφ)`. Establish `hASB : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), A φ ∈ SB (Fin n × Fin d → Fv F v)` using `fun φ hφ => (hA φ hφ).1`. Establish `restA : ∀ φ r, φ ∈ SB (Fin n × Fin d → Fv F v) → Rest (evFin F v) φ r → Rest (evFin F v) (A φ) r` using `fun φ r hφ hr => ⟨hr.1, by rw [← (hA φ hφ).2 r hr]; exact hSplit.pres _ _ hr.2⟩`.

Establish `hvac` using `hP.good.vac v`. Establish `hlin : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ' ∈ SB (Fin n × Fin d → Fv F v), ∀ c : ℂ, A (c • φ + φ') = c • A φ + A φ'`. Introduce `φ hφ φ' hφ' c`. Use `GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v (M.vac v) _ _ hvac.1 fun r hr => ?_` and prove the remaining obligations. Establish `hsum : c • φ + φ' ∈ SB (Fin n × Fin d → Fv F v)` using `Submodule.add_mem _ (Submodule.smul_mem _ c hφ) hφ'`.

Establish `r0` using `GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hsum hr`. Establish `r1` using `GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hφ hr`. Establish `r2` using `GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hφ' hr`. Establish `et : ∀ (ψ₁ ψ₂ : (Fin n × Fin d → Fv F v) → ℂ), tens (evFin F v) (c • ψ₁ + ψ₂) r = c • tens (evFin F v) ψ₁ r + tens (evFin F v) ψ₂ r` using `fun ψ₁ ψ₂ => by`. Use function extensionality and compare the values at `x`.

Simplify using `only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← (hA _ hsum).2 r r0, et, map_add, map_smul, (hA φ hφ).2 r r1, (hA φ' hφ').2 r r2, et]`. Establish `hact : ∀ γ : Matrix (Fin n) (Fin d) (AE F E), actAB (cA σ) (g, (1 : UA σ W.J)) γ = mat g * γ`. Introduce `γ`.

Simplify using `[actAB, mat]`. Establish `atMul : ∀ (P : Matrix (Fin n) (Fin n) (AE F E)) (γ : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) γ → At (evFin F v) (P * γ)`. Introduce `P γ hγ u hu`. Rewrite using `[← Matrix.mul_smul, hγ u hu, Matrix.mul_zero]`. Establish `hcov : ∀ γ : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) γ → ∀ φ ∈ SB (Fin n × Fin d → Fv F v), A (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v γ) φ) = schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (mat g * γ)) (A φ)`.

Introduce `γ hγ φ hφ`. Establish `hw` using `GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v (GlobalTheory.LatVac.locCo M.co v γ) φ hφ`. Use `GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_` and prove the remaining obligations. Establish `hb1` using `GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ hγ φ r hr`. Establish `hRw : Rest (evFin F v) (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v γ) φ) r` using `⟨hr.1, by rw [← hb1]; exact GlobalTheory.T.weil_representation_preserves_schwartz M B.ψ hstd γ _ hr.2⟩`.

Rewrite using `[← (hA _ hw).2 r hRw, ← hb1, hSplit.impl _ _ _ hr.2, (hA φ hφ).2 r hr, hact, GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v _ (atMul _ γ hγ) (A φ) r (restA φ r hφ hr)]`. Establish `hL` using `hι`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLinW at hL`. Establish `hsb : ∀ (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) (φ : (Fin n × Fin d → Fv F v) → ℂ), φ ∈ SB (Fin n × Fin d → Fv F v) → schr (GlobalTheory.LatVac.psiAt B.ψ v) w φ ∈ SB (Fin n × Fin d → Fv F v)` using `fun w φ hφ => GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v w φ hφ`. Establish `hT : ∀ γ : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) γ → γ.map (piW (t.comp σ)) = 0 → ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ Y, ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v γ) φ) Y = ι φ (Y + (b⁻¹).val * γ.map (piW t) * ((c⁻¹).val)ᵀ)` using `fun γ hγ h0 φ hφ Y => hL.trans γ hγ h0 φ hφ _ (hsb _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ hγ φ) Y`.

Establish `hM : ∀ γ : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) γ → γ.map (piW t) = 0 → ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ x : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x → x.map (piW (t.comp σ)) = 0 → ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v …` using `fun γ hγ h0 φ hφ x hx hx0 => hL.mult γ hγ h0 φ hφ _ (hsb _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ hγ φ) x hx hx0`. Use `choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin n) (Fin d) (Fv F v)) => GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm v t P₀ P₁`. Use `set A' := X.J.map (t.comp σ) with hA'def`. Use `set B' := W.J.map (t.comp σ) with hB'def`. Establish `hsymp : ∀ x u : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x → x.map (piW (t.comp σ)) = 0 → u.map (piW t) = 0 → B.ψ (symp (R` using `AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) x u) = GlobalTheory.LatVac.psiAt B.ψ v (-(∑ k, ∑ l, (-(A' * x.map (piW t) * B'ᵀ)) k l * u.map (piW (t.comp σ)) k l)) := by`.

Introduce `x u hx hx0 hu1`. Establish `hu1' : u.map (piW ((t.comp σ).comp σ)) = 0` using `by rw [comp_conj_conj hcm]; exact hu1`. Establish `e` using `GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm (t.comp σ) X.J W.J hP.herm.herm hP.skew.skew x u hx0 hu1'`. Rewrite `e` using `[comp_conj_conj hcm]`. Unfold `symp`.

Rewrite using `[GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v (t.comp σ) _ (GlobalTheory.ShapeUV.at_neg_hTens _ _ x u hx), comp_conj_conj hcm]`. Rewrite using `[map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add, e]`. Both sides reduce to the same expression. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `hdV : X.J.det ≠ 0`.

Introduce `h0`. Apply `GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hP.herm.sig w)` to reduce the goal to its premises. Establish `e : (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det` using `(RingHom.map_det _ _).symm`. Rewrite using `[e, h0, map_zero]`. Establish `hdW : W.J.det ≠ 0`.

Introduce `h0`. Apply `GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hP.skew.sig w)` to reduce the goal to its premises. Establish `e : (W.J.map (B.emb w).1).det = (B.emb w).1 W.J.det` using `(RingHom.map_det _ _).symm`. Rewrite using `[Matrix.det_smul, e, h0, map_zero, mul_zero]`. Establish `hA' : IsUnit A'ᵀ.det`.

Establish `e : A'.det = ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) X.J.det` using `(RingHom.map_det _ _).symm`. Rewrite using `[Matrix.det_transpose, e]`. Conclude with `isUnit_iff_ne_zero.2 fun h => hdV (((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v).injective (by rw [map_zero]; exact h))`. Establish `hB' : IsUnit B'.det`. Establish `e : B'.det = ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) W.J.det` using `(RingHom.map_det _ _).symm`.

Rewrite using `[e]`. Conclude with `isUnit_iff_ne_zero.2 fun h => hdW (((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v).injective (by rw [map_zero]; exact h))`. Use `set A'' := A' * b.val with hA''def`. Use `set B'' := B' * c.val with hB''def`. Establish `hA'' : IsUnit A''ᵀ.det`.

Rewrite using `[hA''def, Matrix.transpose_mul, Matrix.det_mul, Matrix.det_transpose]`. Conclude with `(Matrix.isUnits_det_units b).mul hA'`. Establish `hB'' : IsUnit B''.det`. Rewrite using `[hB''def, Matrix.det_mul]`. Conclude with `hB'.mul (Matrix.isUnits_det_units c)`.

Establish `hkey : ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), A' * (b.val * Y * (c.val)ᵀ) * B'ᵀ = A'' * Y * B''ᵀ`. Introduce `Y`. Simplify using `only [hA''def, hB''def, Matrix.transpose_mul, Matrix.mul_assoc]`. Establish `hc1 : (c.val)ᵀ * ((c⁻¹).val)ᵀ = 1`. Rewrite using `[← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]`.

Establish `hb1 : (b⁻¹).val * b.val = 1` using `Units.inv_mul b`. Establish `hcoY : ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), (b⁻¹).val * (b.val * Y * (c.val)ᵀ) * ((c⁻¹).val)ᵀ = Y`. Introduce `Y`. Simplify using `only [Matrix.mul_assoc, hc1, Matrix.mul_one]`. Rewrite using `[← Matrix.mul_assoc, hb1, Matrix.one_mul]`.

Set `Lm : (Matrix (Fin n) (Fin d) (Fv F v) →ₗ[Fv F v] Fv F v) → Matrix (Fin n) (Fin d) (Fv F v)` to `fun l => Matrix.of fun k j => l (Matrix.single k j 1)`. Establish `hchar : ∀ (l : Matrix (Fin n) (Fin d) (Fv F v) →ₗ[Fv F v] Fv F v) (Y : Matrix (Fin n) (Fin d) (Fv F v)), -(∑ k, ∑ j, (-(A'' * Y * B''ᵀ)) k j * ((A''ᵀ)⁻¹ * Lm l * B''⁻¹) k j) = l Y`. Introduce `l Y`. Simplify using `only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg]`. Rewrite using `[GlobalTheory.ShapeUV.sum_conj_mul, GlobalTheory.ShapeUV.linForm_sum l Y]`.

Establish `e : A''ᵀ * ((A''ᵀ)⁻¹ * Lm l * B''⁻¹) * B'' = Lm l`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[Matrix.nonsing_inv_mul _ hB'', Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hA'']`. Rewrite using `[e]`. Both sides reduce to the same expression.

Use `set gt := (mat g).map (piW t) with hgt`. Use `set gti := (mat g⁻¹).map (piW t) with hgti`. Establish `hmatinv : mat g⁻¹ * mat g = 1` using `by simp [mat]`. Establish `hmatinv' : mat g * mat g⁻¹ = 1` using `by simp [mat]`. Establish `hgg : gti * gt = 1`.

Rewrite using `[hgti, hgt, ← Matrix.map_mul, hmatinv, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hU : (mat g)ᵀ * incM F X.J * (mat g).map (cA σ) = incM F X.J` using `g.2`. Establish `hg'val : (locMat t b g).val = (b⁻¹).val * gt * b.val` using `locMat_val t b g`. Establish `hgg' : (locMat t b g).val * ((locMat t b g)⁻¹ : GL (Fin n) (Fv F v)).val = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`.

Establish `hbb : b.val * (b⁻¹).val = 1` using `Units.mul_inv b`. Establish `hco2 : ∀ C : Matrix (Fin n) (Fin d) (Fv F v), (b⁻¹).val * (gt * (b.val * C * (c.val)ᵀ)) * ((c⁻¹).val)ᵀ = (locMat t b g).val * C`. Introduce `C`. Rewrite using `[hg'val]`. Simplify using `only [Matrix.mul_assoc, hc1, Matrix.mul_one]`.

Establish `hgiY : ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), gti * (b.val * ((locMat t b g).val * Y) * (c.val)ᵀ) = b.val * Y * (c.val)ᵀ`. Introduce `Y`. Rewrite using `[hg'val]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc b.val (b⁻¹).val, hbb, Matrix.one_mul, ← Matrix.mul_assoc gti gt, hgg, Matrix.one_mul]`.

Establish `h2lin : ∀ x ∈ SB (Fin n × Fin d → Fv F v), ∀ y ∈ SB (Fin n × Fin d → Fv F v), ∀ c : ℂ, (fun (Y : Matrix (Fin n) (Fin d) (Fv F v)) => ι (A (c • x + y)) ((locMat t b g).val * Y)) = c • (fun (Y : Matrix (Fin n) (Fin d) (Fv F v)) => ι (A x) ((locMat t b g).val * Y)) + (fun (Y : Matri …`. Introduce `x hx y hy c`. Use function extensionality and compare the values at `Y`. Simplify using `only [hlin x hx y hy c, map_add, map_smul, Pi.add_apply, Pi.smul_apply]`. Establish `h2tr : ∀ C : Matrix (Fin n) (Fin d) (Fv F v), ∀ x ∈ SB (Fin n × Fin d → Fv F v), schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (U (b.val * C * (c.val)ᵀ) 0)) x ∈ SB (Fin n × Fin d → Fv F v) ∧ ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac …`.

Introduce `C x hx`. Use `⟨hsb _ x hx, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `Y`. Rewrite using `[hT _ (hUat _ 0) (hU1 _ 0) x hx Y, hU0, hcoY]`. Use function extensionality and compare the values at `Y`.

Establish `h0 : (mat g * U (b.val * C * (c.val)ᵀ) 0).map (piW (t.comp σ)) = 0`. Rewrite using `[Matrix.map_mul, hU1, Matrix.mul_zero]`. Rewrite using `[hcov _ (hUat _ 0) x hx, hT _ (atMul _ _ (hUat _ 0)) h0 (A x) (hASB x hx), Matrix.map_mul, hU0, ← hgt, hco2, Matrix.mul_add]`. Establish `h2mu : ∀ (l : Matrix (Fin n) (Fin d) (Fv F v) →ₗ[Fv F v] Fv F v), ∀ x ∈ SB (Fin n × Fin d → Fv F v), schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (U 0 ((A''ᵀ)⁻¹ * Lm l * B''⁻¹))) x ∈ SB (Fin n × Fin d → Fv F v) ∧ ι (schr (GlobalTheory.LatVac.psiAt B.ψ …`. Introduce `l x hx`.

Use `set P := (A''ᵀ)⁻¹ * Lm l * B''⁻¹ with hP`. Use `⟨hsb _ x hx, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `Y`. Establish `hm` using `hM (U 0 P) (hUat 0 P) (hU0 0 P) x hx (U (b.val * Y * (c.val)ᵀ) 0) (hUat _ 0) (hU1 _ 0)`. Rewrite `hm` using `[hU0, hcoY]`.

Rewrite using `[hm, hsymp _ _ (hUat _ 0) (hU1 _ 0) (hU0 0 P), hU0, hU1, hkey, hchar]`. Use function extensionality and compare the values at `Y`. Establish `h0 : (mat g * U 0 P).map (piW t) = 0`. Rewrite using `[Matrix.map_mul, hU0, Matrix.mul_zero]`. Use `set Z := b.val * ((locMat t b g).val * Y) * (c.val)ᵀ with hZ`.

Establish `hm` using `hM _ (atMul _ _ (hUat 0 P)) h0 (A x) (hASB x hx) (U Z 0) (hUat Z 0) (hU1 Z 0)`. Rewrite `hm` using `[hU0, hZ, hcoY]`. Establish `hx' : symp (cA σ) (-1) (incM F X.J) (incM F W.J) (U Z 0) (mat g * U 0 P) = symp (cA σ) (-1) (incM F X.J) (incM F W.J) (mat g⁻¹ * U Z 0) (U 0 P)` using `by conv_lhs => rw [show U Z 0 = mat g * (mat g⁻¹ * U Z 0) by`. Rewrite using `[← Matrix.mul_assoc, hmatinv', Matrix.one_mul]]`. Conclude with `GlobalTheory.ShapeUV.symp_mul_mul _ _ _ _ _ hU _ _`.

Establish `h1 : (mat g⁻¹ * U Z 0).map (piW (t.comp σ)) = 0`. Rewrite using `[Matrix.map_mul, hU1, Matrix.mul_zero]`. Establish `h2 : (mat g⁻¹ * U Z 0).map (piW t) = b.val * Y * (c.val)ᵀ`. Rewrite using `[Matrix.map_mul, hU0, ← hgti, hZ, hgiY]`. Rewrite using `[hcov _ (hUat 0 P) x hx, hm, hx', hsymp _ _ (atMul _ _ (hUat Z 0)) h1 (hU0 0 P), h2, hU1, hkey, hchar]`.

Take `⟨κ₀, hc⟩` from `GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (SB (Fin n × Fin d → Fv F v)) (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1 ι (fun φ (Y : Matrix (Fin n) (Fin d) (Fv F v)) => ι (A φ) ((locMat t b g).val * Y)) hL.bij h2lin _ _ h2tr h2mu`. Use `⟨κ₀, fun φ hφ φ₁ hφ₁ hact1 => ?_⟩` and prove the remaining obligations. Rewrite using `[huniq φ hφ φ₁ hφ₁ hact1]`. Use function extensionality and compare the values at `Y`. Establish `e` using `congrFun (hc φ hφ) (((locMat t b g)⁻¹ : GL (Fin n) (Fv F v)).val * Y)`.

Simplify using `only [Pi.smul_apply, smul_eq_mul] at e ⊢`. Rewrite `e` using `[← Matrix.mul_assoc, hgg', Matrix.one_mul]`. Conclude with `e`.
-/
theorem shapeX : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∃ κ : UA σ X.J → ℂ, ∀ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = κ g • fun Y => ι φ (((locMat t b g)⁻¹ : GL (Fin n) (Fv F v)).val * Y) := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v t b c ι hι
  suffices H : ∀ g ∈ UAt σ X (evFin F v), ∃ κ₀ : ℂ, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = κ₀ • fun Y => ι φ (((locMat t b g)⁻¹ : GL (Fin n) (Fv F v)).val * Y) by
    classical
    refine ⟨fun g => if hg : g ∈ UAt σ X (evFin F v) then (H g hg).choose else 0, fun g hg => ?_⟩
    simp only [dif_pos hg]
    exact (H g hg).choose_spec
  intro g hg
  have hcm : IsCMExt F E σ := hP.base.cm
  have hstd := hP.base.std
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt _ hstd.1 v
  have hψ1 : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one _ hstd v
  have hSplit := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hP.weil
  have hAE := (GlobalTheory.T.theta_action_exists hPr) F E σ B n d X W M χX χW om r s r' s' hP v
  have h1W : (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := by
    intro u _
    simp [mat]

  have hex : ∀ φ : (Fin n × Fin d → Fv F v) → ℂ, ∃ φ₁ : (Fin n × Fin d → Fv F v) → ℂ,
      φ ∈ SB (Fin n × Fin d → Fv F v) → φ₁ ∈ SB (Fin n × Fin d → Fv F v) ∧
        Acts (evFin F v) (om (g, 1)) φ φ₁ := by
    intro φ
    by_cases hφ : φ ∈ SB (Fin n × Fin d → Fv F v)
    · obtain ⟨φ₁, h, -⟩ := hAE.1 g hg 1 h1W φ hφ
      exact ⟨φ₁, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hφ⟩
  choose A hA using hex
  have huniq : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → φ₁ = A φ := fun φ hφ φ₁ hφ₁ h =>
    (hAE.1 g hg 1 h1W φ hφ).unique ⟨hφ₁, h⟩ (hA φ hφ)
  have hASB : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), A φ ∈ SB (Fin n × Fin d → Fv F v) :=
    fun φ hφ => (hA φ hφ).1
  have restA : ∀ φ r, φ ∈ SB (Fin n × Fin d → Fv F v) → Rest (evFin F v) φ r → Rest (evFin F v) (A φ) r :=
    fun φ r hφ hr => ⟨hr.1, by rw [← (hA φ hφ).2 r hr]; exact hSplit.pres _ _ hr.2⟩

  have hvac := hP.good.vac v
  have hlin : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ' ∈ SB (Fin n × Fin d → Fv F v), ∀ c : ℂ,
      A (c • φ + φ') = c • A φ + A φ' := by
    intro φ hφ φ' hφ' c
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v (M.vac v) _ _ hvac.1 fun r hr => ?_
    have hsum : c • φ + φ' ∈ SB (Fin n × Fin d → Fv F v) :=
      Submodule.add_mem _ (Submodule.smul_mem _ c hφ) hφ'
    have r0 := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hsum hr
    have r1 := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hφ hr
    have r2 := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hφ' hr
    have et : ∀ (ψ₁ ψ₂ : (Fin n × Fin d → Fv F v) → ℂ), tens (evFin F v) (c • ψ₁ + ψ₂) r =
        c • tens (evFin F v) ψ₁ r + tens (evFin F v) ψ₂ r := fun ψ₁ ψ₂ => by
      funext x; simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [← (hA _ hsum).2 r r0, et, map_add, map_smul, (hA φ hφ).2 r r1, (hA φ' hφ').2 r r2, et]

  have hact : ∀ γ : Matrix (Fin n) (Fin d) (AE F E),
      actAB (cA σ) (g, (1 : UA σ W.J)) γ = mat g * γ := by
    intro γ
    simp [actAB, mat]
  have atMul : ∀ (P : Matrix (Fin n) (Fin n) (AE F E)) (γ : Matrix (Fin n) (Fin d) (AE F E)),
      At (evFin F v) γ → At (evFin F v) (P * γ) := by
    intro P γ hγ u hu
    rw [← Matrix.mul_smul, hγ u hu, Matrix.mul_zero]
  have hcov : ∀ γ : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) γ →
      ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
        A (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v γ) φ) =
          schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (mat g * γ)) (A φ) := by
    intro γ hγ φ hφ
    have hw := GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v (GlobalTheory.LatVac.locCo M.co v γ) φ hφ
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_
    have hb1 := GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ hγ φ r hr
    have hRw : Rest (evFin F v) (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v γ) φ) r :=
      ⟨hr.1, by rw [← hb1]; exact GlobalTheory.T.weil_representation_preserves_schwartz M B.ψ hstd γ _ hr.2⟩
    rw [← (hA _ hw).2 r hRw, ← hb1, hSplit.impl _ _ _ hr.2, (hA φ hφ).2 r hr, hact,
      GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v _ (atMul _ γ hγ) (A φ) r (restA φ r hφ hr)]

  have hL := hι
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLinW at hL
  have hsb : ∀ (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) (φ : (Fin n × Fin d → Fv F v) → ℂ),
      φ ∈ SB (Fin n × Fin d → Fv F v) → schr (GlobalTheory.LatVac.psiAt B.ψ v) w φ ∈ SB (Fin n × Fin d → Fv F v) :=
    fun w φ hφ => GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v w φ hφ
  have hT : ∀ γ : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) γ → γ.map (piW (t.comp σ)) = 0 →
      ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ Y,
        ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v γ) φ) Y =
          ι φ (Y + (b⁻¹).val * γ.map (piW t) * ((c⁻¹).val)ᵀ) :=
    fun γ hγ h0 φ hφ Y => hL.trans γ hγ h0 φ hφ _ (hsb _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ hγ φ) Y
  have hM : ∀ γ : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) γ → γ.map (piW t) = 0 →
      ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ x : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x →
        x.map (piW (t.comp σ)) = 0 →
        ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v γ) φ) ((b⁻¹).val * x.map (piW t) * ((c⁻¹).val)ᵀ) =
          B.ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) x γ) * ι φ ((b⁻¹).val * x.map (piW t) * ((c⁻¹).val)ᵀ) :=
    fun γ hγ h0 φ hφ x hx hx0 =>
      hL.mult γ hγ h0 φ hφ _ (hsb _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ hγ φ) x hx hx0

  choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin n) (Fin d) (Fv F v)) => GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm v t P₀ P₁

  set A' := X.J.map (t.comp σ) with hA'def
  set B' := W.J.map (t.comp σ) with hB'def
  have hsymp : ∀ x u : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x → x.map (piW (t.comp σ)) = 0 →
      u.map (piW t) = 0 →
      B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) x u) =
        GlobalTheory.LatVac.psiAt B.ψ v (-(∑ k, ∑ l, (-(A' * x.map (piW t) * B'ᵀ)) k l * u.map (piW (t.comp σ)) k l)) := by
    intro x u hx hx0 hu1
    have hu1' : u.map (piW ((t.comp σ).comp σ)) = 0 := by rw [comp_conj_conj hcm]; exact hu1
    have e := GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm (t.comp σ) X.J W.J hP.herm.herm hP.skew.skew x u hx0 hu1'
    rw [comp_conj_conj hcm] at e
    unfold symp
    rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v (t.comp σ) _ (GlobalTheory.ShapeUV.at_neg_hTens _ _ x u hx), comp_conj_conj hcm]
    rw [map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add, e]
    rfl

  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdV : X.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hP.herm.sig w)
    have e : (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det := (RingHom.map_det _ _).symm
    rw [e, h0, map_zero]
  have hdW : W.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hP.skew.sig w)
    have e : (W.J.map (B.emb w).1).det = (B.emb w).1 W.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero]
  have hA' : IsUnit A'ᵀ.det := by
    have e : A'.det = ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) X.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_transpose, e]
    exact isUnit_iff_ne_zero.2 fun h =>
      hdV (((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v).injective (by rw [map_zero]; exact h))
  have hB' : IsUnit B'.det := by
    have e : B'.det = ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) W.J.det := (RingHom.map_det _ _).symm
    rw [e]
    exact isUnit_iff_ne_zero.2 fun h =>
      hdW (((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v).injective (by rw [map_zero]; exact h))

  set A'' := A' * b.val with hA''def
  set B'' := B' * c.val with hB''def
  have hA'' : IsUnit A''ᵀ.det := by
    rw [hA''def, Matrix.transpose_mul, Matrix.det_mul, Matrix.det_transpose]
    exact (Matrix.isUnits_det_units b).mul hA'
  have hB'' : IsUnit B''.det := by
    rw [hB''def, Matrix.det_mul]
    exact hB'.mul (Matrix.isUnits_det_units c)
  have hkey : ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), A' * (b.val * Y * (c.val)ᵀ) * B'ᵀ = A'' * Y * B''ᵀ := by
    intro Y
    simp only [hA''def, hB''def, Matrix.transpose_mul, Matrix.mul_assoc]
  have hc1 : (c.val)ᵀ * ((c⁻¹).val)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  have hb1 : (b⁻¹).val * b.val = 1 := Units.inv_mul b
  have hcoY : ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), (b⁻¹).val * (b.val * Y * (c.val)ᵀ) * ((c⁻¹).val)ᵀ = Y := by
    intro Y
    simp only [Matrix.mul_assoc, hc1, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hb1, Matrix.one_mul]
  let Lm : (Matrix (Fin n) (Fin d) (Fv F v) →ₗ[Fv F v] Fv F v) → Matrix (Fin n) (Fin d) (Fv F v) :=
    fun l => Matrix.of fun k j => l (Matrix.single k j 1)
  have hchar : ∀ (l : Matrix (Fin n) (Fin d) (Fv F v) →ₗ[Fv F v] Fv F v) (Y : Matrix (Fin n) (Fin d) (Fv F v)),
      -(∑ k, ∑ j, (-(A'' * Y * B''ᵀ)) k j * ((A''ᵀ)⁻¹ * Lm l * B''⁻¹) k j) = l Y := by
    intro l Y
    simp only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg]
    rw [GlobalTheory.ShapeUV.sum_conj_mul, GlobalTheory.ShapeUV.linForm_sum l Y]
    have e : A''ᵀ * ((A''ᵀ)⁻¹ * Lm l * B''⁻¹) * B'' = Lm l := by
      simp only [Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul _ hB'', Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hA'']
    rw [e]
    rfl

  set gt := (mat g).map (piW t) with hgt
  set gti := (mat g⁻¹).map (piW t) with hgti
  have hmatinv : mat g⁻¹ * mat g = 1 := by simp [mat]
  have hmatinv' : mat g * mat g⁻¹ = 1 := by simp [mat]
  have hgg : gti * gt = 1 := by
    rw [hgti, hgt, ← Matrix.map_mul, hmatinv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hU : (mat g)ᵀ * incM F X.J * (mat g).map (cA σ) = incM F X.J := g.2
  have hg'val : (locMat t b g).val = (b⁻¹).val * gt * b.val := locMat_val t b g
  have hgg' : (locMat t b g).val * ((locMat t b g)⁻¹ : GL (Fin n) (Fv F v)).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hbb : b.val * (b⁻¹).val = 1 := Units.mul_inv b
  have hco2 : ∀ C : Matrix (Fin n) (Fin d) (Fv F v),
      (b⁻¹).val * (gt * (b.val * C * (c.val)ᵀ)) * ((c⁻¹).val)ᵀ = (locMat t b g).val * C := by
    intro C
    rw [hg'val]
    simp only [Matrix.mul_assoc, hc1, Matrix.mul_one]
  have hgiY : ∀ Y : Matrix (Fin n) (Fin d) (Fv F v),
      gti * (b.val * ((locMat t b g).val * Y) * (c.val)ᵀ) = b.val * Y * (c.val)ᵀ := by
    intro Y
    rw [hg'val]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc b.val (b⁻¹).val, hbb, Matrix.one_mul, ← Matrix.mul_assoc gti gt, hgg, Matrix.one_mul]

  have h2lin : ∀ x ∈ SB (Fin n × Fin d → Fv F v), ∀ y ∈ SB (Fin n × Fin d → Fv F v), ∀ c : ℂ,
      (fun (Y : Matrix (Fin n) (Fin d) (Fv F v)) => ι (A (c • x + y)) ((locMat t b g).val * Y)) =
        c • (fun (Y : Matrix (Fin n) (Fin d) (Fv F v)) => ι (A x) ((locMat t b g).val * Y)) +
          (fun (Y : Matrix (Fin n) (Fin d) (Fv F v)) => ι (A y) ((locMat t b g).val * Y)) := by
    intro x hx y hy c
    funext Y
    simp only [hlin x hx y hy c, map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  have h2tr : ∀ C : Matrix (Fin n) (Fin d) (Fv F v), ∀ x ∈ SB (Fin n × Fin d → Fv F v),
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (U (b.val * C * (c.val)ᵀ) 0)) x ∈ SB (Fin n × Fin d → Fv F v) ∧
      ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (U (b.val * C * (c.val)ᵀ) 0)) x) = (fun Y => ι x (Y + C)) ∧
      (fun (Y : Matrix (Fin n) (Fin d) (Fv F v)) =>
          ι (A (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (U (b.val * C * (c.val)ᵀ) 0)) x))
            ((locMat t b g).val * Y)) =
        fun Y => ι (A x) ((locMat t b g).val * (Y + C)) := by
    intro C x hx
    refine ⟨hsb _ x hx, ?_, ?_⟩
    · funext Y
      rw [hT _ (hUat _ 0) (hU1 _ 0) x hx Y, hU0, hcoY]
    · funext Y
      have h0 : (mat g * U (b.val * C * (c.val)ᵀ) 0).map (piW (t.comp σ)) = 0 := by
        rw [Matrix.map_mul, hU1, Matrix.mul_zero]
      rw [hcov _ (hUat _ 0) x hx, hT _ (atMul _ _ (hUat _ 0)) h0 (A x) (hASB x hx), Matrix.map_mul, hU0,
        ← hgt, hco2, Matrix.mul_add]
  have h2mu : ∀ (l : Matrix (Fin n) (Fin d) (Fv F v) →ₗ[Fv F v] Fv F v), ∀ x ∈ SB (Fin n × Fin d → Fv F v),
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (U 0 ((A''ᵀ)⁻¹ * Lm l * B''⁻¹))) x ∈
        SB (Fin n × Fin d → Fv F v) ∧
      ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (U 0 ((A''ᵀ)⁻¹ * Lm l * B''⁻¹))) x) =
        (fun Y => GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι x Y) ∧
      (fun (Y : Matrix (Fin n) (Fin d) (Fv F v)) =>
          ι (A (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (U 0 ((A''ᵀ)⁻¹ * Lm l * B''⁻¹))) x))
            ((locMat t b g).val * Y)) =
        fun Y => GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι (A x) ((locMat t b g).val * Y) := by
    intro l x hx
    set P := (A''ᵀ)⁻¹ * Lm l * B''⁻¹ with hP
    refine ⟨hsb _ x hx, ?_, ?_⟩
    · funext Y
      have hm := hM (U 0 P) (hUat 0 P) (hU0 0 P) x hx (U (b.val * Y * (c.val)ᵀ) 0) (hUat _ 0) (hU1 _ 0)
      rw [hU0, hcoY] at hm
      rw [hm, hsymp _ _ (hUat _ 0) (hU1 _ 0) (hU0 0 P), hU0, hU1, hkey, hchar]
    · funext Y
      have h0 : (mat g * U 0 P).map (piW t) = 0 := by
        rw [Matrix.map_mul, hU0, Matrix.mul_zero]
      set Z := b.val * ((locMat t b g).val * Y) * (c.val)ᵀ with hZ
      have hm := hM _ (atMul _ _ (hUat 0 P)) h0 (A x) (hASB x hx) (U Z 0) (hUat Z 0) (hU1 Z 0)
      rw [hU0, hZ, hcoY] at hm
      have hx' : symp (cA σ) (-1) (incM F X.J) (incM F W.J) (U Z 0) (mat g * U 0 P) =
          symp (cA σ) (-1) (incM F X.J) (incM F W.J) (mat g⁻¹ * U Z 0) (U 0 P) := by
        conv_lhs => rw [show U Z 0 = mat g * (mat g⁻¹ * U Z 0) by
          rw [← Matrix.mul_assoc, hmatinv', Matrix.one_mul]]
        exact GlobalTheory.ShapeUV.symp_mul_mul _ _ _ _ _ hU _ _
      have h1 : (mat g⁻¹ * U Z 0).map (piW (t.comp σ)) = 0 := by
        rw [Matrix.map_mul, hU1, Matrix.mul_zero]
      have h2 : (mat g⁻¹ * U Z 0).map (piW t) = b.val * Y * (c.val)ᵀ := by
        rw [Matrix.map_mul, hU0, ← hgti, hZ, hgiY]
      rw [hcov _ (hUat 0 P) x hx, hm, hx', hsymp _ _ (atMul _ _ (hUat Z 0)) h1 (hU0 0 P), h2, hU1, hkey, hchar]
  obtain ⟨κ₀, hc⟩ := GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (SB (Fin n × Fin d → Fv F v)) (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1 ι
    (fun φ (Y : Matrix (Fin n) (Fin d) (Fv F v)) => ι (A φ) ((locMat t b g).val * Y)) hL.bij h2lin _ _ h2tr h2mu
  refine ⟨κ₀, fun φ hφ φ₁ hφ₁ hact1 => ?_⟩
  rw [huniq φ hφ φ₁ hφ₁ hact1]
  funext Y
  have e := congrFun (hc φ hφ) (((locMat t b g)⁻¹ : GL (Fin n) (Fv F v)).val * Y)
  simp only [Pi.smul_apply, smul_eq_mul] at e ⊢
  rw [← Matrix.mul_assoc, hgg', Matrix.one_mul] at e
  exact e

end GlobalTheory.ShapeUXBas

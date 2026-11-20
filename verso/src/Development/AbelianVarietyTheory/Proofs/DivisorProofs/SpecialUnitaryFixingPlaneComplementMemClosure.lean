import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationQuaternionNormOneSplitStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalAnisotropicPairPlaneMatricesFactsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixFixesLowRankProjectorOfFixesRationalKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFixingKernelEqOneAddLowRankOfUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuaternionMatrixEqOfUnitaryDetOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOneAddLowRankEmbeddingQuaternionMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegInvRatioIsNormOfNegRatioIsNormStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

namespace GlobalTheory.PlaneSU

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ S₁ S₂ ε hε hS e₁ e₂ h12 h11 h22 ⟨t, ht⟩ g hg hfix`. Take `⟨hσσ, hfixF⟩` from `GlobalTheory.CMConjInvol.cm_conj_invol_fixed F E σ hCM`. Take `⟨hs1, hs2, hBA₀, h1₀, h2₀, hker⟩` from `GlobalTheory.T.orthogonalAnisotropicPair_planeMatrices_facts F E σ hσσ M J hJ e₁ e₂ h12 h11 h22`. Take `⟨f₁, hf₁⟩` from `hfixF _ hs1`. Take `⟨f₂, hf₂⟩` from `hfixF _ hs2`.

Establish `hf₁0 : f₁ ≠ 0` using `by rintro rfl; exact h11 (by rw [← hf₁, map_zero])`. Establish `hf₂0 : f₂ ≠ 0` using `by rintro rfl; exact h22 (by rw [← hf₂, map_zero])`. Take `⟨δ, bs, hδ, hb0, hb1, hbb⟩` from `GlobalTheory.QuadNormBase.exists_basis F E σ hCM.2.2.1 hσσ (GlobalTheory.HermLineZeros.exists_conj_ne hCM)`. Establish `hδ0 : δ ≠ 0` using `by rintro rfl; exact hδ ⟨0, by simp⟩`. Establish `hbq0 : -(f₂ / f₁) ≠ 0` using `neg_ne_zero.2 (div_ne_zero hf₂0 hf₁0)`.

Set `ιR : E →+* AF F ⊗[F] E` to `inclR (F := F) (AF F)`. Set `ι : AF F →+* AF F ⊗[F] E` to `algebraMap (AF F) (AF F ⊗[F] E)`. Set `c : AF F ⊗[F] E →+* AF F ⊗[F] E` to `sigR (AF F) σ`. Set `θ : AF F ⊗[F] E` to `(1 : AF F) ⊗ₜ[F] bs 1`. Set `A` to `(planeA e₁ e₂).map ιR`.

Set `B` to `(planeB σ J e₁ e₂).map ιR`. Set `H` to `(planeH σ J e₁ e₂).map ιR`. Establish `hιR : ∀ r : F, ιR (algebraMap F E r) = algebraMap F (AF F ⊗[F] E) r` using `fun r => (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E).commutes r`. Establish `hιF : ∀ r : F, ι (algebraMap F (AF F) r) = algebraMap F (AF F ⊗[F] E) r` using `fun r => (IsScalarTower.algebraMap_apply F (AF F) (AF F ⊗[F] E) r).symm`. Establish `hcR : ∀ x : E, c (ιR x) = ιR (σ x)` using `fun x => by simp [c, ιR, sigR, inclR]`.

Establish `hcι : ∀ s : AF F, c (ι s) = ι s` using `StrongApprox.sigR_algebraMap σ`. Establish `hcc : ∀ x, c (c x) = x`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul r y => simp [c, sigR, hσσ]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Establish `hcT : ∀ {m p : Type} (P : Matrix m p E), Formalism.UG.cT c (P.map ιR) = (Formalism.UG.cT (σ : E →+* E) P).map ιR`. Introduce `m p P`. Use extensionality with `i j`.

Simplify using `[Formalism.UG.cT, hcR]`. Establish `hBA : B * A = 1`. Simplify using `only [B, A]`. Rewrite using `[← Matrix.map_mul, hBA₀, Matrix.map_one _ (map_zero ιR) (map_one ιR)]`. Establish `h1 : Formalism.UG.cT c A * J.map ιR = H * B`.

Simplify using `only [A, B, H]`. Rewrite using `[hcT, ← Matrix.map_mul, h1₀, Matrix.map_mul]`. Establish `h2 : J.map ιR * A = Formalism.UG.cT c B * H`. Simplify using `only [A, B, H]`. Rewrite using `[hcT, ← Matrix.map_mul, h2₀, Matrix.map_mul]`.

Establish `hH : H = Matrix.diagonal ![algebraMap F (AF F ⊗[F] E) f₁, algebraMap F (AF F ⊗[F] E) f₂]`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [H, planeH, ← hf₁, ← hf₂, hιR]`. Establish `hJu : IsUnit (J.map ιR).det`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `(IsUnit.mk0 _ hJ.2).map _`.

Establish `hθ : θ * θ = ι (algebraMap F (AF F) δ)`. Rewrite using `[hιF, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hbb]`. Conclude with `(hιR δ)`. Establish `hcθ : c θ = -θ` using `by simp [c, θ, sigR, hb1, TensorProduct.tmul_neg]`. Establish `hbH : ι (algebraMap F (AF F) (-(f₂ / f₁))) * algebraMap F (AF F ⊗[F] E) f₁ = -algebraMap F (AF F ⊗[F] E) f₂`.

Rewrite using `[hιF, ← map_mul, ← map_neg]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Establish `hιinj : Function.Injective ι` using `Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective`. Use `set G : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) := ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) with hGdef`.

Establish `hGu : Formalism.UG.cT c G * J.map ιR * G = J.map ιR` using `((show HR (AF F) σ J from g).2)`. Establish `hfixM : G * (1 - A * B) = 1 - A * B` using `GlobalTheory.T.matrix_fixes_lowRankProjector_of_fixes_rationalKernel F E (AF F) M _ _ hBA₀ G (fun v hv => hfix v ((hker v).1 hv).1 ((hker v).1 hv).2)`. Take `⟨hGemb, hXu⟩` from `GlobalTheory.T.unitary_fixing_kernel_eq_oneAddLowRank_of_unitary _ c hcc M (J.map ιR) hJu A B H hBA h1 h2 G hGu hfixM`. Establish `hdetX : (B * G * A).det = 1`. Rewrite using `[← det_emb hBA, ← hGemb]`.

Conclude with `StrongApprox.mem_SUAdelic.1 hg`. Take `⟨x, hxX⟩` from `GlobalTheory.T.exists_quaternionMatrix_eq_of_unitary_det_one F E σ δ bs hb0 hb1 hbb f₁ f₂ hf₁0 hf₂0 (AF F) (B * G * A) (hH ▸ hXu) hdetX`. Establish `hx1 : nrm x = 1`. Apply `hιinj` to reduce the goal to its premises. Rewrite using `[map_one, ← det_qm ι θ hθ, hxX, hdetX]`.

Establish `hpq : ∃ p q : AF F, ε * (algebraMap F (AF F) (-(f₂ / f₁)) - (p ^ 2 - algebraMap F (AF F) δ * q ^ 2)) = 0`. Use `GlobalTheory.T.neg_inv_ratio_isNorm_of_neg_ratio_isNorm F E σ δ bs hb0 hb1 hbb f₁ f₂ hf₁0 hf₂0 (AF F) ε t ?_` and prove the remaining obligations. Establish `e : inclR (F` using `F) (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂) = algebraMap F (AF F ⊗[F] E) (f₁ / f₂) := by`. Rewrite using `[← hf₁, ← hf₂, ← map_div₀]`. Conclude with `hιR _`.

Rewrite using `[← e]`. Conclude with `ht`. Establish `hxcl : x ∈ closure (H0 (a` using `δ) (b := -(f₂ / f₁)) ε) := GlobalTheory.T.strongApproximation_quaternion_normOne_split F δ (-(f₂ / f₁)) hδ0 hbq0 S₁ S₂ ε hε hS hpq x hx1`. Establish `hunit : ∀ y : DA F δ (-(f₂ / f₁)), nrm y = 1 → Formalism.UG.cT c (emb A B (qm ι θ y)) * J.map ιR * emb A B (qm ι θ y) = J.map ιR`. Introduce `y hy`.

Use `emb_unitary c hBA h1 h2 ?_` and prove the remaining obligations. Rewrite using `[hH]`. Conclude with `qm_unitary ι θ c hcι hcθ hθ hbH hy`. Establish `hdet : ∀ y : DA F δ (-(f₂ / f₁)), nrm y = 1 → (emb A B (qm ι θ y)).det = 1`. Introduce `y hy`.

Rewrite using `[det_emb hBA, det_qm ι θ hθ, hy, map_one]`. Set `Φ : {y : DA F δ (-(f₂ / f₁)) // nrm y = 1} → HA (AF F) σ J` to `fun y => (⟨Matrix.GeneralLinearGroup.mk'' (emb A B (qm ι θ y.1)) (by rw [hdet y.1 y.2]; exact isUnit_one), hunit y.1 y.2⟩ : HR (AF F) σ J)`. Establish `hΦmat : ∀ y, ((HA.mat (AF F) σ J (Φ y)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) = emb A B (qm ι θ y.1)` using `fun y => rfl`. Establish `hco : ∀ i, Continuous fun y : DA F δ (-(f₂ / f₁)) => coords y i` using `fun i => (continuous_apply i).comp continuous_induced_dom`. Establish `hstar : Continuous (star : DA F δ (-(f₂ / f₁)) → DA F δ (-(f₂ / f₁)))`.

Use `continuous_induced_rng.2 (continuous_pi fun i => ?_)` and prove the remaining obligations. Use `fin_cases i`. Simplify `hco 0` using `[coords]`. Conclude with `((hco 1).neg).congr fun y => by simp [coords]`. Conclude with `((hco 2).neg).congr fun y => by simp [coords]`.

Conclude with `((hco 3).neg).congr fun y => by simp [coords]`. Establish `hE0` using `GlobalTheory.T.continuous_oneAddLowRankEmbedding_quaternionMatrix F E δ (-(f₂ / f₁)) M A B θ`. Establish `hnstar : ∀ y : {y : DA F δ (-(f₂ / f₁)) // nrm y = 1}, nrm (star y.1) = 1` using `fun y => by`. Combine the equalities or inequalities in the displayed calculation. Establish `hinv : ∀ y, ((Φ y)⁻¹ : HA (AF F) σ J) = Φ ⟨star y.1, hnstar y⟩`.

Introduce `y`. Use `inv_eq_of_mul_eq_one_right ?_` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `emb A B (qm ι θ y.1) * emb A B (qm ι θ (star y.1)) = 1`.

Rewrite using `[← emb_mul hBA, ← qm_mul ι θ hθ, mul_star_eq, y.2, map_one, qm_one, emb_one]`. Establish `hΦc : Continuous Φ`. Establish `hU : Continuous fun y : {y : DA F δ (-(f₂ / f₁)) // nrm y = 1} => (Φ y : HR (AF F) σ J).1`. Use `Units.continuous_iff.2 ⟨hE0.comp continuous_subtype_val, ?_⟩` and prove the remaining obligations. Establish `e : (fun y : {y : DA F δ (-(f₂ / f₁)) // nrm y = 1} => ((((Φ y : HR (AF F) σ J).1)⁻¹ : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) = fun y => emb A B (qm ι θ (star y.1))`.

Use function extensionality and compare the values at `y`. Use `congrArg (fun z : HA (AF F) σ J => (((z : HR (AF F) σ J).1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) (hinv y)` as an intermediate fact. Conclude with `this`. Rewrite using `[e]`. Conclude with `hE0.comp (hstar.comp continuous_subtype_val)`.

Conclude with `continuous_induced_rng.2 hU`. Establish `hg_eq : g = Φ ⟨x, hx1⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `G = emb A B (qm ι θ x)`.

Rewrite using `[hxX]`. Conclude with `hGemb`. Establish `hH0N : H0 (a` using `δ) (b := -(f₂ / f₁)) ε ⊆ {y | nrm y = 1} := by`. Introduce and unpack `_ ⟨γ, hγ, h, hh, -, rfl⟩`. Simplify using `[nrm_mul, nrm_rat, hγ, hh]`.

Establish `hx' : (⟨x, hx1⟩ : {y : DA F δ (-(f₂ / f₁)) // nrm y = 1}) ∈ closure (Subtype.val ⁻¹' H0 ε)`. Rewrite using `[closure_subtype, Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype, Set.inter_eq_left.2 hH0N]`. Conclude with `hxcl`. Establish `hsub : Φ '' (Subtype.val ⁻¹' H0 ε) ⊆ {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}`. Introduce and unpack `_ ⟨⟨y, hy1⟩, ⟨γ, hγ, h, hh, hεh, hy⟩, rfl⟩`.

Establish `hγ1 : nrm (rat γ) = 1` using `by rw [nrm_rat, hγ, map_one]`. Use `⟨Φ ⟨rat γ, hγ1⟩, ?_, Φ ⟨h, hh⟩, ?_, ?_⟩` and prove the remaining obligations. Use `⟨StrongApprox.mem_SUAdelic.2 (hdet _ hγ1), ?_⟩ show HA.mat (AF F) σ J (Φ ⟨rat γ, hγ1⟩) ∈ HFin (AF F) σ J` and prove the remaining obligations. Establish `hbE : algebraMap F E (-(f₂ / f₁)) * hE σ J e₁ e₁ = -hE σ J e₂ e₂`. Rewrite using `[← hf₁, ← hf₂, ← map_mul, ← map_neg]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Establish `hdE : IsUnit (emb (planeA e₁ e₂) (planeB σ J e₁ e₂) (qm (algebraMap F E) (bs 1) γ)).det`. Rewrite using `[det_emb hBA₀, det_qm _ _ hbb, hγ, map_one]`. Conclude with `isUnit_one`.

Establish `huE : Formalism.UG.cT (σ : E →+* E) (emb (planeA e₁ e₂) (planeB σ J e₁ e₂) (qm (algebraMap F E) (bs 1) γ)) * J * emb (planeA e₁ e₂) (planeB σ J e₁ e₂) (qm (algebraMap F E) (bs 1) γ) = J` using `emb_unitary (σ : E →+* E) hBA₀ h1₀ h2₀ (qm_unitary (algebraMap F E) (bs 1) (σ : E →+* E) (fun s => σ.commutes s) hb1 hbb hbE hγ)`. Use `⟨Matrix.GeneralLinearGroup.mk'' _ hdE, huE, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(emb (planeA e₁ e₂) (planeB σ J e₁ e₂) (qm (algebraMap F E) (bs 1) γ)).map ιR = emb A B (qm ι θ (rat γ))`. Rewrite using `[emb_map]`.

Use `congr 1`. Establish `hcomp : ιR.comp (algebraMap F E) = ι.comp (algebraMap F (AF F))` using `RingHom.ext fun r => (hιR r).trans (hιF r).symm`. Establish `e1 : (qm (algebraMap F E) (bs 1) γ).map ιR = qm (ιR.comp (algebraMap F E)) (ιR (bs 1)) γ`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [qm]`. Rewrite using `[e1, hcomp]`.

Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> rfl`. Use `⟨StrongApprox.mem_SUAdelic.2 (hdet _ hh), fun i j => ?_⟩` and prove the remaining obligations. Establish `hεε : ε * ε = ε`. Establish `h1 : fstA F (ε * ε) = fstA F ε`. Rewrite using `[map_mul]`.

Use function extensionality and compare the values at `w`. Express the relevant statement in the definitionally equal form `fstA F ε w * fstA F ε w = fstA F ε w`. Distinguish the cases in `hw : w ∈ S₁`. Rewrite using `[hε.1 w hw, one_mul]`. Rewrite using `[hε.2.1 w hw, zero_mul]`.

Establish `h2 : sndA F (ε * ε) = sndA F ε`. Rewrite using `[map_mul]`. Use `RestrictedProduct.ext _ _ fun v => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `evalV F v (sndA F ε * sndA F ε) = evalV F v (sndA F ε)`. Rewrite using `[map_mul]`.

Distinguish the cases in `hv : v ∈ S₂`. Rewrite using `[hε.2.2.1 v hv, one_mul]`. Rewrite using `[hε.2.2.2 v hv, zero_mul]`. Conclude with `Prod.ext h1 h2`. Establish `e2 : qm ι θ h - 1 = ι ε • qm ι θ (h - 1)` using `by rw [← qm_smul, hεh, qm_sub, qm_one]`.

Establish `e : emb A B (qm ι θ h) - 1 = ι ε • (A * qm ι θ (h - 1) * B)`. Unfold `emb`. Rewrite using `[add_sub_cancel_left, e2, Matrix.mul_smul, Matrix.smul_mul]`. Express the relevant statement in the definitionally equal form `ι ε * (emb A B (qm ι θ h) - 1) i j = (emb A B (qm ι θ h) - 1) i j`. Rewrite using `[e, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← map_mul, hεε]`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `emb A B (qm ι θ y) = emb A B (qm ι θ (rat γ)) * emb A B (qm ι θ h)`. Rewrite using `[show y = rat γ * h from hy, qm_mul ι θ hθ, emb_mul hBA]`. Rewrite using `[hg_eq]`.

Conclude with `closure_mono hsub (image_closure_subset_closure_image hΦc ⟨_, hx', rfl⟩)`.
-/
theorem plane_closure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → (∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂)) = 0) → ∀ g ∈ SUAdelic σ J, (∀ v : Fin M → E, hE σ J e₁ v = 0 → hE σ J e₂ v = 0 → Matrix.mulVec ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) (fun i => inclR (AF F) (v i)) = (fun i => inclR (AF F) (v i))) → g ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
  intro F E _ _ _ _ _ σ hCM M J hJ S₁ S₂ ε hε hS e₁ e₂ h12 h11 h22 ⟨t, ht⟩ g hg hfix
  obtain ⟨hσσ, hfixF⟩ := GlobalTheory.CMConjInvol.cm_conj_invol_fixed F E σ hCM
  obtain ⟨hs1, hs2, hBA₀, h1₀, h2₀, hker⟩ := GlobalTheory.T.orthogonalAnisotropicPair_planeMatrices_facts F E σ hσσ M J hJ e₁ e₂ h12 h11 h22
  obtain ⟨f₁, hf₁⟩ := hfixF _ hs1
  obtain ⟨f₂, hf₂⟩ := hfixF _ hs2
  have hf₁0 : f₁ ≠ 0 := by rintro rfl; exact h11 (by rw [← hf₁, map_zero])
  have hf₂0 : f₂ ≠ 0 := by rintro rfl; exact h22 (by rw [← hf₂, map_zero])
  obtain ⟨δ, bs, hδ, hb0, hb1, hbb⟩ := GlobalTheory.QuadNormBase.exists_basis F E σ hCM.2.2.1 hσσ
    (GlobalTheory.HermLineZeros.exists_conj_ne hCM)
  have hδ0 : δ ≠ 0 := by rintro rfl; exact hδ ⟨0, by simp⟩
  have hbq0 : -(f₂ / f₁) ≠ 0 := neg_ne_zero.2 (div_ne_zero hf₂0 hf₁0)

  let ιR : E →+* AF F ⊗[F] E := inclR (F := F) (AF F)
  let ι : AF F →+* AF F ⊗[F] E := algebraMap (AF F) (AF F ⊗[F] E)
  let c : AF F ⊗[F] E →+* AF F ⊗[F] E := sigR (AF F) σ
  let θ : AF F ⊗[F] E := (1 : AF F) ⊗ₜ[F] bs 1
  let A := (planeA e₁ e₂).map ιR
  let B := (planeB σ J e₁ e₂).map ιR
  let H := (planeH σ J e₁ e₂).map ιR
  have hιR : ∀ r : F, ιR (algebraMap F E r) = algebraMap F (AF F ⊗[F] E) r := fun r =>
    (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E).commutes r
  have hιF : ∀ r : F, ι (algebraMap F (AF F) r) = algebraMap F (AF F ⊗[F] E) r := fun r =>
    (IsScalarTower.algebraMap_apply F (AF F) (AF F ⊗[F] E) r).symm
  have hcR : ∀ x : E, c (ιR x) = ιR (σ x) := fun x => by simp [c, ιR, sigR, inclR]
  have hcι : ∀ s : AF F, c (ι s) = ι s := StrongApprox.sigR_algebraMap σ
  have hcc : ∀ x, c (c x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r y => simp [c, sigR, hσσ]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hcT : ∀ {m p : Type} (P : Matrix m p E), Formalism.UG.cT c (P.map ιR) = (Formalism.UG.cT (σ : E →+* E) P).map ιR := by
    intro m p P; ext i j; simp [Formalism.UG.cT, hcR]
  have hBA : B * A = 1 := by
    simp only [B, A]; rw [← Matrix.map_mul, hBA₀, Matrix.map_one _ (map_zero ιR) (map_one ιR)]
  have h1 : Formalism.UG.cT c A * J.map ιR = H * B := by
    simp only [A, B, H]; rw [hcT, ← Matrix.map_mul, h1₀, Matrix.map_mul]
  have h2 : J.map ιR * A = Formalism.UG.cT c B * H := by
    simp only [A, B, H]; rw [hcT, ← Matrix.map_mul, h2₀, Matrix.map_mul]
  have hH : H = Matrix.diagonal ![algebraMap F (AF F ⊗[F] E) f₁, algebraMap F (AF F ⊗[F] E) f₂] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [H, planeH, ← hf₁, ← hf₂, hιR]
  have hJu : IsUnit (J.map ιR).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ hJ.2).map _
  have hθ : θ * θ = ι (algebraMap F (AF F) δ) := by
    rw [hιF, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hbb]
    exact (hιR δ)
  have hcθ : c θ = -θ := by simp [c, θ, sigR, hb1, TensorProduct.tmul_neg]
  have hbH : ι (algebraMap F (AF F) (-(f₂ / f₁))) * algebraMap F (AF F ⊗[F] E) f₁ =
      -algebraMap F (AF F ⊗[F] E) f₂ := by
    rw [hιF, ← map_mul, ← map_neg]; congr 1; field_simp
  have hιinj : Function.Injective ι :=
    Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective

  set G : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) := ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))
    with hGdef
  have hGu : Formalism.UG.cT c G * J.map ιR * G = J.map ιR := ((show HR (AF F) σ J from g).2)
  have hfixM : G * (1 - A * B) = 1 - A * B :=
    GlobalTheory.T.matrix_fixes_lowRankProjector_of_fixes_rationalKernel F E (AF F) M _ _ hBA₀ G (fun v hv => hfix v ((hker v).1 hv).1 ((hker v).1 hv).2)
  obtain ⟨hGemb, hXu⟩ := GlobalTheory.T.unitary_fixing_kernel_eq_oneAddLowRank_of_unitary _ c hcc M (J.map ιR) hJu A B H hBA h1 h2 G hGu hfixM
  have hdetX : (B * G * A).det = 1 := by
    rw [← det_emb hBA, ← hGemb]; exact StrongApprox.mem_SUAdelic.1 hg
  obtain ⟨x, hxX⟩ := GlobalTheory.T.exists_quaternionMatrix_eq_of_unitary_det_one F E σ δ bs hb0 hb1 hbb f₁ f₂ hf₁0 hf₂0 (AF F) (B * G * A) (hH ▸ hXu) hdetX
  have hx1 : nrm x = 1 := by
    apply hιinj
    rw [map_one, ← det_qm ι θ hθ, hxX, hdetX]
  have hpq : ∃ p q : AF F, ε * (algebraMap F (AF F) (-(f₂ / f₁)) - (p ^ 2 - algebraMap F (AF F) δ * q ^ 2)) = 0 := by
    refine GlobalTheory.T.neg_inv_ratio_isNorm_of_neg_ratio_isNorm F E σ δ bs hb0 hb1 hbb f₁ f₂ hf₁0 hf₂0 (AF F) ε t ?_
    have e : inclR (F := F) (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂) = algebraMap F (AF F ⊗[F] E) (f₁ / f₂) := by
      rw [← hf₁, ← hf₂, ← map_div₀]; exact hιR _
    rw [← e]; exact ht
  have hxcl : x ∈ closure (H0 (a := δ) (b := -(f₂ / f₁)) ε) :=
    GlobalTheory.T.strongApproximation_quaternion_normOne_split F δ (-(f₂ / f₁)) hδ0 hbq0 S₁ S₂ ε hε hS hpq x hx1

  have hunit : ∀ y : DA F δ (-(f₂ / f₁)), nrm y = 1 →
      Formalism.UG.cT c (emb A B (qm ι θ y)) * J.map ιR * emb A B (qm ι θ y) = J.map ιR := by
    intro y hy
    refine emb_unitary c hBA h1 h2 ?_
    rw [hH]
    exact qm_unitary ι θ c hcι hcθ hθ hbH hy
  have hdet : ∀ y : DA F δ (-(f₂ / f₁)), nrm y = 1 → (emb A B (qm ι θ y)).det = 1 := by
    intro y hy
    rw [det_emb hBA, det_qm ι θ hθ, hy, map_one]
  let Φ : {y : DA F δ (-(f₂ / f₁)) // nrm y = 1} → HA (AF F) σ J := fun y =>
    (⟨Matrix.GeneralLinearGroup.mk'' (emb A B (qm ι θ y.1)) (by rw [hdet y.1 y.2]; exact isUnit_one),
      hunit y.1 y.2⟩ : HR (AF F) σ J)
  have hΦmat : ∀ y, ((HA.mat (AF F) σ J (Φ y)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) = emb A B (qm ι θ y.1) :=
    fun y => rfl

  have hco : ∀ i, Continuous fun y : DA F δ (-(f₂ / f₁)) => coords y i := fun i =>
    (continuous_apply i).comp continuous_induced_dom
  have hstar : Continuous (star : DA F δ (-(f₂ / f₁)) → DA F δ (-(f₂ / f₁))) := by
    refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
    fin_cases i
    · simpa [coords] using hco 0
    · exact ((hco 1).neg).congr fun y => by simp [coords]
    · exact ((hco 2).neg).congr fun y => by simp [coords]
    · exact ((hco 3).neg).congr fun y => by simp [coords]
  have hE0 := GlobalTheory.T.continuous_oneAddLowRankEmbedding_quaternionMatrix F E δ (-(f₂ / f₁)) M A B θ
  have hnstar : ∀ y : {y : DA F δ (-(f₂ / f₁)) // nrm y = 1}, nrm (star y.1) = 1 := fun y => by
    calc nrm (star y.1) = nrm y.1 := by simp [nrm]
      _ = 1 := y.2
  have hinv : ∀ y, ((Φ y)⁻¹ : HA (AF F) σ J) = Φ ⟨star y.1, hnstar y⟩ := by
    intro y
    refine inv_eq_of_mul_eq_one_right ?_
    apply Subtype.ext; apply Units.ext
    change emb A B (qm ι θ y.1) * emb A B (qm ι θ (star y.1)) = 1
    rw [← emb_mul hBA, ← qm_mul ι θ hθ, mul_star_eq, y.2, map_one, qm_one, emb_one]
  have hΦc : Continuous Φ := by
    have hU : Continuous fun y : {y : DA F δ (-(f₂ / f₁)) // nrm y = 1} => (Φ y : HR (AF F) σ J).1 := by
      refine Units.continuous_iff.2 ⟨hE0.comp continuous_subtype_val, ?_⟩
      have e : (fun y : {y : DA F δ (-(f₂ / f₁)) // nrm y = 1} =>
          ((((Φ y : HR (AF F) σ J).1)⁻¹ : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) =
          fun y => emb A B (qm ι θ (star y.1)) := by
        funext y
        have := congrArg (fun z : HA (AF F) σ J => (((z : HR (AF F) σ J).1 : GL (Fin M) (AF F ⊗[F] E)) :
          Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) (hinv y)
        exact this
      rw [e]
      exact hE0.comp (hstar.comp continuous_subtype_val)
    exact continuous_induced_rng.2 hU
  have hg_eq : g = Φ ⟨x, hx1⟩ := by
    apply Subtype.ext; apply Units.ext
    change G = emb A B (qm ι θ x)
    rw [hxX]; exact hGemb
  have hH0N : H0 (a := δ) (b := -(f₂ / f₁)) ε ⊆ {y | nrm y = 1} := by
    rintro _ ⟨γ, hγ, h, hh, -, rfl⟩
    simp [nrm_mul, nrm_rat, hγ, hh]
  have hx' : (⟨x, hx1⟩ : {y : DA F δ (-(f₂ / f₁)) // nrm y = 1}) ∈ closure (Subtype.val ⁻¹' H0 ε) := by
    rw [closure_subtype, Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype, Set.inter_eq_left.2 hH0N]
    exact hxcl
  have hsub : Φ '' (Subtype.val ⁻¹' H0 ε) ⊆
      {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
    rintro _ ⟨⟨y, hy1⟩, ⟨γ, hγ, h, hh, hεh, hy⟩, rfl⟩
    have hγ1 : nrm (rat γ) = 1 := by rw [nrm_rat, hγ, map_one]
    refine ⟨Φ ⟨rat γ, hγ1⟩, ?_, Φ ⟨h, hh⟩, ?_, ?_⟩
    · refine ⟨StrongApprox.mem_SUAdelic.2 (hdet _ hγ1), ?_⟩
      show HA.mat (AF F) σ J (Φ ⟨rat γ, hγ1⟩) ∈ HFin (AF F) σ J
      have hbE : algebraMap F E (-(f₂ / f₁)) * hE σ J e₁ e₁ = -hE σ J e₂ e₂ := by
        rw [← hf₁, ← hf₂, ← map_mul, ← map_neg]; congr 1; field_simp
      have hdE : IsUnit (emb (planeA e₁ e₂) (planeB σ J e₁ e₂) (qm (algebraMap F E) (bs 1) γ)).det := by
        rw [det_emb hBA₀, det_qm _ _ hbb, hγ, map_one]; exact isUnit_one
      have huE : Formalism.UG.cT (σ : E →+* E) (emb (planeA e₁ e₂) (planeB σ J e₁ e₂) (qm (algebraMap F E) (bs 1) γ)) * J *
          emb (planeA e₁ e₂) (planeB σ J e₁ e₂) (qm (algebraMap F E) (bs 1) γ) = J :=
        emb_unitary (σ : E →+* E) hBA₀ h1₀ h2₀
          (qm_unitary (algebraMap F E) (bs 1) (σ : E →+* E) (fun s => σ.commutes s) hb1 hbb hbE hγ)
      refine ⟨Matrix.GeneralLinearGroup.mk'' _ hdE, huE, ?_⟩
      apply Units.ext
      change (emb (planeA e₁ e₂) (planeB σ J e₁ e₂) (qm (algebraMap F E) (bs 1) γ)).map ιR = emb A B (qm ι θ (rat γ))
      rw [emb_map]
      congr 1
      have hcomp : ιR.comp (algebraMap F E) = ι.comp (algebraMap F (AF F)) :=
        RingHom.ext fun r => (hιR r).trans (hιF r).symm
      have e1 : (qm (algebraMap F E) (bs 1) γ).map ιR = qm (ιR.comp (algebraMap F E)) (ιR (bs 1)) γ := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [qm]
      rw [e1, hcomp]
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    · refine ⟨StrongApprox.mem_SUAdelic.2 (hdet _ hh), fun i j => ?_⟩
      have hεε : ε * ε = ε := by
        have h1 : fstA F (ε * ε) = fstA F ε := by
          rw [map_mul]
          funext w
          change fstA F ε w * fstA F ε w = fstA F ε w
          by_cases hw : w ∈ S₁
          · rw [hε.1 w hw, one_mul]
          · rw [hε.2.1 w hw, zero_mul]
        have h2 : sndA F (ε * ε) = sndA F ε := by
          rw [map_mul]
          refine RestrictedProduct.ext _ _ fun v => ?_
          change evalV F v (sndA F ε * sndA F ε) = evalV F v (sndA F ε)
          rw [map_mul]
          by_cases hv : v ∈ S₂
          · rw [hε.2.2.1 v hv, one_mul]
          · rw [hε.2.2.2 v hv, zero_mul]
        exact Prod.ext h1 h2
      have e2 : qm ι θ h - 1 = ι ε • qm ι θ (h - 1) := by rw [← qm_smul, hεh, qm_sub, qm_one]
      have e : emb A B (qm ι θ h) - 1 = ι ε • (A * qm ι θ (h - 1) * B) := by
        unfold emb; rw [add_sub_cancel_left, e2, Matrix.mul_smul, Matrix.smul_mul]
      change ι ε * (emb A B (qm ι θ h) - 1) i j = (emb A B (qm ι θ h) - 1) i j
      rw [e, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← map_mul, hεε]
    · apply Subtype.ext; apply Units.ext
      change emb A B (qm ι θ y) = emb A B (qm ι θ (rat γ)) * emb A B (qm ι θ h)
      rw [show y = rat γ * h from hy, qm_mul ι θ hθ, emb_mul hBA]
  rw [hg_eq]
  exact closure_mono hsub (image_closure_subset_closure_image hΦc ⟨_, hx', rfl⟩)

end GlobalTheory.PlaneSU

end

import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSubAug

import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalTranslationEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupSurjectsGeneralLinearRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryDeterminedBySplitImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftVOneMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterSmoothUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenKerOfContinuous
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalGoodPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LagrangianDecompositionWeilStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalWeilLinearModelActionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalWeilLinearModelUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalWeilLinearModelInvariantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalWeilLinearModelMeasureStatement

open NumberField IsDedekindDomain

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SplitTransport

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

section Lin

open GlobalTheory.LinWAt
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny

/- English proof (translation)
Take `⟨uT, uM, hT, hM, hspan, hsymp⟩` from `(GlobalTheory.T.local_unipotent_embeddings_exist) F E σ B a a' G X om om' hTr v t`. Establish `hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v)` using `GlobalTheory.VacAny.continuous_psiV hTr.base.std.1 v`. Establish `hψ1 : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1` using `GlobalTheory.PsiNontriv.psiAt_ne_one _ hTr.base.std v`. Establish `hcoT : ∀ Y, coW G t (uT Y) = 0` using `fun Y => coW_eq_zero G t _ (hT Y).2.1`. Use `haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F _).injective`.

Take `⟨ι, hbij, htr, hmu⟩` from `GlobalTheory.T.lagrangian_decomposition_weil (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1 ((GlobalTheory.LatVac.locCo G.M.co v).comp uT) ((GlobalTheory.LatVac.locCo G.M.co v).comp uM) (fun Y Y' => by`. Simplify using `only [AddMonoidHom.comp_apply]`. Rewrite using `[locCo_form, hsymp _ _ (hT Y).1 (hT Y').1, hcoT, hcoT]`. Use the proof step `simp)`. Use the proof step `(fun z z' => by`.

Simplify using `only [AddMonoidHom.comp_apply]`. Rewrite using `[locCo_form, hsymp _ _ (hM z).1 (hM z').1, (hM z).2.1, (hM z').2.1]`. Use the proof step `simp)`. Use the proof step `(fun Y z => by`. Simplify using `only [AddMonoidHom.comp_apply]`.

Rewrite using `[locCo_form, hsymp _ _ (hT Y).1 (hM z).1, (hT Y).2.2, (hM z).2.2, hcoT, (hM z).2.1]`. Use the proof step `simp)`. Use the proof step `(fun w => by`. Take `⟨u, hu, rfl⟩` from `locCo_surj G.M.co v w`. Take `⟨Y, z, rfl⟩` from `hspan u hu`.

Conclude with `⟨Y, z, by simp only [AddMonoidHom.comp_apply, map_add]⟩)`. Establish `hφ₁ : ∀ (u : Matrix (Fin a) (Fin (a + a')) (AE F E)), At (evFin F v) u → ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ₁, Acts (evFin F v) (G.M.co.rho B.ψ u) φ φ₁ → φ₁ = GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v u) φ` using `fun u hu φ hφ φ₁ hact => GlobalTheory.TensUniq.eq_of_tens_eq v φ φ₁ _ hφ fun r hr => (hact r hr).symm.trans (GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v u hu φ r hr)`. Use `⟨ι, hbij, ?_, ?_⟩` and prove the remaining obligations. Introduce `u hu hu0 φ hφ φ₁ _ hact Y`. Establish `e1` using `hφ₁ u hu φ hφ φ₁ hact`.

Take `⟨Y₀, z, rfl⟩` from `hspan u hu`. Establish `hz : z = 0`. Establish `h` using `hu0`. Rewrite `h` using `[Matrix.map_add _ (map_add _), (hT Y₀).2.1, zero_add]`. Rewrite using `[← (hM z).2.2]`.

Conclude with `coW_eq_zero G t _ h`. Substitute `hz` using the available equality. Rewrite `e1`, the goal using `[map_zero, add_zero]`. Rewrite using `[co_one, (hT Y₀).2.2, e1]`. Conclude with `congrFun (htr Y₀ φ hφ) Y`.

Introduce `u hu hu1 φ hφ φ₁ _ hact x hx hx0`. Establish `e1` using `hφ₁ u hu φ hφ φ₁ hact`. Take `⟨Y₀, z, rfl⟩` from `hspan u hu`. Establish `hY : Y₀ = 0`. Establish `h` using `hu1`.

Rewrite `h` using `[Matrix.map_add _ (map_add _), (hM z).2.1, add_zero]`. Rewrite using `[← (hT Y₀).2.2]`. Conclude with `h`. Substitute `hY` using the available equality. Rewrite `e1`, the goal using `[map_zero, zero_add]`.

Rewrite using `[co_one, e1, GlobalTheory.VacIndic.psi_of_at B.ψ (at_symp _ _ _ x (uM z) hx), hsymp x (uM z) hx (hM z).1, coW_eq_zero G t x hx0, (hM z).2.1, (hM z).2.2]`. Establish `h2` using `congrFun (hmu z φ hφ) (x.map (piW t))`. Simplify using `only [AddMonoidHom.comp_apply] at h2`. Rewrite using `[h2, ← GlobalTheory.LatVac.psiAt_apply]`. Use `congr 2`.

Simplify using the standard rewrite rules.
-/
theorem exists_isLinW (hP : GlobalTheory.FunPr.Hypotheses₂) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (hTr : IsTriple B G X om om') (v : Pl F) (t : E →ₐ[F] Fv F v) :
    ∃ ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ),
      G.M.IsLinW B.ψ t 1 1 ι := by
  obtain ⟨uT, uM, hT, hM, hspan, hsymp⟩ := (GlobalTheory.T.local_unipotent_embeddings_exist) F E σ B a a' G X om om' hTr v t
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.VacAny.continuous_psiV hTr.base.std.1 v
  have hψ1 : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one _ hTr.base.std v
  have hcoT : ∀ Y, coW G t (uT Y) = 0 := fun Y => coW_eq_zero G t _ (hT Y).2.1
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F _).injective
  obtain ⟨ι, hbij, htr, hmu⟩ := GlobalTheory.T.lagrangian_decomposition_weil (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1
    ((GlobalTheory.LatVac.locCo G.M.co v).comp uT) ((GlobalTheory.LatVac.locCo G.M.co v).comp uM)
    (fun Y Y' => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form, hsymp _ _ (hT Y).1 (hT Y').1, hcoT, hcoT]
      simp)
    (fun z z' => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form, hsymp _ _ (hM z).1 (hM z').1, (hM z).2.1, (hM z').2.1]
      simp)
    (fun Y z => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form, hsymp _ _ (hT Y).1 (hM z).1, (hT Y).2.2, (hM z).2.2, hcoT, (hM z).2.1]
      simp)
    (fun w => by
      obtain ⟨u, hu, rfl⟩ := locCo_surj G.M.co v w
      obtain ⟨Y, z, rfl⟩ := hspan u hu
      exact ⟨Y, z, by simp only [AddMonoidHom.comp_apply, map_add]⟩)
  have hφ₁ : ∀ (u : Matrix (Fin a) (Fin (a + a')) (AE F E)), At (evFin F v) u →
      ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ₁, Acts (evFin F v) (G.M.co.rho B.ψ u) φ φ₁ →
        φ₁ = GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v u) φ :=
    fun u hu φ hφ φ₁ hact => GlobalTheory.TensUniq.eq_of_tens_eq v φ φ₁ _ hφ fun r hr =>
      (hact r hr).symm.trans (GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v u hu φ r hr)
  refine ⟨ι, hbij, ?_, ?_⟩
  · intro u hu hu0 φ hφ φ₁ _ hact Y
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    obtain ⟨Y₀, z, rfl⟩ := hspan u hu
    have hz : z = 0 := by
      have h := hu0
      rw [Matrix.map_add _ (map_add _), (hT Y₀).2.1, zero_add] at h
      rw [← (hM z).2.2]
      exact coW_eq_zero G t _ h
    subst hz
    rw [map_zero, add_zero] at e1 ⊢
    rw [co_one, (hT Y₀).2.2, e1]
    exact congrFun (htr Y₀ φ hφ) Y
  · intro u hu hu1 φ hφ φ₁ _ hact x hx hx0
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    obtain ⟨Y₀, z, rfl⟩ := hspan u hu
    have hY : Y₀ = 0 := by
      have h := hu1
      rw [Matrix.map_add _ (map_add _), (hM z).2.1, add_zero] at h
      rw [← (hT Y₀).2.2]
      exact h
    subst hY
    rw [map_zero, zero_add] at e1 ⊢
    rw [co_one, e1, GlobalTheory.VacIndic.psi_of_at B.ψ (at_symp _ _ _ x (uM z) hx), hsymp x (uM z) hx (hM z).1,
      coW_eq_zero G t x hx0, (hM z).2.1, (hM z).2.2]
    have h2 := congrFun (hmu z φ hφ) (x.map (piW t))
    simp only [AddMonoidHom.comp_apply] at h2
    rw [h2, ← GlobalTheory.LatVac.psiAt_apply]
    congr 2
    simp

end Lin

section Points

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

/- English proof (translation)
Establish `hcm` using `hTr.base.cm`. Establish `herm : ∀ i j, σ (G.V.J j i) = algebraMap F E 1 * G.V.J i j` using `fun i j => by`. Rewrite using `[map_one, one_mul]`. Conclude with `hTr.geo.hV.herm i j`. Establish `hJ : IsUnit (G.V.J.map t).det`.

Establish `w` using `Classical.arbitrary (InfinitePlace F)`. Conclude with `GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.V.J t (B.emb w).1 1 one_ne_zero (G.V.θ w) (by rw [one_smul]; exact hTr.geo.hV.cartan w)`. Conclude with `⟨_, GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t G.V 1 herm hJ g', GlobalTheory.SplitUnitLift.liftU_piW hcm t G.V.J 1 herm hJ g'⟩`.
-/
theorem surjV (hTr : IsTriple B G X om om') (v : Pl F) (t : E →ₐ[F] Fv F v) (g' : GL (Fin a) (Fv F v)) :
    ∃ g ∈ UAt σ G.V (evFin F v), (mat g).map (piW t) = g'.1 := by
  have hcm := hTr.base.cm
  have herm : ∀ i j, σ (G.V.J j i) = algebraMap F E 1 * G.V.J i j := fun i j => by
    rw [map_one, one_mul]; exact hTr.geo.hV.herm i j
  have hJ : IsUnit (G.V.J.map t).det := by
    have w := Classical.arbitrary (InfinitePlace F)
    exact GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.V.J t (B.emb w).1 1 one_ne_zero (G.V.θ w)
      (by rw [one_smul]; exact hTr.geo.hV.cartan w)
  exact ⟨_, GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t G.V 1 herm hJ g', GlobalTheory.SplitUnitLift.liftU_piW hcm t G.V.J 1 herm hJ g'⟩

/- English proof (translation)
Establish `w` using `Classical.arbitrary (InfinitePlace F)`. Conclude with `GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.W.J t (B.emb w).1 Complex.I Complex.I_ne_zero (G.W.θ w) (hTr.geo.hW.cartan w)`.
-/
theorem isUnit_det_map_J_of_isTriple (hTr : IsTriple B G X om om') (v : Pl F) (t : E →ₐ[F] Fv F v) : IsUnit (G.W.J.map t).det := by
  have w := Classical.arbitrary (InfinitePlace F)
  exact GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.W.J t (B.emb w).1 Complex.I Complex.I_ne_zero (G.W.θ w)
    (hTr.geo.hW.cartan w)

/- English proof (translation)
Establish `hcm` using `hTr.base.cm`. Establish `herm : ∀ i j, σ (G.W.J j i) = algebraMap F E (-1) * G.W.J i j` using `fun i j => by`. Rewrite using `[map_neg, map_one, neg_one_mul]`. Conclude with `hTr.geo.hW.skew i j`. Conclude with `⟨_, GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t G.W (-1) herm (isUnit_det_map_J_of_isTriple hTr v t) h', GlobalTheory.SplitUnitLift.liftU_piW hcm t G.W.J (-1) herm (isUnit_det_map_J_of_isTriple hTr v t) h'⟩`.
-/
theorem surjW (hTr : IsTriple B G X om om') (v : Pl F) (t : E →ₐ[F] Fv F v) (h' : GL (Fin (a + a')) (Fv F v)) :
    ∃ h ∈ UAt σ G.W (evFin F v), (mat h).map (piW t) = h'.1 := by
  have hcm := hTr.base.cm
  have herm : ∀ i j, σ (G.W.J j i) = algebraMap F E (-1) * G.W.J i j := fun i j => by
    rw [map_neg, map_one, neg_one_mul]; exact hTr.geo.hW.skew i j
  exact ⟨_, GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t G.W (-1) herm (isUnit_det_map_J_of_isTriple hTr v t) h',
    GlobalTheory.SplitUnitLift.liftU_piW hcm t G.W.J (-1) herm (isUnit_det_map_J_of_isTriple hTr v t) h'⟩

open GlobalTheory.EmbChart GlobalTheory.LeviAtPlace GlobalTheory.UnitaryInjAtPlace in

/- English proof (translation)
Introduce `h₁ hh₁ h₂ hh₂ heq`. Establish `hcm` using `hTr.base.cm`. Establish `hJ` using `isUnit_det_map_J_of_isTriple hTr v t`. Establish `u₁` using `unitary_at_components v t h₁`. Establish `u₂` using `unitary_at_components v t h₂`.

Rewrite `u₁` using `[heq]`. Use `set A := ((mat h₂).map (piW t))ᵀ * G.W.J.map t with hA`. Establish `hAu : IsUnit A.det`. Establish `hd` using `congrArg Matrix.det u₂`. Rewrite `hd` using `[Matrix.det_mul]`.

Conclude with `isUnit_of_mul_isUnit_left (hd ▸ hJ)`. Establish `hQ : (mat h₁).map (piW (t.comp σ)) = (mat h₂).map (piW (t.comp σ))`. Rewrite using `[← Matrix.nonsing_inv_mul_cancel_left _ ((mat h₁).map (piW (t.comp σ))) hAu, ← Matrix.nonsing_inv_mul_cancel_left _ ((mat h₂).map (piW (t.comp σ))) hAu, u₁, u₂]`. Establish `hpi : ∀ (h : UA σ G.W.J) (τ : E →ₐ[F] Fv F v), (mat h).map (piW τ) = ((mat h).map (compFin F E v)).map (splitProj τ)`. Introduce `h τ`.

Rewrite using `[Matrix.map_map]`. Both sides reduce to the same expression. Establish `hY : (mat h₁).map (compFin F E v) = (mat h₂).map (compFin F E v)`. Use `mat_split_ext hcm t ?_ ?_` and prove the remaining obligations. Rewrite using `[← hpi, ← hpi, heq]`.

Rewrite using `[← hpi, ← hpi, hQ]`. Establish `hz : At (evFin F v) (mat h₁ - mat h₂)`. Introduce `u hu`. Establish `e : mat h₁ - mat h₂ = (mat h₁ - 1) - (mat h₂ - 1)` using `by abel`. Rewrite using `[e, smul_sub, hh₁ u hu, hh₂ u hu, sub_zero]`.

Establish `h0 : (mat h₁ - mat h₂).map (compFin F E v) = 0`. Rewrite using `[Matrix.map_sub _ (fun x y => map_sub _ x y), hY, sub_self]`. Establish `hm` using `mat_eq_zero_of_at v _ hz h0`. Conclude with `Subtype.ext (Units.ext (sub_eq_zero.1 hm))`.
-/
theorem injW (hTr : IsTriple B G X om om') (v : Pl F) (t : E →ₐ[F] Fv F v) :
    ∀ h₁ ∈ UAt σ G.W (evFin F v), ∀ h₂ ∈ UAt σ G.W (evFin F v),
      (mat h₁).map (piW t) = (mat h₂).map (piW t) → h₁ = h₂ := by
  intro h₁ hh₁ h₂ hh₂ heq
  have hcm := hTr.base.cm
  have hJ := isUnit_det_map_J_of_isTriple hTr v t
  have u₁ := unitary_at_components v t h₁
  have u₂ := unitary_at_components v t h₂
  rw [heq] at u₁
  set A := ((mat h₂).map (piW t))ᵀ * G.W.J.map t with hA
  have hAu : IsUnit A.det := by
    have hd := congrArg Matrix.det u₂
    rw [Matrix.det_mul] at hd
    exact isUnit_of_mul_isUnit_left (hd ▸ hJ)
  have hQ : (mat h₁).map (piW (t.comp σ)) = (mat h₂).map (piW (t.comp σ)) := by
    rw [← Matrix.nonsing_inv_mul_cancel_left _ ((mat h₁).map (piW (t.comp σ))) hAu,
      ← Matrix.nonsing_inv_mul_cancel_left _ ((mat h₂).map (piW (t.comp σ))) hAu, u₁, u₂]
  have hpi : ∀ (h : UA σ G.W.J) (τ : E →ₐ[F] Fv F v),
      (mat h).map (piW τ) = ((mat h).map (compFin F E v)).map (splitProj τ) := by
    intro h τ; rw [Matrix.map_map]; rfl
  have hY : (mat h₁).map (compFin F E v) = (mat h₂).map (compFin F E v) := by
    refine mat_split_ext hcm t ?_ ?_
    · rw [← hpi, ← hpi, heq]
    · rw [← hpi, ← hpi, hQ]
  have hz : At (evFin F v) (mat h₁ - mat h₂) := by
    intro u hu
    have e : mat h₁ - mat h₂ = (mat h₁ - 1) - (mat h₂ - 1) := by abel
    rw [e, smul_sub, hh₁ u hu, hh₂ u hu, sub_zero]
  have h0 : (mat h₁ - mat h₂).map (compFin F E v) = 0 := by
    rw [Matrix.map_sub _ (fun x y => map_sub _ x y), hY, sub_self]
  have hm := mat_eq_zero_of_at v _ hz h0
  exact Subtype.ext (Units.ext (sub_eq_zero.1 hm))

end Points

end GlobalTheory.SplitTransport

namespace GlobalTheory.SplitTransport

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

section Scalars

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n m : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `X`. Simplify using `only [GlobalTheory.SplitFlip.omA, GlobalTheory.SplitWeil.om, GlobalTheory.SplitFlip.apow, Pi.smul_apply, smul_eq_mul, map_one, Units.val_one, one_mul, mul_one, inv_one, GlobalTheory.SplitFlip.invT_val, Matrix.transpose_one, Fintype.card_fin, MonoidHom.one_apply, GlobalTheory.Spli …`. Simplify using `[GlobalTheory.SplitWeil.nabs]`. Rewrite using `[Complex.ofReal_cpow (NNReal.coe_nonneg _)]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem omA_left (ν : kˣ →* ℂˣ) (g : GL (Fin n) k) (Φ : Matrix (Fin n) (Fin m) k → ℂ) :
    GlobalTheory.SplitFlip.omA ν 1 g 1 Φ = (((ν (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) •
      GlobalTheory.SplitWeil.om 1 (1 : GL (Fin m) k) g Φ := by
  funext X
  simp only [GlobalTheory.SplitFlip.omA, GlobalTheory.SplitWeil.om, GlobalTheory.SplitFlip.apow, Pi.smul_apply, smul_eq_mul, map_one,
    Units.val_one, one_mul, mul_one, inv_one, GlobalTheory.SplitFlip.invT_val, Matrix.transpose_one, Fintype.card_fin,
    MonoidHom.one_apply, GlobalTheory.SplitFlip.gdet]
  simp [GlobalTheory.SplitWeil.nabs]
  rw [Complex.ofReal_cpow (NNReal.coe_nonneg _)]
  push_cast
  ring

/- English proof (translation)
Establish `h1 : (β (GlobalTheory.SplitFlip.gdet (GlobalTheory.SplitFlip.invT g)) : ℂ) ≠ 0` using `Units.ne_zero _`. Establish `h2` using `GlobalTheory.SplitFlip.apow_ne_zero (GlobalTheory.SplitFlip.gdet (GlobalTheory.SplitFlip.invT g)) (-(Fintype.card (Fin n) : ℂ) / 2)`. Use `⟨((GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det g) ^ ((Fintype.card (Fin n) : ℝ) / 2) : ℝ) : ℂ) / ((β (GlobalTheory.SplitFlip.gdet (GlobalTheory.SplitFlip.invT g)) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (GlobalTheory.SplitFlip.invT g)) (-( …` and prove the remaining obligations. Use function extensionality and compare the values at `X`. Simplify using `only [GlobalTheory.SplitFlip.omA, GlobalTheory.SplitWeil.om, Pi.smul_apply, smul_eq_mul, GlobalTheory.SplitFlip.invT_invT, inv_one, Units.val_one, map_one, MonoidHom.one_apply, one_mul, Matrix.one_mul, GlobalTheory.SplitFlip.apow_one, mul_one]`.

Simplify using `[GlobalTheory.SplitWeil.nabs] at h1 h2 ⊢`. Clear the denominators using the available nonvanishing facts. Rewrite using `[mul_div_assoc, div_self (GlobalTheory.SplitFlip.apow_ne_zero _ _), mul_one]`.
-/
theorem om_right (β : kˣ →* ℂˣ) (g : GL (Fin m) k) (Φ : Matrix (Fin n) (Fin m) k → ℂ) :
    ∃ s : ℂ, GlobalTheory.SplitWeil.om 1 g (1 : GL (Fin n) k) Φ = s • GlobalTheory.SplitFlip.omA 1 β 1 (GlobalTheory.SplitFlip.invT g) Φ := by
  have h1 : (β (GlobalTheory.SplitFlip.gdet (GlobalTheory.SplitFlip.invT g)) : ℂ) ≠ 0 := Units.ne_zero _
  have h2 := GlobalTheory.SplitFlip.apow_ne_zero (GlobalTheory.SplitFlip.gdet (GlobalTheory.SplitFlip.invT g)) (-(Fintype.card (Fin n) : ℂ) / 2)
  refine ⟨((GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det g) ^ ((Fintype.card (Fin n) : ℝ) / 2) : ℝ) : ℂ) /
    ((β (GlobalTheory.SplitFlip.gdet (GlobalTheory.SplitFlip.invT g)) : ℂ) *
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (GlobalTheory.SplitFlip.invT g)) (-(Fintype.card (Fin n) : ℂ) / 2)), ?_⟩
  funext X
  simp only [GlobalTheory.SplitFlip.omA, GlobalTheory.SplitWeil.om, Pi.smul_apply, smul_eq_mul, GlobalTheory.SplitFlip.invT_invT, inv_one,
    Units.val_one, map_one, MonoidHom.one_apply, one_mul, Matrix.one_mul, GlobalTheory.SplitFlip.apow_one, mul_one]
  simp [GlobalTheory.SplitWeil.nabs] at h1 h2 ⊢
  field_simp
  rw [mul_div_assoc, div_self (GlobalTheory.SplitFlip.apow_ne_zero _ _), mul_one]

/- English proof (translation)
Establish `h2 : ((GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det (GlobalTheory.SplitFlip.invT h')) ^ ((Fintype.card (Fin n) : ℝ) / 2) : ℝ) : ℂ) ≠ 0`. Use `GlobalTheory.SplitWeil.Model.nabs_pos (Matrix.GeneralLinearGroup.det (GlobalTheory.SplitFlip.invT h'))` as an intermediate fact. Conclude with `(Real.rpow_pos_of_pos this _).ne'` after adjusting the coercions. Use `⟨(β (GlobalTheory.SplitFlip.gdet h') : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet h') (-(Fintype.card (Fin n) : ℂ) / 2) / ((GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det (GlobalTheory.SplitFlip.invT h')) ^ ((Fintype.card (Fin n) : ℝ) / 2) : ℝ) : …` and prove the remaining obligations. Use function extensionality and compare the values at `X`.

Simplify using `only [GlobalTheory.SplitFlip.omA, GlobalTheory.SplitWeil.om, Pi.smul_apply, smul_eq_mul, inv_one, Units.val_one, map_one, MonoidHom.one_apply, one_mul, Matrix.one_mul, GlobalTheory.SplitFlip.apow_one, mul_one]`. Simplify using `only [ne_eq] at h2`. Simplify using `[GlobalTheory.SplitWeil.nabs] at h2 ⊢`. Establish `h3 : ((↑((MeasureTheory.distribHaarChar k) (Matrix.GeneralLinearGroup.det (GlobalTheory.SplitFlip.invT h'))) ^ ((n : ℝ) / 2) : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast h2`. Clear the denominators using the available nonvanishing facts.
-/
theorem omA_right (β : kˣ →* ℂˣ) (h' : GL (Fin m) k) (Φ : Matrix (Fin n) (Fin m) k → ℂ) :
    ∃ s : ℂ, GlobalTheory.SplitFlip.omA 1 β 1 h' Φ = s • GlobalTheory.SplitWeil.om 1 (GlobalTheory.SplitFlip.invT h') (1 : GL (Fin n) k) Φ := by
  have h2 : ((GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det (GlobalTheory.SplitFlip.invT h')) ^
      ((Fintype.card (Fin n) : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    have := GlobalTheory.SplitWeil.Model.nabs_pos (Matrix.GeneralLinearGroup.det (GlobalTheory.SplitFlip.invT h'))
    exact_mod_cast (Real.rpow_pos_of_pos this _).ne'
  refine ⟨(β (GlobalTheory.SplitFlip.gdet h') : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet h') (-(Fintype.card (Fin n) : ℂ) / 2) /
    ((GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det (GlobalTheory.SplitFlip.invT h')) ^
      ((Fintype.card (Fin n) : ℝ) / 2) : ℝ) : ℂ), ?_⟩
  funext X
  simp only [GlobalTheory.SplitFlip.omA, GlobalTheory.SplitWeil.om, Pi.smul_apply, smul_eq_mul, inv_one,
    Units.val_one, map_one, MonoidHom.one_apply, one_mul, Matrix.one_mul, GlobalTheory.SplitFlip.apow_one, mul_one]
  simp only [ne_eq] at h2
  simp [GlobalTheory.SplitWeil.nabs] at h2 ⊢
  have h3 : ((↑((MeasureTheory.distribHaarChar k) (Matrix.GeneralLinearGroup.det (GlobalTheory.SplitFlip.invT h'))) ^ ((n : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h2
  field_simp

end Scalars

end GlobalTheory.SplitTransport

namespace GlobalTheory.SplitTransport

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B a a' G X om om' hTr v ⟨t⟩`. Take `⟨ι, hι⟩` from `exists_isLinW hP hTr v t`. Take `⟨ν₀, hV⟩` from `GlobalTheory.T.local_weil_linear_model_invariant hP F E σ B a a' G X om om' hTr v t ι hι (GlobalTheory.T.local_weil_linear_model_action hP F E σ B a a' G X om om' hTr v t ι hι)`. Take `⟨t', ht'⟩` from `GlobalTheory.T.local_weil_linear_model_measure hP F E σ B a a' G X om om' hTr v t ι hι ν₀ hV`. Establish `hloc` using `((GlobalTheory.T.theta_action_exists hP) F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ (GlobalTheory.ThK.Check.isPair_of_isTriple hTr).1 v).1`.

Take `⟨β₀, hW⟩` from `GlobalTheory.LocalUnitSubgroupClosure.core hTr v t ι (hloc 1 (GlobalTheory.LocalUnitSubgroupClosure.one_mem_UAt _ _)) (surjW hTr v t) (injW hTr v t) (GlobalTheory.T.local_weil_linear_model_unitary hP F E σ B a a' G X om om' hTr v t ι hι)`. Establish `hνc : Continuous X.ν` using `by show Continuous fun x => X.α x / X.β x`. Conclude with `hTr.chars.heckeα.1.div' hTr.chars.heckeβ.1`. Establish `hs0 : GlobalTheory.SmGL.IsSmoothChar (chrW X.ν t')` using `GlobalTheory.RootEx.UniformLattices.isOpen_ker_of_continuous _ (GlobalTheory.ChrWSmooth.continuous_chrW hνc t')`. Establish `hνs : GlobalTheory.SmGL.IsSmoothChar ν₀`.

Break down `ht' with h | h` into its components or cases. Rewrite using `[h]`. Conclude with `hs0`. Rewrite using `[h]`. Conclude with `hs0.inv`.

Use `set χ : GL (Fin a) (Fv F v) →* ℂˣ := GlobalTheory.SmGL.detChar (Fin a) ν₀ with hχ`. Establish `hχv : ∀ g, χ g = ν₀ (Matrix.GeneralLinearGroup.det g)` using `fun g => rfl`. Establish `hbij` using `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι`. Establish `hinj` using `hbij.injOn`. Establish `hmaps : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ι φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin a) (Fin (a + a')) (Fv F v))` using `fun φ hφ => hbij.mapsTo hφ`.

Use `⟨χ, ι, ?_, hbij, ?_⟩` and prove the remaining obligations. Use `hνs.detChar (n := Fin a)` as an intermediate fact. Conclude with `this`. Introduce `N hN`. Establish `hAugSB : augAt om v ≤ SB (Fin a × Fin (a + a') → Fv F v)`.

Rewrite using `[augAt, Submodule.span_le]`. Introduce and unpack `_ ⟨g, hg, φ, hφ, φ₁, hφ₁, -, rfl⟩`. Conclude with `Submodule.sub_mem _ hφ₁ hφ`. Establish `hVsc : ∀ g ∈ UAt σ G.V (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ → ∃ g' : GL (Fin a) (Fv F v), (mat g).map (piW t) = g'.1 ∧ ι (φ₁ - φ) = (((χ g')⁻¹ : ℂˣ) : ℂ) • (GlobalTheory.SplitWeil.om 1 …`. Introduce `g hg φ hφ φ₁ hφ₁ hA`.

Take `⟨g', hg', hact⟩` from `hV g hg`. Use `⟨g', hg', ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, hact φ hφ φ₁ hφ₁ hA, omA_left, smul_sub, smul_smul, hχv]`. Simplify using the standard rewrite rules. Establish `hmapAug : (augAt om v).map ι = GlobalTheory.ThetaGLSub.aug (a + a') χ`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[augAt, Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩, rfl⟩`. Take `⟨g', -, e⟩` from `hVsc g hg φ hφ φ₁ hφ₁ hA`. Rewrite using `[SetLike.mem_coe, e]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨g', ι φ, hmaps φ hφ, rfl⟩)`. Rewrite using `[GlobalTheory.ThetaGLSub.aug, Submodule.span_le]`. Introduce and unpack `_ ⟨h, Φ, hΦ, rfl⟩`. Take `⟨φ, hφ, rfl⟩` from `hbij.surjOn hΦ`. Take `⟨g, hg, hgt⟩` from `surjV hTr v t h`.

Take `⟨φ₁, ⟨hφ₁, hA⟩, -⟩` from `hloc g hg 1 (GlobalTheory.LocalUnitSubgroupClosure.one_mem_UAt _ _) φ hφ`. Take `⟨g', hg', e⟩` from `hVsc g hg φ hφ φ₁ hφ₁ hA`. Establish `: g' = h` using `Units.ext (hg'.symm.trans hgt)`. Substitute `this` using the available equality. Use `⟨(χ g' : ℂ) • (φ₁ - φ), Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_smul, e, smul_smul]`. Simplify using the standard rewrite rules. Establish `hiffAug : augAt om v ≤ N ↔ GlobalTheory.ThetaGLSub.aug (a + a') χ ≤ N.map ι`. Rewrite using `[← hmapAug]`. Use `⟨Submodule.map_mono, fun h x hx => ?_⟩` and prove the remaining obligations.

Take `⟨y, hy, e⟩` from `Submodule.mem_map.1 (h (Submodule.mem_map_of_mem hx))`. Rewrite `hy` using `[hinj (hN hy) (hAugSB hx) e]`. Then use the resulting hypothesis. Establish `hiffW : (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → φ₁ ∈ N) ↔ ∀ g : GL (Fin (a + a')) (Fv F v), ∀ Φ ∈ N.map ι, GlobalTheory.SplitWeil.om 1 g (1 : GL (Fin a) (Fv F v)) Φ ∈ N.map ι`. Prove the components needed by the constructor for the conclusion. Introduce `H g Φ hΦ`.

Take `⟨φ, hφN, rfl⟩` from `Submodule.mem_map.1 hΦ`. Take `⟨h, hh, hht⟩` from `surjW hTr v t (GlobalTheory.SplitFlip.invT g)`. Take `⟨φ₁, ⟨hφ₁, hA⟩, -⟩` from `hloc 1 (GlobalTheory.LocalUnitSubgroupClosure.one_mem_UAt _ _) h hh φ (hN hφN)`. Take `⟨h', hh', hact⟩` from `hW h hh`. Establish `: h' = GlobalTheory.SplitFlip.invT g` using `Units.ext (hh'.symm.trans hht)`.

Substitute `this` using the available equality. Take `⟨s, hs⟩` from `om_right β₀ g (ι φ)`. Rewrite using `[hs, ← hact φ (hN hφN) φ₁ hφ₁ hA, ← map_smul]`. Conclude with `Submodule.mem_map_of_mem (N.smul_mem s (H h hh φ hφN φ₁ hφ₁ hA))`. Introduce `H h hh φ hφN φ₁ hφ₁ hA`.

Take `⟨h', -, hact⟩` from `hW h hh`. Take `⟨s, hs⟩` from `omA_right β₀ h' (ι φ)`. Establish `h1 : ι φ₁ ∈ N.map ι`. Rewrite using `[hact φ (hN hφN) φ₁ hφ₁ hA, hs]`. Conclude with `Submodule.smul_mem _ _ (H _ _ (Submodule.mem_map_of_mem hφN))`.

Take `⟨y, hy, e⟩` from `Submodule.mem_map.1 h1`. Rewrite `hy` using `[hinj (hN hy) hφ₁ e]`. Then use the resulting hypothesis. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, -, h3⟩`. Use `⟨hiffAug.1 h1, ?_, hiffW.1 h3⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨φ, hφ, rfl⟩`. Conclude with `hmaps φ (hN hφ)`. Introduce and unpack `⟨h1, -, h3⟩`. Conclude with `⟨hiffAug.2 h1, hN, hiffW.2 h3⟩`.
-/
theorem transport : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs G Xc om om' →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, Nonempty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) →
      ∃ (χ : GL (Fin a) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) →* ℂˣ)
        (ι : ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) →ₗ[ℂ]
          (Matrix (Fin a) (Fin (a + a')) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        IsOpen {g | χ g = 1} ∧
        Set.BijOn ι (GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) : Set _)
          (GlobalTheory.SplitWeil.SB (Matrix (Fin a) (Fin (a + a')) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) : Set _) ∧
        ∀ N : Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
          N ≤ GlobalTheory.WeilM.SB _ → (GlobalTheory.Published.ThetaSub om v N ↔ GlobalTheory.ThetaGLSub.IsSub χ (N.map ι)) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v ⟨t⟩
  obtain ⟨ι, hι⟩ := exists_isLinW hP hTr v t
  obtain ⟨ν₀, hV⟩ := GlobalTheory.T.local_weil_linear_model_invariant hP F E σ B a a' G X om om' hTr v t ι hι (GlobalTheory.T.local_weil_linear_model_action hP F E σ B a a' G X om om' hTr v t ι hι)
  obtain ⟨t', ht'⟩ := GlobalTheory.T.local_weil_linear_model_measure hP F E σ B a a' G X om om' hTr v t ι hι ν₀ hV
  have hloc := ((GlobalTheory.T.theta_action_exists hP) F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hTr).1 v).1
  obtain ⟨β₀, hW⟩ := GlobalTheory.LocalUnitSubgroupClosure.core hTr v t ι (hloc 1 (GlobalTheory.LocalUnitSubgroupClosure.one_mem_UAt _ _)) (surjW hTr v t) (injW hTr v t)
    (GlobalTheory.T.local_weil_linear_model_unitary hP F E σ B a a' G X om om' hTr v t ι hι)

  have hνc : Continuous X.ν := by
    show Continuous fun x => X.α x / X.β x
    exact hTr.chars.heckeα.1.div' hTr.chars.heckeβ.1
  have hs0 : GlobalTheory.SmGL.IsSmoothChar (chrW X.ν t') :=
    GlobalTheory.RootEx.UniformLattices.isOpen_ker_of_continuous _ (GlobalTheory.ChrWSmooth.continuous_chrW hνc t')
  have hνs : GlobalTheory.SmGL.IsSmoothChar ν₀ := by
    rcases ht' with h | h
    · rw [h]; exact hs0
    · rw [h]; exact hs0.inv
  set χ : GL (Fin a) (Fv F v) →* ℂˣ := GlobalTheory.SmGL.detChar (Fin a) ν₀ with hχ
  have hχv : ∀ g, χ g = ν₀ (Matrix.GeneralLinearGroup.det g) := fun g => rfl
  have hbij := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι
  have hinj := hbij.injOn
  have hmaps : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ι φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) :=
    fun φ hφ => hbij.mapsTo hφ
  refine ⟨χ, ι, ?_, hbij, ?_⟩
  · have := hνs.detChar (n := Fin a)
    exact this
  intro N hN

  have hAugSB : augAt om v ≤ SB (Fin a × Fin (a + a') → Fv F v) := by
    rw [augAt, Submodule.span_le]
    rintro _ ⟨g, hg, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact Submodule.sub_mem _ hφ₁ hφ
  have hVsc : ∀ g ∈ UAt σ G.V (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ →
      ∃ g' : GL (Fin a) (Fv F v), (mat g).map (piW t) = g'.1 ∧
        ι (φ₁ - φ) = (((χ g')⁻¹ : ℂˣ) : ℂ) • (GlobalTheory.SplitWeil.om 1 1 g' (ι φ) - (χ g' : ℂ) • ι φ) := by
    intro g hg φ hφ φ₁ hφ₁ hA
    obtain ⟨g', hg', hact⟩ := hV g hg
    refine ⟨g', hg', ?_⟩
    rw [map_sub, hact φ hφ φ₁ hφ₁ hA, omA_left, smul_sub, smul_smul, hχv]
    simp
  have hmapAug : (augAt om v).map ι = GlobalTheory.ThetaGLSub.aug (a + a') χ := by
    apply le_antisymm
    · rw [augAt, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩, rfl⟩
      obtain ⟨g', -, e⟩ := hVsc g hg φ hφ φ₁ hφ₁ hA
      rw [SetLike.mem_coe, e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g', ι φ, hmaps φ hφ, rfl⟩)
    · rw [GlobalTheory.ThetaGLSub.aug, Submodule.span_le]
      rintro _ ⟨h, Φ, hΦ, rfl⟩
      obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hΦ
      obtain ⟨g, hg, hgt⟩ := surjV hTr v t h
      obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hloc g hg 1 (GlobalTheory.LocalUnitSubgroupClosure.one_mem_UAt _ _) φ hφ
      obtain ⟨g', hg', e⟩ := hVsc g hg φ hφ φ₁ hφ₁ hA
      have : g' = h := Units.ext (hg'.symm.trans hgt)
      subst this
      refine ⟨(χ g' : ℂ) • (φ₁ - φ), Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩), ?_⟩
      rw [map_smul, e, smul_smul]
      simp
  have hiffAug : augAt om v ≤ N ↔ GlobalTheory.ThetaGLSub.aug (a + a') χ ≤ N.map ι := by
    rw [← hmapAug]
    refine ⟨Submodule.map_mono, fun h x hx => ?_⟩
    obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 (h (Submodule.mem_map_of_mem hx))
    rwa [hinj (hN hy) (hAugSB hx) e] at hy

  have hiffW : (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → φ₁ ∈ N) ↔
      ∀ g : GL (Fin (a + a')) (Fv F v), ∀ Φ ∈ N.map ι, GlobalTheory.SplitWeil.om 1 g (1 : GL (Fin a) (Fv F v)) Φ ∈ N.map ι := by
    constructor
    · intro H g Φ hΦ
      obtain ⟨φ, hφN, rfl⟩ := Submodule.mem_map.1 hΦ
      obtain ⟨h, hh, hht⟩ := surjW hTr v t (GlobalTheory.SplitFlip.invT g)
      obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hloc 1 (GlobalTheory.LocalUnitSubgroupClosure.one_mem_UAt _ _) h hh φ (hN hφN)
      obtain ⟨h', hh', hact⟩ := hW h hh
      have : h' = GlobalTheory.SplitFlip.invT g := Units.ext (hh'.symm.trans hht)
      subst this
      obtain ⟨s, hs⟩ := om_right β₀ g (ι φ)
      rw [hs, ← hact φ (hN hφN) φ₁ hφ₁ hA, ← map_smul]
      exact Submodule.mem_map_of_mem (N.smul_mem s (H h hh φ hφN φ₁ hφ₁ hA))
    · intro H h hh φ hφN φ₁ hφ₁ hA
      obtain ⟨h', -, hact⟩ := hW h hh
      obtain ⟨s, hs⟩ := omA_right β₀ h' (ι φ)
      have h1 : ι φ₁ ∈ N.map ι := by
        rw [hact φ (hN hφN) φ₁ hφ₁ hA, hs]
        exact Submodule.smul_mem _ _ (H _ _ (Submodule.mem_map_of_mem hφN))
      obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 h1
      rwa [hinj (hN hy) hφ₁ e] at hy
  constructor
  · rintro ⟨h1, -, h3⟩
    refine ⟨hiffAug.1 h1, ?_, hiffW.1 h3⟩
    rintro _ ⟨φ, hφ, rfl⟩
    exact hmaps φ (hN hφ)
  · rintro ⟨h1, -, h3⟩
    exact ⟨hiffAug.2 h1, hN, hiffW.2 h3⟩

end GlobalTheory.SplitTransport

import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Mfac
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilTransportAdelicSchwartzCmExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTransportWeilDatumCmExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedEqDiagonalLagrangianThetaIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHalfAbstract
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.PhaseFourierInjectivity

open PositivityTheory.ThKW.ModulusFactorDefinition

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Establish `e : (J.map (σ : E →+* E))ᵀ = J` using `Matrix.ext fun i j => h.1 i j`. Establish `e2 : J⁻¹ = (J⁻¹.map (σ : E →+* E))ᵀ`. Use `Matrix.inv_eq_left_inv ?_` and prove the remaining obligations. Use `conv_lhs => arg 2`. Rewrite using `[← e]`.

Rewrite using `[← Matrix.transpose_mul, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ (Ne.isUnit h.2), Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]`. Conclude with `(congrFun (congrFun e2 i) j).symm`.
-/
theorem inv_herm {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : IsHermND σ J) (i j : Fin n) : σ (J⁻¹ j i) = J⁻¹ i j := by
  have e : (J.map (σ : E →+* E))ᵀ = J := Matrix.ext fun i j => h.1 i j
  have e2 : J⁻¹ = (J⁻¹.map (σ : E →+* E))ᵀ := by
    refine Matrix.inv_eq_left_inv ?_
    conv_lhs => arg 2; rw [← e]
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ (Ne.isUnit h.2),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  exact (congrFun (congrFun e2 i) j).symm

/- English proof (translation)
Establish `h1 : ((mtF σ J h).map (sigR (AF F) σ))ᵀ * JR (AF F) J * mtF σ J h = JR (AF F) J` using `h.2`. Establish `h2` using `congrArg Matrix.transpose h1`. Rewrite `h2` using `[Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc]`. Establish `e : (mtF σ J h).map (cA σ) = (mtF σ J h).map (sigR (AF F) σ)`. Use extensionality with `i j`.

Conclude with `GlobalTheory.TransportF.cA_eq σ _`. Use `show (mtF σ J h)ᵀ * incM F Jᵀ * (mtF σ J h).map (cA σ) = incM F Jᵀ`. Rewrite using `[e]`. Conclude with `h2`.
-/
theorem mem_UG {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : GAF σ J) : matHomF σ J h ∈ UG (cA σ) (incM F Jᵀ) := by
  have h1 : ((mtF σ J h).map (sigR (AF F) σ))ᵀ * JR (AF F) J * mtF σ J h = JR (AF F) J := h.2
  have h2 := congrArg Matrix.transpose h1
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at h2
  have e : (mtF σ J h).map (cA σ) = (mtF σ J h).map (sigR (AF F) σ) := by
    ext i j
    exact GlobalTheory.TransportF.cA_eq σ _
  show (mtF σ J h)ᵀ * incM F Jᵀ * (mtF σ J h).map (cA σ) = incM F Jᵀ
  rw [e]
  exact h2

/- English proof (translation)
Establish `eB : (-1 : AF F ⊗[F] E) • incM F (-(ξ₀ • JS⁻¹)) = incM F (ξ₀ • JS⁻¹)`. Use function extensionality and compare the values at `i j`. Simplify using `[incM]`. Take `⟨co, hrat⟩ : ∃ co : Darboux (symp (cA σ) (-1) (incM F JTᵀ) (incM F (-(ξ₀ • JS⁻¹)))) (Fin nT × Fin nS), ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin nT × Fin nS → F, co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))` from `GlobalTheory.RatDarboux.exists_darboux (AF F) hB.cm.2.2.1 σ (GlobalTheory.SplitDetCharF.sig_invol hB.cm) (JA := JTᵀ) (JB := -(ξ₀ • JS⁻¹)) (fun i j => hT.1 j i) (fun i j => by simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, map_neg, map_mul, hσ, inv_herm hS]; ring) (b …`. Rewrite using `[← neg_smul, Matrix.det_smul]`.

Conclude with `mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 hξ)) (Matrix.isUnit_nonsing_inv_det _ (Ne.isUnit hS.2)).ne_zero)`. Use `⟨eB, co, hrat, fun f hf => ?_⟩` and prove the remaining obligations. Set `τ` to `Fintype.equivFin (Fin nT × Fin nS)`. Establish `he : ∀ w w', symplOF σ JS JT ξ₀ w w' = GlobalTheory.ThetaTransform.symV (GlobalTheory.TransportF.numCoordF (σ` using `σ) co τ w) (GlobalTheory.TransportF.numCoordF (σ := σ) co τ w') := fun w w' => by`. Rewrite using `[GlobalTheory.TransportF.symplOF_eq_symp rfl eB]`.

Use `(co.form w w').trans ?_` and prove the remaining obligations. Simplify using `only [GlobalTheory.ThetaTransform.symV, GlobalTheory.TransportF.numCoordF_apply, comp_equiv_dotProduct_comp_equiv]`. Establish `hr : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin (Fintype.card (Fin nT × Fin nS)) → F, GlobalTheory.TransportF.numCoordF (σ` using `σ) co τ (ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := fun x => by`. Take `⟨y, z, h⟩` from `hrat x`. Conclude with `⟨y ∘ τ.symm, z ∘ τ.symm, by rw [GlobalTheory.TransportF.numCoordF_apply]; erw [h]; rfl⟩`.

Take `⟨Φ, hΦ, h⟩` from `GlobalTheory.T.exists_thetaTransform_eq_orientedThetaFunction_CM F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB) _ (GlobalTheory.TransportF.numCoordF (σ := σ) co τ) he hr f hf`. Use `⟨_, GlobalTheory.TransportF.comp_mem_schA τ.symm hΦ, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.TransportF.thetaTr_eqF (σ := σ) co τ, ← h]`. Use `congr 2`. Use function extensionality and compare the values at `x`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.
-/
theorem exists_coord {B : Base F E} (hB : B.IsGood σ) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E}
    {JT : Matrix (Fin nT) (Fin nT) E} (hS : IsHermND σ JS) (hT : IsHermND σ JT) {ξ₀ : E} (hξ : ξ₀ ≠ 0) (hσ : σ ξ₀ = -ξ₀) :
    (-1 : AF F ⊗[F] E) • incM F (-(ξ₀ • JS⁻¹)) = incM F (ξ₀ • JS⁻¹) ∧
    ∃ co : Darboux (symp (cA σ) (-1) (incM F JTᵀ) (incM F (-(ξ₀ • JS⁻¹)))) (Fin nT × Fin nS),
      (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin nT × Fin nS → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) ∧
      ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∃ Φ ∈ schA F (Fin nT × Fin nS), GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ = f := by
  have eB : (-1 : AF F ⊗[F] E) • incM F (-(ξ₀ • JS⁻¹)) = incM F (ξ₀ • JS⁻¹) := by
    funext i j
    simp [incM]
  obtain ⟨co, hrat⟩ : ∃ co : Darboux (symp (cA σ) (-1) (incM F JTᵀ) (incM F (-(ξ₀ • JS⁻¹)))) (Fin nT × Fin nS),
      ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin nT × Fin nS → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) :=
    GlobalTheory.RatDarboux.exists_darboux (AF F) hB.cm.2.2.1 σ (GlobalTheory.SplitDetCharF.sig_invol hB.cm)
    (JA := JTᵀ) (JB := -(ξ₀ • JS⁻¹)) (fun i j => hT.1 j i)
    (fun i j => by simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, map_neg, map_mul, hσ, inv_herm hS]; ring)
    (by rw [Matrix.det_transpose]; exact hT.2)
    (by
      rw [← neg_smul, Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 hξ)) (Matrix.isUnit_nonsing_inv_det _ (Ne.isUnit hS.2)).ne_zero)
  refine ⟨eB, co, hrat, fun f hf => ?_⟩
  let τ := Fintype.equivFin (Fin nT × Fin nS)
  have he : ∀ w w', symplOF σ JS JT ξ₀ w w' =
      GlobalTheory.ThetaTransform.symV (GlobalTheory.TransportF.numCoordF (σ := σ) co τ w) (GlobalTheory.TransportF.numCoordF (σ := σ) co τ w') := fun w w' => by
    rw [GlobalTheory.TransportF.symplOF_eq_symp rfl eB]
    refine (co.form w w').trans ?_
    simp only [GlobalTheory.ThetaTransform.symV, GlobalTheory.TransportF.numCoordF_apply, comp_equiv_dotProduct_comp_equiv]
  have hr : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin (Fintype.card (Fin nT × Fin nS)) → F,
      GlobalTheory.TransportF.numCoordF (σ := σ) co τ (ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := fun x => by
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨y ∘ τ.symm, z ∘ τ.symm, by rw [GlobalTheory.TransportF.numCoordF_apply]; erw [h]; rfl⟩
  obtain ⟨Φ, hΦ, h⟩ := GlobalTheory.T.exists_thetaTransform_eq_orientedThetaFunction_CM F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ
    (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB) _ (GlobalTheory.TransportF.numCoordF (σ := σ) co τ) he hr f hf
  refine ⟨_, GlobalTheory.TransportF.comp_mem_schA τ.symm hΦ, ?_⟩
  rw [GlobalTheory.TransportF.thetaTr_eqF (σ := σ) co τ, ← h]
  congr 2
  funext x
  congr 1
  funext i
  simp

end

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ ν 𝓕 hν h𝓕 χS ωd hω f hf`. Establish `hT'` using `GlobalTheory.WeilSchrodinger.DblTargetF.isHermND_dblG hT`. Take `⟨eB, co, hrat, hon⟩` from `exists_coord hB hS hT' hξ hσ`. Take `⟨Φ, hΦ, rfl⟩` from `hon f hf`. Take `⟨om, hom⟩` from `GlobalTheory.TransportF.exists_isTransportF F E σ B hB _ _ JS _ hS hT' ξ₀ hξ hσ χS 1 hω.hecS hω.hecT hω.resS hω.resT ωd hω _ _ _ rfl eB _ co hrat`.

Establish `hc` using `GlobalTheory.T.continuous_transport_weil_datum_cm_extension F E σ B hB _ _ JS _ hS hT' ξ₀ hξ hσ χS 1 hω.hecS hω.hecT hω.resS hω.resT ωd hω _ _ _ rfl eB _ co hrat om hom`. Take `⟨l, hl, hl'⟩` from `GlobalTheory.T.exists_admitted_eq_diagonalLagrangian_thetaIntegral F E σ B hB nS nT JT _ _ _ co hrat ν 𝓕 hν h𝓕`. Set `a : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) → UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ)` to `fun h => ⟨matHomF σ _ h, mem_UG h⟩`. Establish `ha : Continuous a` using `Continuous.subtype_mk continuous_subtype_val _`. Use `((hc l hl Φ hΦ).comp (ha.prodMk (continuous_const (y := 1)))).congr fun h => ?_` and prove the remaining obligations.

Take `⟨h1, h2⟩` from `hom (a h) 1 1 h rfl (by`. Rewrite using `[inv_one]`. Conclude with `Matrix.transpose_one.symm) Φ hΦ`. Use `show l (om (a h, 1) Φ) = _`. Rewrite using `[hl' _ h1, h2]`.
-/
theorem cont : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
        Continuous fun h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) =>
          GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (ωd (1, h) f) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ ν 𝓕 hν h𝓕 χS ωd hω f hf
  have hT' := GlobalTheory.WeilSchrodinger.DblTargetF.isHermND_dblG hT
  obtain ⟨eB, co, hrat, hon⟩ := exists_coord hB hS hT' hξ hσ
  obtain ⟨Φ, hΦ, rfl⟩ := hon f hf
  obtain ⟨om, hom⟩ := GlobalTheory.TransportF.exists_isTransportF F E σ B hB _ _ JS _ hS hT' ξ₀ hξ hσ χS 1 hω.hecS hω.hecT hω.resS
    hω.resT ωd hω _ _ _ rfl eB _ co hrat
  have hc := GlobalTheory.T.continuous_transport_weil_datum_cm_extension F E σ B hB _ _ JS _ hS hT' ξ₀ hξ hσ χS 1 hω.hecS hω.hecT hω.resS
    hω.resT ωd hω _ _ _ rfl eB _ co hrat om hom
  obtain ⟨l, hl, hl'⟩ := GlobalTheory.T.exists_admitted_eq_diagonalLagrangian_thetaIntegral F E σ B hB nS nT JT _ _ _ co hrat ν 𝓕 hν h𝓕
  let a : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →
      UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) := fun h => ⟨matHomF σ _ h, mem_UG h⟩
  have ha : Continuous a := Continuous.subtype_mk continuous_subtype_val _
  refine ((hc l hl Φ hΦ).comp (ha.prodMk (continuous_const (y := 1)))).congr fun h => ?_
  obtain ⟨h1, h2⟩ := hom (a h) 1 1 h rfl (by
    rw [inv_one]
    exact Matrix.transpose_one.symm) Φ hΦ
  show l (om (a h, 1) Φ) = _
  rw [hl' _ h1, h2]

end PositivityTheory.ThKW.PhaseFourierInjectivity

end

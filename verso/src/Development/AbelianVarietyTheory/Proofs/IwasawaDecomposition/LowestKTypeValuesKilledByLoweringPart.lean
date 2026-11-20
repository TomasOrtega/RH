import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilDatumGeneratorRealOneParamGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLift.LowerKill

open GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.RealTranslate

/- English proof (translation)
Establish `e` using `congrFun (congrFun h a) b`. Simplify using `only [Formalism.REAL.Jm, mul_diagonal, diagonal_mul] at e`. Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;> simp only [ha, hb, ne_eq, not_true_eq_false] at hab e`. Simplify using `only [Bool.false_eq_true, if_false, if_true] at e`. Take the linear combination `(1 / 2 : ℂ) * e`.

Simplify using `only [Bool.false_eq_true, if_false, if_true] at e`. Take the linear combination `(-1 / 2 : ℂ) * e`.
-/
theorem entry_eq_zero {n : ℕ} {ε : Fin n → Bool} {κ : Matrix (Fin n) (Fin n) ℂ}
    (h : κ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * κ) {a b : Fin n} (hab : ε a ≠ ε b) : κ a b = 0 := by
  have e := congrFun (congrFun h a) b
  simp only [Formalism.REAL.Jm, mul_diagonal, diagonal_mul] at e
  cases ha : ε a <;> cases hb : ε b <;> simp only [ha, hb, ne_eq, not_true_eq_false] at hab e
  · simp only [Bool.false_eq_true, if_false, if_true] at e
    linear_combination (1 / 2 : ℂ) * e
  · simp only [Bool.false_eq_true, if_false, if_true] at e
    linear_combination (-1 / 2 : ℂ) * e

/- English proof (translation)
Rewrite using `[mul_apply]`. Use `Finset.sum_eq_zero fun d _ => ?_` and prove the remaining obligations. Distinguish the cases in `hd : ε d = ε b`. Rewrite using `[mul_apply, Finset.sum_eq_zero fun c _ => ?_, zero_mul]`. Distinguish the cases in `hc : ε a = ε c`.

Rewrite using `[hY c d (by rw [← hc, hd]; exact hab), mul_zero]`. Rewrite using `[entry_eq_zero h' hc, zero_mul]`. Rewrite using `[entry_eq_zero h hd, mul_zero]`.
-/
theorem block_conj {n : ℕ} {ε : Fin n → Bool} {κ κ' Y : Matrix (Fin n) (Fin n) ℂ}
    (h : κ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * κ) (h' : κ' * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * κ')
    (hY : ∀ a b, ¬ (ε a = false ∧ ε b = true) → Y a b = 0) (a b : Fin n) (hab : ¬ (ε a = false ∧ ε b = true)) :
    (κ' * Y * κ) a b = 0 := by
  rw [mul_apply]
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases hd : ε d = ε b
  · rw [mul_apply, Finset.sum_eq_zero fun c _ => ?_, zero_mul]
    by_cases hc : ε a = ε c
    · rw [hY c d (by rw [← hc, hd]; exact hab), mul_zero]
    · rw [entry_eq_zero h' hc, zero_mul]
  · rw [entry_eq_zero h hd, mul_zero]

variable {D : D7} {T : HSp D} {Sp : D.what₂.Tau → SPar}

/- English proof (translation)
Establish `hu : IsUnit (M.fr τ).det` using `(isUnit_iff_isUnit_det _).1 (M.fr_unit τ)`. Establish `h1 : κᴴ * κ = 1` using `hκ.1.1`. Establish `h2 : κᴴ * Formalism.REAL.Jm (M.ε τ) * κ = Formalism.REAL.Jm (M.ε τ)`. Rewrite using `[Matrix.mul_assoc, ← hκ.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]`. Establish `h3 : M.fr τ * ((M.fr τ)⁻¹ * κ * M.fr τ) = κ * M.fr τ`.

Rewrite using `[Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hu]`. Use `show ((M.fr τ)⁻¹ * κ * M.fr τ)ᴴ * gramAt D T τ * ((M.fr τ)⁻¹ * κ * M.fr τ) = gramAt D T τ`. Rewrite using `[← M.fr_gram τ]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[conjTranspose_mul (M.fr τ)]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = (M.fr τ)ᴴ * (κᴴ * Formalism.REAL.Jm (M.ε τ) * κ) * M.fr τ := by`. Rewrite using `[h3, conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [h2]`.
-/
theorem frame_mem_UH (M : DSModel T Sp) (τ : D.what₂.Tau) {κ : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hκ : κ ∈ Formalism.REAL.Kset (M.ε τ)) : (M.fr τ)⁻¹ * κ * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D T τ) := by
  have hu : IsUnit (M.fr τ).det := (isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : κᴴ * κ = 1 := hκ.1.1
  have h2 : κᴴ * Formalism.REAL.Jm (M.ε τ) * κ = Formalism.REAL.Jm (M.ε τ) := by
    rw [Matrix.mul_assoc, ← hκ.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have h3 : M.fr τ * ((M.fr τ)⁻¹ * κ * M.fr τ) = κ * M.fr τ := by
    rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hu]
  show ((M.fr τ)⁻¹ * κ * M.fr τ)ᴴ * gramAt D T τ * ((M.fr τ)⁻¹ * κ * M.fr τ) = gramAt D T τ
  rw [← M.fr_gram τ]
  calc _ = (M.fr τ * ((M.fr τ)⁻¹ * κ * M.fr τ))ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * ((M.fr τ)⁻¹ * κ * M.fr τ)) := by
        rw [conjTranspose_mul (M.fr τ)]
        simp only [Matrix.mul_assoc]
    _ = (M.fr τ)ᴴ * (κᴴ * Formalism.REAL.Jm (M.ε τ) * κ) * M.fr τ := by
        rw [h3, conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h2]

/- English proof (translation)
Establish `hs` using `atTau_spec hθ T ρ (frame_mem_UH M ρ hκ)`. Establish `hi : infMat D.sp.cm.sig T.gram (θ τ) (atTau θ T ρ ((M.fr ρ)⁻¹ * κ * M.fr ρ)) * infMat D.sp.cm.sig T.gram (θ τ) (atTau θ T ρ ((M.fr ρ)⁻¹ * κ * M.fr ρ))⁻¹ = 1`. Rewrite using `[← infMat_mul, mul_inv_cancel, infMat_one]`. Unfold `adAt`. Distinguish the cases in `c : τ = ρ`.

Substitute `c` using the available equality. Establish `hu : IsUnit (M.fr τ).det` using `(isUnit_iff_isUnit_det _).1 (M.fr_unit τ)`. Establish `h1 : κ * κᴴ = 1` using `hκ.1.2`. Establish `h1' : κᴴ * κ = 1` using `hκ.1.1`. Establish `hJ : κᴴ * Formalism.REAL.Jm (M.ε τ) = Formalism.REAL.Jm (M.ε τ) * κᴴ`.

Use `congrArg conjTranspose hκ.2` as an intermediate fact. Rewrite `this` using `[conjTranspose_mul, conjTranspose_mul, Formalism.REAL.Jm_conjTranspose]`. Conclude with `this.symm`. Rewrite `hi`, the goal using `[hs.2.1]`. Establish `hi2 : (M.fr τ)⁻¹ * κ * M.fr τ * ((M.fr τ)⁻¹ * κᴴ * M.fr τ) = 1`.

Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc _ κᴴ, mul_nonsing_inv_cancel_left _ _ hu, Matrix.mul_assoc, ← Matrix.mul_assoc κ, h1, Matrix.one_mul, nonsing_inv_mul _ hu]`. Rewrite using `[← inv_eq_right_inv hi, inv_eq_right_inv hi2]`. Introduce `a b hab`. Establish `e : M.fr τ * ((M.fr τ)⁻¹ * κᴴ * M.fr τ * Z * ((M.fr τ)⁻¹ * κ * M.fr τ)) * (M.fr τ)⁻¹ = κᴴ * (M.fr τ * Z * (M.fr τ)⁻¹) * κ`. Simplify using `only [Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one, mul_nonsing_inv_cancel_left _ _ hu]`.

Rewrite using `[e]`. Conclude with `block_conj hκ.2 hJ hZ a b hab`. Rewrite `hi`, the goal using `[hs.2.2 τ c]`. Rewrite `hi` using `[Matrix.one_mul]`. Rewrite using `[hi, Matrix.one_mul, Matrix.mul_one]`.

Conclude with `hZ`.
-/
theorem adAt_mem_pMinus {θ : InfFam D} (hθ : IsInfFam θ) (M : DSModel T Sp) (ρ τ : D.what₂.Tau)
    {κ : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hκ : κ ∈ Formalism.REAL.Kset (M.ε ρ))
    {Z : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hZ : Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ) :
    adAt θ (atTau θ T ρ ((M.fr ρ)⁻¹ * κ * M.fr ρ)) τ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ := by
  have hs := atTau_spec hθ T ρ (frame_mem_UH M ρ hκ)
  have hi : infMat D.sp.cm.sig T.gram (θ τ) (atTau θ T ρ ((M.fr ρ)⁻¹ * κ * M.fr ρ)) *
      infMat D.sp.cm.sig T.gram (θ τ) (atTau θ T ρ ((M.fr ρ)⁻¹ * κ * M.fr ρ))⁻¹ = 1 := by
    rw [← infMat_mul, mul_inv_cancel, infMat_one]
  unfold adAt
  by_cases c : τ = ρ
  · subst c
    have hu : IsUnit (M.fr τ).det := (isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
    have h1 : κ * κᴴ = 1 := hκ.1.2
    have h1' : κᴴ * κ = 1 := hκ.1.1
    have hJ : κᴴ * Formalism.REAL.Jm (M.ε τ) = Formalism.REAL.Jm (M.ε τ) * κᴴ := by
      have := congrArg conjTranspose hκ.2
      rw [conjTranspose_mul, conjTranspose_mul, Formalism.REAL.Jm_conjTranspose] at this
      exact this.symm
    rw [hs.2.1] at hi ⊢
    have hi2 : (M.fr τ)⁻¹ * κ * M.fr τ * ((M.fr τ)⁻¹ * κᴴ * M.fr τ) = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc _ κᴴ, mul_nonsing_inv_cancel_left _ _ hu, Matrix.mul_assoc,
        ← Matrix.mul_assoc κ, h1, Matrix.one_mul, nonsing_inv_mul _ hu]
    rw [← inv_eq_right_inv hi, inv_eq_right_inv hi2]
    intro a b hab
    have e : M.fr τ * ((M.fr τ)⁻¹ * κᴴ * M.fr τ * Z * ((M.fr τ)⁻¹ * κ * M.fr τ)) * (M.fr τ)⁻¹ =
        κᴴ * (M.fr τ * Z * (M.fr τ)⁻¹) * κ := by
      simp only [Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one, mul_nonsing_inv_cancel_left _ _ hu]
    rw [e]
    exact block_conj hκ.2 hJ hZ a b hab
  · rw [hs.2.2 τ c] at hi ⊢
    rw [Matrix.one_mul] at hi
    rw [hi, Matrix.one_mul, Matrix.mul_one]
    exact hZ

variable {ψ : AddChar (AF D.host.F) ℂ} {S : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {θ : InfFam D}

/- English proof (translation)
Establish `key : ∀ X ∈ lieAt T τ, ∃ L : Module.End ℂ (WO S T → ℂ), ∀ f, IsThetaFunO ψ S T f → ∀ h, Rder θ T τ X (fun g => thetaKO om h g f) = fun g => thetaKO om h g (L f)`. Introduce `X hX`. Take `⟨L, hL⟩` from `GlobalTheory.T.exists_weilDatum_generator_realOneParamGroup D ψ S T χS χT om hom θ hθ τ X hX`. Use `⟨L, fun f hf h => funext fun g => ?_⟩` and prove the remaining obligations. Use `((hL f hf).2.2.2 (h, g) 0).deriv` as an intermediate fact.

Simplify using `only [Prod.mk_mul_mk, mul_one] at this`. Conclude with `this`. Take `⟨h1, h2⟩` from `GlobalTheory.SmoothAutCheck.parts_mem T τ Z`. Take `⟨L₁, e1⟩` from `key _ h1`. Take `⟨L₂, e2⟩` from `key _ h2`.

Use `⟨L₁ + Complex.I • L₂, fun f hf h => ?_⟩` and prove the remaining obligations. Unfold `RderC`. Rewrite using `[e1 f hf, e2 f hf]`. Use function extensionality and compare the values at `g`. Simplify using `[thetaKO]`.
-/
theorem exists_op (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
    (Z : Matrix (Fin T.rank) (Fin T.rank) ℂ) : ∃ L : Module.End ℂ (WO S T → ℂ), ∀ f, IsThetaFunO ψ S T f → ∀ h,
      RderC θ T τ Z (fun g => thetaKO om h g f) = fun g => thetaKO om h g (L f) := by
  have key : ∀ X ∈ lieAt T τ, ∃ L : Module.End ℂ (WO S T → ℂ), ∀ f, IsThetaFunO ψ S T f → ∀ h,
      Rder θ T τ X (fun g => thetaKO om h g f) = fun g => thetaKO om h g (L f) := by
    intro X hX
    obtain ⟨L, hL⟩ := GlobalTheory.T.exists_weilDatum_generator_realOneParamGroup D ψ S T χS χT om hom θ hθ τ X hX
    refine ⟨L, fun f hf h => funext fun g => ?_⟩
    have := ((hL f hf).2.2.2 (h, g) 0).deriv
    simp only [Prod.mk_mul_mk, mul_one] at this
    exact this
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem T τ Z
  obtain ⟨L₁, e1⟩ := key _ h1
  obtain ⟨L₂, e2⟩ := key _ h2
  refine ⟨L₁ + Complex.I • L₂, fun f hf h => ?_⟩
  unfold RderC
  rw [e1 f hf, e2 f hf]
  funext g
  simp [thetaKO]

def killed (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (M : DSModel T Sp) {Y : Type} [AddCommGroup Y]
    [Module ℂ Y] (pt : Y →ₗ[ℂ] (WO S T → ℂ)) (hpt : ∀ P, IsThetaFunO ψ S T (pt P)) : Submodule ℂ Y where
  carrier := {P | ∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ h, RderC θ T τ Z (fun g => thetaKO om h g (pt P)) = 0}
  add_mem' := by
    intro P Q hP hQ τ Z hZ h
    obtain ⟨L, hL⟩ := exists_op hom hθ τ Z
    have a := hP τ Z hZ h
    have b := hQ τ Z hZ h
    rw [hL _ (hpt _)] at a b ⊢
    funext g
    have a' := congrFun a g
    have b' := congrFun b g
    simp only [thetaKO, map_add, Pi.add_apply, Pi.zero_apply] at a' b' ⊢
    rw [a', b', add_zero]
  zero_mem' := by
    intro τ Z _ h
    obtain ⟨L, hL⟩ := exists_op hom hθ τ Z
    rw [hL _ (hpt _)]
    funext g
    simp [thetaKO]
  smul_mem' := by
    intro r P hP τ Z hZ h
    obtain ⟨L, hL⟩ := exists_op hom hθ τ Z
    have a := hP τ Z hZ h
    rw [hL _ (hpt _)] at a ⊢
    funext g
    have a' := congrFun a g
    simp only [thetaKO, map_smul, Pi.smul_apply, Pi.zero_apply] at a' ⊢
    rw [a', smul_zero]

/- English proof (translation)
Introduce `D ψ S T χS χT om hom θ hθ Sp M h1 h2 c hc pt hpt Δ io hio hΔ τ Z hZ v w h`. Take `⟨hS, hK, v₀, w₀, hv₀, hw₀, e₀⟩` from `hio`. Use `beta_reduce at hS hK`. Set `N` to `killed hom hθ M pt hpt`. Establish `step1 : ∀ w, io (PiTensorProduct.tprod ℂ v₀) w ∈ N`.

Take `⟨-, -, -, -, -, -, -, hd, -⟩` from `GlobalTheory.RealLift.exists_real_lift D θ S hθ`. It suffices to establish `hst : ∀ g, (N.comap (io (PiTensorProduct.tprod ℂ v₀))).map (c.ρ g) ≤ N.comap (io (PiTensorProduct.tprod ℂ v₀)) by`. Introduce `w`. Use `(((hc.2.2.2.2 _ hst).resolve_left fun h0 => ?_).ge Submodule.mem_top : w ∈ N.comap (io (PiTensorProduct.tprod ℂ v₀)))` and prove the remaining obligations. Establish `hm : w₀ ∈ N.comap (io (PiTensorProduct.tprod ℂ v₀))` using `by show io (PiTensorProduct.tprod ℂ v₀) w₀ ∈ N`.

Rewrite using `[e₀]`. Conclude with `hΔ`. Rewrite `hm` using `[h0, Submodule.mem_bot]`. Rewrite `hw₀` using `[hm, norm_zero]`. Conclude with `zero_ne_one hw₀`.

Introduce and unpack `g _ ⟨x, hx, rfl⟩`. Take `⟨a, ha, u, hu, rfl⟩` from `hd g`. Introduce `τ Z hZ h`. Establish `e : (fun g => thetaKO om h g (pt (io (PiTensorProduct.tprod ℂ v₀) (c.ρ (a * u) x)))) = fun g => thetaKO om (h * u) g (pt (io (PiTensorProduct.tprod ℂ v₀) x))`. Use function extensionality and compare the values at `g`.

Rewrite using `[map_mul, hc.1 a ha, one_mul, ← hS u hu]`. Unfold `thetaKO`. Rewrite using `[← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]`. Rewrite using `[e]`. Conclude with `hx τ Z hZ (h * u)`.

Set `B : MultilinearMap ℂ (fun τ => lowT M τ) (PolF D T.rank S.rank)` to `(io.flip w).compMultilinearMap (PiTensorProduct.tprod ℂ)`. Use `mem_of_translates h1 h2 B N v₀ (fun ρ h0 => ?_) (step1 w) ?_ v τ Z hZ h` and prove the remaining obligations. Use `hv₀ ρ` as an intermediate fact. Rewrite `this` using `[h0]`. Simplify using `at this`.

Introduce `ρ k hk v u hu hv τ Z hZ h`. Establish `e : (fun g => thetaKO om h g (pt (B (Function.update v ρ u)))) = rTr T (atTau θ T ρ ((M.fr ρ)⁻¹ * k * M.fr ρ)) fun g => thetaKO om h g (pt (B v))`. Use function extensionality and compare the values at `g`. Use `hK ρ k hk v u hu w` as an intermediate fact. Use `show om (h, g) (pt (io (PiTensorProduct.tprod ℂ (Function.update v ρ u)) w)) 0 = om (h, g * atTau θ T ρ ((M.fr ρ)⁻¹ * k * M.fr ρ)) (pt (io (PiTensorProduct.tprod ℂ v) w)) 0`.

Rewrite using `[← this, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]`. Rewrite using `[e, RderC_rTr hθ (isRealPt_atTau hθ ρ (frame_mem_UH M ρ hk)), hv τ _ (adAt_mem_pMinus hθ M ρ τ hk hZ) h]`. Both sides reduce to the same expression.
-/
theorem values_killed : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp), LowSm M → GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M → ∀ c : CoefA S, c.Is → ∀ pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ), (∀ P, IsThetaFunO ψ S T (pt P)) → ∀ (Δ : PolF D T.rank S.rank) (io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D T.rank S.rank), IsIoW θ M c om (fun P => pt P) Δ io → (∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ h, RderC θ T τ Z (fun g => thetaKO om h g (pt Δ)) = 0) → ∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ (v : ∀ ρ, lowT M ρ) w h, RderC θ T τ Z (fun g => thetaKO om h g (pt (io (PiTensorProduct.tprod ℂ v) w))) = 0 := by
  intro D ψ S T χS χT om hom θ hθ Sp M h1 h2 c hc pt hpt Δ io hio hΔ τ Z hZ v w h
  classical
  obtain ⟨hS, hK, v₀, w₀, hv₀, hw₀, e₀⟩ := hio
  beta_reduce at hS hK
  let N := killed hom hθ M pt hpt
  have step1 : ∀ w, io (PiTensorProduct.tprod ℂ v₀) w ∈ N := by
    obtain ⟨-, -, -, -, -, -, -, hd, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ S hθ
    suffices hst : ∀ g, (N.comap (io (PiTensorProduct.tprod ℂ v₀))).map (c.ρ g) ≤
        N.comap (io (PiTensorProduct.tprod ℂ v₀)) by
      intro w
      refine (((hc.2.2.2.2 _ hst).resolve_left fun h0 => ?_).ge Submodule.mem_top :
        w ∈ N.comap (io (PiTensorProduct.tprod ℂ v₀)))
      have hm : w₀ ∈ N.comap (io (PiTensorProduct.tprod ℂ v₀)) := by
        show io (PiTensorProduct.tprod ℂ v₀) w₀ ∈ N
        rw [e₀]
        exact hΔ
      rw [h0, Submodule.mem_bot] at hm
      rw [hm, norm_zero] at hw₀
      exact zero_ne_one hw₀
    · rintro g _ ⟨x, hx, rfl⟩
      obtain ⟨a, ha, u, hu, rfl⟩ := hd g
      intro τ Z hZ h
      have e : (fun g => thetaKO om h g (pt (io (PiTensorProduct.tprod ℂ v₀) (c.ρ (a * u) x)))) =
          fun g => thetaKO om (h * u) g (pt (io (PiTensorProduct.tprod ℂ v₀) x)) := by
        funext g
        rw [map_mul, hc.1 a ha, one_mul, ← hS u hu]
        unfold thetaKO
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
      rw [e]
      exact hx τ Z hZ (h * u)
  let B : MultilinearMap ℂ (fun τ => lowT M τ) (PolF D T.rank S.rank) :=
    (io.flip w).compMultilinearMap (PiTensorProduct.tprod ℂ)
  refine mem_of_translates h1 h2 B N v₀ (fun ρ h0 => ?_) (step1 w) ?_ v τ Z hZ h
  · have := hv₀ ρ
    rw [h0] at this
    simp at this
  · intro ρ k hk v u hu hv τ Z hZ h
    have e : (fun g => thetaKO om h g (pt (B (Function.update v ρ u)))) =
        rTr T (atTau θ T ρ ((M.fr ρ)⁻¹ * k * M.fr ρ)) fun g => thetaKO om h g (pt (B v)) := by
      funext g
      have := hK ρ k hk v u hu w
      show om (h, g) (pt (io (PiTensorProduct.tprod ℂ (Function.update v ρ u)) w)) 0 =
        om (h, g * atTau θ T ρ ((M.fr ρ)⁻¹ * k * M.fr ρ)) (pt (io (PiTensorProduct.tprod ℂ v) w)) 0
      rw [← this, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    rw [e, RderC_rTr hθ (isRealPt_atTau hθ ρ (frame_mem_UH M ρ hk)), hv τ _ (adAt_mem_pMinus hθ M ρ τ hk hZ) h]
    rfl

end GlobalTheory.DefLift.LowerKill

end

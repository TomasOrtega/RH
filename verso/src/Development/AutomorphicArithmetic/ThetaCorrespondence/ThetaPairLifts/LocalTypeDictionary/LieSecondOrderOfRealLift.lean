import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSecondOfPrints
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSecondOfPrintsStatement

section
noncomputable section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl
namespace GlobalTheory.RealLift.LieSecondPf
/- English proof (translation)
Introduce `_ hD hF hV hL F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ om χ m hCM hψ hFr hΦ hW hχ`. Take `⟨hU, dd, omd, hdd, hWS, hres⟩` from `hW`. Take `⟨c, hc⟩` from `hL F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ om hCM hψ hFr hΦ hU`. Establish `hFrd` using `GlobalTheory.T.doubled_hermitian_space_frame_of_frame F E α β P Q R S τ JA JB a b A C hFr`. Take `⟨Φd, hΦd⟩` from `hF F E σ α (β ⊕ β) (κ ⊕ κ) P Q (R + S) (S + R) ψ τ JA (dbl JB) dd a b A (fun w => dblM (C w)) hCM hψ hFrd`.

Take `⟨cd, hcd⟩` from `hL F E σ α (β ⊕ β) (κ ⊕ κ) P Q (R + S) (S + R) ψ τ JA (dbl JB) dd a b A (fun w => dblM (C w)) Φd omd hCM hψ hFrd hΦd hWS.2.1`. Establish `key : ∀ w (Y : Mat R S), c w * Y.trace = (m w : ℂ) / 2 * Y.trace`. Introduce `w Y`. Break down `Nat.eq_zero_or_pos (R + S) with h0 | hpos` into its components or cases. Establish `hR : R = 0` using `by omega`.

Establish `hS : S = 0` using `by omega`. Substitute `hR hS` using the available equality. Establish `: Y.trace = 0` using `by simp [Matrix.trace]`. Rewrite using `[this, mul_zero, mul_zero]`. Establish `hbox` using `GlobalTheory.T.doubledFockVacuum_eq_smul_vacuum_mul_conj hD hV F E σ α β κ P Q R S ψ τ JA JB d dd a b A C Φ Φd hCM hψ hFr hΦ hdd hΦd`.

Establish `hl` using `GlobalTheory.T.diagonal_integral_invariant_form_diagonalLagrangian F E σ α β κ ψ JA JB d dd hψ hdd`. Establish `hne : (∫ x : κ → mixedEmbedding.mixedSpace F, Φd (PiTensorProduct.tprod ℂ fun _ => 1) (Sum.elim x x)) ≠ 0`. Take `⟨z, hz, hzx⟩` from `hbox`. Establish `h1 : ∀ x : κ → mixedEmbedding.mixedSpace F, Φd (PiTensorProduct.tprod ℂ fun _ => 1) (Sum.elim x x) = z * (Φ (PiTensorProduct.tprod ℂ fun _ => 1) x * star (Φ (PiTensorProduct.tprod ℂ fun _ => 1) x))`. Introduce `x`.

Rewrite using `[hzx, Sum.elim_comp_inl, Sum.elim_comp_inr, mul_assoc]`. Repeatedly rewrite using `[h1]`. Rewrite using `[MeasureTheory.integral_const_mul]`. Use `mul_ne_zero hz (GlobalTheory.T.archimedeanSchwartz_integral_mul_star_ne_zero F κ _ ?_)` and prove the remaining obligations. Introduce `h0`.

Conclude with `GlobalTheory.T.tprod_constant_polynomials_ne_zero F P Q R S (hΦ.1 (by rw [h0, map_zero]))`. Establish `h1` using `GlobalTheory.T.doubledSpace_splitting_constant_half_realPlaces F E σ α β κ P Q R S ψ τ JA JB dd a b A C Φd omd χ m cd hCM hψ hFr hWS hχ hcd hl hne hpos w`. Establish `h2` using `GlobalTheory.T.realPlace_splittingConstant_eq_doubledSpace F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ Φd om omd c cd hCM hψ hΦ hres hc hcd hbox hpos w`. Rewrite using `[h2, h1]`. Introduce `γ hγ Y hY T`.

Establish `e : (fun w => fockAct2 P Q R S (Y w) + (((m w : ℂ) / 2) * (Y w).trace) • (1 : Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))) = fun w => fockAct2 P Q R S (Y w) + (c w * (Y w).trace) • 1`. Use function extensionality and compare the values at `w`. Rewrite using `[key w (Y w)]`. Use `hc γ hγ Y hY T` as an intermediate fact. Rewrite `this` using `[← e]`.

Conclude with `this`.
-/
theorem lie_second_order_of_real_lift : _root_.GlobalTheory.FunPr.ThetaLocalInputs → DerEx → FockEx → VacLine → LieScalar → LieSecond := by
  intro _ hD hF hV hL F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ om χ m hCM hψ hFr hΦ hW hχ
  obtain ⟨hU, dd, omd, hdd, hWS, hres⟩ := hW
  obtain ⟨c, hc⟩ := hL F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ om hCM hψ hFr hΦ hU
  have hFrd := GlobalTheory.T.doubled_hermitian_space_frame_of_frame F E α β P Q R S τ JA JB a b A C hFr
  obtain ⟨Φd, hΦd⟩ := hF F E σ α (β ⊕ β) (κ ⊕ κ) P Q (R + S) (S + R) ψ τ JA (dbl JB) dd a b A
    (fun w => dblM (C w)) hCM hψ hFrd
  obtain ⟨cd, hcd⟩ := hL F E σ α (β ⊕ β) (κ ⊕ κ) P Q (R + S) (S + R) ψ τ JA (dbl JB) dd a b A
    (fun w => dblM (C w)) Φd omd hCM hψ hFrd hΦd hWS.2.1
  have key : ∀ w (Y : Mat R S), c w * Y.trace = (m w : ℂ) / 2 * Y.trace := by
    intro w Y
    rcases Nat.eq_zero_or_pos (R + S) with h0 | hpos
    · have hR : R = 0 := by omega
      have hS : S = 0 := by omega
      subst hR hS
      have : Y.trace = 0 := by simp [Matrix.trace]
      rw [this, mul_zero, mul_zero]
    · have hbox := GlobalTheory.T.doubledFockVacuum_eq_smul_vacuum_mul_conj hD hV F E σ α β κ P Q R S ψ τ JA JB d dd a b A C Φ Φd hCM hψ hFr hΦ hdd hΦd
      have hl := GlobalTheory.T.diagonal_integral_invariant_form_diagonalLagrangian F E σ α β κ ψ JA JB d dd hψ hdd
      have hne : (∫ x : κ → mixedEmbedding.mixedSpace F,
          Φd (PiTensorProduct.tprod ℂ fun _ => 1) (Sum.elim x x)) ≠ 0 := by
        obtain ⟨z, hz, hzx⟩ := hbox
        have h1 : ∀ x : κ → mixedEmbedding.mixedSpace F, Φd (PiTensorProduct.tprod ℂ fun _ => 1) (Sum.elim x x) =
            z * (Φ (PiTensorProduct.tprod ℂ fun _ => 1) x * star (Φ (PiTensorProduct.tprod ℂ fun _ => 1) x)) := by
          intro x
          rw [hzx, Sum.elim_comp_inl, Sum.elim_comp_inr, mul_assoc]
        simp_rw [h1]
        rw [MeasureTheory.integral_const_mul]
        refine mul_ne_zero hz (GlobalTheory.T.archimedeanSchwartz_integral_mul_star_ne_zero F κ _ ?_)
        intro h0
        exact GlobalTheory.T.tprod_constant_polynomials_ne_zero F P Q R S (hΦ.1 (by rw [h0, map_zero]))
      have h1 := GlobalTheory.T.doubledSpace_splitting_constant_half_realPlaces F E σ α β κ P Q R S ψ τ JA JB dd a b A C Φd omd χ m cd hCM hψ hFr hWS hχ hcd hl hne hpos w
      have h2 := GlobalTheory.T.realPlace_splittingConstant_eq_doubledSpace F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ Φd om omd c cd hCM hψ hΦ hres hc hcd hbox hpos w
      rw [h2, h1]
  intro γ hγ Y hY T
  have e : (fun w => fockAct2 P Q R S (Y w) + (((m w : ℂ) / 2) * (Y w).trace) • (1 : Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))) =
      fun w => fockAct2 P Q R S (Y w) + (c w * (Y w).trace) • 1 := by
    funext w
    rw [key w (Y w)]
  have := hc γ hγ Y hY T
  rw [← e] at this
  exact this
end GlobalTheory.RealLift.LieSecondPf
end
end

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.RealLift.LieSecondPf.lie_second_order_of_real_lift | exact _root_.GlobalTheory.RealLift.LieSecondPf.lie_second_order_of_real_lift | (intros; apply _root_.GlobalTheory.RealLift.LieSecondPf.lie_second_order_of_real_lift <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.real_lift_lie_second_order : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.FockEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar → GlobalTheory.RealLift.LieSecond := by
  first | exact @_root_.GlobalTheory.RealLift.LieSecondPf.lie_second_order_of_real_lift | exact _root_.GlobalTheory.RealLift.LieSecondPf.lie_second_order_of_real_lift | (intros; apply _root_.GlobalTheory.RealLift.LieSecondPf.lie_second_order_of_real_lift <;> assumption)
end

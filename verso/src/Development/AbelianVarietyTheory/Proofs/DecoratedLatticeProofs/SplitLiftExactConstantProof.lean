import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DoubleCollapse
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedThetaLiftCommutesSplitPlaceOperators
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearModelSplitPlaceCharacterEquivarianceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelsCommuteExplicitConstStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing MeasureTheory

noncomputable section

namespace GlobalTheory.FinPl.LiftExactPf

/- English proof (translation)
Establish `h1` using `Matrix.rank_mul_le_left α.b α.b'`. Establish `h2` using `Matrix.rank_mul_le_left α.b' α.b`. Rewrite `h1` using `[α.bb', Matrix.rank_one]`. Rewrite `h2` using `[α.b'b, Matrix.rank_one]`. Establish `h3` using `Matrix.rank_le_card_width α.b`.

Establish `h4` using `Matrix.rank_le_card_width α.b'`. Simplify using `only [Fintype.card_fin] at h1 h4`. Use linear arithmetic over natural numbers and integers.
-/
theorem frame_card {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (α : Frame p S n) :
    Fintype.card n = S.rank := by
  have h1 := Matrix.rank_mul_le_left α.b α.b'
  have h2 := Matrix.rank_mul_le_left α.b' α.b
  rw [α.bb', Matrix.rank_one] at h1
  rw [α.b'b, Matrix.rank_one] at h2
  have h3 := Matrix.rank_le_card_width α.b
  have h4 := Matrix.rank_le_card_width α.b'
  simp only [Fintype.card_fin] at h1 h4
  omega

/- English proof (translation)
Unfold `chrPow`. Rewrite using `[← Circle.coe_mul, ← zpow_add, add_neg_cancel, zpow_zero, Circle.coe_one]`.
-/
theorem chrPow_mul_neg {D : D7} (χ : (AE D)ˣ →* Circle) (a : (AE D)ˣ) (e : ℤ) :
    chrPow χ a e * chrPow χ a (-e) = 1 := by
  unfold chrPow
  rw [← Circle.coe_mul, ← zpow_add, add_neg_cancel, zpow_zero, Circle.coe_one]

end GlobalTheory.FinPl.LiftExactPf

namespace GlobalTheory.FinPl

open GlobalTheory.FinPl.LiftRam GlobalTheory.FinPl.LiftExactPf in

/- English proof (translation)
Introduce `D k _ _ _ _ p q χ hχ`. Use `⟨-1, Or.inr rfl, ?_⟩` and prove the remaining obligations. Introduce `n n' _ _ _ _ ψ S T hS vS χS χT om hW hχS hχT α β P Q a ha LS LT f₀ f hOv φ₀ hφ₀ ε`. Establish `haq : a = p.idele q.unit` using `Units.ext (by rw [SplitPt.idele_val, ha]; abel)`. Substitute `haq` using the available equality.

Take `⟨lS, lT, hlS, hlT, hlSq, hlTq, hlinE⟩` from `GlobalTheory.T.linearModel_splitPlace_characterEquivariance D k p q ψ S T χS χT om hW`. Take `⟨lS₀, lT₀, -, -, hlin⟩` from `GlobalTheory.T.splitPlace_linearModel_latticeVacuum_base D k p ψ S T χS χT om hW`. Establish `hK` using `GlobalTheory.T.kernelsCommuteExplicitConstAlt k n n' q χ hχ lS lT (hlS hχT) (hlT hχS) P Q`. Establish `hOv2` using `hOv`. Take `⟨hLS, hLT, hVac, -, -⟩` from `hOv2`.

Take `⟨hex, hth, -⟩` from `GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hW.std S T α β LS LT hLS hLT f₀ hVac`. Set `F : SB (Matrix n n' k) → WO S T → ℂ` to `fun Ψ => (hex Ψ.1 Ψ.2).exists.choose`. Establish `hF : ∀ Ψ : SB (Matrix n n' k), Over ψ α β LS LT f₀ Ψ.1 (F Ψ)` using `fun Ψ => (hex Ψ.1 Ψ.2).exists.choose_spec`. Establish `hFu : ∀ (Ψ : SB (Matrix n n' k)) g, Over ψ α β LS LT f₀ Ψ.1 g → g = F Ψ` using `fun Ψ g hg => (hex Ψ.1 Ψ.2).unique hg (hF Ψ)`. Establish `hFth : ∀ Ψ, IsThetaFunO ψ S T (F Ψ)` using `fun Ψ => (hth _ _ (hF Ψ)).1`.

Establish `hFlin : ∀ (a : ℂ) (Ψ Ψ' : SB (Matrix n n' k)), F (a • Ψ + Ψ') = a • F Ψ + F Ψ'` using `fun a Ψ Ψ' => (hFu (a • Ψ + Ψ') _ ((hlin n n' α β LS LT f₀ Ψ.1 (F Ψ) (hF Ψ)).2.2 a Ψ'.1 (F Ψ') (hF Ψ'))).symm`. Establish `hF0 : F 0 = 0`. Establish `h1` using `hFlin 1 0 0`. Simplify using `only [one_smul, add_zero] at h1`. Establish `h2 : F 0 + F 0 = F 0 + 0` using `by rw [← h1, add_zero]`.

Conclude with `add_left_cancel h2`. Establish `hFadd : ∀ Ψ Ψ' : SB (Matrix n n' k), F (Ψ + Ψ') = F Ψ + F Ψ'` using `fun Ψ Ψ' => by`. Simplify using `using hFlin 1 Ψ Ψ'`. Establish `hFsmul : ∀ (a : ℂ) (Ψ : SB (Matrix n n' k)), F (a • Ψ) = a • F Ψ` using `fun a Ψ => by`. Simplify `hFlin a Ψ 0` using `[hF0]`.

Establish `hint : ∀ (v : contAutSub S) (Ψ : SB (Matrix n n' k)) h, IntegrableOn (fun g => om (g, h) (F Ψ) 0 * v.1 g) vS.𝓕 vS.μ` using `fun v Ψ h => (lift_facts hS vS hW (hFth Ψ) v.2).1 h`. Set `θ : contAutSub S →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] (GA D T → ℂ)` to `LinearMap.mk₂ ℂ (fun v Ψ => liftT om vS.μ vS.𝓕 v.1 (F Ψ)) (fun v₁ v₂ Ψ => by`. Use function extensionality and compare the values at `h`. Simplify using `only [liftT_apply, Pi.add_apply, Submodule.coe_add, mul_add]`. Conclude with `integral_add (hint v₁ Ψ h) (hint v₂ Ψ h))`.

Use the proof step `(fun a v Ψ => by`. Use function extensionality and compare the values at `h`. Simplify using `only [liftT_apply, Pi.smul_apply, Submodule.coe_smul, smul_eq_mul, mul_left_comm _ a]`. Conclude with `integral_const_mul a _)`. Use the proof step `(fun v Ψ₁ Ψ₂ => by`.

Use function extensionality and compare the values at `h`. Simplify using `only [liftT_apply, Pi.add_apply, hFadd, map_add, add_mul]`. Conclude with `integral_add (hint v Ψ₁ h) (hint v Ψ₂ h))`. Use the proof step `(fun a v Ψ => by`. Use function extensionality and compare the values at `h`.

Simplify using `only [liftT_apply, Pi.smul_apply, hFsmul, map_smul, smul_eq_mul, mul_assoc]`. Conclude with `integral_const_mul a _)`. Establish `hθ : ∀ v Ψ, θ v Ψ = liftT om vS.μ vS.𝓕 v.1 (F Ψ)` using `fun v Ψ => rfl`. Establish `hEq : ∀ (g : GL n' k) (h : GL n k) (v : contAutSub S) (Ψ Ψ' : SB (Matrix n n' k)), (∀ x, Ψ'.1 x = (lS (Matrix.GeneralLinearGroup.det g) : ℂ) * (lT (Matrix.GeneralLinearGroup.det h) : ℂ) * Ψ.1 ((h⁻¹ : GL n k).val * x * g.val)) → θ (repAut α g v) Ψ' = β.rep h (θ v Ψ)`. Introduce `g h v Ψ Ψ' hΨ`.

Establish `e : F Ψ' = om (α.gl g, β.gl h) (F Ψ)`. Use `(hFu Ψ' _ ?_).symm` and prove the remaining obligations. Use `hlinE n n' α β LS LT f₀ Ψ.1 (F Ψ) (hF Ψ) g h` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`.

Conclude with `hΨ x`. Use function extensionality and compare the values at `h₁`. Rewrite using `[hθ, hθ, rep_apply, liftT_apply, liftT_apply, e, repAut_val]`. Simplify using `only [rep_apply, LiftRam.om_mul]`. Conclude with `setIntegral_mul_right hS vS (fun x => om (x, h₁ * β.gl h) (F Ψ) 0 * v.1 x) (fun γ hγ x => by rw [om_left hW (hFth Ψ) hγ, v.2.1 γ hγ x]) (α.gl g)`.

Take `⟨K, hKval, hKdia, hKram⟩` from `hK (contAutSub S) (GA D T → ℂ) (repAut α) β.rep θ hEq`. Take `⟨φ, ⟨hφE, hφM, hφC⟩, rfl⟩` from `hφ₀`. Set `φ' : EqForm (repAut α)` to `⟨toAut hφC, fun g P₁ => Subtype.ext (hφE g P₁)⟩`. Establish `hφ'M : φ'.1 ∈ Mram k n' (contAutSub S)`. Use `letI := Fintype.ofFinite 𝓀[k]ˣ`.

Use `(mem_Mram _).2 fun P₁ => Subtype.ext ?_` and prove the remaining obligations. Use `(mem_Mram _).1 hφM P₁` as an intermediate fact. Simplify `this` using `[φ', toAut, Submodule.coe_sum]`. Establish `hFf : F (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOneSB P Q) = f` using `(hFu _ f hOv).symm`. Establish `hfth : IsThetaFunO ψ S T f` using `hFf ▸ hFth _`.

Use `set φT : Form k n (GA D T → ℂ) := (K φ').1 with hφT`. Establish `hφTQ : φT Q = liftT om vS.μ vS.𝓕 (φ P) f`. Rewrite using `[hφT, hKval φ', hθ, hFf]`. Both sides reduce to the same expression. Establish `hcQ : IsContAut T (φT Q)`.

Rewrite using `[hφTQ]`. Conclude with `(lift_facts hS vS hW hfth (hφC P)).2`. Establish `hRam : IsRam β φT`. Use `⟨(K φ').2, (hKram φ' hφ'M).1, fun Q' => ?_⟩` and prove the remaining obligations. Take `⟨g, rfl⟩` from `MulAction.exists_smul_eq (GL n k) Q Q'`.

Establish `e : φT (g • Q) = β.rep g (φT Q)` using `(K φ').2 g Q`. Rewrite using `[e]`. Conclude with `isContAut_mul_right hcQ (β.gl g)`. Use `set c : ℂ := (lS q.unit : ℂ) * (lT q.unit : ℂ) with hc`. Establish `h1` using `(hKram φ' hφ'M).2`.

Establish `h2` using `hKdia ε ⟨FFStar q (resChar χ hχ q) φ'.1, FFStar_mem_EqForm q _ φ'.2⟩`. Establish `h3` using `hKval ⟨dia ε (FFStar q (resChar χ hχ q) φ'.1), dia_mem_EqForm ε (FFStar_mem_EqForm q _ φ'.2)⟩`. Establish `key : liftT om vS.μ vS.𝓕 (FFStar q (resChar χ hχ q) φ (ε • P)) f = c • FFStar q (resChar χ hχ q) φT (ε • Q)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hθ, hFf, dia_apply]`.

Conclude with `congrArg (liftT om vS.μ vS.𝓕 · f) (toAut_FFStar q _ hφC (ε • P)).symm`. Use `_ = (K ⟨dia ε (FFStar q (resChar χ hχ q) φ'.1), dia_mem_EqForm ε (FFStar_mem_EqForm q _ φ'.2)⟩).1 Q := h3.symm`. Use `_ = dia ε (K ⟨FFStar q (resChar χ hχ q) φ'.1, FFStar_mem_EqForm q _ φ'.2⟩).1 Q := by rw [h2]`. Use `_ = c • FFStar q (resChar χ hχ q) φT (ε • Q) := by rw [h1, dia_apply]; rfl`. Establish `hQ : (0 : ℝ) < resCard k`.

Unfold `resCard`. Conclude with `Nat.card_pos` after adjusting the coercions. Establish `hnT` using `frame_card β`. Establish `hnS` using `frame_card α`. Establish `hR : ((resCard k : ℝ) ^ (((Fintype.card n : ℝ) - Fintype.card n') / 2)) * ((resCard k : ℝ) ^ (-(T.rank : ℝ) / 2)) * ((resCard k : ℝ) ^ ((S.rank : ℝ) / 2)) = 1`.

Rewrite using `[← Real.rpow_add hQ, ← Real.rpow_add hQ, hnT, hnS]`. Use `Real.rpow_zero (resCard k : ℝ) using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `hR' : (((resCard k : ℝ) ^ (((Fintype.card n : ℝ) - Fintype.card n') / 2) : ℝ) : ℂ) * (((resCard k : ℝ) ^ (-(T.rank : ℝ) / 2) : ℝ) : ℂ) * (((resCard k : ℝ) ^ ((S.rank : ℝ) / 2) : ℝ) : ℂ) = 1`. Conclude with `hR` after adjusting the coercions.

Establish `eS` using `chrPow_mul_neg χS (p.idele q.unit) (-1)`. Establish `eT` using `chrPow_mul_neg χT (p.idele q.unit) 1`. Simplify using `only [neg_neg] at eS ⊢`. Establish `hCc : ((((resCard k : ℝ) ^ (((Fintype.card n : ℝ) - Fintype.card n') / 2) : ℝ) : ℂ) * chrPow χS (p.idele q.unit) (-1) * chrPow χT (p.idele q.unit) 1) * c = 1`. Rewrite using `[hc, hlSq, hlTq]`.

Take the linear combination `(chrPow χS (p.idele q.unit) (-1) * chrPow χS (p.idele q.unit) 1 * (chrPow χT (p.idele q.unit) 1 * chrPow χT (p.idele q.unit) (-1))) * hR' + (chrPow χT (p.idele q.unit) 1 * chrPow χT (p.idele q.unit) (-1)) * eS + eT`. Rewrite using `[← hφTQ]`. Unfold `sOp`. Rewrite using `[formAt_eq α hφE P, formAt_eq β hRam.1 Q, dia_apply, dia_apply, key, smul_smul, hCc, one_smul]`.
-/
theorem liftExact : ∀ D : D7, GlobalTheory.FinPl.LiftExact D := by
  intro D k _ _ _ _ p q χ hχ
  refine ⟨-1, Or.inr rfl, ?_⟩
  intro n n' _ _ _ _ ψ S T hS vS χS χT om hW hχS hχT α β P Q a ha LS LT f₀ f hOv φ₀ hφ₀ ε
  have haq : a = p.idele q.unit := Units.ext (by rw [SplitPt.idele_val, ha]; abel)
  subst haq
  obtain ⟨lS, lT, hlS, hlT, hlSq, hlTq, hlinE⟩ := GlobalTheory.T.linearModel_splitPlace_characterEquivariance D k p q ψ S T χS χT om hW
  obtain ⟨lS₀, lT₀, -, -, hlin⟩ := GlobalTheory.T.splitPlace_linearModel_latticeVacuum_base D k p ψ S T χS χT om hW
  have hK := GlobalTheory.T.kernelsCommuteExplicitConstAlt k n n' q χ hχ lS lT (hlS hχT) (hlT hχS) P Q
  have hOv2 := hOv
  obtain ⟨hLS, hLT, hVac, -, -⟩ := hOv2
  obtain ⟨hex, hth, -⟩ := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hW.std S T α β LS LT hLS hLT f₀ hVac

  let F : SB (Matrix n n' k) → WO S T → ℂ := fun Ψ => (hex Ψ.1 Ψ.2).exists.choose
  have hF : ∀ Ψ : SB (Matrix n n' k), Over ψ α β LS LT f₀ Ψ.1 (F Ψ) := fun Ψ => (hex Ψ.1 Ψ.2).exists.choose_spec
  have hFu : ∀ (Ψ : SB (Matrix n n' k)) g, Over ψ α β LS LT f₀ Ψ.1 g → g = F Ψ :=
    fun Ψ g hg => (hex Ψ.1 Ψ.2).unique hg (hF Ψ)
  have hFth : ∀ Ψ, IsThetaFunO ψ S T (F Ψ) := fun Ψ => (hth _ _ (hF Ψ)).1
  have hFlin : ∀ (a : ℂ) (Ψ Ψ' : SB (Matrix n n' k)), F (a • Ψ + Ψ') = a • F Ψ + F Ψ' := fun a Ψ Ψ' =>
    (hFu (a • Ψ + Ψ') _ ((hlin n n' α β LS LT f₀ Ψ.1 (F Ψ) (hF Ψ)).2.2 a Ψ'.1 (F Ψ') (hF Ψ'))).symm
  have hF0 : F 0 = 0 := by
    have h1 := hFlin 1 0 0
    simp only [one_smul, add_zero] at h1
    have h2 : F 0 + F 0 = F 0 + 0 := by rw [← h1, add_zero]
    exact add_left_cancel h2
  have hFadd : ∀ Ψ Ψ' : SB (Matrix n n' k), F (Ψ + Ψ') = F Ψ + F Ψ' := fun Ψ Ψ' => by
    simpa using hFlin 1 Ψ Ψ'
  have hFsmul : ∀ (a : ℂ) (Ψ : SB (Matrix n n' k)), F (a • Ψ) = a • F Ψ := fun a Ψ => by
    simpa [hF0] using hFlin a Ψ 0
  have hint : ∀ (v : contAutSub S) (Ψ : SB (Matrix n n' k)) h,
      IntegrableOn (fun g => om (g, h) (F Ψ) 0 * v.1 g) vS.𝓕 vS.μ :=
    fun v Ψ h => (lift_facts hS vS hW (hFth Ψ) v.2).1 h

  let θ : contAutSub S →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] (GA D T → ℂ) :=
    LinearMap.mk₂ ℂ (fun v Ψ => liftT om vS.μ vS.𝓕 v.1 (F Ψ))
      (fun v₁ v₂ Ψ => by
        funext h
        simp only [liftT_apply, Pi.add_apply, Submodule.coe_add, mul_add]
        exact integral_add (hint v₁ Ψ h) (hint v₂ Ψ h))
      (fun a v Ψ => by
        funext h
        simp only [liftT_apply, Pi.smul_apply, Submodule.coe_smul, smul_eq_mul, mul_left_comm _ a]
        exact integral_const_mul a _)
      (fun v Ψ₁ Ψ₂ => by
        funext h
        simp only [liftT_apply, Pi.add_apply, hFadd, map_add, add_mul]
        exact integral_add (hint v Ψ₁ h) (hint v Ψ₂ h))
      (fun a v Ψ => by
        funext h
        simp only [liftT_apply, Pi.smul_apply, hFsmul, map_smul, smul_eq_mul, mul_assoc]
        exact integral_const_mul a _)
  have hθ : ∀ v Ψ, θ v Ψ = liftT om vS.μ vS.𝓕 v.1 (F Ψ) := fun v Ψ => rfl
  have hEq : ∀ (g : GL n' k) (h : GL n k) (v : contAutSub S) (Ψ Ψ' : SB (Matrix n n' k)),
      (∀ x, Ψ'.1 x = (lS (Matrix.GeneralLinearGroup.det g) : ℂ) * (lT (Matrix.GeneralLinearGroup.det h) : ℂ) *
        Ψ.1 ((h⁻¹ : GL n k).val * x * g.val)) → θ (repAut α g v) Ψ' = β.rep h (θ v Ψ) := by
    intro g h v Ψ Ψ' hΨ
    have e : F Ψ' = om (α.gl g, β.gl h) (F Ψ) := by
      refine (hFu Ψ' _ ?_).symm
      have := hlinE n n' α β LS LT f₀ Ψ.1 (F Ψ) (hF Ψ) g h
      convert this using 1
      funext x
      exact hΨ x
    funext h₁
    rw [hθ, hθ, rep_apply, liftT_apply, liftT_apply, e, repAut_val]
    simp only [rep_apply, LiftRam.om_mul]
    exact setIntegral_mul_right hS vS (fun x => om (x, h₁ * β.gl h) (F Ψ) 0 * v.1 x)
      (fun γ hγ x => by rw [om_left hW (hFth Ψ) hγ, v.2.1 γ hγ x]) (α.gl g)
  obtain ⟨K, hKval, hKdia, hKram⟩ := hK (contAutSub S) (GA D T → ℂ) (repAut α) β.rep θ hEq
  obtain ⟨φ, ⟨hφE, hφM, hφC⟩, rfl⟩ := hφ₀
  let φ' : EqForm (repAut α) := ⟨toAut hφC, fun g P₁ => Subtype.ext (hφE g P₁)⟩
  have hφ'M : φ'.1 ∈ Mram k n' (contAutSub S) := by
    letI := Fintype.ofFinite 𝓀[k]ˣ
    refine (mem_Mram _).2 fun P₁ => Subtype.ext ?_
    have := (mem_Mram _).1 hφM P₁
    simpa [φ', toAut, Submodule.coe_sum] using this
  have hFf : F (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOneSB P Q) = f := (hFu _ f hOv).symm
  have hfth : IsThetaFunO ψ S T f := hFf ▸ hFth _
  set φT : Form k n (GA D T → ℂ) := (K φ').1 with hφT
  have hφTQ : φT Q = liftT om vS.μ vS.𝓕 (φ P) f := by
    rw [hφT, hKval φ', hθ, hFf]
    rfl
  have hcQ : IsContAut T (φT Q) := by
    rw [hφTQ]
    exact (lift_facts hS vS hW hfth (hφC P)).2
  have hRam : IsRam β φT := by
    refine ⟨(K φ').2, (hKram φ' hφ'M).1, fun Q' => ?_⟩
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n k) Q Q'
    have e : φT (g • Q) = β.rep g (φT Q) := (K φ').2 g Q
    rw [e]
    exact isContAut_mul_right hcQ (β.gl g)
  set c : ℂ := (lS q.unit : ℂ) * (lT q.unit : ℂ) with hc
  have h1 := (hKram φ' hφ'M).2
  have h2 := hKdia ε ⟨FFStar q (resChar χ hχ q) φ'.1, FFStar_mem_EqForm q _ φ'.2⟩
  have h3 := hKval ⟨dia ε (FFStar q (resChar χ hχ q) φ'.1), dia_mem_EqForm ε (FFStar_mem_EqForm q _ φ'.2)⟩
  have key : liftT om vS.μ vS.𝓕 (FFStar q (resChar χ hχ q) φ (ε • P)) f =
      c • FFStar q (resChar χ hχ q) φT (ε • Q) := by
    calc liftT om vS.μ vS.𝓕 (FFStar q (resChar χ hχ q) φ (ε • P)) f
        = θ (dia ε (FFStar q (resChar χ hχ q) φ'.1) P) (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOneSB P Q) := by
          rw [hθ, hFf, dia_apply]
          exact congrArg (liftT om vS.μ vS.𝓕 · f) (toAut_FFStar q _ hφC (ε • P)).symm
      _ = (K ⟨dia ε (FFStar q (resChar χ hχ q) φ'.1), dia_mem_EqForm ε (FFStar_mem_EqForm q _ φ'.2)⟩).1 Q := h3.symm
      _ = dia ε (K ⟨FFStar q (resChar χ hχ q) φ'.1, FFStar_mem_EqForm q _ φ'.2⟩).1 Q := by rw [h2]
      _ = c • FFStar q (resChar χ hχ q) φT (ε • Q) := by rw [h1, dia_apply]; rfl

  have hQ : (0 : ℝ) < resCard k := by
    unfold resCard
    exact_mod_cast Nat.card_pos
  have hnT := frame_card β
  have hnS := frame_card α
  have hR : ((resCard k : ℝ) ^ (((Fintype.card n : ℝ) - Fintype.card n') / 2)) * ((resCard k : ℝ) ^ (-(T.rank : ℝ) / 2)) *
      ((resCard k : ℝ) ^ ((S.rank : ℝ) / 2)) = 1 := by
    rw [← Real.rpow_add hQ, ← Real.rpow_add hQ, hnT, hnS]
    convert Real.rpow_zero (resCard k : ℝ) using 2
    ring
  have hR' : (((resCard k : ℝ) ^ (((Fintype.card n : ℝ) - Fintype.card n') / 2) : ℝ) : ℂ) *
      (((resCard k : ℝ) ^ (-(T.rank : ℝ) / 2) : ℝ) : ℂ) * (((resCard k : ℝ) ^ ((S.rank : ℝ) / 2) : ℝ) : ℂ) = 1 := by
    exact_mod_cast hR
  have eS := chrPow_mul_neg χS (p.idele q.unit) (-1)
  have eT := chrPow_mul_neg χT (p.idele q.unit) 1
  simp only [neg_neg] at eS ⊢
  have hCc : ((((resCard k : ℝ) ^ (((Fintype.card n : ℝ) - Fintype.card n') / 2) : ℝ) : ℂ) *
      chrPow χS (p.idele q.unit) (-1) * chrPow χT (p.idele q.unit) 1) * c = 1 := by
    rw [hc, hlSq, hlTq]
    linear_combination (chrPow χS (p.idele q.unit) (-1) * chrPow χS (p.idele q.unit) 1 *
      (chrPow χT (p.idele q.unit) 1 * chrPow χT (p.idele q.unit) (-1))) * hR' +
      (chrPow χT (p.idele q.unit) 1 * chrPow χT (p.idele q.unit) (-1)) * eS + eT
  rw [← hφTQ]
  unfold sOp
  rw [formAt_eq α hφE P, formAt_eq β hRam.1 Q, dia_apply, dia_apply, key, smul_smul, hCc, one_smul]

end GlobalTheory.FinPl

end

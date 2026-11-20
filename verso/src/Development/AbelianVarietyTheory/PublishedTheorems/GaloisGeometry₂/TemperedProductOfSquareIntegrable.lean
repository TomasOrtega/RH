import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedCoeff

noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.Published

def TemperedProductOfSquareIntegrable : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (N : ℕ), 1 ≤ N →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible →
      (IsTemperedCoeff π ↔ ∃ (h : ℕ) (δ : Fin h → IrrGL k) (hd : ∑ i, (δ i).1 = N),
        (∀ i, 1 ≤ (δ i).1 ∧ IsSqIntCoeff (δ i).rep) ∧ Nonempty (π.Equiv (prodIrr δ hd)))

namespace TemperedProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem coeffLp_of_equiv {N : ℕ} {p : ℝ} {π : Representation ℂ (GL (Fin N) k) V} {σ : Representation ℂ (GL (Fin N) k) W}
    (φ : π.Equiv σ) (h : CoeffLp p π) : CoeffLp p σ := by
  intro _ _ μ hμ w l hl
  have hφ : ∀ g v, φ.toLinearEquiv (π g v) = σ g (φ.toLinearEquiv v) := fun g v =>
    φ.toIntertwiningMap.isIntertwining _ _ g v
  have hs : {g : GL (Fin N) k | (l ∘ₗ φ.toLinearEquiv.toLinearMap) ∘ₗ π g = l ∘ₗ φ.toLinearEquiv.toLinearMap} =
      {g : GL (Fin N) k | l ∘ₗ σ g = l} := by
    ext g
    refine ⟨fun H => LinearMap.ext fun x => ?_, fun H => LinearMap.ext fun x => ?_⟩
    · have h1 : l (φ.toLinearEquiv (π g (φ.toLinearEquiv.symm x))) = l (φ.toLinearEquiv (φ.toLinearEquiv.symm x)) :=
        LinearMap.congr_fun H (φ.toLinearEquiv.symm x)
      rwa [hφ, LinearEquiv.apply_symm_apply] at h1
    · show l (φ.toLinearEquiv (π g x)) = l (φ.toLinearEquiv x)
      rw [hφ]
      exact LinearMap.congr_fun H _
  obtain ⟨F, hF, hF'⟩ := h μ hμ (φ.toLinearEquiv.symm w) (l ∘ₗ φ.toLinearEquiv.toLinearMap) (hs ▸ hl)
  refine ⟨F, fun g => ?_, hF'⟩
  rw [hF, LinearMap.comp_apply, LinearEquiv.coe_coe, hφ, LinearEquiv.apply_symm_apply]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Proceed by induction. Proceed by induction. Reduce the conclusion to the remaining proof obligations. Replace the chosen expression with an arbitrary variable.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem subsingleton_adGL_one : Subsingleton (AdGL k 1) := by
  refine ⟨fun a b => ?_⟩
  induction a using QuotientGroup.induction_on
  induction b using QuotientGroup.induction_on
  refine QuotientGroup.eq.2 (Subgroup.mem_center_iff.2 fun g => ?_)
  generalize (_⁻¹ * _ : GL (Fin 1) k) = c
  ext i j
  simp [Matrix.mul_apply, Subsingleton.elim i 0, Subsingleton.elim j 0, mul_comm]

/- English proof (translation)
Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion.

By extensionality, compare the relevant components. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem coeffLp_detRep_one_iff (p : ℝ) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    CoeffLp p (detRep (Fin 1) χ) ↔ ∀ x, ‖(χ x : ℂ)‖ = 1 := by
  haveI : Subsingleton (AdGL k 1) := subsingleton_adGL_one
  have key : ∀ g v, detRep (Fin 1) χ g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v := fun _ _ => rfl
  constructor
  · intro h x
    borelize (AdGL k 1)
    have ho : IsOpen {g : GL (Fin 1) k | (LinearMap.id : Module.Dual ℂ ℂ) ∘ₗ detRep (Fin 1) χ g = LinearMap.id} := by
      convert (isSmooth_ofChar_iff _).2 (hχ.detChar (n := Fin 1)) 1 using 2
      ext g
      exact ⟨fun H => LinearMap.congr_fun H 1, fun H => LinearMap.ext_ring H⟩
    obtain ⟨F, hF, -⟩ := h Measure.haar inferInstance 1 LinearMap.id ho
    have h1 := hF (Matrix.GeneralLinearGroup.scalar (Fin 1) x)
    have h2 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) x) = x := by
      ext; simp [Matrix.GeneralLinearGroup.scalar]
    rw [Subsingleton.elim (QuotientGroup.mk _ : AdGL k 1) (QuotientGroup.mk 1), hF, key, key, h2] at h1
    simpa using h1.symm
  · intro hu _ _ μ hμ v l _
    refine ⟨fun _ => ‖l v‖, fun g => ?_, memLp_const _⟩
    rw [key, map_smul, norm_smul, hu, one_mul]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem unitary_char {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (hu : ∀ x, ‖(χ x : ℂ)‖ = 1) :
    IsSmooth (detRep (Fin 1) χ) ∧ (detRep (Fin 1) χ).IsIrreducible ∧ IsTemperedCoeff (detRep (Fin 1) χ) ∧
      ∃ (h : ℕ) (δ : Fin h → IrrGL k) (hd : ∑ i, (δ i).1 = 1),
        (∀ i, 1 ≤ (δ i).1 ∧ IsSqIntCoeff (δ i).rep) ∧ Nonempty ((detRep (Fin 1) χ).Equiv (prodIrr δ hd)) := by
  have hs : IsSmooth (detRep (Fin 1) χ) := (isSmooth_ofChar_iff _).2 hχ.detChar
  have hi : (detRep (Fin 1) χ).IsIrreducible := isIrreducible_ofChar _
  let x := IrrGL.of _ hs hi
  let φ : (detRep (Fin 1) χ).Equiv x.rep := IrrGL.equivOf _ _ _
  have hd : ∑ _ : Fin 1, x.1 = x.1 := by simp
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one x hd
  have ht : IsTemperedCoeff (detRep (Fin 1) χ) := by
    intro ε _
    exact @Iff.mpr _ _ (coeffLp_detRep_one_iff (2 + ε) hχ) hu
  have h2 : IsSqIntCoeff x.rep := by
    exact @coeffLp_of_equiv k _ _ _ _ _ _ _ _ 1 2 _ _ φ (@Iff.mpr _ _ (coeffLp_detRep_one_iff 2 hχ) hu)
  exact ⟨hs, hi, ht, 1, fun _ => x, hd,
    fun _ => ⟨le_rfl, h2⟩, ⟨φ.trans ψ⟩⟩

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem not_tempered_char {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (hu : ¬ ∀ x, ‖(χ x : ℂ)‖ = 1) :
    IsSmooth (detRep (Fin 1) χ) ∧ (detRep (Fin 1) χ).IsIrreducible ∧ ¬ IsTemperedCoeff (detRep (Fin 1) χ) :=
  ⟨(isSmooth_ofChar_iff _).2 hχ.detChar, isIrreducible_ofChar _,
    fun h => hu ((coeffLp_detRep_one_iff _ hχ).1 (h 1 one_pos))⟩

end TemperedProduct

end GlobalTheory.Published

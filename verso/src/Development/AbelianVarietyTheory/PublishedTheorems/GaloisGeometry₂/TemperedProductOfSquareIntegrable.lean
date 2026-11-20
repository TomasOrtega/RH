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
Introduce `_ _ μ hμ w l hl`. Establish `hφ : ∀ g v, φ.toLinearEquiv (π g v) = σ g (φ.toLinearEquiv v)` using `fun g v => φ.toIntertwiningMap.isIntertwining _ _ g v`. Establish `hs : {g : GL (Fin N) k | (l ∘ₗ φ.toLinearEquiv.toLinearMap) ∘ₗ π g = l ∘ₗ φ.toLinearEquiv.toLinearMap} = {g : GL (Fin N) k | l ∘ₗ σ g = l}`. Use extensionality with `g`. Use `⟨fun H => LinearMap.ext fun x => ?_, fun H => LinearMap.ext fun x => ?_⟩` and prove the remaining obligations.

Establish `h1 : l (φ.toLinearEquiv (π g (φ.toLinearEquiv.symm x))) = l (φ.toLinearEquiv (φ.toLinearEquiv.symm x))` using `LinearMap.congr_fun H (φ.toLinearEquiv.symm x)`. Rewrite `h1` using `[hφ, LinearEquiv.apply_symm_apply]`. Then use the resulting hypothesis. Use `show l (φ.toLinearEquiv (π g x)) = l (φ.toLinearEquiv x)`. Rewrite using `[hφ]`. Conclude with `LinearMap.congr_fun H _`.

Take `⟨F, hF, hF'⟩` from `h μ hμ (φ.toLinearEquiv.symm w) (l ∘ₗ φ.toLinearEquiv.toLinearMap) (hs ▸ hl)`. Use `⟨F, fun g => ?_, hF'⟩` and prove the remaining obligations. Rewrite using `[hF, LinearMap.comp_apply, LinearEquiv.coe_coe, hφ, LinearEquiv.apply_symm_apply]`.
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
Use `⟨fun a b => ?_⟩` and prove the remaining obligations. Proceed by induction on `a using QuotientGroup.induction_on`. Proceed by induction on `b using QuotientGroup.induction_on`. Use `QuotientGroup.eq.2 (Subgroup.mem_center_iff.2 fun g => ?_)` and prove the remaining obligations. Generalize the expression as in `(_⁻¹ * _ : GL (Fin 1) k) = c`.

Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Subsingleton.elim i 0, Subsingleton.elim j 0, mul_comm]`.
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
Use `haveI : Subsingleton (AdGL k 1) := subsingleton_adGL_one`. Establish `key : ∀ g v, detRep (Fin 1) χ g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v` using `fun _ _ => rfl`. Prove the components needed by the constructor for the conclusion. Introduce `h x borelize (AdGL k 1)`. Establish `ho : IsOpen {g : GL (Fin 1) k | (LinearMap.id : Module.Dual ℂ ℂ) ∘ₗ detRep (Fin 1) χ g = LinearMap.id}`.

Use `(isSmooth_ofChar_iff _).2 (hχ.detChar (n := Fin 1)) 1 using 2` and compare the differences between its conclusion and the goal. Use extensionality with `g`. Conclude with `⟨fun H => LinearMap.congr_fun H 1, fun H => LinearMap.ext_ring H⟩`. Take `⟨F, hF, -⟩` from `h Measure.haar inferInstance 1 LinearMap.id ho`. Establish `h1` using `hF (Matrix.GeneralLinearGroup.scalar (Fin 1) x)`.

Establish `h2 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) x) = x` using `by ext; simp [Matrix.GeneralLinearGroup.scalar]`. Rewrite `h1` using `[Subsingleton.elim (QuotientGroup.mk _ : AdGL k 1) (QuotientGroup.mk 1), hF, key, key, h2]`. Simplify using `using h1.symm`. Introduce `hu _ _ μ hμ v l _`. Use `⟨fun _ => ‖l v‖, fun g => ?_, memLp_const _⟩` and prove the remaining obligations.

Rewrite using `[key, map_smul, norm_smul, hu, one_mul]`.
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
Establish `hs : IsSmooth (detRep (Fin 1) χ)` using `(isSmooth_ofChar_iff _).2 hχ.detChar`. Establish `hi : (detRep (Fin 1) χ).IsIrreducible` using `isIrreducible_ofChar _`. Set `x` to `IrrGL.of _ hs hi`. Set `φ : (detRep (Fin 1) χ).Equiv x.rep` to `IrrGL.equivOf _ _ _`. Establish `hd : ∑ _ : Fin 1, x.1 = x.1` using `by simp`.

Take `⟨ψ⟩` from `nonempty_equiv_prodIrr_one x hd`. Establish `ht : IsTemperedCoeff (detRep (Fin 1) χ)`. Introduce `ε _`. Conclude with `@Iff.mpr _ _ (coeffLp_detRep_one_iff (2 + ε) hχ) hu`. Establish `h2 : IsSqIntCoeff x.rep`.

Conclude with `@coeffLp_of_equiv k _ _ _ _ _ _ _ _ 1 2 _ _ φ (@Iff.mpr _ _ (coeffLp_detRep_one_iff 2 hχ) hu)`. Conclude with `⟨hs, hi, ht, 1, fun _ => x, hd, fun _ => ⟨le_rfl, h2⟩, ⟨φ.trans ψ⟩⟩`.
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
Assemble the required witnesses or components as `⟨(isSmooth_ofChar_iff _).2 hχ.detChar, isIrreducible_ofChar _, fun h => hu ((coeffLp_detRep_one_iff _ hχ).1 (h 1 one_pos))⟩`.
-/
theorem not_tempered_char {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (hu : ¬ ∀ x, ‖(χ x : ℂ)‖ = 1) :
    IsSmooth (detRep (Fin 1) χ) ∧ (detRep (Fin 1) χ).IsIrreducible ∧ ¬ IsTemperedCoeff (detRep (Fin 1) χ) :=
  ⟨(isSmooth_ofChar_iff _).2 hχ.detChar, isIrreducible_ofChar _,
    fun h => hu ((coeffLp_detRep_one_iff _ hχ).1 (h 1 one_pos))⟩

end TemperedProduct

end GlobalTheory.Published

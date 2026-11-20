import Mathlib
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.GoodChar

open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.SchrLaw

/- English proof (translation)
Establish `hone : ∀ z : R, ((u⁻¹ : Rˣ) : R) * z ∈ O → ψ z = 1`. Introduce `z hz`. Establish `hu : ∀ y ∈ O, ψ ((u : R) * y) = 1` using `(h.ann (u : R)).2 (by rw [Units.inv_mul]; exact O.one_mem)`. Use `hu _ hz` as an intermediate fact. Rewrite `this` using `[Units.mul_inv_cancel_left]`. Then use the resulting hypothesis.

Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `x`. Use `⟨{y | ((u⁻¹ : Rˣ) : R) * (y - x) ∈ O}, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `h.isOpen.preimage (continuous_const.mul (continuous_id.sub continuous_const))`. Simplify using `only [Set.mem_ofPred_eq, sub_self, mul_zero]`.

Conclude with `O.zero_mem`. Introduce `y hy`. Establish `hy' : y = x + (y - x)` using `by abel`. Rewrite using `[hy', AddChar.map_add_eq_mul, hone _ hy, mul_one]`.
-/
theorem goodChar_isLocallyConstant {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {ψ : AddChar R ℂ} {O : Subring R} {u : Rˣ} (h : GoodChar ψ O u) : IsLocallyConstant (ψ : R → ℂ) := by
  have hone : ∀ z : R, ((u⁻¹ : Rˣ) : R) * z ∈ O → ψ z = 1 := by
    intro z hz
    have hu : ∀ y ∈ O, ψ ((u : R) * y) = 1 :=
      (h.ann (u : R)).2 (by rw [Units.inv_mul]; exact O.one_mem)
    have := hu _ hz
    rwa [Units.mul_inv_cancel_left] at this
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨{y | ((u⁻¹ : Rˣ) : R) * (y - x) ∈ O}, ?_, ?_, ?_⟩
  · exact h.isOpen.preimage (continuous_const.mul (continuous_id.sub continuous_const))
  · simp only [Set.mem_ofPred_eq, sub_self, mul_zero]
    exact O.zero_mem
  · intro y hy
    have hy' : y = x + (y - x) := by abel
    rw [hy', AddChar.map_add_eq_mul, hone _ hy, mul_one]

/- English proof (translation)
Introduce `R _ _ _ _ _ _ ψ O u W _ _ B κ _ d μ w w' φ φ' hψ hμ`. Establish `h2 : ⅟(2 : R) * 2 = 1` using `invOf_mul_self _`. Establish `hloc : IsLocallyConstant (ψ : R → ℂ)` using `goodChar_isLocallyConstant hψ`. Establish `hdot : ∀ b : κ → R, Continuous fun x : κ → R => x ⬝ᵥ b` using `fun b => continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `x`. Simplify using `only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, map_add, Prod.fst_add, Prod.snd_add, d.form]`. Rewrite using `[← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x]`. Use `congr 2`. Simplify using `only [add_dotProduct, dotProduct_add]`.

Take the linear combination `(-((d.e w).1 ⬝ᵥ (d.e w').2)) * h2`. Use function extensionality and compare the values at `x`. Simplify using `[Darboux.rho, schr]`. Introduce `hφ`. Express the relevant statement in the definitionally equal form `IsLocallyConstant _ ∧ HasCompactSupport _ at hφ`.

Express the relevant statement in the definitionally equal form `IsLocallyConstant _ ∧ HasCompactSupport _`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `(hloc.comp_continuous ((hdot _).add continuous_const)).mul (hφ.1.comp_continuous (continuous_id.add continuous_const))`. Conclude with `(hφ.2.comp_homeomorph (Homeomorph.addRight (d.e w).1)).mul_left`. Set `_ : MeasurableSpace (κ → R)` to `borel _`.

Establish `: BorelSpace (κ → R)` using `⟨rfl⟩`. Establish `: μ.IsAddHaarMeasure` using `hμ`. Establish `hpt : ∀ x, (starRingEnd ℂ) (d.rho ψ w φ x) * d.rho ψ w φ' x = (starRingEnd ℂ) (φ ((d.e w).1 + x)) * φ' ((d.e w).1 + x)`. Introduce `x`. Simplify using `only [Darboux.rho, schr, map_mul]`.

Establish `hn : (starRingEnd ℂ) (ψ (x ⬝ᵥ (d.e w).2 + ⅟(2 : R) * ((d.e w).1 ⬝ᵥ (d.e w).2))) * ψ (x ⬝ᵥ (d.e w).2 + ⅟(2 : R) * ((d.e w).1 ⬝ᵥ (d.e w).2)) = 1`. Rewrite using `[Complex.conj_mul', hψ.norm_one]`. Simplify using the standard rewrite rules. Rewrite using `[add_comm (d.e w).1 x]`. Take the linear combination `((starRingEnd ℂ) (φ (x + (d.e w).1)) * φ' (x + (d.e w).1)) * hn`.

Unfold `pair`. Repeatedly rewrite using `[hpt]`. Conclude with `integral_add_left_eq_self (fun x => (starRingEnd ℂ) (φ x) * φ' x) (d.e w).1`.
-/
theorem schr_law : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (μ : @Measure (κ → R) (borel _)) (w w' : W) (φ φ' : (κ → R) → ℂ), GoodChar ψ O u → @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → d.rho ψ w (d.rho ψ w' φ) = ψ (⅟(2 : R) * B w w') • d.rho ψ (w + w') φ ∧ d.rho ψ 0 φ = φ ∧ (φ ∈ SB (κ → R) → d.rho ψ w φ ∈ SB (κ → R)) ∧ pair μ (d.rho ψ w φ) (d.rho ψ w φ') = pair μ φ φ' := by
  intro R _ _ _ _ _ _ ψ O u W _ _ B κ _ d μ w w' φ φ' hψ hμ
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self _
  have hloc : IsLocallyConstant (ψ : R → ℂ) := goodChar_isLocallyConstant hψ
  have hdot : ∀ b : κ → R, Continuous fun x : κ → R => x ⬝ᵥ b := fun b =>
    continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext x
    simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, map_add, Prod.fst_add, Prod.snd_add, d.form]
    rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x]
    congr 2
    simp only [add_dotProduct, dotProduct_add]
    linear_combination (-((d.e w).1 ⬝ᵥ (d.e w').2)) * h2
  · funext x
    simp [Darboux.rho, schr]
  · intro hφ
    change IsLocallyConstant _ ∧ HasCompactSupport _ at hφ
    change IsLocallyConstant _ ∧ HasCompactSupport _
    refine ⟨?_, ?_⟩
    · exact (hloc.comp_continuous ((hdot _).add continuous_const)).mul
        (hφ.1.comp_continuous (continuous_id.add continuous_const))
    · exact (hφ.2.comp_homeomorph (Homeomorph.addRight (d.e w).1)).mul_left
  · let _ : MeasurableSpace (κ → R) := borel _
    have : BorelSpace (κ → R) := ⟨rfl⟩
    have : μ.IsAddHaarMeasure := hμ
    have hpt : ∀ x, (starRingEnd ℂ) (d.rho ψ w φ x) * d.rho ψ w φ' x =
        (starRingEnd ℂ) (φ ((d.e w).1 + x)) * φ' ((d.e w).1 + x) := by
      intro x
      simp only [Darboux.rho, schr, map_mul]
      have hn : (starRingEnd ℂ) (ψ (x ⬝ᵥ (d.e w).2 + ⅟(2 : R) * ((d.e w).1 ⬝ᵥ (d.e w).2))) *
          ψ (x ⬝ᵥ (d.e w).2 + ⅟(2 : R) * ((d.e w).1 ⬝ᵥ (d.e w).2)) = 1 := by
        rw [Complex.conj_mul', hψ.norm_one]
        simp
      rw [add_comm (d.e w).1 x]
      linear_combination ((starRingEnd ℂ) (φ (x + (d.e w).1)) * φ' (x + (d.e w).1)) * hn
    unfold pair
    simp_rw [hpt]
    exact integral_add_left_eq_self (fun x => (starRingEnd ℂ) (φ x) * φ' x) (d.e w).1

end GlobalTheory.CompanionTheory.SchrLaw

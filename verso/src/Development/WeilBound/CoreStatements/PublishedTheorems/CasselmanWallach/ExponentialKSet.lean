import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.LowTypeDetermined

namespace PositivityTheory.CW

namespace ExistsFunctional

/- English proof (translation)
Establish `h0 : x₀ ≠ 0`. Introduce and unpack `rfl`. Conclude with `hx (map_zero q)`. Set `e` to `LinearEquiv.toSpanNonzeroSingleton ℂ E x₀ h0`. Set `f : Module.Dual ℂ (Submodule.span ℂ {x₀})` to `(q x₀ : ℂ) • (e.symm : _ →ₗ[ℂ] ℂ)`.

Establish `hfe : ∀ t : ℂ, f (e t) = t * q x₀`. Introduce `t`. Simplify using `[f, mul_comm]`. Take `⟨g, hg, hgp⟩` from `Module.Dual.exists_extension_of_le_seminorm (Submodule.span ℂ {x₀}) f (p := q) (by`. Introduce `y`.

Take `⟨t, rfl⟩` from `e.surjective y`. Rewrite using `[hfe, norm_mul, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg q x₀)]`. Rewrite using `[LinearEquiv.toSpanNonzeroSingleton_apply]`. Simplify using `[map_smul_eq_mul])`. Use `⟨g, ?_, hgp⟩` and prove the remaining obligations.

Establish `h1` using `hg (e 1)`. Rewrite `h1` using `[hfe, one_mul]`. Establish `: ((e 1 : Submodule.span ℂ {x₀}) : E) = x₀`. Rewrite using `[LinearEquiv.toSpanNonzeroSingleton_one]`. Rewrite `h1` using `[this]`.

Rewrite using `[h1]`. Conclude with `hx` after adjusting the coercions.
-/
theorem exists_functional {E : Type} [AddCommGroup E] [Module ℂ E] (q : Seminorm ℂ E) {x₀ : E} (hx : q x₀ ≠ 0) :
    ∃ φ : Module.Dual ℂ E, φ x₀ ≠ 0 ∧ ∀ x, ‖φ x‖ ≤ q x := by
  have h0 : x₀ ≠ 0 := by
    rintro rfl
    exact hx (map_zero q)
  let e := LinearEquiv.toSpanNonzeroSingleton ℂ E x₀ h0
  let f : Module.Dual ℂ (Submodule.span ℂ {x₀}) := (q x₀ : ℂ) • (e.symm : _ →ₗ[ℂ] ℂ)
  have hfe : ∀ t : ℂ, f (e t) = t * q x₀ := by
    intro t
    simp [f, mul_comm]
  obtain ⟨g, hg, hgp⟩ := Module.Dual.exists_extension_of_le_seminorm (Submodule.span ℂ {x₀}) f
    (p := q) (by
      intro y
      obtain ⟨t, rfl⟩ := e.surjective y
      rw [hfe, norm_mul, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg q x₀)]
      rw [LinearEquiv.toSpanNonzeroSingleton_apply]
      simp [map_smul_eq_mul])
  refine ⟨g, ?_, hgp⟩
  have h1 := hg (e 1)
  rw [hfe, one_mul] at h1
  have : ((e 1 : Submodule.span ℂ {x₀}) : E) = x₀ := by
    rw [LinearEquiv.toSpanNonzeroSingleton_one]
  rw [this] at h1
  rw [h1]
  exact_mod_cast hx

end ExistsFunctional

/- English proof (translation)
Unfold `faceMap_comp_succAbove_castSucc AllTgt`. Introduce `n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hrep T hT i w₀ hw₀ hp u hu hu0`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Take `⟨φ, hφ0, hφ⟩` from `ExistsFunctional.exists_functional (p i) hp`.

Set `ℓ : H →ₗ[ℂ] ℂ` to `φ ∘ₗ T`. Establish `hlie : ((GlobalTheory.LowTypeDetermined.lie (Jm ε) : Set (Mx n))) = lieSet ε` using `rfl`. Establish `hsm : ∀ w, Sm ε σ w → w ∈ GlobalTheory.LowTypeDetermined.smooth (Jm ε) (fun g => σ (1 * g * (1 : Mx n)⁻¹))`. Introduce `w hw`. Express the relevant statement in the definitionally equal form `SmoothVec ((GlobalTheory.LowTypeDetermined.lie (Jm ε) : Set (Mx n))) (fun g => σ (1 * g * (1 : Mx n)⁻¹)) w`.

Simplify using `only [inv_one, mul_one, one_mul]`. Rewrite using `[hlie]`. Conclude with `hw`. Establish `key` using `GlobalTheory.LowTypeDetermined.eq_zero_of_translates (G := Jm ε) (P := 1) hU hI isUnit_one (by simp) (ℓ := ℓ) ?_ (hsm u hu) hu0 ?_ (hsm w₀ hw₀)`. Conclude with `hφ0 key`.

Take `⟨S, C, hS, hb⟩` from `hT.2 i`. Use `⟨S, C, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hlie]`. Conclude with `hS`. Simplify using `only [inv_one, mul_one, one_mul]`.

Rewrite using `[hlie]`. Introduce `w hw`. Conclude with `(hφ (T w)).trans (hb w hw)`. Introduce `g hg show φ (T (σ g u)) = 0`. Rewrite using `[hT.1 g hg u hu]`.

Conclude with `norm_le_zero_iff.mp ((hφ _).trans (hall g hg).le)`.
-/
theorem e1b : faceMap_comp_succAbove_castSucc := by
  unfold faceMap_comp_succAbove_castSucc AllTgt
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hrep T hT i w₀ hw₀ hp u hu hu0
  by_contra hall
  push_neg at hall
  obtain ⟨φ, hφ0, hφ⟩ := ExistsFunctional.exists_functional (p i) hp
  let ℓ : H →ₗ[ℂ] ℂ := φ ∘ₗ T
  have hlie : ((GlobalTheory.LowTypeDetermined.lie (Jm ε) : Set (Mx n))) = lieSet ε := rfl
  have hsm : ∀ w, Sm ε σ w →
      w ∈ GlobalTheory.LowTypeDetermined.smooth (Jm ε) (fun g => σ (1 * g * (1 : Mx n)⁻¹)) := by
    intro w hw
    change SmoothVec ((GlobalTheory.LowTypeDetermined.lie (Jm ε) : Set (Mx n)))
      (fun g => σ (1 * g * (1 : Mx n)⁻¹)) w
    simp only [inv_one, mul_one, one_mul]
    rw [hlie]
    exact hw
  have key := GlobalTheory.LowTypeDetermined.eq_zero_of_translates (G := Jm ε) (P := 1) hU hI isUnit_one
    (by simp) (ℓ := ℓ) ?_ (hsm u hu) hu0 ?_ (hsm w₀ hw₀)
  · exact hφ0 key
  · obtain ⟨S, C, hS, hb⟩ := hT.2 i
    refine ⟨S, C, ?_, ?_⟩
    · rw [hlie]
      exact hS
    · simp only [inv_one, mul_one, one_mul]
      rw [hlie]
      intro w hw
      exact (hφ (T w)).trans (hb w hw)
  · intro g hg
    show φ (T (σ g u)) = 0
    rw [hT.1 g hg u hu]
    exact norm_le_zero_iff.mp ((hφ _).trans (hall g hg).le)

end PositivityTheory.CW

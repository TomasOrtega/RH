import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Introduce `A Ω K _ _ _ φ ρ hφ`. Use `letI : Algebra A Ω := φ.toAlgebra`. Use `haveI : Module.Finite A Ω := hφ`. Take `⟨s, hs⟩` from `Module.Finite.fg_top (R := A) (M := Ω)`. Use `haveI : Algebra.IsIntegral A Ω := Algebra.IsIntegral.of_finite A Ω`.

Establish `hint : ∀ g : Ω, ∃ p : Polynomial A, p.Monic ∧ p.eval₂ φ g = 0` using `fun g => by`. Take `⟨q, hq, he⟩` from `Algebra.IsIntegral.isIntegral (R := A) g`. Conclude with `⟨q, hq, he⟩`. Use `choose p hpm hpe using hint`. Set `F : (Ω →+* K) → (s → K)` to `fun τ g => τ g`.

Apply `Set.Finite.of_finite_image (f := F)` to reduce the goal to its premises. Use `Set.Finite.subset (Set.Finite.pi (t := fun g : s => (((p g).map ρ).roots.toFinset : Set K)) (fun _ => Finset.finite_toSet _)) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨τ, hτ, rfl⟩ g _`. Establish `hτ' : τ.comp φ = ρ` using `hτ`. Simplify using `only [Finset.mem_coe, Multiset.mem_toFinset]`.

Rewrite using `[Polynomial.mem_roots ((hpm g).map ρ).ne_zero, Polynomial.IsRoot, Polynomial.eval_map, ← hτ', ← Polynomial.hom_eval₂, hpe, map_zero]`. Introduce `τ₁ h₁ τ₂ h₂ he`. Establish `h₁' : τ₁.comp φ = ρ` using `h₁`. Establish `h₂' : τ₂.comp φ = ρ` using `h₂`. Use extensionality with `x`.

Establish `hx : x ∈ Submodule.span A (s : Set Ω)` using `hs ▸ Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact congrFun he ⟨y, hy⟩`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => simp [hy, hz]`.

Consider the case `smul a y _ hy`. Rewrite using `[Algebra.smul_def, map_mul, map_mul, hy]`. Use `congr 1`. Conclude with `(RingHom.congr_fun h₁' a).trans (RingHom.congr_fun h₂' a).symm`.
-/
theorem finite_setOf_ringHom_comp_eq_of_finite : ∀ (A Ω K : Type) [CommRing A] [CommRing Ω] [Field K]
    (φ : A →+* Ω) (ρ : A →+* K), φ.Finite → Set.Finite {τ : Ω →+* K | τ.comp φ = ρ} := by
  intro A Ω K _ _ _ φ ρ hφ
  classical
  letI : Algebra A Ω := φ.toAlgebra
  haveI : Module.Finite A Ω := hφ
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := Ω)
  haveI : Algebra.IsIntegral A Ω := Algebra.IsIntegral.of_finite A Ω
  have hint : ∀ g : Ω, ∃ p : Polynomial A, p.Monic ∧ p.eval₂ φ g = 0 := fun g => by
    obtain ⟨q, hq, he⟩ := Algebra.IsIntegral.isIntegral (R := A) g
    exact ⟨q, hq, he⟩
  choose p hpm hpe using hint
  let F : (Ω →+* K) → (s → K) := fun τ g => τ g
  apply Set.Finite.of_finite_image (f := F)
  · refine Set.Finite.subset (Set.Finite.pi (t := fun g : s => (((p g).map ρ).roots.toFinset : Set K))
      (fun _ => Finset.finite_toSet _)) ?_
    rintro _ ⟨τ, hτ, rfl⟩ g _
    have hτ' : τ.comp φ = ρ := hτ
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots ((hpm g).map ρ).ne_zero, Polynomial.IsRoot, Polynomial.eval_map,
      ← hτ', ← Polynomial.hom_eval₂, hpe, map_zero]
  · intro τ₁ h₁ τ₂ h₂ he
    have h₁' : τ₁.comp φ = ρ := h₁
    have h₂' : τ₂.comp φ = ρ := h₂
    ext x
    have hx : x ∈ Submodule.span A (s : Set Ω) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact congrFun he ⟨y, hy⟩
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul a y _ hy =>
      rw [Algebra.smul_def, map_mul, map_mul, hy]
      congr 1
      exact (RingHom.congr_fun h₁' a).trans (RingHom.congr_fun h₂' a).symm

end GlobalTheory

import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.TopGroup

/- English proof (translation)
Introduce `G _ _ _ J hJ g`. Establish `hpre : ((J.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) = (fun x : G => g⁻¹ * x * g) ⁻¹' (J : Set G)`. Use extensionality with `x`. Simplify using `only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, rfl⟩`. Simplify `hy` using `[mul_assoc]`. Introduce `hx`. Conclude with `⟨g⁻¹ * x * g, hx, by simp [mul_assoc]⟩`. Establish `hcont : Continuous (fun x : G => g⁻¹ * x * g)` using `by fun_prop`.

Establish `h2 : IsOpen ((J.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)`. Rewrite using `[hpre]`. Conclude with `hJ.preimage hcont`. Rewrite using `[Subgroup.coe_inf]`. Conclude with `hJ.inter h2`.
-/
theorem inter_conj_isOpen :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G),
      IsOpen (J : Set G) → ∀ g : G,
        IsOpen ((J ⊓ J.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  intro G _ _ _ J hJ g
  have hpre : ((J.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)
      = (fun x : G => g⁻¹ * x * g) ⁻¹' (J : Set G) := by
    ext x
    simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨g⁻¹ * x * g, hx, by simp [mul_assoc]⟩
  have hcont : Continuous (fun x : G => g⁻¹ * x * g) := by fun_prop
  have h2 : IsOpen ((J.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    rw [hpre]; exact hJ.preimage hcont
  rw [Subgroup.coe_inf]
  exact hJ.inter h2

end GlobalTheory.CompanionTheory.TopGroup

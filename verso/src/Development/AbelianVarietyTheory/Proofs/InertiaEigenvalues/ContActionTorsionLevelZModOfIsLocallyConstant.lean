import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

/- English proof (translation)
Use `letI := GlobalTheory.ShapeNeg.levZ (M := M) p r h`. Unfold `ReciprocityTheory.Gal.ContAction`. Apply `IsLocallyConstant.continuous` to reduce the goal to its premises. Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce and unpack `⟨g₀, x₀⟩`.

Establish `hx` using `hloc x₀.val (Lev.smul_val x₀)`. Use `⟨{g | ρ g x₀.val = ρ g₀ x₀.val} ×ˢ {x₀}, (hx.isOpen_fiber _).prod (isOpen_discrete _), ⟨rfl, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨g, x⟩ ⟨hg, hx'⟩`. Simplify using `only [Set.mem_singleton_iff] at hx'`. Substitute `hx'` using the available equality.

Apply `Lev.ext` to reduce the goal to its premises. Use `show (levRep ρ c g x).val = (levRep ρ c g₀ x).val`. Rewrite using `[levRep_val, levRep_val]`. Conclude with `hg`.
-/
theorem contAction_levRepZ_of_isLocallyConstant
    {G : Type} [Group G] [TopologicalSpace G] {O : Type} [CommRing O] {M : Type} [AddCommGroup M]
    [Module O M] (ρ : Representation O G M) (p r : ℕ) [NeZero (p ^ r)] (c : O)
    (h : ((p : O) ^ r) ∈ Ideal.span {c})
    (hloc : ∀ m : M, c • m = 0 → IsLocallyConstant (fun g => ρ g m)) :
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p r h
    ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p r h ρ) := by
  letI := GlobalTheory.ShapeNeg.levZ (M := M) p r h
  unfold ReciprocityTheory.Gal.ContAction
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_exists_open]
  rintro ⟨g₀, x₀⟩
  have hx := hloc x₀.val (Lev.smul_val x₀)
  refine ⟨{g | ρ g x₀.val = ρ g₀ x₀.val} ×ˢ {x₀},
    (hx.isOpen_fiber _).prod (isOpen_discrete _), ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨g, x⟩ ⟨hg, hx'⟩
  simp only [Set.mem_singleton_iff] at hx'
  subst hx'
  apply Lev.ext
  show (levRep ρ c g x).val = (levRep ρ c g₀ x).val
  rw [levRep_val, levRep_val]
  exact hg

end GlobalTheory.ShapeNeg

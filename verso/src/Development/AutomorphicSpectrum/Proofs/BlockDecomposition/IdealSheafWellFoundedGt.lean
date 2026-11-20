import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

/- English proof (translation)
Introduce `X _`. Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => ((U.1 : X.Opens) : Set X)) (fun U => U.1.isOpen) (by`. Introduce `x _`. Establish `hx : x ∈ (⨆ U : X.affineOpens, (U.1 : X.Opens))`. Rewrite using `[iSup_affineOpens_eq_top X]`.

Discharge the goal by the elementary cases of `trivial`. Take `⟨U, hU⟩` from `TopologicalSpace.Opens.mem_iSup.mp hx`. Conclude with `Set.mem_iUnion.mpr ⟨U, hU⟩)`. Establish `hcov : ⨆ i : t, ((i.1 : X.affineOpens).1 : X.Opens) = ⊤`. Rewrite using `[eq_top_iff]`.

Introduce `x _`. Establish `hx` using `ht (Set.mem_univ x)`. Simplify using `only [Set.mem_iUnion] at hx`. Take `⟨U, hUt, hxU⟩` from `hx`. Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hUt⟩, hxU⟩`.

Establish `hnoeth : ∀ i : t, WellFoundedGT (Ideal Γ(X, (i.1 : X.affineOpens).1))` using `fun i => by haveI : IsNoetherianRing Γ(X, (i.1 : X.affineOpens).1) := IsLocallyNoetherian.component_noetherian i.1 infer_instance`. Set `φ : X.IdealSheafData → (∀ i : t, Ideal Γ(X, (i.1 : X.affineOpens).1))` to `fun I i => I.ideal i.1`. Establish `hφ : StrictMono φ`. Use `Monotone.strictMono_of_injective (fun I J h i => h i.1) ?_` and prove the remaining obligations. Introduce `I J h`.

Conclude with `Scheme.IdealSheafData.ext_of_iSup_eq_top (fun i : t => i.1) hcov (fun i => congrFun h i)`. Establish `h1 : WellFoundedLT (∀ i : t, (Ideal Γ(X, (i.1 : X.affineOpens).1))ᵒᵈ)` using `Pi.wellFoundedLT`. Establish `h2 : WellFoundedGT (∀ i : t, Ideal Γ(X, (i.1 : X.affineOpens).1))` using `⟨h1.wf⟩`. Conclude with `hφ.wellFoundedGT`.
-/
theorem idealSheafData_wellFoundedGT :
    ∀ {X : Scheme.{0}} [IsNoetherian X], WellFoundedGT X.IdealSheafData := by
  intro X _
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens => ((U.1 : X.Opens) : Set X)) (fun U => U.1.isOpen) (by
      intro x _
      have hx : x ∈ (⨆ U : X.affineOpens, (U.1 : X.Opens)) := by
        rw [iSup_affineOpens_eq_top X]; trivial
      obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨U, hU⟩)
  have hcov : ⨆ i : t, ((i.1 : X.affineOpens).1 : X.Opens) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at hx
    obtain ⟨U, hUt, hxU⟩ := hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hUt⟩, hxU⟩
  have hnoeth : ∀ i : t, WellFoundedGT (Ideal Γ(X, (i.1 : X.affineOpens).1)) := fun i => by
    haveI : IsNoetherianRing Γ(X, (i.1 : X.affineOpens).1) :=
      IsLocallyNoetherian.component_noetherian i.1
    infer_instance
  let φ : X.IdealSheafData → (∀ i : t, Ideal Γ(X, (i.1 : X.affineOpens).1)) :=
    fun I i => I.ideal i.1
  have hφ : StrictMono φ := by
    refine Monotone.strictMono_of_injective (fun I J h i => h i.1) ?_
    intro I J h
    exact Scheme.IdealSheafData.ext_of_iSup_eq_top (fun i : t => i.1) hcov
      (fun i => congrFun h i)
  have h1 : WellFoundedLT (∀ i : t, (Ideal Γ(X, (i.1 : X.affineOpens).1))ᵒᵈ) := Pi.wellFoundedLT
  have h2 : WellFoundedGT (∀ i : t, Ideal Γ(X, (i.1 : X.affineOpens).1)) := ⟨h1.wf⟩
  exact hφ.wellFoundedGT

end GlobalTheory.CompanionTheory.GE

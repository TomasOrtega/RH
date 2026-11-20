import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegreeDual
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix NumberField

noncomputable section

namespace DualLatticeBasisExistsAlt

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem eq_zero_of_dotProduct_gens (F : HermLattice K i) (s : Finset (Fin i → K))
    (hs : Submodule.span (𝓞 K) (s : Set (Fin i → K)) = F.lattice) (φ : Fin i → K)
    (h : ∀ g ∈ s, φ ⬝ᵥ g = 0) : φ = 0 := by
  let L : (Fin i → K) →ₗ[K] K :=
    { toFun := fun x => φ ⬝ᵥ x
      map_add' := dotProduct_add φ
      map_smul' := fun c x => by simp [dotProduct_smul] }
  have h1 : F.lattice ≤ (LinearMap.ker L).restrictScalars (𝓞 K) := by
    rw [← hs, Submodule.span_le]
    intro g hg
    exact h g hg
  have h2 : Submodule.span K (F.lattice : Set (Fin i → K)) ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    intro x hx
    exact h1 hx
  rw [F.span_eq, top_le_iff] at h2
  funext j
  have hj : Pi.single j (1 : K) ∈ LinearMap.ker L := by rw [h2]; trivial
  have : φ ⬝ᵥ Pi.single j (1 : K) = 0 := hj
  simpa [dotProduct_single] using this

/- English proof (translation)
Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Introduce a local definition for the expression. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Supply the required witnesses or components. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem dualLattice_fg (F : HermLattice K i) : (dualLattice F).FG := by
  classical
  obtain ⟨s, hs⟩ := F.fg

  let G : (Fin i → K) →ₗ[ℤ] (s → K) :=
    { toFun := fun φ g => φ ⬝ᵥ (g : Fin i → K)
      map_add' := fun φ ψ => by funext g; simp [add_dotProduct]
      map_smul' := fun c φ => by
        funext g
        show (c • φ) ⬝ᵥ (g : Fin i → K) = c • (φ ⬝ᵥ (g : Fin i → K))
        exact smul_dotProduct c φ _ }
  have hG : Function.Injective G := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ hφ
    refine eq_zero_of_dotProduct_gens F s hs φ (fun g hg => ?_)
    exact congrFun hφ ⟨g, hg⟩

  let ι : (s → 𝓞 K) →ₗ[ℤ] (s → K) :=
    LinearMap.pi (fun g => ((Algebra.linearMap (𝓞 K) K).restrictScalars ℤ).comp (LinearMap.proj g))
  have hle : (dualLattice F).map G ≤ LinearMap.range ι := by
    rintro _ ⟨φ, hφ, rfl⟩
    have hv : ∀ g : s, ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = φ ⬝ᵥ (g : Fin i → K) := fun g =>
      hφ g (hs ▸ Submodule.subset_span g.2)
    choose a ha using hv
    exact ⟨a, funext fun g => ha g⟩
  have hfg : ((dualLattice F).map G).FG := by
    have e : (dualLattice F).map G = (((dualLattice F).map G).comap ι).map ι := by
      rw [Submodule.map_comap_eq, inf_eq_right.mpr hle]
    rw [e]
    exact (IsNoetherian.noetherian _).map ι
  exact Submodule.fg_of_fg_map_injective G hG hfg

end DualLatticeBasisExistsAlt

open DualLatticeBasisExistsAlt in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem DualLatticeBasisExists.proof : DualLatticeBasisExists.Statement := by
  intro K _ _ i F
  classical
  have : Module.Finite ℤ (dualLattice F) := Module.Finite.iff_fg.mpr (dualLattice_fg F)
  exact ⟨Module.Free.ChooseBasisIndex ℤ (dualLattice F), inferInstance, inferInstance,
    ⟨Module.Free.chooseBasis ℤ (dualLattice F)⟩⟩

end

end GroundTheory.Heights₂.Heights

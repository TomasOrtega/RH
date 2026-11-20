import Mathlib
open Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ n ι A hc`. Set `f : ι → Module.End K (Fin n → K)` to `fun i => Matrix.toLin' (A i)`. Establish `hcf : ∀ i j, Commute (f i) (f j)`. Introduce `i j`. Conclude with `(hc i j).map Matrix.toLinAlgEquiv'`.

Establish `hind` using `Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcf j i) φ)`. Use `(WellFoundedGT.finite_ne_bot_of_iSupIndep hind).subset ?_` and prove the remaining obligations. Introduce and unpack `χ ⟨c, hc0, hχ⟩`. Use `show (⨅ i, (f i).maxGenEigenspace (χ i)) ≠ ⊥`. Introduce `hbot`.

Apply `hc0` to reduce the goal to its premises. Establish `hmem : c ∈ ⨅ i, (f i).maxGenEigenspace (χ i)`. Rewrite using `[Submodule.mem_iInf]`. Introduce `i`. Apply `Module.End.eigenspace_le_maxGenEigenspace` to reduce the goal to its premises.

Rewrite using `[Module.End.mem_eigenspace_iff]`. Simplify `hχ i` using `[f]`. Rewrite `hmem` using `[hbot]`. Conclude with `(Submodule.mem_bot K).mp hmem`.
-/
theorem finite_joint_eigensystems : ∀ (K : Type) [Field K] (n : ℕ) (ι : Type) (A : ι → Matrix (Fin n) (Fin n) K), (∀ i j, Commute (A i) (A j)) → Set.Finite {χ : ι → K | ∃ c : Fin n → K, c ≠ 0 ∧ ∀ i, A i *ᵥ c = χ i • c} := by
  intro K _ n ι A hc
  let f : ι → Module.End K (Fin n → K) := fun i => Matrix.toLin' (A i)
  have hcf : ∀ i j, Commute (f i) (f j) := by
    intro i j
    exact (hc i j).map Matrix.toLinAlgEquiv'
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcf j i) φ)
  refine (WellFoundedGT.finite_ne_bot_of_iSupIndep hind).subset ?_
  rintro χ ⟨c, hc0, hχ⟩
  show (⨅ i, (f i).maxGenEigenspace (χ i)) ≠ ⊥
  intro hbot
  apply hc0
  have hmem : c ∈ ⨅ i, (f i).maxGenEigenspace (χ i) := by
    rw [Submodule.mem_iInf]
    intro i
    apply Module.End.eigenspace_le_maxGenEigenspace
    rw [Module.End.mem_eigenspace_iff]
    simpa [f] using hχ i
  rw [hbot] at hmem
  exact (Submodule.mem_bot K).mp hmem

end GlobalTheory

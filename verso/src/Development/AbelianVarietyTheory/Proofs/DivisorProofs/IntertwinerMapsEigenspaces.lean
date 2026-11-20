import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

/- English proof (translation)
Introduce `C _ O _ _ Λ _ h ρ ρ' X hX`. Use `set f := Matrix.toLin' (X.map (algebraMap O C)) with hf`. Establish `hcomm : ∀ (l : Λ) (v : Fin h → C), f (Matrix.toLin' ((ρ l).map (algebraMap O C)) v) = Matrix.toLin' ((ρ' l).map (algebraMap O C)) (f v)`. Introduce `l v`. Establish `e : X.map (algebraMap O C) * (ρ l).map (algebraMap O C) = (ρ' l).map (algebraMap O C) * X.map (algebraMap O C)`.

Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, hX l]`. Simplify using `only [hf, Matrix.toLin'_apply, Matrix.mulVec_mulVec, e]`. Establish `h1 : ∀ σ : Λ →+* O, (eig C ρ σ).map f ≤ eig C ρ' σ`. Introduce `σ y hy`. Take `⟨x, hx, rfl⟩` from `Submodule.mem_map.mp hy`.

Simplify using `only [eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hx ⊢`. Introduce `a`. Rewrite using `[← hcomm, hx a, map_smul]`. Use `⟨h1, fun htop hind σ => le_antisymm ?_ ?_⟩` and prove the remaining obligations. Introduce and unpack `y ⟨⟨z, rfl⟩, hy⟩`.

Establish `hz : z ∈ eig C ρ σ ⊔ ⨆ (j : Λ →+* O) (_ : j ≠ σ), eig C ρ j`. Rewrite using `[← iSup_split_single (fun j : Λ →+* O => eig C ρ j) σ, htop]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨x, hx, z', hz', rfl⟩` from `Submodule.mem_sup.mp hz`. Establish `hfx : f x ∈ eig C ρ' σ` using `h1 σ (Submodule.mem_map_of_mem hx)`.

Establish `hother : f z' ∈ ⨆ (j : Λ →+* O) (_ : j ≠ σ), eig C ρ' j`. Establish `hle : (⨆ (j : Λ →+* O) (_ : j ≠ σ), eig C ρ j).map f ≤ ⨆ (j : Λ →+* O) (_ : j ≠ σ), eig C ρ' j`. Rewrite using `[Submodule.map_iSup]`. Use `iSup_le fun j => ?_` and prove the remaining obligations. Rewrite using `[Submodule.map_iSup]`.

Conclude with `iSup_le fun hj => (h1 j).trans (le_iSup₂_of_le j hj le_rfl)`. Conclude with `hle (Submodule.mem_map_of_mem hz')`. Establish `hself : f z' ∈ eig C ρ' σ`. Establish `e : f z' = f (x + z') - f x` using `by simp`. Rewrite using `[e]`.

Conclude with `Submodule.sub_mem _ hy hfx`. Establish `h0 : f z' = 0`. Use `(hind σ).le_bot (Submodule.mem_inf.mpr ⟨hself, hother⟩)` as an intermediate fact. Simplify using `using this`. Use `Submodule.mem_map.mpr ⟨x, hx, ?_⟩` and prove the remaining obligations.

Simplify using `[h0]`. Conclude with `le_inf (LinearMap.map_le_range) (h1 σ)`.
-/
theorem eig_map_equivariant : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h : ℕ) (ρ ρ' : Λ → Matrix (Fin h) (Fin h) O) (X : Matrix (Fin h) (Fin h) O), (∀ l, X * ρ l = ρ' l * X) → (∀ σ : Λ →+* O, (eig C ρ σ).map (Matrix.toLin' (X.map (algebraMap O C))) ≤ eig C ρ' σ) ∧ ((⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → iSupIndep (fun σ : Λ →+* O => eig C ρ' σ) → ∀ σ : Λ →+* O, LinearMap.range (Matrix.toLin' (X.map (algebraMap O C))) ⊓ eig C ρ' σ = (eig C ρ σ).map (Matrix.toLin' (X.map (algebraMap O C)))) := by
  intro C _ O _ _ Λ _ h ρ ρ' X hX
  set f := Matrix.toLin' (X.map (algebraMap O C)) with hf
  have hcomm : ∀ (l : Λ) (v : Fin h → C), f (Matrix.toLin' ((ρ l).map (algebraMap O C)) v) =
      Matrix.toLin' ((ρ' l).map (algebraMap O C)) (f v) := by
    intro l v
    have e : X.map (algebraMap O C) * (ρ l).map (algebraMap O C) =
        (ρ' l).map (algebraMap O C) * X.map (algebraMap O C) := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, hX l]
    simp only [hf, Matrix.toLin'_apply, Matrix.mulVec_mulVec, e]
  have h1 : ∀ σ : Λ →+* O, (eig C ρ σ).map f ≤ eig C ρ' σ := by
    intro σ y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    simp only [eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hx ⊢
    intro a
    rw [← hcomm, hx a, map_smul]
  refine ⟨h1, fun htop hind σ => le_antisymm ?_ ?_⟩
  · rintro y ⟨⟨z, rfl⟩, hy⟩
    have hz : z ∈ eig C ρ σ ⊔ ⨆ (j : Λ →+* O) (_ : j ≠ σ), eig C ρ j := by
      rw [← iSup_split_single (fun j : Λ →+* O => eig C ρ j) σ, htop]
      trivial
    obtain ⟨x, hx, z', hz', rfl⟩ := Submodule.mem_sup.mp hz
    have hfx : f x ∈ eig C ρ' σ := h1 σ (Submodule.mem_map_of_mem hx)
    have hother : f z' ∈ ⨆ (j : Λ →+* O) (_ : j ≠ σ), eig C ρ' j := by
      have hle : (⨆ (j : Λ →+* O) (_ : j ≠ σ), eig C ρ j).map f ≤
          ⨆ (j : Λ →+* O) (_ : j ≠ σ), eig C ρ' j := by
        rw [Submodule.map_iSup]
        refine iSup_le fun j => ?_
        rw [Submodule.map_iSup]
        exact iSup_le fun hj => (h1 j).trans (le_iSup₂_of_le j hj le_rfl)
      exact hle (Submodule.mem_map_of_mem hz')
    have hself : f z' ∈ eig C ρ' σ := by
      have e : f z' = f (x + z') - f x := by simp
      rw [e]
      exact Submodule.sub_mem _ hy hfx
    have h0 : f z' = 0 := by
      have := (hind σ).le_bot (Submodule.mem_inf.mpr ⟨hself, hother⟩)
      simpa using this
    refine Submodule.mem_map.mpr ⟨x, hx, ?_⟩
    simp [h0]
  · exact le_inf (LinearMap.map_le_range) (h1 σ)

end GlobalTheory.DetInv

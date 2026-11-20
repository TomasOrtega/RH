import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.SubMat

open Matrix UpperTheory.V.Weyl

/- English proof (translation)
Introduce `G _ d ρ hd`. Establish `hex : ∃ m, ∃ S : Submodule ℂ (Fin d → ℂ), (∀ y, ∀ v ∈ S, ρ y *ᵥ v ∈ S) ∧ S ≠ ⊥ ∧ Module.finrank ℂ S = m`. Use `⟨_, ⊤, fun y v _ => Submodule.mem_top, ?_, rfl⟩` and prove the remaining obligations. Introduce `h`. Establish `h1 : Module.finrank ℂ (⊤ : Submodule ℂ (Fin d → ℂ)) = 0`.

Rewrite using `[h]`. Conclude with `finrank_bot ℂ (Fin d → ℂ)`. Rewrite `h1` using `[finrank_top, Module.finrank_fin_fun]`. Use linear arithmetic over natural numbers and integers. Take `⟨S, hSinv, hSne, hSrank⟩` from `Nat.find_spec hex`.

Take `⟨d', A, B, ρ', hd', hBA, -, hρ', hint⟩` from `subMat G d ρ S hSinv`. Establish `hSpos : Module.finrank ℂ S ≠ 0` using `fun h => hSne (Submodule.finrank_eq_zero.mp h)`. Use `⟨d', A, B, ρ', ?_, ?_, hBA, hρ', hint, ?_⟩` and prove the remaining obligations. Use linear arithmetic over natural numbers and integers. Establish `hle` using `Submodule.finrank_le S`.

Rewrite `hle` using `[Module.finrank_fin_fun]`. Use linear arithmetic over natural numbers and integers. Introduce `W hW`. Distinguish the cases in `hWb : W = ⊥`. Conclude with `Or.inl hWb`.

Use `right`. Establish `hinj : Function.Injective A.mulVecLin`. Introduce `v w h`. Establish `h2` using `congrArg (fun u => B *ᵥ u) h`. Simplify `h2` using `[Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hBA]`.

Establish `hrank : Module.finrank ℂ (W.map A.mulVecLin) = Module.finrank ℂ W` using `(LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj W)).symm`. Establish `hW'inv : ∀ y, ∀ v ∈ W.map A.mulVecLin, ρ y *ᵥ v ∈ W.map A.mulVecLin`. Introduce `y v hv`. Take `⟨w, hw, rfl⟩` from `Submodule.mem_map.mp hv`. Use `Submodule.mem_map.mpr ⟨ρ' y *ᵥ w, hW y w hw, ?_⟩` and prove the remaining obligations.

Simplify using `only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hint]`. Establish `hW'ne : W.map A.mulVecLin ≠ ⊥`. Introduce `h`. Apply `hWb` to reduce the goal to its premises. Rewrite using `[← Submodule.finrank_eq_zero, ← hrank, h]`.

Conclude with `finrank_bot ℂ (Fin d → ℂ)`. Establish `hmin` using `Nat.find_min' hex ⟨W.map A.mulVecLin, hW'inv, hW'ne, rfl⟩`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Establish `hle` using `Submodule.finrank_le W`. Rewrite `hle`, the goal using `[Module.finrank_fin_fun]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.V.Weyl.irrSub :
    ∀ (G : Type) [Monoid G] (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ), 0 < d →
      ∃ (d' : ℕ) (A : Matrix (Fin d) (Fin d') ℂ) (B : Matrix (Fin d') (Fin d) ℂ) (ρ' : G →* Matrix (Fin d') (Fin d') ℂ),
        0 < d' ∧ d' ≤ d ∧ B * A = 1 ∧ (∀ y, ρ' y = B * ρ y * A) ∧ (∀ y, ρ y * A = A * ρ' y) ∧
        ∀ W : Submodule ℂ (Fin d' → ℂ), (∀ y, ∀ v ∈ W, ρ' y *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro G _ d ρ hd
  classical
  have hex : ∃ m, ∃ S : Submodule ℂ (Fin d → ℂ), (∀ y, ∀ v ∈ S, ρ y *ᵥ v ∈ S) ∧ S ≠ ⊥ ∧
      Module.finrank ℂ S = m := by
    refine ⟨_, ⊤, fun y v _ => Submodule.mem_top, ?_, rfl⟩
    intro h
    have h1 : Module.finrank ℂ (⊤ : Submodule ℂ (Fin d → ℂ)) = 0 := by
      rw [h]; exact finrank_bot ℂ (Fin d → ℂ)
    rw [finrank_top, Module.finrank_fin_fun] at h1
    omega
  obtain ⟨S, hSinv, hSne, hSrank⟩ := Nat.find_spec hex
  obtain ⟨d', A, B, ρ', hd', hBA, -, hρ', hint⟩ := subMat G d ρ S hSinv
  have hSpos : Module.finrank ℂ S ≠ 0 := fun h => hSne (Submodule.finrank_eq_zero.mp h)
  refine ⟨d', A, B, ρ', ?_, ?_, hBA, hρ', hint, ?_⟩
  · omega
  · have hle := Submodule.finrank_le S
    rw [Module.finrank_fin_fun] at hle
    omega
  · intro W hW
    by_cases hWb : W = ⊥
    · exact Or.inl hWb
    right
    have hinj : Function.Injective A.mulVecLin := by
      intro v w h
      have h2 := congrArg (fun u => B *ᵥ u) h
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hBA] using h2
    have hrank : Module.finrank ℂ (W.map A.mulVecLin) = Module.finrank ℂ W :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj W)).symm
    have hW'inv : ∀ y, ∀ v ∈ W.map A.mulVecLin, ρ y *ᵥ v ∈ W.map A.mulVecLin := by
      intro y v hv
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
      refine Submodule.mem_map.mpr ⟨ρ' y *ᵥ w, hW y w hw, ?_⟩
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hint]
    have hW'ne : W.map A.mulVecLin ≠ ⊥ := by
      intro h
      apply hWb
      rw [← Submodule.finrank_eq_zero, ← hrank, h]
      exact finrank_bot ℂ (Fin d → ℂ)
    have hmin := Nat.find_min' hex ⟨W.map A.mulVecLin, hW'inv, hW'ne, rfl⟩
    apply Submodule.eq_top_of_finrank_eq
    have hle := Submodule.finrank_le W
    rw [Module.finrank_fin_fun] at hle ⊢
    omega

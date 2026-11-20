import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult

/- English proof (translation)
Introduce `R S W _ _ _ actW B hB U hU`. Take `⟨_, hpos, hadj⟩` from `hB`. Prove the components needed by the constructor for the conclusion. Introduce `X hX x hx`. Use `GlobalTheory.TensorHW.kc_ind actW (U.orthogonalBilin B) x (fun a b hab => ?_) hX` and prove the remaining obligations.

Rewrite `hx`, the goal using `[Submodule.mem_orthogonalBilin_iff]`. Introduce `n hn`. Establish `hba : sameBlock b a`. Apply the tactic sequence `cases a <;> cases b <;> simp_all [sameBlock]`. Establish `h` using `hadj b a hba n x`.

Use `show B n (actW (Eab a b) x) = 0`. Rewrite using `[← h]`. Conclude with `hx _ (hU _ (GlobalTheory.TensorHW.isKC_Eab hba) n hn)`. Establish `hinf : U ⊓ U.orthogonalBilin B = ⊥`. Rewrite using `[eq_bot_iff]`.

Introduce `x hx`. Take `⟨hxU, hxo⟩` from `Submodule.mem_inf.mp hx`. Rewrite `hxo` using `[Submodule.mem_orthogonalBilin_iff]`. Establish `h0 : B x x = 0` using `hxo x hxU`. Rewrite using `[Submodule.mem_bot]`.

Assume the negation of the conclusion as `hne`. Establish `h` using `hpos x hne`. Rewrite `h` using `[h0]`. Simplify using `at h`. Set `b` to `Module.finBasis ℂ U`.

Set `ψ : W →ₗ[ℂ] (Fin (Module.finrank ℂ U) → ℂ)` to `LinearMap.pi (fun i => B (b i : W))`. Establish `hker : LinearMap.ker ψ ≤ U.orthogonalBilin B`. Introduce `x hx`. Rewrite `hx` using `[LinearMap.mem_ker]`. Rewrite using `[Submodule.mem_orthogonalBilin_iff]`.

Introduce `n hn`. Establish `hf : (B.flip x).comp U.subtype = 0`. Use `b.ext (fun i => ?_)` and prove the remaining obligations. Establish `h` using `congrFun hx i`. Simplify `h` using `[ψ]`.

Establish `h` using `LinearMap.congr_fun hf ⟨n, hn⟩`. Simplify using `using h`. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker ψ`. Establish `h2 : Module.finrank ℂ (LinearMap.range ψ) ≤ Module.finrank ℂ U`. Establish `h` using `Submodule.finrank_le (LinearMap.range ψ)`.

Simplify using `using h`. Establish `h3` using `Submodule.finrank_mono hker`. Establish `h4` using `Submodule.finrank_sup_add_finrank_inf_eq U (U.orthogonalBilin B)`. Rewrite `h4` using `[hinf, finrank_bot]`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises.

Apply `le_antisymm (Submodule.finrank_le _)` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers.
-/
theorem orthogonal_kstable_compl : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), IsUnitary actW B →
    ∀ U : Submodule ℂ W, KStable actW U → KStable actW (U.orthogonalBilin B) ∧ U ⊔ U.orthogonalBilin B = ⊤ := by
  intro R S W _ _ _ actW B hB U hU
  obtain ⟨_, hpos, hadj⟩ := hB
  constructor
  · intro X hX x hx
    refine GlobalTheory.TensorHW.kc_ind actW (U.orthogonalBilin B) x (fun a b hab => ?_) hX
    rw [Submodule.mem_orthogonalBilin_iff] at hx ⊢
    intro n hn
    have hba : sameBlock b a := by
      cases a <;> cases b <;> simp_all [sameBlock]
    have h := hadj b a hba n x
    show B n (actW (Eab a b) x) = 0
    rw [← h]
    exact hx _ (hU _ (GlobalTheory.TensorHW.isKC_Eab hba) n hn)
  · have hinf : U ⊓ U.orthogonalBilin B = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxU, hxo⟩ := Submodule.mem_inf.mp hx
      rw [Submodule.mem_orthogonalBilin_iff] at hxo
      have h0 : B x x = 0 := hxo x hxU
      rw [Submodule.mem_bot]
      by_contra hne
      have h := hpos x hne
      rw [h0] at h
      simp at h
    let b := Module.finBasis ℂ U
    let ψ : W →ₗ[ℂ] (Fin (Module.finrank ℂ U) → ℂ) := LinearMap.pi (fun i => B (b i : W))
    have hker : LinearMap.ker ψ ≤ U.orthogonalBilin B := by
      intro x hx
      rw [LinearMap.mem_ker] at hx
      rw [Submodule.mem_orthogonalBilin_iff]
      intro n hn
      have hf : (B.flip x).comp U.subtype = 0 := by
        refine b.ext (fun i => ?_)
        have h := congrFun hx i
        simpa [ψ] using h
      have h := LinearMap.congr_fun hf ⟨n, hn⟩
      simpa using h
    have h1 := LinearMap.finrank_range_add_finrank_ker ψ
    have h2 : Module.finrank ℂ (LinearMap.range ψ) ≤ Module.finrank ℂ U := by
      have h := Submodule.finrank_le (LinearMap.range ψ)
      simpa using h
    have h3 := Submodule.finrank_mono hker
    have h4 := Submodule.finrank_sup_add_finrank_inf_eq U (U.orthogonalBilin B)
    rw [hinf, finrank_bot] at h4
    apply Submodule.eq_top_of_finrank_eq
    apply le_antisymm (Submodule.finrank_le _)
    omega

end GlobalTheory.SteepMult

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordConjOfCoord
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open GlobalTheory.Sl2Ad

namespace GlobalTheory

/- English proof (translation)
Use `set Y : Matrix (Fin 2) (Fin 2) K := ofCoord v with hY`. Establish `hcomm : ∀ g, ((ρ g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Y = Y * (ρ g : Matrix (Fin 2) (Fin 2) K)`. Introduce `g`. Establish `h1 : coord ((ρ g : Matrix (Fin 2) (Fin 2) K) * Y * (((ρ g)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = coord Y`. Rewrite using `[coord_conj_ofCoord, hv g, coord_ofCoord]`.

Establish `h2 : (ρ g : Matrix (Fin 2) (Fin 2) K) * Y * (((ρ g)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Y`. Use `congrArg ofCoord h1` as an intermediate fact. Rewrite `this` using `[ofCoord_coord (by rw [trace_conj, trace_ofCoord]), ofCoord_coord (trace_ofCoord v)]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc _ _ (ρ g : Matrix (Fin 2) (Fin 2) K), ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]`.

Use `_ = Y * (ρ g : Matrix (Fin 2) (Fin 2) K) := by rw [h2]`. Take `⟨μ, hμ⟩` from `Module.End.exists_eigenvalue (Matrix.toLin' Y)`. Use `set W := Module.End.eigenspace (Matrix.toLin' Y) μ with hW`. Establish `hWne : W ≠ ⊥` using `Module.End.hasEigenvalue_iff.mp hμ`. Establish `hWinv : IsInv ρ W`.

Introduce `g x hx`. Rewrite `hx`, the goal using `[hW, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]`. Rewrite using `[Matrix.mulVec_mulVec, ← hcomm g, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]`. Establish `hWtop : W = ⊤`. Break down `hρ.2.2 W le_top hWinv with h | h` into its components or cases.

Conclude with `absurd h hWne`. Conclude with `h`. Establish `hYμ : Y = μ • (1 : Matrix (Fin 2) (Fin 2) K)`. Use extensionality with `i j`. Establish `hx : (Pi.single j 1 : Fin 2 → K) ∈ W` using `by rw [hWtop]; trivial`.

Rewrite `hx` using `[hW, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, Matrix.mulVec_single_one]`. Use `congrFun hx i` as an intermediate fact. Simplify using `only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at this`. Rewrite using `[this, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hij, Pi.single_apply, Ne.symm hij]`. Establish `htr : (2 : K) * μ = 0`. Use `trace_ofCoord v` as an intermediate fact.

Rewrite `this` using `[← hY, hYμ, Matrix.trace_smul, Matrix.trace_one]`. Simplify `this` using `[mul_comm]`. Establish `hμ0 : μ = 0`. Break down `mul_eq_zero.mp htr with h | h` into its components or cases. Conclude with `absurd h two_ne_zero`.

Conclude with `h`. Establish `hY0 : Y = 0` using `by rw [hYμ, hμ0, zero_smul]`. Rewrite using `[← coord_ofCoord v, ← hY, hY0]`. Apply the tactic sequence `ext i; fin_cases i <;> simp [coord]`.
-/
theorem ad_invariant_eq_zero_of_isIrr {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {Γ : Type} [Group Γ]
    (ρ : Γ →* GL (Fin 2) K) (hρ : IsIrr ρ) (v : Fin 3 → K) (hv : ∀ g, ad (ρ g) *ᵥ v = v) : v = 0 := by
  set Y : Matrix (Fin 2) (Fin 2) K := ofCoord v with hY

  have hcomm : ∀ g, ((ρ g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Y = Y * (ρ g : Matrix (Fin 2) (Fin 2) K) := by
    intro g
    have h1 : coord ((ρ g : Matrix (Fin 2) (Fin 2) K) * Y * (((ρ g)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = coord Y := by
      rw [coord_conj_ofCoord, hv g, coord_ofCoord]
    have h2 : (ρ g : Matrix (Fin 2) (Fin 2) K) * Y * (((ρ g)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Y := by
      have := congrArg ofCoord h1
      rwa [ofCoord_coord (by rw [trace_conj, trace_ofCoord]), ofCoord_coord (trace_ofCoord v)] at this
    calc (ρ g : Matrix (Fin 2) (Fin 2) K) * Y
        = (ρ g : Matrix (Fin 2) (Fin 2) K) * Y * (((ρ g)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (ρ g : Matrix (Fin 2) (Fin 2) K) := by
          rw [Matrix.mul_assoc _ _ (ρ g : Matrix (Fin 2) (Fin 2) K), ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      _ = Y * (ρ g : Matrix (Fin 2) (Fin 2) K) := by rw [h2]
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' Y)
  set W := Module.End.eigenspace (Matrix.toLin' Y) μ with hW
  have hWne : W ≠ ⊥ := Module.End.hasEigenvalue_iff.mp hμ
  have hWinv : IsInv ρ W := by
    intro g x hx
    rw [hW, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hx ⊢
    rw [Matrix.mulVec_mulVec, ← hcomm g, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]
  have hWtop : W = ⊤ := by
    rcases hρ.2.2 W le_top hWinv with h | h
    · exact absurd h hWne
    · exact h
  have hYμ : Y = μ • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    have hx : (Pi.single j 1 : Fin 2 → K) ∈ W := by rw [hWtop]; trivial
    rw [hW, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, Matrix.mulVec_single_one] at hx
    have := congrFun hx i
    simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Pi.single_apply, Ne.symm hij]
  have htr : (2 : K) * μ = 0 := by
    have := trace_ofCoord v
    rw [← hY, hYμ, Matrix.trace_smul, Matrix.trace_one] at this
    simpa [mul_comm] using this
  have hμ0 : μ = 0 := by
    rcases mul_eq_zero.mp htr with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hY0 : Y = 0 := by rw [hYμ, hμ0, zero_smul]
  rw [← coord_ofCoord v, ← hY, hY0]
  ext i; fin_cases i <;> simp [coord]

end GlobalTheory

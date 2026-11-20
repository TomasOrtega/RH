import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open UpperHalfPlane hiding I
open scoped MatrixGroups

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Take a linear combination of the given relations to obtain the conclusion. Rewrite the indicated hypotheses using the stated equalities. Take a linear combination of the given relations to obtain the conclusion.
-/
private theorem UpperTheory.V.Af.Rs.eq_T_zpow_mul_of_row_eq {γ δ : SL(2, ℤ)}
    (h : UpperTheory.V.Af.Rs.row γ = UpperTheory.V.Af.Rs.row δ) : ∃ n : ℤ, γ = ModularGroup.T ^ n * δ := by
  have hc : (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := congrFun h 0
  have hd : (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 := congrFun h 1
  have hγ := γ.det_coe
  have hδ := δ.det_coe
  rw [Matrix.det_fin_two] at hγ hδ
  refine ⟨-(γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1
      + (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two, hc, hd]
  · rw [hc, hd] at hγ
    linear_combination (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * hγ
      - (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * hδ
  · rw [hc, hd] at hγ
    linear_combination (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * hγ
      - (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * hδ

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
private theorem UpperTheory.V.Af.Rs.row_T_zpow_mul (n : ℤ) (δ : SL(2, ℤ)) :
    UpperTheory.V.Af.Rs.row (ModularGroup.T ^ n * δ) = UpperTheory.V.Af.Rs.row δ := by
  funext i
  simp [UpperTheory.V.Af.Rs.row, ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Prove the components needed by the constructor for the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact.

Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Af.Rs.rowBij :
    UpperTheory.V.Af.Rs.RowBij := by
  refine ⟨fun γ => ModularGroup.bottom_row_coprime γ, ?_⟩
  intro z x
  obtain ⟨g, -, hg⟩ := ModularGroup.bottom_row_surj (R := ℤ) (Set.mem_setOf_eq ▸ x.2 : x.1 ∈ _)
  have hrow : UpperTheory.V.Af.Rs.row g = x.1 := hg
  refine ⟨ModularGroup.T ^ (-⌊(g • z).re⌋) * g, ⟨?_, ?_⟩, ?_⟩
  · rw [UpperTheory.V.Af.Rs.row_T_zpow_mul, hrow]
  · show 0 ≤ (_ : ℍ).re ∧ (_ : ℍ).re < 1
    rw [mul_smul, ModularGroup.re_T_zpow_smul]
    push_cast
    constructor
    · linarith [Int.floor_le (g • z).re]
    · linarith [Int.lt_floor_add_one (g • z).re]
  · rintro γ' ⟨hr, hs⟩
    have hr' : UpperTheory.V.Af.Rs.row γ' = UpperTheory.V.Af.Rs.row g := by rw [hr, hrow]
    obtain ⟨m, rfl⟩ := UpperTheory.V.Af.Rs.eq_T_zpow_mul_of_row_eq hr'
    have hs' : 0 ≤ ((ModularGroup.T ^ m * g) • z).re ∧ ((ModularGroup.T ^ m * g) • z).re < 1 := hs
    rw [mul_smul, ModularGroup.re_T_zpow_smul] at hs'
    have h1 : ((m + ⌊(g • z).re⌋ : ℤ) : ℝ) < 1 := by
      push_cast
      linarith [Int.floor_le (g • z).re]
    have h2 : (-1 : ℝ) < ((m + ⌊(g • z).re⌋ : ℤ) : ℝ) := by
      push_cast
      linarith [Int.lt_floor_add_one (g • z).re]
    have h1' : m + ⌊(g • z).re⌋ < 1 := by exact_mod_cast h1
    have h2' : -1 < m + ⌊(g • z).re⌋ := by exact_mod_cast h2
    have hm : m = -⌊(g • z).re⌋ := by omega
    rw [hm]

import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW.DomLEOfSle

noncomputable def diagU {n : ℕ} (u : Fin n → ℂˣ) : GL (Fin n) ℂ :=
  ⟨Matrix.diagonal (fun i => (u i : ℂ)), Matrix.diagonal (fun i => ((u i)⁻¹ : ℂˣ)),
    by simp [Matrix.diagonal_mul_diagonal], by simp [Matrix.diagonal_mul_diagonal]⟩

/- English proof (translation)
Use `ext1`. Simplify using `only [Units.val_mul]`. Rewrite using `[← hD.diagonal_diag, ← hE.diagonal_diag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Conclude with `mul_comm _ _`.
-/
lemma diag_commute {n : ℕ} (D E : GL (Fin n) ℂ) (hD : D.val.IsDiag) (hE : E.val.IsDiag) :
    D * E = E * D := by
  ext1
  simp only [Units.val_mul]
  rw [← hD.diagonal_diag, ← hE.diagonal_diag, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

/- English proof (translation)
Establish `h' : ((2 : ℝ) ^ a : ℝ) = (2 : ℝ) ^ b`. Use `congrArg Complex.re h` as an intermediate fact. Establish `ha : ((2 : ℂ) ^ a) = (((2 : ℝ) ^ a : ℝ) : ℂ)` using `by push_cast; rfl`. Establish `hb : ((2 : ℂ) ^ b) = (((2 : ℝ) ^ b : ℝ) : ℂ)` using `by push_cast; rfl`. Rewrite `h` using `[ha, hb]`.

Conclude with `h` after adjusting the coercions. Conclude with `zpow_right_injective₀ (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1) h'`.
-/
lemma two_zpow_inj {a b : ℤ} (h : (2 : ℂ) ^ a = (2 : ℂ) ^ b) : a = b := by
  have h' : ((2 : ℝ) ^ a : ℝ) = (2 : ℝ) ^ b := by
    have := congrArg Complex.re h
    have ha : ((2 : ℂ) ^ a) = (((2 : ℝ) ^ a : ℝ) : ℂ) := by push_cast; rfl
    have hb : ((2 : ℂ) ^ b) = (((2 : ℝ) ^ b : ℝ) : ℂ) := by push_cast; rfl
    rw [ha, hb] at h
    exact_mod_cast h
  exact zpow_right_injective₀ (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1) h'

end GlobalTheory.AlgWtHW.DomLEOfSle

namespace GlobalTheory.AlgWtHW.DomLEOfSle

/- English proof (translation)
Introduce `n ι _ _ Φ hΦ μ lam w hw hw0 hS`. Assume the negation of the conclusion as `hnot`. Set `J` to `{D : GL (Fin n) ℂ // D.val.IsDiag}`. Set `T : J → Module.End ℂ (ι → ℂ)` to `fun D => Matrix.toLin' (Φ D.1)`. Establish `hc : ∀ a b : J, Commute (T a) (T b)`.

Introduce `a b`. Use `show T a * T b = T b * T a`. Establish `e : ∀ A B : Matrix ι ι ℂ, Matrix.toLin' A * Matrix.toLin' B = Matrix.toLin' (A * B)` using `fun A B => by rw [Matrix.toLin'_mul]; rfl`. Simplify using `only [T]`. Rewrite using `[e, e, ← hΦ.mul, ← hΦ.mul, diag_commute a.1 b.1 a.2 b.2]`.

Establish `hind` using `Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo T (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ)`. Set `χ : (Fin n → ℤ) → J → ℂ` to `fun ν D => ∏ i, (D.1.val i i) ^ (ν i)`. Set `E : (J → ℂ) → Submodule ℂ (ι → ℂ)` to `fun c => ⨅ D, (T D).maxGenEigenspace (c D)`. Establish `hmem : ∀ ν v, IsWtVec Φ ν v → v ∈ E (χ ν)`. Introduce `ν v hv`.

Use `Submodule.mem_iInf _ |>.mpr fun D => ?_` and prove the remaining obligations. Apply `Module.End.eigenspace_le_maxGenEigenspace` to reduce the goal to its premises. Rewrite using `[Module.End.mem_eigenspace_iff]`. Simplify using `only [T, Matrix.toLin'_apply]`. Conclude with `hv D.1 D.2`.

Establish `hχinj : ∀ ν ν', χ ν = χ ν' → ν = ν'`. Introduce `ν ν' h`. Use function extensionality and compare the values at `i`. Set `u : Fin n → ℂˣ` to `Function.update 1 i (Units.mk0 2 two_ne_zero)`. Establish `hD : (diagU u).val.IsDiag` using `by show (Matrix.diagonal _).IsDiag`.

Conclude with `Matrix.isDiag_diagonal _`. Establish `key` using `congrFun h ⟨diagU u, hD⟩`. Establish `hprod : ∀ ν'' : Fin n → ℤ, χ ν'' ⟨diagU u, hD⟩ = (2 : ℂ) ^ (ν'' i)`. Introduce `ν''`. Simplify using `only [χ, diagU, Matrix.diagonal_apply_eq]`.

Rewrite using `[Finset.prod_eq_single i]`. Simplify using `[u]`. Introduce `j _ hj`. Simplify using `[u, Function.update_of_ne hj]`. Simplify using the standard rewrite rules.

Rewrite `key` using `[hprod, hprod]`. Conclude with `two_zpow_inj key`. Establish `hle : Sle Φ lam ≤ ⨆ (c : J → ℂ) (_ : c ≠ χ μ), E c`. Unfold `Sle`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `v ⟨ν, hν, hv⟩`. Establish `hne : χ ν ≠ χ μ`. Introduce `h`. Use `hχinj _ _ h` as an intermediate fact. Substitute `this` using the available equality.

Conclude with `hnot hν`. Conclude with `(le_iSup₂ (f := fun (c : J → ℂ) (_ : c ≠ χ μ) => E c) (χ ν) hne) (hmem ν v hv)`. Establish `hdis` using `hind (χ μ)`. Establish `h1 : w ∈ E (χ μ)` using `hmem μ w hw`. Establish `h2 : w ∈ ⨆ (c : J → ℂ) (_ : c ≠ χ μ), E c` using `hle hS`.

Conclude with `hw0 ((Submodule.disjoint_def.mp hdis) w h1 h2)`.
-/
theorem domLE_of_mem_Sle : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (μ lam : Fin n → ℤ) (w : ι → ℂ),
    IsWtVec Φ μ w → w ≠ 0 → w ∈ Sle Φ lam → DomLE μ lam := by
  intro n ι _ _ Φ hΦ μ lam w hw hw0 hS
  by_contra hnot
  let J := {D : GL (Fin n) ℂ // D.val.IsDiag}
  let T : J → Module.End ℂ (ι → ℂ) := fun D => Matrix.toLin' (Φ D.1)
  have hc : ∀ a b : J, Commute (T a) (T b) := by
    intro a b
    show T a * T b = T b * T a
    have e : ∀ A B : Matrix ι ι ℂ, Matrix.toLin' A * Matrix.toLin' B = Matrix.toLin' (A * B) :=
      fun A B => by rw [Matrix.toLin'_mul]; rfl
    simp only [T]
    rw [e, e, ← hΦ.mul, ← hΦ.mul, diag_commute a.1 b.1 a.2 b.2]
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo T
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ)
  let χ : (Fin n → ℤ) → J → ℂ := fun ν D => ∏ i, (D.1.val i i) ^ (ν i)
  let E : (J → ℂ) → Submodule ℂ (ι → ℂ) := fun c => ⨅ D, (T D).maxGenEigenspace (c D)
  have hmem : ∀ ν v, IsWtVec Φ ν v → v ∈ E (χ ν) := by
    intro ν v hv
    refine Submodule.mem_iInf _ |>.mpr fun D => ?_
    apply Module.End.eigenspace_le_maxGenEigenspace
    rw [Module.End.mem_eigenspace_iff]
    simp only [T, Matrix.toLin'_apply]
    exact hv D.1 D.2
  have hχinj : ∀ ν ν', χ ν = χ ν' → ν = ν' := by
    intro ν ν' h
    funext i
    let u : Fin n → ℂˣ := Function.update 1 i (Units.mk0 2 two_ne_zero)
    have hD : (diagU u).val.IsDiag := by
      show (Matrix.diagonal _).IsDiag
      exact Matrix.isDiag_diagonal _
    have key := congrFun h ⟨diagU u, hD⟩
    have hprod : ∀ ν'' : Fin n → ℤ, χ ν'' ⟨diagU u, hD⟩ = (2 : ℂ) ^ (ν'' i) := by
      intro ν''
      simp only [χ, diagU, Matrix.diagonal_apply_eq]
      rw [Finset.prod_eq_single i]
      · simp [u]
      · intro j _ hj
        simp [u, Function.update_of_ne hj]
      · simp
    rw [hprod, hprod] at key
    exact two_zpow_inj key
  have hle : Sle Φ lam ≤ ⨆ (c : J → ℂ) (_ : c ≠ χ μ), E c := by
    unfold Sle
    rw [Submodule.span_le]
    rintro v ⟨ν, hν, hv⟩
    have hne : χ ν ≠ χ μ := by
      intro h
      have := hχinj _ _ h
      subst this
      exact hnot hν
    exact (le_iSup₂ (f := fun (c : J → ℂ) (_ : c ≠ χ μ) => E c) (χ ν) hne) (hmem ν v hv)
  have hdis := hind (χ μ)
  have h1 : w ∈ E (χ μ) := hmem μ w hw
  have h2 : w ∈ ⨆ (c : J → ℂ) (_ : c ≠ χ μ), E c := hle hS
  exact hw0 ((Submodule.disjoint_def.mp hdis) w h1 h2)

end GlobalTheory.AlgWtHW.DomLEOfSle

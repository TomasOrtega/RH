import Mathlib

noncomputable def UpperTheory.Reformulated.B.CharpolyPowersRatios.FreeRatios :
    {κ ι : Type} → [inst : Field κ] → (ι → κˣ) → Prop :=
    fun {κ ι : Type} [Field κ] (α : ι → κˣ) ↦ ∀ (i j : ι), i ≠ j → ∀ (m : ℕ), (0 : ℕ) < m → α i ^ m ≠ α j ^ m

/- English proof (translation)
Introduce `K _ n M a hM hfree d _`. Establish `hinj : Function.Injective (fun i => (a i : K))`. Introduce `i j hij`. Assume the negation of the conclusion as `hne`. Conclude with `hfree i j hne 1 one_pos (by simpa using Units.ext hij)`.

Establish `hev : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' M) (a i : K)`. Introduce `i`. Rewrite using `[Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM, Polynomial.IsRoot.def, Polynomial.eval_prod]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by simp)`. Use `choose v hv using fun i => (hev i).exists_hasEigenvector`.

Establish `hli : LinearIndependent K v` using `Module.End.eigenvectors_linearIndependent' _ (fun i => (a i : K)) hinj v hv`. Set `b : Module.Basis (Fin n) K (Fin n → K)` to `basisOfLinearIndependentOfCardEqFinrank' v hli (by simp)`. Establish `hb : ⇑b = v` using `coe_basisOfLinearIndependentOfCardEqFinrank' v hli _`. Establish `hpow : ∀ j, Matrix.toLin' (M ^ d) (v j) = ((a j : K) ^ d) • v j`. Introduce `j`.

Rewrite using `[Matrix.toLin'_pow]`. Conclude with `(hv j).pow_apply d`. Establish `hmat : LinearMap.toMatrix b b (Matrix.toLin' (M ^ d)) = Matrix.diagonal (fun i => (a i : K) ^ d)`. Use extensionality with `i j`. Rewrite using `[LinearMap.toMatrix_apply, hb, hpow, map_smul, ← hb]`.

Simplify using `only [Module.Basis.repr_self, Matrix.diagonal_apply, Finsupp.smul_single, Finsupp.single_apply, smul_eq_mul, mul_one]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`.

Rewrite using `[← Matrix.charpoly_toLin', ← LinearMap.charpoly_toMatrix _ b, hmat, Matrix.charpoly_diagonal]`.
-/
theorem UpperTheory.Reformulated.B.CharpolyPowersRatios.charpoly_pow :
    ∀ {K : Type} [inst : Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (a : Fin n → Kˣ),
      M.charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : K → Polynomial K) (↑(a i) : K)) →
        UpperTheory.Reformulated.B.CharpolyPowersRatios.FreeRatios a →
          ∀ (d : ℕ),
            (0 : ℕ) < d →
              (M ^ d).charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : K → Polynomial K) ((↑(a i) : K) ^ d)) := by
  intro K _ n M a hM hfree d _
  have hinj : Function.Injective (fun i => (a i : K)) := by
    intro i j hij
    by_contra hne
    exact hfree i j hne 1 one_pos (by simpa using Units.ext hij)
  have hev : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' M) (a i : K) := by
    intro i
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM,
      Polynomial.IsRoot.def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  choose v hv using fun i => (hev i).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' _ (fun i => (a i : K)) hinj v hv
  let b : Module.Basis (Fin n) K (Fin n → K) :=
    basisOfLinearIndependentOfCardEqFinrank' v hli (by simp)
  have hb : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank' v hli _
  have hpow : ∀ j, Matrix.toLin' (M ^ d) (v j) = ((a j : K) ^ d) • v j := by
    intro j
    rw [Matrix.toLin'_pow]
    exact (hv j).pow_apply d
  have hmat : LinearMap.toMatrix b b (Matrix.toLin' (M ^ d)) =
      Matrix.diagonal (fun i => (a i : K) ^ d) := by
    ext i j
    rw [LinearMap.toMatrix_apply, hb, hpow, map_smul, ← hb]
    simp only [Module.Basis.repr_self, Matrix.diagonal_apply, Finsupp.smul_single, Finsupp.single_apply, smul_eq_mul, mul_one]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [← Matrix.charpoly_toLin', ← LinearMap.charpoly_toMatrix _ b, hmat, Matrix.charpoly_diagonal]

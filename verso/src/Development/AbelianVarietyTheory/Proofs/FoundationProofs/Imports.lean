import Mathlib

namespace GlobalTheory.IdealPowerMembership

open MvPolynomial

/- English proof (translation)
Introduce `K L _ _ _ _`. Set `b` to `Module.finBasis K L`. Set `P : Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) (MvPolynomial (Fin (Module.finrank K L)) K)` to `fun j k => ∑ i, X i * C (Algebra.leftMulMatrix b (b i) j k)`. Establish `hP : ∀ j k, (P j k).IsHomogeneous 1`. Introduce `j k`.

Apply `IsHomogeneous.sum` to reduce the goal to its premises. Introduce `i _`. Simplify using `using (isHomogeneous_X K i).mul (isHomogeneous_C (Fin (Module.finrank K L)) (Algebra.leftMulMatrix b (b i) j k))`. Use `⟨P.det, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_apply]`.

Apply `IsHomogeneous.sum` to reduce the goal to its premises. Introduce `σ _`. Establish `h` using `IsHomogeneous.prod (Finset.univ : Finset (Fin (Module.finrank K L))) (fun i => P (σ i) i) (fun _ => 1) (fun i _ => hP (σ i) i)`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h`. Break down `Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs` into its components or cases.

Rewrite using `[hs, one_smul]`. Conclude with `h`. Rewrite using `[hs, Units.neg_smul, one_smul]`. Conclude with `h.neg`. Introduce `x`.

Rewrite using `[Algebra.norm_eq_matrix_det b, RingHom.map_det]`. Use `congr 1`. Use extensionality with `j k`. Establish `hx : x = ∑ i, b.repr x i • b i` using `(b.sum_repr x).symm`. Establish `e1 : Algebra.leftMulMatrix b x = ∑ i, b.repr x i • Algebra.leftMulMatrix b (b i)` using `by conv_lhs => rw [hx]`.

Rewrite using `[map_sum]`. Simplify using `only [map_smul]`. Rewrite using `[e1, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply]`. Simplify using `only [P, map_sum, eval_mul, eval_X, eval_C, Matrix.smul_apply, smul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem main : ∀ (K L : Type) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] [inst_3 : FiniteDimensional K L], ∃ (f : MvPolynomial (Fin (Module.finrank K L)) K), MvPolynomial.IsHomogeneous f (Module.finrank K L) ∧ ∀ (x : L), (Algebra.norm K : L → K) x = (MvPolynomial.eval fun (i : Fin (Module.finrank K L)) ↦ ((Module.Basis.repr (Module.finBasis K L) : L → Fin (Module.finrank K L) →₀ K) x : Fin (Module.finrank K L) → K) i : MvPolynomial (Fin (Module.finrank K L)) K → K) f := by
  intro K L _ _ _ _
  classical
  let b := Module.finBasis K L
  let P : Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) (MvPolynomial (Fin (Module.finrank K L)) K) :=
    fun j k => ∑ i, X i * C (Algebra.leftMulMatrix b (b i) j k)
  have hP : ∀ j k, (P j k).IsHomogeneous 1 := by
    intro j k
    apply IsHomogeneous.sum
    intro i _
    simpa using (isHomogeneous_X K i).mul (isHomogeneous_C (Fin (Module.finrank K L)) (Algebra.leftMulMatrix b (b i) j k))
  refine ⟨P.det, ?_, ?_⟩
  · rw [Matrix.det_apply]
    apply IsHomogeneous.sum
    intro σ _
    have h := IsHomogeneous.prod (Finset.univ : Finset (Fin (Module.finrank K L))) (fun i => P (σ i) i) (fun _ => 1) (fun i _ => hP (σ i) i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · rw [hs, one_smul]; exact h
    · rw [hs, Units.neg_smul, one_smul]; exact h.neg
  · intro x
    rw [Algebra.norm_eq_matrix_det b, RingHom.map_det]
    congr 1
    ext j k
    have hx : x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm
    have e1 : Algebra.leftMulMatrix b x = ∑ i, b.repr x i • Algebra.leftMulMatrix b (b i) := by
      conv_lhs => rw [hx]
      rw [map_sum]
      simp only [map_smul]
    rw [e1, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply]
    simp only [P, map_sum, eval_mul, eval_X, eval_C, Matrix.smul_apply, smul_eq_mul]
    rfl

import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

namespace UpperTheory.V.AlgRepEndIrreducible

open GlobalTheory.WignerGL

section

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {A : Type} [Ring A] [Algebra ℂ A] [Module ℝ A]

omit [Algebra ℂ A] in

private noncomputable def sL (L : Lie E a →ₗ[ℝ] A) (i j : Fin a) : Cinf E →ₗ[ℝ] A where
  toFun x := L (toL (Matrix.single i j x))
  map_add' x y := by
    have h : toL (Matrix.single i j (x + y)) = toL (Matrix.single i j x) + toL (Matrix.single i j y) :=
      congrArg toL (Matrix.single_add i j x y)
    exact (congrArg L h).trans (L.map_add _ _)
  map_smul' c x := by
    have h : toL (Matrix.single i j (c • x)) = c • toL (Matrix.single i j x) :=
      congrArg toL (Matrix.smul_single c i j x).symm
    exact (congrArg L h).trans (L.map_smul _ _)

omit [Algebra ℂ A] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem sL_apply (L : Lie E a →ₗ[ℝ] A) (i j : Fin a) (x : Cinf E) :
    sL L i j x = L (toL (Matrix.single i j x)) := rfl

omit [Algebra ℂ A] in
/- English proof (translation)
Establish `h` using `hL (Matrix.single i j x) (Matrix.single k l y)`. Establish `e : ∀ X Y : Matrix (Fin a) (Fin a) (Cinf E), toL (X - Y) = toL X - toL Y` using `fun _ _ => rfl`. Rewrite `h` using `[e, map_sub]`. Simplify using `only [sL_apply]`. Rewrite using `[h]`.

Establish `z : L (toL 0) = 0` using `map_zero _`. Use `congr 1`. Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[Matrix.single_mul_single_same]`.

Rewrite using `[Matrix.single_mul_single_of_ne _ _ _ _ h, z]`. Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[Matrix.single_mul_single_same, mul_comm y]`. Rewrite using `[Matrix.single_mul_single_of_ne _ _ _ _ h, z]`.
-/
private theorem sL_comm (L : Lie E a →ₗ[ℝ] A) (hL : IsLieHom L) (i j k l : Fin a) (x y : Cinf E) :
    sL L i j x * sL L k l y - sL L k l y * sL L i j x =
      (if j = k then sL L i l (x * y) else 0) - (if l = i then sL L k j (x * y) else 0) := by
  have h := hL (Matrix.single i j x) (Matrix.single k l y)
  have e : ∀ X Y : Matrix (Fin a) (Fin a) (Cinf E), toL (X - Y) = toL X - toL Y := fun _ _ => rfl
  rw [e, map_sub] at h
  simp only [sL_apply]
  rw [h]
  have z : L (toL 0) = 0 := map_zero _
  congr 1
  · split_ifs with h
    · subst h; rw [Matrix.single_mul_single_same]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, z]
  · split_ifs with h
    · subst h; rw [Matrix.single_mul_single_same, mul_comm y]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, z]

/- English proof (translation)
Establish `h1` using `sL_comm L hL i j k l (atEmb τ 1) (atEmb τ' 1)`. Establish `h2` using `sL_comm L hL i j k l (atEmb τ 1) (atEmb τ' .I)`. Establish `h3` using `sL_comm L hL i j k l (atEmb τ .I) (atEmb τ' 1)`. Establish `h4` using `sL_comm L hL i j k l (atEmb τ .I) (atEmb τ' .I)`. Simplify using `only [eL, ← sL_apply, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, smul_sub, smul_smul]`.

Establish `hI : Complex.I * Complex.I = -1` using `Complex.I_mul_I`. Apply the tactic sequence `split_ifs at h1 h2 h3 h4 ⊢ <;>`. Apply the tactic sequence `linear_combination (norm := skip) (exp := 1) (1 / 4 : ℂ) • h1 - (Complex.I / 4 : ℂ) • h2 - (Complex.I / 4 : ℂ) • h3 - (1 / 4 : ℂ) • h4 <;>`. Apply the tactic sequence `match_scalars <;> ring_nf <;> simp`.
-/
private theorem eL_comm_aux (L : Lie E a →ₗ[ℝ] A) (hL : IsLieHom L) (τ τ' : E →+* ℂ) (i j k l : Fin a) :
    eL L τ i j * eL L τ' k l - eL L τ' k l * eL L τ i j =
      (if j = k then (1 / 4 : ℂ) • (sL L i l (atEmb τ 1 * atEmb τ' 1) - sL L i l (atEmb τ .I * atEmb τ' .I) -
        Complex.I • (sL L i l (atEmb τ 1 * atEmb τ' .I) + sL L i l (atEmb τ .I * atEmb τ' 1))) else 0) -
      (if l = i then (1 / 4 : ℂ) • (sL L k j (atEmb τ 1 * atEmb τ' 1) - sL L k j (atEmb τ .I * atEmb τ' .I) -
        Complex.I • (sL L k j (atEmb τ 1 * atEmb τ' .I) + sL L k j (atEmb τ .I * atEmb τ' 1))) else 0) := by
  have h1 := sL_comm L hL i j k l (atEmb τ 1) (atEmb τ' 1)
  have h2 := sL_comm L hL i j k l (atEmb τ 1) (atEmb τ' .I)
  have h3 := sL_comm L hL i j k l (atEmb τ .I) (atEmb τ' 1)
  have h4 := sL_comm L hL i j k l (atEmb τ .I) (atEmb τ' .I)
  simp only [eL, ← sL_apply, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, smul_sub, smul_smul]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  split_ifs at h1 h2 h3 h4 ⊢ <;>
    linear_combination (norm := skip) (exp := 1) (1 / 4 : ℂ) • h1 - (Complex.I / 4 : ℂ) • h2 - (Complex.I / 4 : ℂ) • h3 - (1 / 4 : ℂ) • h4 <;>
    match_scalars <;> ring_nf <;> simp

end

end UpperTheory.V.AlgRepEndIrreducible

open GlobalTheory.WignerGL in
/- English proof (translation)
Introduce `E _ _ _ a A _ _ _ _ L hL`. Use `⟨fun τ i j k l => ?_, fun τ τ' h i j k l => ?_⟩` and prove the remaining obligations. Establish `e : atEmb τ (Complex.I * Complex.I) = -atEmb τ 1`. Rewrite using `[atEmb_eq]`. Simplify using the standard rewrite rules.

Rewrite using `[eL_comm_aux L hL]`. Simplify using `only [atEmb_mul, one_mul, mul_one, e, map_neg, eL, ← sL_apply]`. Apply the tactic sequence `congr 1 <;> split_ifs <;> first | rfl | (match_scalars <;> ring)`. Rewrite using `[← sub_eq_zero, eL_comm_aux L hL]`. Distinguish the cases in `hw : InfinitePlace.mk τ = InfinitePlace.mk τ'`.

Take `rfl : ComplexEmbedding.conjugate τ = τ'` from `(InfinitePlace.mk_eq_iff.1 hw).resolve_left h`. Establish `e : atEmb τ (-Complex.I) = -atEmb τ Complex.I`. Rewrite using `[atEmb_eq]`. Simplify using the standard rewrite rules. Establish `e' : atEmb τ (-1) = -atEmb τ 1`.

Rewrite using `[atEmb_eq]`. Simplify using the standard rewrite rules. Simplify using `[atEmb_conj, atEmb_mul, e, e']`. Simplify using `[atEmb_mul_of_ne hw]`.
-/
theorem UpperTheory.V.AlgRepEndIrreducible.eLRel :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (A : Type) [Ring A] [Algebra ℂ A] [Module ℝ A] [IsScalarTower ℝ ℂ A] (L : Lie E a →ₗ[ℝ] A),
      IsLieHom L → IsMultiGl (eL L) := by
  intro E _ _ _ a A _ _ _ _ L hL
  refine ⟨fun τ i j k l => ?_, fun τ τ' h i j k l => ?_⟩
  · have e : atEmb τ (Complex.I * Complex.I) = -atEmb τ 1 := by
      rw [atEmb_eq]; simp
    rw [eL_comm_aux L hL]
    simp only [atEmb_mul, one_mul, mul_one, e, map_neg, eL, ← sL_apply]
    congr 1 <;> split_ifs <;> first | rfl | (match_scalars <;> ring)
  · rw [← sub_eq_zero, eL_comm_aux L hL]
    by_cases hw : InfinitePlace.mk τ = InfinitePlace.mk τ'
    · obtain rfl : ComplexEmbedding.conjugate τ = τ' := (InfinitePlace.mk_eq_iff.1 hw).resolve_left h
      have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
        rw [atEmb_eq]; simp
      have e' : atEmb τ (-1) = -atEmb τ 1 := by
        rw [atEmb_eq]; simp
      simp [atEmb_conj, atEmb_mul, e, e']
    · simp [atEmb_mul_of_ne hw]

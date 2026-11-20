import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDdSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeEqDet

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

/- English proof (translation)
Introduce `w`. Establish `h2` using `congrArg (rename ⇑w) (h w⁻¹)`. Simplify using `only [map_sum, map_mul, rename_rename] at h2`. Establish `hc : (⇑w ∘ ⇑w⁻¹ : Fin n → Fin n) = id`. Use function extensionality and compare the values at `k`.

Simplify using the standard rewrite rules. Simplify using `only [hc, rename_id, AlgHom.id_apply] at h2`. Repeatedly rewrite using `[mul_comm (b _)]`. Rewrite using `[h2]`. Distinguish the cases in `hw : w = 1`.

Substitute `hw` using the available equality. Simplify using the standard rewrite rules. Establish `hw' : w⁻¹ ≠ 1` using `inv_ne_one.mpr hw`. Simplify using `[hw, hw']`.
-/
private theorem dual_symm {R : Type} [CommRing R] {n : ℕ} {ι : Type} [Fintype ι]
    {a b : ι → MvPolynomial (Fin n) R} (h : IsDual a b) : IsDual b a := by
  intro w
  have h2 := congrArg (rename ⇑w) (h w⁻¹)
  simp only [map_sum, map_mul, rename_rename] at h2
  have hc : (⇑w ∘ ⇑w⁻¹ : Fin n → Fin n) = id := by
    funext k
    simp
  simp only [hc, rename_id, AlgHom.id_apply] at h2
  simp_rw [mul_comm (b _)]
  rw [h2]
  by_cases hw : w = 1
  · subst hw
    simp
  · have hw' : w⁻¹ ≠ 1 := inv_ne_one.mpr hw
    simp [hw, hw']

/- English proof (translation)
Take `⟨hD, -, -⟩` from `UpperTheory.V.AlgebraTools.hkDe R n`. Apply `mul_left_cancel₀ hD` to reduce the goal to its premises. Rewrite using `[Finset.mul_sum]`. Repeatedly rewrite using `[mul_left_comm (De R n), UpperTheory.V.AlgebraTools.hkDdSpec, alt, Finset.mul_sum, map_mul]`. Rewrite using `[Finset.sum_comm]`.

Establish `key : ∀ y : Perm (Fin n), ∑ i, a i * Perm.sign y • ((rename ⇑y) (b i) * (rename ⇑y) x) = Perm.sign y • ((if y = 1 then De R n else 0) * (rename ⇑y) x)`. Introduce `y`. Rewrite using `[← h y, Finset.sum_mul, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, mul_assoc]`.

Rewrite using `[Finset.sum_congr rfl fun y _ => key y]`. Simplify using the standard rewrite rules.
-/
private theorem dual_exp {R : Type} [CommRing R] [IsDomain R] {n : ℕ} {ι : Type} [Fintype ι]
    {a b : ι → MvPolynomial (Fin n) R} (h : IsDual a b) (x : MvPolynomial (Fin n) R) :
    ∑ i, a i * dd (b i * x) = x := by
  obtain ⟨hD, -, -⟩ := UpperTheory.V.AlgebraTools.hkDe R n
  apply mul_left_cancel₀ hD
  rw [Finset.mul_sum]
  simp_rw [mul_left_comm (De R n), UpperTheory.V.AlgebraTools.hkDdSpec, alt, Finset.mul_sum, map_mul]
  rw [Finset.sum_comm]
  have key : ∀ y : Perm (Fin n), ∑ i, a i * Perm.sign y • ((rename ⇑y) (b i) * (rename ⇑y) x) =
      Perm.sign y • ((if y = 1 then De R n else 0) * (rename ⇑y) x) := by
    intro y
    rw [← h y, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, mul_assoc]
  rw [Finset.sum_congr rfl fun y _ => key y]
  simp

/- English proof (translation)
Introduce `R _ _ n ι _ a b h x`. Conclude with `⟨dual_exp h x, dual_exp (dual_symm h) x⟩`.
-/
theorem UpperTheory.V.AlgebraTools.hkDualExp :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (ι : Type) [Fintype ι] (a b : ι → MvPolynomial (Fin n) R), IsDual a b →
      ∀ x, ∑ i, a i * dd (b i * x) = x ∧ ∑ i, b i * dd (a i * x) = x := by
  intro R _ _ n ι _ a b h x
  exact ⟨dual_exp h x, dual_exp (dual_symm h) x⟩

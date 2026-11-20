import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InvAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqLagIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UnitsBasic

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

/- English proof (translation)
Introduce `B E _ _ _ T ι _ _ o U p ho`. Take `⟨hA, hB, -, hD, hE, hF, -⟩` from `units_basic T o U`. Establish `hidem : U.ep p * U.ep p = U.ep p` using `(U.coi.idem p).eq`. Establish `hte : T.tr (U.ep p) = 1` using `U.tr_ep p`. Establish `hxs : ∀ i j, U.x i * T.st (U.x j) = if i = j then U.ep p else 0`.

Introduce `i j`. Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[U.x_st, ho]`. Conclude with `hA i j h`.

Establish `hex : ∀ j, U.ep p * U.x j = U.x j`. Introduce `j`. Establish `h` using `U.x_mem j`. Rewrite `h` using `[ho]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hE' : ∀ i j y, U.x i * y * T.st (U.x j) = T.tr (U.x i * y * T.st (U.x j)) • U.ep p`. Introduce `i j y`. Establish `h` using `hE i j y (by rw [ho i, ho j])`. Rewrite `h` using `[ho i]`. Then use the resulting hypothesis. Establish `hpair : ∀ a b : E, a = T.tr a • U.ep p → b = T.tr b • U.ep p → T.tr (a * b) = T.tr a * T.tr b`.

Introduce `a b ha hb`. Combine the equalities or inequalities in the displayed calculation. Set `f : E → Matrix ι ι B` to `fun y => Matrix.of fun i j => T.tr (U.x i * y * T.st (U.x j))`. Set `g : Matrix ι ι B → E` to `fun M => ∑ i, ∑ j, M i j • (T.st (U.x i) * U.x j)`. Establish `hfmul : ∀ y z, f (y * z) = f y * f z`.

Introduce `y z`. Use extensionality with `i j`. Simplify using `only [f, Matrix.of_apply, Matrix.mul_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hB, mul_one, mul_assoc (U.x i) y z]`.

Use `_ = ∑ k, T.tr ((U.x i * y * T.st (U.x k)) * (U.x k * z * T.st (U.x j))) := by`. Simplify using `only [Finset.mul_sum, Finset.sum_mul, map_sum, mul_assoc]`. Use `_ = _ := by`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Conclude with `hpair _ _ (hE' i k y) (hE' k j z)`.

Establish `hfadd : ∀ y z, f (y + z) = f y + f z`. Introduce `y z`. Use extensionality with `i j`. Simplify using `only [f, Matrix.of_apply, Matrix.add_apply, mul_add, add_mul, map_add]`. Establish `hfsmul : ∀ (r : B) y, f (r • y) = r • f y`.

Introduce `r y`. Use extensionality with `i j`. Simplify using `only [f, Matrix.of_apply, Matrix.smul_apply, mul_smul_comm, smul_mul_assoc, map_smul]`. Establish `hf1 : f 1 = 1`. Use extensionality with `i j`.

Simplify using `only [f, Matrix.of_apply, mul_one, hxs, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp [hte]`. Establish `hgf : ∀ y, g (f y) = y`. Introduce `y`. Simplify using `only [g, f, Matrix.of_apply]`.

Use `conv_rhs => rw [hF y]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `h` using `hE' i j y`. Use `set c := T.tr (U.x i * y * T.st (U.x j)) with hc`. Rewrite using `[h, mul_smul_comm, smul_mul_assoc, mul_assoc, hex]`.

Establish `hfg : ∀ M, f (g M) = M`. Introduce `M`. Use extensionality with `i j`. Establish `hq : ∀ k l, U.x i * (T.st (U.x k) * U.x l) * T.st (U.x j) = (U.x i * T.st (U.x k)) * (U.x l * T.st (U.x j))`. Introduce `k l`.

Simplify using `only [mul_assoc]`. Simplify using `only [f, g, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul, map_sum, mul_smul_comm, smul_mul_assoc, map_smul, hq, hxs]`. Simplify using `[ite_mul, mul_ite, hidem, hte, apply_ite]`. Establish `hfst : ∀ y, f (T.st y) = (f y)ᵀ`. Introduce `y`.

Use extensionality with `i j`. Simplify using `only [f, Matrix.of_apply, Matrix.transpose_apply]`. Rewrite using `[← T.tr_st (U.x j * y * T.st (U.x i)), T.st_mul, T.st_mul, T.st_st, mul_assoc]`. Establish `hftr : ∀ y, (f y).trace = T.tr y`. Introduce `y`.

Simplify using `only [Matrix.trace, Matrix.diag, f, Matrix.of_apply]`. Conclude with `(hD y).symm`. Establish `hcomm : ∀ r : B, f (algebraMap B E r) = algebraMap B (Matrix ι ι B) r`. Introduce `r`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, hfsmul, hf1]`.

Set `φ : E ≃ₐ[B] Matrix ι ι B` to `{ toFun := f, invFun := g, left_inv := hgf, right_inv := hfg, map_mul' := hfmul, map_add' := hfadd, commutes' := hcomm }`. Conclude with `⟨φ, fun y i j => rfl, hfst, hftr⟩`.
-/
theorem UpperTheory.V.AlgebraTools.units_one_block :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o) (p : ι), (∀ i, o i = p) → ∃ φ : E ≃ₐ[B] Matrix ι ι B, (∀ y i j, φ y i j = T.tr (U.x i * y * T.st (U.x j))) ∧ (∀ y, φ (T.st y) = (φ y)ᵀ) ∧ ∀ y, (φ y).trace = T.tr y := by
  intro B E _ _ _ T ι _ _ o U p ho
  obtain ⟨hA, hB, -, hD, hE, hF, -⟩ := units_basic T o U
  have hidem : U.ep p * U.ep p = U.ep p := (U.coi.idem p).eq
  have hte : T.tr (U.ep p) = 1 := U.tr_ep p
  have hxs : ∀ i j, U.x i * T.st (U.x j) = if i = j then U.ep p else 0 := by
    intro i j
    split_ifs with h
    · subst h
      rw [U.x_st, ho]
    · exact hA i j h
  have hex : ∀ j, U.ep p * U.x j = U.x j := by
    intro j
    have h := U.x_mem j
    rw [ho] at h
    calc U.ep p * U.x j = U.ep p * (U.ep p * U.x j * U.ep j) := by rw [h]
      _ = U.ep p * U.ep p * U.x j * U.ep j := by simp only [mul_assoc]
      _ = U.x j := by rw [hidem, h]
  have hE' : ∀ i j y, U.x i * y * T.st (U.x j) = T.tr (U.x i * y * T.st (U.x j)) • U.ep p := by
    intro i j y
    have h := hE i j y (by rw [ho i, ho j])
    rwa [ho i] at h
  have hpair : ∀ a b : E, a = T.tr a • U.ep p → b = T.tr b • U.ep p → T.tr (a * b) = T.tr a * T.tr b := by
    intro a b ha hb
    calc T.tr (a * b) = T.tr ((T.tr a • U.ep p) * (T.tr b • U.ep p)) := by rw [← ha, ← hb]
      _ = T.tr a * T.tr b := by rw [smul_mul_smul_comm, hidem, map_smul, hte, smul_eq_mul, mul_one]
  let f : E → Matrix ι ι B := fun y => Matrix.of fun i j => T.tr (U.x i * y * T.st (U.x j))
  let g : Matrix ι ι B → E := fun M => ∑ i, ∑ j, M i j • (T.st (U.x i) * U.x j)
  have hfmul : ∀ y z, f (y * z) = f y * f z := by
    intro y z
    ext i j
    simp only [f, Matrix.of_apply, Matrix.mul_apply]
    calc T.tr (U.x i * (y * z) * T.st (U.x j))
        = T.tr (U.x i * y * (∑ k, T.st (U.x k) * U.x k) * z * T.st (U.x j)) := by
          rw [hB, mul_one, mul_assoc (U.x i) y z]
      _ = ∑ k, T.tr ((U.x i * y * T.st (U.x k)) * (U.x k * z * T.st (U.x j))) := by
          simp only [Finset.mul_sum, Finset.sum_mul, map_sum, mul_assoc]
      _ = _ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          exact hpair _ _ (hE' i k y) (hE' k j z)
  have hfadd : ∀ y z, f (y + z) = f y + f z := by
    intro y z
    ext i j
    simp only [f, Matrix.of_apply, Matrix.add_apply, mul_add, add_mul, map_add]
  have hfsmul : ∀ (r : B) y, f (r • y) = r • f y := by
    intro r y
    ext i j
    simp only [f, Matrix.of_apply, Matrix.smul_apply, mul_smul_comm, smul_mul_assoc, map_smul]
  have hf1 : f 1 = 1 := by
    ext i j
    simp only [f, Matrix.of_apply, mul_one, hxs, Matrix.one_apply]
    split_ifs <;> simp [hte]
  have hgf : ∀ y, g (f y) = y := by
    intro y
    simp only [g, f, Matrix.of_apply]
    conv_rhs => rw [hF y]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h := hE' i j y
    set c := T.tr (U.x i * y * T.st (U.x j)) with hc
    rw [h, mul_smul_comm, smul_mul_assoc, mul_assoc, hex]
  have hfg : ∀ M, f (g M) = M := by
    intro M
    ext i j
    have hq : ∀ k l, U.x i * (T.st (U.x k) * U.x l) * T.st (U.x j) = (U.x i * T.st (U.x k)) * (U.x l * T.st (U.x j)) := by
      intro k l
      simp only [mul_assoc]
    simp only [f, g, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul, map_sum, mul_smul_comm, smul_mul_assoc, map_smul, hq, hxs]
    simp [ite_mul, mul_ite, hidem, hte, apply_ite]
  have hfst : ∀ y, f (T.st y) = (f y)ᵀ := by
    intro y
    ext i j
    simp only [f, Matrix.of_apply, Matrix.transpose_apply]
    rw [← T.tr_st (U.x j * y * T.st (U.x i)), T.st_mul, T.st_mul, T.st_st, mul_assoc]
  have hftr : ∀ y, (f y).trace = T.tr y := by
    intro y
    simp only [Matrix.trace, Matrix.diag, f, Matrix.of_apply]
    exact (hD y).symm
  have hcomm : ∀ r : B, f (algebraMap B E r) = algebraMap B (Matrix ι ι B) r := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, hfsmul, hf1]
  let φ : E ≃ₐ[B] Matrix ι ι B := { toFun := f, invFun := g, left_inv := hgf, right_inv := hfg, map_mul' := hfmul, map_add' := hfadd, commutes' := hcomm }
  exact ⟨φ, fun y i j => rfl, hfst, hftr⟩

import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.OrdinaryFlagThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.PotOfUnl
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.BlockValuationRep

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.Th UpperTheory.V.Z.J
open scoped Pointwise

namespace UpperTheory.V.Z.Keep.K3

open UpperTheory.V.Th.End3

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)` and prove the remaining obligations. Break down `lt_or_gt_of_ne hj with h | h` into its components or cases. Rewrite using `[hA (show id j < id i from h), zero_mul]`. Rewrite using `[hB (show id i < id j from h), mul_zero]`.
-/
private theorem diag_mul {k : Type} [CommRing k] {n : ℕ} (A B : Matrix (Fin n) (Fin n) k)
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hA (show id j < id i from h), zero_mul]
  · rw [hB (show id i < id j from h), mul_zero]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Use `choose g hg using hne`. Set `U : Fin 3 → Matrix (Fin 3) (Fin 3) k` to `fun a => Q.val * (T (g a) - ψ a (g a) • 1) * (Q⁻¹).val`. Establish `hQ : (Q⁻¹).val * Q.val = 1` using `Units.inv_mul Q`.

Establish `hQ' : Q.val * (Q⁻¹).val = 1` using `Units.mul_inv Q`. Establish `hU : ∀ a, U a = Q.val * T (g a) * (Q⁻¹).val - ψ a (g a) • 1` using `fun a => by`. Simplify using `only [U, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hQ']`. Establish `hUt : ∀ a, (U a).BlockTriangular id` using `fun a => by`. Rewrite using `[hU]`.

Use `(tri _).sub fun i j hij => ?_` and prove the remaining obligations. Establish `hne : i ≠ j` using `fun h => by`. Substitute `h` using the available equality. Conclude with `lt_irrefl _ hij`. Simplify using `[Matrix.one_apply_ne hne]`.

Establish `hUd : ∀ a, U a b b ≠ 0` using `fun a => by`. Rewrite using `[hU, Matrix.sub_apply, dg, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]`. Conclude with `sub_ne_zero.2 (hg a)`. Establish `h0 : U 0 * (U 1 * U 2) = 0`. Establish `h1` using `ord g`.

Simplify using `only [Fr.ordProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one] at h1`. Establish `h2 : Q.val * ((T (g 0) - ψ 0 (g 0) • 1) * ((T (g 1) - ψ 1 (g 1) • 1) * (T (g 2) - ψ 2 (g 2) • 1))) * (Q⁻¹).val = 0`. Establish `h3 : (T (g 0) - ψ 0 (g 0) • 1) * ((T (g 1) - ψ 1 (g 1) • 1) * (T (g 2) - ψ 2 (g 2) • 1)) = 0` using `h1`. Rewrite using `[h3, Matrix.mul_zero, Matrix.zero_mul]`. Rewrite using `[← h2]`.

Simplify using `only [U]`. Combine the equalities or inequalities in the displayed calculation. Establish `h4` using `congrFun (congrFun h0 b) b`. Rewrite `h4` using `[diag_mul _ _ (hUt 0) ((hUt 1).mul (hUt 2)), diag_mul _ _ (hUt 1) (hUt 2)]`. Conclude with `mul_ne_zero (hUd 0) (mul_ne_zero (hUd 1) (hUd 2)) h4`.
-/
private theorem graded_match {H k : Type} [Field k] (T : H → Matrix (Fin 3) (Fin 3) k) (ψ : Fin 3 → H → k)
    (D : Fin 3 → H → k) (Q : GL (Fin 3) k)
    (tri : ∀ g, (Q.val * T g * (Q⁻¹).val).BlockTriangular id)
    (dg : ∀ g i, (Q.val * T g * (Q⁻¹).val) i i = D i g)
    (ord : ∀ g, Fr.ordProd T ψ g = 0) (b : Fin 3) : ∃ a, ∀ g, D b g = ψ a g := by
  by_contra hne
  push_neg at hne
  choose g hg using hne
  let U : Fin 3 → Matrix (Fin 3) (Fin 3) k := fun a => Q.val * (T (g a) - ψ a (g a) • 1) * (Q⁻¹).val
  have hQ : (Q⁻¹).val * Q.val = 1 := Units.inv_mul Q
  have hQ' : Q.val * (Q⁻¹).val = 1 := Units.mul_inv Q
  have hU : ∀ a, U a = Q.val * T (g a) * (Q⁻¹).val - ψ a (g a) • 1 := fun a => by
    simp only [U, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hQ']
  have hUt : ∀ a, (U a).BlockTriangular id := fun a => by
    rw [hU]
    refine (tri _).sub fun i j hij => ?_
    have hne : i ≠ j := fun h => by
      subst h
      exact lt_irrefl _ hij
    simp [Matrix.one_apply_ne hne]
  have hUd : ∀ a, U a b b ≠ 0 := fun a => by
    rw [hU, Matrix.sub_apply, dg, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    exact sub_ne_zero.2 (hg a)
  have h0 : U 0 * (U 1 * U 2) = 0 := by
    have h1 := ord g
    simp only [Fr.ordProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one] at h1
    have h2 : Q.val * ((T (g 0) - ψ 0 (g 0) • 1) * ((T (g 1) - ψ 1 (g 1) • 1) * (T (g 2) - ψ 2 (g 2) • 1))) * (Q⁻¹).val = 0 := by
      have h3 : (T (g 0) - ψ 0 (g 0) • 1) * ((T (g 1) - ψ 1 (g 1) • 1) * (T (g 2) - ψ 2 (g 2) • 1)) = 0 := h1
      rw [h3, Matrix.mul_zero, Matrix.zero_mul]
    rw [← h2]
    simp only [U]
    calc _ = Q.val * (T (g 0) - ψ 0 (g 0) • 1) * ((Q⁻¹).val * Q.val) * (T (g 1) - ψ 1 (g 1) • 1) * ((Q⁻¹).val * Q.val) *
          (T (g 2) - ψ 2 (g 2) • 1) * (Q⁻¹).val := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hQ]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have h4 := congrFun (congrFun h0 b) b
  rw [diag_mul _ _ (hUt 0) ((hUt 1).mul (hUt 2)), diag_mul _ _ (hUt 1) (hUt 2)] at h4
  exact mul_ne_zero (hUd 0) (mul_ne_zero (hUd 1) (hUd 2)) h4

/- English proof (translation)
Establish `a1` using `ha 1 0 (by decide)`. Establish `a2` using `ha 2 0 (by decide)`. Establish `a3` using `ha 2 1 (by decide)`. Establish `b4` using `hb 1 0 (by decide)`. Establish `b2` using `hb 2 0 (by decide)`.

Establish `b3` using `hb 2 1 (by decide)`. Establish `c4` using `hc 1 0 (by decide)`. Establish `c5` using `hc 2 0 (by decide)`. Establish `c3` using `hc 2 1 (by decide)`. Use extensionality with `i j`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_three, a0, a1, a2, a3, b1, b2, b3, b4, c2, c3, c4, c5]`.
-/
private theorem tri_zero {k : Type} [CommRing k] (a b c : Matrix (Fin 3) (Fin 3) k)
    (ha : ∀ i j, j < i → a i j = 0) (hb : ∀ i j, j < i → b i j = 0) (hc : ∀ i j, j < i → c i j = 0)
    (a0 : a 0 0 = 0) (b1 : b 1 1 = 0) (c2 : c 2 2 = 0) : a * (b * c) = 0 := by
  have a1 := ha 1 0 (by decide)
  have a2 := ha 2 0 (by decide)
  have a3 := ha 2 1 (by decide)
  have b4 := hb 1 0 (by decide)
  have b2 := hb 2 0 (by decide)
  have b3 := hb 2 1 (by decide)
  have c4 := hc 1 0 (by decide)
  have c5 := hc 2 0 (by decide)
  have c3 := hc 2 1 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, a0, a1, a2, a3, b1, b2, b3, b4, c2, c3, c4, c5]

/- English proof (translation)
Take `⟨P, hP⟩` from `h`. Establish `hQ : (P⁻¹).val * P.val = 1` using `Units.inv_mul P`. Establish `hQ' : P.val * (P⁻¹).val = 1` using `Units.mul_inv P`. Set `U : Fin 3 → Matrix (Fin 3) (Fin 3) k` to `fun a => (P * ρ (g a) * P⁻¹ : GL (Fin 3) k).val - (κ a (g a) : k) • 1`. Establish `tri : ∀ a x y, y < x → U a x y = 0` using `fun a x y h => by`.

Establish `hne : x ≠ y` using `fun e => by`. Substitute `e` using the available equality. Conclude with `lt_irrefl _ h`. Establish `h1` using `(hP (g a)).1 x y h`. Simplify using `only [U, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne hne, smul_zero, sub_zero]`.

Conclude with `h1`. Establish `dg : ∀ a, U a a a = 0` using `fun a => by`. Establish `h1` using `(hP (g a)).2 a`. Simplify using `only [U, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]`. Conclude with `sub_eq_zero.2 h1`.

Establish `hX : ∀ a, (ρ (g a)).val - (κ a (g a) : k) • 1 = (P⁻¹).val * U a * P.val` using `fun a => by`. Establish `e1 : (P⁻¹).val * (P * ρ (g a) * P⁻¹ : GL (Fin 3) k).val * P.val = (ρ (g a)).val`. Rewrite using `[← Units.val_mul, ← Units.val_mul]`. Use `congr 1`. Use `group`.

Simplify using `only [U, Matrix.mul_sub, Matrix.sub_mul, e1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hQ]`. Establish `hm : ∀ x y : Matrix (Fin 3) (Fin 3) k, ((P⁻¹).val * x * P.val) * ((P⁻¹).val * y * P.val) = (P⁻¹).val * (x * y) * P.val` using `fun x y => by`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : ((ρ (g 0)).val - (κ 0 (g 0) : k) • 1) * (((ρ (g 1)).val - (κ 1 (g 1) : k) • 1) * ((ρ (g 2)).val - (κ 2 (g 2) : k) • 1)) = 0`. Rewrite using `[hX 0, hX 1, hX 2, hm, hm, tri_zero _ _ _ (tri 0) (tri 1) (tri 2) (dg 0) (dg 1) (dg 2), Matrix.mul_zero, Matrix.zero_mul]`.

Simplify using `only [Fr.ordProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]`. Conclude with `h3`.
-/
private theorem ord_of_flag {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 3) k) (H : Subgroup Γ)
    (κ : Fin 3 → ↥H →* kˣ) (h : Af.IsFlagOn ρ H κ) (g : Fin 3 → ↥H) :
    Fr.ordProd (fun s : ↥H => (ρ s).val) (fun a s => (κ a s : k)) g = 0 := by
  obtain ⟨P, hP⟩ := h
  have hQ : (P⁻¹).val * P.val = 1 := Units.inv_mul P
  have hQ' : P.val * (P⁻¹).val = 1 := Units.mul_inv P
  let U : Fin 3 → Matrix (Fin 3) (Fin 3) k := fun a =>
    (P * ρ (g a) * P⁻¹ : GL (Fin 3) k).val - (κ a (g a) : k) • 1
  have tri : ∀ a x y, y < x → U a x y = 0 := fun a x y h => by
    have hne : x ≠ y := fun e => by
      subst e
      exact lt_irrefl _ h
    have h1 := (hP (g a)).1 x y h
    simp only [U, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne hne, smul_zero, sub_zero]
    exact h1
  have dg : ∀ a, U a a a = 0 := fun a => by
    have h1 := (hP (g a)).2 a
    simp only [U, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    exact sub_eq_zero.2 h1
  have hX : ∀ a, (ρ (g a)).val - (κ a (g a) : k) • 1 = (P⁻¹).val * U a * P.val := fun a => by
    have e1 : (P⁻¹).val * (P * ρ (g a) * P⁻¹ : GL (Fin 3) k).val * P.val = (ρ (g a)).val := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    simp only [U, Matrix.mul_sub, Matrix.sub_mul, e1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hQ]
  have hm : ∀ x y : Matrix (Fin 3) (Fin 3) k, ((P⁻¹).val * x * P.val) * ((P⁻¹).val * y * P.val) =
      (P⁻¹).val * (x * y) * P.val := fun x y => by
    calc _ = (P⁻¹).val * x * (P.val * (P⁻¹).val) * y * P.val := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hQ']; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have h3 : ((ρ (g 0)).val - (κ 0 (g 0) : k) • 1) * (((ρ (g 1)).val - (κ 1 (g 1) : k) • 1) *
      ((ρ (g 2)).val - (κ 2 (g 2) : k) • 1)) = 0 := by
    rw [hX 0, hX 1, hX 2, hm, hm, tri_zero _ _ _ (tri 0) (tri 1) (tri 2) (dg 0) (dg 1) (dg 2), Matrix.mul_zero,
      Matrix.zero_mul]
  simp only [Fr.ordProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  exact h3

/- English proof (translation)
Take `⟨P, hP⟩` from `h₀`. Take `⟨a, ha⟩` from `graded_match (fun s : ↥H => (ρ s).val) (fun a s => (κ₁ a s : k)) (fun a s => (κ₀ a s : k)) P (fun g x y hxy => (hP g).1 x y hxy) (fun g x => (hP g).2 x) (ord_of_flag ρ H κ₁ h₁) b`. Conclude with `⟨a, MonoidHom.ext fun s => Units.ext (ha s)⟩`.
-/
private theorem flag_same {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 3) k) (H : Subgroup Γ)
    (κ₀ κ₁ : Fin 3 → ↥H →* kˣ) (h₀ : Af.IsFlagOn ρ H κ₀) (h₁ : Af.IsFlagOn ρ H κ₁) (b : Fin 3) :
    ∃ a, κ₀ b = κ₁ a := by
  obtain ⟨P, hP⟩ := h₀
  obtain ⟨a, ha⟩ := graded_match (fun s : ↥H => (ρ s).val) (fun a s => (κ₁ a s : k)) (fun a s => (κ₀ a s : k)) P
    (fun g x y hxy => (hP g).1 x y hxy) (fun g x => (hP g).2 x) (ord_of_flag ρ H κ₁ h₁) b
  exact ⟨a, MonoidHom.ext fun s => Units.ext (ha s)⟩

/- English proof (translation)
Establish `h : (0 : ℤ) < e` using `by exact_mod_cast he`. Introduce `a b hab`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> first | (exfalso; revert hab; decide) | (simp; omega)`.
-/
private theorem anti3 (e : ℕ) (he : 1 ≤ e) : StrictAnti ![(e : ℤ), 0, -(e : ℤ)] := by
  have h : (0 : ℤ) < e := by exact_mod_cast he
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | (exfalso; revert hab; decide) | (simp; omega)

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨h, ?_⟩` and prove the remaining obligations. Simplify using `only [← map_inv]`. Conclude with `h.comp continuous_inv`.
-/
private theorem cont_units {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ] [Monoid M] [TopologicalSpace M]
    (f : Γ →* Mˣ) (h : Continuous fun g => (f g : M)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

end UpperTheory.V.Z.Keep.K3

namespace UpperTheory.V.Z.Keep.K3

open UpperTheory.V.Th.End3

/- English proof (translation)
Establish `hc : ((b⁻¹ : GL (Fin 3) k)).val.BlockTriangular id` using `by haveI : Invertible b.val := ⟨(b⁻¹ : GL (Fin 3) k).val, Units.inv_mul b, Units.mul_inv b⟩`. Rewrite using `[Matrix.coe_units_inv]`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hb`. Establish `hd : ∀ i, ((b⁻¹ : GL (Fin 3) k)).val i i = (b.val i i)⁻¹` using `fun i => by`. Establish `h1` using `congrFun (congrFun (Units.mul_inv b) i) i`.

Rewrite `h1` using `[diag_mul _ _ hb hc, Matrix.one_apply_eq]`. Conclude with `eq_inv_of_mul_eq_one_right h1`. Establish `he : ∀ i j, (theta b).val i j = ((b⁻¹ : GL (Fin 3) k)).val j.rev i.rev` using `fun i j => by`. Rewrite using `[theta_val, Matrix.mul_apply, Finset.sum_eq_single j.rev]`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i.rev]`.

Simplify using `[Jmat]`. Introduce `x _ hx`. Simplify using `[Jmat, hx]`. Simplify using the standard rewrite rules. Introduce `x _ hx`.

Establish `: ¬ j = x.rev` using `fun h => hx (by rw [h, Fin.rev_rev])`. Simplify using `[Jmat, this]`. Simplify using the standard rewrite rules. Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[he]`.

Conclude with `hc (show id i.rev < id j.rev from Fin.rev_lt_rev.2 hij)`. Rewrite using `[he, hd]`.
-/
private theorem theta_upper {k : Type} [Field k] (b : GL (Fin 3) k) (hb : b.val.BlockTriangular id) :
    (theta b).val.BlockTriangular id ∧ ∀ i, (theta b).val i i = (b.val i.rev i.rev)⁻¹ := by
  have hc : ((b⁻¹ : GL (Fin 3) k)).val.BlockTriangular id := by
    haveI : Invertible b.val := ⟨(b⁻¹ : GL (Fin 3) k).val, Units.inv_mul b, Units.mul_inv b⟩
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  have hd : ∀ i, ((b⁻¹ : GL (Fin 3) k)).val i i = (b.val i i)⁻¹ := fun i => by
    have h1 := congrFun (congrFun (Units.mul_inv b) i) i
    rw [diag_mul _ _ hb hc, Matrix.one_apply_eq] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have he : ∀ i j, (theta b).val i j = ((b⁻¹ : GL (Fin 3) k)).val j.rev i.rev := fun i j => by
    rw [theta_val, Matrix.mul_apply, Finset.sum_eq_single j.rev]
    · rw [Matrix.mul_apply, Finset.sum_eq_single i.rev]
      · simp [Jmat]
      · intro x _ hx
        simp [Jmat, hx]
      · simp
    · intro x _ hx
      have : ¬ j = x.rev := fun h => hx (by rw [h, Fin.rev_rev])
      simp [Jmat, this]
    · simp
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [he]
    exact hc (show id i.rev < id j.rev from Fin.rev_lt_rev.2 hij)
  · rw [he, hd]

/- English proof (translation)
Simplify using `[SemidirectProduct.mul_left, SemidirectProduct.inv_left, h1, h2, sgnAct_one]`.
-/
private theorem conj_left_pos {k : Type} [CommRing k] (x y : GG 3 k) (h1 : x.right = 1) (h2 : y.right = 1) :
    (x * y * x⁻¹).left = x.left * y.left * x.left⁻¹ := by
  simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left, h1, h2, sgnAct_one]

/- English proof (translation)
Simplify using `[SemidirectProduct.mul_left, SemidirectProduct.inv_left, h1, h2, sgnAct_neg_one, sgnAct_one, theta_theta]`.
-/
private theorem conj_left_neg {k : Type} [CommRing k] (x y : GG 3 k) (h1 : x.right = -1) (h2 : y.right = 1) :
    (x * y * x⁻¹).left = x.left * theta y.left * x.left⁻¹ := by
  simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left, h1, h2, sgnAct_neg_one, sgnAct_one, theta_theta]

section Mv

variable {Γ k : Type} [Group Γ] [Field k]

private def into (c : Γ →* Γ) (H H' : Subgroup Γ) (hc : ∀ s ∈ H', c s ∈ H) : ↥H' →* ↥H :=
  (c.comp H'.subtype).codRestrict H fun s => hc s s.2

/- English proof (translation)
Take `⟨P, hP⟩` from `hf`. Use `⟨P * a, fun s => ?_⟩` and prove the remaining obligations. Establish `e : (P * a) * ρ s * (P * a)⁻¹ = P * ρ (into c H H' hc s : Γ) * P⁻¹`. Rewrite using `[show ((into c H H' hc s : ↥H) : Γ) = c s from rfl, ha]`. Use `group`.

Rewrite using `[e]`. Conclude with `hP (into c H H' hc s)`.
-/
private theorem flag_plus (ρ : Γ →* GL (Fin 3) k) (c : Γ →* Γ) (H H' : Subgroup Γ) (hc : ∀ s ∈ H', c s ∈ H)
    (κ : Fin 3 → ↥H →* kˣ) (hf : Af.IsFlagOn ρ H κ) (a : GL (Fin 3) k) (ha : ∀ s, ρ (c s) = a * ρ s * a⁻¹) :
    Af.IsFlagOn ρ H' fun i => (κ i).comp (into c H H' hc) := by
  obtain ⟨P, hP⟩ := hf
  refine ⟨P * a, fun s => ?_⟩
  have e : (P * a) * ρ s * (P * a)⁻¹ = P * ρ (into c H H' hc s : Γ) * P⁻¹ := by
    rw [show ((into c H H' hc s : ↥H) : Γ) = c s from rfl, ha]
    group
  rw [e]
  exact hP (into c H H' hc s)

/- English proof (translation)
Take `⟨P, hP⟩` from `hf`. Use `⟨theta (P * a), fun s => ?_⟩` and prove the remaining obligations. Establish `t : ∀ x : GL (Fin 3) k, theta x = thetaAut 3 k x` using `fun _ => rfl`. Establish `e : theta (P * a) * ρ s * (theta (P * a))⁻¹ = theta (P * ρ (into c H H' hc s : Γ) * P⁻¹)`. Rewrite using `[show ((into c H H' hc s : ↥H) : Γ) = c s from rfl, ha]`.

Simplify using `only [t, map_mul, map_inv]`. Simplify using `only [← t, theta_theta]`. Use `group`. Take `⟨h1, h2⟩` from `hP (into c H H' hc s)`. Take `⟨h3, h4⟩` from `theta_upper _ (show ((P * ρ (into c H H' hc s : Γ) * P⁻¹ : GL (Fin 3) k)).val.BlockTriangular id from fun i j hij => h1 i j hij)`.

Rewrite using `[e]`. Use `⟨fun i j hij => h3 hij, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[h4, h2]`. Simplify using the standard rewrite rules.
-/
private theorem flag_minus (ρ : Γ →* GL (Fin 3) k) (c : Γ →* Γ) (H H' : Subgroup Γ) (hc : ∀ s ∈ H', c s ∈ H)
    (κ : Fin 3 → ↥H →* kˣ) (hf : Af.IsFlagOn ρ H κ) (a : GL (Fin 3) k) (ha : ∀ s, ρ (c s) = a * theta (ρ s) * a⁻¹) :
    Af.IsFlagOn ρ H' fun i => ((κ i.rev).comp (into c H H' hc))⁻¹ := by
  obtain ⟨P, hP⟩ := hf
  refine ⟨theta (P * a), fun s => ?_⟩
  have t : ∀ x : GL (Fin 3) k, theta x = thetaAut 3 k x := fun _ => rfl
  have e : theta (P * a) * ρ s * (theta (P * a))⁻¹ = theta (P * ρ (into c H H' hc s : Γ) * P⁻¹) := by
    rw [show ((into c H H' hc s : ↥H) : Γ) = c s from rfl, ha]
    simp only [t, map_mul, map_inv]
    simp only [← t, theta_theta]
    group
  obtain ⟨h1, h2⟩ := hP (into c H H' hc s)
  obtain ⟨h3, h4⟩ := theta_upper _ (show ((P * ρ (into c H H' hc s : Γ) * P⁻¹ : GL (Fin 3) k)).val.BlockTriangular id from
    fun i j hij => h1 i j hij)
  rw [e]
  refine ⟨fun i j hij => h3 hij, fun i => ?_⟩
  rw [h4, h2]
  simp

/- English proof (translation)
Rewrite `h`, the goal using `[valuation_lt_one_iff']`. Establish `e1 : u (n : Ω) = n` using `map_natCast u n`. Establish `e2 : u ((n : Ω)⁻¹) = (n : Ω)⁻¹` using `by rw [map_inv₀, e1]`. Rewrite using `[hA, hA, e1, e2]` and apply the resulting hypothesis.
-/
private theorem below_move {Ω : Type} [Field Ω] [CharZero Ω] {A A' : ValuationSubring Ω} (u : G ℚ Ω) (hA : ∀ x, x ∈ A' ↔ u x ∈ A) (n : ℕ)
    (h : A.valuation (n : Ω) < 1) : A'.valuation (n : Ω) < 1 := by
  rw [valuation_lt_one_iff'] at h ⊢
  have e1 : u (n : Ω) = n := map_natCast u n
  have e2 : u ((n : Ω)⁻¹) = (n : Ω)⁻¹ := by rw [map_inv₀, e1]
  rwa [hA, hA, e1, e2]

end Mv

section Move

variable {Ω K : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `hinj : Function.Injective (galEmb ℚ K Ω)` using `(galEmbTop ℚ K Ω).1.injective`. Use `haveI hNr : (galEmb ℚ K Ω).range.Normal := by rw [range_galEmb]; exact hN`. Set `e` to `MonoidHom.ofInjective hinj`. Set `c : G K Ω ≃* G K Ω` to `(e.trans (MulAut.conjNormal u)).trans e.symm`. Establish `hc : ∀ s, galEmb ℚ K Ω (c s) = u * galEmb ℚ K Ω s * u⁻¹` using `fun s => (MonoidHom.apply_ofInjective_symm hinj _).trans (by simp [e, MulAut.conjNormal_apply, MonoidHom.ofInjective_apply])`.

Establish `hgP : u • P' = P`. Use extensionality with `x`. Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hP]`. Simplify using `[AlgEquiv.smul_def]`. Establish `hd : ∀ s ∈ Dec (F` using `K) P', c.toMonoidHom s ∈ Dec (F := K) P := fun s hs => by`.

Establish `h1 : galEmb ℚ K Ω s • P' = P'` using `hs`. Use `show galEmb ℚ K Ω (c s) • P = P`. Rewrite using `[hc, ← hgP, mul_smul, mul_smul, inv_smul_smul, h1]`. Establish `hcyc : ∀ s, cycBar K Ω l (c s) = cycBar K Ω l s` using `fun s => by show cycBar ℚ Ω l (galEmb ℚ K Ω (c s)) = cycBar ℚ Ω l (galEmb ℚ K Ω s)`. Rewrite using `[hc, map_mul, map_mul, map_inv, mul_inv_cancel_comm]`.

Establish `hρc : ∀ s, ρ (c s) = (R u * R (galEmb ℚ K Ω s) * (R u)⁻¹).left` using `fun s => by`. Rewrite using `[hρ, hc, map_mul, map_mul, map_inv]`. Establish `h1 : Af.PotCrysAt (ρ.comp c.toMonoidHom) P'` using `UpperTheory.potentiallyCrystalline_comp_conjugation u c hc ρ P P' hP hp`. Establish `hev : ∀ s : ↥(Dec (F` using `K) P'), galEmb ℚ K Ω s ∈ T → ((κ i).comp (into c.toMonoidHom _ _ hd)) s = ((κ j).comp (into c.toMonoidHom _ _ hd)) s * cycBar K Ω l s := fun s hs => by`. Establish `hs' : galEmb ℚ K Ω (into c.toMonoidHom _ _ hd s : G K Ω) ∈ T` using `by show galEmb ℚ K Ω (c s) ∈ T`.

Rewrite using `[hc]`. Conclude with `hT _ hs`. Use `hij _ hs'` as an intermediate fact. Rewrite using `[MonoidHom.comp_apply, MonoidHom.comp_apply, this]`. Conclude with `congrArg _ (hcyc s)`.

Break down `Int.units_eq_one_or (R u).right with hu | hu` into its components or cases. Establish `ha : ∀ s, ρ (c.toMonoidHom s) = (R u).left * ρ s * (R u).left⁻¹` using `fun s => by`. Rewrite using `[hρ s]`. Conclude with `(hρc s).trans (conj_left_pos _ _ hu (hK s))`. Use `⟨h1.of_iso ⟨(R u).left⁻¹, fun s => ?_⟩, _, flag_plus ρ c.toMonoidHom _ _ hd κ hf _ ha, i, j, hev⟩` and prove the remaining obligations.

Rewrite using `[MonoidHom.comp_apply, ha]`. Use `group`. Establish `ha : ∀ s, ρ (c.toMonoidHom s) = (R u).left * theta (ρ s) * (R u).left⁻¹` using `fun s => by`. Rewrite using `[hρ s]`. Conclude with `(hρc s).trans (conj_left_neg _ _ hu (hK s))`.

Set `r₂ : G K Ω →* GL (Fin 3) (Qbar l)` to `{ toFun := fun s => trInv (ρ (c s)) map_one' := by`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `[trInv_val]`. Use the proof step `map_mul' := fun a b => by rw [map_mul, map_mul, trInv_mul] }`. Establish `h2 : Af.PotCrysAt r₂ P'` using `UpperTheory.potentiallyCrystalline_contragredient (ρ.comp c.toMonoidHom) r₂ P' (fun s => rfl) h1`.

Establish `hJ : (Jgl (Qbar l) 3)⁻¹ = Jgl (Qbar l) 3` using `inv_eq_of_mul_eq_one_left Jgl_mul_Jgl`. Establish `t : ∀ x : GL (Fin 3) (Qbar l), theta x = thetaAut 3 (Qbar l) x` using `fun _ => rfl`. Use `⟨h2.of_iso ⟨(theta (R u).left)⁻¹ * Jgl _ 3, fun s => ?_⟩, _, flag_minus ρ c.toMonoidHom _ _ hd κ hf _ ha, j.rev, i.rev, fun s hs => ?_⟩` and prove the remaining obligations. Establish `h3 : theta (ρ (c s)) = theta (R u).left * ρ s * (theta (R u).left)⁻¹`. Use `congrArg theta (ha s)` as an intermediate fact.

Simplify using `only [t, map_mul, map_inv] at this ⊢`. Simplify using `only [← t, theta_theta] at this ⊢`. Conclude with `this`. Establish `h4 : theta (ρ (c s)) = Jgl _ 3 * r₂ s * Jgl _ 3` using `rfl`. Rewrite using `[_root_.mul_inv_rev, inv_inv, hJ]`.

Combine the equalities or inequalities in the displayed calculation. Use `hev s hs` as an intermediate fact. Simplify using `only [MonoidHom.inv_apply, Fin.rev_rev]`. Rewrite using `[this]`. Simplify using `[mul_comm]`.
-/
private theorem move_link (ρ : G K Ω →* GL (Fin 3) (Qbar l)) (R : G ℚ Ω →* GG 3 (Qbar l))
    (hρ : ∀ s, ρ s = (R (galEmb ℚ K Ω s)).left) (hK : ∀ s, (R (galEmb ℚ K Ω s)).right = 1)
    (hN : (galOf ℚ K Ω).Normal) (T : Subgroup (G ℚ Ω)) (u : G ℚ Ω) (hT : ∀ s ∈ T, u * s * u⁻¹ ∈ T)
    (P P' : ValuationSubring Ω) (hP : ∀ x, x ∈ P' ↔ u x ∈ P)
    (κ : Fin 3 → ↥(Dec (F := K) P) →* (Qbar l)ˣ) (hf : Af.IsFlagOn ρ (Dec (F := K) P) κ) (hp : Af.PotCrysAt ρ P)
    (i j : Fin 3) (hij : ∀ s : ↥(Dec (F := K) P), galEmb ℚ K Ω s ∈ T → κ i s = κ j s * cycBar K Ω l s) :
    Af.PotCrysAt ρ P' ∧ ∃ κ' : Fin 3 → ↥(Dec (F := K) P') →* (Qbar l)ˣ, Af.IsFlagOn ρ (Dec (F := K) P') κ' ∧
      ∃ i' j', ∀ s : ↥(Dec (F := K) P'), galEmb ℚ K Ω s ∈ T → κ' i' s = κ' j' s * cycBar K Ω l s := by
  have hinj : Function.Injective (galEmb ℚ K Ω) := (galEmbTop ℚ K Ω).1.injective
  haveI hNr : (galEmb ℚ K Ω).range.Normal := by rw [range_galEmb]; exact hN
  let e := MonoidHom.ofInjective hinj
  let c : G K Ω ≃* G K Ω := (e.trans (MulAut.conjNormal u)).trans e.symm
  have hc : ∀ s, galEmb ℚ K Ω (c s) = u * galEmb ℚ K Ω s * u⁻¹ := fun s =>
    (MonoidHom.apply_ofInjective_symm hinj _).trans (by simp [e, MulAut.conjNormal_apply, MonoidHom.ofInjective_apply])
  have hgP : u • P' = P := by
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hP]
    simp [AlgEquiv.smul_def]
  have hd : ∀ s ∈ Dec (F := K) P', c.toMonoidHom s ∈ Dec (F := K) P := fun s hs => by
    have h1 : galEmb ℚ K Ω s • P' = P' := hs
    show galEmb ℚ K Ω (c s) • P = P
    rw [hc, ← hgP, mul_smul, mul_smul, inv_smul_smul, h1]
  have hcyc : ∀ s, cycBar K Ω l (c s) = cycBar K Ω l s := fun s => by
    show cycBar ℚ Ω l (galEmb ℚ K Ω (c s)) = cycBar ℚ Ω l (galEmb ℚ K Ω s)
    rw [hc, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  have hρc : ∀ s, ρ (c s) = (R u * R (galEmb ℚ K Ω s) * (R u)⁻¹).left := fun s => by
    rw [hρ, hc, map_mul, map_mul, map_inv]
  have h1 : Af.PotCrysAt (ρ.comp c.toMonoidHom) P' := UpperTheory.potentiallyCrystalline_comp_conjugation u c hc ρ P P' hP hp
  have hev : ∀ s : ↥(Dec (F := K) P'), galEmb ℚ K Ω s ∈ T → ((κ i).comp (into c.toMonoidHom _ _ hd)) s =
      ((κ j).comp (into c.toMonoidHom _ _ hd)) s * cycBar K Ω l s := fun s hs => by
    have hs' : galEmb ℚ K Ω (into c.toMonoidHom _ _ hd s : G K Ω) ∈ T := by
      show galEmb ℚ K Ω (c s) ∈ T
      rw [hc]
      exact hT _ hs
    have := hij _ hs'
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, this]
    exact congrArg _ (hcyc s)
  rcases Int.units_eq_one_or (R u).right with hu | hu
  · have ha : ∀ s, ρ (c.toMonoidHom s) = (R u).left * ρ s * (R u).left⁻¹ := fun s => by
      rw [hρ s]
      exact (hρc s).trans (conj_left_pos _ _ hu (hK s))
    refine ⟨h1.of_iso ⟨(R u).left⁻¹, fun s => ?_⟩, _, flag_plus ρ c.toMonoidHom _ _ hd κ hf _ ha, i, j, hev⟩
    rw [MonoidHom.comp_apply, ha]
    group
  · have ha : ∀ s, ρ (c.toMonoidHom s) = (R u).left * theta (ρ s) * (R u).left⁻¹ := fun s => by
      rw [hρ s]
      exact (hρc s).trans (conj_left_neg _ _ hu (hK s))
    let r₂ : G K Ω →* GL (Fin 3) (Qbar l) :=
      { toFun := fun s => trInv (ρ (c s))
        map_one' := by
          apply Units.ext
          simp [trInv_val]
        map_mul' := fun a b => by rw [map_mul, map_mul, trInv_mul] }
    have h2 : Af.PotCrysAt r₂ P' := UpperTheory.potentiallyCrystalline_contragredient (ρ.comp c.toMonoidHom) r₂ P' (fun s => rfl) h1
    have hJ : (Jgl (Qbar l) 3)⁻¹ = Jgl (Qbar l) 3 := inv_eq_of_mul_eq_one_left Jgl_mul_Jgl
    have t : ∀ x : GL (Fin 3) (Qbar l), theta x = thetaAut 3 (Qbar l) x := fun _ => rfl
    refine ⟨h2.of_iso ⟨(theta (R u).left)⁻¹ * Jgl _ 3, fun s => ?_⟩, _, flag_minus ρ c.toMonoidHom _ _ hd κ hf _ ha,
      j.rev, i.rev, fun s hs => ?_⟩
    · have h3 : theta (ρ (c s)) = theta (R u).left * ρ s * (theta (R u).left)⁻¹ := by
        have := congrArg theta (ha s)
        simp only [t, map_mul, map_inv] at this ⊢
        simp only [← t, theta_theta] at this ⊢
        exact this
      have h4 : theta (ρ (c s)) = Jgl _ 3 * r₂ s * Jgl _ 3 := rfl
      rw [_root_.mul_inv_rev, inv_inv, hJ]
      calc ρ s = (theta (R u).left)⁻¹ * (theta (R u).left * ρ s * (theta (R u).left)⁻¹) * theta (R u).left := by group
        _ = _ := by rw [← h3, h4]; simp only [mul_assoc]
    · have := hev s hs
      simp only [MonoidHom.inv_apply, Fin.rev_rev]
      rw [this]
      simp [mul_comm]

end Move

end UpperTheory.V.Z.Keep.K3

section

attribute [local instance 10000] IsDiscreteValuationRing.toIsLocalRing

set_option maxHeartbeats 400000 in
/- English proof (translation)
Introduce `hLP hU Ω _ _ _ l _ c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ C₀ k hok hbig hseed A _ _ r hr hirr K _ _ _ _ _ hker _ _ ρ hρ w hw hU1 Q hQ`. Take `⟨-, hloc, hcont⟩` from `UpperTheory.V.Th.End3.sub_facts c A`. Establish `hl : l ∣ M` using `(dvd_mul_right l N).trans H.dvd`. Establish `hσ : σ * σ = 1` using `Db.cc_sq H.cc`. Establish `hmem : ∀ s : G K Ω, galEmb ℚ K Ω s ∈ η.ker` using `fun s => hker ▸ galEmb_mem ℚ K Ω s`.

Establish `hρ' : ∀ s, ρ s = (UnitaryThreeInertia.push A.val r (galEmb ℚ K Ω s)).left` using `fun s => Units.ext (hρ s)`. Establish `hright : ∀ g, (UnitaryThreeInertia.push A.val r g).right = η g` using `hr.red.mult`. Establish `hK : ∀ s, (UnitaryThreeInertia.push A.val r (galEmb ℚ K Ω s)).right = 1` using `fun s => (hright _).trans (hmem s)`. Establish `hLη : galOf ℚ L Ω ≤ η.ker` using `Db.galL_le k`. Establish `hρc : Continuous ρ`.

Use `K3.cont_units ρ (continuous_matrix fun a b => ?_)` and prove the remaining obligations. Establish `h1 : Alg.AdicCont (maximalIdeal A) fun g : G ℚ Ω => (r g).mat a b` using `fun n => (hr.cont n).comp fun m => m a b`. Use `((hcont (G ℚ Ω) _ h1).comp (galEmbTop ℚ K Ω).1.continuous).congr fun s => ?_` and prove the remaining obligations. Rewrite using `[hρ]`. Both sides reduce to the same expression.

Establish `hv0 : ((l : ℕ) : 𝓞 K) ∈ (w.under (𝓞 K)).asIdeal`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 K) (𝓞 L) _ ∈ w.asIdeal`. Rewrite using `[map_natCast]`. Conclude with `hw`. Establish `hQK : IsPlaceOver Q (w.under (𝓞 K))` using `fun x => by`.

Rewrite using `[IsScalarTower.algebraMap_apply K L Ω]`. Conclude with `hQ (algebraMap (𝓞 K) (𝓞 L) x)`. Take `⟨P₀, hP₀, κ₀, hκ₀⟩` from `Z.Keep.ordFlag3 Ω l c N e ψ η σ g₁ B M H L Φ C₀ k hok A r hr K hker ρ hρ _ hv0`. Take `⟨κ₁, hf₁, hu₁⟩` from `hU1 P₀ hP₀`. Establish `hf₀ : Af.IsFlagOn ρ (Dec (F` using `K) P₀) κ₀ := by`.

Take `⟨_, _, h, _⟩` from `hκ₀`. Conclude with `h`. Establish `hu₀ : ∀ i j, κ₀ i ≠ κ₀ j * (cycBar K Ω l).comp (Dec (F` using `K) P₀).subtype := fun i j hij => by`. Take `⟨a, ha⟩` from `K3.flag_same ρ _ κ₀ κ₁ hf₀ hf₁ i`. Take `⟨b, hb⟩` from `K3.flag_same ρ _ κ₀ κ₁ hf₀ hf₁ j`.

Rewrite `hij` using `[ha, hb]`. Conclude with `hu₁ a b hij`. Establish `hP₀l : P₀.valuation (l : Ω) < 1`. Use `hP₀ ((l : ℕ) : 𝓞 K)` as an intermediate fact. Simplify using `only [map_natCast] at this`.

Conclude with `this.2 hv0`. Establish `hpot₀ : Af.PotCrysAt ρ P₀` using `Z.Keep.potOfUnl hLP K Ω l 3 N ![(e : ℤ), 0, -(e : ℤ)] ρ (Nat.one_le_iff_ne_zero.2 (NeZero.ne N)) (K3.anti3 e H.e_pos) hρc P₀ hP₀l κ₀ hκ₀ hu₀`. Take `⟨g₀, hg₀⟩` from `exists_smul_eq_of_isPlaceOver (F := K) hQK hP₀`. Establish `hpotQ : Af.PotCrysAt ρ Q` using `Br.potMove K Ω l 3 ρ P₀ Q g₀ (fun x => by`. Rewrite using `[← hg₀]`.

Conclude with `ValuationSubring.smul_mem_pointwise_smul_iff.symm) hpot₀`. Take `⟨κ, hf, -⟩` from `hU1 Q hQK`. Set `dm : ↥(Dec (F` to `L) Q) →* ↥(Dec (F := K) Q) := ((galEmb K L Ω).comp (Dec (F := L) Q).subtype).codRestrict _ fun s => s.2`. Use `⟨fun i => (κ i).comp dm, ?_, fun i j hij => ?_⟩` and prove the remaining obligations. Take `⟨P, hP⟩` from `hf`.

Conclude with `⟨P, fun s => hP (dm s)⟩`. Establish `hQl : Q.valuation (l : Ω) < 1`. Use `hQ ((l : ℕ) : 𝓞 L)` as an intermediate fact. Simplify using `only [map_natCast] at this`. Conclude with `this.2 hw`.

Take `⟨v, u, hu, hQv⟩ : ∃ v, ∃ u ∈ Pr.upl Ω L, Q = u • k.pl v` from `(k.pl_all Q hQl).exists`. Establish `hAv : ∀ x, x ∈ k.pl v ↔ u x ∈ Q` using `fun x => by`. Rewrite using `[hQv]`. Conclude with `ValuationSubring.smul_mem_pointwise_smul_iff.symm`. Establish `hTu : ∀ s ∈ galOf ℚ L Ω, u * s * u⁻¹ ∈ galOf ℚ L Ω` using `fun s hs => by`.

Rewrite `hs`, the goal using `[k.gal]`. Take `⟨h1, h2⟩` from `Subgroup.mem_inf.1 hs`. Conclude with `Subgroup.mem_inf.2 ⟨(Pr.upl Ω L).mul_mem ((Pr.upl Ω L).mul_mem hu h1) ((Pr.upl Ω L).inv_mem hu), η.normal_ker.conj_mem _ h2 u⟩`. Establish `hlink : ∀ s : ↥(Dec (F` using `K) Q), galEmb ℚ K Ω s ∈ galOf ℚ L Ω → κ i s = κ j s * cycBar K Ω l s := fun s hs => by`. Rewrite `hs` using `[← range_galEmb]`.

Take `⟨t, ht⟩` from `hs`. Establish `hst : galEmb K L Ω t = s` using `(galEmbTop ℚ K Ω).1.injective ht`. Establish `htd : t ∈ Dec (F` using `L) Q := by`. Establish `h1 : galEmb K L Ω t ∈ Dec (F` using `K) Q := by`. Rewrite using `[hst]`.

Conclude with `s.2`. Conclude with `h1`. Establish `e1 : dm ⟨t, htd⟩ = s` using `Subtype.ext hst`. Establish `e2 : cycBar L Ω l t = cycBar K Ω l s` using `by show cycBar ℚ Ω l (galEmb ℚ L Ω t) = cycBar ℚ Ω l (galEmb ℚ K Ω s)`. Rewrite using `[ht]`.

Establish `e3` using `DFunLike.congr_fun hij ⟨t, htd⟩`. Express the relevant statement in the definitionally equal form `κ i (dm ⟨t, htd⟩) = κ j (dm ⟨t, htd⟩) * cycBar L Ω l t at e3`. Rewrite `e3` using `[e1, e2]`. Conclude with `e3`. Take `⟨pot, κ', ⟨Q', fl⟩, i', j', hl'⟩` from `K3.move_link ρ (UnitaryThreeInertia.push A.val r) hρ' hK (by rw [← hker]; exact η.normal_ker) (galOf ℚ L Ω) u hTu Q (k.pl v) hAv κ hf hpotQ i j hlink`.

Use `haveI hpir : IsPrincipalIdealRing A := IsDiscreteValuationRing.toIsPrincipalIdealRing`. Use `haveI hnoe : IsNoetherianRing A := PrincipalIdealRing.isNoetherianRing`. Take `⟨ν, n1, n2, n3⟩` from `Pr.exists_nrep3 k hok hl hσ r hr`. Establish `key` using `hU Ω l c N e ψ η σ g₁ B M H L Φ C₀ k hok hbig hseed`. Establish `n4 : ∀ s, (ρ.comp (galEmb K L Ω) s).val = (ν.r (k.p0 s)).map A.val` using `fun s => by`.

Rewrite using `[n2, MonoidHom.comp_apply, hρ']`. Both sides reduce to the same expression. Establish `n5 : ∀ v i, ∀ g ∈ Φ.Iv v, (ν.ψ v i g).val = algebraMap c.O A (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (k.j v g) ^ Fr.w 3 i).val` using `fun v i g hg => by`. Rewrite using `[n3 v i g hg, Fr.w, if_pos rfl]`. Both sides reduce to the same expression.

Establish `irr : ∀ U : Subgroup (G L Ω), IsOpen (U : Set (G L Ω)) → Af.IsIrr ((ρ.comp (galEmb K L Ω)).comp U.subtype)`. Introduce `U hUo`. Establish `hoe : Topology.IsOpenEmbedding (galEmb ℚ L Ω)` using `⟨(galEmbTop ℚ L Ω).1, by`. Rewrite using `[← MonoidHom.coe_range, range_galEmb]`. Conclude with `(galEmbTop ℚ L Ω).2.1⟩`.

Use `Db.irr_of_matIrr (by norm_num) (U.map (galEmb ℚ L Ω)) _ (hirr (U.map (galEmb ℚ L Ω)) (hoe.isOpenMap _ hUo) (Subgroup.map_le_iff_le_comap.2 fun s _ => hLη (galEmb_mem ℚ L Ω s))) ((galEmb ℚ L Ω).comp U.subtype) (fun g hg => ?_) _ fun s => ?_` and prove the remaining obligations. Take `⟨s, hs, e⟩` from `hg`. Conclude with `⟨⟨s, hs⟩, e⟩`. Use `show (ρ (galEmb K L Ω s.1)).val = _`. Rewrite using `[hρ']`.

Both sides reduce to the same expression. Establish `hlv : (k.pl v).valuation (l : Ω) < 1` using `K3.below_move u hAv l hQl`. Establish `hMv : (k.pl v).valuation (M : Ω) < 1`. Take `⟨t, rfl⟩` from `hl`. Rewrite using `[Nat.cast_mul, map_mul]`.

Conclude with `mul_lt_one_of_lt_of_le hlv (((k.pl v).valuation_le_one_iff _).2 (natCast_mem _ t))`. Establish `hdec : ∀ g, (k.j v g).1 ∈ Dec (F` using `ℚ) (k.pl v) := fun g => (k.j_range v _).1 ⟨g, rfl⟩`. Establish `hsplit : ∀ g, (k.j v g).1 ∈ (galEmb ℚ L Ω).range` using `fun g => by`. Rewrite using `[range_galEmb, k.gal]`. Conclude with `⟨(k.j v g).2, k.split _ hMv ⟨hdec g, (k.j v g).2⟩⟩`.

Use `choose t ht using hsplit`. Establish `hloc0 : ∀ g, Φ.loc0 v g = k.p0 (t g)` using `fun g => Subtype.ext ((k.j_loc v g).trans (congrArg k.p (Subtype.ext (ht g).symm)))`. Establish `hdm : ∀ g, galEmb K L Ω (t g) ∈ Dec (F` using `K) (k.pl v) := fun g => by`. Use `hdec g` as an intermediate fact. Rewrite `this` using `[← ht]`.

Conclude with `this`. Set `d : Φ.Gv v → ↥(Dec (F` to `K) (k.pl v)) := fun g => ⟨galEmb K L Ω (t g), hdm g⟩`. Set `f : A →+* Qbar l` to `(A.val : A →+* PadicAlgCl l)`. Establish `hT : ∀ g, f.mapMatrix (ν.r (Φ.loc0 v g)) = (ρ (d g).1).val` using `fun g => by`. Rewrite using `[hloc0]`.

Conclude with `(n4 (t g)).symm`. Establish `mt : ∀ b, ∃ a, ∀ g, (κ' b (d g) : Qbar l) = f (ν.ψ v a g : A)` using `fun b => K3.graded_match (fun g => f.mapMatrix (ν.r (Φ.loc0 v g))) (fun a g => f (ν.ψ v a g : A)) (fun a g => (κ' a (d g) : Qbar l)) Q' (fun g => by`. Rewrite using `[hT]`. Conclude with `fun x y hxy => (fl (d g)).1 x y hxy)`. Use the proof step `(fun g x => by`.

Rewrite using `[hT]`. Conclude with `(fl (d g)).2 x)`. Use the proof step `(fun g => by`. Rewrite using `[Fr.ordProd_map f (fun s => ν.r (Φ.loc0 v s)) (fun a s => (ν.ψ v a s : A)) g, ν.ord v g, map_zero]) b`. Take `⟨a, ha⟩` from `mt i'`.

Take `⟨b, hb⟩` from `mt j'`. Take `⟨g, hg⟩` from `key A ν n1 n5 _ n4 irr v (Br.potRes K L Ω l 3 ρ _ pot) a b`. Apply `hg` to reduce the goal to its premises. Establish `e1` using `congrArg Units.val (hl' (d g) (galEmb_mem ℚ L Ω (t g)))`. Establish `e2 : cycBar K Ω l (d g).1 = cycBar ℚ Ω l (k.j v g).1`.

Rewrite using `[← ht]`. Both sides reduce to the same expression. Simplify using `only [Units.val_mul] at e1`. Rewrite `e1` using `[ha, hb, e2]`. Conclude with `e1`.
-/
private theorem UpperTheory.V.Z.Keep.K3.main :
    Loc.LocalPublishedTheorems → LinkedUnl → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), Pr.LinkHyp c N e η σ B M → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O)) (C₀ : ℕ) (k : Pr.GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ), Φ.Ok C₀ → Φ.Big C₀ → Pr.SeedClause c η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ L → ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] (r : G ℚ Ω →* GG 3 A), Pr.OrdPt l η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B r → (∀ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) → U ≤ η.ker → MatIrr U (mats (UnitaryThreeInertia.push A.val r))) → ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω], η.ker = galOf ℚ K Ω → ∀ [Algebra K L] [IsScalarTower K L Ω] (ρ : G K Ω →* GL (Fin 3) (Qbar l)), (∀ s, (ρ s).val = (UnitaryThreeInertia.push A.val r (galEmb ℚ K Ω s)).mat) → Z.Win.Keeps ρ L := by
  intro hLP hU Ω _ _ _ l _ c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ C₀ k hok hbig hseed A _ _ r hr hirr K _ _ _ _ _ hker _ _ ρ hρ
    w hw hU1 Q hQ
  obtain ⟨-, hloc, hcont⟩ := UpperTheory.V.Th.End3.sub_facts c A
  have hl : l ∣ M := (dvd_mul_right l N).trans H.dvd
  have hσ : σ * σ = 1 := Db.cc_sq H.cc
  have hmem : ∀ s : G K Ω, galEmb ℚ K Ω s ∈ η.ker := fun s => hker ▸ galEmb_mem ℚ K Ω s
  have hρ' : ∀ s, ρ s = (UnitaryThreeInertia.push A.val r (galEmb ℚ K Ω s)).left := fun s => Units.ext (hρ s)
  have hright : ∀ g, (UnitaryThreeInertia.push A.val r g).right = η g := hr.red.mult
  have hK : ∀ s, (UnitaryThreeInertia.push A.val r (galEmb ℚ K Ω s)).right = 1 := fun s => (hright _).trans (hmem s)
  have hLη : galOf ℚ L Ω ≤ η.ker := Db.galL_le k
  have hρc : Continuous ρ := by
    refine K3.cont_units ρ (continuous_matrix fun a b => ?_)
    have h1 : Alg.AdicCont (maximalIdeal A) fun g : G ℚ Ω => (r g).mat a b := fun n =>
      (hr.cont n).comp fun m => m a b
    refine ((hcont (G ℚ Ω) _ h1).comp (galEmbTop ℚ K Ω).1.continuous).congr fun s => ?_
    rw [hρ]
    rfl
  have hv0 : ((l : ℕ) : 𝓞 K) ∈ (w.under (𝓞 K)).asIdeal := by
    change algebraMap (𝓞 K) (𝓞 L) _ ∈ w.asIdeal
    rw [map_natCast]
    exact hw
  have hQK : IsPlaceOver Q (w.under (𝓞 K)) := fun x => by
    rw [IsScalarTower.algebraMap_apply K L Ω]
    exact hQ (algebraMap (𝓞 K) (𝓞 L) x)

  obtain ⟨P₀, hP₀, κ₀, hκ₀⟩ := Z.Keep.ordFlag3 Ω l c N e ψ η σ g₁ B M H L Φ C₀ k hok A r hr K hker ρ hρ _ hv0
  obtain ⟨κ₁, hf₁, hu₁⟩ := hU1 P₀ hP₀
  have hf₀ : Af.IsFlagOn ρ (Dec (F := K) P₀) κ₀ := by
    obtain ⟨_, _, h, _⟩ := hκ₀
    exact h
  have hu₀ : ∀ i j, κ₀ i ≠ κ₀ j * (cycBar K Ω l).comp (Dec (F := K) P₀).subtype := fun i j hij => by
    obtain ⟨a, ha⟩ := K3.flag_same ρ _ κ₀ κ₁ hf₀ hf₁ i
    obtain ⟨b, hb⟩ := K3.flag_same ρ _ κ₀ κ₁ hf₀ hf₁ j
    rw [ha, hb] at hij
    exact hu₁ a b hij
  have hP₀l : P₀.valuation (l : Ω) < 1 := by
    have := hP₀ ((l : ℕ) : 𝓞 K)
    simp only [map_natCast] at this
    exact this.2 hv0
  have hpot₀ : Af.PotCrysAt ρ P₀ := Z.Keep.potOfUnl hLP K Ω l 3 N ![(e : ℤ), 0, -(e : ℤ)] ρ
    (Nat.one_le_iff_ne_zero.2 (NeZero.ne N)) (K3.anti3 e H.e_pos) hρc P₀ hP₀l κ₀ hκ₀ hu₀
  obtain ⟨g₀, hg₀⟩ := exists_smul_eq_of_isPlaceOver (F := K) hQK hP₀
  have hpotQ : Af.PotCrysAt ρ Q := Br.potMove K Ω l 3 ρ P₀ Q g₀ (fun x => by
    rw [← hg₀]
    exact ValuationSubring.smul_mem_pointwise_smul_iff.symm) hpot₀

  obtain ⟨κ, hf, -⟩ := hU1 Q hQK
  let dm : ↥(Dec (F := L) Q) →* ↥(Dec (F := K) Q) :=
    ((galEmb K L Ω).comp (Dec (F := L) Q).subtype).codRestrict _ fun s => s.2
  refine ⟨fun i => (κ i).comp dm, ?_, fun i j hij => ?_⟩
  · obtain ⟨P, hP⟩ := hf
    exact ⟨P, fun s => hP (dm s)⟩

  have hQl : Q.valuation (l : Ω) < 1 := by
    have := hQ ((l : ℕ) : 𝓞 L)
    simp only [map_natCast] at this
    exact this.2 hw
  obtain ⟨v, u, hu, hQv⟩ : ∃ v, ∃ u ∈ Pr.upl Ω L, Q = u • k.pl v := (k.pl_all Q hQl).exists
  have hAv : ∀ x, x ∈ k.pl v ↔ u x ∈ Q := fun x => by
    rw [hQv]
    exact ValuationSubring.smul_mem_pointwise_smul_iff.symm
  have hTu : ∀ s ∈ galOf ℚ L Ω, u * s * u⁻¹ ∈ galOf ℚ L Ω := fun s hs => by
    rw [k.gal] at hs ⊢
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hs
    exact Subgroup.mem_inf.2 ⟨(Pr.upl Ω L).mul_mem ((Pr.upl Ω L).mul_mem hu h1) ((Pr.upl Ω L).inv_mem hu),
      η.normal_ker.conj_mem _ h2 u⟩
  have hlink : ∀ s : ↥(Dec (F := K) Q), galEmb ℚ K Ω s ∈ galOf ℚ L Ω → κ i s = κ j s * cycBar K Ω l s := fun s hs => by
    rw [← range_galEmb] at hs
    obtain ⟨t, ht⟩ := hs
    have hst : galEmb K L Ω t = s := (galEmbTop ℚ K Ω).1.injective ht
    have htd : t ∈ Dec (F := L) Q := by
      have h1 : galEmb K L Ω t ∈ Dec (F := K) Q := by
        rw [hst]
        exact s.2
      exact h1
    have e1 : dm ⟨t, htd⟩ = s := Subtype.ext hst
    have e2 : cycBar L Ω l t = cycBar K Ω l s := by
      show cycBar ℚ Ω l (galEmb ℚ L Ω t) = cycBar ℚ Ω l (galEmb ℚ K Ω s)
      rw [ht]
    have e3 := DFunLike.congr_fun hij ⟨t, htd⟩
    change κ i (dm ⟨t, htd⟩) = κ j (dm ⟨t, htd⟩) * cycBar L Ω l t at e3
    rw [e1, e2] at e3
    exact e3
  obtain ⟨pot, κ', ⟨Q', fl⟩, i', j', hl'⟩ := K3.move_link ρ (UnitaryThreeInertia.push A.val r) hρ' hK
    (by rw [← hker]; exact η.normal_ker) (galOf ℚ L Ω) u hTu Q (k.pl v) hAv κ hf hpotQ i j hlink
  haveI hpir : IsPrincipalIdealRing A := IsDiscreteValuationRing.toIsPrincipalIdealRing
  haveI hnoe : IsNoetherianRing A := PrincipalIdealRing.isNoetherianRing
  obtain ⟨ν, n1, n2, n3⟩ := Pr.exists_nrep3 k hok hl hσ r hr
  have key := hU Ω l c N e ψ η σ g₁ B M H L Φ C₀ k hok hbig hseed
  have n4 : ∀ s, (ρ.comp (galEmb K L Ω) s).val = (ν.r (k.p0 s)).map A.val := fun s => by
    rw [n2, MonoidHom.comp_apply, hρ']
    rfl
  have n5 : ∀ v i, ∀ g ∈ Φ.Iv v, (ν.ψ v i g).val =
      algebraMap c.O A (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (k.j v g) ^ Fr.w 3 i).val := fun v i g hg => by
    rw [n3 v i g hg, Fr.w, if_pos rfl]
    rfl
  have irr : ∀ U : Subgroup (G L Ω), IsOpen (U : Set (G L Ω)) → Af.IsIrr ((ρ.comp (galEmb K L Ω)).comp U.subtype) := by
    intro U hUo
    have hoe : Topology.IsOpenEmbedding (galEmb ℚ L Ω) :=
      ⟨(galEmbTop ℚ L Ω).1, by
        rw [← MonoidHom.coe_range, range_galEmb]
        exact (galEmbTop ℚ L Ω).2.1⟩
    refine Db.irr_of_matIrr (by norm_num) (U.map (galEmb ℚ L Ω)) _
      (hirr (U.map (galEmb ℚ L Ω)) (hoe.isOpenMap _ hUo) (Subgroup.map_le_iff_le_comap.2 fun s _ => hLη (galEmb_mem ℚ L Ω s)))
      ((galEmb ℚ L Ω).comp U.subtype) (fun g hg => ?_) _ fun s => ?_
    · obtain ⟨s, hs, e⟩ := hg
      exact ⟨⟨s, hs⟩, e⟩
    · show (ρ (galEmb K L Ω s.1)).val = _
      rw [hρ']
      rfl
  have hlv : (k.pl v).valuation (l : Ω) < 1 := K3.below_move u hAv l hQl
  have hMv : (k.pl v).valuation (M : Ω) < 1 := by
    obtain ⟨t, rfl⟩ := hl
    rw [Nat.cast_mul, map_mul]
    exact mul_lt_one_of_lt_of_le hlv (((k.pl v).valuation_le_one_iff _).2 (natCast_mem _ t))
  have hdec : ∀ g, (k.j v g).1 ∈ Dec (F := ℚ) (k.pl v) := fun g => (k.j_range v _).1 ⟨g, rfl⟩
  have hsplit : ∀ g, (k.j v g).1 ∈ (galEmb ℚ L Ω).range := fun g => by
    rw [range_galEmb, k.gal]
    exact ⟨(k.j v g).2, k.split _ hMv ⟨hdec g, (k.j v g).2⟩⟩
  choose t ht using hsplit
  have hloc0 : ∀ g, Φ.loc0 v g = k.p0 (t g) := fun g =>
    Subtype.ext ((k.j_loc v g).trans (congrArg k.p (Subtype.ext (ht g).symm)))
  have hdm : ∀ g, galEmb K L Ω (t g) ∈ Dec (F := K) (k.pl v) := fun g => by
    have := hdec g
    rw [← ht] at this
    exact this
  let d : Φ.Gv v → ↥(Dec (F := K) (k.pl v)) := fun g => ⟨galEmb K L Ω (t g), hdm g⟩
  let f : A →+* Qbar l := (A.val : A →+* PadicAlgCl l)
  have hT : ∀ g, f.mapMatrix (ν.r (Φ.loc0 v g)) = (ρ (d g).1).val := fun g => by
    rw [hloc0]
    exact (n4 (t g)).symm
  have mt : ∀ b, ∃ a, ∀ g, (κ' b (d g) : Qbar l) = f (ν.ψ v a g : A) := fun b =>
    K3.graded_match (fun g => f.mapMatrix (ν.r (Φ.loc0 v g))) (fun a g => f (ν.ψ v a g : A)) (fun a g => (κ' a (d g) : Qbar l)) Q'
      (fun g => by
        rw [hT]
        exact fun x y hxy => (fl (d g)).1 x y hxy)
      (fun g x => by
        rw [hT]
        exact (fl (d g)).2 x)
      (fun g => by
        rw [Fr.ordProd_map f (fun s => ν.r (Φ.loc0 v s)) (fun a s => (ν.ψ v a s : A)) g, ν.ord v g, map_zero]) b
  obtain ⟨a, ha⟩ := mt i'
  obtain ⟨b, hb⟩ := mt j'
  obtain ⟨g, hg⟩ := key A ν n1 n5 _ n4 irr v (Br.potRes K L Ω l 3 ρ _ pot) a b
  apply hg
  have e1 := congrArg Units.val (hl' (d g) (galEmb_mem ℚ L Ω (t g)))
  have e2 : cycBar K Ω l (d g).1 = cycBar ℚ Ω l (k.j v g).1 := by
    rw [← ht]
    rfl
  simp only [Units.val_mul] at e1
  rw [ha, hb, e2] at e1
  exact e1

end

import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.LogarithmicNormBounds.LinkedUnlEOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.IsIrrOfMatIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.MatrixIrreducibility.IrrOfMatIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.LevelRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.DotProductSymmetry.PotentiallyCrystallineContragredient
import Development.AutomorphicArithmetic.AutomorphicVarieties.DotProductSymmetry.PotentiallyCrystallineCompConjugation

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th UpperTheory.V.Z.J
open scoped Pointwise

namespace UpperTheory.V.Z.J.UnitaryRankTwoFlags

open UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Th.End3

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
attribute [local instance 10000] IsDiscreteValuationRing.toIsLocalRing

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)` and prove the remaining obligations. Break down `lt_or_gt_of_ne hj with h | h` into its components or cases. Rewrite using `[hA (show id j < id i from h), zero_mul]`. Rewrite using `[hB (show id i < id j from h), mul_zero]`.
-/
private theorem block_triangular_diag_mul {k : Type} [CommRing k] {n : ℕ} (A B : Matrix (Fin n) (Fin n) k)
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

Simplify using `only [U]`. Combine the equalities or inequalities in the displayed calculation. Establish `h4` using `congrFun (congrFun h0 b) b`. Rewrite `h4` using `[block_triangular_diag_mul _ _ (hUt 0) ((hUt 1).mul (hUt 2)), block_triangular_diag_mul _ _ (hUt 1) (hUt 2)]`. Conclude with `mul_ne_zero (hUd 0) (mul_ne_zero (hUd 1) (hUd 2)) h4`.
-/
private theorem flag_match {H k : Type} [Field k] (T : H → Matrix (Fin 3) (Fin 3) k) (ψ : Fin 3 → H → k)
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
  rw [block_triangular_diag_mul _ _ (hUt 0) ((hUt 1).mul (hUt 2)), block_triangular_diag_mul _ _ (hUt 1) (hUt 2)] at h4
  exact mul_ne_zero (hUd 0) (mul_ne_zero (hUd 1) (hUd 2)) h4

/- English proof (translation)
Establish `hc : ((b⁻¹ : GL (Fin 3) k)).val.BlockTriangular id` using `by haveI : Invertible b.val := ⟨(b⁻¹ : GL (Fin 3) k).val, Units.inv_mul b, Units.mul_inv b⟩`. Rewrite using `[Matrix.coe_units_inv]`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hb`. Establish `hd : ∀ i, ((b⁻¹ : GL (Fin 3) k)).val i i = (b.val i i)⁻¹` using `fun i => by`. Establish `h1` using `congrFun (congrFun (Units.mul_inv b) i) i`.

Rewrite `h1` using `[block_triangular_diag_mul _ _ hb hc, Matrix.one_apply_eq]`. Conclude with `eq_inv_of_mul_eq_one_right h1`. Establish `he : ∀ i j, (theta b).val i j = ((b⁻¹ : GL (Fin 3) k)).val j.rev i.rev` using `fun i j => by`. Rewrite using `[theta_val, Matrix.mul_apply, Finset.sum_eq_single j.rev]`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i.rev]`.

Simplify using `[Jmat]`. Introduce `x _ hx`. Simplify using `[Jmat, hx]`. Simplify using the standard rewrite rules. Introduce `x _ hx`.

Establish `: ¬ j = x.rev` using `fun h => hx (by rw [h, Fin.rev_rev])`. Simplify using `[Jmat, this]`. Simplify using the standard rewrite rules. Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[he]`.

Conclude with `hc (show id i.rev < id j.rev from Fin.rev_lt_rev.2 hij)`. Rewrite using `[he, hd]`.
-/
private theorem theta_tri {k : Type} [Field k] (b : GL (Fin 3) k) (hb : b.val.BlockTriangular id) :
    (theta b).val.BlockTriangular id ∧ ∀ i, (theta b).val i i = (b.val i.rev i.rev)⁻¹ := by
  have hc : ((b⁻¹ : GL (Fin 3) k)).val.BlockTriangular id := by
    haveI : Invertible b.val := ⟨(b⁻¹ : GL (Fin 3) k).val, Units.inv_mul b, Units.mul_inv b⟩
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  have hd : ∀ i, ((b⁻¹ : GL (Fin 3) k)).val i i = (b.val i i)⁻¹ := fun i => by
    have h1 := congrFun (congrFun (Units.mul_inv b) i) i
    rw [block_triangular_diag_mul _ _ hb hc, Matrix.one_apply_eq] at h1
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
private theorem gg_conj_pos {k : Type} [CommRing k] (x y : GG 3 k) (h1 : x.right = 1) (h2 : y.right = 1) :
    (x * y * x⁻¹).left = x.left * y.left * x.left⁻¹ := by
  simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left, h1, h2, sgnAct_one]

/- English proof (translation)
Simplify using `[SemidirectProduct.mul_left, SemidirectProduct.inv_left, h1, h2, sgnAct_neg_one, sgnAct_one, theta_theta]`.
-/
private theorem gg_conj_neg {k : Type} [CommRing k] (x y : GG 3 k) (h1 : x.right = -1) (h2 : y.right = 1) :
    (x * y * x⁻¹).left = x.left * theta y.left * x.left⁻¹ := by
  simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left, h1, h2, sgnAct_neg_one, sgnAct_one, theta_theta]

section Mv

variable {Γ k : Type} [Group Γ] [Field k]

private def dRes (c : Γ →* Γ) (H H' : Subgroup Γ) (hc : ∀ s ∈ H', c s ∈ H) : ↥H' →* ↥H :=
  (c.comp H'.subtype).codRestrict H fun s => hc s s.2

/- English proof (translation)
Take `⟨P, hP⟩` from `hf`. Use `⟨P * a, fun s => ?_⟩` and prove the remaining obligations. Establish `e : (P * a) * ρ s * (P * a)⁻¹ = P * ρ (dRes c H H' hc s : Γ) * P⁻¹`. Rewrite using `[show ((dRes c H H' hc s : ↥H) : Γ) = c s from rfl, ha]`. Use `group`.

Rewrite using `[e]`. Conclude with `hP (dRes c H H' hc s)`.
-/
private theorem flag_pos (ρ : Γ →* GL (Fin 3) k) (c : Γ →* Γ) (H H' : Subgroup Γ) (hc : ∀ s ∈ H', c s ∈ H)
    (κ : Fin 3 → ↥H →* kˣ) (hf : Af.IsFlagOn ρ H κ) (a : GL (Fin 3) k) (ha : ∀ s, ρ (c s) = a * ρ s * a⁻¹) :
    Af.IsFlagOn ρ H' fun i => (κ i).comp (dRes c H H' hc) := by
  obtain ⟨P, hP⟩ := hf
  refine ⟨P * a, fun s => ?_⟩
  have e : (P * a) * ρ s * (P * a)⁻¹ = P * ρ (dRes c H H' hc s : Γ) * P⁻¹ := by
    rw [show ((dRes c H H' hc s : ↥H) : Γ) = c s from rfl, ha]
    group
  rw [e]
  exact hP (dRes c H H' hc s)

/- English proof (translation)
Take `⟨P, hP⟩` from `hf`. Use `⟨theta (P * a), fun s => ?_⟩` and prove the remaining obligations. Establish `t : ∀ x : GL (Fin 3) k, theta x = thetaAut 3 k x` using `fun _ => rfl`. Establish `e : theta (P * a) * ρ s * (theta (P * a))⁻¹ = theta (P * ρ (dRes c H H' hc s : Γ) * P⁻¹)`. Rewrite using `[show ((dRes c H H' hc s : ↥H) : Γ) = c s from rfl, ha]`.

Simplify using `only [t, map_mul, map_inv]`. Simplify using `only [← t, theta_theta]`. Use `group`. Take `⟨h1, h2⟩` from `hP (dRes c H H' hc s)`. Take `⟨h3, h4⟩` from `theta_tri _ (show ((P * ρ (dRes c H H' hc s : Γ) * P⁻¹ : GL (Fin 3) k)).val.BlockTriangular id from fun i j hij => h1 i j hij)`.

Rewrite using `[e]`. Use `⟨fun i j hij => h3 hij, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[h4, h2]`. Simplify using the standard rewrite rules.
-/
private theorem flag_neg (ρ : Γ →* GL (Fin 3) k) (c : Γ →* Γ) (H H' : Subgroup Γ) (hc : ∀ s ∈ H', c s ∈ H)
    (κ : Fin 3 → ↥H →* kˣ) (hf : Af.IsFlagOn ρ H κ) (a : GL (Fin 3) k) (ha : ∀ s, ρ (c s) = a * theta (ρ s) * a⁻¹) :
    Af.IsFlagOn ρ H' fun i => ((κ i.rev).comp (dRes c H H' hc))⁻¹ := by
  obtain ⟨P, hP⟩ := hf
  refine ⟨theta (P * a), fun s => ?_⟩
  have t : ∀ x : GL (Fin 3) k, theta x = thetaAut 3 k x := fun _ => rfl
  have e : theta (P * a) * ρ s * (theta (P * a))⁻¹ = theta (P * ρ (dRes c H H' hc s : Γ) * P⁻¹) := by
    rw [show ((dRes c H H' hc s : ↥H) : Γ) = c s from rfl, ha]
    simp only [t, map_mul, map_inv]
    simp only [← t, theta_theta]
    group
  obtain ⟨h1, h2⟩ := hP (dRes c H H' hc s)
  obtain ⟨h3, h4⟩ := theta_tri _ (show ((P * ρ (dRes c H H' hc s : Γ) * P⁻¹ : GL (Fin 3) k)).val.BlockTriangular id from
    fun i j hij => h1 i j hij)
  rw [e]
  refine ⟨fun i j hij => h3 hij, fun i => ?_⟩
  rw [h4, h2]
  simp

/- English proof (translation)
Rewrite `h`, the goal using `[valuation_lt_one_iff']`. Establish `e1 : u (n : Ω) = n` using `map_natCast u n`. Establish `e2 : u ((n : Ω)⁻¹) = (n : Ω)⁻¹` using `by rw [map_inv₀, e1]`. Rewrite using `[hA, hA, e1, e2]` and apply the resulting hypothesis.
-/
private theorem val_move {Ω : Type} [Field Ω] [CharZero Ω] {A A' : ValuationSubring Ω} (u : G ℚ Ω) (hA : ∀ x, x ∈ A' ↔ u x ∈ A) (n : ℕ)
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

Establish `hρc : ∀ s, ρ (c s) = (R u * R (galEmb ℚ K Ω s) * (R u)⁻¹).left` using `fun s => by`. Rewrite using `[hρ, hc, map_mul, map_mul, map_inv]`. Establish `h1 : Af.PotCrysAt (ρ.comp c.toMonoidHom) P'` using `UpperTheory.potentiallyCrystalline_comp_conjugation u c hc ρ P P' hP hp`. Establish `hev : ∀ s : ↥(Dec (F` using `K) P'), ((κ i).comp (dRes c.toMonoidHom _ _ hd)) s = ((κ j).comp (dRes c.toMonoidHom _ _ hd)) s * (cycBar K Ω l).comp (Dec (F := K) P').subtype s := fun s => by`. Use `DFunLike.congr_fun hij (dRes c.toMonoidHom _ _ hd s)` as an intermediate fact.

Rewrite using `[MonoidHom.comp_apply, MonoidHom.comp_apply, this, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply]`. Conclude with `congrArg _ (hcyc s)`. Break down `Int.units_eq_one_or (R u).right with hu | hu` into its components or cases. Establish `ha : ∀ s, ρ (c.toMonoidHom s) = (R u).left * ρ s * (R u).left⁻¹` using `fun s => by`. Rewrite using `[hρ s]`.

Conclude with `(hρc s).trans (gg_conj_pos _ _ hu (hK s))`. Use `⟨h1.of_iso ⟨(R u).left⁻¹, fun s => ?_⟩, _, flag_pos ρ c.toMonoidHom _ _ hd κ hf _ ha, i, j, MonoidHom.ext hev⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.comp_apply, ha]`. Use `group`. Establish `ha : ∀ s, ρ (c.toMonoidHom s) = (R u).left * theta (ρ s) * (R u).left⁻¹` using `fun s => by`.

Rewrite using `[hρ s]`. Conclude with `(hρc s).trans (gg_conj_neg _ _ hu (hK s))`. Set `r₂ : G K Ω →* GL (Fin 3) (Qbar l)` to `{ toFun := fun s => trInv (ρ (c s)) map_one' := by`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `[trInv_val]`.

Use the proof step `map_mul' := fun a b => by rw [map_mul, map_mul, trInv_mul] }`. Establish `h2 : Af.PotCrysAt r₂ P'` using `UpperTheory.potentiallyCrystalline_contragredient (ρ.comp c.toMonoidHom) r₂ P' (fun s => rfl) h1`. Establish `hJ : (Jgl (Qbar l) 3)⁻¹ = Jgl (Qbar l) 3` using `inv_eq_of_mul_eq_one_left Jgl_mul_Jgl`. Establish `t : ∀ x : GL (Fin 3) (Qbar l), theta x = thetaAut 3 (Qbar l) x` using `fun _ => rfl`. Use `⟨h2.of_iso ⟨(theta (R u).left)⁻¹ * Jgl _ 3, fun s => ?_⟩, _, flag_neg ρ c.toMonoidHom _ _ hd κ hf _ ha, j.rev, i.rev, MonoidHom.ext fun s => ?_⟩` and prove the remaining obligations.

Establish `h3 : theta (ρ (c s)) = theta (R u).left * ρ s * (theta (R u).left)⁻¹`. Use `congrArg theta (ha s)` as an intermediate fact. Simplify using `only [t, map_mul, map_inv] at this ⊢`. Simplify using `only [← t, theta_theta] at this ⊢`. Conclude with `this`.

Establish `h4 : theta (ρ (c s)) = Jgl _ 3 * r₂ s * Jgl _ 3` using `rfl`. Rewrite using `[_root_.mul_inv_rev, inv_inv, hJ]`. Combine the equalities or inequalities in the displayed calculation. Use `hev s` as an intermediate fact. Simplify using `only [MonoidHom.mul_apply, MonoidHom.inv_apply, Fin.rev_rev]`.

Rewrite using `[this]`. Simplify using `[mul_comm]`.
-/
private theorem move_all (ρ : G K Ω →* GL (Fin 3) (Qbar l)) (R : G ℚ Ω →* GG 3 (Qbar l))
    (hρ : ∀ s, ρ s = (R (galEmb ℚ K Ω s)).left) (hK : ∀ s, (R (galEmb ℚ K Ω s)).right = 1)
    (hN : (galOf ℚ K Ω).Normal) (u : G ℚ Ω) (P P' : ValuationSubring Ω) (hP : ∀ x, x ∈ P' ↔ u x ∈ P)
    (κ : Fin 3 → ↥(Dec (F := K) P) →* (Qbar l)ˣ) (hf : Af.IsFlagOn ρ (Dec (F := K) P) κ) (hp : Af.PotCrysAt ρ P)
    (i j : Fin 3) (hij : κ i = κ j * (cycBar K Ω l).comp (Dec (F := K) P).subtype) :
    Af.PotCrysAt ρ P' ∧ ∃ κ' : Fin 3 → ↥(Dec (F := K) P') →* (Qbar l)ˣ, Af.IsFlagOn ρ (Dec (F := K) P') κ' ∧
      ∃ i' j', κ' i' = κ' j' * (cycBar K Ω l).comp (Dec (F := K) P').subtype := by
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
  have hev : ∀ s : ↥(Dec (F := K) P'), ((κ i).comp (dRes c.toMonoidHom _ _ hd)) s =
      ((κ j).comp (dRes c.toMonoidHom _ _ hd)) s * (cycBar K Ω l).comp (Dec (F := K) P').subtype s := fun s => by
    have := DFunLike.congr_fun hij (dRes c.toMonoidHom _ _ hd s)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, this, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply]
    exact congrArg _ (hcyc s)
  rcases Int.units_eq_one_or (R u).right with hu | hu
  · have ha : ∀ s, ρ (c.toMonoidHom s) = (R u).left * ρ s * (R u).left⁻¹ := fun s => by
      rw [hρ s]
      exact (hρc s).trans (gg_conj_pos _ _ hu (hK s))
    refine ⟨h1.of_iso ⟨(R u).left⁻¹, fun s => ?_⟩, _, flag_pos ρ c.toMonoidHom _ _ hd κ hf _ ha, i, j, MonoidHom.ext hev⟩
    rw [MonoidHom.comp_apply, ha]
    group
  · have ha : ∀ s, ρ (c.toMonoidHom s) = (R u).left * theta (ρ s) * (R u).left⁻¹ := fun s => by
      rw [hρ s]
      exact (hρc s).trans (gg_conj_neg _ _ hu (hK s))
    let r₂ : G K Ω →* GL (Fin 3) (Qbar l) :=
      { toFun := fun s => trInv (ρ (c s))
        map_one' := by
          apply Units.ext
          simp [trInv_val]
        map_mul' := fun a b => by rw [map_mul, map_mul, trInv_mul] }
    have h2 : Af.PotCrysAt r₂ P' := UpperTheory.potentiallyCrystalline_contragredient (ρ.comp c.toMonoidHom) r₂ P' (fun s => rfl) h1
    have hJ : (Jgl (Qbar l) 3)⁻¹ = Jgl (Qbar l) 3 := inv_eq_of_mul_eq_one_left Jgl_mul_Jgl
    have t : ∀ x : GL (Fin 3) (Qbar l), theta x = thetaAut 3 (Qbar l) x := fun _ => rfl
    refine ⟨h2.of_iso ⟨(theta (R u).left)⁻¹ * Jgl _ 3, fun s => ?_⟩, _, flag_neg ρ c.toMonoidHom _ _ hd κ hf _ ha,
      j.rev, i.rev, MonoidHom.ext fun s => ?_⟩
    · have h3 : theta (ρ (c s)) = theta (R u).left * ρ s * (theta (R u).left)⁻¹ := by
        have := congrArg theta (ha s)
        simp only [t, map_mul, map_inv] at this ⊢
        simp only [← t, theta_theta] at this ⊢
        exact this
      have h4 : theta (ρ (c s)) = Jgl _ 3 * r₂ s * Jgl _ 3 := rfl
      rw [_root_.mul_inv_rev, inv_inv, hJ]
      calc ρ s = (theta (R u).left)⁻¹ * (theta (R u).left * ρ s * (theta (R u).left)⁻¹) * theta (R u).left := by group
        _ = _ := by rw [← h3, h4]; simp only [mul_assoc]
    · have := hev s
      simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Fin.rev_rev]
      rw [this]
      simp [mul_comm]

end Move

/- English proof (translation)
The claim follows from `(IsLocallyConstant.iff_exists_open _).2 fun x => ⟨(fun y => x⁻¹ * y) ⁻¹' η.ker, h.preimage (continuous_const.mul continuous_id), by simp, fun y hy => by have : η (x⁻¹ * y) = 1 := hy rw [map_mul, map_inv, inv_mul_eq_one] at this exact this.symm⟩`.
-/
private theorem lc_of_ker {Γ C : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group C] (η : Γ →* C)
    (h : IsOpen (η.ker : Set Γ)) : IsLocallyConstant η :=
  (IsLocallyConstant.iff_exists_open _).2 fun x =>
    ⟨(fun y => x⁻¹ * y) ⁻¹' η.ker, h.preimage (continuous_const.mul continuous_id), by simp, fun y hy => by
      have : η (x⁻¹ * y) = 1 := hy
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      exact this.symm⟩

end UpperTheory.V.Z.J.UnitaryRankTwoFlags

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
attribute [local instance 10000] IsDiscreteValuationRing.toIsLocalRing

set_option maxHeartbeats 400000 in
open UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Th.End3 UpperTheory.V.Z.J.UnitaryRankTwoFlags in
/- English proof (translation)
Introduce `hU Ω _ _ _ l _ c _ N _ e ψ η σ g₁ B M H hev hΨ hF A _ _ r hr hirr K _ _ _ _ _ hK2 hker ρ hρ N' hN' hlev`. Take `⟨L, _, _, _, _, g₂, Φ, C₀, ⟨k⟩, hok, hbig, hseed⟩` from `hF`. Use `haveI := algClo L Ω`. Take `⟨hcpl, hloc, hcont⟩` from `sub_facts c A`. Establish `hl : l ∣ M` using `(dvd_mul_right l N).trans H.dvd`.

Establish `hσ : σ * σ = 1` using `Db.cc_sq H.cc`. Establish `hM` using `Pr.marks_of_link k hok hl hσ hΨ`. Establish `h2 : IsUnit (2 : c.O)`. Rewrite using `[← residue_ne_zero_iff_isUnit, map_ofNat]`. Introduce `h0`.

Conclude with `hok.l_odd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 ((CharP.cast_eq_zero_iff (ResidueField c.O) l 2).1 (by exact_mod_cast h0)))`. Take `⟨h, -, hr'⟩` from `ordPt_renorm hr (lc_of_ker η (hker ▸ (galEmbTop ℚ K Ω).2.1)) h2 hM`. Set `h' : GL (Fin 3) (Qbar l)` to `Matrix.GeneralLinearGroup.map (A.val : A →+* PadicAlgCl l) h`. Establish `eR : UnitaryThreeInertia.push A.val (conjBy h r) = conjBy h' (UnitaryThreeInertia.push A.val r)` using `map_conjBy _ h r`. Establish `hmat : ∀ g ∈ η.ker, (UnitaryThreeInertia.push A.val (conjBy h r) g).left = h' * (UnitaryThreeInertia.push A.val r g).left * h'⁻¹` using `fun g hg => by`.

Rewrite using `[eR, conjBy_left, show (UnitaryThreeInertia.push A.val r g).right = 1 from (hr.red.mult g).trans hg, sgnAct_one]`. Establish `hmem : ∀ s : G K Ω, galEmb ℚ K Ω s ∈ η.ker` using `fun s => hker ▸ galEmb_mem ℚ K Ω s`. Set `ρ' : G K Ω →* GL (Fin 3) (Qbar l)` to `(MulAut.conj h').toMonoidHom.comp ρ`. Establish `hiso : ∀ s, ρ' s = h' * ρ s * h'⁻¹` using `fun _ => rfl`. Establish `hρ' : ∀ s, ρ' s = (UnitaryThreeInertia.push A.val (conjBy h r) (galEmb ℚ K Ω s)).left` using `fun s => by`.

Rewrite using `[hmat _ (hmem s), hiso, show ρ s = _ from Units.ext (hρ s)]`. Establish `hLη : galOf ℚ L Ω ≤ η.ker` using `Db.galL_le k`. Establish `hirrU : ∀ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) → U ≤ η.ker → MatIrr U (mats (UnitaryThreeInertia.push A.val (conjBy h r)))` using `fun U h1 h3 => matIrr_conj (hirr U h1 h3) h' fun g hg => congrArg Units.val (hmat g (h3 hg))`. Generalize the expression as in `conjBy h r = r' at hr' hρ' hirrU`. Establish `hright : ∀ g, (UnitaryThreeInertia.push A.val r' g).right = η g` using `hr'.red.mult`.

Establish `hK : ∀ s, (UnitaryThreeInertia.push A.val r' (galEmb ℚ K Ω s)).right = 1` using `fun s => (hright _).trans (hmem s)`. Take `⟨_, _⟩` from `Db.algKL K L Ω (hLη.trans hker.le)`. Take `⟨ν, n1, n2, n3⟩` from `Pr.exists_nrep3 k hok hl hσ r' hr'`. Establish `key` using `hU Ω l c N e ψ η σ g₂ B M H hev L Φ C₀ k hok hbig hseed`. Establish `n4 : ∀ s, (ρ'.comp (galEmb K L Ω) s).val = (ν.r (k.p0 s)).map A.val` using `fun s => by`.

Rewrite using `[n2, MonoidHom.comp_apply, hρ']`. Both sides reduce to the same expression. Establish `n5 : ∀ v i, ∀ g ∈ Φ.Iv v, (ν.ψ v i g).val = algebraMap c.O A (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (k.j v g) ^ Fr.w 3 i).val` using `fun v i g hg => by`. Rewrite using `[n3 v i g hg, Fr.w, if_pos rfl]`. Both sides reduce to the same expression.

Establish `irr : ∀ U : Subgroup (G L Ω), IsOpen (U : Set (G L Ω)) → Af.IsIrr ((ρ'.comp (galEmb K L Ω)).comp U.subtype)`. Introduce `U hUo`. Establish `hoe : Topology.IsOpenEmbedding (galEmb ℚ L Ω)` using `⟨(galEmbTop ℚ L Ω).1, by`. Rewrite using `[← MonoidHom.coe_range, range_galEmb]`. Conclude with `(galEmbTop ℚ L Ω).2.1⟩`.

Use `Db.irr_of_matIrr (by norm_num) (U.map (galEmb ℚ L Ω)) _ (hirrU (U.map (galEmb ℚ L Ω)) (hoe.isOpenMap _ hUo) (Subgroup.map_le_iff_le_comap.2 fun s _ => hLη (galEmb_mem ℚ L Ω s))) ((galEmb ℚ L Ω).comp U.subtype) (fun g hg => ?_) _ fun s => ?_` and prove the remaining obligations. Take `⟨s, hs, e⟩` from `hg`. Conclude with `⟨⟨s, hs⟩, e⟩`. Use `show (ρ' (galEmb K L Ω s.1)).val = _`. Rewrite using `[hρ']`.

Both sides reduce to the same expression. Introduce `w hw`. Take `⟨P, hP, χ, κ, h1, h3, h4, h5⟩` from `hlev w hw`. Use `⟨P, hP, κ, ⟨χ, h1, h3, h4⟩, ?_⟩` and prove the remaining obligations. Break down `h5 with h5 | h5` into its components or cases.

Conclude with `h5`. Introduce `i j hij`. Establish `hPl : P.valuation (l : Ω) < 1`. Use `hP ((l : ℕ) : 𝓞 K)` as an intermediate fact. Simplify using `only [map_natCast] at this`.

Conclude with `this.2 hw`. Take `⟨v, u, -, hPv⟩ : ∃ v, ∃ u ∈ Pr.upl Ω L, P = u • k.pl v` from `(k.pl_all P hPl).exists`. Establish `hAv : ∀ x, x ∈ k.pl v ↔ u x ∈ P` using `fun x => by`. Rewrite using `[hPv]`. Conclude with `ValuationSubring.smul_mem_pointwise_smul_iff.symm`.

Take `⟨pot, κ', ⟨Q, fl⟩, i', j', hl'⟩` from `move_all ρ' (UnitaryThreeInertia.push A.val r') hρ' hK (by rw [← hker]; exact η.normal_ker) u P (k.pl v) hAv κ (h3.of_iso ⟨h', hiso⟩) (h5.of_iso ⟨h', hiso⟩) i j hij`. Establish `hlv : (k.pl v).valuation (l : Ω) < 1` using `val_move u hAv l hPl`. Establish `hMv : (k.pl v).valuation (M : Ω) < 1`. Take `⟨t, rfl⟩` from `hl`. Rewrite using `[Nat.cast_mul, map_mul]`.

Conclude with `mul_lt_one_of_lt_of_le hlv (((k.pl v).valuation_le_one_iff _).2 (natCast_mem _ t))`. Establish `hdec : ∀ g, (k.j v g).1 ∈ Dec (F` using `ℚ) (k.pl v) := fun g => (k.j_range v _).1 ⟨g, rfl⟩`. Establish `hsplit : ∀ g, (k.j v g).1 ∈ (galEmb ℚ L Ω).range` using `fun g => by`. Rewrite using `[range_galEmb, k.gal]`. Conclude with `⟨(k.j v g).2, k.split _ hMv ⟨hdec g, (k.j v g).2⟩⟩`.

Use `choose t ht using hsplit`. Establish `hloc0 : ∀ g, Φ.loc0 v g = k.p0 (t g)` using `fun g => Subtype.ext ((k.j_loc v g).trans (congrArg k.p (Subtype.ext (ht g).symm)))`. Establish `hdm : ∀ g, galEmb K L Ω (t g) ∈ Dec (F` using `K) (k.pl v) := fun g => by`. Use `hdec g` as an intermediate fact. Rewrite `this` using `[← ht]`.

Conclude with `this`. Set `d : Φ.Gv v → ↥(Dec (F` to `K) (k.pl v)) := fun g => ⟨galEmb K L Ω (t g), hdm g⟩`. Set `f : A →+* Qbar l` to `(A.val : A →+* PadicAlgCl l)`. Establish `hT : ∀ g, f.mapMatrix (ν.r (Φ.loc0 v g)) = (ρ' (d g).1).val` using `fun g => by`. Rewrite using `[hloc0]`.

Conclude with `(n4 (t g)).symm`. Establish `mt : ∀ b, ∃ a, ∀ g, (κ' b (d g) : Qbar l) = f (ν.ψ v a g : A)` using `fun b => flag_match (fun g => f.mapMatrix (ν.r (Φ.loc0 v g))) (fun a g => f (ν.ψ v a g : A)) (fun a g => (κ' a (d g) : Qbar l)) Q (fun g => by`. Rewrite using `[hT]`. Conclude with `fun x y hxy => (fl (d g)).1 x y hxy)`. Use the proof step `(fun g x => by`.

Rewrite using `[hT]`. Conclude with `(fl (d g)).2 x)`. Use the proof step `(fun g => by`. Rewrite using `[Fr.ordProd_map f (fun s => ν.r (Φ.loc0 v s)) (fun a s => (ν.ψ v a s : A)) g, ν.ord v g, map_zero]) b`. Take `⟨a, ha⟩` from `mt i'`.

Take `⟨b, hb⟩` from `mt j'`. Take `⟨g, hg⟩` from `key A ν n1 n5 _ n4 irr v (Br.potRes K L Ω l 3 ρ' _ pot) a b`. Apply `hg` to reduce the goal to its premises. Establish `e1` using `congrArg (fun x : ↥(Dec (F := K) (k.pl v)) →* (Qbar l)ˣ => ((x (d g) : (Qbar l)ˣ) : Qbar l)) hl'`. Establish `e2 : cycBar K Ω l (d g).1 = cycBar ℚ Ω l (k.j v g).1`.

Rewrite using `[← ht]`. Both sides reduce to the same expression. Simplify using `only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, Subgroup.subtype_apply] at e1`. Rewrite `e1` using `[ha, hb, e2]`. Conclude with `e1`.
-/
theorem UpperTheory.V.Z.J.unlEnd3E :
    LinkedUnlE → UnlEndLogNorm := by
  intro hU Ω _ _ _ l _ c _ N _ e ψ η σ g₁ B M H hev hΨ hF A _ _ r hr hirr K _ _ _ _ _ hK2 hker ρ hρ N' hN' hlev
  obtain ⟨L, _, _, _, _, g₂, Φ, C₀, ⟨k⟩, hok, hbig, hseed⟩ := hF
  haveI := algClo L Ω
  obtain ⟨hcpl, hloc, hcont⟩ := sub_facts c A
  have hl : l ∣ M := (dvd_mul_right l N).trans H.dvd
  have hσ : σ * σ = 1 := Db.cc_sq H.cc
  have hM := Pr.marks_of_link k hok hl hσ hΨ
  have h2 : IsUnit (2 : c.O) := by
    rw [← residue_ne_zero_iff_isUnit, map_ofNat]
    intro h0
    exact hok.l_odd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1
      ((CharP.cast_eq_zero_iff (ResidueField c.O) l 2).1 (by exact_mod_cast h0)))
  obtain ⟨h, -, hr'⟩ := ordPt_renorm hr (lc_of_ker η (hker ▸ (galEmbTop ℚ K Ω).2.1)) h2 hM
  let h' : GL (Fin 3) (Qbar l) := Matrix.GeneralLinearGroup.map (A.val : A →+* PadicAlgCl l) h
  have eR : UnitaryThreeInertia.push A.val (conjBy h r) = conjBy h' (UnitaryThreeInertia.push A.val r) := map_conjBy _ h r
  have hmat : ∀ g ∈ η.ker, (UnitaryThreeInertia.push A.val (conjBy h r) g).left = h' * (UnitaryThreeInertia.push A.val r g).left * h'⁻¹ := fun g hg => by
    rw [eR, conjBy_left, show (UnitaryThreeInertia.push A.val r g).right = 1 from (hr.red.mult g).trans hg, sgnAct_one]
  have hmem : ∀ s : G K Ω, galEmb ℚ K Ω s ∈ η.ker := fun s => hker ▸ galEmb_mem ℚ K Ω s
  let ρ' : G K Ω →* GL (Fin 3) (Qbar l) := (MulAut.conj h').toMonoidHom.comp ρ
  have hiso : ∀ s, ρ' s = h' * ρ s * h'⁻¹ := fun _ => rfl
  have hρ' : ∀ s, ρ' s = (UnitaryThreeInertia.push A.val (conjBy h r) (galEmb ℚ K Ω s)).left := fun s => by
    rw [hmat _ (hmem s), hiso, show ρ s = _ from Units.ext (hρ s)]
  have hLη : galOf ℚ L Ω ≤ η.ker := Db.galL_le k
  have hirrU : ∀ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) → U ≤ η.ker →
      MatIrr U (mats (UnitaryThreeInertia.push A.val (conjBy h r))) := fun U h1 h3 =>
    matIrr_conj (hirr U h1 h3) h' fun g hg => congrArg Units.val (hmat g (h3 hg))
  generalize conjBy h r = r' at hr' hρ' hirrU
  have hright : ∀ g, (UnitaryThreeInertia.push A.val r' g).right = η g := hr'.red.mult
  have hK : ∀ s, (UnitaryThreeInertia.push A.val r' (galEmb ℚ K Ω s)).right = 1 := fun s => (hright _).trans (hmem s)
  obtain ⟨_, _⟩ := Db.algKL K L Ω (hLη.trans hker.le)
  obtain ⟨ν, n1, n2, n3⟩ := Pr.exists_nrep3 k hok hl hσ r' hr'
  have key := hU Ω l c N e ψ η σ g₂ B M H hev L Φ C₀ k hok hbig hseed
  have n4 : ∀ s, (ρ'.comp (galEmb K L Ω) s).val = (ν.r (k.p0 s)).map A.val := fun s => by
    rw [n2, MonoidHom.comp_apply, hρ']
    rfl
  have n5 : ∀ v i, ∀ g ∈ Φ.Iv v, (ν.ψ v i g).val =
      algebraMap c.O A (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (k.j v g) ^ Fr.w 3 i).val := fun v i g hg => by
    rw [n3 v i g hg, Fr.w, if_pos rfl]
    rfl
  have irr : ∀ U : Subgroup (G L Ω), IsOpen (U : Set (G L Ω)) → Af.IsIrr ((ρ'.comp (galEmb K L Ω)).comp U.subtype) := by
    intro U hUo
    have hoe : Topology.IsOpenEmbedding (galEmb ℚ L Ω) :=
      ⟨(galEmbTop ℚ L Ω).1, by
        rw [← MonoidHom.coe_range, range_galEmb]
        exact (galEmbTop ℚ L Ω).2.1⟩
    refine Db.irr_of_matIrr (by norm_num) (U.map (galEmb ℚ L Ω)) _
      (hirrU (U.map (galEmb ℚ L Ω)) (hoe.isOpenMap _ hUo) (Subgroup.map_le_iff_le_comap.2 fun s _ => hLη (galEmb_mem ℚ L Ω s)))
      ((galEmb ℚ L Ω).comp U.subtype) (fun g hg => ?_) _ fun s => ?_
    · obtain ⟨s, hs, e⟩ := hg
      exact ⟨⟨s, hs⟩, e⟩
    · show (ρ' (galEmb K L Ω s.1)).val = _
      rw [hρ']
      rfl
  intro w hw
  obtain ⟨P, hP, χ, κ, h1, h3, h4, h5⟩ := hlev w hw
  refine ⟨P, hP, κ, ⟨χ, h1, h3, h4⟩, ?_⟩
  rcases h5 with h5 | h5
  · exact h5
  intro i j hij
  have hPl : P.valuation (l : Ω) < 1 := by
    have := hP ((l : ℕ) : 𝓞 K)
    simp only [map_natCast] at this
    exact this.2 hw
  obtain ⟨v, u, -, hPv⟩ : ∃ v, ∃ u ∈ Pr.upl Ω L, P = u • k.pl v := (k.pl_all P hPl).exists
  have hAv : ∀ x, x ∈ k.pl v ↔ u x ∈ P := fun x => by
    rw [hPv]
    exact ValuationSubring.smul_mem_pointwise_smul_iff.symm
  obtain ⟨pot, κ', ⟨Q, fl⟩, i', j', hl'⟩ := move_all ρ' (UnitaryThreeInertia.push A.val r') hρ' hK
    (by rw [← hker]; exact η.normal_ker) u P (k.pl v) hAv κ (h3.of_iso ⟨h', hiso⟩) (h5.of_iso ⟨h', hiso⟩) i j hij
  have hlv : (k.pl v).valuation (l : Ω) < 1 := val_move u hAv l hPl
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
  have hT : ∀ g, f.mapMatrix (ν.r (Φ.loc0 v g)) = (ρ' (d g).1).val := fun g => by
    rw [hloc0]
    exact (n4 (t g)).symm
  have mt : ∀ b, ∃ a, ∀ g, (κ' b (d g) : Qbar l) = f (ν.ψ v a g : A) := fun b =>
    flag_match (fun g => f.mapMatrix (ν.r (Φ.loc0 v g))) (fun a g => f (ν.ψ v a g : A)) (fun a g => (κ' a (d g) : Qbar l)) Q
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
  obtain ⟨g, hg⟩ := key A ν n1 n5 _ n4 irr v (Br.potRes K L Ω l 3 ρ' _ pot) a b
  apply hg
  have e1 := congrArg (fun x : ↥(Dec (F := K) (k.pl v)) →* (Qbar l)ˣ => ((x (d g) : (Qbar l)ˣ) : Qbar l)) hl'
  have e2 : cycBar K Ω l (d g).1 = cycBar ℚ Ω l (k.j v g).1 := by
    rw [← ht]
    rfl
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, Subgroup.subtype_apply] at e1
  rw [ha, hb, e2] at e1
  exact e1

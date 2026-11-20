import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.MapDiagonalRepMatrixEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia UpperTheory.V.Pr

namespace UpperTheory.V.UnitaryThreeInertia

/- English proof (translation)
Simplify using `[conjBy, GG.mat, hg]`.
-/
private theorem tc_conj_mat {R D : Type} [CommRing R] [Group D] (r : D →* GG 3 R) (h : GL (Fin 3) R) (g : D)
    (hg : (r g).right = 1) :
    (conjBy h⁻¹ r g).mat = ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r g).mat * h := by
  simp [conjBy, GG.mat, hg]

/- English proof (translation)
Establish `h1 : (h : Matrix (Fin 3) (Fin 3) R).map (residue R) = 1`. Use extensionality with `a b`. Use `(residue_eq_zero_iff _).2 (hh a b)` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, map_sub, sub_eq_zero]`. Rewrite using `[Matrix.map_apply, this]`.

Apply the tactic sequence `by_cases e : a = b <;> simp [Matrix.one_apply, e]`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `: (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * h).map (residue R) = 1`. Rewrite using `[Units.inv_mul]`. Simplify using the standard rewrite rules.

Rewrite `this` using `[Matrix.map_mul, h1, Matrix.mul_one]`. Then use the resulting hypothesis.
-/
private theorem tc_res {R : Type} [CommRing R] [IsLocalRing R] (h : GL (Fin 3) R) (hh : InHat h) :
    (h : Matrix (Fin 3) (Fin 3) R).map (residue R) = 1 ∧
      ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R).map (residue R) = 1 := by
  have h1 : (h : Matrix (Fin 3) (Fin 3) R).map (residue R) = 1 := by
    ext a b
    have := (residue_eq_zero_iff _).2 (hh a b)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [Matrix.map_apply, this]
    by_cases e : a = b <;> simp [Matrix.one_apply, e]
  refine ⟨h1, ?_⟩
  have : (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * h).map (residue R) = 1 := by
    rw [Units.inv_mul]; simp
  rwa [Matrix.map_mul, h1, Matrix.mul_one] at this

/- English proof (translation)
Establish `: (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h).map (residue R) = X.map (residue R)`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, (tc_res h hh).1, (tc_res h hh).2, Matrix.one_mul, Matrix.mul_one]`. Conclude with `congrFun (congrFun this a) b`.
-/
private theorem tc_res_conj {R : Type} [CommRing R] [IsLocalRing R] (h : GL (Fin 3) R) (hh : InHat h)
    (X : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    residue R ((((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h) a b) = residue R (X a b) := by
  have : (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h).map (residue R) = X.map (residue R) := by
    rw [Matrix.map_mul, Matrix.map_mul, (tc_res h hh).1, (tc_res h hh).2, Matrix.one_mul, Matrix.mul_one]
  exact congrFun (congrFun this a) b

/- English proof (translation)
Establish `e : (t : O) * ((t⁻¹ : Oˣ) : O) = 1` using `Units.mul_inv t`. Establish `h1 : IsUnit ((t : O) - 1)`. Rewrite `ht` using `[show (t : O) ^ 2 - 1 = ((t : O) - 1) * (t + 1) by ring]`. Conclude with `isUnit_of_mul_isUnit_left ht`. Establish `h2 : IsUnit ((t : O) - ((t⁻¹ : Oˣ) : O))`.

Use `ht.mul (t⁻¹).isUnit` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Take the linear combination `(-(t : O)) * e`. Establish `h3 : IsUnit (1 - ((t⁻¹ : Oˣ) : O))`. Use `h1.mul (t⁻¹).isUnit` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Take the linear combination `(-1 : O) * e`. Establish `h1'` using `h1.neg`. Establish `h2'` using `h2.neg`. Establish `h3'` using `h3.neg`.

Rewrite `h1'`, `h2'`, `h3'` using `[neg_sub]`. Establish `w0 : wt1 0 = 1` using `rfl`. Establish `w1 : wt1 1 = 0` using `rfl`. Establish `w2 : wt1 2 = -1` using `rfl`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;>`.

Apply the tactic sequence `simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, w0, w1, w2, zpow_one, zpow_zero, _root_.zpow_neg, Units.val_one, ne_eq, not_true_eq_false] at hab ⊢ <;> assumption`.
-/
private theorem tc_unit {O : Type} [CommRing O] (t : Oˣ) (ht : IsUnit ((t : O) ^ 2 - 1)) (a b : Fin 3)
    (hab : a ≠ b) : IsUnit (((t ^ wt1 a : Oˣ) : O) - ((t ^ wt1 b : Oˣ) : O)) := by
  have e : (t : O) * ((t⁻¹ : Oˣ) : O) = 1 := Units.mul_inv t
  have h1 : IsUnit ((t : O) - 1) := by
    rw [show (t : O) ^ 2 - 1 = ((t : O) - 1) * (t + 1) by ring] at ht
    exact isUnit_of_mul_isUnit_left ht
  have h2 : IsUnit ((t : O) - ((t⁻¹ : Oˣ) : O)) := by
    have := ht.mul (t⁻¹).isUnit
    convert this using 1
    linear_combination (-(t : O)) * e
  have h3 : IsUnit (1 - ((t⁻¹ : Oˣ) : O)) := by
    have := h1.mul (t⁻¹).isUnit
    convert this using 1
    linear_combination (-1 : O) * e
  have h1' := h1.neg
  have h2' := h2.neg
  have h3' := h3.neg
  rw [neg_sub] at h1' h2' h3'
  have w0 : wt1 0 = 1 := rfl
  have w1 : wt1 1 = 0 := rfl
  have w2 : wt1 2 = -1 := rfl
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, w0, w1, w2, zpow_one, zpow_zero, _root_.zpow_neg,
      Units.val_one, ne_eq, not_true_eq_false] at hab ⊢ <;> assumption

/- English proof (translation)
Establish `e` using `mul_geom_sum (u : R) N`. Rewrite `e` using `[← Units.val_pow_eq_pow_val, h2, Units.val_one, sub_self]`. Establish `hu : residue R (u : R) = 1`. Use `(residue_eq_zero_iff _).2 h1` as an intermediate fact. Rewrite `this` using `[map_sub, map_one, sub_eq_zero]`. Then use the resulting hypothesis.

Establish `hs : IsUnit (∑ i ∈ Finset.range N, (u : R) ^ i)`. Rewrite `hN`, the goal using `[← residue_ne_zero_iff_isUnit]`. Simplify `hN` using `[map_sum, hu]`. Conclude with `Units.ext (sub_eq_zero.1 (hs.mul_left_eq_zero.1 e))`.
-/
private theorem unit_eq_one_of_pow_eq_one_of_residue_one {R : Type} [CommRing R] [IsLocalRing R] (u : Rˣ) (N : ℕ) (hN : IsUnit (N : R))
    (h1 : (u : R) - 1 ∈ maximalIdeal R) (h2 : u ^ N = 1) : u = 1 := by
  have e := mul_geom_sum (u : R) N
  rw [← Units.val_pow_eq_pow_val, h2, Units.val_one, sub_self] at e
  have hu : residue R (u : R) = 1 := by
    have := (residue_eq_zero_iff _).2 h1
    rwa [map_sub, map_one, sub_eq_zero] at this
  have hs : IsUnit (∑ i ∈ Finset.range N, (u : R) ^ i) := by
    rw [← residue_ne_zero_iff_isUnit] at hN ⊢
    simpa [map_sum, hu] using hN
  exact Units.ext (sub_eq_zero.1 (hs.mul_left_eq_zero.1 e))

/- English proof (translation)
Simplify using `[GG.mat, hg]`.
-/
private theorem de_mul' {R D : Type} [CommRing R] [Group D] (r : D →* GG 3 R) (g h : D) (hg : (r g).right = 1) :
    (r (g * h)).mat = (r g).mat * (r h).mat := by
  simp [GG.mat, hg]

/- English proof (translation)
Rewrite using `[de_mul' r g h ((hm g).trans hg), Matrix.mul_apply]`. Use `Finset.sum_eq_single a (fun c _ hc => ?_) (fun hn => absurd (Finset.mem_univ a) hn)` and prove the remaining obligations. Establish `h1 : wt a c < 0 ∧ 0 < wt c a ∨ 0 < wt a c ∧ wt c a < 0`. Establish `: (c : ℕ) ≠ a` using `fun e => hc (Fin.ext e)`. Simplify using `only [wt, wt1]`.

Use linear arithmetic over natural numbers and integers. Apply the tactic sequence `rcases hT with hT | hT <;> rcases h1 with h1 | h1`. Rewrite using `[hT g hg a c h1.1, zero_mul]`. Rewrite using `[hT h hh c a h1.2, mul_zero]`. Rewrite using `[hT h hh c a h1.2, mul_zero]`.

Rewrite using `[hT g hg a c h1.1, zero_mul]`.
-/
private theorem de_mul {R D : Type} [CommRing R] [Group D] {η : D →* ℤˣ} {r : D →* GG 3 R} (hm : HasMult η r)
    (hT : Upper η r ∨ Lower η r) (g h : D) (hg : η g = 1) (hh : η h = 1) (a : Fin 3) :
    (r (g * h)).mat a a = (r g).mat a a * (r h).mat a a := by
  rw [de_mul' r g h ((hm g).trans hg), Matrix.mul_apply]
  refine Finset.sum_eq_single a (fun c _ hc => ?_) (fun hn => absurd (Finset.mem_univ a) hn)
  have h1 : wt a c < 0 ∧ 0 < wt c a ∨ 0 < wt a c ∧ wt c a < 0 := by
    have : (c : ℕ) ≠ a := fun e => hc (Fin.ext e)
    simp only [wt, wt1]; omega
  rcases hT with hT | hT <;> rcases h1 with h1 | h1
  · rw [hT g hg a c h1.1, zero_mul]
  · rw [hT h hh c a h1.2, mul_zero]
  · rw [hT h hh c a h1.2, mul_zero]
  · rw [hT g hg a c h1.1, zero_mul]

/- English proof (translation)
Rewrite using `[Matrix.det_fin_three, Fin.prod_univ_three]`. Break down `hX with hX | hX` into its components or cases. Simplify using `[hX 1 0 (by decide), hX 2 0 (by decide), hX 2 1 (by decide)]`. Simplify using `[hX 0 1 (by decide), hX 0 2 (by decide), hX 1 2 (by decide)]`.
-/
private theorem de_det {R : Type} [CommRing R] (X : Matrix (Fin 3) (Fin 3) R)
    (hX : (∀ a b, wt a b < 0 → X a b = 0) ∨ ∀ a b, 0 < wt a b → X a b = 0) (d : R) :
    (d • (1 : Matrix (Fin 3) (Fin 3) R) - X).det = ∏ b, (d - X b b) := by
  rw [Matrix.det_fin_three, Fin.prod_univ_three]
  rcases hX with hX | hX
  · simp [hX 1 0 (by decide), hX 2 0 (by decide), hX 2 1 (by decide)]
  · simp [hX 0 1 (by decide), hX 0 2 (by decide), hX 1 2 (by decide)]

/- English proof (translation)
Establish `h1 : X a a • (1 : Matrix (Fin 3) (Fin 3) R) - U = ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (X a a • (1 : Matrix (Fin 3) (Fin 3) R) - X) * h`. Rewrite using `[e, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.inv_mul]`. Establish `h2` using `de_det U (Or.inl hU) (X a a)`. Rewrite `h2` using `[h1, Matrix.det_units_conj', de_det X hX, Finset.prod_eq_zero (Finset.mem_univ a) (sub_self _), ← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]`. Establish `h3 : IsUnit (∏ b ∈ Finset.univ.erase a, (X a a - U b b))` using `IsUnit.prod_iff.2 fun b hb => hu b (Finset.ne_of_mem_erase hb).symm`.

Conclude with `sub_eq_zero.1 (h3.mul_left_eq_zero.1 h2.symm)`.
-/
private theorem de_eig {R : Type} [CommRing R] (X U : Matrix (Fin 3) (Fin 3) R) (h : GL (Fin 3) R)
    (e : U = ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h)
    (hX : (∀ a b, wt a b < 0 → X a b = 0) ∨ ∀ a b, 0 < wt a b → X a b = 0) (hU : ∀ a b, wt a b < 0 → U a b = 0)
    (a : Fin 3) (hu : ∀ b, a ≠ b → IsUnit (X a a - U b b)) : X a a = U a a := by
  have h1 : X a a • (1 : Matrix (Fin 3) (Fin 3) R) - U =
      ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (X a a • (1 : Matrix (Fin 3) (Fin 3) R) - X) * h := by
    rw [e, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.inv_mul]
  have h2 := de_det U (Or.inl hU) (X a a)
  rw [h1, Matrix.det_units_conj', de_det X hX,
    Finset.prod_eq_zero (Finset.mem_univ a) (sub_self _), ← Finset.mul_prod_erase _ _ (Finset.mem_univ a)] at h2
  have h3 : IsUnit (∏ b ∈ Finset.univ.erase a, (X a a - U b b)) :=
    IsUnit.prod_iff.2 fun b hb => hu b (Finset.ne_of_mem_erase hb).symm
  exact sub_eq_zero.1 (h3.mul_left_eq_zero.1 h2.symm)

private def kap {R D : Type} [CommRing R] [Group D] (η : D →* ℤˣ) (r : D →* GG 3 R) (hm : HasMult η r)
    (hT : Upper η r ∨ Lower η r) (a : Fin 3) : η.ker →* R where
  toFun g := (r g).mat a a
  map_one' := by simp [GG.mat]
  map_mul' g h := by
    rw [Subgroup.coe_mul, de_mul hm hT _ _ g.2 h.2]

/- English proof (translation)
Take `⟨x, hx, hx'⟩` from `hx`. Take `⟨h, hh, ht⟩` from `hT`. Establish `hm' : HasMult η (conjBy h⁻¹ r)` using `fun g => by`. Use `hr.mult g` as an intermediate fact. Simplify `this` using `[conjBy]`.

Establish `key : ∀ g, η g = 1 → IsUnit ((Ψ g : O) ^ 2 - 1) → (r g).mat a a = (conjBy h⁻¹ r g).mat a a`. Introduce `g hg hg'`. Establish `cm` using `tc_conj_mat r h g ((hr.mult g).trans hg)`. Establish `hX : ∀ a, residue R ((r g).mat a a) = residue R (algebraMap O R ((Ψ g ^ wt1 a : Oˣ) : O))`. Introduce `a`.

Use `(residue_eq_zero_iff _).2 (hr.red g a a)` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, map_sub, sub_eq_zero]`. Rewrite using `[this]`. Simplify using `only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.map_apply, Matrix.diagonal_apply_eq]`. Use `de_eig _ _ h cm (hd.imp (fun H => H g hg) fun H => H g hg) (ht.tri g hg) a fun b hab => ?_` and prove the remaining obligations.

Rewrite using `[← residue_ne_zero_iff_isUnit, map_sub, cm, tc_res_conj h hh, hX, hX, ← map_sub, ← map_sub, residue_ne_zero_iff_isUnit]`. Conclude with `(tc_unit (Ψ g) hg' a b hab).map _`. Rewrite using `[← ht.ine s hs hη a]`. Distinguish the cases in `hs' : IsUnit ((Ψ s : O) ^ 2 - 1)`. Conclude with `key s hη hs'`.

Establish `hxs : IsUnit ((Ψ (x * s) : O) ^ 2 - 1)`. Rewrite `hs'`, `hx'`, the goal using `[← residue_ne_zero_iff_isUnit]`. Rewrite `hs'` using `[not_not, map_sub, map_pow, map_one, sub_eq_zero]`. Rewrite `hx'`, the goal using `[map_sub, map_pow, map_one]`. Rewrite using `[map_mul, Units.val_mul, map_mul, mul_pow, hs', mul_one]` and apply the resulting hypothesis.

Establish `e` using `key (x * s) (by rw [map_mul, hx, hη, mul_one]) hxs`. Rewrite `e` using `[de_mul hr.mult hd x s hx hη, de_mul hm' (Or.inl ht.tri) x s hx hη, ← key x hx hx']`. Conclude with `((kap η r hr.mult hd a).toHomUnits ⟨x, hx⟩).isUnit.mul_left_cancel e`.
-/
private theorem de_ine {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]
    [IsLocalHom (algebraMap O R)] [Group D]
    {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D} {r : D →* GG 3 R} (hr : Red η Ψ r)
    (hd : Upper η r ∨ Lower η r) (hx : ∃ x, η x = 1 ∧ IsUnit ((Ψ x : O) ^ 2 - 1)) (hT : CondT η Ψ I r)
    (s : D) (hs : s ∈ I) (hη : η s = 1) (a : Fin 3) : (r s).mat a a = algebraMap O R (psi Ψ a s) := by
  obtain ⟨x, hx, hx'⟩ := hx
  obtain ⟨h, hh, ht⟩ := hT
  have hm' : HasMult η (conjBy h⁻¹ r) := fun g => by
    have := hr.mult g
    simpa [conjBy] using this
  have key : ∀ g, η g = 1 → IsUnit ((Ψ g : O) ^ 2 - 1) → (r g).mat a a = (conjBy h⁻¹ r g).mat a a := by
    intro g hg hg'
    have cm := tc_conj_mat r h g ((hr.mult g).trans hg)
    have hX : ∀ a, residue R ((r g).mat a a) = residue R (algebraMap O R ((Ψ g ^ wt1 a : Oˣ) : O)) := by
      intro a
      have := (residue_eq_zero_iff _).2 (hr.red g a a)
      rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
      rw [this]
      simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.map_apply, Matrix.diagonal_apply_eq]
    refine de_eig _ _ h cm (hd.imp (fun H => H g hg) fun H => H g hg) (ht.tri g hg) a fun b hab => ?_
    rw [← residue_ne_zero_iff_isUnit, map_sub, cm, tc_res_conj h hh, hX, hX, ← map_sub,
      ← map_sub, residue_ne_zero_iff_isUnit]
    exact (tc_unit (Ψ g) hg' a b hab).map _
  rw [← ht.ine s hs hη a]
  by_cases hs' : IsUnit ((Ψ s : O) ^ 2 - 1)
  · exact key s hη hs'
  · have hxs : IsUnit ((Ψ (x * s) : O) ^ 2 - 1) := by
      rw [← residue_ne_zero_iff_isUnit] at hs' hx' ⊢
      rw [not_not, map_sub, map_pow, map_one, sub_eq_zero] at hs'
      rw [map_sub, map_pow, map_one] at hx' ⊢
      rwa [map_mul, Units.val_mul, map_mul, mul_pow, hs', mul_one]
    have e := key (x * s) (by rw [map_mul, hx, hη, mul_one]) hxs
    rw [de_mul hr.mult hd x s hx hη, de_mul hm' (Or.inl ht.tri) x s hx hη, ← key x hx hx'] at e
    exact ((kap η r hr.mult hd a).toHomUnits ⟨x, hx⟩).isUnit.mul_left_cancel e

/- English proof (translation)
Establish `h1 : (r c).left = 1` using `Units.ext hc`. Establish `h2 : (r (c * x * c⁻¹)).left = theta (r x).left`. Simplify using `[h1, hc', hx, theta_theta]`. Establish `h3 : (r x⁻¹).left = ((r x).left)⁻¹`. Simplify using `[hx]`.

Unfold `GG.mat`. Rewrite using `[h2, h3, theta_val]`. Generalize the expression as in `((((r x).left)⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = Y`. Apply the tactic sequence `fin_cases a <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]`.
-/
private theorem de_c {R D : Type} [CommRing R] [Group D] (r : D →* GG 3 R) (c x : D) (hc : (r c).mat = 1)
    (hc' : (r c).right = -1) (hx : (r x).right = 1) (a : Fin 3) :
    (r (c * x * c⁻¹)).mat a a = (r x⁻¹).mat a.rev a.rev := by
  have h1 : (r c).left = 1 := Units.ext hc
  have h2 : (r (c * x * c⁻¹)).left = theta (r x).left := by
    simp [h1, hc', hx, theta_theta]
  have h3 : (r x⁻¹).left = ((r x).left)⁻¹ := by
    simp [hx]
  unfold GG.mat
  rw [h2, h3, theta_val]
  generalize ((((r x).left)⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = Y
  fin_cases a <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]

/- English proof (translation)
Set `u : Fin 3 → (F.η.ker →* Rˣ)` to `fun a => (kap F.η r hr.mult hd a).toHomUnits / (kap F.η ρ hρ.mult hd' a).toHomUnits`. Establish `hu : ∀ a (g : F.η.ker), (u a g : R) * (ρ g).mat a a = (r g).mat a a` using `fun a g => by show (((kap F.η r hr.mult hd a).toHomUnits g / (kap F.η ρ hρ.mult hd' a).toHomUnits g : Rˣ) : R) * (((kap F.η ρ hρ.mult hd' a).toHomUnits g : Rˣ) : R) = ((kap F.η r hr.mult hd a).toHomUnits g : Rˣ)`. Rewrite using `[← Units.val_mul, div_mul_cancel]`. Establish `hun : ∀ a (g : F.η.ker), IsUnit ((ρ g).mat a a)` using `fun a g => ((kap F.η ρ hρ.mult hd' a).toHomUnits g).isUnit`. Establish `h1 : ∀ (g : F.η.ker) a, (r g).mat a a = (ρ g).mat a a → u a g = 1` using `fun g a e => by`.

Apply `Units.ext` to reduce the goal to its premises. Apply `(hun a g).mul_right_cancel` to reduce the goal to its premises. Rewrite using `[hu, e, Units.val_one, one_mul]`. Establish `h2' : ∀ (g : F.η.ker) a, u a g = 1 → (r g).mat a a = (ρ g).mat a a` using `fun g a e => by`. Rewrite using `[← hu, e, Units.val_one, one_mul]`.

Establish `hI : ∀ v (s : F.D v), s ∈ F.Iv v → F.η (F.loc v s) = 1 → ∀ a, (r (F.loc v s)).mat a a = (ρ (F.loc v s)).mat a a`. Introduce `v s hs hη a`. Distinguish the cases in `hv : v ∈ F.Tb`. Establish `key : ∀ r : Γ →* GG 3 R, F.IsPt g₁ r → (Upper F.η r ∨ Lower F.η r) → (r (F.loc v s)).mat a a = algebraMap O R (psi (F.Ψv v) a s)`. Introduce `r hr hd`.

Use `de_ine (η := F.ηv v) (Ψ := F.Ψv v) (I := F.Iv v) (r := r.comp (F.loc v)) ⟨fun g => hr.mult (F.loc v g), fun g => hr.red (F.loc v g)⟩ (hd.imp (fun H g hg => H (F.loc v g) hg) fun H g hg => H (F.loc v g) hg) (hF.x v hv) ?_ s hs hη a` and prove the remaining obligations. Break down `hv with hv | hv` into its components or cases. Conclude with `(hr.loc v).1 hv`. Take `⟨h, hh, hD⟩` from `(hr.loc v).2.1 hv`. Conclude with `⟨h, hh, hD.toTriIn⟩`.

Conclude with `(key r hr hd).trans (key ρ hρ hd').symm`. Use `haveI := Fintype.ofFinite (ResidueField O)`. Establish `hmem : s ^ Fintype.card (ResidueField O)ˣ ∈ F.Nv v`. Use `⟨⟨pow_mem hs _, pow_mem (show s ∈ (F.ηv v).ker from hη) _⟩, ?_⟩` and prove the remaining obligations. Use `show ((Units.map (residue O).toMonoidHom).comp (F.Ψv v)) _ = 1`.

Rewrite using `[map_pow, pow_card_eq_one]`. Establish `hN : IsUnit ((Fintype.card (ResidueField O)ˣ : ℕ) : O)`. Rewrite using `[← residue_ne_zero_iff_isUnit, map_natCast, Fintype.card_units, Nat.cast_sub Fintype.card_pos, FiniteField.cast_card_eq_zero]`. Simplify using the standard rewrite rules. Use `h2' ⟨_, hη⟩ a (unit_eq_one_of_pow_eq_one_of_residue_one _ (Fintype.card (ResidueField O)ˣ) (by simpa using hN.map (algebraMap O R)) ?_ ?_)` and prove the remaining obligations.

Establish `e1` using `hr.red (F.loc v s) a a`. Establish `e2` using `hρ.red (F.loc v s) a a`. Establish `e3` using `sub_mem e1 e2`. Rewrite `e3` using `[Matrix.sub_apply, Matrix.sub_apply, sub_sub_sub_cancel_right]`. Establish `e4` using `hu a ⟨_, hη⟩`.

Rewrite using `[← Ideal.mul_unit_mem_iff_mem _ (hun a ⟨_, hη⟩), sub_mul, e4, one_mul]`. Conclude with `e3`. Rewrite using `[← map_pow]`. Use `h1 _ a ?_` and prove the remaining obligations. Establish `e1` using `(hr.loc v).2.2 hv _ hmem`.

Establish `e2` using `(hρ.loc v).2.2 hv _ hmem`. Rewrite `e1`, `e2` using `[MonoidHom.comp_apply, map_pow (F.loc v)]`. Conclude with `congrArg (fun y : GG 3 R => y.mat a a) (e1.trans e2.symm)`. Establish `hsplit : ∀ g, F.η g = 1 ∨ ∃ g', F.η g' = 1 ∧ g = g' * F.c` using `fun g => by`. Break down `Int.units_eq_one_or (F.η g) with h | h` into its components or cases.

Conclude with `Or.inl h`. Conclude with `Or.inr ⟨g * F.c, by simp [h, hF.ηc], by rw [mul_assoc, hF.csq, mul_one]⟩`. Establish `hconj : ∀ a (g x : Γ) (hg : F.η g = 1) (hx : F.η x = 1) (h : g * x * g⁻¹ ∈ F.η.ker), (r x).mat a a = (ρ x).mat a a → u a ⟨_, h⟩ = 1`. Introduce `a g x hg hx h e`. Establish `: (⟨_, h⟩ : F.η.ker) = ⟨g, hg⟩ * ⟨x, hx⟩ * ⟨g, hg⟩⁻¹` using `rfl`.

Rewrite using `[this, map_mul, map_mul, h1 ⟨x, hx⟩ a e, map_inv, mul_one, mul_inv_cancel]`. Establish `hker : ∀ g : F.η.ker, (r g).mat a a = (ρ g).mat a a`. Introduce `g`. Use `h2' g a (Units.ext ?_)` and prove the remaining obligations. Rewrite using `[← sub_eq_zero, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) Ideal.IsPrime.ne_top', Submodule.mem_iInf]`.

Introduce `n`. Set `q : R →* R ⧸ maximalIdeal R ^ n` to `(Ideal.Quotient.mk (maximalIdeal R ^ n)).toMonoidHom`. Establish `lc : ∀ (r : Γ →* GG 3 R) (hr : F.IsPt g₁ r) (hd : Upper F.η r ∨ Lower F.η r), IsLocallyConstant fun g => Units.map q ((kap F.η r hr.mult hd a).toHomUnits g)` using `fun r hr hd => IsLocallyConstant.desc _ Units.val (((hr.cont n).comp fun X => X a a).comp_continuous continuous_subtype_val) Units.val_injective`. Establish `hχ` using `hC _ ((Units.map q).comp (u a)) (by`. Use `(lc r hr hd).div (lc ρ hρ hd')` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Conclude with `map_div (Units.map q) _ _) (by`. Introduce `v s g h hs`. Establish `hη : F.η (F.loc v s) = 1`.

Establish `: F.η (g * F.loc v s * g⁻¹) = 1` using `h`. Rewrite `this` using `[map_mul, map_mul, map_inv, mul_inv_cancel_comm]`. Then use the resulting hypothesis. Rewrite using `[MonoidHom.comp_apply]`. Break down `hsplit g with hg | ⟨g', hg, rfl⟩` into its components or cases. Rewrite using `[hconj a g _ hg hη h (hI v s hs hη a), map_one]`.

Establish `e0 : g' * F.c * F.loc v s * (g' * F.c)⁻¹ = g' * (F.c * F.loc v s * F.c⁻¹) * g'⁻¹` using `by group`. Establish `e` using `hI v s⁻¹ (inv_mem hs) (by rw [map_inv, map_inv, hη, inv_one]) a.rev`. Rewrite `e` using `[map_inv (F.loc v)]`. Use `hconj a g' (F.c * F.loc v s * F.c⁻¹) hg (by simp [hη]) (e0 ▸ h) (by` as an intermediate fact. Rewrite using `[de_c r _ _ hr.norm.atc ((hr.mult _).trans hF.ηc) ((hr.mult _).trans hη), de_c ρ _ _ hρ.norm.atc ((hρ.mult _).trans hF.ηc) ((hρ.mult _).trans hη), e])`.

Rewrite using `[show (⟨_, h⟩ : F.η.ker) = ⟨_, e0 ▸ h⟩ from Subtype.ext e0, this, map_one])`. Use `congrArg Units.val (DFunLike.congr_fun hχ g)` as an intermediate fact. Rewrite using `[← Ideal.Quotient.eq]`. Conclude with `this`. Break down `hsplit g with hg | ⟨g', hg, rfl⟩` into its components or cases.

Conclude with `hker ⟨g, hg⟩`. Rewrite using `[de_mul' r _ _ ((hr.mult _).trans hg), de_mul' ρ _ _ ((hρ.mult _).trans hg), hr.norm.atc, hρ.norm.atc, Matrix.mul_one, Matrix.mul_one]`. Conclude with `hker ⟨g', hg⟩`.
-/
private theorem de_core {O R G Γ ι : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra O R] [IsLocalHom (algebraMap O R)] [Group G]
    [TopologicalSpace G]
    [IsTopologicalGroup G] [Group Γ] [TopologicalSpace Γ] (F : Frame O G Γ ι) (hF : F.Ok) (hC : F.Cl1) (g₁ : Γ)
    (r ρ : Γ →* GG 3 R) (hr : F.IsPt g₁ r) (hρ : F.IsPt g₁ ρ) (hd : Upper F.η r ∨ Lower F.η r)
    (hd' : Upper F.η ρ ∨ Lower F.η ρ) (g : Γ) (a : Fin 3) : (r g).mat a a = (ρ g).mat a a := by
  classical
  let u : Fin 3 → (F.η.ker →* Rˣ) := fun a =>
    (kap F.η r hr.mult hd a).toHomUnits / (kap F.η ρ hρ.mult hd' a).toHomUnits
  have hu : ∀ a (g : F.η.ker), (u a g : R) * (ρ g).mat a a = (r g).mat a a := fun a g => by
    show (((kap F.η r hr.mult hd a).toHomUnits g / (kap F.η ρ hρ.mult hd' a).toHomUnits g : Rˣ) : R) *
      (((kap F.η ρ hρ.mult hd' a).toHomUnits g : Rˣ) : R) = ((kap F.η r hr.mult hd a).toHomUnits g : Rˣ)
    rw [← Units.val_mul, div_mul_cancel]
  have hun : ∀ a (g : F.η.ker), IsUnit ((ρ g).mat a a) := fun a g =>
    ((kap F.η ρ hρ.mult hd' a).toHomUnits g).isUnit
  have h1 : ∀ (g : F.η.ker) a, (r g).mat a a = (ρ g).mat a a → u a g = 1 := fun g a e => by
    apply Units.ext
    apply (hun a g).mul_right_cancel
    rw [hu, e, Units.val_one, one_mul]
  have h2' : ∀ (g : F.η.ker) a, u a g = 1 → (r g).mat a a = (ρ g).mat a a := fun g a e => by
    rw [← hu, e, Units.val_one, one_mul]
  have hI : ∀ v (s : F.D v), s ∈ F.Iv v → F.η (F.loc v s) = 1 → ∀ a,
      (r (F.loc v s)).mat a a = (ρ (F.loc v s)).mat a a := by
    intro v s hs hη a
    by_cases hv : v ∈ F.Tb
    · have key : ∀ r : Γ →* GG 3 R, F.IsPt g₁ r → (Upper F.η r ∨ Lower F.η r) →
          (r (F.loc v s)).mat a a = algebraMap O R (psi (F.Ψv v) a s) := by
        intro r hr hd
        refine de_ine (η := F.ηv v) (Ψ := F.Ψv v) (I := F.Iv v) (r := r.comp (F.loc v))
          ⟨fun g => hr.mult (F.loc v g), fun g => hr.red (F.loc v g)⟩
          (hd.imp (fun H g hg => H (F.loc v g) hg) fun H g hg => H (F.loc v g) hg) (hF.x v hv) ?_ s hs hη a
        rcases hv with hv | hv
        · exact (hr.loc v).1 hv
        · obtain ⟨h, hh, hD⟩ := (hr.loc v).2.1 hv
          exact ⟨h, hh, hD.toTriIn⟩
      exact (key r hr hd).trans (key ρ hρ hd').symm
    · haveI := Fintype.ofFinite (ResidueField O)
      have hmem : s ^ Fintype.card (ResidueField O)ˣ ∈ F.Nv v := by
        refine ⟨⟨pow_mem hs _, pow_mem (show s ∈ (F.ηv v).ker from hη) _⟩, ?_⟩
        show ((Units.map (residue O).toMonoidHom).comp (F.Ψv v)) _ = 1
        rw [map_pow, pow_card_eq_one]
      have hN : IsUnit ((Fintype.card (ResidueField O)ˣ : ℕ) : O) := by
        rw [← residue_ne_zero_iff_isUnit, map_natCast, Fintype.card_units,
          Nat.cast_sub Fintype.card_pos, FiniteField.cast_card_eq_zero]
        simp
      refine h2' ⟨_, hη⟩ a (unit_eq_one_of_pow_eq_one_of_residue_one _ (Fintype.card (ResidueField O)ˣ)
        (by simpa using hN.map (algebraMap O R)) ?_ ?_)
      · have e1 := hr.red (F.loc v s) a a
        have e2 := hρ.red (F.loc v s) a a
        have e3 := sub_mem e1 e2
        rw [Matrix.sub_apply, Matrix.sub_apply, sub_sub_sub_cancel_right] at e3
        have e4 := hu a ⟨_, hη⟩
        rw [← Ideal.mul_unit_mem_iff_mem _ (hun a ⟨_, hη⟩), sub_mul, e4, one_mul]
        exact e3
      · rw [← map_pow]
        refine h1 _ a ?_
        have e1 := (hr.loc v).2.2 hv _ hmem
        have e2 := (hρ.loc v).2.2 hv _ hmem
        rw [MonoidHom.comp_apply, map_pow (F.loc v)] at e1 e2
        exact congrArg (fun y : GG 3 R => y.mat a a) (e1.trans e2.symm)
  have hsplit : ∀ g, F.η g = 1 ∨ ∃ g', F.η g' = 1 ∧ g = g' * F.c := fun g => by
    rcases Int.units_eq_one_or (F.η g) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨g * F.c, by simp [h, hF.ηc], by rw [mul_assoc, hF.csq, mul_one]⟩
  have hconj : ∀ a (g x : Γ) (hg : F.η g = 1) (hx : F.η x = 1) (h : g * x * g⁻¹ ∈ F.η.ker),
      (r x).mat a a = (ρ x).mat a a → u a ⟨_, h⟩ = 1 := by
    intro a g x hg hx h e
    have : (⟨_, h⟩ : F.η.ker) = ⟨g, hg⟩ * ⟨x, hx⟩ * ⟨g, hg⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, h1 ⟨x, hx⟩ a e, map_inv, mul_one, mul_inv_cancel]
  have hker : ∀ g : F.η.ker, (r g).mat a a = (ρ g).mat a a := by
    intro g
    refine h2' g a (Units.ext ?_)
    rw [← sub_eq_zero, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) Ideal.IsPrime.ne_top',
      Submodule.mem_iInf]
    intro n
    let q : R →* R ⧸ maximalIdeal R ^ n := (Ideal.Quotient.mk (maximalIdeal R ^ n)).toMonoidHom
    have lc : ∀ (r : Γ →* GG 3 R) (hr : F.IsPt g₁ r) (hd : Upper F.η r ∨ Lower F.η r),
        IsLocallyConstant fun g => Units.map q ((kap F.η r hr.mult hd a).toHomUnits g) := fun r hr hd =>
      IsLocallyConstant.desc _ Units.val
        (((hr.cont n).comp fun X => X a a).comp_continuous continuous_subtype_val) Units.val_injective
    have hχ := hC _ ((Units.map q).comp (u a)) (by
      have := (lc r hr hd).div (lc ρ hρ hd')
      convert this using 1
      funext g
      exact map_div (Units.map q) _ _) (by
      intro v s g h hs
      have hη : F.η (F.loc v s) = 1 := by
        have : F.η (g * F.loc v s * g⁻¹) = 1 := h
        rwa [map_mul, map_mul, map_inv, mul_inv_cancel_comm] at this
      rw [MonoidHom.comp_apply]
      rcases hsplit g with hg | ⟨g', hg, rfl⟩
      · rw [hconj a g _ hg hη h (hI v s hs hη a), map_one]
      · have e0 : g' * F.c * F.loc v s * (g' * F.c)⁻¹ = g' * (F.c * F.loc v s * F.c⁻¹) * g'⁻¹ := by group
        have e := hI v s⁻¹ (inv_mem hs) (by rw [map_inv, map_inv, hη, inv_one]) a.rev
        rw [map_inv (F.loc v)] at e
        have := hconj a g' (F.c * F.loc v s * F.c⁻¹) hg (by simp [hη]) (e0 ▸ h) (by
          rw [de_c r _ _ hr.norm.atc ((hr.mult _).trans hF.ηc) ((hr.mult _).trans hη),
            de_c ρ _ _ hρ.norm.atc ((hρ.mult _).trans hF.ηc) ((hρ.mult _).trans hη), e])
        rw [show (⟨_, h⟩ : F.η.ker) = ⟨_, e0 ▸ h⟩ from Subtype.ext e0, this, map_one])
    have := congrArg Units.val (DFunLike.congr_fun hχ g)
    rw [← Ideal.Quotient.eq]
    exact this
  rcases hsplit g with hg | ⟨g', hg, rfl⟩
  · exact hker ⟨g, hg⟩
  · rw [de_mul' r _ _ ((hr.mult _).trans hg), de_mul' ρ _ _ ((hρ.mult _).trans hg), hr.norm.atc, hρ.norm.atc,
      Matrix.mul_one, Matrix.mul_one]
    exact hker ⟨g', hg⟩

end UpperTheory.V.UnitaryThreeInertia

/- English proof (translation)
Introduce `O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF hC g₁ _ A _ _ _ _ _ _ r hp hT g a`. Use `de_core F hF hC g₁ r (F.rz A) hp (isPt_rz F hF g₁) hT (Or.inl fun g _ a b hab => ?_) g a` and prove the remaining obligations. Establish `hne : a ≠ b`. Introduce and unpack `rfl`. Conclude with `hab.ne (sub_self _)`.

Use `show algebraMap O A (((tor O (F.Ψ g) : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) a b) = 0`. Rewrite using `[tor_val, Matrix.diagonal_apply_ne _ hne, map_zero]`.
-/
theorem UpperTheory.V.UnitaryThreeInertia.diag_eq_of_tri :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.Cl1 → ∀ g₁, F.Marked g₁ → ∀ {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [Algebra O A] [IsLocalHom (algebraMap O A)] (r : Γ →* GG 3 A), F.IsPt g₁ r →
      Upper F.η r ∨ Lower F.η r → ∀ g a, (r g).mat a a = (F.rz A g).mat a a := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF hC g₁ _ A _ _ _ _ _ _ r hp hT g a
  refine de_core F hF hC g₁ r (F.rz A) hp (isPt_rz F hF g₁) hT (Or.inl fun g _ a b hab => ?_) g a
  have hne : a ≠ b := by
    rintro rfl
    exact hab.ne (sub_self _)
  show algebraMap O A (((tor O (F.Ψ g) : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) a b) = 0
  rw [tor_val, Matrix.diagonal_apply_ne _ hne, map_zero]

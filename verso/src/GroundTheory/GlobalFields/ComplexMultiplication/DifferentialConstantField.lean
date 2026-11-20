import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialBaseChange

namespace GroundTheory.Global

open Polynomial KaehlerDifferential GroundTheory.Arith.Abelian IntermediateField

universe u

variable {F : Type u} [Field F]

section Descent

variable (E : WeierstrassCurve F) [E.IsElliptic]

/- English proof (translation)
Use `set F₁ := F⟮genX E⟯`. Establish `hfin : FiniteDimensional F₁ E.toAffine.FunctionField` using `Module.finite_of_finrank_pos (by rw [finrank_adjoin_genX E]; norm_num)`. Establish `hint : IsIntegral F₁ (genY E)` using `Algebra.IsIntegral.isIntegral _`. Establish `htop : F₁⟮genY E⟯ = ⊤`. Rewrite using `[← IntermediateField.restrictScalars_eq_top_iff (K := F), IntermediateField.adjoin_simple_adjoin_simple]`.

Conclude with `adjoin_genX_genY E`. Establish `hdeg : (minpoly F₁ (genY E)).natDegree = 2`. Rewrite using `[← IntermediateField.adjoin.finrank hint, htop, IntermediateField.finrank_top', finrank_adjoin_genX E]`. Establish `hc : c ∈ (F₁⟮genY E⟯).toSubalgebra` using `by rw [htop]; trivial`. Rewrite `hc` using `[IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, Algebra.adjoin_singleton_eq_range_aeval]`.

Take `⟨p, rfl⟩` from `hc`. Establish `hm1 : minpoly F₁ (genY E) ≠ 1` using `fun h => by rw [h, natDegree_one] at hdeg; omega`. Establish `hq : (p %ₘ minpoly F₁ (genY E)).natDegree ≤ 1`. Use `natDegree_modByMonic_lt p (minpoly.monic hint) hm1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hval : aeval (genY E) p = aeval (genY E) (p %ₘ minpoly F₁ (genY E))` using `(aeval_modByMonic_eq_self_of_root (minpoly.aeval F₁ (genY E))).symm`. Take `⟨q, hqdef⟩ : ∃ q, q = p %ₘ minpoly F₁ (genY E)` from `⟨_, rfl⟩`. Rewrite `hq`, `hval` using `[← hqdef]`. Use `⟨(q.coeff 0 : E.toAffine.FunctionField), (q.coeff 1 : E.toAffine.FunctionField), (q.coeff 0).2, (q.coeff 1).2, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `aeval (genY E) p = _`.

Rewrite using `[hval, eq_X_add_C_of_natDegree_le_one hq]`. Simplify using `only [map_add, map_mul, aeval_C, aeval_X, coeff_add, coeff_C_mul_X, coeff_C]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_eq_add_mul_genY (c : E.toAffine.FunctionField) :
    ∃ r s : E.toAffine.FunctionField, r ∈ F⟮genX E⟯ ∧ s ∈ F⟮genX E⟯ ∧ c = r + s * genY E := by
  set F₁ := F⟮genX E⟯
  have hfin : FiniteDimensional F₁ E.toAffine.FunctionField :=
    Module.finite_of_finrank_pos (by rw [finrank_adjoin_genX E]; norm_num)
  have hint : IsIntegral F₁ (genY E) := Algebra.IsIntegral.isIntegral _
  have htop : F₁⟮genY E⟯ = ⊤ := by
    rw [← IntermediateField.restrictScalars_eq_top_iff (K := F),
      IntermediateField.adjoin_simple_adjoin_simple]
    exact adjoin_genX_genY E
  have hdeg : (minpoly F₁ (genY E)).natDegree = 2 := by
    rw [← IntermediateField.adjoin.finrank hint, htop, IntermediateField.finrank_top',
      finrank_adjoin_genX E]
  have hc : c ∈ (F₁⟮genY E⟯).toSubalgebra := by rw [htop]; trivial
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hc
  obtain ⟨p, rfl⟩ := hc
  have hm1 : minpoly F₁ (genY E) ≠ 1 := fun h => by rw [h, natDegree_one] at hdeg; omega
  have hq : (p %ₘ minpoly F₁ (genY E)).natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt p (minpoly.monic hint) hm1
    omega
  have hval : aeval (genY E) p = aeval (genY E) (p %ₘ minpoly F₁ (genY E)) :=
    (aeval_modByMonic_eq_self_of_root (minpoly.aeval F₁ (genY E))).symm
  obtain ⟨q, hqdef⟩ : ∃ q, q = p %ₘ minpoly F₁ (genY E) := ⟨_, rfl⟩
  rw [← hqdef] at hq hval
  refine ⟨(q.coeff 0 : E.toAffine.FunctionField), (q.coeff 1 : E.toAffine.FunctionField),
    (q.coeff 0).2, (q.coeff 1).2, ?_⟩
  change aeval (genY E) p = _
  rw [hval, eq_X_add_C_of_natDegree_le_one hq]
  simp only [map_add, map_mul, aeval_C, aeval_X, coeff_add, coeff_C_mul_X, coeff_C]
  simp
  ring

variable {F' : Type u} [Field F'] [Algebra F F']

/- English proof (translation)
Use `set K' := (E.baseChange F').toAffine.FunctionField`. Establish `hinj : Function.Injective (bcEmb (F'` using `F') E) := (bcEmb (F' := F') E).toRingHom.injective`. Establish `hmap : ∀ w ∈ F⟮genX E⟯, bcEmb (F'` using `F') E w ∈ F'⟮genX (E.baseChange F')⟯ := by`. Introduce `w hw`. Proceed by induction on `hw using IntermediateField.adjoin_induction with`.

Consider the case `mem x hx => rw [Set.mem_singleton_iff.mp hx, bcEmb_genX]`. Conclude with `mem_adjoin_simple_self F' _`. Consider the case `algebraMap x`. Rewrite using `[AlgHom.commutes, IsScalarTower.algebraMap_apply F F' K']`. Conclude with `IntermediateField.algebraMap_mem _ _`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `inv x _ hx => rw [map_inv₀]`. Conclude with `inv_mem hx`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`.

Conclude with `mul_mem hx hy`. Take `⟨r, s, hr, hs, rfl⟩` from `exists_eq_add_mul_genY E c`. Rewrite `h` using `[map_add, map_mul, bcEmb_genY]`. Establish `hs0 : bcEmb (F'` using `F') E s = 0 := by`. Assume the negation of the conclusion as `hne`.

Apply `genY_not_mem (E.baseChange F')` to reduce the goal to its premises. Establish `e : genY (E.baseChange F') = (algebraMap F' K' a - bcEmb (F'` using `F') E r) / bcEmb (F' := F') E s := by`. Rewrite using `[eq_div_iff hne]`. Take the linear combination `h`. Rewrite using `[e]`.

Conclude with `div_mem (sub_mem (IntermediateField.algebraMap_mem _ a) (hmap r hr)) (hmap s hs)`. Establish `hs00 : s = 0` using `hinj (by rw [hs0, map_zero])`. Rewrite `h` using `[hs0, zero_mul, add_zero]`. Rewrite using `[hs00, zero_mul, add_zero]`. Take `⟨p, q, rfl⟩` from `(mem_adjoin_simple_iff F r).mp hr`.

Distinguish the cases in `hq0 : aeval (genX E) q = 0`. Conclude with `⟨0, by rw [hq0, div_zero, map_zero]⟩`. Establish `hq : q ≠ 0` using `fun h0 => hq0 (by rw [h0, map_zero])`. Establish `hq0' : aeval (genX (E.baseChange F')) q ≠ 0`. Rewrite using `[← bcEmb_genX, aeval_algHom_apply]`.

Conclude with `fun h0 => hq0 (hinj (by rw [h0, map_zero]))`. Rewrite `h` using `[map_div₀, ← aeval_algHom_apply, ← aeval_algHom_apply, bcEmb_genX, div_eq_iff hq0']`. Establish `key : aeval (genX (E.baseChange F')) (p.map (algebraMap F F') - C a * q.map (algebraMap F F')) = 0`. Rewrite using `[map_sub, map_mul, aeval_C, aeval_map_algebraMap, aeval_map_algebraMap]`. Take the linear combination `h`.

Rewrite `key` using `[aeval_genX_eq_zero_iff]`. Establish `hcoeff : ∀ j, algebraMap F F' (p.coeff j) = a * algebraMap F F' (q.coeff j)`. Introduce `j`. Use `congrArg (coeff · j) key` as an intermediate fact. Simplify using `only [coeff_sub, coeff_map, coeff_C_mul, coeff_zero] at this`.

Take the linear combination `this`. Establish `hqi : q.coeff q.natDegree ≠ 0` using `leadingCoeff_ne_zero.mpr hq`. Take `⟨a₀, ha₀⟩ : ∃ a₀ : F, a₀ = p.coeff q.natDegree / q.coeff q.natDegree` from `⟨_, rfl⟩`. Establish `ha : a = algebraMap F F' a₀`. Rewrite using `[ha₀, map_div₀, hcoeff, mul_div_cancel_right₀ _ ((_root_.map_ne_zero _).mpr hqi)]`.

Establish `hp : p = C a₀ * q`. Use extensionality with `j`. Apply `(algebraMap F F').injective` to reduce the goal to its premises. Rewrite using `[coeff_C_mul, map_mul, hcoeff j, ← ha]`. Use `⟨a₀, ?_⟩` and prove the remaining obligations.

Rewrite using `[hp, map_mul, aeval_C, mul_div_cancel_right₀ _ hq0]`.
-/
theorem exists_algebraMap_eq_of_bcEmb {c : E.toAffine.FunctionField} {a : F'}
    (h : bcEmb (F' := F') E c = algebraMap F' (E.baseChange F').toAffine.FunctionField a) :
    ∃ a₀ : F, algebraMap F E.toAffine.FunctionField a₀ = c := by
  set K' := (E.baseChange F').toAffine.FunctionField
  have hinj : Function.Injective (bcEmb (F' := F') E) := (bcEmb (F' := F') E).toRingHom.injective
  have hmap : ∀ w ∈ F⟮genX E⟯, bcEmb (F' := F') E w ∈ F'⟮genX (E.baseChange F')⟯ := by
    intro w hw
    induction hw using IntermediateField.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.mp hx, bcEmb_genX]; exact mem_adjoin_simple_self F' _
    | algebraMap x =>
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F F' K']
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  obtain ⟨r, s, hr, hs, rfl⟩ := exists_eq_add_mul_genY E c
  rw [map_add, map_mul, bcEmb_genY] at h
  have hs0 : bcEmb (F' := F') E s = 0 := by
    by_contra hne
    apply genY_not_mem (E.baseChange F')
    have e : genY (E.baseChange F') =
        (algebraMap F' K' a - bcEmb (F' := F') E r) / bcEmb (F' := F') E s := by
      rw [eq_div_iff hne]; linear_combination h
    rw [e]
    exact div_mem (sub_mem (IntermediateField.algebraMap_mem _ a) (hmap r hr)) (hmap s hs)
  have hs00 : s = 0 := hinj (by rw [hs0, map_zero])
  rw [hs0, zero_mul, add_zero] at h
  rw [hs00, zero_mul, add_zero]
  obtain ⟨p, q, rfl⟩ := (mem_adjoin_simple_iff F r).mp hr
  by_cases hq0 : aeval (genX E) q = 0
  · exact ⟨0, by rw [hq0, div_zero, map_zero]⟩
  have hq : q ≠ 0 := fun h0 => hq0 (by rw [h0, map_zero])
  have hq0' : aeval (genX (E.baseChange F')) q ≠ 0 := by
    rw [← bcEmb_genX, aeval_algHom_apply]
    exact fun h0 => hq0 (hinj (by rw [h0, map_zero]))
  rw [map_div₀, ← aeval_algHom_apply, ← aeval_algHom_apply, bcEmb_genX, div_eq_iff hq0'] at h
  have key : aeval (genX (E.baseChange F'))
      (p.map (algebraMap F F') - C a * q.map (algebraMap F F')) = 0 := by
    rw [map_sub, map_mul, aeval_C, aeval_map_algebraMap, aeval_map_algebraMap]
    linear_combination h
  rw [aeval_genX_eq_zero_iff] at key
  have hcoeff : ∀ j, algebraMap F F' (p.coeff j) = a * algebraMap F F' (q.coeff j) := by
    intro j
    have := congrArg (coeff · j) key
    simp only [coeff_sub, coeff_map, coeff_C_mul, coeff_zero] at this
    linear_combination this
  have hqi : q.coeff q.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hq
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : F, a₀ = p.coeff q.natDegree / q.coeff q.natDegree := ⟨_, rfl⟩
  have ha : a = algebraMap F F' a₀ := by
    rw [ha₀, map_div₀, hcoeff, mul_div_cancel_right₀ _ ((_root_.map_ne_zero _).mpr hqi)]
  have hp : p = C a₀ * q := by
    ext j
    apply (algebraMap F F').injective
    rw [coeff_C_mul, map_mul, hcoeff j, ← ha]
  refine ⟨a₀, ?_⟩
  rw [hp, map_mul, aeval_C, mul_div_cancel_right₀ _ hq0]

end Descent

section Constant

variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

/- English proof (translation)
Take `⟨b, hb⟩` from `exists_isogCoeff_eq_algebraMap (isogBaseChange (F' := AlgebraicClosure F) φ)`. Rewrite `hb` using `[isogCoeff_isogBaseChange]`. Conclude with `exists_algebraMap_eq_of_bcEmb E hb.symm`.
-/
theorem exists_algebraMap_eq_isogCoeff (φ : Isogeny E E') :
    ∃ a : F, algebraMap F E.toAffine.FunctionField a = isogCoeff φ := by
  classical
  obtain ⟨b, hb⟩ := exists_isogCoeff_eq_algebraMap
    (isogBaseChange (F' := AlgebraicClosure F) φ)
  rw [isogCoeff_isogBaseChange] at hb
  exact exists_algebraMap_eq_of_bcEmb E hb.symm

noncomputable def invConst (φ : Isogeny E E') : F :=
  (exists_algebraMap_eq_isogCoeff φ).choose

/- English proof (translation)
The claim follows from `(exists_algebraMap_eq_isogCoeff φ).choose_spec`.
-/
theorem algebraMap_invConst (φ : Isogeny E E') :
    algebraMap F E.toAffine.FunctionField (invConst φ) = isogCoeff φ :=
  (exists_algebraMap_eq_isogCoeff φ).choose_spec

/- English proof (translation)
Rewrite using `[isogenyPullback_invariantDifferential_eq_smul, ← algebraMap_invConst, algebraMap_smul]`.
-/
theorem isogenyPullback_eq_invConst_smul (φ : Isogeny E E') :
    isogenyPullback φ (invariantDifferential E') = invConst φ • invariantDifferential E := by
  rw [isogenyPullback_invariantDifferential_eq_smul, ← algebraMap_invConst, algebraMap_smul]

/- English proof (translation)
The claim follows from `(algebraMap F E.toAffine.FunctionField).injective (by rw [map_add, algebraMap_invConst, algebraMap_invConst, algebraMap_invConst, isogCoeff_add h])`.
-/
theorem invConst_add {φ ψ χ : Isogeny E E'} (h : χ.1 = φ.1 + ψ.1) :
    invConst χ = invConst φ + invConst ψ :=
  (algebraMap F E.toAffine.FunctionField).injective (by
    rw [map_add, algebraMap_invConst, algebraMap_invConst, algebraMap_invConst, isogCoeff_add h])

variable (E) in

/- English proof (translation)
The claim follows from `(algebraMap F E.toAffine.FunctionField).injective (by rw [algebraMap_invConst, isogCoeff_mulIsogeny, map_intCast])`.
-/
theorem invConst_mulIsogeny (n : ℤ) (hn : n ≠ 0) : invConst (mulIsogeny E n hn) = n :=
  (algebraMap F E.toAffine.FunctionField).injective (by
    rw [algebraMap_invConst, isogCoeff_mulIsogeny, map_intCast])

/- English proof (translation)
Rewrite using `[isSeparable_iff_isogCoeff_ne_zero, ← algebraMap_invConst, ne_eq, ne_eq, map_eq_zero_iff _ (algebraMap F E.toAffine.FunctionField).injective]`.
-/
theorem isSeparable_iff_invConst_ne_zero (φ : Isogeny E E') :
    φ.IsSeparable ↔ invConst φ ≠ 0 := by
  rw [isSeparable_iff_isogCoeff_ne_zero, ← algebraMap_invConst, ne_eq, ne_eq,
    map_eq_zero_iff _ (algebraMap F E.toAffine.FunctionField).injective]

/- English proof (translation)
The claim follows from `(algebraMap F' (E.baseChange F').toAffine.FunctionField).injective (by rw [algebraMap_invConst, isogCoeff_isogBaseChange, ← algebraMap_invConst, AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (E.baseChange F').toAffine.FunctionField])`.
-/
theorem invConst_isogBaseChange {F' : Type u} [Field F'] [Algebra F F'] [DecidableEq F']
    (φ : Isogeny E E') :
    invConst (isogBaseChange (F' := F') φ) = algebraMap F F' (invConst φ) :=
  (algebraMap F' (E.baseChange F').toAffine.FunctionField).injective (by
    rw [algebraMap_invConst, isogCoeff_isogBaseChange, ← algebraMap_invConst, AlgHom.commutes,
      IsScalarTower.algebraMap_apply F F' (E.baseChange F').toAffine.FunctionField])

end Constant

end GroundTheory.Global

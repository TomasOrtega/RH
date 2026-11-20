import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.FibreStC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.EqZeroOfSecTraceMulEqZero

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module

variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}

/- English proof (translation)
Introduce `hk`. Establish `hmem : (MvPolynomial.X k : MvPolynomial ι ℤ) ∈ coordIdeal ℤ y`. Rewrite using `[coordIdeal, RingHom.mem_ker, coneMap]`. Simplify using `[hk]`. Rewrite `hmem` using `[h, Ideal.mem_bot]`.

Conclude with `MvPolynomial.X_ne_zero k hmem`.
-/
theorem coord_ne_zero {ι : Type*} (y : ι → Ω) (h : coordIdeal ℤ y = ⊥) (k : ι) : y k ≠ 0 := by
  intro hk
  have hmem : (MvPolynomial.X k : MvPolynomial ι ℤ) ∈ coordIdeal ℤ y := by
    rw [coordIdeal, RingHom.mem_ker, coneMap]
    simp [hk]
  rw [h, Ideal.mem_bot] at hmem
  exact MvPolynomial.X_ne_zero k hmem

/- English proof (translation)
Conclude with `IntermediateField.subset_adjoin ℚ {t | ∃ i j, t = x i / x j} ⟨i, j, rfl⟩`.
-/
theorem div_mem_fnField (x : κ → Ω) (i j : κ) : x i / x j ∈ fnField x := by
  exact IntermediateField.subset_adjoin ℚ {t | ∃ i j, t = x i / x j} ⟨i, j, rfl⟩

/- English proof (translation)
Rewrite using `[deh_apply]`. Proceed by induction on `m using MvPolynomial.induction_on`. Rewrite using `[MvPolynomial.eval₂_C]`. Simplify using `using intCast_mem (fnField y) _`. Rewrite using `[MvPolynomial.eval₂_add]`.

Conclude with `add_mem ‹_› ‹_›`. Rewrite using `[MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]`. Conclude with `mul_mem ‹_› (div_mem_fnField y _ i₀)`.
-/
theorem deh_mem_fnField {ι : Type*} (y : ι → Ω) (i₀ : ι) (m : MvPolynomial ι ℤ) :
    deh y i₀ m ∈ fnField y := by
  rw [deh_apply]
  induction m using MvPolynomial.induction_on
  · rw [MvPolynomial.eval₂_C]
    simpa using intCast_mem (fnField y) _
  · rw [MvPolynomial.eval₂_add]
    exact add_mem ‹_› ‹_›
  · rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    exact mul_mem ‹_› (div_mem_fnField y _ i₀)

def dehK (y : Fin (D + 1) → Ω) : MvPolynomial (Fin (D + 1)) ℤ →+* fnField y :=
  (deh y 0).codRestrict (fnField y).toSubfield.toSubring fun m => deh_mem_fnField y 0 m

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_dehK (y : Fin (D + 1) → Ω) (m : MvPolynomial (Fin (D + 1)) ℤ) :
    ((dehK y m : fnField y) : Ω) = deh y 0 m := rfl

def chartGen (y : Fin (D + 1) → Ω) (k : {k : Fin (D + 1) // k ≠ 0}) : fnField y :=
  ⟨y k / y 0, div_mem_fnField y k 0⟩

def chartRing (y : Fin (D + 1) → Ω) : Subalgebra ℤ (fnField y) :=
  Algebra.adjoin ℤ (Set.range (chartGen y))

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a => simp [deh_apply]`. Consider the case `add p q hp hq => simp only [map_add, AddMemClass.coe_add, hp, hq]`. Consider the case `mul_X p i hp`. Simplify using `only [map_mul, MvPolynomial.aeval_X, MvPolynomial.rename_X, MulMemClass.coe_mul, hp]`.

Use `congr 1`. Simplify using `[deh_apply, chartGen]`.
-/
theorem aeval_chartGen (y : Fin (D + 1) → Ω) (g : MvPolynomial {k : Fin (D + 1) // k ≠ 0} ℤ) :
    ((MvPolynomial.aeval (chartGen y) g : fnField y) : Ω) =
      deh y 0 (MvPolynomial.rename Subtype.val g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [deh_apply]
  | add p q hp hq => simp only [map_add, AddMemClass.coe_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.rename_X, MulMemClass.coe_mul, hp]
    congr 1
    simp [deh_apply, chartGen]

/- English proof (translation)
Rewrite using `[algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]`. Introduce `g hg`. Establish `hy0` using `coord_ne_zero y hfree 0`. Use `set G := MvPolynomial.rename Subtype.val g`. Establish `h1 : deh y 0 G = 0`.

Rewrite using `[← aeval_chartGen]`. Express the relevant statement in the definitionally equal form `(((MvPolynomial.aeval (chartGen y) g : fnField y)) : Ω) = 0`. Rewrite using `[hg]`. Both sides reduce to the same expression. Establish `hH` using `homog_isHomogeneous (0 : Fin (D + 1)) G le_rfl`.

Establish `h2 : MvPolynomial.aeval y (homog 0 G.totalDegree G) = 0`. Rewrite using `[MvPolynomial.aeval_def, algebraMap_int_eq, eval₂_homog y 0 hy0 G le_rfl, h1, mul_zero]`. Establish `h3` using `mem_coordIdeal_of_isHomogeneous ℤ y hH h2`. Rewrite `h3` using `[hfree, Ideal.mem_bot]`. Apply `MvPolynomial.funext` to reduce the goal to its premises.

Introduce `u`. Set `v : Fin (D + 1) → ℚ` to `fun k => if h : k = 0 then 1 else (u ⟨k, h⟩ : ℚ)`. Establish `h4` using `eval₂_homog v 0 (by simp [v]) G le_rfl`. Rewrite `h4` using `[h3, MvPolynomial.eval₂_zero]`. Establish `h5 : deh v 0 G = ((MvPolynomial.eval u g : ℤ) : ℚ)`.

Rewrite using `[deh_apply, MvPolynomial.eval₂_rename, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, ← eq_intCast (Int.castRingHom ℚ), MvPolynomial.eval₂_comp_left]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Simplify using `[v, k.2]`. Rewrite `h4` using `[h5]`.

Establish `h6 : ((MvPolynomial.eval u g : ℤ) : ℚ) = 0`. Use `h4.symm` as an intermediate fact. Rewrite `this` using `[mul_eq_zero, or_iff_right (pow_ne_zero _ (by simp [v]))]`. Then use the resulting hypothesis. Simplify using `using h6`.
-/
theorem chartGen_indep (y : Fin (D + 1) → Ω) (hfree : coordIdeal ℤ y = ⊥) :
    AlgebraicIndependent ℤ (chartGen y) := by
  classical
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro g hg
  have hy0 := coord_ne_zero y hfree 0
  set G := MvPolynomial.rename Subtype.val g
  have h1 : deh y 0 G = 0 := by
    rw [← aeval_chartGen]
    change (((MvPolynomial.aeval (chartGen y) g : fnField y)) : Ω) = 0
    rw [hg]; rfl
  have hH := homog_isHomogeneous (0 : Fin (D + 1)) G le_rfl
  have h2 : MvPolynomial.aeval y (homog 0 G.totalDegree G) = 0 := by
    rw [MvPolynomial.aeval_def, algebraMap_int_eq, eval₂_homog y 0 hy0 G le_rfl, h1, mul_zero]
  have h3 := mem_coordIdeal_of_isHomogeneous ℤ y hH h2
  rw [hfree, Ideal.mem_bot] at h3
  apply MvPolynomial.funext
  intro u
  let v : Fin (D + 1) → ℚ := fun k => if h : k = 0 then 1 else (u ⟨k, h⟩ : ℚ)
  have h4 := eval₂_homog v 0 (by simp [v]) G le_rfl
  rw [h3, MvPolynomial.eval₂_zero] at h4
  have h5 : deh v 0 G = ((MvPolynomial.eval u g : ℤ) : ℚ) := by
    rw [deh_apply, MvPolynomial.eval₂_rename, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
      ← eq_intCast (Int.castRingHom ℚ), MvPolynomial.eval₂_comp_left]
    congr 1
    funext k
    simp [v, k.2]
  rw [h5] at h4
  have h6 : ((MvPolynomial.eval u g : ℤ) : ℚ) = 0 := by
    have := h4.symm
    rwa [mul_eq_zero, or_iff_right (pow_ne_zero _ (by simp [v]))] at this
  simpa using h6

/- English proof (translation)
Establish `hind` using `chartGen_indep y hfree`. Use `haveI : UniqueFactorizationMonoid (chartRing y) := MulEquiv.uniqueFactorizationMonoid hind.aevalEquiv.toRingEquiv.toMulEquiv inferInstance`. Use `haveI : IsDomain (chartRing y) := Subalgebra.isDomain _`. Conclude with `UniqueFactorizationMonoid.instIsIntegrallyClosed`.
-/
theorem chartRing_closed (y : Fin (D + 1) → Ω) (hfree : coordIdeal ℤ y = ⊥) :
    IsIntegrallyClosed (chartRing y) := by
  have hind := chartGen_indep y hfree
  haveI : UniqueFactorizationMonoid (chartRing y) :=
    MulEquiv.uniqueFactorizationMonoid hind.aevalEquiv.toRingEquiv.toMulEquiv inferInstance
  haveI : IsDomain (chartRing y) := Subalgebra.isDomain _
  exact UniqueFactorizationMonoid.instIsIntegrallyClosed

/- English proof (translation)
Establish `hl : y 0 ≠ 0` using `coord_ne_zero y hfree 0`. Use `IsFractionRing.of_field _ _ fun z => ?_` and prove the remaining obligations. Establish `hinj : Function.Injective (algebraMap (chartRing y) Ω)`. Introduce `a b hab`. Conclude with `Subtype.val_injective (Subtype.val_injective hab)`.

Set `F : Subfield Ω` to `(IsFractionRing.lift (K := FractionRing (chartRing y)) hinj).fieldRange`. Establish `hgen : ∀ i, y i / y 0 ∈ F`. Introduce `i`. Distinguish the cases in `hi : i = 0`. Substitute `hi` using the available equality.

Rewrite using `[div_self hl]`. Conclude with `F.one_mem`. Use `⟨algebraMap (chartRing y) (FractionRing (chartRing y)) ⟨chartGen y ⟨i, hi⟩, Algebra.subset_adjoin ⟨_, rfl⟩⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[IsFractionRing.lift_algebraMap hinj]`. Both sides reduce to the same expression.

Establish `hle : (fnField y).toSubfield ≤ F`. Unfold `fnField`. Use `IntermediateField.adjoin_le_subfield ℚ _ ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨q, rfl⟩`. Rewrite using `[eq_ratCast]`.

Conclude with `SubfieldClass.ratCast_mem F q`. Introduce and unpack `_ ⟨i, j, rfl⟩`. Establish `: y i / y j = (y i / y 0) / (y j / y 0)`. Rewrite using `[div_div_div_cancel_right₀ hl]`. Express the relevant statement in the definitionally equal form `y i / y j ∈ F`.

Rewrite using `[this]`. Conclude with `F.div_mem (hgen i) (hgen j)`. Take `⟨w, hw⟩` from `hle z.2`. Take `⟨a, b, _, rfl⟩` from `IsFractionRing.div_surjective (A := chartRing y) w`. Use `⟨a, b, Subtype.val_injective ?_⟩` and prove the remaining obligations.

Rewrite `hw` using `[map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap]`. Rewrite using `[← hw]`. Conclude with `(map_div₀ (fnField y).val _ _).symm`.
-/
theorem chartRing_frac (y : Fin (D + 1) → Ω) (hfree : coordIdeal ℤ y = ⊥) :
    IsFractionRing (chartRing y) (fnField y) := by
  have hl : y 0 ≠ 0 := coord_ne_zero y hfree 0
  refine IsFractionRing.of_field _ _ fun z => ?_
  have hinj : Function.Injective (algebraMap (chartRing y) Ω) := by
    intro a b hab
    exact Subtype.val_injective (Subtype.val_injective hab)
  let F : Subfield Ω := (IsFractionRing.lift (K := FractionRing (chartRing y)) hinj).fieldRange
  have hgen : ∀ i, y i / y 0 ∈ F := by
    intro i
    by_cases hi : i = 0
    · subst hi; rw [div_self hl]; exact F.one_mem
    · refine ⟨algebraMap (chartRing y) (FractionRing (chartRing y))
        ⟨chartGen y ⟨i, hi⟩, Algebra.subset_adjoin ⟨_, rfl⟩⟩, ?_⟩
      rw [IsFractionRing.lift_algebraMap hinj]
      rfl
  have hle : (fnField y).toSubfield ≤ F := by
    unfold fnField
    refine IntermediateField.adjoin_le_subfield ℚ _ ?_ ?_
    · rintro _ ⟨q, rfl⟩
      rw [eq_ratCast]
      exact SubfieldClass.ratCast_mem F q
    · rintro _ ⟨i, j, rfl⟩
      have : y i / y j = (y i / y 0) / (y j / y 0) := by
        rw [div_div_div_cancel_right₀ hl]
      change y i / y j ∈ F
      rw [this]
      exact F.div_mem (hgen i) (hgen j)
  obtain ⟨w, hw⟩ := hle z.2
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := chartRing y) w
  refine ⟨a, b, Subtype.val_injective ?_⟩
  rw [map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap] at hw
  rw [← hw]
  exact (map_div₀ (fnField y).val _ _).symm

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module IntermediateField

variable {Ω : Type*} [Field Ω] [CharZero Ω] {ι : Type} [Fintype ι] {D : ℕ}

/- English proof (translation)
Use `set y := x ∘ e with hy`. Express the relevant statement in the definitionally equal form `IsIntegral _ (x i / y 0)`. Establish `hl : y 0 ≠ 0` using `coord_ne_zero y h.free 0`. Establish `hinj : Function.Injective (coneMap ℤ y)`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `f hf`. Establish `: f ∈ coordIdeal ℤ y` using `by rw [coordIdeal, RingHom.mem_ker]; exact hf`. Rewrite `this` using `[h.free, Ideal.mem_bot]`. Then use the resulting hypothesis. Set `eqv : MvPolynomial (Fin (D + 1)) ℤ ≃ₐ[ℤ] coneRing ℤ y` to `AlgEquiv.ofInjective (coneMap ℤ y) hinj`. Set `w : Fin (D + 1) → chartRing y` to `fun k => if hk : k = 0 then 1 else ⟨chartGen y ⟨k, hk⟩, Algebra.subset_adjoin ⟨_, rfl⟩⟩`.

Establish `hw : ∀ k, algebraMap (chartRing y) Ω (w k) = y k * (y 0)⁻¹`. Introduce `k`. Distinguish the cases in `hk : k = 0`. Substitute `hk` using the available equality. Simplify using `[w, mul_inv_cancel₀ hl]`.

Simplify using `only [w, dif_neg hk]`. Express the relevant statement in the definitionally equal form `y k / y 0 = _`. Conclude with `div_eq_mul_inv _ _`. Set `ψ : Polynomial Ω →+* Ω` to `Polynomial.evalRingHom (y 0)⁻¹`. Establish `hev : ∀ f : MvPolynomial (Fin (D + 1)) ℤ, ψ (coneMap ℤ y f) = MvPolynomial.aeval (fun k => y k * (y 0)⁻¹) f`.

Introduce `f`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [coneMap, ψ]`. Consider the case `add p q hp hq => rw [map_add, map_add, map_add, hp, hq]`. Consider the case `mul_X p k hp => rw [map_mul, map_mul, map_mul, hp]`.

Simplify using `[coneMap, ψ]`. Set `φ : coneRing ℤ y →+* chartRing y` to `(MvPolynomial.aeval w).toRingHom.comp eqv.symm.toAlgHom.toRingHom`. Establish `hrel : (algebraMap (chartRing y) Ω).comp φ = ψ.comp (algebraMap (coneRing ℤ y) _)`. Use extensionality with `r`. Take `⟨f, rfl⟩` from `eqv.surjective r`.

Establish `h1 : ((eqv f : coneRing ℤ y) : Polynomial Ω) = coneMap ℤ y f` using `rfl`. Express the relevant statement in the definitionally equal form `algebraMap _ Ω (MvPolynomial.aeval w (eqv.symm (eqv f))) = ψ ((eqv f : coneRing ℤ y) : Polynomial Ω)`. Rewrite using `[eqv.symm_apply_apply, h1, hev, ← MvPolynomial.aeval_algebraMap_apply, show (⇑(algebraMap (chartRing y) Ω) ∘ w) = fun k => y k * (y 0)⁻¹ from funext hw]`. Use `IsIntegral.map_of_comp_eq φ ψ hrel (h.integral i)` as an intermediate fact. Simplify `this` using `[ψ, div_eq_mul_inv]`.
-/
theorem coord_div_isIntegral (x : ι → Ω) (e : Fin (D + 1) → ι) (h : IsProjFrame x e) (i : ι) :
    IsIntegral (chartRing (x ∘ e)) (x i / x (e 0)) := by
  set y := x ∘ e with hy
  change IsIntegral _ (x i / y 0)
  have hl : y 0 ≠ 0 := coord_ne_zero y h.free 0
  have hinj : Function.Injective (coneMap ℤ y) := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    have : f ∈ coordIdeal ℤ y := by rw [coordIdeal, RingHom.mem_ker]; exact hf
    rwa [h.free, Ideal.mem_bot] at this
  let eqv : MvPolynomial (Fin (D + 1)) ℤ ≃ₐ[ℤ] coneRing ℤ y := AlgEquiv.ofInjective (coneMap ℤ y) hinj
  let w : Fin (D + 1) → chartRing y := fun k =>
    if hk : k = 0 then 1 else ⟨chartGen y ⟨k, hk⟩, Algebra.subset_adjoin ⟨_, rfl⟩⟩
  have hw : ∀ k, algebraMap (chartRing y) Ω (w k) = y k * (y 0)⁻¹ := by
    intro k
    by_cases hk : k = 0
    · subst hk; simp [w, mul_inv_cancel₀ hl]
    · simp only [w, dif_neg hk]
      change y k / y 0 = _
      exact div_eq_mul_inv _ _
  let ψ : Polynomial Ω →+* Ω := Polynomial.evalRingHom (y 0)⁻¹
  have hev : ∀ f : MvPolynomial (Fin (D + 1)) ℤ,
      ψ (coneMap ℤ y f) = MvPolynomial.aeval (fun k => y k * (y 0)⁻¹) f := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [coneMap, ψ]
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p k hp => rw [map_mul, map_mul, map_mul, hp]; simp [coneMap, ψ]
  let φ : coneRing ℤ y →+* chartRing y :=
    (MvPolynomial.aeval w).toRingHom.comp eqv.symm.toAlgHom.toRingHom
  have hrel : (algebraMap (chartRing y) Ω).comp φ = ψ.comp (algebraMap (coneRing ℤ y) _) := by
    ext r
    obtain ⟨f, rfl⟩ := eqv.surjective r
    have h1 : ((eqv f : coneRing ℤ y) : Polynomial Ω) = coneMap ℤ y f := rfl
    change algebraMap _ Ω (MvPolynomial.aeval w (eqv.symm (eqv f))) =
      ψ ((eqv f : coneRing ℤ y) : Polynomial Ω)
    rw [eqv.symm_apply_apply, h1, hev, ← MvPolynomial.aeval_algebraMap_apply,
      show (⇑(algebraMap (chartRing y) Ω) ∘ w) = fun k => y k * (y 0)⁻¹ from funext hw]
  have := IsIntegral.map_of_comp_eq φ ψ hrel (h.integral i)
  simpa [ψ, div_eq_mul_inv] using this

abbrev Lx (x : ι → Ω) (e : Fin (D + 1) → ι) : IntermediateField (fnField (x ∘ e)) Ω :=
  extendScalars (fnField_comp_le x e)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `t ht`. Establish `key : fnField x ≤ (adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0))).restrictScalars ℚ`. Use `IntermediateField.adjoin_le_iff.mpr ?_` and prove the remaining obligations. Introduce and unpack `s ⟨i, j, rfl⟩`.

Establish `hi : x i / x (e 0) ∈ adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0))` using `subset_adjoin _ _ ⟨i, rfl⟩`. Establish `hj : x j / x (e 0) ∈ adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0))` using `subset_adjoin _ _ ⟨j, rfl⟩`. Establish `hq` using `div_mem hi hj`. Establish `e2 : x i / x (e 0) / (x j / x (e 0)) = x i / x j`. Distinguish the cases in `hj0 : x j = 0`.

Simplify using `[hj0]`. Clear the denominators using the available nonvanishing facts. Rewrite `hq` using `[e2]`. Conclude with `hq`. Conclude with `key ht`.

Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `t ⟨i, rfl⟩`. Conclude with `div_mem_fnField x i (e 0)`.
-/
theorem Lx_eq (x : ι → Ω) (e : Fin (D + 1) → ι) (hx0 : x (e 0) ≠ 0) :
    Lx x e = adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0)) := by
  apply le_antisymm
  · intro t ht
    have key : fnField x ≤
        (adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0))).restrictScalars ℚ := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro s ⟨i, j, rfl⟩
      have hi : x i / x (e 0) ∈ adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0)) :=
        subset_adjoin _ _ ⟨i, rfl⟩
      have hj : x j / x (e 0) ∈ adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0)) :=
        subset_adjoin _ _ ⟨j, rfl⟩
      have hq := div_mem hi hj
      have e2 : x i / x (e 0) / (x j / x (e 0)) = x i / x j := by
        by_cases hj0 : x j = 0
        · simp [hj0]
        · field_simp
      rw [e2] at hq
      exact hq
    exact key ht
  · rw [IntermediateField.adjoin_le_iff]
    rintro t ⟨i, rfl⟩
    exact div_mem_fnField x i (e 0)

/- English proof (translation)
Establish `hx0 : x (e 0) ≠ 0` using `coord_ne_zero (x ∘ e) h.free 0`. Establish `hint : ∀ t ∈ Set.range (fun i => x i / x (e 0)), IsIntegral (fnField (x ∘ e)) t`. Introduce and unpack `t ⟨i, rfl⟩`. Conclude with `(coord_div_isIntegral x e h i).tower_top`. Rewrite using `[Lx_eq x e hx0]`.

Conclude with `IntermediateField.finiteDimensional_adjoin hint`.
-/
theorem Lx_finite (x : ι → Ω) (e : Fin (D + 1) → ι) (h : IsProjFrame x e) :
    FiniteDimensional (fnField (x ∘ e)) (Lx x e) := by
  have hx0 : x (e 0) ≠ 0 := coord_ne_zero (x ∘ e) h.free 0
  have hint : ∀ t ∈ Set.range (fun i => x i / x (e 0)), IsIntegral (fnField (x ∘ e)) t := by
    rintro t ⟨i, rfl⟩
    exact (coord_div_isIntegral x e h i).tower_top
  rw [Lx_eq x e hx0]
  exact IntermediateField.finiteDimensional_adjoin hint

def gL (x : ι → Ω) (e : Fin (D + 1) → ι) (i : ι) : Lx x e :=
  ⟨x i / x (e 0), div_mem_fnField x i (e 0)⟩

/- English proof (translation)
Apply `IntermediateField.map_injective (Lx x e).val` to reduce the goal to its premises. Establish `htop : (⊤ : IntermediateField (fnField (x ∘ e)) (Lx x e)).map (Lx x e).val = Lx x e`. Use extensionality with `z`. Rewrite using `[IntermediateField.mem_map]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨w, -, rfl⟩`. Conclude with `w.2`. Introduce `hz`. Conclude with `⟨⟨z, hz⟩, IntermediateField.mem_top, rfl⟩`. Rewrite using `[IntermediateField.adjoin_map, ← Set.range_comp, htop]`.

Conclude with `(Lx_eq x e hx0).symm`.
-/
theorem adjoin_gL (x : ι → Ω) (e : Fin (D + 1) → ι) (hx0 : x (e 0) ≠ 0) :
    adjoin (fnField (x ∘ e)) (Set.range (gL x e)) = ⊤ := by
  apply IntermediateField.map_injective (Lx x e).val
  have htop : (⊤ : IntermediateField (fnField (x ∘ e)) (Lx x e)).map (Lx x e).val = Lx x e := by
    ext z
    rw [IntermediateField.mem_map]
    constructor
    · rintro ⟨w, -, rfl⟩
      exact w.2
    · intro hz
      exact ⟨⟨z, hz⟩, IntermediateField.mem_top, rfl⟩
  rw [IntermediateField.adjoin_map, ← Set.range_comp, htop]
  exact (Lx_eq x e hx0).symm

/- English proof (translation)
Establish `hx0 : x (e 0) ≠ 0` using `coord_ne_zero (x ∘ e) h.free 0`. Use `Lx_finite x e h` as an intermediate fact. Conclude with `exists_int_primitive (gL x e) (adjoin_gL x e hx0)`.
-/
theorem exists_primitive (x : ι → Ω) (e : Fin (D + 1) → ι) (h : IsProjFrame x e) :
    ∃ c : ι → ℤ, (fnField (x ∘ e))⟮∑ i, (c i : Lx x e) * gL x e i⟯ = ⊤ := by
  have hx0 : x (e 0) ≠ 0 := coord_ne_zero (x ∘ e) h.free 0
  have := Lx_finite x e h
  exact exists_int_primitive (gL x e) (adjoin_gL x e hx0)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

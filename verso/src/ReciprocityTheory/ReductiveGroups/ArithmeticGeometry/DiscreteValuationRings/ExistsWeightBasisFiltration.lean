import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Mathlib.AlgebraicGeometry.ValuativeCriterion

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.DVR.TWO

open ReciprocityTheory.ChartRestriction.G.Out

variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))

/- English proof (translation)
Break down `eq_or_ne b ⊤ with rfl | hbt` into its components or cases. Conclude with `le_top`. Break down `eq_or_ne a ⊤ with rfl | hat` into its components or cases. Simplify using `at h`. Use `lift a to ℚ using hat`.

Use `lift b to ℚ using hbt`. Normalize the coercions in `at h ha ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_weight_basis_filtration {a b : WithTop ℚ} (h : a + b = 0) (ha : a ≤ 0) : 0 ≤ b := by
  rcases eq_or_ne b ⊤ with rfl | hbt
  · exact le_top
  rcases eq_or_ne a ⊤ with rfl | hat
  · simp at h
  lift a to ℚ using hat
  lift b to ℚ using hbt
  norm_cast at h ha ⊢
  linarith

/- English proof (translation)
Break down `eq_or_ne b ⊤ with rfl | hbt` into its components or cases. Simplify using `at h`. Break down `eq_or_ne a ⊤ with rfl | hat` into its components or cases. Simplify using `at h`. Use `lift a to ℚ using hat`.

Use `lift b to ℚ using hbt`. Normalize the coercions in `at h hb ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem le_zero_of_add_eq_zero_nonneg {a b : WithTop ℚ} (h : a + b = 0) (hb : 0 ≤ b) : a ≤ 0 := by
  rcases eq_or_ne b ⊤ with rfl | hbt
  · simp at h
  rcases eq_or_ne a ⊤ with rfl | hat
  · simp at h
  lift a to ℚ using hat
  lift b to ℚ using hbt
  norm_cast at h hb ⊢
  linarith

def Ov : ValuationSubring F where
  carrier := {x | 0 ≤ v x}
  mul_mem' {a b} ha hb := by
    show 0 ≤ v (a * b)
    rw [AddValuation.map_mul]; exact add_nonneg ha hb
  one_mem' := by show 0 ≤ v 1; rw [AddValuation.map_one]
  add_mem' {a b} ha hb := le_trans (le_min ha hb) (AddValuation.map_add v a b)
  zero_mem' := by show 0 ≤ v 0; rw [AddValuation.map_zero]; exact le_top
  neg_mem' {a} ha := by show 0 ≤ v (-a); rw [AddValuation.map_neg]; exact ha
  mem_or_inv_mem' x := by
    by_cases hx : x = 0
    · left; show 0 ≤ v x; rw [hx, AddValuation.map_zero]; exact le_top
    rcases le_total 0 (v x) with h | h
    · exact Or.inl h
    · right
      show 0 ≤ v x⁻¹
      refine exists_weight_basis_filtration ?_ h
      rw [← AddValuation.map_mul, mul_inv_cancel₀ hx, AddValuation.map_one]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_Ov {x : F} : x ∈ Ov v ↔ 0 ≤ v x := Iff.rfl

/- English proof (translation)
The claim follows from `(mem_Ov v).1 r.2`.
-/
theorem v_nonneg (r : Ov v) : (0 : WithTop ℚ) ≤ v (r : F) := (mem_Ov v).1 r.2

/- English proof (translation)
Establish `h1` using `v_nonneg v (r : Ov v)`. Establish `h2` using `v_nonneg v ((r⁻¹ : (Ov v)ˣ) : Ov v)`. Establish `hm : ((r : Ov v) : F) * (((r⁻¹ : (Ov v)ˣ) : Ov v) : F) = 1` using `congrArg Subtype.val r.mul_inv`. Establish `hs : v ((r : Ov v) : F) + v (((r⁻¹ : (Ov v)ˣ) : Ov v) : F) = 0`. Rewrite using `[← AddValuation.map_mul, hm, AddValuation.map_one]`.

Conclude with `le_antisymm (le_zero_of_add_eq_zero_nonneg hs h2) h1`.
-/
theorem v_unit (r : (Ov v)ˣ) : v ((r : Ov v) : F) = 0 := by
  have h1 := v_nonneg v (r : Ov v)
  have h2 := v_nonneg v ((r⁻¹ : (Ov v)ˣ) : Ov v)
  have hm : ((r : Ov v) : F) * (((r⁻¹ : (Ov v)ˣ) : Ov v) : F) = 1 := congrArg Subtype.val r.mul_inv
  have hs : v ((r : Ov v) : F) + v (((r⁻¹ : (Ov v)ˣ) : Ov v) : F) = 0 := by
    rw [← AddValuation.map_mul, hm, AddValuation.map_one]
  exact le_antisymm (le_zero_of_add_eq_zero_nonneg hs h2) h1

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  [Algebra (FractionRing V) F]

abbrev algVF : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))

/- English proof (translation)
Distinguish the cases in `hx0 : x = 0`. Substitute `hx0` using the available equality. Use `⟨?_, fun _ h => absurd rfl h⟩` and prove the remaining obligations. Rewrite using `[map_zero, AddValuation.map_zero]`. Conclude with `le_top`.

Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ`. Establish `hH : HasVal ϖ (algebraMap V (FractionRing V) x) (n : ℤ)` using `⟨u, by rw [hu, map_mul, map_pow, zpow_natCast, mul_comm]⟩`. Establish `hval : v (algVF x) = (((n : ℤ) : ℚ) : WithTop ℚ)` using `hv _ _ hH`. Rewrite using `[hval]`. Use `⟨?_, fun hnu _ => ?_⟩` and prove the remaining obligations.

Establish `h0 : (0 : ℚ) ≤ ((n : ℤ) : ℚ)` using `by positivity`. Conclude with `h0` after adjusting the coercions. Break down `Nat.eq_zero_or_pos n with h0 | hpos` into its components or cases. Conclude with `(hnu (by rw [hu, h0, pow_zero, mul_one]; exact u.isUnit)).elim`. Establish `h1 : (1 : ℚ) ≤ ((n : ℤ) : ℚ)` using `by exact_mod_cast hpos`.

Conclude with `h1` after adjusting the coercions.
-/
theorem v_of_V (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) (x : V) : (0 : WithTop ℚ) ≤ v (algVF x) ∧
    (¬ IsUnit x → x ≠ 0 → (1 : WithTop ℚ) ≤ v (algVF x)) := by
  by_cases hx0 : x = 0
  · subst hx0
    refine ⟨?_, fun _ h => absurd rfl h⟩
    rw [map_zero, AddValuation.map_zero]
    exact le_top
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hH : HasVal ϖ (algebraMap V (FractionRing V) x) (n : ℤ) :=
    ⟨u, by rw [hu, map_mul, map_pow, zpow_natCast, mul_comm]⟩
  have hval : v (algVF x) = (((n : ℤ) : ℚ) : WithTop ℚ) := hv _ _ hH
  rw [hval]
  refine ⟨?_, fun hnu _ => ?_⟩
  · have h0 : (0 : ℚ) ≤ ((n : ℤ) : ℚ) := by positivity
    exact_mod_cast h0
  · rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exact (hnu (by rw [hu, h0, pow_zero, mul_one]; exact u.isUnit)).elim
    · have h1 : (1 : ℚ) ≤ ((n : ℤ) : ℚ) := by exact_mod_cast hpos
      exact_mod_cast h1

def fO (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) : V →+* Ov v :=
  (algVF (F := F) (V := V)).codRestrict (Ov v).toSubring fun x => (v_of_V v hϖ hv x).1

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fO_comp (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) :
    (algebraMap (Ov v) F).comp (fO v hϖ hv) = algVF := rfl

instance isLocalHom_fO (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) : IsLocalHom (fO v hϖ hv) where
  map_nonunit x hx := by
    by_contra hxu
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    have h1 := (v_of_V v hϖ hv x).2 hxu hx0
    have h0 := v_unit v hx.unit
    rw [IsUnit.unit_spec] at h0
    have : v (algVF x) = 0 := h0
    rw [this] at h1
    exact absurd h1 (by decide)

/- English proof (translation)
Establish `hE : ValuativeCriterion.Existence p`. Establish `h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) p`. Rewrite using `[← UniversallyClosed.eq_valuativeCriterion]`. Use `infer_instance`. Conclude with `h.1`.

Set `S : ValuativeCommSq p` to `{ R := Ov v, K := F, i₁ := x, i₂ := Spec.map (CommRingCat.ofHom (fO v hϖ hv)), commSq := ⟨by rw [hx, ← Spec.map_comp, ← CommRingCat.ofHom_comp, fO_comp]⟩ }`. Take `⟨l⟩` from `(hE S).exists_lift`. Conclude with `⟨l.l, l.fac_right, l.fac_left⟩`.
-/
theorem exists_lift (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of V))
    [IsProper p] (x : Spec (CommRingCat.of F) ⟶ X) (hx : x ≫ p = Spec.map (CommRingCat.ofHom algVF)) :
    ∃ x' : Spec (CommRingCat.of (Ov v)) ⟶ X, x' ≫ p = Spec.map (CommRingCat.ofHom (fO v hϖ hv)) ∧
      Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F)) ≫ x' = x := by
  have hE : ValuativeCriterion.Existence p := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) p := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    exact h.1
  let S : ValuativeCommSq p :=
    { R := Ov v, K := F, i₁ := x, i₂ := Spec.map (CommRingCat.ofHom (fO v hϖ hv)),
      commSq := ⟨by rw [hx, ← Spec.map_comp, ← CommRingCat.ofHom_comp, fO_comp]⟩ }
  obtain ⟨l⟩ := (hE S).exists_lift
  exact ⟨l.l, l.fac_right, l.fac_left⟩

/- English proof (translation)
Set `S : ValuativeCommSq p` to `{ R := Ov v, K := F, i₁ := Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F)) ≫ x₁, i₂ := Spec.map (CommRingCat.ofHom (fO v hϖ hv)), commSq := ⟨by rw [Category.assoc, h₁]⟩ }`. Establish `hU : Subsingleton S.commSq.LiftStruct` using `IsSeparated.valuativeCriterion p S`. Establish `hl : (⟨x₁, rfl, h₁⟩ : S.commSq.LiftStruct) = ⟨x₂, h.symm, h₂⟩` using `@Subsingleton.elim _ hU _ _`. Conclude with `congrArg CommSq.LiftStruct.l hl`.
-/
theorem lift_unique (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of V))
    [IsSeparated p] (x₁ x₂ : Spec (CommRingCat.of (Ov v)) ⟶ X)
    (h₁ : x₁ ≫ p = Spec.map (CommRingCat.ofHom (fO v hϖ hv))) (h₂ : x₂ ≫ p = Spec.map (CommRingCat.ofHom (fO v hϖ hv)))
    (h : Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F)) ≫ x₁ = Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F)) ≫ x₂) :
    x₁ = x₂ := by
  let S : ValuativeCommSq p :=
    { R := Ov v, K := F, i₁ := Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F)) ≫ x₁,
      i₂ := Spec.map (CommRingCat.ofHom (fO v hϖ hv)),
      commSq := ⟨by rw [Category.assoc, h₁]⟩ }
  have hU : Subsingleton S.commSq.LiftStruct := IsSeparated.valuativeCriterion p S
  have hl : (⟨x₁, rfl, h₁⟩ : S.commSq.LiftStruct) = ⟨x₂, h.symm, h₂⟩ := @Subsingleton.elim _ hU _ _
  exact congrArg CommSq.LiftStruct.l hl

end ReciprocityTheory.ChartRestriction.G.DVR.TWO

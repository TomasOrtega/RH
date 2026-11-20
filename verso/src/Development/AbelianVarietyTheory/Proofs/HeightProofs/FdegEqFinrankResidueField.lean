import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAE
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct

namespace GlobalTheory.ResDegPlace

open IsLocalRing

/- English proof (translation)
Establish `hk : RingHom.ker p = RingHom.ker q`. Use extensionality with `x`. Simplify using `only [RingHom.mem_ker]`. Conclude with `hker x`. Establish `hk₀ : RingHom.ker p₀ = RingHom.ker q₀`.

Use extensionality with `x`. Simplify using `only [RingHom.mem_ker]`. Rewrite using `[← map_eq_zero_iff _ (algebraMap k K).injective, h₁, hker, ← h₂, map_eq_zero_iff _ (algebraMap k' K').injective]`. Set `e : K ≃+* K'` to `(RingHom.quotientKerEquivOfSurjective hp).symm.trans ((Ideal.quotEquivOfEq hk).trans (RingHom.quotientKerEquivOfSurjective hq))`. Set `e₀ : k ≃+* k'` to `(RingHom.quotientKerEquivOfSurjective hp₀).symm.trans ((Ideal.quotEquivOfEq hk₀).trans (RingHom.quotientKerEquivOfSurjective hq₀))`.

Establish `he : ∀ x, e (p x) = q x` using `fun x => by`. Establish `: (RingHom.quotientKerEquivOfSurjective hp).symm (p x) = Ideal.Quotient.mk _ x`. Rewrite using `[RingEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Simplify using `only [e, RingEquiv.trans_apply, this]`.

Both sides reduce to the same expression. Establish `he₀ : ∀ x, e₀ (p₀ x) = q₀ x` using `fun x => by`. Establish `: (RingHom.quotientKerEquivOfSurjective hp₀).symm (p₀ x) = Ideal.Quotient.mk _ x`. Rewrite using `[RingEquiv.symm_apply_eq]`. Both sides reduce to the same expression.

Simplify using `only [e₀, RingEquiv.trans_apply, this]`. Both sides reduce to the same expression. Use `Algebra.finrank_eq_of_equiv_equiv e₀ e ?_` and prove the remaining obligations. Use extensionality with `y`. Take `⟨r, rfl⟩` from `hp₀ y`.

Express the relevant statement in the definitionally equal form `algebraMap k' K' (e₀ (p₀ r)) = e (algebraMap k K (p₀ r))`. Rewrite using `[he₀, h₂, h₁, he]`.
-/
theorem finrank_eq_of_surjective {S₀ S k K k' K' : Type*} [CommRing S₀] [CommRing S] [Field k]
    [Field K] [Field k'] [Field K'] [Algebra k K] [Algebra k' K'] (j : S₀ →+* S)
    (p₀ : S₀ →+* k) (q₀ : S₀ →+* k') (p : S →+* K) (q : S →+* K')
    (hp₀ : Function.Surjective p₀) (hq₀ : Function.Surjective q₀)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (hker : ∀ x, p x = 0 ↔ q x = 0)
    (h₁ : ∀ r, algebraMap k K (p₀ r) = p (j r)) (h₂ : ∀ r, algebraMap k' K' (q₀ r) = q (j r)) :
    Module.finrank k K = Module.finrank k' K' := by
  have hk : RingHom.ker p = RingHom.ker q := by
    ext x; simp only [RingHom.mem_ker]; exact hker x
  have hk₀ : RingHom.ker p₀ = RingHom.ker q₀ := by
    ext x
    simp only [RingHom.mem_ker]
    rw [← map_eq_zero_iff _ (algebraMap k K).injective, h₁, hker, ← h₂,
      map_eq_zero_iff _ (algebraMap k' K').injective]
  let e : K ≃+* K' := (RingHom.quotientKerEquivOfSurjective hp).symm.trans
    ((Ideal.quotEquivOfEq hk).trans (RingHom.quotientKerEquivOfSurjective hq))
  let e₀ : k ≃+* k' := (RingHom.quotientKerEquivOfSurjective hp₀).symm.trans
    ((Ideal.quotEquivOfEq hk₀).trans (RingHom.quotientKerEquivOfSurjective hq₀))
  have he : ∀ x, e (p x) = q x := fun x => by
    have : (RingHom.quotientKerEquivOfSurjective hp).symm (p x) = Ideal.Quotient.mk _ x := by
      rw [RingEquiv.symm_apply_eq]; rfl
    simp only [e, RingEquiv.trans_apply, this]; rfl
  have he₀ : ∀ x, e₀ (p₀ x) = q₀ x := fun x => by
    have : (RingHom.quotientKerEquivOfSurjective hp₀).symm (p₀ x) = Ideal.Quotient.mk _ x := by
      rw [RingEquiv.symm_apply_eq]; rfl
    simp only [e₀, RingEquiv.trans_apply, this]; rfl
  refine Algebra.finrank_eq_of_equiv_equiv e₀ e ?_
  ext y
  obtain ⟨r, rfl⟩ := hp₀ y
  change algebraMap k' K' (e₀ (p₀ r)) = e (algebraMap k K (p₀ r))
  rw [he₀, h₂, h₁, he]

/- English proof (translation)
Establish `hunit : IsUnit x ↔ w (x : L) = 0` using `(Valuation.valuationSubring.integers (w : Valuation L _)).isUnit_iff_valuation_eq_one`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]`. Conclude with `⟨fun h => lt_of_le_of_ne x.2 (Ne.symm h), fun h => h.ne'⟩`.
-/
theorem mem_maximalIdeal_vRing {L : Type*} [Field L] (w : AddValuation L (WithTop ℤ))
    (x : vRing w) : x ∈ maximalIdeal (vRing w) ↔ 0 < w (x : L) := by
  have hunit : IsUnit x ↔ w (x : L) = 0 :=
    (Valuation.valuationSubring.integers (w : Valuation L _)).isUnit_iff_valuation_eq_one
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]
  exact ⟨fun h => lt_of_le_of_ne x.2 (Ne.symm h), fun h => h.ne'⟩

/- English proof (translation)
Distinguish the cases in `hx0 : x = 0`. Conclude with `⟨0, by rw [map_zero, hx0]⟩`. Break down `ValuationRing.isInteger_or_isInteger R x with ⟨a, ha⟩ | ⟨a, ha⟩` into its components or cases. Conclude with `⟨a, ha⟩`. Distinguish the cases in `hau : IsUnit a`.

Take `⟨u, rfl⟩` from `hau`. Use `⟨↑u⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[map_units_inv, ha, inv_inv]`. It suffices to derive a contradiction. Establish `hpos` using `((hw.2 a).2).2 hau`.

Rewrite `hpos` using `[IsScalarTower.algebraMap_apply R F L, ha, map_inv₀]`. Establish `hxL : algebraMap F L x ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff _ (algebraMap F L).injective]`. Conclude with `hx0`. Establish `hs : w (algebraMap F L x) + w (algebraMap F L x)⁻¹ = 0`.

Rewrite using `[← AddValuation.map_mul, mul_inv_cancel₀ hxL, AddValuation.map_one]`. Use `ValPl.wt_add_eq_zero hx hpos.le hs` as an intermediate fact. Rewrite `hs` using `[this, zero_add]`. Rewrite `hpos` using `[hs]`. Conclude with `lt_irrefl _ hpos`.
-/
theorem exists_eq_of_nonneg {R F L : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field F] [Algebra R F] [IsFractionRing R F] [Field L] [Algebra F L] [Algebra R L]
    [IsScalarTower R F L] {w : AddValuation L (WithTop ℤ)} (hw : w ∈ ValPl.PlacesOver R L)
    (x : F) (hx : 0 ≤ w (algebraMap F L x)) : ∃ a : R, algebraMap R F a = x := by
  by_cases hx0 : x = 0
  · exact ⟨0, by rw [map_zero, hx0]⟩
  rcases ValuationRing.isInteger_or_isInteger R x with ⟨a, ha⟩ | ⟨a, ha⟩
  · exact ⟨a, ha⟩
  · by_cases hau : IsUnit a
    · obtain ⟨u, rfl⟩ := hau
      refine ⟨↑u⁻¹, ?_⟩
      rw [map_units_inv, ha, inv_inv]
    · exfalso
      have hpos := ((hw.2 a).2).2 hau
      rw [IsScalarTower.algebraMap_apply R F L, ha, map_inv₀] at hpos
      have hxL : algebraMap F L x ≠ 0 := by
        rw [Ne, map_eq_zero_iff _ (algebraMap F L).injective]; exact hx0
      have hs : w (algebraMap F L x) + w (algebraMap F L x)⁻¹ = 0 := by
        rw [← AddValuation.map_mul, mul_inv_cancel₀ hxL, AddValuation.map_one]
      have := ValPl.wt_add_eq_zero hx hpos.le hs
      rw [this, zero_add] at hs
      rw [hs] at hpos
      exact lt_irrefl _ hpos

section
variable {O A : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A]
  [Algebra O A] {ϖ : O}

/- English proof (translation)
Rewrite using `[ord_of_mem ζ h a.2, ← not_not (a := a ∈ ζ.asIdeal), ← vL_eq_zero_iff ζ a]`. Express the relevant statement in the definitionally equal form `0 < (vL ζ a).map (Nat.cast : ℕ → ℤ) ↔ _`. Generalize the expression as in `vL ζ a = v`. Consider the cases of `v with`. Consider the case `top => simp`.

Consider the case `coe n`. Rewrite using `[ENat.map_natCast, WithTop.coe_pos]`. Simplify using `[Nat.pos_iff_ne_zero]`.
-/
theorem ord_pos_iff (h : IsUnif A ϖ) (ζ : Pts O A) [IsDVRAt ζ] (a : As O A) :
    0 < ord ϖ ζ (a : A) ↔ a ∈ ζ.asIdeal := by
  rw [ord_of_mem ζ h a.2, ← not_not (a := a ∈ ζ.asIdeal), ← vL_eq_zero_iff ζ a]
  change 0 < (vL ζ a).map (Nat.cast : ℕ → ℤ) ↔ _
  generalize vL ζ a = v
  cases v with
  | top => simp
  | coe n =>
    rw [ENat.map_natCast, WithTop.coe_pos]
    simp [Nat.pos_iff_ne_zero]

/- English proof (translation)
Take `⟨n, hn⟩` from `h.denom x`. Establish `h1` using `hx`. Rewrite `h1` using `[ord_eq ζ h hn, ordAt_nonneg_iff ζ h, vL_eq_addVal, vL_eq_addVal, IsDiscreteValuationRing.addVal_le_iff_dvd]`. Take `⟨c, hc⟩` from `h1`. Take `⟨⟨b, s⟩, rfl⟩` from `IsLocalization.mk'_surjective ζ.asIdeal.primeCompl c`.

Establish `h2 : algebraMap (As O A) (Loc ζ) (⟨ϖ ^ n • x, hn⟩ * (s : As O A)) = algebraMap (As O A) (Loc ζ) (algebraMap O (As O A) ϖ ^ n * b)`. Rewrite using `[map_mul, hc, mul_assoc, IsLocalization.mk'_spec, ← map_mul]`. Take `⟨t, ht⟩` from `(IsLocalization.eq_iff_exists ζ.asIdeal.primeCompl (Loc ζ)).1 h2`. Establish `h3 : (algebraMap O A ϖ) ^ n * ((((t : As O A) : A) * ((s : As O A) : A)) * x) = (algebraMap O A ϖ) ^ n * (((t : As O A) : A) * (b : A))`. Use `congrArg Subtype.val ht` as an intermediate fact.

Simplify using `only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, Algebra.smul_def, map_pow] at this`. Establish `e : ((algebraMap O (As O A) ϖ : As O A) : A) = algebraMap O A ϖ` using `rfl`. Rewrite `this` using `[e]`. Take the linear combination `this`. Establish `h4` using `(h.isUnit.pow n).mul_right_inj.1 h3`.

Take `⟨d, i, hi, hdi⟩` from `Ideal.IsMaximal.exists_inv ζ.isMaximal (t * s).2`. Use `⟨d * (t * b), ?_⟩` and prove the remaining obligations. Establish `h5 : ((d * (t * b) : As O A) : A) - x = ((-i : As O A) : A) * x`. Use `congrArg Subtype.val hdi` as an intermediate fact. Simplify using `only [Submonoid.coe_mul, AddMemClass.coe_add, MulMemClass.coe_mul, OneMemClass.coe_one, NegMemClass.coe_neg] at this ⊢`.

Take the linear combination `x * this - (d : A) * h4`. Rewrite using `[h5, ord_mul ζ h]`. Conclude with `add_pos_of_pos_of_nonneg ((ord_pos_iff h ζ _).2 (ζ.asIdeal.neg_mem hi)) hx`.
-/
theorem exists_approx (h : IsUnif A ϖ) (ζ : Pts O A) [IsDVRAt ζ] (x : A) (hx : 0 ≤ ord ϖ ζ x) :
    ∃ a : As O A, 0 < ord ϖ ζ ((a : A) - x) := by
  obtain ⟨n, hn⟩ := h.denom x
  have h1 := hx
  rw [ord_eq ζ h hn, ordAt_nonneg_iff ζ h, vL_eq_addVal, vL_eq_addVal,
    IsDiscreteValuationRing.addVal_le_iff_dvd] at h1
  obtain ⟨c, hc⟩ := h1
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective ζ.asIdeal.primeCompl c
  have h2 : algebraMap (As O A) (Loc ζ) (⟨ϖ ^ n • x, hn⟩ * (s : As O A)) =
      algebraMap (As O A) (Loc ζ) (algebraMap O (As O A) ϖ ^ n * b) := by
    rw [map_mul, hc, mul_assoc, IsLocalization.mk'_spec, ← map_mul]
  obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists ζ.asIdeal.primeCompl (Loc ζ)).1 h2
  have h3 : (algebraMap O A ϖ) ^ n * ((((t : As O A) : A) * ((s : As O A) : A)) * x) =
      (algebraMap O A ϖ) ^ n * (((t : As O A) : A) * (b : A)) := by
    have := congrArg Subtype.val ht
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, Algebra.smul_def, map_pow] at this
    have e : ((algebraMap O (As O A) ϖ : As O A) : A) = algebraMap O A ϖ := rfl
    rw [e] at this
    linear_combination this
  have h4 := (h.isUnit.pow n).mul_right_inj.1 h3
  obtain ⟨d, i, hi, hdi⟩ := Ideal.IsMaximal.exists_inv ζ.isMaximal (t * s).2
  refine ⟨d * (t * b), ?_⟩
  have h5 : ((d * (t * b) : As O A) : A) - x = ((-i : As O A) : A) * x := by
    have := congrArg Subtype.val hdi
    simp only [Submonoid.coe_mul, AddMemClass.coe_add, MulMemClass.coe_mul, OneMemClass.coe_one,
      NegMemClass.coe_neg] at this ⊢
    linear_combination x * this - (d : A) * h4
  rw [h5, ord_mul ζ h]
  exact add_pos_of_pos_of_nonneg ((ord_pos_iff h ζ _).2 (ζ.asIdeal.neg_mem hi)) hx

end

/- English proof (translation)
Use `u.map_lt_add h hy` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem pos_of_sub_pos {S : Type*} [CommRing S] (u : AddValuation S (WithTop ℤ)) {x y : S}
    (h : 0 < u (x - y)) (hy : 0 < u y) : 0 < u x := by
  have := u.map_lt_add h hy
  rwa [sub_add_cancel] at this

/- English proof (translation)
Introduce `R R' F _ _ _ _ _ _ _ _ _ _ _ hRR L _ _ _ _ A _ _ ϖ h ζ _ w hw S _ u Ψ ι hΨ hcomp hι hord hres`. Use `letI := resAlg (F := F) w`. Set `T : Subring (As R' A × vRing w)` to `{ carrier := {z | 0 < u (Ψ (z.1 : A) - ι (z.2 : L))} mul_mem' := by`. Introduce `z z' hz hz'`. Express the relevant statement in the definitionally equal form `0 < u (Ψ ((z.1 : A) * z'.1) - ι ((z.2 : L) * z'.2))`.

Establish `e : Ψ ((z.1 : A) * z'.1) - ι ((z.2 : L) * z'.2) = (Ψ (z'.1 : A) - ι (z'.2 : L)) * Ψ z.1 + (Ψ (z.1 : A) - ι (z.2 : L)) * ι z'.2`. Rewrite using `[map_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `u.map_lt_add ?_ ?_` and prove the remaining obligations.

Rewrite using `[u.map_mul, ← hord]`. Conclude with `add_pos_of_pos_of_nonneg hz' (ord_nonneg ζ h z.1.2)`. Rewrite using `[u.map_mul, hι]`. Conclude with `add_pos_of_pos_of_nonneg hz z'.2.2`. Use the proof step `one_mem' := by`.

Express the relevant statement in the definitionally equal form `0 < u (Ψ 1 - ι 1)`. Simplify using the standard rewrite rules. Use the proof step `add_mem' := by`. Introduce `z z' hz hz'`. Express the relevant statement in the definitionally equal form `0 < u (Ψ ((z.1 : A) + z'.1) - ι ((z.2 : L) + z'.2))`.

Rewrite using `[map_add, map_add, add_sub_add_comm]`. Conclude with `u.map_lt_add hz hz'`. Use the proof step `zero_mem' := by`. Express the relevant statement in the definitionally equal form `0 < u (Ψ 0 - ι 0)`. Simplify using the standard rewrite rules.

Use the proof step `neg_mem' := by`. Introduce `z hz`. Express the relevant statement in the definitionally equal form `0 < u (Ψ (-(z.1 : A)) - ι (-(z.2 : L)))`. Rewrite using `[map_neg, map_neg, ← neg_sub', u.map_neg]`. Conclude with `hz }`.

Establish `hT : ∀ z : T, 0 < u (Ψ (z.1.1 : A) - ι (z.1.2 : L))` using `fun z => z.2`. Set `jw : R →+* vRing w` to `(algebraMap R L).codRestrict (vRing w) (fun r => (hw.2 r).1)`. Set `j : R →+* T` to `(((algebraMap R' (As R' A)).comp (algebraMap R R')).prod jw).codRestrict T (fun r => by`. Express the relevant statement in the definitionally equal form `0 < u (Ψ (algebraMap R' A (algebraMap R R' r)) - ι (algebraMap R L r))`. Rewrite using `[hcomp, sub_self]`.

Use the proof step `simp)`. Establish `hOw : ∀ a : R, algebraMap R F a ∈ (vRing w).comap (algebraMap F L)` using `fun a => by`. Rewrite using `[ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]`. Conclude with `(hw.2 a).1`. Set `φ : R →+* (vRing w).comap (algebraMap F L)` to `(algebraMap R F).codRestrict _ hOw`.

Set `p : T →+* ResidueField (Loc ζ)` to `((residue (Loc ζ)).comp (algebraMap (As R' A) (Loc ζ))).comp ((RingHom.fst _ _).comp T.subtype)`. Set `q : T →+* ResidueField (vRing w)` to `(residue (vRing w)).comp ((RingHom.snd _ _).comp T.subtype)`. Use `finrank_eq_of_surjective j ((residue R').comp (algebraMap R R')) ((residue _).comp φ) p q ?_ ?_ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `y`. Take `⟨y, rfl⟩` from `hRR y`.

Take `⟨r, rfl⟩` from `residue_surjective y`. Conclude with `⟨r, rfl⟩`. Introduce `y`. Take `⟨x, rfl⟩` from `residue_surjective y`. Take `⟨a, ha⟩` from `exists_eq_of_nonneg hw (x : F) x.2`.

Conclude with `⟨a, congrArg (residue _) (Subtype.ext ha)⟩`. Introduce `y haveI := ζ.isMaximal`. Take `⟨a, rfl⟩` from `Ideal.algebraMap_residueField_surjective ζ.asIdeal y`. Take `⟨g, hg, hag⟩` from `hres (Ψ a) (by rw [← hord]; exact ord_nonneg ζ h a.2)`. Conclude with `⟨⟨(a, ⟨g, hg⟩), hag⟩, rfl⟩`.

Introduce `y`. Take `⟨g, rfl⟩` from `residue_surjective y`. Take `⟨x, hx⟩` from `hΨ (ι g)`. Take `⟨a, ha⟩` from `exists_approx h ζ x (by rw [hord, hx, hι]; exact g.2)`. Rewrite `ha` using `[hord, map_sub, hx]`.

Conclude with `⟨⟨(a, g), ha⟩, rfl⟩`. Introduce `z`. Express the relevant statement in the definitionally equal form `residue (Loc ζ) (algebraMap (As R' A) (Loc ζ) z.1.1) = 0 ↔ residue (vRing w) z.1.2 = 0`. Rewrite using `[residue_eq_zero_iff, residue_eq_zero_iff, mem_maximalIdeal_vRing, IsLocalization.AtPrime.to_map_mem_maximal_iff (Loc ζ) ζ.asIdeal, ← ord_pos_iff h, hord, ← hι]`. Use `⟨pos_of_sub_pos u ?_, pos_of_sub_pos u (hT z)⟩` and prove the remaining obligations.

Rewrite using `[← neg_sub, u.map_neg]`. Conclude with `hT z`. Introduce `r`. Both sides reduce to the same expression. Introduce `r`.

Express the relevant statement in the definitionally equal form `residue (vRing w) (comapIncl (vRing w) (algebraMap F L) (φ r)) = residue (vRing w) (jw r)`. Use `congr 1`. Conclude with `Subtype.ext (IsScalarTower.algebraMap_apply R F L r).symm`.
-/
theorem fdeg_eq_finrank_residueField : ∀ (R R' F : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')] [Field F] [Algebra R F] [IsFractionRing R F], Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R')) → ∀ (L : Type) [Field L] [Algebra F L] [Algebra R L] [IsScalarTower R F L] (A : Type) [CommRing A] [Algebra R' A] (ϖ : R'), IsUnif A ϖ → ∀ (ζ : Pts R' A) [IsDVRAt ζ] (w : AddValuation L (WithTop ℤ)), w ∈ ValPl.PlacesOver R L → ∀ (S : Type) [CommRing S] (u : AddValuation S (WithTop ℤ)) (Ψ : A →+* S) (ι : L →+* S), Function.Surjective Ψ → (∀ r : R, Ψ (algebraMap R' A (algebraMap R R' r)) = ι (algebraMap R L r)) → (∀ g, u (ι g) = w g) → (∀ a, ord ϖ ζ a = u (Ψ a)) → (∀ x, 0 ≤ u x → ∃ g, 0 ≤ w g ∧ 0 < u (x - ι g)) → fdeg ζ = (letI := resAlg (F := F) w; Module.finrank (IsLocalRing.ResidueField ((vRing w).comap (algebraMap F L))) (IsLocalRing.ResidueField (vRing w))) := by
  intro R R' F _ _ _ _ _ _ _ _ _ _ _ hRR L _ _ _ _ A _ _ ϖ h ζ _ w hw S _ u Ψ ι hΨ hcomp hι hord
    hres
  letI := resAlg (F := F) w
  let T : Subring (As R' A × vRing w) :=
    { carrier := {z | 0 < u (Ψ (z.1 : A) - ι (z.2 : L))}
      mul_mem' := by
        intro z z' hz hz'
        change 0 < u (Ψ ((z.1 : A) * z'.1) - ι ((z.2 : L) * z'.2))
        have e : Ψ ((z.1 : A) * z'.1) - ι ((z.2 : L) * z'.2) =
            (Ψ (z'.1 : A) - ι (z'.2 : L)) * Ψ z.1 + (Ψ (z.1 : A) - ι (z.2 : L)) * ι z'.2 := by
          rw [map_mul, map_mul]; ring
        rw [e]
        refine u.map_lt_add ?_ ?_
        · rw [u.map_mul, ← hord]
          exact add_pos_of_pos_of_nonneg hz' (ord_nonneg ζ h z.1.2)
        · rw [u.map_mul, hι]
          exact add_pos_of_pos_of_nonneg hz z'.2.2
      one_mem' := by
        change 0 < u (Ψ 1 - ι 1)
        simp
      add_mem' := by
        intro z z' hz hz'
        change 0 < u (Ψ ((z.1 : A) + z'.1) - ι ((z.2 : L) + z'.2))
        rw [map_add, map_add, add_sub_add_comm]
        exact u.map_lt_add hz hz'
      zero_mem' := by
        change 0 < u (Ψ 0 - ι 0)
        simp
      neg_mem' := by
        intro z hz
        change 0 < u (Ψ (-(z.1 : A)) - ι (-(z.2 : L)))
        rw [map_neg, map_neg, ← neg_sub', u.map_neg]
        exact hz }
  have hT : ∀ z : T, 0 < u (Ψ (z.1.1 : A) - ι (z.1.2 : L)) := fun z => z.2
  let jw : R →+* vRing w := (algebraMap R L).codRestrict (vRing w) (fun r => (hw.2 r).1)
  let j : R →+* T := (((algebraMap R' (As R' A)).comp (algebraMap R R')).prod jw).codRestrict T
    (fun r => by
      change 0 < u (Ψ (algebraMap R' A (algebraMap R R' r)) - ι (algebraMap R L r))
      rw [hcomp, sub_self]; simp)
  have hOw : ∀ a : R, algebraMap R F a ∈ (vRing w).comap (algebraMap F L) := fun a => by
    rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact (hw.2 a).1
  let φ : R →+* (vRing w).comap (algebraMap F L) := (algebraMap R F).codRestrict _ hOw
  let p : T →+* ResidueField (Loc ζ) := ((residue (Loc ζ)).comp (algebraMap (As R' A) (Loc ζ))).comp
    ((RingHom.fst _ _).comp T.subtype)
  let q : T →+* ResidueField (vRing w) := (residue (vRing w)).comp
    ((RingHom.snd _ _).comp T.subtype)
  refine finrank_eq_of_surjective j ((residue R').comp (algebraMap R R')) ((residue _).comp φ) p q
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro y
    obtain ⟨y, rfl⟩ := hRR y
    obtain ⟨r, rfl⟩ := residue_surjective y
    exact ⟨r, rfl⟩
  · intro y
    obtain ⟨x, rfl⟩ := residue_surjective y
    obtain ⟨a, ha⟩ := exists_eq_of_nonneg hw (x : F) x.2
    exact ⟨a, congrArg (residue _) (Subtype.ext ha)⟩
  · intro y
    haveI := ζ.isMaximal
    obtain ⟨a, rfl⟩ := Ideal.algebraMap_residueField_surjective ζ.asIdeal y
    obtain ⟨g, hg, hag⟩ := hres (Ψ a) (by rw [← hord]; exact ord_nonneg ζ h a.2)
    exact ⟨⟨(a, ⟨g, hg⟩), hag⟩, rfl⟩
  · intro y
    obtain ⟨g, rfl⟩ := residue_surjective y
    obtain ⟨x, hx⟩ := hΨ (ι g)
    obtain ⟨a, ha⟩ := exists_approx h ζ x (by rw [hord, hx, hι]; exact g.2)
    rw [hord, map_sub, hx] at ha
    exact ⟨⟨(a, g), ha⟩, rfl⟩
  · intro z
    change residue (Loc ζ) (algebraMap (As R' A) (Loc ζ) z.1.1) = 0 ↔ residue (vRing w) z.1.2 = 0
    rw [residue_eq_zero_iff, residue_eq_zero_iff, mem_maximalIdeal_vRing,
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Loc ζ) ζ.asIdeal, ← ord_pos_iff h, hord, ← hι]
    refine ⟨pos_of_sub_pos u ?_, pos_of_sub_pos u (hT z)⟩
    rw [← neg_sub, u.map_neg]
    exact hT z
  · intro r
    rfl
  · intro r
    change residue (vRing w) (comapIncl (vRing w) (algebraMap F L) (φ r)) = residue (vRing w) (jw r)
    congr 1
    exact Subtype.ext (IsScalarTower.algebraMap_apply R F L r).symm

end GlobalTheory.ResDegPlace

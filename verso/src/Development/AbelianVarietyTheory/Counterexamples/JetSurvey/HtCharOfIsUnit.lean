import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueIsAl

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv

namespace GlobalTheory.HodgeTateTest

open GlobalTheory.TangentPow GlobalTheory.GmPoints GlobalTheory.HodgeTateImage

variable {O : Type} [CommRing O]

noncomputable abbrev GmO (O : Type) [CommRing O] : Over (Spec (CommRingCat.of O)) :=
  Gm (Spec (CommRingCat.of O))

noncomputable def taut (p : ℕ) : Tv (GmO O) p where
  χ n := torsion.ι _ _
  isChar _ _ _ _ _ h := h
  compat _ _ _ _ h := h

noncomputable def dlogT (x : LieG (GmO O)) : O := (unitOf x.1 : DualNumber O).snd

/- English proof (translation)
Establish `h` using `unitOf_mul (1 : specO O R ⟶ GmO O) 1`. Rewrite `h` using `[_root_.mul_one]`. Conclude with `left_eq_mul.mp h`.
-/
theorem unitOf_one' {R : Type} [CommRing R] [Algebra O R] :
    unitOf (1 : specO O R ⟶ GmO O) = 1 := by
  have h := unitOf_mul (1 : specO O R ⟶ GmO O) 1
  rw [_root_.mul_one] at h
  exact left_eq_mul.mp h

/- English proof (translation)
Establish `h4` using `unitOf_ptMap (TrivSqZeroExt.fstHom O O O) w`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite `h4` using `[h]`. Establish `h1 : unitOf (toUnit (specO O O) ≫ η[GmO O]) = 1` using `unitOf_one'`.

Rewrite `h4` using `[h1]`. Conclude with `h4.symm`. Introduce `h`. Apply `(unitOf_bijective (O := O) (R := O)).1` to reduce the goal to its premises. Establish `h1 : unitOf (toUnit (specO O O) ≫ η[GmO O]) = 1` using `unitOf_one'`.

Rewrite using `[h1]`. Use `ext`. Rewrite using `[h4]`. Conclude with `h`.
-/
theorem lie_iff (w : specO O (DualNumber O) ⟶ GmO O) :
    ptMap (TrivSqZeroExt.fstHom O O O) ≫ w = toUnit (specO O O) ≫ η[GmO O] ↔
      (unitOf w : DualNumber O).fst = 1 := by
  have h4 := unitOf_ptMap (TrivSqZeroExt.fstHom O O O) w
  constructor
  · intro h
    rw [h] at h4
    have h1 : unitOf (toUnit (specO O O) ≫ η[GmO O]) = 1 := unitOf_one'
    rw [h1] at h4
    exact h4.symm
  · intro h
    apply (unitOf_bijective (O := O) (R := O)).1
    have h1 : unitOf (toUnit (specO O O) ≫ η[GmO O]) = 1 := unitOf_one'
    rw [h1]
    ext
    rw [h4]
    exact h

/- English proof (translation)
The claim follows from `(lie_iff _).1 x.2`.
-/
theorem fst_eq (x : LieG (GmO O)) : (unitOf x.1 : DualNumber O).fst = 1 := (lie_iff _).1 x.2

/- English proof (translation)
Introduce `n R _ _ _ x w hw`. Establish `hw' : w ≫ (taut (O` using `O) p).χ n = _ := hw`. Rewrite using `[hw', unitOf_ptMap]`. Use `ext`. Simplify using `[dualBC_fst, fst_eq]`.

Rewrite using `[dualBC_snd, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]`. Both sides reduce to the same expression.
-/
theorem isAl_taut (p : ℕ) : IsAl (taut (O := O) p) dlogT := by
  intro n R _ _ _ x w hw
  have hw' : w ≫ (taut (O := O) p).χ n = _ := hw
  rw [hw', unitOf_ptMap]
  ext
  · simp [dualBC_fst, fst_eq]
  · rw [dualBC_snd, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
    rfl

/- English proof (translation)
Use `⟨fun x y h => ?_, fun a x h => ?_⟩` and prove the remaining obligations. Use `show (unitOf (x.1 * y.1) : DualNumber O).snd = _`. Rewrite using `[unitOf_mul, Units.val_mul, DualNumber.snd_mul, fst_eq, fst_eq, dlogT, dlogT]`. Expand and normalize the polynomial expressions, which then agree. Use `show (unitOf (ptMap (dualScale a) ≫ x.1) : DualNumber O).snd = _`.

Rewrite using `[unitOf_ptMap]`. Simplify using `[dualScale, dlogT]`.
-/
theorem dlogT_mem : dlogT ∈ omega (GmO O) := by
  refine ⟨fun x y h => ?_, fun a x h => ?_⟩
  · show (unitOf (x.1 * y.1) : DualNumber O).snd = _
    rw [unitOf_mul, Units.val_mul, DualNumber.snd_mul, fst_eq, fst_eq, dlogT, dlogT]
    ring
  · show (unitOf (ptMap (dualScale a) ≫ x.1) : DualNumber O).snd = _
    rw [unitOf_ptMap]
    simp [dualScale, dlogT]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x y h`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `(unitOf_bijective (O := O) (R := DualNumber O)).1` to reduce the goal to its premises. Use `ext`.

Rewrite using `[fst_eq, fst_eq]`. Conclude with `h`. Introduce `a`. Establish `hu : IsUnit (TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr a : DualNumber O)`. Rewrite using `[TrivSqZeroExt.isUnit_iff_isUnit_fst]`.

Simplify using the standard rewrite rules. Take `⟨w, hw⟩` from `(unitOf_bijective (O := O) (R := DualNumber O)).2 hu.unit`. Use `⟨⟨w, (lie_iff w).2 (by rw [hw]; simp)⟩, ?_⟩` and prove the remaining obligations. Use `show (unitOf w : DualNumber O).snd = a`. Rewrite using `[hw]`.

Simplify using the standard rewrite rules.
-/
theorem dlogT_bijective : Function.Bijective (dlogT (O := O)) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply (unitOf_bijective (O := O) (R := DualNumber O)).1
    ext
    · rw [fst_eq, fst_eq]
    · exact h
  · intro a
    have hu : IsUnit (TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr a : DualNumber O) := by
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]; simp
    obtain ⟨w, hw⟩ := (unitOf_bijective (O := O) (R := DualNumber O)).2 hu.unit
    refine ⟨⟨w, (lie_iff w).2 (by rw [hw]; simp)⟩, ?_⟩
    show (unitOf w : DualNumber O).snd = a
    rw [hw]; simp

/- English proof (translation)
Introduce `f hf`. Take `⟨e, he⟩` from `(dlogT_bijective (O := O)).2 1`. Rewrite using `[Submodule.mem_span_singleton]`. Use `⟨f e, funext fun x => ?_⟩` and prove the remaining obligations. Establish `h1 : (unitOf (ptMap (dualScale (dlogT x)) ≫ e.1) : DualNumber O).fst = 1`.

Rewrite using `[unitOf_ptMap]`. Simplify using `[dualScale, fst_eq]`. Establish `hm` using `(lie_iff _).2 h1`. Establish `hx : x = ⟨ptMap (dualScale (dlogT x)) ≫ e.1, hm⟩`. Apply `(dlogT_bijective (O := O)).1` to reduce the goal to its premises.

Rewrite using `[dlogT_mem.2 _ e hm, he, _root_.mul_one]`. Use `hf.2 (dlogT x) e hm` as an intermediate fact. Rewrite `this` using `[← hx]`. Simplify using `[this, mul_comm]`.
-/
theorem omega_le_span : omega (GmO O) ≤ Submodule.span O {dlogT} := by
  intro f hf
  obtain ⟨e, he⟩ := (dlogT_bijective (O := O)).2 1
  rw [Submodule.mem_span_singleton]
  refine ⟨f e, funext fun x => ?_⟩
  have h1 : (unitOf (ptMap (dualScale (dlogT x)) ≫ e.1) : DualNumber O).fst = 1 := by
    rw [unitOf_ptMap]; simp [dualScale, fst_eq]
  have hm := (lie_iff _).2 h1
  have hx : x = ⟨ptMap (dualScale (dlogT x)) ≫ e.1, hm⟩ := by
    apply (dlogT_bijective (O := O)).1
    rw [dlogT_mem.2 _ e hm, he, _root_.mul_one]
  have := hf.2 (dlogT x) e hm
  rw [← hx] at this
  simp [this, mul_comm]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Conclude with `Submodule.span_le.2 fun f hf => hf.1`. Conclude with `omega_le_span.trans (Submodule.span_mono (by`. Introduce and unpack `_ rfl`. Conclude with `⟨dlogT_mem, taut p, isAl_taut p⟩))`.
-/
theorem htSpan_gm (p : ℕ) : htSpan (GmO O) p = omega (GmO O) := by
  apply le_antisymm
  · exact Submodule.span_le.2 fun f hf => hf.1
  · exact omega_le_span.trans (Submodule.span_mono (by
      rintro _ rfl
      exact ⟨dlogT_mem, taut p, isAl_taut p⟩))

/- English proof (translation)
Use `⟨fun c _ f hf => ?_, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[htSpan_gm]`. Conclude with `Submodule.smul_mem _ _ hf`. Establish `h0 : dlogT (O` using `O) = 0 := by`. Use `dlogT_mem (O := O)` as an intermediate fact.

Rewrite `this` using `[h, Submodule.mem_bot]`. Then use the resulting hypothesis. Take `⟨e, he⟩` from `(dlogT_bijective (O := O)).2 1`. Rewrite `he` using `[h0]`. Conclude with `zero_ne_one he`.
-/
theorem htChar_gm (p : ℕ) {C : Type} [Field C] (v : Valuation C NNReal) [Algebra O C]
    [Nontrivial O] : HTChar p v (GmO O) ∧ omega (GmO O) ≠ ⊥ := by
  refine ⟨fun c _ f hf => ?_, fun h => ?_⟩
  · rw [htSpan_gm]; exact Submodule.smul_mem _ _ hf
  · have h0 : dlogT (O := O) = 0 := by
      have := dlogT_mem (O := O); rwa [h, Submodule.mem_bot] at this
    obtain ⟨e, he⟩ := (dlogT_bijective (O := O)).2 1
    rw [h0] at he
    exact zero_ne_one he

/- English proof (translation)
Introduce `h`. Take `⟨e, he⟩` from `(dlogT_bijective (O := O)).2 1`. Establish `h1` using `(isAl_iff _ _).1 h e 1 _ (pow_quot (O := O) 1)`. Establish `h2` using `(isAl_iff _ _).1 (isAl_taut (O := O) p) e 1 _ (pow_quot (O := O) 1)`. Rewrite `h2` using `[← h1, he, Pi.zero_apply, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq, sub_zero, pow_one, ← Ideal.eq_top_iff_one, Ideal.span_singleton_eq_top]`.

Conclude with `hp h2`.
-/
theorem not_isAl_zero (p : ℕ) (hp : ¬IsUnit (p : O)) : ¬IsAl (taut (O := O) p) 0 := by
  intro h
  obtain ⟨e, he⟩ := (dlogT_bijective (O := O)).2 1
  have h1 := (isAl_iff _ _).1 h e 1 _ (pow_quot (O := O) 1)
  have h2 := (isAl_iff _ _).1 (isAl_taut (O := O) p) e 1 _ (pow_quot (O := O) 1)
  rw [← h1, he, Pi.zero_apply, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq, sub_zero,
    pow_one, ← Ideal.eq_top_iff_one, Ideal.span_singleton_eq_top] at h2
  exact hp h2

/- English proof (translation)
Introduce `c _ f hf`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ⟨hf, ⟨fun _ => 1, ?_, ?_⟩, ?_⟩)` and prove the remaining obligations. Introduce `n T x y z _`. Simplify using `only [MonObj.comp_one, _root_.mul_one]`. Introduce `n T x y _`.

Simplify using `only [MonObj.comp_one]`. Introduce `n R _ _ hR x w _`. Establish `hu : IsUnit ((p : R) ^ n)`. Use `hp.map (algebraMap O R)` as an intermediate fact. Rewrite `this` using `[map_natCast]`.

Conclude with `this.pow n`. Rewrite `hu` using `[hR, isUnit_zero_iff]`. Use `haveI : Subsingleton R := subsingleton_of_zero_eq_one hu`. Apply the tactic sequence `ext <;> exact Subsingleton.elim _ _`.
-/
theorem htChar_of_isUnit (p : ℕ) (hp : IsUnit (p : O)) {C : Type} [Field C]
    (v : Valuation C NNReal) [Algebra O C] (G : Over (Spec (CommRingCat.of O))) [GrpObj G] :
    HTChar p v G := by
  intro c _ f hf
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨hf, ⟨fun _ => 1, ?_, ?_⟩, ?_⟩)
  · intro n T x y z _
    simp only [MonObj.comp_one, _root_.mul_one]
  · intro n T x y _
    simp only [MonObj.comp_one]
  · intro n R _ _ hR x w _
    have hu : IsUnit ((p : R) ^ n) := by
      have := hp.map (algebraMap O R)
      rw [map_natCast] at this
      exact this.pow n
    rw [hR, isUnit_zero_iff] at hu
    haveI : Subsingleton R := subsingleton_of_zero_eq_one hu
    ext <;> exact Subsingleton.elim _ _

end GlobalTheory.HodgeTateTest

import Mathlib
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedOrderIffPlacewiseStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteOrderValuation.WeakApprox

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.TrivAbove

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem one_coord' (w : HeightOneSpectrum (𝓞 E)) : (1 : Af E) w = 1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mul_coord' (x y : Af E) (w : HeightOneSpectrum (𝓞 E)) : (x * y) w = x w * y w := rfl

/- English proof (translation)
Use `show (((coord w z)⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _`. Rewrite using `[Units.val_inv_eq_inv_val, coe_coord]`.
-/
theorem inv_coord' (z : (Af E)ˣ) (w : HeightOneSpectrum (𝓞 E)) : (↑z⁻¹ : Af E) w = ((z : Af E) w)⁻¹ := by
  show (((coord w z)⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
  rw [Units.val_inv_eq_inv_val, coe_coord]

open Classical in

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => rw [Finset.prod_empty, Units.val_one, one_coord']`. Simplify using the standard rewrite rules. Consider the case `insert a S ha ih`. Rewrite using `[Finset.prod_insert ha, Units.val_mul, mul_coord', ih]`.

Distinguish the cases in `h : w' = a`. Substitute `h` using the available equality. Simplify using `[ha, single_self]`. Rewrite using `[suppAt_single a (x a) w' h]`. Simplify using `[h]`.
-/
theorem prod_single_coord (S : Finset (HeightOneSpectrum (𝓞 E)))
    (x : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (w' : HeightOneSpectrum (𝓞 E)) :
    ((∏ w ∈ S, single w (x w) : (Af E)ˣ) : Af E) w' = if w' ∈ S then (x w' : w'.adicCompletion E) else 1 := by
  induction S using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Units.val_one, one_coord']; simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Units.val_mul, mul_coord', ih]
    by_cases h : w' = a
    · subst h; simp [ha, single_self]
    · rw [suppAt_single a (x a) w' h]; simp [h]

/- English proof (translation)
Establish `key : ∀ z : Af E, (∀ w : HeightOneSpectrum (𝓞 E), Valued.v (z w - 1) ≤ WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ))) → z ∈ hatO c` using `fun z h => (GlobalTheory.T.mem_completedOrder_iff_placewise E c hc z).2 ⟨1, one_mem _, fun w => by rw [one_coord', map_one], h⟩`. Use `⟨key _ fun w => (hz w).le, key _ fun w => ?_⟩` and prove the remaining obligations. Establish `h1 : Valued.v ((z : Af E) w - 1) < Valued.v (1 : w.adicCompletion E)`. Rewrite using `[map_one]`. Conclude with `(hz w).trans_le (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)`.

Establish `hv : Valued.v ((z : Af E) w) = 1`. Use `Valuation.map_eq_of_sub_lt _ h1` as an intermediate fact. Rewrite `this` using `[map_one]`. Then use the resulting hypothesis. Establish `hz0 : (z : Af E) w ≠ 0` using `by rw [← coe_coord]; exact (coord w z).ne_zero`. Use `show Valued.v ((↑z⁻¹ : Af E) w - 1) ≤ _`.

Rewrite using `[inv_coord']`. Establish `he : ((z : Af E) w)⁻¹ - 1 = -(((z : Af E) w - 1) * ((z : Af E) w)⁻¹)` using `by field_simp; ring`. Rewrite using `[he, Valuation.map_neg, map_mul, map_inv₀, hv, inv_one, mul_one]`. Conclude with `(hz w).le`.
-/
theorem mem_hatOUnits [IsCMField E] {c : Ideal (OF E)} (hc : c ≠ ⊥) (z : (Af E)ˣ)
    (hz : ∀ w : HeightOneSpectrum (𝓞 E), Valued.v ((z : Af E) w - 1) <
      WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ))) :
    z ∈ hatOUnits c := by
  have key : ∀ z : Af E, (∀ w : HeightOneSpectrum (𝓞 E), Valued.v (z w - 1) ≤
      WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ))) → z ∈ hatO c :=
    fun z h => (GlobalTheory.T.mem_completedOrder_iff_placewise E c hc z).2 ⟨1, one_mem _, fun w => by rw [one_coord', map_one], h⟩
  refine ⟨key _ fun w => (hz w).le, key _ fun w => ?_⟩
  have h1 : Valued.v ((z : Af E) w - 1) < Valued.v (1 : w.adicCompletion E) := by
    rw [map_one]
    exact (hz w).trans_le (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  have hv : Valued.v ((z : Af E) w) = 1 := by
    have := Valuation.map_eq_of_sub_lt _ h1
    rwa [map_one] at this
  have hz0 : (z : Af E) w ≠ 0 := by rw [← coe_coord]; exact (coord w z).ne_zero
  show Valued.v ((↑z⁻¹ : Af E) w - 1) ≤ _
  rw [inv_coord']
  have he : ((z : Af E) w)⁻¹ - 1 = -(((z : Af E) w - 1) * ((z : Af E) w)⁻¹) := by
    field_simp; ring
  rw [he, Valuation.map_neg, map_mul, map_inv₀, hv, inv_one, mul_one]
  exact (hz w).le

/- English proof (translation)
Introduce `E _ _ _ c l hc hl q`. Establish `hfin : {w : HeightOneSpectrum (𝓞 E) | (l : 𝓞 E) ∈ w.asIdeal}.Finite`. Establish `hl0 : Ideal.span {(l : 𝓞 E)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hl.ne_zero` after adjusting the coercions.

Conclude with `(Ideal.finite_factors hl0).subset fun w hw => Ideal.dvd_span_singleton.2 hw`. Take `⟨y0, rfl⟩` from `QuotientGroup.mk_surjective q`. Take `⟨a, ha, -⟩` from `PI.FinOrdValD.WA.weakApprox_units hfin.toFinset (fun w => (coord w y0)⁻¹) (fun w => (multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ))`. Use `set A : (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom a with hAdef`. Use `set y1 : (Af E)ˣ := A * y0 with hy1`.

Use `set u : (Af E)ˣ := ∏ w ∈ hfin.toFinset, single w (coord w y1) with hudef`. Establish `hA : A ∈ princ ⊔ hatOUnits c` using `Subgroup.mem_sup_left ⟨a, rfl⟩`. Establish `hu : u ∈ princ ⊔ hatOUnits c`. Use `Subgroup.mem_sup_right (mem_hatOUnits hc u fun w => ?_)` and prove the remaining obligations. Rewrite using `[hudef, prod_single_coord]`.

Use `split_ifs with hw`. Rewrite using `[coe_coord, hy1, Units.val_mul, mul_coord']`. Establish `hAw : (A : Af E) w = algebraMap E (w.adicCompletion E) (a : E)` using `rfl`. Use `ha w hw` as an intermediate fact. Rewrite using `[hAw]`.

Simplify `this` using `[Units.val_inv_eq_inv_val, coe_coord]`. Rewrite using `[sub_self, map_zero]`. Conclude with `WithZero.exp_pos.bot_lt`. Use `⟨y1 * u⁻¹, ?_, fun w hw => ?_⟩` and prove the remaining obligations. Rewrite using `[QuotientGroup.mk_mul, QuotientGroup.mk_inv, hy1, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff A).2 hA, (QuotientGroup.eq_one_iff u).2 hu, one_mul, inv_one, mul_one]`.

Establish `hwT : w ∈ hfin.toFinset` using `hfin.mem_toFinset.2 hw`. Rewrite using `[Units.val_mul, mul_coord', inv_coord', hudef, prod_single_coord, if_pos hwT, coe_coord]`. Conclude with `mul_inv_cancel₀ (by rw [← coe_coord]; exact (coord w y1).ne_zero)`.
-/
theorem exists_rep_trivial_above : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (l : ℕ),
    c ≠ ⊥ → l.Prime → ∀ q : PicO c, ∃ y : (Af E)ˣ, (QuotientGroup.mk y : PicO c) = q ∧
      ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → (y : Af E) w = 1 := by
  intro E _ _ _ c l hc hl q
  classical
  have hfin : {w : HeightOneSpectrum (𝓞 E) | (l : 𝓞 E) ∈ w.asIdeal}.Finite := by
    have hl0 : Ideal.span {(l : 𝓞 E)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hl.ne_zero
    exact (Ideal.finite_factors hl0).subset fun w hw => Ideal.dvd_span_singleton.2 hw
  obtain ⟨y0, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨a, ha, -⟩ := PI.FinOrdValD.WA.weakApprox_units hfin.toFinset (fun w => (coord w y0)⁻¹)
    (fun w => (multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ))
  set A : (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom a with hAdef
  set y1 : (Af E)ˣ := A * y0 with hy1
  set u : (Af E)ˣ := ∏ w ∈ hfin.toFinset, single w (coord w y1) with hudef
  have hA : A ∈ princ ⊔ hatOUnits c := Subgroup.mem_sup_left ⟨a, rfl⟩
  have hu : u ∈ princ ⊔ hatOUnits c := by
    refine Subgroup.mem_sup_right (mem_hatOUnits hc u fun w => ?_)
    rw [hudef, prod_single_coord]
    split_ifs with hw
    · rw [coe_coord, hy1, Units.val_mul, mul_coord']
      have hAw : (A : Af E) w = algebraMap E (w.adicCompletion E) (a : E) := rfl
      have := ha w hw
      rw [hAw]
      simpa [Units.val_inv_eq_inv_val, coe_coord] using this
    · rw [sub_self, map_zero]; exact WithZero.exp_pos.bot_lt
  refine ⟨y1 * u⁻¹, ?_, fun w hw => ?_⟩
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hy1, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff A).2 hA, (QuotientGroup.eq_one_iff u).2 hu, one_mul, inv_one, mul_one]
  · have hwT : w ∈ hfin.toFinset := hfin.mem_toFinset.2 hw
    rw [Units.val_mul, mul_coord', inv_coord', hudef, prod_single_coord, if_pos hwT, coe_coord]
    exact mul_inv_cancel₀ (by rw [← coe_coord]; exact (coord w y1).ne_zero)

end GlobalTheory.CMVal.TrivAbove

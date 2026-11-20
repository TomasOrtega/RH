import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.OhatCompact
import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.AdeleIntA

noncomputable section

namespace PIW.ClassFinD.Icf

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Establish `: (x * y) w = x w * y w` using `rfl`. Rewrite using `[this, map_mul]`.
-/
theorem v_mul (x y : FiniteAdeleRing (𝓞 F) F) (w : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((x * y) w) = Valued.v (x w) * Valued.v (y w) := by
  have : (x * y) w = x w * y w := rfl
  rw [this, map_mul]

/- English proof (translation)
The claim follows from `Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.val_R w r`.
-/
theorem v_algR (r : 𝓞 F) (w : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r) w) = w.intValuation r :=
  Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.val_R w r

/- English proof (translation)
The claim follows from `valuedAdicCompletion_eq_valuation' w f`.
-/
theorem v_algF (f : F) (w : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) f) w) = w.valuation F f :=
  valuedAdicCompletion_eq_valuation' w f

/- English proof (translation)
Rewrite using `[← v_mul, Units.mul_inv]`. Establish `: (1 : FiniteAdeleRing (𝓞 F) F) w = 1` using `rfl`. Rewrite using `[this, map_one]`.
-/
theorem v_unit_mul_inv (b : (FiniteAdeleRing (𝓞 F) F)ˣ) (w : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w) * Valued.v (((b⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
      FiniteAdeleRing (𝓞 F) F) w) = 1 := by
  rw [← v_mul, Units.mul_inv]
  have : (1 : FiniteAdeleRing (𝓞 F) F) w = 1 := rfl
  rw [this, map_one]

/- English proof (translation)
Introduce `h`. Use `v_unit_mul_inv b w` as an intermediate fact. Rewrite `this` using `[h, zero_mul]`. Conclude with `zero_ne_one this`.
-/
theorem v_unit_ne (b : (FiniteAdeleRing (𝓞 F) F)ˣ) (w : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w) ≠ 0 := by
  intro h
  have := v_unit_mul_inv b w
  rw [h, zero_mul] at this
  exact zero_ne_one this

/- English proof (translation)
The claim follows from `(eq_inv_of_mul_eq_one_right (v_unit_mul_inv b w))`.
-/
theorem v_inv (b : (FiniteAdeleRing (𝓞 F) F)ˣ) (w : HeightOneSpectrum (𝓞 F)) :
    Valued.v (((b⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w) =
      (Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w))⁻¹ :=
  (eq_inv_of_mul_eq_one_right (v_unit_mul_inv b w))

def latI (b : (FiniteAdeleRing (𝓞 F) F)ˣ) : Ideal (𝓞 F) where
  carrier := {x | ∀ w : HeightOneSpectrum (𝓞 F), w.intValuation x ≤ Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w)}
  add_mem' := fun {x y} hx hy w => (Valuation.map_add _ x y).trans (max_le (hx w) (hy w))
  zero_mem' := fun w => by rw [map_zero]; exact zero_le
  smul_mem' := fun c x hx w => by
    rw [smul_eq_mul, map_mul]
    exact (mul_le_of_le_one_left' (w.intValuation_le_one c)).trans (hx w)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_latI {b : (FiniteAdeleRing (𝓞 F) F)ˣ} {x : 𝓞 F} :
    x ∈ latI b ↔ ∀ w : HeightOneSpectrum (𝓞 F), w.intValuation x ≤ Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w) :=
  Iff.rfl

/- English proof (translation)
Take `⟨r, hr, h⟩` from `Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_den (((b⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))`. Use `⟨r, hr, fun w => ?_⟩` and prove the remaining obligations. Establish `h1 : Valued.v ((algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r * ((b⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) w) ≤ 1` using `h w`. Rewrite `h1` using `[v_mul, v_algR, v_inv]`. Establish `hpos : 0 < Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w)` using `zero_lt_iff.2 (v_unit_ne b w)`.

Rewrite `h1` using `[mul_inv_le_iff₀ hpos, one_mul]`. Conclude with `h1`.
-/
theorem exists_ne_zero_mem (b : (FiniteAdeleRing (𝓞 F) F)ˣ) : ∃ r : 𝓞 F, r ≠ 0 ∧ r ∈ latI b := by
  obtain ⟨r, hr, h⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_den
    (((b⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
  refine ⟨r, hr, fun w => ?_⟩
  have h1 : Valued.v ((algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r *
      ((b⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) w) ≤ 1 := h w
  rw [v_mul, v_algR, v_inv] at h1
  have hpos : 0 < Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w) := zero_lt_iff.2 (v_unit_ne b w)
  rw [mul_inv_le_iff₀ hpos, one_mul] at h1
  exact h1

/- English proof (translation)
Take `⟨r0, hr0, hr0I⟩` from `exists_ne_zero_mem b`. Take `⟨π, hπv, hπ0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot`. Establish `hr : r0 * π ≠ 0` using `mul_ne_zero hr0 hπ0`. Take `⟨a, ha⟩` from `Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_approx (b : FiniteAdeleRing (𝓞 F) F) (fun w => hb w) (r0 * π) hr`. Establish `hA : ∀ w : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F a)) = w.intValuation a` using `fun w => Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.val_R w a`.

Establish `hsmall : ∀ w : HeightOneSpectrum (𝓞 F), w.intValuation (r0 * π) ≤ w.intValuation r0`. Introduce `w`. Rewrite using `[map_mul]`. Conclude with `mul_le_of_le_one_right' (w.intValuation_le_one π)`. Use `⟨a, fun w => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hA w]`. Establish `e : algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F a) = (b : FiniteAdeleRing (𝓞 F) F) w - ((b : FiniteAdeleRing (𝓞 F) F) w - algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F a))`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `(Valuation.map_sub _ _ _).trans (max_le le_rfl ?_)` and prove the remaining obligations.

Conclude with `(ha w).trans ((hsmall w).trans (hr0I w))`. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Establish `hbpos : 0 < Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v)` using `zero_lt_iff.2 (v_unit_ne b v)`. Establish `hπlt : v.intValuation π < 1` using `(v.intValuation_lt_one_iff_mem π).2 hπv`.

Establish `h2 : Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v)`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hr0I v`. Use `_ < Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v) * 1 := by`. Conclude with `mul_lt_mul_of_pos_left hπlt hbpos`.

Use `_ = _ := mul_one _`. Establish `e : (b : FiniteAdeleRing (𝓞 F) F) v = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) + ((b : FiniteAdeleRing (𝓞 F) F) v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))`. Expand and normalize the polynomial expressions, which then agree. Establish `h3` using `Valuation.map_add (Valued.v : Valuation (v.adicCompletion F) _) (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) ((b : FiniteAdeleRing (𝓞 F) F) v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))`. Rewrite `h3` using `[← e, hA v]`.

Conclude with `absurd h3 (not_le.2 (max_lt hlt h2))`.
-/
theorem approx (b : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hb : ∀ w : HeightOneSpectrum (𝓞 F), Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w) ≤ 1)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ a : 𝓞 F, a ∈ latI b ∧ Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v) ≤ v.intValuation a := by
  obtain ⟨r0, hr0, hr0I⟩ := exists_ne_zero_mem b
  obtain ⟨π, hπv, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hr : r0 * π ≠ 0 := mul_ne_zero hr0 hπ0
  obtain ⟨a, ha⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_approx (b : FiniteAdeleRing (𝓞 F) F)
    (fun w => hb w) (r0 * π) hr
  have hA : ∀ w : HeightOneSpectrum (𝓞 F),
      Valued.v (algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F a)) = w.intValuation a :=
    fun w => Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.val_R w a
  have hsmall : ∀ w : HeightOneSpectrum (𝓞 F), w.intValuation (r0 * π) ≤ w.intValuation r0 := by
    intro w
    rw [map_mul]
    exact mul_le_of_le_one_right' (w.intValuation_le_one π)
  refine ⟨a, fun w => ?_, ?_⟩
  · rw [← hA w]
    have e : algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F a) =
        (b : FiniteAdeleRing (𝓞 F) F) w -
          ((b : FiniteAdeleRing (𝓞 F) F) w - algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F a)) := by
      ring
    rw [e]
    refine (Valuation.map_sub _ _ _).trans (max_le le_rfl ?_)
    exact (ha w).trans ((hsmall w).trans (hr0I w))
  · by_contra hlt
    rw [not_le] at hlt
    have hbpos : 0 < Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v) := zero_lt_iff.2 (v_unit_ne b v)
    have hπlt : v.intValuation π < 1 := (v.intValuation_lt_one_iff_mem π).2 hπv
    have h2 : Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v -
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v) := by
      calc _ ≤ v.intValuation (r0 * π) := ha v
        _ = v.intValuation r0 * v.intValuation π := map_mul _ _ _
        _ ≤ Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v) * v.intValuation π := by
          gcongr
          exact hr0I v
        _ < Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v) * 1 := by
          exact mul_lt_mul_of_pos_left hπlt hbpos
        _ = _ := mul_one _
    have e : (b : FiniteAdeleRing (𝓞 F) F) v = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) +
        ((b : FiniteAdeleRing (𝓞 F) F) v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) := by
      ring
    have h3 := Valuation.map_add (Valued.v : Valuation (v.adicCompletion F) _)
      (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))
      ((b : FiniteAdeleRing (𝓞 F) F) v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))
    rw [← e, hA v] at h3
    exact absurd h3 (not_le.2 (max_lt hlt h2))

/- English proof (translation)
Take `⟨a, haI, hav⟩` from `approx b hb v`. Take `⟨z, hzI, hz⟩` from `(Ideal.span_singleton_mul_le_span_singleton_mul.1 h) a haI`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hzI v`.
-/
theorem val_le_of_le (b b' : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hb : ∀ w : HeightOneSpectrum (𝓞 F), Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w) ≤ 1)
    {x y : 𝓞 F} (h : Ideal.span {x} * latI b ≤ Ideal.span {y} * latI b') (v : HeightOneSpectrum (𝓞 F)) :
    v.intValuation x * Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v) ≤
      v.intValuation y * Valued.v ((b' : FiniteAdeleRing (𝓞 F) F) v) := by
  obtain ⟨a, haI, hav⟩ := approx b hb v
  obtain ⟨z, hzI, hz⟩ := (Ideal.span_singleton_mul_le_span_singleton_mul.1 h) a haI
  calc v.intValuation x * Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v)
      ≤ v.intValuation x * v.intValuation a := by gcongr
    _ = v.intValuation (x * a) := (map_mul _ _ _).symm
    _ = v.intValuation (y * z) := by rw [hz]
    _ = v.intValuation y * v.intValuation z := map_mul _ _ _
    _ ≤ v.intValuation y * Valued.v ((b' : FiniteAdeleRing (𝓞 F) F) v) := by
      gcongr
      exact hzI v

end PIW.ClassFinD.Icf

end

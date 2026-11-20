import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzApprox
import Development.DiscreteGroups.GlobalIrreducibility.DzNormV
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

set_option linter.all false

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E' Ω : Type} [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
  {A : ValuationSubring Ω} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A w'}

/- English proof (translation)
Establish `h1` using `ha'.ord_eq (ineIncl h' t)`. Rewrite `h1` using `[GlobalTheory.SmGL.SphCompletion.ord_completion, deg_ineIncl]`. Establish `hv0 : Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') ≠ 0`. Rewrite using `[Ne, Valuation.zero_iff]`. Conclude with `Units.ne_zero _`.

Establish `hl : WithZero.log (Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E')) = 0`. Simplify using `using h1`. Rewrite using `[← WithZero.exp_log hv0, hl, WithZero.exp_zero]`.
-/
theorem val_artin_ine {a' : Weil h' →* (w'.adicCompletion E')ˣ} (ha' : IsLocalArtin h' a') (t : Ine (F := E') A) :
    Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') = 1 := by
  have h1 := ha'.ord_eq (ineIncl h' t)
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion, deg_ineIncl] at h1
  have hv0 : Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') ≠ 0 := by
    rw [Ne, Valuation.zero_iff]; exact Units.ne_zero _
  have hl : WithZero.log (Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E')) = 0 := by
    simpa using h1
  rw [← WithZero.exp_log hv0, hl, WithZero.exp_zero]

/- English proof (translation)
Establish `e : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) = w'.valuation E' (x : E')` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E') w' (x : E')`. Rewrite using `[e]`. Conclude with `(HeightOneSpectrum.valuation_lt_one_iff_mem (K := E') w' x).mpr hx`.
-/
theorem val_alg_lt_one_of_mem (x : 𝓞 E') (hx : x ∈ w'.asIdeal) :
    Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) < 1 := by
  have e : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) = w'.valuation E' (x : E') :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E') w' (x : E')
  rw [e]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E') w' x).mpr hx

/- English proof (translation)
Establish `e : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) = w'.valuation E' (x : E')` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E') w' (x : E')`. Rewrite using `[e]`. Conclude with `w'.valuation_le_one x`.
-/
theorem val_alg_le_one (x : 𝓞 E') : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) ≤ 1 := by
  have e : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) = w'.valuation E' (x : E') :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E') w' (x : E')
  rw [e]
  exact w'.valuation_le_one x

variable {a' : Weil h' →* (w'.adicCompletion E')ˣ} (ha' : IsLocalArtin h' a') {K : Type} [Field K]
  {red : 𝓞 E' →+* K} (hk : RingHom.ker red = w'.asIdeal)
include ha' hk

/- English proof (translation)
Introduce `h0`. Establish `hxm : x ∈ w'.asIdeal` using `by rw [← hk, RingHom.mem_ker]; exact h0`. Establish `hlt : Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') < 1`. Establish `e : ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') = (((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) + algebraMap E' (w'.adicCompletion E') (x : E')` using `by ring`. Rewrite using `[e]`.

Conclude with `Valuation.map_add_lt _ hx (val_alg_lt_one_of_mem x hxm)`. Rewrite `hlt` using `[val_artin_ine ha' t]`. Conclude with `lt_irrefl _ hlt`.
-/
theorem red_ne_zero_of_approx {t : Ine (F := E') A} {x : 𝓞 E'}
    (hx : Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1) :
    red x ≠ 0 := by
  intro h0
  have hxm : x ∈ w'.asIdeal := by rw [← hk, RingHom.mem_ker]; exact h0
  have hlt : Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') < 1 := by
    have e : ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') =
        (((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') -
          algebraMap E' (w'.adicCompletion E') (x : E')) + algebraMap E' (w'.adicCompletion E') (x : E') := by ring
    rw [e]
    exact Valuation.map_add_lt _ hx (val_alg_lt_one_of_mem x hxm)
  rw [val_artin_ine ha' t] at hlt
  exact lt_irrefl _ hlt

/- English proof (translation)
Rewrite using `[← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, hk]`. Apply `mem_of_val_lt_one w'` to reduce the goal to its premises. Establish `e : algebraMap E' (w'.adicCompletion E') (((x - x' : 𝓞 E')) : E') = ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x' : E')) - ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E'))`. Rewrite using `[show (((x - x' : 𝓞 E')) : E') = (x : E') - (x' : E') by push_cast; ring, map_sub]; ring`. Rewrite using `[e]`.

Conclude with `lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hx' hx)`.
-/
theorem red_eq_of_approx {t : Ine (F := E') A} {x x' : 𝓞 E'}
    (hx : Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1)
    (hx' : Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x' : E')) < 1) :
    red x = red x' := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, hk]
  apply mem_of_val_lt_one w'
  have e : algebraMap E' (w'.adicCompletion E') (((x - x' : 𝓞 E')) : E') =
      ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x' : E')) -
        ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) := by
    rw [show (((x - x' : 𝓞 E')) : E') = (x : E') - (x' : E') by push_cast; ring, map_sub]; ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hx' hx)

/- English proof (translation)
Establish `hex : ∀ t : Ine (F` using `E') A, ∃ x : 𝓞 E', Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 := fun t => exists_int_approx_compl w' _ (val_artin_ine ha' t).le`. Use `choose x hx using hex`. Use `⟨MonoidHom.mk' (fun t => Units.mk0 (red (x t)) (red_ne_zero_of_approx ha' hk (hx t))) ?_, fun t y hy => red_eq_of_approx ha' hk (hx t) hy⟩` and prove the remaining obligations. Introduce `s t`. Use `ext`.

Simplify using `only [Units.val_mk0, Units.val_mul]`. Rewrite using `[← map_mul]`. Apply `red_eq_of_approx ha' hk (hx (s * t))` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, Units.val_mul]`. Establish `e : ((a' (ineIncl h' s) : w'.adicCompletion E') * (a' (ineIncl h' t) : w'.adicCompletion E')) - algebraMap E' (w'.adicCompletion E') (((x s * x t : 𝓞 E')) : E') = (a' (ineIncl h' s) : w'.adicCompletion E') * ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicComp …`.

Rewrite using `[show (((x s * x t : 𝓞 E')) : E') = (x s : E') * (x t : E') by push_cast; ring, map_mul]; ring`. Rewrite using `[e]`. Use `Valuation.map_add_lt _ ?_ ?_` and prove the remaining obligations. Rewrite using `[map_mul, val_artin_ine ha' s, one_mul]`. Conclude with `hx t`.

Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' (val_alg_le_one (x t))) (hx s)`.
-/
theorem exists_resHom : ∃ R : Ine (F := E') A →* Kˣ, ∀ (t : Ine (F := E') A) (x : 𝓞 E'),
    Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
      ((R t : Kˣ) : K) = red x := by
  have hex : ∀ t : Ine (F := E') A, ∃ x : 𝓞 E',
      Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 :=
    fun t => exists_int_approx_compl w' _ (val_artin_ine ha' t).le
  choose x hx using hex
  refine ⟨MonoidHom.mk' (fun t => Units.mk0 (red (x t)) (red_ne_zero_of_approx ha' hk (hx t))) ?_,
    fun t y hy => red_eq_of_approx ha' hk (hx t) hy⟩
  intro s t
  ext
  simp only [Units.val_mk0, Units.val_mul]
  rw [← map_mul]
  apply red_eq_of_approx ha' hk (hx (s * t))
  rw [map_mul, map_mul, Units.val_mul]
  have e : ((a' (ineIncl h' s) : w'.adicCompletion E') * (a' (ineIncl h' t) : w'.adicCompletion E')) -
      algebraMap E' (w'.adicCompletion E') (((x s * x t : 𝓞 E')) : E') =
      (a' (ineIncl h' s) : w'.adicCompletion E') *
        ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x t : E')) +
      ((a' (ineIncl h' s) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x s : E')) *
        algebraMap E' (w'.adicCompletion E') (x t : E') := by
    rw [show (((x s * x t : 𝓞 E')) : E') = (x s : E') * (x t : E') by push_cast; ring, map_mul]; ring
  rw [e]
  refine Valuation.map_add_lt _ ?_ ?_
  · rw [map_mul, val_artin_ine ha' s, one_mul]; exact hx t
  · rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_alg_le_one (x t))) (hx s)

end DiscreteGroups.sglob.DzType

end

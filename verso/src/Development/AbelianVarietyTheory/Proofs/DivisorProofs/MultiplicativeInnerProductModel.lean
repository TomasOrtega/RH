import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchurPolar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

/- English proof (translation)
Introduce `v v'`. Take `⟨ia, ea⟩` from `ha v v'`. Take `⟨ib, eb⟩` from `hb v v'`. Take `⟨is, es⟩` from `hs v v'`. Take `⟨it, et⟩` from `ht v v'`.

Establish `e : (fun g => star (T v g) * T' v' g) = fun g => (1 / 2 : ℂ) * ((star ((T + T') v g) * (T + T') v' g - star (T v g) * T v' g - star (T' v g) * T' v' g) - Complex.I * (star ((T + Complex.I • T') v g) * (T + Complex.I • T') v' g - star (T v g) * T v' g - star (T' v g) * T' v' g))`. Use function extensionality and compare the values at `g`. Use `show _ = (1 / 2 : ℂ) * ((star (T v g + T' v g) * (T v' g + T' v' g) - star (T v g) * T v' g - star (T' v g) * T' v' g) - Complex.I * (star (T v g + Complex.I * T' v g) * (T v' g + Complex.I * T' v' g) - star (T v g) * T v' g - star (T' v g) * T' v' g))`. Establish `hI : star Complex.I = - Complex.I` using `by simp`. Rewrite using `[star_add, star_add, star_mul, hI]`.

Establish `h2` using `Complex.I_mul_I`. Take the linear combination `(1 / 2 : ℂ) * (star (T v g) * T' v' g - star (T' v g) * T v' g - Complex.I * star (T' v g) * T' v' g) * h2`. Establish `i1 : Integrable (fun g => star ((T + T') v g) * (T + T') v' g - star (T v g) * T v' g) (μ.restrict 𝓕)` using `is.sub ia`. Establish `i2 : Integrable (fun g => star ((T + T') v g) * (T + T') v' g - star (T v g) * T v' g - star (T' v g) * T' v' g) (μ.restrict 𝓕)` using `i1.sub ib`. Establish `i3 : Integrable (fun g => star ((T + Complex.I • T') v g) * (T + Complex.I • T') v' g - star (T v g) * T v' g) (μ.restrict 𝓕)` using `it.sub ia`.

Establish `i4 : Integrable (fun g => star ((T + Complex.I • T') v g) * (T + Complex.I • T') v' g - star (T v g) * T v' g - star (T' v g) * T' v' g) (μ.restrict 𝓕)` using `i3.sub ib`. Establish `i5` using `i4.const_mul Complex.I`. Rewrite using `[e]`. Use `⟨(i2.sub i5).const_mul _, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_const_mul, integral_sub i2 i5, integral_const_mul, integral_sub i1 ib, integral_sub i3 ib, integral_sub is ia, integral_sub it ia, ea, eb, es, et]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_of_diag (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M)
    {a b s t : ℂ} (ha : IsMultIP M μ 𝓕 T T a) (hb : IsMultIP M μ 𝓕 T' T' b)
    (hs : IsMultIP M μ 𝓕 (T + T') (T + T') s)
    (ht : IsMultIP M μ 𝓕 (T + Complex.I • T') (T + Complex.I • T') t) :
    IsMultIP M μ 𝓕 T T' ((1 / 2) * ((s - a - b) - Complex.I * (t - a - b))) := by
  intro v v'
  obtain ⟨ia, ea⟩ := ha v v'
  obtain ⟨ib, eb⟩ := hb v v'
  obtain ⟨is, es⟩ := hs v v'
  obtain ⟨it, et⟩ := ht v v'
  have e : (fun g => star (T v g) * T' v' g) =
      fun g => (1 / 2 : ℂ) * ((star ((T + T') v g) * (T + T') v' g - star (T v g) * T v' g
        - star (T' v g) * T' v' g) - Complex.I * (star ((T + Complex.I • T') v g) * (T + Complex.I • T') v' g
        - star (T v g) * T v' g - star (T' v g) * T' v' g)) := by
    funext g
    show _ = (1 / 2 : ℂ) * ((star (T v g + T' v g) * (T v' g + T' v' g) - star (T v g) * T v' g
        - star (T' v g) * T' v' g) - Complex.I * (star (T v g + Complex.I * T' v g) * (T v' g + Complex.I * T' v' g)
        - star (T v g) * T v' g - star (T' v g) * T' v' g))
    have hI : star Complex.I = - Complex.I := by simp
    rw [star_add, star_add, star_mul, hI]
    have h2 := Complex.I_mul_I
    linear_combination (1 / 2 : ℂ) * (star (T v g) * T' v' g - star (T' v g) * T v' g
      - Complex.I * star (T' v g) * T' v' g) * h2
  have i1 : Integrable (fun g => star ((T + T') v g) * (T + T') v' g - star (T v g) * T v' g) (μ.restrict 𝓕) :=
    is.sub ia
  have i2 : Integrable (fun g => star ((T + T') v g) * (T + T') v' g - star (T v g) * T v' g
      - star (T' v g) * T' v' g) (μ.restrict 𝓕) := i1.sub ib
  have i3 : Integrable (fun g => star ((T + Complex.I • T') v g) * (T + Complex.I • T') v' g
      - star (T v g) * T v' g) (μ.restrict 𝓕) := it.sub ia
  have i4 : Integrable (fun g => star ((T + Complex.I • T') v g) * (T + Complex.I • T') v' g
      - star (T v g) * T v' g - star (T' v g) * T' v' g) (μ.restrict 𝓕) := i3.sub ib
  have i5 := i4.const_mul Complex.I
  rw [e]
  refine ⟨(i2.sub i5).const_mul _, ?_⟩
  rw [integral_const_mul, integral_sub i2 i5, integral_const_mul, integral_sub i1 ib, integral_sub i3 ib,
    integral_sub is ia, integral_sub it ia, ea, eb, es, et]
  ring

/- English proof (translation)
Introduce `D V S M μ 𝓕 HM U h x y`. Establish `hip` using `h.2.2`. Establish `hd : ∀ z : HM.H, ∃ c, IsMultIP M μ 𝓕 (HM.e z) (HM.e z) c`. Introduce `z`. Distinguish the cases in `hz : z = 0`.

Use `⟨0, fun v v' => ?_⟩` and prove the remaining obligations. Substitute `hz` using the available equality. Simplify using the standard rewrite rules. Assume the negation of the conclusion as `hn`. Use `hip z z` as an intermediate fact.

Unfold `ipM at this`. Rewrite `this` using `[dif_neg hn]`. Conclude with `hz (inner_self_eq_zero.1 this)`. Rewrite using `[hip]`. Apply `ipM_spec` to reduce the goal to its premises.

Take `⟨a, ha⟩` from `hd x`. Take `⟨b, hb⟩` from `hd y`. Take `⟨s, hs⟩` from `hd (x + y)`. Take `⟨t, ht⟩` from `hd (x + Complex.I • y)`. Rewrite `hs`, `ht` using `[map_add]`.

Rewrite `ht` using `[map_smul]`. Conclude with `⟨_, exists_of_diag M μ 𝓕 _ _ ha hb hs ht⟩`.
-/
theorem isMultiplicityInner_inner : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (HM : HMod (MMap M)) (U : Submodule ℂ (MMap M)), HM.Is U (ipM M μ 𝓕) → ∀ x y : HM.H, IsMultIP M μ 𝓕 (HM.e x) (HM.e y) (inner ℂ x y) := by
  intro D V S M μ 𝓕 HM U h x y
  have hip := h.2.2
  have hd : ∀ z : HM.H, ∃ c, IsMultIP M μ 𝓕 (HM.e z) (HM.e z) c := by
    intro z
    by_cases hz : z = 0
    · refine ⟨0, fun v v' => ?_⟩
      subst hz
      simp
    · by_contra hn
      have := hip z z
      unfold ipM at this
      rw [dif_neg hn] at this
      exact hz (inner_self_eq_zero.1 this)
  rw [hip]
  apply ipM_spec
  obtain ⟨a, ha⟩ := hd x
  obtain ⟨b, hb⟩ := hd y
  obtain ⟨s, hs⟩ := hd (x + y)
  obtain ⟨t, ht⟩ := hd (x + Complex.I • y)
  rw [map_add] at hs ht
  rw [map_smul] at ht
  exact ⟨_, exists_of_diag M μ 𝓕 _ _ ha hb hs ht⟩

end GlobalTheory.SchurPolar

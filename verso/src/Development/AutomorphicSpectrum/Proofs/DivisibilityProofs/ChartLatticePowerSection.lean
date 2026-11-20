import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalAmple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top.EffNm

/- English proof (translation)
Establish `hI : IsIntegral R u` using `hu`. Take `⟨S, hS⟩` from `hI.fg_adjoin_singleton`. Establish `key : ∀ x ∈ Algebra.adjoin R {u}, ∃ m : ℕ, h ^ m * x ∈ R`. Introduce `x hx`. Proceed by induction on `hx using Algebra.adjoin_induction with`.

Consider the case `mem x hx`. Rewrite `hx` using `[Set.mem_singleton_iff]`. Substitute `hx` using the available equality. Conclude with `⟨1, by rw [pow_one, mul_comm, e]; exact hg⟩`. Consider the case `algebraMap r => exact ⟨0, by simpa using r.2⟩`.

Consider the case `add x z _ _ ihx ihz`. Take `⟨m₁, h₁⟩` from `ihx`. Take `⟨m₂, h₂⟩` from `ihz`. Use `⟨m₁ + m₂, ?_⟩` and prove the remaining obligations. Establish `e' : h ^ (m₁ + m₂) * (x + z) = h ^ m₂ * (h ^ m₁ * x) + h ^ m₁ * (h ^ m₂ * z)`.

Rewrite using `[pow_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e']`. Conclude with `add_mem (mul_mem (pow_mem hh _) h₁) (mul_mem (pow_mem hh _) h₂)`. Consider the case `mul x z _ _ ihx ihz`.

Take `⟨m₁, h₁⟩` from `ihx`. Take `⟨m₂, h₂⟩` from `ihz`. Use `⟨m₁ + m₂, ?_⟩` and prove the remaining obligations. Establish `e' : h ^ (m₁ + m₂) * (x * z) = (h ^ m₁ * x) * (h ^ m₂ * z)`. Rewrite using `[pow_add]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e']`. Conclude with `mul_mem h₁ h₂`. Establish `hfin : ∀ T : Finset Ω, (∀ x ∈ T, x ∈ Algebra.adjoin R {u}) → ∃ M : ℕ, ∀ x ∈ T, h ^ M * x ∈ R`. Introduce `T`.

Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => exact fun _ => ⟨0, by simp⟩`. Consider the case `insert x T _ ih`. Introduce `hT`. Take `⟨M, hM⟩` from `ih fun z hz => hT z (Finset.mem_insert_of_mem hz)`.

Take `⟨m, hm⟩` from `key x (hT x (Finset.mem_insert_self x T))`. Use `⟨M + m, fun z hz => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hz with rfl | hz` into its components or cases. Establish `e' : h ^ (M + m) * z = h ^ M * (h ^ m * z)` using `by rw [pow_add]; ring`. Rewrite using `[e']`.

Conclude with `mul_mem (pow_mem hh _) hm`. Establish `e' : h ^ (M + m) * z = h ^ m * (h ^ M * z)` using `by rw [pow_add]; ring`. Rewrite using `[e']`. Conclude with `mul_mem (pow_mem hh _) (hM z hz)`. Establish `hSsub : ∀ x ∈ S, x ∈ Algebra.adjoin R {u}`.

Introduce `x hx`. Establish `: x ∈ Subalgebra.toSubmodule (Algebra.adjoin R {u})` using `hS ▸ Submodule.subset_span hx`. Conclude with `this`. Take `⟨M, hM⟩` from `hfin S hSsub`. Use `⟨M, fun n => ?_⟩` and prove the remaining obligations.

Establish `hn : u ^ n ∈ Subalgebra.toSubmodule (Algebra.adjoin R {u})` using `pow_mem (Algebra.subset_adjoin (Set.mem_singleton u)) n`. Rewrite `hn` using `[← hS]`. Establish `hall : ∀ x ∈ Submodule.span R (S : Set Ω), h ^ M * x ∈ R`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx => exact hM x hx`. Consider the case `zero => simp`. Consider the case `add x z _ _ ihx ihz => rw [mul_add]`. Conclude with `add_mem ihx ihz`. Consider the case `smul r x _ ih`.

Establish `e' : h ^ M * r • x = (r : Ω) * (h ^ M * x)`. Rewrite using `[Algebra.smul_def]`. Use `show h ^ M * ((r : Ω) * x) = _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e']`.

Conclude with `mul_mem r.2 ih`. Conclude with `hall _ hn`.
-/
theorem exists_pow_mul_pow_mem {Ω : Type} [Field Ω] (R : Subalgebra ℤ Ω) {u g h : Ω}
    (hu : u ∈ integralClosure R Ω) (hg : g ∈ R) (hh : h ∈ R) (e : u * h = g) :
    ∃ M : ℕ, ∀ n : ℕ, h ^ M * u ^ n ∈ R := by
  classical
  have hI : IsIntegral R u := hu
  obtain ⟨S, hS⟩ := hI.fg_adjoin_singleton
  have key : ∀ x ∈ Algebra.adjoin R {u}, ∃ m : ℕ, h ^ m * x ∈ R := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨1, by rw [pow_one, mul_comm, e]; exact hg⟩
    | algebraMap r => exact ⟨0, by simpa using r.2⟩
    | add x z _ _ ihx ihz =>
      obtain ⟨m₁, h₁⟩ := ihx
      obtain ⟨m₂, h₂⟩ := ihz
      refine ⟨m₁ + m₂, ?_⟩
      have e' : h ^ (m₁ + m₂) * (x + z) = h ^ m₂ * (h ^ m₁ * x) + h ^ m₁ * (h ^ m₂ * z) := by
        rw [pow_add]; ring
      rw [e']
      exact add_mem (mul_mem (pow_mem hh _) h₁) (mul_mem (pow_mem hh _) h₂)
    | mul x z _ _ ihx ihz =>
      obtain ⟨m₁, h₁⟩ := ihx
      obtain ⟨m₂, h₂⟩ := ihz
      refine ⟨m₁ + m₂, ?_⟩
      have e' : h ^ (m₁ + m₂) * (x * z) = (h ^ m₁ * x) * (h ^ m₂ * z) := by
        rw [pow_add]; ring
      rw [e']
      exact mul_mem h₁ h₂
  have hfin : ∀ T : Finset Ω, (∀ x ∈ T, x ∈ Algebra.adjoin R {u}) →
      ∃ M : ℕ, ∀ x ∈ T, h ^ M * x ∈ R := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨0, by simp⟩
    | insert x T _ ih =>
      intro hT
      obtain ⟨M, hM⟩ := ih fun z hz => hT z (Finset.mem_insert_of_mem hz)
      obtain ⟨m, hm⟩ := key x (hT x (Finset.mem_insert_self x T))
      refine ⟨M + m, fun z hz => ?_⟩
      rcases Finset.mem_insert.1 hz with rfl | hz
      · have e' : h ^ (M + m) * z = h ^ M * (h ^ m * z) := by rw [pow_add]; ring
        rw [e']
        exact mul_mem (pow_mem hh _) hm
      · have e' : h ^ (M + m) * z = h ^ m * (h ^ M * z) := by rw [pow_add]; ring
        rw [e']
        exact mul_mem (pow_mem hh _) (hM z hz)
  have hSsub : ∀ x ∈ S, x ∈ Algebra.adjoin R {u} := by
    intro x hx
    have : x ∈ Subalgebra.toSubmodule (Algebra.adjoin R {u}) := hS ▸ Submodule.subset_span hx
    exact this
  obtain ⟨M, hM⟩ := hfin S hSsub
  refine ⟨M, fun n => ?_⟩
  have hn : u ^ n ∈ Subalgebra.toSubmodule (Algebra.adjoin R {u}) :=
    pow_mem (Algebra.subset_adjoin (Set.mem_singleton u)) n
  rw [← hS] at hn
  have hall : ∀ x ∈ Submodule.span R (S : Set Ω), h ^ M * x ∈ R := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hM x hx
    | zero => simp
    | add x z _ _ ihx ihz => rw [mul_add]; exact add_mem ihx ihz
    | smul r x _ ih =>
      have e' : h ^ M * r • x = (r : Ω) * (h ^ M * x) := by
        rw [Algebra.smul_def]
        show h ^ M * ((r : Ω) * x) = _
        ring
      rw [e']
      exact mul_mem r.2 ih
  exact hall _ hn

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Establish `hu` using `hs c hc`. Use `set u : Ω := s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) with hudef`. Take `⟨d, g, h, hg, hh, hh0, heq⟩` from `hb u`. Establish `hG` using `(GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.mem_chartLat_one y).1 (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.chartLat_form (y := y) hg) c hc`. Establish `hH` using `(GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.mem_chartLat_one y).1 (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.chartLat_form (y := y) hh) c hc`.

Take `⟨M, hM⟩` from `exists_pow_mul_pow_mem (chartRingZ y c) hu hG hH (by rw [heq]; ring)`. Use `⟨M • d, h ^ M, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_pow hh M, ?_, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow]`. Conclude with `pow_ne_zero _ hh0`. Establish `e' : aeval y (h ^ M) * s ^ n * ∏ k, y ⟨k, c k⟩ ^ (-((((M • d) k : ℕ) : ℤ) + n * a k)) = (aeval y h * ∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ))) ^ M * u ^ n`.

Establish `e2 : ∏ k, y ⟨k, c k⟩ ^ (-((((M • d) k : ℕ) : ℤ) + n * a k)) = (∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ))) ^ M * (∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))) ^ n`. Rewrite using `[← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ (hc k)]`. Use `congr 1`.

Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2, map_pow, hudef, mul_pow, mul_pow]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e']`. Conclude with `hM n`.
-/
theorem exists_form_at (y : (Σ k, ι k) → Ω) (a : K → ℤ) (s : Ω) (hb : Birational y)
    (hs : s ∈ chartLatNm y a 1) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ (e : K → ℕ) (F : MRing ι), IsMultiHomog F e ∧ aeval y F ≠ 0 ∧
      ∀ n : ℕ, aeval y F * s ^ n * ∏ k, y ⟨k, c k⟩ ^ (-((e k : ℤ) + n * a k)) ∈ chartRingZ y c := by
  classical
  have hu := hs c hc
  set u : Ω := s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) with hudef
  obtain ⟨d, g, h, hg, hh, hh0, heq⟩ := hb u
  have hG := (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.mem_chartLat_one y).1
    (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.chartLat_form (y := y) hg) c hc
  have hH := (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.mem_chartLat_one y).1
    (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.chartLat_form (y := y) hh) c hc
  obtain ⟨M, hM⟩ := exists_pow_mul_pow_mem (chartRingZ y c) hu hG hH (by rw [heq]; ring)
  refine ⟨M • d, h ^ M, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_pow hh M, ?_, fun n => ?_⟩
  · rw [map_pow]; exact pow_ne_zero _ hh0
  · have e' : aeval y (h ^ M) * s ^ n * ∏ k, y ⟨k, c k⟩ ^ (-((((M • d) k : ℕ) : ℤ) + n * a k)) =
        (aeval y h * ∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ))) ^ M * u ^ n := by
      have e2 : ∏ k, y ⟨k, c k⟩ ^ (-((((M • d) k : ℕ) : ℤ) + n * a k)) =
          (∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ))) ^ M * (∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))) ^ n := by
        rw [← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ (hc k)]
        congr 1
        simp only [Pi.smul_apply, smul_eq_mul]
        push_cast
        ring
      rw [e2, map_pow, hudef, mul_pow, mul_pow]
      ring
    rw [e']
    exact hM n

end GlobalTheory.CompanionTheory.Ar.Top.EffNm

namespace GlobalTheory.CompanionTheory.Ar.Top

/- English proof (translation)
Introduce `K _ ι _ Ω _ y _ a s _ hb hs`. Establish `hex : ∀ c : ∀ k, ι k, ∃ (e : K → ℕ) (F : MRing ι), IsMultiHomog F e ∧ aeval y F ≠ 0 ∧ ((∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ n : ℕ, aeval y F * s ^ n * ∏ k, y ⟨k, c k⟩ ^ (-((e k : ℤ) + n * a k)) ∈ chartRingZ y c)`. Introduce `c`. Distinguish the cases in `hc : ∀ k, y ⟨k, c k⟩ ≠ 0`. Take `⟨e, F, h1, h2, h3⟩` from `EffNm.exists_form_at y a s hb hs c hc`.

Conclude with `⟨e, F, h1, h2, fun _ => h3⟩`. Conclude with `⟨0, 1, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_one, by simp, fun h => absurd h hc⟩`. Use `choose e F hF hF0 hFc using hex`. Use `⟨∑ c, fun k => (e c k : ℤ), ∏ c, aeval y (F c), Finset.prod_ne_zero_iff.2 fun c _ => hF0 c, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.mem_chartLat_one]`.

Introduce `c₀ hc₀`. Establish `hP` using `(GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.mem_chartLat_one y).1 (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.chartLat_prod (y := y) (Finset.univ.erase c₀) (fun c => aeval y (F c)) (fun c k => (e c k : ℤ)) (fun c _ => GroundTheory.Heights …`. Establish `hQ` using `hFc c₀ hc₀ n`. Establish `e' : (∏ c, aeval y (F c)) * s ^ n * ∏ k, y ⟨k, c₀ k⟩ ^ (-(((∑ c, fun k => (e c k : ℤ)) + (n : ℤ) • a) k)) = (aeval y (F c₀) * s ^ n * ∏ k, y ⟨k, c₀ k⟩ ^ (-((e c₀ k : ℤ) + n * a k))) * ((∏ c ∈ Finset.univ.erase c₀, aeval y (F c)) * ∏ k, y ⟨k, c₀ k⟩ ^ (-((∑ c ∈ Finset.univ.erase c₀ …`. Establish `e1 : ∏ c, aeval y (F c) = aeval y (F c₀) * ∏ c ∈ Finset.univ.erase c₀, aeval y (F c)` using `(Finset.mul_prod_erase _ _ (Finset.mem_univ c₀)).symm`.

Establish `e2 : ∏ k, y ⟨k, c₀ k⟩ ^ (-(((∑ c, fun k => (e c k : ℤ)) + (n : ℤ) • a) k)) = (∏ k, y ⟨k, c₀ k⟩ ^ (-((e c₀ k : ℤ) + n * a k))) * ∏ k, y ⟨k, c₀ k⟩ ^ (-((∑ c ∈ Finset.univ.erase c₀, fun k => (e c k : ℤ)) k))`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_add₀ (hc₀ k)]`. Use `congr 1`.

Establish `e3 : (∑ c, fun k => (e c k : ℤ)) = (fun k => (e c₀ k : ℤ)) + ∑ c ∈ Finset.univ.erase c₀, fun k => (e c k : ℤ)` using `(Finset.add_sum_erase _ _ (Finset.mem_univ c₀)).symm`. Rewrite using `[e3]`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e']`. Conclude with `mul_mem hQ hP`.
-/
theorem exists_mul_pow_mem_chartLat_of_mem_chartLatNm :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (a : K → ℤ) (s : Ω), IsArithVar (mCoordIdeal y) d → Birational y → s ∈ chartLatNm y a 1 → ∃ (b : K → ℤ) (c : Ω), c ≠ 0 ∧ ∀ n : ℕ, c * s ^ n ∈ chartLat y (b + (n : ℤ) • a) 1 := by
  intro K _ ι _ Ω _ y _ a s _ hb hs
  classical
  have hex : ∀ c : ∀ k, ι k, ∃ (e : K → ℕ) (F : MRing ι), IsMultiHomog F e ∧ aeval y F ≠ 0 ∧
      ((∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ n : ℕ,
        aeval y F * s ^ n * ∏ k, y ⟨k, c k⟩ ^ (-((e k : ℤ) + n * a k)) ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨e, F, h1, h2, h3⟩ := EffNm.exists_form_at y a s hb hs c hc
      exact ⟨e, F, h1, h2, fun _ => h3⟩
    · exact ⟨0, 1, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_one, by simp, fun h => absurd h hc⟩
  choose e F hF hF0 hFc using hex
  refine ⟨∑ c, fun k => (e c k : ℤ), ∏ c, aeval y (F c),
    Finset.prod_ne_zero_iff.2 fun c _ => hF0 c, fun n => ?_⟩
  rw [GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.mem_chartLat_one]
  intro c₀ hc₀
  have hP := (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.mem_chartLat_one y).1
    (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.chartLat_prod (y := y)
      (Finset.univ.erase c₀) (fun c => aeval y (F c)) (fun c k => (e c k : ℤ))
      (fun c _ => GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.chartLat_form (y := y) (hF c)))
    c₀ hc₀
  have hQ := hFc c₀ hc₀ n
  have e' : (∏ c, aeval y (F c)) * s ^ n *
        ∏ k, y ⟨k, c₀ k⟩ ^ (-(((∑ c, fun k => (e c k : ℤ)) + (n : ℤ) • a) k)) =
      (aeval y (F c₀) * s ^ n * ∏ k, y ⟨k, c₀ k⟩ ^ (-((e c₀ k : ℤ) + n * a k))) *
        ((∏ c ∈ Finset.univ.erase c₀, aeval y (F c)) *
          ∏ k, y ⟨k, c₀ k⟩ ^ (-((∑ c ∈ Finset.univ.erase c₀, fun k => (e c k : ℤ)) k))) := by
    have e1 : ∏ c, aeval y (F c) = aeval y (F c₀) * ∏ c ∈ Finset.univ.erase c₀, aeval y (F c) :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ c₀)).symm
    have e2 : ∏ k, y ⟨k, c₀ k⟩ ^ (-(((∑ c, fun k => (e c k : ℤ)) + (n : ℤ) • a) k)) =
        (∏ k, y ⟨k, c₀ k⟩ ^ (-((e c₀ k : ℤ) + n * a k))) *
          ∏ k, y ⟨k, c₀ k⟩ ^ (-((∑ c ∈ Finset.univ.erase c₀, fun k => (e c k : ℤ)) k)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_add₀ (hc₀ k)]
      congr 1
      have e3 : (∑ c, fun k => (e c k : ℤ)) =
          (fun k => (e c₀ k : ℤ)) + ∑ c ∈ Finset.univ.erase c₀, fun k => (e c k : ℤ) :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ c₀)).symm
      rw [e3]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, e2]
    ring
  rw [e']
  exact mul_mem hQ hP

end GlobalTheory.CompanionTheory.Ar.Top

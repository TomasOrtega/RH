import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.OfParts
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CoeNeZeroOfNotMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)
open IndefiniteRowSideFullHecke.Kleiman2 (locIn modelPts modVec resImage residue ResField)

noncomputable section

namespace RestrictionPoints

section Proof

variable {S : Type*} [CommRing S] {Ω : Type*} [Field Ω] [Algebra S Ω] {K : Type} {ι : K → Type}

/- English proof (translation)
The claim follows from `Algebra.subset_adjoin ⟨q, rfl⟩`.
-/
theorem ratio_mem (y : (Σ k, ι k) → Ω) (c₁ : ∀ k, ι k) (q : Σ k, ι k) :
    y q / y ⟨q.1, c₁ q.1⟩ ∈ chartRingOver S y c₁ :=
  Algebra.subset_adjoin ⟨q, rfl⟩

/- English proof (translation)
The claim follows from `Subring.subset_closure ⟨⟨x, hx⟩, 1, Ideal.one_notMem q, by simp⟩`.
-/
theorem mem_locIn_of_mem (A : Subalgebra S Ω) (q : Ideal A) [q.IsPrime] {x : Ω} (hx : x ∈ A) :
    x ∈ locIn A q :=
  Subring.subset_closure ⟨⟨x, hx⟩, 1, Ideal.one_notMem q, by simp⟩

variable (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [p.IsPrime]

/- English proof (translation)
Rewrite using `[Ne, resMap_eq_zero_iff, not_not]`. Conclude with `IsUnit.of_mul_eq_one (⟨x⁻¹, hxi⟩ : locIn (chartRingOver S y c) p) (Subtype.ext (mul_inv_cancel₀ hx0))`.
-/
theorem resMap_ne_zero_of_inv {x : Ω} (hx : x ∈ locIn (chartRingOver S y c) p) (hx0 : x ≠ 0)
    (hxi : x⁻¹ ∈ locIn (chartRingOver S y c) p) : resMap y c p ⟨x, hx⟩ ≠ 0 := by
  rw [Ne, resMap_eq_zero_iff, not_not]
  exact IsUnit.of_mul_eq_one (⟨x⁻¹, hxi⟩ : locIn (chartRingOver S y c) p)
    (Subtype.ext (mul_inv_cancel₀ hx0))

/- English proof (translation)
Establish `hu : IsUnit (⟨x, hx⟩ : locIn (chartRingOver S y c) p)`. Assume the negation of the conclusion as `hn`. Conclude with `h ((resMap_eq_zero_iff y c p _).mpr hn)`. Take `⟨t, ht⟩` from `hu`. Establish `h1 : (⟨x, hx⟩ : locIn (chartRingOver S y c) p) * ↑t⁻¹ = 1` using `by rw [← ht]; exact t.mul_inv`.

Establish `h2 : x * ((↑t⁻¹ : locIn (chartRingOver S y c) p) : Ω) = 1` using `congrArg Subtype.val h1`. Rewrite using `[← eq_inv_of_mul_eq_one_right h2]`. Conclude with `(↑t⁻¹ : locIn (chartRingOver S y c) p).2`.
-/
theorem inv_mem_of_resMap_ne_zero {x : Ω} (hx : x ∈ locIn (chartRingOver S y c) p)
    (h : resMap y c p ⟨x, hx⟩ ≠ 0) : x⁻¹ ∈ locIn (chartRingOver S y c) p := by
  have hu : IsUnit (⟨x, hx⟩ : locIn (chartRingOver S y c) p) := by
    by_contra hn
    exact h ((resMap_eq_zero_iff y c p _).mpr hn)
  obtain ⟨t, ht⟩ := hu
  have h1 : (⟨x, hx⟩ : locIn (chartRingOver S y c) p) * ↑t⁻¹ = 1 := by rw [← ht]; exact t.mul_inv
  have h2 : x * ((↑t⁻¹ : locIn (chartRingOver S y c) p) : Ω) = 1 := congrArg Subtype.val h1
  rw [← eq_inv_of_mul_eq_one_right h2]
  exact (↑t⁻¹ : locIn (chartRingOver S y c) p).2

/- English proof (translation)
Rewrite using `[eq_div_iff ht, ← map_mul]`. Conclude with `congrArg _ (Subtype.ext h)`.
-/
theorem resMap_div (u w t : locIn (chartRingOver S y c) p) (h : (w : Ω) * t = u)
    (ht : resMap y c p t ≠ 0) : resMap y c p w = resMap y c p u / resMap y c p t := by
  rw [eq_div_iff ht, ← map_mul]
  exact congrArg _ (Subtype.ext h)

/- English proof (translation)
The claim follows from `(resMap_of_mem y c p ⟨_, ratio_mem y c q⟩ h).trans (residue_of_mem y c p _).symm`.
-/
theorem resMap_ratio (q : Σ k, ι k) (h : y q / y ⟨q.1, c q.1⟩ ∈ locIn (chartRingOver S y c) p) :
    resMap y c p ⟨y q / y ⟨q.1, c q.1⟩, h⟩ = modVec S y c p q :=
  (resMap_of_mem y c p ⟨_, ratio_mem y c q⟩ h).trans (residue_of_mem y c p _).symm

/- English proof (translation)
Introduce `h0`. Apply `h` to reduce the goal to its premises. Establish `e : (⟨y q / y ⟨q.1, c q.1⟩, ratio_mem y c q⟩ : chartRingOver S y c) = 0` using `Subtype.ext (by simp [h0])`. Use `show residue S y c p ((⟨y q / y ⟨q.1, c q.1⟩, ratio_mem y c q⟩ : chartRingOver S y c) : Ω) = 0`. Rewrite using `[residue_of_mem, e, resq]`.

Simplify using the standard rewrite rules.
-/
theorem ne_zero_of_modVec_ne_zero {q : Σ k, ι k} (h : modVec S y c p q ≠ 0) : y q ≠ 0 := by
  intro h0
  apply h
  have e : (⟨y q / y ⟨q.1, c q.1⟩, ratio_mem y c q⟩ : chartRingOver S y c) = 0 :=
    Subtype.ext (by simp [h0])
  show residue S y c p ((⟨y q / y ⟨q.1, c q.1⟩, ratio_mem y c q⟩ : chartRingOver S y c) : Ω) = 0
  rw [residue_of_mem, e, resq]
  simp

variable (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
include hc

/- English proof (translation)
Set `T : Subalgebra S Ω` to `{ toSubsemiring := (locIn (chartRingOver S y c) p).toSubsemiring algebraMap_mem' := fun s => mem_locIn_of_mem (chartRingOver S y c) p ((chartRingOver S y c).algebraMap_mem s) }`. Establish `hle : chartRingOver S y c₁ ≤ T`. Apply `Algebra.adjoin_le` to reduce the goal to its premises. Introduce and unpack `_ ⟨q, rfl⟩`. Establish `h1` using `mem_locIn_of_mem (chartRingOver S y c) p (ratio_mem y c q)`.

Establish `h2` using `mem_locIn_of_mem (chartRingOver S y c) p (ratio_mem y c ⟨q.1, c₁ q.1⟩)`. Establish `h3` using `inv_mem_of_resMap_ne_zero y c p h2 (by rw [resMap_ratio]; exact hv q.1)`. Establish `hy1 : y ⟨q.1, c₁ q.1⟩ ≠ 0` using `ne_zero_of_modVec_ne_zero y c p (hv q.1)`. Establish `e : y q / y ⟨q.1, c₁ q.1⟩ = y q / y ⟨q.1, c q.1⟩ * (y ⟨q.1, c₁ q.1⟩ / y ⟨q.1, c q.1⟩)⁻¹`. Rewrite using `[inv_div, div_mul_div_comm, mul_comm (y ⟨q.1, c q.1⟩) (y ⟨q.1, c₁ q.1⟩), mul_div_mul_right _ _ (hc q.1)]`.

Use `show y q / y ⟨q.1, c₁ q.1⟩ ∈ locIn (chartRingOver S y c) p`. Rewrite using `[e]`. Conclude with `mul_mem h1 h3`. Conclude with `fun x hx => hle hx`.
-/
theorem chart_le (c₁ : ∀ k, ι k) (hv : ∀ k, modVec S y c p ⟨k, c₁ k⟩ ≠ 0) :
    ∀ x ∈ chartRingOver S y c₁, x ∈ locIn (chartRingOver S y c) p := by
  let T : Subalgebra S Ω :=
    { toSubsemiring := (locIn (chartRingOver S y c) p).toSubsemiring
      algebraMap_mem' := fun s =>
        mem_locIn_of_mem (chartRingOver S y c) p ((chartRingOver S y c).algebraMap_mem s) }
  have hle : chartRingOver S y c₁ ≤ T := by
    apply Algebra.adjoin_le
    rintro _ ⟨q, rfl⟩
    have h1 := mem_locIn_of_mem (chartRingOver S y c) p (ratio_mem y c q)
    have h2 := mem_locIn_of_mem (chartRingOver S y c) p (ratio_mem y c ⟨q.1, c₁ q.1⟩)
    have h3 := inv_mem_of_resMap_ne_zero y c p h2 (by rw [resMap_ratio]; exact hv q.1)
    have hy1 : y ⟨q.1, c₁ q.1⟩ ≠ 0 := ne_zero_of_modVec_ne_zero y c p (hv q.1)
    have e : y q / y ⟨q.1, c₁ q.1⟩ =
        y q / y ⟨q.1, c q.1⟩ * (y ⟨q.1, c₁ q.1⟩ / y ⟨q.1, c q.1⟩)⁻¹ := by
      rw [inv_div, div_mul_div_comm, mul_comm (y ⟨q.1, c q.1⟩) (y ⟨q.1, c₁ q.1⟩),
        mul_div_mul_right _ _ (hc q.1)]
    show y q / y ⟨q.1, c₁ q.1⟩ ∈ locIn (chartRingOver S y c) p
    rw [e]
    exact mul_mem h1 h3
  exact fun x hx => hle hx

omit hc in

def resAlg (c₁ : ∀ k, ι k) (hA : ∀ x ∈ chartRingOver S y c₁, x ∈ locIn (chartRingOver S y c) p) :
    chartRingOver S y c₁ →ₐ[S] ResField S y c p where
  toFun a := resMap y c p ⟨a, hA a a.2⟩
  map_one' := (resMap y c p).map_one
  map_mul' a b := (resMap y c p).map_mul ⟨a, hA a a.2⟩ ⟨b, hA b b.2⟩
  map_zero' := (resMap y c p).map_zero
  map_add' a b := (resMap y c p).map_add ⟨a, hA a a.2⟩ ⟨b, hA b b.2⟩
  commutes' s := resMap_algebraMap y c p s _

/- English proof (translation)
Establish `h1` using `mem_locIn_of_mem (chartRingOver S y c) p (ratio_mem y c q)`. Establish `h2` using `mem_locIn_of_mem (chartRingOver S y c) p (ratio_mem y c ⟨q.1, c₁ q.1⟩)`. Establish `hy1 : y ⟨q.1, c₁ q.1⟩ ≠ 0` using `ne_zero_of_modVec_ne_zero y c p (hv q.1)`. Rewrite using `[← resMap_ratio y c p q h1, ← resMap_ratio y c p ⟨q.1, c₁ q.1⟩ h2]`. Use `resMap_div y c p _ _ _ ?_ ?_` and prove the remaining obligations.

Use `show y q / y ⟨q.1, c₁ q.1⟩ * (y ⟨q.1, c₁ q.1⟩ / y ⟨q.1, c q.1⟩) = y q / y ⟨q.1, c q.1⟩`. Rewrite using `[div_mul_div_comm, mul_comm (y ⟨q.1, c₁ q.1⟩) (y ⟨q.1, c q.1⟩), mul_div_mul_right _ _ hy1]`. Rewrite using `[resMap_ratio]`. Conclude with `hv q.1`.
-/
theorem resAlg_ratio (c₁ : ∀ k, ι k) (hv : ∀ k, modVec S y c p ⟨k, c₁ k⟩ ≠ 0) (q : Σ k, ι k) :
    resAlg y c p c₁ (chart_le y c p hc c₁ hv) ⟨_, ratio_mem y c₁ q⟩ =
      modVec S y c p q / modVec S y c p ⟨q.1, c₁ q.1⟩ := by
  have h1 := mem_locIn_of_mem (chartRingOver S y c) p (ratio_mem y c q)
  have h2 := mem_locIn_of_mem (chartRingOver S y c) p (ratio_mem y c ⟨q.1, c₁ q.1⟩)
  have hy1 : y ⟨q.1, c₁ q.1⟩ ≠ 0 := ne_zero_of_modVec_ne_zero y c p (hv q.1)
  rw [← resMap_ratio y c p q h1, ← resMap_ratio y c p ⟨q.1, c₁ q.1⟩ h2]
  refine resMap_div y c p _ _ _ ?_ ?_
  · show y q / y ⟨q.1, c₁ q.1⟩ * (y ⟨q.1, c₁ q.1⟩ / y ⟨q.1, c q.1⟩) = y q / y ⟨q.1, c q.1⟩
    rw [div_mul_div_comm, mul_comm (y ⟨q.1, c₁ q.1⟩) (y ⟨q.1, c q.1⟩), mul_div_mul_right _ _ hy1]
  · rw [resMap_ratio]
    exact hv q.1

/- English proof (translation)
Take `⟨a, ha⟩` from `a`. Establish `hA` using `chart_le y c p hc c₁ hv`. Use `show resMap y c p ⟨a, hA a ha⟩ ∈ _`. Use `Algebra.adjoin_induction (p := fun x hx => resMap y c p ⟨x, hA x hx⟩ ∈ chartRingOver S (modVec S y c p) c₁) ?_ ?_ ?_ ?_ ha` and prove the remaining obligations. Introduce and unpack `_ ⟨q, rfl⟩`.

Establish `e` using `resAlg_ratio y c p hc c₁ hv q`. Use `show resMap y c p ⟨_, hA _ (ratio_mem y c₁ q)⟩ ∈ _`. Rewrite using `[show resMap y c p ⟨_, hA _ (ratio_mem y c₁ q)⟩ = _ from e]`. Conclude with `Algebra.subset_adjoin ⟨q, rfl⟩`. Introduce `s show resMap y c p ⟨algebraMap S Ω s, _⟩ ∈ _`.

Rewrite using `[resMap_algebraMap]`. Conclude with `Subalgebra.algebraMap_mem _ s`. Introduce `x₁ x₂ h₁ h₂ ih₁ ih₂ show resMap y c p ⟨x₁ + x₂, hA _ (add_mem h₁ h₂)⟩ ∈ _`. Rewrite using `[show (⟨x₁ + x₂, hA _ (add_mem h₁ h₂)⟩ : locIn (chartRingOver S y c) p) = ⟨x₁, hA x₁ h₁⟩ + ⟨x₂, hA x₂ h₂⟩ from rfl, map_add]`. Conclude with `add_mem ih₁ ih₂`.

Introduce `x₁ x₂ h₁ h₂ ih₁ ih₂ show resMap y c p ⟨x₁ * x₂, hA _ (mul_mem h₁ h₂)⟩ ∈ _`. Rewrite using `[show (⟨x₁ * x₂, hA _ (mul_mem h₁ h₂)⟩ : locIn (chartRingOver S y c) p) = ⟨x₁, hA x₁ h₁⟩ * ⟨x₂, hA x₂ h₂⟩ from rfl, map_mul]`. Conclude with `mul_mem ih₁ ih₂`.
-/
theorem resAlg_mem (c₁ : ∀ k, ι k) (hv : ∀ k, modVec S y c p ⟨k, c₁ k⟩ ≠ 0)
    (a : chartRingOver S y c₁) :
    resAlg y c p c₁ (chart_le y c p hc c₁ hv) a ∈ chartRingOver S (modVec S y c p) c₁ := by
  obtain ⟨a, ha⟩ := a
  have hA := chart_le y c p hc c₁ hv
  show resMap y c p ⟨a, hA a ha⟩ ∈ _
  refine Algebra.adjoin_induction
    (p := fun x hx => resMap y c p ⟨x, hA x hx⟩ ∈
      chartRingOver S (modVec S y c p) c₁) ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨q, rfl⟩
    have e := resAlg_ratio y c p hc c₁ hv q
    show resMap y c p ⟨_, hA _ (ratio_mem y c₁ q)⟩ ∈ _
    rw [show resMap y c p ⟨_, hA _ (ratio_mem y c₁ q)⟩ = _ from e]
    exact Algebra.subset_adjoin ⟨q, rfl⟩
  · intro s
    show resMap y c p ⟨algebraMap S Ω s, _⟩ ∈ _
    rw [resMap_algebraMap]
    exact Subalgebra.algebraMap_mem _ s
  · intro x₁ x₂ h₁ h₂ ih₁ ih₂
    show resMap y c p ⟨x₁ + x₂, hA _ (add_mem h₁ h₂)⟩ ∈ _
    rw [show (⟨x₁ + x₂, hA _ (add_mem h₁ h₂)⟩ : locIn (chartRingOver S y c) p) =
      ⟨x₁, hA x₁ h₁⟩ + ⟨x₂, hA x₂ h₂⟩ from rfl, map_add]
    exact add_mem ih₁ ih₂
  · intro x₁ x₂ h₁ h₂ ih₁ ih₂
    show resMap y c p ⟨x₁ * x₂, hA _ (mul_mem h₁ h₂)⟩ ∈ _
    rw [show (⟨x₁ * x₂, hA _ (mul_mem h₁ h₂)⟩ : locIn (chartRingOver S y c) p) =
      ⟨x₁, hA x₁ h₁⟩ * ⟨x₂, hA x₂ h₂⟩ from rfl, map_mul]
    exact mul_mem ih₁ ih₂

def chartRes (c₁ : ∀ k, ι k) (hv : ∀ k, modVec S y c p ⟨k, c₁ k⟩ ≠ 0) :
    chartRingOver S y c₁ →ₐ[S] chartRingOver S (modVec S y c p) c₁ :=
  (resAlg y c p c₁ (chart_le y c p hc c₁ hv)).codRestrict _ (resAlg_mem y c p hc c₁ hv)

/- English proof (translation)
Establish `hle : chartRingOver S (modVec S y c p) c₁ ≤ (resAlg y c p c₁ (chart_le y c p hc c₁ hv)).range`. Apply `Algebra.adjoin_le` to reduce the goal to its premises. Introduce and unpack `_ ⟨q, rfl⟩`. Conclude with `(AlgHom.mem_range _).mpr ⟨⟨_, ratio_mem y c₁ q⟩, resAlg_ratio y c p hc c₁ hv q⟩`. Introduce and unpack `⟨t, ht⟩`.

Take `⟨a, ha⟩` from `(AlgHom.mem_range _).mp (hle ht)`. Conclude with `⟨a, Subtype.ext ha⟩`.
-/
theorem chartRes_surjective (c₁ : ∀ k, ι k) (hv : ∀ k, modVec S y c p ⟨k, c₁ k⟩ ≠ 0) :
    Function.Surjective (chartRes y c p hc c₁ hv) := by
  have hle : chartRingOver S (modVec S y c p) c₁ ≤
      (resAlg y c p c₁ (chart_le y c p hc c₁ hv)).range := by
    apply Algebra.adjoin_le
    rintro _ ⟨q, rfl⟩
    exact (AlgHom.mem_range _).mpr ⟨⟨_, ratio_mem y c₁ q⟩, resAlg_ratio y c p hc c₁ hv q⟩
  rintro ⟨t, ht⟩
  obtain ⟨a, ha⟩ := (AlgHom.mem_range _).mp (hle ht)
  exact ⟨a, Subtype.ext ha⟩

/- English proof (translation)
Establish `hA` using `chart_le y c p hc c₁ hv`. Establish `hqp : (P.comap (chartRes y c p hc c₁ hv)).IsPrime` using `Ideal.comap_isPrime _ _`. Establish `hqb : ∀ b : chartRingOver S y c₁, b ∉ P.comap (chartRes y c p hc c₁ hv) → resMap y c p ⟨b, hA b b.2⟩ ≠ 0`. Introduce `b hb h0`. Apply `hb` to reduce the goal to its premises.

Use `show chartRes y c p hc c₁ hv b ∈ P`. Establish `: chartRes y c p hc c₁ hv b = 0` using `Subtype.ext h0`. Rewrite using `[this]`. Conclude with `P.zero_mem`. Establish `hz : locIn (chartRingOver S y c₁) (P.comap (chartRes y c p hc c₁ hv)) ≤ locIn (chartRingOver S y c) p`.

Introduce `u hu`. Take `⟨a, b, hb, rfl⟩` from `(mem_locIn_chart_iff y c₁ _).mp hu`. Rewrite using `[div_eq_mul_inv]`. Conclude with `mul_mem (hA a a.2) (inv_mem_of_resMap_ne_zero y c p (hA b b.2) (hqb b hb))`. Use `⟨hz, ?_⟩` and prove the remaining obligations.

Rewrite using `[resImage_eq y c p _ hz]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Subring.closure_le]`. Introduce and unpack `_ ⟨u, huz, rfl⟩`. Take `⟨a, b, hb, hu⟩` from `(mem_locIn_chart_iff y c₁ _).mp huz`.

Establish `hb0` using `coe_ne_zero_of_notMem y c₁ _ hb`. Rewrite using `[resMap_div y c p ⟨a, hA a a.2⟩ u ⟨b, hA b b.2⟩ (by rw [hu]; exact div_mul_cancel₀ _ hb0) (hqb b hb)]`. Conclude with `Subring.subset_closure ⟨chartRes y c p hc c₁ hv a, chartRes y c p hc c₁ hv b, hb, rfl⟩`. Use `show Subring.closure _ ≤ _`. Rewrite using `[Subring.closure_le]`.

Introduce and unpack `_ ⟨a', b', hb', rfl⟩`. Take `⟨a, rfl⟩` from `chartRes_surjective y c p hc c₁ hv a'`. Take `⟨b, rfl⟩` from `chartRes_surjective y c p hc c₁ hv b'`. Establish `hb : b ∉ P.comap (chartRes y c p hc c₁ hv)` using `hb'`. Establish `hmem : (a : Ω) / b ∈ locIn (chartRingOver S y c₁) (P.comap (chartRes y c p hc c₁ hv))` using `(mem_locIn_chart_iff y c₁ _).mpr ⟨a, b, hb, rfl⟩`.

Establish `hb0` using `coe_ne_zero_of_notMem y c₁ _ hb`. Apply `Subring.subset_closure` to reduce the goal to its premises. Use `⟨⟨_, hz hmem⟩, hmem, ?_⟩` and prove the remaining obligations. Conclude with `(resMap_div y c p ⟨a, hA a a.2⟩ ⟨_, hz hmem⟩ ⟨b, hA b b.2⟩ (div_mul_cancel₀ _ hb0) (hqb b hb)).symm`.
-/
theorem main (c₁ : ∀ k, ι k) (hv : ∀ k, modVec S y c p ⟨k, c₁ k⟩ ≠ 0)
    (P : Ideal (chartRingOver S (modVec S y c p) c₁)) [P.IsPrime] :
    locIn (chartRingOver S y c₁) (P.comap (chartRes y c p hc c₁ hv)) ≤
        locIn (chartRingOver S y c) p ∧
      Subring.closure (resImage S y c p
          (locIn (chartRingOver S y c₁) (P.comap (chartRes y c p hc c₁ hv)))) =
        locIn (chartRingOver S (modVec S y c p) c₁) P := by
  have hA := chart_le y c p hc c₁ hv
  have hqp : (P.comap (chartRes y c p hc c₁ hv)).IsPrime := Ideal.comap_isPrime _ _
  have hqb : ∀ b : chartRingOver S y c₁, b ∉ P.comap (chartRes y c p hc c₁ hv) →
      resMap y c p ⟨b, hA b b.2⟩ ≠ 0 := by
    intro b hb h0
    apply hb
    show chartRes y c p hc c₁ hv b ∈ P
    have : chartRes y c p hc c₁ hv b = 0 := Subtype.ext h0
    rw [this]
    exact P.zero_mem
  have hz : locIn (chartRingOver S y c₁) (P.comap (chartRes y c p hc c₁ hv)) ≤
      locIn (chartRingOver S y c) p := by
    intro u hu
    obtain ⟨a, b, hb, rfl⟩ := (mem_locIn_chart_iff y c₁ _).mp hu
    rw [div_eq_mul_inv]
    exact mul_mem (hA a a.2) (inv_mem_of_resMap_ne_zero y c p (hA b b.2) (hqb b hb))
  refine ⟨hz, ?_⟩
  rw [resImage_eq y c p _ hz]
  apply le_antisymm
  · rw [Subring.closure_le]
    rintro _ ⟨u, huz, rfl⟩
    obtain ⟨a, b, hb, hu⟩ := (mem_locIn_chart_iff y c₁ _).mp huz
    have hb0 := coe_ne_zero_of_notMem y c₁ _ hb
    rw [resMap_div y c p ⟨a, hA a a.2⟩ u ⟨b, hA b b.2⟩
      (by rw [hu]; exact div_mul_cancel₀ _ hb0) (hqb b hb)]
    exact Subring.subset_closure ⟨chartRes y c p hc c₁ hv a, chartRes y c p hc c₁ hv b, hb, rfl⟩
  · show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    rintro _ ⟨a', b', hb', rfl⟩
    obtain ⟨a, rfl⟩ := chartRes_surjective y c p hc c₁ hv a'
    obtain ⟨b, rfl⟩ := chartRes_surjective y c p hc c₁ hv b'
    have hb : b ∉ P.comap (chartRes y c p hc c₁ hv) := hb'
    have hmem : (a : Ω) / b ∈ locIn (chartRingOver S y c₁) (P.comap (chartRes y c p hc c₁ hv)) :=
      (mem_locIn_chart_iff y c₁ _).mpr ⟨a, b, hb, rfl⟩
    have hb0 := coe_ne_zero_of_notMem y c₁ _ hb
    apply Subring.subset_closure
    refine ⟨⟨_, hz hmem⟩, hmem, ?_⟩
    exact (resMap_div y c p ⟨a, hA a a.2⟩ ⟨_, hz hmem⟩ ⟨b, hA b b.2⟩
      (div_mul_cancel₀ _ hb0) (hqb b hb)).symm

end Proof

end RestrictionPoints

/- English proof (translation)
Introduce `S _ K _ ι Ω _ _ y c p _ hc`. Use extensionality with `z'`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c₁, hv, P, hP, rfl⟩`. Take `⟨hz, heq⟩` from `RestrictionPoints.main y c p hc c₁ hv P`.

Conclude with `⟨_, ⟨c₁, fun k => RestrictionPoints.ne_zero_of_modVec_ne_zero y c p (hv k), _, Ideal.comap_isPrime _ _, rfl⟩, hz, heq.symm⟩`. Introduce and unpack `⟨_, ⟨c₁, hc₁, q, hq, rfl⟩, hz, rfl⟩`. Establish `hA : ∀ x ∈ chartRingOver S y c₁, x ∈ locIn (chartRingOver S y c) p` using `fun x hx => hz (RestrictionPoints.mem_locIn_of_mem _ q hx)`. Establish `hv : ∀ k, modVec S y c p ⟨k, c₁ k⟩ ≠ 0`. Introduce `k`.

Establish `h1` using `RestrictionPoints.mem_locIn_of_mem (chartRingOver S y c) p (RestrictionPoints.ratio_mem y c ⟨k, c₁ k⟩)`. Rewrite using `[← RestrictionPoints.resMap_ratio y c p ⟨k, c₁ k⟩ h1]`. Use `RestrictionPoints.resMap_ne_zero_of_inv y c p h1 (div_ne_zero (hc₁ k) (hc k)) ?_` and prove the remaining obligations. Rewrite using `[inv_div]`. Conclude with `hA _ (RestrictionPoints.ratio_mem y c₁ ⟨k, c k⟩)`.

Establish `hker : RingHom.ker (RestrictionPoints.chartRes y c p hc c₁ hv) ≤ q`. Introduce `b hb`. Assume the negation of the conclusion as `hbq`. Establish `hb0 : (b : Ω) ≠ 0` using `coe_ne_zero_of_notMem y c₁ q hbq`. Establish `hbi : (b : Ω)⁻¹ ∈ locIn (chartRingOver S y c₁) q` using `(mem_locIn_chart_iff y c₁ q).mpr ⟨1, b, hbq, by simp⟩`.

Apply `RestrictionPoints.resMap_ne_zero_of_inv y c p (hA b b.2) hb0 (hz hbi)` to reduce the goal to its premises. Conclude with `congrArg Subtype.val (RingHom.mem_ker.mp hb)`. Establish `hsurj` using `RestrictionPoints.chartRes_surjective y c p hc c₁ hv`. Establish `hP : (q.map (RestrictionPoints.chartRes y c p hc c₁ hv)).IsPrime` using `Ideal.map_isPrime_of_surjective hsurj hker`. Establish `hcq : (q.map (RestrictionPoints.chartRes y c p hc c₁ hv)).comap (RestrictionPoints.chartRes y c p hc c₁ hv) = q`.

Rewrite using `[Ideal.comap_map_of_surjective _ hsurj]`. Conclude with `sup_eq_left.mpr hker`. Take `⟨-, heq⟩` from `RestrictionPoints.main y c p hc c₁ hv (q.map (RestrictionPoints.chartRes y c p hc c₁ hv))`. Rewrite `heq` using `[hcq]`. Conclude with `⟨c₁, hv, _, hP, heq⟩`.
-/
theorem RestrictionPoints.proof : RestrictionPoints.Statement := by
  intro S _ K _ ι Ω _ _ y c p _ hc
  ext z'
  constructor
  · rintro ⟨c₁, hv, P, hP, rfl⟩
    obtain ⟨hz, heq⟩ := RestrictionPoints.main y c p hc c₁ hv P
    exact ⟨_, ⟨c₁, fun k => RestrictionPoints.ne_zero_of_modVec_ne_zero y c p (hv k), _,
      Ideal.comap_isPrime _ _, rfl⟩, hz, heq.symm⟩
  · rintro ⟨_, ⟨c₁, hc₁, q, hq, rfl⟩, hz, rfl⟩
    have hA : ∀ x ∈ chartRingOver S y c₁, x ∈ locIn (chartRingOver S y c) p :=
      fun x hx => hz (RestrictionPoints.mem_locIn_of_mem _ q hx)
    have hv : ∀ k, modVec S y c p ⟨k, c₁ k⟩ ≠ 0 := by
      intro k
      have h1 := RestrictionPoints.mem_locIn_of_mem (chartRingOver S y c) p
        (RestrictionPoints.ratio_mem y c ⟨k, c₁ k⟩)
      rw [← RestrictionPoints.resMap_ratio y c p ⟨k, c₁ k⟩ h1]
      refine RestrictionPoints.resMap_ne_zero_of_inv y c p h1 (div_ne_zero (hc₁ k) (hc k)) ?_
      rw [inv_div]
      exact hA _ (RestrictionPoints.ratio_mem y c₁ ⟨k, c k⟩)
    have hker : RingHom.ker (RestrictionPoints.chartRes y c p hc c₁ hv) ≤ q := by
      intro b hb
      by_contra hbq
      have hb0 : (b : Ω) ≠ 0 := coe_ne_zero_of_notMem y c₁ q hbq
      have hbi : (b : Ω)⁻¹ ∈ locIn (chartRingOver S y c₁) q :=
        (mem_locIn_chart_iff y c₁ q).mpr ⟨1, b, hbq, by simp⟩
      apply RestrictionPoints.resMap_ne_zero_of_inv y c p (hA b b.2) hb0 (hz hbi)
      exact congrArg Subtype.val (RingHom.mem_ker.mp hb)
    have hsurj := RestrictionPoints.chartRes_surjective y c p hc c₁ hv
    have hP : (q.map (RestrictionPoints.chartRes y c p hc c₁ hv)).IsPrime :=
      Ideal.map_isPrime_of_surjective hsurj hker
    have hcq : (q.map (RestrictionPoints.chartRes y c p hc c₁ hv)).comap
        (RestrictionPoints.chartRes y c p hc c₁ hv) = q := by
      rw [Ideal.comap_map_of_surjective _ hsurj]
      exact sup_eq_left.mpr hker
    obtain ⟨-, heq⟩ := RestrictionPoints.main y c p hc c₁ hv
      (q.map (RestrictionPoints.chartRes y c p hc c₁ hv))
    rw [hcq] at heq
    exact ⟨c₁, hv, _, hP, heq⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

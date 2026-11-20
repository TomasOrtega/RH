import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.TargetSt
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PFiniteIntegralClosure
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsRational
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecEq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace Conductor

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def invMon (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (δ : K → ℕ) : Ω := ∏ k, (y ⟨k, c k⟩ ^ δ k)⁻¹

/- English proof (translation)
Rewrite using `[invMon, invMon, invMon, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add, mul_inv]`.
-/
theorem invMon_add (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (δ ε : K → ℕ) :
    invMon y c (δ + ε) = invMon y c δ * invMon y c ε := by
  rw [invMon, invMon, invMon, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add, mul_inv]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [invMon]`. Consider the case `insert b s hb ih => rw [Finset.prod_insert hb, Finset.sum_insert hb, ih, invMon_add]`.
-/
theorem invMon_sum {β : Type} (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (s : Finset β) (δ : β → K → ℕ) :
    ∏ b ∈ s, invMon y c (δ b) = invMon y c (∑ b ∈ s, δ b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [invMon]
  | insert b s hb ih => rw [Finset.prod_insert hb, Finset.sum_insert hb, ih, invMon_add]

/- English proof (translation)
Simplify using `[invMon, zpow_neg, zpow_natCast]`.
-/
theorem prod_zpow_eq_invMon (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (δ : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ (-(δ k : ℤ)) = invMon y c δ := by
  simp [invMon, zpow_neg, zpow_natCast]

/- English proof (translation)
Rewrite using `[← prod_zpow_eq_invMon, NmSectionsRationalProof.aeval_mul_prod_zpow y c hg, chartRingZ, Algebra.adjoin_range_eq_range_aeval]`. Conclude with `⟨g, rfl⟩`.
-/
theorem form_mul_invMon_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {δ : K → ℕ} {g : MRing ι}
    (hg : IsMultiHomog g δ) : aeval y g * invMon y c δ ∈ chartRingZ y c := by
  rw [← prod_zpow_eq_invMon, NmSectionsRationalProof.aeval_mul_prod_zpow y c hg, chartRingZ,
    Algebra.adjoin_range_eq_range_aeval]
  exact ⟨g, rfl⟩

/- English proof (translation)
Use `IsFractionRing.of_field (chartRingZ y c) Ω fun z => ?_` and prove the remaining obligations. Take `⟨d, g, h, hg, hh, hh0, hgh⟩` from `hbir z`. Establish `hP : invMon y c d ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => inv_ne_zero (pow_ne_zero _ (hc k))`. Use `⟨⟨_, form_mul_invMon_mem y c hg⟩, ⟨_, form_mul_invMon_mem y c hh⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `z = aeval y g * _ / (aeval y h * _)`.

Rewrite using `[hgh, mul_assoc, mul_div_assoc, div_self (mul_ne_zero hh0 hP), mul_one]`.
-/
theorem isFractionRing_chartRingZ (y : (Σ k, ι k) → Ω) (hbir : Birational y) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : IsFractionRing (chartRingZ y c) Ω := by
  refine IsFractionRing.of_field (chartRingZ y c) Ω fun z => ?_
  obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hbir z
  have hP : invMon y c d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => inv_ne_zero (pow_ne_zero _ (hc k))
  refine ⟨⟨_, form_mul_invMon_mem y c hg⟩, ⟨_, form_mul_invMon_mem y c hh⟩, ?_⟩
  change z = aeval y g * _ / (aeval y h * _)
  rw [hgh, mul_assoc, mul_div_assoc, div_self (mul_ne_zero hh0 hP), mul_one]

/- English proof (translation)
Use `set A := chartRingZ y c`. Use `isFractionRing_chartRingZ y hbir c hc` as an intermediate fact. Establish `: Algebra.FiniteType ℤ A` using `.adjoin_of_finite (Set.finite_range _)`. Establish `hfin : Module.Finite A (integralClosure A Ω)` using `Model.FiniteIntegralClosure.proof A Ω Ω`. Take `⟨s, hs⟩` from `hfin.fg_top`.

Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A) (s.image fun z : integralClosure A Ω => (z : Ω))`. Establish `key : ∀ z : integralClosure A Ω, ((b : A) : Ω) * (z : Ω) ∈ A`. Introduce `z`. Establish `hz : z ∈ Submodule.span A (s : Set (integralClosure A Ω))` using `hs ▸ Submodule.mem_top`. Proceed by induction on `hz using Submodule.span_induction with`.

Consider the case `mem w hw`. Take `⟨u, hu⟩` from `hb _ (Finset.mem_image_of_mem _ hw)`. Establish `: (u : Ω) = ((b : A) : Ω) * (w : Ω)` using `by rw [Algebra.smul_def] at hu; exact hu`. Rewrite using `[← this]`. Conclude with `u.2`.

Consider the case `zero => simp`. Consider the case `add w v _ _ hw hv => rw [Subalgebra.coe_add, mul_add]`. Conclude with `add_mem hw hv`. Consider the case `smul r w _ hw`. Rewrite using `[Subalgebra.coe_smul, Algebra.smul_def, mul_left_comm]`.

Conclude with `mul_mem r.2 hw`. Establish `hb0 : ((b : A) : Ω) ≠ 0`. Introduce `h`. Conclude with `nonZeroDivisors.coe_ne_zero b (Subtype.ext h)`. Take `⟨δ, e, he, hv⟩` from `SectionBounded.exists_form_of_mem_chartRingZ y c hc (b : A).2`.

Establish `hm : (∏ k, y ⟨k, c k⟩ ^ δ k) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)`. Establish `hbv : aeval y e * invMon y c δ = ((b : A) : Ω)`. Rewrite using `[hv, invMon, Finset.prod_inv_distrib, mul_assoc, mul_inv_cancel₀ hm, mul_one]`. Use `⟨δ, e, he, by rw [hv]; exact mul_ne_zero hb0 hm, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[hbv]`.

Conclude with `key ⟨x, hx⟩`.
-/
theorem exists_chart_conductor (y : (Σ k, ι k) → Ω) (hbir : Birational y) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ (δ : K → ℕ) (F : MRing ι), IsMultiHomog F δ ∧ aeval y F ≠ 0 ∧
      ∀ x ∈ integralClosure (chartRingZ y c) Ω, aeval y F * invMon y c δ * x ∈ chartRingZ y c := by
  classical
  set A := chartRingZ y c
  have := isFractionRing_chartRingZ y hbir c hc
  have : Algebra.FiniteType ℤ A := .adjoin_of_finite (Set.finite_range _)
  have hfin : Module.Finite A (integralClosure A Ω) := Model.FiniteIntegralClosure.proof A Ω Ω
  obtain ⟨s, hs⟩ := hfin.fg_top
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A)
    (s.image fun z : integralClosure A Ω => (z : Ω))
  have key : ∀ z : integralClosure A Ω, ((b : A) : Ω) * (z : Ω) ∈ A := by
    intro z
    have hz : z ∈ Submodule.span A (s : Set (integralClosure A Ω)) := hs ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨u, hu⟩ := hb _ (Finset.mem_image_of_mem _ hw)
      have : (u : Ω) = ((b : A) : Ω) * (w : Ω) := by rw [Algebra.smul_def] at hu; exact hu
      rw [← this]; exact u.2
    | zero => simp
    | add w v _ _ hw hv => rw [Subalgebra.coe_add, mul_add]; exact add_mem hw hv
    | smul r w _ hw =>
      rw [Subalgebra.coe_smul, Algebra.smul_def, mul_left_comm]
      exact mul_mem r.2 hw
  have hb0 : ((b : A) : Ω) ≠ 0 := by
    intro h
    exact nonZeroDivisors.coe_ne_zero b (Subtype.ext h)
  obtain ⟨δ, e, he, hv⟩ := SectionBounded.exists_form_of_mem_chartRingZ y c hc (b : A).2
  have hm : (∏ k, y ⟨k, c k⟩ ^ δ k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have hbv : aeval y e * invMon y c δ = ((b : A) : Ω) := by
    rw [hv, invMon, Finset.prod_inv_distrib, mul_assoc, mul_inv_cancel₀ hm, mul_one]
  refine ⟨δ, e, he, by rw [hv]; exact mul_ne_zero hb0 hm, fun x hx => ?_⟩
  rw [hbv]
  exact key ⟨x, hx⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using (SectionBounded.homog_one (ι := ι))`. Consider the case `insert b s hb ih`. Rewrite using `[Finset.prod_insert hb, Finset.sum_insert hb]`. Conclude with `SectionBounded.homog_mul (h b (Finset.mem_insert_self b s)) (ih fun b' hb' => h b' (Finset.mem_insert_of_mem hb'))`.
-/
theorem homog_prod {β : Type} (s : Finset β) (F : β → MRing ι) (δ : β → K → ℕ)
    (h : ∀ b ∈ s, IsMultiHomog (F b) (δ b)) : IsMultiHomog (∏ b ∈ s, F b) (∑ b ∈ s, δ b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (SectionBounded.homog_one (ι := ι))
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb]
    exact SectionBounded.homog_mul (h b (Finset.mem_insert_self b s))
      (ih fun b' hb' => h b' (Finset.mem_insert_of_mem hb'))

end Conductor

/- English proof (translation)
Introduce `K _ ι _ Ω _ y a ha hy hbir`. Take `⟨τ₀, hτ₀⟩` from `hS K ι Ω y a ha hy`. Set `C` to `{c : ∀ k, ι k // ∀ k, y ⟨k, c k⟩ ≠ 0}`. Use `choose δ F hF hF0 hcond using fun c : C => Conductor.exists_chart_conductor y hbir c.1 c.2`. Use `choose i0 hi0 using hy`.

Use `set Δ : K → ℕ := ∑ c : C, δ c`. Use `set k' : ℕ := τ₀ + ∑ κ, Δ κ`. Establish `hΔ : ∀ κ, Δ κ ≤ k' * a κ` using `fun κ => (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ κ)).trans ((Nat.le_add_left _ _).trans (Nat.le_mul_of_pos_right _ (ha κ)))`. Use `set e : K → ℕ := fun κ => k' * a κ - Δ κ`. Use `set Φ : MRing ι := (∏ c : C, F c) * SectionBounded.chartMon i0 e`.

Establish `hΦ : IsMultiHomog Φ (fun κ => k' * a κ)` using `SectionBounded.homog_congr (SectionBounded.homog_mul (Conductor.homog_prod Finset.univ F δ fun c _ => hF c) (SectionBounded.homog_chartMon i0 e)) fun κ => by simp only [Pi.add_apply, e]; exact Nat.add_sub_cancel' (hΔ κ)`. Establish `hM : aeval y (SectionBounded.chartMon i0 e) ≠ 0`. Rewrite using `[SectionBounded.aeval_chartMon]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun κ _ => pow_ne_zero _ (hi0 κ)`. Establish `hΦ0 : aeval y Φ ≠ 0`.

Rewrite using `[map_mul, map_prod]`. Conclude with `mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun c _ => hF0 c) hM`. Use `⟨k', Φ, hΦ, hΦ0, fun τ s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[← hτ₀ (τ + k') (by omega)]`. Introduce `c' hc'`.

Use `set c : C := ⟨c', hc'⟩`. Establish `hx` using `hs c' hc'`. Establish `hτ : (fun κ => τ * a κ) + Δ + e = fun κ => (τ + k') * a κ`. Use function extensionality and compare the values at `κ`. Simplify using `only [Pi.add_apply, e]`.

Rewrite using `[add_assoc, Nat.add_sub_cancel' (hΔ κ)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hexp : ∀ n : K → ℕ, (∏ κ, y ⟨κ, c' κ⟩ ^ (-((n κ : ℕ) : ℤ))) = Conductor.invMon y c' n` using `Conductor.prod_zpow_eq_invMon y c'`. Use `beta_reduce at hx ⊢`. Establish `e1 : ∀ κ, -((τ : ℤ) * (a κ : ℤ)) = -(((τ * a κ : ℕ)) : ℤ)` using `fun κ => by push_cast; ring`.

Establish `e2 : ∀ κ, -(((τ + k' : ℕ) : ℤ) * (a κ : ℤ)) = -((((τ + k') * a κ : ℕ)) : ℤ)` using `fun κ => by push_cast; ring`. Simplify using `only [e1] at hx`. Simplify using `only [e2]`. Rewrite `hx` using `[hexp (fun κ => τ * a κ)]`. Rewrite using `[hexp (fun κ => (τ + k') * a κ), ← hτ, Conductor.invMon_add, Conductor.invMon_add, ← Conductor.invMon_sum y c' Finset.univ δ]`.

Establish `hsplit : aeval y Φ * s * (Conductor.invMon y c' (fun κ => τ * a κ) * (∏ b : C, Conductor.invMon y c' (δ b)) * Conductor.invMon y c' e) = (∏ b ∈ Finset.univ.erase c, aeval y (F b) * Conductor.invMon y c' (δ b)) * (aeval y (SectionBounded.chartMon i0 e) * Conductor.invMon y c' e) * …`. Rewrite using `[map_mul, map_prod]`. Rewrite using `[← Finset.mul_prod_erase Finset.univ (fun b => aeval y (F b)) (Finset.mem_univ c), ← Finset.mul_prod_erase Finset.univ (fun b => Conductor.invMon y c' (δ b)) (Finset.mem_univ c), Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit]`.

Use `mul_mem (mul_mem (prod_mem fun b _ => Conductor.form_mul_invMon_mem y c' (hF b)) (Conductor.form_mul_invMon_mem y c' (SectionBounded.homog_chartMon i0 e))) ?_` and prove the remaining obligations. Conclude with `hcond c _ hx`.
-/
theorem Conductor.proof (hS : SecEq.Statement) : KH.CondStatement := by
  classical
  intro K _ ι _ Ω _ y a ha hy hbir
  obtain ⟨τ₀, hτ₀⟩ := hS K ι Ω y a ha hy
  let C := {c : ∀ k, ι k // ∀ k, y ⟨k, c k⟩ ≠ 0}
  choose δ F hF hF0 hcond using fun c : C => Conductor.exists_chart_conductor y hbir c.1 c.2
  choose i0 hi0 using hy
  set Δ : K → ℕ := ∑ c : C, δ c
  set k' : ℕ := τ₀ + ∑ κ, Δ κ
  have hΔ : ∀ κ, Δ κ ≤ k' * a κ := fun κ =>
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ κ)).trans
      ((Nat.le_add_left _ _).trans (Nat.le_mul_of_pos_right _ (ha κ)))
  set e : K → ℕ := fun κ => k' * a κ - Δ κ
  set Φ : MRing ι := (∏ c : C, F c) * SectionBounded.chartMon i0 e
  have hΦ : IsMultiHomog Φ (fun κ => k' * a κ) :=
    SectionBounded.homog_congr (SectionBounded.homog_mul
      (Conductor.homog_prod Finset.univ F δ fun c _ => hF c) (SectionBounded.homog_chartMon i0 e))
      fun κ => by simp only [Pi.add_apply, e]; exact Nat.add_sub_cancel' (hΔ κ)
  have hM : aeval y (SectionBounded.chartMon i0 e) ≠ 0 := by
    rw [SectionBounded.aeval_chartMon]
    exact Finset.prod_ne_zero_iff.mpr fun κ _ => pow_ne_zero _ (hi0 κ)
  have hΦ0 : aeval y Φ ≠ 0 := by
    rw [map_mul, map_prod]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun c _ => hF0 c) hM
  refine ⟨k', Φ, hΦ, hΦ0, fun τ s hs => ?_⟩
  rw [← hτ₀ (τ + k') (by omega)]
  intro c' hc'
  set c : C := ⟨c', hc'⟩
  have hx := hs c' hc'
  have hτ : (fun κ => τ * a κ) + Δ + e = fun κ => (τ + k') * a κ := by
    funext κ
    simp only [Pi.add_apply, e]
    rw [add_assoc, Nat.add_sub_cancel' (hΔ κ)]
    ring
  have hexp : ∀ n : K → ℕ, (∏ κ, y ⟨κ, c' κ⟩ ^ (-((n κ : ℕ) : ℤ))) = Conductor.invMon y c' n :=
    Conductor.prod_zpow_eq_invMon y c'
  beta_reduce at hx ⊢
  have e1 : ∀ κ, -((τ : ℤ) * (a κ : ℤ)) = -(((τ * a κ : ℕ)) : ℤ) := fun κ => by push_cast; ring
  have e2 : ∀ κ, -(((τ + k' : ℕ) : ℤ) * (a κ : ℤ)) = -((((τ + k') * a κ : ℕ)) : ℤ) := fun κ => by push_cast; ring
  simp only [e1] at hx
  simp only [e2]
  rw [hexp (fun κ => τ * a κ)] at hx
  rw [hexp (fun κ => (τ + k') * a κ), ← hτ, Conductor.invMon_add, Conductor.invMon_add,
    ← Conductor.invMon_sum y c' Finset.univ δ]
  have hsplit : aeval y Φ * s * (Conductor.invMon y c' (fun κ => τ * a κ) *
      (∏ b : C, Conductor.invMon y c' (δ b)) * Conductor.invMon y c' e) =
      (∏ b ∈ Finset.univ.erase c, aeval y (F b) * Conductor.invMon y c' (δ b)) *
        (aeval y (SectionBounded.chartMon i0 e) * Conductor.invMon y c' e) *
        (aeval y (F c) * Conductor.invMon y c' (δ c) * (s * Conductor.invMon y c' (fun κ => τ * a κ))) := by
    rw [map_mul, map_prod]
    rw [← Finset.mul_prod_erase Finset.univ (fun b => aeval y (F b)) (Finset.mem_univ c),
      ← Finset.mul_prod_erase Finset.univ (fun b => Conductor.invMon y c' (δ b)) (Finset.mem_univ c),
      Finset.prod_mul_distrib]
    ring
  rw [hsplit]
  refine mul_mem (mul_mem (prod_mem fun b _ => Conductor.form_mul_invMon_mem y c' (hF b))
    (Conductor.form_mul_invMon_mem y c' (SectionBounded.homog_chartMon i0 e))) ?_
  exact hcond c _ hx

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

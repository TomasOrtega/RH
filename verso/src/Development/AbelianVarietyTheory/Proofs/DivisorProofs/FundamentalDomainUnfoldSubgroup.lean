import Mathlib
open MeasureTheory
open scoped Pointwise

namespace GlobalTheory

/- English proof (translation)
Introduce `G G₁ _ _ _ N Q Γ μN ι 𝓕 D h hQc hΓc hL hh hD hιQ huniq hconj hinv hfd`. Establish `hLN : ∀ g : N, Measurable (fun x : N => g * x)` using `fun g => ((hL g.1).comp measurable_subtype_coe).subtype_mk`. Use `haveI : MeasurableConstSMul (Q.subgroupOf N) N := ⟨fun g => hLN g.1⟩`. Use `haveI : SMulInvariantMeasure (Q.subgroupOf N) N μN := ⟨fun g s hs => by show μN ((fun x : N => (g : N) * x) ⁻¹' s) = μN s`. Rewrite using `[← Measure.map_apply (hLN g.1) hs, map_mul_left_eq_self]⟩`.

Use `haveI : Countable (Q.subgroupOf N) := by`. Establish `: Function.Injective (fun ν : Q.subgroupOf N => (⟨ν.1.1, ν.2⟩ : Q))`. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Conclude with `congrArg (fun q : Q => q.1) hab`. Conclude with `this.countable`. Establish `hmem : ∀ p : Γ × Q.subgroupOf N, ι p.1.1 * p.2.1.1 ∈ Q` using `fun p => Q.mul_mem (hιQ p.1.1 p.1.2) p.2.2`. Set `e0 : Γ × Q.subgroupOf N → Q` to `fun p => ⟨ι p.1.1 * p.2.1.1, hmem p⟩`. Establish `hbij : Function.Bijective e0`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨γ, ν⟩ ⟨γ', ν'⟩ hE`. Establish `hE' : ι γ.1 * ν.1.1 = ι γ'.1 * ν'.1.1` using `congrArg (fun q : Q => q.1) hE`. Establish `hq : ι γ.1 * ν.1.1 ∈ Q` using `hmem (γ, ν)`. Take `⟨γ0, _, hu⟩` from `huniq _ hq`.

Establish `h1 : (ι γ.1)⁻¹ * (ι γ.1 * ν.1.1) ∈ N`. Rewrite using `[inv_mul_cancel_left]`. Conclude with `ν.1.2`. Establish `h2 : (ι γ'.1)⁻¹ * (ι γ.1 * ν.1.1) ∈ N`. Rewrite using `[hE', inv_mul_cancel_left]`.

Conclude with `ν'.1.2`. Establish `hγ : γ = γ'` using `(hu γ h1).trans (hu γ' h2).symm`. Substitute `hγ` using the available equality. Establish `: ν.1.1 = ν'.1.1` using `mul_left_cancel hE'`. Simplify using `only [Prod.mk.injEq, true_and]`.

Conclude with `Subtype.ext (Subtype.ext this)`. Introduce and unpack `⟨q, hq⟩`. Take `⟨γ, hγ, _⟩` from `huniq q hq`. Establish `hνQ : (ι γ.1)⁻¹ * q ∈ Q` using `Q.mul_mem (Q.inv_mem (hιQ γ.1 γ.2)) hq`. Use `⟨(γ, ⟨⟨(ι γ.1)⁻¹ * q, hγ⟩, hνQ⟩), ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show ι γ.1 * ((ι γ.1)⁻¹ * q) = q`. Rewrite using `[mul_inv_cancel_left]`. Set `e` to `Equiv.ofBijective e0 hbij`. Establish `hmeas : ∀ (γ : Γ) (ν : Q.subgroupOf N), Measurable (fun n : N => D.indicator (1 : G → ENNReal) (ι γ.1 * (ν • n).1 * h))`.

Introduce `γ ν`. Establish `: (fun n : N => ι γ.1 * (ν • n).1 * h) = fun n : N => (ι γ.1 * ν.1.1) * (n.1 * h)`. Use function extensionality and compare the values at `n`. Use `show ι γ.1 * (ν.1.1 * n.1) * h = _`. Simplify using `only [mul_assoc]`.

Establish `hm : Measurable (fun n : N => (ι γ.1 * ν.1.1) * (n.1 * h))` using `(hL _).comp hh`. Rewrite `hm` using `[← this]`. Conclude with `(measurable_one.indicator hD).comp hm`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lintegral_tsum]`.

Use `tsum_congr fun γ => ?_` and prove the remaining obligations. Rewrite using `[lintegral_tsum]`. Conclude with `fun ν => (hmeas γ ν).aemeasurable`. Conclude with `fun γ => (Measurable.ennreal_tsum fun ν => hmeas γ ν).aemeasurable`. Use `_ = ∫⁻ n in 𝓕, ∑' p : Γ × Q.subgroupOf N, D.indicator (1 : G → ENNReal) ((e p).1 * (n.1 * h)) ∂μN := by`.

Use `lintegral_congr fun n => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.tsum_prod']`. Use `tsum_congr fun γ => tsum_congr fun ν => ?_` and prove the remaining obligations. Use `show _ = D.indicator (1 : G → ENNReal) ((ι γ.1 * ν.1.1) * (n.1 * h))`. Use `show D.indicator (1 : G → ENNReal) (ι γ.1 * (ν.1.1 * n.1) * h) = _`.

Simplify using `only [mul_assoc]`. Use `_ = ∫⁻ n in 𝓕, ∑' q : Q, D.indicator (1 : G → ENNReal) (q.1 * (n.1 * h)) ∂μN := by`. Use `lintegral_congr fun n => ?_` and prove the remaining obligations. Conclude with `e.tsum_eq (fun q : Q => D.indicator (1 : G → ENNReal) (q.1 * (n.1 * h)))`.
-/
theorem sum_integral_indicator_eq_setIntegral_count :
  ∀ {G G₁ : Type} [Group G] [MeasurableSpace G] [Group G₁] (N Q : Subgroup G) (Γ : Subgroup G₁)
    (μN : Measure N) (ι : G₁ → G) (𝓕 : Set N) (D : Set G) (h : G),
    Countable Q → Countable Γ → (∀ g : G, Measurable (g * ·)) →
    Measurable (fun n : N => n.1 * h) → MeasurableSet D →
    (∀ γ ∈ Γ, ι γ ∈ Q) → (∀ q ∈ Q, ∃! γ : Γ, (ι γ)⁻¹ * q ∈ N) →
    (∀ γ ∈ Γ, ∫⁻ n, D.indicator (1 : G → ENNReal) (n.1 * ι γ * h) ∂μN
      = ∫⁻ n, D.indicator (1 : G → ENNReal) (ι γ * n.1 * h) ∂μN) →
    μN.IsMulLeftInvariant → IsFundamentalDomain (Q.subgroupOf N) 𝓕 μN →
    ∑' γ : Γ, ∫⁻ n, D.indicator (1 : G → ENNReal) (n.1 * ι γ * h) ∂μN
      = ∫⁻ n in 𝓕, ∑' q : Q, D.indicator (1 : G → ENNReal) (q.1 * (n.1 * h)) ∂μN := by
  intro G G₁ _ _ _ N Q Γ μN ι 𝓕 D h hQc hΓc hL hh hD hιQ huniq hconj hinv hfd
  have hLN : ∀ g : N, Measurable (fun x : N => g * x) := fun g =>
    ((hL g.1).comp measurable_subtype_coe).subtype_mk
  haveI : MeasurableConstSMul (Q.subgroupOf N) N := ⟨fun g => hLN g.1⟩
  haveI : SMulInvariantMeasure (Q.subgroupOf N) N μN := ⟨fun g s hs => by
    show μN ((fun x : N => (g : N) * x) ⁻¹' s) = μN s
    rw [← Measure.map_apply (hLN g.1) hs, map_mul_left_eq_self]⟩
  haveI : Countable (Q.subgroupOf N) := by
    have : Function.Injective (fun ν : Q.subgroupOf N => (⟨ν.1.1, ν.2⟩ : Q)) := by
      intro a b hab
      apply Subtype.ext; apply Subtype.ext
      exact congrArg (fun q : Q => q.1) hab
    exact this.countable

  have hmem : ∀ p : Γ × Q.subgroupOf N, ι p.1.1 * p.2.1.1 ∈ Q := fun p =>
    Q.mul_mem (hιQ p.1.1 p.1.2) p.2.2
  let e0 : Γ × Q.subgroupOf N → Q := fun p => ⟨ι p.1.1 * p.2.1.1, hmem p⟩
  have hbij : Function.Bijective e0 := by
    constructor
    · rintro ⟨γ, ν⟩ ⟨γ', ν'⟩ hE
      have hE' : ι γ.1 * ν.1.1 = ι γ'.1 * ν'.1.1 := congrArg (fun q : Q => q.1) hE
      have hq : ι γ.1 * ν.1.1 ∈ Q := hmem (γ, ν)
      obtain ⟨γ0, _, hu⟩ := huniq _ hq
      have h1 : (ι γ.1)⁻¹ * (ι γ.1 * ν.1.1) ∈ N := by
        rw [inv_mul_cancel_left]; exact ν.1.2
      have h2 : (ι γ'.1)⁻¹ * (ι γ.1 * ν.1.1) ∈ N := by
        rw [hE', inv_mul_cancel_left]; exact ν'.1.2
      have hγ : γ = γ' := (hu γ h1).trans (hu γ' h2).symm
      subst hγ
      have : ν.1.1 = ν'.1.1 := mul_left_cancel hE'
      simp only [Prod.mk.injEq, true_and]
      exact Subtype.ext (Subtype.ext this)
    · rintro ⟨q, hq⟩
      obtain ⟨γ, hγ, _⟩ := huniq q hq
      have hνQ : (ι γ.1)⁻¹ * q ∈ Q := Q.mul_mem (Q.inv_mem (hιQ γ.1 γ.2)) hq
      refine ⟨(γ, ⟨⟨(ι γ.1)⁻¹ * q, hγ⟩, hνQ⟩), ?_⟩
      apply Subtype.ext
      show ι γ.1 * ((ι γ.1)⁻¹ * q) = q
      rw [mul_inv_cancel_left]
  let e := Equiv.ofBijective e0 hbij
  have hmeas : ∀ (γ : Γ) (ν : Q.subgroupOf N),
      Measurable (fun n : N => D.indicator (1 : G → ENNReal) (ι γ.1 * (ν • n).1 * h)) := by
    intro γ ν
    have : (fun n : N => ι γ.1 * (ν • n).1 * h) = fun n : N => (ι γ.1 * ν.1.1) * (n.1 * h) := by
      funext n; show ι γ.1 * (ν.1.1 * n.1) * h = _; simp only [mul_assoc]
    have hm : Measurable (fun n : N => (ι γ.1 * ν.1.1) * (n.1 * h)) := (hL _).comp hh
    rw [← this] at hm
    exact (measurable_one.indicator hD).comp hm
  calc ∑' γ : Γ, ∫⁻ n, D.indicator (1 : G → ENNReal) (n.1 * ι γ * h) ∂μN
      = ∑' γ : Γ, ∫⁻ n, D.indicator (1 : G → ENNReal) (ι γ * n.1 * h) ∂μN :=
        tsum_congr fun γ => hconj γ.1 γ.2
    _ = ∑' γ : Γ, ∑' ν : Q.subgroupOf N,
          ∫⁻ n in 𝓕, D.indicator (1 : G → ENNReal) (ι γ.1 * (ν • n).1 * h) ∂μN :=
        tsum_congr fun γ => hfd.lintegral_eq_tsum'' _
    _ = ∫⁻ n in 𝓕, ∑' γ : Γ, ∑' ν : Q.subgroupOf N,
          D.indicator (1 : G → ENNReal) (ι γ.1 * (ν • n).1 * h) ∂μN := by
        rw [lintegral_tsum]
        · refine tsum_congr fun γ => ?_
          rw [lintegral_tsum]
          exact fun ν => (hmeas γ ν).aemeasurable
        · exact fun γ => (Measurable.ennreal_tsum fun ν => hmeas γ ν).aemeasurable
    _ = ∫⁻ n in 𝓕, ∑' p : Γ × Q.subgroupOf N,
          D.indicator (1 : G → ENNReal) ((e p).1 * (n.1 * h)) ∂μN := by
        refine lintegral_congr fun n => ?_
        rw [ENNReal.tsum_prod']
        refine tsum_congr fun γ => tsum_congr fun ν => ?_
        show _ = D.indicator (1 : G → ENNReal) ((ι γ.1 * ν.1.1) * (n.1 * h))
        show D.indicator (1 : G → ENNReal) (ι γ.1 * (ν.1.1 * n.1) * h) = _
        simp only [mul_assoc]
    _ = ∫⁻ n in 𝓕, ∑' q : Q, D.indicator (1 : G → ENNReal) (q.1 * (n.1 * h)) ∂μN := by
        refine lintegral_congr fun n => ?_
        exact e.tsum_eq (fun q : Q => D.indicator (1 : G → ENNReal) (q.1 * (n.1 * h)))

end GlobalTheory

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenGraph
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCoveringMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLiftGlobalPrimitiveStatement

namespace GlobalTheory.PrimLift

open Metric Set Topology

/- English proof (translation)
Rewrite using `[Metric.isOpen_iff]`. Introduce and unpack `y ⟨hyO, hy⟩`. Take `⟨r, hr, hrO⟩` from `Metric.isOpen_iff.mp hO y hyO`. Use `⟨r, hr, fun z hz => ⟨hrO hz, ?_⟩⟩` and prove the remaining obligations. Establish `hd : ∀ x ∈ ball y r, HasFDerivAt (fun v => f v - g v) (0 : V →L[ℝ] ℂ) x`.

Introduce `x hx`. Establish `h` using `(hf x (hrO hx)).sub (hg x (hrO hx))`. Rewrite `h` using `[sub_self]`. Then use the resulting hypothesis. Use `(convex_ball y r).is_const_of_fderivWithin_eq_zero (𝕜 := ℝ) (f := fun v => f v - g v) (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt) (fun x hx => ((hd x hx).hasFDerivWithinAt).fderivWithin ((isOpen_ball.uniqueDiffWithinAt hx))) hz (mem_ball_self hr)` as an intermediate fact. Establish `h2 : f z - g z = f y - g y` using `this`.

Rewrite `h2` using `[hy, sub_self, sub_eq_zero]`. Conclude with `h2`.
-/
theorem isOpen_eq_of_hasFDerivAt {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (w : V → V →L[ℝ] ℂ) {O : Set V} {f g : V → ℂ} (hO : IsOpen O)
    (hf : ∀ y ∈ O, HasFDerivAt f (w y) y) (hg : ∀ y ∈ O, HasFDerivAt g (w y) y) :
    IsOpen {y | y ∈ O ∧ f y = g y} := by
  rw [Metric.isOpen_iff]
  rintro y ⟨hyO, hy⟩
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO y hyO
  refine ⟨r, hr, fun z hz => ⟨hrO hz, ?_⟩⟩
  have hd : ∀ x ∈ ball y r, HasFDerivAt (fun v => f v - g v) (0 : V →L[ℝ] ℂ) x := by
    intro x hx
    have h := (hf x (hrO hx)).sub (hg x (hrO hx))
    rwa [sub_self] at h
  have := (convex_ball y r).is_const_of_fderivWithin_eq_zero (𝕜 := ℝ)
    (f := fun v => f v - g v) (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => ((hd x hx).hasFDerivWithinAt).fderivWithin
      ((isOpen_ball.uniqueDiffWithinAt hx))) hz (mem_ball_self hr)
  have h2 : f z - g z = f y - g y := this
  rw [hy, sub_self, sub_eq_zero] at h2
  exact h2

/- English proof (translation)
Take `⟨r, hr, hrU⟩` from `Metric.isOpen_iff.mp hU a ha`. Use `⟨r, hr, hrU, ?_⟩` and prove the remaining obligations. Conclude with `(convex_ball a r).exists_forall_hasFDerivAt_of_fderiv_symmetric isOpen_ball ((hw.differentiableOn one_ne_zero).mono hrU) (fun b hb => hsymm b (hrU hb))`.
-/
theorem exists_ball_primitive {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {U : Set V} (w : V → V →L[ℝ] ℂ) (hU : IsOpen U) (hw : ContDiffOn ℝ 1 w U)
    (hsymm : ∀ a ∈ U, ∀ x y : V, fderiv ℝ w a x y = fderiv ℝ w a y x) (a : V) (ha : a ∈ U) :
    ∃ r > 0, ball a r ⊆ U ∧ ∃ f : V → ℂ, ∀ y ∈ ball a r, HasFDerivAt f (w y) y := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU a ha
  refine ⟨r, hr, hrU, ?_⟩
  exact (convex_ball a r).exists_forall_hasFDerivAt_of_fderiv_symmetric isOpen_ball
    ((hw.differentiableOn one_ne_zero).mono hrU) (fun b hb => hsymm b (hrU hb))

/- English proof (translation)
Introduce `V _ _ _ U w hU hsc hw hsymm`. Set `P : Set U → (U → ℂ) → Prop` to `fun O f => IsOpen O ∧ ∃ g : V → ℂ, (∀ y ∈ O, f y = g y) ∧ ∀ y ∈ O, HasFDerivAt g (w y) y`. Establish `hopenmap : IsOpenMap (Subtype.val : U → V)` using `hU.isOpenMap_subtype_val`. Establish `h1 : ∀ O f, P O f → IsOpen O` using `fun O f h => h.1`. Establish `h2 : ∀ O O' f, P O f → IsOpen O' → O' ⊆ O → P O' f`.

Introduce and unpack `O O' f ⟨-, g, hfg, hg⟩ hO' hsub`. Conclude with `⟨hO', g, fun y hy => hfg y (hsub hy), fun y hy => hg y (hsub hy)⟩`. Establish `h3 : ∀ O f (c : ℂ), P O f → P O (fun y => f y + c)`. Introduce and unpack `O f c ⟨hO, g, hfg, hg⟩`. Conclude with `⟨hO, fun v => g v + c, fun y hy => by simp [hfg y hy], fun y hy => (hg y hy).add_const c⟩`.

Establish `h4 : ∀ x, ∃ O f, x ∈ O ∧ P O f`. Introduce `x`. Take `⟨r, hr, -, g, hg⟩` from `exists_ball_primitive w hU hw hsymm x x.2`. Use `⟨Subtype.val ⁻¹' ball (x : V) r, fun y => g y, mem_ball_self hr, isOpen_ball.preimage continuous_subtype_val, g, fun _ _ => rfl, fun y hy => hg y hy⟩` and prove the remaining obligations. Establish `h5 : ∀ O f g, P O f → P O g → IsOpen {y | y ∈ O ∧ f y = g y}`.

Introduce and unpack `O f g ⟨hO, gf, hfgf, hgf⟩ ⟨-, gg, hggg, hgg⟩`. Establish `hO' : IsOpen (Subtype.val '' O)` using `hopenmap O hO`. Establish `ho` using `isOpen_eq_of_hasFDerivAt w hO' (fun y hy => by obtain ⟨y, hy, rfl⟩ := hy; exact hgf y hy) (fun y hy => by obtain ⟨y, hy, rfl⟩ := hy; exact hgg y hy)`. Use `ho.preimage continuous_subtype_val using 1` and compare the differences between its conclusion and the goal. Use extensionality with `y`.

Simplify using `only [mem_setOf_eq, mem_preimage]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hy, he⟩; exact ⟨⟨y, hy, rfl⟩, by rw [← hfgf y hy, ← hggg y hy, he]⟩`. Introduce and unpack `⟨⟨z, hz, hzy⟩, he⟩`. Establish `: z = y` using `Subtype.ext hzy`.

Substitute `this` using the available equality. Conclude with `⟨hz, by rw [hfgf z hz, hggg z hz, he]⟩`. Establish `hcov : IsCoveringMap (Etale.proj P)` using `(GlobalTheory.T.etale_space_covering_map) P h1 h2 h3 h4 h5`. Use `haveI : LocallyPathConnectedSpace U := hU.locallyPathConnectedSpace`. Take `⟨F, hF⟩` from `(GlobalTheory.T.etale_lift_global_primitive) P h1 h2 h3 h4 hcov`.

Use `⟨fun v => if h : v ∈ U then F ⟨v, h⟩ else 0, fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨O, f, haO, ⟨hO, g, hfg, hg⟩, hFf⟩` from `hF ⟨a, ha⟩`. Establish `hO' : IsOpen (Subtype.val '' O)` using `hopenmap O hO`. Use `(hg ⟨a, ha⟩ haO).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hO'.mem_nhds ⟨⟨a, ha⟩, haO, rfl⟩] with v hv`.

Take `⟨y, hy, rfl⟩` from `hv`. Simplify using `only [Subtype.coe_prop, dif_pos]`. Rewrite using `[hFf hy, hfg y hy]`.
-/
theorem exists_primitive_of_simplyConnected : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {U : Set V} (w₁ : V → V →L[ℝ] ℂ), IsOpen U → SimplyConnectedSpace U → ContDiffOn ℝ 1 w₁ U → (∀ a ∈ U, ∀ x y : V, fderiv ℝ w₁ a x y = fderiv ℝ w₁ a y x) → ∃ F : V → ℂ, ∀ a ∈ U, HasFDerivAt F (w₁ a) a := by
  intro V _ _ _ U w hU hsc hw hsymm
  classical

  let P : Set U → (U → ℂ) → Prop := fun O f => IsOpen O ∧
    ∃ g : V → ℂ, (∀ y ∈ O, f y = g y) ∧ ∀ y ∈ O, HasFDerivAt g (w y) y
  have hopenmap : IsOpenMap (Subtype.val : U → V) := hU.isOpenMap_subtype_val
  have h1 : ∀ O f, P O f → IsOpen O := fun O f h => h.1
  have h2 : ∀ O O' f, P O f → IsOpen O' → O' ⊆ O → P O' f := by
    rintro O O' f ⟨-, g, hfg, hg⟩ hO' hsub
    exact ⟨hO', g, fun y hy => hfg y (hsub hy), fun y hy => hg y (hsub hy)⟩
  have h3 : ∀ O f (c : ℂ), P O f → P O (fun y => f y + c) := by
    rintro O f c ⟨hO, g, hfg, hg⟩
    exact ⟨hO, fun v => g v + c, fun y hy => by simp [hfg y hy], fun y hy => (hg y hy).add_const c⟩
  have h4 : ∀ x, ∃ O f, x ∈ O ∧ P O f := by
    intro x
    obtain ⟨r, hr, -, g, hg⟩ := exists_ball_primitive w hU hw hsymm x x.2
    refine ⟨Subtype.val ⁻¹' ball (x : V) r, fun y => g y, mem_ball_self hr,
      isOpen_ball.preimage continuous_subtype_val, g, fun _ _ => rfl, fun y hy => hg y hy⟩
  have h5 : ∀ O f g, P O f → P O g → IsOpen {y | y ∈ O ∧ f y = g y} := by
    rintro O f g ⟨hO, gf, hfgf, hgf⟩ ⟨-, gg, hggg, hgg⟩
    have hO' : IsOpen (Subtype.val '' O) := hopenmap O hO
    have ho := isOpen_eq_of_hasFDerivAt w hO'
      (fun y hy => by obtain ⟨y, hy, rfl⟩ := hy; exact hgf y hy)
      (fun y hy => by obtain ⟨y, hy, rfl⟩ := hy; exact hgg y hy)
    convert ho.preimage continuous_subtype_val using 1
    ext y
    simp only [mem_setOf_eq, mem_preimage]
    constructor
    · rintro ⟨hy, he⟩; exact ⟨⟨y, hy, rfl⟩, by rw [← hfgf y hy, ← hggg y hy, he]⟩
    · rintro ⟨⟨z, hz, hzy⟩, he⟩
      have : z = y := Subtype.ext hzy
      subst this
      exact ⟨hz, by rw [hfgf z hz, hggg z hz, he]⟩
  have hcov : IsCoveringMap (Etale.proj P) := (GlobalTheory.T.etale_space_covering_map) P h1 h2 h3 h4 h5
  haveI : LocallyPathConnectedSpace U := hU.locallyPathConnectedSpace
  obtain ⟨F, hF⟩ := (GlobalTheory.T.etale_lift_global_primitive) P h1 h2 h3 h4 hcov
  refine ⟨fun v => if h : v ∈ U then F ⟨v, h⟩ else 0, fun a ha => ?_⟩
  obtain ⟨O, f, haO, ⟨hO, g, hfg, hg⟩, hFf⟩ := hF ⟨a, ha⟩
  have hO' : IsOpen (Subtype.val '' O) := hopenmap O hO
  refine (hg ⟨a, ha⟩ haO).congr_of_eventuallyEq ?_
  filter_upwards [hO'.mem_nhds ⟨⟨a, ha⟩, haO, rfl⟩] with v hv
  obtain ⟨y, hy, rfl⟩ := hv
  simp only [Subtype.coe_prop, dif_pos]
  rw [hFf hy, hfg y hy]

end GlobalTheory.PrimLift

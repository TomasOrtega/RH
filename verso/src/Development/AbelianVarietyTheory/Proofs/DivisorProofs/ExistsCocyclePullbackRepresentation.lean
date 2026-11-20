import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LactMemDomOfIsom

set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

namespace GlobalTheory.PullCocycle

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

/- English proof (translation)
Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨F, hF, rfl⟩` from `hy`. Conclude with `ha h F hF c x`. Consider the case `zero => show ((ρ h⁻¹ 0 : M.cusp ka) : C → M.dom → ℂ) c x = _`.

Simplify using the standard rewrite rules. Consider the case `add y z hy hz ihy ihz => show ((ρ h⁻¹ ((⟨y, hy⟩ : M.cusp ka) + ⟨z, hz⟩) : M.cusp ka) : C → M.dom → ℂ) c x = _`. Rewrite using `[map_add, Submodule.coe_add, Pi.add_apply, Pi.add_apply, ihy, ihz]`. Simplify using `[mul_add]`. Consider the case `smul t y hy ih => show ((ρ h⁻¹ (t • (⟨y, hy⟩ : M.cusp ka)) : M.cusp ka) : C → M.dom → ℂ) c x = _`.

Rewrite using `[map_smul, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, ih]`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem formula_span (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka))
    (a : U → C → ℂˣ)
    (ha : ∀ (h : U) (F : C → Frame M.Ψ r → ℂ) (hF : F ∈ M.SS ka) (c : C) (x : M.dom),
      ((ρ h⁻¹ ⟨M.res F, Submodule.subset_span ⟨F, hF, rfl⟩⟩ : M.cusp ka) : C → M.dom → ℂ) c x =
        (a h c : ℂ) * M.pull h F c x.1)
    (h : U) (c : C) (x : M.dom) (g : C → M.dom → ℂ) (hg : g ∈ Submodule.span ℂ (M.res '' M.SS ka)) :
    ((ρ h⁻¹ ⟨g, hg⟩ : M.cusp ka) : C → M.dom → ℂ) c x = (a h c : ℂ) * g (h • c) (Lmap M h c x) := by
  induction hg using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨F, hF, rfl⟩ := hy
    exact ha h F hF c x
  | zero =>
    show ((ρ h⁻¹ 0 : M.cusp ka) : C → M.dom → ℂ) c x = _
    simp
  | add y z hy hz ihy ihz =>
    show ((ρ h⁻¹ ((⟨y, hy⟩ : M.cusp ka) + ⟨z, hz⟩) : M.cusp ka) : C → M.dom → ℂ) c x = _
    rw [map_add, Submodule.coe_add, Pi.add_apply, Pi.add_apply, ihy, ihz]
    simp [mul_add]
  | smul t y hy ih =>
    show ((ρ h⁻¹ (t • (⟨y, hy⟩ : M.cusp ka)) : M.cusp ka) : C → M.dom → ℂ) c x = _
    rw [map_smul, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, ih]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/- English proof (translation)
Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`.
-/
theorem rho_inv_rho (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)) (h : U)
    (f : M.cusp ka) : ρ h⁻¹ (ρ h f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/- English proof (translation)
Use `set γ := M.tr (h * g) c * (M.tr h (g • c) * M.tr g c)⁻¹ with hγdef`. Establish `hγ : γ ∈ (M.comp ((h * g) • c)).Γ` using `M.tr_mul h g c`. Establish `e : lact γ (Lmap M h (g • c) (Lmap M g c x)).1 = (Lmap M (h * g) c x).1` using `by show lact γ (lact (M.tr h (g • c)) (lact (M.tr g c) x.1)) = lact (M.tr (h * g) c) x.1`. Rewrite using `[← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul (M.tr h (g • c)) (M.tr g c), ← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul γ, hγdef, inv_mul_cancel_right]`. Establish `hx : lact γ (Lmap M h (g • c) (Lmap M g c x)).1 ∈ M.dom` using `e ▸ (Lmap M (h * g) c x).2`.

Use `hf ((h * g) • c) γ hγ (Lmap M h (g • c) (Lmap M g c x)) hx` as an intermediate fact. Establish `e2 : (⟨lact γ (Lmap M h (g • c) (Lmap M g c x)).1, hx⟩ : M.dom) = Lmap M (h * g) c x` using `Subtype.ext e`. Rewrite `this` using `[e2]`. Rewrite using `[this, mul_smul]`.
-/
theorem pull_mul_eq (M : TwoLevels E r U C) (f : C → M.dom → ℂ) (hf : IsInv M f) (g h : U) (c : C) (x : M.dom) :
    f ((h * g) • c) (Lmap M (h * g) c x) = f (h • g • c) (Lmap M h (g • c) (Lmap M g c x)) := by
  set γ := M.tr (h * g) c * (M.tr h (g • c) * M.tr g c)⁻¹ with hγdef
  have hγ : γ ∈ (M.comp ((h * g) • c)).Γ := M.tr_mul h g c
  have e : lact γ (Lmap M h (g • c) (Lmap M g c x)).1 = (Lmap M (h * g) c x).1 := by
    show lact γ (lact (M.tr h (g • c)) (lact (M.tr g c) x.1)) = lact (M.tr (h * g) c) x.1
    rw [← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul (M.tr h (g • c)) (M.tr g c),
      ← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul γ, hγdef, inv_mul_cancel_right]
  have hx : lact γ (Lmap M h (g • c) (Lmap M g c x)).1 ∈ M.dom := e ▸ (Lmap M (h * g) c x).2
  have := hf ((h * g) • c) γ hγ (Lmap M h (g • c) (Lmap M g c x)) hx
  have e2 : (⟨lact γ (Lmap M h (g • c) (Lmap M g c x)).1, hx⟩ : M.dom) = Lmap M (h * g) c x := Subtype.ext e
  rw [e2] at this
  rw [this, mul_smul]

/- English proof (translation)
Introduce `E _ _ _ r U C _ _ M ka ρ hρ hinv`. Take `⟨a, ha⟩` from `hρ`. Establish `hform : ∀ (h : U) (f : M.cusp ka) (c : C) (x : M.dom), ((ρ h⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x = (a h c : ℂ) * (f : C → M.dom → ℂ) (h • c) (Lmap M h c x)`. Introduce and unpack `h ⟨g, hg⟩ c x`. Conclude with `formula_span M ka ρ a ha h c x g hg`.

Set `C0 : C → Prop` to `fun c => ∃ f : M.cusp ka, ∃ x : M.dom, (f : C → M.dom → ℂ) c x ≠ 0`. Establish `hstab : ∀ (h : U) (c : C), C0 c → C0 (h • c)`. Introduce and unpack `h c ⟨f, x, hfx⟩`. Use `⟨ρ h f, Lmap M h c x, fun h0 => hfx ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[rho_inv_rho]`. Use `_ = (a h c : ℂ) * ((ρ h f : M.cusp ka) : C → M.dom → ℂ) (h • c) (Lmap M h c x) := hform h _ c x`. Use `_ = 0 := by rw [h0, mul_zero]`. Establish `hstab' : ∀ (h : U) (c : C), ¬ C0 c → ¬ C0 (h • c)` using `fun h c hc h1 => hc (by`. Use `hstab h⁻¹ (h • c) h1` as an intermediate fact.

Rewrite using `[inv_smul_smul] at this)` and apply the resulting hypothesis. Establish `hcoc : ∀ (g h : U) (c : C) (x : M.dom) (f : M.cusp ka), (a (h * g) c : ℂ) * (f : C → M.dom → ℂ) ((h * g) • c) (Lmap M (h * g) c x) = (a g c : ℂ) * (a h (g • c) : ℂ) * (f : C → M.dom → ℂ) ((h * g) • c) (Lmap M (h * g) c x)`. Introduce `g h c x f`. Establish `L` using `hform (h * g) f c x`. Establish `R : ((ρ (h * g)⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x = (a g c : ℂ) * ((a h (g • c) : ℂ) * (f : C → M.dom → ℂ) (h • g • c) (Lmap M h (g • c) (Lmap M g c x)))`.

Rewrite using `[mul_inv_rev, map_mul, Module.End.mul_apply, hform g, hform h]`. Rewrite using `[← L, R, pull_mul_eq M _ (hinv _ f.2) g h c x]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨fun h c => if C0 c then a h c else 1, ?_, ?_⟩` and prove the remaining obligations. Introduce `g h c`.

Distinguish the cases in `hc : C0 c`. Establish `hgc : C0 (g • c)` using `hstab g c hc`. Establish `hhgc : C0 ((h * g) • c)` using `hstab (h * g) c hc`. Simplify using `only [hc, hgc, if_true]`. Take `⟨f', x, hfx⟩` from `hc`.

Use `set f := ρ (h * g) f' with hfdef`. Establish `hV : (f : C → M.dom → ℂ) ((h * g) • c) (Lmap M (h * g) c x) ≠ 0`. Introduce `h0`. Apply `hfx` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hfdef, rho_inv_rho]`. Use `_ = 0 := by rw [hform, h0, mul_zero]`. Use `ext`. Use `push_cast`. Conclude with `mul_right_cancel₀ hV (hcoc g h c x f)`.

Establish `hgc : ¬ C0 (g • c)` using `hstab' g c hc`. Simplify using `[hc, hgc]`. Introduce `h f c x`. Distinguish the cases in `hc : C0 c`. Simplify using `only [hc, if_true]`.

Conclude with `hform h f c x`. Establish `hhc : ¬ C0 (h • c)` using `hstab' h c hc`. Simplify using `only [hc, if_false, Units.val_one, one_mul]`. Establish `l0 : ((ρ h⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x = 0`. Assume the negation of the conclusion as `hne`.

Conclude with `hc ⟨ρ h⁻¹ f, x, hne⟩`. Establish `r0 : (f : C → M.dom → ℂ) (h • c) (Lmap M h c x) = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hhc ⟨f, _, hne⟩`. Rewrite using `[l0, r0]`.
-/
theorem exists_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → (∀ f ∈ M.cusp ka, IsInv M f) → ∃ a : U → C → ℂˣ, (∀ (g h : U) (c : C), a (h * g) c = a g c * a h (g • c)) ∧ ∀ (h : U) (f : M.cusp ka) (c : C) (x : M.dom), ((ρ h⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x = (a h c : ℂ) * (f : C → M.dom → ℂ) (h • c) (Lmap M h c x) := by
  intro E _ _ _ r U C _ _ M ka ρ hρ hinv
  obtain ⟨a, ha⟩ := hρ
  have hform : ∀ (h : U) (f : M.cusp ka) (c : C) (x : M.dom),
      ((ρ h⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x = (a h c : ℂ) * (f : C → M.dom → ℂ) (h • c) (Lmap M h c x) := by
    rintro h ⟨g, hg⟩ c x
    exact formula_span M ka ρ a ha h c x g hg
  classical
  let C0 : C → Prop := fun c => ∃ f : M.cusp ka, ∃ x : M.dom, (f : C → M.dom → ℂ) c x ≠ 0
  have hstab : ∀ (h : U) (c : C), C0 c → C0 (h • c) := by
    rintro h c ⟨f, x, hfx⟩
    refine ⟨ρ h f, Lmap M h c x, fun h0 => hfx ?_⟩
    calc (f : C → M.dom → ℂ) c x = ((ρ h⁻¹ (ρ h f) : M.cusp ka) : C → M.dom → ℂ) c x := by
          rw [rho_inv_rho]
      _ = (a h c : ℂ) * ((ρ h f : M.cusp ka) : C → M.dom → ℂ) (h • c) (Lmap M h c x) := hform h _ c x
      _ = 0 := by rw [h0, mul_zero]
  have hstab' : ∀ (h : U) (c : C), ¬ C0 c → ¬ C0 (h • c) := fun h c hc h1 => hc (by
    have := hstab h⁻¹ (h • c) h1
    rwa [inv_smul_smul] at this)
  have hcoc : ∀ (g h : U) (c : C) (x : M.dom) (f : M.cusp ka),
      (a (h * g) c : ℂ) * (f : C → M.dom → ℂ) ((h * g) • c) (Lmap M (h * g) c x) =
        (a g c : ℂ) * (a h (g • c) : ℂ) * (f : C → M.dom → ℂ) ((h * g) • c) (Lmap M (h * g) c x) := by
    intro g h c x f
    have L := hform (h * g) f c x
    have R : ((ρ (h * g)⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x =
        (a g c : ℂ) * ((a h (g • c) : ℂ) * (f : C → M.dom → ℂ) (h • g • c) (Lmap M h (g • c) (Lmap M g c x))) := by
      rw [mul_inv_rev, map_mul, Module.End.mul_apply, hform g, hform h]
    rw [← L, R, pull_mul_eq M _ (hinv _ f.2) g h c x]
    ring
  refine ⟨fun h c => if C0 c then a h c else 1, ?_, ?_⟩
  · intro g h c
    by_cases hc : C0 c
    · have hgc : C0 (g • c) := hstab g c hc
      have hhgc : C0 ((h * g) • c) := hstab (h * g) c hc
      simp only [hc, hgc, if_true]
      obtain ⟨f', x, hfx⟩ := hc
      set f := ρ (h * g) f' with hfdef
      have hV : (f : C → M.dom → ℂ) ((h * g) • c) (Lmap M (h * g) c x) ≠ 0 := by
        intro h0
        apply hfx
        calc (f' : C → M.dom → ℂ) c x = ((ρ (h * g)⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x := by
              rw [hfdef, rho_inv_rho]
          _ = 0 := by rw [hform, h0, mul_zero]
      ext
      push_cast
      exact mul_right_cancel₀ hV (hcoc g h c x f)
    · have hgc : ¬ C0 (g • c) := hstab' g c hc
      simp [hc, hgc]
  · intro h f c x
    by_cases hc : C0 c
    · simp only [hc, if_true]
      exact hform h f c x
    · have hhc : ¬ C0 (h • c) := hstab' h c hc
      simp only [hc, if_false, Units.val_one, one_mul]
      have l0 : ((ρ h⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x = 0 := by
        by_contra hne
        exact hc ⟨ρ h⁻¹ f, x, hne⟩
      have r0 : (f : C → M.dom → ℂ) (h • c) (Lmap M h c x) = 0 := by
        by_contra hne
        exact hhc ⟨f, _, hne⟩
      rw [l0, r0]

end GlobalTheory.PullCocycle

end

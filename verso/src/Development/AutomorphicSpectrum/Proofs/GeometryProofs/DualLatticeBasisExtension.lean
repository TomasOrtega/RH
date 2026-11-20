import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HcptPull

/- English proof (translation)
Introduce `Ω Ω' _ _ i R R' V V' _ _ _ _ j jd W W' ω ω' r b hj hR hjd hW' hω' hli hsp hmap`. Break down `Nat.eq_zero_or_pos r with rfl | hr` into its components or cases. Establish `hD : ∀ f : Module.Dual Ω W, f = 0`. Introduce `f`. Establish `hf : f ∈ Submodule.span Ω (Set.range b)` using `hsp ▸ Submodule.mem_top`.

Rewrite `hf` using `[Set.range_eq_empty, Submodule.span_empty]`. Conclude with `(Submodule.mem_bot Ω).1 hf`. Establish `hW0 : ∀ e ∈ W, e = 0`. Introduce `e he`. Establish `: (⟨e, he⟩ : W) = 0` using `(Module.forall_dual_apply_eq_zero_iff Ω _).1 fun f => by rw [hD f]; rfl`.

Conclude with `congrArg Subtype.val this`. Establish `hW'0 : W' = ⊥`. Rewrite using `[hW', Submodule.span_eq_bot]`. Introduce and unpack `_ ⟨e, he, rfl⟩`. Rewrite using `[hW0 e he, map_zero]`.

Establish `hS0 : Submodule.span R {e | e ∈ W ∧ ∀ w ∈ ω, w e ∈ R} = ⊥` using `Submodule.span_eq_bot.2 fun e he => hW0 e he.1`. Rewrite using `[hS0, Submodule.span_eq_bot.2, Submodule.span_eq_bot.2]`. Introduce and unpack `_ ⟨e, he, rfl⟩`. Establish `: e = 0` using `by simpa using he`. Rewrite using `[this, map_zero]`.

Introduce and unpack `e ⟨he, -⟩`. Rewrite `he` using `[hW'0]`. Conclude with `(Submodule.mem_bot Ω').1 he`. Establish `hω''` using `hω' hr`. Set `hb : Module.Basis (Fin r) Ω (Module.Dual Ω W)` to `Module.Basis.mk hli hsp.ge`.

Establish `hbb : ∀ k, hb k = b k` using `fun k => Module.Basis.mk_apply hli hsp.ge k`. Use `haveI : Module.Finite Ω (Module.Dual Ω W) := Module.Finite.of_basis hb`. Use `haveI : Module.Finite Ω W := Module.finite_dual_iff Ω |>.1 inferInstance`. Set `c : Module.Basis (Fin r) Ω W` to `hb.dualBasis.map (Module.evalEquiv Ω W).symm`. Establish `hbc : ∀ l k, b l (c k) = if l = k then 1 else 0`.

Introduce `l k`. Establish `h1 : c k = (Module.evalEquiv Ω W).symm (hb.dualBasis k)`. Simplify using `[c]`. Rewrite using `[h1, Module.apply_evalEquiv_symm_apply, ← hbb, Module.Basis.dualBasis_apply_self]`. Establish `hexp : ∀ e : W, e = ∑ k, b k e • c k`.

Introduce `e`. Use `conv_lhs => rw [← c.sum_repr e]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `congr 1`. Establish `: b k e = ∑ m, c.repr e m * b k (c m)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[this]`. Simplify using `[hbc]`. Establish `hcS : ∀ k, (c k : V) ∈ {e | e ∈ W ∧ ∀ w ∈ ω, w e ∈ R}`. Introduce `k`.

Use `⟨(c k).2, fun w hw => ?_⟩` and prove the remaining obligations. Establish `hwr : W.dualRestrict w ∈ Submodule.span R (Set.range b)`. Rewrite using `[← hmap]`. Conclude with `⟨w, hw, rfl⟩`. Establish `key : ∀ f ∈ Submodule.span R (Set.range b), f (c k) ∈ R`.

Introduce `f hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨l, rfl⟩` from `hx`. Rewrite using `[hbc]`.

Use `split_ifs`. Conclude with `R.one_mem`. Conclude with `R.zero_mem`. Consider the case `zero => simpa using R.zero_mem`. Consider the case `add x y _ _ hx hy => simpa using R.add_mem hx hy`.

Consider the case `smul a x _ hx`. Establish `: (a • x) (c k) = (a : Ω) * x (c k)` using `rfl`. Rewrite using `[this]`. Conclude with `R.mul_mem a.2 hx`. Conclude with `key _ hwr`.

Establish `hpick : ∀ l, ∃ w ∈ ω, W.dualRestrict w = b l`. Introduce `l`. Establish `: b l ∈ ω.map (W.dualRestrict.restrictScalars R)`. Rewrite using `[hmap]`. Conclude with `Submodule.subset_span ⟨l, rfl⟩`.

Take `⟨w, hw, hwb⟩` from `this`. Conclude with `⟨w, hw, hwb⟩`. Use `choose wl hwl hwb using hpick`. Establish `hspan : ∀ e' ∈ W', ∃ a : Fin r → Ω', e' = ∑ k, a k • j (c k : V)`. Introduce `e' he'`.

Establish `hle : W' ≤ Submodule.span Ω' (Set.range fun k => j (c k : V))`. Rewrite using `[hW', Submodule.span_le]`. Introduce and unpack `_ ⟨e, he, rfl⟩`. Establish `h1 : e = ∑ k, b k ⟨e, he⟩ • (c k : V)`. Use `congrArg (Subtype.val) (hexp ⟨e, he⟩)` as an intermediate fact.

Simplify using `using this`. Rewrite using `[SetLike.mem_coe, h1, map_sum]`. Use `sum_mem fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hj.1]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`.

Take `⟨a, ha⟩` from `(Submodule.mem_span_range_iff_exists_fun Ω').1 (hle he')`. Conclude with `⟨a, ha.symm⟩`. Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `e' ⟨he', hint⟩`.

Take `⟨a, rfl⟩` from `hspan e' he'`. Establish `hal : ∀ l, a l ∈ R'`. Introduce `l`. Establish `h1` using `hint (jd (wl l)) (by`. Rewrite using `[hω'']`.

Conclude with `Submodule.subset_span ⟨wl l, hwl l, rfl⟩)`. Establish `h2 : jd (wl l) (∑ k, a k • j (c k : V)) = a l`. Rewrite using `[map_sum]`. Establish `: ∀ k, jd (wl l) (a k • j (c k : V)) = a k * (if l = k then 1 else 0)`. Introduce `k`.

Establish `h3 : wl l (c k : V) = if l = k then 1 else 0`. Rewrite using `[← hbc, ← hwb]`. Simplify using `[Submodule.dualRestrict_apply]`. Rewrite using `[map_smul, hjd, smul_eq_mul, h3, apply_ite i, map_one, map_zero]`. Simplify using `[this]`.

Rewrite `h1` using `[h2]`. Then use the resulting hypothesis. Rewrite using `[SetLike.mem_coe]`. Use `sum_mem fun k _ => ?_` and prove the remaining obligations. Establish `: a k • j (c k : V) = (⟨a k, hal k⟩ : R') • j (c k : V)` using `rfl`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨(c k : V), Submodule.subset_span (hcS k), rfl⟩)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite `hx`, the goal using `[SetLike.mem_coe]`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Use `Submodule.subset_span ⟨?_, fun w hw => ?_⟩` and prove the remaining obligations. Rewrite using `[hW']`. Conclude with `Submodule.subset_span ⟨x, hx.1, rfl⟩`. Rewrite `hw` using `[hω'']`.

Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem f hf`. Take `⟨u, hu, rfl⟩` from `hf`. Rewrite using `[hjd]`. Conclude with `hR _ (hx.2 u hu)`.

Consider the case `zero => simpa using R'.zero_mem`. Consider the case `add f g _ _ hf hg => simpa using R'.add_mem hf hg`. Consider the case `smul a f _ hf`. Establish `: (a • f) (j x) = (a : Ω') * f (j x)` using `rfl`. Rewrite using `[this]`.

Conclude with `R'.mul_mem a.2 hf`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simpa using add_mem hx hy`. Consider the case `smul a x _ hx`. Establish `: j (a • x) = (⟨i a, hR a a.2⟩ : R') • j x` using `hj.1 (a : Ω) x`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem dual_pull : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (R : Subring Ω) (R' : Subring Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (jd : Module.Dual Ω V →+ Module.Dual Ω' V') (W : Submodule Ω V) (W' : Submodule Ω' V') (ω : Submodule R (Module.Dual Ω V)) (ω' : Submodule R' (Module.Dual Ω' V')) (r : ℕ) (b : Fin r → Module.Dual Ω W), IsExtOver i j → (∀ a ∈ R, i a ∈ R') → (∀ w e, jd w (j e) = i (w e)) → W' = Submodule.span Ω' (j '' (W : Set V)) → (0 < r → ω' = Submodule.span R' (jd '' (ω : Set (Module.Dual Ω V)))) → LinearIndependent Ω b → Submodule.span Ω (Set.range b) = ⊤ → ω.map (W.dualRestrict.restrictScalars R) = Submodule.span R (Set.range b) → Submodule.span R' {e | e ∈ W' ∧ ∀ w ∈ ω', w e ∈ R'} = Submodule.span R' (j '' (Submodule.span R {e | e ∈ W ∧ ∀ w ∈ ω, w e ∈ R} : Set V)) := by
  intro Ω Ω' _ _ i R R' V V' _ _ _ _ j jd W W' ω ω' r b hj hR hjd hW' hω' hli hsp hmap
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hD : ∀ f : Module.Dual Ω W, f = 0 := by
      intro f
      have hf : f ∈ Submodule.span Ω (Set.range b) := hsp ▸ Submodule.mem_top
      rw [Set.range_eq_empty, Submodule.span_empty] at hf
      exact (Submodule.mem_bot Ω).1 hf
    have hW0 : ∀ e ∈ W, e = 0 := by
      intro e he
      have : (⟨e, he⟩ : W) = 0 :=
        (Module.forall_dual_apply_eq_zero_iff Ω _).1 fun f => by rw [hD f]; rfl
      exact congrArg Subtype.val this
    have hW'0 : W' = ⊥ := by
      rw [hW', Submodule.span_eq_bot]
      rintro _ ⟨e, he, rfl⟩
      rw [hW0 e he, map_zero]
    have hS0 : Submodule.span R {e | e ∈ W ∧ ∀ w ∈ ω, w e ∈ R} = ⊥ :=
      Submodule.span_eq_bot.2 fun e he => hW0 e he.1
    rw [hS0, Submodule.span_eq_bot.2, Submodule.span_eq_bot.2]
    · rintro _ ⟨e, he, rfl⟩
      have : e = 0 := by simpa using he
      rw [this, map_zero]
    · rintro e ⟨he, -⟩
      rw [hW'0] at he
      exact (Submodule.mem_bot Ω').1 he
  have hω'' := hω' hr
  let hb : Module.Basis (Fin r) Ω (Module.Dual Ω W) := Module.Basis.mk hli hsp.ge
  have hbb : ∀ k, hb k = b k := fun k => Module.Basis.mk_apply hli hsp.ge k
  haveI : Module.Finite Ω (Module.Dual Ω W) := Module.Finite.of_basis hb
  haveI : Module.Finite Ω W := Module.finite_dual_iff Ω |>.1 inferInstance
  let c : Module.Basis (Fin r) Ω W := hb.dualBasis.map (Module.evalEquiv Ω W).symm
  have hbc : ∀ l k, b l (c k) = if l = k then 1 else 0 := by
    intro l k
    have h1 : c k = (Module.evalEquiv Ω W).symm (hb.dualBasis k) := by
      simp [c]
    rw [h1, Module.apply_evalEquiv_symm_apply, ← hbb, Module.Basis.dualBasis_apply_self]

  have hexp : ∀ e : W, e = ∑ k, b k e • c k := by
    intro e
    conv_lhs => rw [← c.sum_repr e]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    have : b k e = ∑ m, c.repr e m * b k (c m) := by
      calc b k e = b k (∑ m, c.repr e m • c m) := by rw [c.sum_repr]
        _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]
    rw [this]
    simp [hbc]

  have hcS : ∀ k, (c k : V) ∈ {e | e ∈ W ∧ ∀ w ∈ ω, w e ∈ R} := by
    intro k
    refine ⟨(c k).2, fun w hw => ?_⟩
    have hwr : W.dualRestrict w ∈ Submodule.span R (Set.range b) := by
      rw [← hmap]
      exact ⟨w, hw, rfl⟩
    have key : ∀ f ∈ Submodule.span R (Set.range b), f (c k) ∈ R := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨l, rfl⟩ := hx
        rw [hbc]
        split_ifs
        · exact R.one_mem
        · exact R.zero_mem
      | zero => simpa using R.zero_mem
      | add x y _ _ hx hy => simpa using R.add_mem hx hy
      | smul a x _ hx =>
        have : (a • x) (c k) = (a : Ω) * x (c k) := rfl
        rw [this]
        exact R.mul_mem a.2 hx
    exact key _ hwr

  have hpick : ∀ l, ∃ w ∈ ω, W.dualRestrict w = b l := by
    intro l
    have : b l ∈ ω.map (W.dualRestrict.restrictScalars R) := by
      rw [hmap]
      exact Submodule.subset_span ⟨l, rfl⟩
    obtain ⟨w, hw, hwb⟩ := this
    exact ⟨w, hw, hwb⟩
  choose wl hwl hwb using hpick
  have hspan : ∀ e' ∈ W', ∃ a : Fin r → Ω', e' = ∑ k, a k • j (c k : V) := by
    intro e' he'
    have hle : W' ≤ Submodule.span Ω' (Set.range fun k => j (c k : V)) := by
      rw [hW', Submodule.span_le]
      rintro _ ⟨e, he, rfl⟩
      have h1 : e = ∑ k, b k ⟨e, he⟩ • (c k : V) := by
        have := congrArg (Subtype.val) (hexp ⟨e, he⟩)
        simpa using this
      rw [SetLike.mem_coe, h1, map_sum]
      refine sum_mem fun k _ => ?_
      rw [hj.1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Ω').1 (hle he')
    exact ⟨a, ha.symm⟩
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro e' ⟨he', hint⟩
    obtain ⟨a, rfl⟩ := hspan e' he'
    have hal : ∀ l, a l ∈ R' := by
      intro l
      have h1 := hint (jd (wl l)) (by
        rw [hω'']
        exact Submodule.subset_span ⟨wl l, hwl l, rfl⟩)
      have h2 : jd (wl l) (∑ k, a k • j (c k : V)) = a l := by
        rw [map_sum]
        have : ∀ k, jd (wl l) (a k • j (c k : V)) = a k * (if l = k then 1 else 0) := by
          intro k
          have h3 : wl l (c k : V) = if l = k then 1 else 0 := by
            rw [← hbc, ← hwb]
            simp [Submodule.dualRestrict_apply]
          rw [map_smul, hjd, smul_eq_mul, h3, apply_ite i, map_one, map_zero]
        simp [this]
      rwa [h2] at h1
    rw [SetLike.mem_coe]
    refine sum_mem fun k _ => ?_
    have : a k • j (c k : V) = (⟨a k, hal k⟩ : R') • j (c k : V) := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨(c k : V), Submodule.subset_span (hcS k), rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem x hx =>
      refine Submodule.subset_span ⟨?_, fun w hw => ?_⟩
      · rw [hW']
        exact Submodule.subset_span ⟨x, hx.1, rfl⟩
      · rw [hω''] at hw
        induction hw using Submodule.span_induction with
        | mem f hf =>
          obtain ⟨u, hu, rfl⟩ := hf
          rw [hjd]
          exact hR _ (hx.2 u hu)
        | zero => simpa using R'.zero_mem
        | add f g _ _ hf hg => simpa using R'.add_mem hf hg
        | smul a f _ hf =>
          have : (a • f) (j x) = (a : Ω') * f (j x) := rfl
          rw [this]
          exact R'.mul_mem a.2 hf
    | zero => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul a x _ hx =>
      have : j (a • x) = (⟨i a, hR a a.2⟩ : R') • j x := hj.1 (a : Ω) x
      rw [this]
      exact Submodule.smul_mem _ _ hx

end GlobalTheory.CompanionTheory.Ar.HcptPull

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxCoh.Cx

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨c, rfl⟩` from `QuotientAddGroup.mk_surjective x`. Establish `hc : K.D1 c.1 = 0` using `c.2`.

Rewrite `hx` using `[CxMap.h1, QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]`. Take `⟨g, hg⟩` from `hx`. Rewrite using `[QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]`. Use `⟨g, ?_⟩` and prove the remaining obligations. Establish `hf : ∀ T T' (φ : T ⟶ T'), c.1.1 T T' φ = g T' - K.M0.map φ (g T)`.

Introduce `T T' φ`. Use `congrArg (fun p => p.1 T T' φ) hg` as an intermediate fact. Conclude with `this.symm`. Establish `h2c : ∀ T T' (φ : T ⟶ T'), c.1.2 T' - K.M1.map φ (c.1.2 T) - K.d0 T' (c.1.1 T T' φ) = 0`. Introduce `T T' φ`.

Use `congrArg (fun p => p.2.1 T T' φ) hc` as an intermediate fact. Simplify `this` using `[Cx.D1]`. Establish `hw` using `hA0 (fun T => c.1.2 T - K.d0 T (g T)) (by`. Introduce `T T' φ`. Use `h2c T T' φ` as an intermediate fact.

Rewrite `this` using `[hf, map_sub, K.diffZero_natural]`. Simplify using `only [map_sub]`. Rewrite using `[← sub_eq_zero, ← this]`. Use the proof step `abel)`. Use `Prod.ext (funext fun T => funext fun T' => funext fun φ => ?_) (funext fun T => ?_)` and prove the remaining obligations.

Simplify using `[Cx.D0, hf]`. Use `congrFun hw T` as an intermediate fact. Simplify using `only [Pi.zero_apply, sub_eq_zero] at this`. Simplify using `[Cx.D0, this]`. Introduce `y`.

Take `⟨c, rfl⟩` from `QuotientAddGroup.mk_surjective y`. Establish `hc : (Cx.single K.M0).D1 c.1 = 0` using `c.2`. Establish `hδ : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''), K.M0.map ψ (c.1.1 T T' φ) - c.1.1 T T'' (φ ≫ ψ) + c.1.1 T' T'' ψ = 0`. Introduce `T T' T'' φ ψ`. Use `congrArg (fun p => p.1 T T' T'' φ ψ) hc` as an intermediate fact.

Simplify `this` using `[Cx.D1]`. Take `⟨w, hw⟩` from `hA1 (fun T T' φ => K.d0 T' (c.1.1 T T' φ)) (by`. Introduce `T T' T'' φ ψ`. Establish `h` using `congrArg (K.d0 T'') (hδ T T' T'' φ ψ)`. Simplify using `only [map_add, map_sub, map_zero, K.diffZero_natural] at h ⊢`.

Rewrite using `[← sub_eq_zero, ← neg_eq_zero, ← h]`. Use the proof step `abel)`. Establish `hdw` using `hB0 (fun T => K.d1 T (w T)) (by`. Introduce `T T' φ`. Establish `h` using `congrArg (K.d1 T') (hw T T' φ)`.

Rewrite `h` using `[K.diffOne_diffZero, map_sub, K.diffOne_natural]`. Conclude with `(sub_eq_zero.mp h.symm))`. Set `z : K.Z1` to `⟨(c.1.1, w), by show K.D1 _ = 0`. Use `Prod.ext (funext fun T => funext fun T' => funext fun T'' => funext fun φ =>` and prove the remaining obligations. Use function extensionality and compare the values at `fun ψ => ?_) (Prod.ext (funext fun T => funext fun T' => funext fun φ => ?_)`.

Use the proof step `(funext fun T => ?_))`. Simplify `hδ T T' T'' φ ψ` using `[Cx.D1]`. Simplify using `[Cx.D1, hw T T' φ]`. Simplify `congrFun hdw T⟩` using `[Cx.D1]`. Use `⟨QuotientAddGroup.mk z, ?_⟩` and prove the remaining obligations.

Rewrite using `[CxMap.h1, QuotientAddGroup.map_mk]`. Use `congr 1`.
-/
theorem fnMap_h1_bijective (C : Type 1) [Category.{0} C] (K : Cx C) (hA0 : K.M1.Ac0)
    (hA1 : K.M1.Ac1) (hB0 : K.M2.Ac0) : Function.Bijective K.fnMap.h1 := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective x
    have hc : K.D1 c.1 = 0 := c.2
    rw [CxMap.h1, QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff,
      AddSubgroup.mem_addSubgroupOf] at hx
    obtain ⟨g, hg⟩ := hx
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    refine ⟨g, ?_⟩
    have hf : ∀ T T' (φ : T ⟶ T'), c.1.1 T T' φ = g T' - K.M0.map φ (g T) := by
      intro T T' φ
      have := congrArg (fun p => p.1 T T' φ) hg
      exact this.symm
    have h2c : ∀ T T' (φ : T ⟶ T'),
        c.1.2 T' - K.M1.map φ (c.1.2 T) - K.d0 T' (c.1.1 T T' φ) = 0 := by
      intro T T' φ
      have := congrArg (fun p => p.2.1 T T' φ) hc
      simpa [Cx.D1] using this
    have hw := hA0 (fun T => c.1.2 T - K.d0 T (g T)) (by
      intro T T' φ
      have := h2c T T' φ
      rw [hf, map_sub, K.diffZero_natural] at this
      simp only [map_sub]
      rw [← sub_eq_zero, ← this]; abel)
    refine Prod.ext (funext fun T => funext fun T' => funext fun φ => ?_) (funext fun T => ?_)
    · simp [Cx.D0, hf]
    · have := congrFun hw T
      simp only [Pi.zero_apply, sub_eq_zero] at this
      simp [Cx.D0, this]
  · intro y
    obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective y
    have hc : (Cx.single K.M0).D1 c.1 = 0 := c.2
    have hδ : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''),
        K.M0.map ψ (c.1.1 T T' φ) - c.1.1 T T'' (φ ≫ ψ) + c.1.1 T' T'' ψ = 0 := by
      intro T T' T'' φ ψ
      have := congrArg (fun p => p.1 T T' T'' φ ψ) hc
      simpa [Cx.D1] using this
    obtain ⟨w, hw⟩ := hA1 (fun T T' φ => K.d0 T' (c.1.1 T T' φ)) (by
      intro T T' T'' φ ψ
      have h := congrArg (K.d0 T'') (hδ T T' T'' φ ψ)
      simp only [map_add, map_sub, map_zero, K.diffZero_natural] at h ⊢
      rw [← sub_eq_zero, ← neg_eq_zero, ← h]; abel)
    have hdw := hB0 (fun T => K.d1 T (w T)) (by
      intro T T' φ
      have h := congrArg (K.d1 T') (hw T T' φ)
      rw [K.diffOne_diffZero, map_sub, K.diffOne_natural] at h
      exact (sub_eq_zero.mp h.symm))
    let z : K.Z1 := ⟨(c.1.1, w), by
      show K.D1 _ = 0
      refine Prod.ext (funext fun T => funext fun T' => funext fun T'' => funext fun φ =>
        funext fun ψ => ?_) (Prod.ext (funext fun T => funext fun T' => funext fun φ => ?_)
        (funext fun T => ?_))
      · simpa [Cx.D1] using hδ T T' T'' φ ψ
      · simp [Cx.D1, hw T T' φ]
      · simpa [Cx.D1] using congrFun hdw T⟩
    refine ⟨QuotientAddGroup.mk z, ?_⟩
    rw [CxMap.h1, QuotientAddGroup.map_mk]
    congr 1
end GlobalTheory.CxCoh.Cx

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxCoh

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `c hc`. Take `⟨a, rfl⟩` from `QuotientAddGroup.mk_surjective c`. Express the relevant statement in the definitionally equal form `(QuotientAddGroup.mk (K.fnMap.z2 a) : (Cx.single K.M0).H2) = 0 at hc`.

Rewrite `hc` using `[QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]`. Take `⟨⟨f, ω0⟩, hf⟩` from `hc`. Establish `hz : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''), K.M0.map ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ = a.1.1 T T' T'' φ ψ`. Introduce `T T' T'' φ ψ`. Use `congrArg (fun x => x.1 T T' T'' φ ψ) hf` as an intermediate fact.

Simplify using `[Cx.D1, Cx.fnMap, CxMap.z2, CxMap.p2] at this`. Conclude with `this`. Establish `ha` using `a.2`. Take `⟨ha1, ha2, ha3, ha4⟩` from `ha`. Take `⟨ω, hω⟩` from `h11 (fun T T' φ => a.1.2.1 T T' φ + K.d0 T' (f T T' φ)) (by`.

Introduce `T T' T'' φ ψ`. Rewrite using `[ha2 T T' T'' φ ψ, ← hz T T' T'' φ ψ]`. Simplify using `only [map_add, map_sub, K.diffZero_natural]`. Use the proof step `abel)`. Establish `hη : (fun T => a.1.2.2 T - K.d1 T (ω T)) = 0`.

Apply `h20` to reduce the goal to its premises. Introduce `T T' φ`. Establish `e` using `hω T T' φ`. Establish `e2 : a.1.2.1 T T' φ = ω T' - K.M1.map φ (ω T) - K.d0 T' (f T T' φ)`. Rewrite using `[← e]`.

Normalize the expressions using the abelian group laws. Rewrite using `[ha3 T T' φ, e2]`. Simplify using `only [map_sub, K.diffOne_diffZero, K.diffOne_natural]`. Normalize the expressions using the abelian group laws. Rewrite using `[QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]`.

Use `⟨(f, ω), ?_⟩` and prove the remaining obligations. Use `Prod.ext ?_ (Prod.ext ?_ ?_)` and prove the remaining obligations. Use function extensionality and compare the values at `T T' T'' φ ψ`. Conclude with `hz T T' T'' φ ψ`. Use function extensionality and compare the values at `T T' φ`.

Establish `e` using `hω T T' φ`. Express the relevant statement in the definitionally equal form `ω T' - K.M1.map φ (ω T) - K.d0 T' (f T T' φ) = _`. Rewrite using `[← e]`. Normalize the expressions using the abelian group laws. Use function extensionality and compare the values at `T`.

Establish `e` using `congrFun hη T`. Express the relevant statement in the definitionally equal form `K.d1 T (ω T) = _`. Simplify using `only [Pi.zero_apply, sub_eq_zero] at e`. Conclude with `e.symm`. Introduce `c`.

Take `⟨b, rfl⟩` from `QuotientAddGroup.mk_surjective c`. Take `⟨hb1, -, -, -⟩` from `b.2`. Take `⟨f, hf⟩` from `h12 (fun T T' T'' φ ψ => K.d0 T'' (b.1.1 T T' T'' φ ψ)) (by`. Introduce `T T' T'' T''' φ ψ χ`. Rewrite using `[← K.diffZero_natural, ← map_add, hb1, map_add])`.

Take `⟨g, hg⟩` from `h21 (fun T T' φ => K.d1 T' (-f T T' φ)) (by`. Introduce `T T' T'' φ ψ`. Establish `e` using `hf T T' T'' φ ψ`. Establish `e2 : f T T'' (φ ≫ ψ) = K.M1.map ψ (f T T' φ) + f T' T'' ψ - K.d0 T'' (b.1.1 T T' T'' φ ψ)`. Rewrite using `[e]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e2]`. Simplify using `only [map_neg, map_add, map_sub, K.diffOne_diffZero, K.diffOne_natural]`. Use the proof step `abel)`. Establish `h3 : (fun T => K.d2 T (g T)) = 0`.

Apply `h30` to reduce the goal to its premises. Introduce `T T' φ`. Establish `e` using `hg T T' φ`. Establish `e2 : g T' = K.M2.map φ (g T) + K.d1 T' (-f T T' φ)` using `by rw [e]; abel`. Rewrite using `[e2, map_add, K.diffTwo_comp_diffOne, add_zero, K.diffTwo_natural]`.

Set `a : K.Z2` to `⟨(b.1.1, fun T T' φ => -f T T' φ, g), by`. Use `⟨hb1, fun T T' T'' φ ψ => ?_, fun T T' φ => ?_, fun T => ?_⟩` and prove the remaining obligations. Rewrite using `[hf T T' T'' φ ψ]`. Simplify using `only [map_neg, map_sub, map_add]`. Normalize the expressions using the abelian group laws.

Establish `e` using `hg T T' φ`. Express the relevant statement in the definitionally equal form `g T' = K.M2.map φ (g T) + K.d1 T' (-f T T' φ)`. Rewrite using `[e]`. Normalize the expressions using the abelian group laws. Conclude with `congrFun h3 T⟩`.

Use `⟨QuotientAddGroup.mk a, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(QuotientAddGroup.mk (K.fnMap.z2 a) : (Cx.single K.M0).H2) = QuotientAddGroup.mk b`. Use `congr 1`.
-/
theorem fnMap_h2_bijective (C : Type 1) [Category.{0} C] (K : Cx C) (h11 : K.M1.Ac1) (h12 : K.M1.Ac2)
    (h20 : K.M2.Ac0) (h21 : K.M2.Ac1) (h30 : K.M3.Ac0) : Function.Bijective K.fnMap.h2 := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
    change (QuotientAddGroup.mk (K.fnMap.z2 a) : (Cx.single K.M0).H2) = 0 at hc
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range] at hc
    obtain ⟨⟨f, ω0⟩, hf⟩ := hc
    have hz : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''),
        K.M0.map ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ = a.1.1 T T' T'' φ ψ := by
      intro T T' T'' φ ψ
      have := congrArg (fun x => x.1 T T' T'' φ ψ) hf
      simp [Cx.D1, Cx.fnMap, CxMap.z2, CxMap.p2] at this
      exact this
    have ha := a.2
    obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
    obtain ⟨ω, hω⟩ := h11 (fun T T' φ => a.1.2.1 T T' φ + K.d0 T' (f T T' φ)) (by
      intro T T' T'' φ ψ
      rw [ha2 T T' T'' φ ψ, ← hz T T' T'' φ ψ]
      simp only [map_add, map_sub, K.diffZero_natural]
      abel)
    have hη : (fun T => a.1.2.2 T - K.d1 T (ω T)) = 0 := by
      apply h20
      intro T T' φ
      have e := hω T T' φ
      have e2 : a.1.2.1 T T' φ = ω T' - K.M1.map φ (ω T) - K.d0 T' (f T T' φ) := by
        rw [← e]; abel
      rw [ha3 T T' φ, e2]
      simp only [map_sub, K.diffOne_diffZero, K.diffOne_natural]
      abel
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]
    refine ⟨(f, ω), ?_⟩
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext T T' T'' φ ψ
      exact hz T T' T'' φ ψ
    · funext T T' φ
      have e := hω T T' φ
      change ω T' - K.M1.map φ (ω T) - K.d0 T' (f T T' φ) = _
      rw [← e]; abel
    · funext T
      have e := congrFun hη T
      change K.d1 T (ω T) = _
      simp only [Pi.zero_apply, sub_eq_zero] at e
      exact e.symm
  · intro c
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨hb1, -, -, -⟩ := b.2
    obtain ⟨f, hf⟩ := h12 (fun T T' T'' φ ψ => K.d0 T'' (b.1.1 T T' T'' φ ψ)) (by
      intro T T' T'' T''' φ ψ χ
      rw [← K.diffZero_natural, ← map_add, hb1, map_add])
    obtain ⟨g, hg⟩ := h21 (fun T T' φ => K.d1 T' (-f T T' φ)) (by
      intro T T' T'' φ ψ
      have e := hf T T' T'' φ ψ
      have e2 : f T T'' (φ ≫ ψ) = K.M1.map ψ (f T T' φ) + f T' T'' ψ - K.d0 T'' (b.1.1 T T' T'' φ ψ) := by
        rw [e]; abel
      rw [e2]
      simp only [map_neg, map_add, map_sub, K.diffOne_diffZero, K.diffOne_natural]
      abel)
    have h3 : (fun T => K.d2 T (g T)) = 0 := by
      apply h30
      intro T T' φ
      have e := hg T T' φ
      have e2 : g T' = K.M2.map φ (g T) + K.d1 T' (-f T T' φ) := by rw [e]; abel
      rw [e2, map_add, K.diffTwo_comp_diffOne, add_zero, K.diffTwo_natural]
    let a : K.Z2 := ⟨(b.1.1, fun T T' φ => -f T T' φ, g), by
      refine ⟨hb1, fun T T' T'' φ ψ => ?_, fun T T' φ => ?_, fun T => ?_⟩
      · rw [hf T T' T'' φ ψ]; simp only [map_neg, map_sub, map_add]; abel
      · have e := hg T T' φ
        change g T' = K.M2.map φ (g T) + K.d1 T' (-f T T' φ)
        rw [e]; abel
      · exact congrFun h3 T⟩
    refine ⟨QuotientAddGroup.mk a, ?_⟩
    change (QuotientAddGroup.mk (K.fnMap.z2 a) : (Cx.single K.M0).H2) = QuotientAddGroup.mk b
    congr 1

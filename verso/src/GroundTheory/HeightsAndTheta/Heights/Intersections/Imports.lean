import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreSide
import GroundTheory.HeightsAndTheta.Heights.Intersections.StChartSpecCount
import GroundTheory.HeightsAndTheta.Heights.Intersections.StChartNormPts
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

/- English proof (translation)
Introduce `K _ ι _ K' _ ι' _ κ v P' n G j hv hP' hZ hj hfin`. Establish `hchar : CharZero G.Φ`. Use `charZero_of_inj_zero fun N hN => ?_` and prove the remaining obligations. Establish `hmem : (C (N : ℤ) : MRing ι) ∈ imageZ v P'`. Rewrite using `[← G.ker_x, RingHom.mem_ker]`.

Simplify using `using hN`. Establish `h2 : (N : ℤ) ∈ (imageZ v P').comap (C : ℤ →+* MRing ι)` using `hmem`. Rewrite `h2` using `[hZ.2.2.1]`. Conclude with `(Ideal.mem_bot.mp h2)` after adjusting the coercions. Take `⟨E, hE, hcount⟩` from `hSC (MRing ι) G.Φ G.Φ' (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom _ (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩) G.gen hfin`.

Use `⟨E, fun hm => hE ?_, fun w hw hEw => ?_⟩` and prove the remaining obligations. Rewrite `hm` using `[← G.ker_x]`. Conclude with `hm`. Establish `hker : RingHom.ker (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom ≤ RingHom.ker (eval₂Hom (Int.castRingHom ℂ) w)`. Introduce `f hf`.

Establish `hf' : f ∈ imageZ v P'`. Rewrite using `[← G.ker_x]`. Conclude with `hf`. Establish `h0` using `hw.2 f hf'`. Rewrite using `[RingHom.mem_ker, coe_eval₂Hom]`.

Rewrite `h0` using `[eval_map]`. Then use the resulting hypothesis. Establish `hψE : eval₂Hom (Int.castRingHom ℂ) w E ≠ 0`. Rewrite using `[coe_eval₂Hom, ← eval_map]` and apply the resulting hypothesis. Take `⟨hZfin, hZcard, hZne⟩` from `hcount _ hker hψE`. Establish `hmh : IsMultiHomogIdeal P'` using `hP'.2.1.2.1`.

Establish `hiff : ∀ z' : (Σ k', ι' k') → ℂ, (∀ p, z' (v p) = w p) → (∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ = 1) → (z' ∈ mcPts P' ↔ ∀ F : MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι), eval₂ ((algebraMap G.Φ G.Φ').comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom) (fun q => G.x' ⟨q.1.1, q.2⟩ …`. Introduce `z' hzw hz1`. Establish `hw' : (fun p => z' (v p)) = w` using `funext hzw`. Establish `hwz : (fun p => z' (v p)) ∈ mcPts (imageZ v P')`. Rewrite using `[hw']`.

Conclude with `hw`. Establish `h` using `hNP K ι K' ι' κ v P' G j hv hmh hj z' hwz hz1`. Rewrite `h` using `[hw']`. Conclude with `h`. Use `set Z := {y : (Σ k : FibreBlock κ, ι' k.1) → ℂ | ∀ F : MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι), eval₂ ((algebraMap G.Φ G.Φ').comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom) (fun q => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩) F = 0 → eval₂ (eval₂Hom (Int.castRingHom ℂ) …`.

Use `set N := {z' | z' ∈ mcPts P' ∧ (∀ p, z' (v p) = w p) ∧ ∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ = 1} with hNdef`. Set `res : ((Σ k', ι' k') → ℂ) → (Σ k : FibreBlock κ, ι' k.1) → ℂ` to `fun z' q => z' ⟨q.1.1, q.2⟩`. Establish `hinj : Set.InjOn res N`. Introduce `a ha b hb hab`. Use function extensionality and compare the values at `q'`.

Take `⟨k', i⟩` from `q'`. Distinguish the cases in `h : k' ∈ Set.range κ`. Take `⟨p, hp⟩` from `hv.2.2.2 ⟨k', i⟩ h`. Rewrite using `[← hp, ha.2.1 p, hb.2.1 p]`. Conclude with `congrFun hab ⟨⟨k', h⟩, i⟩`.

Establish `himg : res '' N = Z`. Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨z', hz', rfl⟩`. Conclude with `(hiff z' hz'.2.1 hz'.2.2).1 hz'.1`. Introduce `y hy`.

Establish `hy1 : ∀ k : FibreBlock κ, y ⟨k, j k⟩ = 1`. Introduce `k`. Establish `h` using `hy (X ⟨k, j k⟩ - 1) (by simp [div_self (hj k)])`. Simplify `h` using `[sub_eq_zero]`. Set `z' : (Σ k', ι' k') → ℂ` to `fun q' => if h : q'.1 ∈ Set.range κ then w (hv.2.2.2 q' h).choose else y ⟨⟨q'.1, h⟩, q'.2⟩`.

Establish `hzw : ∀ p, z' (v p) = w p`. Introduce `p`. Establish `h : (v p).1 ∈ Set.range κ` using `⟨p.1, (hv.2.2.1 p).symm⟩`. Establish `hc : (hv.2.2.2 (v p) h).choose = p` using `hv.2.1 (hv.2.2.2 (v p) h).choose_spec`. Simplify using `only [z', dif_pos h, hc]`.

Establish `hz1 : ∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ = 1`. Introduce `k`. Simplify using `only [z', dif_neg k.2]`. Conclude with `hy1 k`. Establish `hres : res z' = y`.

Use function extensionality and compare the values at `q`. Simplify using `only [res, z', dif_neg q.1.2]`. Use `⟨z', ⟨(hiff z' hzw hz1).2 ?_, hzw, hz1⟩, hres⟩` and prove the remaining obligations. Establish `: (fun q : Σ k : FibreBlock κ, ι' k.1 => z' ⟨q.1.1, q.2⟩) = y` using `hres`. Rewrite using `[this]`.

Conclude with `hy`. Use `⟨Set.Finite.of_finite_image (himg ▸ hZfin) hinj, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hinj.ncard_image, himg]`. Conclude with `hZcard`. Introduce `z' hz' hzw hz1 q hq`.

Establish `hy` using `(hiff z' hzw hz1).1 hz'`. Conclude with `hZne _ hy q (div_ne_zero hq (hj q.1))`.
-/
theorem ChartNormCount.proof (hSC : ChartSpecCount.Statement) (hNP : ChartNormPts.Statement) :
    ChartNormCount.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G j hv hP' hZ hj hfin
  classical
  have hchar : CharZero G.Φ := by
    refine charZero_of_inj_zero fun N hN => ?_
    have hmem : (C (N : ℤ) : MRing ι) ∈ imageZ v P' := by
      rw [← G.ker_x, RingHom.mem_ker]
      simpa using hN
    have h2 : (N : ℤ) ∈ (imageZ v P').comap (C : ℤ →+* MRing ι) := hmem
    rw [hZ.2.2.1] at h2
    exact_mod_cast (Ideal.mem_bot.mp h2)
  obtain ⟨E, hE, hcount⟩ := hSC (MRing ι) G.Φ G.Φ' (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom _
    (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩) G.gen hfin
  refine ⟨E, fun hm => hE ?_, fun w hw hEw => ?_⟩
  · rw [← G.ker_x] at hm
    exact hm
  have hker : RingHom.ker (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom ≤
      RingHom.ker (eval₂Hom (Int.castRingHom ℂ) w) := by
    intro f hf
    have hf' : f ∈ imageZ v P' := by
      rw [← G.ker_x]
      exact hf
    have h0 := hw.2 f hf'
    rw [RingHom.mem_ker, coe_eval₂Hom]
    rwa [eval_map] at h0
  have hψE : eval₂Hom (Int.castRingHom ℂ) w E ≠ 0 := by
    rwa [coe_eval₂Hom, ← eval_map]
  obtain ⟨hZfin, hZcard, hZne⟩ := hcount _ hker hψE
  have hmh : IsMultiHomogIdeal P' := hP'.2.1.2.1
  have hiff : ∀ z' : (Σ k', ι' k') → ℂ, (∀ p, z' (v p) = w p) → (∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ = 1) →
      (z' ∈ mcPts P' ↔ ∀ F : MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι),
        eval₂ ((algebraMap G.Φ G.Φ').comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom)
          (fun q => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩) F = 0 →
        eval₂ (eval₂Hom (Int.castRingHom ℂ) w) (fun q => z' ⟨q.1.1, q.2⟩) F = 0) := by
    intro z' hzw hz1
    have hw' : (fun p => z' (v p)) = w := funext hzw
    have hwz : (fun p => z' (v p)) ∈ mcPts (imageZ v P') := by
      rw [hw']
      exact hw
    have h := hNP K ι K' ι' κ v P' G j hv hmh hj z' hwz hz1
    rw [hw'] at h
    exact h
  set Z := {y : (Σ k : FibreBlock κ, ι' k.1) → ℂ | ∀ F : MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι),
        eval₂ ((algebraMap G.Φ G.Φ').comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom)
          (fun q => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩) F = 0 →
        eval₂ (eval₂Hom (Int.castRingHom ℂ) w) y F = 0} with hZdef
  set N := {z' | z' ∈ mcPts P' ∧ (∀ p, z' (v p) = w p) ∧ ∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ = 1} with hNdef
  let res : ((Σ k', ι' k') → ℂ) → (Σ k : FibreBlock κ, ι' k.1) → ℂ := fun z' q => z' ⟨q.1.1, q.2⟩
  have hinj : Set.InjOn res N := by
    intro a ha b hb hab
    funext q'
    obtain ⟨k', i⟩ := q'
    by_cases h : k' ∈ Set.range κ
    · obtain ⟨p, hp⟩ := hv.2.2.2 ⟨k', i⟩ h
      rw [← hp, ha.2.1 p, hb.2.1 p]
    · exact congrFun hab ⟨⟨k', h⟩, i⟩
  have himg : res '' N = Z := by
    apply Set.Subset.antisymm
    · rintro _ ⟨z', hz', rfl⟩
      exact (hiff z' hz'.2.1 hz'.2.2).1 hz'.1
    · intro y hy
      have hy1 : ∀ k : FibreBlock κ, y ⟨k, j k⟩ = 1 := by
        intro k
        have h := hy (X ⟨k, j k⟩ - 1) (by simp [div_self (hj k)])
        simpa [sub_eq_zero] using h
      let z' : (Σ k', ι' k') → ℂ := fun q' =>
        if h : q'.1 ∈ Set.range κ then w (hv.2.2.2 q' h).choose else y ⟨⟨q'.1, h⟩, q'.2⟩
      have hzw : ∀ p, z' (v p) = w p := by
        intro p
        have h : (v p).1 ∈ Set.range κ := ⟨p.1, (hv.2.2.1 p).symm⟩
        have hc : (hv.2.2.2 (v p) h).choose = p := hv.2.1 (hv.2.2.2 (v p) h).choose_spec
        simp only [z', dif_pos h, hc]
      have hz1 : ∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ = 1 := by
        intro k
        simp only [z', dif_neg k.2]
        exact hy1 k
      have hres : res z' = y := by
        funext q
        simp only [res, z', dif_neg q.1.2]
      refine ⟨z', ⟨(hiff z' hzw hz1).2 ?_, hzw, hz1⟩, hres⟩
      have : (fun q : Σ k : FibreBlock κ, ι' k.1 => z' ⟨q.1.1, q.2⟩) = y := hres
      rw [this]
      exact hy
  refine ⟨Set.Finite.of_finite_image (himg ▸ hZfin) hinj, ?_, ?_⟩
  · rw [← hinj.ncard_image, himg]
    exact hZcard
  · intro z' hz' hzw hz1 q hq
    have hy := (hiff z' hzw hz1).1 hz'
    exact hZne _ hy q (div_ne_zero hq (hj q.1))

end GroundTheory.Heights₂.Heights.Inter

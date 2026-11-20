import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingCyclotomicTowerLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemAdjoinDivOfFixed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelOfMemAdjoin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerEmbeddingInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTowerUnionAdjoinIntegralClosureIffStatement

noncomputable section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5.TowerFix

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

/- English proof (translation)
Establish `hinj : Function.Injective ι` using `GlobalTheory.T.tower_embedding_injective p Ω h T n hn ι hι`. Take `⟨hdom, hdvr, -⟩` from `GlobalTheory.K5.OnDVR.isDVR_On p n hn`. Set `K` to `FractionRing (On p n)`. Set `φ : K →+* Ω` to `IsFractionRing.lift (g := ι.toRingHom) hinj`. Establish `hφ : ∀ w : On p n, φ (algebraMap (On p n) K w) = ι w` using `fun w => IsFractionRing.lift_algebraMap _ _`.

Set `φa : K →ₐ[O0 p] Ω` to `{ φ with commutes' := fun r => by`. Establish `: algebraMap (O0 p) K r = algebraMap (On p n) K (algebraMap (O0 p) (On p n) r)` using `IsScalarTower.algebraMap_apply _ _ _ r`. Use `show φ (algebraMap (O0 p) K r) = _`. Rewrite using `[this, hφ, AlgHom.commutes] }`. Establish `hwc0 : wc ≠ 0` using `fun h0 => hc (by rw [h0, map_zero])`.

Set `z : K` to `algebraMap (On p n) K wb / algebraMap (On p n) K wc`. Establish `hz : φa z = x` using `by show φ z = x`. Simplify using `only [z, map_div₀, hφ, hxe]`. Establish `hzi : IsIntegral (O0 p) z`. Rewrite using `[← isIntegral_algHom_iff φa φa.toRingHom.injective, hz]`.

Conclude with `hx`. Establish `hzi' : IsIntegral (On p n) z` using `hzi.tower_top`. Take `⟨w, hw⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hzi'`. Use `⟨w, ?_⟩` and prove the remaining obligations. Rewrite using `[← hφ, hw]`.

Conclude with `hz`.
-/
theorem exists_eq_of_isIntegral_div (h : IsClo p Ω) (T : Tower p Ω) {n : ℕ} (hn : 1 ≤ n)
    (ι : On p n →ₐ[O0 p] Ω) (hι : IsEmb T n ι) (wb wc : On p n) (hc : ι wc ≠ 0) {x : Ω}
    (hx : IsIntegral (O0 p) x) (hxe : x = ι wb / ι wc) : ∃ w : On p n, ι w = x := by
  have hinj : Function.Injective ι := GlobalTheory.T.tower_embedding_injective p Ω h T n hn ι hι
  obtain ⟨hdom, hdvr, -⟩ := GlobalTheory.K5.OnDVR.isDVR_On p n hn
  let K := FractionRing (On p n)
  let φ : K →+* Ω := IsFractionRing.lift (g := ι.toRingHom) hinj
  have hφ : ∀ w : On p n, φ (algebraMap (On p n) K w) = ι w := fun w =>
    IsFractionRing.lift_algebraMap _ _
  let φa : K →ₐ[O0 p] Ω :=
    { φ with
      commutes' := fun r => by
        have : algebraMap (O0 p) K r = algebraMap (On p n) K (algebraMap (O0 p) (On p n) r) :=
          IsScalarTower.algebraMap_apply _ _ _ r
        show φ (algebraMap (O0 p) K r) = _
        rw [this, hφ, AlgHom.commutes] }
  have hwc0 : wc ≠ 0 := fun h0 => hc (by rw [h0, map_zero])
  let z : K := algebraMap (On p n) K wb / algebraMap (On p n) K wc
  have hz : φa z = x := by
    show φ z = x
    simp only [z, map_div₀, hφ, hxe]
  have hzi : IsIntegral (O0 p) z := by
    rw [← isIntegral_algHom_iff φa φa.toRingHom.injective, hz]; exact hx
  have hzi' : IsIntegral (On p n) z := hzi.tower_top
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 hzi'
  refine ⟨w, ?_⟩
  rw [← hφ, hw]
  exact hz

end GlobalTheory.K5.TowerFix

/- English proof (translation)
Introduce `p _ Ω _ _ h T x hx`. Use `haveI := h.clo`. Use `haveI := h.alg`. Use `haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo h`. Rewrite using `[GlobalTheory.T.mem_towerUnionAdjoinIntegralClosure_iff p Ω T x]`.

Use `set B := Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq)`. Take `⟨b, hb, c, hc, hc0, hbc⟩` from `GlobalTheory.mem_adjoin_div_of_fixed (O0 p) Ω h.inj (Set.range T.ζ ∪ Set.range T.qq) (x : Ω) (fun g hg => hx g (by`. Rewrite using `[Subgroup.mem_iInf]`. Introduce `n`. Conclude with `⟨hg _ (Or.inl ⟨n, rfl⟩), hg _ (Or.inr ⟨n, rfl⟩)⟩))`.

Take `⟨m, hm⟩` from `GlobalTheory.K5.Level.exists_mem_bn T hb`. Take `⟨k, hk⟩` from `GlobalTheory.K5.Level.exists_mem_bn T hc`. Use `set N := max m k + 1`. Establish `hN : 1 ≤ N` using `Nat.le_add_left 1 _`. Establish `hbN : b ∈ GlobalTheory.K5.Level.Bn T N` using `GlobalTheory.K5.Level.bn_mono T (le_trans (le_max_left m k) (Nat.le_succ _)) hm`.

Establish `hcN : c ∈ GlobalTheory.K5.Level.Bn T N` using `GlobalTheory.K5.Level.bn_mono T (le_trans (le_max_right m k) (Nat.le_succ _)) hk`. Take `⟨ι, hι⟩` from `GlobalTheory.K5.Basic.exists_isEmb T N`. Take `⟨wb, hwb⟩` from `GlobalTheory.K5.Level.bn_le_range T N ι hι hbN`. Take `⟨wc, hwc⟩` from `GlobalTheory.K5.Level.bn_le_range T N ι hι hcN`. Take `⟨w, hw⟩` from `GlobalTheory.K5.TowerFix.exists_eq_of_isIntegral_div h T hN ι hι wb wc (by rw [show ι wc = c from hwc]; exact hc0) x.2 (by rw [hbc, show ι wb = b from hwb, show ι wc = c from hwc])`.

Rewrite using `[← hw]`. Conclude with `GlobalTheory.K5.Level.bn_le_B T N (GlobalTheory.K5.Level.range_le_bn T N ι hι w)`.
-/
theorem GlobalTheory.K5.mem_towerAlg_of_fixed :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
      ∀ (T : Tower p Ω) (x : (integralClosure (O0 p) Ω)),
        (∀ g ∈ ⨅ n, Gn T n, g (x : Ω) = x) → x ∈ towerAlg T := by
  intro p _ Ω _ _ h T x hx
  haveI := h.clo
  haveI := h.alg
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo h
  rw [GlobalTheory.T.mem_towerUnionAdjoinIntegralClosure_iff p Ω T x]
  set B := Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq)
  obtain ⟨b, hb, c, hc, hc0, hbc⟩ := GlobalTheory.mem_adjoin_div_of_fixed (O0 p) Ω h.inj
    (Set.range T.ζ ∪ Set.range T.qq) (x : Ω) (fun g hg => hx g (by
      rw [Subgroup.mem_iInf]
      intro n
      exact ⟨hg _ (Or.inl ⟨n, rfl⟩), hg _ (Or.inr ⟨n, rfl⟩)⟩))
  obtain ⟨m, hm⟩ := GlobalTheory.K5.Level.exists_mem_bn T hb
  obtain ⟨k, hk⟩ := GlobalTheory.K5.Level.exists_mem_bn T hc
  set N := max m k + 1
  have hN : 1 ≤ N := Nat.le_add_left 1 _
  have hbN : b ∈ GlobalTheory.K5.Level.Bn T N :=
    GlobalTheory.K5.Level.bn_mono T (le_trans (le_max_left m k) (Nat.le_succ _)) hm
  have hcN : c ∈ GlobalTheory.K5.Level.Bn T N :=
    GlobalTheory.K5.Level.bn_mono T (le_trans (le_max_right m k) (Nat.le_succ _)) hk
  obtain ⟨ι, hι⟩ := GlobalTheory.K5.Basic.exists_isEmb T N
  obtain ⟨wb, hwb⟩ := GlobalTheory.K5.Level.bn_le_range T N ι hι hbN
  obtain ⟨wc, hwc⟩ := GlobalTheory.K5.Level.bn_le_range T N ι hι hcN
  obtain ⟨w, hw⟩ := GlobalTheory.K5.TowerFix.exists_eq_of_isIntegral_div h T hN ι hι wb wc
    (by rw [show ι wc = c from hwc]; exact hc0) x.2
    (by rw [hbc, show ι wb = b from hwb, show ι wc = c from hwc])
  rw [← hw]
  exact GlobalTheory.K5.Level.bn_le_B T N (GlobalTheory.K5.Level.range_le_bn T N ι hι w)

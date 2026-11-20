import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section
open Filter Topology

namespace GlobalTheory.WeakClosed

/- English proof (translation)
Use `letI V : Valued K (ValuationRing.ValueGroup A K) := Valued.mk' (ValuationRing.valuation A K)`. Establish `hle : ∀ x y : K, Valued.v x ≤ Valued.v y ↔ ∃ c : A, algebraMap A K c * y = x`. Introduce `x y`. Express the relevant statement in the definitionally equal form `(∃ c : A, c • y = x) ↔ _`. Simplify using `only [Algebra.smul_def]`.

Establish `hinj` using `IsFractionRing.injective A K`. Use `GlobalTheory.WeakTop.continuous_act_of_orbits σ ?_ ?_` and prove the remaining obligations. Introduce `g x y`. Simplify using `only [← not_le, hle]`. Introduce and unpack `h ⟨c, hc⟩`.

Use `h ⟨(τ g).symm c, (σ g).injective ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hσ, RingEquiv.apply_symm_apply, hc]`. Establish `hA : ∀ x : A, Continuous fun g => σ g (algebraMap A K x)`. Introduce `x`. Rewrite using `[continuous_iff_continuousAt]`.

Introduce `g₀ s hs`. Take `⟨c, hc, hs⟩` from `GlobalTheory.WeakTop.mem_nhds_iff_lt.1 hs`. Take `⟨a, d, hd, rfl⟩` from `IsFractionRing.div_surjective A c`. Establish `hd0 : algebraMap A K d ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd`. Establish `ha : a ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at hc`. Rewrite using `[mem_map]`. Use `filter_upwards [ho x a g₀ ha] with g hg`. Apply `hs` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `Valued.v (σ g (algebraMap A K x) - σ g₀ (algebraMap A K x)) < _`. Rewrite using `[← not_le, hle, hσ, hσ, ← map_sub]`. Introduce and unpack `⟨e, he⟩`. Use `hg ⟨e * d, hinj ?_⟩` and prove the remaining obligations. Rewrite `he` using `[eq_div_iff hd0]`.

Rewrite using `[← he, map_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Introduce `x`. Take `⟨a, d, hd, rfl⟩` from `IsFractionRing.div_surjective A x`. Establish `hd0 : algebraMap A K d ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd`.

Simplify using `only [map_div₀]`. Conclude with `(hA a).div (hA d) fun g => by simpa using hd0`.
-/
theorem continuous_frac_act {A K G : Type} [CommRing A] [IsDomain A] [ValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K] [TopologicalSpace G] (τ : G → (A ≃+* A))
    (σ : G → (K ≃+* K)) (hσ : ∀ g a, σ g (algebraMap A K a) = algebraMap A K (τ g a))
    (ho : ∀ (x a : A) (g₀ : G), a ≠ 0 → ∀ᶠ g in 𝓝 g₀, ¬ (τ g x - τ g₀ x ∣ a)) :
    letI : Valued K (ValuationRing.ValueGroup A K) := Valued.mk' (ValuationRing.valuation A K)
    Continuous fun p : G × K => σ p.1 p.2 := by
  letI V : Valued K (ValuationRing.ValueGroup A K) := Valued.mk' (ValuationRing.valuation A K)
  have hle : ∀ x y : K, Valued.v x ≤ Valued.v y ↔ ∃ c : A, algebraMap A K c * y = x := by
    intro x y
    change (∃ c : A, c • y = x) ↔ _
    simp only [Algebra.smul_def]
  have hinj := IsFractionRing.injective A K
  refine GlobalTheory.WeakTop.continuous_act_of_orbits σ ?_ ?_
  · intro g x y
    simp only [← not_le, hle]
    rintro h ⟨c, hc⟩
    refine h ⟨(τ g).symm c, (σ g).injective ?_⟩
    rw [map_mul, hσ, RingEquiv.apply_symm_apply, hc]
  · have hA : ∀ x : A, Continuous fun g => σ g (algebraMap A K x) := by
      intro x
      rw [continuous_iff_continuousAt]
      intro g₀ s hs
      obtain ⟨c, hc, hs⟩ := GlobalTheory.WeakTop.mem_nhds_iff_lt.1 hs
      obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective A c
      have hd0 : algebraMap A K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
      have ha : a ≠ 0 := by
        rintro rfl
        simp at hc
      rw [mem_map]
      filter_upwards [ho x a g₀ ha] with g hg
      apply hs
      change Valued.v (σ g (algebraMap A K x) - σ g₀ (algebraMap A K x)) < _
      rw [← not_le, hle, hσ, hσ, ← map_sub]
      rintro ⟨e, he⟩
      refine hg ⟨e * d, hinj ?_⟩
      rw [eq_div_iff hd0] at he
      rw [← he, map_mul, map_mul]
      ring
    intro x
    obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective A x
    have hd0 : algebraMap A K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    simp only [map_div₀]
    exact (hA a).div (hA d) fun g => by simpa using hd0

/- English proof (translation)
Introduce `l _ P AI`. Use `continuous_frac_act (A := OCb l) (fun g => AI.actT g) (fun g => autCb l (AI.actT g)) (fun g a => autCb_alg l _ a) fun x a g₀ ha => ?_` and prove the remaining obligations. Take `⟨n, hn⟩ : ∃ n, PreTilt.coeff n a ≠ 0` from `by by_contra! h`. Use `ha (Perfection.ext fun n => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `PreTilt.coeff n a = PreTilt.coeff n 0`.

Rewrite using `[h, map_zero]`. Use `filter_upwards [GlobalTheory.WeakTop.eventually_coeff_eq AI x n g₀] with g hg`. Introduce and unpack `⟨c, hc⟩`. Apply `hn` to reduce the goal to its premises. Rewrite using `[hc, map_mul, map_sub, hg, sub_self, zero_mul]`.
-/
theorem continuous_autCb_cbTop : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P),
    letI := cbTop l; Continuous fun q : GQ l × Cb l => autCb l (AI.actT q.1) q.2 := by
  intro l _ P AI
  refine continuous_frac_act (A := OCb l) (fun g => AI.actT g) (fun g => autCb l (AI.actT g))
    (fun g a => autCb_alg l _ a) fun x a g₀ ha => ?_
  obtain ⟨n, hn⟩ : ∃ n, PreTilt.coeff n a ≠ 0 := by
    by_contra! h
    refine ha (Perfection.ext fun n => ?_)
    change PreTilt.coeff n a = PreTilt.coeff n 0
    rw [h, map_zero]
  filter_upwards [GlobalTheory.WeakTop.eventually_coeff_eq AI x n g₀] with g hg
  rintro ⟨c, hc⟩
  apply hn
  rw [hc, map_mul, map_sub, hg, sub_self, zero_mul]

end GlobalTheory.WeakClosed

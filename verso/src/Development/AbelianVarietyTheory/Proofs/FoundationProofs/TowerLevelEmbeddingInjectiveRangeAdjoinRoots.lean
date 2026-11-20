import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBasisOnZetaPowMulQPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingCyclotomicTowerLevel

open GlobalTheory.K5 GlobalTheory.KumDlog

noncomputable section

namespace GlobalTheory.K5.LevEmb

/- English proof (translation)
Introduce `p _ Ω _ _ hΩ T m hm ι hι`. Take `⟨b, hb⟩` from `GlobalTheory.K5.OnFree.on_free p m`. Establish `hadj : Algebra.adjoin (O0 p) {xn p m, yn p m} = ⊤` using `GlobalTheory.K5.OnDVR.adjoin_eq_top_of_basis b (xn p m) (yn p m) (fun i => (i : ℕ)) (fun j => (j : ℕ)) (fun i j => hb i j)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨hdom, -, -⟩` from `GlobalTheory.K5.OnDVR.isDVR_On p m hm haveI : Module.Finite (O0 p) (On p m) := Module.Finite.of_basis b haveI : Algebra.IsIntegral (O0 p) (On p m) := Algebra.IsIntegral.of_finite _ _`.

Establish `hk : RingHom.ker (ι : On p m →+* Ω) = ⊥`. Apply `Ideal.eq_bot_of_comap_eq_bot (R := O0 p)` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`. Introduce `a ha`. Rewrite `ha` using `[Ideal.mem_comap, RingHom.mem_ker]`.

Establish `h1 : algebraMap (O0 p) Ω a = 0`. Rewrite using `[← ι.commutes]`. Conclude with `ha`. Rewrite using `[Ideal.mem_bot]`. Conclude with `hΩ.inj (by rw [h1, map_zero])`.

Conclude with `(RingHom.injective_iff_ker_eq_bot _).2 hk`. Rewrite using `[← Algebra.map_top, ← hadj, AlgHom.map_adjoin, Set.image_pair, hι.1, hι.2]`. Both sides reduce to the same expression.
-/
theorem emb_inj_range : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (m : ℕ), 1 ≤ m → ∀ ι : On p m →ₐ[O0 p] Ω, IsEmb T m ι →
    Function.Injective ι ∧ ι.range = Lev T m := by
  intro p _ Ω _ _ hΩ T m hm ι hι
  obtain ⟨b, hb⟩ := GlobalTheory.K5.OnFree.on_free p m
  have hadj : Algebra.adjoin (O0 p) {xn p m, yn p m} = ⊤ :=
    GlobalTheory.K5.OnDVR.adjoin_eq_top_of_basis b (xn p m) (yn p m) (fun i => (i : ℕ)) (fun j => (j : ℕ))
      (fun i j => hb i j)
  refine ⟨?_, ?_⟩
  · obtain ⟨hdom, -, -⟩ := GlobalTheory.K5.OnDVR.isDVR_On p m hm
    haveI : Module.Finite (O0 p) (On p m) := Module.Finite.of_basis b
    haveI : Algebra.IsIntegral (O0 p) (On p m) := Algebra.IsIntegral.of_finite _ _
    have hk : RingHom.ker (ι : On p m →+* Ω) = ⊥ := by
      apply Ideal.eq_bot_of_comap_eq_bot (R := O0 p)
      rw [eq_bot_iff]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker] at ha
      have h1 : algebraMap (O0 p) Ω a = 0 := by
        rw [← ι.commutes]; exact ha
      rw [Ideal.mem_bot]
      exact hΩ.inj (by rw [h1, map_zero])
    exact (RingHom.injective_iff_ker_eq_bot _).2 hk
  · rw [← Algebra.map_top, ← hadj, AlgHom.map_adjoin, Set.image_pair, hι.1, hι.2]
    rfl

end GlobalTheory.K5.LevEmb

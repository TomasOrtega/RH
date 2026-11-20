import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrandPeriodic
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdeleVectorAnnihilatorsCompactOpenBasisStatement

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

namespace GlobalTheory.ThetaTransform

noncomputable def finEmbSnd (F : Type) [Field F] [NumberField F] (N : ℕ) : (Fin N → Af F) →+ VA F N where
  toFun v := (0, fun i => pairA F 0 (v i))
  map_zero' := rfl
  map_add' v w := by
    refine Prod.ext (add_zero _).symm ?_
    funext i
    exact Prod.ext (add_zero _).symm rfl

/- English proof (translation)
The claim follows from `continuous_const.prodMk (continuous_pi fun i => continuous_const.prodMk (continuous_apply i))`.
-/
theorem continuous_finEmbSnd (F : Type) [Field F] [NumberField F] (N : ℕ) : Continuous (finEmbSnd F N) :=
  continuous_const.prodMk (continuous_pi fun i => continuous_const.prodMk (continuous_apply i))

/- English proof (translation)
Establish `h : Bd (Af F) (half F N) (fin x) v = ∑ i, fin x i * v i`. Simplify using `[Bd, half]`. Rewrite using `[h]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `fstA F (∑ i, x i * pairA F 0 (v i)) = 0`.

Rewrite using `[map_sum]`. Conclude with `Finset.sum_eq_zero fun i _ => by rw [map_mul]; exact mul_zero _`. Express the relevant statement in the definitionally equal form `sndA F (∑ i, x i * pairA F 0 (v i)) = _`. Rewrite using `[map_sum]`. Both sides reduce to the same expression.
-/
theorem dotProduct_finEmbSnd {F : Type} [Field F] [NumberField F] {N : ℕ} (x : Fin N → AF F) (v : Fin N → Af F) :
    x ⬝ᵥ (finEmbSnd F N v).2 = pairA F 0 (Bd (Af F) (half F N) (fin x) v) := by
  have h : Bd (Af F) (half F N) (fin x) v = ∑ i, fin x i * v i := by
    simp [Bd, half]
  rw [h]
  refine Prod.ext ?_ ?_
  · change fstA F (∑ i, x i * pairA F 0 (v i)) = 0
    rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [map_mul]; exact mul_zero _
  · change sndA F (∑ i, x i * pairA F 0 (v i)) = _
    rw [map_sum]
    rfl

/- English proof (translation)
Introduce `F _ _ N _ ψ lam ν hc 𝓓 hD _ f hq hl`. Take `⟨U, hU, hf⟩` from `hl`. Establish `h0 : inf (0 : Fin N → AF F) = 0` using `rfl`. Use `⟨⟨U.comap (AddMonoidHom.inl (Fin N → AF F) (Fin N → AF F)), hU.preimage (f := fun u : Fin N → AF F => ((u, 0) : VA F N)) (continuous_id.prodMk continuous_const), ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `u hu hi x`.

Rewrite using `[← invV_heisV_fst, hf (u, 0) hu hi h0]`. Use `⟨_, (GlobalTheory.T.finiteAdeleVector_annihilators_compact_open_basis F N ψ lam ν (half F N) hc).1 (U.comap (finEmbSnd F N)) (hU.preimage (continuous_finEmbSnd F N)), fun x hx v hv => ?_⟩` and prove the remaining obligations. Establish `h1` using `invV_heisV_snd hc.2.2.2.1 hD hq (finEmbSnd F N v).2 x`. Rewrite `h1` using `[show ((0 : Fin N → AF F), (finEmbSnd F N v).2) = finEmbSnd F N v from rfl, hf _ hv h0 rfl, dotProduct_finEmbSnd]`. Conclude with `mul_right_cancel₀ hx (h1.symm.trans (one_mul _).symm)`.
-/
theorem invV_level_support : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ f : VA F N → ℂ, QuasiV ψ f → LevelV ψ f → (∃ U : AddSubgroup (Fin N → AF F), IsOpen (U : Set (Fin N → AF F)) ∧ ∀ u ∈ U, inf u = 0 → ∀ x, invV ψ ν 𝓓 f (x + u) = invV ψ ν 𝓓 f x) ∧ ∃ K : Set (Fin N → Af F), IsCompact K ∧ ∀ x, invV ψ ν 𝓓 f x ≠ 0 → fin x ∈ K := by
  intro F _ _ N _ ψ lam ν hc 𝓓 hD _ f hq hl
  obtain ⟨U, hU, hf⟩ := hl
  have h0 : inf (0 : Fin N → AF F) = 0 := rfl
  refine ⟨⟨U.comap (AddMonoidHom.inl (Fin N → AF F) (Fin N → AF F)),
    hU.preimage (f := fun u : Fin N → AF F => ((u, 0) : VA F N)) (continuous_id.prodMk continuous_const), ?_⟩, ?_⟩
  · intro u hu hi x
    rw [← invV_heisV_fst, hf (u, 0) hu hi h0]
  · refine ⟨_, (GlobalTheory.T.finiteAdeleVector_annihilators_compact_open_basis F N ψ lam ν (half F N) hc).1 (U.comap (finEmbSnd F N))
      (hU.preimage (continuous_finEmbSnd F N)), fun x hx v hv => ?_⟩
    have h1 := invV_heisV_snd hc.2.2.2.1 hD hq (finEmbSnd F N v).2 x
    rw [show ((0 : Fin N → AF F), (finEmbSnd F N v).2) = finEmbSnd F N v from rfl, hf _ hv h0 rfl,
      dotProduct_finEmbSnd] at h1
    exact mul_right_cancel₀ hx (h1.symm.trans (one_mul _).symm)

end GlobalTheory.ThetaTransform

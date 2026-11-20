import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SChain

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

/- English proof (translation)
Introduce `k _ A _ m θ hθ H V P U`. Introduce `_ _ _ _ _ _ _ _ _ _ μ φ z hz`. Take `⟨-, hnat, hcomp, -, hsub⟩` from `sChain A`. Establish `cyc : ∀ {G G' : Type} [Group G] [Group G'] (f : G →* G') (w : Ch A G (m + 1)), Cyc w → Cyc (cm A f (m + 1) w)`. Introduce `G G' _ _ f w hw`.

Unfold `Cyc at hw ⊢`. Rewrite using `[hnat, hw, map_zero]`. Rewrite using `[hcomp, hθ.iso (V × P) U φ _ (cyc _ _ hz), hθ.add H V P μ 1 z hz]`. Establish `htriv : (θ P) (cm A (1 : H →* P ≃ₗ[k] P) (m + 1) z) = 0`. Apply `hθ.bdry` to reduce the goal to its premises.

Establish `hf : (1 : H →* P ≃ₗ[k] P) = (1 : Unit →* P ≃ₗ[k] P).comp (1 : H →* Unit)`. Use extensionality with `h x`. Both sides reduce to the same expression. Rewrite using `[hf, hcomp]`. Take `⟨w, hw⟩` from `hsub Unit m _ (cyc (1 : H →* Unit) z hz)`.

Rewrite using `[← hw, ← hnat]`. Conclude with `⟨_, rfl⟩`. Rewrite using `[htriv, add_zero]`.
-/
theorem UpperTheory.V.ZK.Cl.cTriv :
    UpperTheory.V.ZK.Cl.CTriv := by
  intro k _ A _ m θ hθ H V P U
  intro _ _ _ _ _ _ _ _ _ _ μ φ z hz
  obtain ⟨-, hnat, hcomp, -, hsub⟩ := sChain A
  have cyc : ∀ {G G' : Type} [Group G] [Group G'] (f : G →* G') (w : Ch A G (m + 1)),
      Cyc w → Cyc (cm A f (m + 1) w) := by
    intro G G' _ _ f w hw
    unfold Cyc at hw ⊢
    rw [hnat, hw, map_zero]
  rw [hcomp, hθ.iso (V × P) U φ _ (cyc _ _ hz), hθ.add H V P μ 1 z hz]
  have htriv : (θ P) (cm A (1 : H →* P ≃ₗ[k] P) (m + 1) z) = 0 := by
    apply hθ.bdry
    have hf : (1 : H →* P ≃ₗ[k] P) = (1 : Unit →* P ≃ₗ[k] P).comp (1 : H →* Unit) := by
      ext h x
      rfl
    rw [hf, hcomp]
    obtain ⟨w, hw⟩ := hsub Unit m _ (cyc (1 : H →* Unit) z hz)
    rw [← hw, ← hnat]
    exact ⟨_, rfl⟩
  rw [htriv, add_zero]

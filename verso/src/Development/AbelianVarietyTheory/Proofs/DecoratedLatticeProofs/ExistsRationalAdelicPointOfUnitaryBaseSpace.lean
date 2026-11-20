import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicPointInfiniteMatricesEqOneOfFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

/- English proof (translation)
Substitute `hn` using the available equality. Establish `hγ' : Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) γ.1 * HSpace.gram V * γ.1 = HSpace.gram V` using `hγ`. Establish `hmem : Formalism.UG.bc (inclR (F` using `D.host.F) (AF D.host.F)) γ ∈ HR (AF D.host.F) (Formalism.L2.Forms.sigD D) (HSpace.gram V) := by`. Express the relevant statement in the definitionally equal form `Formalism.UG.cT (sigR (AF D.host.F) (Formalism.L2.Forms.sigD D)) (γ.1.map (inclR (F := D.host.F) (AF D.host.F))) * (HSpace.gram V).map (inclR (F := D.host.F) (AF D.host.F)) * γ.1.map (inclR (F := D.host.F) (AF D.host.F)) = (HSpace.gram V).map (inclR (F := D.host.F) (AF D.host.F))`. Establish `e : Formalism.UG.cT (sigR (AF D.host.F) (Formalism.L2.Forms.sigD D)) (γ.1.map (inclR (F` using `D.host.F) (AF D.host.F))) = (Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) γ.1).map (inclR (F := D.host.F) (AF D.host.F)) := by`.

Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite using `[e, ← Matrix.map_mul, ← Matrix.map_mul, hγ']`. Use `⟨⟨_, hmem⟩, ⟨γ, hγ', rfl⟩, ?_, fun τ => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Both sides reduce to the same expression. Use extensionality with `i j`. Conclude with `(hθ τ).1 (γ.1 i j)`.
-/
theorem exists_GQ_of_unitary {D : D7} (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) {n : ℕ} (hn : V.rank = n)
    (γ : GL (Fin n) D.host.E)
    (hγ : γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E)
      (Matrix.reindex (finCongr hn) (finCongr hn) (HSpace.gram V))) :
    ∃ a : GA D V, a ∈ GQ V ∧
      GlobalTheory.AdForm.finM V hn a =
        (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ).1 ∧
      ∀ τ, GlobalTheory.AdForm.infM θ V hn a τ = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ : Matrix _ _ _) τ := by
  subst hn
  have hγ' : Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) γ.1 * HSpace.gram V * γ.1 = HSpace.gram V := hγ
  have hmem : Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γ ∈
      HR (AF D.host.F) (Formalism.L2.Forms.sigD D) (HSpace.gram V) := by
    change Formalism.UG.cT (sigR (AF D.host.F) (Formalism.L2.Forms.sigD D)) (γ.1.map (inclR (F := D.host.F) (AF D.host.F))) *
      (HSpace.gram V).map (inclR (F := D.host.F) (AF D.host.F)) * γ.1.map (inclR (F := D.host.F) (AF D.host.F)) =
      (HSpace.gram V).map (inclR (F := D.host.F) (AF D.host.F))
    have e : Formalism.UG.cT (sigR (AF D.host.F) (Formalism.L2.Forms.sigD D)) (γ.1.map (inclR (F := D.host.F) (AF D.host.F))) =
        (Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) γ.1).map (inclR (F := D.host.F) (AF D.host.F)) := by
      ext i j
      rfl
    rw [e, ← Matrix.map_mul, ← Matrix.map_mul, hγ']
  refine ⟨⟨_, hmem⟩, ⟨γ, hγ', rfl⟩, ?_, fun τ => ?_⟩
  · ext i j
    rfl
  · ext i j
    exact (hθ τ).1 (γ.1 i j)

/- English proof (translation)
Introduce `D θ hθ γ hγ` and use `exists_GQ_of_unitary θ hθ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) γ hγ`.
-/
theorem exists_GQ_of_unitary0 : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ γ : GL (Fin (D.R.N 0)) D.host.E, γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) → ∃ a : GA D (D.sp.X 0), a ∈ GQ (D.sp.X 0) ∧ GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ).1 ∧ ∀ τ, GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ : Matrix _ _ _) τ :=
  fun D θ hθ γ hγ => exists_GQ_of_unitary θ hθ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) γ hγ

end GlobalTheory.Core.Mi

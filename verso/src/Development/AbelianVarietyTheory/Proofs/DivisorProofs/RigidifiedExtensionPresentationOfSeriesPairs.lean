import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricFormalGroupCocycleIffMemCocyclesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CounitCotangentClassPowerSeriesEvalAtNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupFormalLawCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDifferentialsConnectedPDivGroupCoordinaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionsEqSeriesInChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSquareCoordinatesPresentLevelsStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

/- English proof (translation)
Introduce `p k _ d G c μ ρ hμ hρ`. Establish `hcoc` using `GlobalTheory.T.isSymmetricFormalGroupCocycle_iff_mem_cocycles p k d G c μ hμ`. Establish `hdu` using `GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k d`. Establish `hlaw` using `((GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k d G c).2 μ hμ).2`. Establish `hom` using `GlobalTheory.T.invariantDifferentials_connectedPDivGroup_coordinates p k d G c`.

Establish `hone` using `GlobalTheory.T.functions_eq_series_in_chart p k d G c`. Establish `hpres` using `(GlobalTheory.T.chart_square_coordinates_present_levels p k d G c).2`. Prove the components needed by the constructor for the conclusion. Introduce `v`. Take `⟨⟨z, u⟩, rfl⟩` from `Submodule.mkQ_surjective _ v`.

Take `⟨s, hs, -⟩` from `hpres z.1 (fun n => (z.2 n).2)`. Take `⟨w, hw, -⟩` from `hom.2 u`. Establish `hz : (fun n => c.ev₂ n s) = z.1` using `funext hs`. Use `⟨s, w, (hcoc s).2 (hz ▸ z.2), ?_⟩` and prove the remaining obligations. Conclude with `hρ s w z u (fun n => (hs n).symm) hw`.

Introduce `s w hs`. Set `z : G.cocycles` to `⟨fun n => c.ev₂ n s, (hcoc s).1 hs⟩`. Set `u : G.omega` to `⟨fun n => ∑ i, w i • dUnit k (c.x n i), hom.1 w⟩`. Rewrite using `[hρ s w z u (fun _ => rfl) (fun _ => rfl)]`. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk _ = 0 ↔ _`.

Rewrite using `[Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨B, hB⟩`. Rewrite `hB` using `[LinearMap.prod_apply, Prod.mk.injEq]`. Take `⟨b, hb, -⟩` from `hone.2.2 B.1 B.2`.

Use `⟨b, ?_, ?_⟩` and prove the remaining obligations. Establish `hz2 : ∀ n, pullbackTwo (G.res n) (c.ev₂ (n + 1) s) = c.ev₂ n s` using `fun n => hone.2.1 n s`. Take `⟨t, -, ht⟩` from `hpres (fun n => c.ev₂ n s) hz2`. Establish `h1` using `ht s (fun _ => rfl)`. Establish `h2` using `ht (cob1 μ b) (fun n => by`.

Rewrite using `[(hlaw n b).2, hb n]`. Conclude with `(congrArg (fun y : G.cocycles => y.1 n) hB.1))`. Conclude with `h1.trans h2.symm`. Take `⟨w', -, hw'⟩` from `hom.2 u`. Establish `e1` using `hw' w (fun _ => rfl)`.

Establish `e2` using `hw' (lin b) (fun n => by`. Rewrite using `[← (hdu (G.A n) (c.x n) (c.nil n) (c.aug n) b).2]`. Express the relevant statement in the definitionally equal form `_ = dUnit k (c.ev n b)`. Rewrite using `[hb n]`. Conclude with `(congrArg (fun y : G.omega => y.1 n) hB.2).symm)`.

Conclude with `e1.trans e2.symm`. Introduce and unpack `⟨b, rfl, rfl⟩`. Use `⟨⟨fun n => c.ev n b, fun n => hone.1 n b⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.prod_apply, Prod.mk.injEq]`. Prove the components needed by the constructor for the conclusion.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `n`. Conclude with `((hlaw n b).2).symm`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `n`.

Conclude with `(hdu (G.A n) (c.x n) (c.nil n) (c.aug n) b).2`.
-/
theorem GlobalTheory.Katz.isRigOf_rigMk : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] G.RigExt), c.IsLawOf μ → (∀ s w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n s) → (∀ n, u.1 n = ∑ i, w i • dUnit k (c.x n i)) → ρ (s, w) = G.rigMk (z, u)) → IsRigOf μ ρ := by
  intro p k _ d G c μ ρ hμ hρ
  have hcoc := GlobalTheory.T.isSymmetricFormalGroupCocycle_iff_mem_cocycles p k d G c μ hμ
  have hdu := GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k d
  have hlaw := ((GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k d G c).2 μ hμ).2
  have hom := GlobalTheory.T.invariantDifferentials_connectedPDivGroup_coordinates p k d G c
  have hone := GlobalTheory.T.functions_eq_series_in_chart p k d G c
  have hpres := (GlobalTheory.T.chart_square_coordinates_present_levels p k d G c).2
  constructor
  · intro v
    obtain ⟨⟨z, u⟩, rfl⟩ := Submodule.mkQ_surjective _ v
    obtain ⟨s, hs, -⟩ := hpres z.1 (fun n => (z.2 n).2)
    obtain ⟨w, hw, -⟩ := hom.2 u
    have hz : (fun n => c.ev₂ n s) = z.1 := funext hs
    refine ⟨s, w, (hcoc s).2 (hz ▸ z.2), ?_⟩
    exact hρ s w z u (fun n => (hs n).symm) hw
  · intro s w hs
    let z : G.cocycles := ⟨fun n => c.ev₂ n s, (hcoc s).1 hs⟩
    let u : G.omega := ⟨fun n => ∑ i, w i • dUnit k (c.x n i), hom.1 w⟩
    rw [hρ s w z u (fun _ => rfl) (fun _ => rfl)]
    change Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
    constructor
    · rintro ⟨B, hB⟩
      rw [LinearMap.prod_apply, Prod.mk.injEq] at hB
      obtain ⟨b, hb, -⟩ := hone.2.2 B.1 B.2
      refine ⟨b, ?_, ?_⟩
      · have hz2 : ∀ n, pullbackTwo (G.res n) (c.ev₂ (n + 1) s) = c.ev₂ n s := fun n => hone.2.1 n s
        obtain ⟨t, -, ht⟩ := hpres (fun n => c.ev₂ n s) hz2
        have h1 := ht s (fun _ => rfl)
        have h2 := ht (cob1 μ b) (fun n => by
          rw [(hlaw n b).2, hb n]
          exact (congrArg (fun y : G.cocycles => y.1 n) hB.1))
        exact h1.trans h2.symm
      · obtain ⟨w', -, hw'⟩ := hom.2 u
        have e1 := hw' w (fun _ => rfl)
        have e2 := hw' (lin b) (fun n => by
          rw [← (hdu (G.A n) (c.x n) (c.nil n) (c.aug n) b).2]
          change _ = dUnit k (c.ev n b)
          rw [hb n]
          exact (congrArg (fun y : G.omega => y.1 n) hB.2).symm)
        exact e1.trans e2.symm
    · rintro ⟨b, rfl, rfl⟩
      refine ⟨⟨fun n => c.ev n b, fun n => hone.1 n b⟩, ?_⟩
      rw [LinearMap.prod_apply, Prod.mk.injEq]
      constructor
      · apply Subtype.ext; funext n
        exact ((hlaw n b).2).symm
      · apply Subtype.ext; funext n
        exact (hdu (G.A n) (c.x n) (c.nil n) (c.aug n) b).2

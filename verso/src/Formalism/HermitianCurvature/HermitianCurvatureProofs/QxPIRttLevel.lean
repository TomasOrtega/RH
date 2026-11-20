import Formalism.HermitianCurvature.StatementQ
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormLevel.Imports

/- English proof (translation)
Introduce `hU hLT hGI hFF _ k r i`. Proceed by induction on `i using Fin.cases with`. Consider the case `succ l => exact hU k r l`. Consider the case `zero`. Introduce `Wp Wq _ _ _ _ z z' π π' D hz hz' hD J hJ g hg u v a b c d`.

Take `⟨π₁, π₁', D₁, f, hw, hw', hD₁, hf, hfJ⟩` from `hFF Wp Wq k r z z' π π' D hz hz' hD J hJ`. Establish `key : ∀ (Y Y' : ℂ) (p q p' q' : Fin 2), Formalism.FourierDecayAlt.Q.tL k (1 + r) (Formalism.QuantumDeterminants.liftVec k 1 r z) (Formalism.QuantumDeterminants.liftVec k 1 r z') ⟨1, by omega⟩ Y p q (Formalism.FourierDecayAlt.Q.tL k (1 + r) (Formalism.QuantumDeterminants.liftVec k …`. Introduce `Y Y' p q p' q'`. Rewrite using `[hLT (Wq →L[ℂ] Wp) k 1 r z z' Y p q _ g hg.1.1]`. Use `(Formalism.FourierDecayAlt.P.Qx2.ll_tL (i := 0) hD.1 z z' Y p q).loc _ _ ?_ g hg` and prove the remaining obligations.

Introduce `x hx`. Rewrite using `[hLT (Wq →L[ℂ] Wp) k 1 r z z' Y' p' q' f x hx.1.1]`. Use `(Formalism.FourierDecayAlt.P.Qx2.ll_tL (i := 0) hD.1 z z' Y' p' q').loc _ _ ?_ x hx` and prove the remaining obligations. Introduce `y hy`. Conclude with `(hfJ y hy.1.1).2`.

Establish `hιg : Formalism.QuantumDeterminants.ιLev k 1 r g ∈ Formalism.FourierDecayAlt.Q.Glev k (1 + r) ⟨1, by omega⟩ ∩ D₁`. Use `⟨?_, (hfJ g hg.1.1).1.mpr hg.2⟩` and prove the remaining obligations. Rewrite using `[hGI k 1 r]`. Conclude with `⟨g, hg.1.1, rfl⟩`. Establish `h1 : Formalism.FourierDecayAlt.Q.RTTAt k (1 + r) ⟨1, by omega⟩` using `hU k (1 + r) ⟨0, by omega⟩`.

Establish `h` using `h1 Wp Wq _ _ π₁ π₁' D₁ hw hw' hD₁ f hf _ hιg u v a b c d`. Simplify using `only [key] at h`. Conclude with `h`.
-/
theorem Formalism.FourierDecayAlt.P.rtt_level_from_upper : Formalism.FourierDecayAlt.Q.RTTLevelFromUpper := by
  intro hU hLT hGI hFF _ k r i
  induction i using Fin.cases with
  | succ l => exact hU k r l
  | zero =>
    intro Wp Wq _ _ _ _ z z' π π' D hz hz' hD J hJ g hg u v a b c d
    obtain ⟨π₁, π₁', D₁, f, hw, hw', hD₁, hf, hfJ⟩ := hFF Wp Wq k r z z' π π' D hz hz' hD J hJ
    have key : ∀ (Y Y' : ℂ) (p q p' q' : Fin 2),
        Formalism.FourierDecayAlt.Q.tL k (1 + r) (Formalism.QuantumDeterminants.liftVec k 1 r z) (Formalism.QuantumDeterminants.liftVec k 1 r z') ⟨1, by omega⟩
                  Y p q (Formalism.FourierDecayAlt.Q.tL k (1 + r) (Formalism.QuantumDeterminants.liftVec k 1 r z) (Formalism.QuantumDeterminants.liftVec k 1 r z')
                    ⟨1, by omega⟩ Y' p' q' f) (Formalism.QuantumDeterminants.ιLev k 1 r g) =
          Formalism.FourierDecayAlt.Q.tL k r z z' 0 Y p q (Formalism.FourierDecayAlt.Q.tL k r z z' 0 Y' p' q' J) g := by
      intro Y Y' p q p' q'
      rw [hLT (Wq →L[ℂ] Wp) k 1 r z z' Y p q _ g hg.1.1]
      refine (Formalism.FourierDecayAlt.P.Qx2.ll_tL (i := 0) hD.1 z z' Y p q).loc _ _ ?_ g hg
      intro x hx
      rw [hLT (Wq →L[ℂ] Wp) k 1 r z z' Y' p' q' f x hx.1.1]
      refine (Formalism.FourierDecayAlt.P.Qx2.ll_tL (i := 0) hD.1 z z' Y' p' q').loc _ _ ?_ x hx
      intro y hy
      exact (hfJ y hy.1.1).2
    have hιg : Formalism.QuantumDeterminants.ιLev k 1 r g ∈ Formalism.FourierDecayAlt.Q.Glev k (1 + r) ⟨1, by omega⟩ ∩ D₁ := by
      refine ⟨?_, (hfJ g hg.1.1).1.mpr hg.2⟩
      rw [hGI k 1 r]
      exact ⟨g, hg.1.1, rfl⟩
    have h1 : Formalism.FourierDecayAlt.Q.RTTAt k (1 + r) ⟨1, by omega⟩ := hU k (1 + r) ⟨0, by omega⟩
    have h := h1 Wp Wq _ _ π₁ π₁' D₁ hw hw' hD₁ f hf _ hιg u v a b c d
    simp only [key] at h
    exact h

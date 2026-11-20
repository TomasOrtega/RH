import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoNuFin

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal

def DetAdm : Prop := InCtx fun F E _ _ _ _ _ _σ M _J a _X0 _hT =>
  ∀ ν1 ν2 : Measure (Fin a → Fin M → AF F ⊗[F] E),
    (∀ K, IsCompact K → ν1 K < ⊤) → (∀ K, IsCompact K → ν2 K < ⊤) →
    (∀ Φ, IsAdm F E Φ → ∫ X, Φ X ∂ν1 = ∫ X, Φ X ∂ν2) → ν1 = ν2

def OmUniq : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ ν1 ν2, IsOmT F E σ M J ψ (gramE σ J X0) hT ν1 →
    IsOmT F E σ M J ψ (gramE σ J X0) hT ν2 → ν1 = ν2

def OmInv : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
    ∀ g : HA (AF F) σ J, IsOmT F E σ M J ψ (gramE σ J X0) hT (νX.map fun y => g • y)

/- English proof (translation)
Establish `hm : ∀ A : Matrix (Fin M) (Fin M) (AF F ⊗[F] E), Continuous fun y : Fin a → Fin M → AF F ⊗[F] E => fun i => A.mulVec (y i)` using `fun A => continuous_pi fun i => continuous_const.matrix_mulVec (continuous_apply i)`. Use `first`. Consider the case `exact hm _`. Consider the case `exact hm ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) _)`.
-/
theorem continuous_smul_tup {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : HA (AF F) σ J) :
    Continuous (fun y : Fin a → Fin M → AF F ⊗[F] E => g • y) := by

  have hm : ∀ A : Matrix (Fin M) (Fin M) (AF F ⊗[F] E),
      Continuous fun y : Fin a → Fin M → AF F ⊗[F] E => fun i => A.mulVec (y i) := fun A =>
    continuous_pi fun i => continuous_const.matrix_mulVec (continuous_apply i)
  first
  | exact hm _
  | exact hm ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) _)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ h1 h2 a ha haM X0 hT hdet ψ hψ νX hν g s hs`. Use `haveI : FiniteDimensional F E := by first`. Consider the case `infer_instance`. Consider the case `exact Module.Finite.of_restrictScalars_finite ℚ F E`. Consider the case `exact FiniteDimensional.right ℚ F E`.

Establish `hm : Measurable (fun y : Fin a → Fin M → AF F ⊗[F] E => g • y)` using `(continuous_smul_tup σ J g).measurable`. Establish `heq` using `hU F E σ hCM M J hJ h1 h2 a ha haM X0 hT hdet ψ hψ _ _ (hI F E σ hCM M J hJ h1 h2 a ha haM X0 hT hdet ψ hψ νX hν g) hν`. Rewrite using `[← Measure.map_apply hm hs, heq]`.
-/
theorem nuInv_of (hU : OmUniq) (hI : OmInv) : NuInv := by

  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a ha haM X0 hT hdet ψ hψ νX hν g s hs
  haveI : FiniteDimensional F E := by
    first
    | infer_instance
    | exact Module.Finite.of_restrictScalars_finite ℚ F E
    | exact FiniteDimensional.right ℚ F E
  have hm : Measurable (fun y : Fin a → Fin M → AF F ⊗[F] E => g • y) :=
    (continuous_smul_tup σ J g).measurable
  have heq := hU F E σ hCM M J hJ h1 h2 a ha haM X0 hT hdet ψ hψ _ _
    (hI F E σ hCM M J hJ h1 h2 a ha haM X0 hT hdet ψ hψ νX hν g) hν
  rw [← Measure.map_apply hm hs, heq]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ h1 h2 a ha haM X0 hT hdet ψ hψ ν1 ν2 hν1 hν2`. Use `haveI : FiniteDimensional F E := by first`. Consider the case `infer_instance`. Consider the case `exact Module.Finite.of_restrictScalars_finite ℚ F E`. Consider the case `exact FiniteDimensional.right ℚ F E`.

Use `hD F E σ hCM M J hJ h1 h2 a ha haM X0 hT hdet ν1 ν2 (fun K hK => nuFin_gen σ J _ hT ψ ν1 hν1 K hK) (fun K hK => nuFin_gen σ J _ hT ψ ν2 hν2 K hK) ?_` and prove the remaining obligations. Introduce and unpack `Φ ⟨d, b, Φinf, Φf, Φv, hc, hcs, hpure, hprod⟩`. Take `⟨-, ⟨μinf, hμinf⟩, A1⟩` from `hν1`. Take `⟨-, -, A2⟩` from `hν2`. Take `⟨⟨νinf, hνinf⟩, B1⟩` from `A1 μinf hμinf`.

Take `⟨-, B2⟩` from `A2 μinf hμinf`. Take `⟨⟨μv, hμv⟩, C1⟩` from `B1 νinf hνinf`. Take `⟨-, C2⟩` from `B2 νinf hνinf`. Take `⟨⟨νv, hνv⟩, D1⟩` from `C1 μv hμv`. Take `⟨-, D2⟩` from `C2 μv hμv`.

Take `⟨⟨fi, hfi⟩, E1⟩` from `D1 νv hνv`. Take `⟨-, E2⟩` from `D2 νv hνv`. Take `⟨⟨fv, hfv⟩, G1⟩` from `E1 fi hfi`. Take `⟨-, G2⟩` from `E2 fi hfi`. Take `⟨-, -, H1⟩` from `G1 fv hfv d b Φ Φinf Φf Φv hc hcs hpure hprod`.

Take `⟨-, -, H2⟩` from `G2 fv hfv d b Φ Φinf Φf Φv hc hcs hpure hprod`. Rewrite using `[H1, H2]`.
-/
theorem omUniq_of (hD : DetAdm) : OmUniq := by

  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a ha haM X0 hT hdet ψ hψ ν1 ν2 hν1 hν2
  haveI : FiniteDimensional F E := by
    first
    | infer_instance
    | exact Module.Finite.of_restrictScalars_finite ℚ F E
    | exact FiniteDimensional.right ℚ F E
  refine hD F E σ hCM M J hJ h1 h2 a ha haM X0 hT hdet ν1 ν2
    (fun K hK => nuFin_gen σ J _ hT ψ ν1 hν1 K hK) (fun K hK => nuFin_gen σ J _ hT ψ ν2 hν2 K hK) ?_
  rintro Φ ⟨d, b, Φinf, Φf, Φv, hc, hcs, hpure, hprod⟩
  obtain ⟨-, ⟨μinf, hμinf⟩, A1⟩ := hν1
  obtain ⟨-, -, A2⟩ := hν2
  obtain ⟨⟨νinf, hνinf⟩, B1⟩ := A1 μinf hμinf
  obtain ⟨-, B2⟩ := A2 μinf hμinf
  obtain ⟨⟨μv, hμv⟩, C1⟩ := B1 νinf hνinf
  obtain ⟨-, C2⟩ := B2 νinf hνinf
  obtain ⟨⟨νv, hνv⟩, D1⟩ := C1 μv hμv
  obtain ⟨-, D2⟩ := C2 μv hμv
  obtain ⟨⟨fi, hfi⟩, E1⟩ := D1 νv hνv
  obtain ⟨-, E2⟩ := D2 νv hνv
  obtain ⟨⟨fv, hfv⟩, G1⟩ := E1 fi hfi
  obtain ⟨-, G2⟩ := E2 fi hfi
  obtain ⟨-, -, H1⟩ := G1 fv hfv d b Φ Φinf Φf Φv hc hcs hpure hprod
  obtain ⟨-, -, H2⟩ := G2 fv hfv d b Φ Φinf Φf Φv hc hcs hpure hprod
  rw [H1, H2]

end PI.VolStabS

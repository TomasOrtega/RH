import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDetEqOne

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen GLnLocal

/- English proof (translation)
Introduce `F _ _ _ _ n _ _ μ _ z h g`. Establish `hf : ∀ (g k : GL (Fin n) F), k ∈ integralGL F n → zonalSpherical μ z (g * k) = zonalSpherical μ z g` using `fun g k hk => zonalSpherical_mul_right z g hk`. Establish `hpos : (0 : ℝ) < μ.real ↑(integralGL F n)` using `HeckeAlgebra.measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)`. Establish `hne : ((μ.real ↑(integralGL F n) : ℝ) : ℂ) ≠ 0`. Conclude with `hpos.ne'` after adjusting the coercions.

Establish `hmin : ∀ r, minusculeHecke μ r ∈ eigenSubalgebra μ z (zonalSpherical μ z) hf`. Introduce `r y`. Rewrite using `[integral_minusculeHecke_mul hf y r, sum_zonalSpherical_gMat z r y]`. Clear the denominators using the available nonvanishing facts. Establish `htop : eigenSubalgebra μ z (zonalSpherical μ z) hf = ⊤` using `eigenSubalgebra_eq_top z hf (fun r _ => hmin r) (GlobalTheory.HenQ.ShellOp.central_mem_of_top z hf (hmin n))`.

Establish `hmem : h ∈ eigenSubalgebra μ z (zonalSpherical μ z) hf`. Rewrite using `[htop]`. Conclude with `Algebra.mem_top`. Conclude with `hmem g`.
-/
theorem UpperTheory.Gal.Gen.gammaEig_pf :
    UpperTheory.Gal.Gen.GammaEig := by
  intro F _ _ _ _ n _ _ μ _ z h g
  have hf : ∀ (g k : GL (Fin n) F), k ∈ integralGL F n →
      zonalSpherical μ z (g * k) = zonalSpherical μ z g :=
    fun g k hk => zonalSpherical_mul_right z g hk
  have hpos : (0 : ℝ) < μ.real ↑(integralGL F n) :=
    HeckeAlgebra.measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)
  have hne : ((μ.real ↑(integralGL F n) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  have hmin : ∀ r, minusculeHecke μ r ∈ eigenSubalgebra μ z (zonalSpherical μ z) hf := by
    intro r y
    rw [integral_minusculeHecke_mul hf y r, sum_zonalSpherical_gMat z r y]
    field_simp
  have htop : eigenSubalgebra μ z (zonalSpherical μ z) hf = ⊤ :=
    eigenSubalgebra_eq_top z hf (fun r _ => hmin r)
      (GlobalTheory.HenQ.ShellOp.central_mem_of_top z hf (hmin n))
  have hmem : h ∈ eigenSubalgebra μ z (zonalSpherical μ z) hf := by
    rw [htop]
    exact Algebra.mem_top
  exact hmem g

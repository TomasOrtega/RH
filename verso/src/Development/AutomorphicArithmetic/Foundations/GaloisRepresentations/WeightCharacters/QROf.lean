import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaUnitaryUpperTriangularStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

/- English proof (translation)
Introduce `a y`. Take `⟨k, hk, b, hg, hb⟩` from `GlobalTheory.T.iwasawa_unitary_upper_triangular (y : Matrix (Fin a) (Fin a) ℂ) y.isUnit`. Set `u : Matrix.unitaryGroup (Fin a) ℂ` to `⟨k, hk⟩`. Establish `hu : ((unitaryIncl a u : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) = k` using `rfl`. Use `⟨u, (unitaryIncl a u)⁻¹ * y, ?_, (mul_inv_cancel_left _ _).symm⟩` and prove the remaining obligations.

Establish `hbm : (((unitaryIncl a u)⁻¹ * y : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) = b`. Rewrite using `[Units.val_mul, hg, ← hu, ← mul_assoc, Units.inv_mul, one_mul]`. Introduce `i j hij`. Rewrite using `[hbm]`. Conclude with `hb hij`.
-/
theorem UpperTheory.Gal.Wt.qR_of :
    UpperTheory.Gal.Wt.QR := by
  intro a y
  obtain ⟨k, hk, b, hg, hb⟩ := GlobalTheory.T.iwasawa_unitary_upper_triangular (y : Matrix (Fin a) (Fin a) ℂ) y.isUnit
  let u : Matrix.unitaryGroup (Fin a) ℂ := ⟨k, hk⟩
  have hu : ((unitaryIncl a u : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) = k := rfl
  refine ⟨u, (unitaryIncl a u)⁻¹ * y, ?_, (mul_inv_cancel_left _ _).symm⟩
  have hbm : (((unitaryIncl a u)⁻¹ * y : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) = b := by
    rw [Units.val_mul, hg, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
  intro i j hij
  rw [hbm]
  exact hb hij

import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericScale
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSstAtOfIsCrysAt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `l _ P AI hT K LL`. Take `⟨T⟩` from `hT`. Use `⟨?_, fun f g => ?_⟩` and prove the remaining obligations. Introduce `U _ _ _ _ _ ρ`. Rewrite using `[dinv_σSt]`.

Use `haveI := LL.2`. Use `haveI : FiniteDimensional ℚ_[l] U := Module.Finite.trans ↥LL.1 U`. Take `⟨hfin, hb⟩` from `GlobalTheory.CrysSst.finrank_Dst_le P AI T (GlobalTheory.PstCoeff.resQ ρ)`. Establish `hD : Dst P (GlobalTheory.PstCoeff.resQ ρ) = (Dst P ρ).restrictScalars ℚ_[l]`. Use extensionality with `x`.

Simplify using `[mem_Dst, GlobalTheory.PstCoeff.stRep_resQ]`. Establish `e : finrank ℚ_[l] ↥(Dst P (GlobalTheory.PstCoeff.resQ ρ)) = finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 ↥(Dst P ρ)`. Rewrite using `[hD, finrank_mul_finrank]`. Both sides reduce to the same expression. Establish `hfin' : FiniteDimensional ℚ_[l] ↥((Dst P ρ).restrictScalars ℚ_[l])` using `hD ▸ hfin`.

Use `haveI : Module.Finite ℚ_[l] ↥(Dst P ρ) := hfin'`. Use `haveI hL : FiniteDimensional ↥LL.1 ↥(Dst P ρ) := Module.Finite.of_restrictScalars_finite ℚ_[l] ↥LL.1 ↥(Dst P ρ)`. Use `⟨hL, ?_⟩` and prove the remaining obligations. Establish `hV : finrank ℚ_[l] U = finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 U` using `(finrank_mul_finrank ℚ_[l] ↥LL.1 U).symm`. Rewrite `hb` using `[e, hV]`.

Use `Nat.le_of_mul_le_mul_left ?_ (finrank_pos (R := ℚ_[l]) (M := ↥LL.1))` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `Commute.pow_right ?_ f` and prove the remaining obligations. Conclude with `LinearMap.ext fun p => (phiSt_actSt P (g : GQ l) p).symm`.
-/
theorem UpperTheory.Gal.crystallineComparison.boundSt_of :
    BoundSt := by
  intro l _ P AI hT K LL
  obtain ⟨T⟩ := hT
  refine ⟨?_, fun f g => ?_⟩
  · intro U _ _ _ _ _ ρ
    rw [dinv_σSt]
    haveI := LL.2
    haveI : FiniteDimensional ℚ_[l] U := Module.Finite.trans ↥LL.1 U
    obtain ⟨hfin, hb⟩ := GlobalTheory.CrysSst.finrank_Dst_le P AI T (GlobalTheory.PstCoeff.resQ ρ)
    have hD : Dst P (GlobalTheory.PstCoeff.resQ ρ) = (Dst P ρ).restrictScalars ℚ_[l] := by
      ext x
      simp [mem_Dst, GlobalTheory.PstCoeff.stRep_resQ]
    have e : finrank ℚ_[l] ↥(Dst P (GlobalTheory.PstCoeff.resQ ρ)) =
        finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 ↥(Dst P ρ) := by
      rw [hD, finrank_mul_finrank]
      rfl
    have hfin' : FiniteDimensional ℚ_[l] ↥((Dst P ρ).restrictScalars ℚ_[l]) := hD ▸ hfin
    haveI : Module.Finite ℚ_[l] ↥(Dst P ρ) := hfin'
    haveI hL : FiniteDimensional ↥LL.1 ↥(Dst P ρ) :=
      Module.Finite.of_restrictScalars_finite ℚ_[l] ↥LL.1 ↥(Dst P ρ)
    refine ⟨hL, ?_⟩
    have hV : finrank ℚ_[l] U = finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 U :=
      (finrank_mul_finrank ℚ_[l] ↥LL.1 U).symm
    rw [e, hV] at hb
    refine Nat.le_of_mul_le_mul_left ?_ (finrank_pos (R := ℚ_[l]) (M := ↥LL.1))
    calc finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 ↥(Dst P ρ)
        ≤ finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 U * finrank ℚ_[l] ↥(K0 K) := hb
      _ = finrank ℚ_[l] ↥LL.1 * (finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 U) := by ring
  · refine Commute.pow_right ?_ f
    exact LinearMap.ext fun p => (phiSt_actSt P (g : GQ l) p).symm

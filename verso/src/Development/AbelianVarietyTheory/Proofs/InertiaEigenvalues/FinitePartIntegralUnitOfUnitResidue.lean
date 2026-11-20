import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExportSeries

/- English proof (translation)
Introduce `D ι h1 h2 P e he x hxe hx v hv`. Establish `hun : GlobalTheory.GeoLevel.unswap D (toEAf D (x : AE D)) = finPart D (x : AE D)` using `GlobalTheory.GeoLevel.unswap_swap (finPart D (x : AE D))`. Establish `hy : ∀ P' : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (x : AE D)) P') = 1`. Introduce `P'`. Distinguish the cases in `hP : P' = P`.

Substitute `hP` using the available equality. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective (v : kP P')`. Establish `hna : a ∉ P'.asIdeal` using `fun h => v.ne_zero (by rw [← ha]; exact Ideal.Quotient.eq_zero_iff_mem.2 h)`. Establish `h4` using `GlobalTheory.GeoLevel.valued_sub_le ι h1 h2 P' ⟨_, hx⟩ a (hv.trans ha.symm)`. Establish `h5 : Valued.v (algebraMap D.host.E (P'.adicCompletion D.host.E) (a : D.host.E)) = 1`.

Rewrite using `[GlobalTheory.GeoLevel.valued_coe_int]`. Conclude with `HeightOneSpectrum.intValuation_eq_one_iff.2 hna`. Establish `h6 : Valued.v (ι (finPart D (x : AE D)) P' - algebraMap D.host.E (P'.adicCompletion D.host.E) (a : D.host.E)) ≤ WithZero.exp (-1 : ℤ)`. Rewrite using `[← hun]`. Conclude with `h4`.

Rewrite using `[← h5]`. Use `Valuation.map_eq_of_sub_lt _ (h6.trans_lt ?_)` and prove the remaining obligations. Rewrite using `[h5, ← WithZero.exp_zero]`. Conclude with `WithZero.exp_lt_exp.2 (by norm_num)`. Set `ev : FiniteAdeleRing (𝓞 D.host.E) D.host.E →+* P'.adicCompletion D.host.E` to `RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 D.host.E) => v.adicCompletion D.host.E) P'`.

Establish `h0 : ev (ι (finPart D e)) = 0` using `he P' hP`. Establish `h3` using `congrArg (fun z => ev (ι (finPart D z))) hxe`. Simplify using `only [map_mul, map_sub, map_one, h0, sub_zero, one_mul] at h3`. Establish `h4 : ι (finPart D (x : AE D)) P' = 1` using `h3`. Rewrite using `[h4, map_one]`.

Use `⟨(h2 _).2 fun P' => (hy P').le, (h2 _).2 fun P' => ?_⟩` and prove the remaining obligations. Establish `e1 : ι (finPart D (x : AE D)) * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) = 1`. Rewrite using `[← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]`. Establish `e2 : ι (finPart D (x : AE D)) P' * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P' = 1` using `congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z P') e1`. Establish `e3` using `congrArg (Valued.v : P'.adicCompletion D.host.E → _) e2`.

Rewrite `e3` using `[map_mul, map_one, hy P', one_mul]`. Conclude with `e3.le`.
-/
theorem finPart_mem_intAE_of_unit_residue : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ k : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] k) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) k) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → ∀ (P : Pl D.host.E) (e : AE D), (∀ P' : Pl D.host.E, P' ≠ P → ι (finPart D e) P' = 0) → ∀ (x : (AE D)ˣ), (1 - e) * (x : AE D) = 1 - e → ∀ (hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (v : (kP P)ˣ), resS D.host.F P ⟨_, hx⟩ = v → finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D := by
  intro D ι h1 h2 P e he x hxe hx v hv
  have hun : GlobalTheory.GeoLevel.unswap D (toEAf D (x : AE D)) = finPart D (x : AE D) :=
    GlobalTheory.GeoLevel.unswap_swap (finPart D (x : AE D))
  have hy : ∀ P' : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (x : AE D)) P') = 1 := by
    intro P'
    by_cases hP : P' = P
    · subst hP
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (v : kP P')
      have hna : a ∉ P'.asIdeal := fun h => v.ne_zero (by rw [← ha]; exact Ideal.Quotient.eq_zero_iff_mem.2 h)
      have h4 := GlobalTheory.GeoLevel.valued_sub_le ι h1 h2 P' ⟨_, hx⟩ a (hv.trans ha.symm)
      have h5 : Valued.v (algebraMap D.host.E (P'.adicCompletion D.host.E) (a : D.host.E)) = 1 := by
        rw [GlobalTheory.GeoLevel.valued_coe_int]
        exact HeightOneSpectrum.intValuation_eq_one_iff.2 hna
      have h6 : Valued.v (ι (finPart D (x : AE D)) P' -
          algebraMap D.host.E (P'.adicCompletion D.host.E) (a : D.host.E)) ≤ WithZero.exp (-1 : ℤ) := by
        rw [← hun]; exact h4
      rw [← h5]
      refine Valuation.map_eq_of_sub_lt _ (h6.trans_lt ?_)
      rw [h5, ← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.2 (by norm_num)
    · let ev : FiniteAdeleRing (𝓞 D.host.E) D.host.E →+* P'.adicCompletion D.host.E :=
        RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 D.host.E) => v.adicCompletion D.host.E) P'
      have h0 : ev (ι (finPart D e)) = 0 := he P' hP
      have h3 := congrArg (fun z => ev (ι (finPart D z))) hxe
      simp only [map_mul, map_sub, map_one, h0, sub_zero, one_mul] at h3
      have h4 : ι (finPart D (x : AE D)) P' = 1 := h3
      rw [h4, map_one]
  refine ⟨(h2 _).2 fun P' => (hy P').le, (h2 _).2 fun P' => ?_⟩
  have e1 : ι (finPart D (x : AE D)) * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have e2 : ι (finPart D (x : AE D)) P' * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P' = 1 :=
    congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z P') e1
  have e3 := congrArg (Valued.v : P'.adicCompletion D.host.E → _) e2
  rw [map_mul, map_one, hy P', one_mul] at e3
  exact e3.le

end GlobalTheory.ExportSeries

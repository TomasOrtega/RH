import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormOneIdeleOrderOneTrivialElsewhere
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HeckeLocalProduct.PvLocalSelf
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.HeckeFinVal

open Neutral.B1 Formalism.L2.Host PI.HeckeProdW

/- English proof (translation)
The claim follows from `Units.ext (Prod.ext (funext fun w => h1 w) (Subtype.ext (funext fun v => h2 v)))`.
-/
theorem idele_ext {L : Type} [Field L] [NumberField L] {a c : Ideles L}
    (h1 : ∀ w, pw w a = pw w c) (h2 : ∀ v, pv v a = pv v c) : a = c :=
  Units.ext (Prod.ext (funext fun w => h1 w) (Subtype.ext (funext fun v => h2 v)))

/- English proof (translation)
Establish `hx0 : Valued.v (x : P.adicCompletion L) ≠ 0` using `by simp`. Use `set m : ℤ := WithZero.log (Valued.v (x : P.adicCompletion L)) with hm`. Establish `hxm : Valued.v (x : P.adicCompletion L) = WithZero.exp m` using `(WithZero.exp_log hx0).symm`. Use `set ϖ : (P.adicCompletion L)ˣ := atFin P (unif P) with hϖ`. Establish `hϖv : Valued.v (ϖ : P.adicCompletion L) = WithZero.exp (-1 : ℤ)` using `unif_spec P`.

Use `⟨-m, ?_⟩` and prove the remaining obligations. Establish `hu : IsUnitAt P (x * ϖ ^ m)`. Unfold `IsUnitAt`. Rewrite using `[Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hxm, hϖv, ← WithZero.exp_zsmul, ← WithZero.exp_add]`. Simplify using the standard rewrite rules.

Establish `h3` using `hP _ hu`. Rewrite `h3` using `[map_mul, map_zpow, mul_eq_one_iff_eq_inv, ← zpow_neg]`. Conclude with `h3`.
-/
theorem loc_eq_val_zpow {L : Type} [Field L] [NumberField L] (χ : HChar L) (P : HeightOneSpectrum (𝓞 L))
    (hP : χ.UnrAt P) (x : (P.adicCompletion L)ˣ) : ∃ k : ℤ, χ.loc P x = χ.val P ^ k := by
  have hx0 : Valued.v (x : P.adicCompletion L) ≠ 0 := by simp
  set m : ℤ := WithZero.log (Valued.v (x : P.adicCompletion L)) with hm
  have hxm : Valued.v (x : P.adicCompletion L) = WithZero.exp m := (WithZero.exp_log hx0).symm
  set ϖ : (P.adicCompletion L)ˣ := atFin P (unif P) with hϖ
  have hϖv : Valued.v (ϖ : P.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec P
  refine ⟨-m, ?_⟩
  have hu : IsUnitAt P (x * ϖ ^ m) := by
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hxm, hϖv, ← WithZero.exp_zsmul,
      ← WithZero.exp_add]
    simp
  have h3 := hP _ hu
  rw [map_mul, map_zpow, mul_eq_one_iff_eq_inv, ← zpow_neg] at h3
  exact h3

/- English proof (translation)
Introduce `L _ _ χ T b hb hout hunr`. Set `u : ∀ P : HeightOneSpectrum (𝓞 L), (P.adicCompletion L)ˣ` to `fun P => ⟨pv P b, pv P b⁻¹, by rw [← map_mul, mul_inv_cancel, map_one], by rw [← map_mul, inv_mul_cancel, map_one]⟩`. Establish `hdec : b = ∏ P ∈ T, localIdele L P (u P)`. Use `idele_ext (fun w => ?_) (fun v => ?_)` and prove the remaining obligations. Rewrite using `[map_prod]`.

Rewrite using `[Finset.prod_eq_one fun P _ => pw_local w P (u P)]`. Conclude with `hb w`. Rewrite using `[map_prod]`. Distinguish the cases in `hv : v ∈ T`. Rewrite using `[Finset.prod_eq_single v]`.

Rewrite using `[pv_local_self]`. Introduce `P _ hPv`. Conclude with `pv_local_ne P v (Ne.symm hPv) _`. Introduce `h`. Conclude with `absurd hv h`.

Rewrite using `[Finset.prod_eq_one fun P hP => pv_local_ne P v (fun e => hv (e ▸ hP)) _]`. Conclude with `hout v hv`. Establish `hk : ∀ P ∈ T, ∃ k : ℤ, χ.loc P (u P) = χ.val P ^ k` using `fun P hP => loc_eq_val_zpow χ P (hunr P hP) (u P)`. Use `choose! n hn using hk`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Rewrite using `[hdec, map_prod]`. Conclude with `Finset.prod_congr rfl fun P hP => hn P hP`.
-/
theorem eq_prod_val_zpow : ∀ {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (b : Neutral.B1.Ideles L), Formalism.L2.Host.IsFinIdele b → (∀ P, P ∉ T → (b : AdeleRing (𝓞 L) L).2 P = 1) →
    (∀ P ∈ T, χ.UnrAt P) → ∃ n : HeightOneSpectrum (𝓞 L) → ℤ, χ.1 b = ∏ P ∈ T, χ.val P ^ n P := by
  intro L _ _ χ T b hb hout hunr
  classical
  let u : ∀ P : HeightOneSpectrum (𝓞 L), (P.adicCompletion L)ˣ := fun P =>
    ⟨pv P b, pv P b⁻¹, by rw [← map_mul, mul_inv_cancel, map_one], by rw [← map_mul, inv_mul_cancel, map_one]⟩
  have hdec : b = ∏ P ∈ T, localIdele L P (u P) := by
    refine idele_ext (fun w => ?_) (fun v => ?_)
    · rw [map_prod]
      rw [Finset.prod_eq_one fun P _ => pw_local w P (u P)]
      exact hb w
    · rw [map_prod]
      by_cases hv : v ∈ T
      · rw [Finset.prod_eq_single v]
        · rw [pv_local_self]
        · intro P _ hPv
          exact pv_local_ne P v (Ne.symm hPv) _
        · intro h; exact absurd hv h
      · rw [Finset.prod_eq_one fun P hP => pv_local_ne P v (fun e => hv (e ▸ hP)) _]
        exact hout v hv
  have hk : ∀ P ∈ T, ∃ k : ℤ, χ.loc P (u P) = χ.val P ^ k := fun P hP => loc_eq_val_zpow χ P (hunr P hP) (u P)
  choose! n hn using hk
  refine ⟨n, ?_⟩
  rw [hdec, map_prod]
  exact Finset.prod_congr rfl fun P hP => hn P hP

end GlobalTheory.HeckeFinVal

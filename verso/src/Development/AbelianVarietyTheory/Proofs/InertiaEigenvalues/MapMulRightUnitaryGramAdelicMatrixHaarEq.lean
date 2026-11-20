import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapPiEqOfMapAddHaarEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsHermNDInvTranspose
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

/- English proof (translation)
Introduce `D N m K hK hdet g μ hμ`. Take `⟨h1, h2, h3, h4, h5⟩` from `Formalism.IndefR.Eqv.ae_facts D`. Establish `hcm` using `GlobalTheory.Mem.VolExists.isCMExt D.sp.cm`. Set `A : Matrix (Fin N) (Fin N) (AE D)` to `(HA.mat (AF D.host.F) D.sp.cm.sig K g).1`. Set `φ : (Fin N → AE D) →+ (Fin N → AE D)` to `{ toFun := fun v => Matrix.vecMul v A map_zero' := Matrix.zero_vecMul A map_add' := fun a b => Matrix.add_vecMul A a b }`.

Establish `hφ : Continuous φ` using `continuous_id.matrix_vecMul continuous_const`. Conclude with `GlobalTheory.map_pi_eq_of_map_addHaar_eq (Fin N → AE D) φ hφ (fun ν hν => GlobalTheory.AdelicModulus.Row.map_vecMul_unitary _ _ D.sp.cm.sig hcm N K ⟨fun i j => hK i j, hdet⟩ g ν hν) m μ hμ`.
-/
theorem mul_unitary_map_haar : ∀ (D : D7) (N m : ℕ) (K : Matrix (Fin N) (Fin N) D.host.E), (∀ a b, D.sp.cm.sig (K b a) = K a b) → K.det ≠ 0 → ∀ (g : HA (AF D.host.F) D.sp.cm.sig K) (μ : Measure (Mx D m N)), μ.IsAddHaarMeasure → μ.map (fun x : Mx D m N => (HMul.hMul (x : Matrix (Fin m) (Fin N) (AE D)) ((HA.mat (AF D.host.F) D.sp.cm.sig K g).1 : Matrix (Fin N) (Fin N) (AE D)) : Mx D m N)) = μ := by
  intro D N m K hK hdet g μ hμ
  obtain ⟨h1, h2, h3, h4, h5⟩ := Formalism.IndefR.Eqv.ae_facts D
  have hcm := GlobalTheory.Mem.VolExists.isCMExt D.sp.cm
  let A : Matrix (Fin N) (Fin N) (AE D) := (HA.mat (AF D.host.F) D.sp.cm.sig K g).1
  let φ : (Fin N → AE D) →+ (Fin N → AE D) :=
    { toFun := fun v => Matrix.vecMul v A
      map_zero' := Matrix.zero_vecMul A
      map_add' := fun a b => Matrix.add_vecMul A a b }
  have hφ : Continuous φ := continuous_id.matrix_vecMul continuous_const
  exact GlobalTheory.map_pi_eq_of_map_addHaar_eq (Fin N → AE D) φ hφ
    (fun ν hν => GlobalTheory.AdelicModulus.Row.map_vecMul_unitary _ _ D.sp.cm.sig hcm N K ⟨fun i j => hK i j, hdet⟩ g ν hν) m μ hμ

end GlobalTheory

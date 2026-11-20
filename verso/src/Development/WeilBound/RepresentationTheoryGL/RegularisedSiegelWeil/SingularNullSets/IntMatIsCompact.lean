import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LBumpExA

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PositivityTheory.Rg.Rsw.L.LBumpEx

variable {D : D7}

/- English proof (translation)
Establish `e : {w : Matrix (Fin m) (Fin n) (AfE D) | ∀ i j, w i j ∈ intAE D} = ⋂ i, ⋂ j, (fun w : Matrix (Fin m) (Fin n) (AfE D) => w i j) ⁻¹' (intAE D : Set (AfE D))`. Use extensionality with `w`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i))`.
-/
theorem intMat_isOpen (m n : ℕ) :
    IsOpen {w : Matrix (Fin m) (Fin n) (AfE D) | ∀ i j, w i j ∈ intAE D} := by
  have e : {w : Matrix (Fin m) (Fin n) (AfE D) | ∀ i j, w i j ∈ intAE D} =
      ⋂ i, ⋂ j, (fun w : Matrix (Fin m) (Fin n) (AfE D) => w i j) ⁻¹' (intAE D : Set (AfE D)) := by
    ext w; simp
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i))

/- English proof (translation)
The claim follows from `isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => GlobalTheory.SchwartzBruhatTensor.isCompact_intAE D`.
-/
theorem intMat_isCompact (m n : ℕ) :
    IsCompact {w : Matrix (Fin m) (Fin n) (AfE D) | ∀ i j, w i j ∈ intAE D} :=
  isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => GlobalTheory.SchwartzBruhatTensor.isCompact_intAE D

/- English proof (translation)
Establish `: IsModuleTopology (Af D.host.F) (AfE D)` using `⟨rfl⟩`. Establish `: Module.Finite D.host.F D.host.E` using `Module.Finite.of_restrictScalars_finite ℚ _ _`. Establish `: IsTopologicalRing (AfE D)` using `IsModuleTopology.isTopologicalRing (Af D.host.F) _`. Use `AddSubgroup.isOpen_of_mem_nhds (U S ef N m n) (g := 0) ?_` and prove the remaining obligations. Use `Filter.mem_of_superset ((intMat_isOpen m n).mem_nhds fun i j => zero_mem _) fun w hw => ?_` and prove the remaining obligations.

Conclude with `⟨fun v _ i j => cf_mem_of_mem (hw i j) v, fun i j => GlobalTheory.HostAdeleIso.intAE_mul_mem D (GlobalTheory.IwaPlace.SdComap.natCast_mem_intAE N) (GlobalTheory.HostAdeleIso.intAE_mul_mem D hef (hw i j))⟩`.
-/
theorem U_isOpen {S : Finset (Pl D)} {ef : AfE D} (hef : ef ∈ intAE D) (N m n : ℕ) :
    IsOpen (U S ef N m n : Set (Matrix (Fin m) (Fin n) (AfE D))) := by
  have : IsModuleTopology (Af D.host.F) (AfE D) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AfE D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  refine AddSubgroup.isOpen_of_mem_nhds (U S ef N m n) (g := 0) ?_
  refine Filter.mem_of_superset ((intMat_isOpen m n).mem_nhds fun i j => zero_mem _) fun w hw => ?_
  exact ⟨fun v _ i j => cf_mem_of_mem (hw i j) v, fun i j =>
    GlobalTheory.HostAdeleIso.intAE_mul_mem D (GlobalTheory.IwaPlace.SdComap.natCast_mem_intAE N)
      (GlobalTheory.HostAdeleIso.intAE_mul_mem D hef (hw i j))⟩

open Classical in
/- English proof (translation)
Establish `: IsModuleTopology (Af D.host.F) (AfE D)` using `⟨rfl⟩`. Establish `: Module.Finite D.host.F D.host.E` using `Module.Finite.of_restrictScalars_finite ℚ _ _`. Establish `: IsTopologicalRing (AfE D)` using `IsModuleTopology.isTopologicalRing (Af D.host.F) _`. Establish `hcl : IsClosed (U S ef N m n : Set (Matrix (Fin m) (Fin n) (AfE D)))` using `AddSubgroup.isClosed_of_isOpen _ (U_isOpen hef N m n)`. Set `c : AfE D` to `algebraMap D.host.F (AfE D) ((N : D.host.F)⁻¹)`.

Establish `hc : c * (N : AfE D) = 1`. Establish `hN' : (N : D.host.F) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`. Rewrite using `[← map_natCast (algebraMap D.host.F (AfE D)) N, ← map_mul, inv_mul_cancel₀ hN', map_one]`. Establish `hK : IsCompact ((fun w : Matrix (Fin m) (Fin n) (AfE D) => Matrix.of fun i j => c * w i j) '' {w : Matrix (Fin m) (Fin n) (AfE D) | ∀ i j, w i j ∈ intAE D})` using `(intMat_isCompact m n).image (continuous_pi fun i => continuous_pi fun j => continuous_const.mul ((continuous_apply j).comp (continuous_apply i)))`. Use `hK.of_isClosed_subset hcl fun w hw => ?_` and prove the remaining obligations.

Use `⟨Matrix.of fun i j => (N : AfE D) * w i j, fun i j => ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : (1 - ef) * w i j ∈ intAE D` using `mem_of_cf_mem fun v => by`. Rewrite using `[map_mul, map_sub, map_one, hS v]`. Distinguish the cases in `hv : v ∈ S`. Rewrite using `[if_pos hv, sub_self, zero_mul]`.

Conclude with `zero_mem _`. Rewrite using `[if_neg hv, sub_zero, one_mul]`. Conclude with `hw.1 v hv i j`. Establish `h2 : (N : AfE D) * w i j = (N : AfE D) * (ef * w i j) + (N : AfE D) * ((1 - ef) * w i j)` using `by ring`. Rewrite using `[Matrix.of_apply, h2]`.

Conclude with `add_mem (hw.2 i j) (GlobalTheory.HostAdeleIso.intAE_mul_mem D (GlobalTheory.IwaPlace.SdComap.natCast_mem_intAE N) h1)`. Use extensionality with `i j`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[← mul_assoc, hc, one_mul]`.
-/
theorem U_isCompact {S : Finset (Pl D)} {ef : AfE D} (hef : ef ∈ intAE D)
    (hS : ∀ v : Pl D, cf v ef = if v ∈ S then 1 else 0) {N : ℕ} (hN : 0 < N) (m n : ℕ) :
    IsCompact (U S ef N m n : Set (Matrix (Fin m) (Fin n) (AfE D))) := by
  have : IsModuleTopology (Af D.host.F) (AfE D) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AfE D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  have hcl : IsClosed (U S ef N m n : Set (Matrix (Fin m) (Fin n) (AfE D))) :=
    AddSubgroup.isClosed_of_isOpen _ (U_isOpen hef N m n)
  let c : AfE D := algebraMap D.host.F (AfE D) ((N : D.host.F)⁻¹)
  have hc : c * (N : AfE D) = 1 := by
    have hN' : (N : D.host.F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    rw [← map_natCast (algebraMap D.host.F (AfE D)) N, ← map_mul, inv_mul_cancel₀ hN', map_one]
  have hK : IsCompact ((fun w : Matrix (Fin m) (Fin n) (AfE D) => Matrix.of fun i j => c * w i j) ''
      {w : Matrix (Fin m) (Fin n) (AfE D) | ∀ i j, w i j ∈ intAE D}) :=
    (intMat_isCompact m n).image (continuous_pi fun i => continuous_pi fun j =>
      continuous_const.mul ((continuous_apply j).comp (continuous_apply i)))
  refine hK.of_isClosed_subset hcl fun w hw => ?_
  refine ⟨Matrix.of fun i j => (N : AfE D) * w i j, fun i j => ?_, ?_⟩
  · have h1 : (1 - ef) * w i j ∈ intAE D := mem_of_cf_mem fun v => by
      rw [map_mul, map_sub, map_one, hS v]
      by_cases hv : v ∈ S
      · rw [if_pos hv, sub_self, zero_mul]; exact zero_mem _
      · rw [if_neg hv, sub_zero, one_mul]; exact hw.1 v hv i j
    have h2 : (N : AfE D) * w i j = (N : AfE D) * (ef * w i j) + (N : AfE D) * ((1 - ef) * w i j) := by ring
    rw [Matrix.of_apply, h2]
    exact add_mem (hw.2 i j) (GlobalTheory.HostAdeleIso.intAE_mul_mem D (GlobalTheory.IwaPlace.SdComap.natCast_mem_intAE N) h1)
  · ext i j
    simp only [Matrix.of_apply]
    rw [← mul_assoc, hc, one_mul]

end PositivityTheory.Rg.Rsw.L.LBumpEx

end

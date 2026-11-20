import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.SymplecticTensorMeasures
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IntegralTransport

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures (cE cE_cE cA_inc cA_cA ConjIsom conj_map_mem_unitaryGroup)
open GlobalTheory.LocWCompare
open scoped TensorProduct

namespace GlobalTheory.ConjAutProps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

/- English proof (translation)
Establish `: IsModuleTopology (AF D.host.F) (AE D)` using `⟨rfl⟩`. Establish `: IsTopologicalRing (AE D)` using `IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)`. Use `IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig).toLinearMap` as an intermediate fact. Conclude with `this`.
-/
theorem continuous_conjA (D : D7) : Continuous (cA D) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have := IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig).toLinearMap
  exact this

/- English proof (translation)
Establish `: IsModuleTopology (AF D.host.F) (AE D)` using `⟨rfl⟩`. Establish `: IsTopologicalRing (AE D)` using `IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)`. Establish `hm : Continuous (matHom V)` using `continuous_subtype_val`. Establish `hmap : Continuous fun x : Matrix (Fin V.rank) (Fin V.rank) (AE D) => x.map (cA D)` using `continuous_id.matrix_map (continuous_conjA D)`. Establish `hc : Continuous (cG D V.rank)` using `Units.continuous_iff.2 ⟨hmap.comp Units.continuous_val, hmap.comp Units.continuous_coe_inv⟩`.

Establish `h : Continuous fun g : GA D V => s.PA * cG D _ (matHom V g) * s.PA⁻¹` using `(continuous_const.mul (hc.comp hm)).mul continuous_const`. Conclude with `h.subtype_mk fun g => (s.aut g).2`.
-/
theorem continuous_aut (s : ConjIsom V) : Continuous s.aut := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have hm : Continuous (matHom V) := continuous_subtype_val
  have hmap : Continuous fun x : Matrix (Fin V.rank) (Fin V.rank) (AE D) => x.map (cA D) :=
    continuous_id.matrix_map (continuous_conjA D)
  have hc : Continuous (cG D V.rank) :=
    Units.continuous_iff.2 ⟨hmap.comp Units.continuous_val, hmap.comp Units.continuous_coe_inv⟩
  have h : Continuous fun g : GA D V => s.PA * cG D _ (matHom V g) * s.PA⁻¹ :=
    (continuous_const.mul (hc.comp hm)).mul continuous_const
  exact h.subtype_mk fun g => (s.aut g).2

/- English proof (translation)
Establish `hk' : Formalism.UG.bc (infPart D) (matHom V k) = 1` using `hk`. Establish `h2 : Formalism.UG.bc (infPart D) (cG D _ (matHom V k)) = 1`. Apply `Units.ext` to reduce the goal to its premises. Establish `h3 : (mt V k).map (infPart D) = 1` using `congrArg Units.val hk'`. Establish `h4 : ((mt V k).map (cA D)).map (infPart D) = ((mt V k).map (infPart D)).map (sigR (Ainf D.host.F) D.sp.cm.sig)`.

Use function extensionality and compare the values at `i j`. Conclude with `infPart_cA _`. Express the relevant statement in the definitionally equal form `((mt V k).map (cA D)).map (infPart D) = 1`. Rewrite using `[h4, h3, Matrix.map_one _ (map_zero _) (map_one _)]`. Express the relevant statement in the definitionally equal form `Formalism.UG.bc (infPart D) (matHom V (s.aut k)) = 1`.

Rewrite using `[matHom_aut, map_mul, map_mul, h2, map_inv, mul_one, mul_inv_cancel]`.
-/
theorem aut_mem_GfC (s : ConjIsom V) {k : GA D V} (hk : k ∈ GfC V) : s.aut k ∈ GfC V := by
  have hk' : Formalism.UG.bc (infPart D) (matHom V k) = 1 := hk
  have h2 : Formalism.UG.bc (infPart D) (cG D _ (matHom V k)) = 1 := by
    apply Units.ext
    have h3 : (mt V k).map (infPart D) = 1 := congrArg Units.val hk'
    have h4 : ((mt V k).map (cA D)).map (infPart D) =
        ((mt V k).map (infPart D)).map (sigR (Ainf D.host.F) D.sp.cm.sig) := by
      funext i j; exact infPart_cA _
    change ((mt V k).map (cA D)).map (infPart D) = 1
    rw [h4, h3, Matrix.map_one _ (map_zero _) (map_one _)]
  change Formalism.UG.bc (infPart D) (matHom V (s.aut k)) = 1
  rw [matHom_aut, map_mul, map_mul, h2, map_inv, mul_one, mul_inv_cancel]

/- English proof (translation)
Take `⟨γ, hγ, e⟩ : ∃ γ ∈ Formalism.UG.UJ (cE D) V.gram, Formalism.UG.bc (incA D) γ = matHom V k` from `hk`. Use `⟨_, conj_map_mem_unitaryGroup (cE D) V.gram s.P γ s.iso hγ, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Formalism.UG.bc (incA D) (s.P * Matrix.GeneralLinearGroup.map (cE D) γ * s.P⁻¹) = matHom V (s.aut k)`. Establish `h1 : Formalism.UG.bc (incA D) s.P = s.PA` using `Units.ext rfl`. Establish `h2 : Formalism.UG.bc (incA D) (Matrix.GeneralLinearGroup.map (cE D) γ) = cG D _ (Formalism.UG.bc (incA D) γ)`.

Use extensionality with `i j`. Conclude with `(cA_inc _).symm`. Rewrite using `[matHom_aut, map_mul, map_mul, map_inv, h1, h2, e]`.
-/
theorem aut_mem_GQ (s : ConjIsom V) {k : GA D V} (hk : k ∈ GQ V) : s.aut k ∈ GQ V := by
  obtain ⟨γ, hγ, e⟩ : ∃ γ ∈ Formalism.UG.UJ (cE D) V.gram, Formalism.UG.bc (incA D) γ = matHom V k := hk
  refine ⟨_, conj_map_mem_unitaryGroup (cE D) V.gram s.P γ s.iso hγ, ?_⟩
  change Formalism.UG.bc (incA D) (s.P * Matrix.GeneralLinearGroup.map (cE D) γ * s.P⁻¹) = matHom V (s.aut k)
  have h1 : Formalism.UG.bc (incA D) s.P = s.PA := Units.ext rfl
  have h2 : Formalism.UG.bc (incA D) (Matrix.GeneralLinearGroup.map (cE D) γ) = cG D _ (Formalism.UG.bc (incA D) γ) := by
    ext i j; exact (cA_inc _).symm
  rw [matHom_aut, map_mul, map_mul, map_inv, h1, h2, e]

/- English proof (translation)
The claim follows from `(autEquiv s).left_inv g`.
-/
theorem inv_aut_aut (s : ConjIsom V) (g : GA D V) : (invIsom s).aut (s.aut g) = g :=
  (autEquiv s).left_inv g

/- English proof (translation)
The claim follows from `(autEquiv s).right_inv g`.
-/
theorem aut_inv_aut (s : ConjIsom V) (g : GA D V) : s.aut ((invIsom s).aut g) = g :=
  (autEquiv s).right_inv g

/- English proof (translation)
Establish `h1 : s.PA.val.det * (s.PA⁻¹).val.det = 1`. Rewrite using `[← det_mul, s.PA.mul_inv, det_one]`. Establish `h2 : (cM (mt V g)).det = cA D (mt V g).det` using `((cA D).map_det _).symm`. Rewrite using `[s.mt_aut, det_mul, det_mul, h2, mul_right_comm, h1, one_mul]`.
-/
theorem det_aut (s : ConjIsom V) (g : GA D V) : (mt V (s.aut g)).det = cA D (mt V g).det := by
  have h1 : s.PA.val.det * (s.PA⁻¹).val.det = 1 := by
    rw [← det_mul, s.PA.mul_inv, det_one]
  have h2 : (cM (mt V g)).det = cA D (mt V g).det := ((cA D).map_det _).symm
  rw [s.mt_aut, det_mul, det_mul, h2, mul_right_comm, h1, one_mul]

/- English proof (translation)
Introduce `D V s`. Use `⟨isHomeomorph_iff_exists_inverse.2 ⟨continuous_aut s, (invIsom s).aut, inv_aut_aut s, aut_inv_aut s, continuous_aut _⟩, fun g => ⟨⟨fun h => ?_, aut_mem_GQ s⟩, ⟨fun h => ?_, aut_mem_GfC s⟩, ⟨fun h => ?_, aut_mem_GinfC s⟩, det_aut s g⟩⟩` and prove the remaining obligations. Conclude with `inv_aut_aut s g ▸ aut_mem_GQ (invIsom s) h`. Conclude with `inv_aut_aut s g ▸ aut_mem_GfC (invIsom s) h`. Conclude with `inv_aut_aut s g ▸ aut_mem_GinfC (invIsom s) h`.
-/
theorem autProps : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures.AutProps D := by
  intro D V s
  refine ⟨isHomeomorph_iff_exists_inverse.2 ⟨continuous_aut s, (invIsom s).aut, inv_aut_aut s, aut_inv_aut s,
    continuous_aut _⟩, fun g => ⟨⟨fun h => ?_, aut_mem_GQ s⟩, ⟨fun h => ?_, aut_mem_GfC s⟩,
    ⟨fun h => ?_, aut_mem_GinfC s⟩, det_aut s g⟩⟩
  · exact inv_aut_aut s g ▸ aut_mem_GQ (invIsom s) h
  · exact inv_aut_aut s g ▸ aut_mem_GfC (invIsom s) h
  · exact inv_aut_aut s g ▸ aut_mem_GinfC (invIsom s) h

end GlobalTheory.ConjAutProps

end

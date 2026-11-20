import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LevelCongruenceTypedPlaces
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.AdelicLatticeToLocalLattices
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.LocFrom
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.LocInj

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct
open Matrix

/- English proof (translation)
Rewrite using `[X.g_eq]`. Use `push_cast`. Conclude with `mul_ne_zero (Nat.cast_ne_zero.2 (D.host.g_prime 0).ne_zero) (Nat.cast_ne_zero.2 (D.host.g_prime 1).ne_zero)`.
-/
theorem g_cast_ne_zero {D : D7} (X : HidaSetting D) : (X.B.g : X.B.I.F) ≠ 0 := by
  rw [X.g_eq]
  push_cast
  exact mul_ne_zero (Nat.cast_ne_zero.2 (D.host.g_prime 0).ne_zero) (Nat.cast_ne_zero.2 (D.host.g_prime 1).ne_zero)

/- English proof (translation)
Rewrite `hv` using `[mem_typSet X.B.I.F _ _ (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero]`. Unfold `IsTyped at hv`. Rewrite `hv` using `[not_or]`. Establish `hg : ((X.B.g : 𝓞 X.B.I.F)) ∉ v.asIdeal`. Rewrite using `[X.g_eq]`.

Use `push_cast`. Introduce `h`. Break down `v.isPrime.mem_or_mem h with h | h` into its components or cases. Use `exacts [hv.1 h, hv.2 h]`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`.

Establish `e : algebraMap X.B.I.F (Fv X.B.I.F v) ((X.B.g : X.B.I.F)⁻¹) = (((X.B.g : X.B.I.F)⁻¹ : X.B.I.F) : v.adicCompletion X.B.I.F)` using `rfl`. Rewrite using `[e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀]`. Establish `: v.valuation X.B.I.F (X.B.g : X.B.I.F) = 1`. Rewrite using `[show (X.B.g : X.B.I.F) = algebraMap (𝓞 X.B.I.F) X.B.I.F (X.B.g : 𝓞 X.B.I.F) by simp, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hg]`. Rewrite using `[this, inv_one]`.
-/
theorem ginv_int {D : D7} (X : HidaSetting D) (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (hv : v ∉ typSet X.B.I.F (D.host.g 0) (D.host.g 1)) :
    (algebraMap X.B.I.F (Fv X.B.I.F v) ((X.B.g : X.B.I.F)⁻¹)) ∈ v.adicCompletionIntegers X.B.I.F := by
  rw [mem_typSet X.B.I.F _ _ (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero] at hv
  unfold IsTyped at hv
  rw [not_or] at hv
  have hg : ((X.B.g : 𝓞 X.B.I.F)) ∉ v.asIdeal := by
    rw [X.g_eq]
    push_cast
    intro h
    rcases v.isPrime.mem_or_mem h with h | h
    exacts [hv.1 h, hv.2 h]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have e : algebraMap X.B.I.F (Fv X.B.I.F v) ((X.B.g : X.B.I.F)⁻¹) =
      (((X.B.g : X.B.I.F)⁻¹ : X.B.I.F) : v.adicCompletion X.B.I.F) := rfl
  rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀]
  have : v.valuation X.B.I.F (X.B.g : X.B.I.F) = 1 := by
    rw [show (X.B.g : X.B.I.F) = algebraMap (𝓞 X.B.I.F) X.B.I.F (X.B.g : 𝓞 X.B.I.F) by simp,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hg]
  rw [this, inv_one]

/- English proof (translation)
Use `Submodule.smul_mem _ (⟨_, ginv_int X v hv⟩ : v.adicCompletionIntegers X.B.I.F) hu` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.smul_apply, IsScalarTower.algebraMap_apply X.B.I.F (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E), ← Algebra.smul_def]`. Both sides reduce to the same expression.
-/
theorem smul_latLoc {D : D7} (X : HidaSetting D) (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (hv : v ∉ typSet X.B.I.F (D.host.g 0) (D.host.g 1))
    (u : Fin X.B.I.n → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)
    (hu : u ∈ latLoc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) :
    (fun i => algebraMap X.B.I.F (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) ((X.B.g : X.B.I.F)⁻¹) * u i) ∈
      latLoc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  have := Submodule.smul_mem _ (⟨_, ginv_int X v hv⟩ : v.adicCompletionIntegers X.B.I.F) hu
  convert this using 1
  funext i
  rw [Pi.smul_apply, IsScalarTower.algebraMap_apply X.B.I.F (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E),
    ← Algebra.smul_def]
  rfl

/- English proof (translation)
Introduce `D X hb κ hκ hT`. Use `⟨hκ, fun y hy => ?_⟩` and prove the remaining obligations. Set `c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F` to `algebraMap X.B.I.F _ ((X.B.g : X.B.I.F)⁻¹)`. Use `⟨fun i => c * ((X.B.I.fmat κ - 1) *ᵥ y) i, ?_, ?_⟩` and prove the remaining obligations. Apply `PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective` to reduce the goal to its premises.

Introduce `v`. Establish `hy'` using `PI.FinKW.LocTo.mem_local_lattice_iff X.B.I y hy v`. Establish `hmat : (X.B.I.fmat κ).map (PI.FinKW.psiV X.B.I v) = ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) (finHA X hb κ)) : GL (Fin X.B.I.n) _) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E))`. Express the relevant statement in the definitionally equal form `_ = (((HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (PI.MassDataKppVolLemmas.tf X.B.I hb κ) : GL (Fin X.B.I.n) _) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E))).map (tensMap (E := X.B.I.E) (evalV X.B.I.F v))`. Rewrite using `[PI.MassDataKppVolLemmas.Bridge_mat X.B.I hb κ, Matrix.map_map]`.

Both sides reduce to the same expression. Establish `hvec : PI.FinKW.vecV X.B.I v (fun i => c * ((X.B.I.fmat κ - 1) *ᵥ y) i) = fun i => algebraMap X.B.I.F (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) ((X.B.g : X.B.I.F)⁻¹) * ((((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) (finHA X hb κ)) : GL (Fin X …`. Use function extensionality and compare the values at `i`. Simplify using `only [PI.FinKW.vecV, map_mul, c, AlgHom.commutes]`. Use `congr 1`.

Establish `h1` using `RingHom.map_mulVec (PI.FinKW.psiV X.B.I v).toRingHom (X.B.I.fmat κ - 1) y i`. Rewrite using `[← hmat, ← Matrix.map_one (PI.FinKW.psiV X.B.I v).toRingHom (map_zero _) (map_one _)]`. Rewrite `h1` using `[Matrix.map_sub _ (fun a b => map_sub _ a b)]`. Conclude with `h1`. Rewrite using `[hvec]`.

Distinguish the cases in `hv : v ∈ typSet X.B.I.F (D.host.g 0) (D.host.g 1)`. Establish `e` using `hT ⟨v, hv⟩`. Simplify using `only at e`. Rewrite using `[e]`. Establish `: ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (1 : HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) : GL (Fin X.B.I.n) _) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) = 1` using `rfl`.

Rewrite using `[this, sub_self, Matrix.zero_mulVec]`. Simplify using `only [Pi.zero_apply, mul_zero]`. Conclude with `Submodule.zero_mem _`. Apply `smul_latLoc X v hv` to reduce the goal to its premises. Establish `hK` using `compK_holds X v (finHA X hb κ) (finHA_mem_Kf X hb κ hκ)`.

Establish `hm` using `(hK (PI.FinKW.vecV X.B.I v y)).1 hy'`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec]`. Conclude with `Submodule.sub_mem _ hm hy'`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, c, ← mul_assoc]`.

Rewrite using `[show ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = algebraMap X.B.I.F _ (X.B.g : X.B.I.F) by simp, ← map_mul, mul_inv_cancel₀ (g_cast_ne_zero X), map_one, one_mul]`.
-/
theorem kgLoc_holds : KgLoc := by
  intro D X hb κ hκ hT
  refine ⟨hκ, fun y hy => ?_⟩
  let c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F := algebraMap X.B.I.F _ ((X.B.g : X.B.I.F)⁻¹)
  refine ⟨fun i => c * ((X.B.I.fmat κ - 1) *ᵥ y) i, ?_, ?_⟩
  · apply PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective
    intro v
    have hy' := PI.FinKW.LocTo.mem_local_lattice_iff X.B.I y hy v
    have hmat : (X.B.I.fmat κ).map (PI.FinKW.psiV X.B.I v) =
        ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
          (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) (finHA X hb κ)) : GL (Fin X.B.I.n) _) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) := by
      change _ = (((HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (PI.MassDataKppVolLemmas.tf X.B.I hb κ) :
        GL (Fin X.B.I.n) _) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E))).map
          (tensMap (E := X.B.I.E) (evalV X.B.I.F v))
      rw [PI.MassDataKppVolLemmas.Bridge_mat X.B.I hb κ, Matrix.map_map]
      rfl
    have hvec : PI.FinKW.vecV X.B.I v (fun i => c * ((X.B.I.fmat κ - 1) *ᵥ y) i) =
        fun i => algebraMap X.B.I.F (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) ((X.B.g : X.B.I.F)⁻¹) *
          ((((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
          (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) (finHA X hb κ)) : GL (Fin X.B.I.n) _) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
            PI.FinKW.vecV X.B.I v y) i := by
      funext i
      simp only [PI.FinKW.vecV, map_mul, c, AlgHom.commutes]
      congr 1
      have h1 := RingHom.map_mulVec (PI.FinKW.psiV X.B.I v).toRingHom (X.B.I.fmat κ - 1) y i
      rw [← hmat, ← Matrix.map_one (PI.FinKW.psiV X.B.I v).toRingHom (map_zero _) (map_one _)]
      rw [Matrix.map_sub _ (fun a b => map_sub _ a b)] at h1
      exact h1
    rw [hvec]
    by_cases hv : v ∈ typSet X.B.I.F (D.host.g 0) (D.host.g 1)
    · have e := hT ⟨v, hv⟩
      simp only at e
      rw [e]
      have : ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (1 : HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) :
          GL (Fin X.B.I.n) _) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) = 1 := rfl
      rw [this, sub_self, Matrix.zero_mulVec]
      simp only [Pi.zero_apply, mul_zero]
      exact Submodule.zero_mem _
    · apply smul_latLoc X v hv
      have hK := compK_holds X v (finHA X hb κ) (finHA_mem_Kf X hb κ hκ)
      have hm := (hK (PI.FinKW.vecV X.B.I v y)).1 hy'
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact Submodule.sub_mem _ hm hy'
  · funext i
    simp only [Pi.smul_apply, smul_eq_mul, c, ← mul_assoc]
    rw [show ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = algebraMap X.B.I.F _ (X.B.g : X.B.I.F) by simp,
      ← map_mul, mul_inv_cancel₀ (g_cast_ne_zero X), map_one, one_mul]

/- English proof (translation)
The claim follows from `globProd_of_loc kgLoc_holds ht`.
-/
theorem globProd_of_k2LocT (ht : LevelCongruenceTypedPlaces) : GlobProd := globProd_of_loc kgLoc_holds ht

end MassDataLevelSSteps

import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FirstEmbeddingAlgebraMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LatTop

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions
  Formalism.L2.SG.HidaSetting
open scoped TensorProduct Matrix

instance charZero_adicCompletion {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    CharZero (v.adicCompletion F) :=
  charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

/- English proof (translation)
Introduce `c ε hε`. Establish `hO : IsOpen ((OpX X p : Set (FpX X p)))` using `Valued.isOpen_integer _`. Establish `hU : IsOpen {k : FpX X p | (k - c) * ε⁻¹ ∈ OpX X p}` using `hO.preimage ((continuous_id.sub continuous_const).mul continuous_const)`. Take `⟨b, hb⟩` from `(HeightOneSpectrum.denseRange_algebraMap (v := p.1) (K := X.B.I.F)).exists_mem_open hU ⟨c, by simp [zero_mem]⟩`. Use `⟨b, _, hb, ?_⟩` and prove the remaining obligations.

Clear the denominators using the available nonvanishing facts.
-/
theorem denseF_holds : DenseF X p := by
  intro c ε hε
  have hO : IsOpen ((OpX X p : Set (FpX X p))) := Valued.isOpen_integer _
  have hU : IsOpen {k : FpX X p | (k - c) * ε⁻¹ ∈ OpX X p} :=
    hO.preimage ((continuous_id.sub continuous_const).mul continuous_const)
  obtain ⟨b, hb⟩ := (HeightOneSpectrum.denseRange_algebraMap (v := p.1) (K := X.B.I.F)).exists_mem_open hU
    ⟨c, by simp [zero_mem]⟩
  refine ⟨b, _, hb, ?_⟩
  field_simp

/- English proof (translation)
Establish `heq : (M : FpX X p) • u = ∑ j, (⟨u j, hu j⟩ : OpX X p) • (fun i => ι ((M • (Pi.single j (1 : X.B.I.E) : Fin X.B.I.n → X.B.I.E)) i))`. Use function extensionality and compare the values at `i`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, map_zsmul, Pi.single_apply]`. Rewrite using `[Finset.sum_eq_single i]`.

Simplify using `only [if_true, map_one] show (M : FpX X p) * u i = u i * (M • (1 : FpX X p))`. Rewrite using `[zsmul_eq_mul, mul_one, mul_comm]`. Introduce `j _ hji`. Simplify using `only [if_neg (Ne.symm hji), map_zero, smul_zero]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ i) h`. Rewrite using `[heq]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hgen j)`.
-/
theorem cube_mem (ι : X.B.I.E →+* FpX X p) (Msub : Submodule (OpX X p) (Fin X.B.I.n → FpX X p)) (M : ℤ)
    (hgen : ∀ j : Fin X.B.I.n, (fun i => ι ((M • (Pi.single j (1 : X.B.I.E) : Fin X.B.I.n → X.B.I.E)) i)) ∈ Msub)
    (u : Fin X.B.I.n → FpX X p) (hu : ∀ i, u i ∈ OpX X p) : (M : FpX X p) • u ∈ Msub := by
  classical
  have heq : (M : FpX X p) • u =
      ∑ j, (⟨u j, hu j⟩ : OpX X p) • (fun i => ι ((M • (Pi.single j (1 : X.B.I.E) : Fin X.B.I.n → X.B.I.E)) i)) := by
    funext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, map_zsmul, Pi.single_apply]
    rw [Finset.sum_eq_single i]
    · simp only [if_true, map_one]
      show (M : FpX X p) * u i = u i * (M • (1 : FpX X p))
      rw [zsmul_eq_mul, mul_one, mul_comm]
    · intro j _ hji
      simp only [if_neg (Ne.symm hji), map_zero, smul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [heq]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hgen j)

/- English proof (translation)
Establish `h : ∀ j : Fin X.B.I.n, ∃ N : ℤ, N ≠ 0 ∧ N • (Pi.single j (1 : X.B.I.E) : Fin X.B.I.n → X.B.I.E) ∈ X.B.I.L` using `fun j => MassDataLevelSSteps.LatTop.exists_int_smul_mem X.B.I.L X.B.I.L_span _`. Use `choose N hN0 hNL using h`. Use `set M : ℤ := ∏ j, N j with hM`. Establish `hM0 : M ≠ 0` using `Finset.prod_ne_zero_iff.2 fun j _ => hN0 j`. Establish `hML : ∀ j, M • (Pi.single j (1 : X.B.I.E) : Fin X.B.I.n → X.B.I.E) ∈ X.B.I.L`.

Introduce `j`. Rewrite using `[hM, ← Finset.mul_prod_erase Finset.univ N (Finset.mem_univ j), mul_comm, mul_smul]`. Conclude with `zsmul_mem (hNL j) _`. Use `⟨(M : FpX X p), ?_, fun u hu => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `Int.cast_ne_zero.2 hM0`.

Conclude with `cube_mem X p (iota1 X p θ) (Mlat1 X p θ) M (fun j => by unfold Mlat1; exact Submodule.subset_span ⟨_, hML j, rfl⟩) u hu`. Conclude with `cube_mem X p (iota2 X p θ) (Mlat2 X p θ) M (fun j => by unfold Mlat2; exact Submodule.subset_span ⟨_, hML j, rfl⟩) u hu`.
-/
theorem epsLat_holds : EpsLat X p θ := by
  classical
  have h : ∀ j : Fin X.B.I.n, ∃ N : ℤ, N ≠ 0 ∧ N • (Pi.single j (1 : X.B.I.E) : Fin X.B.I.n → X.B.I.E) ∈ X.B.I.L :=
    fun j => MassDataLevelSSteps.LatTop.exists_int_smul_mem X.B.I.L X.B.I.L_span _
  choose N hN0 hNL using h
  set M : ℤ := ∏ j, N j with hM
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hN0 j
  have hML : ∀ j, M • (Pi.single j (1 : X.B.I.E) : Fin X.B.I.n → X.B.I.E) ∈ X.B.I.L := by
    intro j
    rw [hM, ← Finset.mul_prod_erase Finset.univ N (Finset.mem_univ j), mul_comm, mul_smul]
    exact zsmul_mem (hNL j) _
  refine ⟨(M : FpX X p), ?_, fun u hu => ⟨?_, ?_⟩⟩
  · exact Int.cast_ne_zero.2 hM0
  · exact cube_mem X p (iota1 X p θ) (Mlat1 X p θ) M
      (fun j => by unfold Mlat1; exact Submodule.subset_span ⟨_, hML j, rfl⟩) u hu
  · exact cube_mem X p (iota2 X p θ) (Mlat2 X p θ) M
      (fun j => by unfold Mlat2; exact Submodule.subset_span ⟨_, hML j, rfl⟩) u hu

/- English proof (translation)
The claim follows from `latBasisAll_of_parts X p (fun θ hθ => denom_holds X p θ hθ) (fun θ hθ => approx_of X p θ hθ (denseF_holds X p) (epsLat_holds X p θ))`.
-/
theorem latBasisAll_holds' : LatBasisAll X p :=
  latBasisAll_of_parts X p (fun θ hθ => denom_holds X p θ hθ)
    (fun θ hθ => approx_of X p θ hθ (denseF_holds X p) (epsLat_holds X p θ))

end Loc

end MassDataIdxSteps

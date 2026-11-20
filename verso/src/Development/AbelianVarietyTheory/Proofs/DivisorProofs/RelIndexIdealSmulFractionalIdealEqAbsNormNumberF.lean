import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.FracIdealIndex

/- English proof (translation)
Introduce `F _ _ I p hp hI ⟨c, hc0, hc⟩`. Establish `hc' : (c : F) ≠ 0` using `by exact_mod_cast hc0`. Set `f : F →ₗ[𝓞 F] F` to `c • LinearMap.id`. Establish `hf : ∀ y, f y = c • y` using `fun y => rfl`. Establish `hfi : Function.Injective f` using `fun y z h => by`.

Simplify using `only [hf, Algebra.smul_def] at h`. Conclude with `mul_left_cancel₀ (by simpa using hc') h`. Set `g : 𝓞 F →ₗ[𝓞 F] F` to `Algebra.linearMap (𝓞 F) F`. Establish `hgi : Function.Injective g` using `fun y z h => by`. Simplify `h` using `[g]`.

Establish `hle : Submodule.map f I ≤ LinearMap.range g`. Rewrite using `[← Submodule.one_eq_range]`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `hc y hy`. Set `J : Ideal (𝓞 F)` to `(Submodule.map f I).comap g`.

Establish `hJ : Submodule.map g J = Submodule.map f I` using `Submodule.map_comap_eq_of_le hle`. Establish `hJ0 : J ≠ ⊥`. Introduce `h`. Apply `hI` to reduce the goal to its premises. Establish `: Submodule.map f I = ⊥` using `by rw [← hJ, h, Submodule.map_bot]`.

Conclude with `Submodule.map_injective_of_injective hfi (this.trans (Submodule.map_bot f).symm)`. Establish `hpJ : Submodule.map g (p * J) = Submodule.map f (p • I)`. Rewrite using `[← Ideal.smul_eq_mul, Submodule.map_smul'', Submodule.map_smul'', hJ]`. Establish `e1 : (p • I).toAddSubgroup.relIndex I.toAddSubgroup = (p * J).toAddSubgroup.relIndex J.toAddSubgroup`. Establish `a1` using `AddSubgroup.relIndex_map_map_of_injective (p • I).toAddSubgroup I.toAddSubgroup (f := (f : F →+ F)) hfi`.

Establish `a2` using `AddSubgroup.relIndex_map_map_of_injective (p * J).toAddSubgroup J.toAddSubgroup (f := (g : 𝓞 F →+ F)) hgi`. Rewrite `a1`, `a2` using `[← Submodule.map_toAddSubgroup, ← Submodule.map_toAddSubgroup]`. Rewrite using `[← a1, ← a2, hpJ, hJ]`. Apply the tactic sequence `have hle2 : p * J ≤ J := by first | exact Ideal.mul_le_left | exact Ideal.mul_le_right`. Establish `hidx : (p * J).toAddSubgroup.relIndex J.toAddSubgroup * Ideal.absNorm J = Ideal.absNorm (p * J)` using `AddSubgroup.relIndex_mul_index (H := (p * J).toAddSubgroup) (K := J.toAddSubgroup) hle2`.

Establish `hN : Ideal.absNorm J ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `hJ0`. Rewrite using `[e1]`. Rewrite `hidx` using `[map_mul]`.

Conclude with `mul_right_cancel₀ hN hidx`.
-/
theorem relIndex_smul_eq_absNorm : ∀ (F : Type) [Field F] [NumberField F] (I : Submodule (𝓞 F) F) (p : Ideal (𝓞 F)), p ≠ ⊥ → I ≠ ⊥ → (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ y ∈ I, c • y ∈ (1 : Submodule (𝓞 F) F)) → (p • I).toAddSubgroup.relIndex I.toAddSubgroup = Ideal.absNorm p := by
  intro F _ _ I p hp hI ⟨c, hc0, hc⟩
  have hc' : (c : F) ≠ 0 := by exact_mod_cast hc0
  let f : F →ₗ[𝓞 F] F := c • LinearMap.id
  have hf : ∀ y, f y = c • y := fun y => rfl
  have hfi : Function.Injective f := fun y z h => by
    simp only [hf, Algebra.smul_def] at h
    exact mul_left_cancel₀ (by simpa using hc') h
  let g : 𝓞 F →ₗ[𝓞 F] F := Algebra.linearMap (𝓞 F) F
  have hgi : Function.Injective g := fun y z h => by
    simpa [g] using h
  have hle : Submodule.map f I ≤ LinearMap.range g := by
    rw [← Submodule.one_eq_range]
    rintro _ ⟨y, hy, rfl⟩
    exact hc y hy
  let J : Ideal (𝓞 F) := (Submodule.map f I).comap g
  have hJ : Submodule.map g J = Submodule.map f I := Submodule.map_comap_eq_of_le hle
  have hJ0 : J ≠ ⊥ := by
    intro h
    apply hI
    have : Submodule.map f I = ⊥ := by rw [← hJ, h, Submodule.map_bot]
    exact Submodule.map_injective_of_injective hfi (this.trans (Submodule.map_bot f).symm)
  have hpJ : Submodule.map g (p * J) = Submodule.map f (p • I) := by
    rw [← Ideal.smul_eq_mul, Submodule.map_smul'', Submodule.map_smul'', hJ]
  have e1 : (p • I).toAddSubgroup.relIndex I.toAddSubgroup =
      (p * J).toAddSubgroup.relIndex J.toAddSubgroup := by
    have a1 := AddSubgroup.relIndex_map_map_of_injective (p • I).toAddSubgroup I.toAddSubgroup
      (f := (f : F →+ F)) hfi
    have a2 := AddSubgroup.relIndex_map_map_of_injective (p * J).toAddSubgroup J.toAddSubgroup
      (f := (g : 𝓞 F →+ F)) hgi
    rw [← Submodule.map_toAddSubgroup, ← Submodule.map_toAddSubgroup] at a1 a2
    rw [← a1, ← a2, hpJ, hJ]
  have hle2 : p * J ≤ J := by first | exact Ideal.mul_le_left | exact Ideal.mul_le_right
  have hidx : (p * J).toAddSubgroup.relIndex J.toAddSubgroup * Ideal.absNorm J = Ideal.absNorm (p * J) :=
    AddSubgroup.relIndex_mul_index (H := (p * J).toAddSubgroup) (K := J.toAddSubgroup) hle2
  have hN : Ideal.absNorm J ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hJ0
  rw [e1]
  rw [map_mul] at hidx
  exact mul_right_cancel₀ hN hidx

end GlobalTheory.FracIdealIndex

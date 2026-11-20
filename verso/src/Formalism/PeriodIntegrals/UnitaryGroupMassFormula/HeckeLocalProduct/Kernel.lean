import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Lemmata.MiscLemmasM.Imports

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host RestrictedProduct Topology

namespace PI.HeckeProdW

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.SecondBlockLemmaN.goal1 .. | (apply Bl.SecondBlockLemmaN.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaN.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaN.goal1 <;> assumption) | (intros; apply @Bl.SecondBlockLemmaN.goal1 <;> assumption) | (apply @ …`.
-/
theorem no_small (z : ℂ) (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first | exact Bl.SecondBlockLemmaN.goal1 .. | (apply Bl.SecondBlockLemmaN.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaN.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaN.goal1 <;> assumption) | (intros; apply @Bl.SecondBlockLemmaN.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaN.goal1 <;> first | assumption | infer_instance) | exact @Bl.SecondBlockLemmaN.goal1 z h | exact @Bl.SecondBlockLemmaN.goal1 z

variable (L : Type) [Field L] [NumberField L]

abbrev Pu : Type := (v : HeightOneSpectrum (𝓞 L)) → (v.adicCompletionIntegers L)ˣ

def gI : ((v : HeightOneSpectrum (𝓞 L)) → v.adicCompletionIntegers L) →* AdeleRing (𝓞 L) L where
  toFun x := ((1 : InfiniteAdeleRing L),
    (structureMap (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
      (fun v => v.adicCompletionIntegers L) Filter.cofinite x : FiniteAdeleRing (𝓞 L) L))
  map_one' := rfl
  map_mul' _ _ := Prod.ext (mul_one 1).symm rfl

/- English proof (translation)
Use `show Continuous (fun x => ((1 : InfiniteAdeleRing L), (structureMap (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L) (fun v => v.adicCompletionIntegers L) Filter.cofinite x : FiniteAdeleRing (𝓞 L) L)))`. Conclude with `continuous_const.prodMk isEmbedding_structureMap.continuous`.
-/
theorem gI_cont : Continuous (gI L) := by
  show Continuous (fun x => ((1 : InfiniteAdeleRing L),
    (structureMap (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
      (fun v => v.adicCompletionIntegers L) Filter.cofinite x : FiniteAdeleRing (𝓞 L) L)))
  exact continuous_const.prodMk isEmbedding_structureMap.continuous

def Phi : Pu L →* Ideles L :=
  (Units.map (gI L)).comp (MulEquiv.piUnits (M := fun v : HeightOneSpectrum (𝓞 L) =>
    v.adicCompletionIntegers L)).symm.toMonoidHom

/- English proof (translation)
The claim follows from `(Continuous.units_map _ (gI_cont L)).comp (ContinuousMulEquiv.piUnits (M := fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletionIntegers L)).symm.continuous`.
-/
theorem Phi_cont : Continuous (Phi L) :=
  (Continuous.units_map _ (gI_cont L)).comp
    (ContinuousMulEquiv.piUnits (M := fun v : HeightOneSpectrum (𝓞 L) =>
      v.adicCompletionIntegers L)).symm.continuous

variable {L}

/- English proof (translation)
Use `set W : Set ℂˣ := {z | ‖(z : ℂ) - 1‖ < 1 / 2} with hWdef`. Establish `hW : IsOpen W` using `isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const`. Establish `hc : Continuous (fun y => χ.1 (Phi L y))` using `χ.2.1.comp (Phi_cont L)`. Establish `h1 : (fun y => χ.1 (Phi L y)) 1 ∈ W`. Simplify using `only [map_one, hWdef, Set.mem_setOf_eq, Units.val_one, sub_self, norm_zero]`.

Evaluate the numerical expressions. Establish `hmem : (fun y => χ.1 (Phi L y)) ⁻¹' W ∈ 𝓝 (1 : Pu L)` using `hc.continuousAt.preimage_mem_nhds (hW.mem_nhds h1)`. Rewrite `hmem` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, hI, t, ht, hsub⟩` from `hmem`. Use `⟨hI.toFinset, fun y hy => ?_⟩` and prove the remaining obligations.

Establish `hyI : ∀ n : ℕ, y ^ n ∈ I.pi t`. Introduce `n i hi`. Rewrite using `[Pi.pow_apply, hy i (hI.mem_toFinset.2 hi), one_pow]`. Conclude with `mem_of_mem_nhds (ht i)`. Use `Units.ext (no_small _ fun n => ?_)` and prove the remaining obligations.

Establish `h2` using `hsub (hyI n)`. Simplify using `only [Set.mem_preimage, map_pow, hWdef, Set.mem_setOf_eq, Units.val_pow_eq_pow_val] at h2`. Conclude with `h2`.
-/
theorem exists_strictHenselian_absolutely_closed_local_ring (χ : HChar L) : ∃ T : Finset (HeightOneSpectrum (𝓞 L)),
    ∀ y : Pu L, (∀ v ∈ T, y v = 1) → χ.1 (Phi L y) = 1 := by
  set W : Set ℂˣ := {z | ‖(z : ℂ) - 1‖ < 1 / 2} with hWdef
  have hW : IsOpen W :=
    isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const
  have hc : Continuous (fun y => χ.1 (Phi L y)) := χ.2.1.comp (Phi_cont L)
  have h1 : (fun y => χ.1 (Phi L y)) 1 ∈ W := by
    simp only [map_one, hWdef, Set.mem_setOf_eq, Units.val_one, sub_self, norm_zero]
    norm_num
  have hmem : (fun y => χ.1 (Phi L y)) ⁻¹' W ∈ 𝓝 (1 : Pu L) :=
    hc.continuousAt.preimage_mem_nhds (hW.mem_nhds h1)
  rw [nhds_pi, Filter.mem_pi] at hmem
  obtain ⟨I, hI, t, ht, hsub⟩ := hmem
  refine ⟨hI.toFinset, fun y hy => ?_⟩
  have hyI : ∀ n : ℕ, y ^ n ∈ I.pi t := by
    intro n i hi
    rw [Pi.pow_apply, hy i (hI.mem_toFinset.2 hi), one_pow]
    exact mem_of_mem_nhds (ht i)
  refine Units.ext (no_small _ fun n => ?_)
  have h2 := hsub (hyI n)
  simp only [Set.mem_preimage, map_pow, hWdef, Set.mem_setOf_eq, Units.val_pow_eq_pow_val] at h2
  exact h2

end PI.HeckeProdW

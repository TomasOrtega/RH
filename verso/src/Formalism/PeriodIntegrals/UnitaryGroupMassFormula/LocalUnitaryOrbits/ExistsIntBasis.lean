import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.SdVolWOfTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.VolStabSW
  PI.VolStabSW.PositiveNearLattice PI.VolStabSW.SdDualW
open scoped TensorProduct

section Top

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def oevS : AddSubgroup (Fv F v ⊗[F] E) :=
  (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)).toAddSubgroup

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_oevS : (oevS (E := E) v : Set (Fv F v ⊗[F] E)) = OEv (E := E) v := rfl

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨x, Set.mem_univ _, rfl⟩`.
-/
theorem inclR_mem_oev (x : 𝓞 E) : inclR (F := F) (Fv F v) (x : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨x, Set.mem_univ _, rfl⟩

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Take `⟨y, hy, hint⟩` from `exists_integral_multiples ℤ ℚ (Finset.univ.image (Module.finBasis F E))`. Establish `hyF : IsUnit ((y : F))`. Rewrite using `[isUnit_iff_ne_zero]`. Conclude with `hy` after adjusting the coercions.

Use `⟨_, (Module.finBasis F E).isUnitSMul (fun _ => hyF), fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul]`. Conclude with `hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))`.
-/
theorem exists_int_basis : ∃ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ k, IsIntegral ℤ (b k) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  classical
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image (Module.finBasis F E))
  have hyF : IsUnit ((y : F)) := by
    rw [isUnit_iff_ne_zero]
    exact_mod_cast hy
  refine ⟨_, (Module.finBasis F E).isUnitSMul (fun _ => hyF), fun k => ?_⟩
  rw [Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul]
  exact hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))

/- English proof (translation)
Introduce `z hz`. Establish `hz' : ∀ k, crd b (Fv F v) z k ∈ v.adicCompletionIntegers F` using `hz`. Rewrite using `[← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr z]`. Use `AddSubgroup.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.basis_apply]`.

Establish `hm : inclR (F` using `F) (Fv F v) (((⟨b k, hb k⟩ : 𝓞 E)) : E) ∈ OEv (E := E) v := inclR_mem_oev v (⟨b k, hb k⟩ : 𝓞 E)`. Conclude with `Submodule.smul_mem _ (⟨_, hz' k⟩ : v.adicCompletionIntegers F) hm`.
-/
theorem latA_le_oevS [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
    (hb : ∀ k, IsIntegral ℤ (b k)) : latA v b ≤ oevS (E := E) v := by
  intro z hz
  have hz' : ∀ k, crd b (Fv F v) z k ∈ v.adicCompletionIntegers F := hz
  rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr z]
  refine AddSubgroup.sum_mem _ fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply]
  have hm : inclR (F := F) (Fv F v) (((⟨b k, hb k⟩ : 𝓞 E)) : E) ∈ OEv (E := E) v :=
    inclR_mem_oev v (⟨b k, hb k⟩ : 𝓞 E)
  exact Submodule.smul_mem _ (⟨_, hz' k⟩ : v.adicCompletionIntegers F) hm

/- English proof (translation)
Establish `: FiniteDimensional F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Take `⟨d, b, hb⟩` from `exists_int_basis (F := F) (E := E)`. Rewrite using `[← coe_oevS]`. Conclude with `AddSubgroup.isOpen_mono (latA_le_oevS v b hb) (isOpen_latA v b)`.
-/
theorem isOpen_oev : IsOpen (OEv (E := E) v) := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨d, b, hb⟩ := exists_int_basis (F := F) (E := E)
  rw [← coe_oevS]
  exact AddSubgroup.isOpen_mono (latA_le_oevS v b hb) (isOpen_latA v b)

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Take `⟨m, s, hs⟩` from `Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)`. Use `set g : Fin m → Fv F v ⊗[F] E := fun i => inclR (F := F) (Fv F v) ((s i : 𝓞 E) : E) with hg`. Establish `e : OEv (E` using `E) v = (fun c : Fin m → Fv F v => ∑ i, c i • g i) '' Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by`. Use extensionality with `z`.

Prove the components needed by the constructor for the conclusion. Introduce `hz`. Establish `h1 : z ∈ Submodule.span (v.adicCompletionIntegers F) (Set.range g)`. Use `(Submodule.span_le.2 ?_) hz` and prove the remaining obligations. Introduce and unpack `_ ⟨x, _, rfl⟩`.

Establish `hx : x ∈ Submodule.span ℤ (Set.range s)` using `by rw [hs]; exact Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨i, rfl⟩` from `hy`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`.

Consider the case `zero => simpa using Submodule.zero_mem _`. Consider the case `add p q _ _ hp hq`. Establish `e1 : inclR (F` using `F) (Fv F v) (((p + q : 𝓞 E)) : E) = inclR (F := F) (Fv F v) (p : E) + inclR (F := F) (Fv F v) (q : E) := by`. Rewrite using `[← map_add]`. Both sides reduce to the same expression.

Use `show inclR (F := F) (Fv F v) (((p + q : 𝓞 E)) : E) ∈ _`. Rewrite using `[e1]`. Conclude with `Submodule.add_mem _ (hp trivial) (hq trivial)`. Consider the case `smul r p _ hp`. Establish `e1 : inclR (F` using `F) (Fv F v) (((r • p : 𝓞 E)) : E) = r • inclR (F := F) (Fv F v) (p : E) := by`.

Rewrite using `[show ((r • p : 𝓞 E) : E) = r • (p : E) from map_zsmul (algebraMap (𝓞 E) E) r p, map_zsmul]`. Use `show inclR (F := F) (Fv F v) (((r • p : 𝓞 E)) : E) ∈ _`. Rewrite using `[e1]`. Conclude with `zsmul_mem (hp trivial) r`. Rewrite `h1` using `[Submodule.mem_span_range_iff_exists_fun]`.

Take `⟨c, rfl⟩` from `h1`. Conclude with `⟨fun i => (c i : Fv F v), fun i _ => (c i).2, rfl⟩`. Introduce and unpack `⟨c, hc, rfl⟩`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (⟨c i, hc i (Set.mem_univ _)⟩ : v.adicCompletionIntegers F) (inclR_mem_oev v (s i))`. Rewrite using `[e]`.

Conclude with `(isCompact_univ_pi fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).image (continuous_finsetSum _ fun i _ => by fun_prop)`.
-/
theorem isCompact_oev : IsCompact (OEv (E := E) v) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  set g : Fin m → Fv F v ⊗[F] E := fun i => inclR (F := F) (Fv F v) ((s i : 𝓞 E) : E) with hg
  have e : OEv (E := E) v = (fun c : Fin m → Fv F v => ∑ i, c i • g i) ''
      Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext z
    constructor
    · intro hz
      have h1 : z ∈ Submodule.span (v.adicCompletionIntegers F) (Set.range g) := by
        refine (Submodule.span_le.2 ?_) hz
        rintro _ ⟨x, _, rfl⟩
        have hx : x ∈ Submodule.span ℤ (Set.range s) := by rw [hs]; exact Submodule.mem_top
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨i, rfl⟩ := hy
          exact Submodule.subset_span ⟨i, rfl⟩
        | zero => simpa using Submodule.zero_mem _
        | add p q _ _ hp hq =>
          have e1 : inclR (F := F) (Fv F v) (((p + q : 𝓞 E)) : E) =
              inclR (F := F) (Fv F v) (p : E) + inclR (F := F) (Fv F v) (q : E) := by
            rw [← map_add]
            rfl
          show inclR (F := F) (Fv F v) (((p + q : 𝓞 E)) : E) ∈ _
          rw [e1]
          exact Submodule.add_mem _ (hp trivial) (hq trivial)
        | smul r p _ hp =>
          have e1 : inclR (F := F) (Fv F v) (((r • p : 𝓞 E)) : E) =
              r • inclR (F := F) (Fv F v) (p : E) := by
            rw [show ((r • p : 𝓞 E) : E) = r • (p : E) from map_zsmul (algebraMap (𝓞 E) E) r p,
              map_zsmul]
          show inclR (F := F) (Fv F v) (((r • p : 𝓞 E)) : E) ∈ _
          rw [e1]
          exact zsmul_mem (hp trivial) r
      rw [Submodule.mem_span_range_iff_exists_fun] at h1
      obtain ⟨c, rfl⟩ := h1
      exact ⟨fun i => (c i : Fv F v), fun i _ => (c i).2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ (⟨c i, hc i (Set.mem_univ _)⟩ : v.adicCompletionIntegers F)
          (inclR_mem_oev v (s i))
  rw [e]
  exact (isCompact_univ_pi fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).image
    (continuous_finsetSum _ fun i _ => by fun_prop)

variable (σ : E →ₐ[F] E)

/- English proof (translation)
Use extensionality with `S`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite `h` using `[SetLike.mem_coe, mem_HO]`. Conclude with `fun i _ j _ => h i j`.

Introduce `h`. Rewrite using `[SetLike.mem_coe, mem_HO]`. Conclude with `fun i j => h i (Set.mem_univ _) j (Set.mem_univ _)`.
-/
theorem coe_HO (a : ℕ) : (HO σ v a : Set (HermR (Fv F v) σ a)) =
    Subtype.val ⁻¹' (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin a => OEv (E := E) v) := by
  ext S
  constructor
  · intro h
    rw [SetLike.mem_coe, mem_HO] at h
    exact fun i _ j _ => h i j
  · intro h
    rw [SetLike.mem_coe, mem_HO]
    exact fun i j => h i (Set.mem_univ _) j (Set.mem_univ _)

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Establish `hK : IsCompact (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin a => OEv (E` using `E) v) := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_oev v`. Use `locallyCompact_Fv F v` as an intermediate fact. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[coe_HO]`.

Conclude with `(isClosed_HermR (Fv F v) σ a).isClosedEmbedding_subtypeVal.isCompact_preimage hK`. Rewrite using `[coe_HO]`. Conclude with `(isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_oev v).preimage continuous_subtype_val`.
-/
theorem topH_holds (a : ℕ) : TopH σ v a := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin a => OEv (E := E) v) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_oev v
  have := locallyCompact_Fv F v
  refine ⟨?_, ?_⟩
  · rw [coe_HO]
    exact (isClosed_HermR (Fv F v) σ a).isClosedEmbedding_subtypeVal.isCompact_preimage hK
  · rw [coe_HO]
    exact (isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_set_pi Set.finite_univ fun _ _ => isOpen_oev v).preimage continuous_subtype_val

end Top

end PI.OmLocU

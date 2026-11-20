import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicCompactDensity.ExistsNatLocal

noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
  IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct Matrix

section Adele

variable (F : Type) [Field F] [NumberField F]

/- English proof (translation)
Use `show Continuous fun y : InfiniteAdeleRing F => ∏ v, ‖y v‖ ^ v.mult`. Conclude with `continuous_finsetProd _ fun v _ => ((continuous_apply v).norm).pow _`.
-/
theorem continuous_norm_inf : Continuous fun y : InfiniteAdeleRing F => ‖y‖ := by
  show Continuous fun y : InfiniteAdeleRing F => ∏ v, ‖y v‖ ^ v.mult
  exact continuous_finsetProd _ fun v _ => ((continuous_apply v).norm).pow _

def nbhdA : Set (AF F) := {x | ‖x.1‖ < 1 ∧ x.2 ∈ PI.AdCpctDenWork.intAd F}

/- English proof (translation)
The claim follows from `(isOpen_lt ((continuous_norm_inf F).comp continuous_fst) continuous_const).inter (PI.AdCpctDenWork.isOpen_intAd.preimage continuous_snd)`.
-/
theorem isOpen_nbhdA : IsOpen (nbhdA F) :=
  (isOpen_lt ((continuous_norm_inf F).comp continuous_fst) continuous_const).inter
    (PI.AdCpctDenWork.isOpen_intAd.preimage continuous_snd)

/- English proof (translation)
Take `⟨h1, h2⟩` from `hf`. Establish `hint : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F f ≤ 1`. Introduce `v`. Rewrite using `[← valuedAdicCompletion_eq_valuation', ← mem_adicCompletionIntegers]`. Establish `h3 : (algebraMap F (FiniteAdeleRing (𝓞 F) F) f) v ∈ v.adicCompletionIntegers F` using `h2 v`.

Rewrite `h3` using `[FiniteAdeleRing.algebraMap_apply]`. Conclude with `h3`. Take `⟨r, hr⟩` from `mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) _ hint`. Establish `h4 : ‖algebraMap F (InfiniteAdeleRing F) f‖ < 1` using `h1`. Rewrite `h4` using `[InfiniteAdeleRing.coe_norm_eq_abs_norm]`.

Assume the negation of the conclusion as `hf0`. Establish `hr0 : r ≠ 0`. Introduce and unpack `rfl`. Apply `hf0` to reduce the goal to its premises. Rewrite using `[← hr, map_zero]`.

Establish `h5 : (1 : ℚ) ≤ |Algebra.norm ℚ ((r : 𝓞 F) : F)|`. Use `Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr hr0)` as an intermediate fact. Rewrite using `[← Algebra.coe_norm_int]`. Conclude with `this` after adjusting the coercions. Establish `h6 : ((r : 𝓞 F) : F) = f` using `hr`.

Rewrite `h5` using `[h6]`. Establish `h4' : |Algebra.norm ℚ f| < 1` using `by exact_mod_cast h4`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eq_zero_of_mem_nbhdA (f : F) (hf : algebraMap F (AF F) f ∈ nbhdA F) : f = 0 := by
  obtain ⟨h1, h2⟩ := hf
  have hint : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F f ≤ 1 := by
    intro v
    rw [← valuedAdicCompletion_eq_valuation', ← mem_adicCompletionIntegers]
    have h3 : (algebraMap F (FiniteAdeleRing (𝓞 F) F) f) v ∈ v.adicCompletionIntegers F := h2 v
    rw [FiniteAdeleRing.algebraMap_apply] at h3
    exact h3
  obtain ⟨r, hr⟩ := mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) _ hint
  have h4 : ‖algebraMap F (InfiniteAdeleRing F) f‖ < 1 := h1
  rw [InfiniteAdeleRing.coe_norm_eq_abs_norm] at h4
  by_contra hf0
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hf0
    rw [← hr, map_zero]
  have h5 : (1 : ℚ) ≤ |Algebra.norm ℚ ((r : 𝓞 F) : F)| := by
    have := Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr hr0)
    rw [← Algebra.coe_norm_int]
    exact_mod_cast this
  have h6 : ((r : 𝓞 F) : F) = f := hr
  rw [h6] at h5
  have h4' : |Algebra.norm ℚ f| < 1 := by exact_mod_cast h4
  linarith

/- English proof (translation)
Establish `h : algebraMap F (AF F) 0 ∈ nbhdA F`. Use `⟨?_, fun v => ?_⟩` and prove the remaining obligations. Use `show ‖algebraMap F (InfiniteAdeleRing F) 0‖ < 1`. Rewrite using `[InfiniteAdeleRing.coe_norm_eq_abs_norm]`. Simplify using the standard rewrite rules.

Use `show (algebraMap F (FiniteAdeleRing (𝓞 F) F) 0) v ∈ v.adicCompletionIntegers F`. Rewrite using `[map_zero]`. Conclude with `zero_mem _`. Rewrite `h` using `[map_zero]`. Then use the resulting hypothesis.
-/
theorem zero_mem_nbhdA : (0 : AF F) ∈ nbhdA F := by
  have h : algebraMap F (AF F) 0 ∈ nbhdA F := by
    refine ⟨?_, fun v => ?_⟩
    · show ‖algebraMap F (InfiniteAdeleRing F) 0‖ < 1
      rw [InfiniteAdeleRing.coe_norm_eq_abs_norm]
      simp
    · show (algebraMap F (FiniteAdeleRing (𝓞 F) F) 0) v ∈ v.adicCompletionIntegers F
      rw [map_zero]
      exact zero_mem _
  rwa [map_zero] at h

end Adele

section Tens

variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [Module.Finite F E]

/- English proof (translation)
Use `haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩`. Set `b` to `Module.finBasis F E`. Set `B` to `Algebra.TensorProduct.basis (AF F) b`. Use `⟨⋂ i, (B.coord i) ⁻¹' nbhdA F, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `isOpen_iInter_of_finite fun i => (isOpen_nbhdA F).preimage (IsModuleTopology.continuous_of_linearMap (B.coord i))`.

Simplify using `only [Set.mem_iInter, Set.mem_preimage, map_zero]`. Conclude with `fun _ => zero_mem_nbhdA F`. Introduce `e he`. Simplify using `only [Set.mem_iInter, Set.mem_preimage] at he`. Establish `hc : ∀ i, b.repr e i = 0`.

Introduce `i`. Apply `eq_zero_of_mem_nbhdA F` to reduce the goal to its premises. Use `he i` as an intermediate fact. Establish `hco : B.coord i (inclR (F` using `F) (AF F) e) = algebraMap F (AF F) (b.repr e i) := by`. Simplify using `[B, inclR, Module.Basis.coord_apply, Algebra.TensorProduct.basis_repr_tmul]`.

Rewrite `this` using `[hco]`. Then use the resulting hypothesis. Establish `: b.repr e = 0` using `Finsupp.ext hc`. Simplify using `using this`.
-/
theorem exists_nbhd_tens : ∃ U : Set (AF F ⊗[F] E), IsOpen U ∧ (0 : AF F ⊗[F] E) ∈ U ∧
    ∀ e : E, inclR (F := F) (AF F) e ∈ U → e = 0 := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  let b := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (AF F) b
  refine ⟨⋂ i, (B.coord i) ⁻¹' nbhdA F, ?_, ?_, ?_⟩
  · exact isOpen_iInter_of_finite fun i =>
      (isOpen_nbhdA F).preimage (IsModuleTopology.continuous_of_linearMap (B.coord i))
  · simp only [Set.mem_iInter, Set.mem_preimage, map_zero]
    exact fun _ => zero_mem_nbhdA F
  · intro e he
    simp only [Set.mem_iInter, Set.mem_preimage] at he
    have hc : ∀ i, b.repr e i = 0 := by
      intro i
      apply eq_zero_of_mem_nbhdA F
      have := he i
      have hco : B.coord i (inclR (F := F) (AF F) e) = algebraMap F (AF F) (b.repr e i) := by
        simp [B, inclR, Module.Basis.coord_apply, Algebra.TensorProduct.basis_repr_tmul]
      rwa [hco] at this
    have : b.repr e = 0 := Finsupp.ext hc
    simpa using this

end Tens

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J _`. Use `haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)`. Take `⟨h1, -, -, -⟩` from `hT F E`. Prove the components needed by the constructor for the conclusion. Use `haveI : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable haveI : Countable (Matrix (Fin M) (Fin M) E) := inferInstanceAs (Countable (Fin M → Fin M → E)) haveI : Countable (GL (Fin M) E) := (Units.val_injective (α := Matrix (Fin M) (Fin M) E)).countable`.

Establish `hS : (HFin (AF F) σ J : Set (GL (Fin M) (AF F ⊗[F] E))).Countable`. Rewrite using `[HFin, Subgroup.coe_map]`. Conclude with `(Set.to_countable _).image _`. Use `haveI : Countable (HFin (AF F) σ J) := hS.to_subtype`. Set `φ : HFinIn (AF F) σ J → HFin (AF F) σ J` to `fun x => ⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2⟩`.

Establish `hφ : Function.Injective φ`. Introduce `x y h`. Simplify using `only [φ, Subtype.mk.injEq] at h`. Conclude with `Subtype.ext (Subtype.ext h)`. Conclude with `hφ.countable`.

Take `⟨U, hUo, hU0, hUe⟩` from `exists_nbhd_tens F E`. Rewrite using `[discreteTopology_iff_isOpen_singleton]`. Introduce `x`. Take `⟨γ, -, hγ⟩` from `Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 x.2)`. Set `V : Set (HR (AF F) σ J)` to `{g | ∀ i j, ((g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j - ((x.1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j ∈ U}`.

Establish `hVo : IsOpen V`. Establish `hc : Continuous fun g : HR (AF F) σ J => ((g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))` using `Units.continuous_val.comp continuous_subtype_val`. Establish `: V = ⋂ i, ⋂ j, (fun g : HR (AF F) σ J => ((g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j - ((x.1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j) ⁻¹' U`. Use extensionality with `g`. Simplify using `[V]`.

Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hUo.preimage (((continuous_apply j).comp ((continuous_apply i).comp hc)).sub continuous_const)`. Rewrite using `[isOpen_induced_iff]`. Use `⟨V, hVo, Set.ext fun y => ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce `hy`. Take `⟨δ, -, hδ⟩` from `Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 y.2)`. Establish `hent : ∀ i j, (δ : Matrix (Fin M) (Fin M) E) i j = (γ : Matrix (Fin M) (Fin M) E) i j`. Introduce `i j`.

Establish `h` using `hy i j`. Rewrite `h` using `[← hδ, ← hγ]`. Establish `h' : inclR (F` using `F) (AF F) ((δ : Matrix (Fin M) (Fin M) E) i j - (γ : Matrix (Fin M) (Fin M) E) i j) ∈ U := by`. Rewrite using `[map_sub]`. Conclude with `h`.

Conclude with `sub_eq_zero.1 (hUe _ h')`. Establish `hm : δ = γ` using `Units.ext (Matrix.ext hent)`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hδ, ← hγ, hm]`.

Introduce and unpack `rfl i j`. Simplify using `only [sub_self]`. Conclude with `hU0`.
-/
theorem discHA_of (hT : TensTop) : DiscHA := by
  intro F E _ _ _ _ _ σ hCM M J _
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨h1, -, -, -⟩ := hT F E
  constructor
  · haveI : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
    haveI : Countable (Matrix (Fin M) (Fin M) E) := inferInstanceAs (Countable (Fin M → Fin M → E))
    haveI : Countable (GL (Fin M) E) :=
      (Units.val_injective (α := Matrix (Fin M) (Fin M) E)).countable
    have hS : (HFin (AF F) σ J : Set (GL (Fin M) (AF F ⊗[F] E))).Countable := by
      rw [HFin, Subgroup.coe_map]
      exact (Set.to_countable _).image _
    haveI : Countable (HFin (AF F) σ J) := hS.to_subtype
    let φ : HFinIn (AF F) σ J → HFin (AF F) σ J := fun x => ⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2⟩
    have hφ : Function.Injective φ := by
      intro x y h
      simp only [φ, Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext h)
    exact hφ.countable
  · obtain ⟨U, hUo, hU0, hUe⟩ := exists_nbhd_tens F E
    rw [discreteTopology_iff_isOpen_singleton]
    intro x
    obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 x.2)
    let V : Set (HR (AF F) σ J) := {g | ∀ i j,
      ((g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j -
        ((x.1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j ∈ U}
    have hVo : IsOpen V := by
      have hc : Continuous fun g : HR (AF F) σ J =>
          ((g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :=
        Units.continuous_val.comp continuous_subtype_val
      have : V = ⋂ i, ⋂ j, (fun g : HR (AF F) σ J =>
          ((g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j -
            ((x.1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j) ⁻¹' U := by
        ext g
        simp [V]
      rw [this]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        hUo.preimage (((continuous_apply j).comp ((continuous_apply i).comp hc)).sub
          continuous_const)
    rw [isOpen_induced_iff]
    refine ⟨V, hVo, Set.ext fun y => ?_⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hy
      obtain ⟨δ, -, hδ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 y.2)
      have hent : ∀ i j, (δ : Matrix (Fin M) (Fin M) E) i j = (γ : Matrix (Fin M) (Fin M) E) i j := by
        intro i j
        have h := hy i j
        rw [← hδ, ← hγ] at h
        have h' : inclR (F := F) (AF F) ((δ : Matrix (Fin M) (Fin M) E) i j -
            (γ : Matrix (Fin M) (Fin M) E) i j) ∈ U := by
          rw [map_sub]
          exact h
        exact sub_eq_zero.1 (hUe _ h')
      have hm : δ = γ := Units.ext (Matrix.ext hent)
      apply Subtype.ext
      apply Subtype.ext
      rw [← hδ, ← hγ, hm]
    · rintro rfl i j
      simp only [sub_self]
      exact hU0

end PI.VolSemiDirect.W

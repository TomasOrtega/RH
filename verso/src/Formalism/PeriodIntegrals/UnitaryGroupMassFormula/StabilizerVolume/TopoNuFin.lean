import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoAF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosNear
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExStabSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoMeas

noncomputable section

namespace PI.VolStabS.TopoNuFin

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Filter Topology
  PI.VolFromSW PI.VolStabS.PositiveNearLattice
open scoped TensorProduct ENNReal

section Adele

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Set `U : Set (Af F)` to `{y | ∀ v, y v ∈ v.adicCompletionIntegers F}`. Establish `hU : IsOpen U` using `RestrictedProduct.isOpen_forall_mem (fun v => PI.VolStabS.TopoAF.isOpen_integers (F := F) v)`. Establish `h0 : (0 : Af F) ∈ U` using `fun v => zero_mem _`. Take `⟨t, ht⟩` from `hC.elim_finite_subcover (fun x : C => (fun y => y - (x : Af F)) ⁻¹' U) (fun x => hU.preimage (continuous_sub_right _)) (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, by simpa using h0⟩)`. Establish `hfin : ∀ᶠ v in cofinite, ∀ i ∈ t, ((i : C) : Af F) v ∈ v.adicCompletionIntegers F` using `(Filter.eventually_all_finset t).mpr fun i _ => i.1.2`.

Use `filter_upwards [hfin] with v hv x hx`. Take `⟨i, hi, hxi⟩` from `Set.mem_iUnion₂.mp (ht hx)`. Establish `h1 : (x - (i : Af F)) v ∈ v.adicCompletionIntegers F` using `hxi v`. Establish `h2` using `hv i hi`. Establish `he : x v = (x - (i : Af F)) v + (i : Af F) v` using `by first`.

Consider the case `(rw [RestrictedProduct.sub_apply]; ring)`. Consider the case `(show x v = (x v - (i : Af F) v) + (i : Af F) v; ring)`. Rewrite using `[he]`. Conclude with `add_mem h1 h2`.
-/
theorem eventually_int_of_compact {C : Set (Af F)} (hC : IsCompact C) :
    ∀ᶠ v in cofinite, ∀ x ∈ C, x v ∈ v.adicCompletionIntegers F := by
  classical
  let U : Set (Af F) := {y | ∀ v, y v ∈ v.adicCompletionIntegers F}
  have hU : IsOpen U :=
    RestrictedProduct.isOpen_forall_mem (fun v => PI.VolStabS.TopoAF.isOpen_integers (F := F) v)
  have h0 : (0 : Af F) ∈ U := fun v => zero_mem _
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun x : C => (fun y => y - (x : Af F)) ⁻¹' U)
    (fun x => hU.preimage (continuous_sub_right _))
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, by simpa using h0⟩)
  have hfin : ∀ᶠ v in cofinite, ∀ i ∈ t, ((i : C) : Af F) v ∈ v.adicCompletionIntegers F :=
    (Filter.eventually_all_finset t).mpr fun i _ => i.1.2
  filter_upwards [hfin] with v hv x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
  have h1 : (x - (i : Af F)) v ∈ v.adicCompletionIntegers F := hxi v
  have h2 := hv i hi
  have he : x v = (x - (i : Af F)) v + (i : Af F) v := by
    first
    | (rw [RestrictedProduct.sub_apply]; ring)
    | (show x v = (x v - (i : Af F) v) + (i : Af F) v; ring)
  rw [he]
  exact add_mem h1 h2

end Adele

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Simplify using `only [latV, Set.mem_setOf_eq, Pi.zero_apply, map_zero, Finsupp.zero_apply]`. Conclude with `fun _ _ _ => zero_mem _`.
-/
theorem zero_mem_latV (a M : ℕ) : (0 : Fin a → Fin M → Fv F v ⊗[F] E) ∈ latV b v := by

  simp only [latV, Set.mem_setOf_eq, Pi.zero_apply, map_zero, Finsupp.zero_apply]
  exact fun _ _ _ => zero_mem _

include b in

/- English proof (translation)
Set `L` to `latV (M := M) (n := a) b v`. Establish `hLo` using `isClopen_latV b v a M`. Establish `hLc` using `isCompact_latV b v a M`. Set `tr : (Fin a → Fin M → Fv F v ⊗[F] E) → Set (Fin a → Fin M → Fv F v ⊗[F] E)` to `fun y => (Homeomorph.subRight y) ⁻¹' L`. Take `⟨t, ht⟩` from `hK.elim_finite_subcover (fun y : K => tr (y : Fin a → Fin M → Fv F v ⊗[F] E)) (fun y => hLo.isOpen.preimage (Homeomorph.subRight _).continuous) (fun z hz => Set.mem_iUnion.2 ⟨⟨z, hz⟩, by show z - z ∈ L`.

Rewrite using `[sub_self]`. Conclude with `zero_mem_latV b v a M⟩)`. Use `⟨⋃ y ∈ t, tr (y : Fin a → Fin M → Fv F v ⊗[F] E), ?_, ?_, ht⟩` and prove the remaining obligations. Conclude with `isClopen_biUnion_finset fun y _ => hLo.preimage (Homeomorph.subRight _).continuous`. Conclude with `t.isCompact_biUnion fun y _ => (Homeomorph.subRight _).isCompact_preimage.2 hLc`.
-/
theorem exists_clopen_compact {a M : ℕ} {K : Set (Fin a → Fin M → Fv F v ⊗[F] E)}
    (hK : IsCompact K) : ∃ C, IsClopen C ∧ IsCompact C ∧ K ⊆ C := by
  classical
  let L := latV (M := M) (n := a) b v
  have hLo := isClopen_latV b v a M
  have hLc := isCompact_latV b v a M
  let tr : (Fin a → Fin M → Fv F v ⊗[F] E) → Set (Fin a → Fin M → Fv F v ⊗[F] E) :=
    fun y => (Homeomorph.subRight y) ⁻¹' L
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y : K => tr (y : Fin a → Fin M → Fv F v ⊗[F] E))
    (fun y => hLo.isOpen.preimage (Homeomorph.subRight _).continuous)
    (fun z hz => Set.mem_iUnion.2 ⟨⟨z, hz⟩, by
      show z - z ∈ L
      rw [sub_self]
      exact zero_mem_latV b v a M⟩)
  refine ⟨⋃ y ∈ t, tr (y : Fin a → Fin M → Fv F v ⊗[F] E), ?_, ?_, ht⟩
  · exact isClopen_biUnion_finset fun y _ => hLo.preimage (Homeomorph.subRight _).continuous
  · exact t.isCompact_biUnion fun y _ => (Homeomorph.subRight _).isCompact_preimage.2 hLc

end Local

end PI.VolStabS.TopoNuFin

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Filter Topology
  PI.VolFromSW PI.VolStabS.PositiveNearLattice PI.VolStabS.TopoNuFin
open scoped TensorProduct ENNReal

/- English proof (translation)
Take `⟨⟨μinf, hμinf⟩, h1⟩` from `hν.2`. Take `⟨⟨νinf, hνinf⟩, h2⟩` from `h1 μinf hμinf`. Take `⟨⟨μv, hμv⟩, h3⟩` from `h2 νinf hνinf`. Take `⟨⟨νv, hνv⟩, h4⟩` from `h3 μv hμv`. Take `⟨⟨fibInf, hfi⟩, h5⟩` from `h4 νv hνv`.

Take `⟨⟨fibV, hfv⟩, h6⟩` from `h5 fibInf hfi`. Establish `key` using `h6 fibV hfv`. Set `b` to `Module.finBasis F E`. Establish `hKi : IsCompact (projInf '' K)` using `hK.image (continuous_projInf b)`. Take `⟨f, hf1, -, hfc, -⟩` from `exists_continuous_one_zero_of_isCompact hKi isClosed_empty (Set.disjoint_empty _)`.

Set `Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ` to `fun Y => ((f Y : ℝ) : ℂ)`. Establish `hΦic : Continuous Φinf` using `Complex.continuous_ofReal.comp f.continuous`. Establish `hΦis : HasCompactSupport Φinf` using `hfc.comp_left Complex.ofReal_zero`. Establish `hKf : IsCompact (projFin '' K)` using `hK.image (continuous_projFin b)`. Set `Kv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin a → Fin M → Fv F v ⊗[F] E)` to `fun v => projV v '' (projFin '' K)`.

Establish `hKv : ∀ v, IsCompact (Kv v)` using `fun v => hKf.image (TopoMeas.continuous_projV b v)`. Establish `hev : ∀ᶠ v in cofinite, Kv v ⊆ latV b v`. Establish `h` using `fun (x : Fin a) (i : Fin M) (k : Fin (Module.finrank F E)) => eventually_int_of_compact (hKf.image (f := fun Y : Fin a → Fin M → Af F ⊗[F] E => crd b (Af F) (Y x i) k) ((continuous_crd b (Af F) k).comp ((continuous_apply i).comp (continuous_apply x))))`. Use `filter_upwards [eventually_all.2 fun x => eventually_all.2 fun i => eventually_all.2 fun k => h x i k] with v hv`. Introduce and unpack `_ ⟨Y, hY, rfl⟩ x i k`.

Establish `e` using `crd_map b (evalV F v) (Y x i) k`. Express the relevant statement in the definitionally equal form `crd b (Fv F v) (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) (Y x i)) k ∈ _`. Rewrite using `[e]`. Conclude with `hv x i k _ ⟨Y, hY, rfl⟩`. Use `choose C hCo hCc hKC using fun v => exists_clopen_compact b v (hKv v)`.

Set `Cv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin a → Fin M → Fv F v ⊗[F] E)` to `fun v => if Kv v ⊆ latV b v then latV b v else C v`. Establish `hCvo : ∀ v, IsClopen (Cv v)` using `fun v => by`. Distinguish the cases in `h : Kv v ⊆ latV b v`. Rewrite using `[show Cv v = latV b v from if_pos h]`. Conclude with `isClopen_latV b v a M`.

Rewrite using `[show Cv v = C v from if_neg h]`. Conclude with `hCo v`. Establish `hCvc : ∀ v, IsCompact (Cv v)` using `fun v => by`. Distinguish the cases in `h : Kv v ⊆ latV b v`. Rewrite using `[show Cv v = latV b v from if_pos h]`.

Conclude with `isCompact_latV b v a M`. Rewrite using `[show Cv v = C v from if_neg h]`. Conclude with `hCc v`. Establish `hKCv : ∀ v, Kv v ⊆ Cv v` using `fun v => by`. Distinguish the cases in `h : Kv v ⊆ latV b v`.

Rewrite using `[show Cv v = latV b v from if_pos h]`. Conclude with `h`. Rewrite using `[show Cv v = C v from if_neg h]`. Conclude with `hKC v`. Set `Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ` to `fun v => (Cv v).indicator 1`.

Set `Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ` to `fun Y => ∏ᶠ v, Φv v (projV v Y)`. Set `Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ` to `fun X => Φinf (projInf X) * Φf (projFin X)`. Establish `hSB : ∀ v, IsSB (Φv v)` using `fun v => ⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) (hCvo v)).isLocallyConstant, HasCompactSupport.intro' (hCvc v) (hCvo v).isClosed fun Y hY => Set.indicator_of_notMem hY _⟩`. Establish `hpure : IsPureFin b Φf Φv`. Use `⟨hSB, ?_, fun _ => rfl⟩` and prove the remaining obligations.

Use `filter_upwards [hev] with v hv`. Simplify using `only [Φv, Cv, hv, if_true]`. Take `⟨hint, -, -⟩` from `key _ b Φ Φinf Φf Φv hΦic hΦis hpure (fun _ => rfl)`. Establish `hone : ∀ X ∈ K, Φ X = 1`. Introduce `X hX`.

Establish `h1 : Φinf (projInf X) = 1`. Simplify using `only [Φinf, hf1 ⟨X, hX, rfl⟩, Pi.one_apply, Complex.ofReal_one]`. Establish `h2 : Φf (projFin X) = 1`. Use `finprod_eq_one_of_forall_eq_one fun v => ?_` and prove the remaining obligations. Conclude with `Set.indicator_of_mem (hKCv v ⟨projFin X, ⟨X, hX, rfl⟩, rfl⟩) _`.

Simplify using `only [Φ, h1, h2, mul_one]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[hone X hX]`. Use `_ ≤ ∫⁻ X, ‖Φ X‖ₑ ∂νX := by`. Use `mul_meas_ge_le_lintegral₀ hint.aestronglyMeasurable.enorm 1` as an intermediate fact.

Simplify using `using this`. Use `_ < ⊤ := hint.2`.
-/
theorem nuFin_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (T : Matrix (Fin a) (Fin a) E) (hT : ∀ i j, σ (T j i) = T i j) (ψ : AddChar (AF F) ℂ)
    (νX : Measure (Fin a → Fin M → AF F ⊗[F] E)) (hν : IsOmT F E σ M J ψ T hT νX)
    (K : Set (Fin a → Fin M → AF F ⊗[F] E)) (hK : IsCompact K) : νX K < ⊤ := by
  classical
  obtain ⟨⟨μinf, hμinf⟩, h1⟩ := hν.2
  obtain ⟨⟨νinf, hνinf⟩, h2⟩ := h1 μinf hμinf
  obtain ⟨⟨μv, hμv⟩, h3⟩ := h2 νinf hνinf
  obtain ⟨⟨νv, hνv⟩, h4⟩ := h3 μv hμv
  obtain ⟨⟨fibInf, hfi⟩, h5⟩ := h4 νv hνv
  obtain ⟨⟨fibV, hfv⟩, h6⟩ := h5 fibInf hfi
  have key := h6 fibV hfv
  let b := Module.finBasis F E

  have hKi : IsCompact (projInf '' K) := hK.image (continuous_projInf b)
  obtain ⟨f, hf1, -, hfc, -⟩ :=
    exists_continuous_one_zero_of_isCompact hKi isClosed_empty (Set.disjoint_empty _)
  let Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ := fun Y => ((f Y : ℝ) : ℂ)
  have hΦic : Continuous Φinf := Complex.continuous_ofReal.comp f.continuous
  have hΦis : HasCompactSupport Φinf := hfc.comp_left Complex.ofReal_zero

  have hKf : IsCompact (projFin '' K) := hK.image (continuous_projFin b)
  let Kv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin a → Fin M → Fv F v ⊗[F] E) :=
    fun v => projV v '' (projFin '' K)
  have hKv : ∀ v, IsCompact (Kv v) := fun v => hKf.image (TopoMeas.continuous_projV b v)
  have hev : ∀ᶠ v in cofinite, Kv v ⊆ latV b v := by
    have h := fun (x : Fin a) (i : Fin M) (k : Fin (Module.finrank F E)) =>
      eventually_int_of_compact (hKf.image
        (f := fun Y : Fin a → Fin M → Af F ⊗[F] E => crd b (Af F) (Y x i) k)
        ((continuous_crd b (Af F) k).comp ((continuous_apply i).comp (continuous_apply x))))
    filter_upwards [eventually_all.2 fun x => eventually_all.2 fun i => eventually_all.2 fun k =>
      h x i k] with v hv
    rintro _ ⟨Y, hY, rfl⟩ x i k
    have e := crd_map b (evalV F v) (Y x i) k
    change crd b (Fv F v) (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) (Y x i)) k ∈ _
    rw [e]
    exact hv x i k _ ⟨Y, hY, rfl⟩
  choose C hCo hCc hKC using fun v => exists_clopen_compact b v (hKv v)
  let Cv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin a → Fin M → Fv F v ⊗[F] E) :=
    fun v => if Kv v ⊆ latV b v then latV b v else C v
  have hCvo : ∀ v, IsClopen (Cv v) := fun v => by
    by_cases h : Kv v ⊆ latV b v
    · rw [show Cv v = latV b v from if_pos h]; exact isClopen_latV b v a M
    · rw [show Cv v = C v from if_neg h]; exact hCo v
  have hCvc : ∀ v, IsCompact (Cv v) := fun v => by
    by_cases h : Kv v ⊆ latV b v
    · rw [show Cv v = latV b v from if_pos h]; exact isCompact_latV b v a M
    · rw [show Cv v = C v from if_neg h]; exact hCc v
  have hKCv : ∀ v, Kv v ⊆ Cv v := fun v => by
    by_cases h : Kv v ⊆ latV b v
    · rw [show Cv v = latV b v from if_pos h]; exact h
    · rw [show Cv v = C v from if_neg h]; exact hKC v
  let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ :=
    fun v => (Cv v).indicator 1
  let Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ := fun Y => ∏ᶠ v, Φv v (projV v Y)
  let Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ := fun X => Φinf (projInf X) * Φf (projFin X)
  have hSB : ∀ v, IsSB (Φv v) := fun v =>
    ⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) (hCvo v)).isLocallyConstant,
      HasCompactSupport.intro' (hCvc v) (hCvo v).isClosed fun Y hY => Set.indicator_of_notMem hY _⟩
  have hpure : IsPureFin b Φf Φv := by
    refine ⟨hSB, ?_, fun _ => rfl⟩
    filter_upwards [hev] with v hv
    simp only [Φv, Cv, hv, if_true]
  obtain ⟨hint, -, -⟩ := key _ b Φ Φinf Φf Φv hΦic hΦis hpure (fun _ => rfl)
  have hone : ∀ X ∈ K, Φ X = 1 := by
    intro X hX
    have h1 : Φinf (projInf X) = 1 := by
      simp only [Φinf, hf1 ⟨X, hX, rfl⟩, Pi.one_apply, Complex.ofReal_one]
    have h2 : Φf (projFin X) = 1 := by
      refine finprod_eq_one_of_forall_eq_one fun v => ?_
      exact Set.indicator_of_mem (hKCv v ⟨projFin X, ⟨X, hX, rfl⟩, rfl⟩) _
    simp only [Φ, h1, h2, mul_one]
  calc νX K ≤ νX {X | 1 ≤ ‖Φ X‖ₑ} := measure_mono fun X hX => by
        simp [hone X hX]
    _ ≤ ∫⁻ X, ‖Φ X‖ₑ ∂νX := by
        have := mul_meas_ge_le_lintegral₀ hint.aestronglyMeasurable.enorm 1
        simpa using this
    _ < ⊤ := hint.2

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ h1 h2 a ha haM X0 hT hdet ψ hψ νX hν K hK`. Use `haveI : FiniteDimensional F E := by first`. Consider the case `infer_instance`. Consider the case `exact Module.Finite.of_restrictScalars_finite ℚ F E`. Consider the case `exact FiniteDimensional.right ℚ F E`.

Conclude with `nuFin_gen σ J (gramE σ J X0) hT ψ νX hν K hK`.
-/
theorem nuFin_holds : NuFin := by

  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a ha haM X0 hT hdet ψ hψ νX hν K hK
  haveI : FiniteDimensional F E := by
    first
    | infer_instance
    | exact Module.Finite.of_restrictScalars_finite ℚ F E
    | exact FiniteDimensional.right ℚ F E
  exact nuFin_gen σ J (gramE σ J X0) hT ψ νX hν K hK

end PI.VolStabS

import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.MassDataKppVolOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.LocIdxLift
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StKHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.HaarIdx

noncomputable section

namespace PI.MassDataKppVolLemmas

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Topology
open scoped ENNReal TensorProduct

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

def LevelSubgroupOfCharacter (hK : X.LevelSubgroupCharacter) : Subgroup X.B.I.Gf where
  carrier := X.K2
  one_mem' := hK.1
  mul_mem' := fun ha hb' => hK.2.1 _ ha _ hb'
  inv_mem' := fun ha => hK.2.2.1 _ ha

def LocIdx_Asub (hK : X.LevelSubgroupCharacter) (p : TypX X) : Subgroup (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) :=
  (LevelSubgroupOfCharacter X hK).map ((piV X.B.I p.1).comp (tfHom X.B.I hb))

/- English proof (translation)
Use extensionality with `y`. Simplify using `[LocIdx_Asub, LevelSubgroupOfCharacter, compSet, levelUnitary]`. Discharge the remaining goals by the proof search in `aesop`.
-/
theorem LocIdx_Asub_coe (hK : X.LevelSubgroupCharacter) (p : TypX X) :
    (LocIdx_Asub X hb hK p : Set (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J)) =
      compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1 := by
  ext y
  simp [LocIdx_Asub, LevelSubgroupOfCharacter, compSet, levelUnitary]
  aesop

/- English proof (translation)
Introduce `y hy`. Establish `hy' : y ∈ (LevelSubgroupOfCharacter X hK).map ((piV X.B.I p.1).comp (tfHom X.B.I hb))` using `hy`. Take `⟨x, hx, rfl⟩` from `Subgroup.mem_map.1 hy'`. Establish `hKf : tf X.B.I hb x ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))` using `(Bridge_mem_Kf_iff X.B.I hb x).2 (hL.2.1 x hx)`. Establish `hv` using `(Subgroup.mem_iInf.1 hKf) p.1`.

Rewrite using `[MonoidHom.comp_apply, Bridge_tfHom_apply]`. Conclude with `hv`.
-/
theorem LocIdx_A_le (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized) (p : TypX X) :
    ∀ y ∈ (LocIdx_Asub X hb hK p : Set (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J)),
      y ∈ Kv X.B.I.cm.sig X.B.I.J (lamS X) p.1 := by
  intro y hy
  have hy' : y ∈ (LevelSubgroupOfCharacter X hK).map ((piV X.B.I p.1).comp (tfHom X.B.I hb)) := hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy'
  have hKf : tf X.B.I hb x ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    (Bridge_mem_Kf_iff X.B.I hb x).2 (hL.2.1 x hx)
  have hv := (Subgroup.mem_iInf.1 hKf) p.1
  rw [MonoidHom.comp_apply, Bridge_tfHom_apply]
  exact hv

/- English proof (translation)
Rewrite using `[X.g_eq]`. Conclude with `mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero`.
-/
theorem LocIdx_g_ne : X.B.g ≠ 0 := by
  rw [X.g_eq]
  exact mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

/- English proof (translation)
Introduce `y hy`. Take `⟨x, hxK, hxy⟩` from `LocIdxLift_Kg X.B.I hb p.1 X.B.g (LocIdx_g_ne X) y hy`. Conclude with `(Subgroup.mem_map (f := (piV X.B.I p.1).comp (tfHom X.B.I hb))).2 ⟨x, (hL.1 x hxK).1, by rw [MonoidHom.comp_apply, Bridge_tfHom_apply, hxy]⟩`.
-/
theorem LocIdx_Kg_sub (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized) (p : TypX X) :
    Kgv X.B.I.cm.sig X.B.I.J (lamS X) X.B.g p.1 ⊆
      (LocIdx_Asub X hb hK p : Set (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J)) := by
  intro y hy
  obtain ⟨x, hxK, hxy⟩ := LocIdxLift_Kg X.B.I hb p.1 X.B.g (LocIdx_g_ne X) y hy
  exact (Subgroup.mem_map (f := (piV X.B.I p.1).comp (tfHom X.B.I hb))).2
    ⟨x, (hL.1 x hxK).1, by rw [MonoidHom.comp_apply, Bridge_tfHom_apply, hxy]⟩

/- English proof (translation)
Take `⟨K, hKeq, -, hKc, -⟩` from `MassDataIdxSteps.stK_holds X p`. Use `(MassDataIdxSteps.stTop X p).1` as an intermediate fact. Establish `hle : LocIdx_Asub X hb hK p ≤ K`. Introduce `y hy`. Establish `hy'` using `LocIdx_A_le X hb hK hL p y hy`.

Use `show y ∈ (K : Set (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J))`. Rewrite using `[hKeq]`. Conclude with `hy'`. Take `⟨-, -, -, -, hgo⟩` from `MassDataIdxK.stK_gen p.1 X.B.I.cm.sig X.B.I.J X.B.I.L X.B.I.L_span X.B.I.L_fg X.B.g (LocIdx_g_ne X)`. Establish `h1 : (1 : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ Kgv X.B.I.cm.sig X.B.I.J (lamS X) X.B.g p.1`.

Use `⟨?_, fun y _ => ⟨0, Submodule.zero_mem _, ?_⟩⟩` and prove the remaining obligations. Establish `h1K` using `K.one_mem`. Rewrite `h1K` using `[← SetLike.mem_coe, hKeq]`. Conclude with `h1K`. Rewrite using `[smul_zero] show Matrix.mulVec ((1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) - 1) y = 0`.

Rewrite using `[sub_self, Matrix.zero_mulVec]`. Establish `hAo : IsOpen (LocIdx_Asub X hb hK p : Set (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J))` using `Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hgo.mem_nhds h1) (LocIdx_Kg_sub X hb hK hL p))`. Establish `: CompactSpace K` using `isCompact_iff_compactSpace.1 hKc`. Establish `hUo : IsOpen (((LocIdx_Asub X hb hK p).subgroupOf K : Subgroup K) : Set K)`. Rewrite using `[Subgroup.coe_subgroupOf]`.

Conclude with `hAo.preimage continuous_subtype_val`. Establish `hK1 : ContinuousMul K` using `⟨(continuous_mul.comp (continuous_subtype_val.prodMap continuous_subtype_val)).subtype_mk _⟩`. Establish `hK2 : SeparatelyContinuousMul K` using `inferInstance`. Use `Subgroup.quotient_finite_of_isOpen ((LocIdx_Asub X hb hK p).subgroupOf K) hUo` as an intermediate fact. Conclude with `⟨K, hKeq, hKc, hle, hAo, Subgroup.index_ne_zero_of_finite⟩`.
-/
theorem LocIdx_main (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized) (p : TypX X) :
    ∃ K : Subgroup (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J),
      (K : Set (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J)) = Kv X.B.I.cm.sig X.B.I.J (lamS X) p.1 ∧
      IsCompact (K : Set (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J)) ∧ LocIdx_Asub X hb hK p ≤ K ∧
      IsOpen (LocIdx_Asub X hb hK p : Set (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J)) ∧
      (LocIdx_Asub X hb hK p).relIndex K ≠ 0 := by
  obtain ⟨K, hKeq, -, hKc, -⟩ := MassDataIdxSteps.stK_holds X p
  have := (MassDataIdxSteps.stTop X p).1
  have hle : LocIdx_Asub X hb hK p ≤ K := by
    intro y hy
    have hy' := LocIdx_A_le X hb hK hL p y hy
    show y ∈ (K : Set (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J))
    rw [hKeq]
    exact hy'
  obtain ⟨-, -, -, -, hgo⟩ := MassDataIdxK.stK_gen p.1 X.B.I.cm.sig X.B.I.J X.B.I.L X.B.I.L_span X.B.I.L_fg X.B.g
    (LocIdx_g_ne X)
  have h1 : (1 : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈
      Kgv X.B.I.cm.sig X.B.I.J (lamS X) X.B.g p.1 := by
    refine ⟨?_, fun y _ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
    · have h1K := K.one_mem
      rw [← SetLike.mem_coe, hKeq] at h1K
      exact h1K
    · rw [smul_zero]
      show Matrix.mulVec ((1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) - 1) y = 0
      rw [sub_self, Matrix.zero_mulVec]
  have hAo : IsOpen (LocIdx_Asub X hb hK p : Set (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J)) :=
    Subgroup.isOpen_of_mem_nhds _ (g := 1)
      (Filter.mem_of_superset (hgo.mem_nhds h1) (LocIdx_Kg_sub X hb hK hL p))
  have : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  have hUo : IsOpen (((LocIdx_Asub X hb hK p).subgroupOf K : Subgroup K) : Set K) := by
    rw [Subgroup.coe_subgroupOf]
    exact hAo.preimage continuous_subtype_val
  have hK1 : ContinuousMul K :=
    ⟨(continuous_mul.comp (continuous_subtype_val.prodMap continuous_subtype_val)).subtype_mk _⟩
  have hK2 : SeparatelyContinuousMul K := inferInstance
  have := Subgroup.quotient_finite_of_isOpen ((LocIdx_Asub X hb hK p).subgroupOf K) hUo
  exact ⟨K, hKeq, hKc, hle, hAo, Subgroup.index_ne_zero_of_finite⟩

/- English proof (translation)
Unfold `KppvS`. Rewrite using `[← LocIdx_Asub_coe X hb hK p, Subgroup.closure_eq]`.
-/
theorem LocIdx_KppvS (hK : X.LevelSubgroupCharacter) (p : TypX X) : KppvS X hb p = LocIdx_Asub X hb hK p := by
  unfold KppvS
  rw [← LocIdx_Asub_coe X hb hK p, Subgroup.closure_eq]

/- English proof (translation)
Introduce `D X hb hK _ hL p _`. Take `⟨K, hKeq, -, hle, hAo, hidx⟩` from `LocIdx_main X hb hK hL p`. Use `(MassDataIdxSteps.stTop X p).1` as an intermediate fact. Use `(MassDataIdxSteps.stTop X p).2` as an intermediate fact. Use `X.measG_norm.2.2.2.1 p.1` as an intermediate fact.

Establish `hkv : KvS X p = K`. Unfold `KvS`. Rewrite using `[← hKeq, Subgroup.closure_eq]`. Simplify using `only [lIdx, hkv, LocIdx_KppvS X hb hK p]`. Rewrite using `[← hKeq, ← LocIdx_Asub_coe X hb hK p]`.

Conclude with `MassDataIdxSteps.haarIdx _ (X.measG.μGv p.1) K _ hle hAo hidx`.
-/
theorem locIdxAll : LocIdxAll := by
  intro D X hb hK _ hL p _
  obtain ⟨K, hKeq, -, hle, hAo, hidx⟩ := LocIdx_main X hb hK hL p
  have := (MassDataIdxSteps.stTop X p).1
  have := (MassDataIdxSteps.stTop X p).2
  have := X.measG_norm.2.2.2.1 p.1
  have hkv : KvS X p = K := by
    unfold KvS
    rw [← hKeq, Subgroup.closure_eq]
  simp only [lIdx, hkv, LocIdx_KppvS X hb hK p]
  rw [← hKeq, ← LocIdx_Asub_coe X hb hK p]
  exact MassDataIdxSteps.haarIdx _ (X.measG.μGv p.1) K _ hle hAo hidx

/- English proof (translation)
Introduce `D X hb hK _ hL p`. Take `⟨K, hKeq, hKc, hle, hAo, hidx⟩` from `LocIdx_main X hb hK hL p`. Use `X.measG_norm.2.2.2.1 p.1` as an intermediate fact. Establish `hkv : KvS X p = K`. Unfold `KvS`.

Rewrite using `[← hKeq, Subgroup.closure_eq]`. Rewrite using `[← LocIdx_Asub_coe X hb hK p]`. Use `⟨hAo.measure_pos (X.measG.μGv p.1) ⟨1, (LocIdx_Asub X hb hK p).one_mem⟩, lt_of_le_of_lt (measure_mono (SetLike.coe_subset_coe.2 hle)) hKc.measure_lt_top, ?_⟩` and prove the remaining obligations. Simplify using `only [lIdx, hkv, LocIdx_KppvS X hb hK p]`. Conclude with `hidx`.
-/
theorem locPosAll : LocPosAll := by
  intro D X hb hK _ hL p
  obtain ⟨K, hKeq, hKc, hle, hAo, hidx⟩ := LocIdx_main X hb hK hL p
  have := X.measG_norm.2.2.2.1 p.1
  have hkv : KvS X p = K := by
    unfold KvS
    rw [← hKeq, Subgroup.closure_eq]
  rw [← LocIdx_Asub_coe X hb hK p]
  refine ⟨hAo.measure_pos (X.measG.μGv p.1) ⟨1, (LocIdx_Asub X hb hK p).one_mem⟩,
    lt_of_le_of_lt (measure_mono (SetLike.coe_subset_coe.2 hle)) hKc.measure_lt_top, ?_⟩
  simp only [lIdx, hkv, LocIdx_KppvS X hb hK p]
  exact hidx

end PI.MassDataKppVolLemmas

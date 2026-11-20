import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GaugeVolumeBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionA

noncomputable section

open MeasureTheory Set Topology Formalism.MainNotions.S Formalism.MainNotions.FundamentalDomainUnfolding

namespace Formalism.L2.S.S7.FundamentalDomainSubgroups

variable (I : AutInst)

def kSub : Subgroup I.Gf := (Formalism.UG.stabGL I.Lf).comap (Formalism.UG.UPts I.cm.sig I.J (Af I.F)).subtype

def gamSub (y : I.Gf) : Subgroup I.GA where
  carrier := GamY I y
  one_mem' := ⟨(Formalism.MainNotions.LeviCoordinates.rr_GF I).one_mem, by
    show y⁻¹ * 1 * y ∈ I.Kset
    rw [mul_one, inv_mul_cancel]
    exact (kSub I).one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(Formalism.MainNotions.LeviCoordinates.rr_GF I).mul_mem ha hb, ?_⟩
    have e : y⁻¹ * (a * b).2 * y = (y⁻¹ * a.2 * y) * (y⁻¹ * b.2 * y) := by
      rw [Prod.snd_mul]; group
    rw [e]
    exact (kSub I).mul_mem ha' hb'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(Formalism.MainNotions.LeviCoordinates.rr_GF I).inv_mem ha, ?_⟩
    have e : y⁻¹ * a⁻¹.2 * y = (y⁻¹ * a.2 * y)⁻¹ := by
      rw [Prod.snd_inv]; group
    rw [e]
    exact (kSub I).inv_mem ha'

def gamInf (y : I.Gf) : Subgroup I.Ginf := (gamSub I y).map (MonoidHom.fst I.Ginf I.Gf)

/- English proof (translation)
Take `⟨M, -, hv, hf⟩` from `hγ`. Take `⟨v⟩ : Nonempty (NumberField.InfinitePlace I.F)` from `inferInstance`. Establish `hP : I.P v * (I.P v)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))`. Establish `hP' : (I.P v)⁻¹ * I.P v = 1` using `Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))`. Establish `h` using `hv v`.

Establish `hu : uMat (γ.1 v) = 1` using `by rw [h1]; rfl`. Rewrite `h` using `[hu]`. Establish `hMφ : (M : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = 1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc, hP, Matrix.mul_one]`.

Rewrite using `[← Matrix.mul_assoc, hP, Matrix.one_mul]`. Use `_ = 1 := by rw [← h, Matrix.mul_one, hP]`. Establish `hM : (M : Matrix (Fin I.n) (Fin I.n) I.E) = 1`. Use extensionality with `i j`. Use `congrFun (congrFun hMφ i) j` as an intermediate fact.

Rewrite `this` using `[Matrix.map_apply]`. Apply `(I.φ v).injective` to reduce the goal to its premises. Rewrite using `[this]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne hij]`. Establish `hf1 : I.fmat γ.2 = 1`. Rewrite using `[hf, hM, Matrix.map_one _ (map_zero _) (map_one _)]`. Use `Prod.ext h1 ?_` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Conclude with `hf1`.
-/
theorem eq_one_of_fst (γ : I.GA) (hγ : γ ∈ I.GFset) (h1 : γ.1 = 1) : γ = 1 := by
  obtain ⟨M, -, hv, hf⟩ := hγ
  obtain ⟨v⟩ : Nonempty (NumberField.InfinitePlace I.F) := inferInstance
  have hP : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
  have hP' : (I.P v)⁻¹ * I.P v = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
  have h := hv v
  have hu : uMat (γ.1 v) = 1 := by rw [h1]; rfl
  rw [hu] at h
  have hMφ : (M : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = 1 := by
    calc (M : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)
        = I.P v * ((I.P v)⁻¹ * (M : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) * (I.P v)⁻¹ := by
          simp only [Matrix.mul_assoc, hP, Matrix.mul_one]
          rw [← Matrix.mul_assoc, hP, Matrix.one_mul]
      _ = 1 := by rw [← h, Matrix.mul_one, hP]
  have hM : (M : Matrix (Fin I.n) (Fin I.n) I.E) = 1 := by
    ext i j
    have := congrFun (congrFun hMφ i) j
    rw [Matrix.map_apply] at this
    apply (I.φ v).injective
    rw [this]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  have hf1 : I.fmat γ.2 = 1 := by
    rw [hf, hM, Matrix.map_one _ (map_zero _) (map_one _)]
  refine Prod.ext h1 ?_
  apply Subtype.ext
  apply Units.ext
  exact hf1

/- English proof (translation)
Use `haveI : T2Space I.Gf := Formalism.L2.SG.Pf.finite_adeles_group_t2 I`. Use `haveI hD : DiscreteTopology (Formalism.MainNotions.LeviCoordinates.rr_GF I) := Formalism.L2.SG.Pf.gf_discrete I`. Establish `hS : IsClosed ((Formalism.MainNotions.LeviCoordinates.rr_GF I : Subgroup I.GA) : Set I.GA)` using `Subgroup.isClosed_of_discrete`. Take `⟨C, hCc, hC1⟩` from `exists_compact_mem_nhds (1 : I.Ginf)`. Use `set Cf : Set I.Gf := (fun k => y * k * y⁻¹) '' I.Kset with hCfdef`.

Establish `hK : IsCompact Cf` using `(PI.WAU.maximal_compact_isCompact I).image (by fun_prop)`. Establish `hC : IsCompact (C ×ˢ Cf)` using `hCc.prod hK`. Use `set Fs : Set I.GA := ((Formalism.MainNotions.LeviCoordinates.rr_GF I : Subgroup I.GA) : Set I.GA) ∩ C ×ˢ Cf with hFsdef`. Establish `hDs : DiscreteTopology Fs` using `DiscreteTopology.of_subset hD inter_subset_left`. Apply the tactic sequence `have hFin : Fs.Finite := IsCompact.finite (hC.inter_left hS) (by first | exact ⟨hDs⟩ | exact hDs | exact isDiscrete_iff_discreteTopology.2 hDs)`.

Use `set T : Set I.Ginf := ((fun γ : I.GA => γ.1) '' Fs) \ {1} with hTdef`. Establish `hT : IsClosed T` using `((hFin.image _).subset diff_subset).isClosed`. Rewrite using `[discreteTopology_iff_isOpen_singleton_one]`. Use `isOpen_induced_iff.2 ⟨interior C \ T, isOpen_interior.sdiff hT, ?_⟩` and prove the remaining obligations. Use extensionality with `⟨h, hh⟩`.

Simplify using `only [mem_preimage, mem_diff, mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hint, hnT⟩`. Take `⟨γ, ⟨hγF, hγK⟩, rfl⟩` from `Subgroup.mem_map.1 hh`. Apply `Subtype.ext` to reduce the goal to its premises.

Assume the negation of the conclusion as `hne`. Apply `hnT` to reduce the goal to its premises. Establish `hFs : γ ∈ Fs` using `⟨hγF, interior_subset hint, ⟨y⁻¹ * γ.2 * y, hγK, (by group)⟩⟩`. Conclude with `⟨⟨γ, hFs, rfl⟩, hne⟩`. Introduce `h1`.

Establish `e : h = 1` using `congrArg Subtype.val h1`. Substitute `e` using the available equality. Conclude with `⟨mem_interior_iff_mem_nhds.2 hC1, fun hT1 => hT1.2 rfl⟩`.
-/
theorem gamInf_discrete (y : I.Gf) : DiscreteTopology (gamInf I y) := by
  haveI : T2Space I.Gf := Formalism.L2.SG.Pf.finite_adeles_group_t2 I
  haveI hD : DiscreteTopology (Formalism.MainNotions.LeviCoordinates.rr_GF I) := Formalism.L2.SG.Pf.gf_discrete I
  have hS : IsClosed ((Formalism.MainNotions.LeviCoordinates.rr_GF I : Subgroup I.GA) : Set I.GA) := Subgroup.isClosed_of_discrete
  obtain ⟨C, hCc, hC1⟩ := exists_compact_mem_nhds (1 : I.Ginf)
  set Cf : Set I.Gf := (fun k => y * k * y⁻¹) '' I.Kset with hCfdef
  have hK : IsCompact Cf := (PI.WAU.maximal_compact_isCompact I).image (by fun_prop)
  have hC : IsCompact (C ×ˢ Cf) := hCc.prod hK
  set Fs : Set I.GA := ((Formalism.MainNotions.LeviCoordinates.rr_GF I : Subgroup I.GA) : Set I.GA) ∩ C ×ˢ Cf with hFsdef
  have hDs : DiscreteTopology Fs := DiscreteTopology.of_subset hD inter_subset_left
  have hFin : Fs.Finite := IsCompact.finite (hC.inter_left hS)
    (by first | exact ⟨hDs⟩ | exact hDs | exact isDiscrete_iff_discreteTopology.2 hDs)
  set T : Set I.Ginf := ((fun γ : I.GA => γ.1) '' Fs) \ {1} with hTdef
  have hT : IsClosed T := ((hFin.image _).subset diff_subset).isClosed
  rw [discreteTopology_iff_isOpen_singleton_one]
  refine isOpen_induced_iff.2 ⟨interior C \ T, isOpen_interior.sdiff hT, ?_⟩
  ext ⟨h, hh⟩
  simp only [mem_preimage, mem_diff, mem_singleton_iff]
  constructor
  · rintro ⟨hint, hnT⟩
    obtain ⟨γ, ⟨hγF, hγK⟩, rfl⟩ := Subgroup.mem_map.1 hh
    apply Subtype.ext
    by_contra hne
    apply hnT
    have hFs : γ ∈ Fs := ⟨hγF, interior_subset hint, ⟨y⁻¹ * γ.2 * y, hγK, (by group)⟩⟩
    exact ⟨⟨γ, hFs, rfl⟩, hne⟩
  · intro h1
    have e : h = 1 := congrArg Subtype.val h1
    subst e
    exact ⟨mem_interior_iff_mem_nhds.2 hC1, fun hT1 => hT1.2 rfl⟩

/- English proof (translation)
Introduce `I y`. Use `haveI := gamInf_discrete I y`. Take `⟨F, hFm, hcov, huniq⟩` from `Formalism.L2.SG.Pf.exists_strictFund (gamInf I y)`. Use `⟨F, hFm, fun z => ?_, fun γ hγ hne => ?_⟩` and prove the remaining obligations. Take `⟨s, hs, hsz⟩` from `hcov z`.

Take `⟨γ, hγ, rfl⟩` from `Subgroup.mem_map.1 hs`. Conclude with `⟨γ, hγ, hsz⟩`. Establish `e : (fun z => γ.1 * z) '' F ∩ F = ∅`. Use extensionality with `w`. Simplify using `only [mem_inter_iff, mem_image, mem_empty_iff_false, iff_false, not_and]`.

Introduce and unpack `⟨x, hx, rfl⟩ hw`. Establish `h1` using `huniq x hx γ.1 (Subgroup.mem_map.2 ⟨γ, hγ, rfl⟩) hw`. Conclude with `hne (eq_one_of_fst I γ hγ.1 h1)`. Rewrite using `[e, measure_empty]`.
-/
theorem FundInfExists_holds : FundInfExists := by
  intro I y
  haveI := gamInf_discrete I y
  obtain ⟨F, hFm, hcov, huniq⟩ := Formalism.L2.SG.Pf.exists_strictFund (gamInf I y)
  refine ⟨F, hFm, fun z => ?_, fun γ hγ hne => ?_⟩
  · obtain ⟨s, hs, hsz⟩ := hcov z
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hs
    exact ⟨γ, hγ, hsz⟩
  · have e : (fun z => γ.1 * z) '' F ∩ F = ∅ := by
      ext w
      simp only [mem_inter_iff, mem_image, mem_empty_iff_false, iff_false, not_and]
      rintro ⟨x, hx, rfl⟩ hw
      have h1 := huniq x hx γ.1 (Subgroup.mem_map.2 ⟨γ, hγ, rfl⟩) hw
      exact hne (eq_one_of_fst I γ hγ.1 h1)
    rw [e, measure_empty]

end Formalism.L2.S.S7.FundamentalDomainSubgroups

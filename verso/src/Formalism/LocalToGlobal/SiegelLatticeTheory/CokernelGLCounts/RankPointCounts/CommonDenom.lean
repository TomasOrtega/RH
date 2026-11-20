import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.IsOpenAddSubgroup
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices

noncomputable section

open ValuativeRel Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.ProdEP2Uni

section LocTop

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

/- English proof (translation)
Use `haveI := M.L.top`. Use `haveI := M.L.free`. Use `haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)`. Use `first`. Consider the case `exact IsModuleTopology.isTopologicalRing F E`.

Consider the case `exact IsModuleTopology.topologicalRing F E`.
-/
theorem topE (M : Loc.Model F E) : IsTopologicalRing E := by
  haveI := M.L.top
  haveI := M.L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
  first
    | exact IsModuleTopology.isTopologicalRing F E
    | exact IsModuleTopology.topologicalRing F E

/- English proof (translation)
Use `haveI := M.L.top`. Use `haveI := M.L.free`. Use `haveI : T2Space F := MainNotions.LocalModelPeriodLattices.nonarchimedean_local_field_t2 inferInstance`. Use `haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)`. Set `b` to `Module.Free.chooseBasis F E`.

Establish `hc : Continuous (b.equivFun : E → (Module.Free.ChooseBasisIndex F E → F))` using `IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap`. Conclude with `T2Space.of_injective_continuous b.equivFun.injective hc`.
-/
theorem t2E (M : Loc.Model F E) : T2Space E := by
  haveI := M.L.top
  haveI := M.L.free
  haveI : T2Space F := MainNotions.LocalModelPeriodLattices.nonarchimedean_local_field_t2 inferInstance
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
  let b := Module.Free.chooseBasis F E
  have hc : Continuous (b.equivFun : E → (Module.Free.ChooseBasisIndex F E → F)) :=
    IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  exact T2Space.of_injective_continuous b.equivFun.injective hc

/- English proof (translation)
Use `first`. Consider the case `exact (Valuation.integer.integers (ValuativeRel.valuation F)).mem_of_integral h`. Consider the case `(obtain ⟨y, hy⟩ := (Valuation.integer.integers (ValuativeRel.valuation F)).mem_of_integral h`. Rewrite using `[← hy]`. Conclude with `y.2)`.
-/
theorem int_mem {x : F} (h : IsIntegral 𝒪[F] x) : x ∈ 𝒪[F] := by
  first
    | exact (Valuation.integer.integers (ValuativeRel.valuation F)).mem_of_integral h
    | (obtain ⟨y, hy⟩ := (Valuation.integer.integers (ValuativeRel.valuation F)).mem_of_integral h
       rw [← hy]
       exact y.2)

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `exact (IsScalarTower.algebraMap_apply 𝒪[F] F E x).symm`.
-/
theorem alg_int (x : 𝒪[F]) : algebraMap F E (x : F) = algebraMap 𝒪[F] E x := by
  first
    | rfl
    | exact (IsScalarTower.algebraMap_apply 𝒪[F] F E x).symm

/- English proof (translation)
Simplify using `only [Loc.Model.R, hg]`.
-/
private theorem R_eq_O_of_split_eq_none (M : Loc.Model F E) (hg : M.split = none) : M.R = M.L.O := by
  simp only [Loc.Model.R, hg]

/- English proof (translation)
Simplify using `only [Loc.Model.R, hg, Subring.mem_comap, Subring.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨a, b⟩, hab, he⟩`. Conclude with `⟨a, b, he.symm, RingHom.mem_eqLocus.mp hab⟩`. Introduce and unpack `⟨a, b, he, hab⟩`.

Conclude with `⟨(a, b), RingHom.mem_eqLocus.mpr hab, he.symm⟩`.
-/
private theorem mem_R_iff_of_split_eq_some (M : Loc.Model F E) (g : Loc.SplitG M.L) (hg : M.split = some g) (z : E) :
    z ∈ M.R ↔ ∃ a b : 𝒪[F], g.e z = ((a : F), (b : F)) ∧
      Ideal.Quotient.mk (Ideal.span {g.q}) a = Ideal.Quotient.mk (Ideal.span {g.q}) b := by
  simp only [Loc.Model.R, hg, Subring.mem_comap, Subring.mem_map]
  constructor
  · rintro ⟨⟨a, b⟩, hab, he⟩
    exact ⟨a, b, he.symm, RingHom.mem_eqLocus.mp hab⟩
  · rintro ⟨a, b, he, hab⟩
    exact ⟨(a, b), RingHom.mem_eqLocus.mpr hab, he.symm⟩

/- English proof (translation)
Consider the cases of `hg : M.split with`. Consider the case `none`. Rewrite using `[R_eq_O_of_split_eq_none M hg, M.L.O_def, alg_int]`. Conclude with `isIntegral_algebraMap`. Consider the case `some g`.

Rewrite using `[mem_R_iff_of_split_eq_some M g hg]`. Use `⟨a, a, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[AlgEquiv.commutes]`. Use `first`. Consider the case `rfl`.

Consider the case `simp`.
-/
theorem alg_mem_R (M : Loc.Model F E) (a : 𝒪[F]) : algebraMap F E (a : F) ∈ M.R := by
  cases hg : M.split with
  | none =>
    rw [R_eq_O_of_split_eq_none M hg, M.L.O_def, alg_int]
    exact isIntegral_algebraMap
  | some g =>
    rw [mem_R_iff_of_split_eq_some M g hg]
    refine ⟨a, a, ?_, rfl⟩
    rw [AlgEquiv.commutes]
    first
      | rfl
      | simp

/- English proof (translation)
Establish `h1 : IsIntegral 𝒪[F] (g.e z)` using `((L.O_def z).mp hz).map (g.e.toAlgHom.restrictScalars 𝒪[F])`. Conclude with `⟨int_mem (h1.map ((AlgHom.fst F F F).restrictScalars 𝒪[F])), int_mem (h1.map ((AlgHom.snd F F F).restrictScalars 𝒪[F]))⟩`.
-/
private theorem splitG_e_mem_integers_of_mem_O (L : Loc.LocE F E) (g : Loc.SplitG L) {z : E} (hz : z ∈ L.O) :
    (g.e z).1 ∈ 𝒪[F] ∧ (g.e z).2 ∈ 𝒪[F] := by
  have h1 : IsIntegral 𝒪[F] (g.e z) := ((L.O_def z).mp hz).map (g.e.toAlgHom.restrictScalars 𝒪[F])
  exact ⟨int_mem (h1.map ((AlgHom.fst F F F).restrictScalars 𝒪[F])),
    int_mem (h1.map ((AlgHom.snd F F F).restrictScalars 𝒪[F]))⟩

/- English proof (translation)
Consider the cases of `hg : M.split with`. Consider the case `none`. Rewrite `hz` using `[R_eq_O_of_split_eq_none M hg]`. Then use the resulting hypothesis. Consider the case `some g`. Take `⟨a, b, he, -⟩` from `(mem_R_iff_of_split_eq_some M g hg z).mp hz`.

Rewrite using `[M.L.O_def]`. Establish `ha : IsIntegral 𝒪[F] (a : F)` using `(isIntegral_algebraMap : IsIntegral 𝒪[F] (algebraMap 𝒪[F] F a))`. Establish `hb : IsIntegral 𝒪[F] (b : F)` using `(isIntegral_algebraMap : IsIntegral 𝒪[F] (algebraMap 𝒪[F] F b))`. Establish `h1 : IsIntegral 𝒪[F] (((a : F), (b : F)) : F × F)` using `IsIntegral.pair ha hb`. Establish `h2` using `h1.map (g.e.symm.toAlgHom.restrictScalars 𝒪[F])`.

Rewrite `h2` using `[← he]`. Establish `e : (g.e.symm.toAlgHom.restrictScalars 𝒪[F]) (g.e z) = z` using `g.e.symm_apply_apply z`. Rewrite `h2` using `[e]`. Then use the resulting hypothesis.
-/
private theorem mem_O_of_mem_R (M : Loc.Model F E) {z : E} (hz : z ∈ M.R) : z ∈ M.L.O := by
  cases hg : M.split with
  | none =>
    rwa [R_eq_O_of_split_eq_none M hg] at hz
  | some g =>
    obtain ⟨a, b, he, -⟩ := (mem_R_iff_of_split_eq_some M g hg z).mp hz
    rw [M.L.O_def]
    have ha : IsIntegral 𝒪[F] (a : F) := (isIntegral_algebraMap : IsIntegral 𝒪[F] (algebraMap 𝒪[F] F a))
    have hb : IsIntegral 𝒪[F] (b : F) := (isIntegral_algebraMap : IsIntegral 𝒪[F] (algebraMap 𝒪[F] F b))
    have h1 : IsIntegral 𝒪[F] (((a : F), (b : F)) : F × F) := IsIntegral.pair ha hb
    have h2 := h1.map (g.e.symm.toAlgHom.restrictScalars 𝒪[F])
    rw [← he] at h2
    have e : (g.e.symm.toAlgHom.restrictScalars 𝒪[F]) (g.e z) = z := g.e.symm_apply_apply z
    rwa [e] at h2

/- English proof (translation)
Use `haveI := topE M`. Establish `hO` using `(MainNotions.LocalModelPeriodLattices.O_top M.L).2.1`. Establish `hRo : IsOpen (M.R : Set E)` using `PI.ProdFormulaE.ROpen.isOpen_R M`. Establish `hRc : IsClosed (M.R : Set E)` using `M.R.toAddSubgroup.isClosed_of_isOpen hRo`. Conclude with `hO.of_isClosed_subset hRc (fun z hz => mem_O_of_mem_R M hz)`.
-/
theorem R_compact [CharZero F] (M : Loc.Model F E) : IsCompact (M.R : Set E) := by
  haveI := topE M
  have hO := (MainNotions.LocalModelPeriodLattices.O_top M.L).2.1
  have hRo : IsOpen (M.R : Set E) := PI.ProdFormulaE.ROpen.isOpen_R M
  have hRc : IsClosed (M.R : Set E) := M.R.toAddSubgroup.isClosed_of_isOpen hRo
  exact hO.of_isClosed_subset hRc (fun z hz => mem_O_of_mem_R M hz)

/- English proof (translation)
Use `haveI := M.L.free`. Use `haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)`. Use `haveI : Nontrivial E := by first`. Consider the case `exact Module.nontrivial_of_finrank_pos (R := F) (by rw [M.L.rank]; norm_num)`. Consider the case `exact Module.nontrivial_of_finrank_eq_succ M.L.rank`.

Use `haveI : IsFractionRing 𝒪[F] F := ValuationRing.instIsFractionRingInteger (ValuativeRel.valuation F)`. Establish `hinj : ∀ x : 𝒪[F], algebraMap 𝒪[F] E x = 0 → x = 0`. Introduce `x hx`. Rewrite `hx` using `[← alg_int]`. Conclude with `Subtype.ext ((map_eq_zero_iff _ (algebraMap F E).injective).mp hx)`.

Establish `halg : IsAlgebraic 𝒪[F] y`. Establish `hF : IsAlgebraic F y` using `(Algebra.IsIntegral.isIntegral (R := F) y).isAlgebraic`. Conclude with `(IsFractionRing.isAlgebraic_iff 𝒪[F] F E).mpr hF`. Establish `hex : ∃ s : 𝒪[F], s ≠ 0 ∧ IsIntegral 𝒪[F] (algebraMap 𝒪[F] E s * y)` using `by first`. Consider the case `(obtain ⟨z, s, hs, hz⟩ := exists_integral_multiple halg hinj`.

Conclude with `⟨s, hs, by rw [mul_comm, hz]; exact z.2⟩)`. Consider the case `(obtain ⟨s, hs, hi⟩ := halg.exists_integral_multiple`. Conclude with `⟨s, hs, by rwa [Algebra.smul_def] at hi⟩)`. Take `⟨s, hs, hsi⟩` from `hex`. Establish `hsy : algebraMap F E (s : F) * y ∈ M.L.O`.

Rewrite using `[M.L.O_def, alg_int]`. Conclude with `hsi`. Consider the cases of `hg : M.split with`. Consider the case `none`. Conclude with `⟨s, hs, by rw [R_eq_O_of_split_eq_none M hg]; exact hsy⟩`.

Consider the case `some g`. Use `⟨g.q * s, mul_ne_zero g.q_irr.ne_zero hs, ?_⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `splitG_e_mem_integers_of_mem_O M.L g hsy`. Rewrite using `[mem_R_iff_of_split_eq_some M g hg]`. Use `⟨g.q * ⟨_, h1⟩, g.q * ⟨_, h2⟩, ?_, ?_⟩` and prove the remaining obligations.

Establish `e : algebraMap F E ((g.q * s : 𝒪[F]) : F) * y = algebraMap F E (g.q : F) * (algebraMap F E (s : F) * y)`. Rewrite using `[MulMemClass.coe_mul, map_mul, mul_assoc]`. Rewrite using `[e, map_mul, AlgEquiv.commutes]`. Apply the tactic sequence `ext <;> simp`. Establish `hq : ∀ t : 𝒪[F], Ideal.Quotient.mk (Ideal.span {g.q}) (g.q * t) = 0` using `fun t => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right t _ (Ideal.mem_span_singleton_self _))`.

Rewrite using `[hq, hq]`.
-/
theorem R_denom (M : Loc.Model F E) (y : E) : ∃ a : 𝒪[F], a ≠ 0 ∧ algebraMap F E (a : F) * y ∈ M.R := by
  haveI := M.L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
  haveI : Nontrivial E := by
    first
      | exact Module.nontrivial_of_finrank_pos (R := F) (by rw [M.L.rank]; norm_num)
      | exact Module.nontrivial_of_finrank_eq_succ M.L.rank
  haveI : IsFractionRing 𝒪[F] F := ValuationRing.instIsFractionRingInteger (ValuativeRel.valuation F)
  have hinj : ∀ x : 𝒪[F], algebraMap 𝒪[F] E x = 0 → x = 0 := by
    intro x hx
    rw [← alg_int] at hx
    exact Subtype.ext ((map_eq_zero_iff _ (algebraMap F E).injective).mp hx)
  have halg : IsAlgebraic 𝒪[F] y := by
    have hF : IsAlgebraic F y := (Algebra.IsIntegral.isIntegral (R := F) y).isAlgebraic
    exact (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).mpr hF
  have hex : ∃ s : 𝒪[F], s ≠ 0 ∧ IsIntegral 𝒪[F] (algebraMap 𝒪[F] E s * y) := by
    first
      | (obtain ⟨z, s, hs, hz⟩ := exists_integral_multiple halg hinj
         exact ⟨s, hs, by rw [mul_comm, hz]; exact z.2⟩)
      | (obtain ⟨s, hs, hi⟩ := halg.exists_integral_multiple
         exact ⟨s, hs, by rwa [Algebra.smul_def] at hi⟩)
  obtain ⟨s, hs, hsi⟩ := hex
  have hsy : algebraMap F E (s : F) * y ∈ M.L.O := by
    rw [M.L.O_def, alg_int]
    exact hsi
  cases hg : M.split with
  | none =>
    exact ⟨s, hs, by rw [R_eq_O_of_split_eq_none M hg]; exact hsy⟩
  | some g =>
    refine ⟨g.q * s, mul_ne_zero g.q_irr.ne_zero hs, ?_⟩
    obtain ⟨h1, h2⟩ := splitG_e_mem_integers_of_mem_O M.L g hsy
    rw [mem_R_iff_of_split_eq_some M g hg]
    refine ⟨g.q * ⟨_, h1⟩, g.q * ⟨_, h2⟩, ?_, ?_⟩
    · have e : algebraMap F E ((g.q * s : 𝒪[F]) : F) * y =
          algebraMap F E (g.q : F) * (algebraMap F E (s : F) * y) := by
        rw [MulMemClass.coe_mul, map_mul, mul_assoc]
      rw [e, map_mul, AlgEquiv.commutes]
      ext <;> simp
    · have hq : ∀ t : 𝒪[F], Ideal.Quotient.mk (Ideal.span {g.q}) (g.q * t) = 0 := fun t =>
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right t _ (Ideal.mem_span_singleton_self _))
      rw [hq, hq]

/- English proof (translation)
Use `choose d hd0 hd using fun k => R_denom M (y k)`. Use `⟨∏ k, d k, Finset.prod_ne_zero_iff.mpr fun k _ => hd0 k, fun k => ?_⟩` and prove the remaining obligations. Establish `hp : (∏ j, d j) = (∏ j ∈ Finset.univ.erase k, d j) * d k` using `(Finset.prod_erase_mul _ _ (Finset.mem_univ k)).symm`. Rewrite using `[hp]`. Establish `e : algebraMap F E (((∏ j ∈ Finset.univ.erase k, d j) * d k : 𝒪[F]) : F) * y k = algebraMap F E ((∏ j ∈ Finset.univ.erase k, d j : 𝒪[F]) : F) * (algebraMap F E (d k : F) * y k)`.

Rewrite using `[MulMemClass.coe_mul, map_mul, mul_assoc]`. Rewrite using `[e]`. Conclude with `M.R.mul_mem (alg_mem_R M _) (hd k)`.
-/
theorem common_denom (M : Loc.Model F E) {ι : Type} [Fintype ι] (y : ι → E) :
    ∃ a : 𝒪[F], a ≠ 0 ∧ ∀ k, algebraMap F E (a : F) * y k ∈ M.R := by
  classical
  choose d hd0 hd using fun k => R_denom M (y k)
  refine ⟨∏ k, d k, Finset.prod_ne_zero_iff.mpr fun k _ => hd0 k, fun k => ?_⟩
  have hp : (∏ j, d j) = (∏ j ∈ Finset.univ.erase k, d j) * d k :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ k)).symm
  rw [hp]
  have e : algebraMap F E (((∏ j ∈ Finset.univ.erase k, d j) * d k : 𝒪[F]) : F) * y k =
      algebraMap F E ((∏ j ∈ Finset.univ.erase k, d j : 𝒪[F]) : F) * (algebraMap F E (d k : F) * y k) := by
    rw [MulMemClass.coe_mul, map_mul, mul_assoc]
  rw [e]
  exact M.R.mul_mem (alg_mem_R M _) (hd k)

end LocTop

end Formalism.L2.SG.Pf.ProdEP2Uni

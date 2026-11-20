import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariant
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelTestFunctionMapLinearInjectiveEquivarStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorTestThetaZeroEqThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatticeVacuaTensorCorrespondLineStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.LevVec

variable {D : D7} {S T : HSp D}

/- English proof (translation)
Establish `h0 : C.Th x 0 = 0`. Simplify using `using (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C x hx 0 SW.isSB_zero).2.1 0`. Use `Finset.induction_on s (by simpa using h0) ?_` and prove the remaining obligations. Introduce `i s hi ih`. Rewrite using `[Finset.sum_insert hi, Finset.sum_insert hi, ← ih]`.

Conclude with `((GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C x hx (f i) (hf i)).1 _ (GlobalTheory.SW.RecSum.isSB_sum s f hf)).1`.
-/
theorem th_sum (C : Ctx S T) {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {ι : Type} (s : Finset ι)
    (f : ι → TF S.rank C.g) (hf : ∀ i, SW.IsSB (f i)) :
    C.Th x (∑ i ∈ s, f i) = ∑ i ∈ s, C.Th x (f i) := by
  classical
  have h0 : C.Th x 0 = 0 := by
    simpa using (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C x hx 0 SW.isSB_zero).2.1 0
  refine Finset.induction_on s (by simpa using h0) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
  exact ((GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C x hx (f i) (hf i)).1 _ (GlobalTheory.SW.RecSum.isSB_sum s f hf)).1

/- English proof (translation)
Establish `h0 : C.Th x 0 = 0`. Simplify using `using (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C x hx 0 SW.isSB_zero).2.1 0`. Establish `hsub : (Function.support fun i => C.Th x (f i)) ⊆ (hfin.toFinset : Set ι)`. Introduce `i hi`. Rewrite using `[hfin.coe_toFinset, Function.mem_support]`.

Introduce `hfi`. Conclude with `(Function.mem_support.1 hi) (by simp [hfi, h0])`. Rewrite using `[finsum_eq_sum_of_support_subset f (by rw [hfin.coe_toFinset]), finsum_eq_sum_of_support_subset _ hsub]`. Conclude with `th_sum C hx hfin.toFinset f hf`.
-/
theorem th_finsum (C : Ctx S T) {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {ι : Type}
    (f : ι → TF S.rank C.g) (hf : ∀ i, SW.IsSB (f i)) (hfin : (Function.support f).Finite) :
    C.Th x (∑ᶠ i, f i) = ∑ᶠ i, C.Th x (f i) := by
  classical
  have h0 : C.Th x 0 = 0 := by
    simpa using (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C x hx 0 SW.isSB_zero).2.1 0
  have hsub : (Function.support fun i => C.Th x (f i)) ⊆ (hfin.toFinset : Set ι) := by
    intro i hi
    rw [hfin.coe_toFinset, Function.mem_support]
    intro hfi
    exact (Function.mem_support.1 hi) (by simp [hfi, h0])
  rw [finsum_eq_sum_of_support_subset f (by rw [hfin.coe_toFinset]),
    finsum_eq_sum_of_support_subset _ hsub]
  exact th_sum C hx hfin.toFinset f hf

/- English proof (translation)
Establish `key : ∀ c : A ⧸ B.addSubgroupOf A, F (-(c.out : G)) = F (((-c).out : A) : G)`. Introduce `c`. Establish `hc : ((-c.out : A) : A ⧸ B.addSubgroupOf A) = (((-c).out : A) : A ⧸ B.addSubgroupOf A)`. Rewrite using `[QuotientAddGroup.mk_neg, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']`. Rewrite `hc` using `[QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`.

Establish `e : (((-c).out : A) : G) = -(c.out : G) + ((-(-c.out) + (-c).out : A) : G)`. Use `push_cast`. Normalize the expressions using the abelian group laws. Rewrite using `[e, hF _ (neg_mem c.out.2) _ hc]`. Rewrite using `[finsum_congr key]`.

Conclude with `finsum_comp_equiv (Equiv.neg _) (f := fun c : A ⧸ B.addSubgroupOf A => F ((c.out : A) : G))`.
-/
theorem finsum_out_neg {G N : Type} [AddCommGroup G] [AddCommMonoid N] (A B : AddSubgroup G)
    (F : G → N) (hF : ∀ y ∈ A, ∀ δ ∈ B, F (y + δ) = F y) :
    ∑ᶠ c : A ⧸ B.addSubgroupOf A, F (-(c.out : G)) = ∑ᶠ c : A ⧸ B.addSubgroupOf A, F (c.out : G) := by
  classical
  have key : ∀ c : A ⧸ B.addSubgroupOf A, F (-(c.out : G)) = F (((-c).out : A) : G) := by
    intro c
    have hc : ((-c.out : A) : A ⧸ B.addSubgroupOf A) = (((-c).out : A) : A ⧸ B.addSubgroupOf A) := by
      rw [QuotientAddGroup.mk_neg, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at hc
    have e : (((-c).out : A) : G) = -(c.out : G) + ((-(-c.out) + (-c).out : A) : G) := by
      push_cast
      abel
    rw [e, hF _ (neg_mem c.out.2) _ hc]
  rw [finsum_congr key]
  exact finsum_comp_equiv (Equiv.neg _) (f := fun c : A ⧸ B.addSubgroupOf A => F ((c.out : A) : G))

/- English proof (translation)
Distinguish the cases in `hfin : (Function.support f).Finite`. Conclude with `th_finsum C hx f hf hfin`. Establish `h0 : C.Th x 0 = 0`. Simplify using `using (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C x hx 0 SW.isSB_zero).2.1 0`. Establish `hsupp : (Function.support fun i => C.Th x (f i)) = Function.support f`.

Use extensionality with `i`. Simplify using `only [Function.mem_support, ne_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h hfi`. Conclude with `h (by rw [hfi, h0])`.

Introduce `h hT`. Conclude with `h (((GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C x hx (f i) (hf i)).1 0 SW.isSB_zero).2 (by rw [hT, h0]))`. Establish `hinf : (Function.support fun i => C.Th x (f i)).Infinite`. Rewrite using `[hsupp]`. Conclude with `hfin`.

Rewrite using `[finsum_of_infinite_support hfin, finsum_of_infinite_support hinf, h0]`.
-/
private theorem ctx_Th_finsum_of_isSB (C : Ctx S T) {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {ι : Type}
    (f : ι → TF S.rank C.g) (hf : ∀ i, SW.IsSB (f i)) :
    C.Th x (∑ᶠ i, f i) = ∑ᶠ i, C.Th x (f i) := by
  by_cases hfin : (Function.support f).Finite
  · exact th_finsum C hx f hf hfin
  · have h0 : C.Th x 0 = 0 := by
      simpa using (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C x hx 0 SW.isSB_zero).2.1 0
    have hsupp : (Function.support fun i => C.Th x (f i)) = Function.support f := by
      ext i
      simp only [Function.mem_support, ne_eq]
      constructor
      · intro h hfi
        exact h (by rw [hfi, h0])
      · intro h hT
        exact h (((GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C x hx (f i) (hf i)).1 0 SW.isSB_zero).2 (by rw [hT, h0]))
    have hinf : (Function.support fun i => C.Th x (f i)).Infinite := by
      rw [hsupp]
      exact hfin
    rw [finsum_of_infinite_support hfin, finsum_of_infinite_support hinf, h0]

/- English proof (translation)
Introduce `D S T C Lv hn M hw2 hM0 hM B hB`. Establish `hs` using `C.sympl`. Establish `he` using `C.even`. Establish `h6833` using `GlobalTheory.T.level_structure_properties D.host.E T.rank C.X C.g C.bas C.idx S.rank hs he Lv hn`. Establish `hΛlats : C.X.Λ ∈ Lv.lats` using `h6833.1`.

Establish `hΛself : SelfD C.X C.X.Λ` using `hΛlats.1`. Establish `hSelf : SelfD C.X (Lv.sh C.X.Λ)` using `(h6833.2.2.2.1 _ hΛlats).1`. Establish `hstd : stdL D.host.E S.rank ∈ Vset D.host.E S.rank M` using `GlobalTheory.SW.Base.stdL_mem_Vset _ _`. Establish `h26522` using `GlobalTheory.T.latticeVacua_tensor_correspond_line D S T C Lv.w Lv.w_int Lv.w_tr hw2 M _ hstd _ hSelf`. Establish `hxdom : C.xB B ∈ C.X.dom` using `((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.1`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `f' hf' v hv`. Take `⟨t, ht⟩` from `h26522.2 B hB v hv f' hf'.th hf'.fock hf'.lat`. Use `⟨t, ?_, ht⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Conclude with `hf'.ne (by simpa using ht)`. Introduce `v₀ hv₀`. Establish `hv` using `hv₀ _ hΛlats`. Establish `hvSB : SW.IsSB (v₀ C.X.Λ)` using `hv.1`. Establish `hvip : SW.ip (v₀ C.X.Λ) (v₀ C.X.Λ) = 1` using `hv.2.1`.

Establish `hTh` using `GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hxdom (v₀ C.X.Λ) hvSB`. Establish `h0 : C.Th (C.xB B) 0 = 0`. Simplify using `using (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hxdom 0 SW.isSB_zero).2.1 0`. Use `⟨⟨(GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ hxdom _ hvSB).1.1, ?_, ((GlobalTheory.T.fockPolynomialVector_testTheta_zero_eq_thetaSeries D S T C).2 B hB _ hvSB).1, (h26522.1 _ hxdom _ hvSB).2 hv.2.2⟩, ?_⟩` and prove the remaining obligations. Introduce `hz`.

Establish `h1 : C.Th (C.xB B) (v₀ C.X.Λ) = C.Th (C.xB B) 0` using `by rw [hz, h0]`. Establish `h2` using `(hTh.1 0 SW.isSB_zero).2 h1`. Establish `h3` using `GlobalTheory.SW.TensVac.ip_smul_left (φ := (0 : TF S.rank C.g)) (ψ := 0) (0 : ℂ) SW.isSB_zero SW.isSB_zero`. Rewrite `hvip` using `[h2]`. Simplify using `only [smul_zero, zero_mul] at h3`.

Rewrite `hvip` using `[h3]`. Conclude with `zero_ne_one hvip`. Introduce `t`. Establish `htv : SW.IsSB (t • v₀ C.X.Λ)` using `GlobalTheory.SW.TensVac.sb_smul t hvSB`. Establish `hsbH : ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, SW.IsSB (heisG C.X C.bas y (v₀ C.X.Λ))` using `fun y => (GlobalTheory.SW.TensVac.laws C.idx hs he y hvSB).1`.

Establish `hterm : ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, Lv.dat hn y • C.Th (C.xB B) (heisG C.X C.bas y (t • v₀ C.X.Λ)) = t • C.Th (C.xB B) (Lv.dat hn y • heisG C.X C.bas y (v₀ C.X.Λ))`. Introduce `y`. Establish `e1` using `(GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hxdom _ (hsbH y)).2.1`. Rewrite using `[GlobalTheory.SW.TensVac.heisG_smul, e1, e1, smul_comm]`. Establish `hu : unitv (projA C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) (v₀ C.X.Λ)) = v₀ C.X.Λ`.

Rewrite using `[(GlobalTheory.SW.RecSum.unitv_proj C.idx hs he hstd hSelf hv hv).2, hvip]`. Simplify using the standard rewrite rules. Establish `hrho : ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, C.rho (finW S T y) (t • C.Th (C.xB B) (v₀ C.X.Λ)) = C.Th (C.xB B) (heisG C.X C.bas (-y) (t • v₀ C.X.Λ))`. Introduce `y`. Rewrite using `[← hTh.2.1 t]`.

Conclude with `(GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hxdom _ htv).2.2.1 y`. Simplify using `only [GlobalTheory.Ker.Ctx.uVec, GlobalTheory.SW.Level.phi, hu, hrho]`. Use `Eq.trans (finsum_out_neg (tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ)) (tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪 * Lv.𝔪) • C.X.Λ)) (fun y => Lv.dat hn y • C.Th (C.xB B) (heisG C.X C.bas y (t • v₀ C.X.Λ))) ?_) ?_` and prove the remaining obligations. Introduce `y hy δ hδ`. Establish `hcong : ∀ k, Cong C.X Lv.𝔪 ((y + δ) k) (y k)` using `GlobalTheory.SW.RecSum.cong_of_mem hstd hM (GlobalTheory.SW.RecSum.near_of_mem hΛlats) (by simpa using hδ)`.

Establish `hdat : Lv.dat hn (y + δ) = Lv.dat hn y` using `h6833.2.2.2.2.2.1 _ _ hcong`. Use `show Lv.dat hn (y + δ) • _ = Lv.dat hn y • _`. Rewrite using `[hdat, GlobalTheory.SW.TensVac.heisG_smul, GlobalTheory.SW.TensVac.heisG_smul, GlobalTheory.SW.RecSum.heis_add C.idx hs he Lv hstd hΛself hSelf hv hy hδ]`. Rewrite using `[ctx_Th_finsum_of_isSB C hxdom _ (fun c => GlobalTheory.SW.TensVac.sb_smul _ (hsbH _)), smul_finsum]`. Conclude with `finsum_congr fun c => hterm _`.
-/
theorem uVec_eq : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → (∀ f', C.IsBase Lv B f' → ∀ v, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) v → ∃ t : ℂ, t ≠ 0 ∧ f' = t • (C.Th (C.xB B) v)) ∧ ∀ v₀ : Lt D.host.E T.rank → TF S.rank C.g, (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → C.IsBase Lv B (C.Th (C.xB B) (v₀ C.X.Λ)) ∧ ∀ t : ℂ, C.uVec Lv hn (t • (C.Th (C.xB B) (v₀ C.X.Λ))) = t • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) := by
  intro D S T C Lv hn M hw2 hM0 hM B hB
  classical
  have hs := C.sympl
  have he := C.even
  have h6833 := GlobalTheory.T.level_structure_properties D.host.E T.rank C.X C.g C.bas C.idx S.rank hs he Lv hn
  have hΛlats : C.X.Λ ∈ Lv.lats := h6833.1
  have hΛself : SelfD C.X C.X.Λ := hΛlats.1
  have hSelf : SelfD C.X (Lv.sh C.X.Λ) := (h6833.2.2.2.1 _ hΛlats).1
  have hstd : stdL D.host.E S.rank ∈ Vset D.host.E S.rank M := GlobalTheory.SW.Base.stdL_mem_Vset _ _
  have h26522 := GlobalTheory.T.latticeVacua_tensor_correspond_line D S T C Lv.w Lv.w_int Lv.w_tr hw2 M _ hstd _ hSelf
  have hxdom : C.xB B ∈ C.X.dom := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.1
  refine ⟨?_, ?_⟩
  · intro f' hf' v hv
    obtain ⟨t, ht⟩ := h26522.2 B hB v hv f' hf'.th hf'.fock hf'.lat
    refine ⟨t, ?_, ht⟩
    rintro rfl
    exact hf'.ne (by simpa using ht)
  · intro v₀ hv₀
    have hv := hv₀ _ hΛlats
    have hvSB : SW.IsSB (v₀ C.X.Λ) := hv.1
    have hvip : SW.ip (v₀ C.X.Λ) (v₀ C.X.Λ) = 1 := hv.2.1
    have hTh := GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hxdom (v₀ C.X.Λ) hvSB
    have h0 : C.Th (C.xB B) 0 = 0 := by
      simpa using (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hxdom 0 SW.isSB_zero).2.1 0
    refine ⟨⟨(GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ hxdom _ hvSB).1.1, ?_,
      ((GlobalTheory.T.fockPolynomialVector_testTheta_zero_eq_thetaSeries D S T C).2 B hB _ hvSB).1, (h26522.1 _ hxdom _ hvSB).2 hv.2.2⟩, ?_⟩
    · intro hz
      have h1 : C.Th (C.xB B) (v₀ C.X.Λ) = C.Th (C.xB B) 0 := by rw [hz, h0]
      have h2 := (hTh.1 0 SW.isSB_zero).2 h1
      have h3 := GlobalTheory.SW.TensVac.ip_smul_left (φ := (0 : TF S.rank C.g)) (ψ := 0) (0 : ℂ)
        SW.isSB_zero SW.isSB_zero
      rw [h2] at hvip
      simp only [smul_zero, zero_mul] at h3
      rw [h3] at hvip
      exact zero_ne_one hvip
    · intro t
      have htv : SW.IsSB (t • v₀ C.X.Λ) := GlobalTheory.SW.TensVac.sb_smul t hvSB
      have hsbH : ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E,
          SW.IsSB (heisG C.X C.bas y (v₀ C.X.Λ)) :=
        fun y => (GlobalTheory.SW.TensVac.laws C.idx hs he y hvSB).1
      have hterm : ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E,
          Lv.dat hn y • C.Th (C.xB B) (heisG C.X C.bas y (t • v₀ C.X.Λ)) =
            t • C.Th (C.xB B) (Lv.dat hn y • heisG C.X C.bas y (v₀ C.X.Λ)) := by
        intro y
        have e1 := (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hxdom _ (hsbH y)).2.1
        rw [GlobalTheory.SW.TensVac.heisG_smul, e1, e1, smul_comm]
      have hu : unitv (projA C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) (v₀ C.X.Λ)) =
          v₀ C.X.Λ := by
        rw [(GlobalTheory.SW.RecSum.unitv_proj C.idx hs he hstd hSelf hv hv).2, hvip]
        simp
      have hrho : ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E,
          C.rho (finW S T y) (t • C.Th (C.xB B) (v₀ C.X.Λ)) =
            C.Th (C.xB B) (heisG C.X C.bas (-y) (t • v₀ C.X.Λ)) := by
        intro y
        rw [← hTh.2.1 t]
        exact (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hxdom _ htv).2.2.1 y
      simp only [GlobalTheory.Ker.Ctx.uVec, GlobalTheory.SW.Level.phi, hu, hrho]
      refine Eq.trans (finsum_out_neg
        (tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ))
        (tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪 * Lv.𝔪) • C.X.Λ))
        (fun y => Lv.dat hn y • C.Th (C.xB B) (heisG C.X C.bas y (t • v₀ C.X.Λ))) ?_) ?_
      · intro y hy δ hδ
        have hcong : ∀ k, Cong C.X Lv.𝔪 ((y + δ) k) (y k) :=
          GlobalTheory.SW.RecSum.cong_of_mem hstd hM (GlobalTheory.SW.RecSum.near_of_mem hΛlats) (by simpa using hδ)
        have hdat : Lv.dat hn (y + δ) = Lv.dat hn y := h6833.2.2.2.2.2.1 _ _ hcong
        show Lv.dat hn (y + δ) • _ = Lv.dat hn y • _
        rw [hdat, GlobalTheory.SW.TensVac.heisG_smul, GlobalTheory.SW.TensVac.heisG_smul,
          GlobalTheory.SW.RecSum.heis_add C.idx hs he Lv hstd hΛself hSelf hv hy hδ]
      · rw [ctx_Th_finsum_of_isSB C hxdom _ (fun c => GlobalTheory.SW.TensVac.sb_smul _ (hsbH _)), smul_finsum]
        exact finsum_congr fun c => hterm _

end GlobalTheory.Ker.LevVec

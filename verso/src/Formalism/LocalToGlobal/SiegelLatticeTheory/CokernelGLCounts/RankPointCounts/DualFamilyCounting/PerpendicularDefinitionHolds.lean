import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.StepsR
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GoodRDet
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ExtendByIdentitySymmFixOrth

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PairSpanDimension

variable {D : Formalism.BasicNotions.D7}

/- English proof (translation)
Establish `: Nonempty D.what₂.Tau` using `Fintype.card_pos_iff.1 (by`. Rewrite using `[D.what₂.card_Tau]`. Unfold `Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n`. Use the proof step `positivity)`. Take `⟨τ⟩` from `this`.

Introduce `h`. Use `hx τ` as an intermediate fact. Rewrite `this` using `[h, map_zero, Complex.zero_re]`. Conclude with `lt_irrefl _ this`.
-/
theorem totPos_ne_zero {x : D.host.E} (hx : TotPos x) : x ≠ 0 := by
  have : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n; positivity)
  obtain ⟨τ⟩ := this
  intro h
  have := hx τ
  rw [h, map_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

def fam {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') :
    Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (VS D).V :=
  Sum.elim F0.fvec F'.fl.fvec

variable {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')

/- English proof (translation)
Unfold `UPair fam`. Rewrite using `[Set.Sum.elim_range]`.
-/
theorem upair_eq : UPair D F0 F' = Submodule.span D.host.E (Set.range (fam F0 F')) := by
  unfold UPair fam
  rw [Set.Sum.elim_range]

/- English proof (translation)
Establish `hs : ∀ x y, star ((VS D).hT x y) = (VS D).hT y x`. Introduce `x y`. Rewrite using `[← starRingEnd_apply]`. Use `first`. Consider the case `exact (VS D).herm.eq x y`.

Consider the case `exact (VS D).herm x y`. Establish `hze : ∀ j, (VS D).hT F0.z (F0.e j) = 0` using `fun j => by rw [← hs, F0.z_orth, star_zero]`. Establish `hze' : ∀ j, (VS D).hT F'.fl.z (F'.fl.e j) = 0` using `fun j => by rw [← hs, F'.fl.z_orth, star_zero]`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b`. Simplify using `only [fam, Sum.elim_inl, Ga, Matrix.fromBlocks_apply₁₁, Matrix.of_apply]`.

Apply the tactic sequence `induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>`. Simplify using `[FlagG.fvec, F0.e_iso, F0.z_orth, F0.z_norm, hze]`. Simplify using `only [fam, Sum.elim_inl, Sum.elim_inr, Ga, Matrix.fromBlocks_apply₁₂]`. Both sides reduce to the same expression. Simplify using `only [fam, Sum.elim_inl, Sum.elim_inr, Ga, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply] show _ = star ((VS D).hT (F0.fvec b) (F'.fl.fvec a))`.

Rewrite using `[hs]`. Simplify using `only [fam, Sum.elim_inr, Ga, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]`. Apply the tactic sequence `induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>`. Simplify using `[FlagG.fvec, F'.fl.e_iso, F'.fl.z_orth, F'.fl.z_norm, hze']`.
-/
theorem hT_fam (a b : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) :
    (VS D).hT (fam F0 F' a) (fam F0 F' b) = Ga T T' (ZhatL (lf D F0) F') a b := by
  have hs : ∀ x y, star ((VS D).hT x y) = (VS D).hT y x := by
    intro x y
    rw [← starRingEnd_apply]
    first
      | exact (VS D).herm.eq x y
      | exact (VS D).herm x y
  have hze : ∀ j, (VS D).hT F0.z (F0.e j) = 0 := fun j => by rw [← hs, F0.z_orth, star_zero]
  have hze' : ∀ j, (VS D).hT F'.fl.z (F'.fl.e j) = 0 := fun j => by rw [← hs, F'.fl.z_orth, star_zero]
  rcases a with a | a <;> rcases b with b | b
  · simp only [fam, Sum.elim_inl, Ga, Matrix.fromBlocks_apply₁₁, Matrix.of_apply]
    induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
      simp [FlagG.fvec, F0.e_iso, F0.z_orth, F0.z_norm, hze]
  · simp only [fam, Sum.elim_inl, Sum.elim_inr, Ga, Matrix.fromBlocks_apply₁₂]
    rfl
  · simp only [fam, Sum.elim_inl, Sum.elim_inr, Ga, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply]
    show _ = star ((VS D).hT (F0.fvec b) (F'.fl.fvec a))
    rw [hs]
  · simp only [fam, Sum.elim_inr, Ga, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
    induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
      simp [FlagG.fvec, F'.fl.e_iso, F'.fl.z_orth, F'.fl.z_norm, hze']

/- English proof (translation)
Establish `hdet : (Ga T T' (ZhatL (lf D F0) F')).det ≠ 0`. Rewrite using `[PI.UnitaryGroupMassFormula.CntFormula.DetGa.det_Ga]`. Use `mul_ne_zero ?_ hG` and prove the remaining obligations. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.sumComm (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)))) with h1 | h1 <;>`. Apply the tactic sequence `rw [h1] <;> simp`.

Apply `Matrix.eq_zero_of_mulVec_eq_zero hdet` to reduce the goal to its premises. Use function extensionality and compare the values at `a`. Establish `ha` using `h a`. Simplify using `only [map_sum, map_smul, smul_eq_mul, hT_fam] at ha`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.zero_apply]`.

Rewrite using `[← ha]`. Conclude with `Finset.sum_congr rfl (fun i _ => mul_comm _ _)`.
-/
theorem eq_zero_of_orth (hG : GZ T T' (ZhatL (lf D F0) F') ≠ 0)
    (c : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → D.host.E)
    (h : ∀ a, (VS D).hT (fam F0 F' a) (∑ i, c i • fam F0 F' i) = 0) : c = 0 := by
  have hdet : (Ga T T' (ZhatL (lf D F0) F')).det ≠ 0 := by
    rw [PI.UnitaryGroupMassFormula.CntFormula.DetGa.det_Ga]
    refine mul_ne_zero ?_ hG
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.sumComm (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)))) with h1 | h1 <;>
      rw [h1] <;> simp
  apply Matrix.eq_zero_of_mulVec_eq_zero hdet
  funext a
  have ha := h a
  simp only [map_sum, map_smul, smul_eq_mul, hT_fam] at ha
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  rw [← ha]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc`. Establish `h0` using `eq_zero_of_orth F0 F' hG c (fun a => by rw [hc, map_zero])`. Introduce `i`. Conclude with `congrFun h0 i`.
-/
theorem fam_li (hG : GZ T T' (ZhatL (lf D F0) F') ≠ 0) : LinearIndependent D.host.E (fam F0 F') := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h0 := eq_zero_of_orth F0 F' hG c (fun a => by rw [hc, map_zero])
  intro i
  exact congrFun h0 i

/- English proof (translation)
Simplify using `only [orthK, Submodule.mem_iInf, LinearMap.mem_ker]`.
-/
theorem mem_orthK {U : Submodule D.host.E (VS D).V} {x : (VS D).V} :
    x ∈ orthK (VS D).hT U ↔ ∀ u ∈ U, (VS D).hT u x = 0 := by
  simp only [orthK, Submodule.mem_iInf, LinearMap.mem_ker]

/- English proof (translation)
Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Rewrite `hx` using `[Submodule.mem_inf]`. Take `⟨hxU, hxO⟩` from `hx`. Rewrite `hxU` using `[upair_eq, Submodule.mem_span_range_iff_exists_fun]`.

Take `⟨c, rfl⟩` from `hxU`. Establish `hc` using `eq_zero_of_orth F0 F' hG c (fun a => (mem_orthK.mp hxO) _ (by rw [upair_eq]; exact Submodule.subset_span ⟨a, rfl⟩))`. Rewrite using `[Submodule.mem_bot, hc]`. Simplify using the standard rewrite rules.
-/
theorem inf_orth (hG : GZ T T' (ZhatL (lf D F0) F') ≠ 0) :
    UPair D F0 F' ⊓ orthK (VS D).hT (UPair D F0 F') = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_inf] at hx
  obtain ⟨hxU, hxO⟩ := hx
  rw [upair_eq, Submodule.mem_span_range_iff_exists_fun] at hxU
  obtain ⟨c, rfl⟩ := hxU
  have hc := eq_zero_of_orth F0 F' hG c (fun a => (mem_orthK.mp hxO) _
    (by rw [upair_eq]; exact Submodule.subset_span ⟨a, rfl⟩))
  rw [Submodule.mem_bot, hc]
  simp

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[disjoint_iff]`. Conclude with `inf_orth F0 F' hG`. Rewrite using `[codisjoint_iff, eq_top_iff]`. Introduce `v _`.

Set `Φ : ((Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) → D.host.E) →ₗ[D.host.E] ((Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) → D.host.E)` to `{ toFun := fun c a => (VS D).hT (fam F0 F' a) (∑ i, c i • fam F0 F' i) map_add' := by`. Introduce `c d`. Use extensionality with `a`. Simplify using `[add_smul, Finset.sum_add_distrib]`. Use the proof step `map_smul' := by`.

Introduce `s c`. Use extensionality with `a`. Simplify using `[mul_smul, ← Finset.smul_sum, mul_add] }`. Establish `hinj : Function.Injective Φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce `c hc`. Conclude with `eq_zero_of_orth F0 F' hG c (fun a => congrFun hc a)`. Take `⟨c, hc⟩` from `(LinearMap.injective_iff_surjective.mp hinj) (fun a => (VS D).hT (fam F0 F' a) v)`. Establish `hu : ∑ i, c i • fam F0 F' i ∈ UPair D F0 F'`. Rewrite using `[upair_eq]`.

Conclude with `Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))`. Establish `hw : v - ∑ i, c i • fam F0 F' i ∈ orthK (VS D).hT (UPair D F0 F')`. Rewrite using `[mem_orthK]`. Introduce `u hu'`. Rewrite `hu'` using `[upair_eq]`.

Proceed by induction on `hu' using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, rfl⟩` from `hx`. Establish `h1` using `congrFun hc a`. Simplify using `only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at h1`.

Rewrite using `[map_sub, h1, sub_self]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]`. Consider the case `smul s x _ hx => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hx, smul_zero]`. Establish `hv : v = ∑ i, c i • fam F0 F' i + (v - ∑ i, c i • fam F0 F' i)` using `by abel`.

Rewrite using `[hv]`. Conclude with `Submodule.add_mem_sup hu hw`.
-/
theorem isCompl (hG : GZ T T' (ZhatL (lf D F0) F') ≠ 0) :
    IsCompl (UPair D F0 F') (orthK (VS D).hT (UPair D F0 F')) := by
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff]
    exact inf_orth F0 F' hG
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    let Φ : ((Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) → D.host.E) →ₗ[D.host.E]
        ((Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) → D.host.E) :=
      { toFun := fun c a => (VS D).hT (fam F0 F' a) (∑ i, c i • fam F0 F' i)
        map_add' := by
          intro c d
          ext a
          simp [add_smul, Finset.sum_add_distrib]
        map_smul' := by
          intro s c
          ext a
          simp [mul_smul, ← Finset.smul_sum, mul_add] }
    have hinj : Function.Injective Φ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro c hc
      exact eq_zero_of_orth F0 F' hG c (fun a => congrFun hc a)
    obtain ⟨c, hc⟩ := (LinearMap.injective_iff_surjective.mp hinj) (fun a => (VS D).hT (fam F0 F' a) v)
    have hu : ∑ i, c i • fam F0 F' i ∈ UPair D F0 F' := by
      rw [upair_eq]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    have hw : v - ∑ i, c i • fam F0 F' i ∈ orthK (VS D).hT (UPair D F0 F') := by
      rw [mem_orthK]
      intro u hu'
      rw [upair_eq] at hu'
      induction hu' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        have h1 := congrFun hc a
        simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at h1
        rw [map_sub, h1, sub_self]
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
      | smul s x _ hx => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hx, smul_zero]
    have hv : v = ∑ i, c i • fam F0 F' i + (v - ∑ i, c i • fam F0 F' i) := by abel
    rw [hv]
    exact Submodule.add_mem_sup hu hw

/- English proof (translation)
Rewrite using `[upair_eq, finrank_span_eq_card (fam_li F0 F' hG)]`. Simplify using `only [Fintype.card_sum, Fintype.card_fin]`. Use `D.R.rS_two` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_upair (hG : GZ T T' (ZhatL (lf D F0) F') ≠ 0) :
    finrank D.host.E (UPair D F0 F') = D.R.m := by
  rw [upair_eq, finrank_span_eq_card (fam_li F0 F' hG)]
  simp only [Fintype.card_sum, Fintype.card_fin]
  have := D.R.rS_two
  omega

/- English proof (translation)
Rewrite using `[(VS D).rank_eq, D.sp.Y_rank 0 (Nat.zero_le _)]`. Simplify using `[Formalism.BasicNotions.Ranks.rankY]`.
-/
theorem finrank_V : finrank D.host.E (VS D).V = D.R.r := by
  rw [(VS D).rank_eq, D.sp.Y_rank 0 (Nat.zero_le _)]
  simp [Formalism.BasicNotions.Ranks.rankY]

/- English proof (translation)
Unfold `FlagG.X UPair`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `left`.

Conclude with `⟨i.castSucc, by simp [FlagG.fvec]⟩`.
-/
theorem X_le_upair : F0.X ≤ UPair D F0 F' := by
  unfold FlagG.X UPair
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  apply Submodule.subset_span
  left
  exact ⟨i.castSucc, by simp [FlagG.fvec]⟩

/- English proof (translation)
Unfold `UPair`. Conclude with `Submodule.subset_span (Or.inl ⟨Fin.last _, by simp [FlagG.fvec]⟩)`.
-/
theorem z_mem_upair : F0.z ∈ UPair D F0 F' := by
  unfold UPair
  exact Submodule.subset_span (Or.inl ⟨Fin.last _, by simp [FlagG.fvec]⟩)

/- English proof (translation)
Unfold `FlagG.Xplus`. Conclude with `sup_le (X_le_upair F0 F') ((Submodule.span_singleton_le_iff_mem _ _).mpr (z_mem_upair F0 F'))`.
-/
theorem Xplus_le_upair : F0.Xplus ≤ UPair D F0 F' := by
  unfold FlagG.Xplus
  exact sup_le (X_le_upair F0 F') ((Submodule.span_singleton_le_iff_mem _ _).mpr (z_mem_upair F0 F'))

end PairSpanDimension

open PairSpanDimension in

/- English proof (translation)
Introduce `D u u' _ F0 what₂ _ Z F' _ hZ hP`. Establish `hG : GZ (Tn u) (Tn u') (ZhatL (lf D F0) F') ≠ 0` using `by rw [hZ]; exact totPos_ne_zero hP`. Establish `hC` using `PairSpanDimension.isCompl F0 F' hG`. Establish `hU` using `PairSpanDimension.finrank_upair F0 F' hG`. Establish `hW : finrank D.host.E (orthK (VS D).hT (UPair D F0 F')) = D.R.k - 1`.

Establish `h1` using `Submodule.finrank_add_eq_of_isCompl hC`. Establish `h2` using `D.R.r_eq`. Rewrite `h1` using `[PairSpanDimension.finrank_V, hU]`. Use linear arithmetic over natural numbers and integers. Use `⟨hC, ?_, hU, hW⟩` and prove the remaining obligations.

Introduce `x hx hx0 φ`. Establish `hpos` using `Formalism.MainNotions.LatticeGluingRadicals.p_posX D (D.mem u).A.T (D.mem u).A.T_prime.pos (lf D F0)`. Establish `hxO : x ∈ orth (VS D) (Xplus (lf D F0))`. Rewrite using `[Formalism.MainNotions.LatticeGluingRadicals.p_mem_orth]`. Introduce `w hw`.

Conclude with `(PairSpanDimension.mem_orthK.1 hx) w (PairSpanDimension.Xplus_le_upair F0 F' hw)`. Establish `hxX : x ∉ Xsp (lf D F0)`. Introduce `hxX`. Establish `: x ∈ UPair D F0 F' ⊓ orthK (VS D).hT (UPair D F0 F')` using `⟨PairSpanDimension.X_le_upair F0 F' hxX, hx⟩`. Rewrite `this` using `[PairSpanDimension.inf_orth F0 F' hG]`.

Conclude with `hx0 ((Submodule.mem_bot _).1 this)`. Conclude with `hpos φ x hxO hxX`.
-/
theorem perpendicular_definition_holds : PerpDef := by
  intro D u u' _ F0 what₂ _ Z F' _ hZ hP
  have hG : GZ (Tn u) (Tn u') (ZhatL (lf D F0) F') ≠ 0 := by rw [hZ]; exact totPos_ne_zero hP
  have hC := PairSpanDimension.isCompl F0 F' hG
  have hU := PairSpanDimension.finrank_upair F0 F' hG
  have hW : finrank D.host.E (orthK (VS D).hT (UPair D F0 F')) = D.R.k - 1 := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hC
    have h2 := D.R.r_eq
    rw [PairSpanDimension.finrank_V, hU] at h1
    omega
  refine ⟨hC, ?_, hU, hW⟩
  intro x hx hx0 φ
  have hpos := Formalism.MainNotions.LatticeGluingRadicals.p_posX D (D.mem u).A.T (D.mem u).A.T_prime.pos (lf D F0)
  have hxO : x ∈ orth (VS D) (Xplus (lf D F0)) := by
    rw [Formalism.MainNotions.LatticeGluingRadicals.p_mem_orth]
    intro w hw
    exact (PairSpanDimension.mem_orthK.1 hx) w (PairSpanDimension.Xplus_le_upair F0 F' hw)
  have hxX : x ∉ Xsp (lf D F0) := by
    intro hxX
    have : x ∈ UPair D F0 F' ⊓ orthK (VS D).hT (UPair D F0 F') := ⟨PairSpanDimension.X_le_upair F0 F' hxX, hx⟩
    rw [PairSpanDimension.inf_orth F0 F' hG] at this
    exact hx0 ((Submodule.mem_bot _).1 this)
  exact hpos φ x hxO hxX

end Formalism.L2.SG.Pf.Cnt

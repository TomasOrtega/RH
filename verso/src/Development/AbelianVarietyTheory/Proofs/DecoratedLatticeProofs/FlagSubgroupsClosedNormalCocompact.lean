import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.Unf.FlagSub

variable {D : D7} {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ)

variable {D : D7} {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ)

local instance topRingAE : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1

local instance t2AE : T2Space (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.1

local instance topAddAE : IsTopologicalAddGroup (AE D) := inferInstance

set_option synthInstance.maxHeartbeats 400000 in
local instance contSubVec (n : ℕ) : ContinuousSub (Fin n → AE D) := inferInstance

set_option synthInstance.maxHeartbeats 400000 in
local instance contSubMx (m n : ℕ) : ContinuousSub (Mx D m n) := inferInstance

local instance t2Mx (m n : ℕ) : T2Space (Mx D m n) := (lattice_Mx D m n).2.2.2.1

/- English proof (translation)
The claim follows from `isClosed_eq ((continuous_mt (S := V)).matrix_mul continuous_const) continuous_const`.
-/
theorem isClosed_fixer {k : ℕ} (x : Mx D V.rank k) : IsClosed (fixer V x : Set (GA D V)) :=
  isClosed_eq ((continuous_mt (S := V)).matrix_mul continuous_const) continuous_const

/- English proof (translation)
Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩`. Conclude with `⟨d.nC_jX c, d.nC_j0 c⟩`. Introduce and unpack `⟨h1, h2⟩`.

Take `⟨c, rfl⟩` from `GlobalTheory.MixPer.Decomp.eq_nC d h1 h2`. Conclude with `⟨c, rfl⟩`.
-/
theorem centre_eq : (centre d : Set (GA D V)) = {g | mt V g ⬝ d.jX = d.jX} ∩ {g | mt V g ⬝ d.j0 = d.j0} := by
  ext g
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨d.nC_jX c, d.nC_j0 c⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨c, rfl⟩ := GlobalTheory.MixPer.Decomp.eq_nC d h1 h2
    exact ⟨c, rfl⟩

/- English proof (translation)
Rewrite using `[centre_eq]`. Conclude with `(isClosed_eq ((continuous_mt (S := V)).matrix_mul continuous_const) continuous_const).inter (isClosed_eq ((continuous_mt (S := V)).matrix_mul continuous_const) continuous_const)`.
-/
theorem isClosed_centre : IsClosed (centre d : Set (GA D V)) := by
  rw [centre_eq]
  exact (isClosed_eq ((continuous_mt (S := V)).matrix_mul continuous_const) continuous_const).inter
    (isClosed_eq ((continuous_mt (S := V)).matrix_mul continuous_const) continuous_const)

/- English proof (translation)
Take `⟨u, hu, b, c, rfl⟩` from `GlobalTheory.MixPer.Decomp.flag_decomp d hk`. Conclude with `⟨u, hu, GlobalTheory.MixPer.Decomp.mt_flag_jX d u b c⟩`.
-/
theorem flag_jX {k : GA D V} (hk : k ∈ flagN d) : ∃ u ∈ UX D ρ, mt V k ⬝ d.jX = d.jX ⬝ u.1 := by
  obtain ⟨u, hu, b, c, rfl⟩ := GlobalTheory.MixPer.Decomp.flag_decomp d hk
  exact ⟨u, hu, GlobalTheory.MixPer.Decomp.mt_flag_jX d u b c⟩

/- English proof (translation)
Rewrite using `[Subgroup.normal_subgroupOf_iff (show radX d ≤ flagN d from inf_le_left)]`. Introduce `h k hh hk`. Establish `hh1 : h ∈ flagN d` using `(Subgroup.mem_inf.1 hh).1`. Use `Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hk hh1) (inv_mem hk), ?_⟩` and prove the remaining obligations. Take `⟨u, -, hu⟩` from `flag_jX d (inv_mem hk)`.

Establish `hh2 : mt V h ⬝ d.jX = d.jX` using `(Subgroup.mem_inf.1 hh).2`. Establish `e1 : mt V h ⬝ (mt V k⁻¹ ⬝ d.jX) = mt V k⁻¹ ⬝ d.jX` using `by rw [hu, ← Matrix.mul_assoc, hh2]`. Express the relevant statement in the definitionally equal form `mt V (k * h * k⁻¹) ⬝ d.jX = d.jX`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem radX_normal : ((radX d).subgroupOf (flagN d)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (show radX d ≤ flagN d from inf_le_left)]
  intro h k hh hk
  have hh1 : h ∈ flagN d := (Subgroup.mem_inf.1 hh).1
  refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hk hh1) (inv_mem hk), ?_⟩
  obtain ⟨u, -, hu⟩ := flag_jX d (inv_mem hk)
  have hh2 : mt V h ⬝ d.jX = d.jX := (Subgroup.mem_inf.1 hh).2
  have e1 : mt V h ⬝ (mt V k⁻¹ ⬝ d.jX) = mt V k⁻¹ ⬝ d.jX := by rw [hu, ← Matrix.mul_assoc, hh2]
  change mt V (k * h * k⁻¹) ⬝ d.jX = d.jX
  calc mt V (k * h * k⁻¹) ⬝ d.jX = mt V k ⬝ (mt V h ⬝ (mt V k⁻¹ ⬝ d.jX)) := by simp only [mt_mul, Matrix.mul_assoc]
    _ = d.jX := by rw [e1, ← Matrix.mul_assoc, ← mt_mul, mul_inv_cancel, mt_one, Matrix.one_mul]

/- English proof (translation)
Introduce and unpack `g ⟨c, rfl⟩`. Conclude with `d.nC_mem_NFlag c`.
-/
theorem centre_le : centre d ≤ flagN d := by
  rintro g ⟨c, rfl⟩
  exact d.nC_mem_NFlag c

/- English proof (translation)
Rewrite using `[Subgroup.normal_subgroupOf_iff (centre_le d)]`. Introduce and unpack `h k ⟨c, rfl⟩ hk`. Take `⟨u, -, b, c', rfl⟩` from `GlobalTheory.MixPer.Decomp.flag_decomp d hk`. Use `⟨skewConj u.1 c, ?_⟩` and prove the remaining obligations. Establish `e1 : d.nC c' * d.nC c * (d.nC c')⁻¹ = d.nC c`.

Rewrite using `[d.nC_inv, ← d.nC_add, ← d.nC_add]`. Use `congr 1`. Normalize the expressions using the abelian group laws. Establish `e2 : d.nB b * d.nC c * (d.nB b)⁻¹ = d.nC c`. Rewrite using `[← d.nC_mul_nB (c := c) (b := b), mul_inv_cancel_right]`.

Establish `e3 : d.levi u * d.nC c * (d.levi u)⁻¹ = d.nC (skewConj u.1 c)`. Rewrite using `[d.levi_mul_nC, mul_inv_cancel_right]`. Use `symm`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem centre_normal : ((centre d).subgroupOf (flagN d)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (centre_le d)]
  rintro h k ⟨c, rfl⟩ hk
  obtain ⟨u, -, b, c', rfl⟩ := GlobalTheory.MixPer.Decomp.flag_decomp d hk
  refine ⟨skewConj u.1 c, ?_⟩
  have e1 : d.nC c' * d.nC c * (d.nC c')⁻¹ = d.nC c := by
    rw [d.nC_inv, ← d.nC_add, ← d.nC_add]
    congr 1
    abel
  have e2 : d.nB b * d.nC c * (d.nB b)⁻¹ = d.nC c := by
    rw [← d.nC_mul_nB (c := c) (b := b), mul_inv_cancel_right]
  have e3 : d.levi u * d.nC c * (d.levi u)⁻¹ = d.nC (skewConj u.1 c) := by
    rw [d.levi_mul_nC, mul_inv_cancel_right]
  symm
  calc d.levi u * (d.nB b * d.nC c') * d.nC c * (d.levi u * (d.nB b * d.nC c'))⁻¹
      = d.levi u * (d.nB b * (d.nC c' * d.nC c * (d.nC c')⁻¹) * (d.nB b)⁻¹) * (d.levi u)⁻¹ := by group
    _ = d.nC (skewConj u.1 c) := by rw [e1, e2, e3]

/- English proof (translation)
Rewrite using `[mem_fixer]`. Prove the components needed by the constructor for the conclusion. Introduce `H r`. Use `congrFun (congrFun H r) 0` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply]`.

Introduce `H`. Use extensionality with `r a`. Use `H r` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply]`.
-/
theorem fix_col_iff (h : GA D V) (i : Fin ρ) :
    h ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => i) ↔ ∀ r, (mt V h ⬝ d.jX) r i = d.jX r i := by
  rw [mem_fixer]
  constructor
  · intro H r
    have := congrFun (congrFun H r) 0
    simpa [Matrix.mul_apply] using this
  · intro H
    ext r a
    have := H r
    simpa [Matrix.mul_apply] using this

/- English proof (translation)
Rewrite using `[Nfix, Subgroup.mem_inf, Subgroup.mem_iInf]`. Use `and_congr Iff.rfl ⟨fun H l hl => (fix_col_iff d h l).1 (H ⟨l, hl⟩), fun H l => (fix_col_iff d h l.1).2 (H l.1 l.2)⟩` and prove the remaining obligations.
-/
theorem mem_Nfix_iff (h : GA D V) (j : Fin ρ) :
    h ∈ Nfix d j ↔ h ∈ flagN d ∧ ∀ l : Fin ρ, l ≤ j → ∀ r, (mt V h ⬝ d.jX) r l = d.jX r l := by
  rw [Nfix, Subgroup.mem_inf, Subgroup.mem_iInf]
  refine and_congr Iff.rfl ⟨fun H l hl => (fix_col_iff d h l).1 (H ⟨l, hl⟩), fun H l => (fix_col_iff d h l.1).2 (H l.1 l.2)⟩

/- English proof (translation)
Introduce `h hh` and use `((mem_Nfix_iff d h j).1 hh).1`.
-/
theorem Nfix_le (j : Fin ρ) : Nfix d j ≤ flagN d := fun h hh => ((mem_Nfix_iff d h j).1 hh).1

/- English proof (translation)
Rewrite using `[Subgroup.normal_subgroupOf_iff (Nfix_le d j)]`. Introduce `h k hh hk`. Take `⟨hh1, hh2⟩` from `(mem_Nfix_iff d h j).1 hh`. Use `(mem_Nfix_iff d _ j).2 ⟨mul_mem (mul_mem hk hh1) (inv_mem hk), fun i hi r => ?_⟩` and prove the remaining obligations. Take `⟨u, hu, hku⟩` from `flag_jX d (inv_mem hk)`.

Establish `hcol : ∀ s, ((mt V h ⬝ d.jX) ⬝ u.1) s i = (d.jX ⬝ u.1) s i`. Introduce `s`. Rewrite using `[Matrix.mul_apply (M := mt V h ⬝ d.jX), Matrix.mul_apply (M := d.jX)]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : l ≤ i`.

Rewrite using `[hh2 l (hl.trans hi) s]`. Rewrite using `[(hu l i).1 (not_le.1 hl), mul_zero, mul_zero]`. Establish `e : mt V (k * h * k⁻¹) ⬝ d.jX = mt V k ⬝ ((mt V h ⬝ d.jX) ⬝ u.1)`. Rewrite using `[mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, hku, Matrix.mul_assoc]`. Establish `e2 : mt V k ⬝ (d.jX ⬝ u.1) = d.jX`.

Rewrite using `[← hku, ← Matrix.mul_assoc, ← mt_mul, mul_inv_cancel, mt_one, Matrix.one_mul]`. Rewrite using `[e]`. Use `conv_rhs => rw [← e2]`. Rewrite using `[Matrix.mul_apply (M := mt V k), Matrix.mul_apply (M := mt V k)]`. Conclude with `Finset.sum_congr rfl fun s _ => by rw [hcol s]`.
-/
theorem Nfix_normal (j : Fin ρ) : ((Nfix d j).subgroupOf (flagN d)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (Nfix_le d j)]
  intro h k hh hk
  obtain ⟨hh1, hh2⟩ := (mem_Nfix_iff d h j).1 hh
  refine (mem_Nfix_iff d _ j).2 ⟨mul_mem (mul_mem hk hh1) (inv_mem hk), fun i hi r => ?_⟩
  obtain ⟨u, hu, hku⟩ := flag_jX d (inv_mem hk)
  have hcol : ∀ s, ((mt V h ⬝ d.jX) ⬝ u.1) s i = (d.jX ⬝ u.1) s i := by
    intro s
    rw [Matrix.mul_apply (M := mt V h ⬝ d.jX), Matrix.mul_apply (M := d.jX)]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l ≤ i
    · rw [hh2 l (hl.trans hi) s]
    · rw [(hu l i).1 (not_le.1 hl), mul_zero, mul_zero]
  have e : mt V (k * h * k⁻¹) ⬝ d.jX = mt V k ⬝ ((mt V h ⬝ d.jX) ⬝ u.1) := by
    rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, hku, Matrix.mul_assoc]
  have e2 : mt V k ⬝ (d.jX ⬝ u.1) = d.jX := by
    rw [← hku, ← Matrix.mul_assoc, ← mt_mul, mul_inv_cancel, mt_one, Matrix.one_mul]
  rw [e]
  conv_rhs => rw [← e2]
  rw [Matrix.mul_apply (M := mt V k), Matrix.mul_apply (M := mt V k)]
  exact Finset.sum_congr rfl fun s _ => by rw [hcol s]

/- English proof (translation)
Use extensionality with `g`. Express the relevant statement in the definitionally equal form `g ∈ NFlag V d.e ↔ _`. Rewrite using `[GlobalTheory.BesselChar.mem_NFlag_iff V d.e (GlobalTheory.MixPer.Decomp.linInd d) g]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨T, hT, h1⟩, h2⟩`.

Establish `h1' : mt V g ⬝ d.jX = d.jX + d.jX ⬝ T` using `h1`. Establish `hP : d.pX ⬝ (mt V g ⬝ d.jX) = 1 + T`. Rewrite using `[h1', Matrix.mul_add, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]`. Use `⟨⟨?_, ?_⟩, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[hP, Matrix.mul_add, Matrix.mul_one, h1']`.

Introduce `j i hij`. Rewrite using `[hP, add_sub_cancel_left]`. Conclude with `hT j i hij`. Take `⟨a, ha⟩` from `h2 y hy`. Establish `ha' : mt V g *ᵥ y - y = d.jX *ᵥ a`.

Rewrite using `[show mt V g *ᵥ y = y + d.jX *ᵥ a from ha, add_sub_cancel_left]`. Rewrite using `[ha', Matrix.mulVec_mulVec a d.pX d.jX, d.pX_jX, Matrix.one_mulVec]`. Introduce and unpack `⟨⟨h1, hT⟩, h2⟩`. Use `⟨⟨d.pX ⬝ (mt V g ⬝ d.jX) - 1, hT, ?_⟩, fun y hy => ⟨d.pX *ᵥ (mt V g *ᵥ y - y), ?_⟩⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `mt V g ⬝ d.jX = d.jX + d.jX ⬝ (d.pX ⬝ (mt V g ⬝ d.jX) - 1)`.

Rewrite using `[Matrix.mul_sub, Matrix.mul_one, ← h1]`. Normalize the expressions using the abelian group laws. Express the relevant statement in the definitionally equal form `mt V g *ᵥ y = y + d.jX *ᵥ (d.pX *ᵥ (mt V g *ᵥ y - y))`. Rewrite using `[← h2 y hy]`. Normalize the expressions using the abelian group laws.
-/
theorem flagN_eq : (flagN d : Set (GA D V)) = {g | (mt V g ⬝ d.jX = d.jX ⬝ (d.pX ⬝ (mt V g ⬝ d.jX)) ∧
        ∀ j i : Fin ρ, i ≤ j → (d.pX ⬝ (mt V g ⬝ d.jX) - 1) j i = 0) ∧
      ∀ y : Fin V.rank → AE D, (GlobalTheory.BesselChar.perpMat V d.e).map (incA D) *ᵥ y = 0 →
        mt V g *ᵥ y - y = d.jX *ᵥ (d.pX *ᵥ (mt V g *ᵥ y - y))} := by
  ext g
  change g ∈ NFlag V d.e ↔ _
  rw [GlobalTheory.BesselChar.mem_NFlag_iff V d.e (GlobalTheory.MixPer.Decomp.linInd d) g]
  constructor
  · rintro ⟨⟨T, hT, h1⟩, h2⟩
    have h1' : mt V g ⬝ d.jX = d.jX + d.jX ⬝ T := h1
    have hP : d.pX ⬝ (mt V g ⬝ d.jX) = 1 + T := by
      rw [h1', Matrix.mul_add, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]
    refine ⟨⟨?_, ?_⟩, fun y hy => ?_⟩
    · rw [hP, Matrix.mul_add, Matrix.mul_one, h1']
    · intro j i hij
      rw [hP, add_sub_cancel_left]
      exact hT j i hij
    · obtain ⟨a, ha⟩ := h2 y hy
      have ha' : mt V g *ᵥ y - y = d.jX *ᵥ a := by
        rw [show mt V g *ᵥ y = y + d.jX *ᵥ a from ha, add_sub_cancel_left]
      rw [ha', Matrix.mulVec_mulVec a d.pX d.jX, d.pX_jX, Matrix.one_mulVec]
  · rintro ⟨⟨h1, hT⟩, h2⟩
    refine ⟨⟨d.pX ⬝ (mt V g ⬝ d.jX) - 1, hT, ?_⟩, fun y hy => ⟨d.pX *ᵥ (mt V g *ᵥ y - y), ?_⟩⟩
    · change mt V g ⬝ d.jX = d.jX + d.jX ⬝ (d.pX ⬝ (mt V g ⬝ d.jX) - 1)
      rw [Matrix.mul_sub, Matrix.mul_one, ← h1]
      abel
    · change mt V g *ᵥ y = y + d.jX *ᵥ (d.pX *ᵥ (mt V g *ᵥ y - y))
      rw [← h2 y hy]
      abel

/- English proof (translation)
Establish `hM : Continuous (mt V)` using `continuous_mt (S := V)`. Establish `hA : Continuous fun g : GA D V => d.pX ⬝ (mt V g ⬝ d.jX)` using `continuous_const.matrix_mul (hM.matrix_mul continuous_const)`. Rewrite using `[flagN_eq, Set.setOf_and, Set.setOf_and]`. Use `IsClosed.inter (IsClosed.inter ?_ ?_) ?_` and prove the remaining obligations. Conclude with `isClosed_eq (hM.matrix_mul continuous_const) (continuous_const.matrix_mul hA)`.

Simplify using `only [Set.setOf_forall]`. Use `isClosed_iInter fun j => isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_eq ?_ continuous_const` and prove the remaining obligations. Conclude with `(continuous_apply i).comp ((continuous_apply j).comp (hA.sub continuous_const))`. Simplify using `only [Set.setOf_forall]`. Use `isClosed_iInter fun y => isClosed_iInter fun _ => isClosed_eq ?_ ?_` and prove the remaining obligations.

Conclude with `(hM.matrix_mulVec continuous_const).sub continuous_const`. Conclude with `continuous_const.matrix_mulVec (continuous_const.matrix_mulVec ((hM.matrix_mulVec continuous_const).sub continuous_const))`.
-/
theorem isClosed_flagN : IsClosed (flagN d : Set (GA D V)) := by
  have hM : Continuous (mt V) := continuous_mt (S := V)
  have hA : Continuous fun g : GA D V => d.pX ⬝ (mt V g ⬝ d.jX) :=
    continuous_const.matrix_mul (hM.matrix_mul continuous_const)
  rw [flagN_eq, Set.setOf_and, Set.setOf_and]
  refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
  · exact isClosed_eq (hM.matrix_mul continuous_const) (continuous_const.matrix_mul hA)
  · simp only [Set.setOf_forall]
    refine isClosed_iInter fun j => isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_eq ?_ continuous_const
    exact (continuous_apply i).comp ((continuous_apply j).comp (hA.sub continuous_const))
  · simp only [Set.setOf_forall]
    refine isClosed_iInter fun y => isClosed_iInter fun _ => isClosed_eq ?_ ?_
    · exact (hM.matrix_mulVec continuous_const).sub continuous_const
    · exact continuous_const.matrix_mulVec (continuous_const.matrix_mulVec
        ((hM.matrix_mulVec continuous_const).sub continuous_const))

local instance topGrpGA (S : HSp D) : IsTopologicalGroup (GA D S) := (Formalism.IndefR.Eqv.ga_facts D S).1

def skPart (x : Mx D ρ ρ) : skewA D ρ :=
  ⟨half D • (x - adj x), by rw [mem_skewA, adj_smul, cA_half, adj_sub, adj_adj, ← smul_neg, neg_sub]⟩

/- English proof (translation)
Establish `h1 : Continuous fun x : Mx D ρ ρ => x - adj x` using `continuous_id.sub continuous_adj`. Establish `h2 : Continuous fun x : Mx D ρ ρ => half D • (x - adj x)` using `h1.const_smul (half D)`. Conclude with `continuous_induced_rng.2 h2`.
-/
theorem continuous_skPart : Continuous (skPart (D := D) (ρ := ρ)) :=
  by
  have h1 : Continuous fun x : Mx D ρ ρ => x - adj x := continuous_id.sub continuous_adj
  have h2 : Continuous fun x : Mx D ρ ρ => half D • (x - adj x) := h1.const_smul (half D)
  exact continuous_induced_rng.2 h2

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `half D • (x + c.1 - adj (x + c.1)) = half D • (x - adj x) + c.1`. Rewrite using `[adj_add, mem_skewA.1 c.2, show x + c.1 - (adj x + -c.1) = (x - adj x) + (c.1 + c.1) by abel, smul_add, smul_add, half_smul_add]`.
-/
theorem skPart_add_skew (x : Mx D ρ ρ) (c : skewA D ρ) : skPart (x + c.1) = skPart x + c := by
  apply Subtype.ext
  change half D • (x + c.1 - adj (x + c.1)) = half D • (x - adj x) + c.1
  rw [adj_add, mem_skewA.1 c.2, show x + c.1 - (adj x + -c.1) = (x - adj x) + (c.1 + c.1) by abel, smul_add, smul_add,
    half_smul_add]

/- English proof (translation)
The claim follows from `ratMx_smul (1 / 2) (sub_mem hx (ratMx_adj hx))`.
-/
theorem skPart_rat {x : Mx D ρ ρ} (hx : x ∈ ratMx D ρ ρ) : (skPart x).1 ∈ ratMx D ρ ρ :=
  ratMx_smul (1 / 2) (sub_mem hx (ratMx_adj hx))

/- English proof (translation)
Take `⟨-, -, -, -, -, K0, hK0, hcov⟩` from `lattice_Mx D ρ ρ`. Use `⟨K0, hK0, fun c => ?_⟩` and prove the remaining obligations. Take `⟨γ, hγ, hk⟩` from `hcov c.1`. Use `⟨-skPart γ, neg_mem (skPart_rat hγ), _, hk, ?_⟩` and prove the remaining obligations. Rewrite using `[skPart_add_skew, neg_add_cancel_left]`.
-/
theorem skew_reduce : ∃ K0 : Set (Mx D ρ ρ), IsCompact K0 ∧ ∀ c : skewA D ρ, ∃ s : skewA D ρ, s.1 ∈ ratMx D ρ ρ ∧
    ∃ x ∈ K0, c = s + skPart x := by
  obtain ⟨-, -, -, -, -, K0, hK0, hcov⟩ := lattice_Mx D ρ ρ
  refine ⟨K0, hK0, fun c => ?_⟩
  obtain ⟨γ, hγ, hk⟩ := hcov c.1
  refine ⟨-skPart γ, neg_mem (skPart_rat hγ), _, hk, ?_⟩
  rw [skPart_add_skew, neg_add_cancel_left]

/- English proof (translation)
Take `⟨K0, hK0, hred⟩` from `skew_reduce (D := D) (ρ := ρ)`. Set `f : Mx D ρ ρ → centre d` to `fun x => ⟨d.nC (skPart x), skPart x, rfl⟩`. Establish `hf : Continuous f` using `(d.continuous_nC.comp continuous_skPart).subtype_mk _`. Use `⟨f '' K0, hK0.image hf, fun m => ?_⟩` and prove the remaining obligations. Take `⟨g, c, rfl⟩` from `m`.

Take `⟨s, hs, x, hx, rfl⟩` from `hred c`. Use `⟨⟨d.nC s, s, rfl⟩, Subgroup.mem_subgroupOf.2 (d.nC_mem_GQ hs), f x, ⟨x, hx, rfl⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `d.nC (s + skPart x) = d.nC s * d.nC (skPart x)`. Rewrite using `[d.nC_add]`.
-/
theorem centre_cocompact : ∃ K : Set (centre d), IsCompact K ∧
    ∀ m, ∃ γ ∈ (GQ V).subgroupOf (centre d), ∃ k ∈ K, m = γ * k := by
  obtain ⟨K0, hK0, hred⟩ := skew_reduce (D := D) (ρ := ρ)
  let f : Mx D ρ ρ → centre d := fun x => ⟨d.nC (skPart x), skPart x, rfl⟩
  have hf : Continuous f := (d.continuous_nC.comp continuous_skPart).subtype_mk _
  refine ⟨f '' K0, hK0.image hf, fun m => ?_⟩
  obtain ⟨g, c, rfl⟩ := m
  obtain ⟨s, hs, x, hx, rfl⟩ := hred c
  refine ⟨⟨d.nC s, s, rfl⟩, Subgroup.mem_subgroupOf.2 (d.nC_mem_GQ hs), f x, ⟨x, hx, rfl⟩, ?_⟩
  apply Subtype.ext
  change d.nC (s + skPart x) = d.nC s * d.nC (skPart x)
  rw [d.nC_add]

/- English proof (translation)
Take `⟨K0, hK0, hred⟩` from `skew_reduce (D := D) (ρ := ρ)`. Take `⟨-, -, -, -, -, Kb, hKb, hcov⟩` from `lattice_Mx D ρ V₀.rank`. Set `f : Mx D ρ V₀.rank × Mx D ρ ρ → radX d` to `fun p => ⟨d.nB p.1 * d.nC (skPart p.2), (GlobalTheory.MixPer.Decomp.mem_radX_iff d).2 ⟨_, _, rfl⟩⟩`. Establish `hf : Continuous f` using `Continuous.subtype_mk ((d.continuous_nB.comp continuous_fst).mul (d.continuous_nC.comp (continuous_skPart.comp continuous_snd))) _`. Use `⟨f '' (Kb ×ˢ K0), (hKb.prod hK0).image hf, fun m => ?_⟩` and prove the remaining obligations.

Take `⟨n, hn⟩` from `m`. Take `⟨b, c, rfl⟩` from `(GlobalTheory.MixPer.Decomp.mem_radX_iff d).1 hn`. Take `⟨β, hβ, hk⟩` from `hcov b`. Take `⟨s, hs, x, hx, hcs⟩` from `hred (cComm V₀ β b + c)`. Establish `hγ : d.nB (-β) * d.nC s ∈ radX d` using `(GlobalTheory.MixPer.Decomp.mem_radX_iff d).2 ⟨_, _, rfl⟩`.

Use `⟨⟨_, hγ⟩, Subgroup.mem_subgroupOf.2 (mul_mem (d.nB_mem_GQ (neg_mem hβ)) (d.nC_mem_GQ hs)), f (β + b, x), ⟨(β + b, x), ⟨hk, hx⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `d.nB b * d.nC c = d.nB (-β) * d.nC s * (d.nB (β + b) * d.nC (skPart x))`. Establish `e1 : d.nB b = d.nB (-β) * (d.nB (β + b) * d.nC (cComm V₀ β b))`. Rewrite using `[← d.nB_mul_nB, ← mul_assoc, ← d.nB_inv, inv_mul_cancel, one_mul]`.

Establish `e2 : d.nC (cComm V₀ β b) * d.nC c = d.nC s * d.nC (skPart x)`. Rewrite using `[← d.nC_add, ← d.nC_add, hcs]`. Rewrite using `[e1, mul_assoc, mul_assoc, e2, ← mul_assoc (d.nB (β + b)), ← d.nC_mul_nB (c := s) (b := β + b)]`. Use `group`.
-/
theorem radX_cocompact : ∃ K : Set (radX d), IsCompact K ∧
    ∀ m, ∃ γ ∈ (GQ V).subgroupOf (radX d), ∃ k ∈ K, m = γ * k := by
  obtain ⟨K0, hK0, hred⟩ := skew_reduce (D := D) (ρ := ρ)
  obtain ⟨-, -, -, -, -, Kb, hKb, hcov⟩ := lattice_Mx D ρ V₀.rank
  let f : Mx D ρ V₀.rank × Mx D ρ ρ → radX d := fun p =>
    ⟨d.nB p.1 * d.nC (skPart p.2), (GlobalTheory.MixPer.Decomp.mem_radX_iff d).2 ⟨_, _, rfl⟩⟩
  have hf : Continuous f := Continuous.subtype_mk
    ((d.continuous_nB.comp continuous_fst).mul (d.continuous_nC.comp (continuous_skPart.comp continuous_snd))) _
  refine ⟨f '' (Kb ×ˢ K0), (hKb.prod hK0).image hf, fun m => ?_⟩
  obtain ⟨n, hn⟩ := m
  obtain ⟨b, c, rfl⟩ := (GlobalTheory.MixPer.Decomp.mem_radX_iff d).1 hn
  obtain ⟨β, hβ, hk⟩ := hcov b
  obtain ⟨s, hs, x, hx, hcs⟩ := hred (cComm V₀ β b + c)
  have hγ : d.nB (-β) * d.nC s ∈ radX d := (GlobalTheory.MixPer.Decomp.mem_radX_iff d).2 ⟨_, _, rfl⟩
  refine ⟨⟨_, hγ⟩, Subgroup.mem_subgroupOf.2 (mul_mem (d.nB_mem_GQ (neg_mem hβ)) (d.nC_mem_GQ hs)),
    f (β + b, x), ⟨(β + b, x), ⟨hk, hx⟩, rfl⟩, ?_⟩
  apply Subtype.ext
  change d.nB b * d.nC c = d.nB (-β) * d.nC s * (d.nB (β + b) * d.nC (skPart x))
  have e1 : d.nB b = d.nB (-β) * (d.nB (β + b) * d.nC (cComm V₀ β b)) := by
    rw [← d.nB_mul_nB, ← mul_assoc, ← d.nB_inv, inv_mul_cancel, one_mul]
  have e2 : d.nC (cComm V₀ β b) * d.nC c = d.nC s * d.nC (skPart x) := by
    rw [← d.nC_add, ← d.nC_add, hcs]
  rw [e1, mul_assoc, mul_assoc, e2, ← mul_assoc (d.nB (β + b)), ← d.nC_mul_nB (c := s) (b := β + b)]
  group

/- English proof (translation)
Take `⟨-, -, -, -, -, K1, hK1, hcov⟩` from `lattice_Mx D 1 1`. Use `⟨(fun M : Mx D 1 1 => M 0 0) '' K1 ∪ {0}, (hK1.image ((continuous_apply 0).comp (continuous_apply 0))).union isCompact_singleton, ?_⟩` and prove the remaining obligations. Establish `hpick : ∀ a : AE D, ∃ e : D.host.E, (a = 0 → e = 0) ∧ incA D e + a ∈ (fun M : Mx D 1 1 => M 0 0) '' K1 ∪ {0}`. Introduce `a`. Distinguish the cases in `ha : a = 0`.

Use `⟨0, fun _ => rfl, Or.inr ?_⟩` and prove the remaining obligations. Rewrite using `[ha, map_zero, add_zero]`. Both sides reduce to the same expression. Take `⟨γ, hγ, hk⟩` from `hcov (Matrix.of fun _ _ => a)`. Take `⟨g, rfl⟩` from `mem_ratMx.1 hγ`.

Conclude with `⟨g 0 0, fun h => absurd h ha, Or.inl ⟨_, hk, rfl⟩⟩`. Use `choose pick h0 hp using hpick`. Conclude with `⟨pick, h0 0 rfl, hp⟩`.
-/
theorem exists_pick (D : D7) : ∃ C : Set (AE D), IsCompact C ∧ ∃ pick : AE D → D.host.E, pick 0 = 0 ∧
    ∀ a, incA D (pick a) + a ∈ C := by
  obtain ⟨-, -, -, -, -, K1, hK1, hcov⟩ := lattice_Mx D 1 1
  refine ⟨(fun M : Mx D 1 1 => M 0 0) '' K1 ∪ {0},
    (hK1.image ((continuous_apply 0).comp (continuous_apply 0))).union isCompact_singleton, ?_⟩
  have hpick : ∀ a : AE D, ∃ e : D.host.E, (a = 0 → e = 0) ∧ incA D e + a ∈ (fun M : Mx D 1 1 => M 0 0) '' K1 ∪ {0} := by
    intro a
    by_cases ha : a = 0
    · refine ⟨0, fun _ => rfl, Or.inr ?_⟩
      rw [ha, map_zero, add_zero]
      rfl
    · obtain ⟨γ, hγ, hk⟩ := hcov (Matrix.of fun _ _ => a)
      obtain ⟨g, rfl⟩ := mem_ratMx.1 hγ
      exact ⟨g 0 0, fun h => absurd h ha, Or.inl ⟨_, hk, rfl⟩⟩
  choose pick h0 hp using hpick
  exact ⟨pick, h0 0 rfl, hp⟩

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `D ρ j`. Take `⟨C, hC, pick, hp0, hp⟩` from `exists_pick D`. Set `S : Set (Matrix (Fin ρ) (Fin ρ) (AE D))` to `Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C ∪ {0, 1}`. Establish `hS : IsCompact S` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC.union (Set.toFinite _).isCompact`. Use `⟨(fun u : UX D ρ => u.1.1) ⁻¹' S, (GlobalTheory.UnitU.isClosedEmbedding_val D ρ).isCompact_preimage hS, fun u hucol => ?_⟩` and prove the remaining obligations.

Establish `hu : u.1.1 ∈ GlobalTheory.UnitU.uniSet D ρ` using `u.2`. Set `δ : Matrix (Fin ρ) (Fin ρ) D.host.E` to `fun i l => GlobalTheory.UnitU.row u.1.1 pick i l`. Establish `hδ : rat δ ∈ GlobalTheory.UnitU.uniSet D ρ`. Introduce `i l`. Use `⟨fun h => ?_, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `incA D (GlobalTheory.UnitU.row u.1.1 pick i l) = 0`. Rewrite using `[GlobalTheory.UnitU.row_eq, if_pos h, map_zero]`. Express the relevant statement in the definitionally equal form `incA D (GlobalTheory.UnitU.row u.1.1 pick i i) = 1`. Rewrite using `[GlobalTheory.UnitU.row_eq, if_neg (lt_irrefl i), if_pos rfl, map_one]`. Set `w : UX D ρ` to `⟨GlobalTheory.UnitU.toUnit (rat δ) hδ, hδ⟩`.

Establish `hwcol : ∀ l : Fin ρ, l ≤ j → ∀ s : Fin ρ, w.1.1 s l = (1 : Matrix (Fin ρ) (Fin ρ) (AE D)) s l`. Introduce `l hl s`. Express the relevant statement in the definitionally equal form `incA D (GlobalTheory.UnitU.row u.1.1 pick s l) = _`. Rewrite using `[GlobalTheory.UnitU.row_eq]`. Break down `lt_trichotomy l s with h | rfl | h` into its components or cases.

Rewrite using `[if_pos h, map_zero, Matrix.one_apply_ne h.ne']`. Rewrite using `[if_neg (lt_irrefl _), if_pos rfl, map_one, Matrix.one_apply_eq]`. Establish `h0 : (∑ l' : Fin ρ, if l' < l then incA D (GlobalTheory.UnitU.row u.1.1 pick s l') * u.1.1 l' l else 0) = 0`. Use `Finset.sum_eq_zero fun l' _ => ?_` and prove the remaining obligations. Use `split_ifs with hl'`.

Rewrite using `[hucol l hl l', Matrix.one_apply_ne hl'.ne, mul_zero]`. Both sides reduce to the same expression. Rewrite using `[if_neg (not_lt.2 h.le), if_neg h.ne', Matrix.one_apply_ne h.ne, h0, hp0, map_zero]`. Establish `hγcol : ∀ l : Fin ρ, l ≤ j → ∀ s : Fin ρ, (w⁻¹).1.1 s l = (1 : Matrix (Fin ρ) (Fin ρ) (AE D)) s l`. Introduce `l hl s`.

Establish `h1 : ((w⁻¹).1.1 * w.1.1) s l = (w⁻¹).1.1 s l`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single l (fun t _ ht => by rw [hwcol l hl t, Matrix.one_apply_ne ht, mul_zero]) (fun h => absurd (Finset.mem_univ l) h), hwcol l hl l, Matrix.one_apply_eq, mul_one]`. Rewrite using `[← h1]`. Establish `h2 : (w⁻¹).1.1 * w.1.1 = 1`. Rewrite using `[← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]`.

Both sides reduce to the same expression. Rewrite using `[h2]`. Use `⟨w⁻¹, ⟨?_, ?_⟩, hγcol, w * u, fun i _ l _ => ?_, by rw [inv_mul_cancel_left]⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.UnitU.inv_eq_adjugate w]`. Conclude with `⟨δ.adjugate, RingHom.map_adjugate (incA D) δ⟩`.

Conclude with `⟨δ, rfl⟩`. Establish `hk` using `((GlobalTheory.UnitU.mem_UX_iff _).1 (w * u).2)`. Break down `lt_trichotomy i l with hil | rfl | hil` into its components or cases. Use `Or.inl ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(rat δ * u.1.1) i l ∈ C`.

Rewrite using `[GlobalTheory.UnitU.mul_apply_of_uni δ hu i l]`. Express the relevant statement in the definitionally equal form `incA D (GlobalTheory.UnitU.row u.1.1 pick i l) + _ ∈ C`. Rewrite using `[GlobalTheory.UnitU.row_eq, if_neg (not_lt.2 hil.le), if_neg hil.ne']`. Conclude with `hp _`. Conclude with `Or.inr (Or.inr (hk i i).2)`.

Conclude with `Or.inr (Or.inl ((hk i l).1 hil))`.
-/
theorem unip_cols_cocompact : ∀ (D : D7) (ρ : ℕ) (j : Fin ρ), ∃ K : Set (UX D ρ), IsCompact K ∧ ∀ u : UX D ρ, (∀ l : Fin ρ, l ≤ j → ∀ s : Fin ρ, u.1.1 s l = (1 : Matrix (Fin ρ) (Fin ρ) (AE D)) s l) → ∃ γ ∈ UXQ D ρ, (∀ l : Fin ρ, l ≤ j → ∀ s : Fin ρ, γ.1.1 s l = (1 : Matrix (Fin ρ) (Fin ρ) (AE D)) s l) ∧ ∃ k ∈ K, u = γ * k := by
  intro D ρ j
  obtain ⟨C, hC, pick, hp0, hp⟩ := exists_pick D
  let S : Set (Matrix (Fin ρ) (Fin ρ) (AE D)) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C ∪ {0, 1}
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC.union (Set.toFinite _).isCompact
  refine ⟨(fun u : UX D ρ => u.1.1) ⁻¹' S, (GlobalTheory.UnitU.isClosedEmbedding_val D ρ).isCompact_preimage hS,
    fun u hucol => ?_⟩
  have hu : u.1.1 ∈ GlobalTheory.UnitU.uniSet D ρ := u.2
  let δ : Matrix (Fin ρ) (Fin ρ) D.host.E := fun i l => GlobalTheory.UnitU.row u.1.1 pick i l
  have hδ : rat δ ∈ GlobalTheory.UnitU.uniSet D ρ := by
    intro i l
    refine ⟨fun h => ?_, ?_⟩
    · change incA D (GlobalTheory.UnitU.row u.1.1 pick i l) = 0
      rw [GlobalTheory.UnitU.row_eq, if_pos h, map_zero]
    · change incA D (GlobalTheory.UnitU.row u.1.1 pick i i) = 1
      rw [GlobalTheory.UnitU.row_eq, if_neg (lt_irrefl i), if_pos rfl, map_one]
  let w : UX D ρ := ⟨GlobalTheory.UnitU.toUnit (rat δ) hδ, hδ⟩
  have hwcol : ∀ l : Fin ρ, l ≤ j → ∀ s : Fin ρ, w.1.1 s l = (1 : Matrix (Fin ρ) (Fin ρ) (AE D)) s l := by
    intro l hl s
    change incA D (GlobalTheory.UnitU.row u.1.1 pick s l) = _
    rw [GlobalTheory.UnitU.row_eq]
    rcases lt_trichotomy l s with h | rfl | h
    · rw [if_pos h, map_zero, Matrix.one_apply_ne h.ne']
    · rw [if_neg (lt_irrefl _), if_pos rfl, map_one, Matrix.one_apply_eq]
    · have h0 : (∑ l' : Fin ρ, if l' < l then incA D (GlobalTheory.UnitU.row u.1.1 pick s l') * u.1.1 l' l else 0) = 0 := by
        refine Finset.sum_eq_zero fun l' _ => ?_
        split_ifs with hl'
        · rw [hucol l hl l', Matrix.one_apply_ne hl'.ne, mul_zero]
        · rfl
      rw [if_neg (not_lt.2 h.le), if_neg h.ne', Matrix.one_apply_ne h.ne, h0, hp0, map_zero]
  have hγcol : ∀ l : Fin ρ, l ≤ j → ∀ s : Fin ρ, (w⁻¹).1.1 s l = (1 : Matrix (Fin ρ) (Fin ρ) (AE D)) s l := by
    intro l hl s
    have h1 : ((w⁻¹).1.1 * w.1.1) s l = (w⁻¹).1.1 s l := by
      rw [Matrix.mul_apply, Finset.sum_eq_single l (fun t _ ht => by rw [hwcol l hl t, Matrix.one_apply_ne ht, mul_zero])
        (fun h => absurd (Finset.mem_univ l) h), hwcol l hl l, Matrix.one_apply_eq, mul_one]
    rw [← h1]
    have h2 : (w⁻¹).1.1 * w.1.1 = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
      rfl
    rw [h2]
  refine ⟨w⁻¹, ⟨?_, ?_⟩, hγcol, w * u, fun i _ l _ => ?_, by rw [inv_mul_cancel_left]⟩
  · rw [GlobalTheory.UnitU.inv_eq_adjugate w]
    exact ⟨δ.adjugate, RingHom.map_adjugate (incA D) δ⟩
  · exact ⟨δ, rfl⟩
  · have hk := ((GlobalTheory.UnitU.mem_UX_iff _).1 (w * u).2)
    rcases lt_trichotomy i l with hil | rfl | hil
    · refine Or.inl ?_
      change (rat δ * u.1.1) i l ∈ C
      rw [GlobalTheory.UnitU.mul_apply_of_uni δ hu i l]
      change incA D (GlobalTheory.UnitU.row u.1.1 pick i l) + _ ∈ C
      rw [GlobalTheory.UnitU.row_eq, if_neg (not_lt.2 hil.le), if_neg hil.ne']
      exact hp _
    · exact Or.inr (Or.inr (hk i i).2)
    · exact Or.inr (Or.inl ((hk i l).1 hil))

/- English proof (translation)
Introduce `h hh`. Establish `hh2 : mt V h ⬝ d.jX = d.jX` using `(Subgroup.mem_inf.1 hh).2`. Conclude with `(mem_Nfix_iff d h j).2 ⟨(Subgroup.mem_inf.1 hh).1, fun l _ r => by rw [hh2]⟩`.
-/
theorem radX_le_Nfix (j : Fin ρ) : radX d ≤ Nfix d j := by
  intro h hh
  have hh2 : mt V h ⬝ d.jX = d.jX := (Subgroup.mem_inf.1 hh).2
  exact (mem_Nfix_iff d h j).2 ⟨(Subgroup.mem_inf.1 hh).1, fun l _ r => by rw [hh2]⟩

/- English proof (translation)
Use `(mem_Nfix_iff d _ j).2 ⟨d.levi_mem_NFlag hu, fun l hl r => ?_⟩` and prove the remaining obligations. Rewrite using `[d.levi_jX]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_apply, Matrix.mul_apply (M := d.jX)]`. Conclude with `Finset.sum_congr rfl fun s _ => by rw [hcol l hl s]`.

Use `_ = d.jX r l := by rw [Matrix.mul_one]`.
-/
theorem levi_mem_Nfix (j : Fin ρ) {u : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ)
    (hcol : ∀ l : Fin ρ, l ≤ j → ∀ s : Fin ρ, u.1 s l = (1 : Matrix (Fin ρ) (Fin ρ) (AE D)) s l) : d.levi u ∈ Nfix d j := by
  refine (mem_Nfix_iff d _ j).2 ⟨d.levi_mem_NFlag hu, fun l hl r => ?_⟩
  rw [d.levi_jX]
  calc (d.jX ⬝ u.1) r l = (d.jX ⬝ (1 : Matrix (Fin ρ) (Fin ρ) (AE D))) r l := by
        rw [Matrix.mul_apply, Matrix.mul_apply (M := d.jX)]
        exact Finset.sum_congr rfl fun s _ => by rw [hcol l hl s]
    _ = d.jX r l := by rw [Matrix.mul_one]

/- English proof (translation)
Introduce `l hl s`. Establish `H` using `((mem_Nfix_iff d _ j).1 h).2 l hl`. Rewrite `H` using `[GlobalTheory.MixPer.Decomp.mt_flag_jX]`. Establish `e1 : (d.pX ⬝ (d.jX ⬝ u.1)) s l = (d.pX ⬝ d.jX) s l`. Rewrite using `[Matrix.mul_apply, Matrix.mul_apply]`.

Conclude with `Finset.sum_congr rfl fun r _ => by rw [H r]`. Rewrite `e1` using `[← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]`. Then use the resulting hypothesis.
-/
theorem col_of_mem_Nfix (j : Fin ρ) {u : GL (Fin ρ) (AE D)} {b : Mx D ρ V₀.rank} {c : skewA D ρ}
    (h : d.levi u * (d.nB b * d.nC c) ∈ Nfix d j) :
    ∀ l : Fin ρ, l ≤ j → ∀ s : Fin ρ, u.1 s l = (1 : Matrix (Fin ρ) (Fin ρ) (AE D)) s l := by
  intro l hl s
  have H := ((mem_Nfix_iff d _ j).1 h).2 l hl
  rw [GlobalTheory.MixPer.Decomp.mt_flag_jX] at H
  have e1 : (d.pX ⬝ (d.jX ⬝ u.1)) s l = (d.pX ⬝ d.jX) s l := by
    rw [Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun r _ => by rw [H r]
  rwa [← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul] at e1

/- English proof (translation)
Take `⟨Kr, hKr, hr⟩` from `radX_cocompact d`. Take `⟨Ku, hKu, hu⟩` from `unip_cols_cocompact D ρ j`. Set `f : radX d × UX D ρ → GA D V` to `fun p => p.1.1 * d.levi p.2.1`. Establish `hf : Continuous f` using `(continuous_subtype_val.comp continuous_fst).mul (d.continuous_levi.comp (continuous_subtype_val.comp continuous_snd))`. Establish `hC : IsCompact (f '' (Kr ×ˢ Ku))` using `(hKr.prod hKu).image hf`.

Establish `hcl : IsClosed (Nfix d j : Set (GA D V))`. Rewrite using `[Nfix, Subgroup.coe_inf, Subgroup.coe_iInf]`. Conclude with `(isClosed_flagN d).inter (isClosed_iInter fun _ => isClosed_fixer _)`. Use `⟨Subtype.val ⁻¹' (f '' (Kr ×ˢ Ku)), hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hC, fun m => ?_⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `m`.

Take `⟨u, huX, b, c, rfl⟩` from `GlobalTheory.MixPer.Decomp.flag_decomp d (Nfix_le d j hn)`. Establish `hcol` using `col_of_mem_Nfix d j hn`. Take `⟨γ, hγQ, hγc, k, hk, hγk⟩` from `hu ⟨u, huX⟩ hcol`. Establish `hu' : u = γ.1 * k.1` using `congrArg Subtype.val hγk`. Establish `hrad : d.nB b * d.nC c ∈ radX d` using `(GlobalTheory.MixPer.Decomp.mem_radX_iff d).2 ⟨b, c, rfl⟩`.

Establish `hlk : d.levi k.1 ∈ flagN d` using `d.levi_mem_NFlag k.2`. Establish `hconj : d.levi k.1 * (d.nB b * d.nC c) * (d.levi k.1)⁻¹ ∈ radX d` using `(Subgroup.normal_subgroupOf_iff (show radX d ≤ flagN d from inf_le_left)).1 (radX_normal d) _ _ hrad hlk`. Take `⟨γr, hγr, kr, hkr, hrk⟩` from `hr ⟨_, hconj⟩`. Establish `hγ1 : d.levi γ.1 ∈ Nfix d j` using `levi_mem_Nfix d j γ.2 hγc`. Establish `hγr' : γr.1 ∈ Nfix d j` using `radX_le_Nfix d j γr.2`.

Establish `hn' : d.levi u * (d.nB b * d.nC c) = d.levi γ.1 * γr.1 * (kr.1 * d.levi k.1)`. Establish `e` using `congrArg Subtype.val hrk`. Simplify using `only [Subgroup.coe_mul] at e`. Establish `e2 : d.levi k.1 * (d.nB b * d.nC c) = γr.1 * kr.1 * d.levi k.1`. Rewrite using `[← e]`.

Use `group`. Rewrite using `[hu', map_mul, mul_assoc, e2]`. Use `group`. Establish `hk' : kr.1 * d.levi k.1 ∈ Nfix d j`. Use `mul_mem (inv_mem (mul_mem hγ1 hγr')) hn` as an intermediate fact.

Rewrite `this` using `[hn', ← mul_assoc, inv_mul_cancel, one_mul]`. Then use the resulting hypothesis. Use `⟨⟨_, mul_mem hγ1 hγr'⟩, Subgroup.mem_subgroupOf.2 (mul_mem (d.levi_mem_GQ hγQ.1 hγQ.2) (Subgroup.mem_subgroupOf.1 hγr)), ⟨_, hk'⟩, ⟨(kr, k), ⟨hkr, hk⟩, rfl⟩, Subtype.ext hn'⟩` and prove the remaining obligations.
-/
theorem Nfix_cocompact (j : Fin ρ) : ∃ K : Set (Nfix d j), IsCompact K ∧
    ∀ m, ∃ γ ∈ (GQ V).subgroupOf (Nfix d j), ∃ k ∈ K, m = γ * k := by
  obtain ⟨Kr, hKr, hr⟩ := radX_cocompact d
  obtain ⟨Ku, hKu, hu⟩ := unip_cols_cocompact D ρ j
  let f : radX d × UX D ρ → GA D V := fun p => p.1.1 * d.levi p.2.1
  have hf : Continuous f := (continuous_subtype_val.comp continuous_fst).mul
    (d.continuous_levi.comp (continuous_subtype_val.comp continuous_snd))
  have hC : IsCompact (f '' (Kr ×ˢ Ku)) := (hKr.prod hKu).image hf
  have hcl : IsClosed (Nfix d j : Set (GA D V)) := by
    rw [Nfix, Subgroup.coe_inf, Subgroup.coe_iInf]
    exact (isClosed_flagN d).inter (isClosed_iInter fun _ => isClosed_fixer _)
  refine ⟨Subtype.val ⁻¹' (f '' (Kr ×ˢ Ku)), hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hC, fun m => ?_⟩
  obtain ⟨n, hn⟩ := m
  obtain ⟨u, huX, b, c, rfl⟩ := GlobalTheory.MixPer.Decomp.flag_decomp d (Nfix_le d j hn)
  have hcol := col_of_mem_Nfix d j hn
  obtain ⟨γ, hγQ, hγc, k, hk, hγk⟩ := hu ⟨u, huX⟩ hcol
  have hu' : u = γ.1 * k.1 := congrArg Subtype.val hγk

  have hrad : d.nB b * d.nC c ∈ radX d := (GlobalTheory.MixPer.Decomp.mem_radX_iff d).2 ⟨b, c, rfl⟩
  have hlk : d.levi k.1 ∈ flagN d := d.levi_mem_NFlag k.2
  have hconj : d.levi k.1 * (d.nB b * d.nC c) * (d.levi k.1)⁻¹ ∈ radX d :=
    (Subgroup.normal_subgroupOf_iff (show radX d ≤ flagN d from inf_le_left)).1 (radX_normal d) _ _ hrad hlk
  obtain ⟨γr, hγr, kr, hkr, hrk⟩ := hr ⟨_, hconj⟩
  have hγ1 : d.levi γ.1 ∈ Nfix d j := levi_mem_Nfix d j γ.2 hγc
  have hγr' : γr.1 ∈ Nfix d j := radX_le_Nfix d j γr.2
  have hn' : d.levi u * (d.nB b * d.nC c) = d.levi γ.1 * γr.1 * (kr.1 * d.levi k.1) := by
    have e := congrArg Subtype.val hrk
    simp only [Subgroup.coe_mul] at e
    have e2 : d.levi k.1 * (d.nB b * d.nC c) = γr.1 * kr.1 * d.levi k.1 := by
      rw [← e]
      group
    rw [hu', map_mul, mul_assoc, e2]
    group
  have hk' : kr.1 * d.levi k.1 ∈ Nfix d j := by
    have := mul_mem (inv_mem (mul_mem hγ1 hγr')) hn
    rwa [hn', ← mul_assoc, inv_mul_cancel, one_mul] at this
  refine ⟨⟨_, mul_mem hγ1 hγr'⟩, Subgroup.mem_subgroupOf.2 (mul_mem (d.levi_mem_GQ hγQ.1 hγQ.2)
    (Subgroup.mem_subgroupOf.1 hγr)), ⟨_, hk'⟩, ⟨(kr, k), ⟨hkr, hk⟩, rfl⟩, Subtype.ext hn'⟩

/- English proof (translation)
Introduce `D V V₀ ρ d`. Use `⟨isClosed_flagN d, ?_⟩` and prove the remaining obligations. Introduce and unpack `M (rfl | rfl | ⟨j, rfl⟩)`. Conclude with `⟨centre_le d, isClosed_centre d, centre_normal d, centre_cocompact d⟩`. Use `⟨inf_le_left, ?_, radX_normal d, radX_cocompact d⟩` and prove the remaining obligations.

Rewrite using `[radX, Subgroup.coe_inf]`. Conclude with `(isClosed_flagN d).inter (isClosed_fixer _)`. Use `⟨Nfix_le d j, ?_, Nfix_normal d j, Nfix_cocompact d j⟩` and prove the remaining obligations. Rewrite using `[Nfix, Subgroup.coe_inf, Subgroup.coe_iInf]`. Conclude with `(isClosed_flagN d).inter (isClosed_iInter fun _ => isClosed_fixer _)`.
-/
theorem flag_subgroups_closed_normal_cocompact : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ),
    IsClosed (flagN d : Set (GA D V)) ∧ ∀ M : Subgroup (GA D V), (M = centre d ∨ M = radX d ∨ ∃ j, M = Nfix d j) →
      M ≤ flagN d ∧ IsClosed (M : Set (GA D V)) ∧ (M.subgroupOf (flagN d)).Normal ∧
        ∃ K : Set M, IsCompact K ∧ ∀ m, ∃ γ ∈ (GQ V).subgroupOf M, ∃ k ∈ K, m = γ * k := by
  intro D V V₀ ρ d
  refine ⟨isClosed_flagN d, ?_⟩
  rintro M (rfl | rfl | ⟨j, rfl⟩)
  · exact ⟨centre_le d, isClosed_centre d, centre_normal d, centre_cocompact d⟩
  · refine ⟨inf_le_left, ?_, radX_normal d, radX_cocompact d⟩
    rw [radX, Subgroup.coe_inf]
    exact (isClosed_flagN d).inter (isClosed_fixer _)
  · refine ⟨Nfix_le d j, ?_, Nfix_normal d j, Nfix_cocompact d j⟩
    rw [Nfix, Subgroup.coe_inf, Subgroup.coe_iInf]
    exact (isClosed_flagN d).inter (isClosed_iInter fun _ => isClosed_fixer _)

end GlobalTheory.Unf.FlagSub

end

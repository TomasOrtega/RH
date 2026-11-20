import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisMemIffNormLeOne

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.Cyc.LatBasis

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Set `b` to `Module.finBasis ℤ_[l] S`. Establish `hli : LinearIndependent ℤ_[l] (fun i => (b i : V))` using `b.linearIndependent.map' S.subtype (Submodule.ker_subtype S)`. Establish `hli' : LinearIndependent ℚ_[l] (fun i => (b i : V))` using `(LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]).1 hli`. Establish `hsum : ∀ t : S, (t : V) = ∑ i, ((b.repr t i : ℤ_[l]) : ℚ_[l]) • (b i : V)`. Introduce `t`.

Use `conv_lhs => rw [← b.sum_repr t]`. Rewrite using `[Submodule.coe_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, ← algebraMap_smul ℚ_[l]]`. Both sides reduce to the same expression.

Establish `hsp : ⊤ ≤ Submodule.span ℚ_[l] (Set.range fun i => (b i : V))`. Introduce `x _`. Take `⟨y, hy, hx⟩` from `hS x`. Establish `hy' : algebraMap ℤ_[l] ℚ_[l] y ≠ 0`. Simplify using `using hy`.

Establish `h1 : y • x ∈ Submodule.span ℚ_[l] (Set.range fun i => (b i : V))`. Use `hsum ⟨_, hx⟩` as an intermediate fact. Express the relevant statement in the definitionally equal form `y • x = _ at this`. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Rewrite `h1` using `[← algebraMap_smul ℚ_[l]]`. Conclude with `(Submodule.smul_mem_iff _ hy').1 h1`. Set `w` to `Module.Basis.mk hli' hsp`. Establish `hw : ∀ i, w i = (b i : V)` using `fun i => Module.Basis.mk_apply _ _ i`. Use `⟨_, w, fun x => ⟨fun hx i => ?_, fun hx => ?_⟩⟩` and prove the remaining obligations.

Use `hsum ⟨x, hx⟩` as an intermediate fact. Express the relevant statement in the definitionally equal form `x = _ at this`. Simplify using `only [← hw] at this`. Establish `h2 : w.repr x i = ((b.repr ⟨x, hx⟩ i : ℤ_[l]) : ℚ_[l])` using `by conv_lhs => rw [this]`. Conclude with `congrFun (w.repr_sum_self _) i`.

Rewrite using `[h2]`. Conclude with `PadicInt.norm_le_one _`. Rewrite using `[← w.sum_repr x]`. Use `S.sum_mem fun i _ => ?_` and prove the remaining obligations. Take `⟨z, h3⟩ : ∃ z : ℤ_[l], w.repr x i = algebraMap ℤ_[l] ℚ_[l] z` from `⟨⟨_, hx i⟩, rfl⟩`.

Rewrite using `[h3, algebraMap_smul, hw]`. Conclude with `S.smul_mem _ (b i).2`.
-/
theorem exists_basis_of_submodule {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V]
    [IsScalarTower ℤ_[l] ℚ_[l] V] (S : Submodule ℤ_[l] V) [Module.Free ℤ_[l] S]
    [Module.Finite ℤ_[l] S] (hS : ∀ x : V, ∃ y : ℤ_[l], y ≠ 0 ∧ y • x ∈ S) :
    ∃ (n : ℕ) (w : Module.Basis (Fin n) ℚ_[l] V), ∀ x : V, x ∈ S ↔ ∀ i, ‖w.repr x i‖ ≤ 1 := by
  let b := Module.finBasis ℤ_[l] S
  have hli : LinearIndependent ℤ_[l] (fun i => (b i : V)) :=
    b.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  have hli' : LinearIndependent ℚ_[l] (fun i => (b i : V)) :=
    (LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]).1 hli
  have hsum : ∀ t : S, (t : V) = ∑ i, ((b.repr t i : ℤ_[l]) : ℚ_[l]) • (b i : V) := by
    intro t
    conv_lhs => rw [← b.sum_repr t]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, ← algebraMap_smul ℚ_[l]]
    rfl
  have hsp : ⊤ ≤ Submodule.span ℚ_[l] (Set.range fun i => (b i : V)) := by
    intro x _
    obtain ⟨y, hy, hx⟩ := hS x
    have hy' : algebraMap ℤ_[l] ℚ_[l] y ≠ 0 := by
      simpa using hy
    have h1 : y • x ∈ Submodule.span ℚ_[l] (Set.range fun i => (b i : V)) := by
      have := hsum ⟨_, hx⟩
      change y • x = _ at this
      rw [this]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [← algebraMap_smul ℚ_[l]] at h1
    exact (Submodule.smul_mem_iff _ hy').1 h1
  let w := Module.Basis.mk hli' hsp
  have hw : ∀ i, w i = (b i : V) := fun i => Module.Basis.mk_apply _ _ i
  refine ⟨_, w, fun x => ⟨fun hx i => ?_, fun hx => ?_⟩⟩
  · have := hsum ⟨x, hx⟩
    change x = _ at this
    simp only [← hw] at this
    have h2 : w.repr x i = ((b.repr ⟨x, hx⟩ i : ℤ_[l]) : ℚ_[l]) := by
      conv_lhs => rw [this]
      exact congrFun (w.repr_sum_self _) i
    rw [h2]
    exact PadicInt.norm_le_one _
  · rw [← w.sum_repr x]
    refine S.sum_mem fun i _ => ?_
    obtain ⟨z, h3⟩ : ∃ z : ℤ_[l], w.repr x i = algebraMap ℤ_[l] ℚ_[l] z := ⟨⟨_, hx i⟩, rfl⟩
    rw [h3, algebraMap_smul, hw]
    exact S.smul_mem _ (b i).2

/- English proof (translation)
Use `haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup L V`. Use `haveI : ContinuousSMul L V := IsModuleTopology.toContinuousSMul L V`. Use `haveI : T2Space V := by`. Set `c` to `Module.finBasis L V`. Establish `h1 : Continuous c.equivFun` using `IsModuleTopology.continuous_of_linearMap c.equivFun.toLinearMap`.

Conclude with `T2Space.of_injective_continuous c.equivFun.injective h1`. Use `haveI : ContinuousSMul ℚ_[l] V := ⟨by`. Establish `h : (fun p : ℚ_[l] × V => p.1 • p.2) = fun p => algebraMap ℚ_[l] L p.1 • p.2`. Use function extensionality and compare the values at `p`. Rewrite using `[algebraMap_smul]`.

Rewrite using `[h]`. Conclude with `(hc.comp continuous_fst).smul continuous_snd⟩`. Conclude with `⟨w.equivFunL.continuous, w.equivFunL.symm.continuous⟩`.
-/
theorem continuous_coord {L V : Type} [Field L] [Algebra ℚ_[l] L] [TopologicalSpace L]
    [IsTopologicalRing L] [T2Space L] (hc : Continuous (algebraMap ℚ_[l] L))
    [AddCommGroup V] [Module L V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] L V] [TopologicalSpace V]
    [IsModuleTopology L V] [FiniteDimensional L V] {n : ℕ} (w : Module.Basis (Fin n) ℚ_[l] V) :
    Continuous w.equivFun ∧ Continuous w.equivFun.symm := by
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup L V
  haveI : ContinuousSMul L V := IsModuleTopology.toContinuousSMul L V
  haveI : T2Space V := by
    let c := Module.finBasis L V
    have h1 : Continuous c.equivFun :=
      IsModuleTopology.continuous_of_linearMap c.equivFun.toLinearMap
    exact T2Space.of_injective_continuous c.equivFun.injective h1
  haveI : ContinuousSMul ℚ_[l] V := ⟨by
    have h : (fun p : ℚ_[l] × V => p.1 • p.2) = fun p => algebraMap ℚ_[l] L p.1 • p.2 := by
      funext p; rw [algebraMap_smul]
    rw [h]
    exact (hc.comp continuous_fst).smul continuous_snd⟩
  exact ⟨w.equivFunL.continuous, w.equivFunL.symm.continuous⟩

/- English proof (translation)
Use `first`. Consider the case `(rename_i h_1 h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_14 h_15 h_16 h_17 h_18 h_19; revert l h_1 L O V h_5 h_6 h_7 h_8 h_9 h_10 h_11 hcomp hL h_14 h_15 h_16 h_17 h_18 h_19 S hfg hfree hspan; exact @_root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one)`. Consider the case `exact @_root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one`. Consider the case `exact _root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one`. Consider the case `(apply _root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one <;> assumption)`.

Consider the case `(intros; apply _root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one <;> assumption)`. Consider the case `(intros; apply @_root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one ..)`.
-/
theorem exists_basis_lattice {L O V : Type} [Field L] [Algebra ℚ_[l] L] [CommRing O] [Algebra O L]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    (hcomp : ∀ a : ℤ_[l], algebraMap O L (algebraMap ℤ_[l] O a) = algebraMap ℚ_[l] L (a : ℚ_[l]))
    (hL : ∀ a : L, ∃ y : ℤ_[l], y ≠ 0 ∧ ∃ o : O, algebraMap O L o = algebraMap ℚ_[l] L y * a)
    [AddCommGroup V] [Module L V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] L V] [Module O V]
    [IsScalarTower O L V] (S : Submodule O V) (hfg : S.FG) (hfree : Module.Free O S)
    (hspan : Submodule.span L (S : Set V) = ⊤) :
    ∃ (n : ℕ) (w : Module.Basis (Fin n) ℚ_[l] V), ∀ x : V, x ∈ S ↔ ∀ i, ‖w.repr x i‖ ≤ 1 := by
  first
  | (rename_i h_1 h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_14 h_15 h_16 h_17 h_18 h_19; revert l h_1 L O V h_5 h_6 h_7 h_8 h_9 h_10 h_11 hcomp hL h_14 h_15 h_16 h_17 h_18 h_19 S hfg hfree hspan; exact @_root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one)
  | exact @_root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one
  | exact _root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one
  | (apply _root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one ..)

/- English proof (translation)
Use `haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2`. Establish `h1 : IsAlgebraic ℚ_[l] a` using `Algebra.IsAlgebraic.isAlgebraic a`. Establish `h2 : IsAlgebraic ℤ_[l] a` using `(IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 h1`. Take `⟨y, hy, hi⟩` from `h2.exists_integral_multiple`. Use `⟨y, hy, ⟨_, hi⟩, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `y • a = _`. Rewrite using `[Algebra.smul_def]`. Both sides reduce to the same expression.
-/
theorem exists_mul_mem (LL : FinExt l) (a : ↥LL.1) :
    ∃ y : ℤ_[l], y ≠ 0 ∧ ∃ o : ↥(OL LL),
      algebraMap ↥(OL LL) ↥LL.1 o = algebraMap ℚ_[l] ↥LL.1 y * a := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h1 : IsAlgebraic ℚ_[l] a := Algebra.IsAlgebraic.isAlgebraic a
  have h2 : IsAlgebraic ℤ_[l] a := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 h1
  obtain ⟨y, hy, hi⟩ := h2.exists_integral_multiple
  refine ⟨y, hy, ⟨_, hi⟩, ?_⟩
  change y • a = _
  rw [Algebra.smul_def]
  rfl

/- English proof (translation)
The claim follows from `continuous_induced_rng.2 (continuous_algebraMap ℚ_[l] (Om l))`.
-/
theorem continuous_algebraMap_ext (LL : FinExt l) : Continuous (algebraMap ℚ_[l] ↥LL.1) :=
  continuous_induced_rng.2 (continuous_algebraMap ℚ_[l] (Om l))

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Use `haveI := Decomp.freeOL LL`. Use `haveI := Decomp.finiteOL LL`. Take `⟨n, w, hw⟩` from `exists_basis_lattice (l := l) (L := ↥LL.1) (O := ↥(OL LL)) (fun _ => rfl) (exists_mul_mem LL) T.L.T T.L.fg T.L.free T.L.span`. Conclude with `⟨n, w, hw, continuous_coord (continuous_algebraMap_ext LL) w⟩`.
-/
theorem exists_basis (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G]
    (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) :
    ∃ (n : ℕ) (w : Module.Basis (Fin n) ℚ_[l] T.V),
      (∀ x : T.V, x ∈ T.L.T ↔ ∀ i, ‖w.repr x i‖ ≤ 1) ∧
        Continuous w.equivFun ∧ Continuous w.equivFun.symm := by
  haveI := Decomp.freeOL LL
  haveI := Decomp.finiteOL LL
  obtain ⟨n, w, hw⟩ := exists_basis_lattice (l := l) (L := ↥LL.1) (O := ↥(OL LL)) (fun _ => rfl)
    (exists_mul_mem LL) T.L.T T.L.fg T.L.free T.L.span
  exact ⟨n, w, hw, continuous_coord (continuous_algebraMap_ext LL) w⟩

end GlobalTheory.Cyc.LatBasis

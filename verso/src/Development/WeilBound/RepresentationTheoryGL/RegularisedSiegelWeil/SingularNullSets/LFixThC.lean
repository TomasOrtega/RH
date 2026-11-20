import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixThB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleCharacterNormEulerFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterConductorCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicAddCharEqArchimedeanMulFinprodLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LFixTh

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open PositivityTheory.Rg.Rsw.L

variable {D : D7} {ρ p n : ℕ}

instance finDim (D : D7) : FiniteDimensional D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _

structure GoodPl (χ : (AE D)ˣ →* Circle) (b₀ : HermE D ρ) (v : Pl D) : Prop where
  good : LFixW.IsGood D.host.F D.host.E v
  unr : ∀ u ∈ GlobalTheory.ThK.unitsAt D.host.E v, χ u = 1
  bint : ∀ i j, inclR (Fv D.host.F v) (b₀.1 i j) ∈ intLoc D.host.F D.host.E v

/- English proof (translation)
Set `m : Pl D → (AE D)ˣ` to `fun v => if h : ∃ u ∈ GlobalTheory.ThK.unitsAt D.host.E v, χ u ≠ 1 then h.choose else 1`. Establish `hm : ∀ v, m v ∈ GlobalTheory.ThK.unitsAt D.host.E v` using `fun v => by`. Simplify using `only [m]`. Use `split_ifs with h`. Conclude with `h.choose_spec.1`.

Conclude with `one_mem _`. Use `filter_upwards [GlobalTheory.ThK.ConeEulerChr.eventually_chr_eq_one (ν := χ) hχ.1 m (Eventually.of_forall hm)] with v hv u hu`. Assume the negation of the conclusion as `hne`. Establish `h : ∃ u ∈ GlobalTheory.ThK.unitsAt D.host.E v, χ u ≠ 1` using `⟨u, hu, hne⟩`. Establish `e : m v = h.choose` using `dif_pos h`.

Conclude with `h.choose_spec.2 (e ▸ hv)`.
-/
theorem eventually_unr {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) :
    ∀ᶠ v in cofinite, ∀ u ∈ GlobalTheory.ThK.unitsAt D.host.E v, χ u = 1 := by
  classical
  let m : Pl D → (AE D)ˣ := fun v =>
    if h : ∃ u ∈ GlobalTheory.ThK.unitsAt D.host.E v, χ u ≠ 1 then h.choose else 1
  have hm : ∀ v, m v ∈ GlobalTheory.ThK.unitsAt D.host.E v := fun v => by
    simp only [m]
    split_ifs with h
    · exact h.choose_spec.1
    · exact one_mem _
  filter_upwards [GlobalTheory.ThK.ConeEulerChr.eventually_chr_eq_one (ν := χ) hχ.1 m (Eventually.of_forall hm)] with v hv u hu
  by_contra hne
  have h : ∃ u ∈ GlobalTheory.ThK.unitsAt D.host.E v, χ u ≠ 1 := ⟨u, hu, hne⟩
  have e : m v = h.choose := dif_pos h
  exact h.choose_spec.2 (e ▸ hv)

/- English proof (translation)
Use `filter_upwards [LFixW.eventually_good (F := D.host.F) (E := D.host.E), eventually_unr hχ, eventually_all.2 fun i => eventually_all.2 fun j => GlobalTheory.AdelicU.SelfDual.eventually_mem_intLoc (F := D.host.F) (b₀.1 i j)] with v h1 h2 h3`. Conclude with `⟨h1, h2, h3⟩`.
-/
theorem eventually_goodPl {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (b₀ : HermE D ρ) :
    ∀ᶠ v in cofinite, GoodPl χ b₀ v := by
  filter_upwards [LFixW.eventually_good (F := D.host.F) (E := D.host.E), eventually_unr hχ,
    eventually_all.2 fun i => eventually_all.2 fun j =>
      GlobalTheory.AdelicU.SelfDual.eventually_mem_intLoc (F := D.host.F) (b₀.1 i j)] with v h1 h2 h3
  exact ⟨h1, h2, h3⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem adj_apply (x : Mx D ρ p) (i : Fin p) (j : Fin ρ) : adj x i j = cA D (x j i) := rfl

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => rfl`. Consider the case `add x y hx hy => rw [map_add (cA D), map_add (cv D v), map_add (cv D v), hx, hy, map_add (sigR (Fv D.host.F v) D.sp.cm.sig)]`.
-/
theorem cv_cA (v : Pl D) (x : AE D) : cv D v (cA D x) = sigR (Fv D.host.F v) D.sp.cm.sig (cv D v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => rw [map_add (cA D), map_add (cv D v), map_add (cv D v), hx, hy, map_add (sigR (Fv D.host.F v) D.sp.cm.sig)]

/- English proof (translation)
Rewrite using `[← block_matrix_one (R := R), block_matrix_apply_top_right, Matrix.zero_apply]`.
-/
theorem one_cn {R : Type} [Ring R] (i j : Fin n) :
    (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) (Fin.castAdd n i) (Fin.natAdd n j) = 0 := by
  rw [← block_matrix_one (R := R), block_matrix_apply_top_right, Matrix.zero_apply]

/- English proof (translation)
Establish `hbe : ∀ i j, b i j = mat g (Fin.castAdd p i) (Fin.natAdd p j)` using `fun i j => by rw [hb, block_matrix_apply_top_right]`. Establish `hbInf : ∀ w i j, compInf D.host.F D.host.E w (b i j) = 0` using `fun w i j => by`. Apply the tactic sequence `rw [hbe, (kOff_entry hg _ _).1 w, one_cn]`. Establish `hbS : ∀ v ∈ S, ∀ i j, cv D v (b i j) = 0` using `fun v hv i j => by`. Apply the tactic sequence `rw [hbe, (kOff_entry hg _ _).2.1 v hv, one_cn]`.

Establish `hbI : ∀ v ∉ S, ∀ i j, cv D v (b i j) ∈ intLoc D.host.F D.host.E v` using `fun v hv i j => by`. Rewrite using `[hbe]`. Apply the tactic sequence `exact (kOff_entry hg _ _).2.2 v hv`. Establish `hPI : ∀ v ∉ S, ∀ k i, cv D v (pr b₀ y y k i) ∈ intLoc D.host.F D.host.E v`. Introduce `v hv k i`.

Simplify using `only [pr, Matrix.mul_apply, map_sum, map_mul]`. Use `sum_mem fun l _ => mul_mem ?_ (sum_mem fun m _ => mul_mem ?_ (hy v hv m i))` and prove the remaining obligations. Rewrite using `[adj_apply, cv_cA]`. Conclude with `sigR_mem_intLoc _ (hy v hv l k)`. Rewrite using `[Matrix.map_apply]`.

Conclude with `(hS v hv).bint l m`. Establish `hX : ∀ (R : Type) [CommRing R] (f : AE D →+* R), f (b * pr b₀ y y).trace = ∑ i, ∑ k, f (b i k) * f (pr b₀ y y k i)` using `fun R _ f => by`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul]`. Establish `hXinf : ∀ w, compInf D.host.F D.host.E w (b * pr b₀ y y).trace = 0` using `fun w => by`. Rewrite using `[hX]`.

Simplify using `[hbInf]`. Establish `hXS : ∀ v ∈ S, cv D v (b * pr b₀ y y).trace = 0` using `fun v hv => by`. Rewrite using `[hX]`. Simplify using `[hbS v hv]`. Establish `hXI : ∀ v ∉ S, cv D v (b * pr b₀ y y).trace ∈ intLoc D.host.F D.host.E v` using `fun v hv => by`.

Rewrite using `[hX]`. Conclude with `sum_mem fun i _ => sum_mem fun k _ => mul_mem (hbI v hv i k) (hPI v hv k i)`. Apply `hker` to reduce the goal to its premises. Use `funext fun w => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `evInf D.host.F w (algebraMap D.host.F (AF D.host.F) (1 / 2) * trA (b * pr b₀ y y).trace) = 0`.

Rewrite using `[map_mul, LFixW.evInf_apply w (trA _), LFixW.trA_fst, hXinf, map_zero, mul_zero]`. Introduce `v hv`. Express the relevant statement in the definitionally equal form `evFin D.host.F v (algebraMap D.host.F (AF D.host.F) (1 / 2) * trA (b * pr b₀ y y).trace) = 0`. Rewrite using `[map_mul, LFixW.evFin_apply v (trA _), LFixW.trA_snd, hXS v hv, map_zero, mul_zero]`. Introduce `v hv`.

Express the relevant statement in the definitionally equal form `evFin D.host.F v (algebraMap D.host.F (AF D.host.F) (1 / 2) * trA (b * pr b₀ y y).trace) ∈ _`. Rewrite using `[map_mul, LFixW.evFin_apply v (trA _), LFixW.trA_snd, AlgHom.commutes, one_div]`. Conclude with `mul_mem (hS v hv).good.half (LFixW.trace_mem (hS v hv).good (hXI v hv))`.
-/
theorem unip_one {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {b₀ : HermE D ρ} {S : Finset (Pl D)}
    (hS : ∀ v ∉ S, GoodPl χ b₀ v)
    (hker : ∀ y : AF D.host.F, y.1 = 0 → (∀ v ∈ S, y.2 v = 0) →
      (∀ v ∉ S, y.2 v ∈ v.adicCompletionIntegers D.host.F) → ψ y = 1)
    {g : G D p} (hg : g ∈ KOff D p S) {b : Mx D p p} (hb : mat g = blk4 1 b 0 1) {y : Mx D ρ p} (hy : IntOff S y) :
    ψ (halfTr (b * pr b₀ y y).trace) = 1 := by
  have hbe : ∀ i j, b i j = mat g (Fin.castAdd p i) (Fin.natAdd p j) := fun i j => by rw [hb, block_matrix_apply_top_right]
  have hbInf : ∀ w i j, compInf D.host.F D.host.E w (b i j) = 0 := fun w i j => by
    rw [hbe, (kOff_entry hg _ _).1 w, one_cn]
  have hbS : ∀ v ∈ S, ∀ i j, cv D v (b i j) = 0 := fun v hv i j => by
    rw [hbe, (kOff_entry hg _ _).2.1 v hv, one_cn]
  have hbI : ∀ v ∉ S, ∀ i j, cv D v (b i j) ∈ intLoc D.host.F D.host.E v := fun v hv i j => by
    rw [hbe]; exact (kOff_entry hg _ _).2.2 v hv
  have hPI : ∀ v ∉ S, ∀ k i, cv D v (pr b₀ y y k i) ∈ intLoc D.host.F D.host.E v := by
    intro v hv k i
    simp only [pr, Matrix.mul_apply, map_sum, map_mul]
    refine sum_mem fun l _ => mul_mem ?_ (sum_mem fun m _ => mul_mem ?_ (hy v hv m i))
    · rw [adj_apply, cv_cA]; exact sigR_mem_intLoc _ (hy v hv l k)
    · rw [Matrix.map_apply]; exact (hS v hv).bint l m
  have hX : ∀ (R : Type) [CommRing R] (f : AE D →+* R), f (b * pr b₀ y y).trace =
      ∑ i, ∑ k, f (b i k) * f (pr b₀ y y k i) := fun R _ f => by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul]
  have hXinf : ∀ w, compInf D.host.F D.host.E w (b * pr b₀ y y).trace = 0 := fun w => by
    rw [hX]; simp [hbInf]
  have hXS : ∀ v ∈ S, cv D v (b * pr b₀ y y).trace = 0 := fun v hv => by
    rw [hX]; simp [hbS v hv]
  have hXI : ∀ v ∉ S, cv D v (b * pr b₀ y y).trace ∈ intLoc D.host.F D.host.E v := fun v hv => by
    rw [hX]; exact sum_mem fun i _ => sum_mem fun k _ => mul_mem (hbI v hv i k) (hPI v hv k i)
  apply hker
  · refine funext fun w => ?_
    change evInf D.host.F w (algebraMap D.host.F (AF D.host.F) (1 / 2) * trA (b * pr b₀ y y).trace) = 0
    rw [map_mul, LFixW.evInf_apply w (trA _), LFixW.trA_fst, hXinf, map_zero, mul_zero]
  · intro v hv
    change evFin D.host.F v (algebraMap D.host.F (AF D.host.F) (1 / 2) * trA (b * pr b₀ y y).trace) = 0
    rw [map_mul, LFixW.evFin_apply v (trA _), LFixW.trA_snd, hXS v hv, map_zero, mul_zero]
  · intro v hv
    change evFin D.host.F v (algebraMap D.host.F (AF D.host.F) (1 / 2) * trA (b * pr b₀ y y).trace) ∈ _
    rw [map_mul, LFixW.evFin_apply v (trA _), LFixW.trA_snd, AlgHom.commutes, one_div]
    exact mul_mem (hS v hv).good.half (LFixW.trace_mem (hS v hv).good (hXI v hv))

end PositivityTheory.Rg.Rsw.L.LFixTh

end

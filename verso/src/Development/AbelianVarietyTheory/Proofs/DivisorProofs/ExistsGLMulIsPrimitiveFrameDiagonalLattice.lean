import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open ValuativeRel

namespace GlobalTheory.PrimFrameExist

/- English proof (translation)
Introduce `k _ _ _ _ a C _ _ d X hX`. Use `set Λ : Submodule 𝒪[k] (C → k) := diagLat d with hΛdef`. Use `set V : Submodule k (C → k) := Submodule.span k (Set.range X.row) with hVdef`. Use `set M : Submodule 𝒪[k] (C → k) := V.restrictScalars 𝒪[k] ⊓ Λ with hMdef`. Establish `hΛfg : Λ.FG` using `(isLattice_diagLat d).fg`.

Use `haveI : IsNoetherian 𝒪[k] Λ := isNoetherian_of_fg_of_noetherian Λ hΛfg`. Use `haveI : IsNoetherian 𝒪[k] M := isNoetherian_of_le inf_le_right`. Use `haveI : Module.IsTorsionFree 𝒪[k] k := inferInstance`. Use `haveI : Module.IsTorsionFree 𝒪[k] (C → k) := Module.IsTorsionFree.trans_faithfulSMul 𝒪[k] k (C → k)`. Use `haveI : Module.IsTorsionFree 𝒪[k] M := inferInstance`.

Use `haveI : Module.Free 𝒪[k] M := Module.free_of_finite_type_torsion_free'`. Set `ι` to `Module.Free.ChooseBasisIndex 𝒪[k] M`. Set `b : Module.Basis ι 𝒪[k] M` to `Module.Free.chooseBasis 𝒪[k] M`. Set `v : ι → (C → k)` to `fun i => (b i : C → k)`. Establish `hvV : ∀ i, v i ∈ V` using `fun i => (b i).2.1`.

Establish `hvΛ : ∀ i, v i ∈ Λ` using `fun i => (b i).2.2`. Establish `hrepr : ∀ y (hy : y ∈ M), y = ∑ i, ((b.repr ⟨y, hy⟩ i : 𝒪[k]) : k) • v i`. Introduce `y hy`. Establish `h` using `congrArg Subtype.val (b.sum_repr ⟨y, hy⟩)`. Rewrite `h` using `[Submodule.coe_sum]`.

Conclude with `h.symm.trans (Finset.sum_congr rfl fun i _ => rfl)`. Establish `hli : LinearIndependent k v`. Rewrite using `[← LinearIndependent.iff_fractionRing (R := 𝒪[k]) (K := k)]`. Conclude with `b.linearIndependent.map' M.subtype M.ker_subtype`. Establish `hclear : ∀ x : C → k, ∃ r : 𝒪[k], r ≠ 0 ∧ (r : k) • x ∈ Λ`.

Introduce `x`. Take `⟨r, hr⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors 𝒪[k]) (fun j => x j / (d j : k))`. Use `⟨r, nonZeroDivisors.coe_ne_zero r, ?_⟩` and prove the remaining obligations. Rewrite using `[hΛdef, mem_diagLat]`. Introduce `j`.

Take `⟨s, hs⟩` from `hr j`. Rewrite `hs` using `[Algebra.smul_def]`. Establish `h1 : valuation k (algebraMap 𝒪[k] k r * (x j / d j)) ≤ 1`. Rewrite using `[← hs]`. Conclude with `(Valuation.mem_integer_iff _ _).1 s.2`.

Establish `e : ((r : 𝒪[k]) : k) • x = fun l => (algebraMap 𝒪[k] k r * (x l / d l)) * d l`. Use function extensionality and compare the values at `l`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[mul_assoc, div_mul_cancel₀ _ (d l).ne_zero]`. Both sides reduce to the same expression.

Rewrite using `[e, map_mul]`. Conclude with `mul_le_of_le_one_left' h1`. Establish `hli' : X.rank = Fintype.card (Fin a) ↔ LinearIndependent k X.row`. Rewrite using `[rank_eq_finrank_span_row, linearIndependent_iff_card_eq_finrank_span, eq_comm]`. Both sides reduce to the same expression.

Establish `hXli : LinearIndependent k X.row` using `hli'.1 (by simpa using hX)`. Establish `hVle : V ≤ Submodule.span k (Set.range v)`. Introduce `x hx`. Take `⟨r, hr0, hr⟩` from `hclear x`. Establish `hrx : ((r : 𝒪[k]) : k) • x ∈ M` using `⟨V.smul_mem _ hx, hr⟩`.

Establish `e` using `hrepr _ hrx`. Establish `hr0' : ((r : 𝒪[k]) : k) ≠ 0` using `fun h => hr0 (Subtype.ext h)`. Establish `hx' : x = ((r : 𝒪[k]) : k)⁻¹ • (((r : 𝒪[k]) : k) • x)` using `(inv_smul_smul₀ hr0' x).symm`. Rewrite using `[hx', e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))`.

Establish `hspan : Submodule.span k (Set.range v) = V` using `le_antisymm (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hvV i)) hVle`. Establish `hcard : Fintype.card ι = a`. Rewrite using `[← finrank_span_eq_card hli, hspan, hVdef, finrank_span_eq_card hXli, Fintype.card_fin]`. Set `e : Fin a ≃ ι` to `(Fintype.equivFinOfCardEq hcard).symm`. Set `Y : Matrix (Fin a) C k` to `Matrix.of fun i => v (e i)`.

Establish `hYV : ∀ i, Y.row i ∈ V` using `fun i => hvV (e i)`. Use `choose g hg using fun i => (Submodule.mem_span_range_iff_exists_fun k).1 (hYV i)`. Establish `hYg : (Matrix.of g) * X = Y`. Use extensionality with `i l`. Establish `h` using `congrFun (hg i) l`.

Rewrite `h` using `[Finset.sum_apply]`. Rewrite using `[Matrix.mul_apply]`. Conclude with `(Finset.sum_congr rfl fun j _ => rfl).trans h`. Establish `hYli : LinearIndependent k Y.row` using `hli.comp e e.injective`. Establish `hgli : LinearIndependent k (Matrix.of g).row`.

Use `LinearIndependent.of_comp (Matrix.vecMulLinear X) ?_` and prove the remaining obligations. Use `hYli using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Rewrite using `[← hYg]`. Apply the tactic sequence `try rfl`.

Establish `hu : IsUnit (Matrix.of g)` using `Matrix.linearIndependent_rows_iff_isUnit.1 hgli`. Use `⟨hu.unit, ?_⟩` and prove the remaining obligations. Rewrite using `[IsUnit.unit_spec, hYg, isPrimFrame_iff]`. Use `⟨fun i => hvΛ (e i), fun c hc i => ?_⟩` and prove the remaining obligations. Establish `hcV : c ᵥ* Y ∈ V`.

Rewrite using `[vecMul_eq_sum]`. Conclude with `V.sum_mem fun i _ => V.smul_mem _ (hYV i)`. Establish `hcM : c ᵥ* Y ∈ M` using `⟨hcV, hc⟩`. Establish `e1` using `hrepr _ hcM`. Establish `e2 : c ᵥ* Y = ∑ t, c (e.symm t) • v t`.

Rewrite using `[vecMul_eq_sum, ← e.sum_comp]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [e.symm_apply_apply]; rfl`. Establish `h` using `Fintype.linearIndependent_iffₛ.1 hli (fun t => c (e.symm t)) (fun t => ((b.repr ⟨_, hcM⟩ t : 𝒪[k]) : k)) (by rw [← e2, ← e1]) (e i)`. Simplify using `only [Equiv.symm_apply_apply] at h`. Rewrite using `[h]`.

Conclude with `(b.repr _ _).2`.
-/
theorem exists_gl_mul_isPrimFrame : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a : ℕ) (C : Type) [Fintype C] [DecidableEq C] (d : C → kˣ) (X : Matrix (Fin a) C k), X.rank = a →
    ∃ g₀ : GL (Fin a) k, IsPrimFrame (diagLat d) (g₀.val * X) := by
  intro k _ _ _ _ a C _ _ d X hX
  classical
  set Λ : Submodule 𝒪[k] (C → k) := diagLat d with hΛdef
  set V : Submodule k (C → k) := Submodule.span k (Set.range X.row) with hVdef
  set M : Submodule 𝒪[k] (C → k) := V.restrictScalars 𝒪[k] ⊓ Λ with hMdef
  have hΛfg : Λ.FG := (isLattice_diagLat d).fg
  haveI : IsNoetherian 𝒪[k] Λ := isNoetherian_of_fg_of_noetherian Λ hΛfg
  haveI : IsNoetherian 𝒪[k] M := isNoetherian_of_le inf_le_right
  haveI : Module.IsTorsionFree 𝒪[k] k := inferInstance
  haveI : Module.IsTorsionFree 𝒪[k] (C → k) := Module.IsTorsionFree.trans_faithfulSMul 𝒪[k] k (C → k)
  haveI : Module.IsTorsionFree 𝒪[k] M := inferInstance
  haveI : Module.Free 𝒪[k] M := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex 𝒪[k] M
  let b : Module.Basis ι 𝒪[k] M := Module.Free.chooseBasis 𝒪[k] M
  let v : ι → (C → k) := fun i => (b i : C → k)
  have hvV : ∀ i, v i ∈ V := fun i => (b i).2.1
  have hvΛ : ∀ i, v i ∈ Λ := fun i => (b i).2.2
  have hrepr : ∀ y (hy : y ∈ M), y = ∑ i, ((b.repr ⟨y, hy⟩ i : 𝒪[k]) : k) • v i := by
    intro y hy
    have h := congrArg Subtype.val (b.sum_repr ⟨y, hy⟩)
    rw [Submodule.coe_sum] at h
    exact h.symm.trans (Finset.sum_congr rfl fun i _ => rfl)
  have hli : LinearIndependent k v := by
    rw [← LinearIndependent.iff_fractionRing (R := 𝒪[k]) (K := k)]
    exact b.linearIndependent.map' M.subtype M.ker_subtype
  have hclear : ∀ x : C → k, ∃ r : 𝒪[k], r ≠ 0 ∧ (r : k) • x ∈ Λ := by
    intro x
    obtain ⟨r, hr⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors 𝒪[k])
      (fun j => x j / (d j : k))
    refine ⟨r, nonZeroDivisors.coe_ne_zero r, ?_⟩
    rw [hΛdef, mem_diagLat]
    intro j
    obtain ⟨s, hs⟩ := hr j
    rw [Algebra.smul_def] at hs
    have h1 : valuation k (algebraMap 𝒪[k] k r * (x j / d j)) ≤ 1 := by
      rw [← hs]; exact (Valuation.mem_integer_iff _ _).1 s.2
    have e : ((r : 𝒪[k]) : k) • x = fun l => (algebraMap 𝒪[k] k r * (x l / d l)) * d l := by
      funext l; simp only [Pi.smul_apply, smul_eq_mul]; rw [mul_assoc, div_mul_cancel₀ _ (d l).ne_zero]; rfl
    rw [e, map_mul]
    exact mul_le_of_le_one_left' h1
  have hli' : X.rank = Fintype.card (Fin a) ↔ LinearIndependent k X.row := by
    rw [rank_eq_finrank_span_row, linearIndependent_iff_card_eq_finrank_span, eq_comm]; rfl
  have hXli : LinearIndependent k X.row := hli'.1 (by simpa using hX)
  have hVle : V ≤ Submodule.span k (Set.range v) := by
    intro x hx
    obtain ⟨r, hr0, hr⟩ := hclear x
    have hrx : ((r : 𝒪[k]) : k) • x ∈ M := ⟨V.smul_mem _ hx, hr⟩
    have e := hrepr _ hrx
    have hr0' : ((r : 𝒪[k]) : k) ≠ 0 := fun h => hr0 (Subtype.ext h)
    have hx' : x = ((r : 𝒪[k]) : k)⁻¹ • (((r : 𝒪[k]) : k) • x) := (inv_smul_smul₀ hr0' x).symm
    rw [hx', e]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have hspan : Submodule.span k (Set.range v) = V :=
    le_antisymm (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hvV i)) hVle
  have hcard : Fintype.card ι = a := by
    rw [← finrank_span_eq_card hli, hspan, hVdef, finrank_span_eq_card hXli, Fintype.card_fin]
  let e : Fin a ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
  let Y : Matrix (Fin a) C k := Matrix.of fun i => v (e i)
  have hYV : ∀ i, Y.row i ∈ V := fun i => hvV (e i)
  choose g hg using fun i => (Submodule.mem_span_range_iff_exists_fun k).1 (hYV i)
  have hYg : (Matrix.of g) * X = Y := by
    ext i l
    have h := congrFun (hg i) l
    rw [Finset.sum_apply] at h
    rw [Matrix.mul_apply]
    exact (Finset.sum_congr rfl fun j _ => rfl).trans h
  have hYli : LinearIndependent k Y.row := hli.comp e e.injective
  have hgli : LinearIndependent k (Matrix.of g).row := by
    refine LinearIndependent.of_comp (Matrix.vecMulLinear X) ?_
    convert hYli using 1
    funext i
    rw [← hYg]
    try rfl
  have hu : IsUnit (Matrix.of g) := Matrix.linearIndependent_rows_iff_isUnit.1 hgli
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec, hYg, isPrimFrame_iff]
  refine ⟨fun i => hvΛ (e i), fun c hc i => ?_⟩
  have hcV : c ᵥ* Y ∈ V := by
    rw [vecMul_eq_sum]; exact V.sum_mem fun i _ => V.smul_mem _ (hYV i)
  have hcM : c ᵥ* Y ∈ M := ⟨hcV, hc⟩
  have e1 := hrepr _ hcM
  have e2 : c ᵥ* Y = ∑ t, c (e.symm t) • v t := by
    rw [vecMul_eq_sum, ← e.sum_comp]
    exact Finset.sum_congr rfl fun i _ => by rw [e.symm_apply_apply]; rfl
  have h := Fintype.linearIndependent_iffₛ.1 hli (fun t => c (e.symm t))
    (fun t => ((b.repr ⟨_, hcM⟩ t : 𝒪[k]) : k)) (by rw [← e2, ← e1]) (e i)
  simp only [Equiv.symm_apply_apply] at h
  rw [h]
  exact (b.repr _ _).2

end GlobalTheory.PrimFrameExist

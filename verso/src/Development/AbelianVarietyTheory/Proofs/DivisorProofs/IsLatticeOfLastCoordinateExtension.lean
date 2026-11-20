import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BrPairFApply
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.PieriBlockIdeals.StatementLA
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumExactExponentsSmulMemLocalizedCoeffLattice
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
import Formalism.LocalToGlobal.Divisibility.BrJoint
import Formalism.LocalToGlobal.Columns.CoefficientsModP
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionLemmaFirst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSmulMemOfLeLocP

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ n N hN M L hM hL`. Substitute `hN` using the available equality. Establish `hiC : ∀ k : Fin n, Formalism.L2.Col.Br.iC (rfl : n + 1 = n + 1) k = Fin.castSucc k` using `fun k => Fin.ext rfl`. Establish `hiL : Formalism.L2.Col.Br.iL (rfl : n + 1 = n + 1) = Fin.last n` using `Fin.ext rfl`. Simplify using `only [hiC, hiL] at hL`.

Set `g : (Fin n → E) →ₗ[E] (Fin (n + 1) → E)` to `{ toFun := fun x => Fin.snoc (α := fun _ => E) x 0 map_add' := by`. Introduce `x y`. Use extensionality with `j`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun i => ?_) j <;> simp`. Use the proof step `map_smul' := by`.

Introduce `a x`. Use extensionality with `j`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun i => ?_) j <;> simp }`. Establish `gC : ∀ x k, g x (Fin.castSucc k) = x k` using `fun x k => by simp [g]`. Establish `gL : ∀ x, g x (Fin.last n) = 0` using `fun x => by simp [g]`.

Set `e : Fin (n + 1) → E` to `Pi.single (Fin.last n) 1`. Establish `gm : ∀ m ∈ M, g m ∈ L` using `fun m hm => (hL _).2 ⟨by simpa [gC] using hm, 0, by simp [gL]⟩`. Establish `he : e ∈ L` using `(hL _).2 ⟨by`. Establish `: (fun k : Fin n => e (Fin.castSucc k)) = 0`. Use function extensionality and compare the values at `k`.

Simplify using `[e, Pi.single_apply, Fin.castSucc_ne_last]`. Rewrite using `[this]; exact M.zero_mem, 1, by simp [e]⟩`. Establish `dec : ∀ x : Fin (n + 1) → E, x = g (fun k => x (Fin.castSucc k)) + x (Fin.last n) • e`. Introduce `x`. Use extensionality with `j`.

Use `Fin.lastCases ?_ (fun i => ?_) j` and prove the remaining obligations. Simplify using `[gL, e]`. Simplify using `[gC, e, Pi.single_apply, Fin.castSucc_ne_last]`. Establish `hLeq : L = M.map (g.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {e}`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce `v hv`. Take `⟨hvM, c, hc⟩` from `(hL v).1 hv`. Rewrite using `[dec v]`. Use `Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_map_of_mem hvM)) (Submodule.mem_sup_right ?_)` and prove the remaining obligations. Establish `hs : (c : E) • e = c • e` using `algebraMap_smul E c e`.

Rewrite using `[← hc, hs]`. Conclude with `Submodule.smul_mem _ c (Submodule.mem_span_singleton_self e)`. Conclude with `sup_le (Submodule.map_le_iff_le_comap.2 fun m hm => gm m hm) (Submodule.span_le.2 (by simpa using he))`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hLeq]`.

Conclude with `Submodule.FG.sup (hM.fg.map _) (Submodule.fg_span_singleton e)`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Rewrite using `[dec x]`. Use `Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (Submodule.subset_span he))` and prove the remaining obligations.

Establish `hy : (fun k => x (Fin.castSucc k)) ∈ Submodule.span E (M : Set (Fin n → E))`. Rewrite using `[hM.span_eq_top]`. Conclude with `Submodule.mem_top`. Establish `hmap : (Submodule.span E (M : Set (Fin n → E))).map g ≤ Submodule.span E (L : Set (Fin (n + 1) → E))`. Rewrite using `[Submodule.map_span]`.

Conclude with `Submodule.span_mono (by rintro _ ⟨m, hm, rfl⟩; exact gm m hm)`. Conclude with `hmap (Submodule.mem_map_of_mem hy)`.
-/
theorem latLast_isLattice : ∀ {E : Type} [Field E] [NumberField E] {n N : ℕ} (hN : N = n + 1)
    (M : Submodule (𝓞 E) (Fin n → E)) (L : Submodule (𝓞 E) (Fin N → E)), Submodule.IsLattice E M →
    (∀ v, v ∈ L ↔ (fun k => v (Formalism.L2.Col.Br.iC hN k)) ∈ M ∧ ∃ c : 𝓞 E, (c : E) = v (Formalism.L2.Col.Br.iL hN)) →
    Submodule.IsLattice E L := by
  intro E _ _ n N hN M L hM hL
  subst hN
  have hiC : ∀ k : Fin n, Formalism.L2.Col.Br.iC (rfl : n + 1 = n + 1) k = Fin.castSucc k := fun k => Fin.ext rfl
  have hiL : Formalism.L2.Col.Br.iL (rfl : n + 1 = n + 1) = Fin.last n := Fin.ext rfl
  simp only [hiC, hiL] at hL
  let g : (Fin n → E) →ₗ[E] (Fin (n + 1) → E) :=
    { toFun := fun x => Fin.snoc (α := fun _ => E) x 0
      map_add' := by
        intro x y; ext j
        refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
      map_smul' := by
        intro a x; ext j
        refine Fin.lastCases ?_ (fun i => ?_) j <;> simp }
  have gC : ∀ x k, g x (Fin.castSucc k) = x k := fun x k => by simp [g]
  have gL : ∀ x, g x (Fin.last n) = 0 := fun x => by simp [g]
  let e : Fin (n + 1) → E := Pi.single (Fin.last n) 1
  have gm : ∀ m ∈ M, g m ∈ L := fun m hm => (hL _).2 ⟨by simpa [gC] using hm, 0, by simp [gL]⟩
  have he : e ∈ L := (hL _).2 ⟨by
      have : (fun k : Fin n => e (Fin.castSucc k)) = 0 := by
        funext k; simp [e, Pi.single_apply, Fin.castSucc_ne_last]
      rw [this]; exact M.zero_mem, 1, by simp [e]⟩
  have dec : ∀ x : Fin (n + 1) → E, x = g (fun k => x (Fin.castSucc k)) + x (Fin.last n) • e := by
    intro x; ext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [gL, e]
    · simp [gC, e, Pi.single_apply, Fin.castSucc_ne_last]
  have hLeq : L = M.map (g.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {e} := by
    apply le_antisymm
    · intro v hv
      obtain ⟨hvM, c, hc⟩ := (hL v).1 hv
      rw [dec v]
      refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_map_of_mem hvM))
        (Submodule.mem_sup_right ?_)
      have hs : (c : E) • e = c • e := algebraMap_smul E c e
      rw [← hc, hs]
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self e)
    · exact sup_le (Submodule.map_le_iff_le_comap.2 fun m hm => gm m hm)
        (Submodule.span_le.2 (by simpa using he))
  refine ⟨?_, ?_⟩
  · rw [hLeq]
    exact Submodule.FG.sup (hM.fg.map _) (Submodule.fg_span_singleton e)
  · rw [eq_top_iff]
    intro x _
    rw [dec x]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (Submodule.subset_span he))
    have hy : (fun k => x (Fin.castSucc k)) ∈ Submodule.span E (M : Set (Fin n → E)) := by
      rw [hM.span_eq_top]; exact Submodule.mem_top
    have hmap : (Submodule.span E (M : Set (Fin n → E))).map g ≤ Submodule.span E (L : Set (Fin (n + 1) → E)) := by
      rw [Submodule.map_span]
      exact Submodule.span_mono (by rintro _ ⟨m, hm, rfl⟩; exact gm m hm)
    exact hmap (Submodule.mem_map_of_mem hy)

end GlobalTheory

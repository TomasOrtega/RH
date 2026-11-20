import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.ParaUnit

/- English proof (translation)
Set `O` to `v.valuationSubring`. Set `A' : Matrix ι ι O` to `Matrix.of fun a b => ⟨A a b, hA a b⟩`. Set `B' : Matrix ι ι O` to `Matrix.of fun a b => ⟨B a b, hB a b⟩`. Establish `hAB' : A' * B' = 1`. Use extensionality with `a b`.

Use `congrFun (congrFun hAB a) b` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply]`. Simplify using `only [Matrix.mul_apply, Matrix.one_apply] at this ⊢`. Rewrite using `[AddSubmonoidClass.coe_finsetSum, apply_ite (fun x : O => (x : K))]`. Simplify `this` using `[A', B']`.

Set `f` to `IsLocalRing.residue O`. Establish `hf : ∀ a b, p a → ¬ p b → f (A' a b) = 0`. Introduce `a b ha hb`. Rewrite using `[IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]`. Conclude with `hlow a b ha hb`.

Set `A₁ : Matrix {x // p x} {x // p x} O` to `Matrix.of fun a b => A' a.1 b.1`. Set `B₁ : Matrix {x // p x} {x // p x} O` to `Matrix.of fun a b => B' a.1 b.1`. Establish `h1 : f.mapMatrix A₁ * f.mapMatrix B₁ = 1`. Use extensionality with `a b`. Establish `h` using `congrArg f (congrFun (congrFun hAB' a.1) b.1)`.

Rewrite `h` using `[Matrix.mul_apply, map_sum, ← Fintype.sum_subtype_add_sum_subtype p]`. Rewrite `h` using `[Finset.sum_eq_zero (s := (Finset.univ : Finset {x // ¬ p x})) (fun c _ => by rw [map_mul, hf a.1 c.1 a.2 c.2, zero_mul]), add_zero]`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [map_mul] at h`. Use `Eq.trans h ?_` and prove the remaining obligations.

Simplify using `only [Matrix.one_apply, Subtype.ext_iff]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `h2 : f A₁.det ≠ 0`. Introduce `h0`. Use `congrArg Matrix.det h1` as an intermediate fact.

Rewrite `this` using `[Matrix.det_mul, ← RingHom.map_det, h0, zero_mul, Matrix.det_one]`. Conclude with `zero_ne_one this`. Establish `h3 : ((A₁.det : O) : K) = (Matrix.of fun a b : {x // p x} => A a.1 b.1).det`. Use `RingHom.map_det O.subtype A₁` as an intermediate fact. Conclude with `this`.

Rewrite using `[← h3]`. Use `le_antisymm A₁.det.2 (not_lt.1 fun hlt => h2 ?_)` and prove the remaining obligations. Rewrite using `[IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]`. Conclude with `hlt`.
-/
theorem val_det_block {K Γ ι : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] [Fintype ι] [DecidableEq ι]
    (v : Valuation K Γ) (p : ι → Prop) [DecidablePred p] (A B : Matrix ι ι K)
    (hA : ∀ a b, v (A a b) ≤ 1) (hB : ∀ a b, v (B a b) ≤ 1) (hAB : A * B = 1)
    (hlow : ∀ a b, p a → ¬ p b → v (A a b) < 1) :
    v (Matrix.of fun a b : {x // p x} => A a.1 b.1).det = 1 := by
  let O := v.valuationSubring
  let A' : Matrix ι ι O := Matrix.of fun a b => ⟨A a b, hA a b⟩
  let B' : Matrix ι ι O := Matrix.of fun a b => ⟨B a b, hB a b⟩
  have hAB' : A' * B' = 1 := by
    ext a b
    have := congrFun (congrFun hAB a) b
    rw [Matrix.mul_apply] at this
    simp only [Matrix.mul_apply, Matrix.one_apply] at this ⊢
    rw [AddSubmonoidClass.coe_finsetSum, apply_ite (fun x : O => (x : K))]
    simpa [A', B'] using this
  let f := IsLocalRing.residue O
  have hf : ∀ a b, p a → ¬ p b → f (A' a b) = 0 := by
    intro a b ha hb
    rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
    exact hlow a b ha hb
  let A₁ : Matrix {x // p x} {x // p x} O := Matrix.of fun a b => A' a.1 b.1
  let B₁ : Matrix {x // p x} {x // p x} O := Matrix.of fun a b => B' a.1 b.1
  have h1 : f.mapMatrix A₁ * f.mapMatrix B₁ = 1 := by
    ext a b
    have h := congrArg f (congrFun (congrFun hAB' a.1) b.1)
    rw [Matrix.mul_apply, map_sum, ← Fintype.sum_subtype_add_sum_subtype p] at h
    rw [Finset.sum_eq_zero (s := (Finset.univ : Finset {x // ¬ p x}))
      (fun c _ => by rw [map_mul, hf a.1 c.1 a.2 c.2, zero_mul]), add_zero] at h
    rw [Matrix.mul_apply]
    simp only [map_mul] at h
    refine Eq.trans h ?_
    simp only [Matrix.one_apply, Subtype.ext_iff]
    split_ifs <;> simp
  have h2 : f A₁.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, ← RingHom.map_det, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have h3 : ((A₁.det : O) : K) = (Matrix.of fun a b : {x // p x} => A a.1 b.1).det := by
    have := RingHom.map_det O.subtype A₁
    exact this
  rw [← h3]
  refine le_antisymm A₁.det.2 (not_lt.1 fun hlt => h2 ?_)
  rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  exact hlt

/- English proof (translation)
Introduce `L _ _ _ n r s h hp`. Establish `key : ∀ g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)), g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring → ∀ a b, Valued.v (g.val a b) ≤ 1`. Introduce and unpack `g ⟨x, rfl⟩ a b`. Conclude with `(x.val a b).2`. Establish `hA` using `key h hp.1`.

Establish `hB` using `key h⁻¹ (inv_mem hp.1)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `val_det_block Valued.v (fun x : Fin n => r ≤ x.val) h.val (h⁻¹).val hA hB (by simp) (fun a b ha hb => hp.2 a b ha (not_le.1 hb))`. Unfold `NG.supDiag`. Use `Valuation.map_sum_le _ fun a _ => Valuation.map_sum_le _ fun b _ => ?_` and prove the remaining obligations.

Use `split_ifs`. Conclude with `hA a b`. Simplify using the standard rewrite rules.
-/
theorem detDD_unit_supDiag_int : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (r : ℕ) (s : SplitPlace L) (h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))), NG.ParaRT s r h → Valued.v (NG.detDD s r h) = 1 ∧ Valued.v (NG.supDiag s r h) ≤ 1 := by
  intro L _ _ _ n r s h hp
  have key : ∀ g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)),
      g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring →
      ∀ a b, Valued.v (g.val a b) ≤ 1 := by
    rintro g ⟨x, rfl⟩ a b
    exact (x.val a b).2
  have hA := key h hp.1
  have hB := key h⁻¹ (inv_mem hp.1)
  refine ⟨?_, ?_⟩
  · exact val_det_block Valued.v (fun x : Fin n => r ≤ x.val) h.val (h⁻¹).val hA hB (by simp)
      (fun a b ha hb => hp.2 a b ha (not_le.1 hb))
  · unfold NG.supDiag
    refine Valuation.map_sum_le _ fun a _ => Valuation.map_sum_le _ fun b _ => ?_
    split_ifs
    · exact hA a b
    · simp

end GlobalTheory.ParaUnit

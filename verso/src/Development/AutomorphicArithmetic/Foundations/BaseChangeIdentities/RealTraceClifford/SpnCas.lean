import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SpnAdj
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfMulSum
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.MultTrOnBot
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SymOfMul
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfBasic
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.IsoFacts
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Sl2Core
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.TraceRestrictSupDisjoint
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DominantRearrangementProperties

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

namespace UpperTheory.RealTr.SpinCasimir

variable {n : ℕ} {J : Type} [Fintype J] [DecidableEq J]

private abbrev Fm (c : Fin n → Fin n → Matrix J J ℂ) : Fin n → Fin n → Module.End ℂ (Ten J ℂ) :=
  dg (fun _ _ : Fin n => (0 : Module.End ℂ ℂ)) c

/- English proof (translation)
Simplify using `[Fm, dg]`.
-/
private theorem Fm_eq (c : Fin n → Fin n → Matrix J J ℂ) (a b : Fin n) :
    Fm c a b = mt ℂ (spn c a b) := by
  simp [Fm, dg]

/- English proof (translation)
Establish `key : ∀ a j, (Fm c a a x) j = (η j a : ℂ) * x j`. Introduce `a j`. Rewrite using `[Fm_eq, h.diag a]`. Simplify using `[mt, Matrix.diagonal_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx j hj`. Use function extensionality and compare the values at `a`. Establish `e : (Fm c a a x) j = ((μ a : ℂ) • x) j` using `congrArg (fun y : Ten J ℂ => y j) (hx a)`. Rewrite `e` using `[key]`. Establish `e' : (η j a : ℂ) * x j = (μ a : ℂ) * x j` using `by simpa using e`.

Conclude with `Complex.ofReal_injective (mul_right_cancel₀ hj e')`. Introduce `hx a`. Use extensionality with `j`. Rewrite using `[key]`. Distinguish the cases in `hj : x j = 0`.

Simplify using `[hj]`. Simplify using `[hx j hj]`.
-/
private theorem mem_wsp (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n) (h : ClifMod c η)
    (μ : Wt n) (x : Ten J ℂ) : x ∈ wsp (Fm c) μ ↔ ∀ j, x j ≠ 0 → η j = μ := by
  have key : ∀ a j, (Fm c a a x) j = (η j a : ℂ) * x j := by
    intro a j
    rw [Fm_eq, h.diag a]
    simp [mt, Matrix.diagonal_apply]
  constructor
  · intro hx j hj
    funext a
    have e : (Fm c a a x) j = ((μ a : ℂ) • x) j := congrArg (fun y : Ten J ℂ => y j) (hx a)
    rw [key] at e
    have e' : (η j a : ℂ) * x j = (μ a : ℂ) * x j := by simpa using e
    exact Complex.ofReal_injective (mul_right_cancel₀ hj e')
  · intro hx a
    ext j
    rw [key]
    by_cases hj : x j = 0
    · simp [hj]
    · simp [hx j hj]

private def wEquiv (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n) (h : ClifMod c η) (μ : Wt n) :
    wsp (Fm c) μ ≃ₗ[ℂ] ({j // η j = μ} → ℂ) where
  toFun x := fun j => x.1 j.1
  map_add' x y := by ext j; simp
  map_smul' r x := by ext j; simp
  invFun y := ⟨WithLp.toLp 2 fun j => if hj : η j = μ then y ⟨j, hj⟩ else 0, by
    rw [mem_wsp c η h]
    intro j hj
    by_contra hc
    exact hj (by simp [hc])⟩
  left_inv x := by
    ext j
    by_cases hj : η j = μ
    · simp [hj]
    · have : x.1 j = 0 := by
        by_contra hc
        exact hj ((mem_wsp c η h μ x.1).1 x.2 j hc)
      simp [hj, this]
  right_inv y := by
    ext j
    simp [j.2]

/- English proof (translation)
Simplify using `[cf, ex, Finsupp.finset_sum_apply, Finsupp.single_apply, Fintype.card_subtype]`.
-/
private theorem cf_sum_ex (η : J → Wt n) (μ : Wt n) :
    cf (∑ j, ex (η j)) μ = (Fintype.card {j // η j = μ} : ℂ) := by
  classical
  simp [cf, ex, Finsupp.finset_sum_apply, Finsupp.single_apply, Fintype.card_subtype]

/- English proof (translation)
Introduce `μ`. Rewrite using `[cf_sum_ex, inf_top_eq, (trAdd _ 1).2.2.2 _ inferInstance, (wEquiv c η h μ).finrank_eq, Module.finrank_fintype_fun_eq_card]`.
-/
private theorem isCh_top (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n) (h : ClifMod c η) :
    IsCh (Fm c) ⊤ 1 (∑ j, ex (η j)) := by
  intro μ
  rw [cf_sum_ex, inf_top_eq, (trAdd _ 1).2.2.2 _ inferInstance,
    (wEquiv c η h μ).finrank_eq, Module.finrank_fintype_fun_eq_card]

/- English proof (translation)
Use extensionality with `j k`. Establish `e` using `congrArg (fun y : Ten J ℂ => y j) (hs (WithLp.toLp 2 (Pi.single k 1)))`. Simplify `e` using `[mt, Pi.single_apply, Matrix.one_apply, eq_comm]`.
-/
private theorem mt_ext (M : Matrix J J ℂ) (s : ℂ) (hs : ∀ x : Ten J ℂ, mt ℂ M x = s • x) :
    M = s • (1 : Matrix J J ℂ) := by
  ext j k
  have e := congrArg (fun y : Ten J ℂ => y j) (hs (WithLp.toLp 2 (Pi.single k 1)))
  simpa [mt, Pi.single_apply, Matrix.one_apply, eq_comm] using e

/- English proof (translation)
Take `⟨φ, hφ⟩` from `(tenF n ℂ J).1`. Simplify using `only [Cas, Fm_eq, ← hφ, map_sum, map_mul]`.
-/
private theorem cas_eq (c : Fin n → Fin n → Matrix J J ℂ) :
    Cas (Fm c) = mt ℂ (Cas (spn c)) := by
  obtain ⟨φ, hφ⟩ := (tenF n ℂ J).1
  simp only [Cas, Fm_eq, ← hφ, map_sum, map_mul]

/- English proof (translation)
Rewrite using `[inf_top_eq]`. Assume the negation of the conclusion as `hne`. Take `⟨x, hx, hx0⟩` from `(Submodule.ne_bot_iff _).1 hne`. Establish `hS : FiniteDimensional ℂ (⊤ : Submodule ℂ (Ten J ℂ))` using `inferInstance`. Establish `hStb : Stb (Fm c) ⊤` using `fun _ _ _ _ => Submodule.mem_top`.

Establish `hdom : Dom μ` using `hwDom n _ _ hU ⊤ hS hStb μ x Submodule.mem_top hx0 hx`. Take `⟨-, -, hρ, -, hd, -⟩` from `rearr n`. Establish `hanti : StrictAnti (μ + rhoV n)` using `(hd μ hdom).1.add_strictAnti hρ`. Establish `hm` using `mult n _ _ hU ⊤ hS hStb 1 _ ⟨fun a b => by simp, fun _ _ => Submodule.mem_top⟩ (isCh_top c η h) μ hanti`. Establish `hfin : FiniteDimensional ℂ (hw (Fm c) μ ⊓ ⊤ : Submodule ℂ (Ten J ℂ))` using `inferInstance`.

Rewrite `hm` using `[(trAdd _ 1).2.2.2 _ hfin, inf_top_eq, h.chr, mul_smul_comm, ← (chRF n).1]`. Establish `hpos : Module.finrank ℂ (hw (Fm c) μ) ≠ 0`. Introduce `h0`. Conclude with `hne (Submodule.finrank_eq_zero.1 h0)`. Establish `h2 : StrictAnti ((2 : ℝ) • rhoV n)` using `fun a b hab => by`.

Use `hρ hab` as an intermediate fact. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨-, -, -, hcf, -, -, -, -, -, -, -, htop, -⟩` from `cfBasic n`. Establish `hne2 : μ + rhoV n ≠ (2 : ℝ) • rhoV n` using `fun e => hμ (by`.

Use function extensionality and compare the values at `a`. Use `congrFun e a` as an intermediate fact. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this`. Use the proof step `linarith)`. Rewrite `hm` using `[(hcf _ 0 _ _).2, (htop _ h2).2 _ hanti hne2, mul_zero]`.

Conclude with `hpos (by exact_mod_cast hm.symm)`.
-/
private theorem hw_bot (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n) (h : ClifMod c η)
    (hU : UF (Fm c)) (μ : Wt n) (hμ : μ ≠ rhoV n) : hw (Fm c) μ ⊓ ⊤ = ⊥ := by
  rw [inf_top_eq]
  by_contra hne
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hS : FiniteDimensional ℂ (⊤ : Submodule ℂ (Ten J ℂ)) := inferInstance
  have hStb : Stb (Fm c) ⊤ := fun _ _ _ _ => Submodule.mem_top
  have hdom : Dom μ := hwDom n _ _ hU ⊤ hS hStb μ x Submodule.mem_top hx0 hx
  obtain ⟨-, -, hρ, -, hd, -⟩ := rearr n
  have hanti : StrictAnti (μ + rhoV n) := (hd μ hdom).1.add_strictAnti hρ
  have hm := mult n _ _ hU ⊤ hS hStb 1 _ ⟨fun a b => by simp, fun _ _ => Submodule.mem_top⟩
    (isCh_top c η h) μ hanti
  have hfin : FiniteDimensional ℂ (hw (Fm c) μ ⊓ ⊤ : Submodule ℂ (Ten J ℂ)) := inferInstance
  rw [(trAdd _ 1).2.2.2 _ hfin, inf_top_eq, h.chr, mul_smul_comm, ← (chRF n).1] at hm
  have hpos : Module.finrank ℂ (hw (Fm c) μ) ≠ 0 := by
    intro h0
    exact hne (Submodule.finrank_eq_zero.1 h0)
  have h2 : StrictAnti ((2 : ℝ) • rhoV n) := fun a b hab => by
    have := hρ hab
    simp only [Pi.smul_apply, smul_eq_mul]
    linarith
  obtain ⟨-, -, -, hcf, -, -, -, -, -, -, -, htop, -⟩ := cfBasic n
  have hne2 : μ + rhoV n ≠ (2 : ℝ) • rhoV n := fun e => hμ (by
    funext a
    have := congrFun e a
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith)
  rw [(hcf _ 0 _ _).2, (htop _ h2).2 _ hanti hne2, mul_zero] at hm
  exact hpos (by exact_mod_cast hm.symm)

end UpperTheory.RealTr.SpinCasimir

open UpperTheory.RealTr.SpinCasimir in
/- English proof (translation)
Introduce `n J _ _ c η h`. Establish `hU : UF (Fm c)` using `(tenF n ℂ J).2.2.2.2 _ c η uf_zero h`. Establish `hS : FiniteDimensional ℂ (⊤ : Submodule ℂ (Ten J ℂ))` using `inferInstance`. Establish `hStb : Stb (Fm c) ⊤` using `fun _ _ _ _ => Submodule.mem_top`. Establish `hiso` using `(isoFacts n _ _ hU ⊤ hS hStb (rhoV n) (hw_bot c η h hU)).1`.

Establish `hn : nsq (rhoV n + rhoV n) - nsq (rhoV n) = 3 * nsq (rhoV n)`. Simplify using `only [nsq, Pi.add_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun a _ => by ring`. Use `mt_ext _ _ fun x => ?_` and prove the remaining obligations. Rewrite using `[← cas_eq, hiso x Submodule.mem_top, hn]`.
-/
theorem UpperTheory.RealTr.spnCas :
    ∀ n : ℕ, ∀ (J : Type) [Fintype J] [DecidableEq J] (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n), ClifMod c η → Cas (spn c) = ((3 * nsq (rhoV n) : ℝ) : ℂ) • (1 : Matrix J J ℂ) := by
  intro n J _ _ c η h
  have hU : UF (Fm c) := (tenF n ℂ J).2.2.2.2 _ c η uf_zero h
  have hS : FiniteDimensional ℂ (⊤ : Submodule ℂ (Ten J ℂ)) := inferInstance
  have hStb : Stb (Fm c) ⊤ := fun _ _ _ _ => Submodule.mem_top
  have hiso := (isoFacts n _ _ hU ⊤ hS hStb (rhoV n) (hw_bot c η h hU)).1
  have hn : nsq (rhoV n + rhoV n) - nsq (rhoV n) = 3 * nsq (rhoV n) := by
    simp only [nsq, Pi.add_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  refine mt_ext _ _ fun x => ?_
  rw [← cas_eq, hiso x Submodule.mem_top, hn]

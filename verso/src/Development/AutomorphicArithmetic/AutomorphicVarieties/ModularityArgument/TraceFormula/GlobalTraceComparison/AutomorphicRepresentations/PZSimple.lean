import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

/- English proof (translation)
Introduce `hG hC hS hY E _ _ _ n S Z N hSec hZ hN π y W hW hst`. Establish `key : ∀ U : Submodule ℂ (Sm E n), U ≤ y.Y → (∀ i, Sl S i → ∀ f, IsHecke (N i.1) f → ∀ x ∈ U, Lw N i.1 i.2 f x ∈ U) → U = ⊥ ∨ U = y.Y`. Introduce `U hU hUs`. Establish `hgen` using `hG E n S Z N hSec hZ hN U (hU.trans y.fix) hUs`. Establish `hs` using `y.simple (U.comap y.Y.subtype) (by`.

Introduce `h hh x hx`. Establish `hmem : ((y.r h x : y.Y) : Sm E n) ∈ U`. Rewrite using `[y.act h hh x]`. Conclude with `hgen h hh _ hx`. Conclude with `hmem)`.

Break down `hs with hs | hs` into its components or cases. Use `left`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Establish `hx' : (⟨x, hU hx⟩ : y.Y) ∈ U.comap y.Y.subtype` using `hx`.

Rewrite `hx'` using `[hs]`. Establish `h0` using `(Submodule.mem_bot ℂ).1 hx'`. Conclude with `(Submodule.mem_bot ℂ).2 (congrArg Subtype.val h0)`. Use `right`. Use `le_antisymm hU fun x hx => ?_` and prove the remaining obligations.

Establish `hx' : (⟨x, hx⟩ : y.Y) ∈ U.comap y.Y.subtype`. Rewrite using `[hs]`. Conclude with `Submodule.mem_top`. Conclude with `hx'`. Establish `scal : ∀ i, Sl S i → i.1 ∉ Z → ∀ f, IsHecke (N i.1) f → ∃ c : ℂ, ∀ x ∈ y.Y, Lw N i.1 i.2 f x = c • x`.

Introduce `i hi hiZ f hf`. Use `haveI := y.fd`. Use `haveI : Nontrivial y.Y := Submodule.nontrivial_iff_ne_bot.2 y.ne`. Establish `hNw : N i.1 = KGL i.1 n` using `(hN i.1).2.2.2 hiZ`. Set `T : Module.End ℂ y.Y` to `(Lw N i.1 i.2 f).restrict (fun x hx => hY E n S Z N hSec hZ hN π y i hi f hf x hx)`.

Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue T`. Take `⟨v, hv⟩` from `hc.exists_hasEigenvector`. Use `⟨c, ?_⟩` and prove the remaining obligations. Set `U : Submodule ℂ (Sm E n)` to `y.Y ⊓ LinearMap.ker (Lw N i.1 i.2 f - c • LinearMap.id)`. Establish `memU : ∀ x, x ∈ U ↔ x ∈ y.Y ∧ Lw N i.1 i.2 f x = c • x`.

Introduce `x`. Simplify using `[U, Submodule.mem_inf, LinearMap.mem_ker, sub_eq_zero]`. Establish `hcomm : ∀ k, Sl S k → ∀ g, IsHecke (N k.1) g → ∀ x ∈ y.Y, Lw N i.1 i.2 f (Lw N k.1 k.2 g x) = Lw N k.1 k.2 g (Lw N i.1 i.2 f x)`. Introduce `k hk g hg x hx`. Distinguish the cases in `hik : i = k`.

Substitute `hik` using the available equality. Establish `hxf : x ∈ fixed (rw' n i.1 i.2) (N i.1)` using `((hC E n S Z N hSec hZ hN i hi f hf).1 x (y.fix hx)).1`. Rewrite `hf`, `hg`, `hxf` using `[hNw]`. Simplify using `only [Lw]`. Rewrite using `[hNw]`.

Conclude with `hS E n i.1 (Sm E n) (rw' n i.1 i.2) f g hf hg x hxf`. Conclude with `LinearMap.congr_fun ((hC E n S Z N hSec hZ hN i hi f hf).2 k hk hik g hg).eq x`. Establish `hUs : ∀ k, Sl S k → ∀ g, IsHecke (N k.1) g → ∀ x ∈ U, Lw N k.1 k.2 g x ∈ U`. Introduce `k hk g hg x hx`. Take `⟨hxY, hxe⟩` from `(memU x).1 hx`.

Use `(memU _).2 ⟨hY E n S Z N hSec hZ hN π y k hk g hg x hxY, ?_⟩` and prove the remaining obligations. Rewrite using `[hcomm k hk g hg x hxY, hxe, map_smul]`. Establish `hvU : (v : Sm E n) ∈ U`. Use `(memU _).2 ⟨v.2, ?_⟩` and prove the remaining obligations. Establish `h1 : T v = c • v` using `hv.apply_eq_smul`.

Conclude with `congrArg Subtype.val h1`. Break down `key U inf_le_left hUs with h0 | h1` into its components or cases. It suffices to derive a contradiction. Rewrite `hvU` using `[h0]`. Conclude with `hv.2 (Subtype.ext ((Submodule.mem_bot ℂ).1 hvU))`.

Introduce `x hx`. Rewrite `hx` using `[← h1]`. Conclude with `((memU x).1 hx).2`. Use `key W hW fun i hi f hf x hx => ?_` and prove the remaining obligations. Distinguish the cases in `hiZ : i.1 ∈ Z`.

Conclude with `hst i.1 hiZ i.2 f hf x hx`. Take `⟨c, hc⟩` from `scal i hi hiZ f hf`. Rewrite using `[hc x (hW hx)]`. Conclude with `W.smul_mem c hx`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.zSimple_pf :
    GenLoc → LocComm → SphOp → YLoc → ZSimple := by
  intro hG hC hS hY E _ _ _ n S Z N hSec hZ hN π y W hW hst
  have key : ∀ U : Submodule ℂ (Sm E n), U ≤ y.Y →
      (∀ i, Sl S i → ∀ f, IsHecke (N i.1) f → ∀ x ∈ U, Lw N i.1 i.2 f x ∈ U) →
      U = ⊥ ∨ U = y.Y := by
    intro U hU hUs
    have hgen := hG E n S Z N hSec hZ hN U (hU.trans y.fix) hUs
    have hs := y.simple (U.comap y.Y.subtype) (by
      intro h hh x hx
      have hmem : ((y.r h x : y.Y) : Sm E n) ∈ U := by
        rw [y.act h hh x]
        exact hgen h hh _ hx
      exact hmem)
    rcases hs with hs | hs
    · left
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hU hx⟩ : y.Y) ∈ U.comap y.Y.subtype := hx
      rw [hs] at hx'
      have h0 := (Submodule.mem_bot ℂ).1 hx'
      exact (Submodule.mem_bot ℂ).2 (congrArg Subtype.val h0)
    · right
      refine le_antisymm hU fun x hx => ?_
      have hx' : (⟨x, hx⟩ : y.Y) ∈ U.comap y.Y.subtype := by
        rw [hs]
        exact Submodule.mem_top
      exact hx'
  have scal : ∀ i, Sl S i → i.1 ∉ Z → ∀ f, IsHecke (N i.1) f →
      ∃ c : ℂ, ∀ x ∈ y.Y, Lw N i.1 i.2 f x = c • x := by
    intro i hi hiZ f hf
    haveI := y.fd
    haveI : Nontrivial y.Y := Submodule.nontrivial_iff_ne_bot.2 y.ne
    have hNw : N i.1 = KGL i.1 n := (hN i.1).2.2.2 hiZ
    let T : Module.End ℂ y.Y := (Lw N i.1 i.2 f).restrict
      (fun x hx => hY E n S Z N hSec hZ hN π y i hi f hf x hx)
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
    obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
    refine ⟨c, ?_⟩
    let U : Submodule ℂ (Sm E n) := y.Y ⊓ LinearMap.ker (Lw N i.1 i.2 f - c • LinearMap.id)
    have memU : ∀ x, x ∈ U ↔ x ∈ y.Y ∧ Lw N i.1 i.2 f x = c • x := by
      intro x
      simp [U, Submodule.mem_inf, LinearMap.mem_ker, sub_eq_zero]
    have hcomm : ∀ k, Sl S k → ∀ g, IsHecke (N k.1) g → ∀ x ∈ y.Y,
        Lw N i.1 i.2 f (Lw N k.1 k.2 g x) = Lw N k.1 k.2 g (Lw N i.1 i.2 f x) := by
      intro k hk g hg x hx
      by_cases hik : i = k
      · subst hik
        have hxf : x ∈ fixed (rw' n i.1 i.2) (N i.1) := ((hC E n S Z N hSec hZ hN i hi f hf).1 x (y.fix hx)).1
        rw [hNw] at hf hg hxf
        simp only [Lw]
        rw [hNw]
        exact hS E n i.1 (Sm E n) (rw' n i.1 i.2) f g hf hg x hxf
      · exact LinearMap.congr_fun ((hC E n S Z N hSec hZ hN i hi f hf).2 k hk hik g hg).eq x
    have hUs : ∀ k, Sl S k → ∀ g, IsHecke (N k.1) g → ∀ x ∈ U, Lw N k.1 k.2 g x ∈ U := by
      intro k hk g hg x hx
      obtain ⟨hxY, hxe⟩ := (memU x).1 hx
      refine (memU _).2 ⟨hY E n S Z N hSec hZ hN π y k hk g hg x hxY, ?_⟩
      rw [hcomm k hk g hg x hxY, hxe, map_smul]
    have hvU : (v : Sm E n) ∈ U := by
      refine (memU _).2 ⟨v.2, ?_⟩
      have h1 : T v = c • v := hv.apply_eq_smul
      exact congrArg Subtype.val h1
    rcases key U inf_le_left hUs with h0 | h1
    · exfalso
      rw [h0] at hvU
      exact hv.2 (Subtype.ext ((Submodule.mem_bot ℂ).1 hvU))
    · intro x hx
      rw [← h1] at hx
      exact ((memU x).1 hx).2
  refine key W hW fun i hi f hf x hx => ?_
  by_cases hiZ : i.1 ∈ Z
  · exact hst i.1 hiZ i.2 f hf x hx
  · obtain ⟨c, hc⟩ := scal i hi hiZ f hf
    rw [hc x (hW hx)]
    exact W.smul_mem c hx

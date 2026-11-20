import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentProductEquivalence.CsReorderord

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace PositivityTheory.PfEss.Zc2

section OrderFree

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Take `⟨n, a⟩` from `x`. Take `⟨m, b⟩` from `y`. Take `rfl : n = m` from `hx.deg_eq.symm.trans hy.deg_eq`. Establish `key : IrrGL.of a.rep.ρ a.rep.smooth a.rep.irr = IrrGL.of b.rep.ρ b.rep.smooth b.rep.irr` using `IrrGL.of_eq_of.mpr (IsLSeg.unique hy hx)`. Establish `ea : IrrGL.of a.rep.ρ a.rep.smooth a.rep.irr = ⟨n, a⟩` using `by conv_rhs => rw [← a.cl_rep]`.

Both sides reduce to the same expression. Establish `eb : IrrGL.of b.rep.ρ b.rep.smooth b.rep.irr = ⟨n, b⟩` using `by conv_rhs => rw [← b.cl_rep]`. Both sides reduce to the same expression. Rewrite using `[← ea, ← eb]`. Conclude with `key`.
-/
theorem irrGL_eq_of_isLSeg_same {Δ : Segment k} {x y : IrrGL k} (hx : IsLSeg Δ x.rep) (hy : IsLSeg Δ y.rep) :
    x = y := by
  obtain ⟨n, a⟩ := x
  obtain ⟨m, b⟩ := y
  obtain rfl : n = m := hx.deg_eq.symm.trans hy.deg_eq
  have key : IrrGL.of a.rep.ρ a.rep.smooth a.rep.irr = IrrGL.of b.rep.ρ b.rep.smooth b.rep.irr :=
    IrrGL.of_eq_of.mpr (IsLSeg.unique hy hx)
  have ea : IrrGL.of a.rep.ρ a.rep.smooth a.rep.irr = ⟨n, a⟩ := by
    conv_rhs => rw [← a.cl_rep]
    rfl
  have eb : IrrGL.of b.rep.ρ b.rep.smooth b.rep.irr = ⟨n, b⟩ := by
    conv_rhs => rw [← b.cl_rep]
    rfl
  rw [← ea, ← eb]
  exact key

/- English proof (translation)
Establish `hc : ∀ b : α, Fintype.card {a // y a = b} = Fintype.card {a // x a = b}`. Introduce `b`. Establish `hb` using `congrArg (Multiset.count b) h`. Rewrite `hb` using `[Multiset.count_map, Multiset.count_map]`. Rewrite using `[Fintype.card_subtype, Fintype.card_subtype, Finset.card_def, Finset.card_def, Finset.filter_val, Finset.filter_val]`.

Establish `e1 : (fun a => b = y a) = (fun a => y a = b)` using `funext fun a => propext eq_comm`. Establish `e2 : (fun a => b = x a) = (fun a => x a = b)` using `funext fun a => propext eq_comm`. Apply the tactic sequence `convert hb using 3 <;> simp [eq_comm]`. Use `⟨Equiv.ofFiberEquiv (fun b => Fintype.equivOfCardEq (hc b)), fun a => ?_⟩` and prove the remaining obligations. Conclude with `(Equiv.ofFiberEquiv_map _ a).symm`.
-/
theorem perm_of_univ_map_eq {α : Type*} {l : ℕ} {x y : Fin l → α}
    (h : Finset.univ.val.map y = Finset.univ.val.map x) : ∃ e : Equiv.Perm (Fin l), ∀ a, y a = x (e a) := by
  classical
  have hc : ∀ b : α, Fintype.card {a // y a = b} = Fintype.card {a // x a = b} := by
    intro b
    have hb := congrArg (Multiset.count b) h
    rw [Multiset.count_map, Multiset.count_map] at hb
    rw [Fintype.card_subtype, Fintype.card_subtype, Finset.card_def, Finset.card_def,
      Finset.filter_val, Finset.filter_val]
    have e1 : (fun a => b = y a) = (fun a => y a = b) := funext fun a => propext eq_comm
    have e2 : (fun a => b = x a) = (fun a => x a = b) := funext fun a => propext eq_comm
    convert hb using 3 <;> simp [eq_comm]
  refine ⟨Equiv.ofFiberEquiv (fun b => Fintype.equivOfCardEq (hc b)), fun a => ?_⟩
  exact (Equiv.ofFiberEquiv_map _ a).symm

end OrderFree

/- English proof (translation)
Introduce `k _ _ _ _ hIA hUC 𝔪 n N x hd hLF V _ _ π hL`. Take `⟨m, x', hd', ⟨Δ', ⟨hm', hord'⟩, hseg'⟩, hcos⟩` from `hL`. Take `⟨Δ, ⟨hm, hord⟩, hseg⟩` from `hLF`. Choose the witnesses or unpack the hypotheses as in `rfl : m = n := by`. Establish `hc` using `congrArg Multiset.card (hm'.trans hm.symm)`.

Simplify using `using hc`. Take `⟨e, he⟩` from `perm_of_univ_map_eq (x := Δ') (y := Δ) (hm.trans hm'.symm)`. Establish `hxe : ∀ a, x' (e a) = x a` using `fun a => irrGL_eq_of_isLSeg_same (Δ := Δ a) (by rw [he a]; exact hseg' (e a)) (hseg a)`. Establish `hdσ : ∑ a, (x' (e a)).fst = N`. Simplify using `only [hxe]`.

Conclude with `hd`. Establish `hordσ : ∀ i j, i < j → ¬(Δ' (e i)).Precedes (Δ' (e j))`. Introduce `i j hij`. Rewrite using `[← he i, ← he j]`. Conclude with `hord i j hij`.

Take `⟨f⟩` from `cs_reorderord hIA hUC Δ' e x' hd' hdσ hord' hordσ hseg'`. Take `⟨g⟩` from `prodIrr_equiv_of_eq (funext hxe : x' ∘ e = x) hdσ hd`. Conclude with `hcos.of_equiv (Representation.Equiv.refl π) (f.trans g)`.
-/
theorem cs_orderfree : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LUnlinkedComm k → LOrderFree k := by
  intro k _ _ _ _ hIA hUC 𝔪 n N x hd hLF V _ _ π hL
  obtain ⟨m, x', hd', ⟨Δ', ⟨hm', hord'⟩, hseg'⟩, hcos⟩ := hL
  obtain ⟨Δ, ⟨hm, hord⟩, hseg⟩ := hLF
  obtain rfl : m = n := by
    have hc := congrArg Multiset.card (hm'.trans hm.symm)
    simpa using hc
  obtain ⟨e, he⟩ := perm_of_univ_map_eq (x := Δ') (y := Δ) (hm.trans hm'.symm)
  have hxe : ∀ a, x' (e a) = x a := fun a =>
    irrGL_eq_of_isLSeg_same (Δ := Δ a) (by rw [he a]; exact hseg' (e a)) (hseg a)
  have hdσ : ∑ a, (x' (e a)).fst = N := by
    simp only [hxe]
    exact hd
  have hordσ : ∀ i j, i < j → ¬(Δ' (e i)).Precedes (Δ' (e j)) := by
    intro i j hij
    rw [← he i, ← he j]
    exact hord i j hij
  obtain ⟨f⟩ := cs_reorderord hIA hUC Δ' e x' hd' hdσ hord' hordσ hseg'
  obtain ⟨g⟩ := prodIrr_equiv_of_eq (funext hxe : x' ∘ e = x) hdσ hd
  exact hcos.of_equiv (Representation.Equiv.refl π) (f.trans g)

end PositivityTheory.PfEss.Zc2

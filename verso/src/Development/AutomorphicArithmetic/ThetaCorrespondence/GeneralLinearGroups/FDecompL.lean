import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FirstIn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.ExistsJacQuot
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FAssocL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTwoBlocksEmptyProductLeft
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `nonempty_prod₂_equiv_prodIrr_pair y z hd`.
-/
private theorem ind₂_equiv_pair (y z : IrrGL k) {N : ℕ} (h : y.1 + z.1 = N) (hd : ∑ a, (![y, z] a).1 = N) :
    Nonempty ((ind₂ (stdSum h) (extTensor y.rep z.rep)).Equiv (prodIrr ![y, z] hd)) := by
  subst h
  exact nonempty_prod₂_equiv_prodIrr_pair y z hd

/- English proof (translation)
Set `o : IrrRep (GL (Fin 0) k)` to `IrrRep.det (k := k) (Fin 0) 1 isSmoothChar_one`. Set `y : IrrGL k` to `IrrGL.of o.ρ o.smooth o.irr`. Establish `φ : o.ρ.Equiv y.rep` using `IrrGL.equivOf o.ρ o.smooth o.irr`. Establish `κ : y.2.rep.V ≃ₗ[ℂ] ℂ` using `φ.toLinearEquiv.symm`. Establish `h : 0 + x.1 = x.1` using `Nat.zero_add _`.

Establish `hd : ∑ a, (![y, x] a).1 = x.1` using `(Fin.sum_univ_two _).trans h`. Take `⟨a⟩` from `GlobalTheory.ProdReorder.ind₂_line_left h y.rep κ x.rep x.2.rep.smooth`. Take `⟨b⟩` from `ind₂_equiv_pair y x h hd`. Conclude with `⟨y, rfl, hd, (a.symm.trans b).toIntertwiningMap, (a.symm.trans b).toLinearEquiv.injective⟩`.
-/
private theorem emb_unit (x : IrrGL k) : ∃ y : IrrGL k, y.1 = 0 ∧ Emb x y x := by
  let o : IrrRep (GL (Fin 0) k) := IrrRep.det (k := k) (Fin 0) 1 isSmoothChar_one
  let y : IrrGL k := IrrGL.of o.ρ o.smooth o.irr
  have φ : o.ρ.Equiv y.rep := IrrGL.equivOf o.ρ o.smooth o.irr
  have κ : y.2.rep.V ≃ₗ[ℂ] ℂ := φ.toLinearEquiv.symm
  have h : 0 + x.1 = x.1 := Nat.zero_add _
  have hd : ∑ a, (![y, x] a).1 = x.1 := (Fin.sum_univ_two _).trans h
  obtain ⟨a⟩ := GlobalTheory.ProdReorder.ind₂_line_left h y.rep κ x.rep x.2.rep.smooth
  obtain ⟨b⟩ := ind₂_equiv_pair y x h hd
  exact ⟨y, rfl, hd, (a.symm.trans b).toIntertwiningMap, (a.symm.trans b).toLinearEquiv.injective⟩

/- English proof (translation)
Take `⟨hd, -⟩` from `h`. Conclude with `(Fin.sum_univ_two _).symm.trans hd`.
-/
private theorem emb_deg {x y z : IrrGL k} (h : Emb x y z) : y.1 + z.1 = x.1 := by
  obtain ⟨hd, -⟩ := h
  exact (Fin.sum_univ_two _).symm.trans hd

/- English proof (translation)
Take `⟨hd, hne⟩` from `h`. Take `⟨A, hA, hAP⟩` from `hy`. Establish `hS` using `GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (y := ![y, ρ]) (hd := hd) (t := ![A, {ρ}]) (fun a => by fin_cases a`. Conclude with `hA`. Conclude with `hasSupport_self hρ) v.2.rep.irr (jhMult_ne_zero_iff.1 hne)`.

Use `⟨_, hS, fun w hw => ?_⟩` and prove the remaining obligations. Rewrite `hw` using `[Fin.sum_univ_two]`. Break down `Multiset.mem_add.1 hw with h | h` into its components or cases. Conclude with `hAP w h`. Establish `: w = ρ` using `Multiset.mem_singleton.1 h`.

Conclude with `this ▸ hP`.
-/
private theorem suppIn_occ {v y ρ : IrrGL k} {P : Set (IrrGL k)} (h : Occ v y ρ) (hy : SuppIn y P)
    (hρ : ρ.IsCusp) (hP : ρ ∈ P) : SuppIn v P := by
  obtain ⟨hd, hne⟩ := h
  obtain ⟨A, hA, hAP⟩ := hy
  have hS := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (y := ![y, ρ]) (hd := hd) (t := ![A, {ρ}])
    (fun a => by
      fin_cases a
      · exact hA
      · exact hasSupport_self hρ) v.2.rep.irr (jhMult_ne_zero_iff.1 hne)
  refine ⟨_, hS, fun w hw => ?_⟩
  rw [Fin.sum_univ_two] at hw
  rcases Multiset.mem_add.1 hw with h | h
  · exact hAP w h
  · have : w = ρ := Multiset.mem_singleton.1 h
    exact this ▸ hP

end

/- English proof (translation)
Introduce `hG hBZ k _ _ _ _ x P`. Establish `key : ∀ (n : ℕ) (y z : IrrGL k), z.1 = n → Emb x y z → SuppIn y P → ∃ y z, Emb x y z ∧ SuppIn y P ∧ FirstIn z Pᶜ`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`.

Introduce `y z hz hE hS`. Distinguish the cases in `hF : FirstIn z Pᶜ`. Conclude with `⟨y, z, hE, hS, hF⟩`. Unfold `FirstIn at hF`. Use `push Not at hF`.

Take `⟨q, hq, hc, hj, hP⟩` from `hF`. Establish `hP' : q 0 ∈ P` using `by simpa using hP`. Take `⟨w, hw⟩` from `UpperTheory.Lit.Full.embL hG hBZ k z q hq hc hj`. Take `⟨v, hv, hvw⟩` from `UpperTheory.Lit.Full.assocL hG hBZ k x y z (q 0) w hE hw`. Establish `h1` using `emb_deg hw`.

Establish `h2` using `hc.1`. Conclude with `ih w.1 (by omega) v w rfl hvw (suppIn_occ hv hS hc hP')`. Take `⟨y, hy, hE⟩` from `emb_unit x`. Take `⟨s, hs⟩` from `GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hBZ hG y`. Use `key _ y x rfl hE ⟨s, hs, ?_⟩` and prove the remaining obligations.

Rewrite using `[GlobalTheory.LocGL.SupportUnique.eq_zero_of_hasSupport hy hs]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.Lit.Full.decompL :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL k) (P : Set (IrrGL k)), ∃ y z, Emb x y z ∧ SuppIn y P ∧ FirstIn z Pᶜ := by
  intro hG hBZ k _ _ _ _ x P
  have key : ∀ (n : ℕ) (y z : IrrGL k), z.1 = n → Emb x y z → SuppIn y P →
      ∃ y z, Emb x y z ∧ SuppIn y P ∧ FirstIn z Pᶜ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro y z hz hE hS
      by_cases hF : FirstIn z Pᶜ
      · exact ⟨y, z, hE, hS, hF⟩
      unfold FirstIn at hF
      push Not at hF
      obtain ⟨q, hq, hc, hj, hP⟩ := hF
      have hP' : q 0 ∈ P := by simpa using hP
      obtain ⟨w, hw⟩ := UpperTheory.Lit.Full.embL hG hBZ k z q hq hc hj
      obtain ⟨v, hv, hvw⟩ := UpperTheory.Lit.Full.assocL hG hBZ k x y z (q 0) w hE hw
      have h1 := emb_deg hw
      have h2 := hc.1
      exact ih w.1 (by omega) v w rfl hvw (suppIn_occ hv hS hc hP')
  obtain ⟨y, hy, hE⟩ := emb_unit x
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hBZ hG y
  refine key _ y x rfl hE ⟨s, hs, ?_⟩
  rw [GlobalTheory.LocGL.SupportUnique.eq_zero_of_hasSupport hy hs]
  simp

import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FirstIn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.ExistsNeOfNeBot
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FAssocR
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivProdChosenIrrGLPairDegreeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

/- English proof (translation)
Introduce `hG hBZ k _ _ _ _ x P`. Establish `key : ∀ (n : ℕ) (y z : IrrGL k), y.1 = n → Emb x y z → SuppIn z P → ∃ y z, Emb x y z ∧ LastIn y Pᶜ ∧ SuppIn z P`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`.

Introduce and unpack `y z rfl hxyz hz`. Distinguish the cases in `hl : LastIn y Pᶜ`. Conclude with `⟨y, z, hxyz, hl, hz⟩`. Choose the witnesses or unpack the hypotheses as in `⟨q, hq, hc, hj, hP⟩ : ∃ (q : Fin 2 → IrrGL k) (hq : ∑ a, (q a).1 = y.1), (q 1).IsCusp ∧ jm q hq y.rep ≠ 0 ∧ q 1 ∈ P := by`. Assume the negation of the conclusion as `hn`.

Conclude with `hl fun q hq hc hj hP => hn ⟨q, hq, hc, hj, hP⟩`. Take `⟨u, hu⟩` from `UpperTheory.Lit.Full.embR hG hBZ k y q hq hc hj`. Take `⟨v, ⟨hd, hv⟩, hxuv⟩` from `UpperTheory.Lit.Full.assocR hG hBZ k x y z u (q 1) hxyz hu`. Take `⟨A, hA, hAP⟩` from `hz`. Establish `hlt : u.1 < y.1`.

Take `⟨hd', -⟩` from `hu`. Establish `h1 : u.1 + (q 1).1 = y.1` using `by simpa using hd'`. Use `hc.1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `ih u.1 hlt u v rfl hxuv ⟨∑ a, (![{q 1}, A] : Fin 2 → Multiset (IrrGL k)) a, ?_, ?_⟩` and prove the remaining obligations.

Use `GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (y := ![q 1, z]) ?_ v.2.rep.irr (jhMult_ne_zero_iff.1 hv)` and prove the remaining obligations. Conclude with `Fin.forall_fin_two.2 ⟨hasSupport_self hc, hA⟩`. Introduce `w hw`. Establish `hw' : w ∈ ({q 1} : Multiset (IrrGL k)) + A` using `by simpa using hw`. Break down `Multiset.mem_add.1 hw' with h | h` into its components or cases.

Rewrite using `[Multiset.mem_singleton.1 h]`. Conclude with `hP`. Conclude with `hAP w h`. Set `o : IrrGL k` to `⟨0, (IrrRep.det (Fin 0) (1 : kˣ →* ℂˣ) isSmoothChar_one).cl⟩`. Establish `hd : ∑ a, (![x, o] a).1 = x.1` using `by simp [o]`.

Take `⟨φ⟩` from `nonempty_equiv_prodIrr_pair_zero k x o rfl hd`. Take `⟨s, hs⟩` from `GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hBZ hG o`. Use `key x.1 x o rfl ⟨hd, φ.toIntertwiningMap, φ.toLinearEquiv.injective⟩ ⟨s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.LocGL.SupportUnique.eq_zero_of_hasSupport (N := o.1) rfl hs]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.Lit.Full.decompR :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL k) (P : Set (IrrGL k)), ∃ y z, Emb x y z ∧ LastIn y Pᶜ ∧ SuppIn z P := by
  intro hG hBZ k _ _ _ _ x P
  have key : ∀ (n : ℕ) (y z : IrrGL k), y.1 = n → Emb x y z → SuppIn z P →
      ∃ y z, Emb x y z ∧ LastIn y Pᶜ ∧ SuppIn z P := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rintro y z rfl hxyz hz
      by_cases hl : LastIn y Pᶜ
      · exact ⟨y, z, hxyz, hl, hz⟩
      obtain ⟨q, hq, hc, hj, hP⟩ : ∃ (q : Fin 2 → IrrGL k) (hq : ∑ a, (q a).1 = y.1),
          (q 1).IsCusp ∧ jm q hq y.rep ≠ 0 ∧ q 1 ∈ P := by
        by_contra hn
        exact hl fun q hq hc hj hP => hn ⟨q, hq, hc, hj, hP⟩
      obtain ⟨u, hu⟩ := UpperTheory.Lit.Full.embR hG hBZ k y q hq hc hj
      obtain ⟨v, ⟨hd, hv⟩, hxuv⟩ := UpperTheory.Lit.Full.assocR hG hBZ k x y z u (q 1) hxyz hu
      obtain ⟨A, hA, hAP⟩ := hz
      have hlt : u.1 < y.1 := by
        obtain ⟨hd', -⟩ := hu
        have h1 : u.1 + (q 1).1 = y.1 := by simpa using hd'
        have := hc.1
        omega
      refine ih u.1 hlt u v rfl hxuv ⟨∑ a, (![{q 1}, A] : Fin 2 → Multiset (IrrGL k)) a, ?_, ?_⟩
      · refine GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (y := ![q 1, z]) ?_ v.2.rep.irr
          (jhMult_ne_zero_iff.1 hv)
        exact Fin.forall_fin_two.2 ⟨hasSupport_self hc, hA⟩
      · intro w hw
        have hw' : w ∈ ({q 1} : Multiset (IrrGL k)) + A := by simpa using hw
        rcases Multiset.mem_add.1 hw' with h | h
        · rw [Multiset.mem_singleton.1 h]; exact hP
        · exact hAP w h
  let o : IrrGL k := ⟨0, (IrrRep.det (Fin 0) (1 : kˣ →* ℂˣ) isSmoothChar_one).cl⟩
  have hd : ∑ a, (![x, o] a).1 = x.1 := by simp [o]
  obtain ⟨φ⟩ := nonempty_equiv_prodIrr_pair_zero k x o rfl hd
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hBZ hG o
  refine key x.1 x o rfl ⟨hd, φ.toIntertwiningMap, φ.toLinearEquiv.injective⟩ ⟨s, hs, ?_⟩
  rw [GlobalTheory.LocGL.SupportUnique.eq_zero_of_hasSupport (N := o.1) rfl hs]
  simp

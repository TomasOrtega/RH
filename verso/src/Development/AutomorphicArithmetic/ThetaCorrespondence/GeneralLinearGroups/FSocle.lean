import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FirstIn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

/- English proof (translation)
Take `⟨hGT, hLT⟩` from `(hasFiniteLength_iff_wellFounded _).1 hfl`. Use `haveI : IsAtomic (Subrepresentation π) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt`. Establish `hnt : (⊤ : Subrepresentation π) ≠ ⊥` using `fun hb => by`. Take `⟨u, hu⟩` from `exists_ne (0 : V)`. Establish `h1 : u ∈ (⊥ : Subrepresentation π)` using `hb ▸ trivial`.

Conclude with `hu h1`. Take `⟨S, hS, -⟩` from `(eq_bot_or_exists_atom_le (⊤ : Subrepresentation π)).resolve_left hnt`. Conclude with `⟨S, hS⟩`.
-/
private theorem exists_isAtom {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (π : Representation ℂ G V) (hfl : HasFiniteLength π) : ∃ S : Subrepresentation π, IsAtom S := by
  obtain ⟨hGT, hLT⟩ := (hasFiniteLength_iff_wellFounded _).1 hfl
  haveI : IsAtomic (Subrepresentation π) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
  have hnt : (⊤ : Subrepresentation π) ≠ ⊥ := fun hb => by
    obtain ⟨u, hu⟩ := exists_ne (0 : V)
    have h1 : u ∈ (⊥ : Subrepresentation π) := hb ▸ trivial
    exact hu h1
  obtain ⟨S, hS, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation π)).resolve_left hnt
  exact ⟨S, hS⟩

/- English proof (translation)
Introduce `hBZ k _ _ _ _ y z`. Establish `hA : GlobalTheory.Published.IrreducibleAdmissibleGL` using `fun k _ _ _ _ n V _ _ π => (hBZ k).1 (Fin n) V π`. Establish `hρ : (piTensor fun a => (![y, z] a).rep).IsIrreducible` using `GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA ![y, z]`. Establish `hsρ : IsSmooth (piTensor fun a => (![y, z] a).rep)` using `isSmooth_piTensor fun a => (![y, z] a).2.rep.smooth`. Use `⟨?_, fun N hd hjm x x' hx hx' => ?_⟩` and prove the remaining obligations.

Establish `hd : ∑ a, (![y, z] a).1 = ∑ a, (![y, z] a).1` using `rfl haveI := GlobalTheory.CompanionTheory.SocleJm.nontrivial_indSp (stdBlocks (fun a => (![y, z] a).1) hd) hρ hsρ`. Take `⟨S, hS⟩` from `exists_isAtom (prodIrr ![y, z] hd) ((hBZ k).2.2.1 _ _ _ _ _ _ hsρ (hasFiniteLength_of_isIrreducible hρ))`. Set `ι : S.toRepresentation.IntertwiningMap (prodIrr ![y, z] hd)` to `⟨S.toSubmodule.subtype, fun _ => rfl⟩`. Establish `hSs : IsSmooth S.toRepresentation` using `(IsSubquotient.of_injective ι Subtype.val_injective).isSmooth (isSmooth_prodIrr _ hd)`. Establish `hSi` using `GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom S hS`.

Set `φ` to `(IrrGL.equivOf S.toRepresentation hSs hSi).symm`. Conclude with `⟨IrrGL.of S.toRepresentation hSs hSi, hd, ι.comp φ.toIntertwiningMap, Subtype.val_injective.comp φ.toLinearEquiv.injective⟩`. Take `⟨n, c⟩` from `x`. Take `⟨n', c'⟩` from `x'`. Take `⟨h1, f, hf⟩` from `hx`.

Take `⟨h2, f', hf'⟩` from `hx'`. Take `rfl : N = n` from `hd.symm.trans h1`. Take `rfl : N = n'` from `hd.symm.trans h2`. Take `⟨τ, hτ⟩` from `GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one hA ![y, z] hd hjm`. Take `⟨φ⟩` from `hτ.equiv_of_embeds c.rep.irr ⟨f, hf⟩`.

Take `⟨φ'⟩` from `hτ.equiv_of_embeds c'.rep.irr ⟨f', hf'⟩`. Rewrite using `[← IrrGL.of_rep ⟨N, c⟩, ← IrrGL.of_rep ⟨N, c'⟩]`. Conclude with `IrrGL.of_eq_of.2 ⟨φ.trans φ'.symm⟩`.
-/
theorem UpperTheory.Lit.Full.socle :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (y z : IrrGL k), (∃ x, Emb x y z) ∧ ∀ (N : ℕ) (hd : ∑ a, (![y, z] a).1 = N), jm ![y, z] hd (prodIrr ![y, z] hd) ≤ 1 → ∀ x x', Emb x y z → Emb x' y z → x = x' := by
  intro hBZ k _ _ _ _ y z
  have hA : GlobalTheory.Published.IrreducibleAdmissibleGL := fun k _ _ _ _ n V _ _ π => (hBZ k).1 (Fin n) V π
  have hρ : (piTensor fun a => (![y, z] a).rep).IsIrreducible :=
    GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA ![y, z]
  have hsρ : IsSmooth (piTensor fun a => (![y, z] a).rep) := isSmooth_piTensor fun a => (![y, z] a).2.rep.smooth
  refine ⟨?_, fun N hd hjm x x' hx hx' => ?_⟩
  · have hd : ∑ a, (![y, z] a).1 = ∑ a, (![y, z] a).1 := rfl
    haveI := GlobalTheory.CompanionTheory.SocleJm.nontrivial_indSp (stdBlocks (fun a => (![y, z] a).1) hd) hρ hsρ
    obtain ⟨S, hS⟩ := exists_isAtom (prodIrr ![y, z] hd)
      ((hBZ k).2.2.1 _ _ _ _ _ _ hsρ (hasFiniteLength_of_isIrreducible hρ))
    let ι : S.toRepresentation.IntertwiningMap (prodIrr ![y, z] hd) := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
    have hSs : IsSmooth S.toRepresentation :=
      (IsSubquotient.of_injective ι Subtype.val_injective).isSmooth (isSmooth_prodIrr _ hd)
    have hSi := GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom S hS
    let φ := (IrrGL.equivOf S.toRepresentation hSs hSi).symm
    exact ⟨IrrGL.of S.toRepresentation hSs hSi, hd, ι.comp φ.toIntertwiningMap,
      Subtype.val_injective.comp φ.toLinearEquiv.injective⟩
  · obtain ⟨n, c⟩ := x
    obtain ⟨n', c'⟩ := x'
    obtain ⟨h1, f, hf⟩ := hx
    obtain ⟨h2, f', hf'⟩ := hx'
    obtain rfl : N = n := hd.symm.trans h1
    obtain rfl : N = n' := hd.symm.trans h2
    obtain ⟨τ, hτ⟩ := GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one hA ![y, z] hd hjm
    obtain ⟨φ⟩ := hτ.equiv_of_embeds c.rep.irr ⟨f, hf⟩
    obtain ⟨φ'⟩ := hτ.equiv_of_embeds c'.rep.irr ⟨f', hf'⟩
    rw [← IrrGL.of_rep ⟨N, c⟩, ← IrrGL.of_rep ⟨N, c'⟩]
    exact IrrGL.of_eq_of.2 ⟨φ.trans φ'.symm⟩

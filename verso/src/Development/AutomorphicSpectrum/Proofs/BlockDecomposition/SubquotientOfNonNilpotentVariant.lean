import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfEig
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HkMemFixed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientOfNonNilpotent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.HeckeSub

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Take `⟨hGT, hLT⟩` from `(hasFiniteLength_iff_wellFounded ρ).1 hfl`. Proceed by induction on `S using WellFoundedLT.induction with`. Consider the case `ind S ih`. Distinguish the cases in `hS : S = ⊥`. Substitute `hS` using the available equality.

Conclude with `⟨0, fun u hu _ => hu⟩`. Take `⟨T, hT, hmax⟩` from `(wellFounded_gt (α := Subrepresentation ρ)).has_min {T | T < S} ⟨⊥, bot_lt_iff_ne_bot.2 hS⟩`. Establish `hcov : T ⋖ S` using `⟨hT, fun c h1 h2 => hmax c h2 h1⟩`. Set `p : S.toRepresentation.IntertwiningMap (subQuot S T)` to `⟨Submodule.mkQ _, fun _ => rfl⟩`. Establish `hsq : IsSubquotient (subQuot S T) ρ` using `⟨S, p, Submodule.mkQ_surjective _⟩`.

Establish `hne : IsEmpty ((subQuot S T).Equiv π)` using `⟨fun φ => hns ((IsSubquotient.trans (IsSubquotient.of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective) hsq))⟩`. Take `⟨r, hr⟩` from `ih T hT`. Use `⟨r + 1, fun u huS hufix => ?_⟩` and prove the remaining obligations. Establish `hfixS : (Submodule.mkQ _ (⟨u, huS⟩ : S.toSubmodule) : S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) ∈ fixed (subQuot S T) K`. Introduce `h`.

Establish `h1 : ρ (h : GL ι F) u = u` using `by simpa using hufix h`. Establish `h2 : S.toRepresentation (h : GL ι F) ⟨u, huS⟩ = ⟨u, huS⟩` using `Subtype.ext h1`. Simplify using `only [MonoidHom.one_apply, Units.val_one, one_smul]`. Conclude with `congrArg (Submodule.mkQ _) h2`. Establish `h0` using `hkill _ (subQuot S T) (hsq.isSmooth hρ) (isIrreducible_subQuot hcov) hsq hne _ hfixS`.

Establish `h1 : (hk S.toRepresentation K e ⟨u, huS⟩ : S.toSubmodule).1 = hk ρ K e u` using `hk_map S.toRepresentation ρ S.toSubmodule.subtype (fun _ _ => rfl) hE ⟨u, huS⟩`. Establish `h2` using `hk_map S.toRepresentation (subQuot S T) (Submodule.mkQ _) (fun _ _ => rfl) hE ⟨u, huS⟩`. Rewrite `h2` using `[h0]`. Establish `h3 : hk ρ K e u ∈ T.toSubmodule`. Rewrite using `[← h1]`.

Conclude with `(Submodule.Quotient.mk_eq_zero (T.toSubmodule.comap S.toSubmodule.subtype)).1 h2`. Rewrite using `[Function.iterate_succ_apply]`. Conclude with `hr _ h3 (GlobalTheory.CompanionTheory.HeckeFix.hk_mem_fixed F ι K e hE U ρ u hufix).1`.
-/
theorem exists_iterate_eq_zero_of_subquot {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (hE : IsHk K e) (π : Representation ℂ (GL ι F) V)
    (ρ : Representation ℂ (GL ι F) U) (hρ : IsSmooth ρ) (hfl : HasFiniteLength ρ)
    (hkill : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL ι F) W), IsSmooth τ →
      τ.IsIrreducible → IsSubquotient τ ρ → IsEmpty (τ.Equiv π) → ∀ w ∈ fixed τ K, hk τ K e w = 0)
    (hns : ¬ IsSubquotient π ρ) (S : Subrepresentation ρ) :
    ∃ r : ℕ, ∀ u ∈ S.toSubmodule, u ∈ fixed ρ K → (hk ρ K e)^[r] u = 0 := by
  obtain ⟨hGT, hLT⟩ := (hasFiniteLength_iff_wellFounded ρ).1 hfl
  induction S using WellFoundedLT.induction with
  | ind S ih =>
    by_cases hS : S = ⊥
    · subst hS
      exact ⟨0, fun u hu _ => hu⟩
    obtain ⟨T, hT, hmax⟩ := (wellFounded_gt (α := Subrepresentation ρ)).has_min {T | T < S}
      ⟨⊥, bot_lt_iff_ne_bot.2 hS⟩
    have hcov : T ⋖ S := ⟨hT, fun c h1 h2 => hmax c h2 h1⟩
    let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    have hsq : IsSubquotient (subQuot S T) ρ := ⟨S, p, Submodule.mkQ_surjective _⟩
    have hne : IsEmpty ((subQuot S T).Equiv π) := ⟨fun φ => hns
      ((IsSubquotient.trans (IsSubquotient.of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective) hsq))⟩
    obtain ⟨r, hr⟩ := ih T hT
    refine ⟨r + 1, fun u huS hufix => ?_⟩
    have hfixS : (Submodule.mkQ _ (⟨u, huS⟩ : S.toSubmodule) :
        S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) ∈ fixed (subQuot S T) K := by
      intro h
      have h1 : ρ (h : GL ι F) u = u := by simpa using hufix h
      have h2 : S.toRepresentation (h : GL ι F) ⟨u, huS⟩ = ⟨u, huS⟩ := Subtype.ext h1
      simp only [MonoidHom.one_apply, Units.val_one, one_smul]
      exact congrArg (Submodule.mkQ _) h2
    have h0 := hkill _ (subQuot S T) (hsq.isSmooth hρ) (isIrreducible_subQuot hcov) hsq hne _ hfixS
    have h1 : (hk S.toRepresentation K e ⟨u, huS⟩ : S.toSubmodule).1 = hk ρ K e u :=
      hk_map S.toRepresentation ρ S.toSubmodule.subtype (fun _ _ => rfl) hE ⟨u, huS⟩
    have h2 := hk_map S.toRepresentation (subQuot S T) (Submodule.mkQ _) (fun _ _ => rfl) hE ⟨u, huS⟩
    rw [h0] at h2
    have h3 : hk ρ K e u ∈ T.toSubmodule := by
      rw [← h1]
      exact (Submodule.Quotient.mk_eq_zero (T.toSubmodule.comap S.toSubmodule.subtype)).1 h2
    rw [Function.iterate_succ_apply]
    exact hr _ h3 (GlobalTheory.CompanionTheory.HeckeFix.hk_mem_fixed F ι K e hE U ρ u hufix).1

/- English proof (translation)
Introduce `F _ _ _ _ ι _ _ K e hE V _ _ π _ _ U _ _ ρ hρ hfl hkill hnil`. Assume the negation of the conclusion as `hns`. Take `⟨r, hr⟩` from `exists_iterate_eq_zero_of_subquot hE π ρ hρ hfl hkill hns ⊤`. Take `⟨u, hu, hne⟩` from `hnil r`. Conclude with `hne (hr u trivial hu)`.
-/
theorem subOfNonNil_of_subquot : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], SubOfNonNil' F ι := by
  intro F _ _ _ _ ι _ _ K e hE V _ _ π _ _ U _ _ ρ hρ hfl hkill hnil
  by_contra hns
  obtain ⟨r, hr⟩ := exists_iterate_eq_zero_of_subquot hE π ρ hρ hfl hkill hns ⊤
  obtain ⟨u, hu, hne⟩ := hnil r
  exact hne (hr u trivial hu)

end GlobalTheory.CompanionTheory.HeckeSub

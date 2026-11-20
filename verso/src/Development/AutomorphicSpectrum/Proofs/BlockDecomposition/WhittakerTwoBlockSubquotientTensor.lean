import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitImgMono
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientEquivOfIrreducibleImageStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientOfExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSubquotientEquivStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair

namespace GlobalTheory.CompanionTheory.BZNuPair

/- English proof (translation)
Set `f : (whitImg ψ d J ⊤).toRepresentation.IntertwiningMap (whit2 ψ d J)` to `⟨(whitImg ψ d J ⊤).toSubmodule.subtype, fun _ => rfl⟩`. Use `.of_surjective f fun w => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ w`. Conclude with `⟨⟨Submodule.Quotient.mk x, x, trivial, rfl⟩, rfl⟩`.
-/
theorem whit2_isSubquotient_whitImg_top {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {X : Type} [AddCommGroup X]
    [Module ℂ X] (J : Representation ℂ (Levi k fun a => Fin (d a)) X) :
    IsSubquotient (whit2 ψ d J) (whitImg ψ d J ⊤).toRepresentation := by
  let f : (whitImg ψ d J ⊤).toRepresentation.IntertwiningMap (whit2 ψ d J) :=
    ⟨(whitImg ψ d J ⊤).toSubmodule.subtype, fun _ => rfl⟩
  refine .of_surjective f fun w => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  exact ⟨⟨Submodule.Quotient.mk x, x, trivial, rfl⟩, rfl⟩

/- English proof (translation)
Introduce and unpack `⟨R, f, hf⟩`. Use `nontrivial_of_irreducible hσ` as an intermediate fact. Take `⟨w, hw⟩` from `exists_ne (0 : W)`. Take `⟨v, rfl⟩` from `hf w`. Establish `hv : v = 0`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Take `⟨t, ht, h⟩` from `v.1.2`. Establish `ht0 : t = 0` using `ht`. Rewrite using `[← h, ht0]`.

Simplify using the standard rewrite rules. Conclude with `hw (by rw [hv, map_zero])`.
-/
theorem not_isSubquotient_whitImg_bot {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {X W : Type} [AddCommGroup X]
    [Module ℂ X] [AddCommGroup W] [Module ℂ W] (J : Representation ℂ (Levi k fun a => Fin (d a)) X)
    {σ : Representation ℂ (GL (Fin (d 0)) k) W} (hσ : σ.IsIrreducible) :
    ¬ IsSubquotient σ (whitImg ψ d J ⊥).toRepresentation := by
  rintro ⟨R, f, hf⟩
  have := nontrivial_of_irreducible hσ
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hf w
  have hv : v = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨t, ht, h⟩ := v.1.2
    have ht0 : t = 0 := ht
    rw [← h, ht0]
    simp
  exact hw (by rw [hv, map_zero])

/- English proof (translation)
Introduce `k _ _ _ _ ψ _ d X _ _ J hs hfl S hS`. Take `⟨hgt, hlt⟩` from `(hasFiniteLength_iff_wellFounded J).1 hfl`. Take `⟨T, hT, hmin⟩` from `WellFounded.has_min hlt.wf {T : Subrepresentation J | IsSubquotient S.ρ (whitImg ψ d J T).toRepresentation} ⟨⊤, hS.trans (whit2_isSubquotient_whitImg_top ψ d J)⟩`. Establish `hne : T ≠ ⊥`. Introduce and unpack `rfl`.

Conclude with `not_isSubquotient_whitImg_bot ψ d J S.irr hT`. Take `⟨T', hT'lt, hmax⟩` from `WellFounded.has_min hgt.wf {U : Subrepresentation J | U < T} ⟨⊥, bot_lt_iff_ne_bot.2 hne⟩`. Establish `hcov : T' ⋖ T` using `⟨hT'lt, fun c h1 h2 => hmax c h2 h1⟩`. Establish `hq : IsSubquotient (subQuot T T') J` using `⟨T, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.mkQ_surjective _⟩`. Set `τ : IrrRep (Levi k fun a => Fin (d a))` to `⟨_, subQuot T T', hq.isSmooth hs, isIrreducible_subQuot hcov⟩`.

Take `⟨s, ⟨Φ⟩⟩` from `GlobalTheory.LeviFactor.exists_equiv_piTensor_levi GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k (Fin 2) (fun a => Fin (d a)) τ`. Establish `hspan` using `GlobalTheory.T.whittaker_subquotient_equiv k ψ d X J T T' (fun a => (s a).V) (fun a => (s a).ρ) hT'lt.le Φ`. Use `⟨s, (IsSubquotient.of_surjective Φ.toIntertwiningMap Φ.surjective).trans hq, ?_⟩` and prove the remaining obligations. Break down `GlobalTheory.T.irreducible_subquotient_of_extension _ _ _ (whit2 ψ d J) S.ρ _ _ (whitImg_mono ψ d J hT'lt.le) S.irr hT with h | h` into its components or cases. Conclude with `absurd hT'lt (hmin T' h)`.

Take `⟨e⟩` from `GlobalTheory.T.subquotient_equiv_of_irreducible_image _ _ _ _ (s 0).ρ _ S.ρ (s 0).irr S.irr hspan h`. Conclude with `⟨e.symm⟩`.
-/
theorem exists_constituent_of_whit2 : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (d : Fin 2 → ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    (J : Representation ℂ (Levi k fun a => Fin (d a)) X), IsSmooth J → HasFiniteLength J → ∀ S : IrrRep (GL (Fin (d 0)) k),
    IsSubquotient S.ρ (whit2 ψ d J) → ∃ s : ∀ a, IrrRep (GL (Fin (d a)) k),
      IsSubquotient (piTensor fun a => (s a).ρ) J ∧ Nonempty ((s 0).ρ.Equiv S.ρ) := by
  intro k _ _ _ _ ψ _ d X _ _ J hs hfl S hS
  obtain ⟨hgt, hlt⟩ := (hasFiniteLength_iff_wellFounded J).1 hfl
  obtain ⟨T, hT, hmin⟩ := WellFounded.has_min hlt.wf
    {T : Subrepresentation J | IsSubquotient S.ρ (whitImg ψ d J T).toRepresentation}
    ⟨⊤, hS.trans (whit2_isSubquotient_whitImg_top ψ d J)⟩
  have hne : T ≠ ⊥ := by
    rintro rfl
    exact not_isSubquotient_whitImg_bot ψ d J S.irr hT
  obtain ⟨T', hT'lt, hmax⟩ := WellFounded.has_min hgt.wf {U : Subrepresentation J | U < T}
    ⟨⊥, bot_lt_iff_ne_bot.2 hne⟩
  have hcov : T' ⋖ T := ⟨hT'lt, fun c h1 h2 => hmax c h2 h1⟩
  have hq : IsSubquotient (subQuot T T') J :=
    ⟨T, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.mkQ_surjective _⟩
  let τ : IrrRep (Levi k fun a => Fin (d a)) :=
    ⟨_, subQuot T T', hq.isSmooth hs, isIrreducible_subQuot hcov⟩
  obtain ⟨s, ⟨Φ⟩⟩ := GlobalTheory.LeviFactor.exists_equiv_piTensor_levi GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k (Fin 2)
    (fun a => Fin (d a)) τ
  have hspan := GlobalTheory.T.whittaker_subquotient_equiv k ψ d X J T T' (fun a => (s a).V) (fun a => (s a).ρ) hT'lt.le Φ
  refine ⟨s, (IsSubquotient.of_surjective Φ.toIntertwiningMap Φ.surjective).trans hq, ?_⟩
  rcases GlobalTheory.T.irreducible_subquotient_of_extension _ _ _ (whit2 ψ d J) S.ρ _ _ (whitImg_mono ψ d J hT'lt.le) S.irr hT with h | h
  · exact absurd hT'lt (hmin T' h)
  · obtain ⟨e⟩ := GlobalTheory.T.subquotient_equiv_of_irreducible_image _ _ _ _ (s 0).ρ _ S.ρ (s 0).irr S.irr hspan h
    exact ⟨e.symm⟩

end GlobalTheory.CompanionTheory.BZNuPair

end

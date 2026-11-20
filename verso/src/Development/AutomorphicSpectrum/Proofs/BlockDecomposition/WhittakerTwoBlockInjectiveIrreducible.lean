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

namespace GlobalTheory.CompanionTheory.BZNuPair.WhitSub

/- English proof (translation)
Substitute `hB` using the available equality. Establish `hle : (⊥ : Subrepresentation ρ).toSubmodule.comap A.toSubmodule.subtype ≤ LinearMap.ker A.toSubmodule.subtype` using `fun v hv => by`. Establish `: (v : V) ∈ (⊥ : Subrepresentation ρ).toSubmodule` using `hv`. Conclude with `this`. Set `p : (subQuot A ⊥).IntertwiningMap ρ` to `.mk (Submodule.liftQ _ A.toSubmodule.subtype hle) (fun g => by`.

Use extensionality with `v`. Use the proof step `rfl)`. Establish `hp : Function.Injective p`. Use `(injective_iff_map_eq_zero _).2 fun x hx => ?_` and prove the remaining obligations. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`.

Conclude with `(Submodule.Quotient.mk_eq_zero _).2 hx`. Establish `hi : Function.Injective (p.comp f)`. Use `(injective_iff_map_eq_zero _).2 fun x hx => ?_` and prove the remaining obligations. Break down `eq_bot_or_eq_top (p.comp f).ker with h | h` into its components or cases. Establish `: x ∈ (p.comp f).ker` using `hx`.

Rewrite `this` using `[h]`. Conclude with `this`. It suffices to derive a contradiction. Use `hf (LinearMap.ext fun y => ?_)` and prove the remaining obligations. Establish `hy : y ∈ (p.comp f).ker` using `by rw [h]; trivial`.

Conclude with `hp (by simpa using hy)`. Conclude with `⟨p.comp f, hi⟩`.
-/
theorem exists_injective_of_subQuot_bot {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} (hσ : σ.IsIrreducible) {ρ : Representation ℂ G V}
    (A B : Subrepresentation ρ) (hB : B = ⊥) (f : σ.IntertwiningMap (subQuot A B))
    (hf : f.toLinearMap ≠ 0) : ∃ g : σ.IntertwiningMap ρ, Function.Injective g := by
  subst hB
  have hle : (⊥ : Subrepresentation ρ).toSubmodule.comap A.toSubmodule.subtype ≤
      LinearMap.ker A.toSubmodule.subtype := fun v hv => by
    have : (v : V) ∈ (⊥ : Subrepresentation ρ).toSubmodule := hv
    exact this
  let p : (subQuot A ⊥).IntertwiningMap ρ :=
    .mk (Submodule.liftQ _ A.toSubmodule.subtype hle) (fun g => by
      ext v
      rfl)
  have hp : Function.Injective p := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact (Submodule.Quotient.mk_eq_zero _).2 hx
  have hi : Function.Injective (p.comp f) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    rcases eq_bot_or_eq_top (p.comp f).ker with h | h
    · have : x ∈ (p.comp f).ker := hx
      rw [h] at this
      exact this
    · exfalso
      refine hf (LinearMap.ext fun y => ?_)
      have hy : y ∈ (p.comp f).ker := by rw [h]; trivial
      exact hp (by simpa using hy)
  exact ⟨p.comp f, hi⟩

/- English proof (translation)
Introduce `k _ _ _ _ ψ _ d X _ _ J hs hfl hnt`. Take `⟨hgt, hlt⟩` from `(hasFiniteLength_iff_wellFounded J).1 hfl`. Establish `hbotImg : whitImg ψ d J ⊥ = ⊥`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Conclude with `Submodule.map_bot _`.

Establish `htop : whitImg ψ d J ⊤ ≠ ⊥`. Introduce `h`. Establish `h1 : (whitImg ψ d J ⊤).toSubmodule = ⊤` using `by show (⊤ : Subrepresentation J).toSubmodule.map (whitKer ψ d J).mkQ = ⊤`. Conclude with `(Submodule.map_top _).trans (Submodule.range_mkQ _)`. Rewrite `h1` using `[h]`.

Take `⟨x, hx⟩` from `exists_ne (0 : X ⧸ whitKer ψ d J)`. Establish `: x ∈ (⊥ : Subrepresentation (whit2 ψ d J)).toSubmodule` using `by rw [h1]; trivial`. Conclude with `hx this`. Take `⟨T, hT, hmin⟩` from `(wellFounded_lt (α := Subrepresentation J)).has_min {T | whitImg ψ d J T ≠ ⊥} ⟨⊤, htop⟩`. Establish `hbot : (⊥ : Subrepresentation J) < T`.

Use `bot_lt_iff_ne_bot.2 fun h => hT ?_` and prove the remaining obligations. Rewrite using `[h]`. Conclude with `hbotImg`. Take `⟨T', hT', hmax⟩` from `(wellFounded_gt (α := Subrepresentation J)).has_min {B | B < T} ⟨⊥, hbot⟩`. Establish `hcov : T' ⋖ T` using `⟨hT', fun C hBC hCA => hmax C hCA hBC⟩`.

Establish `hImg' : whitImg ψ d J T' = ⊥`. Assume the negation of the conclusion as `h`. Conclude with `hmin T' h hT'`. Set `τ : IrrRep (Levi k fun a => Fin (d a))` to `⟨_, subQuot T T', IsSubquotient.isSmooth ⟨T, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.mkQ_surjective _⟩ hs, isIrreducible_subQuot hcov⟩`. Take `⟨s, ⟨Φ⟩⟩` from `GlobalTheory.LeviFactor.exists_equiv_piTensor_levi GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k (Fin 2) (fun a => Fin (d a)) τ`.

Establish `hspan` using `GlobalTheory.T.whittaker_subquotient_equiv k ψ d X J T T' (fun a => (s a).V) (fun a => (s a).ρ) hT'.le Φ`. Establish `hQ : Nontrivial ((whitImg ψ d J T).toSubmodule ⧸ (whitImg ψ d J T').toSubmodule.comap (whitImg ψ d J T).toSubmodule.subtype)`. Use `Submodule.Quotient.nontrivial_iff.2 fun h => hT ?_` and prove the remaining obligations. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Use `le_antisymm (fun x hx => ?_) bot_le` and prove the remaining obligations.

Establish `hx' : (⟨x, hx⟩ : (whitImg ψ d J T).toSubmodule) ∈ (whitImg ψ d J T').toSubmodule.comap (whitImg ψ d J T).toSubmodule.subtype`. Rewrite using `[h]`. Discharge the goal by the elementary cases of `trivial`. Rewrite `hx'` using `[Submodule.mem_comap, hImg']`. Conclude with `hx'`.

Choose the witnesses or unpack the hypotheses as in `⟨f, hf⟩ : ∃ f : (s 0).ρ.IntertwiningMap (subQuot (whitImg ψ d J T) (whitImg ψ d J T')), f.toLinearMap ≠ 0 := by`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Establish `: (⨆ f : (s 0).ρ.IntertwiningMap (subQuot (whitImg ψ d J T) (whitImg ψ d J T')), LinearMap.range f.toLinearMap) = ⊥`. Use `le_antisymm (iSup_le fun f => ?_) bot_le` and prove the remaining obligations.

Rewrite using `[hno f, LinearMap.range_zero]`. Rewrite `hspan` using `[this]`. Conclude with `bot_ne_top hspan`. Take `⟨g, hg⟩` from `exists_injective_of_subQuot_bot (s 0).irr _ _ hImg' f hf`. Conclude with `⟨s 0, g, hg⟩`.
-/
theorem exists_irr_sub : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (d : Fin 2 → ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    (J : Representation ℂ (Levi k fun a => Fin (d a)) X), IsSmooth J → HasFiniteLength J → Nontrivial (X ⧸ whitKer ψ d J) →
    ∃ (S : IrrRep (GL (Fin (d 0)) k)) (f : S.ρ.IntertwiningMap (whit2 ψ d J)), Function.Injective f := by
  intro k _ _ _ _ ψ _ d X _ _ J hs hfl hnt
  obtain ⟨hgt, hlt⟩ := (hasFiniteLength_iff_wellFounded J).1 hfl
  have hbotImg : whitImg ψ d J ⊥ = ⊥ := by
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.map_bot _
  have htop : whitImg ψ d J ⊤ ≠ ⊥ := by
    intro h
    have h1 : (whitImg ψ d J ⊤).toSubmodule = ⊤ := by
      show (⊤ : Subrepresentation J).toSubmodule.map (whitKer ψ d J).mkQ = ⊤
      exact (Submodule.map_top _).trans (Submodule.range_mkQ _)
    rw [h] at h1
    obtain ⟨x, hx⟩ := exists_ne (0 : X ⧸ whitKer ψ d J)
    have : x ∈ (⊥ : Subrepresentation (whit2 ψ d J)).toSubmodule := by rw [h1]; trivial
    exact hx this
  obtain ⟨T, hT, hmin⟩ := (wellFounded_lt (α := Subrepresentation J)).has_min
    {T | whitImg ψ d J T ≠ ⊥} ⟨⊤, htop⟩
  have hbot : (⊥ : Subrepresentation J) < T := by
    refine bot_lt_iff_ne_bot.2 fun h => hT ?_
    rw [h]
    exact hbotImg
  obtain ⟨T', hT', hmax⟩ := (wellFounded_gt (α := Subrepresentation J)).has_min
    {B | B < T} ⟨⊥, hbot⟩
  have hcov : T' ⋖ T := ⟨hT', fun C hBC hCA => hmax C hCA hBC⟩
  have hImg' : whitImg ψ d J T' = ⊥ := by
    by_contra h
    exact hmin T' h hT'
  let τ : IrrRep (Levi k fun a => Fin (d a)) :=
    ⟨_, subQuot T T', IsSubquotient.isSmooth ⟨T, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.mkQ_surjective _⟩ hs, isIrreducible_subQuot hcov⟩
  obtain ⟨s, ⟨Φ⟩⟩ := GlobalTheory.LeviFactor.exists_equiv_piTensor_levi GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
    k (Fin 2) (fun a => Fin (d a)) τ
  have hspan := GlobalTheory.T.whittaker_subquotient_equiv k ψ d X J T T' (fun a => (s a).V) (fun a => (s a).ρ) hT'.le Φ
  have hQ : Nontrivial ((whitImg ψ d J T).toSubmodule ⧸
      (whitImg ψ d J T').toSubmodule.comap (whitImg ψ d J T).toSubmodule.subtype) := by
    refine Submodule.Quotient.nontrivial_iff.2 fun h => hT ?_
    apply Subrepresentation.toSubmodule_injective
    refine le_antisymm (fun x hx => ?_) bot_le
    have hx' : (⟨x, hx⟩ : (whitImg ψ d J T).toSubmodule) ∈
        (whitImg ψ d J T').toSubmodule.comap (whitImg ψ d J T).toSubmodule.subtype := by
      rw [h]; trivial
    rw [Submodule.mem_comap, hImg'] at hx'
    exact hx'
  obtain ⟨f, hf⟩ : ∃ f : (s 0).ρ.IntertwiningMap (subQuot (whitImg ψ d J T) (whitImg ψ d J T')),
      f.toLinearMap ≠ 0 := by
    by_contra hno
    push_neg at hno
    have : (⨆ f : (s 0).ρ.IntertwiningMap (subQuot (whitImg ψ d J T) (whitImg ψ d J T')),
        LinearMap.range f.toLinearMap) = ⊥ := by
      refine le_antisymm (iSup_le fun f => ?_) bot_le
      rw [hno f, LinearMap.range_zero]
    rw [this] at hspan
    exact bot_ne_top hspan
  obtain ⟨g, hg⟩ := exists_injective_of_subQuot_bot (s 0).irr _ _ hImg' f hf
  exact ⟨s 0, g, hg⟩

end GlobalTheory.CompanionTheory.BZNuPair.WhitSub

end

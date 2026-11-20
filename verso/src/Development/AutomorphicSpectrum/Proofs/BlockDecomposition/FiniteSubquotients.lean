import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfEig
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2 GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.RepFinSubq

variable {F G V W : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

/- English proof (translation)
Take `⟨s, h0, h1⟩` from `isFiniteLength_iff_exists_compositionSeries.1 h`. Set `e` to `(Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).symm`. Use `⟨s.length, fun i => e (s i), ?_, ?_, ?_, fun t => ?_⟩` and prove the remaining obligations. Conclude with `e.monotone.comp s.strictMono.monotone`. Use `show e s.head = ⊥`.

Rewrite using `[h0, map_bot]`. Use `show e s.last = ⊤`. Rewrite using `[h1, map_top]`. Conclude with `(apply_covBy_apply_iff e).2 (s.step t)`.
-/
theorem exists_series {ρ : Representation F G V} (h : HasFiniteLength ρ) :
    ∃ (N : ℕ) (S : Fin (N + 1) → Subrepresentation ρ), Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last N) = ⊤ ∧
      ∀ t : Fin N, S t.castSucc ⋖ S t.succ := by
  obtain ⟨s, h0, h1⟩ := isFiniteLength_iff_exists_compositionSeries.1 h
  let e := (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).symm
  refine ⟨s.length, fun i => e (s i), ?_, ?_, ?_, fun t => ?_⟩
  · exact e.monotone.comp s.strictMono.monotone
  · show e s.head = ⊥
    rw [h0, map_bot]
  · show e s.last = ⊤
    rw [h1, map_top]
  · exact (apply_covBy_apply_iff e).2 (s.step t)

/- English proof (translation)
Assemble the required witnesses or components as `⟨S, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.mkQ_surjective _⟩`.
-/
theorem isSubquotient_subQuot {ρ : Representation F G V} (S T : Subrepresentation ρ) :
    IsSubquotient (subQuot S T) ρ :=
  ⟨S, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.mkQ_surjective _⟩

/- English proof (translation)
Establish `hne : jhMult τ ρ ≠ 0` using `jhMult_ne_zero_iff.2 hq`. Rewrite `hne` using `[jhMult_filtration hτ S hS h0 h1]`. Take `⟨t, -, ht⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hne`. Take `⟨e⟩` from `(jhMult_ne_zero_iff.1 ht).nonempty_equiv hτ (isIrreducible_subQuot (hc t))`. Conclude with `⟨t, ⟨e.symm⟩⟩`.
-/
theorem exists_factor_equiv {ρ : Representation F G V} {N : ℕ} {S : Fin (N + 1) → Subrepresentation ρ}
    (hS : Monotone S) (h0 : S 0 = ⊥) (h1 : S (Fin.last N) = ⊤) (hc : ∀ t : Fin N, S t.castSucc ⋖ S t.succ)
    {τ : Representation F G W} (hτ : τ.IsIrreducible) (hq : IsSubquotient τ ρ) :
    ∃ t : Fin N, Nonempty (τ.Equiv (subQuot (S t.succ) (S t.castSucc))) := by
  have hne : jhMult τ ρ ≠ 0 := jhMult_ne_zero_iff.2 hq
  rw [jhMult_filtration hτ S hS h0 h1] at hne
  obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨e⟩ := (jhMult_ne_zero_iff.1 ht).nonempty_equiv hτ (isIrreducible_subQuot (hc t))
  exact ⟨t, ⟨e.symm⟩⟩

/- English proof (translation)
Introduce `F _ _ _ _ ι _ _ U _ _ ρ hρ hfl`. Take `⟨N, S, hS, h0, h1, hc⟩` from `exists_series hfl`. Use `⟨Fin N, inferInstance, fun t => _, fun _ => inferInstance, fun _ => inferInstance, fun t => subQuot (S t.succ) (S t.castSucc), fun t => ?_, fun W' _ _ τ' hτ hq => ?_⟩` and prove the remaining obligations. Conclude with `⟨(isSubquotient_subQuot _ _).isSmooth hρ, isIrreducible_subQuot (hc t), isSubquotient_subQuot _ _⟩`. Conclude with `exists_factor_equiv hS h0 h1 hc hτ hq`.
-/
theorem finSubq : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (ι : Type) [Fintype ι] [DecidableEq ι], FinSubq F ι := by
  intro F _ _ _ _ ι _ _ U _ _ ρ hρ hfl
  obtain ⟨N, S, hS, h0, h1, hc⟩ := exists_series hfl
  refine ⟨Fin N, inferInstance, fun t => _, fun _ => inferInstance, fun _ => inferInstance,
    fun t => subQuot (S t.succ) (S t.castSucc), fun t => ?_, fun W' _ _ τ' hτ hq => ?_⟩
  · exact ⟨(isSubquotient_subQuot _ _).isSmooth hρ, isIrreducible_subQuot (hc t), isSubquotient_subQuot _ _⟩
  · exact exists_factor_equiv hS h0 h1 hc hτ hq

end GlobalTheory.CompanionTheory.RepFinSubq

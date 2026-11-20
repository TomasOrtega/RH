import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatIndLastKerRow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineModelKappaTransformIsLocalModel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHomLatticeCompletionOpenCompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSchwartzBruhatExtByZeroOfSplitPlaceHalfStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMulConjugateHalfCharacterSplitPlacStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ModelExtend

/- English proof (translation)
Use `⟨Submodule.fg_span_singleton ζ, ?_⟩` and prove the remaining obligations. Establish `h0 : ζ ≠ 0` using `fun h0 => h.2 (by simp [h0])`. Rewrite using `[Submodule.span_span_of_tower]`. Establish `hr : Module.finrank D.host.E (Fin L.rank → D.host.E) = 1` using `by simp [h.1]`. Conclude with `(finrank_eq_one_iff_of_nonzero ζ h0).1 hr`.
-/
theorem isLattice_span {D : D7} {L : HSp D} {ζ : Fin L.rank → D.host.E} (h : IsLineVec L ζ) :
    Submodule.IsLattice D.host.E (Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) := by
  refine ⟨Submodule.fg_span_singleton ζ, ?_⟩
  have h0 : ζ ≠ 0 := fun h0 => h.2 (by simp [h0])
  rw [Submodule.span_span_of_tower]
  have hr : Module.finrank D.host.E (Fin L.rank → D.host.E) = 1 := by simp [h.1]
  exact (finrank_eq_one_iff_of_nonzero ζ h0).1 hr

open GlobalTheory.LocMod in

/- English proof (translation)
Introduce `D k _ _ _ _ p ψ hψ hU S L'' ζ₀ hζ LS hLS n _ _ FS FL'' TL hTL`. Use `set P := GlobalTheory.LocMod.Place.ofSplitPt p with hP`. Use `set Λ := latO S L'' (LS : Set _) ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀} : Lat L'') : Set _) (· = p.v) with hΛ`. Take `⟨hAo, hAc⟩` from `GlobalTheory.T.splitPlace_homLattice_completion_openCompact D k p S L'' LS (Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀}) hLS.1 (isLattice_span hζ) Unit n FS FL''`. Establish `hinj : Function.Injective (Witness.ext P FS FL'')`.

Introduce `Φ Ψ h`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Use `congrFun h (P.up FS FL'' x)` as an intermediate fact. Rewrite `this` using `[Witness.ext_apply, Witness.ext_apply, if_pos (Witness.up_half P FS FL'' x), if_pos (Witness.up_half P FS FL'' x), Witness.down_up]`. Then use the resulting hypothesis.

Take `⟨G, hG⟩` from `LinearMap.exists_leftInverse_of_injective (Witness.ext P FS FL'') (LinearMap.ker_eq_bot.2 hinj)`. Use `set T₃ : (WO S L'' → ℂ) →ₗ[ℂ] (WO S L'' → ℂ) := TL ∘ₗ G with hT₃d`. Establish `hT₃ : ∀ Φ, T₃ (Witness.ext P FS FL'' Φ) = TL Φ` using `fun Φ => by`. Express the relevant statement in the definitionally equal form `TL (G (Witness.ext P FS FL'' Φ)) = TL Φ`. Rewrite using `[← LinearMap.comp_apply G, hG, LinearMap.id_apply]`.

Establish `hsb : ∀ Φ, IsSBHalf p.e Λ Φ → ∃ Φ' : SB (Matrix Unit n k), Witness.ext P FS FL'' Φ' = Φ` using `GlobalTheory.T.exists_schwartzBruhat_extByZero_of_splitPlaceHalf D k P S L'' Unit n FS FL'' Λ hAo hAc`. Generalize the expression as in `hA : (Λ.comap (Witness.upH P FS FL'') : AddSubgroup (Matrix Unit n k)) = A at hAo hAc`. Establish `hcl : IsClopen (A : Set (Matrix Unit n k))` using `⟨A.isClosed_of_isOpen hAo, hAo⟩`. Set `Φ₀ : SB (Matrix Unit n k)` to `⟨(A : Set (Matrix Unit n k)).indicator 1, (LocallyConstant.charFn ℂ hcl).isLocallyConstant, HasCompactSupport.intro hAc fun x hx => Set.indicator_of_notMem hx _⟩`. Establish `e1 : Witness.ext P FS FL'' Φ₀ = halfInd p.e Λ`.

Use function extensionality and compare the values at `t`. Rewrite using `[Witness.ext_apply, halfInd]`. Express the relevant statement in the definitionally equal form `(if IsHalf p.e t then _ else _) = _`. Distinguish the cases in `ht : IsHalf p.e t`. Rewrite using `[if_pos ht]`.

Express the relevant statement in the definitionally equal form `(A : Set (Matrix Unit n k)).indicator 1 _ = _`. Rewrite using `[Set.indicator_apply, ← hA]`. Use `if_congr ?_ rfl rfl` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `P.up FS FL'' (P.down FS FL'' t) ∈ Λ ↔ _`. Rewrite using `[Witness.up_down P FS FL'' ht, and_iff_left ht]`.

Rewrite using `[if_neg ht, if_neg fun h => ht h.2]`. Use `⟨TL Φ₀, T₃, hTL.theta Φ₀, ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩, hT₃⟩` and prove the remaining obligations. Take `⟨Φ', rfl⟩` from `hsb Φ hΦ`. Set `Φ'' : SB (Matrix Unit n k)` to `⟨fun s => Φ'.1 (s + P.down FS FL'' x), Φ'.2.1.comp_continuous (continuous_add_right _), Φ'.2.2.comp_homeomorph (Homeomorph.addRight _)⟩`. Establish `e2 : (fun t => Witness.ext P FS FL'' Φ' (t + x)) = Witness.ext P FS FL'' Φ''`.

Use function extensionality and compare the values at `t`. Rewrite using `[Witness.ext_apply, Witness.ext_apply, Witness.down_add]`. Conclude with `if_congr (Witness.half_add hx) rfl rfl`. Rewrite using `[e2, hT₃, hT₃, hTL.trans (P.down FS FL'' x) Φ' Φ'' (fun t => rfl), Witness.up_down P FS FL'' hx]`. Take `⟨Φ', rfl⟩` from `hsb Φ hΦ`.

Set `Φ'' : SB (Matrix Unit n k)` to `⟨fun s => ψ (symplO S L'' (P.up FS FL'' s) y) * Φ'.1 s, GlobalTheory.T.schwartzBruhat_mul_conjugateHalf_character_splitPlace D k P ψ hψ S L'' Unit n FS FL'' y hy Φ'.1 Φ'.2⟩`. Establish `e2 : (fun t => ψ (symplO S L'' t y) * Witness.ext P FS FL'' Φ' t) = Witness.ext P FS FL'' Φ''`. Use function extensionality and compare the values at `t`. Rewrite using `[Witness.ext_apply, Witness.ext_apply]`. Use `split_ifs with ht`.

Express the relevant statement in the definitionally equal form `_ = ψ (symplO S L'' (P.up FS FL'' (P.down FS FL'' t)) y) * _`. Rewrite using `[Witness.up_down P FS FL'' ht]`. Rewrite using `[mul_zero]`. Rewrite using `[e2, hT₃, hT₃, hTL.modul y hy Φ' Φ'' (fun t => rfl)]`. Rewrite using `[one_smul, ← e1, hT₃]`.
-/
theorem exists_placeModel_ext : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S L'' : HSp D) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L'' ζ₀ → ∀ (LS : Lat S), IsSelfDualC S LS → ∀ (n : Type) [Fintype n] [DecidableEq n] (FS : GlobalTheory.LocMod.Frame k S.rank n) (FL'' : GlobalTheory.LocMod.Frame k L''.rank Unit) (TL : SB (Matrix Unit n k) →ₗ[ℂ] (WO S L'' → ℂ)), (GlobalTheory.LocMod.Place.ofSplitPt p).IsModel ψ FS FL'' TL → ∃ (g₃ : WO S L'' → ℂ) (T₃ : (WO S L'' → ℂ) →ₗ[ℂ] (WO S L'' → ℂ)), IsThetaFunO ψ S L'' g₃ ∧ IsPlaceModel ψ (symplO S L'') (heisO ψ S L'') p.e (latO S L'' (LS : Set _) ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀} : Lat L'') : Set _) (· = p.v)) 1 g₃ T₃ ∧ ∀ Φ, T₃ (GlobalTheory.LocMod.Witness.ext (GlobalTheory.LocMod.Place.ofSplitPt p) FS FL'' Φ) = TL Φ := by
  intro D k _ _ _ _ p ψ hψ hU S L'' ζ₀ hζ LS hLS n _ _ FS FL'' TL hTL
  classical
  set P := GlobalTheory.LocMod.Place.ofSplitPt p with hP
  set Λ := latO S L'' (LS : Set _) ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀} : Lat L'') : Set _) (· = p.v) with hΛ
  obtain ⟨hAo, hAc⟩ := GlobalTheory.T.splitPlace_homLattice_completion_openCompact D k p S L'' LS (Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀}) hLS.1
    (isLattice_span hζ) Unit n FS FL''
  have hinj : Function.Injective (Witness.ext P FS FL'') := by
    intro Φ Ψ h
    apply Subtype.ext; funext x
    have := congrFun h (P.up FS FL'' x)
    rwa [Witness.ext_apply, Witness.ext_apply, if_pos (Witness.up_half P FS FL'' x),
      if_pos (Witness.up_half P FS FL'' x), Witness.down_up] at this
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective (Witness.ext P FS FL'') (LinearMap.ker_eq_bot.2 hinj)
  set T₃ : (WO S L'' → ℂ) →ₗ[ℂ] (WO S L'' → ℂ) := TL ∘ₗ G with hT₃d
  have hT₃ : ∀ Φ, T₃ (Witness.ext P FS FL'' Φ) = TL Φ := fun Φ => by
    change TL (G (Witness.ext P FS FL'' Φ)) = TL Φ
    rw [← LinearMap.comp_apply G, hG, LinearMap.id_apply]
  have hsb : ∀ Φ, IsSBHalf p.e Λ Φ → ∃ Φ' : SB (Matrix Unit n k), Witness.ext P FS FL'' Φ' = Φ :=
    GlobalTheory.T.exists_schwartzBruhat_extByZero_of_splitPlaceHalf D k P S L'' Unit n FS FL'' Λ hAo hAc
  generalize hA : (Λ.comap (Witness.upH P FS FL'') : AddSubgroup (Matrix Unit n k)) = A at hAo hAc
  have hcl : IsClopen (A : Set (Matrix Unit n k)) := ⟨A.isClosed_of_isOpen hAo, hAo⟩
  let Φ₀ : SB (Matrix Unit n k) := ⟨(A : Set (Matrix Unit n k)).indicator 1,
    (LocallyConstant.charFn ℂ hcl).isLocallyConstant,
    HasCompactSupport.intro hAc fun x hx => Set.indicator_of_notMem hx _⟩
  have e1 : Witness.ext P FS FL'' Φ₀ = halfInd p.e Λ := by
    funext t
    rw [Witness.ext_apply, halfInd]
    change (if IsHalf p.e t then _ else _) = _
    by_cases ht : IsHalf p.e t
    · rw [if_pos ht]
      change (A : Set (Matrix Unit n k)).indicator 1 _ = _
      rw [Set.indicator_apply, ← hA]
      refine if_congr ?_ rfl rfl
      change P.up FS FL'' (P.down FS FL'' t) ∈ Λ ↔ _
      rw [Witness.up_down P FS FL'' ht, and_iff_left ht]
    · rw [if_neg ht, if_neg fun h => ht h.2]
  refine ⟨TL Φ₀, T₃, hTL.theta Φ₀, ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩, hT₃⟩
  · obtain ⟨Φ', rfl⟩ := hsb Φ hΦ
    let Φ'' : SB (Matrix Unit n k) := ⟨fun s => Φ'.1 (s + P.down FS FL'' x),
      Φ'.2.1.comp_continuous (continuous_add_right _), Φ'.2.2.comp_homeomorph (Homeomorph.addRight _)⟩
    have e2 : (fun t => Witness.ext P FS FL'' Φ' (t + x)) = Witness.ext P FS FL'' Φ'' := by
      funext t
      rw [Witness.ext_apply, Witness.ext_apply, Witness.down_add]
      exact if_congr (Witness.half_add hx) rfl rfl
    rw [e2, hT₃, hT₃, hTL.trans (P.down FS FL'' x) Φ' Φ'' (fun t => rfl), Witness.up_down P FS FL'' hx]
  · obtain ⟨Φ', rfl⟩ := hsb Φ hΦ
    let Φ'' : SB (Matrix Unit n k) := ⟨fun s => ψ (symplO S L'' (P.up FS FL'' s) y) * Φ'.1 s,
      GlobalTheory.T.schwartzBruhat_mul_conjugateHalf_character_splitPlace D k P ψ hψ S L'' Unit n FS FL'' y hy Φ'.1 Φ'.2⟩
    have e2 : (fun t => ψ (symplO S L'' t y) * Witness.ext P FS FL'' Φ' t) = Witness.ext P FS FL'' Φ'' := by
      funext t
      rw [Witness.ext_apply, Witness.ext_apply]
      split_ifs with ht
      · change _ = ψ (symplO S L'' (P.up FS FL'' (P.down FS FL'' t)) y) * _
        rw [Witness.up_down P FS FL'' ht]
      · rw [mul_zero]
    rw [e2, hT₃, hT₃, hTL.modul y hy Φ' Φ'' (fun t => rfl)]
  · rw [one_smul, ← e1, hT₃]

end GlobalTheory.ModelExtend

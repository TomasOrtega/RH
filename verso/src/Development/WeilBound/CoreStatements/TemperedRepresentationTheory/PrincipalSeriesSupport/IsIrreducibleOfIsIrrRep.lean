import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationUnitsMapEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtTensorTwistApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLtOneIffTendsto
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.ExtTensorTwistApply
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace Ysupp.IrreducibleSupport

open GlobalTheory GlobalTheory.SerSys

section Chain

open GlobalTheory.LocGL

/- English proof (translation)
Take `⟨hn, hW⟩` from `h`. Take `⟨v, hv⟩` from `exists_ne (0 : V)`. Use `{ exists_pair_ne := ⟨⊥, ⊤, fun e => hv ?_⟩, eq_bot_or_eq_top := fun S => ?_ }` and prove the remaining obligations. Establish `h1 : v ∈ (⊤ : Subrepresentation ρ).toSubmodule` using `Submodule.mem_top`. Rewrite `h1` using `[← e]`.

Conclude with `(Submodule.mem_bot ℂ).1 h1`. Break down `hW S.toSubmodule (fun x w hw => S.apply_mem_toSubmodule x hw) with h0 | h1` into its components or cases. Conclude with `Or.inl (Subrepresentation.ext (by rw [h0]; rfl))`. Conclude with `Or.inr (Subrepresentation.ext (by rw [h1]; rfl))`.
-/
theorem isIrreducible_of_isIrrRep {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (h : IsIrrRep ρ) : ρ.IsIrreducible := by
  obtain ⟨hn, hW⟩ := h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine { exists_pair_ne := ⟨⊥, ⊤, fun e => hv ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · have h1 : v ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← e] at h1
    exact (Submodule.mem_bot ℂ).1 h1
  · rcases hW S.toSubmodule (fun x w hw => S.apply_mem_toSubmodule x hw) with h0 | h1
    · exact Or.inl (Subrepresentation.ext (by rw [h0]; rfl))
    · exact Or.inr (Subrepresentation.ext (by rw [h1]; rfl))

/- English proof (translation)
Use `haveI := h`. Use `⟨?_, fun W hW => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`. Establish `: (⊥ : Subrepresentation ρ) = ⊤` using `Subrepresentation.ext (Subsingleton.elim (α := Submodule ℂ V) _ _)`.

Conclude with `bot_ne_top this`. Break down `eq_bot_or_eq_top (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation ρ) with h0 | h1` into its components or cases. Conclude with `Or.inl (congrArg Subrepresentation.toSubmodule h0)`. Conclude with `Or.inr (congrArg Subrepresentation.toSubmodule h1)`.
-/
theorem isIrrRep_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) : IsIrrRep ρ := by
  haveI := h
  refine ⟨?_, fun W hW => ?_⟩
  · by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have : (⊥ : Subrepresentation ρ) = ⊤ := Subrepresentation.ext (Subsingleton.elim (α := Submodule ℂ V) _ _)
    exact bot_ne_top this
  · rcases eq_bot_or_eq_top (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation ρ) with h0 | h1
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h0)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)

/- English proof (translation)
Take `⟨s, hs'⟩` from `Ysupp.exists_hasSupport hS (IrrGL.of π hs hi)`. Establish `h1 : HasSupport π s` using `hs'.of_equiv (IrrGL.equivOf π hs hi).symm`. Establish `h2` using `h1.sum_fst`. Rewrite `h2` using `[Fintype.card_fin]`. Establish `h3 : s = 0`.

Assume the negation of the conclusion as `hne`. Take `⟨y, hy⟩` from `Multiset.exists_mem_of_ne_zero hne`. Establish `h4` using `(h1.isCusp hy).1`. Establish `h5 : y.1 ≤ (s.map Sigma.fst).sum` using `Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hy)`. Use linear arithmetic over natural numbers and integers.

Rewrite `h1` using `[h3]`. Then use the resulting hypothesis.
-/
theorem hasSupport_zero (hS : Ysupp.SubEmbedding) {g : ℕ} [Fact g.Prime] {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin 0) ℚ_[g]) V) (hs : GlobalTheory.PRep.IsSmooth π)
    (hi : π.IsIrreducible) : HasSupport π (0 : Multiset (IrrGL ℚ_[g])) := by
  obtain ⟨s, hs'⟩ := Ysupp.exists_hasSupport hS (IrrGL.of π hs hi)
  have h1 : HasSupport π s := hs'.of_equiv (IrrGL.equivOf π hs hi).symm
  have h2 := h1.sum_fst
  rw [Fintype.card_fin] at h2
  have h3 : s = 0 := by
    by_contra hne
    obtain ⟨y, hy⟩ := Multiset.exists_mem_of_ne_zero hne
    have h4 := (h1.isCusp hy).1
    have h5 : y.1 ≤ (s.map Sigma.fst).sum := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hy)
    omega
  rwa [h3] at h1

/- English proof (translation)
Introduce `hS hP g _`. Establish `H : ∀ (N : ℕ) (π : Supp.GLRep g), π.1 = N → IsIrrRep π.2.ρ → GlobalTheory.PRep.IsSmooth π.2.ρ → ∃ (L : List (Supp.GLRep g)) (y : List (IrrGL ℚ_[g])), Supp.InInd π L ∧ (∀ ρ ∈ L, 0 < ρ.1 ∧ IsIrrRep ρ.2.ρ ∧ GlobalTheory.PRep.IsSmooth ρ.2.ρ ∧ ρ.2.ρ.IsIrreducible ∧ GlobalTheory.SmGL.I …`. Introduce `N`. Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ N ih`.

Introduce `π hN hπ hs`. Break down `Nat.eq_zero_or_pos N with h0 | hpos` into its components or cases. Substitute `h0` using the available equality. Use `⟨[], [], Supp.InInd.nil π hN hπ, by simp, ?_, List.Forall₂.nil⟩` and prove the remaining obligations. Take `⟨n, π⟩` from `π`.

Simplify using `only at hN`. Substitute `hN` using the available equality. Conclude with `hasSupport_zero hS _ hs (isIrreducible_of_isIrrRep hπ)`. Take `⟨a, b, hab, W, W', _, _, _, _, σ, ρ, hb, hσs, hσi, hρs, hρi, hρc, φ, hφ⟩` from `GlobalTheory.JacFactor.exists_map_jac₂ ℚ_[g] π.1 _ π.2.ρ hs (isIrreducible_of_isIrrRep hπ) (hN ▸ hpos)`. Establish `hM : Supp.MapsToProd π.2.ρ σ ρ` using `GlobalTheory.GLp.Supp.mapsToProd_of_jac₂ g a b π.1 hab _ _ _ π.2.ρ σ ρ φ hφ`.

Set `σ' : Supp.GLRep g` to `⟨a, Rep.of σ⟩`. Set `ρ' : Supp.GLRep g` to `⟨b, Rep.of ρ⟩`. Take `⟨Lσ, yσ, hI, hL, hS, hF⟩` from `ih a (by omega) σ' rfl (isIrrRep_of_isIrreducible hσi) hσs`. Establish `hρsupp : HasSupport ρ {IrrGL.of ρ hρs hρi}` using `(hasSupport_self (IrrGL.isCusp_of.2 ⟨hb, hρc⟩)).of_equiv (IrrGL.equivOf ρ hρs hρi).symm`. Take `⟨μ₁, μ₂, h₁, h₂, hsupp⟩` from `Ysupp.UnramifiedTwistSupport.supp_of_mapsToProd hP g _ _ _ _ _ _ π.2.ρ σ ρ hs (isIrreducible_of_isIrrRep hπ) hM yσ {IrrGL.of ρ hρs hρi} hS hρsupp`.

Use `⟨ρ' :: Lσ, (IrrGL.of ρ hρs hρi).tw μ₂ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h₂) :: yσ.map (fun x => x.tw μ₁ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h₁)), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Supp.InInd.cons π σ' ρ' Lσ hπ (isIrrRep_of_isIrreducible hρi) hI hM`. Conclude with `List.forall_mem_cons.2 ⟨⟨hb, isIrrRep_of_isIrreducible hρi, hρs, hρi, hρc⟩, hL⟩`. Use `hsupp using 1` and compare the differences between its conclusion and the goal. Rewrite using `[← Multiset.cons_coe, ← Multiset.map_coe, Multiset.map_singleton, add_comm, Multiset.singleton_add]`.

Use `List.Forall₂.cons ⟨hρs, hρi, μ₂, h₂, rfl⟩ ?_` and prove the remaining obligations. Use `List.forall₂_map_right_iff.2 (hF.imp fun ρ x ⟨hs, hi, hin⟩ => ⟨hs, hi, ?_⟩)` and prove the remaining obligations. Conclude with `IrrGL.inert_equivalence.trans hin ⟨μ₁, h₁, rfl⟩`. Introduce `π hπ hs`. Conclude with `H _ π rfl hπ hs`.
-/
theorem chain : Ysupp.SubEmbedding → Ysupp.ProdSupport → ∀ (g : ℕ) [Fact g.Prime] (π : Supp.GLRep g), IsIrrRep π.2.ρ → GlobalTheory.PRep.IsSmooth π.2.ρ → ∃ (L : List (Supp.GLRep g)) (y : List (GlobalTheory.LocGL.IrrGL ℚ_[g])), Supp.InInd π L ∧ (∀ ρ ∈ L, 0 < ρ.1 ∧ IsIrrRep ρ.2.ρ ∧ GlobalTheory.PRep.IsSmooth ρ.2.ρ ∧ ρ.2.ρ.IsIrreducible ∧ GlobalTheory.SmGL.IsCuspidal ρ.2.ρ) ∧ GlobalTheory.LocGL.HasSupport π.2.ρ (y : Multiset (GlobalTheory.LocGL.IrrGL ℚ_[g])) ∧ List.Forall₂ (fun (ρ : Supp.GLRep g) (x : GlobalTheory.LocGL.IrrGL ℚ_[g]) => ∃ (hs : GlobalTheory.PRep.IsSmooth ρ.2.ρ) (hi : ρ.2.ρ.IsIrreducible), (GlobalTheory.LocGL.IrrGL.of ρ.2.ρ hs hi).Inert x) L y := by
  intro hS hP g _
  have H : ∀ (N : ℕ) (π : Supp.GLRep g), π.1 = N → IsIrrRep π.2.ρ → GlobalTheory.PRep.IsSmooth π.2.ρ →
      ∃ (L : List (Supp.GLRep g)) (y : List (IrrGL ℚ_[g])), Supp.InInd π L ∧
        (∀ ρ ∈ L, 0 < ρ.1 ∧ IsIrrRep ρ.2.ρ ∧ GlobalTheory.PRep.IsSmooth ρ.2.ρ ∧ ρ.2.ρ.IsIrreducible ∧
          GlobalTheory.SmGL.IsCuspidal ρ.2.ρ) ∧ HasSupport π.2.ρ (y : Multiset (IrrGL ℚ_[g])) ∧
        List.Forall₂ (fun (ρ : Supp.GLRep g) (x : IrrGL ℚ_[g]) =>
          ∃ (hs : GlobalTheory.PRep.IsSmooth ρ.2.ρ) (hi : ρ.2.ρ.IsIrreducible), (IrrGL.of ρ.2.ρ hs hi).Inert x) L y := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro π hN hπ hs
      rcases Nat.eq_zero_or_pos N with h0 | hpos
      · subst h0
        refine ⟨[], [], Supp.InInd.nil π hN hπ, by simp, ?_, List.Forall₂.nil⟩
        obtain ⟨n, π⟩ := π
        simp only at hN
        subst hN
        exact hasSupport_zero hS _ hs (isIrreducible_of_isIrrRep hπ)
      · obtain ⟨a, b, hab, W, W', _, _, _, _, σ, ρ, hb, hσs, hσi, hρs, hρi, hρc, φ, hφ⟩ :=
          GlobalTheory.JacFactor.exists_map_jac₂ ℚ_[g] π.1 _ π.2.ρ hs (isIrreducible_of_isIrrRep hπ) (hN ▸ hpos)
        have hM : Supp.MapsToProd π.2.ρ σ ρ := GlobalTheory.GLp.Supp.mapsToProd_of_jac₂ g a b π.1 hab _ _ _ π.2.ρ σ ρ φ hφ
        let σ' : Supp.GLRep g := ⟨a, Rep.of σ⟩
        let ρ' : Supp.GLRep g := ⟨b, Rep.of ρ⟩
        obtain ⟨Lσ, yσ, hI, hL, hS, hF⟩ :=
          ih a (by omega) σ' rfl (isIrrRep_of_isIrreducible hσi) hσs
        have hρsupp : HasSupport ρ {IrrGL.of ρ hρs hρi} :=
          (hasSupport_self (IrrGL.isCusp_of.2 ⟨hb, hρc⟩)).of_equiv (IrrGL.equivOf ρ hρs hρi).symm
        obtain ⟨μ₁, μ₂, h₁, h₂, hsupp⟩ := Ysupp.UnramifiedTwistSupport.supp_of_mapsToProd hP g _ _ _ _ _ _ π.2.ρ σ ρ hs (isIrreducible_of_isIrrRep hπ) hM
          yσ {IrrGL.of ρ hρs hρi} hS hρsupp
        refine ⟨ρ' :: Lσ, (IrrGL.of ρ hρs hρi).tw μ₂ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h₂) ::
          yσ.map (fun x => x.tw μ₁ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h₁)), ?_, ?_, ?_, ?_⟩
        · exact Supp.InInd.cons π σ' ρ' Lσ hπ (isIrrRep_of_isIrreducible hρi) hI hM
        · exact List.forall_mem_cons.2 ⟨⟨hb, isIrrRep_of_isIrreducible hρi, hρs, hρi, hρc⟩, hL⟩
        · convert hsupp using 1
          rw [← Multiset.cons_coe, ← Multiset.map_coe, Multiset.map_singleton, add_comm, Multiset.singleton_add]
        · refine List.Forall₂.cons ⟨hρs, hρi, μ₂, h₂, rfl⟩ ?_
          refine List.forall₂_map_right_iff.2 (hF.imp fun ρ x ⟨hs, hi, hin⟩ => ⟨hs, hi, ?_⟩)
          exact IrrGL.inert_equivalence.trans hin ⟨μ₁, h₁, rfl⟩
  intro π hπ hs
  exact H _ π rfl hπ hs

end Chain

end Ysupp.IrreducibleSupport

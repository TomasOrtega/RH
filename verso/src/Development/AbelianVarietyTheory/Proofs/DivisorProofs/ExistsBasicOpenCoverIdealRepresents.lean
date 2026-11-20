import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsKillIdeal
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed

noncomputable section

namespace GlobalTheory.PtClosed

/- English proof (translation)
Set `ρ` to `(S.presheaf.map (homOfLE (S.basicOpen_le a)).op).hom`. Use `letI : Algebra Γ(S, V) Γ(S, S.basicOpen a) := ρ.toAlgebra`. Use `haveI : IsLocalization.Away a Γ(S, S.basicOpen a) := hV.isLocalization_basicOpen a`. Set `e : Localization.Away a ≃ₐ[Γ(S, V)] Γ(S, S.basicOpen a)` to `IsLocalization.algEquiv (Submonoid.powers a) (Localization.Away a) Γ(S, S.basicOpen a)`. Use `⟨J.map (e.symm : Γ(S, S.basicOpen a) →+* Localization.Away a), ?_⟩` and prove the remaining obligations.

Introduce `R' _ h`. Establish `hc : h.comp (algebraMap Γ(S, V) (Localization.Away a)) = (h.comp (e.symm : Γ(S, S.basicOpen a) →+* Localization.Away a)).comp ρ`. Use extensionality with `x`. Simplify using `only [RingHom.comp_apply]`. Use `congr 1`.

Use `e.symm.commutes x` as an intermediate fact. Rewrite using `[← this]`. Both sides reduce to the same expression. Establish `hs : ∀ g : Γ(S, S.basicOpen a) →+* R', spMap (g.comp ρ) ≫ hV.fromSpec = spMap g ≫ (hV.basicOpen a).fromSpec`. Introduce `g`.

Rewrite using `[← hV.map_fromSpec (hV.basicOpen a) (homOfLE (S.basicOpen_le a)).op]`. Simplify using `only [ρ, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom]`. Use `show P R' (spMap _ ≫ hV.fromSpec) ↔ _`. Rewrite using `[hc, hs, Ideal.map_le_iff_le_comap, RingHom.comap_ker]`. Conclude with `hJ R' _`.
-/
theorem represents_away (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop)
    (V : S.Opens) (hV : IsAffineOpen V) (a : Γ(S, V)) (J : Ideal Γ(S, S.basicOpen a))
    (hJ : Represents (ptQ P (S.basicOpen a) (hV.basicOpen a)) J) :
    ∃ J' : Ideal (Localization.Away a),
      Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
        ptQ P V hV R' (h.comp (algebraMap Γ(S, V) (Localization.Away a)))) J' := by
  let ρ := (S.presheaf.map (homOfLE (S.basicOpen_le a)).op).hom
  letI : Algebra Γ(S, V) Γ(S, S.basicOpen a) := ρ.toAlgebra
  haveI : IsLocalization.Away a Γ(S, S.basicOpen a) := hV.isLocalization_basicOpen a
  let e : Localization.Away a ≃ₐ[Γ(S, V)] Γ(S, S.basicOpen a) :=
    IsLocalization.algEquiv (Submonoid.powers a) (Localization.Away a) Γ(S, S.basicOpen a)
  refine ⟨J.map (e.symm : Γ(S, S.basicOpen a) →+* Localization.Away a), ?_⟩
  intro R' _ h
  have hc : h.comp (algebraMap Γ(S, V) (Localization.Away a)) =
      (h.comp (e.symm : Γ(S, S.basicOpen a) →+* Localization.Away a)).comp ρ := by
    ext x
    simp only [RingHom.comp_apply]
    congr 1
    have := e.symm.commutes x
    rw [← this]
    rfl
  have hs : ∀ g : Γ(S, S.basicOpen a) →+* R',
      spMap (g.comp ρ) ≫ hV.fromSpec = spMap g ≫ (hV.basicOpen a).fromSpec := by
    intro g
    rw [← hV.map_fromSpec (hV.basicOpen a) (homOfLE (S.basicOpen_le a)).op]
    simp only [ρ, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom]
  show P R' (spMap _ ≫ hV.fromSpec) ↔ _
  rw [hc, hs, Ideal.map_le_iff_le_comap, RingHom.comap_ker]
  exact hJ R' _

end GlobalTheory.PtClosed

namespace GlobalTheory.PtClosed

/- English proof (translation)
Introduce `S P hcov V hV`. Set `T : Set Γ(S, V)` to `{a | ∃ J : Ideal (Localization.Away a), Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦ ptQ P V hV R' (h.comp (algebraMap Γ(S, V) (Localization.Away a)))) J}`. Establish `hT : Ideal.span T = ⊤`. Rewrite using `[← hV.self_le_iSup_basicOpen_iff]`. Introduce `z hzV`.

Take `⟨U, hU, hzU, K, hK⟩` from `hcov z`. Take `⟨a, b, hab, hz⟩` from `exists_basicOpen_le_affine_inter hV hU z ⟨hzV, hzU⟩`. Establish `hle : S.basicOpen a ≤ U` using `hab ▸ S.basicOpen_le b`. Establish `hJ` using `represents_restrict S P U (S.basicOpen a) hU (hV.basicOpen a) hle K hK`. Establish `haT : a ∈ T` using `represents_away S P V hV a _ hJ`.

Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, haT⟩, hz⟩`. Take `⟨s, hsT, hs⟩` from `(Ideal.span_eq_top_iff_finite T).1 hT`. Conclude with `⟨s, hs, fun a ha ↦ hsT ha⟩`.
-/
theorem affine_local_represents : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ z : S, ∃ (U : S.Opens) (hU : IsAffineOpen U), z ∈ U ∧ ∃ K : Ideal Γ(S, U),
    ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R'), P R' (spMap f ≫ hU.fromSpec) ↔ K ≤ RingHom.ker f) →
  ∀ (V : S.Opens) (hV : IsAffineOpen V), ∃ s : Finset Γ(S, V), Ideal.span (s : Set Γ(S, V)) = ⊤ ∧
    ∀ a ∈ s, ∃ J : Ideal (Localization.Away a),
      Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
        ptQ P V hV R' (h.comp (algebraMap Γ(S, V) (Localization.Away a)))) J := by
  intro S P hcov V hV
  let T : Set Γ(S, V) := {a | ∃ J : Ideal (Localization.Away a),
      Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
        ptQ P V hV R' (h.comp (algebraMap Γ(S, V) (Localization.Away a)))) J}
  have hT : Ideal.span T = ⊤ := by
    rw [← hV.self_le_iSup_basicOpen_iff]
    intro z hzV
    obtain ⟨U, hU, hzU, K, hK⟩ := hcov z
    obtain ⟨a, b, hab, hz⟩ := exists_basicOpen_le_affine_inter hV hU z ⟨hzV, hzU⟩
    have hle : S.basicOpen a ≤ U := hab ▸ S.basicOpen_le b
    have hJ := represents_restrict S P U (S.basicOpen a) hU (hV.basicOpen a) hle K hK
    have haT : a ∈ T := represents_away S P V hV a _ hJ
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, haT⟩, hz⟩
  obtain ⟨s, hsT, hs⟩ := (Ideal.span_eq_top_iff_finite T).1 hT
  exact ⟨s, hs, fun a ha ↦ hsT ha⟩

end GlobalTheory.PtClosed

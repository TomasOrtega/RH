import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwKerWhitCharReflect

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.PRep.WhitSup

/- English proof (translation)
Unfold `GlobalTheory.PRep.twKer at hw ⊢`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨h, u, rfl⟩` from `hz`. Establish `hu : (u : V) ∈ X.toSubmodule ⊔ Y.toSubmodule`.

Rewrite using `[← Subrepresentation.toSubmodule_sup]`. Conclude with `u.2`. Take `⟨x, hx, y, hy, hxy⟩` from `Submodule.mem_sup.1 hu`. Establish `hρu : ((X ⊔ Y).toRepresentation h u : V) = ρ h u` using `rfl`. Establish `hcoe : (((X ⊔ Y).toRepresentation h u - (χ h : ℂ) • u : (X ⊔ Y).toSubmodule) : V) = (ρ h x - (χ h : ℂ) • x) + (ρ h y - (χ h : ℂ) • y)`.

Rewrite using `[Submodule.coe_sub, Submodule.coe_smul, hρu, ← hxy, map_add, smul_add]`. Normalize the expressions using the abelian group laws. Rewrite using `[hcoe]`. Apply `Submodule.add_mem_sup` to reduce the goal to its premises. Conclude with `Submodule.mem_inf.2 ⟨X.toSubmodule.sub_mem (X.apply_mem_toSubmodule h hx) (X.toSubmodule.smul_mem _ hx), Submodule.subset_span ⟨h, x, rfl⟩⟩`.

Conclude with `Submodule.mem_inf.2 ⟨Y.toSubmodule.sub_mem (Y.apply_mem_toSubmodule h hy) (Y.toSubmodule.smul_mem _ hy), Submodule.subset_span ⟨h, y, rfl⟩⟩`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb`. Rewrite using `[Submodule.coe_add]`. Conclude with `Submodule.add_mem _ ha hb`.

Consider the case `smul c a _ ha`. Rewrite using `[Submodule.coe_smul]`. Conclude with `Submodule.smul_mem _ c ha`.
-/
theorem mem_sup_of_mem_twKer_sup {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (X Y : Subrepresentation ρ) (H : Subgroup G) (χ : H →* ℂˣ)
    {w : (X ⊔ Y).toSubmodule} (hw : w ∈ twKer (X ⊔ Y).toRepresentation H χ) :
    (w : V) ∈ X.toSubmodule ⊓ twKer ρ H χ ⊔ Y.toSubmodule ⊓ twKer ρ H χ := by
  unfold GlobalTheory.PRep.twKer at hw ⊢
  induction hw using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨h, u, rfl⟩ := hz
    have hu : (u : V) ∈ X.toSubmodule ⊔ Y.toSubmodule := by
      rw [← Subrepresentation.toSubmodule_sup]
      exact u.2
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hu
    have hρu : ((X ⊔ Y).toRepresentation h u : V) = ρ h u := rfl
    have hcoe : (((X ⊔ Y).toRepresentation h u - (χ h : ℂ) • u : (X ⊔ Y).toSubmodule) : V) =
        (ρ h x - (χ h : ℂ) • x) + (ρ h y - (χ h : ℂ) • y) := by
      rw [Submodule.coe_sub, Submodule.coe_smul, hρu, ← hxy, map_add, smul_add]
      abel
    rw [hcoe]
    apply Submodule.add_mem_sup
    · exact Submodule.mem_inf.2
        ⟨X.toSubmodule.sub_mem (X.apply_mem_toSubmodule h hx) (X.toSubmodule.smul_mem _ hx),
          Submodule.subset_span ⟨h, x, rfl⟩⟩
    · exact Submodule.mem_inf.2
        ⟨Y.toSubmodule.sub_mem (Y.apply_mem_toSubmodule h hy) (Y.toSubmodule.smul_mem _ hy),
          Submodule.subset_span ⟨h, y, rfl⟩⟩
  | zero => simp
  | add a b _ _ ha hb =>
    rw [Submodule.coe_add]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [Submodule.coe_smul]
    exact Submodule.smul_mem _ c ha

/- English proof (translation)
Introduce `k _ _ _ _ ψ hψ N V _ _ ρ hρ X Y w hw`. Take `⟨hw1, hw2⟩` from `Submodule.mem_inf.1 hw`. Establish `hW : GlobalTheory.PRep.IsSmooth (X ⊔ Y).toRepresentation`. Unfold `GlobalTheory.PRep.IsSmooth at hρ ⊢`. Introduce `v`.

Establish `hset : {g | (X ⊔ Y).toRepresentation g v = v} = {g | ρ g v = v}`. Use extensionality with `g`. Conclude with `Subtype.ext_iff`. Rewrite using `[hset]`. Conclude with `hρ v`.

Establish `hw' : (⟨w, hw1⟩ : (X ⊔ Y).toSubmodule) ∈ GlobalTheory.PRep.twKer (X ⊔ Y).toRepresentation (GlobalTheory.SmGL.unipB k (Fin N)) (GlobalTheory.LocGL.whitChar ψ N)` using `GlobalTheory.CompanionTheory.PRep.WhitExact.twKer_whitChar_reflect k ψ hψ N (X ⊔ Y).toRepresentation ρ hW hρ (X ⊔ Y).toSubmodule.subtype Subtype.val_injective (fun _ _ => rfl) _ hw2`. Conclude with `GlobalTheory.CompanionTheory.PRep.WhitSup.mem_sup_of_mem_twKer_sup X Y _ _ hw'`.
-/
theorem sup_inf_twKer_le : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V), IsSmooth ρ → ∀ X Y : Subrepresentation ρ, (X ⊔ Y).toSubmodule ⊓ twKer ρ (unipB k (Fin N)) (whitChar ψ N) ≤ X.toSubmodule ⊓ twKer ρ (unipB k (Fin N)) (whitChar ψ N) ⊔ Y.toSubmodule ⊓ twKer ρ (unipB k (Fin N)) (whitChar ψ N) := by
  intro k _ _ _ _ ψ hψ N V _ _ ρ hρ X Y w hw
  obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.1 hw
  have hW : GlobalTheory.PRep.IsSmooth (X ⊔ Y).toRepresentation := by
    unfold GlobalTheory.PRep.IsSmooth at hρ ⊢
    intro v
    have hset : {g | (X ⊔ Y).toRepresentation g v = v} = {g | ρ g v = v} := by
      ext g
      exact Subtype.ext_iff
    rw [hset]
    exact hρ v
  have hw' : (⟨w, hw1⟩ : (X ⊔ Y).toSubmodule) ∈ GlobalTheory.PRep.twKer
      (X ⊔ Y).toRepresentation (GlobalTheory.SmGL.unipB k (Fin N))
      (GlobalTheory.LocGL.whitChar ψ N) :=
    GlobalTheory.CompanionTheory.PRep.WhitExact.twKer_whitChar_reflect k ψ hψ N (X ⊔ Y).toRepresentation ρ
      hW hρ (X ⊔ Y).toSubmodule.subtype Subtype.val_injective (fun _ _ => rfl) _ hw2
  exact GlobalTheory.CompanionTheory.PRep.WhitSup.mem_sup_of_mem_twKer_sup X Y _ _ hw'

end GlobalTheory.CompanionTheory.PRep.WhitSup

end

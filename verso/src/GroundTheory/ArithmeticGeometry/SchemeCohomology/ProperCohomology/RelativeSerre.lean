import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RelSerreSections
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.AcyclicLeray
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.QcqsPushforward
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowProduct
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

universe u

noncomputable section

attribute [local instance] algebraOfOver

namespace ProjScheme

/- English proof (translation)
Establish `h : i ≫ ProjSpace.toSpecBase A N = ψ ≫ (X ↘ Spec (.of A))`. Rewrite using `[CategoryTheory.comp_over ψ (Spec (.of A))]`. Conclude with `CategoryTheory.comp_over i (Spec (.of A))`. Establish `: X.IsSeparated` using `⟨by`. Rewrite using `[show terminal.from X = (X ↘ Spec (.of A)) ≫ terminal.from _ from terminal.hom_ext _ _]`.

Use the proof step `infer_instance⟩`. Establish `: QuasiCompact (ψ ≫ (X ↘ Spec (.of A)))`. Rewrite using `[← h]`. Use `infer_instance`. Establish `: QuasiCompact ψ` using `QuasiCompact.of_comp ψ (X ↘ Spec (.of A))`.

Establish `: QuasiSeparated (ψ ≫ (X ↘ Spec (.of A)))`. Rewrite using `[← h]`. Use `infer_instance`. Establish `: QuasiSeparated ψ` using `QuasiSeparated.of_comp ψ (X ↘ Spec (.of A))`. Take `⟨t, ht⟩` from `(isCompact_univ (X := X)).elim_finite_subcover (fun U : X.affineOpens => (U : Set X)) (fun U => U.1.isOpen) (by`.

Introduce `x _`. Take `⟨U, hU⟩` from `Opens.mem_iSup.1 (show x ∈ ⨆ U : X.affineOpens, (U : X.Opens) by rw [iSup_affineOpens_eq_top X]; trivial)`. Conclude with `Set.mem_iUnion.2 ⟨U, hU⟩)`. Set `ι` to `{ U // U ∈ t }`. Set `V : ι → X.Opens` to `fun a => a.1.1`.

Establish `hVaff1 : ∀ a, IsAffineOpen (V a)` using `fun a => a.1.2`. Establish `hV : iSup V = ⊤`. Apply `le_antisymm le_top` to reduce the goal to its premises. Introduce `x _`. Take `⟨U, hU⟩` from `Set.mem_iUnion.1 (ht (Set.mem_univ x))`.

Take `⟨hUt, hxU⟩` from `Set.mem_iUnion.1 hU`. Conclude with `Opens.mem_iSup.2 ⟨⟨U, hUt⟩, hxU⟩`. Set `W : Finset ι → X.Opens` to `fun S => ⨅ a : S, V a`. Establish `hWaff : ∀ S : Finset ι, S.Nonempty → IsAffineOpen (W S)` using `fun S hS => by`. Establish `: Nonempty S` using `hS.to_subtype`.

Conclude with `IsAffineOpen.iInf fun a => hVaff1 a`. Establish `hWtuple : ∀ (m : ℕ) (s : Fin (m + 1) → ι), (⨅ a, V (s a)) = W (Finset.univ.image s)` using `fun m s => by`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `le_iInf fun b => by`. Take `⟨a, -, ha⟩` from `Finset.mem_image.1 b.2`.

Conclude with `(iInf_le _ a).trans (le_of_eq (congrArg V ha))`. Conclude with `le_iInf fun a => iInf_le (fun b : (Finset.univ.image s : Finset ι) => V b) ⟨s a, Finset.mem_image_of_mem s (Finset.mem_univ a)⟩`. Establish `hWsingle : ∀ a : ι, W {a} = V a` using `fun a => by`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `iInf_le (fun b : ({a} : Finset ι) => V b) ⟨a, Finset.mem_singleton_self a⟩`.

Conclude with `le_iInf fun b => le_of_eq (congrArg V (Finset.mem_singleton.1 b.2).symm)`. Establish `key : ∀ S : Finset ι, ∃ n₁ : ℕ, S.Nonempty → ∀ n : ℕ, n₁ ≤ n → (∀ q : ℕ, Subsingleton (Sheaf.H.{u} (modulesAb ((ProjScheme.twist i G n).restrict (ψ ⁻¹ᵁ W S).ι)) (q + 1))) ∧ Module.Finite Γ(X, W S) Γ((Scheme.Modules.pushforward ψ).obj (ProjScheme.twist i G n), W S)`. Introduce `S`. Distinguish the cases in `hS : S.Nonempty`. Establish `hA` using `hWaff S hS`.

Establish `: IsNoetherianRing Γ(X, W S)` using `IsLocallyNoetherian.component_noetherian ⟨_, hA⟩`. Take `⟨n₁, hn₁⟩` from `RelSerre.exists_vanishing_finite i ψ h hA G hG`. Conclude with `⟨n₁, fun _ n hn => ⟨(hn₁ n hn).1, RelSerre.finite_sections_pushforward i ψ h hA _ (hn₁ n hn).2⟩⟩`. Conclude with `⟨0, fun h' => absurd h' hS⟩`. Use `choose nS hnS using key`.

Use `⟨Finset.univ.sup nS, fun n hn => ?_⟩` and prove the remaining obligations. Establish `hle : ∀ S, nS S ≤ n` using `fun S => (Finset.le_sup (Finset.mem_univ S)).trans hn`. Establish `: G.IsQuasicoherent` using `hG.1`. Establish `: ((Scheme.Modules.pushforward ψ).obj (ProjScheme.twist i G n)).IsQuasicoherent` using `isQuasicoherent_pushforward_of_qcqs ψ _`. Use `⟨?_, fun p => ?_⟩` and prove the remaining obligations.

Use `isCoherent_of_affineCover _ V hVaff1 hV fun a => ?_` and prove the remaining obligations. Establish `hfin` using `(hnS {a} (Finset.singleton_nonempty a) n (hle _)).2`. Rewrite `hfin` using `[hWsingle]`. Conclude with `hfin`. Establish `hVaff : ∀ (m : ℕ) (s : Fin (m + 1) → ι), IsAffineOpen (⨅ a, V (s a))` using `fun m s => IsAffineOpen.iInf fun a => hVaff1 (s a)`.

Use `⟨HLinearEquivPushforwardOfAcyclic ψ A V hV hVaff (ProjScheme.twist i G n) (fun m s q => ?_) p⟩` and prove the remaining obligations. Establish `h1` using `(hnS (Finset.univ.image s) (Finset.univ_nonempty.image s) n (hle _)).1 q`. Rewrite `h1` using `[← hWtuple]`. Conclude with `h1`.
-/
theorem exists_relativeSerre {A : Type u} [CommRing A] [IsNoetherianRing A] {X X' : Scheme.{u}}
    [X.Over (Spec (.of A))] [X'.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [CompactSpace X] [IsLocallyNoetherian X] {N : ℕ} (i : X' ⟶ projectiveSpace A N)
    [IsClosedImmersion i] [i.IsOver (Spec (.of A))] (ψ : X' ⟶ X) [ψ.IsOver (Spec (.of A))]
    (G : X'.Modules) (hG : IsCoherent G) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      IsCoherent ((Scheme.Modules.pushforward ψ).obj (ProjScheme.twist i G n)) ∧
      ∀ p : ℕ, Nonempty (Sheaf.H.{u} (modulesAb (ProjScheme.twist i G n)) p ≃ₗ[A]
        Sheaf.H.{u} (modulesAb ((Scheme.Modules.pushforward ψ).obj (ProjScheme.twist i G n))) p) := by
  classical
  have h : i ≫ ProjSpace.toSpecBase A N = ψ ≫ (X ↘ Spec (.of A)) := by
    rw [CategoryTheory.comp_over ψ (Spec (.of A))]
    exact CategoryTheory.comp_over i (Spec (.of A))
  have : X.IsSeparated := ⟨by
    rw [show terminal.from X = (X ↘ Spec (.of A)) ≫ terminal.from _ from terminal.hom_ext _ _]
    infer_instance⟩
  have : QuasiCompact (ψ ≫ (X ↘ Spec (.of A))) := by
    rw [← h]
    infer_instance
  have : QuasiCompact ψ := QuasiCompact.of_comp ψ (X ↘ Spec (.of A))
  have : QuasiSeparated (ψ ≫ (X ↘ Spec (.of A))) := by
    rw [← h]
    infer_instance
  have : QuasiSeparated ψ := QuasiSeparated.of_comp ψ (X ↘ Spec (.of A))

  obtain ⟨t, ht⟩ := (isCompact_univ (X := X)).elim_finite_subcover
    (fun U : X.affineOpens => (U : Set X)) (fun U => U.1.isOpen) (by
      intro x _
      obtain ⟨U, hU⟩ := Opens.mem_iSup.1
        (show x ∈ ⨆ U : X.affineOpens, (U : X.Opens) by rw [iSup_affineOpens_eq_top X]; trivial)
      exact Set.mem_iUnion.2 ⟨U, hU⟩)
  let ι := { U // U ∈ t }
  let V : ι → X.Opens := fun a => a.1.1
  have hVaff1 : ∀ a, IsAffineOpen (V a) := fun a => a.1.2
  have hV : iSup V = ⊤ := by
    apply le_antisymm le_top
    intro x _
    obtain ⟨U, hU⟩ := Set.mem_iUnion.1 (ht (Set.mem_univ x))
    obtain ⟨hUt, hxU⟩ := Set.mem_iUnion.1 hU
    exact Opens.mem_iSup.2 ⟨⟨U, hUt⟩, hxU⟩

  let W : Finset ι → X.Opens := fun S => ⨅ a : S, V a
  have hWaff : ∀ S : Finset ι, S.Nonempty → IsAffineOpen (W S) := fun S hS => by
    have : Nonempty S := hS.to_subtype
    exact IsAffineOpen.iInf fun a => hVaff1 a
  have hWtuple : ∀ (m : ℕ) (s : Fin (m + 1) → ι),
      (⨅ a, V (s a)) = W (Finset.univ.image s) := fun m s => by
    apply le_antisymm
    · exact le_iInf fun b => by
        obtain ⟨a, -, ha⟩ := Finset.mem_image.1 b.2
        exact (iInf_le _ a).trans (le_of_eq (congrArg V ha))
    · exact le_iInf fun a => iInf_le (fun b : (Finset.univ.image s : Finset ι) => V b)
        ⟨s a, Finset.mem_image_of_mem s (Finset.mem_univ a)⟩
  have hWsingle : ∀ a : ι, W {a} = V a := fun a => by
    apply le_antisymm
    · exact iInf_le (fun b : ({a} : Finset ι) => V b) ⟨a, Finset.mem_singleton_self a⟩
    · exact le_iInf fun b => le_of_eq (congrArg V (Finset.mem_singleton.1 b.2).symm)

  have key : ∀ S : Finset ι, ∃ n₁ : ℕ, S.Nonempty → ∀ n : ℕ, n₁ ≤ n →
      (∀ q : ℕ, Subsingleton (Sheaf.H.{u}
        (modulesAb ((ProjScheme.twist i G n).restrict (ψ ⁻¹ᵁ W S).ι)) (q + 1))) ∧
      Module.Finite Γ(X, W S) Γ((Scheme.Modules.pushforward ψ).obj (ProjScheme.twist i G n), W S) := by
    intro S
    by_cases hS : S.Nonempty
    · have hA := hWaff S hS
      have : IsNoetherianRing Γ(X, W S) := IsLocallyNoetherian.component_noetherian ⟨_, hA⟩
      obtain ⟨n₁, hn₁⟩ := RelSerre.exists_vanishing_finite i ψ h hA G hG
      exact ⟨n₁, fun _ n hn => ⟨(hn₁ n hn).1,
        RelSerre.finite_sections_pushforward i ψ h hA _ (hn₁ n hn).2⟩⟩
    · exact ⟨0, fun h' => absurd h' hS⟩
  choose nS hnS using key
  refine ⟨Finset.univ.sup nS, fun n hn => ?_⟩
  have hle : ∀ S, nS S ≤ n := fun S => (Finset.le_sup (Finset.mem_univ S)).trans hn
  have : G.IsQuasicoherent := hG.1
  have : ((Scheme.Modules.pushforward ψ).obj (ProjScheme.twist i G n)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_qcqs ψ _
  refine ⟨?_, fun p => ?_⟩
  · refine isCoherent_of_affineCover _ V hVaff1 hV fun a => ?_
    have hfin := (hnS {a} (Finset.singleton_nonempty a) n (hle _)).2
    rw [hWsingle] at hfin
    exact hfin
  · have hVaff : ∀ (m : ℕ) (s : Fin (m + 1) → ι), IsAffineOpen (⨅ a, V (s a)) := fun m s =>
      IsAffineOpen.iInf fun a => hVaff1 (s a)
    refine ⟨HLinearEquivPushforwardOfAcyclic ψ A V hV hVaff (ProjScheme.twist i G n)
      (fun m s q => ?_) p⟩
    have h1 := (hnS (Finset.univ.image s) (Finset.univ_nonempty.image s) n (hle _)).1 q
    rw [← hWtuple] at h1
    exact h1

end ProjScheme

end

end GroundTheory.Arith.SchemeCoh

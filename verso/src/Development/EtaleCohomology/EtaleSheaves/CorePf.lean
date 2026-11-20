import Development.EtaleCohomology.EtaleSheaves.ChowGraphCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut LateralTheory.E.ChowGraphCut

namespace LateralTheory.E.CorePf

def ImageClosed : Prop := ∀ {S X₁ : Scheme.{0}} (p₁ : X₁ ⟶ S) [IsProper p₁]
  (n : ℕ) (U : Fin n → X₁.Opens) (Pj : Fin n → Scheme.{0}) (qj : ∀ j, Pj j ⟶ S) (W : ∀ j, (Pj j).Opens)
    (e : ∀ j, (U j).toScheme ⟶ (W j).toScheme) (P : Scheme.{0}) (q : P ⟶ S) (π : ∀ j, P ⟶ Pj j),
    (∀ x : X₁, ∃ j, x ∈ U j) → (∀ j, IsSeparated (qj j)) →
    (∀ j, IsClosedImmersion (e j)) → (∀ j, e j ≫ (W j).ι ≫ qj j = (U j).ι ≫ p₁) → (∀ j, π j ≫ qj j = q) →
    ∀ (V : X₁.Opens) (hV : ∀ j, V ≤ U j) (γ : V.toScheme ⟶ pullback p₁ q),
      γ ≫ pullback.fst p₁ q = V.ι → (∀ j, γ ≫ pullback.snd p₁ q ≫ π j = X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) →
      IsClosedImmersion (γ.imageι ≫ pullback.snd p₁ q)

/- English proof (translation)
Introduce `s hs`. Proceed by induction on `hs using Finset.Nonempty.cons_induction with`. Consider the case `singleton a => simpa using hU a`. Consider the case `cons a s ha hs ih`. Rewrite using `[Finset.inf_cons, TopologicalSpace.Opens.coe_inf]`.

Conclude with `nonempty_preirreducible_inter (U a).2 (s.inf U).2 (hU a) ih`.
-/
theorem inf_nonempty {X : Type} [TopologicalSpace X] [PreirreducibleSpace X] {n : ℕ}
    (U : Fin n → TopologicalSpace.Opens X) (hU : ∀ j, (U j : Set X).Nonempty) :
    ∀ s : Finset (Fin n), s.Nonempty → ((s.inf U : TopologicalSpace.Opens X) : Set X).Nonempty := by
  intro s hs
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hU a
  | cons a s ha hs ih =>
    rw [Finset.inf_cons, TopologicalSpace.Opens.coe_inf]
    exact nonempty_preirreducible_inter (U a).2 (s.inf U).2 (hU a) ih

/- English proof (translation)
Introduce `S X₁ p₁ _ hX n U Pj qj W e P q π hUn hUc hsep he hc hπ hUP`. Establish `hne : Nonempty X₁` using `inferInstance`. Take `⟨x₀⟩` from `hne`. Take `⟨j₀, -⟩` from `hUc x₀`. Set `V : X₁.Opens` to `Finset.univ.inf U`.

Establish `hV : ∀ j, V ≤ U j` using `fun j => Finset.inf_le (Finset.mem_univ j)`. Establish `hVne : (V : Set X₁).Nonempty` using `inf_nonempty U hUn _ ⟨j₀, Finset.mem_univ _⟩`. Take `⟨g, ⟨hg1, hg2⟩, -⟩` from `hUP (V.ι ≫ p₁) (fun j => X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) (by`. Introduce `j`. Simplify using `only [Category.assoc, hc j, Scheme.homOfLE_ι_assoc])`.

Set `γ : V.toScheme ⟶ pullback p₁ q` to `pullback.lift V.ι g hg1.symm`. Establish `hγ1 : γ ≫ pullback.fst p₁ q = V.ι` using `pullback.lift_fst _ _ _`. Establish `hγ2 : ∀ j, γ ≫ pullback.snd p₁ q ≫ π j = X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι`. Introduce `j`. Rewrite using `[pullback.lift_snd_assoc, hg2 j]`.

Use `⟨γ.image, γ.imageι, V, γ.toImage, inferInstance, hI p₁ n U Pj qj W e P q π hUc hsep he hc hπ V hV γ hγ1 hγ2, hVne, ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.Hom.toImage_imageι_assoc, hγ1]`.
-/
theorem Core_of (hI : ImageClosed) : Core := by
  intro S X₁ p₁ _ hX n U Pj qj W e P q π hUn hUc hsep he hc hπ hUP
  have hne : Nonempty X₁ := inferInstance
  obtain ⟨x₀⟩ := hne
  obtain ⟨j₀, -⟩ := hUc x₀
  let V : X₁.Opens := Finset.univ.inf U
  have hV : ∀ j, V ≤ U j := fun j => Finset.inf_le (Finset.mem_univ j)
  have hVne : (V : Set X₁).Nonempty := inf_nonempty U hUn _ ⟨j₀, Finset.mem_univ _⟩
  obtain ⟨g, ⟨hg1, hg2⟩, -⟩ := hUP (V.ι ≫ p₁) (fun j => X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) (by
    intro j
    simp only [Category.assoc, hc j, Scheme.homOfLE_ι_assoc])
  let γ : V.toScheme ⟶ pullback p₁ q := pullback.lift V.ι g hg1.symm
  have hγ1 : γ ≫ pullback.fst p₁ q = V.ι := pullback.lift_fst _ _ _
  have hγ2 : ∀ j, γ ≫ pullback.snd p₁ q ≫ π j = X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι := by
    intro j; rw [pullback.lift_snd_assoc, hg2 j]
  refine ⟨γ.image, γ.imageι, V, γ.toImage, inferInstance,
    hI p₁ n U Pj qj W e P q π hUc hsep he hc hπ V hV γ hγ1 hγ2, hVne, ?_⟩
  rw [Scheme.Hom.toImage_imageι_assoc, hγ1]

end LateralTheory.E.CorePf

end

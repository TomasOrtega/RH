import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.WeilBound.CoreStatements.SesquilinearFractions.GBridge
import Development.WeilBound.CoreStatements.SesquilinearFractions.GModel
import Development.WeilBound.CoreStatements.SesquilinearFractions.FrameBCLin

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf.EigenspaceComposition

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `X g₁ g₂ h`. Take `⟨⟨x₁, φ₁⟩, rfl⟩` from `(Scheme.SpecToEquivOfField K X).symm.surjective g₁`. Take `⟨⟨x₂, φ₂⟩, rfl⟩` from `(Scheme.SpecToEquivOfField K X).symm.surjective g₂`. Establish `h' : (Scheme.SpecToEquivOfField L X).symm ⟨x₁, φ₁ ≫ CommRingCat.ofHom a⟩ = (Scheme.SpecToEquivOfField L X).symm ⟨x₂, φ₂ ≫ CommRingCat.ofHom a⟩`.

Simplify `h` using `[Scheme.SpecToEquivOfField, spMap, Spec.map_comp, Category.assoc]`. Establish `h''` using `(Scheme.SpecToEquivOfField L X).symm.injective h'`. Rewrite `h''` using `[Scheme.SpecToEquivOfField_eq_iff]`. Take `⟨e, he⟩` from `h''`. Simplify using `only at e he`.

Substitute `e` using the available equality. Establish `hφ : φ₁ = φ₂`. Use extensionality with `z`. Establish `hz` using `congrArg (fun m => m.hom z) he`. Simplify using `at hz`.

Conclude with `a.injective hz`. Rewrite using `[hφ]`.
-/
theorem epi_spMap {K L : Type} [Field K] [Field L] (a : K →+* L) : Epi (spMap a) := by
  constructor
  intro X g₁ g₂ h
  obtain ⟨⟨x₁, φ₁⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective g₁
  obtain ⟨⟨x₂, φ₂⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective g₂
  have h' : (Scheme.SpecToEquivOfField L X).symm ⟨x₁, φ₁ ≫ CommRingCat.ofHom a⟩ =
      (Scheme.SpecToEquivOfField L X).symm ⟨x₂, φ₂ ≫ CommRingCat.ofHom a⟩ := by
    simpa [Scheme.SpecToEquivOfField, spMap, Spec.map_comp, Category.assoc] using h
  have h'' := (Scheme.SpecToEquivOfField L X).symm.injective h'
  rw [Scheme.SpecToEquivOfField_eq_iff] at h''
  obtain ⟨e, he⟩ := h''
  dsimp only at e he
  subst e
  have hφ : φ₁ = φ₂ := by
    ext z
    have hz := congrArg (fun m => m.hom z) he
    simp at hz
    exact a.injective hz
  rw [hφ]

/- English proof (translation)
Rewrite using `[Hom.one_def, Over.comp_left]`. Use `congr 1`.
-/
theorem one_left' {S : Scheme.{0}} (G : Over S) [GrpObj G] (Y : Over S) :
    (1 : Y ⟶ G).left = Y.hom ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

end PositivityTheory.Xgf.EigenspaceComposition

namespace PositivityTheory.Xgf

/- English proof (translation)
Establish `key : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom F' F' F').toRingHom) ≫ spMap (dualMap f) = spMap f ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom F F F).toRingHom)`. Simplify using `only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `a`.

Simplify using `[dualMap]`. Use `haveI := EigenspaceComposition.epi_spMap f`. Use `show _ = (1 : Over.mk x' ⟶ G).left ↔ _ = (1 : Over.mk x ⟶ G).left`. Rewrite using `[EigenspaceComposition.one_left', EigenspaceComposition.one_left', hw, ← Category.assoc, key, Category.assoc]`. Simplify using `only [Over.mk_hom, hx, Category.assoc]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `(cancel_epi (spMap f)).mp h`. Introduce `h`. Rewrite using `[h]`.
-/
private theorem isTanAt_base_change_iff {S : Scheme.{0}} (G : Over S) [GrpObj G] {F F' : Type} [Field F] [Field F']
    (f : F →+* F') (x : Sp F ⟶ S) (x' : Sp F' ⟶ S) (hx : x' = spMap f ≫ x)
    (w : epsAt x ⟶ G) (w' : epsAt x' ⟶ G) (hw : w'.left = spMap (dualMap f) ≫ w.left) :
    IsTanAt G x' w' ↔ IsTanAt G x w := by
  have key : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom F' F' F').toRingHom) ≫ spMap (dualMap f) =
      spMap f ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom F F F).toRingHom) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply RingHom.ext
    intro a
    simp [dualMap]
  haveI := EigenspaceComposition.epi_spMap f
  show _ = (1 : Over.mk x' ⟶ G).left ↔ _ = (1 : Over.mk x ⟶ G).left
  rw [EigenspaceComposition.one_left', EigenspaceComposition.one_left', hw, ← Category.assoc, key, Category.assoc]
  simp only [Over.mk_hom, hx, Category.assoc]
  constructor
  · intro h
    exact (cancel_epi (spMap f)).mp h
  · intro h
    rw [h]

open PositivityTheory.Xgf.EigenspaceComposition in
/- English proof (translation)
Introduce `E _ _ _ H S t F F' _ _ f x x' τ n v hx'`. Establish `hcomp : ∀ w : epsAt x ⟶ t.G, ∃ w' : epsAt x' ⟶ t.G, w'.left = spMap (dualMap f) ≫ w.left`. Introduce `w`. Use `⟨Over.homMk (spMap (dualMap f) ≫ w.left) ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, Over.w w]`.

Simplify using `only [epsAt, Over.mk_hom, hx', spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 3`. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[dualMap, TrivSqZeroExt.algebraMap_eq_inl]`.

Use `⟨⟨fun k => Classical.choose (hcomp (v k)), fun k => Classical.choose_spec (hcomp (v k))⟩, ?_⟩` and prove the remaining obligations. Introduce `v' hv'`. Establish `htan : ∀ k, IsTanAt t.G x' (v' k) ↔ IsTanAt t.G x (v k)` using `fun k => isTanAt_base_change_iff t.G f x x' hx' (v k) (v' k) (hv' k)`. Distinguish the cases in `hT : ∀ k, IsTanAt t.G x (v k)`. Take `⟨N, M, ρ, hρ, hbc⟩` from `lie_model_action_base_change E H S t F x`.

Take `⟨M', ρ', hρ', hpt, hc⟩` from `hbc F' f x' hx'`. Use `choose u hu using fun k => M.onto (v k) (hT k)`. Establish `hv'eq : v' = fun k => M'.pt (f ∘ u k)`. Use function extensionality and compare the values at `k`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Rewrite using `[hv' k, hpt, hu k]`. Establish `hveq : v = fun k => M.pt (u k)` using `funext fun k => (hu k).symm`. Rewrite using `[hv'eq, hveq, ((lie_model_eigenvectors_action S F t.G x _ M).2 _ t.act ρ τ hρ).2 n u, ((lie_model_eigenvectors_action S F' t.G x' _ M').2 _ t.act ρ' (f.comp τ) hρ').2 n (fun k => f ∘ u k)]`. Conclude with `EigenspaceComposition.core (τ := τ) hc u`. Use `push_neg at hT`.

Take `⟨k, hk⟩` from `hT`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `absurd (h.1 k).1 hk`. Introduce `h`.

Conclude with `absurd ((htan k).1 (h.1 k).1) hk`.
-/
theorem tangent_vectors_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (F F' : Type) [Field F] [Field F'] (f : F →+* F') (x : Sp F ⟶ S) (x' : Sp F' ⟶ S) (τ : 𝓞 E →+* F) (n : ℕ) (v : Fin n → (epsAt x ⟶ t.G)), x' = spMap f ≫ x → (∃ v' : Fin n → (epsAt x' ⟶ t.G), ∀ k, (v' k).left = spMap (dualMap f) ≫ (v k).left) ∧ ∀ v' : Fin n → (epsAt x' ⟶ t.G), (∀ k, (v' k).left = spMap (dualMap f) ≫ (v k).left) → (IsEigFrame t.act x τ v ↔ IsEigFrame t.act x' (f.comp τ) v') := by
  intro E _ _ _ H S t F F' _ _ f x x' τ n v hx'
  have hcomp : ∀ w : epsAt x ⟶ t.G, ∃ w' : epsAt x' ⟶ t.G, w'.left = spMap (dualMap f) ≫ w.left := by
    intro w
    refine ⟨Over.homMk (spMap (dualMap f) ≫ w.left) ?_, rfl⟩
    rw [Category.assoc, Over.w w]
    simp only [epsAt, Over.mk_hom, hx', spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    apply RingHom.ext
    intro a
    simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  refine ⟨⟨fun k => Classical.choose (hcomp (v k)), fun k => Classical.choose_spec (hcomp (v k))⟩, ?_⟩
  intro v' hv'
  have htan : ∀ k, IsTanAt t.G x' (v' k) ↔ IsTanAt t.G x (v k) :=
    fun k => isTanAt_base_change_iff t.G f x x' hx' (v k) (v' k) (hv' k)
  by_cases hT : ∀ k, IsTanAt t.G x (v k)
  · obtain ⟨N, M, ρ, hρ, hbc⟩ := lie_model_action_base_change E H S t F x
    obtain ⟨M', ρ', hρ', hpt, hc⟩ := hbc F' f x' hx'
    choose u hu using fun k => M.onto (v k) (hT k)
    have hv'eq : v' = fun k => M'.pt (f ∘ u k) := by
      funext k
      apply Over.OverMorphism.ext
      rw [hv' k, hpt, hu k]
    have hveq : v = fun k => M.pt (u k) := funext fun k => (hu k).symm
    rw [hv'eq, hveq, ((lie_model_eigenvectors_action S F t.G x _ M).2 _ t.act ρ τ hρ).2 n u,
      ((lie_model_eigenvectors_action S F' t.G x' _ M').2 _ t.act ρ' (f.comp τ) hρ').2 n (fun k => f ∘ u k)]
    exact EigenspaceComposition.core (τ := τ) hc u
  · push_neg at hT
    obtain ⟨k, hk⟩ := hT
    constructor
    · intro h
      exact absurd (h.1 k).1 hk
    · intro h
      exact absurd ((htan k).1 (h.1 k).1) hk

end PositivityTheory.Xgf

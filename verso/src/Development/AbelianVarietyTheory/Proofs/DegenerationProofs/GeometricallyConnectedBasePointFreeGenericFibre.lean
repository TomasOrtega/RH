import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsScalMulEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedGenericFibreOfDense
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.GenericSplit

/- English proof (translation)
Use `⟨fun L _ y Z fst snd H ↦ ?_⟩` and prove the remaining obligations. Establish `H' : IsPullback (fst ≫ pullback.fst f t') snd f (y ≫ t')` using `H.paste_horiz (.of_hasPullback f t')`. Take `⟨s, hs⟩` from `hr ⟨y (default : PrimeSpectrum L), rfl⟩`. Take `⟨w, -⟩` from `Scheme.exists_preimage_of_isPullback (.of_hasPullback (y ≫ t') t) (default : PrimeSpectrum L) s ((Scheme.Hom.comp_apply _ _ _).trans hs.symm)`. Set `m` to `(pullback (y ≫ t') t).fromSpecResidueField w`.

Set `m₁` to `m ≫ pullback.fst (y ≫ t') t`. Set `m₂` to `m ≫ pullback.snd (y ≫ t') t`. Establish `hm : m₁ ≫ y ≫ t' = m₂ ≫ t`. Simplify using `only [m₁, m₂, Category.assoc, pullback.condition]`. Establish `H1 : IsPullback (pullback.fst snd m₁ ≫ fst ≫ pullback.fst f t') (pullback.snd snd m₁) f (m₂ ≫ t)`.

Rewrite using `[← hm]`. Conclude with `(IsPullback.of_hasPullback snd m₁).paste_horiz H'`. Establish `H2 : IsPullback (pullback.lift _ _ (H1.w.trans (Category.assoc _ _ _).symm)) (pullback.snd snd m₁) (pullback.snd f t) m₂`. Use `IsPullback.of_right (h₁₂ := pullback.fst f t) (v₁₃ := f) (h₂₂ := t) ?_ (pullback.lift_snd _ _ _) (.of_hasPullback _ _)` and prove the remaining obligations. Rewrite using `[pullback.lift_fst]`.

Conclude with `H1`. Establish `hc : ConnectedSpace ↥(pullback snd m₁)` using `h.geometrically_connectedSpace _ _ _ H2`. Establish `: Surjective m₁` using `⟨fun z ↦ ⟨(default : PrimeSpectrum _), Subsingleton.elim (α := PrimeSpectrum L) _ _⟩⟩`. Establish `hsurj : Function.Surjective (pullback.fst snd m₁)` using `(pullback.fst snd m₁).surjective`. Conclude with `hsurj.connectedSpace (pullback.fst snd m₁).continuous`.
-/
theorem geometricallyConnected_snd_of_range_subset {X S T T' : Scheme.{0}} (f : X ⟶ S) (t : T ⟶ S) (t' : T' ⟶ S)
    (hr : Set.range t' ⊆ Set.range t) (h : GeometricallyConnected (pullback.snd f t)) :
    GeometricallyConnected (pullback.snd f t') := by
  refine ⟨fun L _ y Z fst snd H ↦ ?_⟩
  have H' : IsPullback (fst ≫ pullback.fst f t') snd f (y ≫ t') :=
    H.paste_horiz (.of_hasPullback f t')
  obtain ⟨s, hs⟩ := hr ⟨y (default : PrimeSpectrum L), rfl⟩
  obtain ⟨w, -⟩ := Scheme.exists_preimage_of_isPullback (.of_hasPullback (y ≫ t') t)
    (default : PrimeSpectrum L) s ((Scheme.Hom.comp_apply _ _ _).trans hs.symm)
  let m := (pullback (y ≫ t') t).fromSpecResidueField w
  let m₁ := m ≫ pullback.fst (y ≫ t') t
  let m₂ := m ≫ pullback.snd (y ≫ t') t
  have hm : m₁ ≫ y ≫ t' = m₂ ≫ t := by
    simp only [m₁, m₂, Category.assoc, pullback.condition]
  have H1 : IsPullback (pullback.fst snd m₁ ≫ fst ≫ pullback.fst f t') (pullback.snd snd m₁) f (m₂ ≫ t) := by
    rw [← hm]
    exact (IsPullback.of_hasPullback snd m₁).paste_horiz H'
  have H2 : IsPullback (pullback.lift _ _ (H1.w.trans (Category.assoc _ _ _).symm)) (pullback.snd snd m₁)
      (pullback.snd f t) m₂ := by
    refine IsPullback.of_right (h₁₂ := pullback.fst f t) (v₁₃ := f) (h₂₂ := t) ?_
      (pullback.lift_snd _ _ _) (.of_hasPullback _ _)
    rw [pullback.lift_fst]
    exact H1
  have hc : ConnectedSpace ↥(pullback snd m₁) := h.geometrically_connectedSpace _ _ _ H2
  have : Surjective m₁ := ⟨fun z ↦ ⟨(default : PrimeSpectrum _), Subsingleton.elim (α := PrimeSpectrum L) _ _⟩⟩
  have hsurj : Function.Surjective (pullback.fst snd m₁) := (pullback.fst snd m₁).surjective
  exact hsurj.connectedSpace (pullback.fst snd m₁).continuous

/- English proof (translation)
Establish `hz : z.asIdeal = ⊥` using `congrArg PrimeSpectrum.asIdeal (Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) z ⟨⊥, Ideal.isPrime_bot⟩)`. Express the relevant statement in the definitionally equal form `Ideal.comap (algebraMap R (FractionRing R)) z.asIdeal = ⊥`. Rewrite using `[hz]`. Conclude with `Ideal.comap_bot_of_injective _ (IsFractionRing.injective R _)`.
-/
theorem jK_asIdeal (R : Type) [CommRing R] [IsDomain R] (z : Sp (FractionRing R)) :
    (Out.jK R z).asIdeal = ⊥ := by
  have hz : z.asIdeal = ⊥ := congrArg PrimeSpectrum.asIdeal
    (Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) z ⟨⊥, Ideal.isPrime_bot⟩)
  change Ideal.comap (algebraMap R (FractionRing R)) z.asIdeal = ⊥
  rw [hz]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R _)

/- English proof (translation)
Introduce `R _ _ _ G _ _ _ _ _ C d c Sg _ hD hS`. Prove the components needed by the constructor for the conclusion. Establish `h` using `geometricallyConnected_genericFibre_of_dense G.left (Sp R) G.hom Sg hD fun x hx ↦ by`. Take `⟨K, _, t, _, ht, hc, -⟩` from `hS x hx`. Conclude with `geometricallyConnected_snd_of_range_subset G.hom t _ (by rw [Scheme.range_fromSpecResidueField, ht]) hc`.

Use `geometricallyConnected_snd_of_range_subset G.hom _ _ ?_ h` and prove the remaining obligations. Rewrite using `[Scheme.range_fromSpecResidueField]`. Introduce and unpack `_ ⟨z, rfl⟩`. Rewrite using `[genericPoint_eq_bot_of_affine]`. Conclude with `PrimeSpectrum.ext (jK_asIdeal R z)`.

Introduce `n x`. Set `V : G.left.Opens` to `⨆ (a) (j) (_ : C.wt j = c n), G.left.basicOpen (C.r a j)`. Take `⟨b, hb0, hb⟩` from `GenericEq.exists_mem_of_not_mem R G Sg hD V fun y hy ↦ by`. Take `⟨K, _, t, _, ht, -, i, hi⟩` from `hS _ hy`. Take `⟨s, hs⟩ : G.hom y ∈ Set.range t` from `ht ▸ rfl`.

Take `⟨z, hz, -⟩` from `Scheme.exists_preimage_of_isPullback (.of_hasPullback G.hom t) y s hs.symm`. Take `⟨a, j, hj, hz'⟩` from `hi.bpf n z`. Establish `: z ∈ pullback.fst G.hom t ⁻¹ᵁ G.left.basicOpen (C.r a j)`. Rewrite using `[Scheme.preimage_basicOpen]`. Conclude with `hz'`.

Simplify using `only [V, TopologicalSpace.Opens.mem_iSup]`. Conclude with `⟨a, j, hj, hz ▸ this⟩`. Establish `hx` using `hb (pullback.fst G.hom (Out.jK R) x) (by`. Rewrite using `[← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, jK_asIdeal]`. Conclude with `hb0)`.

Simplify using `only [V, TopologicalSpace.Opens.mem_iSup] at hx`. Take `⟨a, j, hj, hx⟩` from `hx`. Use `⟨a, j, hj, ?_⟩` and prove the remaining obligations. Establish `: x ∈ pullback.fst G.hom (Out.jK R) ⁻¹ᵁ G.left.basicOpen (C.r a j)` using `hx`. Rewrite `this` using `[Scheme.preimage_basicOpen]`.

Conclude with `this`.
-/
theorem geometricallyConnected_and_basePointFree_generic :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → GeometricallyConnected ((Over.pullback (Out.jK R)).obj G).hom ∧ ∀ (n : Fin d) (x : ((Over.pullback (Out.jK R)).obj G).left), ∃ a j, C.wt j = c n ∧ x ∈ ((Over.pullback (Out.jK R)).obj G).left.basicOpen ((C.pull (pullback.fst G.hom (Out.jK R))).r a j) := by
  intro R _ _ _ G _ _ _ _ _ C d c Sg _ hD hS
  constructor
  · have h := geometricallyConnected_genericFibre_of_dense G.left (Sp R) G.hom Sg hD fun x hx ↦ by
      obtain ⟨K, _, t, _, ht, hc, -⟩ := hS x hx
      exact geometricallyConnected_snd_of_range_subset G.hom t _
        (by rw [Scheme.range_fromSpecResidueField, ht]) hc
    refine geometricallyConnected_snd_of_range_subset G.hom _ _ ?_ h
    rw [Scheme.range_fromSpecResidueField]
    rintro _ ⟨z, rfl⟩
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext (jK_asIdeal R z)
  · intro n x
    let V : G.left.Opens := ⨆ (a) (j) (_ : C.wt j = c n), G.left.basicOpen (C.r a j)
    obtain ⟨b, hb0, hb⟩ := GenericEq.exists_mem_of_not_mem R G Sg hD V fun y hy ↦ by
      obtain ⟨K, _, t, _, ht, -, i, hi⟩ := hS _ hy
      obtain ⟨s, hs⟩ : G.hom y ∈ Set.range t := ht ▸ rfl
      obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback (.of_hasPullback G.hom t) y s hs.symm
      obtain ⟨a, j, hj, hz'⟩ := hi.bpf n z
      have : z ∈ pullback.fst G.hom t ⁻¹ᵁ G.left.basicOpen (C.r a j) := by
        rw [Scheme.preimage_basicOpen]
        exact hz'
      simp only [V, TopologicalSpace.Opens.mem_iSup]
      exact ⟨a, j, hj, hz ▸ this⟩
    have hx := hb (pullback.fst G.hom (Out.jK R) x) (by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, jK_asIdeal]
      exact hb0)
    simp only [V, TopologicalSpace.Opens.mem_iSup] at hx
    obtain ⟨a, j, hj, hx⟩ := hx
    refine ⟨a, j, hj, ?_⟩
    have : x ∈ pullback.fst G.hom (Out.jK R) ⁻¹ᵁ G.left.basicOpen (C.r a j) := hx
    rw [Scheme.preimage_basicOpen] at this
    exact this

end GlobalTheory.GenericSplit

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFibreAndEqOfSpecializesOfIsFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparatingBasicOpenFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingBasicOpenOfNearGeneratoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingWhereSingleCoefficientStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `Y Y' Z' k hk p' hpc hps V hV y hy _ M hM hloc`. Take `⟨hfin, hdisc⟩` from `GlobalTheory.T.finite_fibre_and_eq_of_specializes_of_isFinite' Y Y' k hk y`. Establish `hU : IsAffineOpen (k ⁻¹ᵁ V)` using `hV.preimage k`. Set `F : Finset Y'` to `hfin.toFinset`. Establish `hF : ∀ a, a ∈ F ↔ k a = y` using `fun a => by simp [F]`.

Establish `hW : ∀ a : Y', ∃ W : Y'.Opens, (k a = y → a ∈ W ∧ ∃ t : LB.Gen (M.pull (p' ⁻¹ᵁ W).ι), t.IsGen)`. Introduce `a`. Distinguish the cases in `h : k a = y`. Take `⟨W, hW, t, ht⟩` from `hloc a h`. Conclude with `⟨W, fun _ => ⟨hW, t, ht⟩⟩`.

Conclude with `⟨⊤, fun h' => absurd h' h⟩`. Use `choose W hW using hW`. Take `⟨f, hf⟩` from `GlobalTheory.T.exists_separating_basicOpen_functions' Y' (k ⁻¹ᵁ V) hU F (fun a ha => by show k a ∈ V`. Rewrite using `[(hF a).1 ha]`. Conclude with `hy) (fun a ha b hb hab => hdisc a b ((hF a).1 ha) ((hF b).1 hb) hab)`.

Use `W (fun a ha => ((hW a) ((hF a).1 ha)).1)`. Set `q : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme ⟶ Y'` to `(p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι ≫ p'`. Establish `hq : (⊤ : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme.Opens) ≤ q ⁻¹ᵁ (k ⁻¹ᵁ V)`. Introduce `z _`. Use `show p' ((p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι z) ∈ k ⁻¹ᵁ V`.

Establish `h : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι z ∈ p' ⁻¹ᵁ (k ⁻¹ᵁ V)` using `(Scheme.Opens.range_ι (p' ⁻¹ᵁ (k ⁻¹ᵁ V))).subset ⟨z, rfl⟩`. Conclude with `h`. Set `r : Y' → Γ((p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme, ⊤)` to `fun a => (q.appLE (k ⁻¹ᵁ V) ⊤ hq).hom (f a)`. Establish `hr : ∀ a (z : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme), z ∈ (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme.basicOpen (r a) ↔ q z ∈ Y'.basicOpen (f a)`. Introduce `a z`.

Rewrite using `[Scheme.basicOpen_appLE]`. Conclude with `⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩`. Use `haveI : CompactSpace (k ⁻¹ᵁ V).toScheme := isCompact_iff_compactSpace.1 hU.isCompact`. Use `haveI : CompactSpace (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme := by`. Use `hpc.isCompact_preimage _ (k ⁻¹ᵁ V).isOpen hU.isCompact` as an intermediate fact.

Conclude with `isCompact_iff_compactSpace.1 this`. Use `haveI : IsAffine (k ⁻¹ᵁ V).toScheme := hU`. Use `haveI : QuasiSeparatedSpace (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme := quasiSeparatedSpace_of_quasiSeparated (p' ∣_ (k ⁻¹ᵁ V))`. Establish `hσ : ∀ a : F, ∃ σ : LB.Sec (M.pull (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι), (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme.basicOpen (r a) ≤ nonzeroLocus σ`. Introduce and unpack `⟨a, ha⟩`.

Take `⟨-, t, ht⟩` from `hW a ((hF a).1 ha)`. Conclude with `GlobalTheory.T.exists_section_nonvanishing_basicOpen_of_nearGenerator Z' _ (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι inferInstance ‹_› ‹_› M hM (r a) (p' ⁻¹ᵁ W a) (fun x hx => (hf a ha).2.1 ((hr a x).1 hx)) t ht`. Use `choose σ hσ using hσ`. Take `⟨s, hs⟩` from `GlobalTheory.T.exists_section_nonvanishing_where_single_coefficient _ (M.pull (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι) F (fun a => r a) σ`. Use `⟨s, fun z hz => ?_⟩` and prove the remaining obligations.

Establish `ha : q z ∈ F` using `(hF _).2 hz`. Establish `h1 : z ∈ (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme.basicOpen (r (q z))` using `(hr _ z).2 (hf _ ha).1`. Use `hs z ⟨q z, ha⟩ h1 (hσ _ h1) (fun j hj => ?_)` and prove the remaining obligations. Rewrite using `[hr]`. Conclude with `(hf j.1 j.2).2.2 (q z) ha (fun h => hj (Subtype.ext h.symm))`.
-/
theorem exists_sec_nonzero_on_fibre : ∀ (Y Y' Z' : Scheme.{0}) (k : Y' ⟶ Y), IsFinite k → ∀ (p' : Z' ⟶ Y'), QuasiCompact p' → QuasiSeparated p' → ∀ (V : Y.Opens), IsAffineOpen V → ∀ y ∈ V, (∀ y₁ ∈ V, y ⤳ y₁ → y₁ = y) → ∀ (M : LB Z'), M.IsLB → (∀ x' : Y', k x' = y → ∃ W : Y'.Opens, x' ∈ W ∧ ∃ t : LB.Gen (M.pull (p' ⁻¹ᵁ W).ι), t.IsGen) → ∃ s : LB.Sec (M.pull (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι), ∀ z : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme, k (p' ((p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι z)) = y → z ∈ nonzeroLocus s := by
  intro Y Y' Z' k hk p' hpc hps V hV y hy _ M hM hloc
  classical
  obtain ⟨hfin, hdisc⟩ := GlobalTheory.T.finite_fibre_and_eq_of_specializes_of_isFinite' Y Y' k hk y
  have hU : IsAffineOpen (k ⁻¹ᵁ V) := hV.preimage k
  let F : Finset Y' := hfin.toFinset
  have hF : ∀ a, a ∈ F ↔ k a = y := fun a => by simp [F]
  have hW : ∀ a : Y', ∃ W : Y'.Opens, (k a = y → a ∈ W ∧ ∃ t : LB.Gen (M.pull (p' ⁻¹ᵁ W).ι), t.IsGen) := by
    intro a
    by_cases h : k a = y
    · obtain ⟨W, hW, t, ht⟩ := hloc a h
      exact ⟨W, fun _ => ⟨hW, t, ht⟩⟩
    · exact ⟨⊤, fun h' => absurd h' h⟩
  choose W hW using hW
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_separating_basicOpen_functions' Y' (k ⁻¹ᵁ V) hU F (fun a ha => by
      show k a ∈ V
      rw [(hF a).1 ha]; exact hy) (fun a ha b hb hab => hdisc a b ((hF a).1 ha) ((hF b).1 hb) hab)
    W (fun a ha => ((hW a) ((hF a).1 ha)).1)
  let q : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme ⟶ Y' := (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι ≫ p'
  have hq : (⊤ : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme.Opens) ≤ q ⁻¹ᵁ (k ⁻¹ᵁ V) := by
    intro z _
    show p' ((p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι z) ∈ k ⁻¹ᵁ V
    have h : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι z ∈ p' ⁻¹ᵁ (k ⁻¹ᵁ V) := (Scheme.Opens.range_ι (p' ⁻¹ᵁ (k ⁻¹ᵁ V))).subset ⟨z, rfl⟩
    exact h
  let r : Y' → Γ((p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme, ⊤) := fun a => (q.appLE (k ⁻¹ᵁ V) ⊤ hq).hom (f a)
  have hr : ∀ a (z : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme), z ∈ (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme.basicOpen (r a) ↔ q z ∈ Y'.basicOpen (f a) := by
    intro a z
    rw [Scheme.basicOpen_appLE]
    exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  haveI : CompactSpace (k ⁻¹ᵁ V).toScheme := isCompact_iff_compactSpace.1 hU.isCompact
  haveI : CompactSpace (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme := by
    have := hpc.isCompact_preimage _ (k ⁻¹ᵁ V).isOpen hU.isCompact
    exact isCompact_iff_compactSpace.1 this
  haveI : IsAffine (k ⁻¹ᵁ V).toScheme := hU
  haveI : QuasiSeparatedSpace (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme := quasiSeparatedSpace_of_quasiSeparated (p' ∣_ (k ⁻¹ᵁ V))
  have hσ : ∀ a : F, ∃ σ : LB.Sec (M.pull (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι), (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme.basicOpen (r a) ≤ nonzeroLocus σ := by
    rintro ⟨a, ha⟩
    obtain ⟨-, t, ht⟩ := hW a ((hF a).1 ha)
    exact GlobalTheory.T.exists_section_nonvanishing_basicOpen_of_nearGenerator Z' _ (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι inferInstance ‹_› ‹_› M hM (r a) (p' ⁻¹ᵁ W a)
      (fun x hx => (hf a ha).2.1 ((hr a x).1 hx)) t ht
  choose σ hσ using hσ
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_section_nonvanishing_where_single_coefficient _ (M.pull (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι) F (fun a => r a) σ
  refine ⟨s, fun z hz => ?_⟩
  have ha : q z ∈ F := (hF _).2 hz
  have h1 : z ∈ (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme.basicOpen (r (q z)) := (hr _ z).2 (hf _ ha).1
  refine hs z ⟨q z, ha⟩ h1 (hσ _ h1) (fun j hj => ?_)
  rw [hr]
  exact (hf j.1 j.2).2.2 (q z) ha (fun h => hj (Subtype.ext h.symm))

end GlobalTheory.Mum

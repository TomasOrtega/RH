import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SerreHolomorphicSectionsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactSpacePts
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.Gaga

/- English proof (translation)
Establish `e₁ : SmoothOfRelativeDimension (0 + n) ((U ⊓ V).ι ≫ f)`. Rewrite using `[← Scheme.homOfLE_ι _ (inf_le_left : U ⊓ V ≤ U), Category.assoc]`. Use `infer_instance`. Establish `e₂ : SmoothOfRelativeDimension (0 + m) ((U ⊓ V).ι ≫ f)`. Rewrite using `[← Scheme.homOfLE_ι _ (inf_le_right : U ⊓ V ≤ V), Category.assoc]`.

Use `infer_instance`. Simplify using `using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ e₁ e₂ ⟨x, hxU, hxV⟩`.
-/
theorem dim_eq_of_mem_inf {X Y : Scheme.{0}} (f : X ⟶ Y) {U V : X.Opens} {n m : ℕ}
    (hU : SmoothOfRelativeDimension n (U.ι ≫ f)) (hV : SmoothOfRelativeDimension m (V.ι ≫ f))
    {x : X} (hxU : x ∈ U) (hxV : x ∈ V) : n = m := by
  have e₁ : SmoothOfRelativeDimension (0 + n) ((U ⊓ V).ι ≫ f) := by
    rw [← Scheme.homOfLE_ι _ (inf_le_left : U ⊓ V ≤ U), Category.assoc]; infer_instance
  have e₂ : SmoothOfRelativeDimension (0 + m) ((U ⊓ V).ι ≫ f) := by
    rw [← Scheme.homOfLE_ι _ (inf_le_right : U ⊓ V ≤ V), Category.assoc]; infer_instance
  simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ e₁ e₂ ⟨x, hxU, hxV⟩

/- English proof (translation)
Establish `: IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} D)` using `HasRingHomProperty.instIsZariskiLocalAtSource`. Use `IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{0} D) (fun i => (⨆ i, U i).ι ⁻¹ᵁ U i) ?_ fun i => ?_` and prove the remaining obligations. Use `top_le_iff.1 fun x _ => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `Opens.mem_iSup.1 x.2`. Conclude with `Opens.mem_iSup.2 ⟨i, hi⟩`.

Set `j` to `((⨆ i, U i).ι ⁻¹ᵁ U i).ι ≫ (⨆ i, U i).ι`. Establish `hr : Set.range j ⊆ Set.range (U i).ι`. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `y.2`.

Set `k` to `IsOpenImmersion.lift (U i).ι j hr`. Establish `hk : k ≫ (U i).ι = j` using `IsOpenImmersion.lift_fac _ _ _`. Establish `: IsOpenImmersion (k ≫ (U i).ι)` using `by rw [hk]; infer_instance`. Establish `: IsOpenImmersion k` using `IsOpenImmersion.of_comp k (U i).ι`. Establish `e : ((⨆ i, U i).ι ⁻¹ᵁ U i).ι ≫ (⨆ i, U i).ι ≫ f = k ≫ (U i).ι ≫ f`.

Rewrite using `[← Category.assoc, ← Category.assoc, hk]`. Rewrite using `[e]`. Conclude with `IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension.{0} D) (hU i) k`.
-/
theorem smoothOfRelativeDimension_iSup {X Y : Scheme.{0}} (f : X ⟶ Y) (D : ℕ) {ι : Type*}
    (U : ι → X.Opens) (hU : ∀ i, SmoothOfRelativeDimension D ((U i).ι ≫ f)) :
    SmoothOfRelativeDimension D ((⨆ i, U i).ι ≫ f) := by
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} D) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{0} D)
    (fun i => (⨆ i, U i).ι ⁻¹ᵁ U i) ?_ fun i => ?_
  · refine top_le_iff.1 fun x _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 x.2
    exact Opens.mem_iSup.2 ⟨i, hi⟩
  · let j := ((⨆ i, U i).ι ⁻¹ᵁ U i).ι ≫ (⨆ i, U i).ι
    have hr : Set.range j ⊆ Set.range (U i).ι := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact y.2
    let k := IsOpenImmersion.lift (U i).ι j hr
    have hk : k ≫ (U i).ι = j := IsOpenImmersion.lift_fac _ _ _
    have : IsOpenImmersion (k ≫ (U i).ι) := by rw [hk]; infer_instance
    have : IsOpenImmersion k := IsOpenImmersion.of_comp k (U i).ι
    have e : ((⨆ i, U i).ι ⁻¹ᵁ U i).ι ≫ (⨆ i, U i).ι ≫ f = k ≫ (U i).ι ≫ f := by
      rw [← Category.assoc, ← Category.assoc, hk]
    rw [e]
    exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension.{0} D) (hU i) k

/- English proof (translation)
Introduce `X s hs`. Set `W : ℕ → X.Opens` to `fun D => ⨆ U : {U : X.Opens // SmoothOfRelativeDimension D (U.ι ≫ s)}, U.1`. Establish `hsm : ∀ D, SmoothOfRelativeDimension D ((W D).ι ≫ s)` using `fun D => smoothOfRelativeDimension_iSup s D _ fun U => U.2`. Establish `hcov : (⨆ D, W D) = ⊤`. Use `top_le_iff.1 fun x _ => ?_` and prove the remaining obligations.

Take `⟨n, U, hx, hU⟩` from `ReciprocityTheory.ChartRestriction.G.H1.exists_dim s x`. Conclude with `Opens.mem_iSup.2 ⟨n, Opens.mem_iSup.2 ⟨⟨U, hU⟩, hx⟩⟩`. Establish `hdis : Pairwise fun D D' => W D ⊓ W D' = ⊥`. Introduce `D D' hne`. Use `le_bot_iff.1 fun x hx => ?_` and prove the remaining obligations.

Take `⟨U, hU⟩` from `Opens.mem_iSup.1 hx.1`. Take `⟨V, hV⟩` from `Opens.mem_iSup.1 hx.2`. Conclude with `(hne (dim_eq_of_mem_inf s U.2 V.2 hU hV)).elim`. Use `⟨W, fun D => ?_, hsm, hcov, hdis⟩` and prove the remaining obligations. Establish `hc : (W D : Set X)ᶜ = ((⨆ D' : {D' // D' ≠ D}, W D'.1 : X.Opens) : Set X)`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hx' : x ∈ (⨆ D, W D)` using `hcov ▸ trivial`. Take `⟨D', hD'⟩` from `Opens.mem_iSup.1 hx'`.

Use `Opens.mem_iSup.2 ⟨⟨D', fun e => hx (e ▸ hD')⟩, hD'⟩` and prove the remaining obligations. Introduce `hx hxD`. Take `⟨D', hD'⟩` from `Opens.mem_iSup.1 hx`. Use `hdis D'.2` as an intermediate fact. Establish `hm : x ∈ W D'.1 ⊓ W D` using `⟨hD', hxD⟩`.

Rewrite `hm` using `[this]`. Conclude with `hm`. Rewrite using `[← isOpen_compl_iff, hc]`. Conclude with `Opens.isOpen _`.
-/
theorem exists_clopen_smoothOfRelativeDimension :
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ), Smooth s → ∃ W : ℕ → X.Opens, (∀ D, IsClosed (W D : Set X)) ∧ (∀ D, SmoothOfRelativeDimension D ((W D).ι ≫ s)) ∧ (⨆ D, W D) = ⊤ ∧ Pairwise fun D D' => W D ⊓ W D' = ⊥ := by
  intro X s hs
  let W : ℕ → X.Opens := fun D => ⨆ U : {U : X.Opens // SmoothOfRelativeDimension D (U.ι ≫ s)}, U.1
  have hsm : ∀ D, SmoothOfRelativeDimension D ((W D).ι ≫ s) := fun D =>
    smoothOfRelativeDimension_iSup s D _ fun U => U.2
  have hcov : (⨆ D, W D) = ⊤ := by
    refine top_le_iff.1 fun x _ => ?_
    obtain ⟨n, U, hx, hU⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim s x
    exact Opens.mem_iSup.2 ⟨n, Opens.mem_iSup.2 ⟨⟨U, hU⟩, hx⟩⟩
  have hdis : Pairwise fun D D' => W D ⊓ W D' = ⊥ := by
    intro D D' hne
    refine le_bot_iff.1 fun x hx => ?_
    obtain ⟨U, hU⟩ := Opens.mem_iSup.1 hx.1
    obtain ⟨V, hV⟩ := Opens.mem_iSup.1 hx.2
    exact (hne (dim_eq_of_mem_inf s U.2 V.2 hU hV)).elim
  refine ⟨W, fun D => ?_, hsm, hcov, hdis⟩
  have hc : (W D : Set X)ᶜ = ((⨆ D' : {D' // D' ≠ D}, W D'.1 : X.Opens) : Set X) := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ (⨆ D, W D) := hcov ▸ trivial
      obtain ⟨D', hD'⟩ := Opens.mem_iSup.1 hx'
      refine Opens.mem_iSup.2 ⟨⟨D', fun e => hx (e ▸ hD')⟩, hD'⟩
    · intro hx hxD
      obtain ⟨D', hD'⟩ := Opens.mem_iSup.1 hx
      have := hdis D'.2
      have hm : x ∈ W D'.1 ⊓ W D := ⟨hD', hxD⟩
      rw [this] at hm
      exact hm
  rw [← isOpen_compl_iff, hc]
  exact Opens.isOpen _

end GlobalTheory.CompanionTheory.Gaga

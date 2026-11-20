import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGroupRelDimGeneric
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteNormalCoverGenericPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionTwoTorsionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusKernelTrivialOpenStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwoTorsionSpreadOpenStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwoTorsionCardBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionRankBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteSurjectiveOpenImageStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionSplitMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.StratOpen

/- English proof (translation)
The claim follows from `(RingHom.charZero_iff (Spec.preimage x).hom.injective).1 inferInstance`.
-/
theorem charZero_of_point {k : Type} [Field k] (x : Sp k ⟶ Sp ℚ) : CharZero k :=
  (RingHom.charZero_iff (Spec.preimage x).hom.injective).1 inferInstance

/- English proof (translation)
Establish `hsm` using `hG.smooth`. Establish `hsep` using `hG.separated`. Establish `hG' : IsSemiAbelian ((Over.pullback π).obj G)` using `IsSemiAbelian.pullback π G hG`. Establish `hsep'` using `hG'.separated`. Establish `hLN : IsLocallyNoetherian Z'` using `LocallyOfFiniteType.isLocallyNoetherian π`.

Establish `hCS : CompactSpace Z'` using `QuasiCompact.compactSpace_of_compactSpace π`. Establish `hN' : AlgebraicGeometry.IsNoetherian Z'` using `{}`. Set `τ' : TorusExtension ((Over.pullback j).obj ((Over.pullback π).obj G))` to `torusExtOfIso (pullCompIso j π G) τ`. Use `letI := τ'.addCommGroup`. Use `haveI := τ'.free`.

Use `haveI := τ'.finite`. Take `⟨u, hu, hmono⟩` from `GlobalTheory.T.torus_extension_split_map hE Z' hnorm ((Over.pullback π).obj G) hG' L' j hj τ'`. Take `⟨V₁, hV₁, hC⟩` from `GlobalTheory.T.torus_kernel_trivial_open Z' ((Over.pullback π).obj G) τ'.X u L' j hj hmono`. Take `⟨V₂, hV₂, hD⟩` from `GlobalTheory.T.two_torsion_spread_open Z' Z π G L' j hj m P hPi hP2`. Establish `hVne : ((V₁ ⊓ V₂ : Z'.Opens) : Set Z').Nonempty` using `nonempty_preirreducible_inter V₁.isOpen V₂.isOpen hV₁ hV₂`.

Take `⟨U, hU, hUV⟩` from `GlobalTheory.T.finite_surjective_open_image Z Z' π hfin hsurj (V₁ ⊓ V₂) hVne`. Establish `hm : 0 < m`. Break down `Nat.eq_zero_or_pos m with rfl | h` into its components or cases. Conclude with `absurd hcount.symm (by simp)`. Conclude with `h`.

Use `⟨Z', inferInstance, π, (Over.pullback π).obj G, inferInstance, pullback.fst G.hom π, τ'.X, τ'.addCommGroup, τ'.free, τ'.finite, u, U, hfin, hsurj, hnorm, isGrpPullback_pullback G π, hu, hU, ?_⟩` and prove the remaining obligations. Introduce `k _ x hx`. Establish `hxV : ∀ W : Z'.Opens, V₁ ⊓ V₂ ≤ W → ⊤ ≤ x ⁻¹ᵁ W` using `fun W hW y _ => hW (hUV (hx trivial))`. Establish `mono : ∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' τ'.X), t ≫ u = 1 → t = 1`. Introduce `A _ g t ht`.

Use `hC A (spMap g ≫ x) (fun y _ => ?_) t ht` and prove the remaining obligations. Establish `h1` using `hxV V₁ inf_le_left (show (spMap g) y ∈ (⊤ : (Sp k).Opens) from trivial)`. Simplify using `using h1`. Use `⟨mono, ?_⟩` and prove the remaining obligations. Introduce `Gk _ ψ hψ τk`.

Use `letI := τk.grpB`. Use `letI := τk.addCommGroup`. Use `haveI := τk.free`. Use `haveI := τk.finite`. Take `⟨Q, hQi, hQ2⟩` from `hD k x (hxV V₂ inf_le_right)`.

Establish `h2 : ((2 : ℕ) : k) ≠ 0` using `by haveI : CharZero k := charZero_of_point (x ≫ π ≫ s)`. Conclude with `Nat.cast_ne_zero.2 two_ne_zero`. Establish `hle` using `GlobalTheory.T.two_torsion_card_bound Z G hG g hg k h2 (x ≫ π) Gk (ψ ≫ pullback.fst G.hom π) (hψ.comp (isGrpPullback_pullback G π)) τk m Q hQi hQ2`. Establish `hrk : Module.finrank ℤ τk.X ≤ Module.finrank ℤ τ'.X`. Establish `h3 : m * 2 ^ Module.finrank ℤ τk.X ≤ m * 2 ^ Module.finrank ℤ τ'.X` using `hle.trans hcount.ge`.

Conclude with `(Nat.pow_le_pow_iff_right (by norm_num)).1 (Nat.le_of_mul_le_mul_left h3 hm)`. Introduce `A _ gg p`. Conclude with `GlobalTheory.T.torus_extension_rank_bound Z' ((Over.pullback π).obj G) τ'.X u k x mono Gk ψ hψ τk hrk A gg p`.
-/
theorem core (hE : GlobalTheory.Published.SemiAbelianHomExtension) (Z : Scheme.{0}) [IsIntegral Z] [AlgebraicGeometry.IsNoetherian Z]
    (s : Z ⟶ Sp ℚ) (G : Over Z) [GrpObj G] (hG : IsSemiAbelian G) (g : ℕ) (hg : SmoothOfRelativeDimension g G.hom)
    (Z' : Scheme.{0}) [IsIntegral Z'] (π : Z' ⟶ Z) (hfin : IsFinite π) (hsurj : Surjective π) (hnorm : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z')
    (L' : Type) [Field L'] (j : Sp L' ⟶ Z') (hj : GlobalTheory.IsGenericPointHom j)
    (τ : TorusExtension ((Over.pullback (j ≫ π)).obj G)) (m : ℕ) (P : Fin m → (Over.mk (j ≫ π) ⟶ G))
    (hPi : Function.Injective P) (hP2 : ∀ i, P i ^ 2 = 1)
    (hcount : letI := τ.addCommGroup; m * 2 ^ Module.finrank ℤ τ.X = 2 ^ (2 * g)) :
    ∃ (Z' : Scheme.{0}) (_ : IsIntegral Z') (π : Z' ⟶ Z) (G' : Over Z') (_ : GrpObj G') (φ : G'.left ⟶ G.left) (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (u : splitTorus Z' X ⟶ G') (U : Z.Opens), IsFinite π ∧ Surjective π ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z' ∧ IsGrpPullback G' G π φ ∧ IsMonHom u ∧ (U : Set Z).Nonempty ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ Z'), ⊤ ≤ (x ≫ π) ⁻¹ᵁ U → (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' X), t ≫ u = 1 → t = 1) ∧ ∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G'.left), IsGrpPullback Gk G' x ψ → ∀ τ : TorusExtension Gk, letI := τ.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk), p ≫ τ.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' X, (t ≫ u).left = p.left ≫ ψ := by
  have hsm := hG.smooth
  have hsep := hG.separated
  have hG' : IsSemiAbelian ((Over.pullback π).obj G) := IsSemiAbelian.pullback π G hG
  have hsep' := hG'.separated
  have hLN : IsLocallyNoetherian Z' := LocallyOfFiniteType.isLocallyNoetherian π
  have hCS : CompactSpace Z' := QuasiCompact.compactSpace_of_compactSpace π
  have hN' : AlgebraicGeometry.IsNoetherian Z' := {}
  let τ' : TorusExtension ((Over.pullback j).obj ((Over.pullback π).obj G)) := torusExtOfIso (pullCompIso j π G) τ
  letI := τ'.addCommGroup
  haveI := τ'.free
  haveI := τ'.finite
  obtain ⟨u, hu, hmono⟩ := GlobalTheory.T.torus_extension_split_map hE Z' hnorm ((Over.pullback π).obj G) hG' L' j hj τ'
  obtain ⟨V₁, hV₁, hC⟩ := GlobalTheory.T.torus_kernel_trivial_open Z' ((Over.pullback π).obj G) τ'.X u L' j hj hmono
  obtain ⟨V₂, hV₂, hD⟩ := GlobalTheory.T.two_torsion_spread_open Z' Z π G L' j hj m P hPi hP2
  have hVne : ((V₁ ⊓ V₂ : Z'.Opens) : Set Z').Nonempty :=
    nonempty_preirreducible_inter V₁.isOpen V₂.isOpen hV₁ hV₂
  obtain ⟨U, hU, hUV⟩ := GlobalTheory.T.finite_surjective_open_image Z Z' π hfin hsurj (V₁ ⊓ V₂) hVne
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exact absurd hcount.symm (by simp)
    · exact h
  refine ⟨Z', inferInstance, π, (Over.pullback π).obj G, inferInstance, pullback.fst G.hom π, τ'.X, τ'.addCommGroup, τ'.free, τ'.finite, u, U, hfin, hsurj, hnorm, isGrpPullback_pullback G π, hu, hU, ?_⟩
  intro k _ x hx
  have hxV : ∀ W : Z'.Opens, V₁ ⊓ V₂ ≤ W → ⊤ ≤ x ⁻¹ᵁ W := fun W hW y _ => hW (hUV (hx trivial))
  have mono : ∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' τ'.X), t ≫ u = 1 → t = 1 := by
    intro A _ g t ht
    refine hC A (spMap g ≫ x) (fun y _ => ?_) t ht
    have h1 := hxV V₁ inf_le_left (show (spMap g) y ∈ (⊤ : (Sp k).Opens) from trivial)
    simpa using h1
  refine ⟨mono, ?_⟩
  intro Gk _ ψ hψ τk
  letI := τk.grpB
  letI := τk.addCommGroup
  haveI := τk.free
  haveI := τk.finite
  obtain ⟨Q, hQi, hQ2⟩ := hD k x (hxV V₂ inf_le_right)
  have h2 : ((2 : ℕ) : k) ≠ 0 := by
    haveI : CharZero k := charZero_of_point (x ≫ π ≫ s)
    exact Nat.cast_ne_zero.2 two_ne_zero
  have hle := GlobalTheory.T.two_torsion_card_bound Z G hG g hg k h2 (x ≫ π) Gk (ψ ≫ pullback.fst G.hom π) (hψ.comp (isGrpPullback_pullback G π)) τk m Q hQi hQ2
  have hrk : Module.finrank ℤ τk.X ≤ Module.finrank ℤ τ'.X := by
    have h3 : m * 2 ^ Module.finrank ℤ τk.X ≤ m * 2 ^ Module.finrank ℤ τ'.X := hle.trans hcount.ge
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 (Nat.le_of_mul_le_mul_left h3 hm)
  intro A _ gg p
  exact GlobalTheory.T.torus_extension_rank_bound Z' ((Over.pullback π).obj G) τ'.X u k x mono Gk ψ hψ τk hrk A gg p

/- English proof (translation)
Introduce `hE Z _ s _ _ G _ hG`. Establish `hLN : IsLocallyNoetherian Z` using `LocallyOfFiniteType.isLocallyNoetherian s`. Establish `hCS : CompactSpace Z` using `QuasiCompact.compactSpace_of_compactSpace s`. Establish `hN : AlgebraicGeometry.IsNoetherian Z` using `{}`. Establish `hsm` using `hG.smooth`.

Establish `hsep` using `hG.separated`. Establish `hfq` using `hG.quasiCompact`. Set `z : Sp Z.functionField ⟶ Z` to `Z.fromSpecStalk (genericPoint Z)`. Establish `hz : GlobalTheory.IsGenericPointHom z` using `GlobalTheory.IsGenericPointHom.fromSpecStalk Z`. Use `haveI : CharZero Z.functionField := charZero_of_point (z ≫ s)`.

Take `⟨g, hg⟩` from `GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.smoothGrp_relDim Z Z.functionField z G (fun q => by`. Establish `: genPt z = genericPoint Z`. Use `hz.range_eq` as an intermediate fact. Establish `h2 : genPt z ∈ Set.range z` using `⟨_, rfl⟩`. Rewrite `h2` using `[this]`.

Conclude with `h2`. Rewrite using `[this]`. Conclude with `genericPoint_specializes q)`. Take `⟨L', _, _, hfd, hB⟩` from `GlobalTheory.T.torus_extension_two_torsion Z G hG g hg Z.functionField z`. Take `⟨Z', _, π, j, hfin, hsurj, hnorm, hj, hjπ⟩` from `GlobalTheory.T.finite_normal_cover_generic_point Z s Z.functionField z hz L'`.

Rewrite `hB` using `[← hjπ]`. Take `⟨τ, m, P, hPi, hP2, hcount⟩` from `hB`. Conclude with `core hE Z s G hG g hg Z' π hfin hsurj hnorm L' j hj τ m P hPi hP2 hcount`.
-/
theorem strat_open : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℚ) [LocallyOfFiniteType s] [QuasiCompact s] (G : Over Z) [GrpObj G], IsSemiAbelian G → ∃ (Z' : Scheme.{0}) (_ : IsIntegral Z') (π : Z' ⟶ Z) (G' : Over Z') (_ : GrpObj G') (φ : G'.left ⟶ G.left) (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (u : splitTorus Z' X ⟶ G') (U : Z.Opens), IsFinite π ∧ Surjective π ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z' ∧ IsGrpPullback G' G π φ ∧ IsMonHom u ∧ (U : Set Z).Nonempty ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ Z'), ⊤ ≤ (x ≫ π) ⁻¹ᵁ U → (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' X), t ≫ u = 1 → t = 1) ∧ ∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G'.left), IsGrpPullback Gk G' x ψ → ∀ τ : TorusExtension Gk, letI := τ.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk), p ≫ τ.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' X, (t ≫ u).left = p.left ≫ ψ := by
  intro hE Z _ s _ _ G _ hG
  have hLN : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian s
  have hCS : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace s
  have hN : AlgebraicGeometry.IsNoetherian Z := {}
  have hsm := hG.smooth
  have hsep := hG.separated
  have hfq := hG.quasiCompact
  let z : Sp Z.functionField ⟶ Z := Z.fromSpecStalk (genericPoint Z)
  have hz : GlobalTheory.IsGenericPointHom z := GlobalTheory.IsGenericPointHom.fromSpecStalk Z
  haveI : CharZero Z.functionField := charZero_of_point (z ≫ s)
  obtain ⟨g, hg⟩ := GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.smoothGrp_relDim Z Z.functionField z G (fun q => by
    have : genPt z = genericPoint Z := by
      have := hz.range_eq
      have h2 : genPt z ∈ Set.range z := ⟨_, rfl⟩
      rw [this] at h2
      exact h2
    rw [this]
    exact genericPoint_specializes q)
  obtain ⟨L', _, _, hfd, hB⟩ := GlobalTheory.T.torus_extension_two_torsion Z G hG g hg Z.functionField z
  obtain ⟨Z', _, π, j, hfin, hsurj, hnorm, hj, hjπ⟩ := GlobalTheory.T.finite_normal_cover_generic_point Z s Z.functionField z hz L'
  rw [← hjπ] at hB
  obtain ⟨τ, m, P, hPi, hP2, hcount⟩ := hB
  exact core hE Z s G hG g hg Z' π hfin hsurj hnorm L' j hj τ m P hPi hP2 hcount

end GlobalTheory.CompanionTheory.Ar.StratOpen

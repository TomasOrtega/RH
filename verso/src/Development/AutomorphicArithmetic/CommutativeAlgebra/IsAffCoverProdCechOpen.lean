import Mathlib
import Development.AutomorphicArithmetic.GenericGermInjectivity.CoverGeneric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericGermDifferentialFormPullbackDominantStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SchemeCechComparisonNaturalRefinementStatement

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.GenericCoverClass

/- English proof (translation)
Introduce `d Z _ p _ inst ι _ _ U B hinst hU d' Z' _ p' _ inst' κ _ _ U' B' hinst' hU' f hf ψ φ τ hDR hψ hUU' a b hm z`. Use `letI := algΓ p`. Use `letI := algΓ p'`. Establish `hσ` using `appTop_algebraMap (k := ℂ) hf`. Establish `hcov : ⨆ i, U i = ⊤` using `hU.cover`.

Establish `haff : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)` using `fun s hs => cover_biInf hU s hs`. Establish `hcov' : ⨆ i, U' i = ⊤` using `hU'.cover`. Establish `haff' : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U' i)` using `fun s hs => cover_biInf hU' s hs`. Take `⟨x, hx⟩` from `(cechClass_surjective (cechCube ℂ (Omega p a) ⊤ U) b) ((cechHEquivCoh ℂ hcov haff (Omega p a) b).symm z)`. Establish `hz : cechHEquivCoh ℂ hcov haff (Omega p a) b (cechClass (cechCube ℂ (Omega p a) ⊤ U) b x) = z`.

Rewrite using `[hx]`. Conclude with `LinearEquiv.apply_symm_apply _ _`. Take `⟨eZ, -, heZ, -⟩` from `cube_exists d p hinst hU a b`. Take `⟨w, hw⟩` from `heZ x`. Establish `hle : ∀ t : Finset κ, cechOpen ⊤ U' t ≤ f ⁻¹ᵁ cechOpen ⊤ U (Finset.image τ t)`.

Introduce `t y hy`. Rewrite `hy` using `[mem_cechOpen]`. Use `show f.base y ∈ cechOpen ⊤ U (Finset.image τ t)`. Rewrite using `[mem_cechOpen]`. Use `⟨trivial, fun i hi => ?_⟩` and prove the remaining obligations.

Take `⟨k, hk, rfl⟩` from `Finset.mem_image.mp hi`. Conclude with `hUU' k (hy.2 k hk)`. Establish `hcard : ∀ t : {s : Finset κ // s.card = b + 1}, Set.InjOn τ t.1 → (Finset.image τ t.1).card = b + 1` using `fun t hinj => (Finset.card_image_of_injOn hinj).trans t.2`. Set `x' : (cechCube ℂ (Omega p' a) ⊤ U').Term (b + 1)` to `fun t => if hinj : Set.InjOn τ t.1 then sortSign τ t.1 • sectionsOn.res ℂ (Omega p' a) (hle t.1) (sectionsOn.map ℂ (omegaPull hf a) (cechOpen ⊤ U (Finset.image τ t.1)) (x.1 ⟨_, hcard t hinj⟩)) else 0`. Establish `hwC` using `hm b w w.2.1`.

Establish `hw'mem : pullC τ φ (w : Finset ι → DR ℂ Z.functionField) ∈ (cech fun I => omB ℂ Z'.functionField (B' I) a).Z b`. Establish `hw0 : (cech fun I => omB ℂ Z.functionField (B I) a).D (w : Finset ι → DR ℂ Z.functionField) = 0` using `w.2.2`. Establish `h0 : (cech fun I => omB ℂ Z'.functionField (B' I) a).D (pullC τ φ (w : Finset ι → DR ℂ Z.functionField)) = 0`. Rewrite using `[← hwC.2, hw0, map_zero]`. Conclude with `⟨hwC.1, h0⟩`.

Set `w' : ↥((cech fun I => omB ℂ Z'.functionField (B' I) a).Z b)` to `⟨_, hw'mem⟩`. Establish `hgm : ∀ t : {s : Finset κ // s.card = b + 1}, (w' : Finset κ → DR ℂ Z'.functionField) t.1 = gm p' hinst' hU' a t.1 (x' t)`. Introduce `t`. Establish `ht : t.1.Nonempty` using `Finset.card_pos.mp (by rw [t.2]; omega)`. Rewrite using `[gm_pos hinst' hU' a ht]`.

Distinguish the cases in `hinj : Set.InjOn τ t.1`. Establish `hne : (Finset.image τ t.1).Nonempty` using `ht.image τ`. Establish `e1 : (w' : Finset κ → DR ℂ Z'.functionField) t.1 = sortSign τ t.1 • φ ((w : Finset ι → DR ℂ Z.functionField) (Finset.image τ t.1))` using `by show pullC τ φ (w : Finset ι → DR ℂ Z.functionField) t.1 = _`. Simplify using `only [pullC, LinearMap.coe_mk, AddHom.coe_mk, if_pos hinj]`. Rewrite using `[e1, show x' t = _ from dif_pos hinj]`.

Use `Eq.trans ?_ (map_zsmul (formGermI p' a _ _ hinst') (sortSign τ t.1) _).symm` and prove the remaining obligations. Rewrite using `[hw ⟨_, hcard t hinj⟩, gm_pos hinst hU a hne]`. Use `congr 1`. Conclude with `(T.genericGerm_differentialForm_pullback_dominant Z Z' p p' hinst hinst' f hf ψ φ hDR hψ a _ _ _ _ _ _ (hle t.1) _).symm`. Establish `e1 : (w' : Finset κ → DR ℂ Z'.functionField) t.1 = 0` using `by show pullC τ φ (w : Finset ι → DR ℂ Z.functionField) t.1 = _`.

Simplify using `only [pullC, LinearMap.coe_mk, AddHom.coe_mk, if_neg hinj]`. Rewrite using `[e1, show x' t = 0 from dif_neg hinj]`. Conclude with `(map_zero (formGermI p' a _ _ hinst')).symm`. Take `⟨eY, -, -, hdY⟩` from `cube_exists d' p' hinst' hU' a b`. Establish `hker : x' ∈ ((cechCube ℂ (Omega p' a) ⊤ U').d (b + 1)).ker` using `hdY x' w' hgm`.

Establish `hR : cechHEquivCoh ℂ hcov' haff' (Omega p' a) b (cechClass (cechCube ℂ (Omega p' a) ⊤ U') b ⟨x', hker⟩) = hodgePull hf a b z`. Use `(T.scheme_cechComparison_natural_refinement Z Z' ℂ f hσ _ _ (omegaPull hf a) ι κ U U' hcov haff hcov' haff' τ hUU' b x ⟨x', hker⟩ ?_ ?_).trans ?_` and prove the remaining obligations. Introduce `t s h hinj hs`. Take `⟨s, hsc⟩` from `s`. Simplify using `only at hs`.

Substitute `hs` using the available equality. Conclude with `dif_pos hinj`. Introduce `t hinj`. Conclude with `dif_neg hinj`. Rewrite using `[hz]`.

Both sides reduce to the same expression. Rewrite using `[← hR, cmp_class d' p' hinst' hU' a b ⟨x', hker⟩ w' hgm, ← hz, cmp_class d p hinst hU a b x w hw]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.isAffCover_prod_cechOpen :
    ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField] (ι : Type) [LinearOrder ι] [Fintype ι] (U : ι → Z.Opens) (B : Finset ι → Subalgebra ℂ Z.functionField) (hinst : inst = ffAlg p) (hU : IsAffCover p U B)
            (d' : ℕ) (Z' : Scheme.{0}) [IsIntegral Z'] (p' : Z' ⟶ Sp ℂ) [SmoothOfRelativeDimension d' p'] [inst' : Algebra ℂ Z'.functionField] (κ : Type) [LinearOrder κ] [Fintype κ] (U' : κ → Z'.Opens) (B' : Finset κ → Subalgebra ℂ Z'.functionField) (hinst' : inst' = ffAlg p') (hU' : IsAffCover p' U' B')
            (f : Z' ⟶ Z) (hf : f ≫ p = p') (ψ : Z.functionField →ₐ[ℂ] Z'.functionField) (φ : DR ℂ Z.functionField →ₗ[ℂ] DR ℂ Z'.functionField) (τ : κ → ι),
            IsDRMap ℂ ψ φ → (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Z' ∈ f ⁻¹ᵁ V) (g : Γ(Z, V)), ψ ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Z'.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Z') hV').hom (f.app V g)) → (∀ k, U' k ≤ f ⁻¹ᵁ U (τ k)) →
            ∀ (a b : ℕ) (hm : IsMap (cech fun I => omB ℂ Z.functionField (B I) a) (cech fun I => omB ℂ Z'.functionField (B' I) a) (pullC τ φ)) (z : hodgeH p a b),
              cmp d' p' hinst' hU' a b (hodgePull hf a b z) = Cx.hmap _ _ (pullC τ φ) hm b (cmp d p hinst hU a b z) := by
  classical
  intro d Z _ p _ inst ι _ _ U B hinst hU d' Z' _ p' _ inst' κ _ _ U' B' hinst' hU' f hf ψ φ τ hDR hψ hUU' a b hm z
  letI := algΓ p
  letI := algΓ p'
  have hσ := appTop_algebraMap (k := ℂ) hf
  have hcov : ⨆ i, U i = ⊤ := hU.cover
  have haff : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i) := fun s hs => cover_biInf hU s hs
  have hcov' : ⨆ i, U' i = ⊤ := hU'.cover
  have haff' : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U' i) := fun s hs => cover_biInf hU' s hs
  obtain ⟨x, hx⟩ := (cechClass_surjective (cechCube ℂ (Omega p a) ⊤ U) b)
    ((cechHEquivCoh ℂ hcov haff (Omega p a) b).symm z)
  have hz : cechHEquivCoh ℂ hcov haff (Omega p a) b (cechClass (cechCube ℂ (Omega p a) ⊤ U) b x) = z := by
    rw [hx]
    exact LinearEquiv.apply_symm_apply _ _
  obtain ⟨eZ, -, heZ, -⟩ := cube_exists d p hinst hU a b
  obtain ⟨w, hw⟩ := heZ x
  have hle : ∀ t : Finset κ, cechOpen ⊤ U' t ≤ f ⁻¹ᵁ cechOpen ⊤ U (Finset.image τ t) := by
    intro t y hy
    rw [mem_cechOpen] at hy
    show f.base y ∈ cechOpen ⊤ U (Finset.image τ t)
    rw [mem_cechOpen]
    refine ⟨trivial, fun i hi => ?_⟩
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
    exact hUU' k (hy.2 k hk)
  have hcard : ∀ t : {s : Finset κ // s.card = b + 1}, Set.InjOn τ t.1 → (Finset.image τ t.1).card = b + 1 :=
    fun t hinj => (Finset.card_image_of_injOn hinj).trans t.2
  let x' : (cechCube ℂ (Omega p' a) ⊤ U').Term (b + 1) := fun t =>
    if hinj : Set.InjOn τ t.1 then
      sortSign τ t.1 • sectionsOn.res ℂ (Omega p' a) (hle t.1)
        (sectionsOn.map ℂ (omegaPull hf a) (cechOpen ⊤ U (Finset.image τ t.1)) (x.1 ⟨_, hcard t hinj⟩))
    else 0
  have hwC := hm b w w.2.1
  have hw'mem : pullC τ φ (w : Finset ι → DR ℂ Z.functionField) ∈
      (cech fun I => omB ℂ Z'.functionField (B' I) a).Z b := by
    have hw0 : (cech fun I => omB ℂ Z.functionField (B I) a).D (w : Finset ι → DR ℂ Z.functionField) = 0 :=
      w.2.2
    have h0 : (cech fun I => omB ℂ Z'.functionField (B' I) a).D (pullC τ φ (w : Finset ι → DR ℂ Z.functionField)) = 0 := by
      rw [← hwC.2, hw0, map_zero]
    exact ⟨hwC.1, h0⟩
  let w' : ↥((cech fun I => omB ℂ Z'.functionField (B' I) a).Z b) := ⟨_, hw'mem⟩
  have hgm : ∀ t : {s : Finset κ // s.card = b + 1},
      (w' : Finset κ → DR ℂ Z'.functionField) t.1 = gm p' hinst' hU' a t.1 (x' t) := by
    intro t
    have ht : t.1.Nonempty := Finset.card_pos.mp (by rw [t.2]; omega)
    rw [gm_pos hinst' hU' a ht]
    by_cases hinj : Set.InjOn τ t.1
    · have hne : (Finset.image τ t.1).Nonempty := ht.image τ
      have e1 : (w' : Finset κ → DR ℂ Z'.functionField) t.1 =
          sortSign τ t.1 • φ ((w : Finset ι → DR ℂ Z.functionField) (Finset.image τ t.1)) := by
        show pullC τ φ (w : Finset ι → DR ℂ Z.functionField) t.1 = _
        simp only [pullC, LinearMap.coe_mk, AddHom.coe_mk, if_pos hinj]
      rw [e1, show x' t = _ from dif_pos hinj]
      refine Eq.trans ?_ (map_zsmul (formGermI p' a _ _ hinst') (sortSign τ t.1) _).symm
      rw [hw ⟨_, hcard t hinj⟩, gm_pos hinst hU a hne]
      congr 1
      exact (T.genericGerm_differentialForm_pullback_dominant Z Z' p p' hinst hinst' f hf ψ φ hDR hψ a _ _ _ _ _ _ (hle t.1) _).symm
    · have e1 : (w' : Finset κ → DR ℂ Z'.functionField) t.1 = 0 := by
        show pullC τ φ (w : Finset ι → DR ℂ Z.functionField) t.1 = _
        simp only [pullC, LinearMap.coe_mk, AddHom.coe_mk, if_neg hinj]
      rw [e1, show x' t = 0 from dif_neg hinj]
      exact (map_zero (formGermI p' a _ _ hinst')).symm
  obtain ⟨eY, -, -, hdY⟩ := cube_exists d' p' hinst' hU' a b
  have hker : x' ∈ ((cechCube ℂ (Omega p' a) ⊤ U').d (b + 1)).ker := hdY x' w' hgm
  have hR : cechHEquivCoh ℂ hcov' haff' (Omega p' a) b
      (cechClass (cechCube ℂ (Omega p' a) ⊤ U') b ⟨x', hker⟩) = hodgePull hf a b z := by
    refine (T.scheme_cechComparison_natural_refinement Z Z' ℂ f hσ _ _ (omegaPull hf a) ι κ U U' hcov haff hcov' haff' τ hUU' b x
      ⟨x', hker⟩ ?_ ?_).trans ?_
    · intro t s h hinj hs
      obtain ⟨s, hsc⟩ := s
      simp only at hs
      subst hs
      exact dif_pos hinj
    · intro t hinj
      exact dif_neg hinj
    · rw [hz]
      rfl
  rw [← hR, cmp_class d' p' hinst' hU' a b ⟨x', hker⟩ w' hgm, ← hz, cmp_class d p hinst hU a b x w hw]
  rfl

import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareZeroNeighbourhoodAffineStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareZeroNeighbourhoodProductZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealSquareLeKernelOfSquareZeroMapStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedImmersionUniversalSquareZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VectorBundleOfLocalFreenessStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CotangentLocalOpenChartExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLocalChartAtPrimeStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.Cot

/- English proof (translation)
The claim follows from `congrArg CommRingCat.Hom.hom (Spec.map_injective h)`.
-/
theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

/- English proof (translation)
Simplify using `[spMap, CommRingCat.ofHom_comp, Spec.map_comp]`.
-/
theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

/- English proof (translation)
Simplify using `[spMap]`.
-/
theorem spMap_id {A : Type} [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp [spMap]

/- English proof (translation)
Introduce `R _ X s e he`. Establish `: IsImmersion (e ≫ s)` using `by rw [he]; infer_instance`. Establish `: IsImmersion e` using `IsImmersion.of_comp e s`. Set `U` to `e.coborderRange`. Set `e' : Sp R ⟶ U` to `e.liftCoborder`.

Establish `he' : e' ≫ U.ι = e` using `e.liftCoborder_ι`. Set `t : (U : Scheme.{0}) ⟶ Sp R` to `U.ι ≫ s`. Establish `het : e' ≫ t = 𝟙 _` using `by simp only [t]; rw [← Category.assoc, he', he]`. Establish `hE : IsAffine (e'.ker ^ 2).subscheme` using `GlobalTheory.T.square_zero_neighbourhood_affine R U t e' het`. Set `c` to `(e'.ker ^ 2).subschemeι`.

Establish `hle : c.ker ≤ e'.ker`. Simplify using `only [c, Scheme.IdealSheafData.ker_subschemeι]`. Conclude with `pow_le_of_le_one zero_le le_top two_ne_zero`. Set `i' : Sp R ⟶ (e'.ker ^ 2).subscheme` to `IsClosedImmersion.lift c e' hle`. Establish `hi' : i' ≫ c = e'` using `IsClosedImmersion.lift_fac _ _ _`.

Set `E` to `(e'.ker ^ 2).subscheme`. Set `P : Type` to `Γ(E, ⊤)`. Set `iso : E ≅ Sp P` to `E.isoSpec`. Set `j : Sp P ⟶ X` to `iso.inv ≫ c ≫ U.ι`. Set `α : R →+* P` to `(Spec.preimage (iso.inv ≫ c ≫ t)).hom`.

Set `ε : P →+* R` to `(Spec.preimage (i' ≫ iso.hom)).hom`. Establish `hα : spMap α = iso.inv ≫ c ≫ t` using `Spec.map_preimage _`. Establish `hε : spMap ε = i' ≫ iso.hom` using `Spec.map_preimage _`. Establish `hjs : j ≫ s = spMap α` using `by simp [j, hα, t]`. Establish `hεj : spMap ε ≫ j = e`.

Simplify using `only [hε, j, Category.assoc, Iso.hom_inv_id_assoc]`. Rewrite using `[← Category.assoc i', hi', he']`. Use `⟨P, inferInstance, α, ε, j, ?_, ?_, hjs, hεj, inferInstance, ?_⟩` and prove the remaining obligations. Apply `spMap_inj` to reduce the goal to its premises. Rewrite using `[spMap_comp, hε, hα, spMap_id]`.

Simplify using `only [Category.assoc, Iso.hom_inv_id_assoc]`. Rewrite using `[← Category.assoc i', hi', het]`. Establish `h0 : CommRingCat.ofHom ε = i'.appTop ≫ (Scheme.ΓSpecIso (.of R)).hom`. Establish `h1 : (spMap ε).appTop = (Scheme.ΓSpecIso (.of P)).hom ≫ i'.appTop`. Rewrite using `[hε, Scheme.Hom.comp_appTop]`.

Simplify using `only [iso, Scheme.isoSpec, asIso_hom]`. Conclude with `congrArg (fun f ↦ f ≫ i'.appTop) (Scheme.toSpecΓ_appTop E)`. Establish `h2` using `Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ε)`. Rewrite `h2` using `[h1, Category.assoc]`. Conclude with `((cancel_epi _).1 h2).symm`.

Establish `hk : ∀ a : P, ε a = 0 → i'.appTop a = 0` using `fun a ha ↦ by`. Establish `h3 : (Scheme.ΓSpecIso (.of R)).hom (i'.appTop a) = 0`. Use `congrArg (fun f ↦ f.hom a) h0` as an intermediate fact. Simplify `this.symm` using `[ha]`. Conclude with `(map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom).1).1 h3`.

Introduce `a b ha hb`. Conclude with `GlobalTheory.T.square_zero_neighbourhood_product_zero R U e' i' hi' a b (hk a ha) (hk b hb)`. Introduce `Q B _ _ q ρ y hq hsq hy`. Establish `hsurj : Function.Surjective (spMap q)`. Introduce `x`.

Establish `hx : x ∈ Set.range (PrimeSpectrum.comap q)`. Rewrite using `[range_comap_of_surjective _ _ hq]`. Introduce `a ha`. Establish `: a * a = 0` using `hsq a a ha ha`. Conclude with `x.2.mem_or_mem (by simp [this] : a * a ∈ x.asIdeal) |>.elim id id`.

Conclude with `hx`. Establish `hr : Set.range y ⊆ Set.range U.ι`. Introduce and unpack `_ ⟨x, rfl⟩`. Take `⟨x', rfl⟩` from `hsurj x`. Establish `h1 : y (spMap q x') = e (spMap ρ x')`.

Rewrite using `[← Scheme.Hom.comp_apply, hy, Scheme.Hom.comp_apply]`. Rewrite using `[h1, ← he', Scheme.Hom.comp_apply]`. Conclude with `⟨_, rfl⟩`. Set `y' : Sp Q ⟶ U` to `IsOpenImmersion.lift U.ι y hr`. Establish `hy' : y' ≫ U.ι = y` using `IsOpenImmersion.lift_fac _ _ _`.

Establish `hy2 : spMap q ≫ y' = spMap ρ ≫ e'`. Rewrite using `[← cancel_mono U.ι, Category.assoc, hy', hy, Category.assoc, he']`. Establish `hk : c.ker ≤ y'.ker`. Simplify using `only [c, Scheme.IdealSheafData.ker_subschemeι]`. Conclude with `GlobalTheory.T.ideal_square_le_kernel_of_square_zero_map R Q B U e' q ρ y' hq hsq hy2`.

Set `w : Sp Q ⟶ E` to `IsClosedImmersion.lift c y' hk`. Establish `hw : w ≫ c = y'` using `IsClosedImmersion.lift_fac _ _ _`. Use `⟨(Spec.preimage (w ≫ iso.hom)).hom, ?_⟩` and prove the remaining obligations. Establish `: spMap (Spec.preimage (w ≫ iso.hom)).hom = w ≫ iso.hom` using `Spec.map_preimage _`. Rewrite using `[this]`.

Simplify using `only [j, Category.assoc, Iso.hom_inv_id_assoc]`. Rewrite using `[← Category.assoc w, hw, hy']`.
-/
theorem exists_nbhd : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (e : Sp R ⟶ X), e ≫ s = 𝟙 _ → ∃ (P : Type) (_ : CommRing P) (α : R →+* P) (ε : P →+* R) (j : Sp P ⟶ X), ε.comp α = RingHom.id R ∧ (∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0) ∧ j ≫ s = spMap α ∧ spMap ε ≫ j = e ∧ Mono j ∧ ∀ (Q B : Type) [CommRing Q] [CommRing B] (q : Q →+* B) (ρ : R →+* B) (y : Sp Q ⟶ X), Function.Surjective q → (∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) → spMap q ≫ y = spMap ρ ≫ e → ∃ φ : P →+* Q, spMap φ ≫ j = y := by
  intro R _ X s e he
  have : IsImmersion (e ≫ s) := by rw [he]; infer_instance
  have : IsImmersion e := IsImmersion.of_comp e s
  let U := e.coborderRange
  let e' : Sp R ⟶ U := e.liftCoborder
  have he' : e' ≫ U.ι = e := e.liftCoborder_ι
  let t : (U : Scheme.{0}) ⟶ Sp R := U.ι ≫ s
  have het : e' ≫ t = 𝟙 _ := by simp only [t]; rw [← Category.assoc, he', he]
  have hE : IsAffine (e'.ker ^ 2).subscheme := GlobalTheory.T.square_zero_neighbourhood_affine R U t e' het
  let c := (e'.ker ^ 2).subschemeι
  have hle : c.ker ≤ e'.ker := by
    simp only [c, Scheme.IdealSheafData.ker_subschemeι]
    exact pow_le_of_le_one zero_le le_top two_ne_zero
  let i' : Sp R ⟶ (e'.ker ^ 2).subscheme := IsClosedImmersion.lift c e' hle
  have hi' : i' ≫ c = e' := IsClosedImmersion.lift_fac _ _ _
  let E := (e'.ker ^ 2).subscheme
  let P : Type := Γ(E, ⊤)
  let iso : E ≅ Sp P := E.isoSpec
  let j : Sp P ⟶ X := iso.inv ≫ c ≫ U.ι
  let α : R →+* P := (Spec.preimage (iso.inv ≫ c ≫ t)).hom
  let ε : P →+* R := (Spec.preimage (i' ≫ iso.hom)).hom
  have hα : spMap α = iso.inv ≫ c ≫ t := Spec.map_preimage _
  have hε : spMap ε = i' ≫ iso.hom := Spec.map_preimage _
  have hjs : j ≫ s = spMap α := by simp [j, hα, t]
  have hεj : spMap ε ≫ j = e := by
    simp only [hε, j, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc i', hi', he']
  refine ⟨P, inferInstance, α, ε, j, ?_, ?_, hjs, hεj, inferInstance, ?_⟩
  · apply spMap_inj
    rw [spMap_comp, hε, hα, spMap_id]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc i', hi', het]
  · have h0 : CommRingCat.ofHom ε = i'.appTop ≫ (Scheme.ΓSpecIso (.of R)).hom := by
      have h1 : (spMap ε).appTop = (Scheme.ΓSpecIso (.of P)).hom ≫ i'.appTop := by
        rw [hε, Scheme.Hom.comp_appTop]
        simp only [iso, Scheme.isoSpec, asIso_hom]
        exact congrArg (fun f ↦ f ≫ i'.appTop) (Scheme.toSpecΓ_appTop E)
      have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ε)
      rw [h1, Category.assoc] at h2
      exact ((cancel_epi _).1 h2).symm
    have hk : ∀ a : P, ε a = 0 → i'.appTop a = 0 := fun a ha ↦ by
      have h3 : (Scheme.ΓSpecIso (.of R)).hom (i'.appTop a) = 0 := by
        have := congrArg (fun f ↦ f.hom a) h0
        simpa [ha] using this.symm
      exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom).1).1 h3
    intro a b ha hb
    exact GlobalTheory.T.square_zero_neighbourhood_product_zero R U e' i' hi' a b (hk a ha) (hk b hb)
  · intro Q B _ _ q ρ y hq hsq hy
    have hsurj : Function.Surjective (spMap q) := by
      intro x
      have hx : x ∈ Set.range (PrimeSpectrum.comap q) := by
        rw [range_comap_of_surjective _ _ hq]
        intro a ha
        have : a * a = 0 := hsq a a ha ha
        exact x.2.mem_or_mem (by simp [this] : a * a ∈ x.asIdeal) |>.elim id id
      exact hx
    have hr : Set.range y ⊆ Set.range U.ι := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨x', rfl⟩ := hsurj x
      have h1 : y (spMap q x') = e (spMap ρ x') := by
        rw [← Scheme.Hom.comp_apply, hy, Scheme.Hom.comp_apply]
      rw [h1, ← he', Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    let y' : Sp Q ⟶ U := IsOpenImmersion.lift U.ι y hr
    have hy' : y' ≫ U.ι = y := IsOpenImmersion.lift_fac _ _ _
    have hy2 : spMap q ≫ y' = spMap ρ ≫ e' := by
      rw [← cancel_mono U.ι, Category.assoc, hy', hy, Category.assoc, he']
    have hk : c.ker ≤ y'.ker := by
      simp only [c, Scheme.IdealSheafData.ker_subschemeι]
      exact GlobalTheory.T.ideal_square_le_kernel_of_square_zero_map R Q B U e' q ρ y' hq hsq hy2
    let w : Sp Q ⟶ E := IsClosedImmersion.lift c y' hk
    have hw : w ≫ c = y' := IsClosedImmersion.lift_fac _ _ _
    refine ⟨(Spec.preimage (w ≫ iso.hom)).hom, ?_⟩
    have : spMap (Spec.preimage (w ≫ iso.hom)).hom = w ≫ iso.hom := Spec.map_preimage _
    rw [this]
    simp only [j, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc w, hw, hy']

/- English proof (translation)
Introduce `R _ X s e g he hs`. Take `⟨P, _, α, ε, j, h1, h2, h3, h4, h5, h6⟩` from `exists_nbhd R X s e he`. Take `⟨W, i1, i2, i3, i4, y₀, hy⟩` from `GlobalTheory.T.closed_immersion_universal_square_zero R X s e P α ε j h1 h2 h3 h4 h5 h6`. Use `⟨W, i1, i2, i3, i4, y₀, GlobalTheory.T.vector_bundle_of_local_freeness R W g fun p ↦ ?_, hy⟩` and prove the remaining obligations. Take `⟨r, A, C, _, _, _, _, j, k, hr, _, _, hjs, hε, f1, f2, f3⟩` from `GlobalTheory.T.exists_local_chart_at_prime R X s e g he hs p`.

Take `⟨E⟩` from `GlobalTheory.T.cotangent_local_open_chart_exists R X s e he W y₀ hy r A C j k hjs hε`. Establish `: Nontrivial (Localization.Away r)`. Use `⟨⟨algebraMap R _ 1, algebraMap R _ 0, fun h ↦ ?_⟩⟩` and prove the remaining obligations. Take `⟨⟨_, n, rfl⟩, hc⟩` from `(IsLocalization.eq_iff_exists (Submonoid.powers r) _).1 h`. Establish `h0 : r ^ n ∈ p.asIdeal`.

Establish `: r ^ n = 0` using `by simpa using hc`. Rewrite using `[this]`. Conclude with `zero_mem _`. Conclude with `hr (p.2.mem_of_pow_mem n h0)`. Establish `: Nontrivial A` using `(algebraMap A (Localization.Away r)).domain_nontrivial`.

Establish `hf : Module.Free (Localization.Away r) (Localization.Away r ⊗[R] W)` using `Module.Free.of_equiv E.symm`. Establish `hn : Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] W)` using `Module.Finite.equiv E.symm`. Conclude with `⟨r, hr, hf, hn, by rw [E.finrank_eq, Module.finrank_baseChange, f3]⟩`.
-/
theorem cotSt : CotSt := by
  intro R _ X s e g he hs
  obtain ⟨P, _, α, ε, j, h1, h2, h3, h4, h5, h6⟩ := exists_nbhd R X s e he
  obtain ⟨W, i1, i2, i3, i4, y₀, hy⟩ := GlobalTheory.T.closed_immersion_universal_square_zero R X s e P α ε j h1 h2 h3 h4 h5 h6
  refine ⟨W, i1, i2, i3, i4, y₀, GlobalTheory.T.vector_bundle_of_local_freeness R W g fun p ↦ ?_, hy⟩
  obtain ⟨r, A, C, _, _, _, _, j, k, hr, _, _, hjs, hε, f1, f2, f3⟩ := GlobalTheory.T.exists_local_chart_at_prime R X s e g he hs p
  obtain ⟨E⟩ := GlobalTheory.T.cotangent_local_open_chart_exists R X s e he W y₀ hy r A C j k hjs hε
  have : Nontrivial (Localization.Away r) := by
    refine ⟨⟨algebraMap R _ 1, algebraMap R _ 0, fun h ↦ ?_⟩⟩
    obtain ⟨⟨_, n, rfl⟩, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers r) _).1 h
    have h0 : r ^ n ∈ p.asIdeal := by
      have : r ^ n = 0 := by simpa using hc
      rw [this]; exact zero_mem _
    exact hr (p.2.mem_of_pow_mem n h0)
  have : Nontrivial A := (algebraMap A (Localization.Away r)).domain_nontrivial
  have hf : Module.Free (Localization.Away r) (Localization.Away r ⊗[R] W) := Module.Free.of_equiv E.symm
  have hn : Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] W) := Module.Finite.equiv E.symm
  exact ⟨r, hr, hf, hn, by rw [E.finrank_eq, Module.finrank_baseChange, f3]⟩

end GlobalTheory.CompanionTheory.Cot

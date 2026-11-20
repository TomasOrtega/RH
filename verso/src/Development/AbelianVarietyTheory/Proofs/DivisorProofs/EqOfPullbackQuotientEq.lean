import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.EqCompSectionOfSurjectiveAppTop
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SurjectiveAppOfIsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NilRigidity

/- English proof (translation)
Establish `hsurj : Function.Surjective (Ideal.Quotient.mk I)` using `Ideal.Quotient.mk_surjective`. Establish `hmem : t ∈ PrimeSpectrum.zeroLocus (RingHom.ker (Ideal.Quotient.mk I) : Set R)`. Rewrite using `[Ideal.mk_ker]`. Introduce `x hx`. Conclude with `(@nilradical_le_prime _ _ t.asIdeal t.isPrime) (hI hx)`.

Rewrite `hmem` using `[← range_comap_of_surjective _ _ hsurj]`. Take `⟨t₀, ht₀⟩` from `hmem`. Conclude with `⟨t₀, ht₀⟩`.
-/
theorem exists_preimage_quotient {R : Type} [CommRing R] (I : Ideal R) (hI : I ≤ nilradical R) (t : Sp R) :
    ∃ t₀ : Sp (R ⧸ I), spMap (Ideal.Quotient.mk I) t₀ = t := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  have hmem : t ∈ PrimeSpectrum.zeroLocus (RingHom.ker (Ideal.Quotient.mk I) : Set R) := by
    rw [Ideal.mk_ker]
    intro x hx
    exact (@nilradical_le_prime _ _ t.asIdeal t.isPrime) (hI hx)
  rw [← range_comap_of_surjective _ _ hsurj] at hmem
  obtain ⟨t₀, ht₀⟩ := hmem
  exact ⟨t₀, ht₀⟩

/- English proof (translation)
Use `haveI := hB.proper`. Set `π` to `spMap (Ideal.Quotient.mk I)`. Set `c : B ⟶ B'` to `f * g⁻¹`. Set `j` to `pullback.fst B.hom π`. Set `j' : Over.mk (j ≫ B.hom) ⟶ B` to `Over.homMk j rfl`.

Establish `h1 : j' ≫ f = j' ≫ g` using `Over.OverMorphism.ext hfg`. Establish `h2 : j' ≫ c = 1`. Simplify using `only [c, MonObj.comp_mul, GrpObj.comp_inv, h1, mul_inv_cancel]`. Establish `h3 : η[B] ≫ c = 1`. Simplify using `only [c, MonObj.comp_mul, GrpObj.comp_inv, hη, mul_inv_cancel]`.

Establish `hpt : ∀ x : B.left, c.left x = (η[B'] : 𝟙_ (Over (Sp R)) ⟶ B').left (B.hom x)`. Introduce `x`. Take `⟨t₀, ht₀⟩` from `exists_preimage_quotient I hI (B.hom x)`. Take `⟨z, rfl, -⟩` from `Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback B.hom π) x t₀ ht₀.symm`. Establish `e : j ≫ c.left = (j' ≫ c).left` using `rfl`.

Rewrite using `[← Scheme.Hom.comp_apply, e, h2, Hom.one_def, Over.comp_left]`. Both sides reduce to the same expression. Establish `hη' : (η[B] : 𝟙_ (Over (Sp R)) ⟶ B).left ≫ B.hom = 𝟙 _` using `Over.w η[B]`. Establish `key : c.left = B.hom ≫ (η[B] : 𝟙_ (Over (Sp R)) ⟶ B).left ≫ c.left`. Use `Scheme.hom_ext_of_forall _ _ fun x ↦ ?_` and prove the remaining obligations.

Take `⟨V, hV, hV'⟩` from `GlobalTheory.local_rigidity B.left (Sp R) B'.left B.hom _ c.left hη' inferInstance (GlobalTheory.surjective_app_of_isAbelianScheme GlobalTheory.globalFns_holds B hB) (B.hom x) ((η[B'] : 𝟙_ (Over (Sp R)) ⟶ B').left (B.hom x)) (fun x' hx' ↦ by rw [hpt, hx'])`. Conclude with `⟨B.hom ⁻¹ᵁ V, hV, hV'⟩`. Establish `key' : c = toUnit B ≫ η[B] ≫ c` using `Over.OverMorphism.ext key`. Rewrite `key'` using `[h3, MonObj.comp_one]`. Conclude with `mul_inv_eq_one.1 key'`.
-/
theorem eq_of_eq_on_quotient {R : Type} [CommRing R] (I : Ideal R) (hI : I ≤ nilradical R)
    (B B' : Over (Sp R)) [GrpObj B] [GrpObj B'] (hB : IsAbelianScheme B) (f g : B ⟶ B')
    (hfg : pullback.fst B.hom (spMap (Ideal.Quotient.mk I)) ≫ f.left =
      pullback.fst B.hom (spMap (Ideal.Quotient.mk I)) ≫ g.left)
    (hη : η[B] ≫ f = η[B] ≫ g) : f = g := by
  haveI := hB.proper
  let π := spMap (Ideal.Quotient.mk I)
  let c : B ⟶ B' := f * g⁻¹
  let j := pullback.fst B.hom π
  let j' : Over.mk (j ≫ B.hom) ⟶ B := Over.homMk j rfl
  have h1 : j' ≫ f = j' ≫ g := Over.OverMorphism.ext hfg
  have h2 : j' ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, h1, mul_inv_cancel]
  have h3 : η[B] ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, hη, mul_inv_cancel]
  have hpt : ∀ x : B.left, c.left x = (η[B'] : 𝟙_ (Over (Sp R)) ⟶ B').left (B.hom x) := by
    intro x
    obtain ⟨t₀, ht₀⟩ := exists_preimage_quotient I hI (B.hom x)
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback B.hom π) x t₀ ht₀.symm
    have e : j ≫ c.left = (j' ≫ c).left := rfl
    rw [← Scheme.Hom.comp_apply, e, h2, Hom.one_def, Over.comp_left]
    rfl
  have hη' : (η[B] : 𝟙_ (Over (Sp R)) ⟶ B).left ≫ B.hom = 𝟙 _ := Over.w η[B]
  have key : c.left = B.hom ≫ (η[B] : 𝟙_ (Over (Sp R)) ⟶ B).left ≫ c.left := by
    refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_
    obtain ⟨V, hV, hV'⟩ := GlobalTheory.local_rigidity B.left (Sp R) B'.left B.hom _ c.left hη' inferInstance
      (GlobalTheory.surjective_app_of_isAbelianScheme GlobalTheory.globalFns_holds B hB) (B.hom x)
      ((η[B'] : 𝟙_ (Over (Sp R)) ⟶ B').left (B.hom x)) (fun x' hx' ↦ by rw [hpt, hx'])
    exact ⟨B.hom ⁻¹ᵁ V, hV, hV'⟩
  have key' : c = toUnit B ≫ η[B] ≫ c := Over.OverMorphism.ext key
  rw [h3, MonObj.comp_one] at key'
  exact mul_inv_eq_one.1 key'

/- English proof (translation)
Establish `hI' : I ≤ nilradical R`. Take `⟨n, hn⟩` from `hI`. Introduce `x hx`. Conclude with `⟨n, by`. Establish `: x ^ n ∈ I ^ n` using `Ideal.pow_mem_pow hx n`.

Rewrite `this` using `[hn]`. Simplify using `using this⟩`. Use `eq_of_eq_on_quotient I hI' B B' hB f g ?_ (by rw [IsMonHom.one_hom, IsMonHom.one_hom])` and prove the remaining obligations. Establish `e` using `congrArg (fun k ↦ k.left ≫ pullback.fst B'.hom (spMap (Ideal.Quotient.mk I))) h`. Simplify using `only [Over.pullback_map_left, pullback.lift_fst] at e`.

Conclude with `e`.
-/
theorem eq_of_pullback_quotient_eq {R : Type} [CommRing R] (I : Ideal R) (hI : IsNilpotent I)
    (B B' : Over (Sp R)) [GrpObj B] [GrpObj B'] (hB : IsAbelianScheme B) (f g : B ⟶ B') [IsMonHom f] [IsMonHom g]
    (h : (Over.pullback (spMap (Ideal.Quotient.mk I))).map f = (Over.pullback (spMap (Ideal.Quotient.mk I))).map g) :
    f = g := by
  have hI' : I ≤ nilradical R := by
    obtain ⟨n, hn⟩ := hI
    intro x hx
    exact ⟨n, by
      have : x ^ n ∈ I ^ n := Ideal.pow_mem_pow hx n
      rw [hn] at this
      simpa using this⟩
  refine eq_of_eq_on_quotient I hI' B B' hB f g ?_ (by rw [IsMonHom.one_hom, IsMonHom.one_hom])
  have e := congrArg (fun k ↦ k.left ≫ pullback.fst B'.hom (spMap (Ideal.Quotient.mk I))) h
  simp only [Over.pullback_map_left, pullback.lift_fst] at e
  exact e

end GlobalTheory.NilRigidity

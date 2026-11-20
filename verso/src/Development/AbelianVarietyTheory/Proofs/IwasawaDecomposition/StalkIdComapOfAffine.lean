import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishesToPullChartIffOfFlat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdlAlongEqIdealAlong

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.AnForm.R (ds_stalkId_eq_map)
open ReciprocityTheory.AnForm.R.FinalTheorems (stalkId)

namespace GlobalTheory.VanStalk

/- English proof (translation)
Rewrite using `[← hA.radical, ← hB.radical, Ideal.radical_eq_sInf, Ideal.radical_eq_sInf]`. Use `congr 1`. Use extensionality with `J`. Conclude with `⟨fun ⟨h1, h2⟩ => ⟨(h ⟨J, h2⟩).1 h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(h ⟨J, h2⟩).2 h1, h2⟩⟩`.
-/
theorem eq_of_forall_prime {R : Type*} [CommRing R] {A B : Ideal R} (hA : A.IsRadical) (hB : B.IsRadical)
    (h : ∀ q : PrimeSpectrum R, A ≤ q.asIdeal ↔ B ≤ q.asIdeal) : A = B := by
  rw [← hA.radical, ← hB.radical, Ideal.radical_eq_sInf, Ideal.radical_eq_sInf]
  congr 1
  ext J
  exact ⟨fun ⟨h1, h2⟩ => ⟨(h ⟨J, h2⟩).1 h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(h ⟨J, h2⟩).2 h1, h2⟩⟩

variable {X X' : Scheme.{0}}

/- English proof (translation)
Take `⟨_, ⟨W, hW, rfl⟩, hx, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`. Rewrite using `[ds_stalkId_eq_map _ ⟨W, hW⟩ x hx, Scheme.IdealSheafData.vanishingIdeal_ideal]`. Use `letI : Algebra Γ(X, W) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩`. Use `haveI := hW.isLocalization_stalk ⟨x, hx⟩`. Establish `hg : (X.presheaf.germ W x hx).hom = algebraMap Γ(X, W) (X.presheaf.stalk x)` using `rfl`.

Establish `hcl : IsClosed (X` using `PrimeSpectrum Γ(X, W)) (hW.fromSpec ⁻¹' (Z : Set X)) := Z.isClosed.preimage hW.fromSpec.continuous`. Rewrite using `[hg]`. Generalize the expression as in `hJ : PrimeSpectrum.vanishingIdeal (R := Γ(X, W)) (hW.fromSpec ⁻¹' (Z : Set X)) = J`. Establish `hz : PrimeSpectrum.zeroLocus (J : Set Γ(X, W)) = hW.fromSpec ⁻¹' (Z : Set X)`. Rewrite using `[← hJ, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hcl.closure_eq]`.

Both sides reduce to the same expression. Establish `hr : J.radical = J` using `hJ ▸ (PrimeSpectrum.isRadical_vanishingIdeal _).radical`. Use `⟨?_, fun q => ?_⟩` and prove the remaining obligations. Rewrite using `[← hr, IsLocalization.map_radical (hW.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl]`. Conclude with `Ideal.radical_isRadical _`.

Establish `e : X.fromSpecStalk x q = hW.fromSpec (PrimeSpectrum.comap (algebraMap Γ(X, W) (X.presheaf.stalk x)) q)`. Rewrite using `[← hW.fromSpecStalk_eq_fromSpecStalk hx]`. Both sides reduce to the same expression. Rewrite using `[e, Ideal.map_le_iff_le_comap]`. Express the relevant statement in the definitionally equal form `PrimeSpectrum.comap (algebraMap Γ(X, W) (X.presheaf.stalk x)) q ∈ hW.fromSpec ⁻¹' (Z : Set X) ↔ _`.

Rewrite using `[← hz]`. Conclude with `(PrimeSpectrum.mem_zeroLocus _ _).trans SetLike.coe_subset_coe`.
-/
theorem van_spec (Z : Closeds X) (x : X) :
    (stalkId (Scheme.IdealSheafData.vanishingIdeal Z) x).IsRadical ∧
    ∀ q : PrimeSpectrum (X.presheaf.stalk x),
      X.fromSpecStalk x q ∈ Z ↔ stalkId (Scheme.IdealSheafData.vanishingIdeal Z) x ≤ q.asIdeal := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hx, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [ds_stalkId_eq_map _ ⟨W, hW⟩ x hx, Scheme.IdealSheafData.vanishingIdeal_ideal]
  letI : Algebra Γ(X, W) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  haveI := hW.isLocalization_stalk ⟨x, hx⟩
  have hg : (X.presheaf.germ W x hx).hom = algebraMap Γ(X, W) (X.presheaf.stalk x) := rfl
  have hcl : IsClosed (X := PrimeSpectrum Γ(X, W)) (hW.fromSpec ⁻¹' (Z : Set X)) :=
    Z.isClosed.preimage hW.fromSpec.continuous
  rw [hg]
  generalize hJ : PrimeSpectrum.vanishingIdeal (R := Γ(X, W)) (hW.fromSpec ⁻¹' (Z : Set X)) = J
  have hz : PrimeSpectrum.zeroLocus (J : Set Γ(X, W)) = hW.fromSpec ⁻¹' (Z : Set X) := by
    rw [← hJ, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hcl.closure_eq]
    rfl
  have hr : J.radical = J := hJ ▸ (PrimeSpectrum.isRadical_vanishingIdeal _).radical
  refine ⟨?_, fun q => ?_⟩
  · rw [← hr, IsLocalization.map_radical (hW.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl]
    exact Ideal.radical_isRadical _
  · have e : X.fromSpecStalk x q =
        hW.fromSpec (PrimeSpectrum.comap (algebraMap Γ(X, W) (X.presheaf.stalk x)) q) := by
      rw [← hW.fromSpecStalk_eq_fromSpecStalk hx]
      rfl
    rw [e, Ideal.map_le_iff_le_comap]
    change PrimeSpectrum.comap (algebraMap Γ(X, W) (X.presheaf.stalk x)) q ∈ hW.fromSpec ⁻¹' (Z : Set X) ↔ _
    rw [← hz]
    exact (PrimeSpectrum.mem_zeroLocus _ _).trans SetLike.coe_subset_coe

end GlobalTheory.VanStalk

namespace GlobalTheory.VanStalk

variable {X X' : Scheme.{0}}

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `h` using `((van_spec Z x).2 (IsLocalRing.closedPoint _)).2 (IsLocalRing.le_maximalIdeal hne)`. Rewrite `h` using `[Scheme.fromSpecStalk_closedPoint]`. Conclude with `hx h`.
-/
theorem van_eq_top (Z : Closeds X) {x : X} (hx : x ∉ Z) :
    stalkId (Scheme.IdealSheafData.vanishingIdeal Z) x = ⊤ := by
  by_contra hne
  have h := ((van_spec Z x).2 (IsLocalRing.closedPoint _)).2 (IsLocalRing.le_maximalIdeal hne)
  rw [Scheme.fromSpecStalk_closedPoint] at h
  exact hx h

/- English proof (translation)
Establish `h` using `congrArg (fun g => g q) (Scheme.SpecMap_stalkMap_fromSpecStalk π (x := x'))`. Simplify using `only [Scheme.Hom.comp_apply] at h`. Conclude with `h.symm`.
-/
theorem fromSpecStalk_comap (π : X' ⟶ X) (x' : X') (q : PrimeSpectrum (X'.presheaf.stalk x')) :
    π (X'.fromSpecStalk x' q) = X.fromSpecStalk (π x') (PrimeSpectrum.comap (π.stalkMap x').hom q) := by
  have h := congrArg (fun g => g q) (Scheme.SpecMap_stalkMap_fromSpecStalk π (x := x'))
  simp only [Scheme.Hom.comp_apply] at h
  exact h.symm

/- English proof (translation)
Use `eq_of_forall_prime (van_spec _ _).1 (Ideal.radical_isRadical _) fun q => ?_` and prove the remaining obligations. Rewrite using `[← (van_spec _ _).2, q.isPrime.radical_le_iff, Ideal.map_le_iff_le_comap, GlobalTheory.TorRef.mem_pre, fromSpecStalk_comap]`. Conclude with `(van_spec Z (π x')).2 _`.
-/
theorem van_pre (π : X' ⟶ X) (Z : Closeds X) (x' : X') :
    stalkId (Scheme.IdealSheafData.vanishingIdeal (GlobalTheory.TorRef.pre π Z)) x' =
      ((stalkId (Scheme.IdealSheafData.vanishingIdeal Z) (π x')).map (π.stalkMap x').hom).radical := by
  refine eq_of_forall_prime (van_spec _ _).1 (Ideal.radical_isRadical _) fun q => ?_
  rw [← (van_spec _ _).2, q.isPrime.radical_le_iff, Ideal.map_le_iff_le_comap, GlobalTheory.TorRef.mem_pre,
    fromSpecStalk_comap]
  exact (van_spec Z (π x')).2 _

/- English proof (translation)
Establish `key : ∀ z : T, stalkId (Scheme.IdealSheafData.ofIdealTop ((J.ideal U).map (χ.appLE U.1 ⊤ hle).hom)) z = (stalkId J (χ z)).map (χ.stalkMap z).hom`. Introduce `z`. Establish `hz : χ z ∈ U.1` using `hle trivial`. Rewrite using `[GlobalTheory.LocM.stalkId_ofIdealTop, ds_stalkId_eq_map J U _ hz, Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc]`. Use `congr 3`.

Conclude with `T.presheaf.germ_res (homOfLE hle) z (by trivial)`. Rewrite using `[← GlobalTheory.Vanishing.eq_comap_of_stalk key, key]`.
-/
theorem stalkId_comap_of_affine {T : Scheme.{0}} [IsAffine T] (J : X.IdealSheafData) (χ : T ⟶ X)
    (U : X.affineOpens) (hle : ⊤ ≤ χ ⁻¹ᵁ U.1) (z : T) :
    stalkId (J.comap χ) z = (stalkId J (χ z)).map (χ.stalkMap z).hom := by
  have key : ∀ z : T, stalkId (Scheme.IdealSheafData.ofIdealTop ((J.ideal U).map (χ.appLE U.1 ⊤ hle).hom)) z =
      (stalkId J (χ z)).map (χ.stalkMap z).hom := by
    intro z
    have hz : χ z ∈ U.1 := hle trivial
    rw [GlobalTheory.LocM.stalkId_ofIdealTop, ds_stalkId_eq_map J U _ hz, Ideal.map_map, Ideal.map_map,
      ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE,
      Category.assoc]
    congr 3
    exact T.presheaf.germ_res (homOfLE hle) z (by trivial)
  rw [← GlobalTheory.Vanishing.eq_comap_of_stalk key, key]

/- English proof (translation)
Distinguish the cases in `hx : x' ∈ (J.comap π).support`. Take `⟨z, rfl⟩` from `GlobalTheory.Vanishing.exists_ι_eq hx`. Establish `h : stalkId J (π ((J.comap π).subschemeι z)) ≤ RingHom.ker (((J.comap π).subschemeι.stalkMap z).hom.comp (π.stalkMap ((J.comap π).subschemeι z)).hom)`. Establish `h0` using `(GlobalTheory.Vanishing.le_ker_iff_stalk ((J.comap π).subschemeι ≫ π)).1 (Scheme.IdealSheafData.le_map_comap J π) z`. Rewrite `h0` using `[Scheme.Hom.stalkMap_comp]`.

Conclude with `h0`. Rewrite `h` using `[← RingHom.comap_ker, GlobalTheory.Vanishing.ker_stalkMap]`. Conclude with `Ideal.map_le_iff_le_comap.2 h`. Rewrite using `[GlobalTheory.Vanishing.stalkId_eq_top _ hx]`. Conclude with `le_top`.
-/
theorem map_le_stalkId_comap (π : X' ⟶ X) (J : X.IdealSheafData) (x' : X') :
    (stalkId J (π x')).map (π.stalkMap x').hom ≤ stalkId (J.comap π) x' := by
  by_cases hx : x' ∈ (J.comap π).support
  · obtain ⟨z, rfl⟩ := GlobalTheory.Vanishing.exists_ι_eq hx
    have h : stalkId J (π ((J.comap π).subschemeι z)) ≤ RingHom.ker
        (((J.comap π).subschemeι.stalkMap z).hom.comp (π.stalkMap ((J.comap π).subschemeι z)).hom) := by
      have h0 := (GlobalTheory.Vanishing.le_ker_iff_stalk ((J.comap π).subschemeι ≫ π)).1
        (Scheme.IdealSheafData.le_map_comap J π) z
      rw [Scheme.Hom.stalkMap_comp] at h0
      exact h0
    rw [← RingHom.comap_ker, GlobalTheory.Vanishing.ker_stalkMap] at h
    exact Ideal.map_le_iff_le_comap.2 h
  · rw [GlobalTheory.Vanishing.stalkId_eq_top _ hx]
    exact le_top

/- English proof (translation)
Use `le_antisymm ?_ (map_le_stalkId_comap π J x')` and prove the remaining obligations. Take `⟨U, hU, hxU, -⟩` from `Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (show π x' ∈ (⊤ : X.Opens) from trivial)`. Take `⟨V₀, hV, hxV, hVU⟩` from `Opens.isBasis_iff_nbhd.1 X'.isBasis_affineOpens (show x' ∈ π ⁻¹ᵁ U from hxU)`. Set `V : X'.Opens` to `V₀`. Use `haveI : IsAffine V.toScheme := hV`.

Take `⟨z, rfl⟩ : ∃ z : V.toScheme, V.ι z = x'` from `⟨⟨x', hxV⟩, rfl⟩`. Establish `hle : ⊤ ≤ (V.ι ≫ π) ⁻¹ᵁ U` using `fun w _ => hVU w.2`. Establish `h1` using `stalkId_comap_of_affine J (V.ι ≫ π) ⟨U, hU⟩ hle z`. Rewrite `h1` using `[Scheme.IdealSheafData.comap_comp]`. Establish `h2 : (stalkId (J.comap π) (V.ι z)).map (V.ι.stalkMap z).hom ≤ ((stalkId J (π (V.ι z))).map (π.stalkMap (V.ι z)).hom).map (V.ι.stalkMap z).hom`.

Establish `h0` using `map_le_stalkId_comap V.ι (J.comap π) z`. Rewrite `h0` using `[h1, Scheme.Hom.stalkMap_comp]`. Rewrite using `[Ideal.map_map]`. Conclude with `h0`. Establish `hb : Function.Bijective (V.ι.stalkMap z).hom` using `ConcreteCategory.bijective_of_isIso _`.

Rewrite `h2` using `[Ideal.map_le_iff_le_comap, Ideal.comap_map_of_bijective _ hb]`. Then use the resulting hypothesis.
-/
theorem stalkId_comap (π : X' ⟶ X) (J : X.IdealSheafData) (x' : X') :
    stalkId (J.comap π) x' = (stalkId J (π x')).map (π.stalkMap x').hom := by
  refine le_antisymm ?_ (map_le_stalkId_comap π J x')
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show π x' ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨V₀, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.1 X'.isBasis_affineOpens
    (show x' ∈ π ⁻¹ᵁ U from hxU)
  let V : X'.Opens := V₀
  haveI : IsAffine V.toScheme := hV
  obtain ⟨z, rfl⟩ : ∃ z : V.toScheme, V.ι z = x' := ⟨⟨x', hxV⟩, rfl⟩
  have hle : ⊤ ≤ (V.ι ≫ π) ⁻¹ᵁ U := fun w _ => hVU w.2
  have h1 := stalkId_comap_of_affine J (V.ι ≫ π) ⟨U, hU⟩ hle z
  rw [Scheme.IdealSheafData.comap_comp] at h1
  have h2 : (stalkId (J.comap π) (V.ι z)).map (V.ι.stalkMap z).hom ≤
      ((stalkId J (π (V.ι z))).map (π.stalkMap (V.ι z)).hom).map (V.ι.stalkMap z).hom := by
    have h0 := map_le_stalkId_comap V.ι (J.comap π) z
    rw [h1, Scheme.Hom.stalkMap_comp] at h0
    rw [Ideal.map_map]
    exact h0
  have hb : Function.Bijective (V.ι.stalkMap z).hom := ConcreteCategory.bijective_of_isIso _
  rwa [Ideal.map_le_iff_le_comap, Ideal.comap_map_of_bijective _ hb] at h2

end GlobalTheory.VanStalk

namespace GlobalTheory.TorRef

end GlobalTheory.TorRef

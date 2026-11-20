import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.GermRegularParameters
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}

/- English proof (authored)
The point determines a proper prime of the affine section ring. If zero and one were equal, then the prime would contain one and be the whole ring. Thus the section ring is nontrivial.
-/
private theorem nontrivial_sections_of_mem (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    Nontrivial Γ(X, U) := by
  rw [← not_subsingleton_iff_nontrivial]
  intro hs
  have := hs
  have h1 : (1 : Γ(X, U)) ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    rw [Subsingleton.elim (1 : Γ(X, U)) 0]
    exact Ideal.zero_mem _
  exact (hU.primeIdealOf ⟨x, hx⟩).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

/- English proof (authored)
At a point of the support every section in the ideal vanishes, meaning the point is outside its basic open. Equivalently the section’s germ is a nonunit in the local ring and lies in its maximal ideal. Contracting the maximal ideal to the affine section ring shows that every such section belongs to the point prime.
-/
private theorem ideal_le_primeIdealOf_of_mem_support (I : X.IdealSheafData)
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (hxI : x ∈ I.support) :
    I.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h1 := (Scheme.IdealSheafData.mem_support_iff_of_mem (I := I) (U := ⟨U, hU⟩) hx).mp hxI
  rw [Scheme.mem_zeroLocus_iff] at h1
  intro f hf
  rw [← germ_mem_maximalIdeal_iff hU x hx f, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact h1 f hf ((X.mem_basicOpen f x hx).mpr hu)

/- English proof (authored)
The section ring is nonzero because the affine open contains a point. It is flat over the polynomial ring by étaleness. A nonzero flat module over the polynomial domain is torsion-free and faithful, so the polynomial algebra map is injective. Distinct coordinate variables are distinct in the polynomial ring, and their images are the chart coordinates. These images are therefore distinct.
-/
private theorem coord_injective (hU : IsAffineOpen U) (c : EtaleChart p U m)
    (x : X) (hx : x ∈ U) : Function.Injective c.coord := by
  let inst : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := c.algebra
  have : Algebra.Etale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := c.algebra_etale hU
  have : Nontrivial Γ(X, U) := nontrivial_sections_of_mem hU x hx
  have : Module.Flat (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := inferInstance
  have := Module.Flat.isTorsionFree (R := MvPolynomial (ULift.{u} (Fin m)) k) (M := Γ(X, U))
  have hinj0 : Function.Injective
      (algebraMap (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U)) :=
    FaithfulSMul.algebraMap_injective _ _
  have hinj : Function.Injective ⇑c.coordRingHom := hinj0
  intro a b hab
  have h1 : (MvPolynomial.X (ULift.up a) : MvPolynomial (ULift.{u} (Fin m)) k)
      = MvPolynomial.X (ULift.up b) := by
    apply hinj
    rw [EtaleChart.coordRingHom_X, EtaleChart.coordRingHom_X, hab]
  have h2 : (ULift.up a : ULift.{u} (Fin m)) = ULift.up b := MvPolynomial.X_injective h1
  exact congrArg ULift.down h2

/- English proof (authored)
The chosen coordinates belong to the point prime, so their germs lie in the maximal ideal. The coordinate parameter theorem supplies a list of sections of length equal to the local Krull dimension, containing all the chosen coordinate sections, whose germs generate the maximal ideal. The coordinates are distinct as sections. Choosing a position for each coordinate gives an injection into the list positions, proving the bound. For an empty choice the bound follows from nonnegativity of the dimension.
-/
theorem card_le_ringKrullDim_stalk (hU : IsAffineOpen U) (c : EtaleChart p U m)
    (x : X) (hx : x ∈ U) (J : Finset (Fin m))
    (hJ : ∀ j ∈ J, c.coord j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :
    (J.card : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := by
  classical
  obtain ⟨d, f, -, hf2, -, hd⟩ :=
    exists_sections_span_eq_maximalIdeal_with_coords hU c x hx J
      (fun j hj => (germ_mem_maximalIdeal_iff hU x hx (c.coord j)).mpr (hJ j hj))
  rw [← hd]
  rcases Finset.eq_empty_or_nonempty J with rfl | hJne
  · simp only [Finset.card_empty]
    exact_mod_cast Nat.zero_le d
  · obtain ⟨j₀, hj₀⟩ := hJne
    obtain ⟨i₀, -⟩ := hf2 j₀ hj₀
    have hch : ∀ j : Fin m, ∃ i : Fin d, j ∈ J → f i = c.coord j := by
      intro j
      by_cases hj : j ∈ J
      · obtain ⟨i, hi⟩ := hf2 j hj
        exact ⟨i, fun _ => hi⟩
      · exact ⟨i₀, fun h => absurd h hj⟩
    choose g hg using hch
    have hmap : ∀ a ∈ J, g a ∈ (Finset.univ : Finset (Fin d)) := fun a _ => Finset.mem_univ _
    have hinjOn : Set.InjOn g (J : Set (Fin m)) := by
      intro a ha b hb hab
      have h1 : c.coord a = c.coord b := by
        rw [← hg a (Finset.mem_coe.mp ha), ← hg b (Finset.mem_coe.mp hb), hab]
      exact coord_injective hU c x hx h1
    have hcard : J.card ≤ (Finset.univ : Finset (Fin d)).card :=
      Finset.card_le_card_of_injOn g hmap hinjOn
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    exact_mod_cast hcard

/- English proof (authored)
The section ideal on the affine chart is generated by the specified coordinate, so it contains that coordinate. Since the point belongs to the support, its prime contains the whole section ideal. It therefore contains the coordinate.
-/
theorem coord_mem_primeIdealOf_of_restrictIdeal_eq_coordIdeal_singleton
    (hU : IsAffineOpen U) (c : EtaleChart p U m)
    (j : Fin m) (D : X.IdealSheafData) (hD : restrictIdeal D U = c.coordIdeal {j})
    (x : X) (hx : x ∈ U) (hxD : x ∈ D.support) :
    c.coord j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h1 : D.ideal ⟨U, hU⟩ = Ideal.span (c.coord '' ((({j} : Finset (Fin m))) : Set (Fin m))) :=
    EtaleChart.ideal_eq_span_coord c hU D {j} hD
  have h2 : D.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    ideal_le_primeIdealOf_of_mem_support D hU hx hxD
  refine h2 ?_
  rw [h1]
  exact Ideal.subset_span ⟨j, by simp, rfl⟩

end FunctorialResolution.EmbeddedResolution

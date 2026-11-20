import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.GenFibre

/- English proof (translation)
Use `(isNoetherianRing_iff_ideal_fg B).2 fun J => ?_` and prove the remaining obligations. Establish `e : (J.comap f).map f = J`. Use `le_antisymm Ideal.map_comap_le fun b hb => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Establish `hne : ((J.comap f).map f).colon {b} ≠ ⊤` using `fun h => hn (by`.

Establish `h1 : (1 : B) ∈ ((J.comap f).map f).colon {b}` using `h ▸ Submodule.mem_top`. Simplify using `using Submodule.mem_colon_singleton.1 h1)`. Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal _ hne`. Take `⟨x, r, c, hc, hr, hx⟩` from `RingHom.surjectiveOnStalks_iff_forall_maximal'.1 hf P hP b`. Set `p : PrimeSpectrum B` to `⟨P, hP.isPrime⟩`.

Take `⟨U, hU, hUc⟩` from `hi.isOpen_iff.1 (PrimeSpectrum.basicOpen c).isOpen`. Establish `hpU : PrimeSpectrum.comap f p ∈ U`. Establish `: p ∈ PrimeSpectrum.comap f ⁻¹' U` using `hUc ▸ hc`. Conclude with `this`. Take `⟨_, ⟨a, rfl⟩, ha, haU⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpU hU`.

Establish `hac : PrimeSpectrum.basicOpen (f a) ≤ PrimeSpectrum.basicOpen c` using `fun q hq => by`. Establish `: q ∈ PrimeSpectrum.comap f ⁻¹' U` using `haU hq`. Conclude with `hUc.subset this`. Take `⟨n, hn⟩` from `(PrimeSpectrum.basicOpen_le_basicOpen_iff _ _).1 hac`. Take `⟨d, hd⟩` from `Ideal.mem_span_singleton'.1 hn`.

Establish `key : f (a ^ n * r) * b = f (a ^ n * x)`. Rewrite using `[map_mul, map_mul, map_pow, ← hd]`. Take the linear combination `d * hx`. Establish `hmem : f (a ^ n * r) ∈ P` using `hle (Submodule.mem_colon_singleton.2 (by`. Rewrite using `[smul_eq_mul, key]`.

Conclude with `Ideal.mem_map_of_mem f (Ideal.mem_comap.2 (key ▸ J.mul_mem_left _ hb))))`. Rewrite `hmem` using `[map_mul, map_pow]`. Break down `hP.isPrime.mem_or_mem hmem with h | h` into its components or cases. Conclude with `ha (hP.isPrime.mem_of_pow_mem n h)`. Conclude with `hr h`.

Rewrite using `[← e]`. Conclude with `Ideal.FG.map (IsNoetherian.noetherian _) f`.
-/
theorem isNoetherianRing_of_isInducing {A B : Type*} [CommRing A] [CommRing B] [IsNoetherianRing A]
    (f : A →+* B) (hi : Topology.IsInducing (PrimeSpectrum.comap f)) (hf : f.SurjectiveOnStalks) :
    IsNoetherianRing B := by
  refine (isNoetherianRing_iff_ideal_fg B).2 fun J => ?_
  have e : (J.comap f).map f = J := by
    refine le_antisymm Ideal.map_comap_le fun b hb => ?_
    by_contra hn
    have hne : ((J.comap f).map f).colon {b} ≠ ⊤ := fun h => hn (by
      have h1 : (1 : B) ∈ ((J.comap f).map f).colon {b} := h ▸ Submodule.mem_top
      simpa using Submodule.mem_colon_singleton.1 h1)
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨x, r, c, hc, hr, hx⟩ := RingHom.surjectiveOnStalks_iff_forall_maximal'.1 hf P hP b
    let p : PrimeSpectrum B := ⟨P, hP.isPrime⟩
    obtain ⟨U, hU, hUc⟩ := hi.isOpen_iff.1 (PrimeSpectrum.basicOpen c).isOpen
    have hpU : PrimeSpectrum.comap f p ∈ U := by
      have : p ∈ PrimeSpectrum.comap f ⁻¹' U := hUc ▸ hc
      exact this
    obtain ⟨_, ⟨a, rfl⟩, ha, haU⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpU hU
    have hac : PrimeSpectrum.basicOpen (f a) ≤ PrimeSpectrum.basicOpen c := fun q hq => by
      have : q ∈ PrimeSpectrum.comap f ⁻¹' U := haU hq
      exact hUc.subset this
    obtain ⟨n, hn⟩ := (PrimeSpectrum.basicOpen_le_basicOpen_iff _ _).1 hac
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hn
    have key : f (a ^ n * r) * b = f (a ^ n * x) := by
      rw [map_mul, map_mul, map_pow, ← hd]
      linear_combination d * hx
    have hmem : f (a ^ n * r) ∈ P := hle (Submodule.mem_colon_singleton.2 (by
      rw [smul_eq_mul, key]
      exact Ideal.mem_map_of_mem f (Ideal.mem_comap.2 (key ▸ J.mul_mem_left _ hb))))
    rw [map_mul, map_pow] at hmem
    rcases hP.isPrime.mem_or_mem hmem with h | h
    · exact ha (hP.isPrime.mem_of_pow_mem n h)
    · exact hr h
  rw [← e]
  exact Ideal.FG.map (IsNoetherian.noetherian _) f

/- English proof (translation)
Establish `H (w : W) : ∃ V : W.affineOpens, w ∈ V.1 ∧ IsNoetherianRing Γ(W, V)`. Take `⟨_, ⟨U, hU, rfl⟩, hw, -⟩` from `Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (j w)) isOpen_univ`. Take `⟨_, ⟨V, hV, rfl⟩, hwV, hVU⟩` from `W.isBasis_affineOpens.exists_subset_of_mem_open (show w ∈ (j ⁻¹ᵁ U : Set W) from hw) (j ⁻¹ᵁ U).isOpen`. Establish `hU' : IsAffineOpen U` using `hU`. Establish `hV' : IsAffineOpen V` using `hV`.

Establish `e` using `IsAffineOpen.SpecMap_appLE_fromSpec j hU' hV' hVU`. Establish `: IsPreimmersion (Spec.map (j.appLE U V hVU) ≫ hU'.fromSpec)`. Rewrite using `[e]`. Use `infer_instance`. Establish `h` using `(IsPreimmersion.SpecMap_iff _).1 (IsPreimmersion.of_comp (Spec.map (j.appLE U V hVU)) hU'.fromSpec)`.

Establish `: IsNoetherianRing Γ(Z, U)` using `IsLocallyNoetherian.component_noetherian ⟨U, hU⟩`. Conclude with `⟨⟨V, hV⟩, hwV, isNoetherianRing_of_isInducing _ h.1.isInducing h.2⟩`. Use `choose V hV hN using H`. Conclude with `isLocallyNoetherian_of_affine_cover (S := V) (top_le_iff.1 fun w _ => TopologicalSpace.Opens.mem_iSup.2 ⟨w, hV w⟩) hN`.
-/
theorem isLocallyNoetherian_of_isPreimmersion {W Z : Scheme.{0}} (j : W ⟶ Z) [IsPreimmersion j]
    [IsLocallyNoetherian Z] : IsLocallyNoetherian W := by
  have H (w : W) : ∃ V : W.affineOpens, w ∈ V.1 ∧ IsNoetherianRing Γ(W, V) := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hw, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (j w)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hwV, hVU⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
      (show w ∈ (j ⁻¹ᵁ U : Set W) from hw) (j ⁻¹ᵁ U).isOpen
    have hU' : IsAffineOpen U := hU
    have hV' : IsAffineOpen V := hV
    have e := IsAffineOpen.SpecMap_appLE_fromSpec j hU' hV' hVU
    have : IsPreimmersion (Spec.map (j.appLE U V hVU) ≫ hU'.fromSpec) := by
      rw [e]; infer_instance
    have h := (IsPreimmersion.SpecMap_iff _).1 (IsPreimmersion.of_comp (Spec.map (j.appLE U V hVU)) hU'.fromSpec)
    have : IsNoetherianRing Γ(Z, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    exact ⟨⟨V, hV⟩, hwV, isNoetherianRing_of_isInducing _ h.1.isInducing h.2⟩
  choose V hV hN using H
  exact isLocallyNoetherian_of_affine_cover (S := V)
    (top_le_iff.1 fun w _ => TopologicalSpace.Opens.mem_iSup.2 ⟨w, hV w⟩) hN

/- English proof (translation)
Introduce `x`. Take `⟨h1, h2⟩` from `h (j x)`. Establish `hf : (j.stalkMap x).hom.Flat` using `Flat.stalkMap j x`. Establish `hs : Function.Surjective (j.stalkMap x).hom` using `j.stalkMap_surjective x`. Establish `hi : Function.Injective (j.stalkMap x).hom`.

Use `letI := (j.stalkMap x).hom.toAlgebra`. Establish `: Module.Flat (X.presheaf.stalk (j x)) (U.presheaf.stalk x)` using `hf`. Establish `: IsLocalHom (algebraMap (X.presheaf.stalk (j x)) (U.presheaf.stalk x))` using `inferInstanceAs (IsLocalHom (j.stalkMap x).hom)`. Use `Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (j x)) (B := U.presheaf.stalk x)` as an intermediate fact. Conclude with `FaithfulSMul.algebraMap_injective (X.presheaf.stalk (j x)) (U.presheaf.stalk x)`.

Set `e` to `RingEquiv.ofBijective (j.stalkMap x).hom ⟨hi, hs⟩`. Establish `h3 : IsDomain (U.presheaf.stalk x)` using `e.symm.toMulEquiv.isDomain _`. Conclude with `⟨h3, IsIntegrallyClosed.of_equiv e⟩`.
-/
theorem isNormalScheme_of_flat_preimmersion {U X : Scheme.{0}} (j : U ⟶ X) [IsPreimmersion j] [Flat j]
    (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme U := by
  intro x
  obtain ⟨h1, h2⟩ := h (j x)
  have hf : (j.stalkMap x).hom.Flat := Flat.stalkMap j x
  have hs : Function.Surjective (j.stalkMap x).hom := j.stalkMap_surjective x
  have hi : Function.Injective (j.stalkMap x).hom := by
    letI := (j.stalkMap x).hom.toAlgebra
    have : Module.Flat (X.presheaf.stalk (j x)) (U.presheaf.stalk x) := hf
    have : IsLocalHom (algebraMap (X.presheaf.stalk (j x)) (U.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (j.stalkMap x).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (j x))
      (B := U.presheaf.stalk x)
    exact FaithfulSMul.algebraMap_injective (X.presheaf.stalk (j x)) (U.presheaf.stalk x)
  let e := RingEquiv.ofBijective (j.stalkMap x).hom ⟨hi, hs⟩
  have h3 : IsDomain (U.presheaf.stalk x) := e.symm.toMulEquiv.isDomain _
  exact ⟨h3, IsIntegrallyClosed.of_equiv e⟩

/- English proof (translation)
Introduce `R K _ _ _ _ _ N g hN hL`. Establish `hb : IsPreimmersion (spMap (algebraMap R K))` using `IsPreimmersion.of_isLocalization (nonZeroDivisors R)`. Establish `hbf : Flat (spMap (algebraMap R K))`. Rewrite using `[Flat.SpecMap_iff]`. Conclude with `RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R))`.

Establish `: IsPreimmersion (pullback.fst g (spMap (algebraMap R K)))` using `MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hb`. Establish `: Flat (pullback.fst g (spMap (algebraMap R K)))` using `inferInstance`. Conclude with `⟨isNormalScheme_of_flat_preimmersion (pullback.fst g (spMap (algebraMap R K))) hN, isLocallyNoetherian_of_isPreimmersion (pullback.fst g _)⟩`.
-/
theorem normal_genericFibre : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (N : Scheme.{0}) (g : N ⟶ Sp R),
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N → IsLocallyNoetherian N →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (pullback g (spMap (algebraMap R K))) ∧
      IsLocallyNoetherian (pullback g (spMap (algebraMap R K))) := by
  intro R K _ _ _ _ _ N g hN hL
  have hb : IsPreimmersion (spMap (algebraMap R K)) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have hbf : Flat (spMap (algebraMap R K)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R))
  have : IsPreimmersion (pullback.fst g (spMap (algebraMap R K))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hb
  have : Flat (pullback.fst g (spMap (algebraMap R K))) :=
    inferInstance
  exact ⟨isNormalScheme_of_flat_preimmersion (pullback.fst g (spMap (algebraMap R K))) hN, isLocallyNoetherian_of_isPreimmersion (pullback.fst g _)⟩

end GlobalTheory.GenFibre

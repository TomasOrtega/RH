import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsBasicOpenCover
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Monomial

namespace ReciprocityTheory.AnForm.R.WMult

open AlgebraicGeometry CategoryTheory IsLocalRing

variable {W : Scheme.{0}}

/- English proof (translation)
Establish `key : ∀ (V V' : W.affineOpens) (h : V' ≤ V) (hyV' : y ∈ V'.1), Ideal.map (W.presheaf.germ V.1 y ((show V'.1 ≤ V.1 from h) hyV')).hom (I.ideal V) = Ideal.map (W.presheaf.germ V'.1 y hyV').hom (I.ideal V')`. Introduce `V V' h hyV'`. Rewrite using `[← I.map_ideal h, Ideal.map_map]`. Use `congr 1`. Rewrite using `[← CommRingCat.hom_comp]`.

Conclude with `congrArg CommRingCat.Hom.hom (W.presheaf.germ_res (homOfLE (show V'.1 ≤ V.1 from h)) y hyV').symm`. Rewrite using `[FinalTheorems.stalkId]`. Apply `le_antisymm` to reduce the goal to its premises. Use `iSup₂_le fun V hyV => ?_` and prove the remaining obligations. Take `⟨f, g, hfg, hyf⟩` from `exists_basicOpen_le_affine_inter U.2 V.2 y ⟨hy, hyV⟩`.

Establish `hWU : W.affineBasicOpen f ≤ U` using `W.basicOpen_le f`. Establish `hWV : W.affineBasicOpen f ≤ V` using `by show W.basicOpen f ≤ V.1`. Rewrite using `[hfg]`. Conclude with `W.basicOpen_le g`. Rewrite using `[key V _ hWV hyf, key U _ hWU hyf]`.

Conclude with `le_iSup₂ (f := fun (V : W.affineOpens) (hV : y ∈ V.1) => Ideal.map (W.presheaf.germ V.1 y hV).hom (I.ideal V)) U hy`.
-/
theorem stalkId_eq_map_germ (I : W.IdealSheafData) (y : W) (U : W.affineOpens) (hy : y ∈ U.1) :
    FinalTheorems.stalkId I y = Ideal.map (W.presheaf.germ U.1 y hy).hom (I.ideal U) := by
  have key : ∀ (V V' : W.affineOpens) (h : V' ≤ V) (hyV' : y ∈ V'.1),
      Ideal.map (W.presheaf.germ V.1 y ((show V'.1 ≤ V.1 from h) hyV')).hom (I.ideal V) =
        Ideal.map (W.presheaf.germ V'.1 y hyV').hom (I.ideal V') := by
    intro V V' h hyV'
    rw [← I.map_ideal h, Ideal.map_map]
    congr 1
    rw [← CommRingCat.hom_comp]
    exact congrArg CommRingCat.Hom.hom (W.presheaf.germ_res (homOfLE (show V'.1 ≤ V.1 from h)) y hyV').symm
  rw [FinalTheorems.stalkId]
  apply le_antisymm
  · refine iSup₂_le fun V hyV => ?_
    obtain ⟨f, g, hfg, hyf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 y ⟨hy, hyV⟩
    have hWU : W.affineBasicOpen f ≤ U := W.basicOpen_le f
    have hWV : W.affineBasicOpen f ≤ V := by
      show W.basicOpen f ≤ V.1
      rw [hfg]
      exact W.basicOpen_le g
    rw [key V _ hWV hyf, key U _ hWU hyf]
  · exact le_iSup₂ (f := fun (V : W.affineOpens) (hV : y ∈ V.1) =>
      Ideal.map (W.presheaf.germ V.1 y hV).hom (I.ideal V)) U hy

/- English proof (translation)
Establish `hmem : hU.fromSpec P ∈ U.1`. Establish `hr : hU.fromSpec P ∈ Set.range hU.fromSpec` using `⟨P, rfl⟩`. Rewrite `hr` using `[hU.range_fromSpec]`. Conclude with `hr`. Use `show hU.fromSpec P ∈ I.support ↔ _`.

Rewrite using `[Scheme.IdealSheafData.mem_support_iff_of_mem hmem]`. Conclude with `(Set.ext_iff.1 (hU.fromSpec_preimage_zeroLocus (I.ideal U : Set Γ(W, U.1))) P).trans ((PrimeSpectrum.mem_zeroLocus _ _).trans SetLike.coe_subset_coe)`.
-/
theorem mem_support_fromSpec_iff (I : W.IdealSheafData) (U : W.affineOpens) (hU : IsAffineOpen U.1)
    (P : PrimeSpectrum Γ(W, U.1)) :
    hU.fromSpec P ∈ (I.support : Set W) ↔ I.ideal U ≤ P.asIdeal := by
  have hmem : hU.fromSpec P ∈ U.1 := by
    have hr : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rw [hU.range_fromSpec] at hr
    exact hr
  show hU.fromSpec P ∈ I.support ↔ _
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hmem]
  exact (Set.ext_iff.1 (hU.fromSpec_preimage_zeroLocus (I.ideal U : Set Γ(W, U.1))) P).trans
    ((PrimeSpectrum.mem_zeroLocus _ _).trans SetLike.coe_subset_coe)

/- English proof (translation)
Establish `hI : Ideal.comap e (Ideal.span {e z}) = Ideal.span {z}`. Rewrite using `[show Ideal.span {e z} = Ideal.map e (Ideal.span {z}) by rw [Ideal.map_span, Set.image_singleton]]`. Conclude with `Ideal.comap_map_of_bijective e e.bijective`. Unfold `Ring.ord`. Apply `WithBot.coe_injective` to reduce the goal to its premises.

Rewrite using `[Module.coe_length, Module.coe_length]`. Use `Order.krullDim_eq_of_orderIso ?_` and prove the remaining obligations. Set `o3` to `Ideal.relIsoOfBijective (e : A →+* B) e.bijective`. Establish `h3 : o3 (Ideal.span {e z}) = Ideal.span {z}` using `hI`. Conclude with `(Submodule.comapMkQRelIso _).trans (((o3.Ici _).trans (OrderIso.setCongr _ _ (by rw [h3]))).trans (Submodule.comapMkQRelIso _).symm)`.
-/
private theorem ring_ord_ringEquiv_apply {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (z : A) : Ring.ord B (e z) = Ring.ord A z := by
  have hI : Ideal.comap e (Ideal.span {e z}) = Ideal.span {z} := by
    rw [show Ideal.span {e z} = Ideal.map e (Ideal.span {z}) by rw [Ideal.map_span, Set.image_singleton]]
    exact Ideal.comap_map_of_bijective e e.bijective
  unfold Ring.ord
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  refine Order.krullDim_eq_of_orderIso ?_
  let o3 := Ideal.relIsoOfBijective (e : A →+* B) e.bijective
  have h3 : o3 (Ideal.span {e z}) = Ideal.span {z} := hI
  exact (Submodule.comapMkQRelIso _).trans (((o3.Ici _).trans
    (OrderIso.setCongr _ _ (by rw [h3]))).trans (Submodule.comapMkQRelIso _).symm)

/- English proof (translation)
Establish `hL` using `ord_localization_eq_exponent f hspan hdim J u m i hi`. Set `e : Localization.AtPrime (Ideal.span {f i}) ≃ₐ[R] S` to `IsLocalization.algEquiv (Ideal.span {f i}).primeCompl (Localization.AtPrime (Ideal.span {f i})) S`. Rewrite using `[← e.commutes, ← hL]`. Conclude with `ring_ord_ringEquiv_apply e.toRingEquiv _`.
-/
theorem ord_isLocalization_eq_exponent {R : Type*} [CommRing R] [IsRegularLocalRing R] {n : ℕ}
    (f : Fin n → R)
    (hspan : Ideal.span (Set.range f) = maximalIdeal R) (hdim : (n : WithBot ℕ∞) = ringKrullDim R)
    (J : Finset (Fin n)) (u : Rˣ) (m : Fin n → ℕ) (i : Fin n) (hi : i ∈ J)
    [(Ideal.span {f i}).IsPrime] (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.AtPrime S (Ideal.span {f i})] :
    Ring.ord S (algebraMap R S (u * ∏ j ∈ J, f j ^ m j)) = (m i : ℕ∞) := by
  have hL := ord_localization_eq_exponent f hspan hdim J u m i hi
  let e : Localization.AtPrime (Ideal.span {f i}) ≃ₐ[R] S :=
    IsLocalization.algEquiv (Ideal.span {f i}).primeCompl (Localization.AtPrime (Ideal.span {f i})) S
  rw [← e.commutes, ← hL]
  exact ring_ord_ringEquiv_apply e.toRingEquiv _

end ReciprocityTheory.AnForm.R.WMult

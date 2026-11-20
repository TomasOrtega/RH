import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkIdComapOfAffine
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GermAff

/- English proof (translation)
Introduce `T Y' _ χ I W hle s hs`. Use `set K := (I.ideal W).map (χ.appLE W ⊤ hle).hom with hK`. Establish `hc : I.comap χ = Scheme.IdealSheafData.ofIdealTop K`. Use `(GlobalTheory.Vanishing.eq_comap_of_stalk fun z => ?_).symm` and prove the remaining obligations. Establish `hz : χ z ∈ W.1` using `hle trivial`.

Rewrite using `[GlobalTheory.LocM.stalkId_ofIdealTop, ds_stalkId_eq_map I W _ hz, Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc]`. Use `congr 3`. Conclude with `T.presheaf.germ_res (homOfLE hle) z (by trivial)`. Establish `hs' : ∀ t : T, (T.presheaf.germ ⊤ t trivial).hom s ∈ K.map (T.presheaf.germ ⊤ t trivial).hom`. Introduce `t`.

Rewrite using `[← GlobalTheory.LocM.stalkId_ofIdealTop, ← hc]`. Conclude with `hs t`. Assume the negation of the conclusion as `hns`. Establish `hne : K.colon {s} ≠ ⊤`. Introduce `htop`.

Establish `h1 : (1 : Γ(T, ⊤)) ∈ K.colon {s}` using `htop ▸ Submodule.mem_top`. Rewrite `h1` using `[Submodule.mem_colon_singleton, one_smul]`. Conclude with `hns h1`. Take `⟨P, hP, hCP⟩` from `Ideal.exists_le_maximal _ hne`. Set `y : PrimeSpectrum Γ(T, ⊤)` to `⟨P, hP.isPrime⟩`.

Establish `hA` using `isAffineOpen_top T`. Set `t : T` to `hA.fromSpec y`. Establish `ht : t ∈ (⊤ : T.Opens)` using `trivial`. Use `letI : Algebra Γ(T, ⊤) (T.presheaf.stalk t) := T.presheaf.algebra_section_stalk ⟨t, ht⟩`. Use `haveI : IsLocalization y.asIdeal.primeCompl (T.presheaf.stalk t) := hA.isLocalization_stalk' y ht`.

Establish `hg : (T.presheaf.germ ⊤ t trivial).hom = algebraMap Γ(T, ⊤) (T.presheaf.stalk t)` using `rfl`. Establish `h` using `hs' t`. Rewrite `h` using `[hg, IsLocalization.mem_map_algebraMap_iff y.asIdeal.primeCompl]`. Take `⟨⟨⟨k, hk⟩, ⟨m, hm⟩⟩, he⟩` from `h`. Simplify using `only at he`.

Rewrite `he` using `[← map_mul, IsLocalization.eq_iff_exists y.asIdeal.primeCompl]`. Take `⟨⟨c, hcm⟩, hc'⟩` from `he`. Simplify using `only at hc'`. Establish `hmem : c * m ∈ K.colon {s}`. Rewrite using `[Submodule.mem_colon_singleton, smul_eq_mul]`.

Establish `: c * m * s = c * k` using `by rw [← hc']; ring`. Rewrite using `[this]`. Conclude with `K.mul_mem_left c hk`. Establish `hnot : c * m ∉ P` using `fun h' => (hP.isPrime.mem_or_mem h').elim hcm hm`. Conclude with `hnot (hCP hmem)`.
-/
theorem mem_map_of_germ : ∀ {T Y' : Scheme.{0}} [IsAffine T] (χ : T ⟶ Y') (I : Y'.IdealSheafData) (W : Y'.affineOpens)
    (hle : ⊤ ≤ χ ⁻¹ᵁ (W : Y'.Opens)) (s : Γ(T, ⊤)),
    (∀ t : T, (T.presheaf.germ ⊤ t trivial).hom s ∈ FinalTheorems.stalkId (I.comap χ) t) →
      s ∈ (I.ideal W).map (χ.appLE W ⊤ hle).hom := by
  intro T Y' _ χ I W hle s hs
  set K := (I.ideal W).map (χ.appLE W ⊤ hle).hom with hK
  have hc : I.comap χ = Scheme.IdealSheafData.ofIdealTop K := by
    refine (GlobalTheory.Vanishing.eq_comap_of_stalk fun z => ?_).symm
    have hz : χ z ∈ W.1 := hle trivial
    rw [GlobalTheory.LocM.stalkId_ofIdealTop, ds_stalkId_eq_map I W _ hz, Ideal.map_map, Ideal.map_map,
      ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc]
    congr 3
    exact T.presheaf.germ_res (homOfLE hle) z (by trivial)
  have hs' : ∀ t : T, (T.presheaf.germ ⊤ t trivial).hom s ∈ K.map (T.presheaf.germ ⊤ t trivial).hom := by
    intro t
    rw [← GlobalTheory.LocM.stalkId_ofIdealTop, ← hc]
    exact hs t
  by_contra hns
  have hne : K.colon {s} ≠ ⊤ := by
    intro htop
    have h1 : (1 : Γ(T, ⊤)) ∈ K.colon {s} := htop ▸ Submodule.mem_top
    rw [Submodule.mem_colon_singleton, one_smul] at h1
    exact hns h1
  obtain ⟨P, hP, hCP⟩ := Ideal.exists_le_maximal _ hne
  let y : PrimeSpectrum Γ(T, ⊤) := ⟨P, hP.isPrime⟩
  have hA := isAffineOpen_top T
  let t : T := hA.fromSpec y
  have ht : t ∈ (⊤ : T.Opens) := trivial
  letI : Algebra Γ(T, ⊤) (T.presheaf.stalk t) := T.presheaf.algebra_section_stalk ⟨t, ht⟩
  haveI : IsLocalization y.asIdeal.primeCompl (T.presheaf.stalk t) := hA.isLocalization_stalk' y ht
  have hg : (T.presheaf.germ ⊤ t trivial).hom = algebraMap Γ(T, ⊤) (T.presheaf.stalk t) := rfl
  have h := hs' t
  rw [hg, IsLocalization.mem_map_algebraMap_iff y.asIdeal.primeCompl] at h
  obtain ⟨⟨⟨k, hk⟩, ⟨m, hm⟩⟩, he⟩ := h
  simp only at he
  rw [← map_mul, IsLocalization.eq_iff_exists y.asIdeal.primeCompl] at he
  obtain ⟨⟨c, hcm⟩, hc'⟩ := he
  simp only at hc'
  have hmem : c * m ∈ K.colon {s} := by
    rw [Submodule.mem_colon_singleton, smul_eq_mul]
    have : c * m * s = c * k := by rw [← hc']; ring
    rw [this]
    exact K.mul_mem_left c hk
  have hnot : c * m ∉ P := fun h' => (hP.isPrime.mem_or_mem h').elim hcm hm
  exact hnot (hCP hmem)

end GlobalTheory.GermAff

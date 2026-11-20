import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormIntExistsAndChowFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageIdealEqConeIdealOfGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndepBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimLeZeroOfSubset
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIsOpenImmersionIsStandardSmoothOfRelativeD
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic.HeightExists

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Twist GlobalTheory.ChowHt GlobalTheory.CompHt GlobalTheory.QCoh

attribute [local instance] MvPolynomial.gradedAlgebra

section Algebra

variable {k K σ : Type} [Field k] [Field K] [Algebra k K]

def coeffMap (l : K →ₗ[k] k) (g : MvPolynomial σ K) : MvPolynomial σ k :=
  ∑ a ∈ g.support, monomial a (l (coeff a g))

/- English proof (translation)
Simplify using `only [coeffMap, coeff_sum, coeff_monomial, Finset.sum_ite_eq']`. Use `split_ifs with h`. Both sides reduce to the same expression. Rewrite using `[notMem_support_iff.1 h, map_zero]`.
-/
theorem coeff_coeffMap (l : K →ₗ[k] k) (g : MvPolynomial σ K) (a : σ →₀ ℕ) :
    coeff a (coeffMap l g) = l (coeff a g) := by
  classical
  simp only [coeffMap, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, map_zero]

/- English proof (translation)
Introduce `a ha` and use `hg fun h => ha (by rw [coeff_coeffMap, h, map_zero])`.
-/
theorem isHomogeneous_coeffMap (l : K →ₗ[k] k) {g : MvPolynomial σ K} {d : ℕ} (hg : g.IsHomogeneous d) :
    (coeffMap l g).IsHomogeneous d := fun a ha =>
  hg fun h => ha (by rw [coeff_coeffMap, h, map_zero])

/- English proof (translation)
Set `b` to `Module.Basis.ofVectorSpace k K`. Set `s` to `g.support.biUnion fun a => (b.repr (coeff a g)).support`. Establish `e : g = ∑ i ∈ s, C (b i) * map (algebraMap k K) (coeffMap (b.coord i) g)`. Use extensionality with `a`. Simplify using `only [coeff_sum, coeff_C_mul, coeff_map, coeff_coeffMap]`.

Establish `hs : (b.repr (coeff a g)).support ⊆ s`. Distinguish the cases in `ha : a ∈ g.support`. Conclude with `Finset.subset_biUnion_of_mem (fun a => (b.repr (coeff a g)).support) ha`. Simplify using `[notMem_support_iff.1 ha]`. Use `conv_lhs => rw [← b.linearCombination_repr (coeff a g), Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ hs _ (by simp)]`.

Conclude with `Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]; rfl`. Rewrite using `[e]`. Conclude with `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (h _))`.
-/
theorem mem_map_of_coeffMap {I : Ideal (MvPolynomial σ k)} {g : MvPolynomial σ K}
    (h : ∀ l : K →ₗ[k] k, coeffMap l g ∈ I) :
    g ∈ I.map (MvPolynomial.map (algebraMap k K) : MvPolynomial σ k →+* MvPolynomial σ K) := by
  classical
  let b := Module.Basis.ofVectorSpace k K
  let s := g.support.biUnion fun a => (b.repr (coeff a g)).support
  have e : g = ∑ i ∈ s, C (b i) * map (algebraMap k K) (coeffMap (b.coord i) g) := by
    ext a
    simp only [coeff_sum, coeff_C_mul, coeff_map, coeff_coeffMap]
    have hs : (b.repr (coeff a g)).support ⊆ s := by
      by_cases ha : a ∈ g.support
      · exact Finset.subset_biUnion_of_mem (fun a => (b.repr (coeff a g)).support) ha
      · simp [notMem_support_iff.1 ha]
    conv_lhs => rw [← b.linearCombination_repr (coeff a g),
      Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ hs _ (by simp)]
    exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]; rfl
  rw [e]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (h _))

/- English proof (translation)
Use `isPrime_coneIdeal (K := k) y` as an intermediate fact. Take `⟨d, h1, h2⟩` from `exists_ringKrullDim_eq_and_trdeg_eq k (MvPolynomial (Fin N) k ⧸ coneIdeal k y)`. Take `rfl : d = e + 1` from `by exact_mod_cast h1.symm.trans he`. Establish `h3` using `trdeg_le_of_injective (Ideal.kerLiftAlg (coneMap k y)) (Ideal.kerLiftAlg_injective _)`. Rewrite `h3` using `[← trdeg_add_eq k K (A := Polynomial K), Polynomial.trdeg_of_isDomain, hD]`.

Establish `h4 : ((e + 1 : ℕ) : Cardinal.{0}) ≤ ((D + 1 : ℕ) : Cardinal.{0})`. Rewrite using `[← h2, Nat.cast_add, Nat.cast_one]`. Conclude with `h3`. Establish `: e + 1 ≤ D + 1` using `by exact_mod_cast h4`. Use linear arithmetic over natural numbers and integers.
-/
theorem le_of_ringKrullDim_coneIdeal {N D e : ℕ} (y : Fin N → K) (hD : Algebra.trdeg k K = D)
    (he : ringKrullDim (MvPolynomial (Fin N) k ⧸ coneIdeal k y) = (e + 1 : ℕ)) : e ≤ D := by
  have := isPrime_coneIdeal (K := k) y
  obtain ⟨d, h1, h2⟩ := exists_ringKrullDim_eq_and_trdeg_eq k (MvPolynomial (Fin N) k ⧸ coneIdeal k y)
  obtain rfl : d = e + 1 := by exact_mod_cast h1.symm.trans he
  have h3 := trdeg_le_of_injective (Ideal.kerLiftAlg (coneMap k y)) (Ideal.kerLiftAlg_injective _)
  rw [← trdeg_add_eq k K (A := Polynomial K), Polynomial.trdeg_of_isDomain, hD] at h3
  have h4 : ((e + 1 : ℕ) : Cardinal.{0}) ≤ ((D + 1 : ℕ) : Cardinal.{0}) := by
    rw [← h2, Nat.cast_add, Nat.cast_one]; exact h3
  have : e + 1 ≤ D + 1 := by exact_mod_cast h4
  omega

end Algebra

variable {k : Type} [Field k] (S : LinSys k)

/- English proof (translation)
Establish `e : resG _ hle (zfun (S.form hg) i) = 0`. Rewrite using `[(S.mem_imageIdeal_iff hg).1 h]`. Conclude with `(congrArg _ (zfun_zero i)).trans (map_zero _)`. Rewrite `e` using `[LinSys.form, zfun_formSec, resG_chartEval]`. Then use the resulting hypothesis.
-/
theorem chartEval_eq_zero {g : MvPolynomial (Fin S.N) k} {d : ℕ} (hg : g.IsHomogeneous d) (h : g ∈ S.imageIdeal)
    (i : S.L.ι) {W : S.Y.Opens} (hle : W ≤ S.L.U i) : chartEval k S.b i hle g = 0 := by
  have e : resG _ hle (zfun (S.form hg) i) = 0 := by
    rw [(S.mem_imageIdeal_iff hg).1 h]
    exact (congrArg _ (zfun_zero i)).trans (map_zero _)
  rwa [LinSys.form, zfun_formSec, resG_chartEval] at e

/- English proof (translation)
Use `(S.mem_imageIdeal_iff (isHomogeneous_coeffMap l hg)).2 (zglobal_ext fun i => ?_)` and prove the remaining obligations. Rewrite using `[zfun_zero, LinSys.form, zfun_formSec]`. Use `S.Y.sheaf.eq_of_locally_eq' (fun W : {W : S.Y.affineOpens // W.1 ≤ S.L.U i} => W.1.1) _ (fun W => homOfLE W.2) (fun y hy => ?_) _ _ fun W => ?_` and prove the remaining obligations. Take `⟨V, hV, hx, hle⟩` from `exists_isAffineOpen_mem_and_subset (U := S.L.U i) (x := y) hy`. Conclude with `Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hle⟩, hx⟩`.

Take `⟨⟨W, hW⟩, hle⟩` from `W`. Establish `H` using `S.isPullback_baseChange E`. Establish `po` using `(isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := W) le_top le_top (UY := S.bcFst E ⁻¹ᵁ W) (by simp)).1 (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hW)`. Establish `po' : IsPushout ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ S.str.appLE ⊤ W le_top) (CommRingCat.ofHom (algebraMap k E)) ((S.bcFst E).appLE W (S.bcFst E ⁻¹ᵁ W) le_rfl) ((Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫ (S.baseChange E).str.appLE ⊤ (S.bcFst E ⁻¹ᵁ W) le_top)`. Use `po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _) (by simp) ?_ (by simp) (by simp)` and prove the remaining obligations.

Rewrite using `[← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Both sides reduce to the same expression. Take `⟨Λ, hΛ⟩` from `IndepBaseChange.exists_contract po' l`. Establish `hle' : S.bcFst E ⁻¹ᵁ W ≤ (S.baseChange E).L.U fun _ => i` using `fun y hy => Set.mem_iInter.2 fun _ => hle hy`. Establish `e` using `(eval₂_eq _ _ _).symm.trans (chartEval_eq_zero (S.baseChange E) hg h (fun _ => i) hle')`.

Establish `e' : ∀ j, resG (S.baseChange E).Y hle' (((S.baseChange E).b j).f fun _ => i) = ((S.bcFst E).appLE W (S.bcFst E ⁻¹ᵁ W) le_rfl).hom (resG S.Y hle ((S.b j).f i))` using `fun j => by`. Establish `a` using `(S.bcFst E).appLE_map (U := S.L.U i) (V := (S.baseChange E).L.U fun _ => i) (fun y hy => Set.mem_iInter.1 hy PUnit.unit) (homOfLE hle').op`. Establish `b` using `(S.bcFst E).map_appLE (U := W) (V := S.bcFst E ⁻¹ᵁ W) le_rfl (homOfLE hle).op`. Conclude with `congrArg (fun g => g.hom ((S.b j).f i)) (a.trans b.symm)`. Establish `e₂` using `congrArg Λ e`.

Rewrite `e₂` using `[map_zero, map_sum]`. Use `(resG_chartEval k S.b i le_rfl hle _).trans (Eq.trans ?_ (e₂.trans (map_zero _).symm))` and prove the remaining obligations. Rewrite using `[coeffMap, map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[chartEval, eval₂Hom_monomial]`.

Use `Eq.trans (hΛ (coeff a g) (a.prod fun j n => resG S.Y hle ((S.b j).f i) ^ n)).symm (congrArg Λ ?_)` and prove the remaining obligations. Use `congrArg₂ (· * ·) rfl ?_` and prove the remaining obligations. Use `(map_prod ((S.bcFst E).appLE W (S.bcFst E ⁻¹ᵁ W) le_rfl).hom _ _).trans (Finset.prod_congr rfl fun j _ => ?_)` and prove the remaining obligations. Conclude with `(map_pow _ _ _).trans (congrArg (· ^ _) (e' j).symm)`.
-/
theorem coeffMap_mem_imageIdeal (E : Type) [Field E] [Algebra k E] {g : MvPolynomial (Fin S.N) E} {d : ℕ}
    (hg : g.IsHomogeneous d) (h : g ∈ (S.baseChange E).imageIdeal) (l : E →ₗ[k] k) :
    coeffMap l g ∈ S.imageIdeal := by
  refine (S.mem_imageIdeal_iff (isHomogeneous_coeffMap l hg)).2 (zglobal_ext fun i => ?_)
  rw [zfun_zero, LinSys.form, zfun_formSec]
  refine S.Y.sheaf.eq_of_locally_eq' (fun W : {W : S.Y.affineOpens // W.1 ≤ S.L.U i} => W.1.1) _
    (fun W => homOfLE W.2) (fun y hy => ?_) _ _ fun W => ?_
  · obtain ⟨V, hV, hx, hle⟩ := exists_isAffineOpen_mem_and_subset (U := S.L.U i) (x := y) hy
    exact Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hle⟩, hx⟩
  obtain ⟨⟨W, hW⟩, hle⟩ := W
  have H := S.isPullback_baseChange E
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := W) le_top le_top
    (UY := S.bcFst E ⁻¹ᵁ W) (by simp)).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hW)
  have po' : IsPushout ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ S.str.appLE ⊤ W le_top)
      (CommRingCat.ofHom (algebraMap k E)) ((S.bcFst E).appLE W (S.bcFst E ⁻¹ᵁ W) le_rfl)
      ((Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫
        (S.baseChange E).str.appLE ⊤ (S.bcFst E ⁻¹ᵁ W) le_top) := by
    refine po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _)
      (by simp) ?_ (by simp) (by simp)
    rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  obtain ⟨Λ, hΛ⟩ := IndepBaseChange.exists_contract po' l
  have hle' : S.bcFst E ⁻¹ᵁ W ≤ (S.baseChange E).L.U fun _ => i :=
    fun y hy => Set.mem_iInter.2 fun _ => hle hy
  have e := (eval₂_eq _ _ _).symm.trans (chartEval_eq_zero (S.baseChange E) hg h (fun _ => i) hle')
  have e' : ∀ j, resG (S.baseChange E).Y hle' (((S.baseChange E).b j).f fun _ => i) =
      ((S.bcFst E).appLE W (S.bcFst E ⁻¹ᵁ W) le_rfl).hom (resG S.Y hle ((S.b j).f i)) := fun j => by
    have a := (S.bcFst E).appLE_map (U := S.L.U i) (V := (S.baseChange E).L.U fun _ => i)
      (fun y hy => Set.mem_iInter.1 hy PUnit.unit) (homOfLE hle').op
    have b := (S.bcFst E).map_appLE (U := W) (V := S.bcFst E ⁻¹ᵁ W) le_rfl (homOfLE hle).op
    exact congrArg (fun g => g.hom ((S.b j).f i)) (a.trans b.symm)
  have e₂ := congrArg Λ e
  rw [map_zero, map_sum] at e₂
  refine (resG_chartEval k S.b i le_rfl hle _).trans (Eq.trans ?_ (e₂.trans (map_zero _).symm))
  rw [coeffMap, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [chartEval, eval₂Hom_monomial]
  refine Eq.trans (hΛ (coeff a g) (a.prod fun j n => resG S.Y hle ((S.b j).f i) ^ n)).symm (congrArg Λ ?_)
  refine congrArg₂ (· * ·) rfl ?_
  refine (map_prod ((S.bcFst E).appLE W (S.bcFst E ⁻¹ᵁ W) le_rfl).hom _ _).trans
    (Finset.prod_congr rfl fun j _ => ?_)
  exact (map_pow _ _ _).trans (congrArg (· ^ _) (e' j).symm)

/- English proof (translation)
Use `isNoetherian_of_isProjOver hp` as an intermediate fact. Establish `key` using `CutDegree.interNum_eq_sum_length S.str hp S.isLB S.chartAt S.mem_chartAt ∅ (by simp) (List.ofFn s) (structureModule S.Y) (fun x _ hx => by`. Take `⟨i, hi⟩` from `hs x`. Conclude with `(hx _ (List.mem_ofFn.2 ⟨i, rfl⟩) hi).elim) (by simp)`. Establish `e : topSelfIntersection k S.L S.D = topSelfIntersection k S.L (List.ofFn s).length` using `by rw [List.length_ofFn]`.

Rewrite using `[LinSys.del, e, topSelf_def]`. Conclude with `key`.
-/
theorem del_eq_zero (hp : IsProjOver S.str) (s : Fin S.D → S.L.Sec) (hs : ∀ y, ∃ i, y ∈ nonzeroLocus (s i)) :
    S.del = 0 := by
  have := isNoetherian_of_isProjOver hp
  have key := CutDegree.interNum_eq_sum_length S.str hp S.isLB S.chartAt S.mem_chartAt ∅ (by simp) (List.ofFn s)
    (structureModule S.Y) (fun x _ hx => by
      obtain ⟨i, hi⟩ := hs x
      exact (hx _ (List.mem_ofFn.2 ⟨i, rfl⟩) hi).elim) (by simp)
  have e : topSelfIntersection k S.L S.D = topSelfIntersection k S.L (List.ofFn s).length := by rw [List.length_ofFn]
  rw [LinSys.del, e, topSelf_def]
  exact key

variable {S}

/- English proof (translation)
Use `h.smooth` as an intermediate fact. Use `h.conn` as an intermediate fact. Establish `: Smooth S.str` using `SmoothOfRelativeDimension.smooth S.D S.str`. Use `geometricallyIntegral_of_smooth S.str` as an intermediate fact. Conclude with `GeometricallyIntegral.isIntegral_of_subsingleton S.str`.
-/
theorem isIntegral (h : S.IsVariety) : IsIntegral S.Y := by
  have := h.smooth
  have := h.conn
  have : Smooth S.str := SmoothOfRelativeDimension.smooth S.D S.str
  have := geometricallyIntegral_of_smooth S.str
  exact GeometricallyIntegral.isIntegral_of_subsingleton S.str

/- English proof (translation)
Use `isIntegral h` as an intermediate fact. Establish `hg` using `genericPoint_spec S.Y`. Use `⟨S.Y.residueField (genericPoint S.Y), inferInstance, (S.baseHom (resPt _)).toAlgebra, ⟨resPt _, S.comp_str _⟩, by rw [ptOf_resPt]; exact hg, ?_⟩` and prove the remaining obligations. Conclude with `(residueField_fg_trdeg_of_smoothOfRelativeDimension S.str S.D h.smooth _ fun y hy => (hy.antisymm (hg.specializes trivial)).eq).2`.
-/
theorem exists_generic (h : S.IsVariety) : ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra k Ω) (x : S.Pt Ω),
    IsGenericPoint (ptOf x.1) Set.univ ∧ Algebra.trdeg k Ω = S.D := by
  have := isIntegral h
  have hg := genericPoint_spec S.Y
  refine ⟨S.Y.residueField (genericPoint S.Y), inferInstance, (S.baseHom (resPt _)).toAlgebra,
    ⟨resPt _, S.comp_str _⟩, by rw [ptOf_resPt]; exact hg, ?_⟩
  exact (residueField_fg_trdeg_of_smoothOfRelativeDimension S.str S.D h.smooth _
    fun y hy => (hy.antisymm (hg.specializes trivial)).eq).2

/- English proof (translation)
Use `le_antisymm ?_ (Ideal.span_le.2 ?_)` and prove the remaining obligations. Use `isIntegral (h.baseChange E)` as an intermediate fact. Take `⟨Ω, _, _, x, hx, -⟩` from `exists_generic (h.baseChange E)`. Set `: Algebra k Ω` to `((algebraMap E Ω).comp (algebraMap k E)).toAlgebra`. Establish `: IsScalarTower k E Ω` using `.of_algebraMap_eq' rfl`.

Take `⟨c, hc, e⟩` from `S.exists_coords_baseChange E x.1`. Rewrite using `[imageIdeal_eq_coneIdeal_of_generic E Ω _ x hx c _ hc e]`. Use `Ideal.map_le_iff_le_comap.2 (Ideal.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `g ⟨d, hg, h0⟩`. Use `(mem_coneIdeal_of_isHomogeneous _ (hg.map (algebraMap k E))).2 ?_` and prove the remaining obligations.

Establish `h1` using `S.eval₂_coords_eq_zero (LinSys.toBase x).1 ((S.mem_imageIdeal_iff hg).2 h0)`. Rewrite `h1` using `[LinSys.baseHom_ptOver]`. Conclude with `(aeval_map_algebraMap E _ g).trans h1`. Introduce and unpack `g ⟨d, hg, h0⟩`. Conclude with `mem_map_of_coeffMap (coeffMap_mem_imageIdeal S E hg (((S.baseChange E).mem_imageIdeal_iff hg).2 h0))`.
-/
theorem map_imageIdeal (h : S.IsVariety) (E : Type) [Field E] [Algebra k E] :
    S.imageIdeal.map (MvPolynomial.map (algebraMap k E) : MvPolynomial (Fin S.N) k →+* MvPolynomial (Fin S.N) E) =
      (S.baseChange E).imageIdeal := by
  refine le_antisymm ?_ (Ideal.span_le.2 ?_)
  · have := isIntegral (h.baseChange E)
    obtain ⟨Ω, _, _, x, hx, -⟩ := exists_generic (h.baseChange E)
    let : Algebra k Ω := ((algebraMap E Ω).comp (algebraMap k E)).toAlgebra
    have : IsScalarTower k E Ω := .of_algebraMap_eq' rfl
    obtain ⟨c, hc, e⟩ := S.exists_coords_baseChange E x.1
    rw [imageIdeal_eq_coneIdeal_of_generic E Ω _ x hx c _ hc e]
    refine Ideal.map_le_iff_le_comap.2 (Ideal.span_le.2 ?_)
    rintro g ⟨d, hg, h0⟩
    refine (mem_coneIdeal_of_isHomogeneous _ (hg.map (algebraMap k E))).2 ?_
    have h1 := S.eval₂_coords_eq_zero (LinSys.toBase x).1 ((S.mem_imageIdeal_iff hg).2 h0)
    rw [LinSys.baseHom_ptOver] at h1
    exact (aeval_map_algebraMap E _ g).trans h1
  · rintro g ⟨d, hg, h0⟩
    exact mem_map_of_coeffMap
      (coeffMap_mem_imageIdeal S E hg (((S.baseChange E).mem_imageIdeal_iff hg).2 h0))

/- English proof (translation)
Use `isIntegral h` as an intermediate fact. Take `⟨Ω, _, _, x, hx, -⟩` from `exists_generic h`. Rewrite using `[imageIdeal_eq_coneIdeal_of_generic k Ω S x hx 1 _ one_ne_zero (one_smul _ _).symm]`. Conclude with `isPrime_coneIdeal _`.
-/
theorem isPrime_imageIdeal (h : S.IsVariety) : S.imageIdeal.IsPrime := by
  have := isIntegral h
  obtain ⟨Ω, _, _, x, hx, -⟩ := exists_generic h
  rw [imageIdeal_eq_coneIdeal_of_generic k Ω S x hx 1 _ one_ne_zero (one_smul _ _).symm]
  exact isPrime_coneIdeal _

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : ∃ u, eval u f ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hf.ne_zero (MvPolynomial.funext fun u => by rw [hc, map_zero])`. Use `del_eq_zero S hp (fun i => if hi : (i : ℕ) < e + 1 then S.comb fun j => u (⟨i, hi⟩, j) else 0) fun y => ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Set `Ω` to `AlgebraicClosure (S.Y.residueField y)`. Set `x : Sp Ω ⟶ S.Y` to `spMap (algebraMap (S.Y.residueField y) Ω) ≫ resPt y`. Establish `hx : ptOf x = y` using `(ptOf_spMap_comp _ _).trans (ptOf_resPt y)`.

Set `: Algebra k Ω` to `(S.baseHom x).toAlgebra`. Establish `h1` using `(hf.zero_iff_of_isAlgClosed S.isHomogeneous_imageIdeal fun p => algebraMap k Ω (u p)).2 ⟨S.coords x, hb.coords_ne_zero x, fun g hg => S.eval₂_coords_eq_zero x hg, fun i => by`. Establish `h2` using `hc ⟨i, by omega⟩`. Rewrite `h2` using `[dif_pos i.2, ← hx, ← S.val_ne_zero_iff, not_not, S.val_comb]`. Conclude with `h2⟩`.

Conclude with `hu ((map_eq_zero (algebraMap k Ω)).1 ((aeval_algebraMap_apply Ω u f).symm.trans h1))`.
-/
theorem del_eq_zero_of_lt [Infinite k] (hp : IsProjOver S.str) (hb : S.BasePointFree) {e δ : ℕ}
    {f : MvPolynomial (Fin (e + 1) × Fin S.N) k} (hf : IsChowFormInt S.imageIdeal e δ f) (he : e < S.D) :
    S.del = 0 := by
  obtain ⟨u, hu⟩ : ∃ u, eval u f ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hf.ne_zero (MvPolynomial.funext fun u => by rw [hc, map_zero])
  refine del_eq_zero S hp (fun i => if hi : (i : ℕ) < e + 1 then S.comb fun j => u (⟨i, hi⟩, j) else 0) fun y => ?_
  by_contra hc
  push Not at hc
  let Ω := AlgebraicClosure (S.Y.residueField y)
  let x : Sp Ω ⟶ S.Y := spMap (algebraMap (S.Y.residueField y) Ω) ≫ resPt y
  have hx : ptOf x = y := (ptOf_spMap_comp _ _).trans (ptOf_resPt y)
  let : Algebra k Ω := (S.baseHom x).toAlgebra
  have h1 := (hf.zero_iff_of_isAlgClosed S.isHomogeneous_imageIdeal fun p => algebraMap k Ω (u p)).2
    ⟨S.coords x, hb.coords_ne_zero x, fun g hg => S.eval₂_coords_eq_zero x hg, fun i => by
      have h2 := hc ⟨i, by omega⟩
      rw [dif_pos i.2, ← hx, ← S.val_ne_zero_iff, not_not, S.val_comb] at h2
      exact h2⟩
  exact hu ((map_eq_zero (algebraMap k Ω)).1 ((aeval_algebraMap_apply Ω u f).symm.trans h1))

/- English proof (translation)
Use `isIntegral h` as an intermediate fact. Establish `hp` using `isPrime_imageIdeal h`. Take `⟨Ω, _, _, x, hx, hD⟩` from `exists_generic h`. Establish `hI` using `imageIdeal_eq_coneIdeal_of_generic k Ω S x hx 1 _ one_ne_zero (one_smul _ _).symm`. Take `⟨j, hj⟩` from `Function.ne_iff.1 (hb.coords_ne_zero x.1)`.

Take `⟨e, he⟩` from `exists_ringKrullDim_quotient_eq_succ S.isHomogeneous_imageIdeal (i := j) fun hX => hj (by simpa using S.eval₂_coords_eq_zero x.1 hX)`. Take `⟨f, hf⟩` from `ChowExists.exists_isChowFormInt hp S.isHomogeneous_imageIdeal he`. Take `rfl : e = S.D` from `le_antisymm (le_of_ringKrullDim_coneIdeal _ hD (hI ▸ he)) (not_lt.1 fun hlt => hd (del_eq_zero_of_lt h.proj hb hf hlt))`. Conclude with `he`.
-/
theorem ringKrullDim_imageIdeal [CharZero k] (h : S.IsVariety) (hb : S.BasePointFree) (hd : S.del ≠ 0) :
    ringKrullDim (MvPolynomial (Fin S.N) k ⧸ S.imageIdeal) = (S.D + 1 : ℕ) := by
  have := isIntegral h
  have hp := isPrime_imageIdeal h
  obtain ⟨Ω, _, _, x, hx, hD⟩ := exists_generic h
  have hI := imageIdeal_eq_coneIdeal_of_generic k Ω S x hx 1 _ one_ne_zero (one_smul _ _).symm
  obtain ⟨j, hj⟩ := Function.ne_iff.1 (hb.coords_ne_zero x.1)
  obtain ⟨e, he⟩ := exists_ringKrullDim_quotient_eq_succ S.isHomogeneous_imageIdeal (i := j)
    fun hX => hj (by simpa using S.eval₂_coords_eq_zero x.1 hX)
  obtain ⟨f, hf⟩ := ChowExists.exists_isChowFormInt hp S.isHomogeneous_imageIdeal he
  obtain rfl : e = S.D := le_antisymm (le_of_ringKrullDim_coneIdeal _ hD (hI ▸ he))
    (not_lt.1 fun hlt => hd (del_eq_zero_of_lt h.proj hb hf hlt))
  exact he

/- English proof (translation)
The claim follows from `ChowExists.exists_isChowForm S.isHomogeneous_imageIdeal (by rw [map_imageIdeal h]; exact isPrime_imageIdeal (h.baseChange _)) (ringKrullDim_imageIdeal h hb hd)`.
-/
theorem exists_isChowForm [CharZero k] (h : S.IsVariety) (hb : S.BasePointFree) (hd : S.del ≠ 0) :
    ∃ f, IsChowForm S.imageIdeal S.D (hilbertDegree S.imageIdeal) f :=
  ChowExists.exists_isChowForm S.isHomogeneous_imageIdeal
    (by rw [map_imageIdeal h]; exact isPrime_imageIdeal (h.baseChange _)) (ringKrullDim_imageIdeal h hb hd)

/- English proof (translation)
Introduce `_ _ _ T h hd` and use `have ⟨_, hf⟩ := exists_isChowForm h.variety h.bpf hd.ne' ⟨_, T.isHeight_of_isChowForm hf⟩`.
-/
theorem exists_isHeight : ∀ (F : Type) [Field F] [NumberField F] (T : HermSys F),
    T.IsAlgebraicData → 0 < T.del → ∃ h, T.IsHeight h := fun _ _ _ T h hd =>
  have ⟨_, hf⟩ := exists_isChowForm h.variety h.bpf hd.ne'
  ⟨_, T.isHeight_of_isChowForm hf⟩

end GlobalTheory.Adelic.HeightExists

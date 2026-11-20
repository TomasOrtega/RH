import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSpMapEv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerVectorBlockTriangularFrameChange
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

namespace GlobalTheory.FlagMod.FieldFlag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {p : Proj (RingHom.id c.F)} {A : Atlas Y p}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X} {g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)}
  {κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)} [∀ b w, IsOpenImmersion (κ b w)]
  {S : Type} [CommRing S]

/- English proof (translation)
The claim follows from `(Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom f')).symm`.
-/
theorem spMap_comp_spMap_cell {R R' U : Type} [CommRing R] [CommRing R'] [CommRing U] (f : R →+* R')
    (f' : R' →+* U) : spMap f' ≫ spMap f = spMap (f'.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom f')).symm

/- English proof (translation)
Use `conv_lhs => rw [← eq_spMap_ev k z hz]`. Rewrite using `[Category.assoc, hZ.plk.base, cbase, ← Category.assoc, spMap_comp_spMap_cell]`. Both sides reduce to the same expression.
-/
theorem base_cellPt (hZ : Cells A π g κ) (k : A.B × Pm Dw.mult) (z : Sp S ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) :
    z ≫ π = spMap (((ev z _ hz).comp (cellθ κ k).toRingHom).comp MvPolynomial.C) ≫ tau (A.aff k.1) := by
  conv_lhs => rw [← eq_spMap_ev k z hz]
  rw [Category.assoc, hZ.plk.base, cbase, ← Category.assoc, spMap_comp_spMap_cell]
  rfl

/- English proof (translation)
Rewrite using `[← hx, base_cellPt hZ k z hz]`. Conclude with `le_preimage_comp _ (tau_le (A.aff k.1) le_rfl)`.
-/
theorem le_cellPt (hZ : Cells A π g κ) (k : A.B × Pm Dw.mult) (z : Sp S ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) : ⊤ ≤ x ⁻¹ᵁ (A.k k.1).V := by
  rw [← hx, base_cellPt hZ k z hz]
  exact le_preimage_comp _ (tau_le (A.aff k.1) le_rfl)

/- English proof (translation)
Establish `hb` using `base_cellPt hZ k z hz`. Use `set φ := (ev z _ hz).comp (cellθ κ k).toRingHom with hφ`. Establish `hev : ev x _ hV = φ.comp MvPolynomial.C`. Substitute `hx` using the available equality. Rewrite using `[ev_congr hb _ hV (hb ▸ hV)]`.

Conclude with `ev_spMap_tau _ _ _`. Establish `hstr : str x = (φ.comp MvPolynomial.C).comp (A.alpha k.1)`. Use `LowRank.str_eq ?_` and prove the remaining obligations. Rewrite using `[← hx, hb, Category.assoc, ← spMap_comp_spMap_cell (A.alpha k.1) (φ.comp MvPolynomial.C)]`. Use `congr 1`.

Conclude with `(spMap_ev_top _).symm`. Take `⟨hu, e⟩` from `hZ.plk.plk k.1 k.2 en`. Establish `key : ∀ (f f' : c.F →+* S) (v v' : Fin (plN A.N en.1 + 1) → S) hv, f = f' → v = v' → ∃ hv', pt f v hv = pt f' v' hv'`. Introduce and unpack `f _ v _ hv rfl rfl`. Conclude with `⟨hv, rfl⟩`.

Use `conv => enter [1, hu']`. Use `lhs`. Rewrite using `[← eq_spMap_ev k z hz]`. Rewrite using `[Category.assoc, e, spMap_pt]`. Use `key _ _ _ _ _ (by rw [hstr]; rfl) ?_` and prove the remaining obligations.

Rewrite using `[map_plk]`. Use `congr 1`. Use function extensionality and compare the values at `t r`. Rewrite using `[Function.comp_apply, uvec_cv]`. Use `show φ _ = _`.

Rewrite using `[← Matrix.map_apply (f := φ), Matrix.map_mul, Matrix.map_map, hev]`. Both sides reduce to the same expression.
-/
theorem g_cellPt (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ) (k : A.B × Pm Dw.mult) (z : Sp S ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) (hV : ⊤ ≤ x ⁻¹ᵁ (A.k k.1).V)
    (en : En Dw.mult) :
    ∃ hu, z ≫ g en = pt (str x) (plk (fun (t : Let Dw.mult) r =>
      ((A.A k.1).map (ev x _ hV) * (show Matrix (Fin (A.k k.1).M.n) (Fin (Dw.mult t.1)) S from
        (cellFrames hZ ht).uAt k z hz t.1)) r t.2) en.2.1) hu := by
  have hb := base_cellPt hZ k z hz
  set φ := (ev z _ hz).comp (cellθ κ k).toRingHom with hφ
  have hev : ev x _ hV = φ.comp MvPolynomial.C := by
    subst hx
    rw [ev_congr hb _ hV (hb ▸ hV)]
    exact ev_spMap_tau _ _ _
  have hstr : str x = (φ.comp MvPolynomial.C).comp (A.alpha k.1) := by
    refine LowRank.str_eq ?_
    rw [← hx, hb, Category.assoc, ← spMap_comp_spMap_cell (A.alpha k.1) (φ.comp MvPolynomial.C)]
    congr 1
    exact (spMap_ev_top _).symm
  obtain ⟨hu, e⟩ := hZ.plk.plk k.1 k.2 en
  have key : ∀ (f f' : c.F →+* S) (v v' : Fin (plN A.N en.1 + 1) → S) hv, f = f' → v = v' →
      ∃ hv', pt f v hv = pt f' v' hv' := by
    rintro f _ v _ hv rfl rfl
    exact ⟨hv, rfl⟩
  conv => enter [1, hu']; lhs; rw [← eq_spMap_ev k z hz]
  rw [Category.assoc, e, spMap_pt]
  refine key _ _ _ _ _ (by rw [hstr]; rfl) ?_
  rw [map_plk]
  congr 1
  funext t r
  rw [Function.comp_apply, uvec_cv]
  show φ _ = _
  rw [← Matrix.map_apply (f := φ), Matrix.map_mul, Matrix.map_map, hev]
  rfl

end GlobalTheory.FlagMod.FieldFlag

namespace GlobalTheory.FlagMod.FieldFlag

open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c Y p A Z π g κ _ hZ ht S _ _ z z' x hx hx' hst`. Take `⟨k, hz⟩` from `exists_chart_of_isLocalRing (cellFrames hZ ht).cover z`. Take `⟨k', hz'⟩` from `exists_chart_of_isLocalRing (cellFrames hZ ht).cover z'`. Establish `hV` using `le_cellPt hZ k z hz hx`. Establish `hV'` using `le_cellPt hZ k' z' hz' hx'`.

Establish `hM : ⊤ ≤ x ⁻¹ᵁ ((A.k k.1).M.U ⊓ (A.k k'.1).M.U)` using `le_preimage_inf ((cellFrames hZ ht).inM hz hx) ((cellFrames hZ ht).inM hz' hx')`. Establish `ex : ∀ σ, ∃ b : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧ ∀ i, (cellFrames hZ ht).vecAt k' z' hz' hx' σ i = ∑ j, b j i • (cellFrames hZ ht).vecAt k z hz hx σ j` using `fun σ => exists_tri_of_eq ((cellFrames hZ ht).linearIndependent_vecAt k z hz hx σ) fun i => by`. Rewrite using `[← (cellFrames hZ ht).step_eq k z hz hx, ← (cellFrames hZ ht).step_eq k' z' hz' hx', hst]`. Use `choose B hB hBu hBe using ex`. Take `⟨a, ha⟩` from `A.tw S x k'.1 k.1 hV' hV hM`.

Establish `hU : ∀ σ, (chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart).map (ev x _ hM) * (show Matrix (Fin (A.k k'.1).M.n) (Fin (Dw.mult σ)) S from (cellFrames hZ ht).uAt k' z' hz' σ) = (show Matrix (Fin (A.k k.1).M.n) (Fin (Dw.mult σ)) S from (cellFrames hZ ht).uAt k z hz σ) * B σ`. Introduce `σ`. Use extensionality with `r i`. Establish `e` using `hBe σ i`. Rewrite `e` using `[(cellFrames hZ ht).sum_vecAt k z hz hx σ (fun j => B σ j i)]`.

Establish `e2` using `vec_chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart x ((cellFrames hZ ht).inM hz hx) ((cellFrames hZ ht).inM hz' hx') hM (fun j => (cellFrames hZ ht).uAt k' z' hz' σ j i)`. Establish `e3` using `congrFun ((vec _ _ _).injective (e2.trans e)) r`. Rewrite using `[Matrix.mul_apply, Matrix.mul_apply]`. Simplify `e3` using `[Matrix.mulVec, dotProduct]`. Establish `hc : ∀ (t : Let Dw.mult), (fun r => ((A.A k'.1).map (ev x _ hV') * (show Matrix (Fin (A.k k'.1).M.n) (Fin (Dw.mult t.1)) S from (cellFrames hZ ht).uAt k' z' hz' t.1)) r t.2) = ∑ j, (a * B t.1 j t.2 : S) • fun r => ((A.A k.1).map (ev x _ hV) * (show Matrix (Fin (A.k k.1).M.n) (Fin …`.

Introduce `t`. Use function extensionality and compare the values at `r`. Rewrite using `[ha, Matrix.smul_mul, Matrix.mul_assoc, hU t.1, ← Matrix.mul_assoc]`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.smul_apply]`. Rewrite using `[Matrix.mul_apply, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Establish `htri : Tri (fun (t : Let Dw.mult) r => ((A.A k.1).map (ev x _ hV) * (show Matrix (Fin (A.k k.1).M.n) (Fin (Dw.mult t.1)) S from (cellFrames hZ ht).uAt k z hz t.1)) r t.2) (fun (t : Let Dw.mult) r => ((A.A k'.1).map (ev x _ hV') * (show Matrix (Fin (A.k k'.1).M.n) (Fin (Dw.mult t. …`. Introduce and unpack `⟨σ, i⟩`. Establish `h1` using `hc ⟨σ, i⟩`. Simplify using `only at h1 ⊢`.

Rewrite using `[h1, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_sub_cancel_left]`. Use `Submodule.sum_mem _ fun j hj => ?_` and prove the remaining obligations. Break down `lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with h | h` into its components or cases. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, h, rfl⟩)`. Rewrite using `[hB σ (show id i < id j from h), mul_zero, zero_smul]`.

Conclude with `Submodule.zero_mem _`. Use `hZ.ext _ z z' (hx.trans hx'.symm) fun en => ?_` and prove the remaining obligations. Take `⟨hu, e⟩` from `g_cellPt hZ ht k z hz hx hV en`. Take `⟨hu', e'⟩` from `g_cellPt hZ ht k' z' hz' hx' hV' en`. Rewrite using `[e, e']`.

Establish `hd : IsUnit (∏ l, a * B (en.2.1 l).1 (en.2.1 l).2 (en.2.1 l).2)` using `IsUnit.prod_univ_iff.2 fun l => a.isUnit.mul (hBu _ _)`. Conclude with `(pt_eq_pt_iff _ hu hu').2 ⟨hd.unit, by rw [plk_tri _ _ S A.N _ _ _ en.1 en.2.1 htri en.2.2]; rfl⟩`.
-/
theorem cell_sep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ) (S : Type) [CommRing S] [IsLocalRing S] (z z' : Sp S ⟶ Z) (x : Sp S ⟶ Y.X) (hx : z ≫ π = x) (hx' : z' ≫ π = x), (∀ σ i, (cellFrames hZ ht).step z hx σ i = (cellFrames hZ ht).step z' hx' σ i) → z = z' := by
  intro E _ _ _ H Dw l Xo c Y p A Z π g κ _ hZ ht S _ _ z z' x hx hx' hst
  obtain ⟨k, hz⟩ := exists_chart_of_isLocalRing (cellFrames hZ ht).cover z
  obtain ⟨k', hz'⟩ := exists_chart_of_isLocalRing (cellFrames hZ ht).cover z'
  have hV := le_cellPt hZ k z hz hx
  have hV' := le_cellPt hZ k' z' hz' hx'
  have hM : ⊤ ≤ x ⁻¹ᵁ ((A.k k.1).M.U ⊓ (A.k k'.1).M.U) :=
    le_preimage_inf ((cellFrames hZ ht).inM hz hx) ((cellFrames hZ ht).inM hz' hx')

  have ex : ∀ σ, ∃ b : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧
      ∀ i, (cellFrames hZ ht).vecAt k' z' hz' hx' σ i = ∑ j, b j i • (cellFrames hZ ht).vecAt k z hz hx σ j :=
    fun σ => exists_tri_of_eq ((cellFrames hZ ht).linearIndependent_vecAt k z hz hx σ) fun i => by
      rw [← (cellFrames hZ ht).step_eq k z hz hx, ← (cellFrames hZ ht).step_eq k' z' hz' hx', hst]
  choose B hB hBu hBe using ex
  obtain ⟨a, ha⟩ := A.tw S x k'.1 k.1 hV' hV hM

  have hU : ∀ σ, (chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart).map (ev x _ hM) *
      (show Matrix (Fin (A.k k'.1).M.n) (Fin (Dw.mult σ)) S from (cellFrames hZ ht).uAt k' z' hz' σ) =
      (show Matrix (Fin (A.k k.1).M.n) (Fin (Dw.mult σ)) S from (cellFrames hZ ht).uAt k z hz σ) * B σ := by
    intro σ
    ext r i
    have e := hBe σ i
    rw [(cellFrames hZ ht).sum_vecAt k z hz hx σ (fun j => B σ j i)] at e
    have e2 := vec_chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart x ((cellFrames hZ ht).inM hz hx)
      ((cellFrames hZ ht).inM hz' hx') hM (fun j => (cellFrames hZ ht).uAt k' z' hz' σ j i)
    have e3 := congrFun ((vec _ _ _).injective (e2.trans e)) r
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simpa [Matrix.mulVec, dotProduct] using e3

  have hc : ∀ (t : Let Dw.mult), (fun r => ((A.A k'.1).map (ev x _ hV') *
      (show Matrix (Fin (A.k k'.1).M.n) (Fin (Dw.mult t.1)) S from (cellFrames hZ ht).uAt k' z' hz' t.1)) r t.2) =
      ∑ j, (a * B t.1 j t.2 : S) • fun r => ((A.A k.1).map (ev x _ hV) *
      (show Matrix (Fin (A.k k.1).M.n) (Fin (Dw.mult t.1)) S from (cellFrames hZ ht).uAt k z hz t.1)) r j := by
    intro t
    funext r
    rw [ha, Matrix.smul_mul, Matrix.mul_assoc, hU t.1, ← Matrix.mul_assoc]
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.smul_apply]
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have htri : Tri (fun (t : Let Dw.mult) r => ((A.A k.1).map (ev x _ hV) *
      (show Matrix (Fin (A.k k.1).M.n) (Fin (Dw.mult t.1)) S from (cellFrames hZ ht).uAt k z hz t.1)) r t.2)
      (fun (t : Let Dw.mult) r => ((A.A k'.1).map (ev x _ hV') *
      (show Matrix (Fin (A.k k'.1).M.n) (Fin (Dw.mult t.1)) S from (cellFrames hZ ht).uAt k' z' hz' t.1)) r t.2)
      (fun t => a * B t.1 t.2 t.2) := by
    rintro ⟨σ, i⟩
    have h1 := hc ⟨σ, i⟩
    dsimp only at h1 ⊢
    rw [h1, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_sub_cancel_left]
    refine Submodule.sum_mem _ fun j hj => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with h | h
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, h, rfl⟩)
    · rw [hB σ (show id i < id j from h), mul_zero, zero_smul]
      exact Submodule.zero_mem _
  refine hZ.ext _ z z' (hx.trans hx'.symm) fun en => ?_
  obtain ⟨hu, e⟩ := g_cellPt hZ ht k z hz hx hV en
  obtain ⟨hu', e'⟩ := g_cellPt hZ ht k' z' hz' hx' hV' en
  rw [e, e']
  have hd : IsUnit (∏ l, a * B (en.2.1 l).1 (en.2.1 l).2 (en.2.1 l).2) :=
    IsUnit.prod_univ_iff.2 fun l => a.isUnit.mul (hBu _ _)
  exact (pt_eq_pt_iff _ hu hu').2 ⟨hd.unit, by rw [plk_tri _ _ S A.N _ _ _ en.1 en.2.1 htri en.2.2]; rfl⟩

end GlobalTheory.FlagMod.FieldFlag

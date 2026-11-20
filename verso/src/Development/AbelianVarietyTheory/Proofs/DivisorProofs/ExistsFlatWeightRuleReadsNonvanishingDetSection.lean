import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsZero
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeterminantSectionRule
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactificationOpenOfClosed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FlatSectionAndDegree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramePointCombinationMatrix

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatRow GlobalTheory.DetExtendZero GlobalTheory.ShFam GlobalTheory.LieMet GlobalTheory.FramePairGram GlobalTheory.Toroidal

namespace GlobalTheory.BdryUnit.ReadDet

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}

section Frames

variable {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {x : Sp R ⟶ Y.X}

def vecs (F : EigFrame Y φ x) (τ : E →+* ℂ) {m : ℕ} (h : m = Dw.mult τ) : Fin m → (FramedFlatCoordinates.epsAt x ⟶ Y.t.G) :=
  fun i => Over.homMk (F.v τ (Fin.cast h i)) (F.tan τ _).1

/- English proof (translation)
Substitute `h` using the available equality. Use `⟨fun i => ⟨(F.tan τ i).2, fun a => F.eig τ i a⟩, fun w hw => ?_⟩` and prove the remaining obligations. Use `(existsUnique_congr fun a => ?_).1 (F.basis τ w.left ⟨Over.w w, hw.1⟩ hw.2)` and prove the remaining obligations. Conclude with `exists_congr fun u => and_congr Iff.rfl ⟨fun e => (Over.OverMorphism.ext e).symm, fun e => (congrArg CommaMorphism.left e).symm⟩`.
-/
theorem vecs_basis (F : EigFrame Y φ x) (τ : E →+* ℂ) {m : ℕ} (h : m = Dw.mult τ) :
    FramedFlatCoordinates.IsEigenBasis Y.t.act x (FramedFlatCoordinates.chr c τ φ) (vecs F τ h) := by
  subst h
  refine ⟨fun i => ⟨(F.tan τ i).2, fun a => F.eig τ i a⟩, fun w hw => ?_⟩
  refine (existsUnique_congr fun a => ?_).1 (F.basis τ w.left ⟨Over.w w, hw.1⟩ hw.2)
  exact exists_congr fun u => and_congr Iff.rfl
    ⟨fun e => (Over.OverMorphism.ext e).symm, fun e => (congrArg CommaMorphism.left e).symm⟩

/- English proof (translation)
Substitute `h` using the available equality. Use `choose cf h1 h2 h3 using ht`. Use `⟨Matrix.of cf, fun i => ?_, ?_⟩` and prove the remaining obligations. Take `⟨u, hu, e⟩` from `h3 i`. Conclude with `⟨u, hu, Over.OverMorphism.ext e.symm⟩`.

Rewrite using `[Matrix.det_of_lowerTriangular (Matrix.of cf) fun i k hk => h2 i k hk]`. Conclude with `Finset.prod_congr rfl fun i _ => h1 i`.
-/
theorem exists_matrix (F F' : EigFrame Y φ x) (τ : E →+* ℂ) {m : ℕ} (h : m = Dw.mult τ) (t : Fin (Dw.mult τ) → R)
    (ht : ∀ i, ∃ cf : Fin (Dw.mult τ) → R, cf i = t i ∧ (∀ k, i < k → cf k = 0) ∧
      IsCombAtG Y.t x (F.v τ) cf (F'.v τ i)) :
    ∃ M : Matrix (Fin m) (Fin m) R, (∀ i, RamifiedPlacesSplitEigen.IsCombAt (M i) (vecs F τ h) (vecs F' τ h i)) ∧ M.det = ∏ i, t i := by
  subst h
  choose cf h1 h2 h3 using ht
  refine ⟨Matrix.of cf, fun i => ?_, ?_⟩
  · obtain ⟨u, hu, e⟩ := h3 i
    exact ⟨u, hu, Over.OverMorphism.ext e.symm⟩
  · rw [Matrix.det_of_lowerTriangular (Matrix.of cf) fun i k hk => h2 i k hk]
    exact Finset.prod_congr rfl fun i _ => h1 i

end Frames

/- English proof (translation)
Rewrite using `[Datum.mult, if_pos τ.2]`.
-/
theorem mult_big (τ : Psi H) : Dw.p = Dw.mult τ.1 := by rw [Datum.mult, if_pos τ.2]

/- English proof (translation)
Rewrite using `[Datum.mult, if_neg (conj_not_mem τ)]`.
-/
theorem mult_small (τ : Psi H) : Dw.q = Dw.mult (conjEmb τ.1) := by rw [Datum.mult, if_neg (conj_not_mem τ)]

/- English proof (translation)
Establish `hne : τ.1 ≠ conjEmb τ.1` using `fun h => conj_not_mem τ (h ▸ τ.2)`. Rewrite using `[Fintype.prod_option, Fintype.prod_sigma, show exOf Dw (flatWt Dw τ) 0 none = 0 from rfl, zpow_zero, one_mul, Finset.prod_eq_mul τ.1 (conjEmb τ.1) hne ?_ (by simp) (by simp), ← Finset.prod_inv_distrib]`. Use `congr 1`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `: exOf Dw (flatWt Dw τ) 0 (some ⟨τ.1, i⟩) = -1` using `(wtOf_big _ 0 τ i (i.2.trans_eq (mult_big τ).symm)).trans (by simp [flatWt, parWt])`.

Rewrite using `[this, zpow_neg_one]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `: exOf Dw (flatWt Dw τ) 0 (some ⟨conjEmb τ.1, i⟩) = 1` using `(wtOf_small _ 0 τ i (i.2.trans_eq (mult_small τ).symm)).trans (by simp [flatWt, parWt])`. Rewrite using `[this, zpow_one]`. Introduce and unpack `ρ - ⟨h1, h2⟩`.

Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Establish `: exOf Dw (flatWt Dw τ) 0 (some ⟨ρ, i⟩) = 0`. Distinguish the cases in `h : ρ (H.rt : E) = H.rt0`. Establish `hn : (⟨ρ, h⟩ : Psi H) ≠ τ` using `fun e => h1 (congrArg Subtype.val e)`. Conclude with `(wtOf_big _ 0 ⟨ρ, h⟩ i (i.2.trans_eq (mult_big ⟨ρ, h⟩).symm)).trans (by simp [flatWt, parWt, hn])`.

Establish `hn : (⟨conjEmb ρ, conj_mem h⟩ : Psi H) ≠ τ` using `fun e => h2 ((conjEmb_conjEmb ρ).symm.trans (congrArg (fun s : Psi H => conjEmb s.1) e))`. Establish `hq : (i : ℕ) < Dw.q` using `by simpa [Datum.mult, h] using i.2`. Establish `e` using `wtOf_small (flatWt Dw τ) 0 ⟨conjEmb ρ, conj_mem h⟩ i hq`. Simplify using `only [conjEmb_conjEmb] at e`. Conclude with `e.trans (by simp [flatWt, parWt, hn])`.

Rewrite using `[this, zpow_zero]`.
-/
theorem prod_flat {G : Type} [CommGroup G] (τ : Psi H) (t : Ix Dw → G) :
    ∏ i, t i ^ exOf Dw (flatWt Dw τ) 0 i =
      (∏ i, t (some ⟨τ.1, i⟩))⁻¹ * ∏ i, t (some ⟨conjEmb τ.1, i⟩) := by
  classical
  have hne : τ.1 ≠ conjEmb τ.1 := fun h => conj_not_mem τ (h ▸ τ.2)
  rw [Fintype.prod_option, Fintype.prod_sigma, show exOf Dw (flatWt Dw τ) 0 none = 0 from rfl, zpow_zero, one_mul,
    Finset.prod_eq_mul τ.1 (conjEmb τ.1) hne ?_ (by simp) (by simp), ← Finset.prod_inv_distrib]
  · congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      have : exOf Dw (flatWt Dw τ) 0 (some ⟨τ.1, i⟩) = -1 :=
        (wtOf_big _ 0 τ i (i.2.trans_eq (mult_big τ).symm)).trans (by simp [flatWt, parWt])
      rw [this, zpow_neg_one]
    · refine Finset.prod_congr rfl fun i _ => ?_
      have : exOf Dw (flatWt Dw τ) 0 (some ⟨conjEmb τ.1, i⟩) = 1 :=
        (wtOf_small _ 0 τ i (i.2.trans_eq (mult_small τ).symm)).trans (by simp [flatWt, parWt])
      rw [this, zpow_one]
  · rintro ρ - ⟨h1, h2⟩
    refine Finset.prod_eq_one fun i _ => ?_
    have : exOf Dw (flatWt Dw τ) 0 (some ⟨ρ, i⟩) = 0 := by
      by_cases h : ρ (H.rt : E) = H.rt0
      · have hn : (⟨ρ, h⟩ : Psi H) ≠ τ := fun e => h1 (congrArg Subtype.val e)
        exact (wtOf_big _ 0 ⟨ρ, h⟩ i (i.2.trans_eq (mult_big ⟨ρ, h⟩).symm)).trans (by simp [flatWt, parWt, hn])
      · have hn : (⟨conjEmb ρ, conj_mem h⟩ : Psi H) ≠ τ := fun e =>
          h2 ((conjEmb_conjEmb ρ).symm.trans (congrArg (fun s : Psi H => conjEmb s.1) e))
        have hq : (i : ℕ) < Dw.q := by simpa [Datum.mult, h] using i.2
        have e := wtOf_small (flatWt Dw τ) 0 ⟨conjEmb ρ, conj_mem h⟩ i hq
        simp only [conjEmb_conjEmb] at e
        exact e.trans (by simp [flatWt, parWt, hn])
    rw [this, zpow_zero]

section Pts

variable {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]

/- English proof (translation)
Take `⟨w, t, e, rfl⟩` from `h`. Take `⟨w', t', e', rfl⟩` from `h'`. Rewrite using `[Y.m0.toSABMap.cart.1.hom_ext (e.trans e'.symm) (t.1.trans t'.1.symm)]`.
-/
theorem sameVec_unique {y : FrPt Xo c S} {u : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    {v v' : Sp (DualNumber S) ⟶ Y.t.G.left} (h : SameVec Y y u v) (h' : SameVec Y y u v') : v = v' := by
  obtain ⟨w, t, e, rfl⟩ := h
  obtain ⟨w', t', e', rfl⟩ := h'
  rw [Y.m0.toSABMap.cart.1.hom_ext (e.trans e'.symm) (t.1.trans t'.1.symm)]

/- English proof (translation)
Use `pullback.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, ptF_fst, ptF_fst, h.1]`. Rewrite using `[Category.assoc, ptF_snd, ptF_snd, ← DetExtendZero.spMap_comp]`. Conclude with `congrArg spMap φ.comp_algebraMap.symm`.
-/
theorem ptF_map {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) :
    ptF z = spMap φ.toRingHom ≫ ptF y := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, ptF_fst, ptF_fst, h.1]
  · rw [Category.assoc, ptF_snd, ptF_snd, ← DetExtendZero.spMap_comp]
    exact congrArg spMap φ.comp_algebraMap.symm

variable (Y) in

abbrev pt (y : FrPt Xo c S) : Sp S ⟶ Y.X := ptF y ≫ Y.jQ ≫ genι Y

variable (Y) in

def fr (y : FrPt Xo c S) : EigFrame Y (algebraMap c.F S) (pt Y y) := EigFrame.ofFrPt Y y rfl

/- English proof (translation)
The claim follows from `EigFrame.ofFrPt_v Y y rfl τ i`.
-/
theorem sameVec_fr (y : FrPt Xo c S) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) : SameVec Y y (y.u τ i) ((fr Y y).v τ i) :=
  EigFrame.ofFrPt_v Y y rfl τ i

/- English proof (translation)
Use `sameVec_unique (sameVec_fr z τ i) ?_` and prove the remaining obligations. Take `⟨w, t, e, e'⟩` from `sameVec_fr (Y := Y) y τ i`. Use `⟨spMap (dualMap φ.toRingHom) ≫ w, isTan_map _ (ptF_map h).symm t, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, e, h.2.1]`. Rewrite using `[Category.assoc, e']`.

Both sides reduce to the same expression.
-/
theorem fr_map {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) (τ : E →+* ℂ)
    (i : Fin (Dw.mult τ)) : (fr Y z).v τ i = spMap (Chart.dualMapR φ.toRingHom) ≫ (fr Y y).v τ i := by
  refine sameVec_unique (sameVec_fr z τ i) ?_
  obtain ⟨w, t, e, e'⟩ := sameVec_fr (Y := Y) y τ i
  refine ⟨spMap (dualMap φ.toRingHom) ≫ w, isTan_map _ (ptF_map h).symm t, ?_, ?_⟩
  · rw [Category.assoc, e, h.2.1]
  · rw [Category.assoc, e']; rfl

/- English proof (translation)
Rewrite using `[Category.assoc, Category.assoc]`. Conclude with `congrArg (ptF y ≫ ·) ((congrArg (Y.jQ ≫ ·) fst_toGen).trans (Category.comp_id _))`.
-/
theorem pt_toGen (y : FrPt Xo c S) : pt Y y ≫ toGen Y = ptF y ≫ Y.jQ := by
  rw [Category.assoc, Category.assoc]
  exact congrArg (ptF y ≫ ·) ((congrArg (Y.jQ ≫ ·) fst_toGen).trans (Category.comp_id _))

/- English proof (translation)
Use `⟨?_, vecs_basis _ _ _, vecs_basis _ _ _⟩` and prove the remaining obligations. Establish `e : genι Y ≫ Y.s = pullback.snd Y.s (spMap (RingHom.id c.F))` using `pullback.condition.trans ((congrArg (_ ≫ ·) (spMap_id _)).trans (Category.comp_id _))`. Rewrite using `[Category.assoc, Category.assoc, e, Y.jQ_over, ptF_snd, RingHom.comp_id]`.
-/
theorem isFrame_fr (τ : Psi H) (y : FrPt Xo c S) : RamifiedPlacesSplitEigen.IsFrame Y τ.1 (algebraMap c.F S) (pt Y y)
    (vecs (fr Y y) τ.1 (mult_big τ)) (vecs (fr Y y) (conjEmb τ.1) (mult_small τ)) := by
  refine ⟨?_, vecs_basis _ _ _, vecs_basis _ _ _⟩
  have e : genι Y ≫ Y.s = pullback.snd Y.s (spMap (RingHom.id c.F)) :=
    pullback.condition.trans ((congrArg (_ ≫ ·) (spMap_id _)).trans (Category.comp_id _))
  rw [Category.assoc, Category.assoc, e, Y.jQ_over, ptF_snd, RingHom.comp_id]

variable {V : (Xo.XF c).Opens} {τ : Psi H}

def val (sig : FramedFlatCoordinates.Rule Y V τ.1) (y : FrPt Xo c S) : S :=
  @Classical.epsilon S ⟨0⟩ (IsExtValue sig (algebraMap c.F S) (pt Y y)
    (vecs (fr Y y) τ.1 (mult_big τ)) (vecs (fr Y y) (conjEmb τ.1) (mult_small τ)))

variable {sig : FramedFlatCoordinates.Rule Y V τ.1} (hU : IsOpen (FramedFlatCoordinates.compactification Y V))
  (hs : sig ∈ FramedFlatCoordinates.sections Y V τ.1)

include hU hs

/- English proof (translation)
The claim follows from `Classical.epsilon_spec_aux ⟨0⟩ _ (exists_extValue (eigStable _ _) hU hs (isFrame_fr τ y))`.
-/
theorem val_spec (y : FrPt Xo c S) : IsExtValue sig (algebraMap c.F S) (pt Y y)
    (vecs (fr Y y) τ.1 (mult_big τ)) (vecs (fr Y y) (conjEmb τ.1) (mult_small τ)) (val sig y) :=
  Classical.epsilon_spec_aux ⟨0⟩ _ (exists_extValue (eigStable _ _) hU hs (isFrame_fr τ y))

/- English proof (translation)
Establish `key : ∀ (j : c.F →+* T) (x : Sp T ⟶ Y.X) (F : EigFrame Y j x), j = φ.toRingHom.comp (algebraMap c.F S) → x = spMap φ.toRingHom ≫ pt Y y → (∀ ρ i, F.v ρ i = spMap (Chart.dualMapR φ.toRingHom) ≫ (fr Y y).v ρ i) → IsExtValue sig j x (vecs F τ.1 (mult_big τ)) (vecs F (conjEmb τ.1) (m …`. Introduce and unpack `_ _ F rfl rfl hF`. Conclude with `(val_spec hU hs y).map φ.toRingHom (fun i => hF _ _) fun i => hF _ _`. Conclude with `extValue_unique (eigStable _ _) hU (isFrame_fr τ z) (val_spec hU hs z) (key _ _ _ φ.comp_algebraMap.symm (by rw [pt, ptF_map h, Category.assoc]) (fr_map h))`.
-/
theorem val_map {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) :
    val sig z = φ (val sig y) := by
  have key : ∀ (j : c.F →+* T) (x : Sp T ⟶ Y.X) (F : EigFrame Y j x), j = φ.toRingHom.comp (algebraMap c.F S) →
      x = spMap φ.toRingHom ≫ pt Y y → (∀ ρ i, F.v ρ i = spMap (Chart.dualMapR φ.toRingHom) ≫ (fr Y y).v ρ i) →
      IsExtValue sig j x (vecs F τ.1 (mult_big τ)) (vecs F (conjEmb τ.1) (mult_small τ)) (φ (val sig y)) := by
    rintro _ _ F rfl rfl hF
    exact (val_spec hU hs y).map φ.toRingHom (fun i => hF _ _) fun i => hF _ _
  exact extValue_unique (eigStable _ _) hU (isFrame_fr τ z) (val_spec hU hs z)
    (key _ _ _ φ.comp_algebraMap.symm (by rw [pt, ptF_map h, Category.assoc]) (fr_map h))

/- English proof (translation)
Establish `key : ∀ (x : Sp S ⟶ Y.X) (F : EigFrame Y (algebraMap c.F S) x) (r : S), x = pt Y y → RamifiedPlacesSplitEigen.IsFrame Y τ.1 (algebraMap c.F S) x (vecs F τ.1 (mult_big τ)) (vecs F (conjEmb τ.1) (mult_small τ)) → IsExtValue sig (algebraMap c.F S) x (vecs F τ.1 (mult_big τ)) (vecs F …`. Introduce and unpack `_ F r rfl hF hr hc`. Take `⟨M, hM, eM⟩` from `exists_matrix (fr Y y) F τ.1 (mult_big τ) _ (hc _)`. Take `⟨N, hN, eN⟩` from `exists_matrix (fr Y y) F (conjEmb τ.1) (mult_small τ) _ (hc _)`. Rewrite using `[← eM, ← eN]`.

Conclude with `IsExtValue.change (eigStable _ _) hU hs (isFrame_fr τ y) hF hM hN (val_spec hU hs y) hr`. Establish `e` using `key _ (fr Y y') _ (by rw [pt, ptF_eq_of_x_eq h.1]) (isFrame_fr τ y') (val_spec hU hs y') fun ρ i => by`. Take `⟨cf, h1, h2, h3⟩` from `h.2.1 ρ i`. Establish `hv : IsTanAtG Xo.univ.t y.x (y'.u ρ i)` using `h.1 ▸ y'.tan ρ i`. Use `⟨cf, h1, h2, ?_⟩` and prove the remaining obligations.

Rewrite using `[show (fr Y y').v ρ i = _ from ofFrPt_v_eq h.1 rfl rfl ρ i hv]`. Conclude with `isComb_ofFrPt y rfl ρ cf hv h3`. Rewrite using `[prod_flat, Units.val_mul, mul_assoc, Units.eq_inv_mul_iff_mul_eq, Units.coe_prod, Units.coe_prod, mul_comm, ← e, mul_comm]`.
-/
theorem val_bor {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} (h : FrBor t y y') :
    val sig y' = ((∏ i, t i ^ exOf Dw (flatWt Dw τ) 0 i : Sˣ) : S) * val sig y := by
  have key : ∀ (x : Sp S ⟶ Y.X) (F : EigFrame Y (algebraMap c.F S) x) (r : S), x = pt Y y →
      RamifiedPlacesSplitEigen.IsFrame Y τ.1 (algebraMap c.F S) x (vecs F τ.1 (mult_big τ)) (vecs F (conjEmb τ.1) (mult_small τ)) →
      IsExtValue sig (algebraMap c.F S) x (vecs F τ.1 (mult_big τ)) (vecs F (conjEmb τ.1) (mult_small τ)) r →
      (∀ ρ i, ∃ cf : Fin (Dw.mult ρ) → S, cf i = t (some ⟨ρ, i⟩) ∧ (∀ k, i < k → cf k = 0) ∧
        IsCombAtG Y.t (pt Y y) ((fr Y y).v ρ) cf (F.v ρ i)) →
      val sig y * ∏ i, (t (some ⟨conjEmb τ.1, i⟩) : S) = r * ∏ i, (t (some ⟨τ.1, i⟩) : S) := by
    rintro _ F r rfl hF hr hc
    obtain ⟨M, hM, eM⟩ := exists_matrix (fr Y y) F τ.1 (mult_big τ) _ (hc _)
    obtain ⟨N, hN, eN⟩ := exists_matrix (fr Y y) F (conjEmb τ.1) (mult_small τ) _ (hc _)
    rw [← eM, ← eN]
    exact IsExtValue.change (eigStable _ _) hU hs (isFrame_fr τ y) hF hM hN (val_spec hU hs y) hr
  have e := key _ (fr Y y') _ (by rw [pt, ptF_eq_of_x_eq h.1]) (isFrame_fr τ y') (val_spec hU hs y') fun ρ i => by
    obtain ⟨cf, h1, h2, h3⟩ := h.2.1 ρ i
    have hv : IsTanAtG Xo.univ.t y.x (y'.u ρ i) := h.1 ▸ y'.tan ρ i
    refine ⟨cf, h1, h2, ?_⟩
    rw [show (fr Y y').v ρ i = _ from ofFrPt_v_eq h.1 rfl rfl ρ i hv]
    exact isComb_ofFrPt y rfl ρ cf hv h3
  rw [prod_flat, Units.val_mul, mul_assoc, Units.eq_inv_mul_iff_mul_eq, Units.coe_prod, Units.coe_prod, mul_comm,
    ← e, mul_comm]

/- English proof (translation)
Use `(val_spec hU hs y).1 S (RingHom.id S) _ a ⟨rfl, ?_, fun i => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[spMap_id, Category.id_comp, pt_toGen, h.1]`. Take `⟨j, hj, e⟩` from `h.2.1 i`. Take `rfl : j = Fin.cast (mult_big τ) i` from `Fin.ext hj`. Rewrite using `[dual_id]`.

Conclude with `(sameVec_unique e (sameVec_fr y _ _)).trans (Category.id_comp _).symm`. Take `⟨j, hj, e⟩` from `h.2.2 i`. Take `rfl : j = Fin.cast (mult_small τ) i` from `Fin.ext hj`. Rewrite using `[dual_id]`. Conclude with `(sameVec_unique e (sameVec_fr y _ _)).trans (Category.id_comp _).symm`.
-/
theorem val_eq {y : FrPt Xo c S} {a : FramedFlatCoordinates.Framed Y V τ.1 S (algebraMap c.F S)} (h : Matches Y V τ y a) :
    val sig y = sig S _ a := by
  refine (val_spec hU hs y).1 S (RingHom.id S) _ a ⟨rfl, ?_, fun i => ?_, fun i => ?_⟩
  · rw [spMap_id, Category.id_comp, pt_toGen, h.1]
  · obtain ⟨j, hj, e⟩ := h.2.1 i
    obtain rfl : j = Fin.cast (mult_big τ) i := Fin.ext hj
    rw [dual_id]
    exact (sameVec_unique e (sameVec_fr y _ _)).trans (Category.id_comp _).symm
  · obtain ⟨j, hj, e⟩ := h.2.2 i
    obtain rfl : j = Fin.cast (mult_small τ) i := Fin.ext hj
    rw [dual_id]
    exact (sameVec_unique e (sameVec_fr y _ _)).trans (Category.id_comp _).symm

/- English proof (translation)
Take `⟨a, ha⟩` from `exists_above (U := V) (eigStable _ _) (Ideal.Quotient.mk (Ideal.span {1 - e})) (isFrame_fr (Y := Y) τ y) fun z => by`. Rewrite using `[pt_toGen, Scheme.Hom.comp_apply]`. Conclude with `subset_closure ⟨_, hz _ (mem_of_one_sub (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)) z), rfl⟩`. Establish `h1` using `hv _ _ a`. Rewrite `h1` using `[← (val_spec hU hs y).1 _ _ _ a ha]`.

Take `⟨s, hs'⟩` from `h1.exists_right_inv`. Take `⟨s, rfl⟩` from `Ideal.Quotient.mk_surjective s`. Rewrite `hs'` using `[← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq, Ideal.mem_span_singleton']`. Take `⟨b, hb⟩` from `hs'`. Establish `he' : e * e = e` using `he`.

Conclude with `⟨s, by linear_combination (-e) * hb - b * he'⟩`.
-/
theorem exists_inv (hv : FramedFlatCoordinates.VanishesNowhere sig) (y : FrPt Xo c S) {e : S} (he : IsIdempotentElem e)
    (hz : ∀ q : PrimeSpectrum S, e ∉ q.asIdeal → ptF y q ∈ (V : Set (Xo.XF c))) : ∃ s, e * val sig y * s = e := by
  obtain ⟨a, ha⟩ := exists_above (U := V) (eigStable _ _) (Ideal.Quotient.mk (Ideal.span {1 - e}))
    (isFrame_fr (Y := Y) τ y) fun z => by
      rw [pt_toGen, Scheme.Hom.comp_apply]
      exact subset_closure ⟨_, hz _ (mem_of_one_sub
        (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)) z), rfl⟩
  have h1 := hv _ _ a
  rw [← (val_spec hU hs y).1 _ _ _ a ha] at h1
  obtain ⟨s, hs'⟩ := h1.exists_right_inv
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hs'
  obtain ⟨b, hb⟩ := hs'
  have he' : e * e = e := he
  exact ⟨s, by linear_combination (-e) * hb - b * he'⟩

end Pts

/- English proof (translation)
Establish `h1 : ∀ p y, f p y * g p y = idem Z p y` using `fun p y => congrFun (congrFun hfg p) y`. Establish `h2 : ∀ p y, idem Z p y * g p y = g p y` using `fun p y => congrFun (congrFun hg p) y`. Use `⟨fun p q φ y z h => ?_, fun p t y y' h => ?_⟩` and prove the remaining obligations. Establish `a1` using `h1 q z`. Establish `a2` using `congrArg φ (h1 p y)`.

Establish `b1` using `h2 q z`. Establish `b2` using `congrArg φ (h2 p y)`. Rewrite `a2`, `b2` using `[map_mul, ← (idem_mem_secZ Z).1 p q φ y z h]`. Rewrite `a2` using `[← hf.1 p q φ y z h]`. Take the linear combination `φ (g p y) * a1 - g q z * a2 - b1 + b2`.

Establish `a1` using `h1 p y'`. Establish `a2` using `h1 p y`. Establish `b1` using `h2 p y'`. Establish `b2` using `h2 p y`. Establish `a0` using `(idem_mem_secZ Z).2 p t y y' h`.

Simplify using `only [Pi.zero_apply, zpow_zero, Finset.prod_const_one, Units.val_one, one_mul] at a0`. Rewrite `a1` using `[hf.2 p t y y' h]`. Rewrite `a1`, `b1` using `[a0]`. Establish `a3 : ((∏ i, t i ^ (-e) i : (p.R)ˣ) : p.R) * ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) = 1`. Rewrite using `[← Units.val_mul, ← Finset.prod_mul_distrib]`.

Simplify using the standard rewrite rules. Generalize the expression as in `((∏ i, t i ^ (-e) i : (p.R)ˣ) : p.R) = A at *`. Generalize the expression as in `((∏ i, t i ^ e i : (p.R)ˣ) : p.R) = B at *`. Take the linear combination `(A * g p y) * a1 - (A * B * g p y') * a2 - (idem Z p y * g p y') * a3 - b1 + A * b2`.
-/
theorem inv_mem {Z : Comp Xo c} {e : Ix Dw → ℤ} {f g : Rul Xo c} (hf : f ∈ secZ Xo c e) (hg : idem Z * g = g)
    (hfg : f * g = idem Z) : g ∈ secZ Xo c (-e) := by
  have h1 : ∀ p y, f p y * g p y = idem Z p y := fun p y => congrFun (congrFun hfg p) y
  have h2 : ∀ p y, idem Z p y * g p y = g p y := fun p y => congrFun (congrFun hg p) y
  refine ⟨fun p q φ y z h => ?_, fun p t y y' h => ?_⟩
  · have a1 := h1 q z
    have a2 := congrArg φ (h1 p y)
    have b1 := h2 q z
    have b2 := congrArg φ (h2 p y)
    rw [map_mul, ← (idem_mem_secZ Z).1 p q φ y z h] at a2 b2
    rw [← hf.1 p q φ y z h] at a2
    linear_combination φ (g p y) * a1 - g q z * a2 - b1 + b2
  · have a1 := h1 p y'
    have a2 := h1 p y
    have b1 := h2 p y'
    have b2 := h2 p y
    have a0 := (idem_mem_secZ Z).2 p t y y' h
    simp only [Pi.zero_apply, zpow_zero, Finset.prod_const_one, Units.val_one, one_mul] at a0
    rw [hf.2 p t y y' h] at a1
    rw [a0] at a1 b1
    have a3 : ((∏ i, t i ^ (-e) i : (p.R)ˣ) : p.R) * ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) = 1 := by
      rw [← Units.val_mul, ← Finset.prod_mul_distrib]; simp
    generalize ((∏ i, t i ^ (-e) i : (p.R)ˣ) : p.R) = A at *
    generalize ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) = B at *
    linear_combination (A * g p y) * a1 - (A * B * g p y') * a2 - (idem Z p y * g p y') * a3 - b1 + A * b2

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c Y Z V τ sig hV hs hv`. Establish `hc : IsClosed (V : Set (Xo.XF c))` using `hV ▸ isClosed_of_mem_irreducibleComponents _ Z.2`. Establish `hU` using `isOpen_compactification E H Dw l Xo c Y V hc`. Set `f₀ : Rul Xo c` to `fun p y => val sig y`. Establish `hf₀ : f₀ ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0)` using `⟨fun p q φ y z h => val_map hU hs h, fun p t y y' h => val_bor hU hs h⟩`.

Establish `hf : idem Z * f₀ ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0)`. Use `mul_mem_secZ (idem_mem_secZ Z) hf₀` as an intermediate fact. Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis. Establish `hZ : IsClopen (Z : Set (Xo.XF c))` using `hV ▸ ⟨hc, V.2⟩`. Establish `hinv : ∀ (p : TRing c.F) (y : FrPt Xo c p.R), ∃ s, idem Z p y * val sig y * s = idem Z p y` using `fun p y => exists_inv hU hs hv y (CompSplitPfB.cspB_idem_idem _ hZ _ _) fun q hq => hV ▸ (CompSplitPfB.cspB_idem_spec _ hZ _ _ q).1 hq`.

Use `choose g₀ hg₀ using hinv`. Establish `e₀ : idem Z * f₀ * (g₀ : Rul Xo c) = idem Z` using `funext fun p => funext fun y => hg₀ p y`. Establish `e₁ : idem Z * (idem Z * g₀) = idem Z * g₀` using `by rw [← mul_assoc, idem_mul_idem]`. Establish `e₂ : idem Z * f₀ * (idem Z * g₀) = idem Z`. Rewrite using `[mul_left_comm, e₀, idem_mul_idem]`.

Use `⟨idem Z * f₀, idem Z * g₀, hf, inv_mem hf e₁ e₂, by rw [← mul_assoc, idem_mul_idem], e₁, e₂, ?_⟩` and prove the remaining obligations. Introduce `S _ _ y ht a ha`. Establish `hon : LiesOn Z y` using `fun s => by`. Establish `h1` using `a.x_mem ⟨s, rfl⟩`. Rewrite `h1` using `[ha.1, Scheme.Hom.comp_apply]`.

Use `haveI := Y.jQ_open`. Establish `h2` using `Y.jQ.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image (V : Set (Xo.XF c))`. Rewrite `h2` using `[hc.closure_eq]`. Rewrite using `[← hV, h2]`. Conclude with `h1`.

Establish `h3 : evR Xo c f₀ y = val sig y` using `(dif_pos ht).trans (val_map hU hs ht.choose_spec.choose_spec.choose_spec).symm`. Establish `h4` using `evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (idem Z) f₀ y`. Conclude with `h4.trans ((congrArg₂ (· * ·) (evR_idem hon ht) h3).trans ((one_mul _).trans (val_eq hU hs ha)))`.
-/
theorem exists_reads : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c)
    (V : (Xo.XF c).Opens) (τ : Psi H) (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1), (V : Set (Xo.XF c)) = Z →
    sig ∈ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.sections Y V τ.1 → GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig →
    ∃ f g : Rul Xo c, f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0) ∧ g ∈ secZ Xo c (-exOf Dw (flatWt Dw τ) 0) ∧
      idem Z * f = f ∧ idem Z * g = g ∧ f * g = idem Z ∧ Reads Y V τ sig f := by
  intro E _ _ _ H Dw l Xo c Y Z V τ sig hV hs hv
  have hc : IsClosed (V : Set (Xo.XF c)) := hV ▸ isClosed_of_mem_irreducibleComponents _ Z.2
  have hU := isOpen_compactification E H Dw l Xo c Y V hc
  let f₀ : Rul Xo c := fun p y => val sig y
  have hf₀ : f₀ ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0) :=
    ⟨fun p q φ y z h => val_map hU hs h, fun p t y y' h => val_bor hU hs h⟩
  have hf : idem Z * f₀ ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0) := by
    have := mul_mem_secZ (idem_mem_secZ Z) hf₀
    rwa [zero_add] at this
  have hZ : IsClopen (Z : Set (Xo.XF c)) := hV ▸ ⟨hc, V.2⟩
  have hinv : ∀ (p : TRing c.F) (y : FrPt Xo c p.R), ∃ s, idem Z p y * val sig y * s = idem Z p y := fun p y =>
    exists_inv hU hs hv y (CompSplitPfB.cspB_idem_idem _ hZ _ _) fun q hq =>
      hV ▸ (CompSplitPfB.cspB_idem_spec _ hZ _ _ q).1 hq
  choose g₀ hg₀ using hinv
  have e₀ : idem Z * f₀ * (g₀ : Rul Xo c) = idem Z := funext fun p => funext fun y => hg₀ p y
  have e₁ : idem Z * (idem Z * g₀) = idem Z * g₀ := by rw [← mul_assoc, idem_mul_idem]
  have e₂ : idem Z * f₀ * (idem Z * g₀) = idem Z := by
    rw [mul_left_comm, e₀, idem_mul_idem]
  refine ⟨idem Z * f₀, idem Z * g₀, hf, inv_mem hf e₁ e₂, by rw [← mul_assoc, idem_mul_idem], e₁, e₂, ?_⟩
  intro S _ _ y ht a ha
  have hon : LiesOn Z y := fun s => by
    have h1 := a.x_mem ⟨s, rfl⟩
    rw [ha.1, Scheme.Hom.comp_apply] at h1
    haveI := Y.jQ_open
    have h2 := Y.jQ.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image (V : Set (Xo.XF c))
    rw [hc.closure_eq] at h2
    rw [← hV, h2]
    exact h1
  have h3 : evR Xo c f₀ y = val sig y :=
    (dif_pos ht).trans (val_map hU hs ht.choose_spec.choose_spec.choose_spec).symm
  have h4 := evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (idem Z) f₀ y
  exact h4.trans ((congrArg₂ (· * ·) (evR_idem hon ht) h3).trans ((one_mul _).trans (val_eq hU hs ha)))

end GlobalTheory.BdryUnit.ReadDet

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtSpMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O

/- English proof (translation)
Establish `hu : under z' = under z` using `by show below z'.1 = below z.1`. Rewrite using `[h]`. Conclude with `HtIndep.below_spMap_comp _ _`. Distinguish the cases in `hf : RegAt (under z) f`. Take `⟨U, hU, a, rfl⟩` from `hf.exists_fnOf`.

Rewrite using `[ratVal_fnOf (CxPts.mem_ptsIn.2 hU), ratVal_fnOf (CxPts.mem_ptsIn.2 (show under z' ∈ U from hu ▸ hU)), CxPts.ev_conj h (CxPts.mem_ptsIn.2 hU), RCLike.norm_conj]`. Establish `hf' : ¬ RegAt (under z') f` using `hu ▸ hf`. Simplify using `only [ratVal, dif_neg hf, dif_neg hf']`.
-/
theorem norm_ratVal_of_conj {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}
    {σ σ' : k →+* ℂ} {z : CxPts q σ} {z' : CxPts q σ'} (h : z'.1 = spMap (starRingEnd ℂ) ≫ z.1)
    (f : Z.functionField) : ‖ratVal f z'‖ = ‖ratVal f z‖ := by
  have hu : under z' = under z := by
    show below z'.1 = below z.1
    rw [h]
    exact HtIndep.below_spMap_comp _ _
  by_cases hf : RegAt (under z) f
  · obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
    rw [ratVal_fnOf (CxPts.mem_ptsIn.2 hU), ratVal_fnOf (CxPts.mem_ptsIn.2 (show under z' ∈ U from hu ▸ hU)),
      CxPts.ev_conj h (CxPts.mem_ptsIn.2 hU), RCLike.norm_conj]
  · have hf' : ¬ RegAt (under z') f := hu ▸ hf
    simp only [ratVal, dif_neg hf, dif_neg hf']

/- English proof (translation)
Introduce `F _ _ C Y V A L k hI σ σ' y y' hy`. Take `⟨r, -, -, hc, -⟩` from `hI`. Establish `hσ : σ' = (starRingEnd ℂ).comp σ` using `CxPts.eq_conj_of_conj hy`. Take `⟨w, hw⟩` from `V.π.surjective (under y)`. Establish `hpos : 0 < V.π.residueDegree w`.

Set `` to `(V.π.residueFieldMap w).hom.toAlgebra`. Establish `: Module.Finite (Y.X.residueField (V.π w)) (V.G.residueField w)` using `residueFieldMap_finite_of_locallyQuasiFinite V.π _`. Conclude with `Module.finrank_pos`. Establish `hcard` using `CoverHt.card_lifts V.π w y.1 hw.symm`. Take `⟨⟨z₀, -, hz₀⟩⟩` from `(Nat.card_pos_iff.1 (hcard ▸ hpos)).1`.

Set `z : CxPts (V.π ≫ Y.str) σ` to `⟨z₀, by show z₀ ≫ V.π ≫ Y.str = _`. Rewrite using `[← Category.assoc, hz₀]`. Conclude with `y.2⟩`. Set `z' : CxPts (V.π ≫ Y.str) σ'` to `⟨spMap (starRingEnd ℂ) ≫ z₀, by show (spMap (starRingEnd ℂ) ≫ z₀) ≫ V.π ≫ Y.str = _`. Rewrite using `[Category.assoc, ← Category.assoc z₀, hz₀, ← Category.assoc, ← hy]`.

Conclude with `y'.2⟩`. Establish `hgen (τ : F →+* ℂ) (t : CxPts (V.π ≫ Y.str) τ) : (t.1 ≫ V.j) ≫ V.p = spMap (τ.comp (algebraMap (𝓞 F) F))`. Rewrite using `[Category.assoc, V.pb.w, ← Category.assoc, t.2]`. Conclude with `(Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)).symm`. Set `u : CxPts V.p (σ.comp (algebraMap (𝓞 F) F))` to `⟨z.1 ≫ V.j, hgen σ z⟩`.

Set `u' : CxPts V.p (σ'.comp (algebraMap (𝓞 F) F))` to `⟨z'.1 ≫ V.j, hgen σ' z'⟩`. Choose the witnesses or unpack the hypotheses as in `⟨i₀, hi₀⟩ : ∃ i₀, V.j (under z) ∈ L.B.U i₀ := by`. Establish `: V.j (under z) ∈ (⊤ : V.X.Opens)` using `trivial`. Rewrite `this` using `[← L.isLB.cover]`. Conclude with `TopologicalSpace.Opens.mem_iSup.1 this`.

Establish `hu : under z' = under z` using `HtIndep.below_spMap_comp _ _`. Establish `hi : under z ∈ (L.B.pull V.j).U (fun _ => i₀)` using `Set.mem_iInter.2 fun _ => hi₀`. Establish `hi' : under z' ∈ (L.B.pull V.j).U (fun _ => i₀)` using `hu ▸ hi`. Establish `e₁` using `hc σ z y u (fun _ => i₀) hz₀.symm rfl hi`. Establish `e₂` using `hc σ' z' y' u' (fun _ => i₀) (by show y'.1 = (spMap (starRingEnd ℂ) ≫ z₀) ≫ V.π`.

Rewrite using `[Category.assoc, hz₀, hy]) rfl hi'`. Establish `hyy : under y' = under y` using `by show below y'.1 = below y.1`. Rewrite using `[hy]`. Conclude with `HtIndep.below_spMap_comp _ _`. Establish `hmk : InfinitePlace.mk σ' = InfinitePlace.mk σ`.

Rewrite using `[hσ]`. Conclude with `InfinitePlace.mk_conjugate_eq σ`. Establish `hn` using `norm_ratVal_of_conj (z := z) (z' := z') rfl (V.φ (genAt A.D (under y)) ^ k * (r (fun _ => i₀) : V.G.functionField))`. Establish `hwt : (L.φ (σ'.comp (algebraMap (𝓞 F) F))).φ i₀ u' = (L.φ (σ.comp (algebraMap (𝓞 F) F))).φ i₀ u` using `L.conj _ _ i₀ u u' (Category.assoc _ _ _) (CxPts.mem_ptsIn.2 hi₀)`. Rewrite `e₂` using `[hyy, hmk, hn]`.

Establish `e` using `e₂.trans (e₁.trans (by rw [hwt])).symm`. Rewrite `e` using `[mul_pow, mul_pow]`. Rewrite using `[hyy]`. Conclude with `mul_left_cancel₀ (pow_ne_zero _ (Real.exp_pos _).ne') e`.
-/
theorem Cover.pn_pow_conj : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (V : Cover Y) (A : Adl C Y) (L : HermLB V.p) (k : ℕ), V.Induces A L k → ∀ (σ σ' : F →+* ℂ) (y : Pts Y σ) (y' : Pts Y σ'), y'.1 = spMap (starRingEnd ℂ) ≫ y.1 → C.pn Y σ' A.D (A.m σ') (C.cx Y σ' (genAt A.D (under y'))) y' ^ k = C.pn Y σ A.D (A.m σ) (C.cx Y σ (genAt A.D (under y))) y ^ k := by
  intro F _ _ C Y V A L k hI σ σ' y y' hy
  obtain ⟨r, -, -, hc, -⟩ := hI
  have hσ : σ' = (starRingEnd ℂ).comp σ := CxPts.eq_conj_of_conj hy

  obtain ⟨w, hw⟩ := V.π.surjective (under y)
  have hpos : 0 < V.π.residueDegree w := by
    let := (V.π.residueFieldMap w).hom.toAlgebra
    have : Module.Finite (Y.X.residueField (V.π w)) (V.G.residueField w) :=
      residueFieldMap_finite_of_locallyQuasiFinite V.π _
    exact Module.finrank_pos
  have hcard := CoverHt.card_lifts V.π w y.1 hw.symm
  obtain ⟨⟨z₀, -, hz₀⟩⟩ := (Nat.card_pos_iff.1 (hcard ▸ hpos)).1
  let z : CxPts (V.π ≫ Y.str) σ := ⟨z₀, by
    show z₀ ≫ V.π ≫ Y.str = _
    rw [← Category.assoc, hz₀]
    exact y.2⟩
  let z' : CxPts (V.π ≫ Y.str) σ' := ⟨spMap (starRingEnd ℂ) ≫ z₀, by
    show (spMap (starRingEnd ℂ) ≫ z₀) ≫ V.π ≫ Y.str = _
    rw [Category.assoc, ← Category.assoc z₀, hz₀, ← Category.assoc, ← hy]
    exact y'.2⟩
  have hgen (τ : F →+* ℂ) (t : CxPts (V.π ≫ Y.str) τ) :
      (t.1 ≫ V.j) ≫ V.p = spMap (τ.comp (algebraMap (𝓞 F) F)) := by
    rw [Category.assoc, V.pb.w, ← Category.assoc, t.2]
    exact (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)).symm
  let u : CxPts V.p (σ.comp (algebraMap (𝓞 F) F)) := ⟨z.1 ≫ V.j, hgen σ z⟩
  let u' : CxPts V.p (σ'.comp (algebraMap (𝓞 F) F)) := ⟨z'.1 ≫ V.j, hgen σ' z'⟩

  obtain ⟨i₀, hi₀⟩ : ∃ i₀, V.j (under z) ∈ L.B.U i₀ := by
    have : V.j (under z) ∈ (⊤ : V.X.Opens) := trivial
    rw [← L.isLB.cover] at this
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have hu : under z' = under z := HtIndep.below_spMap_comp _ _
  have hi : under z ∈ (L.B.pull V.j).U (fun _ => i₀) := Set.mem_iInter.2 fun _ => hi₀
  have hi' : under z' ∈ (L.B.pull V.j).U (fun _ => i₀) := hu ▸ hi
  have e₁ := hc σ z y u (fun _ => i₀) hz₀.symm rfl hi
  have e₂ := hc σ' z' y' u' (fun _ => i₀) (by
    show y'.1 = (spMap (starRingEnd ℂ) ≫ z₀) ≫ V.π
    rw [Category.assoc, hz₀, hy]) rfl hi'
  have hyy : under y' = under y := by
    show below y'.1 = below y.1
    rw [hy]
    exact HtIndep.below_spMap_comp _ _
  have hmk : InfinitePlace.mk σ' = InfinitePlace.mk σ := by
    rw [hσ]
    exact InfinitePlace.mk_conjugate_eq σ
  have hn := norm_ratVal_of_conj (z := z) (z' := z') rfl
    (V.φ (genAt A.D (under y)) ^ k * (r (fun _ => i₀) : V.G.functionField))
  have hwt : (L.φ (σ'.comp (algebraMap (𝓞 F) F))).φ i₀ u' = (L.φ (σ.comp (algebraMap (𝓞 F) F))).φ i₀ u :=
    L.conj _ _ i₀ u u' (Category.assoc _ _ _) (CxPts.mem_ptsIn.2 hi₀)
  rw [hyy, hmk, hn] at e₂
  have e := e₂.trans (e₁.trans (by rw [hwt])).symm
  rw [mul_pow, mul_pow] at e
  rw [hyy]
  exact mul_left_cancel₀ (pow_ne_zero _ (Real.exp_pos _).ne') e

end GlobalTheory.Mean4O

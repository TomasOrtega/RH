import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CorrespondenceDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromPStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LetterSectionOnMapStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.HTLine

attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Take `⟨n, ⟨e⟩⟩` from `Finite.exists_equiv_fin T`. Take `⟨J, hJ, hP⟩` from `GlobalTheory.T.exists_ideal_sheaf_away_from_p X p n (fun i => U (e.symm i)) (fun i => m (e.symm i)) (fun i => A (e.symm i)) (fun i => hU _) (fun i => hA _)`. Use `⟨J, hJ, fun W W' b ν hC w j hw => ?_⟩` and prove the remaining obligations. Take `⟨i, rfl⟩` from `e.symm.surjective j`. Conclude with `hP W W' b ν hC w i hw`.
-/
theorem princ_of_finite (X : Scheme.{0}) [IsLocallyNoetherian X] (p : ℕ) {T : Type} [Finite T] (U : T → X.Opens)
    (m : T → ℕ) (A : ∀ j, Fin (m j) → Γ(X, U j)) (hU : ∀ j, IsAffineOpen (U j))
    (hA : ∀ j, (p : Γ(X, U j)) ∈ (Ideal.span (Set.range (A j))).radical) :
    ∃ J : X.IdealSheafData, (∀ x ∈ J.support, x ∉ X.basicOpen (p : Γ(X, ⊤))) ∧
      ∀ (W W' : Scheme.{0}) (b : W ⟶ X) (ν : W' ⟶ W), ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap b) →
        ∀ (w : W') (j : T), (ν ≫ b) w ∈ U j → ∃ (V : W'.Opens) (hV : V ≤ (ν ≫ b) ⁻¹ᵁ U j), w ∈ V ∧ IsAffineOpen V ∧
          ∃ k, ∀ k', ((ν ≫ b).appLE (U j) V hV).hom (A j k) ∣ ((ν ≫ b).appLE (U j) V hV).hom (A j k') := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin T
  obtain ⟨J, hJ, hP⟩ := GlobalTheory.T.exists_ideal_sheaf_away_from_p X p n (fun i => U (e.symm i)) (fun i => m (e.symm i)) (fun i => A (e.symm i))
    (fun i => hU _) (fun i => hA _)
  refine ⟨J, hJ, fun W W' b ν hC w j hw => ?_⟩
  obtain ⟨i, rfl⟩ := e.symm.surjective j
  exact hP W W' b ν hC w i hw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

/- English proof (translation)
Rewrite `hx` using `[← Z.cover]`. Take `⟨a, ha⟩` from `Set.mem_iUnion.1 hx`. Establish `hu : IsUnit (p : Γ(Z.X, (Z.U a).1))`. Establish `e : (p : Γ(Z.X, (Z.U a).1)) = Z.alg a (p : Z.i.c.F)` using `(map_natCast _ _).symm`. Rewrite using `[e]`.

Use `(IsUnit.mk0 _ ?_).map _` and prove the remaining obligations. Introduce `h0`. Establish `: ((p : Z.i.c.F) : ℂ) = 0` using `by rw [h0]; rfl`. Conclude with `hp (by exact_mod_cast this)`. Establish `h1 : x ∈ Z.X.basicOpen (p : Γ(Z.X, (Z.U a).1))`.

Rewrite using `[Scheme.basicOpen_of_isUnit _ hu]`. Conclude with `ha`. Establish `e2 : (p : Γ(Z.X, (Z.U a).1)) = (Z.X.presheaf.map (homOfLE le_top).op).hom (p : Γ(Z.X, ⊤))` using `(map_natCast _ _).symm`. Rewrite `h1` using `[e2, Scheme.basicOpen_res]`. Conclude with `h1.2`.
-/
theorem mem_basicOpen_p (hp : p ≠ 0) (Z : Mdl Y i₀) {x : Z.X} (hx : x ∈ Z.opn) :
    x ∈ Z.X.basicOpen (p : Γ(Z.X, ⊤)) := by
  rw [← Z.cover] at hx
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hx
  have hu : IsUnit (p : Γ(Z.X, (Z.U a).1)) := by
    have e : (p : Γ(Z.X, (Z.U a).1)) = Z.alg a (p : Z.i.c.F) := (map_natCast _ _).symm
    rw [e]
    refine (IsUnit.mk0 _ ?_).map _
    intro h0
    have : ((p : Z.i.c.F) : ℂ) = 0 := by rw [h0]; rfl
    exact hp (by exact_mod_cast this)
  have h1 : x ∈ Z.X.basicOpen (p : Γ(Z.X, (Z.U a).1)) := by
    rw [Scheme.basicOpen_of_isUnit _ hu]; exact ha
  have e2 : (p : Γ(Z.X, (Z.U a).1)) = (Z.X.presheaf.map (homOfLE le_top).op).hom (p : Γ(Z.X, ⊤)) :=
    (map_natCast _ _).symm
  rw [e2, Scheme.basicOpen_res] at h1
  exact h1.2

/- English proof (translation)
Take `⟨χ, hχ⟩` from `Pull.exists_fromSpec hU y.z hy`. Establish `hg : spMap ((intO ↥y.C.S).subtype.comp χ) ≫ hU.fromSpec = y.gen`. Rewrite using `[Mdl.Pt.gen, ← hχ, ← Category.assoc, spMap, spMap, spMap, ← Spec.map_comp]`. Both sides reduce to the same expression. Use `⟨?_, Pull.le_of_fromSpec hU hg⟩` and prove the remaining obligations.

Rewrite using `[← hg, Pull.valF_fromSpec]`. Conclude with `(χ s).2`.
-/
theorem norm_valF_le_one {Z : Mdl Y i₀} (y : Z.Pt) {U : Z.X.Opens} (hU : IsAffineOpen U) (hy : ⊤ ≤ y.z ⁻¹ᵁ U)
    (s : Γ(Z.X, U)) : ‖valF y.gen U s‖ ≤ 1 ∧ ⊤ ≤ y.gen ⁻¹ᵁ U := by
  obtain ⟨χ, hχ⟩ := Pull.exists_fromSpec hU y.z hy
  have hg : spMap ((intO ↥y.C.S).subtype.comp χ) ≫ hU.fromSpec = y.gen := by
    rw [Mdl.Pt.gen, ← hχ, ← Category.assoc, spMap, spMap, spMap, ← Spec.map_comp]; rfl
  refine ⟨?_, Pull.le_of_fromSpec hU hg⟩
  rw [← hg, Pull.valF_fromSpec]
  exact (χ s).2

/- English proof (translation)
Rewrite using `[Matrix.range_cons, Matrix.range_empty, Set.union_empty]`. Use `le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_mono (Set.singleton_subset_iff.2 ⟨k, rfl⟩))` and prove the remaining obligations. Introduce and unpack `_ ⟨k', rfl⟩`. Conclude with `Ideal.mem_span_singleton.2 (hk k')`.
-/
theorem span_eq_single {R : Type} [CommRing R] {m : ℕ} (A : Fin m → R) (k : Fin m) (hk : ∀ k', A k ∣ A k') :
    Ideal.span (Set.range A) = Ideal.span (Set.range ![A k]) := by
  rw [Matrix.range_cons, Matrix.range_empty, Set.union_empty]
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_mono (Set.singleton_subset_iff.2 ⟨k, rfl⟩))
  rintro _ ⟨k', rfl⟩
  exact Ideal.mem_span_singleton.2 (hk k')

/- English proof (translation)
Establish `e1 : (fun j => valF y.gen U (![A k] j)) = fun _ : Fin 1 => valF y.gen U (A k)`. Use function extensionality and compare the values at `j`. Rewrite using `[Matrix.cons_val_fin_one]`. Rewrite using `[e1, pi_norm_const]`. Use `le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_) (norm_le_pi_norm (fun j => valF y.gen U (A j)) k)` and prove the remaining obligations.

Take `⟨d, hd⟩` from `hk j`. Establish `h` using `norm_valF_le_one y hU hy d`. Rewrite using `[hd, Pull.valF_mul h.2, norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) h.1`.
-/
theorem norm_eq_single {Z : Mdl Y i₀} (y : Z.Pt) {U : Z.X.Opens} (hU : IsAffineOpen U) (hy : ⊤ ≤ y.z ⁻¹ᵁ U) {m : ℕ}
    (A : Fin m → Γ(Z.X, U)) (k : Fin m) (hk : ∀ k', A k ∣ A k') :
    ‖fun j => valF y.gen U (A j)‖ = ‖fun j => valF y.gen U (![A k] j)‖ := by
  have e1 : (fun j => valF y.gen U (![A k] j)) = fun _ : Fin 1 => valF y.gen U (A k) := by
    funext j; rw [Matrix.cons_val_fin_one]
  rw [e1, pi_norm_const]
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_) (norm_le_pi_norm (fun j => valF y.gen U (A j)) k)
  obtain ⟨d, hd⟩ := hk j
  have h := norm_valF_le_one y hU hy d
  rw [hd, Pull.valF_mul h.2, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) h.1

/- English proof (translation)
Take `⟨hA, hB, hr⟩` from `h`. Use `⟨span_eq_single A k₁ hk₁ ▸ hA, span_eq_single B k₂ hk₂ ▸ hB, fun y a φ hφ hy => ?_⟩` and prove the remaining obligations. Rewrite using `[hr y a φ hφ hy, norm_eq_single y hU hy A k₁ hk₁, norm_eq_single y hU hy B k₂ hk₂]`.
-/
theorem ratioAt_single {Z : Mdl Y i₀} {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {U : Z.X.Opens} (hU : IsAffineOpen U) {m m' : ℕ}
    {A : Fin m → Γ(Z.X, U)} {B : Fin m' → Γ(Z.X, U)} (h : RatioAt Z st U A B) (k₁ : Fin m) (hk₁ : ∀ k, A k₁ ∣ A k)
    (k₂ : Fin m') (hk₂ : ∀ k, B k₂ ∣ B k) : RatioAt Z st U ![A k₁] ![B k₂] := by
  obtain ⟨hA, hB, hr⟩ := h
  refine ⟨span_eq_single A k₁ hk₁ ▸ hA, span_eq_single B k₂ hk₂ ▸ hB, fun y a φ hφ hy => ?_⟩
  rw [hr y a φ hφ hy, norm_eq_single y hU hy A k₁ hk₁, norm_eq_single y hU hy B k₂ hk₂]

/- English proof (translation)
Introduce `hHT E _ _ _ H Dw Xo p W Y i₀ hp hW hN2 Z st x hx hty hR`. Use `haveI := GlobalTheory.LocM.Diag.isLocallyNoetherian hp hW Z`. Use `haveI : CompactSpace Z.X := by`. Use `GlobalTheory.LocM.SharedLaws.isProper_toroidalModel_structureMap Z` as an intermediate fact. Conclude with `QuasiCompact.compactSpace_of_compactSpace Z.s`.

Use `choose U m m' A B hzU hUa hRat using hR`. Take `⟨t, ht⟩` from `CompactSpace.elim_nhds_subcover (fun z => (U z : Set Z.X)) fun z => (U z).isOpen.mem_nhds (hzU z)`. Set `pt : (t ⊕ t) → Z.X` to `Sum.elim Subtype.val Subtype.val`. Set `mm : (t ⊕ t) → ℕ` to `Sum.elim (fun z => m z.1) (fun z => m' z.1)`. Set `AA : ∀ j, Fin (mm j) → Γ(Z.X, U (pt j))` to `fun j => Sum.rec (motive := fun j => Fin (mm j) → Γ(Z.X, U (pt j))) (fun z => A z.1) (fun z => B z.1) j`.

Take `⟨J, hJ, hP⟩` from `princ_of_finite Z.X p (fun j => U (pt j)) mm AA (fun j => hUa (pt j)) (by rintro (z | z); exacts [(hRat z.1).1, (hRat z.1).2.1])`. Establish `hJ' : ∀ y ∈ J.support, y ∉ Z.opn` using `fun y hy ho => hJ y hy (mem_basicOpen_p hp.ne_zero Z ho)`. Take `⟨Z', hi, hty', X', b, ν, hbl, -, hmap⟩` from `GlobalTheory.ProjBlowup.exists_isNBlow hp hW Z ⟨J, hJ'⟩`. Use `⟨Z', ν ≫ b, hi, hty', hmap, fun z' => ?_⟩` and prove the remaining obligations. Establish `hmem : (ν ≫ b) z' ∈ ⋃ z ∈ t, (U z : Set Z.X)` using `by rw [ht]; exact Set.mem_univ _`.

Simplify using `only [Set.mem_iUnion] at hmem`. Take `⟨z, hz, hfz⟩` from `hmem`. Take `⟨V₁, hV₁, hz₁, -, k₁, hk₁⟩` from `hP X' Z'.X b ν hbl.1 z' (Sum.inl ⟨z, hz⟩) hfz`. Take `⟨V₂, hV₂, hz₂, -, k₂, hk₂⟩` from `hP X' Z'.X b ν hbl.1 z' (Sum.inr ⟨z, hz⟩) hfz`. Take `⟨V, hVa', hzV, hVle⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z'.X.isBasis_affineOpens) (show z' ∈ V₁ ⊓ V₂ from ⟨hz₁, hz₂⟩)`.

Establish `hVa : IsAffineOpen V` using `hVa'`. Establish `hVU : V ≤ (ν ≫ b) ⁻¹ᵁ U z` using `hVle.trans (inf_le_left.trans hV₁)`. Establish `hres : ∀ (V' : Z'.X.Opens) (hV' : V' ≤ (ν ≫ b) ⁻¹ᵁ U z) (hle : V ≤ V') (s : Γ(Z.X, U z)), ((ν ≫ b).appLE (U z) V hVU).hom s = (Z'.X.presheaf.map (homOfLE hle).op).hom (((ν ≫ b).appLE (U z) V' hV').hom s)`. Introduce `V' hV' hle s`. Rewrite using `[← CommRingCat.comp_apply, Scheme.Hom.appLE_map]`.

Establish `hR'` using `GlobalTheory.T.letter_section_on_map hHT E H Dw Xo p W Y i₀ hp hW hN2 Z Z' (ν ≫ b) hmap hty st x hx (U z) (m z) (m' z) (A z) (B z) (hRat z) V hVU`. Use `⟨V, _, _, hzV, hVa, ratioAt_single hVa hR' k₁ (fun k => ?_) k₂ (fun k => ?_)⟩` and prove the remaining obligations. Rewrite using `[hres V₁ hV₁ (hVle.trans inf_le_left), hres V₁ hV₁ (hVle.trans inf_le_left)]`. Conclude with `map_dvd _ (hk₁ k)`. Rewrite using `[hres V₂ hV₂ (hVle.trans inf_le_right), hres V₂ hV₂ (hVle.trans inf_le_right)]`.

Conclude with `map_dvd _ (hk₂ k)`.
-/
theorem exists_pRatio : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → N2 Y → ∀ (Z : Mdl Y i₀) st (x : Letter Dw), letterOf Dw st = some x → (∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) → HasRatio Z st → ∃ (Z' : Mdl Y i₀) (f : Z'.X ⟶ Z.X), Z'.i = Z.i ∧ Z'.ty = Z.ty ∧ IsMap Z' Z f ∧ HasPRatio Z' st := by
  intro hHT E _ _ _ H Dw Xo p W Y i₀ hp hW hN2 Z st x hx hty hR
  haveI := GlobalTheory.LocM.Diag.isLocallyNoetherian hp hW Z
  haveI : CompactSpace Z.X := by
    have := GlobalTheory.LocM.SharedLaws.isProper_toroidalModel_structureMap Z
    exact QuasiCompact.compactSpace_of_compactSpace Z.s
  choose U m m' A B hzU hUa hRat using hR
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (fun z => (U z : Set Z.X)) fun z => (U z).isOpen.mem_nhds (hzU z)
  let pt : (t ⊕ t) → Z.X := Sum.elim Subtype.val Subtype.val
  let mm : (t ⊕ t) → ℕ := Sum.elim (fun z => m z.1) (fun z => m' z.1)
  let AA : ∀ j, Fin (mm j) → Γ(Z.X, U (pt j)) := fun j =>
    Sum.rec (motive := fun j => Fin (mm j) → Γ(Z.X, U (pt j))) (fun z => A z.1) (fun z => B z.1) j
  obtain ⟨J, hJ, hP⟩ := princ_of_finite Z.X p (fun j => U (pt j)) mm AA (fun j => hUa (pt j))
    (by rintro (z | z); exacts [(hRat z.1).1, (hRat z.1).2.1])
  have hJ' : ∀ y ∈ J.support, y ∉ Z.opn := fun y hy ho => hJ y hy (mem_basicOpen_p hp.ne_zero Z ho)
  obtain ⟨Z', hi, hty', X', b, ν, hbl, -, hmap⟩ := GlobalTheory.ProjBlowup.exists_isNBlow hp hW Z ⟨J, hJ'⟩
  refine ⟨Z', ν ≫ b, hi, hty', hmap, fun z' => ?_⟩
  have hmem : (ν ≫ b) z' ∈ ⋃ z ∈ t, (U z : Set Z.X) := by rw [ht]; exact Set.mem_univ _
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨z, hz, hfz⟩ := hmem
  obtain ⟨V₁, hV₁, hz₁, -, k₁, hk₁⟩ := hP X' Z'.X b ν hbl.1 z' (Sum.inl ⟨z, hz⟩) hfz
  obtain ⟨V₂, hV₂, hz₂, -, k₂, hk₂⟩ := hP X' Z'.X b ν hbl.1 z' (Sum.inr ⟨z, hz⟩) hfz
  obtain ⟨V, hVa', hzV, hVle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z'.X.isBasis_affineOpens)
    (show z' ∈ V₁ ⊓ V₂ from ⟨hz₁, hz₂⟩)
  have hVa : IsAffineOpen V := hVa'
  have hVU : V ≤ (ν ≫ b) ⁻¹ᵁ U z := hVle.trans (inf_le_left.trans hV₁)
  have hres : ∀ (V' : Z'.X.Opens) (hV' : V' ≤ (ν ≫ b) ⁻¹ᵁ U z) (hle : V ≤ V') (s : Γ(Z.X, U z)),
      ((ν ≫ b).appLE (U z) V hVU).hom s =
        (Z'.X.presheaf.map (homOfLE hle).op).hom (((ν ≫ b).appLE (U z) V' hV').hom s) := by
    intro V' hV' hle s
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  have hR' := GlobalTheory.T.letter_section_on_map hHT E H Dw Xo p W Y i₀ hp hW hN2 Z Z' (ν ≫ b) hmap hty st x hx (U z) (m z) (m' z)
    (A z) (B z) (hRat z) V hVU
  refine ⟨V, _, _, hzV, hVa, ratioAt_single hVa hR' k₁ (fun k => ?_) k₂ (fun k => ?_)⟩
  · rw [hres V₁ hV₁ (hVle.trans inf_le_left), hres V₁ hV₁ (hVle.trans inf_le_left)]
    exact map_dvd _ (hk₁ k)
  · rw [hres V₂ hV₂ (hVle.trans inf_le_right), hres V₂ hV₂ (hVle.trans inf_le_right)]
    exact map_dvd _ (hk₂ k)

end GlobalTheory.HTLine

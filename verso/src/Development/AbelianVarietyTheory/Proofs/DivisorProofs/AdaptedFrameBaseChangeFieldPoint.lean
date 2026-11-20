import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFramePullbackSections

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.FlagCell GlobalTheory.FlagConnect GlobalTheory.CovTest GlobalTheory.FlagOverField
open scoped Classical

namespace GlobalTheory.FlagOverField.AdCarr

/- English proof (translation)
Establish `hB : IsUnit ((N.map φ).transpose).det`. Rewrite using `[Matrix.det_transpose]`. Use `(φ : R →+* L).map_det N` as an intermediate fact. Conclude with `(show (φ : R →+* L) N.det = (N.map φ).det from this) ▸ hN.map (φ : R →+* L)`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨T, h₁, h₂, h₃⟩`. Establish `e : g = (T.map φ).transpose * (N.map φ).transpose`. Rewrite using `[← Matrix.transpose_mul]`. Use `congrArg (fun A : Matrix (Fin m) (Fin m) R => (A.map (φ : R →+* L)).transpose) h₃` as an intermediate fact. Simplify using `only [Matrix.map_mul] at this`.

Use `Eq.trans ?_ this` and prove the remaining obligations. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[e, Matrix.mul_nonsing_inv_cancel_right _ _ hB]`. Use `⟨?_, fun i j hij => ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.det_transpose]`. Use `(φ : R →+* L).map_det T` as an intermediate fact. Conclude with `((show (φ : R →+* L) T.det = (T.map φ).det from this) ▸ h₂.map (φ : R →+* L)).ne_zero`. Simplify using `[h₁ (show id i < id j from hij)]`. Introduce and unpack `⟨h₁, h₂⟩`.

Use `⟨(g * ((N.map φ).transpose)⁻¹).transpose.map φ.symm, fun i j hij => ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.map_apply, Matrix.transpose_apply, h₂ j i hij, map_zero]`. Use `(φ.symm : L →+* R).map_det (g * ((N.map φ).transpose)⁻¹).transpose` as an intermediate fact. Use `(show (φ.symm : L →+* R) _ = ((g * ((N.map φ).transpose)⁻¹).transpose.map φ.symm).det from this) ▸ ?_` and prove the remaining obligations. Rewrite using `[Matrix.det_transpose]`.

Conclude with `(Ne.isUnit h₁).map _`. Establish `e : g.transpose = N.map φ * (g * ((N.map φ).transpose)⁻¹).transpose`. Rewrite using `[← Matrix.transpose_transpose (N.map φ), ← Matrix.transpose_mul, Matrix.transpose_transpose (N.map φ), Matrix.nonsing_inv_mul_cancel_right _ _ hB]`. Use `congrArg (fun A : Matrix (Fin m) (Fin m) L => A.map (φ.symm : L →+* R)) e` as an intermediate fact. Simplify using `only [Matrix.map_mul] at this`.

Use `this.trans ?_` and prove the remaining obligations. Use `congr 1`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem exists_upper_iff {R L : Type} [CommRing R] [Field L] (φ : R ≃+* L) {m : ℕ} (N : Matrix (Fin m) (Fin m) R)
    (hN : IsUnit N.det) (g : Matrix (Fin m) (Fin m) L) :
    (∃ T : Matrix (Fin m) (Fin m) R, T.BlockTriangular id ∧ IsUnit T.det ∧ g.transpose.map φ.symm = N * T) ↔
      ((g * ((N.map φ).transpose)⁻¹).det ≠ 0 ∧ ∀ i j, i < j → (g * ((N.map φ).transpose)⁻¹) i j = 0) := by
  have hB : IsUnit ((N.map φ).transpose).det := by
    rw [Matrix.det_transpose]
    have := (φ : R →+* L).map_det N
    exact (show (φ : R →+* L) N.det = (N.map φ).det from this) ▸ hN.map (φ : R →+* L)
  constructor
  · rintro ⟨T, h₁, h₂, h₃⟩
    have e : g = (T.map φ).transpose * (N.map φ).transpose := by
      rw [← Matrix.transpose_mul]
      have := congrArg (fun A : Matrix (Fin m) (Fin m) R => (A.map (φ : R →+* L)).transpose) h₃
      simp only [Matrix.map_mul] at this
      refine Eq.trans ?_ this
      ext i j
      simp
    rw [e, Matrix.mul_nonsing_inv_cancel_right _ _ hB]
    refine ⟨?_, fun i j hij => ?_⟩
    · rw [Matrix.det_transpose]
      have := (φ : R →+* L).map_det T
      exact ((show (φ : R →+* L) T.det = (T.map φ).det from this) ▸ h₂.map (φ : R →+* L)).ne_zero
    · simp [h₁ (show id i < id j from hij)]
  · rintro ⟨h₁, h₂⟩
    refine ⟨(g * ((N.map φ).transpose)⁻¹).transpose.map φ.symm, fun i j hij => ?_, ?_, ?_⟩
    · rw [Matrix.map_apply, Matrix.transpose_apply, h₂ j i hij, map_zero]
    · have := (φ.symm : L →+* R).map_det (g * ((N.map φ).transpose)⁻¹).transpose
      refine (show (φ.symm : L →+* R) _ = ((g * ((N.map φ).transpose)⁻¹).transpose.map φ.symm).det from this) ▸ ?_
      rw [Matrix.det_transpose]
      exact (Ne.isUnit h₁).map _
    · have e : g.transpose = N.map φ * (g * ((N.map φ).transpose)⁻¹).transpose := by
        rw [← Matrix.transpose_transpose (N.map φ), ← Matrix.transpose_mul, Matrix.transpose_transpose (N.map φ),
          Matrix.nonsing_inv_mul_cancel_right _ _ hB]
      have := congrArg (fun A : Matrix (Fin m) (Fin m) L => A.map (φ.symm : L →+* R)) e
      simp only [Matrix.map_mul] at this
      refine this.trans ?_
      congr 1
      ext i j
      simp

/- English proof (translation)
Introduce `F _ Y ι _ r E e fl hE he L _ p x w h fl' hfl' A' hA`. Use `choose U hy M hM hAM using hA`. Establish `hU (a : ι) : ⊤ ≤ p ⁻¹ᵁ U a` using `fun z _ => by`. Establish `: z = IsLocalRing.closedPoint L` using `Subsingleton.elim (α := PrimeSpectrum L) _ _`. Rewrite using `[this]`.

Conclude with `hy a`. Set `φ : Γ(Sp L, ⊤) ≃+* L` to `(Scheme.ΓSpecIso (.of L)).commRingCatIsoToRingEquiv`. Set `N (a : ι) : Matrix (Fin (r a)) (Fin (r a)) Γ(Sp L, ⊤)` to `(M a).map (p.appLE (U a) ⊤ (hU a)).hom`. Establish `hsp (fl'' : ∀ a, Vert.Flag ((Scheme.Modules.pullback x).obj (E a)) (r a)) (hc : Carries Y.str E r fl p x w fl'') (a : ι) : Spans (fl'' a) ⊤ (pullCol x (e a) le_top (N a))` using `spans_pullCol_of_carries _ _ _ Y.str ι r E fl p x w fl'' hc ⊤ a (e a) (U a) le_top (M a) ⊤ (hU a) le_top (hM a)`. Establish `hc` using `carries_carried Y.str E r fl p x w`.

Establish `hq (a : ι) : (E a).IsQuasicoherent` using `(hE a).isQuasicoherent`. Establish `hN (a : ι) : IsUnit (N a).det` using `isUnit_det_of_spans x (he a) le_top (hsp _ hc a)`. Establish `hB (a : ι) : A'.map ((ratOf Y).val p) a = ((N a).map φ).transpose`. Use extensionality with `i j`. Establish `e₁ : A' a i j = valF (ratOf Y).pt (U a) (M a j i)`.

Rewrite using `[hAM a]`. Conclude with `(valF_fromSpecStalk _ _).symm`. Use `show (ratOf Y).val p (A' a i j) = _`. Rewrite using `[e₁]`. Conclude with `(GlobalTheory.ZH.RatModel.val_valF (M := ratOf Y) (y := p) (U := U a) (by rintro _ ⟨z, rfl⟩; exact hU a (x := z) trivial) _).trans (GlobalTheory.Points.valR_eq p (U a) (hU a) _)`.

Establish `key (a : ι)` using `exists_upper_iff φ (N a) (hN a) (h a)`. Simplify using `only [← hB] at key`. Prove the components needed by the constructor for the conclusion. Introduce `hc' a`. Use `(key a).1 (exists_upper_of_spans x (he a) le_top (hsp _ hc' a) (hfl' a))` as an intermediate fact.

Conclude with `⟨fun _ _ => trivial, this.1, trivial, fun i j _ hij => this.2 i j hij⟩`. Introduce `hP a i`. Take `⟨T, h₁, h₂, h₃⟩` from `(key a).2 ⟨(hP a).2.1, fun i j hij => (hP a).2.2.2 i j i.2 hij⟩`. Establish `h₄` using `spans_pullCol_mul x (e a) le_top (hsp _ hc a) h₁ h₂`. Rewrite `h₄` using `[← h₃]`.

Take `⟨e₁, he₁⟩` from `hc a i`. Take `⟨e₂, he₂⟩` from `steps_iso_of_spans_top _ _ _ _ _ _ h₄ (hfl' a) i`. Conclude with `⟨e₁ ≪≫ e₂, by rw [Iso.trans_hom, Category.assoc, he₂, he₁]⟩`.
-/
theorem carries_iff_par : ∀ (F : Type) [Field F] (Y : Var F) (ι : Type) [Fintype ι] (r : ι → ℕ) (E : ι → (Sp F).Modules) (e : ∀ a, Fin (r a) → Γ(E a, ⊤)) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback Y.str).obj (E a)) (r a)), (∀ a, IsVB (E a) (r a)) → (∀ a, IsFrame (e a)) → ∀ (L : Type) [Field L] (p : Sp L ⟶ Y.X) (x : Sp L ⟶ Sp F) (w : p ≫ Y.str = x) (h : Mat r L) (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback x).obj (E a)) (r a)), (∀ a, Spans (fl' a) ⊤ (pullCol x (e a) le_top ((h a).transpose.map (Scheme.ΓSpecIso (.of L)).inv.hom))) → ∀ A' : Mat r Y.Fn, AdFrame e fl (p (IsLocalRing.closedPoint L)) A' → (Carries Y.str E r fl p x w fl' ↔ Par r ⊤ (h * (A'.map ((ratOf Y).val p))⁻¹)) := by
  intro F _ Y ι _ r E e fl hE he L _ p x w h fl' hfl' A' hA
  choose U hy M hM hAM using hA
  have hU (a : ι) : ⊤ ≤ p ⁻¹ᵁ U a := fun z _ => by
    have : z = IsLocalRing.closedPoint L := Subsingleton.elim (α := PrimeSpectrum L) _ _
    rw [this]
    exact hy a
  let φ : Γ(Sp L, ⊤) ≃+* L := (Scheme.ΓSpecIso (.of L)).commRingCatIsoToRingEquiv
  let N (a : ι) : Matrix (Fin (r a)) (Fin (r a)) Γ(Sp L, ⊤) := (M a).map (p.appLE (U a) ⊤ (hU a)).hom
  have hsp (fl'' : ∀ a, Vert.Flag ((Scheme.Modules.pullback x).obj (E a)) (r a))
      (hc : Carries Y.str E r fl p x w fl'') (a : ι) : Spans (fl'' a) ⊤ (pullCol x (e a) le_top (N a)) :=
    spans_pullCol_of_carries _ _ _ Y.str ι r E fl p x w fl'' hc ⊤ a (e a) (U a) le_top (M a) ⊤ (hU a) le_top (hM a)
  have hc := carries_carried Y.str E r fl p x w
  have hq (a : ι) : (E a).IsQuasicoherent := (hE a).isQuasicoherent
  have hN (a : ι) : IsUnit (N a).det := isUnit_det_of_spans x (he a) le_top (hsp _ hc a)
  have hB (a : ι) : A'.map ((ratOf Y).val p) a = ((N a).map φ).transpose := by
    ext i j
    have e₁ : A' a i j = valF (ratOf Y).pt (U a) (M a j i) := by
      rw [hAM a]
      exact (valF_fromSpecStalk _ _).symm
    show (ratOf Y).val p (A' a i j) = _
    rw [e₁]
    exact (GlobalTheory.ZH.RatModel.val_valF (M := ratOf Y) (y := p) (U := U a)
      (by rintro _ ⟨z, rfl⟩; exact hU a (x := z) trivial) _).trans (GlobalTheory.Points.valR_eq p (U a) (hU a) _)
  have key (a : ι) := exists_upper_iff φ (N a) (hN a) (h a)
  simp only [← hB] at key
  constructor
  · intro hc' a
    have := (key a).1 (exists_upper_of_spans x (he a) le_top (hsp _ hc' a) (hfl' a))
    exact ⟨fun _ _ => trivial, this.1, trivial, fun i j _ hij => this.2 i j hij⟩
  · intro hP a i
    obtain ⟨T, h₁, h₂, h₃⟩ := (key a).2 ⟨(hP a).2.1, fun i j hij => (hP a).2.2.2 i j i.2 hij⟩
    have h₄ := spans_pullCol_mul x (e a) le_top (hsp _ hc a) h₁ h₂
    rw [← h₃] at h₄
    obtain ⟨e₁, he₁⟩ := hc a i
    obtain ⟨e₂, he₂⟩ := steps_iso_of_spans_top _ _ _ _ _ _ h₄ (hfl' a) i
    exact ⟨e₁ ≪≫ e₂, by rw [Iso.trans_hom, Category.assoc, he₂, he₁]⟩

end GlobalTheory.FlagOverField.AdCarr

import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerVectorBlockTriangularFrameChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagNeZeroOfTriangularIndependentStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartGluingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesAgreeOnLieEmbeddingChartStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.Uniq

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]
  rfl

/- English proof (translation)
The claim follows from `congrArg CommRingCat.Hom.hom (Spec.map_injective h)`.
-/
theorem spMap_injective {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem pt_congr {R A : Type} [CommRing R] [CommRing A] {N : ℕ} {c c' : R →+* A} (h : c = c') (v : Fin (N + 1) → A)
    (hv hv' : Ideal.span (Set.range v) = ⊤) : pt c v hv = pt c' v hv' := by
  subst h
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : Pre Y i₀} {L : FinLB (Y Z.i).X} {aff : ∀ i, IsAffineOpen (L.U i)} {M : ℕ} {crd : Crd (Y Z.i).t L M}
  {ι : Fin Z.m → Fin L.n} {ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)}
  {g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)}

/- English proof (translation)
Rewrite `hψ`, `hf`, `hs` using `[Category.assoc]`. Rewrite `hs` using `[h.ty]`. Take `⟨hu, e⟩` from `GlobalTheory.T.pre_model_chart_gluing E H Dw Xo p W Y i₀ Z L aff M crd ι ρ g h k a i φ ψ hψ en`. Establish `hfr` using `h.frame a k φ`. Take `⟨d, hd⟩` from `(GlobalTheory.T.frames_agree_on_lie_embedding_chart E H Dw _ _ _ _ L aff M crd h.emb i k ψ _ _ _ _ _ hψ hfr hf).1.1 hs`.

Establish `hli` using `(GlobalTheory.T.frames_agree_on_lie_embedding_chart E H Dw _ _ _ _ L aff M crd h.emb i k ψ _ _ _ _ _ hψ hf hf).2.1`. Establish `hne` using `GlobalTheory.T.diag_ne_zero_of_triangular_independent _ _ k _ _ _ d hli hd`. Establish `hp` using `GlobalTheory.FlagEmb.plk_tri _ _ k M _ _ d _ _ hd en.2.2`. Establish `h0 : (∏ l, d (en.2.1 l)) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun l _ => hne _`. Establish `hp' : plk (fun z : Let Dw.mult => crd i k ψ (u z.1 z.2)) en.2.1 = Units.mk0 _ h0 • _` using `hp`.

Use `⟨hp' ▸ span_range_units_smul hu _, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, e]`. Conclude with `(pt_eq_pt_iff _ _ _).2 ⟨_, hp'⟩`.
-/
theorem plk_adapted (h : Comparison₂ Z L aff crd ι ρ g) {k : Type} [Field k] (a : Fin Z.m) (i : Fin L.n)
    (φ : Γ(Z.X, (Z.U a).1) →+* k) (ψ : Γ((Y Z.i).X, L.U i) →+* k) (u : Vecs Dw (Y Z.i).t k)
    (hψ : spMap ψ ≫ (aff i).fromSpec = (spMap φ ≫ Z.chart a) ≫ Z.π)
    (hf : IsFrame (Y Z.i).t (φ.comp (Z.alg a)) ((spMap φ ≫ Z.chart a) ≫ Z.π) u)
    (hs : SameFlag Z.ty (Y Z.i).t ((spMap φ ≫ Z.chart a) ≫ Z.π) ((Z.fr a).bc φ) u) (en : En Dw.mult) :
    ∃ hu, (spMap φ ≫ Z.chart a) ≫ g en = pt (φ.comp ((Z.alg a).comp (Z.i.c.V W).subtype))
      (plk (fun z : Let Dw.mult => crd i k ψ (u z.1 z.2)) en.2.1) hu := by
  rw [Category.assoc] at hψ hf hs
  rw [h.ty] at hs
  obtain ⟨hu, e⟩ := GlobalTheory.T.pre_model_chart_gluing E H Dw Xo p W Y i₀ Z L aff M crd ι ρ g h k a i φ ψ hψ en
  have hfr := h.frame a k φ
  obtain ⟨d, hd⟩ := (GlobalTheory.T.frames_agree_on_lie_embedding_chart E H Dw _ _ _ _ L aff M crd h.emb i k ψ _ _ _ _ _ hψ hfr hf).1.1 hs
  have hli := (GlobalTheory.T.frames_agree_on_lie_embedding_chart E H Dw _ _ _ _ L aff M crd h.emb i k ψ _ _ _ _ _ hψ hf hf).2.1
  have hne := GlobalTheory.T.diag_ne_zero_of_triangular_independent _ _ k _ _ _ d hli hd
  have hp := GlobalTheory.FlagEmb.plk_tri _ _ k M _ _ d _ _ hd en.2.2
  have h0 : (∏ l, d (en.2.1 l)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun l _ => hne _
  have hp' : plk (fun z : Let Dw.mult => crd i k ψ (u z.1 z.2)) en.2.1 = Units.mk0 _ h0 • _ := hp
  refine ⟨hp' ▸ span_range_units_smul hu _, ?_⟩
  rw [Category.assoc, e]
  exact (pt_eq_pt_iff _ _ _).2 ⟨_, hp'⟩

/- English proof (translation)
Rewrite using `[spMap_comp_eq, ← h.alg_s a]`. Simplify using `only [Category.assoc]`.
-/
theorem spMap_alg (h : Comparison₂ Z L aff crd ι ρ g) {k : Type} [Field k] (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* k) :
    spMap (φ.comp ((Z.alg a).comp (Z.i.c.V W).subtype)) = ((spMap φ ≫ Z.chart a) ≫ Z.π) ≫ (Y Z.i).s := by
  rw [spMap_comp_eq, ← h.alg_s a]
  simp only [Category.assoc]

end GlobalTheory.FlagEmb.Uniq

namespace GlobalTheory.FlagEmb

open Uniq in

/- English proof (translation)
Introduce `E _ _ _ H Dw Xo p W Y i₀ Z L aff M crd ι ρ g h k _ w w' u hπ ⟨a, φ, hw, hf, hs⟩ ⟨a', φ', hw', hf', hs'⟩`. Substitute `hw hw'` using the available equality. Establish `hψ : spMap (φ.comp (ρ a)) ≫ (aff (ι a)).fromSpec = (spMap φ ≫ Z.chart a) ≫ Z.π`. Rewrite using `[spMap_comp_eq, Category.assoc, h.res, Category.assoc]`. Use `h.inj k _ _ ?_ hπ fun en => ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[← h.cover]`. Use `Set.mem_iUnion.2 ⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[← (Z.U a).2.range_fromSpec]`. Conclude with `⟨spMap φ y, by simp [Pre.chart]⟩`.

Take `⟨hu, e⟩` from `plk_adapted h a _ φ _ u hψ hf hs en`. Take `⟨hu', e'⟩` from `plk_adapted h a' _ φ' _ u (hψ.trans hπ) hf' hs' en`. Rewrite using `[e, e']`. Use `pt_congr (spMap_injective ?_) _ _ _` and prove the remaining obligations. Rewrite using `[spMap_alg h, spMap_alg h, hπ]`.
-/
theorem flagAt_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Pre Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M) (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)) (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Comparison₂ Z L aff crd ι ρ g → ∀ (k : Type) [Field k] (w w' : Sp k ⟶ Z.X) (u : Vecs Dw (Y Z.i).t k), w ≫ Z.π = w' ≫ Z.π → Z.FlagAt w u → Z.FlagAt w' u → w = w' := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z L aff M crd ι ρ g h k _ w w' u hπ ⟨a, φ, hw, hf, hs⟩ ⟨a', φ', hw', hf', hs'⟩
  subst hw hw'
  have hψ : spMap (φ.comp (ρ a)) ≫ (aff (ι a)).fromSpec = (spMap φ ≫ Z.chart a) ≫ Z.π := by
    rw [spMap_comp_eq, Category.assoc, h.res, Category.assoc]
  refine h.inj k _ _ ?_ hπ fun en => ?_
  · rintro _ ⟨y, rfl⟩
    rw [← h.cover]
    refine Set.mem_iUnion.2 ⟨a, ?_⟩
    rw [← (Z.U a).2.range_fromSpec]
    exact ⟨spMap φ y, by simp [Pre.chart]⟩
  · obtain ⟨hu, e⟩ := plk_adapted h a _ φ _ u hψ hf hs en
    obtain ⟨hu', e'⟩ := plk_adapted h a' _ φ' _ u (hψ.trans hπ) hf' hs' en
    rw [e, e']
    refine pt_congr (spMap_injective ?_) _ _ _
    rw [spMap_alg h, spMap_alg h, hπ]

end GlobalTheory.FlagEmb

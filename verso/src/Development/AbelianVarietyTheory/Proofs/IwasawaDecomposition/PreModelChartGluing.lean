import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.PlkPt

/- English proof (translation)
Use function extensionality and compare the values at `q`. Establish `h` using `Matrix.det_smul (Matrix.of fun l l' => c (e l) (plE M k q l')) γ`. Rewrite `h` using `[Fintype.card_fin]`. Conclude with `h`.
-/
theorem plk_smul {S ι : Type} [CommRing S] {M k : ℕ} (γ : S) (c : ι → Fin (M + 1) → S) (e : Fin k → ι) :
    plk (fun z => γ • c z) e = γ ^ k • plk c e := by
  funext q
  have h := Matrix.det_smul (Matrix.of fun l l' => c (e l) (plE M k q l')) γ
  rw [Fintype.card_fin] at h
  exact h

/- English proof (translation)
Rewrite using `[valF, dif_pos h]`. Conclude with `((f.isUnit.map _).map _).ne_zero`.
-/
theorem valF_unit_ne {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)ˣ) : valF x U f.val ≠ 0 := by
  rw [valF, dif_pos h]
  exact ((f.isUnit.map _).map _).ne_zero

/- English proof (translation)
Establish `h` using `(spMap φ).preimage_mono hU.fromSpec_preimage_self.ge`. Conclude with `h`.
-/
theorem top_le_pre {A : Type} [CommRing A] {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (φ : Γ(X, U) →+* A) :
    ⊤ ≤ (spMap φ ≫ hU.fromSpec) ⁻¹ᵁ U := by
  have h := (spMap φ).preimage_mono hU.fromSpec_preimage_self.ge
  exact h

/- English proof (translation)
Establish `: dualMap (RingHom.id R) = RingHom.id _`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [dualMap]`. Rewrite using `[this]`. Conclude with `Spec.map_id _`.
-/
theorem spMap_dualMap_id' (R : Type) [CommRing R] : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
  have : dualMap (RingHom.id R) = RingHom.id _ := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [dualMap]
  rw [this]
  exact Spec.map_id _

/- English proof (translation)
Introduce `E _ _ _ H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T k _ a i φ ψ hψ en`. Take `⟨hu, h⟩` from `T.plk a en`. Establish `hφ : spMap (φ.comp (ρ a)) ≫ (aff (ι a)).fromSpec = spMap φ ≫ Z.chart a ≫ Z.π`. Rewrite using `[← T.res a, ← Category.assoc]`. Use `congr 1`.

Conclude with `Spec.map_comp _ _`. Establish `tan : ∀ z : Let Dw.mult, IsTanAtG (Y Z.i).t (spMap (ρ a) ≫ (aff (ι a)).fromSpec) (Z.fr a z.1 z.2)`. Introduce `z`. Establish `h1` using `((T.frame a _ (RingHom.id _)).1 z.1 z.2).1`. Establish `h2 : spMap (RingHom.id Γ(Z.X, (Z.U a).1)) = 𝟙 _` using `Spec.map_id _`.

Rewrite `h1` using `[h2, Category.id_comp, Vecs.bc, spMap_dualMap_id', Category.id_comp]`. Rewrite using `[T.res a]`. Conclude with `h1`. Establish `nat : (fun z : Let Dw.mult => φ ∘ crd (ι a) _ (ρ a) (Z.fr a z.1 z.2)) = fun z : Let Dw.mult => crd (ι a) k (φ.comp (ρ a)) ((Z.fr a).bc φ z.1 z.2)`. Use function extensionality and compare the values at `fun z => (T.emb.nat (ι a) _ k (ρ a) φ _ (tan z)).symm`.

Establish `hγ : valF (spMap ψ ≫ (aff i).fromSpec) _ (L.g i (ι a)).val ≠ 0`. Use `valF_unit_ne _ _ ?_ _` and prove the remaining obligations. Establish `h1` using `top_le_pre (aff i) ψ`. Establish `h2` using `top_le_pre (aff (ι a)) (φ.comp (ρ a))`. Rewrite `h2` using `[hφ, ← hψ]`.

Conclude with `le_inf h1 h2`. Establish `tr : (fun z : Let Dw.mult => crd i k ψ ((Z.fr a).bc φ z.1 z.2)) = fun z : Let Dw.mult => valF (spMap ψ ≫ (aff i).fromSpec) _ (L.g i (ι a)).val • crd (ι a) k (φ.comp (ρ a)) ((Z.fr a).bc φ z.1 z.2)`. Use function extensionality and compare the values at `fun z => T.emb.trans i (ι a) k ψ (φ.comp (ρ a)) _ (hψ.trans hφ.symm) (by rw [hψ]; exact ((T.frame a k φ).1 z.1 z.2).1)`. Establish `key : plk (fun z : Let Dw.mult => crd i k ψ ((Z.fr a).bc φ z.1 z.2)) en.2.1 = (Units.mk0 _ hγ) ^ en.1 • (φ ∘ plk (fun z : Let Dw.mult => crd (ι a) _ (ρ a) (Z.fr a z.1 z.2)) en.2.1)`. Rewrite using `[map_plk, nat, tr, plk_smul]`.

Both sides reduce to the same expression. Establish `hv` using `span_range_comp_eq_top _ hu φ`. Use `⟨key ▸ span_range_units_smul hv _, ?_⟩` and prove the remaining obligations. Rewrite using `[h, GlobalTheory.ProjSpace.spMap_pt]`. Conclude with `(pt_eq_pt_iff _ _ _).2 ⟨_, key⟩`.
-/
theorem plk_pt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Pre Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M) (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)) (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Comparison₂ Z L aff crd ι ρ g → ∀ (k : Type) [Field k] a i (φ : Γ(Z.X, (Z.U a).1) →+* k) (ψ : Γ((Y Z.i).X, L.U i) →+* k), spMap ψ ≫ (aff i).fromSpec = spMap φ ≫ Z.chart a ≫ Z.π → ∀ en : En Dw.mult, ∃ hu, spMap φ ≫ Z.chart a ≫ g en = pt (φ.comp ((Z.alg a).comp (Z.i.c.V W).subtype)) (plk (fun z : Let Dw.mult => crd i k ψ ((Z.fr a).bc φ z.1 z.2)) en.2.1) hu := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T k _ a i φ ψ hψ en
  obtain ⟨hu, h⟩ := T.plk a en
  have hφ : spMap (φ.comp (ρ a)) ≫ (aff (ι a)).fromSpec = spMap φ ≫ Z.chart a ≫ Z.π := by
    rw [← T.res a, ← Category.assoc]
    congr 1
    exact Spec.map_comp _ _
  have tan : ∀ z : Let Dw.mult, IsTanAtG (Y Z.i).t (spMap (ρ a) ≫ (aff (ι a)).fromSpec) (Z.fr a z.1 z.2) := by
    intro z
    have h1 := ((T.frame a _ (RingHom.id _)).1 z.1 z.2).1
    have h2 : spMap (RingHom.id Γ(Z.X, (Z.U a).1)) = 𝟙 _ := Spec.map_id _
    rw [h2, Category.id_comp, Vecs.bc, spMap_dualMap_id', Category.id_comp] at h1
    rw [T.res a]
    exact h1
  have nat : (fun z : Let Dw.mult => φ ∘ crd (ι a) _ (ρ a) (Z.fr a z.1 z.2)) =
      fun z : Let Dw.mult => crd (ι a) k (φ.comp (ρ a)) ((Z.fr a).bc φ z.1 z.2) :=
    funext fun z => (T.emb.nat (ι a) _ k (ρ a) φ _ (tan z)).symm
  have hγ : valF (spMap ψ ≫ (aff i).fromSpec) _ (L.g i (ι a)).val ≠ 0 := by
    refine valF_unit_ne _ _ ?_ _
    have h1 := top_le_pre (aff i) ψ
    have h2 := top_le_pre (aff (ι a)) (φ.comp (ρ a))
    rw [hφ, ← hψ] at h2
    exact le_inf h1 h2
  have tr : (fun z : Let Dw.mult => crd i k ψ ((Z.fr a).bc φ z.1 z.2)) =
      fun z : Let Dw.mult => valF (spMap ψ ≫ (aff i).fromSpec) _ (L.g i (ι a)).val •
        crd (ι a) k (φ.comp (ρ a)) ((Z.fr a).bc φ z.1 z.2) :=
    funext fun z => T.emb.trans i (ι a) k ψ (φ.comp (ρ a)) _ (hψ.trans hφ.symm)
      (by rw [hψ]; exact ((T.frame a k φ).1 z.1 z.2).1)
  have key : plk (fun z : Let Dw.mult => crd i k ψ ((Z.fr a).bc φ z.1 z.2)) en.2.1 =
      (Units.mk0 _ hγ) ^ en.1 • (φ ∘ plk (fun z : Let Dw.mult => crd (ι a) _ (ρ a) (Z.fr a z.1 z.2)) en.2.1) := by
    rw [map_plk, nat, tr, plk_smul]
    rfl
  have hv := span_range_comp_eq_top _ hu φ
  refine ⟨key ▸ span_range_units_smul hv _, ?_⟩
  rw [h, GlobalTheory.ProjSpace.spMap_pt]
  exact (pt_eq_pt_iff _ _ _).2 ⟨_, key⟩

end GlobalTheory.FlagEmb.PlkPt

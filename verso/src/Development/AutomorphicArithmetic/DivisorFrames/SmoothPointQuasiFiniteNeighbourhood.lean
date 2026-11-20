import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

/- English proof (translation)
Take `⟨n, g, hgC, hg⟩` from `RingHom.IsStandardSmooth.exists_etale_mvPolynomial hφ`. Use `choose r hr using fun i : Fin n => hs (ψ.hom (g (MvPolynomial.X i)))`. Set `g' : CommRingCat.of (MvPolynomial (Fin n) R) ⟶ S` to `CommRingCat.ofHom g`. Set `e : CommRingCat.of (MvPolynomial (Fin n) R) ⟶ R` to `CommRingCat.ofHom (MvPolynomial.eval r)`. Establish `hφC (a : R) : g (MvPolynomial.C a) = φ.hom a` using `congr($hgC a)`.

Establish `hw : g' ≫ ψ = e ≫ (φ ≫ ψ)` using `by ext1`. Use `MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)` and prove the remaining obligations. Simplify using `[g', e, hφC]`. Simplify `(hr i).symm` using `[g', e]`. Use `⟨pushout e g', pushout.inr _ _, pushout.desc (φ ≫ ψ) ψ hw.symm, pushout.inr_desc _ _ _, ?_⟩` and prove the remaining obligations.

Establish `h1 : φ ≫ pushout.inr e g' = pushout.inl e g'`. Establish `h2 : φ = CommRingCat.ofHom (MvPolynomial.C (σ` using `Fin n)) ≫ g' := by`. Use extensionality with `a`. Simplify using `[g', hφC]`. Establish `h3 : CommRingCat.ofHom (MvPolynomial.C (σ` using `Fin n)) ≫ e = 𝟙 R := by ext1; ext a; exact MvPolynomial.eval_C a`.

Rewrite using `[h2, Category.assoc, ← pushout.condition, ← Category.assoc, h3, Category.id_comp]`. Rewrite using `[h1]`. Conclude with `RingHom.Etale.isStableUnderBaseChange.pushout_inl RingHom.Etale.respectsIso e g' hg`.
-/
private theorem ring_qsec {R S K : CommRingCat.{0}} (φ : R ⟶ S) (hφ : φ.hom.IsStandardSmooth) (ψ : S ⟶ K)
    (hs : Function.Surjective (φ ≫ ψ).hom) :
    ∃ (T : CommRingCat.{0}) (π : S ⟶ T) (ψ₀ : T ⟶ K), π ≫ ψ₀ = ψ ∧ (φ ≫ π).hom.Etale := by
  obtain ⟨n, g, hgC, hg⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial hφ
  choose r hr using fun i : Fin n => hs (ψ.hom (g (MvPolynomial.X i)))
  let g' : CommRingCat.of (MvPolynomial (Fin n) R) ⟶ S := CommRingCat.ofHom g
  let e : CommRingCat.of (MvPolynomial (Fin n) R) ⟶ R :=
    CommRingCat.ofHom (MvPolynomial.eval r)
  have hφC (a : R) : g (MvPolynomial.C a) = φ.hom a := congr($hgC a)
  have hw : g' ≫ ψ = e ≫ (φ ≫ ψ) := by
    ext1
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp [g', e, hφC]
    · simpa [g', e] using (hr i).symm
  refine ⟨pushout e g', pushout.inr _ _, pushout.desc (φ ≫ ψ) ψ hw.symm, pushout.inr_desc _ _ _, ?_⟩
  have h1 : φ ≫ pushout.inr e g' = pushout.inl e g' := by
    have h2 : φ = CommRingCat.ofHom (MvPolynomial.C (σ := Fin n)) ≫ g' := by
      ext a; simp [g', hφC]
    have h3 : CommRingCat.ofHom (MvPolynomial.C (σ := Fin n)) ≫ e = 𝟙 R := by
      ext1; ext a; exact MvPolynomial.eval_C a
    rw [h2, Category.assoc, ← pushout.condition, ← Category.assoc, h3, Category.id_comp]
  rw [h1]
  exact RingHom.Etale.isStableUnderBaseChange.pushout_inl RingHom.Etale.respectsIso e g' hg

/- English proof (translation)
Introduce `k _ _ C _ hC G hG p hp g`. Establish `: Smooth (strHom k C)` using `have := hC.1`. Use the proof step `SmoothOfRelativeDimension.smooth 1 _`. Establish `: IsLocallyNoetherian C` using `LocallyOfFiniteType.isLocallyNoetherian (strHom k C)`. Set `g₁ : Spec (.of k) ⟶ G.left` to `g.left`.

Establish `hg₁ : g₁ ≫ G.hom = p` using `Over.w g`. Take `⟨U, hU, V, hV, hx, e, hφ⟩` from `Smooth.exists_isStandardSmooth G.hom (g₁ (IsLocalRing.closedPoint k))`. Establish `hr : Set.range g₁ ⊆ Set.range hV.fromSpec`. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[hV.range_fromSpec, Subsingleton.elim y (IsLocalRing.closedPoint k)]`.

Conclude with `hx`. Take `⟨ψ, hψ⟩` from `Spec.map_surjective (IsOpenImmersion.lift hV.fromSpec g₁ hr)`. Establish `hψ' : Spec.map ψ ≫ hV.fromSpec = g₁` using `by rw [hψ, IsOpenImmersion.lift_fac]`. Establish `hφ' : Spec.map (G.hom.appLE U V e) ≫ hU.fromSpec = hV.fromSpec ≫ G.hom` using `IsAffineOpen.SpecMap_appLE_fromSpec G.hom hU hV e`. Take `⟨a, ha⟩` from `Spec.map_surjective (R := .of k) (hU.fromSpec ≫ strHom k C)`.

Establish `hs : a ≫ G.hom.appLE U V e ≫ ψ = 𝟙 _`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, Spec.map_comp, ha, Category.assoc, reassoc_of% hφ', reassoc_of% hψ', reassoc_of% hg₁, Spec.map_id]`. Conclude with `hp`. Take `⟨T, π, ψ₀, hπ, hE⟩` from `ring_qsec _ hφ ψ (fun y => ⟨a.hom y, congr(($hs).hom y)⟩)`.

Establish `hEt : Etale (Spec.map (G.hom.appLE U V e ≫ π))`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Etale)]` and apply the resulting hypothesis. Establish `hZ : (Spec.map π ≫ hV.fromSpec) ≫ G.hom = Spec.map (G.hom.appLE U V e ≫ π) ≫ hU.fromSpec`. Rewrite using `[Spec.map_comp, Category.assoc, Category.assoc, hφ']`. Establish `hg₀ : Spec.map ψ₀ ≫ Spec.map π ≫ hV.fromSpec = g₁`.

Rewrite using `[← Spec.map_comp_assoc, hπ, hψ']`. Use `⟨Over.mk (Spec.map (G.hom.appLE U V e ≫ π) ≫ hU.fromSpec), Over.homMk (Spec.map π ≫ hV.fromSpec) hZ, Over.homMk (Spec.map ψ₀) ?_, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Spec.map ψ₀ ≫ Spec.map (G.hom.appLE U V e ≫ π) ≫ hU.fromSpec = p`. Rewrite using `[← hZ, ← Category.assoc, hg₀, hg₁]`. Establish `: Etale (Spec.map (G.hom.appLE U V e ≫ π) ≫ hU.fromSpec)` using `inferInstance`.

Establish `: QuasiSeparatedSpace C` using `inferInstance`. Establish `: LocallyQuasiFinite (Spec.map (G.hom.appLE U V e ≫ π))`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)]`. Use `algebraize [(G.hom.appLE U V e ≫ π).hom]`. Conclude with `inferInstanceAs (Algebra.QuasiFinite _ _)`.

Apply the tactic sequence `refine ⟨?_, ?_, quasiCompact_of_compactSpace (X := Spec T) _, ?_⟩ <;> simp only [Over.mk_hom] <;> infer_instance`. Use `ext1`. Conclude with `hg₀`.
-/
theorem UpperTheory.smooth_point_quasi_finite_neighbourhood :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C →
        ∀ (G : Over C), Smooth G.hom → ∀ p : Sp k ⟶ C, p ≫ strHom k C = 𝟙 _ → ∀ g : Over.mk p ⟶ G,
        ∃ (Z : Over C) (z : Z ⟶ G) (g₀ : Over.mk p ⟶ Z), QFin Z ∧ g₀ ≫ z = g := by
  intro k _ _ C _ hC G hG p hp g
  have : Smooth (strHom k C) := have := hC.1; SmoothOfRelativeDimension.smooth 1 _
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (strHom k C)
  let g₁ : Spec (.of k) ⟶ G.left := g.left
  have hg₁ : g₁ ≫ G.hom = p := Over.w g
  obtain ⟨U, hU, V, hV, hx, e, hφ⟩ := Smooth.exists_isStandardSmooth G.hom (g₁ (IsLocalRing.closedPoint k))
  have hr : Set.range g₁ ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨y, rfl⟩
    rw [hV.range_fromSpec, Subsingleton.elim y (IsLocalRing.closedPoint k)]
    exact hx
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (IsOpenImmersion.lift hV.fromSpec g₁ hr)
  have hψ' : Spec.map ψ ≫ hV.fromSpec = g₁ := by rw [hψ, IsOpenImmersion.lift_fac]
  have hφ' : Spec.map (G.hom.appLE U V e) ≫ hU.fromSpec = hV.fromSpec ≫ G.hom :=
    IsAffineOpen.SpecMap_appLE_fromSpec G.hom hU hV e
  obtain ⟨a, ha⟩ := Spec.map_surjective (R := .of k) (hU.fromSpec ≫ strHom k C)
  have hs : a ≫ G.hom.appLE U V e ≫ ψ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, ha, Category.assoc, reassoc_of% hφ', reassoc_of% hψ',
      reassoc_of% hg₁, Spec.map_id]
    exact hp
  obtain ⟨T, π, ψ₀, hπ, hE⟩ := ring_qsec _ hφ ψ (fun y => ⟨a.hom y, congr(($hs).hom y)⟩)
  have hEt : Etale (Spec.map (G.hom.appLE U V e ≫ π)) := by
    rwa [HasRingHomProperty.Spec_iff (P := @Etale)]
  have hZ : (Spec.map π ≫ hV.fromSpec) ≫ G.hom = Spec.map (G.hom.appLE U V e ≫ π) ≫ hU.fromSpec := by
    rw [Spec.map_comp, Category.assoc, Category.assoc, hφ']
  have hg₀ : Spec.map ψ₀ ≫ Spec.map π ≫ hV.fromSpec = g₁ := by
    rw [← Spec.map_comp_assoc, hπ, hψ']
  refine ⟨Over.mk (Spec.map (G.hom.appLE U V e ≫ π) ≫ hU.fromSpec),
    Over.homMk (Spec.map π ≫ hV.fromSpec) hZ, Over.homMk (Spec.map ψ₀) ?_, ?_, ?_⟩
  · change Spec.map ψ₀ ≫ Spec.map (G.hom.appLE U V e ≫ π) ≫ hU.fromSpec = p
    rw [← hZ, ← Category.assoc, hg₀, hg₁]
  · have : Etale (Spec.map (G.hom.appLE U V e ≫ π) ≫ hU.fromSpec) := inferInstance
    have : QuasiSeparatedSpace C := inferInstance
    have : LocallyQuasiFinite (Spec.map (G.hom.appLE U V e ≫ π)) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)]
      algebraize [(G.hom.appLE U V e ≫ π).hom]
      exact inferInstanceAs (Algebra.QuasiFinite _ _)
    refine ⟨?_, ?_, quasiCompact_of_compactSpace (X := Spec T) _, ?_⟩ <;> simp only [Over.mk_hom] <;> infer_instance
  · ext1
    exact hg₀

import Mathlib
import Development.AutomorphicArithmetic.DivisorFrames.FlagCarriesEigenframe
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsMatch
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
private theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

/- English proof (translation)
Rewrite using `[← sp_comp]`. Use `congr 1`. Apply the tactic sequence `ext r <;> simp [dualMap]`.
-/
private theorem dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (dualMap (g.comp f)) = spMap (dualMap g) ≫ spMap (dualMap f) := by
  rw [← sp_comp]
  congr 1
  ext r <;> simp [dualMap]

/- English proof (translation)
Use `letI := a.toAlgebra`. Establish `h1 : Flat (spMap a)`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`. Conclude with `(inferInstance : Module.Flat k K)`. Establish `h2 : Surjective (spMap a)` using `⟨fun y => ⟨closedPoint K, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩`.

Conclude with `Flat.epi_of_flat_of_surjective _`.
-/
private theorem epi_sp {k K : Type} [Field k] [Field K] (a : k →+* K) : Epi (spMap a) := by
  letI := a.toAlgebra
  have h1 : Flat (spMap a) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (inferInstance : Module.Flat k K)
  have h2 : Surjective (spMap a) := ⟨fun y => ⟨closedPoint K, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Use `⟨by rw [hx, h1, sp_comp, Category.assoc], by rw [hφ, h2, RingHom.comp_assoc], fun τ i => ?_⟩` and prove the remaining obligations. Take `⟨cf, c1, c2, c3⟩` from `h3 τ i`. Use `⟨fun a => χ (cf a), by simp [c1], fun a ha => by simp [c2 a ha], ?_⟩` and prove the remaining obligations. Rewrite using `[hg τ i]`.

Simplify using `only [dual_comp, Category.assoc]`. Conclude with `GlobalTheory.GradedPieces.comb_map χ hx.symm c3`.
-/
private theorem tri_map {R k K : Type} [CommRing R] [CommRing k] [CommRing K] {φ₁ : c.F →+* R} {x₁ : Sp R ⟶ T.X}
    {φ : c.F →+* k} {x : Sp k ⟶ T.X} {φ' : c.F →+* K} {x' : Sp K ⟶ T.X} {f : EigFrame T φ₁ x₁} {g : EigFrame T φ x}
    {g' : EigFrame T φ' x'} {ψ : R →+* k} {χ : k →+* K} {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ}
    (h : f.Tri ψ g t) (hg : g.IsMap χ g') (hφ : φ' = χ.comp φ) (hx : x' = spMap χ ≫ x) :
    f.Tri (χ.comp ψ) g' (fun τ i => Units.map χ.toMonoidHom (t τ i)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [hx, h1, sp_comp, Category.assoc], by rw [hφ, h2, RingHom.comp_assoc], fun τ i => ?_⟩
  obtain ⟨cf, c1, c2, c3⟩ := h3 τ i
  refine ⟨fun a => χ (cf a), by simp [c1], fun a ha => by simp [c2 a ha], ?_⟩
  rw [hg τ i]
  simp only [dual_comp, Category.assoc]
  exact GlobalTheory.GradedPieces.comb_map χ hx.symm c3

/- English proof (translation)
Establish `e1 : x = spMap ψ ≫ x₁` using `by haveI := epi_sp χ`. Rewrite using `[← cancel_epi (spMap χ), ← hx, h.1, sp_comp, Category.assoc]`. Establish `e2 : φ = ψ.comp φ₁` using `RingHom.ext fun a => χ.injective (RingHom.congr_fun (hφ.symm.trans h.2.1) a)`. Take `⟨f₀, hf₀⟩` from `f.exists_isMap ψ e2 e1`. Take `⟨f', hf'⟩` from `f₀.exists_isMap χ hφ hx`.

Establish `hf : f.IsMap (χ.comp ψ) f'` using `fun τ i => by rw [hf' τ i, hf₀ τ i, dual_comp, Category.assoc]`. Establish `key : ∀ τ, (∀ a i, i < a → f₀.co g τ a i = 0) ∧ ∀ i, f₀.co g τ i i ≠ 0` using `fun τ => by`. Use `EigFrame.Tri.co τ h hf` as an intermediate fact. Rewrite `this` using `[EigFrame.IsMap.co τ hf' hg hx]`. Use `⟨fun a i hi => χ.injective ((this.1 a i hi).trans (map_zero χ).symm), fun i h0 => ?_⟩` and prove the remaining obligations.

Establish `h2` using `this.2 i`. Rewrite `h2` using `[Matrix.map_apply, h0, map_zero]`. Conclude with `(t τ i).ne_zero h2.symm`. Use `⟨fun τ i => Units.mk0 _ ((key τ).2 i), e1, e2, fun τ i => ⟨fun a => f₀.co g τ a i, rfl, fun a ha => (key τ).1 a i ha, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← funext (hf₀ τ)]`.

Conclude with `f₀.co_spec g τ i`.
-/
private theorem tri_descend {R k K : Type} [CommRing R] [Field k] [Field K] {φ₁ : c.F →+* R} {x₁ : Sp R ⟶ T.X}
    {φ : c.F →+* k} {x : Sp k ⟶ T.X} {φ' : c.F →+* K} {x' : Sp K ⟶ T.X} {f : EigFrame T φ₁ x₁} {g : EigFrame T φ x}
    {g' : EigFrame T φ' x'} {ψ : R →+* k} {χ : k →+* K} {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ}
    (h : f.Tri (χ.comp ψ) g' t) (hg : g.IsMap χ g') (hφ : φ' = χ.comp φ) (hx : x' = spMap χ ≫ x) :
    ∃ t₀, f.Tri ψ g t₀ := by
  have e1 : x = spMap ψ ≫ x₁ := by
    haveI := epi_sp χ
    rw [← cancel_epi (spMap χ), ← hx, h.1, sp_comp, Category.assoc]
  have e2 : φ = ψ.comp φ₁ := RingHom.ext fun a => χ.injective (RingHom.congr_fun (hφ.symm.trans h.2.1) a)
  obtain ⟨f₀, hf₀⟩ := f.exists_isMap ψ e2 e1
  obtain ⟨f', hf'⟩ := f₀.exists_isMap χ hφ hx
  have hf : f.IsMap (χ.comp ψ) f' := fun τ i => by rw [hf' τ i, hf₀ τ i, dual_comp, Category.assoc]
  have key : ∀ τ, (∀ a i, i < a → f₀.co g τ a i = 0) ∧ ∀ i, f₀.co g τ i i ≠ 0 := fun τ => by
    have := EigFrame.Tri.co τ h hf
    rw [EigFrame.IsMap.co τ hf' hg hx] at this
    refine ⟨fun a i hi => χ.injective ((this.1 a i hi).trans (map_zero χ).symm), fun i h0 => ?_⟩
    have h2 := this.2 i
    rw [Matrix.map_apply, h0, map_zero] at h2
    exact (t τ i).ne_zero h2.symm
  refine ⟨fun τ i => Units.mk0 _ ((key τ).2 i), e1, e2, fun τ i => ⟨fun a => f₀.co g τ a i, rfl,
    fun a ha => (key τ).1 a i ha, ?_⟩⟩
  rw [← funext (hf₀ τ)]
  exact f₀.co_spec g τ i

/- English proof (translation)
Take `⟨y, ψ, φ₁, f, t, t', h1, h2, h3⟩` from `h`. Conclude with `⟨y, χ.comp ψ, φ₁, f, t, _, by rw [h1, sp_comp, Category.assoc], h2, tri_map h3 hg hφ hx⟩`.
-/
private theorem carries_map {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt T e) {k K : Type} [Field k] [Field K]
    {φ : c.F →+* k} {x : Sp k ⟶ T.X} {φ' : c.F →+* K} {x' : Sp K ⟶ T.X} {g : EigFrame T φ x}
    {g' : EigFrame T φ' x'} {χ : k →+* K} {p : Sp k ⟶ C.Y.X} (h : C.Carries p g)
    (hg : g.IsMap χ g') (hφ : φ' = χ.comp φ) (hx : x' = spMap χ ≫ x) : C.Carries (spMap χ ≫ p) g' := by
  obtain ⟨y, ψ, φ₁, f, t, t', h1, h2, h3⟩ := h
  exact ⟨y, χ.comp ψ, φ₁, f, t, _, by rw [h1, sp_comp, Category.assoc], h2, tri_map h3 hg hφ hx⟩

end

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β T F _ e σ N U Φ k _ φ x hx g`. Use `haveI : CharZero k := φ.charZero_iff φ.injective |>.1 inferInstance`. Set `K` to `AlgebraicClosure k`. Set `a : k →+* K` to `algebraMap k K`. Use `haveI := epi_sp a`.

Establish `hxa : (spMap a ≫ x) ≫ genι T = spMap a ≫ x ≫ genι T` using `Category.assoc _ _ _`. Take `⟨gK, hgK⟩` from `g.exists_isMap (φ' := a.comp φ) a rfl hxa`. Take `⟨⟨i, p⟩, ⟨hp1, hp2⟩, hu⟩` from `Φ.lifts K (a.comp φ) (spMap a ≫ x) (by rw [Category.assoc, hx, sp_comp]) gK`. Simplify using `only at hp1 hp2`. Establish `hfix : ∀ γ : K ≃ₐ[k] K, spMap (γ : K →+* K) ≫ p = p` using `fun γ => by`.

Establish `hγ : (γ : K →+* K).comp a = a` using `RingHom.ext fun z => γ.commutes z`. Establish `hs : spMap (γ : K →+* K) ≫ spMap a = spMap a` using `by rw [← sp_comp, hγ]`. Use `hu ⟨i, spMap (γ : K →+* K) ≫ p⟩ ⟨by dsimp only` as an intermediate fact. Rewrite using `[Category.assoc, hp1, ← Category.assoc, hs],`. Use `carries_map _ hp2 (fun τ j => by rw [hgK τ j, ← Category.assoc, ← dual_comp, hγ]) (by rw [← RingHom.comp_assoc, hγ]) (by simp only [← Category.assoc, hs])⟩`.

Conclude with `eq_of_heq (Sigma.mk.inj this).2`. Take `⟨y, ψ, φ₁, f, t, t', h1, h2, h3⟩` from `hp2`. Establish `hψ : ∀ z, ψ z ∈ a.range` using `fun z => by`. Use `(InfiniteGalois.mem_range_algebraMap_iff_fixed (k := k) (ψ z)).2 fun γ => ?_` and prove the remaining obligations. Establish `h` using `hfix γ`.

Use `haveI : Mono (stalkPt (Φ.C i).Y y) := inferInstanceAs (Mono ((Φ.C i).Y.X.fromSpecStalk y))`. Rewrite `h` using `[h1, ← Category.assoc, cancel_mono, ← sp_comp]`. Conclude with `RingHom.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective h)) z`. Set `ψ₀ : (Φ.C i).Y.X.presheaf.stalk y →+* k` to `(RingEquiv.ofBijective a.rangeRestrict ⟨fun u v h => a.injective (congrArg Subtype.val h), a.rangeRestrict_surjective⟩).symm.toRingHom.comp (ψ.codRestrict a.range hψ)`. Establish `hψ₀ : a.comp ψ₀ = ψ` using `RingHom.ext fun z => congrArg Subtype.val ((RingEquiv.ofBijective a.rangeRestrict ⟨fun u v h => a.injective (congrArg Subtype.val h), a.rangeRestrict_surjective⟩).apply_symm_apply (ψ.codRestrict a.range hψ z))`.

Establish `hq : spMap a ≫ spMap ψ₀ ≫ stalkPt (Φ.C i).Y y = p` using `by rw [← Category.assoc, ← sp_comp, hψ₀, h1]`. Take `⟨t₀, ht₀⟩` from `tri_descend (hψ₀ ▸ h3) hgK rfl hxa`. Establish `hp2 : (Φ.C i).Carries p gK` using `⟨y, ψ, φ₁, f, t, t', h1, h2, h3⟩`. Use `⟨⟨i, spMap ψ₀ ≫ stalkPt (Φ.C i).Y y⟩, ⟨?_, y, ψ₀, φ₁, f, t, t₀, rfl, h2, ht₀⟩, ?_⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[← cancel_epi (spMap a), ← hp1, ← hq]`. Simplify using `only [Category.assoc]`. Introduce and unpack `⟨j, q⟩ ⟨hq1, hq2⟩ dsimp only at hq1 hq2`. Use `hu ⟨j, spMap a ≫ q⟩ ⟨by dsimp only; rw [Category.assoc, hq1], carries_map _ hq2 hgK rfl hxa⟩` as an intermediate fact. Take `⟨rfl, h⟩` from `Sigma.mk.inj this`.

Rewrite using `[(cancel_epi (spMap a)).1 ((eq_of_heq h).trans hq.symm)]`.
-/
theorem UpperTheory.flag_torus_generic_point :
    ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N} (Φ : FlagTor T e U) (k : Type) [Field k] (φ : c.F →+* k) (x : Sp k ⟶ gen T), x ≫ genStr T = spMap φ → ∀ g : EigFrame T φ (x ≫ genι T), ∃! q : Σ i : U.Comp, (Sp k ⟶ (Φ.C i).Y.X), q.2 ≫ (Φ.C q.1).π = x ∧ (Φ.C q.1).Carries q.2 g := by
  intro E _ _ _ H Dw l Xo c O _ β T F _ e σ N U Φ k _ φ x hx g
  haveI : CharZero k := φ.charZero_iff φ.injective |>.1 inferInstance
  let K := AlgebraicClosure k
  let a : k →+* K := algebraMap k K
  haveI := epi_sp a
  have hxa : (spMap a ≫ x) ≫ genι T = spMap a ≫ x ≫ genι T := Category.assoc _ _ _
  obtain ⟨gK, hgK⟩ := g.exists_isMap (φ' := a.comp φ) a rfl hxa
  obtain ⟨⟨i, p⟩, ⟨hp1, hp2⟩, hu⟩ := Φ.lifts K (a.comp φ) (spMap a ≫ x) (by rw [Category.assoc, hx, sp_comp]) gK
  dsimp only at hp1 hp2
  have hfix : ∀ γ : K ≃ₐ[k] K, spMap (γ : K →+* K) ≫ p = p := fun γ => by
    have hγ : (γ : K →+* K).comp a = a := RingHom.ext fun z => γ.commutes z
    have hs : spMap (γ : K →+* K) ≫ spMap a = spMap a := by rw [← sp_comp, hγ]
    have := hu ⟨i, spMap (γ : K →+* K) ≫ p⟩ ⟨by
      dsimp only
      rw [Category.assoc, hp1, ← Category.assoc, hs],
      carries_map _ hp2 (fun τ j => by rw [hgK τ j, ← Category.assoc, ← dual_comp, hγ])
        (by rw [← RingHom.comp_assoc, hγ]) (by simp only [← Category.assoc, hs])⟩
    exact eq_of_heq (Sigma.mk.inj this).2
  obtain ⟨y, ψ, φ₁, f, t, t', h1, h2, h3⟩ := hp2
  have hψ : ∀ z, ψ z ∈ a.range := fun z => by
    refine (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := k) (ψ z)).2 fun γ => ?_
    have h := hfix γ
    haveI : Mono (stalkPt (Φ.C i).Y y) := inferInstanceAs (Mono ((Φ.C i).Y.X.fromSpecStalk y))
    rw [h1, ← Category.assoc, cancel_mono, ← sp_comp] at h
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective h)) z
  let ψ₀ : (Φ.C i).Y.X.presheaf.stalk y →+* k :=
    (RingEquiv.ofBijective a.rangeRestrict ⟨fun u v h => a.injective (congrArg Subtype.val h),
      a.rangeRestrict_surjective⟩).symm.toRingHom.comp (ψ.codRestrict a.range hψ)
  have hψ₀ : a.comp ψ₀ = ψ := RingHom.ext fun z => congrArg Subtype.val
    ((RingEquiv.ofBijective a.rangeRestrict ⟨fun u v h => a.injective (congrArg Subtype.val h),
      a.rangeRestrict_surjective⟩).apply_symm_apply (ψ.codRestrict a.range hψ z))
  have hq : spMap a ≫ spMap ψ₀ ≫ stalkPt (Φ.C i).Y y = p := by rw [← Category.assoc, ← sp_comp, hψ₀, h1]
  obtain ⟨t₀, ht₀⟩ := tri_descend (hψ₀ ▸ h3) hgK rfl hxa
  have hp2 : (Φ.C i).Carries p gK := ⟨y, ψ, φ₁, f, t, t', h1, h2, h3⟩
  refine ⟨⟨i, spMap ψ₀ ≫ stalkPt (Φ.C i).Y y⟩, ⟨?_, y, ψ₀, φ₁, f, t, t₀, rfl, h2, ht₀⟩, ?_⟩
  · dsimp only
    rw [← cancel_epi (spMap a), ← hp1, ← hq]
    simp only [Category.assoc]
  · rintro ⟨j, q⟩ ⟨hq1, hq2⟩
    dsimp only at hq1 hq2
    have := hu ⟨j, spMap a ≫ q⟩ ⟨by dsimp only; rw [Category.assoc, hq1], carries_map _ hq2 hgK rfl hxa⟩
    obtain ⟨rfl, h⟩ := Sigma.mk.inj this
    rw [(cancel_epi (spMap a)).1 ((eq_of_heq h).trans hq.symm)]

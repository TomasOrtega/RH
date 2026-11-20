import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

variable {F : Type} [Field F] {Ω Ω' : Type} [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']

/- English proof (translation)
Use `conv_lhs => rw [← spMap_stalkClosedPointTo g]`. Rewrite using `[← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]`. Use `show Spec.map _ ≫ _ = Spec.map _ ≫ _`. Simplify using `only [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc]`.
-/
private theorem eq_spMap_of_specializes {X : Scheme.{0}} {K : Type} [Field K] (g : Sp K ⟶ X) {z : X}
    (h : g (IsLocalRing.closedPoint K) ⤳ z) :
    g = spMap (X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of K) g).hom ≫
      X.fromSpecStalk z := by
  conv_lhs => rw [← spMap_stalkClosedPointTo g]
  rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]
  show Spec.map _ ≫ _ = Spec.map _ ≫ _
  simp only [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc]

/- English proof (translation)
Use `show Spec.map _ = Spec.map _ ≫ Spec.map _`. Rewrite using `[CommRingCat.ofHom_comp, Spec.map_comp]`.
-/
private theorem spMap_comp_spMap_divisor {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (f : A →+* B) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

/- English proof (translation)
Establish `hp0 : (M'.pt ≫ f) (IsLocalRing.closedPoint Ω') = genericPoint M.Z`. Establish `h1 : (M'.pt ≫ f) (IsLocalRing.closedPoint Ω') = f (M'.pt (IsLocalRing.closedPoint Ω'))` using `rfl`. Rewrite using `[h1]`. Conclude with `(congrArg f (M'.pt_apply (IsLocalRing.closedPoint Ω'))).trans hg`. Establish `hp : (M'.pt ≫ f) (IsLocalRing.closedPoint Ω') ⤳ genericPoint M.Z` using `by rw [hp0]`.

Establish `hq : M.pt = spMap (M.stalkHom (genericPoint M.Z)) ≫ M.Z.fromSpecStalk (genericPoint M.Z)` using `eq_spMap_of_specializes M.pt (M.pt_specializes (IsLocalRing.closedPoint Ω) (genericPoint M.Z))`. Establish `hsurj : Function.Surjective (M.stalkHom (genericPoint M.Z))`. Introduce `x`. Establish `hx : x ∈ M.O (genericPoint M.Z)` using `by rw [M.O_genericPoint]; exact Algebra.mem_top`. Take `⟨a, ha⟩` from `(M.stalkEquiv (genericPoint M.Z)).surjective ⟨x, hx⟩`.

Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[← RatModel.coe_stalkEquiv, ha]`. Set `E` to `RingEquiv.ofBijective (M.stalkHom (genericPoint M.Z)) ⟨M.stalkHom_injective _, hsurj⟩`. Set `α` to `(M.Z.presheaf.stalkSpecializes hp ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of Ω') (M'.pt ≫ f)).hom`. Set `φ₀ : Ω →+* Ω'` to `α.comp E.symm.toRingHom`.

Establish `key : φ₀.comp (M.stalkHom (genericPoint M.Z)) = α`. Use extensionality with `a`. Use `show α (E.symm (E a)) = α a`. Rewrite using `[E.symm_apply_apply]`. Establish `hpt : M'.pt ≫ f = spMap φ₀ ≫ M.pt`.

Rewrite using `[eq_spMap_of_specializes (M'.pt ≫ f) hp, hq, ← Category.assoc, ← spMap_comp_spMap_divisor, key]`. Establish `hc : spMap (φ₀.comp (algebraMap F Ω)) = spMap (algebraMap F Ω')`. Rewrite using `[spMap_comp_spMap_divisor, ← M.pt_s, ← Category.assoc, ← hpt, Category.assoc, hs, M'.pt_s]`. Establish `hinj : φ₀.comp (algebraMap F Ω) = algebraMap F Ω'`. Establish `h2 : CommRingCat.ofHom (φ₀.comp (algebraMap F Ω)) = CommRingCat.ofHom (algebraMap F Ω')` using `Spec.map_injective hc`.

Use extensionality with `a`. Conclude with `congrArg (fun g => g.hom a) h2`. Conclude with `⟨⟨φ₀, fun a => RingHom.congr_fun hinj a⟩, hpt⟩`.
-/
theorem exists_isHom_of_generic (M : RatModel F Ω) (M' : RatModel F Ω') (f : M'.Z ⟶ M.Z) (hs : f ≫ M.s = M'.s)
    (hg : f (genericPoint M'.Z) = genericPoint M.Z) : ∃ φ : Ω →ₐ[F] Ω', M.IsHom M' φ f := by
  classical
  have hp0 : (M'.pt ≫ f) (IsLocalRing.closedPoint Ω') = genericPoint M.Z := by
    have h1 : (M'.pt ≫ f) (IsLocalRing.closedPoint Ω') = f (M'.pt (IsLocalRing.closedPoint Ω')) := rfl
    rw [h1]
    exact (congrArg f (M'.pt_apply (IsLocalRing.closedPoint Ω'))).trans hg
  have hp : (M'.pt ≫ f) (IsLocalRing.closedPoint Ω') ⤳ genericPoint M.Z := by rw [hp0]
  have hq : M.pt = spMap (M.stalkHom (genericPoint M.Z)) ≫ M.Z.fromSpecStalk (genericPoint M.Z) :=
    eq_spMap_of_specializes M.pt (M.pt_specializes (IsLocalRing.closedPoint Ω) (genericPoint M.Z))
  have hsurj : Function.Surjective (M.stalkHom (genericPoint M.Z)) := by
    intro x
    have hx : x ∈ M.O (genericPoint M.Z) := by rw [M.O_genericPoint]; exact Algebra.mem_top
    obtain ⟨a, ha⟩ := (M.stalkEquiv (genericPoint M.Z)).surjective ⟨x, hx⟩
    refine ⟨a, ?_⟩
    rw [← RatModel.coe_stalkEquiv, ha]
  let E := RingEquiv.ofBijective (M.stalkHom (genericPoint M.Z)) ⟨M.stalkHom_injective _, hsurj⟩
  let α := (M.Z.presheaf.stalkSpecializes hp ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of Ω') (M'.pt ≫ f)).hom
  let φ₀ : Ω →+* Ω' := α.comp E.symm.toRingHom
  have key : φ₀.comp (M.stalkHom (genericPoint M.Z)) = α := by
    ext a
    show α (E.symm (E a)) = α a
    rw [E.symm_apply_apply]
  have hpt : M'.pt ≫ f = spMap φ₀ ≫ M.pt := by
    rw [eq_spMap_of_specializes (M'.pt ≫ f) hp, hq, ← Category.assoc, ← spMap_comp_spMap_divisor, key]
  have hc : spMap (φ₀.comp (algebraMap F Ω)) = spMap (algebraMap F Ω') := by
    rw [spMap_comp_spMap_divisor, ← M.pt_s, ← Category.assoc, ← hpt, Category.assoc, hs, M'.pt_s]
  have hinj : φ₀.comp (algebraMap F Ω) = algebraMap F Ω' := by
    have h2 : CommRingCat.ofHom (φ₀.comp (algebraMap F Ω)) = CommRingCat.ofHom (algebraMap F Ω') :=
      Spec.map_injective hc
    ext a
    exact congrArg (fun g => g.hom a) h2
  exact ⟨⟨φ₀, fun a => RingHom.congr_fun hinj a⟩, hpt⟩

/- English proof (translation)
Establish `hpt : (𝟙 M.Z : M.Z ⟶ M.Z) (M.pt (IsLocalRing.closedPoint Ω)) = genericPoint M.Z`. Conclude with `M.pt_apply _`. Establish `hx : x ∈ M.O ((𝟙 M.Z : M.Z ⟶ M.Z) (M.pt (IsLocalRing.closedPoint Ω)))`. Rewrite using `[hpt, M.O_genericPoint]`. Conclude with `Algebra.mem_top`.

Establish `h2` using `h.val_comp M.pt (IsLocalRing.closedPoint Ω) hx`. Rewrite `h2` using `[Category.comp_id, RatModel.val_pt, RatModel.val_pt]`. Conclude with `h2.symm`.
-/
theorem apply_eq_of_isHom_id {M : RatModel F Ω} {χ : Ω →ₐ[F] Ω} (h : M.IsHom M χ (𝟙 M.Z)) (x : Ω) : χ x = x := by
  have hpt : (𝟙 M.Z : M.Z ⟶ M.Z) (M.pt (IsLocalRing.closedPoint Ω)) = genericPoint M.Z := by
    exact M.pt_apply _
  have hx : x ∈ M.O ((𝟙 M.Z : M.Z ⟶ M.Z) (M.pt (IsLocalRing.closedPoint Ω))) := by
    rw [hpt, M.O_genericPoint]; exact Algebra.mem_top
  have h2 := h.val_comp M.pt (IsLocalRing.closedPoint Ω) hx
  rw [Category.comp_id, RatModel.val_pt, RatModel.val_pt] at h2
  exact h2.symm

/- English proof (translation)
Conclude with `genericPoint_eq_of_isOpenImmersion e.hom`.
-/
theorem iso_genericPoint {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (e : X ≅ Y) :
    e.hom (genericPoint X) = genericPoint Y := by
  exact genericPoint_eq_of_isOpenImmersion e.hom

/- English proof (translation)
Rewrite using `[Mat.map_mul, Mat.map_inv]`.
-/
private theorem mat_map_mul_inv {ι : Type} {m : ι → ℕ} {K K' : Type} [Field K] [Field K'] (σ : K →+* K')
    (X Y : Mat m K) : (X * Y⁻¹).map σ = X.map σ * (Y.map σ)⁻¹ := by
  rw [Mat.map_mul, Mat.map_inv]

/- English proof (translation)
Take `⟨φ, hφ⟩` from `exists_isHom_of_generic M M' e.hom hs (iso_genericPoint e)`. Establish `hs' : e.inv ≫ M'.s = M.s` using `by rw [← hs, ← Category.assoc, e.inv_hom_id, Category.id_comp]`. Take `⟨ψ, hψ⟩` from `exists_isHom_of_generic M' M e.inv hs' (iso_genericPoint e.symm)`. Establish `hid : M.IsHom M (ψ.comp φ) (𝟙 M.Z)`. Establish `h1` using `hφ.comp hψ`.

Rewrite `h1` using `[e.inv_hom_id]`. Then use the resulting hypothesis. Establish `hid' : M'.IsHom M' (φ.comp ψ) (𝟙 M'.Z)`. Establish `h1` using `hψ.comp hφ`. Rewrite `h1` using `[e.hom_inv_id]`. Then use the resulting hypothesis. Establish `hψφ : ∀ x, ψ (φ x) = x` using `fun x => apply_eq_of_isHom_id hid x`.

Establish `hφψ : ∀ x, φ (ψ x) = x` using `fun x => apply_eq_of_isHom_id hid' x`. Establish `pt2 : ∀ z' : M'.Z, e.inv (e.hom z') = z'` using `fun z' => by simp`. Establish `memφ : ∀ {z' : M'.Z} {x : Ω}, x ∈ M.O (e.hom z') → φ x ∈ M'.O z'` using `fun hx => hφ.map_mem_O hx`. Establish `memψ : ∀ {z' : M'.Z} {x : Ω'}, x ∈ M'.O z' → ψ x ∈ M.O (e.hom z')`. Introduce `z' x hx`.

Apply `hψ.map_mem_O` to reduce the goal to its premises. Rewrite using `[pt2]` and apply the resulting hypothesis. Establish `mm1 : ∀ g : Mat m Ω, (g.map φ).map ψ = g`. Introduce `g`. Use function extensionality and compare the values at `τ`.

Use extensionality with `i j`. Simplify using `[Mat.map, hψφ]`. Establish `mm2 : ∀ g : Mat m Ω', (g.map ψ).map φ = g`. Introduce `g`. Use function extensionality and compare the values at `τ`.

Use extensionality with `i j`. Simplify using `[Mat.map, hφψ]`. Establish `I1 : ∀ (B : Mat m Ω') (A : Mat m Ω), B.map ψ * A⁻¹ = (B * (A.map φ)⁻¹).map ψ`. Introduce `B A`. Establish `h1` using `mat_map_mul_inv ψ.toRingHom B (A.map φ)`.

Establish `h2 : (B * (A.map φ)⁻¹).map ψ = B.map ψ * ((A.map φ).map ψ)⁻¹` using `h1`. Rewrite using `[h2, mm1]`. Establish `I2 : ∀ (B : Mat m Ω') (A : Mat m Ω), (B.map ψ * A⁻¹).map φ = B * (A.map φ)⁻¹`. Introduce `B A`. Establish `h1` using `mat_map_mul_inv φ.toRingHom (B.map ψ) A`.

Establish `h2 : (B.map ψ * A⁻¹).map φ = (B.map ψ).map φ * (A.map φ)⁻¹` using `h1`. Rewrite using `[h2, mm2]`. Establish `hdet : ∀ {A : Mat m Ω}, (∀ τ, (A τ).det ≠ 0) → ∀ τ, ((A.map φ) τ).det ≠ 0`. Introduce `A hA τ`. Establish `h1 : ((A.map φ) τ).det = φ (A τ).det` using `Mat.det_map A φ.toRingHom τ`.

Rewrite using `[h1]`. Conclude with `(map_ne_zero φ).2 (hA τ)`. Set `S' : Fr M' m k` to `{ S := fun z' => {A' | A'.map ψ ∈ S.S (e.hom z')} loc := by`. Introduce `z'`. Take `⟨U, A, hzU, hA, hU⟩` from `S.loc (e.hom z')`.

Use `⟨e.hom ⁻¹ᵁ U, A.map φ, hzU, hdet hA, fun z'' hz'' A'' => ?_⟩` and prove the remaining obligations. Use `show A''.map ψ ∈ S.S (e.hom z'') ↔ _`. Rewrite using `[hU (e.hom z'') hz'' (A''.map ψ), I1]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `h1 : Par k (M'.O z'').toSubring (((A'' * (A.map φ)⁻¹).map ψ).map φ)` using `h.map φ.toRingHom (fun x hx => memφ hx)`. Rewrite `h1` using `[mm2]`. Then use the resulting hypothesis. Introduce `h`. Conclude with `h.map ψ.toRingHom (fun x hx => memψ hx) }`. Use `⟨φ, S', ⟨le_rfl, hφ, ?_, ?_, ?_⟩⟩` and prove the remaining obligations.

Introduce `z' A' hA' A hA`. Establish `h1 : Par k (M.O (e.hom z')).toSubring (A'.map ψ * A⁻¹)` using `(Fr.mem_iff hA).1 (show A'.map ψ ∈ S.S (e.hom z') from hA')`. Establish `h2 : Par k (M'.O z').toSubring ((A'.map ψ * A⁻¹).map φ)` using `h1.map φ.toRingHom (fun x hx => memφ hx)`. Rewrite `h2` using `[I2]`. Then use the resulting hypothesis. Unfold `KeepsRad Rad`.

Introduce `z' g hg`. Take `⟨hg0, hgO, hgr⟩` from `hg`. Use `⟨(map_ne_zero φ).2 hg0, memφ hgO, fun x n hx hxn => ?_⟩` and prove the remaining obligations. Establish `hx' : ψ x ∈ M.O (e.hom z')` using `memψ hx`. Establish `hxn' : ψ x ^ n / g ∈ M.O (e.hom z')`.

Establish `h1` using `memψ hxn`. Rewrite `h1` using `[map_div₀, map_pow, hψφ]`. Conclude with `h1`. Establish `h2` using `memφ (hgr (ψ x) n hx' hxn')`. Rewrite `h2` using `[map_div₀, hφψ]`.

Conclude with `h2`. Introduce `K _ x A hA h hh`. Use `⟨x ≫ e.inv, ⟨by simp, ?_⟩, fun p hp => ?_⟩` and prove the remaining obligations. Establish `hx1 : e.hom ((x ≫ e.inv) (IsLocalRing.closedPoint K)) = x (IsLocalRing.closedPoint K)`. Establish `h1 : (x ≫ e.inv) (IsLocalRing.closedPoint K) = e.inv (x (IsLocalRing.closedPoint K))` using `rfl`.

Rewrite using `[h1]`. Simplify using the standard rewrite rules. Establish `hd : ∀ τ, ((A.map φ) τ).det ≠ 0` using `hdet (Fr.det_ne hA)`. Establish `hone : (1 : Mat m Ω').map (M'.val (x ≫ e.inv)) = 1`. Use function extensionality and compare the values at `τ`.

Use extensionality with `i j`. Simplify using `only [Mat.map, Matrix.map_apply, Pi.one_apply, Matrix.one_apply]`. Use `split_ifs`. Conclude with `RatModel.val_one _`. Conclude with `RatModel.val_zero _`.

Establish `hinv : (1 : Mat m K)⁻¹ = 1`. Establish `h1` using `Mat.mul_inv (g := (1 : Mat m K)) (fun τ => by simp)`. Rewrite `h1` using `[one_mul]`. Then use the resulting hypothesis. Unfold `Bears`. Use `⟨A.map φ, ?_, ?_⟩` and prove the remaining obligations.

Use `show (A.map φ).map ψ ∈ S.S (e.hom ((x ≫ e.inv) (IsLocalRing.closedPoint K)))`. Rewrite using `[mm1, hx1]`. Conclude with `hA`. Rewrite using `[Mat.mul_inv hd, hone, hinv, mul_one]`. Conclude with `hh`.

Rewrite using `[← hp.1, Category.assoc, e.hom_inv_id, Category.comp_id]`.
-/
theorem exists_refines_of_iso {ι : Type} {m k : ι → ℕ} (M : RatModel F Ω) (M' : RatModel F Ω') (e : M'.Z ≅ M.Z)
    (hs : e.hom ≫ M.s = M'.s) (S : Fr M m k) :
    ∃ (φ : Ω →ₐ[F] Ω') (S' : Fr M' m k), Refines S S' φ e.hom := by
  classical
  obtain ⟨φ, hφ⟩ := exists_isHom_of_generic M M' e.hom hs (iso_genericPoint e)
  have hs' : e.inv ≫ M'.s = M.s := by rw [← hs, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  obtain ⟨ψ, hψ⟩ := exists_isHom_of_generic M' M e.inv hs' (iso_genericPoint e.symm)
  have hid : M.IsHom M (ψ.comp φ) (𝟙 M.Z) := by
    have h1 := hφ.comp hψ
    rwa [e.inv_hom_id] at h1
  have hid' : M'.IsHom M' (φ.comp ψ) (𝟙 M'.Z) := by
    have h1 := hψ.comp hφ
    rwa [e.hom_inv_id] at h1
  have hψφ : ∀ x, ψ (φ x) = x := fun x => apply_eq_of_isHom_id hid x
  have hφψ : ∀ x, φ (ψ x) = x := fun x => apply_eq_of_isHom_id hid' x
  have pt2 : ∀ z' : M'.Z, e.inv (e.hom z') = z' := fun z' => by simp
  have memφ : ∀ {z' : M'.Z} {x : Ω}, x ∈ M.O (e.hom z') → φ x ∈ M'.O z' := fun hx => hφ.map_mem_O hx
  have memψ : ∀ {z' : M'.Z} {x : Ω'}, x ∈ M'.O z' → ψ x ∈ M.O (e.hom z') := by
    intro z' x hx
    apply hψ.map_mem_O
    rwa [pt2]
  have mm1 : ∀ g : Mat m Ω, (g.map φ).map ψ = g := by
    intro g; funext τ; ext i j; simp [Mat.map, hψφ]
  have mm2 : ∀ g : Mat m Ω', (g.map ψ).map φ = g := by
    intro g; funext τ; ext i j; simp [Mat.map, hφψ]
  have I1 : ∀ (B : Mat m Ω') (A : Mat m Ω), B.map ψ * A⁻¹ = (B * (A.map φ)⁻¹).map ψ := by
    intro B A
    have h1 := mat_map_mul_inv ψ.toRingHom B (A.map φ)
    have h2 : (B * (A.map φ)⁻¹).map ψ = B.map ψ * ((A.map φ).map ψ)⁻¹ := h1
    rw [h2, mm1]
  have I2 : ∀ (B : Mat m Ω') (A : Mat m Ω), (B.map ψ * A⁻¹).map φ = B * (A.map φ)⁻¹ := by
    intro B A
    have h1 := mat_map_mul_inv φ.toRingHom (B.map ψ) A
    have h2 : (B.map ψ * A⁻¹).map φ = (B.map ψ).map φ * (A.map φ)⁻¹ := h1
    rw [h2, mm2]
  have hdet : ∀ {A : Mat m Ω}, (∀ τ, (A τ).det ≠ 0) → ∀ τ, ((A.map φ) τ).det ≠ 0 := by
    intro A hA τ
    have h1 : ((A.map φ) τ).det = φ (A τ).det := Mat.det_map A φ.toRingHom τ
    rw [h1]
    exact (map_ne_zero φ).2 (hA τ)
  let S' : Fr M' m k :=
    { S := fun z' => {A' | A'.map ψ ∈ S.S (e.hom z')}
      loc := by
        intro z'
        obtain ⟨U, A, hzU, hA, hU⟩ := S.loc (e.hom z')
        refine ⟨e.hom ⁻¹ᵁ U, A.map φ, hzU, hdet hA, fun z'' hz'' A'' => ?_⟩
        show A''.map ψ ∈ S.S (e.hom z'') ↔ _
        rw [hU (e.hom z'') hz'' (A''.map ψ), I1]
        constructor
        · intro h
          have h1 : Par k (M'.O z'').toSubring (((A'' * (A.map φ)⁻¹).map ψ).map φ) :=
            h.map φ.toRingHom (fun x hx => memφ hx)
          rwa [mm2] at h1
        · intro h
          exact h.map ψ.toRingHom (fun x hx => memψ hx) }
  refine ⟨φ, S', ⟨le_rfl, hφ, ?_, ?_, ?_⟩⟩
  · intro z' A' hA' A hA
    have h1 : Par k (M.O (e.hom z')).toSubring (A'.map ψ * A⁻¹) :=
      (Fr.mem_iff hA).1 (show A'.map ψ ∈ S.S (e.hom z') from hA')
    have h2 : Par k (M'.O z').toSubring ((A'.map ψ * A⁻¹).map φ) :=
      h1.map φ.toRingHom (fun x hx => memφ hx)
    rwa [I2] at h2
  · unfold KeepsRad Rad
    intro z' g hg
    obtain ⟨hg0, hgO, hgr⟩ := hg
    refine ⟨(map_ne_zero φ).2 hg0, memφ hgO, fun x n hx hxn => ?_⟩
    have hx' : ψ x ∈ M.O (e.hom z') := memψ hx
    have hxn' : ψ x ^ n / g ∈ M.O (e.hom z') := by
      have h1 := memψ hxn
      rw [map_div₀, map_pow, hψφ] at h1
      exact h1
    have h2 := memφ (hgr (ψ x) n hx' hxn')
    rw [map_div₀, hφψ] at h2
    exact h2
  · intro K _ x A hA h hh
    refine ⟨x ≫ e.inv, ⟨by simp, ?_⟩, fun p hp => ?_⟩
    · have hx1 : e.hom ((x ≫ e.inv) (IsLocalRing.closedPoint K)) = x (IsLocalRing.closedPoint K) := by
        have h1 : (x ≫ e.inv) (IsLocalRing.closedPoint K) = e.inv (x (IsLocalRing.closedPoint K)) := rfl
        rw [h1]
        simp
      have hd : ∀ τ, ((A.map φ) τ).det ≠ 0 := hdet (Fr.det_ne hA)
      have hone : (1 : Mat m Ω').map (M'.val (x ≫ e.inv)) = 1 := by
        funext τ; ext i j
        simp only [Mat.map, Matrix.map_apply, Pi.one_apply, Matrix.one_apply]
        split_ifs
        · exact RatModel.val_one _
        · exact RatModel.val_zero _
      have hinv : (1 : Mat m K)⁻¹ = 1 := by
        have h1 := Mat.mul_inv (g := (1 : Mat m K)) (fun τ => by simp)
        rwa [one_mul] at h1
      unfold Bears
      refine ⟨A.map φ, ?_, ?_⟩
      · show (A.map φ).map ψ ∈ S.S (e.hom ((x ≫ e.inv) (IsLocalRing.closedPoint K)))
        rw [mm1, hx1]
        exact hA
      · rw [Mat.mul_inv hd, hone, hinv, mul_one]
        exact hh
    · rw [← hp.1, Category.assoc, e.hom_inv_id, Category.comp_id]

/- English proof (translation)
Take `⟨hP, hSm, hGI⟩` from `h`. Use `haveI : SmoothOfRelativeDimension d M.s := hSm`. Use `haveI : GeometricallyIntegral M.s := hGI`. Use `haveI : GeometricallyConnected M.s := by`. Prove the components needed by the constructor for the conclusion.

Introduce `a b y c fst snd hpb`. Use `GeometricallyIntegral.geometrically_isIntegral (f := M.s) y fst snd hpb` as an intermediate fact. Use `infer_instance`. Take `⟨Y, e, hd, he⟩` from `GlobalTheory.ProjVar.Var.exists_iso M.s d hP`. Establish `hs : e.inv ≫ M.s = (ratOf Y).s` using `by show e.inv ≫ M.s = Y.str`.

Rewrite using `[← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]`. Take `⟨φ, S', hS'⟩` from `exists_refines_of_iso M (ratOf Y) e.symm hs S`. Conclude with `⟨Y, φ, e.inv, S', hd, hS'⟩`.
-/
theorem exists_var_refines (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (d : ℕ) (ι : Type)
    (m k : ι → ℕ) (S : Fr M m k) (h : Good M d) :
    ∃ (Y : GlobalTheory.ProjVar.Var F) (φ : Ω →ₐ[F] Y.Fn) (f : Y.X ⟶ M.Z) (S' : Fr (ratOf Y) m k),
      Y.dim = d ∧ Refines S S' φ f := by
  obtain ⟨hP, hSm, hGI⟩ := h
  haveI : SmoothOfRelativeDimension d M.s := hSm
  haveI : GeometricallyIntegral M.s := hGI
  haveI : GeometricallyConnected M.s := by
    constructor
    intro a b y c fst snd hpb
    have := GeometricallyIntegral.geometrically_isIntegral (f := M.s) y fst snd hpb
    infer_instance
  obtain ⟨Y, e, hd, he⟩ := GlobalTheory.ProjVar.Var.exists_iso M.s d hP
  have hs : e.inv ≫ M.s = (ratOf Y).s := by
    show e.inv ≫ M.s = Y.str
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  obtain ⟨φ, S', hS'⟩ := exists_refines_of_iso M (ratOf Y) e.symm hs S
  exact ⟨Y, φ, e.inv, S', hd, hS'⟩

end GlobalTheory.FlagBundle

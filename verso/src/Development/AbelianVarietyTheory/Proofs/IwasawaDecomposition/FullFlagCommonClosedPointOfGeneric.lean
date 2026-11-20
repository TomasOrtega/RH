import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoBear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointCarriesFrameFlagsTransferBetweenFlagBundlesStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

namespace GlobalTheory.FlagBundle.ClosedPt

variable {ι : Type} {m : ι → ℕ}

/- English proof (translation)
Introduce `τ` and use `⟨fun _ _ => trivial, h τ, trivial, fun _ _ hi _ => absurd hi (Nat.not_lt_zero _)⟩`.
-/
theorem par_zero_top {K : Type} [Field K] {g : Mat m K} (h : ∀ τ, (g τ).det ≠ 0) : Par 0 ⊤ g := fun τ =>
  ⟨fun _ _ => trivial, h τ, trivial, fun _ _ hi _ => absurd hi (Nat.not_lt_zero _)⟩

/- English proof (translation)
Establish `e : (N₂ τ).map g * ((N₂ τ)⁻¹).map g = 1`. Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ g.map_zero g.map_one]`. Use `show (N₁ τ).map g * ((N₂ τ).map g)⁻¹ = _`. Rewrite using `[Matrix.map_mul, Matrix.inv_eq_right_inv e]`.
-/
theorem map_mul_inv {R K : Type} [CommRing R] [Field K] (g : R →+* K) (N₁ N₂ : Mat m R) (τ : ι)
    (hu : IsUnit (N₂ τ).det) : (N₁.map g * (N₂.map g)⁻¹) τ = (N₁ τ * (N₂ τ)⁻¹).map g := by
  have e : (N₂ τ).map g * ((N₂ τ)⁻¹).map g = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ g.map_zero g.map_one]
  show (N₁ τ).map g * ((N₂ τ).map g)⁻¹ = _
  rw [Matrix.map_mul, Matrix.inv_eq_right_inv e]

/- English proof (translation)
Establish `hu : ∀ τ, IsUnit (N₂ τ).det` using `fun τ => by`. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]`. Conclude with `h₂ τ`. Establish `hP` using `(par_zero_top h₁).mul (par_zero_top h₂).inv`. Introduce `τ`.

Use `⟨fun _ _ => trivial, hP.det_ne τ, trivial, fun i j hi hij => ?_⟩` and prove the remaining obligations. Establish `h0` using `(hL τ).2.2.2 i j hi hij`. Rewrite `h0` using `[map_mul_inv _ _ _ τ (hu τ)]`. Rewrite using `[map_mul_inv _ _ _ τ (hu τ)]`. Establish `h0' : algebraMap R L ((N₁ τ * (N₂ τ)⁻¹) i j) = 0` using `h0`.

Use `show IsLocalRing.residue R ((N₁ τ * (N₂ τ)⁻¹) i j) = 0`. Rewrite using `[(map_eq_zero_iff _ (IsFractionRing.injective R L)).1 h0', map_zero]`.
-/
theorem descend {R L : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field L] [Algebra R L]
    [IsFractionRing R L] (N₁ N₂ : Mat m R)
    (h₁ : ∀ τ, (N₁.map (IsLocalRing.residue R) τ).det ≠ 0)
    (h₂ : ∀ τ, (N₂.map (IsLocalRing.residue R) τ).det ≠ 0)
    (hL : Par m ⊤ (N₁.map (algebraMap R L) * (N₂.map (algebraMap R L))⁻¹)) :
    Par m ⊤ (N₁.map (IsLocalRing.residue R) * (N₂.map (IsLocalRing.residue R))⁻¹) := by
  have hu : ∀ τ, IsUnit (N₂ τ).det := fun τ => by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    exact h₂ τ
  have hP := (par_zero_top h₁).mul (par_zero_top h₂).inv
  intro τ
  refine ⟨fun _ _ => trivial, hP.det_ne τ, trivial, fun i j hi hij => ?_⟩
  have h0 := (hL τ).2.2.2 i j hi hij
  rw [map_mul_inv _ _ _ τ (hu τ)] at h0
  rw [map_mul_inv _ _ _ τ (hu τ)]
  have h0' : algebraMap R L ((N₁ τ * (N₂ τ)⁻¹) i j) = 0 := h0
  show IsLocalRing.residue R ((N₁ τ * (N₂ τ)⁻¹) i j) = 0
  rw [(map_eq_zero_iff _ (IsFractionRing.injective R L)).1 h0', map_zero]

variable {F : Type} [Field F]

noncomputable def vals {Y : Var F} {R : Type} [CommRing R] [IsLocalRing R] (v : Sp R ⟶ Y.X) (M : Mat m Y.Fn)
    (hM : ∀ τ a b, M τ a b ∈ (ratOf Y).O (v (IsLocalRing.closedPoint R))) : Mat m R :=
  fun τ a b => RatModel.valLoc (M := ratOf Y) v _ specializes_rfl ⟨M τ a b, hM τ a b⟩

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use extensionality with `a b`. Use `RatModel.val_spMap_comp (M := ratOf Y) σ v specializes_rfl ⟨M τ a b, hM τ a b⟩` as an intermediate fact. Conclude with `this`.
-/
theorem map_val {Y : Var F} {R K : Type} [CommRing R] [IsLocalRing R] [Field K] (σ : R →+* K) (v : Sp R ⟶ Y.X)
    (M : Mat m Y.Fn) (hM : ∀ τ a b, M τ a b ∈ (ratOf Y).O (v (IsLocalRing.closedPoint R))) :
    M.map ((ratOf Y).val (spMap σ ≫ v)) = (vals v M hM).map σ := by
  funext τ
  ext a b
  have := RatModel.val_spMap_comp (M := ratOf Y) σ v specializes_rfl ⟨M τ a b, hM τ a b⟩
  exact this

/- English proof (translation)
The claim follows from `Par.map_of hM _ (σ.comp (RatModel.valLoc (M := ratOf Y) v _ specializes_rfl)) (fun x => RatModel.val_spMap_comp (M := ratOf Y) σ v specializes_rfl x)`.
-/
theorem par_val {Y : Var F} {R K : Type} [CommRing R] [IsLocalRing R] [Field K] (σ : R →+* K) (v : Sp R ⟶ Y.X)
    {M : Mat m Y.Fn} (hM : Par 0 ((ratOf Y).O (v (IsLocalRing.closedPoint R))).toSubring M) :
    Par 0 ⊤ (M.map ((ratOf Y).val (spMap σ ≫ v))) :=
  Par.map_of hM _ (σ.comp (RatModel.valLoc (M := ratOf Y) v _ specializes_rfl))
    (fun x => RatModel.val_spMap_comp (M := ratOf Y) σ v specializes_rfl x)

end GlobalTheory.FlagBundle.ClosedPt

namespace GlobalTheory.FlagBundle.ClosedPt

/- English proof (translation)
Use `(Scheme.Hom.comp_apply _ _ _).trans ?_` and prove the remaining obligations. Conclude with `congrArg v (IsLocalRing.comap_closedPoint (IsLocalRing.residue R))`.
-/
theorem closedPt_comp {R : Type} [CommRing R] [IsLocalRing R] {Z : Scheme.{0}} (v : Sp R ⟶ Z) :
    (spMap (IsLocalRing.residue R) ≫ v) (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) =
      v (IsLocalRing.closedPoint R) := by
  refine (Scheme.Hom.comp_apply _ _ _).trans ?_
  exact congrArg v (IsLocalRing.comap_closedPoint (IsLocalRing.residue R))

/- English proof (translation)
Establish `h` using `(IsLocalRing.specializes_closedPoint (spMap (algebraMap R L) w)).map v.continuous`. Use `h using 1` and compare the differences between its conclusion and the goal. Conclude with `Scheme.Hom.comp_apply _ _ _`.
-/
theorem gen_specializes {R L : Type} [CommRing R] [IsLocalRing R] [Field L] [Algebra R L] {Z : Scheme.{0}}
    (v : Sp R ⟶ Z) (w : Sp L) : (spMap (algebraMap R L) ≫ v) w ⤳ v (IsLocalRing.closedPoint R) := by
  have h := (IsLocalRing.specializes_closedPoint (spMap (algebraMap R L) w)).map v.continuous
  convert h using 1
  exact Scheme.Hom.comp_apply _ _ _

end GlobalTheory.FlagBundle.ClosedPt

open GlobalTheory.FlagBundle.ClosedPt in

/- English proof (translation)
Introduce `F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ R _ _ _ L _ _ _ v₁ v₂ e hgen`. Establish `sub₁` using `hR₁.2.1`. Establish `sub₂` using `hR₂.2.1`. Establish `hf₁ : f₁ (v₁ (IsLocalRing.closedPoint R)) = (v₁ ≫ f₁) (IsLocalRing.closedPoint R)` using `(Scheme.Hom.comp_apply _ _ _).symm`. Establish `hf₂ : f₂ (v₂ (IsLocalRing.closedPoint R)) = (v₁ ≫ f₁) (IsLocalRing.closedPoint R)`.

Rewrite using `[e]`. Conclude with `(Scheme.Hom.comp_apply _ _ _).symm`. Take `⟨A, hA⟩` from `Eb.nonempty ((v₁ ≫ f₁) (IsLocalRing.closedPoint R))`. Take `⟨A₁, hA₁⟩` from `S₁.nonempty (v₁ (IsLocalRing.closedPoint R))`. Take `⟨A₂, hA₂⟩` from `S₂.nonempty (v₂ (IsLocalRing.closedPoint R))`.

Establish `hM₁` using `sub₁ _ A₁ hA₁ A (by rw [hf₁]; exact hA)`. Establish `hM₂` using `sub₂ _ A₂ hA₂ A (by rw [hf₂]; exact hA)`. Take `⟨B, hB, hg, hgP, hb1, hb2⟩` from `hgen`. Establish `hA₁g : A₁ ∈ S₁.S ((spMap (algebraMap R L) ≫ v₁) (IsLocalRing.closedPoint L))` using `Fr.mem_of_specializes hA₁ (gen_specializes v₁ _)`. Establish `hA₂g : A₂ ∈ S₂.S ((spMap (algebraMap R L) ≫ v₂) (IsLocalRing.closedPoint L))` using `Fr.mem_of_specializes hA₂ (gen_specializes v₂ _)`.

Establish `hAg : A ∈ Eb.S (((spMap (algebraMap R L) ≫ v₁) ≫ f₁) (IsLocalRing.closedPoint L))`. Rewrite using `[Category.assoc]`. Conclude with `Fr.mem_of_specializes hA (gen_specializes (v₁ ≫ f₁) _)`. Establish `hBg : B ∈ Eb.S (((spMap (algebraMap R L) ≫ v₁) ≫ f₁) (IsLocalRing.closedPoint L))`. Rewrite using `[Category.assoc]`.

Conclude with `hB`. Establish `heq : (spMap (algebraMap R L) ≫ v₁) ≫ f₁ = (spMap (algebraMap R L) ≫ v₂) ≫ f₂`. Rewrite using `[Category.assoc, Category.assoc, e]`. Establish `hH` using `par_val (algebraMap R L) v₁ hM₁`. Establish `hself : Bears S₁ φ₁ A ((A₁ * (A.map φ₁)⁻¹).map ((ratOf Y₁).val (spMap (algebraMap R L) ≫ v₁))) (spMap (algebraMap R L) ≫ v₁)` using `⟨A₁, hA₁g, by rw [Mat.mul_inv hH.det_ne]; exact Par.one⟩`.

Take `⟨A₂', hA₂', hpar⟩` from `GlobalTheory.T.pointCarriesFrameFlags_transfer_between_flag_bundles F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ L _ _ heq A hAg B hBg _ hg hself hb1 hb2`. Establish `hsp₂` using `gen_specializes (L := L) v₂ (IsLocalRing.closedPoint L)`. Establish `hG` using `(Fr.mem_iff hA₂g).1 hA₂'`. Establish `hM₂g : Par 0 ((ratOf Y₂).O ((spMap (algebraMap R L) ≫ v₂) (IsLocalRing.closedPoint L))).toSubring (A₂ * (A.map φ₂)⁻¹)` using `hM₂.mono le_rfl fun _ hx => RatModel.O_le_of_specializes hsp₂ hx`. Use `set ψ := RatModel.valHom (M := ratOf Y₂) (spMap (algebraMap R L) ≫ v₂) _ (RatModel.range_eq_singleton _ (IsLocalRing.closedPoint L))`.

Establish `hv : ∀ x : ((ratOf Y₂).O ((spMap (algebraMap R L) ≫ v₂) (IsLocalRing.closedPoint L))).toSubring, (ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂) x = ψ x` using `fun _ => rfl`. Establish `heqM : A₂' * (A.map φ₂)⁻¹ = (A₂' * A₂⁻¹) * (A₂ * (A.map φ₂)⁻¹)`. Rewrite using `[mul_assoc, ← mul_assoc A₂⁻¹, Mat.inv_mul (Fr.det_ne hA₂), one_mul]`. Establish `hmap : (A₂' * (A.map φ₂)⁻¹).map ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) = (A₂' * A₂⁻¹).map ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) * (A₂ * (A.map φ₂)⁻¹).map ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂))`. Rewrite using `[heqM]`.

Conclude with `Par.map_mul_of hG hM₂g ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) ψ hv`. Establish `hGv` using `Par.map_of hG ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) ψ hv`. Establish `hpar2` using `hpar`. Use `erw [hmap] at hpar2`. Rewrite `hpar2` using `[Mat.mul_inv_rev]`.

Use `clear hpar`. Establish `hL` using `hpar2.mul hGv`. Rewrite `hL` using `[mul_assoc, mul_assoc, Mat.inv_mul hGv.det_ne, mul_one]`. Rewrite `hL` using `[map_val (algebraMap R L) v₁ _ (fun τ a b => (hM₁ τ).1 a b), map_val (algebraMap R L) v₂ _ (fun τ a b => (hM₂ τ).1 a b)]`. Establish `hk₁` using `par_val (IsLocalRing.residue R) v₁ hM₁`.

Establish `hk₂` using `par_val (IsLocalRing.residue R) v₂ hM₂`. Establish `hD` using `descend _ _ (by rw [← map_val]; exact hk₁.det_ne) (by rw [← map_val]; exact hk₂.det_ne) hL`. Rewrite `hD` using `[← map_val, ← map_val]`. Establish `hAk : A ∈ Eb.S ((spMap (IsLocalRing.residue R) ≫ v₁ ≫ f₁) (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)))` using `(congrArg (fun z => A ∈ Eb.S z) (closedPt_comp (v₁ ≫ f₁))).mpr hA`. Establish `hb₁ : Bears S₁ φ₁ A ((A₁ * (A.map φ₁)⁻¹).map ((ratOf Y₁).val (spMap (IsLocalRing.residue R) ≫ v₁))) (spMap (IsLocalRing.residue R) ≫ v₁)` using `⟨A₁, (congrArg (fun z => A₁ ∈ S₁.S z) (closedPt_comp v₁)).mpr hA₁, by`.

Rewrite using `[Mat.mul_inv hk₁.det_ne]`. Conclude with `Par.one⟩`. Establish `hb₂ : Bears S₂ φ₂ A ((A₁ * (A.map φ₁)⁻¹).map ((ratOf Y₁).val (spMap (IsLocalRing.residue R) ≫ v₁))) (spMap (IsLocalRing.residue R) ≫ v₂)` using `⟨A₂, (congrArg (fun z => A₂ ∈ S₂.S z) (closedPt_comp v₂)).mpr hA₂, hD⟩`. Conclude with `⟨A, hAk, _, hk₁, hb₁, hb₂⟩`.
-/
theorem GlobalTheory.FlagBundle.coBear_closedPoint : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (L : Type) [Field L] [Algebra R L] [IsFractionRing R L] (v₁ : Sp R ⟶ Y₁.X) (v₂ : Sp R ⟶ Y₂.X), v₁ ≫ f₁ = v₂ ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (spMap (algebraMap R L) ≫ v₁ ≫ f₁) (spMap (algebraMap R L) ≫ v₁) (spMap (algebraMap R L) ≫ v₂) → CoBear Eb S₁ φ₁ S₂ φ₂ (spMap (IsLocalRing.residue R) ≫ v₁ ≫ f₁) (spMap (IsLocalRing.residue R) ≫ v₁) (spMap (IsLocalRing.residue R) ≫ v₂) := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ R _ _ _ L _ _ _ v₁ v₂ e hgen
  have sub₁ := hR₁.2.1
  have sub₂ := hR₂.2.1
  have hf₁ : f₁ (v₁ (IsLocalRing.closedPoint R)) = (v₁ ≫ f₁) (IsLocalRing.closedPoint R) :=
    (Scheme.Hom.comp_apply _ _ _).symm
  have hf₂ : f₂ (v₂ (IsLocalRing.closedPoint R)) = (v₁ ≫ f₁) (IsLocalRing.closedPoint R) := by
    rw [e]; exact (Scheme.Hom.comp_apply _ _ _).symm
  obtain ⟨A, hA⟩ := Eb.nonempty ((v₁ ≫ f₁) (IsLocalRing.closedPoint R))
  obtain ⟨A₁, hA₁⟩ := S₁.nonempty (v₁ (IsLocalRing.closedPoint R))
  obtain ⟨A₂, hA₂⟩ := S₂.nonempty (v₂ (IsLocalRing.closedPoint R))
  have hM₁ := sub₁ _ A₁ hA₁ A (by rw [hf₁]; exact hA)
  have hM₂ := sub₂ _ A₂ hA₂ A (by rw [hf₂]; exact hA)

  obtain ⟨B, hB, hg, hgP, hb1, hb2⟩ := hgen
  have hA₁g : A₁ ∈ S₁.S ((spMap (algebraMap R L) ≫ v₁) (IsLocalRing.closedPoint L)) :=
    Fr.mem_of_specializes hA₁ (gen_specializes v₁ _)
  have hA₂g : A₂ ∈ S₂.S ((spMap (algebraMap R L) ≫ v₂) (IsLocalRing.closedPoint L)) :=
    Fr.mem_of_specializes hA₂ (gen_specializes v₂ _)
  have hAg : A ∈ Eb.S (((spMap (algebraMap R L) ≫ v₁) ≫ f₁) (IsLocalRing.closedPoint L)) := by
    rw [Category.assoc]
    exact Fr.mem_of_specializes hA (gen_specializes (v₁ ≫ f₁) _)
  have hBg : B ∈ Eb.S (((spMap (algebraMap R L) ≫ v₁) ≫ f₁) (IsLocalRing.closedPoint L)) := by
    rw [Category.assoc]
    exact hB
  have heq : (spMap (algebraMap R L) ≫ v₁) ≫ f₁ = (spMap (algebraMap R L) ≫ v₂) ≫ f₂ := by
    rw [Category.assoc, Category.assoc, e]
  have hH := par_val (algebraMap R L) v₁ hM₁
  have hself : Bears S₁ φ₁ A ((A₁ * (A.map φ₁)⁻¹).map ((ratOf Y₁).val (spMap (algebraMap R L) ≫ v₁)))
      (spMap (algebraMap R L) ≫ v₁) :=
    ⟨A₁, hA₁g, by rw [Mat.mul_inv hH.det_ne]; exact Par.one⟩
  obtain ⟨A₂', hA₂', hpar⟩ := GlobalTheory.T.pointCarriesFrameFlags_transfer_between_flag_bundles F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ L _ _ heq A hAg B hBg
    _ hg hself hb1 hb2

  have hsp₂ := gen_specializes (L := L) v₂ (IsLocalRing.closedPoint L)
  have hG := (Fr.mem_iff hA₂g).1 hA₂'
  have hM₂g : Par 0 ((ratOf Y₂).O ((spMap (algebraMap R L) ≫ v₂) (IsLocalRing.closedPoint L))).toSubring
      (A₂ * (A.map φ₂)⁻¹) :=
    hM₂.mono le_rfl fun _ hx => RatModel.O_le_of_specializes hsp₂ hx
  set ψ := RatModel.valHom (M := ratOf Y₂) (spMap (algebraMap R L) ≫ v₂) _
    (RatModel.range_eq_singleton _ (IsLocalRing.closedPoint L))
  have hv : ∀ x : ((ratOf Y₂).O ((spMap (algebraMap R L) ≫ v₂) (IsLocalRing.closedPoint L))).toSubring,
      (ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂) x = ψ x := fun _ => rfl
  have heqM : A₂' * (A.map φ₂)⁻¹ = (A₂' * A₂⁻¹) * (A₂ * (A.map φ₂)⁻¹) := by
    rw [mul_assoc, ← mul_assoc A₂⁻¹, Mat.inv_mul (Fr.det_ne hA₂), one_mul]
  have hmap : (A₂' * (A.map φ₂)⁻¹).map ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) =
      (A₂' * A₂⁻¹).map ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) *
        (A₂ * (A.map φ₂)⁻¹).map ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) := by
    rw [heqM]
    exact Par.map_mul_of hG hM₂g ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) ψ hv
  have hGv := Par.map_of hG ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) ψ hv
  have hpar2 := hpar
  erw [hmap] at hpar2
  rw [Mat.mul_inv_rev] at hpar2
  clear hpar
  have hL := hpar2.mul hGv
  rw [mul_assoc, mul_assoc, Mat.inv_mul hGv.det_ne, mul_one] at hL
  rw [map_val (algebraMap R L) v₁ _ (fun τ a b => (hM₁ τ).1 a b),
    map_val (algebraMap R L) v₂ _ (fun τ a b => (hM₂ τ).1 a b)] at hL

  have hk₁ := par_val (IsLocalRing.residue R) v₁ hM₁
  have hk₂ := par_val (IsLocalRing.residue R) v₂ hM₂
  have hD := descend _ _ (by rw [← map_val]; exact hk₁.det_ne) (by rw [← map_val]; exact hk₂.det_ne) hL
  rw [← map_val, ← map_val] at hD
  have hAk : A ∈ Eb.S ((spMap (IsLocalRing.residue R) ≫ v₁ ≫ f₁)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) :=
    (congrArg (fun z => A ∈ Eb.S z) (closedPt_comp (v₁ ≫ f₁))).mpr hA
  have hb₁ : Bears S₁ φ₁ A ((A₁ * (A.map φ₁)⁻¹).map ((ratOf Y₁).val (spMap (IsLocalRing.residue R) ≫ v₁)))
      (spMap (IsLocalRing.residue R) ≫ v₁) :=
    ⟨A₁, (congrArg (fun z => A₁ ∈ S₁.S z) (closedPt_comp v₁)).mpr hA₁, by
      rw [Mat.mul_inv hk₁.det_ne]; exact Par.one⟩
  have hb₂ : Bears S₂ φ₂ A ((A₁ * (A.map φ₁)⁻¹).map ((ratOf Y₁).val (spMap (IsLocalRing.residue R) ≫ v₁)))
      (spMap (IsLocalRing.residue R) ≫ v₂) :=
    ⟨A₂, (congrArg (fun z => A₂ ∈ S₂.S z) (closedPt_comp v₂)).mpr hA₂, hD⟩
  exact ⟨A, hAk, _, hk₁, hb₁, hb₂⟩

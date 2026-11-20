import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CoeffEqZeroOfSumSmulEqZeroOfSeparating
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIntegralTensorLeftOfSmoothGrpObj
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteExtensionPrimitiveResidue
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecEqZeroOfThickeningsOfSection
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfFaithfullyFlatBase
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNeZeroIffSvalGenericPointNeZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsProdB
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.TwistNonvan

/- English proof (translation)
The claim follows from `(gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·) (gs_res r z le_top (hJ.mem _ r) _) rfl)`.
-/
theorem sval_scale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (DVR.SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·) (gs_res r z le_top (hJ.mem _ r) _) rfl)

/- English proof (translation)
Use `(congrArg (gs r z _) (hs _)).trans ((gs_eq r z _ (hJ.mem φ r) _).trans ?_)` and prove the remaining obligations. Conclude with `(congrArg _ (map_zero _)).trans (map_zero _)`.
-/
theorem sval_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (hs : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s r z J = 0 := by
  refine (congrArg (gs r z _) (hs _)).trans ((gs_eq r z _ (hJ.mem φ r) _).trans ?_)
  exact (congrArg _ (map_zero _)).trans (map_zero _)

/- English proof (translation)
Assemble the required witnesses or components as `⟨((Z.presheaf.germ (r ⁻¹ᵁ ⊤) z trivial).hom.comp (r.app ⊤).hom).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom), fun w => gs_eq r z ⊤ trivial _⟩`.
-/
theorem exists_constHom {W : Type} [CommRing W] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of W)) (r : Z ⟶ Y)
    (z : Z) : ∃ c : W →+* Z.presheaf.stalk z, ∀ w, gs r z ⊤ (scal p w) = c w :=
  ⟨((Z.presheaf.germ (r ⁻¹ᵁ ⊤) z trivial).hom.comp (r.app ⊤).hom).comp
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom), fun w => gs_eq r z ⊤ trivial _⟩

/- English proof (translation)
Take `⟨p, hp, hsum⟩` from `hc α`. Take `⟨s', hs'⟩` from `hsum e`. Take `⟨h₁, h₂⟩` from `hs' Z.left r.left (by rw [Over.w r]; exact hl) z J hJ`. Establish `hT : ∀ β, sval (p β) r.left z J = c (a (Multiplicative.ofAdd ((k + 1) • β - k • α))).val * (sval (f' β) r.left z J * sval (g' (α - β)) r.left z J * (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c (α - β)) (r ≫ snd _ D.P.A)).val)` using `fun β => by`. Establish `e₁ : a (Multiplicative.ofAdd ((k + 1) • β - k • α)) = a (Multiplicative.ofAdd β) * (a ^ k)⁻¹ (Multiplicative.ofAdd (α - β))`.

Rewrite using `[MonoidHom.inv_apply, MonoidHom.pow_apply, ← map_pow, ← map_inv, ← map_mul]`. Use `congr 1`. Rewrite using `[← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add]`. Use `congr 1`. Use `module`.

Rewrite using `[hp β Z r z J hJ, e₁, Units.val_mul, map_mul]`. Unfold `twist`. Rewrite using `[sval_scale _ _ _ z hJ, sval_scale _ _ _ z hJ, hcw, hcw]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h₂` using `[sval_zero _ h0 _ z hJ]`.

Rewrite using `[← Finset.sum_congr rfl (fun β _ => hT β)]`. Rewrite using `[Finset.sum_subset (Finset.subset_union_left (s₂ := s')) (fun β _ hβ => by rw [hT β, hs β hβ]; ring), ← Finset.sum_subset (Finset.subset_union_right (s₁ := s)) (fun β _ hβ => h₁ β hβ)]`. Conclude with `h₂.symm`.
-/
theorem sum_eq_zero {V : Type} [CommRing V] [IsDomain V] (I : Ideal V) (D : DegPre V) (k : ℕ) (α : D.X)
    {W : Type} [CommRing W] [Algebra V W] (a : Multiplicative D.X →* Wˣ)
    (f' : ∀ α, SecBT D (TA V W) k α) (g' : ∀ α, SecBT D (TA V W) 1 α) (h : ∀ α, SecBT D (TA V W) (k + 1) α)
    (hc : ConvT I (twist a f') (twist (a ^ k)⁻¹ g') h) (h0 : ∀ j, (h α).f j = 0) (e : ℕ)
    (Z : Over (Spec (CommRingCat.of V))) (r : Z ⟶ TA V W ⊗ D.P.A) (hl : Lvl I e Z.hom) (z : Z.left) (J)
    (hJ : Good D.P.L z J) (s : Finset D.X) (hs : ∀ β ∉ s, sval (f' β) r.left z J = 0)
    (c : W →+* Z.left.presheaf.stalk z) (hcw : ∀ w, gs r.left z ⊤ (scal (R := W) (fst (TA V W) D.P.A).left w) = c w) :
    ∑ β ∈ s, c (a (Multiplicative.ofAdd ((k + 1) • β - k • α))).val * (sval (f' β) r.left z J *
      sval (g' (α - β)) r.left z J *
      (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c (α - β)) (r ≫ snd _ D.P.A)).val) = 0 := by
  classical
  obtain ⟨p, hp, hsum⟩ := hc α
  obtain ⟨s', hs'⟩ := hsum e
  obtain ⟨h₁, h₂⟩ := hs' Z.left r.left (by rw [Over.w r]; exact hl) z J hJ
  have hT : ∀ β, sval (p β) r.left z J = c (a (Multiplicative.ofAdd ((k + 1) • β - k • α))).val *
      (sval (f' β) r.left z J * sval (g' (α - β)) r.left z J *
      (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c (α - β)) (r ≫ snd _ D.P.A)).val) := fun β => by
    have e₁ : a (Multiplicative.ofAdd ((k + 1) • β - k • α)) =
        a (Multiplicative.ofAdd β) * (a ^ k)⁻¹ (Multiplicative.ofAdd (α - β)) := by
      rw [MonoidHom.inv_apply, MonoidHom.pow_apply, ← map_pow, ← map_inv, ← map_mul]
      congr 1
      rw [← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add]
      congr 1
      module
    rw [hp β Z r z J hJ, e₁, Units.val_mul, map_mul]
    unfold twist
    rw [sval_scale _ _ _ z hJ, sval_scale _ _ _ z hJ, hcw, hcw]
    ring
  rw [sval_zero _ h0 _ z hJ] at h₂
  rw [← Finset.sum_congr rfl (fun β _ => hT β)]
  rw [Finset.sum_subset (Finset.subset_union_left (s₂ := s')) (fun β _ hβ => by rw [hT β, hs β hβ]; ring),
    ← Finset.sum_subset (Finset.subset_union_right (s₁ := s)) (fun β _ hβ => h₁ β hβ)]
  exact h₂.symm

/- English proof (translation)
Use `D.P.isAb.smooth` as an intermediate fact. Use `D.P.isAb.geomConnected` as an intermediate fact. Establish `: IsIntegral (𝟙_ (Over (Spec (CommRingCat.of V)))).left` using `(inferInstance : IsIntegral (Spec (CommRingCat.of V)))`. Establish `: IsAffine (𝟙_ (Over (Spec (CommRingCat.of V)))).left` using `(inferInstance : IsAffine (Spec (CommRingCat.of V)))`. Set `i : V ≃+* Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤)` to `(Scheme.ΓSpecIso (CommRingCat.of V)).symm.commRingCatIsoToRingEquiv`.

Establish `: IsNoetherianRing Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤)` using `isNoetherianRing_of_ringEquiv V i`. Use `GlobalTheory.isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (𝟙_ _)` as an intermediate fact. Take `⟨j, hj⟩` from `GlobalTheory.exists_ne_zero_of_sval_eq_mul_unit _ _ D.P.L D.P.isLB _ _ _ _ _ _ _ _ _ f g p (fun y J hJ => ⟨_, hp (𝟙_ _ ⊗ D.P.A) (𝟙 _) y J hJ⟩) hf hg`. Assume the negation of the conclusion as `hne`. Use `hj (GlobalTheory.sec_eq_zero_of_sval_finite_level V (IsLocalRing.maximalIdeal V) (𝟙_ _) D.P.A (fun r hr => ?_) _ D.P.L D.P.isLB _ _ _ p (fun e => by` and prove the remaining obligations.

Assume the negation of the conclusion as `h`. Conclude with `hne ⟨e, h⟩) j)`. Establish `e : scal (𝟙_ (Over (Spec (CommRingCat.of V)))).hom r = i r` using `rfl`. Rewrite using `[e, Ideal.mem_jacobson_bot]`. Introduce `y`.

Take `⟨y, rfl⟩` from `i.surjective y`. Rewrite `hr` using `[← IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.mem_jacobson_bot]`. Use `(hr y).map i` as an intermediate fact. Rewrite `this` using `[map_add, map_mul, map_one]`. Then use the resulting hypothesis.
-/
theorem exists_level {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (D : DegPre V)
    {k l m : ℕ} {β ga α : D.X} (f : SecBT D (𝟙_ _) k β) (g : SecBT D (𝟙_ _) l ga) (p : SecBT D (𝟙_ _) m α)
    (hp : IsProdB f g p) (hf : ∃ j, f.f j ≠ 0) (hg : ∃ j, g.f j ≠ 0) :
    ∃ e : ℕ, ¬ ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left),
      Lvl (IsLocalRing.maximalIdeal V) e (r ≫ (𝟙_ _ ⊗ D.P.A).hom) → ∀ (z : Z) (J), Good D.P.L z J →
        sval p r z J = 0 := by
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsIntegral (𝟙_ (Over (Spec (CommRingCat.of V)))).left :=
    (inferInstance : IsIntegral (Spec (CommRingCat.of V)))
  have : IsAffine (𝟙_ (Over (Spec (CommRingCat.of V)))).left :=
    (inferInstance : IsAffine (Spec (CommRingCat.of V)))
  let i : V ≃+* Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of V)).symm.commRingCatIsoToRingEquiv
  have : IsNoetherianRing Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) := isNoetherianRing_of_ringEquiv V i
  have := GlobalTheory.isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (𝟙_ _)
  obtain ⟨j, hj⟩ := GlobalTheory.exists_ne_zero_of_sval_eq_mul_unit _ _ D.P.L D.P.isLB _ _ _ _ _ _ _ _ _ f g p
    (fun y J hJ => ⟨_, hp (𝟙_ _ ⊗ D.P.A) (𝟙 _) y J hJ⟩) hf hg
  by_contra hne
  refine hj (GlobalTheory.sec_eq_zero_of_sval_finite_level V (IsLocalRing.maximalIdeal V) (𝟙_ _) D.P.A (fun r hr => ?_) _ D.P.L
    D.P.isLB _ _ _ p (fun e => by
      by_contra h
      exact hne ⟨e, h⟩) j)
  have e : scal (𝟙_ (Over (Spec (CommRingCat.of V)))).hom r = i r := rfl
  rw [e, Ideal.mem_jacobson_bot]
  intro y
  obtain ⟨y, rfl⟩ := i.surjective y
  rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.mem_jacobson_bot] at hr
  have := (hr y).map i
  rwa [map_add, map_mul, map_one] at this

end GlobalTheory.UU.TwistNonvan

namespace GlobalTheory.UU
open TwistNonvan

/- English proof (translation)
Introduce `V _ _ _ hV D k f g α β₀ hnull hf hg`. Take `⟨hd, hcpl, hch⟩` from `hV`. Take `⟨p, hp⟩` from `exists_isProdB V D (𝟙_ _) k 1 β₀ (α - β₀) α (by abel) (f β₀) (g (α - β₀))`. Take `⟨e, he⟩` from `exists_level D _ _ p hp hf hg`. Take `⟨s₀, hs₀⟩` from `hnull e`.

Take `⟨⟨n, hn, hnu⟩, hcyc⟩` from `GlobalTheory.exists_finite_extension_primitive_residue V`. Set `u : D.X → D.X` to `fun β => (k + 1) • β - k • α`. Establish `hu : Function.Injective u` using `fun x y hxy => by`. Establish `h₁ : ((k + 1 : ℕ) : ℤ) • x = ((k + 1 : ℕ) : ℤ) • y`. Rewrite using `[natCast_zsmul, natCast_zsmul]`.

Conclude with `sub_left_injective hxy`. Conclude with `smul_right_injective D.X (by positivity) h₁`. Take `⟨j₀, hj₀⟩` from `GlobalTheory.laurent_coeff_eq_zero_of_vanish_torsion D.X n hn ((insert β₀ s₀).image u)`. Take `⟨W, iW, iL, iA, φ, ζ, hW, hφ, hnW, hζ, hprim⟩` from `hcyc n j₀ hn hnu`. Assume the negation of the conclusion as `hne`.

Establish `H : ∀ a : Multiplicative D.X →* Wˣ, ∃ (f' : ∀ α, SecBT D (TA V W) k α) (g' : ∀ α, SecBT D (TA V W) 1 α) (h : ∀ α, SecBT D (TA V W) (k + 1) α), PullT (toUnit _) f f' ∧ PullT (toUnit _) g g' ∧ ConvT (IsLocalRing.maximalIdeal V) (twist a f') (twist (a ^ k)⁻¹ g') h ∧ ∀ j, (h α).f j = …` using `fun a => by`. Assume the negation of the conclusion as `hh`. Use `hne ⟨W, iW, iL, iA, φ, a, hW, hφ, fun f' g' h h₁ h₂ h₃ => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h₄`. Conclude with `hh ⟨f', g', h, h₁, h₂, h₃, fun j => by_contra fun h₅ => h₄ ⟨j, h₅⟩⟩`.

Take `⟨hfin, hfree, hdom, -, -⟩` from `hW`. Use `he (GlobalTheory.sval_eq_zero_of_faithfullyFlat_base V W (IsLocalRing.maximalIdeal V) e (𝟙_ _ ⊗ D.P.A) _ D.P.L D.P.isLB _ _ _ p ?_)` and prove the remaining obligations. Introduce `Z r ω hω hl z J hJ`. Set `Z' : Over (Spec (CommRingCat.of V))` to `Over.mk (r ≫ (𝟙_ _ ⊗ D.P.A).hom)`. Set `rr : Z' ⟶ 𝟙_ _ ⊗ D.P.A` to `Over.homMk r rfl`.

Set `ωω : Z' ⟶ TA V W` to `Over.homMk ω hω`. Set `r' : Z' ⟶ TA V W ⊗ D.P.A` to `lift ωω (rr ≫ snd _ _)`. Establish `e₁ : r' ≫ toUnit _ ▷ D.P.A = rr`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Conclude with `toUnit_unique _ _`.

Simplify using `[r']`. Establish `e₂ : r'.left ≫ (toUnit (TA V W) ▷ D.P.A).left = rr.left` using `congrArg (fun q => q.left) e₁`. Establish `e₃ : r' ≫ snd _ _ = rr ≫ snd _ _` using `lift_snd _ _`. Take `⟨c, hc⟩` from `exists_constHom (W := W) (fst (TA V W) D.P.A).left r'.left z`. Set `T : D.X → Z'.left.presheaf.stalk z` to `fun β => sval (f β) rr.left z J * sval (g (α - β)) rr.left z J * (cubV D.cub (T := Z') z J (toUnit Z' ≫ D.c β) (toUnit Z' ≫ D.c (α - β)) (rr ≫ snd _ D.P.A)).val`.

Establish `e₄ : sval p rr.left z J = T β₀` using `hp Z' rr z J hJ`. Use `letI : Module W (Z'.left.presheaf.stalk z) := Module.compHom _ c`. Establish `key` using `hj₀ j₀ le_rfl W ζ hnW hζ hprim (Z'.left.presheaf.stalk z) (Function.extend u T 0) (fun a _ => by`. Take `⟨f', g', h, h₁, h₂, h₃, h₄⟩` from `H a`. Establish `v₁ : ∀ β, sval (f' β) r'.left z J = sval (f β) rr.left z J` using `fun β => (h₁ β _ r'.left z J hJ).trans (by rw [e₂])`.

Establish `v₂ : ∀ β, sval (g' β) r'.left z J = sval (g β) rr.left z J` using `fun β => (h₂ β _ r'.left z J hJ).trans (by rw [e₂])`. Use `sum_eq_zero _ D k α a f' g' h h₃ h₄ e Z' r' hl z J hJ (insert β₀ s₀) (fun β hβ => (v₁ β).trans (hs₀ β (fun hb => hβ (Finset.mem_insert_of_mem hb)) Z r hl z J hJ)) c hc` as an intermediate fact. Rewrite using `[Finset.sum_image (fun x _ y _ hxy => hu hxy)]`. Use `Eq.trans (Finset.sum_congr rfl fun β _ => ?_) this` and prove the remaining obligations. Rewrite using `[hu.extend_apply, v₁, v₂, e₃]`.

Use the proof step `rfl) (u β₀) (Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _))`. Rewrite `key` using `[hu.extend_apply]`. Conclude with `e₄.trans key`.
-/
theorem exists_twist_conv_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V) (k : ℕ) (f : ∀ α, SecBT D (𝟙_ _) k α) (g : ∀ α, SecBT D (𝟙_ _) 1 α) (α β₀ : D.X), NullFam (IsLocalRing.maximalIdeal V) f → (∃ j, (f β₀).f j ≠ 0) → (∃ j, (g (α - β₀)).f j ≠ 0) → ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (_ : Algebra V W) (φ : TF (R := V) (Kbar V) ⟶ TA V W) (a : Multiplicative D.X →* Wˣ), FinExt V W ∧ Function.Injective φ.left.appTop.hom ∧ ∀ (f' : ∀ α, SecBT D (TA V W) k α) (g' : ∀ α, SecBT D (TA V W) 1 α) (h : ∀ α, SecBT D (TA V W) (k + 1) α), PullT (toUnit _) f f' → PullT (toUnit _) g g' → ConvT (IsLocalRing.maximalIdeal V) (twist a f') (twist (a ^ k)⁻¹ g') h → ∃ j, (h α).f j ≠ 0 := by
  intro V _ _ _ hV D k f g α β₀ hnull hf hg
  classical
  obtain ⟨hd, hcpl, hch⟩ := hV
  obtain ⟨p, hp⟩ := exists_isProdB V D (𝟙_ _) k 1 β₀ (α - β₀) α (by abel) (f β₀) (g (α - β₀))
  obtain ⟨e, he⟩ := exists_level D _ _ p hp hf hg
  obtain ⟨s₀, hs₀⟩ := hnull e
  obtain ⟨⟨n, hn, hnu⟩, hcyc⟩ := GlobalTheory.exists_finite_extension_primitive_residue V
  let u : D.X → D.X := fun β => (k + 1) • β - k • α
  have hu : Function.Injective u := fun x y hxy => by
    have h₁ : ((k + 1 : ℕ) : ℤ) • x = ((k + 1 : ℕ) : ℤ) • y := by
      rw [natCast_zsmul, natCast_zsmul]; exact sub_left_injective hxy
    exact smul_right_injective D.X (by positivity) h₁
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.laurent_coeff_eq_zero_of_vanish_torsion D.X n hn ((insert β₀ s₀).image u)
  obtain ⟨W, iW, iL, iA, φ, ζ, hW, hφ, hnW, hζ, hprim⟩ := hcyc n j₀ hn hnu
  by_contra hne
  have H : ∀ a : Multiplicative D.X →* Wˣ, ∃ (f' : ∀ α, SecBT D (TA V W) k α) (g' : ∀ α, SecBT D (TA V W) 1 α)
      (h : ∀ α, SecBT D (TA V W) (k + 1) α), PullT (toUnit _) f f' ∧ PullT (toUnit _) g g' ∧
      ConvT (IsLocalRing.maximalIdeal V) (twist a f') (twist (a ^ k)⁻¹ g') h ∧ ∀ j, (h α).f j = 0 := fun a => by
    by_contra hh
    refine hne ⟨W, iW, iL, iA, φ, a, hW, hφ, fun f' g' h h₁ h₂ h₃ => ?_⟩
    by_contra h₄
    exact hh ⟨f', g', h, h₁, h₂, h₃, fun j => by_contra fun h₅ => h₄ ⟨j, h₅⟩⟩
  obtain ⟨hfin, hfree, hdom, -, -⟩ := hW
  refine he (GlobalTheory.sval_eq_zero_of_faithfullyFlat_base V W (IsLocalRing.maximalIdeal V) e (𝟙_ _ ⊗ D.P.A) _ D.P.L
    D.P.isLB _ _ _ p ?_)
  intro Z r ω hω hl z J hJ
  let Z' : Over (Spec (CommRingCat.of V)) := Over.mk (r ≫ (𝟙_ _ ⊗ D.P.A).hom)
  let rr : Z' ⟶ 𝟙_ _ ⊗ D.P.A := Over.homMk r rfl
  let ωω : Z' ⟶ TA V W := Over.homMk ω hω
  let r' : Z' ⟶ TA V W ⊗ D.P.A := lift ωω (rr ≫ snd _ _)
  have e₁ : r' ≫ toUnit _ ▷ D.P.A = rr := by
    apply CartesianMonoidalCategory.hom_ext
    · exact toUnit_unique _ _
    · simp [r']
  have e₂ : r'.left ≫ (toUnit (TA V W) ▷ D.P.A).left = rr.left := congrArg (fun q => q.left) e₁
  have e₃ : r' ≫ snd _ _ = rr ≫ snd _ _ := lift_snd _ _
  obtain ⟨c, hc⟩ := exists_constHom (W := W) (fst (TA V W) D.P.A).left r'.left z
  let T : D.X → Z'.left.presheaf.stalk z := fun β => sval (f β) rr.left z J * sval (g (α - β)) rr.left z J *
      (cubV D.cub (T := Z') z J (toUnit Z' ≫ D.c β) (toUnit Z' ≫ D.c (α - β)) (rr ≫ snd _ D.P.A)).val
  have e₄ : sval p rr.left z J = T β₀ := hp Z' rr z J hJ
  letI : Module W (Z'.left.presheaf.stalk z) := Module.compHom _ c
  have key := hj₀ j₀ le_rfl W ζ hnW hζ hprim (Z'.left.presheaf.stalk z) (Function.extend u T 0) (fun a _ => by
    obtain ⟨f', g', h, h₁, h₂, h₃, h₄⟩ := H a
    have v₁ : ∀ β, sval (f' β) r'.left z J = sval (f β) rr.left z J := fun β =>
      (h₁ β _ r'.left z J hJ).trans (by rw [e₂])
    have v₂ : ∀ β, sval (g' β) r'.left z J = sval (g β) rr.left z J := fun β =>
      (h₂ β _ r'.left z J hJ).trans (by rw [e₂])
    have := sum_eq_zero _ D k α a f' g' h h₃ h₄ e Z' r' hl z J hJ (insert β₀ s₀) (fun β hβ =>
      (v₁ β).trans (hs₀ β (fun hb => hβ (Finset.mem_insert_of_mem hb)) Z r hl z J hJ)) c hc
    rw [Finset.sum_image (fun x _ y _ hxy => hu hxy)]
    refine Eq.trans (Finset.sum_congr rfl fun β _ => ?_) this
    rw [hu.extend_apply, v₁, v₂, e₃]
    rfl) (u β₀) (Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _))
  rw [hu.extend_apply] at key
  exact e₄.trans key

end GlobalTheory.UU

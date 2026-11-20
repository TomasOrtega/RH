import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkIdComapOfAffine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmpStOfSabExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SabExtNormalStOfHomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TorRef

/- English proof (translation)
Use `revert hn`. Proceed by induction on `n using Nat.recOnMul with`. Consider the case `zero => intro h0`. Conclude with `absurd rfl h0`. Consider the case `one => intro _`.

Simplify using the standard rewrite rules. Consider the case `prime p hp => intro _`. Conclude with `h p hp`. Consider the case `mul a b ha hb`. Introduce `hab`.

Rewrite using `[Nat.cast_mul]`. Conclude with `(ha (left_ne_zero_of_mul hab)).mul (hb (right_ne_zero_of_mul hab))`.
-/
theorem isUnit_natCast_of_primes {W : Type} [CommRing W] (h : ∀ p : ℕ, p.Prime → IsUnit (p : W)) (n : ℕ)
    (hn : n ≠ 0) : IsUnit (n : W) := by
  revert hn
  induction n using Nat.recOnMul with
  | zero => intro h0; exact absurd rfl h0
  | one => intro _; simp
  | prime p hp => intro _; exact h p hp
  | mul a b ha hb =>
    intro hab
    rw [Nat.cast_mul]
    exact (ha (left_ne_zero_of_mul hab)).mul (hb (right_ne_zero_of_mul hab))

/- English proof (translation)
Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))`. Establish `hN : Ideal.absNorm (Ideal.span {a}) ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`. Conclude with `ha`. Establish `e : f b * f a = (Ideal.absNorm (Ideal.span {a}) : W)` using `by rw [← map_mul, hb, map_natCast]`.

Conclude with `isUnit_of_mul_isUnit_right (e ▸ isUnit_natCast_of_primes h _ hN)`.
-/
theorem isUnit_map_of_ne_zero {K : Type} [Field K] [NumberField K] {W : Type} [CommRing W]
    (h : ∀ p : ℕ, p.Prime → IsUnit (p : W)) (f : 𝓞 K →+* W) {a : 𝓞 K} (ha : a ≠ 0) : IsUnit (f a) := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
  have hN : Ideal.absNorm (Ideal.span {a}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact ha
  have e : f b * f a = (Ideal.absNorm (Ideal.span {a}) : W) := by rw [← map_mul, hb, map_natCast]
  exact isUnit_of_mul_isUnit_right (e ▸ isUnit_natCast_of_primes h _ hN)

/- English proof (translation)
Unfold `idlAlong`. Rewrite using `[VanStalk.stalkId_comap, Ideal.map_map, Scheme.stalkClosedPointTo_comp]`. Both sides reduce to the same expression.
-/
theorem idlAlong_comap {X X' : Scheme.{0}} (k : X' ⟶ X) (I : X.IdealSheafData) {R : Type} [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ X') : idlAlong (I.comap k) ξ = idlAlong I (ξ ≫ k) := by
  unfold idlAlong
  rw [VanStalk.stalkId_comap, Ideal.map_map, Scheme.stalkClosedPointTo_comp]
  rfl

/- English proof (translation)
Take `⟨U, hU, hx, -⟩` from `Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (show ξ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)`. Establish `hle : ⊤ ≤ ξ ⁻¹ᵁ U` using `(Scheme.preimage_eq_top_of_closedPoint_mem ξ hx).ge`. Rewrite using `[TraitOrder.idlAlong_eq_map _ ξ ⟨U, hU⟩ hle, TraitOrder.idlAlong_eq_map _ ξ ⟨U, hU⟩ hle, ← Ideal.map_pow]`. Use `congr 1`.
-/
theorem idlAlong_pow {X : Scheme.{0}} (I : X.IdealSheafData) (n : ℕ) {R : Type} [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ X) : idlAlong (I ^ n) ξ = idlAlong I ξ ^ n := by
  obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show ξ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
  have hle : ⊤ ≤ ξ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem ξ hx).ge
  rw [TraitOrder.idlAlong_eq_map _ ξ ⟨U, hU⟩ hle, TraitOrder.idlAlong_eq_map _ ξ ⟨U, hU⟩ hle, ← Ideal.map_pow]
  congr 1

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c X Z Y BY π e J EX n d' φ hY hB W _ _ _ hW hp ϖ hϖ χ t mt P hr be hbe hmon`. Take `⟨-, -, -, hjQ, -, hEX, -⟩` from `hB`. Use `c.fin` as an intermediate fact. Establish `: NumberField c.F` using `{}`. Set `f : 𝓞 c.F →+* W` to `(Spec.preimage (χ ≫ Z.s)).hom`.

Set `g : c.F →+* W` to `IsLocalization.lift (M := nonZeroDivisors (𝓞 c.F)) (S := c.F) (g := f) fun y => isUnit_map_of_ne_zero hp f (nonZeroDivisors.ne_zero y.2)`. Establish `hg : g.comp (algebraMap (𝓞 c.F) c.F) = f` using `IsLocalization.lift_comp _`. Establish `hsq : χ ≫ Z.s = spMap g ≫ spMap (algebraMap (𝓞 c.F) c.F)`. Simplify using `only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hg, f, CommRingCat.ofHom_hom, Spec.map_preimage]`. Set `χ₀ : Sp W ⟶ gen Z` to `pullback.lift χ (spMap g) hsq`.

Establish `hχ : χ₀ ≫ genι Z = χ` using `pullback.lift_fst _ _ _`. Establish `hI : idlAlong EX.idealSheaf χ = idlAlong BY.idealSheaf (χ₀ ≫ e.inv ≫ genι Y) ^ n`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Category.assoc, e.inv_hom_id_assoc, hχ]`. Use `_ = idlAlong (EX.idealSheaf.comap (e.hom ≫ genι Z)) (χ₀ ≫ e.inv) := (idlAlong_comap _ _ _).symm`.

Use `_ = idlAlong ((BY.idealSheaf ^ n).comap (genι Y)) (χ₀ ≫ e.inv) := by rw [hEX]`. Use `_ = idlAlong (BY.idealSheaf ^ n) ((χ₀ ≫ e.inv) ≫ genι Y) := idlAlong_comap _ _ _`. Use `_ = _ := by rw [idlAlong_pow, Category.assoc]`. Establish `hZY : Z.jQ ≫ e.inv = Y.jQ` using `by rw [← hjQ, Category.assoc, Iso.hom_inv_id, Category.comp_id]`. Take `⟨t₀, n₁, n₂, -⟩` from `cmpSt_of_sabExtNormalSt (sabExtNormalSt_of_homExtNormalSt homExtNormal) E H D l Xo c c.F (𝓞 c.F) (RingHom.id c.F) (algebraMap (𝓞 c.F) c.F) Y Z e.inv hZY (ModelRelCompare.normal_genericFibre Z (ModelRelCompare.isDedFrac_in_use c).1).1`.

Take `⟨a⟩` from `TraitOrder.cancel hχ n₁ mt`. Take `⟨b⟩` from `TraitOrder.comp (h := χ₀ ≫ e.inv ≫ genι Y) rfl n₂ a`. Establish `hr' : Set.range (jK W ≫ χ₀ ≫ e.inv ≫ genι Y) ⊆ Set.range Y.j`. Introduce and unpack `_ ⟨p, rfl⟩`. Establish `hz : (jK W ≫ χ₀) p ∈ Set.range Z.jQ`.

Rewrite using `[← Z.ab_gen]`. Take `⟨q, hq⟩` from `hr ⟨p, rfl⟩`. Use `show (jK W ≫ χ₀ ≫ genι Z) p ∈ abLocus Z.t.G`. Rewrite using `[hχ, ← hq]`. Use `show genι Z (Z.jQ q) ∈ abLocus Z.t.G`.

Rewrite using `[← Set.mem_preimage, Z.ab_gen]`. Conclude with `⟨q, rfl⟩`. Take `⟨q, hq⟩` from `hz`. Use `⟨q, ?_⟩` and prove the remaining obligations. Use `show (Y.jQ ≫ genι Y) q = _`.

Rewrite using `[← hZY]`. Simplify using `only [Scheme.Hom.comp_apply] at hq ⊢`. Rewrite using `[hq]`. Take `⟨m₀, hm₀, hid⟩` from `hY W hW ϖ hϖ _ t b P hr' be hbe hmon`. Use `⟨n * m₀, ?_, ?_⟩` and prove the remaining obligations.

Use `push_cast`. Rewrite using `[hm₀]`. Simplify using `only [InvFun.evalZ, InvFun.eval, comb]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hI, hid, Ideal.span_singleton_pow, pow_mul']`.
-/
theorem blowOrd_eqChar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : EffCartierData Y.X) (π : Z.X ⟶ X.X) (e : gen Y ≅ gen Z) (J : X.X.IdealSheafData) (EX : EffCartierData Z.X) (n d' : ℕ) (φ : InvFun (𝓞 E)), IsPhiDiv (comb 0 φ d' φ) Y BY → IsBlowOf X Z Y BY π e J EX n → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → (∀ p : ℕ, p.Prime → IsUnit (p : W)) → ∀ ϖ : W, Irreducible ϖ → ∀ (χ : Sp W ⟶ Z.X) (t : SAB H (Sp W)) (_ : SABMap t Z.t χ) (P : PELUnif (maximalIdeal W) t), Set.range (jK W ≫ χ) ⊆ Set.range Z.j → ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] → ∃ m : ℕ, (m : ℝ) = (comb 0 φ (n * d') φ).evalZ be ∧ idlAlong EX.idealSheaf χ = Ideal.span {ϖ ^ m} := by
  intro E _ _ _ H D l Xo c X Z Y BY π e J EX n d' φ hY hB W _ _ _ hW hp ϖ hϖ χ t mt P hr be hbe hmon
  obtain ⟨-, -, -, hjQ, -, hEX, -⟩ := hB
  have := c.fin
  have : NumberField c.F := {}

  let f : 𝓞 c.F →+* W := (Spec.preimage (χ ≫ Z.s)).hom
  let g : c.F →+* W := IsLocalization.lift (M := nonZeroDivisors (𝓞 c.F)) (S := c.F) (g := f)
    fun y => isUnit_map_of_ne_zero hp f (nonZeroDivisors.ne_zero y.2)
  have hg : g.comp (algebraMap (𝓞 c.F) c.F) = f := IsLocalization.lift_comp _
  have hsq : χ ≫ Z.s = spMap g ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hg, f, CommRingCat.ofHom_hom, Spec.map_preimage]
  let χ₀ : Sp W ⟶ gen Z := pullback.lift χ (spMap g) hsq
  have hχ : χ₀ ≫ genι Z = χ := pullback.lift_fst _ _ _

  have hI : idlAlong EX.idealSheaf χ = idlAlong BY.idealSheaf (χ₀ ≫ e.inv ≫ genι Y) ^ n := by
    calc idlAlong EX.idealSheaf χ = idlAlong EX.idealSheaf ((χ₀ ≫ e.inv) ≫ e.hom ≫ genι Z) := by
          rw [Category.assoc, e.inv_hom_id_assoc, hχ]
      _ = idlAlong (EX.idealSheaf.comap (e.hom ≫ genι Z)) (χ₀ ≫ e.inv) := (idlAlong_comap _ _ _).symm
      _ = idlAlong ((BY.idealSheaf ^ n).comap (genι Y)) (χ₀ ≫ e.inv) := by rw [hEX]
      _ = idlAlong (BY.idealSheaf ^ n) ((χ₀ ≫ e.inv) ≫ genι Y) := idlAlong_comap _ _ _
      _ = _ := by rw [idlAlong_pow, Category.assoc]

  have hZY : Z.jQ ≫ e.inv = Y.jQ := by rw [← hjQ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨t₀, n₁, n₂, -⟩ := cmpSt_of_sabExtNormalSt (sabExtNormalSt_of_homExtNormalSt homExtNormal) E H D l Xo c
    c.F (𝓞 c.F) (RingHom.id c.F) (algebraMap (𝓞 c.F) c.F) Y Z e.inv hZY
    (ModelRelCompare.normal_genericFibre Z (ModelRelCompare.isDedFrac_in_use c).1).1
  obtain ⟨a⟩ := TraitOrder.cancel hχ n₁ mt
  obtain ⟨b⟩ := TraitOrder.comp (h := χ₀ ≫ e.inv ≫ genι Y) rfl n₂ a

  have hr' : Set.range (jK W ≫ χ₀ ≫ e.inv ≫ genι Y) ⊆ Set.range Y.j := by
    rintro _ ⟨p, rfl⟩
    have hz : (jK W ≫ χ₀) p ∈ Set.range Z.jQ := by
      rw [← Z.ab_gen]
      obtain ⟨q, hq⟩ := hr ⟨p, rfl⟩
      show (jK W ≫ χ₀ ≫ genι Z) p ∈ abLocus Z.t.G
      rw [hχ, ← hq]
      show genι Z (Z.jQ q) ∈ abLocus Z.t.G
      rw [← Set.mem_preimage, Z.ab_gen]
      exact ⟨q, rfl⟩
    obtain ⟨q, hq⟩ := hz
    refine ⟨q, ?_⟩
    show (Y.jQ ≫ genι Y) q = _
    rw [← hZY]
    simp only [Scheme.Hom.comp_apply] at hq ⊢
    rw [hq]
  obtain ⟨m₀, hm₀, hid⟩ := hY W hW ϖ hϖ _ t b P hr' be hbe hmon
  refine ⟨n * m₀, ?_, ?_⟩
  · push_cast
    rw [hm₀]
    simp only [InvFun.evalZ, InvFun.eval, comb]
    push_cast
    ring
  · rw [hI, hid, Ideal.span_singleton_pow, pow_mul']

end GlobalTheory.TorRef

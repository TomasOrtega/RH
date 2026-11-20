import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GtPtsVal
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
open GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.Poinc.Sep.Frames

/- English proof (translation)
Use `set a : k₀ := ⟨x ^ n, hx⟩`. Use `set p : Polynomial k₀ := Polynomial.X ^ n - Polynomial.C a`. Establish `hp : p ≠ 0` using `(Polynomial.monic_X_pow_sub_C a (by omega)).ne_zero`. Establish `hs : p.Splits` using `IsAlgClosed.splits p`. Establish `hroot : x ∈ (p.map k₀.subtype).roots`.

Rewrite using `[Polynomial.mem_roots (Polynomial.map_ne_zero hp)]`. Simplify using `[p, a]`. Rewrite `hroot` using `[hs.roots_map k₀.subtype]`. Take `⟨y, -, rfl⟩` from `Multiset.mem_map.1 hroot`. Conclude with `y.2`.
-/
theorem mem_of_pow_mem {K : Type} [Field K] (k₀ : Subfield K) [IsAlgClosed k₀] {n : ℕ} (hn : 1 ≤ n) {x : K}
    (hx : x ^ n ∈ k₀) : x ∈ k₀ := by
  classical
  set a : k₀ := ⟨x ^ n, hx⟩
  set p : Polynomial k₀ := Polynomial.X ^ n - Polynomial.C a
  have hp : p ≠ 0 := (Polynomial.monic_X_pow_sub_C a (by omega)).ne_zero
  have hs : p.Splits := IsAlgClosed.splits p
  have hroot : x ∈ (p.map k₀.subtype).roots := by
    rw [Polynomial.mem_roots (Polynomial.map_ne_zero hp)]
    simp [p, a]
  rw [hs.roots_map k₀.subtype] at hroot
  obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hroot
  exact y.2

/- English proof (translation)
Establish `hi : IsIntegral V x` using `⟨Polynomial.X ^ n - Polynomial.C (u : V), Polynomial.monic_X_pow_sub_C _ (by omega), by simp [hx]⟩`. Take `⟨a, rfl⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hi`. Establish `ha : a ^ n = u` using `IsFractionRing.injective V (FractionRing V) (by rw [map_pow, hx])`. Establish `hu : IsUnit (a ^ n)` using `ha ▸ u.isUnit`. Conclude with `⟨(isUnit_pow_iff (by omega)).1 hu |>.unit, rfl⟩`.
-/
theorem exists_unit_of_pow {V : Type} [CommRing V] [IsDomain V] [IsIntegrallyClosed V] {n : ℕ} (hn : 1 ≤ n)
    {x : FractionRing V} {u : Vˣ} (hx : x ^ n = algebraMap V (FractionRing V) u) :
    ∃ u' : Vˣ, x = algebraMap V (FractionRing V) u' := by
  have hi : IsIntegral V x := ⟨Polynomial.X ^ n - Polynomial.C (u : V), Polynomial.monic_X_pow_sub_C _ (by omega),
    by simp [hx]⟩
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  have ha : a ^ n = u := IsFractionRing.injective V (FractionRing V) (by rw [map_pow, hx])
  have hu : IsUnit (a ^ n) := ha ▸ u.isUnit
  exact ⟨(isUnit_pow_iff (by omega)).1 hu |>.unit, rfl⟩

end GlobalTheory.Poinc.Sep.Frames

namespace GlobalTheory.Poinc.Sep.Frames

variable {V : Type} [CommRing V] [IsDomain V] {D : DegPre V}

/- English proof (translation)
Use `show jFK (R := V) (FractionRing V) ≫ jK V = _`. Rewrite using `[jFK, jK, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem toUnit_left_eq : (toUnit (TF (R := V) (FractionRing V))).left =
    Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) := by
  show jFK (R := V) (FractionRing V) ≫ jK V = _
  rw [jFK, jK, ← Spec.map_comp]
  rfl

/- English proof (translation)
Rewrite using `[← gs_unit _ z ⊤ trivial, toUnit_left_eq, GlobalTheory.RatioVal.gs_specMap]`. Conclude with `(GlobalTheory.RatioVal.gs_id_const z _).symm`.
-/
theorem gm_top_eq (ρ : Γ(Spec (CommRingCat.of V), ⊤)ˣ) (z : (TF (R := V) (FractionRing V)).left) :
    (gm (toUnit (TF (R := V) (FractionRing V))).left z ⊤ ρ).val = cst (FractionRing V) z
      (algebraMap V (FractionRing V) (Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom ρ)) := by
  rw [← gs_unit _ z ⊤ trivial, toUnit_left_eq, GlobalTheory.RatioVal.gs_specMap]
  exact (GlobalTheory.RatioVal.gs_id_const z _).symm

/- English proof (translation)
Introduce `_ _` and use `(map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm`.
-/
theorem oneGen_gen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

/- English proof (translation)
Take `⟨s, hs, vs⟩` from `h.out D.P.isLB (K := PEmpty) PEmpty.elim PEmpty.elim (fun U _ h => (hP U h).trans (Fintype.prod_empty _).symm)`. Take `⟨ρ, hρ⟩` from `exists_ratio D.P.isLB rfl s (LB.oneGen D.P.L) hs (oneGen_gen _)`. Use `⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom ρ, fun z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[← vs _ _ z J hJ, hρ _ _ z J hJ, val_one, _root_.mul_one]`. Conclude with `gm_top_eq ρ z`.
-/
theorem exists_unit_of_triv {P v} (h : SymFrame.GRep D.P.L (𝟙_ (Over (Spec (CommRingCat.of V)))) P v)
    (hP : ∀ (U : Type) [CommGroup U] (h : ((𝟙_ (Over (Spec (CommRingCat.of V)))).left ⟶ D.P.A.left) → U), P U h = 1) :
    ∃ u : Vˣ, ∀ z J, Good D.P.L z J → (v (TF (R := V) (FractionRing V)) (toUnit _) z J).val =
      cst (FractionRing V) z (algebraMap V (FractionRing V) u) := by
  obtain ⟨s, hs, vs⟩ := h.out D.P.isLB (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun U _ h => (hP U h).trans (Fintype.prod_empty _).symm)
  obtain ⟨ρ, hρ⟩ := exists_ratio D.P.isLB rfl s (LB.oneGen D.P.L) hs (oneGen_gen _)
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom ρ, fun z J hJ => ?_⟩
  rw [← vs _ _ z J hJ, hρ _ _ z J hJ, val_one, _root_.mul_one]
  exact gm_top_eq ρ z

/- English proof (translation)
Take `⟨ρ, hρ⟩` from `exists_ratio D.P.isLB (funext hφ) G (LB.pullGen D.P.L _ _ t (toUnit (TF (R := V) (FractionRing V))).left) hG (pullGen_isGen _ _ _ _ ht _)`. Use `⟨(Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).hom.hom ρ.val, fun z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[hρ _ _ z J hJ, val_pull hJ, Category.id_comp, Units.val_mul, ← gs_unit _ z ⊤ trivial]`. Use `congr 1`. Use `show gs (𝟙 _) z ⊤ ρ.val = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).hom.hom ρ.val))`.

Rewrite using `[← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]`.
-/
theorem exists_ratio_gen {K : Type} [Fintype K] {φ : K → ((𝟙_ (Over (Spec (CommRingCat.of V)))).left ⟶ D.P.A.left)}
    {ε : K → ℤ} {φF : K → ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left)}
    (hφ : ∀ k, φF k = (toUnit (TF (R := V) (FractionRing V))).left ≫ φ k)
    (G : LB.Gen (LB.LinComb D.P.L φF ε)) (hG : G.IsGen) (t : LB.Gen (LB.LinComb D.P.L φ ε)) (ht : t.IsGen) :
    ∃ x : FractionRing V, ∀ z J, Good D.P.L z J → (val G (𝟙 _) z J).val =
      cst (FractionRing V) z x * (val t (toUnit (TF (R := V) (FractionRing V))).left z J).val := by
  obtain ⟨ρ, hρ⟩ := exists_ratio D.P.isLB (funext hφ) G
    (LB.pullGen D.P.L _ _ t (toUnit (TF (R := V) (FractionRing V))).left) hG (pullGen_isGen _ _ _ _ ht _)
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).hom.hom ρ.val, fun z J hJ => ?_⟩
  rw [hρ _ _ z J hJ, val_pull hJ, Category.id_comp, Units.val_mul, ← gs_unit _ z ⊤ trivial]
  congr 1
  show gs (𝟙 _) z ⊤ ρ.val = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).hom.hom ρ.val))
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

end GlobalTheory.Poinc.Sep.Frames

namespace GlobalTheory.Poinc.Sep.Frames

variable {V : Type} [CommRing V] [IsDomain V] {D : DegPre V}

/- English proof (translation)
Rewrite using `[toUnit_left_eq]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]`. Introduce `y`. Establish `hz : (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V)) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V)`.

Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Ideal.comap (algebraMap V (FractionRing V)) ⊥ = ⊥`. Conclude with `Ideal.comap_bot_of_injective _ (IsFractionRing.injective V _)`. Establish `hmem : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V) ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))))` using `⟨_, hz⟩`. Conclude with `closure_mono (Set.singleton_subset_iff.2 hmem) ((PrimeSpectrum.le_iff_mem_closure _ _).1 (show (⊥ : Ideal V) ≤ y.asIdeal from bot_le))`.
-/
theorem isDominant_toUnit_left : IsDominant (toUnit (TF (R := V) (FractionRing V))).left := by
  rw [toUnit_left_eq]
  constructor
  rw [DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro y
  have hz : (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))))
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V)) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V) := by
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap V (FractionRing V)) ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V _)
  have hmem : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V) ∈
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) := ⟨_, hz⟩
  exact closure_mono (Set.singleton_subset_iff.2 hmem)
    ((PrimeSpectrum.le_iff_mem_closure _ _).1 (show (⊥ : Ideal V) ≤ y.asIdeal from bot_le))

/- English proof (translation)
Establish `: IsProper D.P.A.hom` using `D.P.isAb.proper`. Use `isDominant_toUnit_left (V := V)` as an intermediate fact. Use `haveI : IsReduced (𝟙_ (Over (Spec (CommRingCat.of V)))).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of V)))`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `ext_of_isDominant_of_isSeparated D.P.A.hom ?_ (toUnit (TF (R := V) (FractionRing V))).left ?_` and prove the remaining obligations.

Rewrite using `[Over.w, Over.w]`. Rewrite using `[← Over.comp_left, ← Over.comp_left, MonObj.comp_pow, h, MonObj.comp_one]`.
-/
theorem pow_eq_one_of_generic (b : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ D.P.A) (n : ℕ)
    (h : (toUnit (TF (R := V) (FractionRing V)) ≫ b) ^ n = 1) : b ^ n = 1 := by
  have : IsProper D.P.A.hom := D.P.isAb.proper
  have := isDominant_toUnit_left (V := V)
  haveI : IsReduced (𝟙_ (Over (Spec (CommRingCat.of V)))).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of V)))
  apply Over.OverMorphism.ext
  refine ext_of_isDominant_of_isSeparated D.P.A.hom ?_ (toUnit (TF (R := V) (FractionRing V))).left ?_
  · rw [Over.w, Over.w]
  · rw [← Over.comp_left, ← Over.comp_left, MonObj.comp_pow, h, MonObj.comp_one]

end GlobalTheory.Poinc.Sep.Frames

namespace GlobalTheory.Poinc.Sep.Frames

open GlobalTheory.UT.CoefBasic

variable {V : Type} [CommRing V] [IsDomain V] {D : DegPre V}

/- English proof (translation)
Rewrite `h` using `[cst_eq, cst_eq]`. Conclude with `cstH_inj z h`.
-/
theorem cst_inj (z : (TF (R := V) (FractionRing V)).left) {x y : FractionRing V}
    (h : cst (FractionRing V) z x = cst (FractionRing V) z y) : x = y := by
  rw [cst_eq, cst_eq] at h; exact cstH_inj z h

/- English proof (translation)
Substitute `hβ` using the available equality. Take `⟨κ, hκn⟩` from `SymFrame.exists_kap (D := D) GlobalTheory.abelianSchemeLaws_all.1.mulPull N`. Apply the tactic sequence `obtain ⟨x, hx⟩ := exists_ratio_gen (φ := ![(η[D.P.A]).left, b.left]) (φF := DegPre.lineφ D (FractionRing V) (toUnit _ ≫ b)) (fun k => by fin_cases k <;> rfl) w hw t ht`. Establish `G` using `((SymFrame.grep_gen t ht (𝟙 _)).pow (N ^ 2)).mul (SymFrame.grep_kap κ hκn.1 b)`. Take `⟨u, hu⟩` from `exists_unit_of_triv G (fun U _ h => by`.

Rewrite using `[Fin.prod_univ_two, hbN, ← SymFrame.eta_eq]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, DegPre.lineε, Category.comp_id, Category.id_comp]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]`. Rewrite using `[← natCast_zsmul]`.

Use `push_cast`. Use the proof step `module)`. Establish `key : ∀ z J, Good D.P.L z J → x ^ (N ^ 2) * algebraMap V (FractionRing V) u = 1` using `fun z J hJ => by`. Establish `a` using `congrArg Units.val (hκ κ hκn z J hJ)`. Establish `c` using `hu z J hJ`.

Simplify using `only [Category.comp_id] at c`. Rewrite `a` using `[Units.val_mul, Units.val_pow_eq_pow_val, hx z J hJ, mul_pow, _root_.mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, c, Units.val_one, cst_eq, cst_eq, ← map_pow, ← map_mul, ← map_one (cstH z)]`. Conclude with `cstH_inj z a`. Take `⟨z⟩` from `exists_pt (R := V) (F := FractionRing V)`. Take `⟨J, hJ⟩` from `exists_good' D.P.isLB z`.

Establish `k` using `key z J hJ`. Establish `hxu : x ^ (N ^ 2) = algebraMap V (FractionRing V) (u⁻¹ : Vˣ)`. Rewrite using `[map_units_inv]`. Conclude with `eq_inv_of_mul_eq_one_left k`. Take `⟨u', hu'⟩` from `exists_unit_of_pow (Nat.one_le_pow _ _ (by omega)) hxu`.

Conclude with `⟨u', fun z J hJ => by rw [hx z J hJ, hu']⟩`.
-/
theorem frame_unit_core [IsNoetherianRing V] [IsIntegrallyClosed V] {N : ℕ} (hN : 1 ≤ N)
    (b : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ D.P.A) (hbN : b ^ N = 1)
    {β : TF (R := V) (FractionRing V) ⟶ D.P.A} (hβ : β = toUnit _ ≫ b)
    (w : Frm D (FractionRing V) 1 β) (hw : w.IsGen)
    (hκ : ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1), Normd κ → ∀ z J, Good D.P.L z J →
      val w (𝟙 _) z J ^ (N ^ 2) * val κ β.left z J = 1)
    (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))) (ht : t.IsGen) :
    ∃ u : Vˣ, ∀ z J, Good D.P.L z J → (val w (𝟙 _) z J).val =
      cst (FractionRing V) z (algebraMap V (FractionRing V) u) *
        (val t (toUnit (TF (R := V) (FractionRing V))).left z J).val := by
  subst hβ
  obtain ⟨κ, hκn⟩ := SymFrame.exists_kap (D := D) GlobalTheory.abelianSchemeLaws_all.1.mulPull N
  obtain ⟨x, hx⟩ := exists_ratio_gen (φ := ![(η[D.P.A]).left, b.left])
    (φF := DegPre.lineφ D (FractionRing V) (toUnit _ ≫ b)) (fun k => by fin_cases k <;> rfl) w hw t ht
  have G := ((SymFrame.grep_gen t ht (𝟙 _)).pow (N ^ 2)).mul (SymFrame.grep_kap κ hκn.1 b)
  obtain ⟨u, hu⟩ := exists_unit_of_triv G (fun U _ h => by
    rw [Fin.prod_univ_two, hbN, ← SymFrame.eta_eq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, DegPre.lineε, Category.comp_id, Category.id_comp]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
    rw [← natCast_zsmul]
    push_cast
    module)
  have key : ∀ z J, Good D.P.L z J → x ^ (N ^ 2) * algebraMap V (FractionRing V) u = 1 := fun z J hJ => by
    have a := congrArg Units.val (hκ κ hκn z J hJ)
    have c := hu z J hJ
    simp only [Category.comp_id] at c
    rw [Units.val_mul, Units.val_pow_eq_pow_val, hx z J hJ, mul_pow, _root_.mul_assoc, ← Units.val_pow_eq_pow_val,
      ← Units.val_mul, c, Units.val_one, cst_eq, cst_eq, ← map_pow, ← map_mul, ← map_one (cstH z)] at a
    exact cstH_inj z a
  obtain ⟨z⟩ := exists_pt (R := V) (F := FractionRing V)
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB z
  have k := key z J hJ
  have hxu : x ^ (N ^ 2) = algebraMap V (FractionRing V) (u⁻¹ : Vˣ) := by
    rw [map_units_inv]; exact eq_inv_of_mul_eq_one_left k
  obtain ⟨u', hu'⟩ := exists_unit_of_pow (Nat.one_le_pow _ _ (by omega)) hxu
  exact ⟨u', fun z J hJ => by rw [hx z J hJ, hu']⟩

end GlobalTheory.Poinc.Sep.Frames

namespace GlobalTheory.Poinc.Sep.Frames

open GlobalTheory.UT.CoefBasic GlobalTheory.TorusExt

variable {V : Type} [CommRing V] [IsDomain V] {D : DegPre V}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Conclude with `⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, LB.oneGen D.P.L, oneGen_gen _, fun _ _ _ => by simp, fun _ _ _ _ _ => by simp [val_one]⟩`. Consider the case `succ n ih`. Conclude with `(ih.mul (SymFrame.grep_cub c (b ^ n) b)).congr (fun _ _ _ => (Finset.prod_range_succ _ _).symm) (fun _ _ _ _ _ => (Finset.prod_range_succ _ _).symm)`.
-/
theorem grep_cubProd (c b : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ D.P.A) (n : ℕ) :
    SymFrame.GRep D.P.L (𝟙_ (Over (Spec (CommRingCat.of V))))
      (fun _ _ h => ∏ i ∈ Finset.range n, (h (c * b ^ i * b).left * (h (c * b ^ i).left)⁻¹ * (h (c * b).left)⁻¹ *
        (h (b ^ i * b).left)⁻¹ * h c.left * h (b ^ i).left * h b.left *
        (h (1 : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ D.P.A).left)⁻¹))
      (fun _ r z J => ∏ i ∈ Finset.range n, cubV D.cub z J (r ≫ c) (r ≫ b ^ i) (r ≫ b)) := by
  induction n with
  | zero =>
    exact ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, LB.oneGen D.P.L, oneGen_gen _,
      fun _ _ _ => by simp, fun _ _ _ _ _ => by simp [val_one]⟩
  | succ n ih =>
    exact (ih.mul (SymFrame.grep_cub c (b ^ n) b)).congr (fun _ _ _ => (Finset.prod_range_succ _ _).symm)
      (fun _ _ _ _ _ => (Finset.prod_range_succ _ _).symm)

attribute [local instance] GlobalTheory.TorusExt.gtGroup

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [zero_nsmul, zero_val χ hJ, Finset.prod_range_zero, _root_.mul_one, pow_zero]`. Consider the case `succ n ih`. Establish `e` using `add_val (n • g) g χ hJ`. Rewrite `e` using `[nsmul_b]`.

Rewrite using `[succ_nsmul, Finset.prod_range_succ, pow_succ, ← ih, ← _root_.mul_assoc, mul_right_comm, e]`. The two sides agree by associativity and commutativity.
-/
theorem charVal_nsmul (g : GtPtF D (FractionRing V)) (χ : D.X) {z J} (hJ : Good D.P.L z J) (n : ℕ) :
    charVal (n • g) χ z J * ∏ i ∈ Finset.range n, th D z J (cP D _ χ) (g.b ^ i) g.b = charVal g χ z J ^ n := by
  induction n with
  | zero => rw [zero_nsmul, zero_val χ hJ, Finset.prod_range_zero, _root_.mul_one, pow_zero]
  | succ n ih =>
    have e := add_val (n • g) g χ hJ
    rw [nsmul_b] at e
    rw [succ_nsmul, Finset.prod_range_succ, pow_succ, ← ih, ← _root_.mul_assoc, mul_right_comm, e]
    ac_rfl

end GlobalTheory.Poinc.Sep.Frames

namespace GlobalTheory.Poinc.Sep.Frames

open GlobalTheory.UT.CoefBasic GlobalTheory.TorusExt

variable {V : Type} [CommRing V] [IsDomain V] {D : DegPre V}

attribute [local instance] GlobalTheory.TorusExt.gtGroup

/- English proof (translation)
Take `⟨x, hx⟩` from `exists_ratio_gen (φ := ![(D.c χ * b).left, (D.c χ).left, b.left, (η[D.P.A]).left]) (φF := DegPre.gtφ D (FractionRing V) g.b χ) (fun k => by fin_cases k`. Use `show (padd D.P.A (DegPre.cF D (FractionRing V) χ) g.b).left = _`. Rewrite using `[hgb]`. Use `show _ = (toUnit (TF (R := V) (FractionRing V)) ≫ (D.c χ * b)).left`. Conclude with `congrArg (fun q : TF (R := V) (FractionRing V) ⟶ D.P.A => q.left) (MonObj.comp_mul (toUnit (TF (R := V) (FractionRing V))) (D.c χ) b).symm`.

Both sides reduce to the same expression. Use `show g.b.left = _`. Rewrite using `[hgb]`. Both sides reduce to the same expression. Use the proof step `rfl) (g.s χ) (g.isGen χ) t ht`.

Establish `G` using `(grep_cubProd (D.c χ) b N).mul ((SymFrame.grep_gen t ht (𝟙 _)).pow N).inv`. Take `⟨u, hu⟩` from `exists_unit_of_triv G (fun U _ h => by`. Establish `hK : ∏ k : Fin 4, h (𝟙 _ ≫ ![(D.c χ * b).left, (D.c χ).left, b.left, (η[D.P.A]).left] k) ^ DegPre.gtε k = (h (D.c χ * b).left)⁻¹ * h (D.c χ).left * h b.left * (h (1 : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ D.P.A).left)⁻¹`. Rewrite using `[Fin.prod_univ_four, ← SymFrame.eta_eq]`. Simplify using `[DegPre.gtε, zpow_neg, zpow_one]`.

Establish `hP : ∀ i, h (D.c χ * b ^ i * b).left * (h (D.c χ * b ^ i).left)⁻¹ * (h (D.c χ * b).left)⁻¹ * (h (b ^ i * b).left)⁻¹ * h (D.c χ).left * h (b ^ i).left * h b.left * (h (1 : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ D.P.A).left)⁻¹ = (h (D.c χ * b ^ (i + 1)).left / h (b ^ (i + 1)).left) …`. Introduce `i`. Rewrite using `[_root_.mul_assoc (D.c χ), ← pow_succ]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_div]`.

Normalize the expressions using the abelian group laws. Rewrite using `[Finset.prod_congr rfl (fun i _ => hP i), Finset.prod_mul_distrib, Finset.prod_range_div (fun i => h (D.c χ * b ^ i).left / h (b ^ i).left), Finset.prod_const, Finset.card_range, hK, hbN, pow_zero]`. Use the proof step `simp)`. Establish `key : ∀ z J, Good D.P.L z J → x ^ N = algebraMap V (FractionRing V) u` using `fun z J hJ => by`. Establish `c` using `hu z J hJ`.

Establish `d` using `charVal_nsmul g χ hJ N`. Rewrite `d` using `[hgN, zero_val χ hJ, _root_.one_mul]`. Establish `e : ∏ i ∈ Finset.range N, th D z J (cP D _ χ) (g.b ^ i) g.b = ∏ i ∈ Finset.range N, cubV D.cub z J (toUnit _ ≫ D.c χ) (toUnit _ ≫ b ^ i) (toUnit (TF (R` using `V) (FractionRing V)) ≫ b) := by`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hgb, ← MonObj.comp_pow]`.

Both sides reduce to the same expression. Rewrite `d` using `[e]`. Simplify using `only [Category.comp_id] at c`. Rewrite `c` using `[d]`. Simplify using `only [charVal] at c`.

Rewrite `c` using `[Units.val_mul, Units.val_pow_eq_pow_val, hx z J hJ, mul_pow, ← Units.val_pow_eq_pow_val, _root_.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, _root_.mul_one, cst_eq, cst_eq, ← map_pow]`. Conclude with `cstH_inj z c`. Take `⟨z⟩` from `exists_pt (R := V) (F := FractionRing V)`. Take `⟨J, hJ⟩` from `exists_good' D.P.isLB z`. Take `⟨u', hu'⟩` from `exists_unit_of_pow hN (key z J hJ)`.

Conclude with `⟨u', fun z J hJ => by rw [hx z J hJ, hu']⟩`.
-/
theorem char_unit_core [IsIntegrallyClosed V] {N : ℕ} (hN : 1 ≤ N)
    (b : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ D.P.A) (hbN : b ^ N = 1)
    (g : GtPtF D (FractionRing V)) (hgb : g.b = toUnit _ ≫ b) (hgN : N • g = 0) (χ : D.X)
    (t : LB.Gen (LB.LinComb D.P.L ![(D.c χ * b).left, (D.c χ).left, b.left, (η[D.P.A]).left] DegPre.gtε))
    (ht : t.IsGen) :
    ∃ u : Vˣ, ∀ z J, Good D.P.L z J → (val (g.s χ) (𝟙 _) z J).val =
      cst (FractionRing V) z (algebraMap V (FractionRing V) u) *
        (val t (toUnit (TF (R := V) (FractionRing V))).left z J).val := by
  obtain ⟨x, hx⟩ := exists_ratio_gen (φ := ![(D.c χ * b).left, (D.c χ).left, b.left, (η[D.P.A]).left])
    (φF := DegPre.gtφ D (FractionRing V) g.b χ) (fun k => by
      fin_cases k
      · show (padd D.P.A (DegPre.cF D (FractionRing V) χ) g.b).left = _
        rw [hgb]
        show _ = (toUnit (TF (R := V) (FractionRing V)) ≫ (D.c χ * b)).left
        exact congrArg (fun q : TF (R := V) (FractionRing V) ⟶ D.P.A => q.left)
          (MonObj.comp_mul (toUnit (TF (R := V) (FractionRing V))) (D.c χ) b).symm
      · rfl
      · show g.b.left = _
        rw [hgb]; rfl
      · rfl) (g.s χ) (g.isGen χ) t ht
  have G := (grep_cubProd (D.c χ) b N).mul ((SymFrame.grep_gen t ht (𝟙 _)).pow N).inv
  obtain ⟨u, hu⟩ := exists_unit_of_triv G (fun U _ h => by
    have hK : ∏ k : Fin 4, h (𝟙 _ ≫ ![(D.c χ * b).left, (D.c χ).left, b.left, (η[D.P.A]).left] k) ^ DegPre.gtε k =
        (h (D.c χ * b).left)⁻¹ * h (D.c χ).left * h b.left *
          (h (1 : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ D.P.A).left)⁻¹ := by
      rw [Fin.prod_univ_four, ← SymFrame.eta_eq]
      simp [DegPre.gtε, zpow_neg, zpow_one]
    have hP : ∀ i, h (D.c χ * b ^ i * b).left * (h (D.c χ * b ^ i).left)⁻¹ * (h (D.c χ * b).left)⁻¹ *
        (h (b ^ i * b).left)⁻¹ * h (D.c χ).left * h (b ^ i).left * h b.left *
        (h (1 : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ D.P.A).left)⁻¹ =
        (h (D.c χ * b ^ (i + 1)).left / h (b ^ (i + 1)).left) / (h (D.c χ * b ^ i).left / h (b ^ i).left) *
          ((h (D.c χ * b).left)⁻¹ * h (D.c χ).left * h b.left *
            (h (1 : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ D.P.A).left)⁻¹) := by
      intro i
      rw [_root_.mul_assoc (D.c χ), ← pow_succ]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_div]
      abel
    rw [Finset.prod_congr rfl (fun i _ => hP i), Finset.prod_mul_distrib,
      Finset.prod_range_div (fun i => h (D.c χ * b ^ i).left / h (b ^ i).left), Finset.prod_const, Finset.card_range, hK,
      hbN, pow_zero]
    simp)
  have key : ∀ z J, Good D.P.L z J → x ^ N = algebraMap V (FractionRing V) u := fun z J hJ => by
    have c := hu z J hJ
    have d := charVal_nsmul g χ hJ N
    rw [hgN, zero_val χ hJ, _root_.one_mul] at d
    have e : ∏ i ∈ Finset.range N, th D z J (cP D _ χ) (g.b ^ i) g.b = ∏ i ∈ Finset.range N,
        cubV D.cub z J (toUnit _ ≫ D.c χ) (toUnit _ ≫ b ^ i) (toUnit (TF (R := V) (FractionRing V)) ≫ b) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hgb, ← MonObj.comp_pow]; rfl
    rw [e] at d
    simp only [Category.comp_id] at c
    rw [d] at c
    dsimp only [charVal] at c
    rw [Units.val_mul, Units.val_pow_eq_pow_val, hx z J hJ, mul_pow, ← Units.val_pow_eq_pow_val, _root_.mul_assoc,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, _root_.mul_one, cst_eq, cst_eq, ← map_pow] at c
    exact cstH_inj z c
  obtain ⟨z⟩ := exists_pt (R := V) (F := FractionRing V)
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB z
  obtain ⟨u', hu'⟩ := exists_unit_of_pow hN (key z J hJ)
  exact ⟨u', fun z J hJ => by rw [hx z J hJ, hu']⟩

end GlobalTheory.Poinc.Sep.Frames

namespace GlobalTheory.Poinc.Sep.Frames

open GlobalTheory.UT.CoefBasic GlobalTheory.TorusExt

variable {V : Type} [CommRing V] [IsDomain V] {D : DegPre V}

/- English proof (translation)
Use `letI := GlobalTheory.TorusExt.gtGroup D (FractionRing V)`. Take `⟨o, h₁, h₂⟩` from `ho`. Establish `e : N • g = 0` using `((isNsmul_iff_eq N g o).1 h₁).symm.trans ((isZero_iff_eq o).1 h₂)`. Use `⟨e, pow_eq_one_of_generic b N ?_⟩` and prove the remaining obligations. Rewrite using `[← hgb, ← nsmul_b, e, zero_b]`.
-/
theorem torsion_of_nsmul {N : ℕ} (g : GtPtF D (FractionRing V)) (b : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ D.P.A)
    (hgb : g.b = toUnit _ ≫ b) (ho : ∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero) :
    (letI := GlobalTheory.TorusExt.gtGroup D (FractionRing V); N • g = 0) ∧ b ^ N = 1 := by
  letI := GlobalTheory.TorusExt.gtGroup D (FractionRing V)
  obtain ⟨o, h₁, h₂⟩ := ho
  have e : N • g = 0 := ((isNsmul_iff_eq N g o).1 h₁).symm.trans ((isZero_iff_eq o).1 h₂)
  refine ⟨e, pow_eq_one_of_generic b N ?_⟩
  rw [← hgb, ← nsmul_b, e, zero_b]

/- English proof (translation)
Take `⟨u, hu⟩` from `frame_unit_core hN b (torsion_of_nsmul g b hgb ho).2 hgb w hw.1 hw.2 t ht`. Use `⟨u, hu, fun κ hκ z J hJ => ?_⟩` and prove the remaining obligations. Establish `a` using `congrArg Units.val (hw.2 κ hκ z J hJ)`. Rewrite `a` using `[Units.val_mul, Units.val_pow_eq_pow_val, hu z J hJ, mul_pow, Units.val_one]`. Rewrite using `[Units.val_mul, Units.val_pow_eq_pow_val]`.

Take the linear combination `a`.
-/
theorem frame_unit [IsNoetherianRing V] [IsIntegrallyClosed V] {N : ℕ} (hN : 1 ≤ N)
    (g : GtPtF D (FractionRing V)) (b : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ D.P.A)
    (hgb : g.b = toUnit _ ≫ b) (ho : ∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero)
    (w : Frm D (FractionRing V) 1 g.b)
    (hw : w.IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1), Normd κ → ∀ z J, Good D.P.L z J →
      val w (𝟙 _) z J ^ (N ^ 2) * val κ g.b.left z J = 1)
    (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))) (ht : t.IsGen) :
    ∃ u : Vˣ, (∀ z J, Good D.P.L z J → (val w (𝟙 _) z J).val =
      cst (FractionRing V) z (algebraMap V (FractionRing V) u) *
        (val t (toUnit (TF (R := V) (FractionRing V))).left z J).val) ∧
      ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1), Normd κ → ∀ z J, Good D.P.L z J →
        cst (FractionRing V) z (algebraMap V (FractionRing V) u) ^ (N ^ 2) *
          (val κ g.b.left z J * val t (toUnit (TF (R := V) (FractionRing V))).left z J ^ (N ^ 2)).val = 1 := by
  obtain ⟨u, hu⟩ := frame_unit_core hN b (torsion_of_nsmul g b hgb ho).2 hgb w hw.1 hw.2 t ht
  refine ⟨u, hu, fun κ hκ z J hJ => ?_⟩
  have a := congrArg Units.val (hw.2 κ hκ z J hJ)
  rw [Units.val_mul, Units.val_pow_eq_pow_val, hu z J hJ, mul_pow, Units.val_one] at a
  rw [Units.val_mul, Units.val_pow_eq_pow_val]
  linear_combination a

attribute [local instance] GlobalTheory.TorusExt.gtGroup

/- English proof (translation)
Take `⟨hgN, hbN⟩` from `torsion_of_nsmul g b hgb ho`. Take `⟨u, hu⟩` from `char_unit_core hN b hbN g hgb hgN χ t ht`. Use `⟨u, hu, fun z J hJ => ?_⟩` and prove the remaining obligations. Establish `d` using `charVal_nsmul g χ hJ N`. Rewrite `d` using `[hgN, zero_val χ hJ, _root_.one_mul]`.

Establish `e : ∏ i ∈ Finset.range N, th D z J (cP D _ χ) (g.b ^ i) g.b = ∏ i ∈ Finset.range N, cubV D.cub z J (toUnit _ ≫ D.c χ) (toUnit _ ≫ b ^ i) (toUnit (TF (R` using `V) (FractionRing V)) ≫ b) := by`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hgb, ← MonObj.comp_pow]`. Both sides reduce to the same expression. Rewrite using `[← e, d]`.

Simplify using `only [charVal]`. Rewrite using `[Units.val_pow_eq_pow_val, hu z J hJ, mul_pow, Units.val_pow_eq_pow_val]`.
-/
theorem char_unit [IsIntegrallyClosed V] {N : ℕ} (hN : 1 ≤ N)
    (g : GtPtF D (FractionRing V)) (b : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ D.P.A)
    (hgb : g.b = toUnit _ ≫ b) (ho : ∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero) (χ : D.X)
    (t : LB.Gen (LB.LinComb D.P.L ![(D.c χ * b).left, (D.c χ).left, b.left, (η[D.P.A]).left] DegPre.gtε))
    (ht : t.IsGen) :
    ∃ u : Vˣ, (∀ z J, Good D.P.L z J → (val (g.s χ) (𝟙 _) z J).val =
      cst (FractionRing V) z (algebraMap V (FractionRing V) u) *
        (val t (toUnit (TF (R := V) (FractionRing V))).left z J).val) ∧
      ∀ z J, Good D.P.L z J → (∏ i ∈ Finset.range N, cubV D.cub z J (toUnit _ ≫ D.c χ) (toUnit _ ≫ b ^ i)
          (toUnit (TF (R := V) (FractionRing V)) ≫ b)).val =
        cst (FractionRing V) z (algebraMap V (FractionRing V) u) ^ N *
          (val t (toUnit (TF (R := V) (FractionRing V))).left z J ^ N).val := by
  obtain ⟨hgN, hbN⟩ := torsion_of_nsmul g b hgb ho
  obtain ⟨u, hu⟩ := char_unit_core hN b hbN g hgb hgN χ t ht
  refine ⟨u, hu, fun z J hJ => ?_⟩
  have d := charVal_nsmul g χ hJ N
  rw [hgN, zero_val χ hJ, _root_.one_mul] at d
  have e : ∏ i ∈ Finset.range N, th D z J (cP D _ χ) (g.b ^ i) g.b = ∏ i ∈ Finset.range N,
      cubV D.cub z J (toUnit _ ≫ D.c χ) (toUnit _ ≫ b ^ i) (toUnit (TF (R := V) (FractionRing V)) ≫ b) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hgb, ← MonObj.comp_pow]; rfl
  rw [← e, d]
  dsimp only [charVal]
  rw [Units.val_pow_eq_pow_val, hu z J hJ, mul_pow, Units.val_pow_eq_pow_val]

end GlobalTheory.Poinc.Sep.Frames

namespace GlobalTheory.Poinc.Sep.Frames

variable {V : Type} [CommRing V] [IsDomain V]

/- English proof (translation)
Take `⟨th, g, b, w, h₁, h₂, h₃, h₄, h₅, h₆⟩` from `hT`. Conclude with `⟨th, g, b, w, h₁, h₂, h₃, h₄, h₅, h₆, fun c => (torsion_of_nsmul (g c) (b c) (h₁ c) (h₂ c)).2, fun c t ht => (frame_unit hN (g c) (b c) (h₁ c) (h₂ c) (w c) (h₄ c) t ht).imp fun _ h => h.1, fun c χ t ht => (char_unit hN (g c) (b c) (h₁ c) (h₂ c) χ t ht).imp fun _ h => h.1⟩`.
-/
theorem thetaTerms_integral [IsNoetherianRing V] [IsIntegrallyClosed V] (D : DegPre V) {N₁ : ℕ} (hN : 1 ≤ N₁)
    {X C : Type} [AddCommGroup X] (e : X ≃+ D.X) (T : X → C → V) (hT : IsThetaTerms D N₁ e T) :
    ∃ (th : Fam D (FractionRing V) 1) (g : C → GtPtF D (FractionRing V)) (b : C → (𝟙_ (Over (Sp V)) ⟶ D.P.A))
      (w : ∀ c, Frm D (FractionRing V) 1 (g c).b),
      (∀ c, (g c).b = toUnit _ ≫ b c) ∧ (∀ c, ∃ o, GtPtF.IsNsmul N₁ (g c) o ∧ o.IsZero) ∧
      (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp V) (p : Over.mk x ⟶ D.P.A), p ^ N₁ = 1 →
        ∃ c, p = toUnit _ ≫ b c) ∧
      (∀ c, (w c).IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N₁) (N₁ ^ 2) 1), Normd κ → ∀ z J, Good D.P.L z J →
        val (w c) (𝟙 _) z J ^ (N₁ ^ 2) * val κ (g c).b.left z J = 1) ∧
      (∀ mu c, IsCoef 1 (g c) (w c) (e mu) (th.s (e mu)) (algebraMap V (FractionRing V) (T mu c))) ∧
      (∃ c, T 0 c = 1) ∧
      (∀ c, b c ^ N₁ = 1) ∧
      (∀ c (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1))), t.IsGen →
        ∃ u : Vˣ, ∀ z J, Good D.P.L z J → (val (w c) (𝟙 _) z J).val =
          cst (FractionRing V) z (algebraMap V (FractionRing V) u) *
            (val t (toUnit (TF (R := V) (FractionRing V))).left z J).val) ∧
      (∀ c (χ : D.X) (t : LB.Gen (LB.LinComb D.P.L
          ![(D.c χ * b c).left, (D.c χ).left, (b c).left, (η[D.P.A]).left] DegPre.gtε)), t.IsGen →
        ∃ u : Vˣ, ∀ z J, Good D.P.L z J → (val ((g c).s χ) (𝟙 _) z J).val =
          cst (FractionRing V) z (algebraMap V (FractionRing V) u) *
            (val t (toUnit (TF (R := V) (FractionRing V))).left z J).val) := by
  obtain ⟨th, g, b, w, h₁, h₂, h₃, h₄, h₅, h₆⟩ := hT
  exact ⟨th, g, b, w, h₁, h₂, h₃, h₄, h₅, h₆, fun c => (torsion_of_nsmul (g c) (b c) (h₁ c) (h₂ c)).2,
    fun c t ht => (frame_unit hN (g c) (b c) (h₁ c) (h₂ c) (w c) (h₄ c) t ht).imp fun _ h => h.1,
    fun c χ t ht => (char_unit hN (g c) (b c) (h₁ c) (h₂ c) χ t ht).imp fun _ h => h.1⟩

end GlobalTheory.Poinc.Sep.Frames

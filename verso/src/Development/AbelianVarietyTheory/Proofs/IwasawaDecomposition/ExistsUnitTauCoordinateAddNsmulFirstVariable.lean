import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiCoordinateEqUnitMulTauCoordinate
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TauShift

open GlobalTheory.PsiTauCoordRel GlobalTheory.PeriodBalance GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

variable {R : Type} [CommRing R] [IsDomain R]

abbrev cK (ξ : Spec (CommRingCat.of (FractionRing R))) : Rˣ →* ((TK R).left.presheaf.stalk ξ)ˣ :=
  Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom

abbrev kK (ξ : Spec (CommRingCat.of (FractionRing R))) : (FractionRing R)ˣ →* ((TK R).left.presheaf.stalk ξ)ˣ :=
  Units.map (kst ξ).toMonoidHom

variable [IsLocalRing R]

/- English proof (translation)
Set `cU : Rˣ →* ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ` to `Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom`. Choose the witnesses or unpack the hypotheses as in `⟨c5, h5⟩ : ∃ w : Rˣ, val D.rigK (𝟙 (TK R).left) ξ J = cU w := by`. Unfold `DegPre.rigK`. Rewrite using `[val_pull hJ]`. Establish `: 𝟙 _ ≫ (toUnit (TK R)).left = jK R ≫ 𝟙 _` using `by rw [toUnit_left]; simp`.

Rewrite using `[this]`. Conclude with `val_int ξ hJc D.rig (𝟙 _) fun _ => by rw [Category.id_comp]; exact Over.w η[D.P.A]`. Take `⟨j, h, i1, i2, i3, i4, rfl⟩` from `hx`. Establish `hm` using `h (show ξ ∈ (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens) from trivial)`. Establish `eT` using `gm_genVal ξ (D.tau a b) j h`.

Establish `dT : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.tau a b).s j) = _` using `gm_mulGen _ _ ξ j hm`. Rewrite `dT` using `[gm_mulGen _ _ ξ _ (mem_inl hm), gm_mulGen _ _ ξ _ (mem_inl (mem_inl hm)), gm_invGen, gm_invGen, gm_invGen]`. Take `⟨c1, g1⟩` from `val_psi_chart D ξ hJ hJc (a + b) _ i1 (mem_inl (mem_inl (mem_inl hm)))`. Take `⟨c2, g2⟩` from `val_psi_chart D ξ hJ hJc a _ i2 (mem_inr (mem_inl (mem_inl hm)))`. Take `⟨c3, g3⟩` from `val_psi_chart D ξ hJ hJc b _ i3 (mem_inr (mem_inl hm))`.

Take `⟨c4, g4⟩` from `gm_rigK D ξ _ i4 (mem_inr hm)`. Establish `vt` using `GlobalTheory.PeriodBalance.val_tau D ξ hJ a b`. Establish `eT' : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.tau a b).s j) = Units.map (kst ξ).toMonoidHom (genVal (D.tau a b) j h)` using `Units.ext eT`. Use `⟨c1⁻¹ * c2 * c3 * c4⁻¹ * c5, ?_⟩` and prove the remaining obligations. Rewrite using `[← eT', dT, g4, vt, g1, g2, g3, h5]`.

Simplify using `only [cU, map_mul, map_inv]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws.
-/
theorem coord_val (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) {a b : D.X} {x : (FractionRing R)ˣ} (hx : IsTauCoord D a b x) :
    ∃ u : Rˣ, Units.map (kst ξ).toMonoidHom x =
      cK ξ u * val (D.tau a b) (𝟙 (TK R).left) ξ J := by
  let cU : Rˣ →* ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom
  obtain ⟨c5, h5⟩ : ∃ w : Rˣ, val D.rigK (𝟙 (TK R).left) ξ J = cU w := by
    unfold DegPre.rigK
    rw [val_pull hJ]
    have : 𝟙 _ ≫ (toUnit (TK R)).left = jK R ≫ 𝟙 _ := by rw [toUnit_left]; simp
    rw [this]
    exact val_int ξ hJc D.rig (𝟙 _) fun _ => by rw [Category.id_comp]; exact Over.w η[D.P.A]
  obtain ⟨j, h, i1, i2, i3, i4, rfl⟩ := hx
  have hm := h (show ξ ∈ (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens) from trivial)
  have eT := gm_genVal ξ (D.tau a b) j h
  have dT : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.tau a b).s j) = _ := gm_mulGen _ _ ξ j hm
  rw [gm_mulGen _ _ ξ _ (mem_inl hm), gm_mulGen _ _ ξ _ (mem_inl (mem_inl hm)), gm_invGen, gm_invGen,
    gm_invGen] at dT
  obtain ⟨c1, g1⟩ := val_psi_chart D ξ hJ hJc (a + b) _ i1 (mem_inl (mem_inl (mem_inl hm)))
  obtain ⟨c2, g2⟩ := val_psi_chart D ξ hJ hJc a _ i2 (mem_inr (mem_inl (mem_inl hm)))
  obtain ⟨c3, g3⟩ := val_psi_chart D ξ hJ hJc b _ i3 (mem_inr (mem_inl hm))
  obtain ⟨c4, g4⟩ := gm_rigK D ξ _ i4 (mem_inr hm)
  have vt := GlobalTheory.PeriodBalance.val_tau D ξ hJ a b
  have eT' : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.tau a b).s j) =
      Units.map (kst ξ).toMonoidHom (genVal (D.tau a b) j h) := Units.ext eT
  refine ⟨c1⁻¹ * c2 * c3 * c4⁻¹ * c5, ?_⟩
  rw [← eT', dT, g4, vt, g1, g2, g3, h5]
  simp only [cU, map_mul, map_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/- English proof (translation)
Establish `e` using `(val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB a a' b) (𝟙 (TK R).left)).trans (val_mul hJ _ _ _))`. Rewrite `e` using `[val_pull (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) hJ D.cub.t (D.pt3 a a' b)]`. Establish `hp : 𝟙 (TK R).left ≫ D.pt3 a a' b = jK R ≫ (lift (D.c a) (lift (D.c a') (D.c b))).left`. Simplify using `[DegPre.pt3, ← CartesianMonoidalCategory.comp_lift]`. Rewrite `e` using `[hp]`.

Take `⟨w, hw⟩` from `val_int (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) ξ hJc D.cub.t (lift (D.c a) (lift (D.c a') (D.c b))).left fun k => by show ((lift (D.c a) (lift (D.c a') (D.c b))).left ≫ (psum D.P.A (x3 D.P.A) k.down).left) ≫ D.P.A.hom = 𝟙 _`. Rewrite using `[Category.assoc, Over.w, Over.w]`. Both sides reduce to the same expression. Use `⟨w⁻¹, ?_⟩` and prove the remaining obligations. Establish `hw' : val D.cub.t (jK R ≫ (lift (D.c a) (lift (D.c a') (D.c b))).left) ξ J = cK ξ w` using `hw`.

Rewrite using `[← e, map_inv, eq_inv_mul_iff_mul_eq, mul_comm]`. Conclude with `congrArg _ hw'.symm`.
-/
theorem val_add (D : DegPre R) (hB : D.TauBimult) (ξ : Spec (CommRingCat.of (FractionRing R))) {J}
    (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (a a' b : D.X) :
    ∃ w : Rˣ, val (D.tau (a + a') b) (𝟙 (TK R).left) ξ J = cK ξ w *
      (val (D.tau a b) (𝟙 (TK R).left) ξ J * val (D.tau a' b) (𝟙 (TK R).left) ξ J) := by
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB a a' b) (𝟙 (TK R).left)).trans (val_mul hJ _ _ _))
  rw [val_pull (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) hJ D.cub.t (D.pt3 a a' b)] at e
  have hp : 𝟙 (TK R).left ≫ D.pt3 a a' b = jK R ≫ (lift (D.c a) (lift (D.c a') (D.c b))).left := by
    simp [DegPre.pt3, ← CartesianMonoidalCategory.comp_lift]
  rw [hp] at e
  obtain ⟨w, hw⟩ := val_int (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) ξ hJc D.cub.t (lift (D.c a) (lift (D.c a') (D.c b))).left fun k => by
    show ((lift (D.c a) (lift (D.c a') (D.c b))).left ≫ (psum D.P.A (x3 D.P.A) k.down).left) ≫ D.P.A.hom = 𝟙 _
    rw [Category.assoc, Over.w, Over.w]; rfl
  refine ⟨w⁻¹, ?_⟩
  have hw' : val D.cub.t (jK R ≫ (lift (D.c a) (lift (D.c a') (D.c b))).left) ξ J = cK ξ w := hw
  rw [← e, map_inv, eq_inv_mul_iff_mul_eq, mul_comm]
  exact congrArg _ hw'.symm

/- English proof (translation)
Introduce `R _ _ _ D hB a z b k x x' x'' hx hx' hx''`. Use `haveI : IsProper D.P.A.hom := D.P.isAb.proper`. Take `⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R)))` from `⟨⟨⊥, Ideal.isPrime_bot⟩⟩`. Take `⟨J, hJ, hJc⟩` from `exists_good_integral ξ D.P.isLB D.P.A.hom`. Establish `hind : ∀ n : ℕ, ∃ w : Rˣ, val (D.tau (a + n • z) b) (𝟙 (TK R).left) ξ J = cK ξ w * (val (D.tau a b) (𝟙 (TK R).left) ξ J * val (D.tau z b) (𝟙 (TK R).left) ξ J ^ n)`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact ⟨1, by rw [zero_nsmul, add_zero, map_one, pow_zero, _root_.one_mul, _root_.mul_one]⟩`. Consider the case `succ n ih`. Take `⟨w, hw⟩` from `ih`.

Take `⟨w', hw'⟩` from `val_add D hB ξ hJ hJc (a + n • z) z b`. Use `⟨w' * w, ?_⟩` and prove the remaining obligations. Rewrite using `[succ_nsmul, ← add_assoc, hw', hw, map_mul, pow_succ]`. The two sides agree by associativity and commutativity. Take `⟨w, hw⟩` from `hind k`.

Take `⟨u1, e1⟩` from `coord_val D ξ hJ hJc hx`. Take `⟨u2, e2⟩` from `coord_val D ξ hJ hJc hx'`. Take `⟨u3, e3⟩` from `coord_val D ξ hJ hJc hx''`. Use `⟨u3 * w * u1⁻¹ * (u2⁻¹) ^ k, ?_⟩` and prove the remaining obligations. Apply `Units.map_injective (f := (kst ξ).toMonoidHom) (kst_injective ξ)` to reduce the goal to its premises.

Use `show kK ξ x'' = kK ξ _`. Use `replace e1 : kK ξ x = _ := e1`. Use `replace e2 : kK ξ x' = _ := e2`. Use `replace e3 : kK ξ x'' = _ := e3`. Establish `hc : ∀ v : Rˣ, kK ξ (Units.map (algebraMap R (FractionRing R)).toMonoidHom v) = cK ξ v` using `fun v => Units.ext rfl`.

Establish `f1 : val (D.tau a b) (𝟙 (TK R).left) ξ J = cK ξ u1⁻¹ * kK ξ x`. Rewrite using `[e1, map_inv, inv_mul_cancel_left]`. Establish `f2 : val (D.tau z b) (𝟙 (TK R).left) ξ J = cK ξ u2⁻¹ * kK ξ x'`. Rewrite using `[e2, map_inv, inv_mul_cancel_left]`. Rewrite using `[map_mul, hc, map_mul, map_pow, e3, hw, f1, f2]`.

Simplify using `only [map_mul, map_inv, map_pow, mul_pow]`. The two sides agree by associativity and commutativity.
-/
theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), D.TauBimult →
    ∀ (a z b : D.X) (k : ℕ) (x x' x'' : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D a b x →
      GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D z b x' → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D (a + k • z) b x'' →
      ∃ u : Rˣ, x'' = Units.map (algebraMap R (FractionRing R)).toMonoidHom u * (x * x' ^ k) := by
  intro R _ _ _ D hB a z b k x x' x'' hx hx' hx''
  haveI : IsProper D.P.A.hom := D.P.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J, hJ, hJc⟩ := exists_good_integral ξ D.P.isLB D.P.A.hom
  have hind : ∀ n : ℕ, ∃ w : Rˣ, val (D.tau (a + n • z) b) (𝟙 (TK R).left) ξ J =
      cK ξ w * (val (D.tau a b) (𝟙 (TK R).left) ξ J * val (D.tau z b) (𝟙 (TK R).left) ξ J ^ n) := by
    intro n
    induction n with
    | zero => exact ⟨1, by rw [zero_nsmul, add_zero, map_one, pow_zero, _root_.one_mul, _root_.mul_one]⟩
    | succ n ih =>
      obtain ⟨w, hw⟩ := ih
      obtain ⟨w', hw'⟩ := val_add D hB ξ hJ hJc (a + n • z) z b
      refine ⟨w' * w, ?_⟩
      rw [succ_nsmul, ← add_assoc, hw', hw, map_mul, pow_succ]
      ac_rfl
  obtain ⟨w, hw⟩ := hind k
  obtain ⟨u1, e1⟩ := coord_val D ξ hJ hJc hx
  obtain ⟨u2, e2⟩ := coord_val D ξ hJ hJc hx'
  obtain ⟨u3, e3⟩ := coord_val D ξ hJ hJc hx''
  refine ⟨u3 * w * u1⁻¹ * (u2⁻¹) ^ k, ?_⟩
  apply Units.map_injective (f := (kst ξ).toMonoidHom) (kst_injective ξ)
  show kK ξ x'' = kK ξ _
  replace e1 : kK ξ x = _ := e1
  replace e2 : kK ξ x' = _ := e2
  replace e3 : kK ξ x'' = _ := e3
  have hc : ∀ v : Rˣ, kK ξ (Units.map (algebraMap R (FractionRing R)).toMonoidHom v) =
      cK ξ v := fun v => Units.ext rfl
  have f1 : val (D.tau a b) (𝟙 (TK R).left) ξ J = cK ξ u1⁻¹ * kK ξ x := by
    rw [e1, map_inv, inv_mul_cancel_left]
  have f2 : val (D.tau z b) (𝟙 (TK R).left) ξ J = cK ξ u2⁻¹ * kK ξ x' := by
    rw [e2, map_inv, inv_mul_cancel_left]
  rw [map_mul, hc, map_mul, map_pow, e3, hw, f1, f2]
  simp only [map_mul, map_inv, map_pow, mul_pow]
  ac_rfl

end GlobalTheory.TauShift

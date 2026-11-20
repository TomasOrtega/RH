import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HRedFst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionValueZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.IntEval
open GlobalTheory.UT.CoefBasic GlobalTheory.ExpansionValueZero GlobalTheory.BoxExpansion

/- English proof (translation)
Introduce `R _ _ D g g' hP t l hl k wk hwk hl' s n c fs hs a ha α`. Establish `hτ : (toUnit (TF (R` using `R) (FractionRing R))).left = jFK (R := R) (FractionRing R) ≫ jK R := by`. Use `Over.w (toUnit (TF (R := R) (FractionRing R)))` as an intermediate fact. Simplify using `using this`. Establish `hb : g'.b.left = (toUnit (TF (R` using `R) (FractionRing R))).left ≫ g.b.left := hP.1`.

Establish `hlk : (l ^ k) ≠ 0` using `pow_ne_zero _ hl`. It suffices to establish `key : IsCoef k g' wk α (s.s α) ((l ^ k)⁻¹ * ∑ i, c i * algebraMap R (FractionRing R) (a i α)) by`. Rewrite using `[coef_eq key, ← _root_.mul_assoc, mul_inv_cancel₀ hlk, _root_.one_mul]`. Introduce `z J hJ`. Establish `e₂ : (lift (𝟙 (TF (R` using `R) (FractionRing R))) g'.b).left ≫ (DegPre.prB D (FractionRing R)).left = (toUnit (TF (R := R) (FractionRing R))).left ≫ g.b.left := by`.

Rewrite using `[← Over.comp_left]`. Use `erw [lift_snd]`. Conclude with `hb`. Establish `e₃ : (lift (𝟙 (TF (R` using `R) (FractionRing R))) g'.b).left ≫ (fst (TF (R := R) (FractionRing R)) D.P.A).left = 𝟙 _ := by`. Rewrite using `[← Over.comp_left, lift_fst]`.

Both sides reduce to the same expression. Establish `v : val (g'.s α) (𝟙 _) z J = val (g.s α) (toUnit (TF (R` using `R) (FractionRing R))).left z J := by`. Rewrite using `[val_corr hJ (hP.2 α), val_pull hJ, Category.id_comp]`. Establish `bi : ∀ i, gs (lift (𝟙 (TF (R` using `R) (FractionRing R))) g'.b).left z ⊤ (scal (fst (TF (R := R) (FractionRing R)) D.P.A).left (c i)) = cstH z (c i) := fun i => ((gs_pull _ _ z ⊤ trivial _).trans (by rw [e₃]; rfl)).trans (cst_eq z _)`. Establish `hai : ∀ i, sval (fs i α) ((toUnit (TF (R` using `R) (FractionRing R))).left ≫ g.b.left) z J * (val (g.s α) (toUnit (TF (R := R) (FractionRing R))).left z J).val * (val t (toUnit (TF (R := R) (FractionRing R))).left z J ^ k).val = cstH z (algebraMap R (FractionRing R) (a i α)) * (val (L := D.P.L) D.rig (toUnit (TF (R := R) (Frac …`.

Rewrite using `[ha i α _ _ z J hJ]`. Use `congr 1`. Rewrite using `[hτ, GlobalTheory.UT.EvalZero.cst_base]`. Simplify using the standard rewrite rules. Establish `hr : rigV D (TF (R` using `R) (FractionRing R)).hom z J = val (L := D.P.L) D.rig (toUnit (TF (R := R) (FractionRing R))).left z J := by`.

Rewrite using `[hτ]`. Both sides reduce to the same expression. Establish `hw` using `hl' z J hJ`. Rewrite `hw`, the goal using `[cst_eq]`. Use `((IsUnit.mk0 _ hlk).map (cstH (R := R) z)).mul_left_cancel ?_` and prove the remaining obligations.

Rewrite using `[secLin_val (hs α) _ z hJ, e₂, v, hr]`. Simplify using `only [bi]`. Rewrite using `[← _root_.mul_assoc, ← map_mul, ← _root_.mul_assoc, mul_inv_cancel₀ hlk, _root_.one_mul, map_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h1` using `hai i`.

Establish `h2` using `hw`. Simplify using `only [Units.val_pow_eq_pow_val, map_mul] at h1 h2 ⊢`. Take the linear combination `(-(cstH (R := R) z (c i))) * h1 - cstH (R := R) z (c i) * sval (fs i α) ((toUnit (TF (R := R) (FractionRing R))).left ≫ g.b.left) z J * (val (g.s α) (toUnit (TF (R := R) (FractionRing R))).left z J).val * h2`.
-/
theorem coef_comb_pull : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (g : GtPt D (𝟙_ (Over (Sp R)))) (g' : GtPtF D (FractionRing R)), GtPt.IsPullF (FractionRing R) (toUnit (TF (R := R) (FractionRing R))).left g g' → ∀ (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, g.b.left] (DegPre.lineε 1))) (l : FractionRing R), l ≠ 0 → ∀ (k : ℕ) (wk : Frm D (FractionRing R) k g'.b), wk.IsGen → (∀ (z : (TF (R := R) (FractionRing R)).left) (J : ((TF (R := R) (FractionRing R)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → GlobalTheory.UT.cst (FractionRing R) z (l ^ k) * (val wk (𝟙 _) z J).val = (val t (toUnit (TF (R := R) (FractionRing R))).left z J ^ k).val) → ∀ (s : Fam D (FractionRing R) k) (n : ℕ) (c : Fin n → FractionRing R) (fs : Fin n → ∀ α : D.X, D.SecB k α), (∀ α : D.X, GeneratorPullback.SecLin D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (s.s α) (D.famφB α) (DegPre.famε k) (fun i => fs i α) (DegPre.prB D (FractionRing R)).left (fun i => scal (fst (TF (R := R) (FractionRing R)) D.P.A).left (c i))) → ∀ a : Fin n → D.X → R, (∀ (i : Fin n) (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → sval (fs i α) (r ≫ g.b.left) z J * (val (g.s α) r z J).val * (val t r z J ^ k).val = Geo.Tor.cst r z (a i α) * (val (L := D.P.L) D.rig r z J ^ k).val) → ∀ α : D.X, l ^ k * coef s g' wk α = ∑ i, c i * algebraMap R (FractionRing R) (a i α) := by
  intro R _ _ D g g' hP t l hl k wk hwk hl' s n c fs hs a ha α
  have hτ : (toUnit (TF (R := R) (FractionRing R))).left = jFK (R := R) (FractionRing R) ≫ jK R := by
    have := Over.w (toUnit (TF (R := R) (FractionRing R)))
    simpa using this
  have hb : g'.b.left = (toUnit (TF (R := R) (FractionRing R))).left ≫ g.b.left := hP.1
  have hlk : (l ^ k) ≠ 0 := pow_ne_zero _ hl
  suffices key : IsCoef k g' wk α (s.s α) ((l ^ k)⁻¹ * ∑ i, c i * algebraMap R (FractionRing R) (a i α)) by
    rw [coef_eq key, ← _root_.mul_assoc, mul_inv_cancel₀ hlk, _root_.one_mul]
  intro z J hJ
  have e₂ : (lift (𝟙 (TF (R := R) (FractionRing R))) g'.b).left ≫ (DegPre.prB D (FractionRing R)).left =
      (toUnit (TF (R := R) (FractionRing R))).left ≫ g.b.left := by
    rw [← Over.comp_left]
    erw [lift_snd]
    exact hb
  have e₃ : (lift (𝟙 (TF (R := R) (FractionRing R))) g'.b).left ≫ (fst (TF (R := R) (FractionRing R)) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have v : val (g'.s α) (𝟙 _) z J = val (g.s α) (toUnit (TF (R := R) (FractionRing R))).left z J := by
    rw [val_corr hJ (hP.2 α), val_pull hJ, Category.id_comp]
  have bi : ∀ i, gs (lift (𝟙 (TF (R := R) (FractionRing R))) g'.b).left z ⊤
      (scal (fst (TF (R := R) (FractionRing R)) D.P.A).left (c i)) = cstH z (c i) := fun i =>
    ((gs_pull _ _ z ⊤ trivial _).trans (by rw [e₃]; rfl)).trans (cst_eq z _)
  have hai : ∀ i, sval (fs i α) ((toUnit (TF (R := R) (FractionRing R))).left ≫ g.b.left) z J *
      (val (g.s α) (toUnit (TF (R := R) (FractionRing R))).left z J).val *
      (val t (toUnit (TF (R := R) (FractionRing R))).left z J ^ k).val =
      cstH z (algebraMap R (FractionRing R) (a i α)) *
        (val (L := D.P.L) D.rig (toUnit (TF (R := R) (FractionRing R))).left z J ^ k).val := fun i => by
    rw [ha i α _ _ z J hJ]
    congr 1
    rw [hτ, GlobalTheory.UT.EvalZero.cst_base]
    simp
  have hr : rigV D (TF (R := R) (FractionRing R)).hom z J =
      val (L := D.P.L) D.rig (toUnit (TF (R := R) (FractionRing R))).left z J := by
    rw [hτ]; rfl
  have hw := hl' z J hJ
  rw [cst_eq] at hw ⊢
  refine ((IsUnit.mk0 _ hlk).map (cstH (R := R) z)).mul_left_cancel ?_
  rw [secLin_val (hs α) _ z hJ, e₂, v, hr]
  simp only [bi]
  rw [← _root_.mul_assoc, ← map_mul, ← _root_.mul_assoc, mul_inv_cancel₀ hlk, _root_.one_mul, map_sum,
    Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := hai i
  have h2 := hw
  simp only [Units.val_pow_eq_pow_val, map_mul] at h1 h2 ⊢
  linear_combination (-(cstH (R := R) z (c i))) * h1 - cstH (R := R) z (c i) *
    sval (fs i α) ((toUnit (TF (R := R) (FractionRing R))).left ≫ g.b.left) z J *
    (val (g.s α) (toUnit (TF (R := R) (FractionRing R))).left z J).val * h2

end GlobalTheory.Poinc.IntEval

import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPow

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.LineNorm

namespace GlobalTheory.LineNorm.Add

/- English proof (translation)
Establish `cA {i : ((CechPic.tens A B).pull j).ι} : ((CechPic.tens A B).pull j).U i ≤ (A.pull j).U fun _ => (i PUnit.unit).1` using `fun _ hx => Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hx PUnit.unit).1`. Establish `cB {i : ((CechPic.tens A B).pull j).ι} : ((CechPic.tens A B).pull j).U i ≤ (B.pull j).U fun _ => (i PUnit.unit).2` using `fun _ hx => Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hx PUnit.unit).2`. Use `⟨LB.isLB_pull (CechPic.isLB_tens hA hB) j, fun i i' h => ?_, fun i x hx => (hr.isEqn _ x (cA hx)).add (hs.isEqn _ x (cB hx))⟩` and prove the remaining obligations. Establish `lA` using `inf_le_inf (cA (i := i)) (cA (i := i'))`. Establish `lB` using `inf_le_inf (cB (i := i)) (cB (i := i'))`.

Rewrite using `[Units.val_mul, Units.val_mul, hr.isRatSec _ _ (lA h), hs.isRatSec _ _ (lB h), mul_mul_mul_comm, ← fnOf_resG lA h, ← fnOf_resG lB h, ← map_mul, InducedPull.val_pull_g _ j i i' (InducedPull.inf_le _ j i i')]`. Use `congr 2`. Use `Eq.trans ?_ (map_mul _ _ _).symm` and prove the remaining obligations. Use `congrArg₂ (· * ·) ?_ ?_` and prove the remaining obligations. Use `(congrArg _ (InducedPull.val_pull_g A j _ _ (InducedPull.inf_le A j _ _))).trans ?_` and prove the remaining obligations.

Establish `e` using `(Scheme.Hom.appLE_map j (InducedPull.inf_le A j (fun _ => (i PUnit.unit).1) fun _ => (i' PUnit.unit).1) (homOfLE lA).op).trans (Scheme.Hom.map_appLE j (InducedPull.inf_le _ j i i') (homOfLE (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))).op).symm`. Conclude with `RingHom.congr_fun (congrArg CommRingCat.Hom.hom e) (A.g (i PUnit.unit).1 (i' PUnit.unit).1).val`. Use `(congrArg _ (InducedPull.val_pull_g B j _ _ (InducedPull.inf_le B j _ _))).trans ?_` and prove the remaining obligations. Establish `e` using `(Scheme.Hom.appLE_map j (InducedPull.inf_le B j (fun _ => (i PUnit.unit).2) fun _ => (i' PUnit.unit).2) (homOfLE lB).op).trans (Scheme.Hom.map_appLE j (InducedPull.inf_le _ j i i') (homOfLE (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))).op).symm`. Conclude with `RingHom.congr_fun (congrArg CommRingCat.Hom.hom e) (B.g (i PUnit.unit).2 (i' PUnit.unit).2).val`.
-/
theorem presents_tens {X Z : Scheme.{0}} [IsIntegral Z] {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (j : Z ⟶ X)
    {D E : CartierDiv Z} {r : (A.pull j).ι → Z.functionFieldˣ} {s : (B.pull j).ι → Z.functionFieldˣ}
    (hr : Presents D (A.pull j) r) (hs : Presents E (B.pull j) s) :
    Presents (D + E) ((CechPic.tens A B).pull j)
      fun i => r (fun _ => (i PUnit.unit).1) * s fun _ => (i PUnit.unit).2 := by
  have cA {i : ((CechPic.tens A B).pull j).ι} :
      ((CechPic.tens A B).pull j).U i ≤ (A.pull j).U fun _ => (i PUnit.unit).1 :=
    fun _ hx => Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hx PUnit.unit).1
  have cB {i : ((CechPic.tens A B).pull j).ι} :
      ((CechPic.tens A B).pull j).U i ≤ (B.pull j).U fun _ => (i PUnit.unit).2 :=
    fun _ hx => Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hx PUnit.unit).2
  refine ⟨LB.isLB_pull (CechPic.isLB_tens hA hB) j, fun i i' h => ?_,
    fun i x hx => (hr.isEqn _ x (cA hx)).add (hs.isEqn _ x (cB hx))⟩
  have lA := inf_le_inf (cA (i := i)) (cA (i := i'))
  have lB := inf_le_inf (cB (i := i)) (cB (i := i'))
  rw [Units.val_mul, Units.val_mul, hr.isRatSec _ _ (lA h), hs.isRatSec _ _ (lB h), mul_mul_mul_comm,
    ← fnOf_resG lA h, ← fnOf_resG lB h, ← map_mul,
    InducedPull.val_pull_g _ j i i' (InducedPull.inf_le _ j i i')]
  congr 2
  refine Eq.trans ?_ (map_mul _ _ _).symm
  refine congrArg₂ (· * ·) ?_ ?_
  · refine (congrArg _ (InducedPull.val_pull_g A j _ _ (InducedPull.inf_le A j _ _))).trans ?_
    have e := (Scheme.Hom.appLE_map j (InducedPull.inf_le A j (fun _ => (i PUnit.unit).1)
      fun _ => (i' PUnit.unit).1) (homOfLE lA).op).trans
      (Scheme.Hom.map_appLE j (InducedPull.inf_le _ j i i') (homOfLE (le_inf (inf_le_left.trans inf_le_left)
        (inf_le_right.trans inf_le_left))).op).symm
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom e) (A.g (i PUnit.unit).1 (i' PUnit.unit).1).val
  · refine (congrArg _ (InducedPull.val_pull_g B j _ _ (InducedPull.inf_le B j _ _))).trans ?_
    have e := (Scheme.Hom.appLE_map j (InducedPull.inf_le B j (fun _ => (i PUnit.unit).2)
      fun _ => (i' PUnit.unit).2) (homOfLE lB).op).trans
      (Scheme.Hom.map_appLE j (InducedPull.inf_le _ j i i') (homOfLE (le_inf (inf_le_left.trans inf_le_right)
        (inf_le_right.trans inf_le_right))).op).symm
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom e) (B.g (i PUnit.unit).2 (i' PUnit.unit).2).val

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def GivenBy (Δ : Y.Dv) (t : Y.X → Y.Fnˣ) (φ : PtFn Y) (M : GlobalTheory.TrueGeo.Model Y) (L : LB M.X) (m : ℕ) : Prop :=
  ∃ r : (L.pull M.j).ι → Y.Fnˣ, L.IsLB ∧ Presents (m • Δ) (L.pull M.j) r ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ M.X) (i : (L.pull M.j).ι),
      spMap e.O.subtype ≫ yt = y.1 ≫ M.j → ⊤ ≤ yt ⁻¹ᵁ L.U (i PUnit.unit) →
      (m : ℝ) * φ v e y = Real.log (e.w (valAt y.1 (((t (below y.1))⁻¹ ^ m * r i : Y.Fnˣ) : Y.Fn)))

variable {Δ Δ' : Y.Dv} {t t' : Y.X → Y.Fnˣ} {φ φ' : PtFn Y}

/- English proof (translation)
Take `⟨MX, Mp, Mar, Mj, Mpb⟩` from `M`. Simplify using `only at π hj L`. Substitute `hj` using the available equality. Take `⟨r, hL, hr, h⟩` from `h`. Use `⟨fun i => r fun _ => i PUnit.unit PUnit.unit, LB.isLB_pull hL π, InducedPull.presents_pull_pull hL π N.j hr, fun v e y yt i hy hi => ?_⟩` and prove the remaining obligations.

Conclude with `h v e y (yt ≫ π) (fun _ => i PUnit.unit PUnit.unit) ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ π) hy).trans (Category.assoc _ _ _))) fun x hx => Set.mem_iInter.1 (hi hx) PUnit.unit`.
-/
theorem GivenBy.pull {M N : GlobalTheory.TrueGeo.Model Y} {L : LB M.X} {m : ℕ} (h : GivenBy Δ t φ M L m) (π : N.X ⟶ M.X)
    (hj : N.j ≫ π = M.j) : GivenBy Δ t φ N (L.pull π) m := by
  obtain ⟨MX, Mp, Mar, Mj, Mpb⟩ := M
  dsimp only at π hj L
  subst hj
  obtain ⟨r, hL, hr, h⟩ := h
  refine ⟨fun i => r fun _ => i PUnit.unit PUnit.unit, LB.isLB_pull hL π,
    InducedPull.presents_pull_pull hL π N.j hr, fun v e y yt i hy hi => ?_⟩
  exact h v e y (yt ≫ π) (fun _ => i PUnit.unit PUnit.unit)
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ π) hy).trans (Category.assoc _ _ _)))
    fun x hx => Set.mem_iInter.1 (hi hx) PUnit.unit

/- English proof (translation)
Establish `h₂ : below y.1 ∈ (L.pull M.j).U i` using `OfModel.le_chart M L e y yt h hi trivial`. Use `((ht (below y.1)).nsmul m).iff_unitAt.1 (hr.isEqn _ _ h₂)` as an intermediate fact. Rewrite `this` using `[div_eq_inv_mul, ← Units.val_inv_eq_inv_val, ← Units.val_mul, ← inv_pow]`. Then use the resulting hypothesis.
-/
theorem unitAt_quot {M : GlobalTheory.TrueGeo.Model Y} {L : LB M.X} {m : ℕ} (ht : ∀ y, Δ.IsEqn y (t y))
    {r : (L.pull M.j).ι → Y.Fnˣ} (hr : Presents (m • Δ) (L.pull M.j) r)
    {v : HeightOneSpectrum (𝓞 F)} {e : Ext v} {y : AlgPt Y} {yt : Sp e.O ⟶ M.X} {i : (L.pull M.j).ι}
    (h : spMap e.O.subtype ≫ yt = y.1 ≫ M.j) (hi : ⊤ ≤ yt ⁻¹ᵁ L.U (i PUnit.unit)) :
    UnitAt (below y.1) (((t (below y.1))⁻¹ ^ m * r i : Y.Fnˣ) : Y.Fn) := by
  have h₂ : below y.1 ∈ (L.pull M.j).U i := OfModel.le_chart M L e y yt h hi trivial
  have := ((ht (below y.1)).nsmul m).iff_unitAt.1 (hr.isEqn _ _ h₂)
  rwa [div_eq_inv_mul, ← Units.val_inv_eq_inv_val, ← Units.val_mul, ← inv_pow] at this

/- English proof (translation)
Take `⟨r, hL, hr, h⟩` from `h`. Establish `hr'` using `InducedPow.presents_pow L M.j n hL hr`. Use `⟨fun i => r (fun _ => i PUnit.unit PUnit.unit) ^ n, LB.isLB_linComb hL _ _, ?_, fun v e y yt i hy hi => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_nsmul]`. Conclude with `hr'`.

Establish `hi' : ⊤ ≤ yt ⁻¹ᵁ L.U (i PUnit.unit PUnit.unit)` using `fun x hx => Set.mem_iInter.1 (hi hx) PUnit.unit`. Establish `h₁` using `h v e y yt (fun _ => i PUnit.unit PUnit.unit) hy hi'`. Establish `hu` using `(unitAt_quot (i := fun _ => i PUnit.unit PUnit.unit) ht hr hy hi').regAt`. Rewrite using `[pow_mul, ← mul_pow, Units.val_pow_eq_pow_val, SmallSec.valAt_pow hu, map_pow, Real.log_pow, ← h₁]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem GivenBy.pow {M : GlobalTheory.TrueGeo.Model Y} {L : LB M.X} {m : ℕ} (ht : ∀ y, Δ.IsEqn y (t y))
    (h : GivenBy Δ t φ M L m) (n : ℕ) : GivenBy Δ t φ M (lbPow L n) (m * n) := by
  obtain ⟨r, hL, hr, h⟩ := h
  have hr' := InducedPow.presents_pow L M.j n hL hr
  refine ⟨fun i => r (fun _ => i PUnit.unit PUnit.unit) ^ n, LB.isLB_linComb hL _ _, ?_,
    fun v e y yt i hy hi => ?_⟩
  · rw [mul_nsmul]; exact hr'
  have hi' : ⊤ ≤ yt ⁻¹ᵁ L.U (i PUnit.unit PUnit.unit) := fun x hx => Set.mem_iInter.1 (hi hx) PUnit.unit
  have h₁ := h v e y yt (fun _ => i PUnit.unit PUnit.unit) hy hi'
  have hu := (unitAt_quot (i := fun _ => i PUnit.unit PUnit.unit) ht hr hy hi').regAt
  rw [pow_mul, ← mul_pow, Units.val_pow_eq_pow_val, SmallSec.valAt_pow hu, map_pow, Real.log_pow, ← h₁]
  push_cast
  ring

/- English proof (translation)
Take `⟨r, hL, hr, h⟩` from `h`. Take `⟨r', hL', hr', h'⟩` from `h'`. Use `⟨fun i => r (fun _ => (i PUnit.unit).1) * r' fun _ => (i PUnit.unit).2, CechPic.isLB_tens hL hL', ?_, fun v e y yt i hy hi => ?_⟩` and prove the remaining obligations. Rewrite using `[nsmul_add]`. Conclude with `presents_tens hL hL' M.j hr hr'`.

Establish `hi₁ : ⊤ ≤ yt ⁻¹ᵁ L.U (i PUnit.unit).1` using `fun x hx => (hi hx).1`. Establish `hi₂ : ⊤ ≤ yt ⁻¹ᵁ L'.U (i PUnit.unit).2` using `fun x hx => (hi hx).2`. Establish `h₁` using `h v e y yt (fun _ => (i PUnit.unit).1) hy hi₁`. Establish `h₂` using `h' v e y yt (fun _ => (i PUnit.unit).2) hy hi₂`. Establish `u₁` using `unitAt_quot (i := fun _ => (i PUnit.unit).1) ht hr hy hi₁`.

Establish `u₂` using `unitAt_quot (i := fun _ => (i PUnit.unit).2) ht' hr' hy hi₂`. Rewrite using `[mul_inv, mul_pow, mul_mul_mul_comm, Units.val_mul, SmallSec.valAt_mul u₁.regAt u₂.regAt, map_mul, Real.log_mul (e.w.pos (SmallSec.valAt_ne_zero u₁)).ne' (e.w.pos (SmallSec.valAt_ne_zero u₂)).ne', ← h₁, ← h₂, mul_add]`.
-/
theorem GivenBy.tens {M : GlobalTheory.TrueGeo.Model Y} {L L' : LB M.X} {m : ℕ} (ht : ∀ y, Δ.IsEqn y (t y))
    (ht' : ∀ y, Δ'.IsEqn y (t' y)) (h : GivenBy Δ t φ M L m) (h' : GivenBy Δ' t' φ' M L' m) :
    GivenBy (Δ + Δ') (fun y => t y * t' y) (fun v e y => φ v e y + φ' v e y) M (CechPic.tens L L') m := by
  obtain ⟨r, hL, hr, h⟩ := h
  obtain ⟨r', hL', hr', h'⟩ := h'
  refine ⟨fun i => r (fun _ => (i PUnit.unit).1) * r' fun _ => (i PUnit.unit).2, CechPic.isLB_tens hL hL', ?_,
    fun v e y yt i hy hi => ?_⟩
  · rw [nsmul_add]; exact presents_tens hL hL' M.j hr hr'
  have hi₁ : ⊤ ≤ yt ⁻¹ᵁ L.U (i PUnit.unit).1 := fun x hx => (hi hx).1
  have hi₂ : ⊤ ≤ yt ⁻¹ᵁ L'.U (i PUnit.unit).2 := fun x hx => (hi hx).2
  have h₁ := h v e y yt (fun _ => (i PUnit.unit).1) hy hi₁
  have h₂ := h' v e y yt (fun _ => (i PUnit.unit).2) hy hi₂
  have u₁ := unitAt_quot (i := fun _ => (i PUnit.unit).1) ht hr hy hi₁
  have u₂ := unitAt_quot (i := fun _ => (i PUnit.unit).2) ht' hr' hy hi₂
  rw [mul_inv, mul_pow, mul_mul_mul_comm, Units.val_mul, SmallSec.valAt_mul u₁.regAt u₂.regAt, map_mul,
    Real.log_mul (e.w.pos (SmallSec.valAt_ne_zero u₁)).ne' (e.w.pos (SmallSec.valAt_ne_zero u₂)).ne', ← h₁, ← h₂,
    mul_add]

/- English proof (translation)
Take `⟨M, L, m, h⟩` from `h`. Take `⟨M', L', m', h'⟩` from `h'`. Take `⟨N, π, π', -, -, -, hj, hj', -⟩` from `ModelDom.exists_normal_dominating F Y M M'`. Establish `a` using `(GivenBy.pull (m := m) h π hj).pow ht m'`. Establish `b` using `(GivenBy.pull (m := m') h' π' hj').pow ht' m`.

Rewrite `b` using `[mul_comm]`. Conclude with `⟨N, _, m * m', a.tens ht ht' b⟩`.
-/
theorem fromModel_add (F : Type) [Field F] [NumberField F] (Y : Var F) (Δ Δ' : Y.Dv) (t t' : Y.X → Y.Fnˣ)
    (φ φ' : PtFn Y) (ht : ∀ y, Δ.IsEqn y (t y)) (ht' : ∀ y, Δ'.IsEqn y (t' y)) (h : FromModel Y Δ t φ)
    (h' : FromModel Y Δ' t' φ') :
    FromModel Y (Δ + Δ') (fun y => t y * t' y) (fun v e y => φ v e y + φ' v e y) := by
  obtain ⟨M, L, m, h⟩ := h
  obtain ⟨M', L', m', h'⟩ := h'
  obtain ⟨N, π, π', -, -, -, hj, hj', -⟩ := ModelDom.exists_normal_dominating F Y M M'
  have a := (GivenBy.pull (m := m) h π hj).pow ht m'
  have b := (GivenBy.pull (m := m') h' π' hj').pow ht' m
  rw [mul_comm] at b
  exact ⟨N, _, m * m', a.tens ht ht' b⟩

end GlobalTheory.LineNorm.Add

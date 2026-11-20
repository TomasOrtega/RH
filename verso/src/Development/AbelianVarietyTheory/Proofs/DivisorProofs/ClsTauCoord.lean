import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauCoordMulSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadNonnegOfInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauCoordinateEqUnitMulPsiQuotient
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitTauCoordinateAddNsmulFirstVariable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPsiCoordinatesOfTauUnits
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.E8Order

open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

variable {R : Type} [CommRing R] [IsDomain R]

abbrev unitsR (R : Type) [CommRing R] [IsDomain R] : Subgroup (FractionRing R)ˣ :=
  (Units.map (algebraMap R (FractionRing R)).toMonoidHom).range

abbrev QR (R : Type) [CommRing R] [IsDomain R] := (FractionRing R)ˣ ⧸ unitsR R

abbrev cls : (FractionRing R)ˣ →* QR R := QuotientGroup.mk' (unitsR R)

/- English proof (translation)
Rewrite using `[eq_comm, QuotientGroup.mk'_eq_mk']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, ⟨u, rfl⟩, hz⟩`. Conclude with `⟨u, by rw [← hz]; rfl⟩`. Introduce and unpack `⟨u, hu⟩`.

Conclude with `⟨_, ⟨u, rfl⟩, Units.ext (by rw [hu]; rfl)⟩`.
-/
theorem cls_eq_iff (x y : (FractionRing R)ˣ) :
    cls x = cls y ↔ ∃ u : Rˣ, (x : FractionRing R) = (y : FractionRing R) * algebraMap R (FractionRing R) u := by
  rw [eq_comm, QuotientGroup.mk'_eq_mk']
  constructor
  · rintro ⟨z, ⟨u, rfl⟩, hz⟩
    exact ⟨u, by rw [← hz]; rfl⟩
  · rintro ⟨u, hu⟩
    exact ⟨_, ⟨u, rfl⟩, Units.ext (by rw [hu]; rfl)⟩

/- English proof (translation)
The claim follows from `(QuotientGroup.eq_one_iff _).2 ⟨u, rfl⟩`.
-/
theorem cls_unit (u : Rˣ) : cls (Units.map (algebraMap R (FractionRing R)).toMonoidHom u) = 1 :=
  (QuotientGroup.eq_one_iff _).2 ⟨u, rfl⟩

variable [IsLocalRing R]

def tq (D : DegPre R) (a b : D.X) : QR R :=
  cls (psiCoord D (a + b)) * (cls (psiCoord D a))⁻¹ * (cls (psiCoord D b))⁻¹

/- English proof (translation)
Take `⟨u, hu⟩` from `GlobalTheory.TauCoordQuot.main R D a b x _ _ _ hx (psiCoord_spec D (a + b)) (psiCoord_spec D a) (psiCoord_spec D b)`. Apply the tactic sequence `have : x = Units.map (algebraMap R (FractionRing R)).toMonoidHom u * (psiCoord D (a + b) * (psiCoord D a)⁻¹ * (psiCoord D b)⁻¹) := by ext; rw [hu]; simp <;> ring`. Rewrite using `[this, map_mul, cls_unit, _root_.one_mul, tq, map_mul, map_mul, map_inv, map_inv]`.
-/
theorem cls_tauCoord {D : DegPre R} {a b : D.X} {x : (FractionRing R)ˣ} (hx : IsTauCoord D a b x) :
    cls x = tq D a b := by
  obtain ⟨u, hu⟩ := GlobalTheory.TauCoordQuot.main R D a b x _ _ _ hx (psiCoord_spec D (a + b)) (psiCoord_spec D a)
    (psiCoord_spec D b)
  have : x = Units.map (algebraMap R (FractionRing R)).toMonoidHom u *
      (psiCoord D (a + b) * (psiCoord D a)⁻¹ * (psiCoord D b)⁻¹) := by
    ext; rw [hu]; simp <;> ring
  rw [this, map_mul, cls_unit, _root_.one_mul, tq, map_mul, map_mul, map_inv, map_inv]

/- English proof (translation)
Simplify using `only [tq, add_comm a b]`. Conclude with `mul_right_comm _ _ _`.
-/
theorem tq_symm (D : DegPre R) (a b : D.X) : tq D a b = tq D b a := by
  simp only [tq, add_comm a b]; exact mul_right_comm _ _ _

/- English proof (translation)
Take `⟨x, hx⟩` from `GlobalTheory.PsiFromTau.exists_isTauCoord R D a b`. Take `⟨x', hx'⟩` from `GlobalTheory.PsiFromTau.exists_isTauCoord R D z b`. Take `⟨x'', hx''⟩` from `GlobalTheory.PsiFromTau.exists_isTauCoord R D (a + (1 : ℕ) • z) b`. Take `⟨u, hu⟩` from `GlobalTheory.TauShift.main R D hB a z b 1 x x' x'' hx hx' hx''`. Rewrite `hx''` using `[one_smul]`.

Rewrite using `[← cls_tauCoord hx'', ← cls_tauCoord hx, ← cls_tauCoord hx', hu, map_mul, cls_unit, _root_.one_mul, pow_one, map_mul]`.
-/
theorem tq_add_left (D : DegPre R) (hB : D.TauBimult) (a z b : D.X) : tq D (a + z) b = tq D a b * tq D z b := by
  obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D a b
  obtain ⟨x', hx'⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D z b
  obtain ⟨x'', hx''⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D (a + (1 : ℕ) • z) b
  obtain ⟨u, hu⟩ := GlobalTheory.TauShift.main R D hB a z b 1 x x' x'' hx hx' hx''
  rw [one_smul] at hx''
  rw [← cls_tauCoord hx'', ← cls_tauCoord hx, ← cls_tauCoord hx', hu, map_mul, cls_unit, _root_.one_mul, pow_one, map_mul]

def tqHom (D : DegPre R) (hB : D.TauBimult) (a : D.X) : D.X →+ Additive (QR R) :=
  AddMonoidHom.mk' (fun b => Additive.ofMul (tq D a b)) fun b b' => by
    rw [tq_symm D a (b + b'), tq_add_left D hB, tq_symm D b a, tq_symm D b' a]; rfl

/- English proof (translation)
Introduce `R _ _ _ hR D D' hB' hE' hB W hW ϖ β hs hp hτ c e hsum hcomp y r hr`. Use `haveI := hR`. Establish `hq : 0 ≤ qW W β (e y)` using `GlobalTheory.Poinc.qW_nonneg_of_posW W hW.1 β hs hp (e y)`. Use `⟨hq, ?_⟩` and prove the remaining obligations. Take `⟨s, hsd⟩ : ∃ s, s = e y` from `⟨_, rfl⟩`.

Take `⟨t, ht⟩ : ∃ t : Fin 8 → D.X, t = fun v => ∑ u, (W + W.transpose) v u • s u` from `⟨_, rfl⟩`. Rewrite `hq`, the goal using `[← hsd]`. Establish `hsum2 : ∑ v, β (s v) (-(t v)) = -(2 * qW W β s)`. Substitute `ht` using the available equality. Simplify using `only [map_neg, map_sum, map_zsmul, smul_eq_mul, Finset.sum_neg_distrib, neg_inj]`.

Simplify using `only [Matrix.add_apply, Matrix.transpose_apply, add_mul, Finset.sum_add_distrib, qW, two_mul]`. Use `congr 1`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by rw [hs]`. Establish `h1 : ∑ v, c v (t v) = y` using `by rw [ht, hsd]; exact hsum y`.

Establish `hy : -y = ∑ v, c v (-(t v))`. Rewrite using `[← h1]`. Simplify using `only [map_neg, Finset.sum_neg_distrib]`. Take `⟨x', hx'⟩` from `GlobalTheory.PsiFromTau.exists_isTauCoord R D' y (-y)`. Establish `hcl : cls x' = tq D' y (-y)` using `cls_tauCoord hx'`.

Establish `hterm : ∀ v, tq D' y (c v (-(t v))) = tq D (s v) (-(t v))`. Introduce `v`. Take `⟨a, ha⟩` from `GlobalTheory.PsiFromTau.exists_isTauCoord R D (e y v) (-(t v))`. Take `⟨b, hb⟩` from `GlobalTheory.PsiFromTau.exists_isTauCoord R D' y (c v (-(t v)))`. Take `⟨u, hu⟩` from `hcomp v y (-(t v)) a b ha hb`.

Rewrite using `[← cls_tauCoord hb, hsd, ← cls_tauCoord ha]`. Conclude with `((cls_eq_iff _ _).2 ⟨u, by rw [hu, mul_comm]⟩).symm`. Establish `hprod : Additive.ofMul (tq D' y (-y)) = ∑ v, Additive.ofMul (tq D (s v) (-(t v)))`. Use `map_sum (tqHom D' hB' y) (fun v => c v (-(t v))) Finset.univ` as an intermediate fact. Rewrite `this` using `[← hy]`.

Use `this.trans ?_` and prove the remaining obligations. Conclude with `Finset.sum_congr rfl fun v _ => congrArg Additive.ofMul (hterm v)`. Take `⟨w0, hw0⟩` from `GlobalTheory.PsiFromTauEven.tauCoord_mul_sq R D' hB' hE' y r hr x' hx'`. Establish `hr0 : r ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hw0` using `[map_zero, zero_pow two_ne_zero, mul_zero]`. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 w0.ne_zero hw0.symm`. Set `ru : (FractionRing R)ˣ` to `toUnitK r hr0`. Establish `hru : x' * ru ^ 2 = Units.map (algebraMap R (FractionRing R)).toMonoidHom w0` using `by ext; simp [ru, toUnitK, hw0]`. Establish `hcr : cls ru ^ 2 = (cls x')⁻¹`.

Use `congrArg cls hru` as an intermediate fact. Rewrite `this` using `[map_mul, map_pow, cls_unit]`. Conclude with `eq_inv_of_mul_eq_one_right this`. Take `⟨n, hn⟩` from `Int.eq_ofNat_of_zero_le hq`. Rewrite using `[hn, Int.toNat_natCast]`.

Establish `final : ∀ ρ : (FractionRing R)ˣ, (ρ : FractionRing R) = algebraMap R (FractionRing R) (ϖ ^ n) → cls ru ^ 2 = cls ρ ^ 2 → Associated r (ϖ ^ n)`. Introduce `ρ hρ h`. Rewrite `h` using `[← map_pow, ← map_pow]`. Take `⟨u, hu⟩` from `(cls_eq_iff _ _).1 h`. Simplify using `only [Units.val_pow_eq_pow_val, hρ, ru, toUnitK, Units.val_mk0, ← map_pow, ← map_mul] at hu`.

Establish `hsq : Associated ((ϖ ^ n) ^ 2) (r ^ 2)` using `⟨u, (IsFractionRing.injective R (FractionRing R) hu).symm⟩`. Conclude with `(associated_of_dvd_dvd ((IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 hsq.dvd) ((IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 hsq.symm.dvd)).symm`. Distinguish the cases in `hϖ : ϖ = 0`. Establish `hβ0 : ∀ a b, β a b = 0`. Introduce `a b`.

Take `⟨x, hx⟩` from `GlobalTheory.PsiFromTau.exists_isTauCoord R D a b`. Take `⟨u, hu⟩` from `hτ a b x hx`. Assume the negation of the conclusion as `h`. Rewrite `hu` using `[hϖ, map_zero, zero_zpow _ h, mul_zero]`. Conclude with `x.ne_zero hu`.

Establish `hq0 : qW W β s = 0` using `by simp [qW, hβ0]`. Establish `htq : ∀ a b, tq D a b = 1`. Introduce `a b`. Take `⟨x, hx⟩` from `GlobalTheory.PsiFromTau.exists_isTauCoord R D a b`. Take `⟨u, hu⟩` from `hτ a b x hx`.

Rewrite using `[← cls_tauCoord hx]`. Establish `: x = Units.map (algebraMap R (FractionRing R)).toMonoidHom u` using `by ext; rw [hu, hβ0, zpow_zero, _root_.mul_one]; rfl`. Rewrite using `[this, cls_unit]`. Establish `h1' : tq D' y (-y) = 1`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Rewrite using `[hprod]`. Simplify using `[htq]`. Establish `hn0 : n = 0` using `by omega`. Substitute `hn0` using the available equality. Use `final 1 (by simp) ?_` and prove the remaining obligations.

Rewrite using `[hcr, hcl, h1']`. Simplify using the standard rewrite rules. Set `ϖu : (FractionRing R)ˣ` to `toUnitK ϖ hϖ`. Establish `htq : ∀ a b, tq D a b = cls ϖu ^ β a b`. Introduce `a b`.

Take `⟨x, hx⟩` from `GlobalTheory.PsiFromTau.exists_isTauCoord R D a b`. Take `⟨u, hu⟩` from `hτ a b x hx`. Rewrite using `[← cls_tauCoord hx, ← map_zpow]`. Conclude with `(cls_eq_iff _ _).2 ⟨u, by rw [hu, Units.val_zpow_eq_zpow_val]; simp [ϖu, toUnitK, mul_comm]⟩`. Establish `hx'cl : cls x' = cls ϖu ^ (-(2 * qW W β s))`.

Rewrite using `[hcl]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Rewrite using `[hprod]`. Simplify using `only [htq, ofMul_zpow]`. Rewrite using `[← Finset.sum_smul, hsum2]`.

Use `final (ϖu ^ n) (by simp [ϖu, toUnitK]) ?_` and prove the remaining obligations. Rewrite using `[hcr, hx'cl, hn, map_pow, ← zpow_neg, neg_neg, show (2 * (n : ℤ)) = ((n * 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul]`.
-/
theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsDiscreteValuationRing R → ∀ (D D' : DegPre R), D'.TauBimult → D'.PsiEven → D.TauBimult → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (ϖ : R) (β : LinearMap.BilinForm ℤ D.X), (∀ a b, β a b = β b a) → (∀ a, 0 ≤ β a a) → (∀ a b' (x : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D a b' x → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * algebraMap R (FractionRing R) ϖ ^ (β a b')) → ∀ (c : Fin 8 → (D.X →+ D'.X)) (e : D'.X ≃+ (Fin 8 → D.X)), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → (∀ v a' b (x x' : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D (e a' v) b x → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D' a' (c v b) x' → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * (x' : FractionRing R)) → ∀ y r, PsiCoord D' y r → 0 ≤ qW W β (e y) ∧ Associated r (ϖ ^ (qW W β (e y)).toNat) := by
  intro R _ _ _ hR D D' hB' hE' hB W hW ϖ β hs hp hτ c e hsum hcomp y r hr
  haveI := hR
  have hq : 0 ≤ qW W β (e y) := GlobalTheory.Poinc.qW_nonneg_of_posW W hW.1 β hs hp (e y)
  refine ⟨hq, ?_⟩
  obtain ⟨s, hsd⟩ : ∃ s, s = e y := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : Fin 8 → D.X, t = fun v => ∑ u, (W + W.transpose) v u • s u := ⟨_, rfl⟩
  rw [← hsd] at hq ⊢
  have hsum2 : ∑ v, β (s v) (-(t v)) = -(2 * qW W β s) := by
    subst ht
    simp only [map_neg, map_sum, map_zsmul, smul_eq_mul, Finset.sum_neg_distrib, neg_inj]
    simp only [Matrix.add_apply, Matrix.transpose_apply, add_mul, Finset.sum_add_distrib, qW, two_mul]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by rw [hs]
  have h1 : ∑ v, c v (t v) = y := by rw [ht, hsd]; exact hsum y
  have hy : -y = ∑ v, c v (-(t v)) := by
    rw [← h1]; simp only [map_neg, Finset.sum_neg_distrib]
  obtain ⟨x', hx'⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D' y (-y)
  have hcl : cls x' = tq D' y (-y) := cls_tauCoord hx'
  have hterm : ∀ v, tq D' y (c v (-(t v))) = tq D (s v) (-(t v)) := by
    intro v
    obtain ⟨a, ha⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D (e y v) (-(t v))
    obtain ⟨b, hb⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D' y (c v (-(t v)))
    obtain ⟨u, hu⟩ := hcomp v y (-(t v)) a b ha hb
    rw [← cls_tauCoord hb, hsd, ← cls_tauCoord ha]
    exact ((cls_eq_iff _ _).2 ⟨u, by rw [hu, mul_comm]⟩).symm
  have hprod : Additive.ofMul (tq D' y (-y)) = ∑ v, Additive.ofMul (tq D (s v) (-(t v))) := by
    have := map_sum (tqHom D' hB' y) (fun v => c v (-(t v))) Finset.univ
    rw [← hy] at this
    refine this.trans ?_
    exact Finset.sum_congr rfl fun v _ => congrArg Additive.ofMul (hterm v)
  obtain ⟨w0, hw0⟩ := GlobalTheory.PsiFromTauEven.tauCoord_mul_sq R D' hB' hE' y r hr x' hx'
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_pow two_ne_zero, mul_zero] at hw0
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 w0.ne_zero hw0.symm
  let ru : (FractionRing R)ˣ := toUnitK r hr0
  have hru : x' * ru ^ 2 = Units.map (algebraMap R (FractionRing R)).toMonoidHom w0 := by
    ext; simp [ru, toUnitK, hw0]
  have hcr : cls ru ^ 2 = (cls x')⁻¹ := by
    have := congrArg cls hru
    rw [map_mul, map_pow, cls_unit] at this
    exact eq_inv_of_mul_eq_one_right this
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hq
  rw [hn, Int.toNat_natCast]
  have final : ∀ ρ : (FractionRing R)ˣ, (ρ : FractionRing R) = algebraMap R (FractionRing R) (ϖ ^ n) →
      cls ru ^ 2 = cls ρ ^ 2 → Associated r (ϖ ^ n) := by
    intro ρ hρ h
    rw [← map_pow, ← map_pow] at h
    obtain ⟨u, hu⟩ := (cls_eq_iff _ _).1 h
    simp only [Units.val_pow_eq_pow_val, hρ, ru, toUnitK, Units.val_mk0, ← map_pow, ← map_mul] at hu
    have hsq : Associated ((ϖ ^ n) ^ 2) (r ^ 2) := ⟨u, (IsFractionRing.injective R (FractionRing R) hu).symm⟩
    exact (associated_of_dvd_dvd ((IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 hsq.dvd)
      ((IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 hsq.symm.dvd)).symm
  by_cases hϖ : ϖ = 0
  · have hβ0 : ∀ a b, β a b = 0 := by
      intro a b
      obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D a b
      obtain ⟨u, hu⟩ := hτ a b x hx
      by_contra h
      rw [hϖ, map_zero, zero_zpow _ h, mul_zero] at hu
      exact x.ne_zero hu
    have hq0 : qW W β s = 0 := by simp [qW, hβ0]
    have htq : ∀ a b, tq D a b = 1 := by
      intro a b
      obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D a b
      obtain ⟨u, hu⟩ := hτ a b x hx
      rw [← cls_tauCoord hx]
      have : x = Units.map (algebraMap R (FractionRing R)).toMonoidHom u := by
        ext; rw [hu, hβ0, zpow_zero, _root_.mul_one]; rfl
      rw [this, cls_unit]
    have h1' : tq D' y (-y) = 1 := by
      apply Additive.ofMul.injective
      rw [hprod]; simp [htq]
    have hn0 : n = 0 := by omega
    subst hn0
    refine final 1 (by simp) ?_
    rw [hcr, hcl, h1']; simp
  · let ϖu : (FractionRing R)ˣ := toUnitK ϖ hϖ
    have htq : ∀ a b, tq D a b = cls ϖu ^ β a b := by
      intro a b
      obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D a b
      obtain ⟨u, hu⟩ := hτ a b x hx
      rw [← cls_tauCoord hx, ← map_zpow]
      exact (cls_eq_iff _ _).2 ⟨u, by rw [hu, Units.val_zpow_eq_zpow_val]; simp [ϖu, toUnitK, mul_comm]⟩
    have hx'cl : cls x' = cls ϖu ^ (-(2 * qW W β s)) := by
      rw [hcl]; apply Additive.ofMul.injective; rw [hprod]
      simp only [htq, ofMul_zpow]
      rw [← Finset.sum_smul, hsum2]
    refine final (ϖu ^ n) (by simp [ϖu, toUnitK]) ?_
    rw [hcr, hx'cl, hn, map_pow, ← zpow_neg, neg_neg, show (2 * (n : ℤ)) = ((n * 2 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast, pow_mul]

end GlobalTheory.Poinc.E8Order

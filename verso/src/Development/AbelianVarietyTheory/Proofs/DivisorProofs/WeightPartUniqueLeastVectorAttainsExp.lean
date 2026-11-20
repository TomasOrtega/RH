import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WtChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalLab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLabOntoAndKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupDividingLabelPersistsDeeperLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartAttainsBoundUniqueShortestVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTranslateValuesShiftByRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.GSumEx

/- English proof (translation)
Establish `key : ∀ h₀ : S.Gam, ∑ j, algebraMap o Ω (S.proj T c j i₀) * S.ev h₀ j = algebraMap o Ω (Ring.inverse (Nat.card T : o)) * ∑ t : T, algebraMap o Ω (S.ζN ^ (-(c t)).val) * ∑ j, algebraMap o Ω (S.ρ t j i₀) * S.ev h₀ j`. Introduce `h₀`. Rewrite using `[ThetaSys.proj, finsum_eq_sum_of_fintype]`. Simplify using `only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, map_mul, map_sum, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations. Establish `hsum : ∑ t : T, algebraMap o Ω (S.ζN ^ (-(c t)).val) * ∑ j, algebraMap o Ω (S.ρ t j i₀) * S.ev h' j = ξ * ∑ t : T, algebraMap o Ω (S.ζN ^ (-(c t)).val) * ∑ j, algebraMap o Ω (S.ρ t j i₀) * S.ev h j`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[hs t t.2]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key h', key h, hsum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_proj_shift {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (i₀ : S.J)
    {T : AddSubgroup S.Gam} (c : T →+ ZMod S.N) {h h' : S.Gam} {ξ : Ω}
    (hs : ∀ t ∈ T, ∑ j, algebraMap o Ω (S.ρ t j i₀) * S.ev h' j = ξ * ∑ j, algebraMap o Ω (S.ρ t j i₀) * S.ev h j) :
    ∑ j, algebraMap o Ω (S.proj T c j i₀) * S.ev h' j = ξ * ∑ j, algebraMap o Ω (S.proj T c j i₀) * S.ev h j := by
  classical
  have key : ∀ h₀ : S.Gam, ∑ j, algebraMap o Ω (S.proj T c j i₀) * S.ev h₀ j =
      algebraMap o Ω (Ring.inverse (Nat.card T : o)) * ∑ t : T, algebraMap o Ω (S.ζN ^ (-(c t)).val) *
        ∑ j, algebraMap o Ω (S.ρ t j i₀) * S.ev h₀ j := by
    intro h₀
    rw [ThetaSys.proj, finsum_eq_sum_of_fintype]
    simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, map_mul, map_sum, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => by ring
  have hsum : ∑ t : T, algebraMap o Ω (S.ζN ^ (-(c t)).val) * ∑ j, algebraMap o Ω (S.ρ t j i₀) * S.ev h' j =
      ξ * ∑ t : T, algebraMap o Ω (S.ζN ^ (-(c t)).val) * ∑ j, algebraMap o Ω (S.ρ t j i₀) * S.ev h j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hs t t.2]
    ring
  rw [key h', key h, hsum]
  ring

/- English proof (translation)
Establish `hR` using `RatModel.range_eq_singleton y (closedPoint (PadicAlgCl p))`. Establish `hsp` using `RatModel.specializes_of_range_eq hR`. Establish `hbu : IsUnit (⟨b, hb⟩ : M.O (y (closedPoint _)))` using `(RatModel.val_ne_zero_iff hR _).1 hb0`. Take `⟨hb0', hbinv⟩` from `(RatModel.isUnit_O_iff _).1 hbu`. Establish `hk' : (⟨ξ * w, hu⟩ : M.O (y (closedPoint _))) ^ k = (⟨w, hw⟩ : M.O (y (closedPoint _))) ^ k`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [SubmonoidClass.coe_pow]`. Rewrite using `[mul_pow, hξ, one_mul]`. Establish `hnorm : ‖M.val y (ξ * w)‖ = ‖M.val y w‖`. Establish `h1` using `congrArg (fun x => ‖RatModel.valHomOf y _ hsp x‖) hk'`.

Simplify using `only [map_pow, norm_pow, RatModel.valHomOf_apply] at h1`. Conclude with `(pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hk.ne').1 h1`. Establish `hdiv : M.val y (ξ * w / b) = M.val y (ξ * w) * M.val y b⁻¹`. Rewrite using `[div_eq_mul_inv]`. Conclude with `RatModel.val_mul hsp hu hbinv`.

Establish `hinv : M.val y b * M.val y b⁻¹ = 1`. Rewrite using `[← RatModel.val_mul hsp hb hbinv, mul_inv_cancel₀ hb0', RatModel.val_one]`. Rewrite using `[hdiv, norm_mul, hnorm, eq_inv_of_mul_eq_one_right hinv, norm_inv, div_eq_mul_inv]`.
-/
theorem norm_val_div {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {p : ℕ} [Fact p.Prime]
    (y : Sp (PadicAlgCl p) ⟶ M.Z) {w b ξ : Ω} {k : ℕ} (hk : 0 < k) (hξ : ξ ^ k = 1)
    (hu : ξ * w ∈ M.O (y (closedPoint _))) (hw : w ∈ M.O (y (closedPoint _))) (hb : b ∈ M.O (y (closedPoint _)))
    (hb0 : M.val y b ≠ 0) : ‖M.val y (ξ * w / b)‖ = ‖M.val y w‖ / ‖M.val y b‖ := by
  have hR := RatModel.range_eq_singleton y (closedPoint (PadicAlgCl p))
  have hsp := RatModel.specializes_of_range_eq hR
  have hbu : IsUnit (⟨b, hb⟩ : M.O (y (closedPoint _))) := (RatModel.val_ne_zero_iff hR _).1 hb0
  obtain ⟨hb0', hbinv⟩ := (RatModel.isUnit_O_iff _).1 hbu
  have hk' : (⟨ξ * w, hu⟩ : M.O (y (closedPoint _))) ^ k = (⟨w, hw⟩ : M.O (y (closedPoint _))) ^ k := by
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow]
    rw [mul_pow, hξ, one_mul]
  have hnorm : ‖M.val y (ξ * w)‖ = ‖M.val y w‖ := by
    have h1 := congrArg (fun x => ‖RatModel.valHomOf y _ hsp x‖) hk'
    simp only [map_pow, norm_pow, RatModel.valHomOf_apply] at h1
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hk.ne').1 h1
  have hdiv : M.val y (ξ * w / b) = M.val y (ξ * w) * M.val y b⁻¹ := by
    rw [div_eq_mul_inv]
    exact RatModel.val_mul hsp hu hbinv
  have hinv : M.val y b * M.val y b⁻¹ = 1 := by
    rw [← RatModel.val_mul hsp hb hbinv, mul_inv_cancel₀ hb0', RatModel.val_one]
  rw [hdiv, norm_mul, hnorm, eq_inv_of_mul_eq_one_right hinv, norm_inv, div_eq_mul_inv]

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

/- English proof (translation)
Use `set yg := gPt p ≫ y with hyg`. Establish `hR` using `RatModel.range_eq_singleton yg (closedPoint (PadicAlgCl p))`. Establish `hsp` using `RatModel.specializes_of_range_eq hR`. Establish `hgz : yg (closedPoint (PadicAlgCl p)) ⤳ y (cPt p)` using `RatModel.gPt_specializes (M := X.M) (y := y) rfl (closedPoint (PadicAlgCl p))`. Establish `hle : ∀ x, ‖X.M.val yg (c₀ * X.S.th x)‖ ≤ ‖X.M.val yg (c₀ * X.S.th x₀)‖`.

Introduce `x`. Establish `hq : X.S.th x / X.S.th x₀ ∈ X.M.O (y (cPt p))` using `hx₀.2 x`. Establish `hq' : X.S.th x / X.S.th x₀ ∈ X.M.O (yg (closedPoint (PadicAlgCl p)))` using `RatModel.O_le_of_specializes hgz hq`. Establish `hc0 : c₀ * X.S.th x₀ ∈ X.M.O (yg (closedPoint (PadicAlgCl p)))` using `hR' (hth x₀)`. Establish `heq : c₀ * X.S.th x = (c₀ * X.S.th x₀) * (X.S.th x / X.S.th x₀)`.

Clear denominators, using `[hx₀.1]` for the nonvanishing conditions. Rewrite using `[heq, RatModel.val_mul hsp hc0 hq', norm_mul]`. Establish `h1 : ‖X.M.val yg (X.S.th x / X.S.th x₀)‖ ≤ 1` using `RatModel.norm_val_le_one rfl hq`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) h1`. Establish `hv : ∀ x, ‖y₀ ⟨c₀ * X.S.th x, hth x⟩‖ = ‖X.M.val yg (c₀ * X.S.th x)‖` using `fun x => by rw [hy₀]`.

Use `show _ = ⨆ x, ‖y₀ ⟨c₀ * X.S.th x, hth x⟩‖`. Simplify using `only [hv]`. Use `le_antisymm (le_ciSup (f := fun x => ‖X.M.val yg (c₀ * X.S.th x)‖) ⟨‖X.M.val yg (c₀ * X.S.th x₀)‖, ?_⟩ x₀) (ciSup_le hle)` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `hle x`.
-/
theorem norm_th_eq_delta (X : Setup F W i) {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ X.M.Z) {c₀ : X.Ω₁} {hc R' fg frac hth hev}
    (hR' : R' ≤ X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p)))) (y₀ : R' →+* PadicAlgCl p)
    (hy₀ : ∀ a : R', y₀ a = X.M.val (gPt p ≫ y) a) {x₀ : X.S.Gam} (hx₀ : X.M.Div X.S.th x₀ (y (cPt p))) :
    ‖X.M.val (gPt p ≫ y) (c₀ * X.S.th x₀)‖ = (X.S.rechart c₀ hc R' fg frac hth hev).delta y₀ := by
  classical
  set yg := gPt p ≫ y with hyg
  have hR := RatModel.range_eq_singleton yg (closedPoint (PadicAlgCl p))
  have hsp := RatModel.specializes_of_range_eq hR
  have hgz : yg (closedPoint (PadicAlgCl p)) ⤳ y (cPt p) := RatModel.gPt_specializes (M := X.M) (y := y) rfl (closedPoint (PadicAlgCl p))
  have hle : ∀ x, ‖X.M.val yg (c₀ * X.S.th x)‖ ≤ ‖X.M.val yg (c₀ * X.S.th x₀)‖ := by
    intro x
    have hq : X.S.th x / X.S.th x₀ ∈ X.M.O (y (cPt p)) := hx₀.2 x
    have hq' : X.S.th x / X.S.th x₀ ∈ X.M.O (yg (closedPoint (PadicAlgCl p))) :=
      RatModel.O_le_of_specializes hgz hq
    have hc0 : c₀ * X.S.th x₀ ∈ X.M.O (yg (closedPoint (PadicAlgCl p))) := hR' (hth x₀)
    have heq : c₀ * X.S.th x = (c₀ * X.S.th x₀) * (X.S.th x / X.S.th x₀) := by
      field_simp [hx₀.1]
    rw [heq, RatModel.val_mul hsp hc0 hq', norm_mul]
    have h1 : ‖X.M.val yg (X.S.th x / X.S.th x₀)‖ ≤ 1 := RatModel.norm_val_le_one rfl hq
    exact mul_le_of_le_one_right (norm_nonneg _) h1
  have hv : ∀ x, ‖y₀ ⟨c₀ * X.S.th x, hth x⟩‖ = ‖X.M.val yg (c₀ * X.S.th x)‖ := fun x => by rw [hy₀]
  show _ = ⨆ x, ‖y₀ ⟨c₀ * X.S.th x, hth x⟩‖
  simp only [hv]
  refine le_antisymm (le_ciSup (f := fun x => ‖X.M.val yg (c₀ * X.S.th x)‖) ⟨‖X.M.val yg (c₀ * X.S.th x₀)‖, ?_⟩ x₀) (ciSup_le hle)
  rintro _ ⟨x, rfl⟩
  exact hle x

/- English proof (translation)
Establish `hd1 : X₁.S.r * X₁.S.N ∣ D.X.S.r * D.X.S.N`. Establish `h2 : D.m ∣ D.X.S.N` using `by rw [D.sq]; exact Dvd.intro_left _ (sq D.m).symm`. Conclude with `(D.dvd.trans h2).trans (Dvd.intro_left _ rfl)`. Take `⟨d, hd⟩` from `hd1`. Establish `hpos : 0 < X₁.S.r * X₁.S.N` using `Nat.pos_of_ne_zero (NeZero.ne _)`.

Establish `hdq : D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) = d`. Rewrite using `[hd, Nat.mul_div_cancel_left _ hpos]`. Establish `hdpos : d ≠ 0`. Introduce and unpack `rfl`. Conclude with `NeZero.ne (D.X.S.r * D.X.S.N) (by rw [hd, mul_zero])`.

Establish `hcoord : ∀ j, d ∣ (x j).val`. Introduce `j`. Establish `h1 : D.X.S.r * D.X.S.N ∣ X₁.S.r * X₁.S.N * (x j).val`. Establish `h0 : ((X₁.S.r * X₁.S.N) • x) j = 0` using `by rw [hk]; rfl`. Rewrite `h0` using `[Pi.smul_apply, nsmul_eq_mul, ← ZMod.natCast_zmod_val (x j), ← Nat.cast_mul]`.

Conclude with `(ZMod.natCast_eq_zero_iff _ _).1 h0`. Generalize the expression as in `(x j).val = v at h1 ⊢`. Rewrite `h1` using `[hd]`. Conclude with `Nat.dvd_of_mul_dvd_mul_left hpos h1`. Set `x' : D.X.S.Gam` to `fun j => (((x j).val / d : ℕ) : ZMod (D.X.S.r * D.X.S.N))`.

Establish `hx' : d • x' = x`. Use function extensionality and compare the values at `j`. Simplify using `only [x', Pi.smul_apply, nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_div_cancel' (hcoord j), ZMod.natCast_zmod_val]`. Take `⟨a, ha⟩` from `D.lab_range x'`. Rewrite `ha` using `[hdq, hx']`.

Use `⟨a, ?_, ha⟩` and prove the remaining obligations. Take `⟨μ, hμ⟩` from `QuotientAddGroup.mk_surjective (yy₁ a)`. Establish `h1` using `hC a μ hμ.symm`. Rewrite `h1` using `[ha, hdq, (AddMonoidHom.mem_ker).1 hx, eq_comm, QuotientAddGroup.eq_zero_iff]`. Take `⟨ν, hν⟩` from `h1`.

Simplify using `only [nsmulAddMonoidHom_apply] at hν`. Rewrite using `[AddMonoidHom.mem_ker, ← hμ, QuotientAddGroup.eq_zero_iff]`. Use `⟨ν, ?_⟩` and prove the remaining obligations. Simplify using `only [nsmulAddMonoidHom_apply]`. Rewrite `hν` using `[hd, mul_comm (X₁.S.r * X₁.S.N) d, mul_nsmul]`.

Use `(nsmul_right_inj hdpos).1 ?_` and prove the remaining obligations. Rewrite using `[← hν]`. Conclude with `smul_comm _ _ _`.
-/
theorem exists_lab {X₁ : Setup F W i} {ε₁} (D : Deep X₁ ε₁) {L : Type} [AddCommGroup L] [IsAddTorsionFree L]
    {yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) L} {yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) L} (hC : D.Compat yy₁ yy)
    {x : D.X.S.Gam} (hx : x ∈ yy.ker) (hk : (X₁.S.r * X₁.S.N) • x = 0) : ∃ b ∈ yy₁.ker, D.lab b = x := by
  classical
  have hd1 : X₁.S.r * X₁.S.N ∣ D.X.S.r * D.X.S.N := by
    have h2 : D.m ∣ D.X.S.N := by rw [D.sq]; exact Dvd.intro_left _ (sq D.m).symm
    exact (D.dvd.trans h2).trans (Dvd.intro_left _ rfl)
  obtain ⟨d, hd⟩ := hd1
  have hpos : 0 < X₁.S.r * X₁.S.N := Nat.pos_of_ne_zero (NeZero.ne _)
  have hdq : D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) = d := by
    rw [hd, Nat.mul_div_cancel_left _ hpos]
  have hdpos : d ≠ 0 := by
    rintro rfl
    exact NeZero.ne (D.X.S.r * D.X.S.N) (by rw [hd, mul_zero])

  have hcoord : ∀ j, d ∣ (x j).val := by
    intro j
    have h1 : D.X.S.r * D.X.S.N ∣ X₁.S.r * X₁.S.N * (x j).val := by
      have h0 : ((X₁.S.r * X₁.S.N) • x) j = 0 := by rw [hk]; rfl
      rw [Pi.smul_apply, nsmul_eq_mul, ← ZMod.natCast_zmod_val (x j), ← Nat.cast_mul] at h0
      exact (ZMod.natCast_eq_zero_iff _ _).1 h0
    generalize (x j).val = v at h1 ⊢
    rw [hd] at h1
    exact Nat.dvd_of_mul_dvd_mul_left hpos h1
  let x' : D.X.S.Gam := fun j => (((x j).val / d : ℕ) : ZMod (D.X.S.r * D.X.S.N))
  have hx' : d • x' = x := by
    funext j
    simp only [x', Pi.smul_apply, nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_div_cancel' (hcoord j),
      ZMod.natCast_zmod_val]
  obtain ⟨a, ha⟩ := D.lab_range x'
  rw [hdq, hx'] at ha
  refine ⟨a, ?_, ha⟩
  obtain ⟨μ, hμ⟩ := QuotientAddGroup.mk_surjective (yy₁ a)
  have h1 := hC a μ hμ.symm
  rw [ha, hdq, (AddMonoidHom.mem_ker).1 hx, eq_comm, QuotientAddGroup.eq_zero_iff] at h1
  obtain ⟨ν, hν⟩ := h1
  simp only [nsmulAddMonoidHom_apply] at hν
  rw [AddMonoidHom.mem_ker, ← hμ, QuotientAddGroup.eq_zero_iff]
  refine ⟨ν, ?_⟩
  simp only [nsmulAddMonoidHom_apply]
  rw [hd, mul_comm (X₁.S.r * X₁.S.N) d, mul_nsmul] at hν
  refine (nsmul_right_inj hdpos).1 ?_
  rw [← hν]
  exact smul_comm _ _ _

/- English proof (translation)
Use `⟨fun n hn a b hab => ?_⟩` and prove the remaining obligations. Set `e` to `(Module.Free.chooseBasis ℤ X).repr`. Apply `e.injective` to reduce the goal to its premises. Establish `h1 : n • e a = n • e b`. Simplify using `only at hab`.

Rewrite using `[← map_nsmul, ← map_nsmul, hab]`. Conclude with `IsAddTorsionFree.nsmul_right_injective hn h1`.
-/
private theorem isAddTorsionFree_of_free_int {X : Type} [AddCommGroup X] [Module.Free ℤ X] : IsAddTorsionFree X := by
  refine ⟨fun n hn a b hab => ?_⟩
  let e := (Module.Free.chooseBasis ℤ X).repr
  apply e.injective
  have h1 : n • e a = n • e b := by
    simp only at hab
    rw [← map_nsmul, ← map_nsmul, hab]
  exact IsAddTorsionFree.nsmul_right_injective hn h1

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem rechart_proj {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (c : Ω)
    (hc : c ≠ 0) (R' : Subalgebra o Ω) (fg : R'.FG) (frac : ∀ x : Ω, ∃ a ∈ R', ∃ b ∈ R', x = a / b)
    (hth : ∀ x, c * S.th x ∈ R') (hev : ∀ x i, c * S.ev x i ∈ R') (T : AddSubgroup S.Gam) (cc : T →+ ZMod S.N) :
    (S.rechart c hc R' fg frac hth hev).proj T cc = S.proj T cc := rfl

/- English proof (translation)
Rewrite `h`, the goal using `[QuotientAddGroup.eq]`. Take `⟨β, hβ⟩` from `h`. Use `⟨e.symm β, ?_⟩` and prove the remaining obligations. Simplify using `only [nsmulAddMonoidHom_apply] at hβ ⊢`. Rewrite using `[← map_nsmul, hβ, map_add, map_neg, AddEquiv.symm_apply_apply]`.
-/
private theorem mk_eq_mk_symm_of_mk_addEquiv_eq {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (k : ℕ) (e : X ≃+ Y) (χ : X) (ν : Y)
    (h : (QuotientAddGroup.mk (e χ) : ModN k Y) = QuotientAddGroup.mk ν) :
    (QuotientAddGroup.mk χ : ModN k X) = QuotientAddGroup.mk (e.symm ν) := by
  rw [QuotientAddGroup.eq] at h ⊢
  obtain ⟨β, hβ⟩ := h
  refine ⟨e.symm β, ?_⟩
  simp only [nsmulAddMonoidHom_apply] at hβ ⊢
  rw [← map_nsmul, hβ, map_add, map_neg, AddEquiv.symm_apply_apply]

/- English proof (translation)
Use extensionality with `a`. Rewrite using `[AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]`. Take `⟨χ, hχ⟩` from `QuotientAddGroup.mk_surjective (f a)`. Rewrite using `[← hχ, hf a χ hχ.symm, QuotientAddGroup.eq_zero_iff, QuotientAddGroup.eq_zero_iff]`. Simplify using `only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨β, hβ⟩`. Conclude with `⟨e β, by rw [← hβ, map_nsmul]⟩`. Introduce and unpack `⟨β, hβ⟩`. Conclude with `⟨e.symm β, by rw [← map_nsmul, hβ, AddEquiv.symm_apply_apply]⟩`.
-/
private theorem ker_eq_of_addEquiv_compat {G X Y : Type} [AddCommGroup G] [AddCommGroup X] [AddCommGroup Y] (k : ℕ)
    (f : G →+ ModN k X) (f' : G →+ ModN k Y) (e : X ≃+ Y)
    (hf : ∀ a χ, f a = QuotientAddGroup.mk χ → f' a = QuotientAddGroup.mk (e χ)) : f.ker = f'.ker := by
  ext a
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]
  obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (f a)
  rw [← hχ, hf a χ hχ.symm, QuotientAddGroup.eq_zero_iff, QuotientAddGroup.eq_zero_iff]
  simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨β, hβ⟩
    exact ⟨e β, by rw [← hβ, map_nsmul]⟩
  · rintro ⟨β, hβ⟩
    exact ⟨e.symm β, by rw [← map_nsmul, hβ, AddEquiv.symm_apply_apply]⟩

/- English proof (translation)
Substitute `hT` using the available equality. Use `congr 1`. Use extensionality with `t`. Conclude with `hc t t.2 t.2`.
-/
private theorem thetaSys_proj_congr {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    {T T' : AddSubgroup S.Gam} (hT : T = T') (c : T →+ ZMod S.N) (c' : T' →+ ZMod S.N)
    (hc : ∀ (t : S.Gam) (h : t ∈ T) (h' : t ∈ T'), c ⟨t, h⟩ = c' ⟨t, h'⟩) : S.proj T c = S.proj T' c' := by
  subst hT
  congr 1
  ext t
  exact hc t t.2 t.2

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `g n F W Z i X₁ hg hn hodd himm hE8 hTI hproj ε₁ hdiag D z₁ z₂ hq p hp c yy₁ hlab₁ y h hy yy hlab hC a ν hν hmin`. Establish `hK1` using `(isLab_onto_and_ker g n F W Z i X₁ hg hn hodd himm hE8 hTI hproj ε₁ hdiag p z₁ c yy₁ hlab₁).2`. Establish `hK2` using `(isLab_onto_and_ker g n F W Z i D.X hg hn hodd himm hE8 hTI D.proj D.ε D.diag p (y (cPt p)) (D.lift c y h) yy hlab).2`. Establish `hK2' : yy.ker = D.X.S.HH D.X.M z₂` using `by rw [← hy]; exact hK2`. Take `⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, hi₀, hR', y₀, hy₀, u, l, j, hq', hyy, -⟩` from `hlab`.

Establish `hint : ∀ b : D.X.o₁, ‖y₀ (algebraMap D.X.o₁ R' b)‖ ≤ 1`. Introduce `b`. Rewrite using `[hy₀]`. Conclude with `RatModel.norm_val_le_one (M := D.X.M) (y := y) rfl ((D.X.M.O _).algebraMap_mem b)`. Establish `hy₀' : ∀ b : R', y₀ b = D.X.M.val (gPt p ≫ y) (b : D.X.Ω₁)` using `hy₀`.

Establish `hL` using `GlobalTheory.abelianSchemeLaws_all`. Establish `hδ` using `(GlobalTheory.UnitTheta.closure_unit_theta hL.1 hL.2 GlobalTheory.ZH.uTors_closed _ _ _ ρ' p y₀ u l hint).1`. Establish `hker : l.yy.ker = yy.ker` using `ker_eq_of_addEquiv_compat _ l.yy yy j hyy`. Use `set ν' := j.symm ν with hν'`. Establish `hla : l.yy a = QuotientAddGroup.mk ν'`.

Take `⟨χ, hχ⟩` from `QuotientAddGroup.mk_surjective (l.yy a)`. Rewrite using `[← hχ]`. Conclude with `mk_eq_mk_symm_of_mk_addEquiv_eq _ j χ ν ((hyy a χ hχ.symm).symm.trans hν)`. Establish `hlma : l.yy (D.m • a) = QuotientAddGroup.mk (D.m • ν')`. Rewrite using `[map_nsmul, hla, ← QuotientAddGroup.mk_nsmul]`.

Establish `hmin' : ∀ χ : u.D.toPre.X, D.m • χ ≠ 0 → l.q ν' < l.q (ν' + D.m • χ)`. Introduce `χ hχ`. Rewrite using `[hq', hq', map_add, map_nsmul, hν', AddEquiv.apply_symm_apply]`. Establish `hne : ν + D.m • j χ ≠ ν`. Introduce `he`.

Apply `hχ` to reduce the goal to its premises. Apply `j.injective` to reduce the goal to its premises. Rewrite using `[map_nsmul, map_zero]`. Simplify using `using he`. Establish `hlt` using `hmin (ν + D.m • j χ) ⟨j χ, rfl⟩ hne`.

Establish `hsc : 0 < c.sc` using `CTrait.scale_pos c`. Conclude with `mul_lt_mul_of_pos_left (by exact_mod_cast hlt) hsc`. Establish `hk2 : 2 ≤ X₁.S.r * X₁.S.N` using `le_trans X₁.S.N_ge (Nat.le_mul_of_pos_left _ X₁.S.r_pos)`. Take `⟨hh, hhker, hkm, hnorm⟩` from `GlobalTheory.T.weightPart_attains_bound_unique_shortest_vector u l hint D.m (X₁.S.r * X₁.S.N) D.sq hk2 D.dvd ν' hmin'`. Rewrite `hhker` using `[hker]`.

Use `isAddTorsionFree_of_free_int (X := c.T.D.toPre.X)` as an intermediate fact. Take `⟨b, hb, hlb⟩` from `exists_lab D hC (x := D.m • hh) (yy.ker.nsmul_mem hhker _) hkm`. Establish `hbH : b ∈ X₁.S.HH X₁.M z₁` using `by rw [← hK1]; exact hb`. Use `⟨⟨b, hbH⟩, ?_⟩` and prove the remaining obligations. Establish `hhH : hh ∈ D.X.S.HH D.X.M z₂` using `by rw [← hK2']; exact hhker`.

Establish `hex : ∃ h' ∈ D.X.S.HH D.X.M z₂, D.m • h' = D.lab b` using `⟨hh, hhH, hlb.symm⟩`. Establish `hlift : GSum.lift D z₂ b = hex.choose` using `by rw [GSum.lift, dif_pos hex]`. Take `⟨hH'', hm''⟩` from `hex.choose_spec`. Take `⟨ξ, ⟨k', hk'pos, hξ⟩, hshift⟩` from `GlobalTheory.T.theta_translate_values_shift_by_root_of_unity D.X.ρ (D.X.S.HH D.X.M z₂) D.m D.sq hh hex.choose (by rw [hm'', hlb]) ((D.X.S.HH D.X.M z₂).sub_mem hH'' hhH)`. Establish `hsh` using `sum_proj_shift (S := D.X.S) D.X.ρ.i₀ (T := D.X.S.TT D.X.M z₂) (GSum.wtChar D _ a) hshift`.

Establish `hne : (X₁.S.supI X₁.M z₁).Nonempty`. Take `⟨x, hx⟩` from `X₁.div z₁`. Conclude with `⟨x, hx⟩`. Establish `hbase : GSum.base X₁ z₁ ∈ X₁.S.supI X₁.M z₁`. Rewrite using `[GSum.base, dif_pos hne]`.

Conclude with `hne.some_mem`. Establish `hqz : D.q (y (cPt p)) = z₁`. Rewrite using `[← c.cen, ← h]`. Both sides reduce to the same expression. Establish `hx₀` using `GlobalTheory.T.thetaSetup_dividingLabel_persists_deeperLevel g n F W Z i X₁ hg hn hodd himm hE8 hTI hproj ε₁ hdiag D z₁ (GSum.base X₁ z₁) hbase (y (cPt p)) hqz`.

Establish `hth0` using `norm_th_eq_delta D.X y (hth := hth) (hev := hev) (hc := hc) (fg := fg) (frac := frac) hR' y₀ hy₀ hx₀`. Use `set x₀ := D.lab (GSum.base X₁ z₁) with hx₀def`. Use `set T := D.X.S.TT D.X.M z₂ with hT`. Use `set wc := GSum.wtChar D T a with hwc`. Use `set Sm := ∑ j, algebraMap D.X.o₁ D.X.Ω₁ (D.X.S.proj T wc j D.X.ρ.i₀) * D.X.S.ev hh j with hSm`.

Establish `hmem : ∀ h₀ : D.X.S.Gam, c₀ * ∑ j, algebraMap D.X.o₁ D.X.Ω₁ (D.X.S.proj T wc j D.X.ρ.i₀) * D.X.S.ev h₀ j = ((∑ j, algebraMap D.X.o₁ R' (D.X.S.proj T wc j D.X.ρ.i₀) * (⟨c₀ * D.X.S.ev h₀ j, hev h₀ j⟩ : R') : R') : D.X.Ω₁)`. Introduce `h₀`. Simplify using `only [Finset.mul_sum, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, Subalgebra.coe_algebraMap]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Establish `hmemO : ∀ h₀ : D.X.S.Gam, c₀ * ∑ j, algebraMap D.X.o₁ D.X.Ω₁ (D.X.S.proj T wc j D.X.ρ.i₀) * D.X.S.ev h₀ j ∈ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p)))` using `fun h₀ => by`.

Rewrite using `[hmem h₀]`. Conclude with `hR' (Subtype.property _)`. Establish `hpart : GSum.part D z₁ z₂ a ⟨b, hbH⟩ = ξ * (c₀ * Sm) / (c₀ * D.X.S.th x₀)`. Rewrite using `[GSum.part]`. Apply the tactic sequence `try dsimp only`.

Rewrite using `[hlift, hsh, mul_left_comm ξ c₀ Sm, mul_div_mul_left _ _ hc]`. Establish `hw : ξ * (c₀ * Sm) ∈ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p)))`. Use `hmemO hex.choose` as an intermediate fact. Rewrite `this` using `[hsh]`. Rewrite using `[← mul_assoc, mul_comm ξ c₀, mul_assoc]`.

Conclude with `this`. Establish `hthO : c₀ * D.X.S.th x₀ ∈ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p)))` using `hR' (hth x₀)`. Establish `hthne : D.X.M.val (gPt p ≫ y) (c₀ * D.X.S.th x₀) ≠ 0`. Introduce `h0`. Rewrite `hth0` using `[h0, norm_zero]`.

Conclude with `hδ.ne' hth0.symm`. Establish `e1 : D.X.S.proj T wc = D.X.S.proj (D.X.S.perp l.yy.ker) (l.wt (D.m • ν'))`. Use `thetaSys_proj_congr _ (by rw [hT, ThetaSys.TT, hker, hK2']) _ _ fun t ht ht' => ?_` and prove the remaining obligations. Conclude with `Eq.trans rfl (l.wt_eq (D.m • a) (D.m • ν') hlma ⟨t, ht'⟩).symm`. Establish `hSmn : ‖D.X.M.val (gPt p ≫ y) (c₀ * Sm)‖ = (D.X.S.rechart c₀ hc R' fg frac hth hev).delta y₀ * Real.exp (-l.q ν')`.

Establish `e1' : D.X.S.proj T wc = (D.X.S.rechart c₀ hc R' fg frac hth hev).proj ((D.X.S.rechart c₀ hc R' fg frac hth hev).perp l.yy.ker) (l.wt (D.m • ν'))`. Rewrite using `[rechart_proj]`. Conclude with `e1`. Rewrite `hnorm` using `[← e1', hi₀]`. Rewrite using `[← hnorm, hSm, hmem hh, ← hy₀', map_sum]`.

Simplify using `only [map_mul]`. Rewrite using `[hpart, norm_val_div (M := D.X.M) (gPt p ≫ y) hk'pos hξ hw (hmemO hh) hthO hthne, hSmn, hth0, mul_div_cancel_left₀ _ hδ.ne', hq', hν', AddEquiv.apply_symm_apply]`. Apply the tactic sequence `try rfl`.
-/
theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (p : ℕ) [Fact p.Prime] (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν, yy a = QuotientAddGroup.mk ν → (∀ χ, CongMod D.m χ ν → χ ≠ ν → qW W c.T.β ν < qW W c.T.β χ) → ∃ κ, ‖D.X.M.val (gPt p ≫ y) (GSum.part D z₁ z₂ a κ)‖ = Real.exp (-(c.sc * (qW W c.T.β ν : ℤ))) := by
  intro g n F W Z i X₁ hg hn hodd himm hE8 hTI hproj ε₁ hdiag D z₁ z₂ hq p hp c yy₁ hlab₁ y h hy yy hlab hC a ν hν hmin
  classical
  have hK1 := (isLab_onto_and_ker g n F W Z i X₁ hg hn hodd himm hE8 hTI hproj ε₁ hdiag p z₁ c yy₁ hlab₁).2
  have hK2 := (isLab_onto_and_ker g n F W Z i D.X hg hn hodd himm hE8 hTI D.proj D.ε D.diag p (y (cPt p))
    (D.lift c y h) yy hlab).2
  have hK2' : yy.ker = D.X.S.HH D.X.M z₂ := by rw [← hy]; exact hK2
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, hi₀, hR', y₀, hy₀, u, l, j, hq', hyy, -⟩ := hlab
  have hint : ∀ b : D.X.o₁, ‖y₀ (algebraMap D.X.o₁ R' b)‖ ≤ 1 := by
    intro b
    rw [hy₀]
    exact RatModel.norm_val_le_one (M := D.X.M) (y := y) rfl ((D.X.M.O _).algebraMap_mem b)
  have hy₀' : ∀ b : R', y₀ b = D.X.M.val (gPt p ≫ y) (b : D.X.Ω₁) := hy₀
  have hL := GlobalTheory.abelianSchemeLaws_all
  have hδ := (GlobalTheory.UnitTheta.closure_unit_theta hL.1 hL.2 GlobalTheory.ZH.uTors_closed _ _ _ ρ' p y₀ u l hint).1
  have hker : l.yy.ker = yy.ker := ker_eq_of_addEquiv_compat _ l.yy yy j hyy

  set ν' := j.symm ν with hν'
  have hla : l.yy a = QuotientAddGroup.mk ν' := by
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (l.yy a)
    rw [← hχ]
    exact mk_eq_mk_symm_of_mk_addEquiv_eq _ j χ ν ((hyy a χ hχ.symm).symm.trans hν)
  have hlma : l.yy (D.m • a) = QuotientAddGroup.mk (D.m • ν') := by
    rw [map_nsmul, hla, ← QuotientAddGroup.mk_nsmul]

  have hmin' : ∀ χ : u.D.toPre.X, D.m • χ ≠ 0 → l.q ν' < l.q (ν' + D.m • χ) := by
    intro χ hχ
    rw [hq', hq', map_add, map_nsmul, hν', AddEquiv.apply_symm_apply]
    have hne : ν + D.m • j χ ≠ ν := by
      intro he
      apply hχ
      apply j.injective
      rw [map_nsmul, map_zero]
      simpa using he
    have hlt := hmin (ν + D.m • j χ) ⟨j χ, rfl⟩ hne
    have hsc : 0 < c.sc := CTrait.scale_pos c
    exact mul_lt_mul_of_pos_left (by exact_mod_cast hlt) hsc
  have hk2 : 2 ≤ X₁.S.r * X₁.S.N := le_trans X₁.S.N_ge (Nat.le_mul_of_pos_left _ X₁.S.r_pos)
  obtain ⟨hh, hhker, hkm, hnorm⟩ := GlobalTheory.T.weightPart_attains_bound_unique_shortest_vector u l hint D.m (X₁.S.r * X₁.S.N) D.sq hk2 D.dvd ν' hmin'
  rw [hker] at hhker

  have := isAddTorsionFree_of_free_int (X := c.T.D.toPre.X)
  obtain ⟨b, hb, hlb⟩ := exists_lab D hC (x := D.m • hh) (yy.ker.nsmul_mem hhker _) hkm
  have hbH : b ∈ X₁.S.HH X₁.M z₁ := by rw [← hK1]; exact hb
  refine ⟨⟨b, hbH⟩, ?_⟩

  have hhH : hh ∈ D.X.S.HH D.X.M z₂ := by rw [← hK2']; exact hhker
  have hex : ∃ h' ∈ D.X.S.HH D.X.M z₂, D.m • h' = D.lab b := ⟨hh, hhH, hlb.symm⟩
  have hlift : GSum.lift D z₂ b = hex.choose := by rw [GSum.lift, dif_pos hex]
  obtain ⟨hH'', hm''⟩ := hex.choose_spec
  obtain ⟨ξ, ⟨k', hk'pos, hξ⟩, hshift⟩ := GlobalTheory.T.theta_translate_values_shift_by_root_of_unity D.X.ρ (D.X.S.HH D.X.M z₂) D.m D.sq hh hex.choose
    (by rw [hm'', hlb]) ((D.X.S.HH D.X.M z₂).sub_mem hH'' hhH)
  have hsh := sum_proj_shift (S := D.X.S) D.X.ρ.i₀ (T := D.X.S.TT D.X.M z₂) (GSum.wtChar D _ a) hshift

  have hne : (X₁.S.supI X₁.M z₁).Nonempty := by
    obtain ⟨x, hx⟩ := X₁.div z₁
    exact ⟨x, hx⟩
  have hbase : GSum.base X₁ z₁ ∈ X₁.S.supI X₁.M z₁ := by
    rw [GSum.base, dif_pos hne]
    exact hne.some_mem
  have hqz : D.q (y (cPt p)) = z₁ := by
    rw [← c.cen, ← h]
    rfl
  have hx₀ := GlobalTheory.T.thetaSetup_dividingLabel_persists_deeperLevel g n F W Z i X₁ hg hn hodd himm hE8 hTI hproj ε₁ hdiag D z₁ (GSum.base X₁ z₁) hbase
    (y (cPt p)) hqz
  have hth0 := norm_th_eq_delta D.X y (hth := hth) (hev := hev) (hc := hc) (fg := fg) (frac := frac) hR' y₀ hy₀ hx₀
  set x₀ := D.lab (GSum.base X₁ z₁) with hx₀def
  set T := D.X.S.TT D.X.M z₂ with hT
  set wc := GSum.wtChar D T a with hwc
  set Sm := ∑ j, algebraMap D.X.o₁ D.X.Ω₁ (D.X.S.proj T wc j D.X.ρ.i₀) * D.X.S.ev hh j with hSm
  have hmem : ∀ h₀ : D.X.S.Gam, c₀ * ∑ j, algebraMap D.X.o₁ D.X.Ω₁ (D.X.S.proj T wc j D.X.ρ.i₀) * D.X.S.ev h₀ j =
      ((∑ j, algebraMap D.X.o₁ R' (D.X.S.proj T wc j D.X.ρ.i₀) * (⟨c₀ * D.X.S.ev h₀ j, hev h₀ j⟩ : R') : R') :
        D.X.Ω₁) := by
    intro h₀
    simp only [Finset.mul_sum, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, Subalgebra.coe_algebraMap]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hmemO : ∀ h₀ : D.X.S.Gam, c₀ * ∑ j, algebraMap D.X.o₁ D.X.Ω₁ (D.X.S.proj T wc j D.X.ρ.i₀) * D.X.S.ev h₀ j ∈
      D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) := fun h₀ => by
    rw [hmem h₀]
    exact hR' (Subtype.property _)
  have hpart : GSum.part D z₁ z₂ a ⟨b, hbH⟩ = ξ * (c₀ * Sm) / (c₀ * D.X.S.th x₀) := by
    rw [GSum.part]
    try dsimp only
    rw [hlift, hsh, mul_left_comm ξ c₀ Sm, mul_div_mul_left _ _ hc]
  have hw : ξ * (c₀ * Sm) ∈ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) := by
    have := hmemO hex.choose
    rw [hsh] at this
    rw [← mul_assoc, mul_comm ξ c₀, mul_assoc]
    exact this
  have hthO : c₀ * D.X.S.th x₀ ∈ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) := hR' (hth x₀)
  have hthne : D.X.M.val (gPt p ≫ y) (c₀ * D.X.S.th x₀) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hth0
    exact hδ.ne' hth0.symm
  have e1 : D.X.S.proj T wc = D.X.S.proj (D.X.S.perp l.yy.ker) (l.wt (D.m • ν')) := by
    refine thetaSys_proj_congr _ (by rw [hT, ThetaSys.TT, hker, hK2']) _ _ fun t ht ht' => ?_
    exact Eq.trans rfl (l.wt_eq (D.m • a) (D.m • ν') hlma ⟨t, ht'⟩).symm
  have hSmn : ‖D.X.M.val (gPt p ≫ y) (c₀ * Sm)‖ = (D.X.S.rechart c₀ hc R' fg frac hth hev).delta y₀ * Real.exp (-l.q ν') := by
    have e1' : D.X.S.proj T wc =
        (D.X.S.rechart c₀ hc R' fg frac hth hev).proj ((D.X.S.rechart c₀ hc R' fg frac hth hev).perp l.yy.ker)
          (l.wt (D.m • ν')) := by
      rw [rechart_proj]
      exact e1
    rw [← e1', hi₀] at hnorm
    rw [← hnorm, hSm, hmem hh, ← hy₀', map_sum]
    simp only [map_mul]
  rw [hpart, norm_val_div (M := D.X.M) (gPt p ≫ y) hk'pos hξ hw (hmemO hh) hthO hthne, hSmn, hth0,
    mul_div_cancel_left₀ _ hδ.ne', hq', hν', AddEquiv.apply_symm_apply]
  try rfl

end GlobalTheory.Poinc.GSumEx

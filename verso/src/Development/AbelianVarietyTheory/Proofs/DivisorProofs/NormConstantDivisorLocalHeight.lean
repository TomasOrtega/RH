import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticHeightTensorAdditiveOnCurves
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeLinearRootSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.DualRef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsDualBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointPlaceCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricOfSameNorms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricShiftElement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechPic
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CoverNorm GlobalTheory.ArDegIndep.TieOther

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverNorm.ConstDeg

/- English proof (translation)
Establish `hp` using `e.w.pos hc`. Establish `key : ∀ x : AlgebraicClosure F, e.w x < e.w c ↔ e.O.valuation (x / c) < 1` using `fun x => by`. Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Simplify using `using hp`. Establish `h₁ : e.O.valuation (x / c) ≠ 0` using `(Valuation.ne_zero_iff _).2 (div_ne_zero hx hc)`.

Rewrite using `[← one_lt_inv₀ (zero_lt_iff.2 h₁), ← map_inv₀, ← not_le (a := e.O.valuation _), ValuationSubring.valuation_le_one_iff, e.mem_O, inv_div, map_div₀, div_le_one (e.w.pos hx), not_le]`. Rewrite using `[key, Finset.sum_div]`. Conclude with `Valuation.map_sum_lt _ one_ne_zero fun k hk => (key _).1 (h k hk)`.
-/
private theorem w_sum_lt {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : TrueGeo.Ext v) {ι : Type}
    (s : Finset ι) (t : ι → AlgebraicClosure F) {c : AlgebraicClosure F} (hc : c ≠ 0) (h : ∀ k ∈ s, e.w (t k) < e.w c) :
    e.w (∑ k ∈ s, t k) < e.w c := by
  have hp := e.w.pos hc
  have key : ∀ x : AlgebraicClosure F, e.w x < e.w c ↔ e.O.valuation (x / c) < 1 := fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · simpa using hp
    · have h₁ : e.O.valuation (x / c) ≠ 0 := (Valuation.ne_zero_iff _).2 (div_ne_zero hx hc)
      rw [← one_lt_inv₀ (zero_lt_iff.2 h₁), ← map_inv₀, ← not_le (a := e.O.valuation _),
        ValuationSubring.valuation_le_one_iff, e.mem_O, inv_div, map_div₀, div_le_one (e.w.pos hx), not_le]
  rw [key, Finset.sum_div]
  exact Valuation.map_sum_lt _ one_ne_zero fun k hk => (key _).1 (h k hk)

/- English proof (translation)
Take `⟨P, hP0, hP⟩ : IsAlgebraic F α` from `Algebra.IsAlgebraic.isAlgebraic α`. Use `set T : ℕ → AlgebraicClosure F := fun k => algebraMap F _ (P.coeff k) * α ^ k with hT`. Establish `hsum : ∑ k ∈ P.support, T k = 0`. Rewrite `hP` using `[Polynomial.aeval_def, Polynomial.eval₂_eq_sum]`. Conclude with `hP`.

Establish `hT0 : ∀ k ∈ P.support, T k ≠ 0` using `fun k hk => mul_ne_zero ((map_ne_zero _).2 (Polynomial.mem_support_iff.1 hk)) (pow_ne_zero _ hα)`. Take `⟨m, hm, hmax⟩` from `P.support.exists_max_image (fun k => e.w (T k)) (Polynomial.support_nonempty.2 hP0)`. Establish `two : ∃ k ∈ P.support, k ≠ m ∧ e.w (T k) = e.w (T m)`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`.

Establish `h₁` using `w_sum_lt e (P.support.erase m) T (hT0 m hm) fun k hk => lt_of_le_of_ne (hmax k (Finset.mem_of_mem_erase hk)) (hne k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk))`. Rewrite `hsum` using `[← Finset.add_sum_erase _ _ hm, add_eq_zero_iff_neg_eq]`. Rewrite `h₁` using `[← hsum, e.w.map_neg]`. Conclude with `lt_irrefl _ h₁`. Establish `fin : ∀ k ∈ P.support, ∀ k' ∈ P.support, k < k' → e.w (T k) = e.w (T k') → ∃ b : ℕ, 0 < b ∧ ∃ t : F, t ≠ 0 ∧ e.w α ^ b = e.w (algebraMap F (AlgebraicClosure F) t)`.

Introduce `k hk k' hk' hlt h`. Establish `c₁` using `Polynomial.mem_support_iff.1 hk`. Establish `c₂` using `Polynomial.mem_support_iff.1 hk'`. Take `⟨b, rfl⟩` from `Nat.exists_eq_add_of_lt hlt`. Use `⟨b + 1, b.succ_pos, P.coeff k / P.coeff (k + b + 1), div_ne_zero c₁ c₂, ?_⟩` and prove the remaining obligations.

Establish `p₂` using `(e.w.pos ((map_ne_zero (algebraMap F (AlgebraicClosure F))).2 c₂)).ne'`. Establish `p₃` using `pow_ne_zero k (e.w.pos hα).ne'`. Simplify using `only [hT, map_mul, map_pow] at h`. Rewrite using `[map_div₀, map_div₀, eq_div_iff p₂]`. Use `mul_right_cancel₀ p₃ ?_` and prove the remaining obligations.

Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨k, hk, hkm, h⟩` from `two`. Break down `lt_or_gt_of_ne hkm with hl | hl` into its components or cases. Conclude with `fin k hk m hm hl h`.

Conclude with `fin m hm k hk hl h.symm`.
-/
private theorem exists_pow_w_eq {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : TrueGeo.Ext v)
    {α : AlgebraicClosure F} (hα : α ≠ 0) :
    ∃ b : ℕ, 0 < b ∧ ∃ t : F, t ≠ 0 ∧ e.w α ^ b = e.w (algebraMap F (AlgebraicClosure F) t) := by
  obtain ⟨P, hP0, hP⟩ : IsAlgebraic F α := Algebra.IsAlgebraic.isAlgebraic α
  set T : ℕ → AlgebraicClosure F := fun k => algebraMap F _ (P.coeff k) * α ^ k with hT
  have hsum : ∑ k ∈ P.support, T k = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum] at hP
    exact hP
  have hT0 : ∀ k ∈ P.support, T k ≠ 0 := fun k hk =>
    mul_ne_zero ((map_ne_zero _).2 (Polynomial.mem_support_iff.1 hk)) (pow_ne_zero _ hα)
  obtain ⟨m, hm, hmax⟩ := P.support.exists_max_image (fun k => e.w (T k)) (Polynomial.support_nonempty.2 hP0)
  have two : ∃ k ∈ P.support, k ≠ m ∧ e.w (T k) = e.w (T m) := by
    by_contra hne
    push_neg at hne
    have h₁ := w_sum_lt e (P.support.erase m) T (hT0 m hm) fun k hk =>
      lt_of_le_of_ne (hmax k (Finset.mem_of_mem_erase hk))
        (hne k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk))
    rw [← Finset.add_sum_erase _ _ hm, add_eq_zero_iff_neg_eq] at hsum
    rw [← hsum, e.w.map_neg] at h₁
    exact lt_irrefl _ h₁
  have fin : ∀ k ∈ P.support, ∀ k' ∈ P.support, k < k' → e.w (T k) = e.w (T k') →
      ∃ b : ℕ, 0 < b ∧ ∃ t : F, t ≠ 0 ∧ e.w α ^ b = e.w (algebraMap F (AlgebraicClosure F) t) := by
    intro k hk k' hk' hlt h
    have c₁ := Polynomial.mem_support_iff.1 hk
    have c₂ := Polynomial.mem_support_iff.1 hk'
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    refine ⟨b + 1, b.succ_pos, P.coeff k / P.coeff (k + b + 1), div_ne_zero c₁ c₂, ?_⟩
    have p₂ := (e.w.pos ((map_ne_zero (algebraMap F (AlgebraicClosure F))).2 c₂)).ne'
    have p₃ := pow_ne_zero k (e.w.pos hα).ne'
    simp only [hT, map_mul, map_pow] at h
    rw [map_div₀, map_div₀, eq_div_iff p₂]
    refine mul_right_cancel₀ p₃ ?_
    rw [h]
    ring
  obtain ⟨k, hk, hkm, h⟩ := two
  rcases lt_or_gt_of_ne hkm with hl | hl
  · exact fin k hk m hm hl h
  · exact fin m hm k hk hl h.symm

/- English proof (translation)
Establish `hv : v.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 F))` using `mem_nonZeroDivisors_of_ne_zero v.ne_bot`. Take `⟨n, hn, h⟩` from `isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_finite (ClassGroup.mk0 ⟨v.asIdeal, hv⟩))`. Rewrite `h` using `[← map_pow]`. Take `⟨a, ha⟩` from `(ClassGroup.mk0_eq_one_iff (pow_mem hv n)).1 h`. Establish `ha' : v.asIdeal ^ n = Ideal.span {a}` using `ha`.

Use `⟨a, Ideal.pow_le_self hn.ne' (ha' ▸ Ideal.mem_span_singleton_self a), fun v' h' => ?_⟩` and prove the remaining obligations. Establish `hle : v.asIdeal ^ n ≤ v'.asIdeal` using `ha' ▸ (Ideal.span_singleton_le_iff_mem _).2 h'`. Use `v'.isPrime` as an intermediate fact. Conclude with `HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top (Ideal.IsPrime.le_of_pow_le hle)).symm`.
-/
private theorem exists_mem_only {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ a ∈ v.asIdeal, ∀ v' : HeightOneSpectrum (𝓞 F), a ∈ v'.asIdeal → v' = v := by
  have hv : v.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero v.ne_bot
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_finite (ClassGroup.mk0 ⟨v.asIdeal, hv⟩))
  rw [← map_pow] at h
  obtain ⟨a, ha⟩ := (ClassGroup.mk0_eq_one_iff (pow_mem hv n)).1 h
  have ha' : v.asIdeal ^ n = Ideal.span {a} := ha
  refine ⟨a, Ideal.pow_le_self hn.ne' (ha' ▸ Ideal.mem_span_singleton_self a), fun v' h' => ?_⟩
  have hle : v.asIdeal ^ n ≤ v'.asIdeal := ha' ▸ (Ideal.span_singleton_le_iff_mem _).2 h'
  have := v'.isPrime
  exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top (Ideal.IsPrime.le_of_pow_le hle)).symm

/- English proof (translation)
Set `W : L.ι → X.Opens` to `fun a => L.U a ⊓ ⟨interior {x | UnitAt x (u a)}, isOpen_interior⟩`. Establish `hW : ∀ z a, g z ∈ L.U a → g z ∈ W a` using `fun z a h => by`. Take `⟨U, hU, hall⟩` from `(hz z a h).exists_nhds`. Conclude with `⟨h, mem_interior.2 ⟨U, hall, U.isOpen, hU⟩⟩`. Use `choose t ht using fun a => exists_unit_fnOf_eq (U := W a) (f := u a) fun x hx => interior_subset (s := {x | UnitAt x (u a)}) hx.2`.

Establish `hN` using `LB.isLB_linComb hL (fun _ : PUnit => g) (fun _ => (n : ℤ))`. Establish `e` using `cls_linComb hL (fun _ : PUnit => g) (fun _ => (n : ℤ)) hN`. Rewrite `e` using `[Fintype.sum_unique]`. Rewrite using `[cls_pull hL, ← e]`. Establish `le : ∀ J : PUnit → L.ι, LB.wchart L (fun _ : PUnit => g) J ≤ g ⁻¹ᵁ W (J PUnit.unit)` using `fun J z h => hW z _ (Set.mem_iInter.1 h PUnit.unit)`.

Use `(cls_eq_zero_iff hN).2 ⟨⟨fun J => res (le J) (pullU g _ (t (J PUnit.unit)))⟩, (isGen_iff_germ _).2 fun y J J' hJ hJ' => ?_⟩` and prove the remaining obligations. Establish `l₀ : W (J PUnit.unit) ⊓ W (J' PUnit.unit) ≤ L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)` using `inf_le_inf inf_le_left inf_le_left`. Establish `hm : g y ∈ W (J PUnit.unit) ⊓ W (J' PUnit.unit)` using `⟨le J hJ, le J' hJ'⟩`. Establish `h₀ : res (inf_le_left : W (J PUnit.unit) ⊓ W (J' PUnit.unit) ≤ _) (t (J PUnit.unit)) = res l₀ (L.g _ _) ^ n * res inf_le_right (t (J' PUnit.unit))`. Use `Units.ext (Cartier.fn_ext fun h => ?_)` and prove the remaining obligations.

Rewrite using `[Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]`. Use `((fnOf_resG inf_le_left h _).trans (ht _ _)).trans ((hu _ _ (l₀ h)).trans ?_)` and prove the remaining obligations. Conclude with `(congrArg₂ (fun a b => a ^ n * b) (fnOf_resG l₀ h _) ((fnOf_resG inf_le_right h _).trans (ht _ _))).symm`. Establish `h₁` using `congrArg (gm g y _) h₀`. Rewrite `h₁` using `[map_mul, map_pow, gm_res g y _ hm, gm_res g y _ hm, gm_res g y _ hm]`.

Use `(gm_rp₁ g y _ _ (le J) hJ _).trans (h₁.trans (Eq.symm (congrArg₂ (· * ·) ?_ (gm_rp₁ g y _ _ (le J') hJ' _))))` and prove the remaining obligations. Use `(gm_linComb L _ _ (𝟙 Z) y J J' hJ hJ').trans ?_` and prove the remaining obligations. Rewrite using `[Fintype.prod_unique, zpow_natCast, Category.id_comp]`.
-/
private theorem zsmul_cls_pull_eq_zero {X Z : Scheme.{0}} [IsIntegral X] {L : LB X} (hL : L.IsLB) (g : Z ⟶ X) (n : ℕ)
    (u : L.ι → X.functionField)
    (hu : ∀ a b (h : genericPoint X ∈ L.U a ⊓ L.U b), u a = fnOf _ h (L.g a b) ^ n * u b)
    (hz : ∀ z a, g z ∈ L.U a → UnitAt (g z) (u a)) : (n : ℤ) • cls (L.pull g) (pull_isLB hL g) = 0 := by
  let W : L.ι → X.Opens := fun a => L.U a ⊓ ⟨interior {x | UnitAt x (u a)}, isOpen_interior⟩
  have hW : ∀ z a, g z ∈ L.U a → g z ∈ W a := fun z a h => by
    obtain ⟨U, hU, hall⟩ := (hz z a h).exists_nhds
    exact ⟨h, mem_interior.2 ⟨U, hall, U.isOpen, hU⟩⟩
  choose t ht using fun a => exists_unit_fnOf_eq (U := W a) (f := u a) fun x hx =>
    interior_subset (s := {x | UnitAt x (u a)}) hx.2
  have hN := LB.isLB_linComb hL (fun _ : PUnit => g) (fun _ => (n : ℤ))
  have e := cls_linComb hL (fun _ : PUnit => g) (fun _ => (n : ℤ)) hN
  rw [Fintype.sum_unique] at e
  rw [cls_pull hL, ← e]
  have le : ∀ J : PUnit → L.ι, LB.wchart L (fun _ : PUnit => g) J ≤ g ⁻¹ᵁ W (J PUnit.unit) :=
    fun J z h => hW z _ (Set.mem_iInter.1 h PUnit.unit)
  refine (cls_eq_zero_iff hN).2 ⟨⟨fun J => res (le J) (pullU g _ (t (J PUnit.unit)))⟩,
    (isGen_iff_germ _).2 fun y J J' hJ hJ' => ?_⟩
  have l₀ : W (J PUnit.unit) ⊓ W (J' PUnit.unit) ≤ L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit) :=
    inf_le_inf inf_le_left inf_le_left
  have hm : g y ∈ W (J PUnit.unit) ⊓ W (J' PUnit.unit) := ⟨le J hJ, le J' hJ'⟩
  have h₀ : res (inf_le_left : W (J PUnit.unit) ⊓ W (J' PUnit.unit) ≤ _) (t (J PUnit.unit)) =
      res l₀ (L.g _ _) ^ n * res inf_le_right (t (J' PUnit.unit)) := by
    refine Units.ext (Cartier.fn_ext fun h => ?_)
    rw [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
    refine ((fnOf_resG inf_le_left h _).trans (ht _ _)).trans ((hu _ _ (l₀ h)).trans ?_)
    exact (congrArg₂ (fun a b => a ^ n * b) (fnOf_resG l₀ h _) ((fnOf_resG inf_le_right h _).trans (ht _ _))).symm
  have h₁ := congrArg (gm g y _) h₀
  rw [map_mul, map_pow, gm_res g y _ hm, gm_res g y _ hm, gm_res g y _ hm] at h₁
  refine (gm_rp₁ g y _ _ (le J) hJ _).trans (h₁.trans (Eq.symm (congrArg₂ (· * ·) ?_ (gm_rp₁ g y _ _ (le J') hJ' _))))
  refine (gm_linComb L _ _ (𝟙 Z) y J J' hJ hJ').trans ?_
  rw [Fintype.prod_unique, zpow_natCast, Category.id_comp]

/- English proof (translation)
Establish `HD` using `diffVanish_chiPic_of_isProjOver (f := strHom κ Z) (algebraMap_eq_strHom κ Z) (structureModule Z) hp (d := 1) (by rw [QCoh.suppDim_structureModule, hd]; rfl)`. Establish `e` using `HD.interNum_of_cls_eq_zsmul (P := fun _ => A) (Q := fun _ => LB.triv Z) (fun _ => hA) (fun _ => LB.isLB_triv Z) (fun _ => n) (fun _ => h.symm)`. Rewrite `e` using `[interNum_eq_zero_of_cls_eq_zero κ _ (fun _ => LB.isLB_triv Z) 0 rfl, Fintype.prod_unique]`. Conclude with `(mul_eq_zero.1 e.symm).resolve_left hn`.
-/
private theorem topSelf_one_eq_zero_of_torsion {κ : Type} [Field κ] {Z : Scheme.{0}} [Algebra κ Γ(Z, ⊤)]
    (hp : IsProjOver (strHom κ Z)) (hd : topologicalKrullDim Z = 1) {A : LB Z} (hA : A.IsLB) {n : ℤ} (hn : n ≠ 0)
    (h : n • cls A hA = 0) : topSelfIntersection κ A 1 = 0 := by
  have HD := diffVanish_chiPic_of_isProjOver (f := strHom κ Z) (algebraMap_eq_strHom κ Z)
    (structureModule Z) hp (d := 1) (by rw [QCoh.suppDim_structureModule, hd]; rfl)
  have e := HD.interNum_of_cls_eq_zsmul (P := fun _ => A) (Q := fun _ => LB.triv Z) (fun _ => hA)
    (fun _ => LB.isLB_triv Z) (fun _ => n) (fun _ => h.symm)
  rw [interNum_eq_zero_of_cls_eq_zero κ _ (fun _ => LB.isLB_triv Z) 0 rfl, Fintype.prod_unique] at e
  exact (mul_eq_zero.1 e.symm).resolve_left hn

open GlobalTheory.TrueGeo.RegCrit in

/- English proof (translation)
Establish `: IsProper V.p`. Take `⟨n, c, hc, h⟩` from `V.ar.isProjOver`. Use `isProper_str (𝓞 F) n` as an intermediate fact. Rewrite using `[← h]`. Use `infer_instance`.

Establish `: IsLocallyNoetherian V.X` using `LocallyOfFiniteType.isLocallyNoetherian V.p`. Assume the negation of the conclusion as `hreg`. Take `⟨z, hz, hzero⟩` from `GlobalTheory.T.exists_zero_of_inv_of_not_regular_normal V.X V.normal x f hreg`. Establish `hf0 : f ≠ 0` using `fun h => hreg (h ▸ regAt_zero x)`. Establish `hzU : z ∈ U` using `hz.mem_open U.isOpen hx`.

Take `⟨l, hlv, honly⟩` from `exists_mem_only v`. Establish `hl : l ∈ (V.p x).asIdeal` using `hxv ▸ hlv`. Establish `hlz : l ∈ (V.p z).asIdeal`. Establish `hne : (V.p z).asIdeal ≠ ⊥` using `fun h => by`. Take `⟨z', rfl⟩` from `HtGen.RegOver.mem_range_j V h`.

Conclude with `(zeroAt_iff.1 hzero).2 ((unitAt_iff (inv_ne_zero hf0)).2 ⟨hzero.regAt, (inv_inv f).symm ▸ hgen z' hzU⟩)`. Establish `hle : (V.p z).asIdeal ≤ (V.p x).asIdeal` using `(PrimeSpectrum.asIdeal_le_asIdeal _ _).2 ((PrimeSpectrum.le_iff_specializes _ _).2 (hz.map V.p.continuous))`. Establish `hmax : (V.p z).asIdeal.IsMaximal` using `Ideal.IsPrime.isMaximal (R := 𝓞 F) (V.p z).isPrime hne`. Rewrite using `[hmax.eq_of_le (V.p x).isPrime.ne_top hle]` and apply the resulting hypothesis. Take `⟨W₀, hzW, g₀, hg₀⟩` from `hzero.regAt.exists_fnOf`.

Establish `hzW' : z ∈ W₀ ⊓ U` using `⟨hzW, hzU⟩`. Take `⟨g, hg⟩ : ∃ g : Γ(V.X, W₀ ⊓ U), ∀ h, fnOf _ h g = f⁻¹` from `⟨resG V.X inf_le_left g₀, fun h => (fnOf_resG _ h _).trans hg₀⟩`. Establish `hg0 : g ≠ 0` using `fun h => inv_ne_zero hf0 (by rw [← hg (gen_mem hzW'), h, map_zero])`. Establish `hzg : z ∉ V.X.basicOpen g` using `fun h => (zeroAt_iff.1 hzero).2 (hg (gen_mem hzW') ▸ (unitAt_fnOf_iff hzW' _ g).2 h)`. Take `⟨v', e, y, yt, hv, hy, hc, hW, hn, hu⟩` from `HtGen.RegOver.exists_horizPt_over V _ z g hzW' hg0 hzg _ hlz`.

Take `rfl` from `honly v' hv`. Establish `hle` using `hf e y yt hy hc fun p hp => (hW hp).2`. Establish `hu' : below (y ≫ V.j) ∈ V.X.basicOpen g` using `hu`. Establish `hb : below (y ≫ V.j) ∈ W₀ ⊓ U` using `V.X.basicOpen_le g hu'`. Establish `ht : ⊤ ≤ (y ≫ V.j) ⁻¹ᵁ (W₀ ⊓ U)` using `fun p _ => by`.

Express the relevant statement in the definitionally equal form `(y ≫ V.j) p ∈ W₀ ⊓ U`. Rewrite using `[← hc]`. Conclude with `hW (x := spMap e.O.subtype p) trivial`. Establish `hunit : UnitAt (below (y ≫ V.j)) f⁻¹` using `hg (gen_mem hb) ▸ (unitAt_fnOf_iff hb _ g).2 hu'`. Establish `hfu : UnitAt (below (y ≫ V.j)) f` using `inv_inv f ▸ hunit.inv`.

Establish `hmul` using `OfModel.valAt_mul (y ≫ V.j) hfu.regAt hunit.regAt`. Establish `hone : TrueGeo.valAt (y ≫ V.j) (1 : V.X.functionField) = 1`. Use `OfModel.valAt_algebraMap (y ≫ V.j) 1` as an intermediate fact. Rewrite `this` using `[map_one, map_one]`. Then use the resulting hypothesis. Establish `hev` using `OfModel.eval_pull e.O.subtype (𝟙 V.X) (y ≫ V.j) yt (hc.trans (Category.comp_id _).symm) (U := W₀ ⊓ U) (W := W₀ ⊓ U) le_rfl ht hW g`.

Establish `hid : ((𝟙 V.X : V.X ⟶ V.X).appLE (W₀ ⊓ U) (W₀ ⊓ U) le_rfl).hom g = g`. Establish `: (𝟙 V.X : V.X ⟶ V.X).appLE (W₀ ⊓ U) (W₀ ⊓ U) le_rfl = 𝟙 _` using `(Category.id_comp _).trans (V.X.presheaf.map_id _)`. Rewrite using `[this]`. Both sides reduce to the same expression. Rewrite `hev` using `[hid]`.

Rewrite `hmul` using `[mul_inv_cancel₀ hf0, hone, ← hg (gen_mem hb), OfModel.valAt_fnOf _ hb ht, hev]`. Use `hn ((isUnit_eval_iff yt hW g).1 (isUnit_of_one_le e _ ?_))` and prove the remaining obligations. Establish `h₁` using `congrArg e.w hmul`. Rewrite `h₁` using `[map_one, map_mul]`. Conclude with `h₁.le.trans (mul_le_of_le_one_left (e.w.nonneg _) hle)`.
-/
private theorem regAt_of_integral_values_at {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y)
    (v : HeightOneSpectrum (𝓞 F)) (U : V.X.Opens) (f : V.X.functionField) (hgen : ∀ z : V.G, V.j z ∈ U → RegAt (V.j z) f)
    (hf : ∀ (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X),
      z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j →
      ⊤ ≤ yt ⁻¹ᵁ U → e.w (TrueGeo.valAt (z ≫ V.j) f) ≤ 1)
    (x : V.X) (hx : x ∈ U) (hxv : (V.p x).asIdeal = v.asIdeal) : RegAt x f := by
  have : IsProper V.p := by
    obtain ⟨n, c, hc, h⟩ := V.ar.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance
  have : IsLocallyNoetherian V.X := LocallyOfFiniteType.isLocallyNoetherian V.p
  by_contra hreg
  obtain ⟨z, hz, hzero⟩ := GlobalTheory.T.exists_zero_of_inv_of_not_regular_normal V.X V.normal x f hreg
  have hf0 : f ≠ 0 := fun h => hreg (h ▸ regAt_zero x)
  have hzU : z ∈ U := hz.mem_open U.isOpen hx
  obtain ⟨l, hlv, honly⟩ := exists_mem_only v
  have hl : l ∈ (V.p x).asIdeal := hxv ▸ hlv
  have hlz : l ∈ (V.p z).asIdeal := by
    have hne : (V.p z).asIdeal ≠ ⊥ := fun h => by
      obtain ⟨z', rfl⟩ := HtGen.RegOver.mem_range_j V h
      exact (zeroAt_iff.1 hzero).2 ((unitAt_iff (inv_ne_zero hf0)).2 ⟨hzero.regAt, (inv_inv f).symm ▸ hgen z' hzU⟩)
    have hle : (V.p z).asIdeal ≤ (V.p x).asIdeal :=
      (PrimeSpectrum.asIdeal_le_asIdeal _ _).2 ((PrimeSpectrum.le_iff_specializes _ _).2 (hz.map V.p.continuous))
    have hmax : (V.p z).asIdeal.IsMaximal := Ideal.IsPrime.isMaximal (R := 𝓞 F) (V.p z).isPrime hne
    rwa [hmax.eq_of_le (V.p x).isPrime.ne_top hle]
  obtain ⟨W₀, hzW, g₀, hg₀⟩ := hzero.regAt.exists_fnOf
  have hzW' : z ∈ W₀ ⊓ U := ⟨hzW, hzU⟩
  obtain ⟨g, hg⟩ : ∃ g : Γ(V.X, W₀ ⊓ U), ∀ h, fnOf _ h g = f⁻¹ :=
    ⟨resG V.X inf_le_left g₀, fun h => (fnOf_resG _ h _).trans hg₀⟩
  have hg0 : g ≠ 0 := fun h => inv_ne_zero hf0 (by rw [← hg (gen_mem hzW'), h, map_zero])
  have hzg : z ∉ V.X.basicOpen g := fun h =>
    (zeroAt_iff.1 hzero).2 (hg (gen_mem hzW') ▸ (unitAt_fnOf_iff hzW' _ g).2 h)
  obtain ⟨v', e, y, yt, hv, hy, hc, hW, hn, hu⟩ := HtGen.RegOver.exists_horizPt_over V _ z g hzW' hg0 hzg _ hlz
  obtain rfl := honly v' hv
  have hle := hf e y yt hy hc fun p hp => (hW hp).2
  have hu' : below (y ≫ V.j) ∈ V.X.basicOpen g := hu
  have hb : below (y ≫ V.j) ∈ W₀ ⊓ U := V.X.basicOpen_le g hu'
  have ht : ⊤ ≤ (y ≫ V.j) ⁻¹ᵁ (W₀ ⊓ U) := fun p _ => by
    change (y ≫ V.j) p ∈ W₀ ⊓ U
    rw [← hc]
    exact hW (x := spMap e.O.subtype p) trivial
  have hunit : UnitAt (below (y ≫ V.j)) f⁻¹ := hg (gen_mem hb) ▸ (unitAt_fnOf_iff hb _ g).2 hu'
  have hfu : UnitAt (below (y ≫ V.j)) f := inv_inv f ▸ hunit.inv
  have hmul := OfModel.valAt_mul (y ≫ V.j) hfu.regAt hunit.regAt
  have hone : TrueGeo.valAt (y ≫ V.j) (1 : V.X.functionField) = 1 := by
    have := OfModel.valAt_algebraMap (y ≫ V.j) 1
    rwa [map_one, map_one] at this
  have hev := OfModel.eval_pull e.O.subtype (𝟙 V.X) (y ≫ V.j) yt (hc.trans (Category.comp_id _).symm)
    (U := W₀ ⊓ U) (W := W₀ ⊓ U) le_rfl ht hW g
  have hid : ((𝟙 V.X : V.X ⟶ V.X).appLE (W₀ ⊓ U) (W₀ ⊓ U) le_rfl).hom g = g := by
    have : (𝟙 V.X : V.X ⟶ V.X).appLE (W₀ ⊓ U) (W₀ ⊓ U) le_rfl = 𝟙 _ :=
      (Category.id_comp _).trans (V.X.presheaf.map_id _)
    rw [this]
    rfl
  rw [hid] at hev
  rw [mul_inv_cancel₀ hf0, hone, ← hg (gen_mem hb), OfModel.valAt_fnOf _ hb ht, hev] at hmul
  refine hn ((isUnit_eval_iff yt hW g).1 (isUnit_of_one_le e _ ?_))
  have h₁ := congrArg e.w hmul
  rw [map_one, map_mul] at h₁
  exact h₁.le.trans (mul_le_of_le_one_left (e.w.nonneg _) hle)

/- English proof (translation)
Introduce `F _ _ Y V M f a l ⟨r, hr, hu, _, hf⟩ σ hσ v C hC Z i _ _ κ _ _ _ hd hZ`. Use `haveI := CoverHt.isPreimmersion_j V`. Establish `hη` using `Isom.j_gen_specializes V`. Set `ρ : V.X.functionField ≃+* V.G.functionField` to `RingEquiv.ofBijective (SmallSec.fnMap V.j hη) ⟨(SmallSec.fnMap V.j hη).injective, SmallSec.fnMap_surjective V.j hη⟩`. Establish `hρ : ∀ (U : V.X.Opens) (hU : genericPoint V.X ∈ U) (hU' : genericPoint V.G ∈ V.j ⁻¹ᵁ U) (s : Γ(V.X, U)), ρ (fnOf U hU s) = fnOf (V.j ⁻¹ᵁ U) hU' (V.j.app U s)` using `fun U hU hU' s => SmallSec.fnMap_fnOf V.j hη hU hU' s`.

Establish `hj : V.j (genericPoint V.G) = genericPoint V.X` using `(hη.antisymm (genericPoint_specializes _)).eq`. Establish `hv : ∀ (y : Sp (AlgebraicClosure F) ⟶ V.G) (g : V.G.functionField), TrueGeo.valAt (y ≫ V.j) (ρ.symm g) = TrueGeo.valAt y g` using `fun y g => (ModelFn.valAt_comp V.j hη y _).trans (congrArg _ (ρ.apply_symm_apply g))`. Establish `hrg : ∀ (z : V.G) (g : V.G.functionField), RegAt z g → RegAt (V.j z) (ρ.symm g)` using `fun z g h => (SmallSec.regAt_fnMap_iff V.j hη).1 (by`. Express the relevant statement in the definitionally equal form `RegAt z (ρ (ρ.symm g))`. Rewrite using `[ρ.apply_symm_apply])` and apply the resulting hypothesis.

Establish `hR` using `InducedIsom.isRatSec_lift V.j ρ hρ hj M.B hr`. Establish `hσ0 : σ ≠ 0` using `fun h => (hσ (genericPoint Y.X)).ne_zero (by rw [h, div_zero])`. Establish `hφ0 : V.φ σ ≠ 0` using `(map_ne_zero _).2 hσ0`. Set `s : M.B.ι → V.G.functionField` to `fun a => V.φ σ * ((r fun _ => a : V.G.functionFieldˣ) : V.G.functionField)`. Establish `mem_pull : ∀ (z : V.G) (a : M.B.ι), V.j z ∈ M.B.U a → z ∈ (M.B.pull V.j).U (fun _ => a)` using `fun z a h => Set.mem_iInter.2 fun _ => h`.

Establish `split : ∀ (x : Y.X) (a : M.B.ι), V.φ (f x) * ((r fun _ => a : V.G.functionFieldˣ) : V.G.functionField) = V.φ (f x / σ) * s a` using `fun x a => by`. Rewrite using `[map_div₀]`. Simplify using `only [s]`. Clear the denominators using the available nonvanishing facts. Establish `sU : ∀ (z : V.G) (a : M.B.ι), V.j z ∈ M.B.U a → UnitAt z (s a)` using `fun z a h => by`.

Establish `h₁` using `V.unitAt_φ (hσ (V.π z))`. Establish `h₂` using `h₁.inv.mul (hu _ _ (mem_pull z a h))`. Rewrite `h₂` using `[split, inv_mul_cancel_left₀ h₁.ne_zero]`. Then use the resulting hypothesis. Establish `pt : ∀ (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X) (a : M.B.ι), spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ M.B.U a → V.j (below z) ∈ M.B.U a`. Introduce `e z yt a e₂ hU`.

Express the relevant statement in the definitionally equal form `(z ≫ V.j) (IsLocalRing.closedPoint _) ∈ _`. Rewrite using `[← e₂]`. Conclude with `hU (Set.mem_univ _)`. Establish `sV : ∀ (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X) (a : M.B.ι), z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ M.B.U a → e.w (TrueGeo.valAt z (s a)) = Real.exp C`. Introduce `e z yt a hz e₂ hU`.

Establish `h₁ : UnitAt (below z) (V.φ (f (V.π (below z)) / σ))` using `V.unitAt_φ (hσ _)`. Establish `h₂` using `sU _ a (pt e z yt a e₂ hU)`. Establish `H : l v e ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩ = Real.log (e.w (TrueGeo.valAt z (V.φ (f (V.π (below z))) * ((r fun _ => a : V.G.functionFieldˣ) : V.G.functionField))))` using `hf v e ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩ z yt (fun _ => a) rfl e₂ hU`. Establish `H' : l v e ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩ - Real.log (e.w (TrueGeo.valAt (z ≫ V.π) (f (V.π (below z)) / σ))) = C` using `hC e ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩`. Establish `p₁` using `e.w.pos (SmallSec.valAt_ne_zero h₁)`.

Establish `p₂` using `e.w.pos (SmallSec.valAt_ne_zero h₂)`. Rewrite `H'` using `[H, ← V.valAt_φ z (hσ _).regAt, split, SmallSec.valAt_mul h₁.regAt h₂.regAt, map_mul, Real.log_mul p₁.ne' p₂.ne', add_sub_cancel_left]`. Rewrite using `[← H', Real.exp_log p₂]`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb, t, ht, hbt⟩ : ∃ b : ℕ, 0 < b ∧ ∃ t : F, t ≠ 0 ∧ ∀ (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X) (a : M.B.ι), z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ M.B.U a → e.w (TrueGeo.va …`. Distinguish the cases in `hex : ∃ (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X) (a : M.B.ι), z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) ∧ spMap e.O.subtype ≫ yt = z ≫ V.j ∧ ⊤ ≤ yt ⁻¹ᵁ M.B.U a`.

Take `⟨e₀, z₀, yt₀, a₀, h₁, h₂, h₃⟩` from `hex`. Take `⟨b, hb, t, ht, hbt⟩` from `exists_pow_w_eq e₀ (SmallSec.valAt_ne_zero (sU _ a₀ (pt e₀ z₀ yt₀ a₀ h₂ h₃)))`. Use `⟨b, hb, t, ht, fun e z yt a hz e₂ hU => ?_⟩` and prove the remaining obligations. Rewrite using `[sV e z yt a hz e₂ hU, ← sV e₀ z₀ yt₀ a₀ h₁ h₂ h₃, hbt, e.w_alg, e₀.w_alg]`. Conclude with `⟨1, one_pos, 1, one_ne_zero, fun e z yt a hz e₂ hU => (hex ⟨e, z, yt, a, hz, e₂, hU⟩).elim⟩`.

Set `c : V.G.functionField` to `Cartier.constFn (V.π ≫ Y.str) t`. Establish `cU : ∀ z : V.G, UnitAt z c` using `fun z => IndScale.unitAt_constFn _ z ht`. Establish `pU : ∀ (z : V.G) (g : V.G.functionField), UnitAt z g → UnitAt z (g ^ b)`. Introduce and unpack `z _ ⟨g, hg, rfl⟩`. Conclude with `⟨g ^ b, hg.pow b, map_pow _ _ _⟩`.

Set `g : M.B.ι → V.G.functionField` to `fun a => s a ^ b * c⁻¹`. Establish `gU : ∀ (z : V.G) (a : M.B.ι), V.j z ∈ M.B.U a → UnitAt z (g a)` using `fun z a h => (pU z _ (sU z a h)).mul (cU z).inv`. Establish `gV : ∀ (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X) (a : M.B.ι), z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ M.B.U a → e.w (TrueGeo.valAt z (g a)) = 1`. Introduce `e z yt a hz e₂ hU`. Establish `h₂` using `sU _ a (pt e z yt a e₂ hU)`.

Establish `h₃ : TrueGeo.valAt z (s a ^ b) = TrueGeo.valAt z (s a) ^ b`. Take `⟨q, hq⟩` from `h₂.regAt`. Rewrite using `[← hq, ← map_pow, OfModel.valAt_algebraMap, OfModel.valAt_algebraMap, map_pow]`. Rewrite using `[SmallSec.valAt_mul (pU _ _ h₂).regAt (cU _).inv.regAt, LineNorm.Neg.valAt_inv (cU _), h₃, IndScale.valAt_constFn _ _ z hz, map_mul, map_pow, map_inv₀, hbt e z yt a hz e₂ hU]`. Conclude with `mul_inv_cancel₀ (e.w.pos ((map_ne_zero _).2 ht)).ne'`.

Establish `g0 : ∀ a, g a ≠ 0` using `fun a => mul_ne_zero (pow_ne_zero _ (mul_ne_zero hφ0 (Units.ne_zero _))) (inv_ne_zero (cU (genericPoint V.G)).ne_zero)`. Establish `hcls` using `zsmul_cls_pull_eq_zero M.isLB i b (fun a => ρ.symm (g a)) (fun a a' h => ?_) fun z a h => ?_`. Establish `: IsProper V.p` using `(isProper_and_exists_isAmpleLB_of_isProjOver V.ar.isProjOver).1`. Establish `: IsFinite (spMap (Int.castRingHom (𝓞 F)))`. Rewrite using `[spMap, IsFinite.SpecMap_iff]`.

Conclude with `(RingHom.finite_algebraMap (A := ℤ) (B := 𝓞 F)).2 inferInstance`. Establish `: IsProper (strHom κ Z)` using `isProper_strHom κ (i ≫ V.p ≫ spMap (Int.castRingHom (𝓞 F)))`. Conclude with `topSelf_one_eq_zero_of_torsion (ProperCurve.isProjOver_of_isProper _ hd) hd _ (Int.natCast_ne_zero.2 hb.ne') hcls`. Establish `h₁ : ρ.symm ((r fun _ => a : V.G.functionFieldˣ) : V.G.functionField) = fnOf _ h (M.B.g a a') * ρ.symm ((r fun _ => a' : V.G.functionFieldˣ) : V.G.functionField)` using `hR a a' h`. Simplify using `only [g, s, map_mul, map_pow, h₁]`.

Expand and normalize the polynomial expressions, which then agree. Use `(unitAt_iff ((map_ne_zero _).2 (g0 a))).2 ⟨?_, ?_⟩` and prove the remaining obligations. Use `regAt_of_integral_values_at V v (M.B.U a) _ (fun z hz => hrg _ _ (gU z a hz).regAt) (fun e z yt hz e₂ hU => ?_) _ h (hZ z)` and prove the remaining obligations. Rewrite using `[hv, gV e z yt a hz e₂ hU]`. Rewrite using `[← map_inv₀]`.

Use `regAt_of_integral_values_at V v (M.B.U a) _ (fun z hz => hrg _ _ (gU z a hz).inv.regAt) (fun e z yt hz e₂ hU => ?_) _ h (hZ z)` and prove the remaining obligations. Rewrite using `[hv, LineNorm.Neg.valAt_inv (gU _ a (pt e z yt a e₂ hU)), map_inv₀, gV e z yt a hz e₂ hU, inv_one]`.
-/
private theorem topSelf_eq_zero_of_const : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (M : HermLB V.p) (f : Y.X → Y.Fn)
    (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ), Norms V M f a l →
    ∀ σ : Y.Fn, (∀ x : Y.X, UnitAt x (f x / σ)) → ∀ (v : HeightOneSpectrum (𝓞 F)) (C : ℝ),
    (∀ (e : Ext v) (y : AlgPt Y), l v e y - Real.log (e.w (valAt y.1 (f (below y.1) / σ))) = C) →
    ∀ (Z : Scheme.{0}) (i : Z ⟶ V.X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ] [Finite κ]
    [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 → (∀ z : Z, (V.p (i z)).asIdeal = v.asIdeal) →
    topSelfIntersection κ (M.B.pull i) 1 = 0 := by
  intro F _ _ Y V M f a l ⟨r, hr, hu, _, hf⟩ σ hσ v C hC Z i _ _ κ _ _ _ hd hZ
  haveI := CoverHt.isPreimmersion_j V
  have hη := Isom.j_gen_specializes V
  let ρ : V.X.functionField ≃+* V.G.functionField := RingEquiv.ofBijective (SmallSec.fnMap V.j hη)
    ⟨(SmallSec.fnMap V.j hη).injective, SmallSec.fnMap_surjective V.j hη⟩
  have hρ : ∀ (U : V.X.Opens) (hU : genericPoint V.X ∈ U) (hU' : genericPoint V.G ∈ V.j ⁻¹ᵁ U) (s : Γ(V.X, U)),
      ρ (fnOf U hU s) = fnOf (V.j ⁻¹ᵁ U) hU' (V.j.app U s) := fun U hU hU' s => SmallSec.fnMap_fnOf V.j hη hU hU' s
  have hj : V.j (genericPoint V.G) = genericPoint V.X := (hη.antisymm (genericPoint_specializes _)).eq
  have hv : ∀ (y : Sp (AlgebraicClosure F) ⟶ V.G) (g : V.G.functionField),
      TrueGeo.valAt (y ≫ V.j) (ρ.symm g) = TrueGeo.valAt y g :=
    fun y g => (ModelFn.valAt_comp V.j hη y _).trans (congrArg _ (ρ.apply_symm_apply g))
  have hrg : ∀ (z : V.G) (g : V.G.functionField), RegAt z g → RegAt (V.j z) (ρ.symm g) :=
    fun z g h => (SmallSec.regAt_fnMap_iff V.j hη).1 (by
      change RegAt z (ρ (ρ.symm g))
      rwa [ρ.apply_symm_apply])
  have hR := InducedIsom.isRatSec_lift V.j ρ hρ hj M.B hr
  have hσ0 : σ ≠ 0 := fun h => (hσ (genericPoint Y.X)).ne_zero (by rw [h, div_zero])
  have hφ0 : V.φ σ ≠ 0 := (map_ne_zero _).2 hσ0
  let s : M.B.ι → V.G.functionField := fun a => V.φ σ * ((r fun _ => a : V.G.functionFieldˣ) : V.G.functionField)
  have mem_pull : ∀ (z : V.G) (a : M.B.ι), V.j z ∈ M.B.U a → z ∈ (M.B.pull V.j).U (fun _ => a) :=
    fun z a h => Set.mem_iInter.2 fun _ => h
  have split : ∀ (x : Y.X) (a : M.B.ι), V.φ (f x) * ((r fun _ => a : V.G.functionFieldˣ) : V.G.functionField) =
      V.φ (f x / σ) * s a := fun x a => by
    rw [map_div₀]
    simp only [s]
    field_simp
  have sU : ∀ (z : V.G) (a : M.B.ι), V.j z ∈ M.B.U a → UnitAt z (s a) := fun z a h => by
    have h₁ := V.unitAt_φ (hσ (V.π z))
    have h₂ := h₁.inv.mul (hu _ _ (mem_pull z a h))
    rwa [split, inv_mul_cancel_left₀ h₁.ne_zero] at h₂
  have pt : ∀ (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X) (a : M.B.ι),
      spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ M.B.U a → V.j (below z) ∈ M.B.U a := by
    intro e z yt a e₂ hU
    change (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ _
    rw [← e₂]
    exact hU (Set.mem_univ _)
  have sV : ∀ (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X) (a : M.B.ι),
      z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j →
      ⊤ ≤ yt ⁻¹ᵁ M.B.U a → e.w (TrueGeo.valAt z (s a)) = Real.exp C := by
    intro e z yt a hz e₂ hU
    have h₁ : UnitAt (below z) (V.φ (f (V.π (below z)) / σ)) := V.unitAt_φ (hσ _)
    have h₂ := sU _ a (pt e z yt a e₂ hU)
    have H : l v e ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩ = Real.log (e.w (TrueGeo.valAt z
        (V.φ (f (V.π (below z))) * ((r fun _ => a : V.G.functionFieldˣ) : V.G.functionField)))) :=
      hf v e ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩ z yt (fun _ => a) rfl e₂ hU
    have H' : l v e ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩ -
        Real.log (e.w (TrueGeo.valAt (z ≫ V.π) (f (V.π (below z)) / σ))) = C :=
      hC e ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩
    have p₁ := e.w.pos (SmallSec.valAt_ne_zero h₁)
    have p₂ := e.w.pos (SmallSec.valAt_ne_zero h₂)
    rw [H, ← V.valAt_φ z (hσ _).regAt, split, SmallSec.valAt_mul h₁.regAt h₂.regAt, map_mul,
      Real.log_mul p₁.ne' p₂.ne', add_sub_cancel_left] at H'
    rw [← H', Real.exp_log p₂]
  obtain ⟨b, hb, t, ht, hbt⟩ : ∃ b : ℕ, 0 < b ∧ ∃ t : F, t ≠ 0 ∧
      ∀ (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X) (a : M.B.ι),
      z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j →
      ⊤ ≤ yt ⁻¹ᵁ M.B.U a → e.w (TrueGeo.valAt z (s a)) ^ b = e.w (algebraMap F (AlgebraicClosure F) t) := by
    by_cases hex : ∃ (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X) (a : M.B.ι),
        z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) ∧ spMap e.O.subtype ≫ yt = z ≫ V.j ∧
        ⊤ ≤ yt ⁻¹ᵁ M.B.U a
    · obtain ⟨e₀, z₀, yt₀, a₀, h₁, h₂, h₃⟩ := hex
      obtain ⟨b, hb, t, ht, hbt⟩ := exists_pow_w_eq e₀ (SmallSec.valAt_ne_zero (sU _ a₀ (pt e₀ z₀ yt₀ a₀ h₂ h₃)))
      refine ⟨b, hb, t, ht, fun e z yt a hz e₂ hU => ?_⟩
      rw [sV e z yt a hz e₂ hU, ← sV e₀ z₀ yt₀ a₀ h₁ h₂ h₃, hbt, e.w_alg, e₀.w_alg]
    · exact ⟨1, one_pos, 1, one_ne_zero, fun e z yt a hz e₂ hU => (hex ⟨e, z, yt, a, hz, e₂, hU⟩).elim⟩
  let c : V.G.functionField := Cartier.constFn (V.π ≫ Y.str) t
  have cU : ∀ z : V.G, UnitAt z c := fun z => IndScale.unitAt_constFn _ z ht
  have pU : ∀ (z : V.G) (g : V.G.functionField), UnitAt z g → UnitAt z (g ^ b) := by
    rintro z _ ⟨g, hg, rfl⟩
    exact ⟨g ^ b, hg.pow b, map_pow _ _ _⟩
  let g : M.B.ι → V.G.functionField := fun a => s a ^ b * c⁻¹
  have gU : ∀ (z : V.G) (a : M.B.ι), V.j z ∈ M.B.U a → UnitAt z (g a) :=
    fun z a h => (pU z _ (sU z a h)).mul (cU z).inv
  have gV : ∀ (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X) (a : M.B.ι),
      z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j →
      ⊤ ≤ yt ⁻¹ᵁ M.B.U a → e.w (TrueGeo.valAt z (g a)) = 1 := by
    intro e z yt a hz e₂ hU
    have h₂ := sU _ a (pt e z yt a e₂ hU)
    have h₃ : TrueGeo.valAt z (s a ^ b) = TrueGeo.valAt z (s a) ^ b := by
      obtain ⟨q, hq⟩ := h₂.regAt
      rw [← hq, ← map_pow, OfModel.valAt_algebraMap, OfModel.valAt_algebraMap, map_pow]
    rw [SmallSec.valAt_mul (pU _ _ h₂).regAt (cU _).inv.regAt, LineNorm.Neg.valAt_inv (cU _), h₃,
      IndScale.valAt_constFn _ _ z hz, map_mul, map_pow, map_inv₀, hbt e z yt a hz e₂ hU]
    exact mul_inv_cancel₀ (e.w.pos ((map_ne_zero _).2 ht)).ne'
  have g0 : ∀ a, g a ≠ 0 := fun a =>
    mul_ne_zero (pow_ne_zero _ (mul_ne_zero hφ0 (Units.ne_zero _))) (inv_ne_zero (cU (genericPoint V.G)).ne_zero)
  have hcls := zsmul_cls_pull_eq_zero M.isLB i b (fun a => ρ.symm (g a)) (fun a a' h => ?_) fun z a h => ?_
  · have : IsProper V.p := (isProper_and_exists_isAmpleLB_of_isProjOver V.ar.isProjOver).1
    have : IsFinite (spMap (Int.castRingHom (𝓞 F))) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := 𝓞 F)).2 inferInstance
    have : IsProper (strHom κ Z) := isProper_strHom κ (i ≫ V.p ≫ spMap (Int.castRingHom (𝓞 F)))
    exact topSelf_one_eq_zero_of_torsion (ProperCurve.isProjOver_of_isProper _ hd) hd _
      (Int.natCast_ne_zero.2 hb.ne') hcls
  · have h₁ : ρ.symm ((r fun _ => a : V.G.functionFieldˣ) : V.G.functionField) =
        fnOf _ h (M.B.g a a') * ρ.symm ((r fun _ => a' : V.G.functionFieldˣ) : V.G.functionField) := hR a a' h
    simp only [g, s, map_mul, map_pow, h₁]
    ring
  · refine (unitAt_iff ((map_ne_zero _).2 (g0 a))).2 ⟨?_, ?_⟩
    · refine regAt_of_integral_values_at V v (M.B.U a) _ (fun z hz => hrg _ _ (gU z a hz).regAt)
        (fun e z yt hz e₂ hU => ?_) _ h (hZ z)
      rw [hv, gV e z yt a hz e₂ hU]
    · rw [← map_inv₀]
      refine regAt_of_integral_values_at V v (M.B.U a) _ (fun z hz => hrg _ _ (gU z a hz).inv.regAt)
        (fun e z yt hz e₂ hU => ?_) _ h (hZ z)
      rw [hv, LineNorm.Neg.valAt_inv (gU _ a (pt e z yt a e₂ hU)), map_inv₀, gV e z yt a hz e₂ hU, inv_one]

end GlobalTheory.CoverNorm.ConstDeg

end

/- English proof (translation)
The claim follows from `GlobalTheory.CoverNorm.ConstDeg.topSelf_eq_zero_of_const`.
-/
theorem _root_.GlobalTheory.T.norm_constant_divisor_local_height : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (M : HermLB V.p) (f : Y.X → Y.Fn)
    (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ), Norms V M f a l →
    ∀ σ : Y.Fn, (∀ x : Y.X, UnitAt x (f x / σ)) → ∀ (v : HeightOneSpectrum (𝓞 F)) (C : ℝ),
    (∀ (e : Ext v) (y : AlgPt Y), l v e y - Real.log (e.w (valAt y.1 (f (below y.1) / σ))) = C) →
    ∀ (Z : Scheme.{0}) (i : Z ⟶ V.X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ] [Finite κ]
    [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 → (∀ z : Z, (V.p (i z)).asIdeal = v.asIdeal) →
    topSelfIntersection κ (M.B.pull i) 1 = 0 :=
  GlobalTheory.CoverNorm.ConstDeg.topSelf_eq_zero_of_const

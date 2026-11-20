import Mathlib
import GroundTheory.PAdicHodge.RobbaSeries
import GroundTheory.PAdicHodge.HighIndexSingleZeroOne
import GroundTheory.PAdicHodge.RobbaBounded
import GroundTheory.PAdicHodge.RobbaNewton
import GroundTheory.PAdicHodge.RobbaClosed
import GroundTheory.PAdicHodge.RobbaUnitApprox
import GroundTheory.PAdicHodge.RobbaMittagLeffler
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace Laurent

def IsUnitOn (a : ℤ → K) (α β : ℝ) : Prop :=
  (∀ ρ ∈ Set.Icc α β, ConvergesAt a ρ) ∧ a ≠ 0 ∧ lowIndex a α = highIndex a β

variable {a b : ℤ → K} {r s : ℝ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, ha, he⟩`. Conclude with `AnnulusRing.isUnit_of_lowIndex_eq_highIndex hr _ (fun e => ha (congrArg AnnulusRing.coeff e)) he`. Introduce `hu`. Use `⟨fun ρ hρ => h ρ hρ (hr.trans_le hρ.1), fun e => ?_, AnnulusRing.lowIndex_eq_highIndex_of_isUnit hr hu⟩` and prove the remaining obligations.

Establish `: (⟨a, h⟩ : AnnulusRing K (Set.Icc r s)) = 0` using `AnnulusRing.ext e`. Rewrite `hu` using `[this]`. Conclude with `not_isUnit_zero hu`.
-/
theorem isUnitOn_iff [Fact (∃ ρ ∈ Set.Icc r s, 0 < ρ)] (hr : 0 < r)
    (h : ∀ ρ ∈ Set.Icc r s, 0 < ρ → ConvergesAt a ρ) :
    IsUnitOn a r s ↔ IsUnit (⟨a, h⟩ : AnnulusRing K (Set.Icc r s)) := by
  constructor
  · rintro ⟨-, ha, he⟩
    exact AnnulusRing.isUnit_of_lowIndex_eq_highIndex hr _ (fun e => ha (congrArg AnnulusRing.coeff e)) he
  · intro hu
    refine ⟨fun ρ hρ => h ρ hρ (hr.trans_le hρ.1), fun e => ?_,
      AnnulusRing.lowIndex_eq_highIndex_of_isUnit hr hu⟩
    have : (⟨a, h⟩ : AnnulusRing K (Set.Icc r s)) = 0 := AnnulusRing.ext e
    rw [this] at hu
    exact not_isUnit_zero hu

/- English proof (translation)
Use `haveI : Fact (∃ ρ ∈ Set.Icc r s, 0 < ρ) := ⟨⟨r, ⟨le_rfl, hrs⟩, hr⟩⟩`. Establish `e : (⟨a, fun ρ hρ _ => ha ρ hρ⟩ : AnnulusRing K (Set.Icc r s)) * ⟨b, fun ρ hρ _ => hb ρ hρ⟩ = 1` using `AnnulusRing.ext hab`. Conclude with `⟨(isUnitOn_iff hr _).2 ⟨⟨_, _, e, by rw [mul_comm]; exact e⟩, rfl⟩, (isUnitOn_iff hr _).2 ⟨⟨_, _, by rw [mul_comm]; exact e, e⟩, rfl⟩⟩`.
-/
theorem isUnitOn_of_cmul_eq_one (hr : 0 < r) (hrs : r ≤ s) (ha : ∀ ρ ∈ Set.Icc r s, ConvergesAt a ρ)
    (hb : ∀ ρ ∈ Set.Icc r s, ConvergesAt b ρ) (hab : cmul a b = Pi.single 0 1) :
    IsUnitOn a r s ∧ IsUnitOn b r s := by
  haveI : Fact (∃ ρ ∈ Set.Icc r s, 0 < ρ) := ⟨⟨r, ⟨le_rfl, hrs⟩, hr⟩⟩
  have e : (⟨a, fun ρ hρ _ => ha ρ hρ⟩ : AnnulusRing K (Set.Icc r s)) * ⟨b, fun ρ hρ _ => hb ρ hρ⟩ = 1 :=
    AnnulusRing.ext hab
  exact ⟨(isUnitOn_iff hr _).2 ⟨⟨_, _, e, by rw [mul_comm]; exact e⟩, rfl⟩,
    (isUnitOn_iff hr _).2 ⟨⟨_, _, by rw [mul_comm]; exact e, e⟩, rfl⟩⟩

/- English proof (translation)
Use `haveI : Fact (∃ ρ ∈ Set.Icc r s, 0 < ρ) := ⟨⟨r, ⟨le_rfl, hrs⟩, hr⟩⟩`. Establish `ha'` using `(isUnitOn_iff hr fun ρ hρ _ => ha.1 ρ hρ).1 ha`. Establish `hb'` using `(isUnitOn_iff hr fun ρ hρ _ => hb.1 ρ hρ).1 hb`. Conclude with `(isUnitOn_iff hr fun ρ hρ h0 => (ha.1 ρ hρ).cmul h0 (hb.1 ρ hρ)).2 (ha'.mul hb')`.
-/
theorem IsUnitOn.cmul (hr : 0 < r) (hrs : r ≤ s) (ha : IsUnitOn a r s) (hb : IsUnitOn b r s) :
    IsUnitOn (Laurent.cmul a b) r s := by
  haveI : Fact (∃ ρ ∈ Set.Icc r s, 0 < ρ) := ⟨⟨r, ⟨le_rfl, hrs⟩, hr⟩⟩
  have ha' := (isUnitOn_iff hr fun ρ hρ _ => ha.1 ρ hρ).1 ha
  have hb' := (isUnitOn_iff hr fun ρ hρ _ => hb.1 ρ hρ).1 hb
  exact (isUnitOn_iff hr fun ρ hρ h0 => (ha.1 ρ hρ).cmul h0 (hb.1 ρ hρ)).2 (ha'.mul hb')

/- English proof (translation)
Establish `hspec : ∀ ρ ∈ Set.Icc r s, ConvergesAt (invDom a (lowIndex a r)) ρ ∧ Laurent.cmul a (invDom a (lowIndex a r)) = Pi.single 0 1` using `fun ρ hρ => invDom_spec (hr.trans_le hρ.1) (ha.1 ρ hρ) ha.2.1 (unique_dominant_of_lowIndex_eq_highIndex hr ha.1 ha.2.1 ha.2.2 hρ)`. Establish `h1` using `(hspec r ⟨le_rfl, hrs⟩).2`. Conclude with `⟨(isUnitOn_of_cmul_eq_one hr hrs ha.1 (fun ρ hρ => (hspec ρ hρ).1) h1).2, h1⟩`.
-/
theorem IsUnitOn.inv (hr : 0 < r) (hrs : r ≤ s) (ha : IsUnitOn a r s) :
    IsUnitOn (invDom a (lowIndex a r)) r s ∧
      Laurent.cmul a (invDom a (lowIndex a r)) = Pi.single 0 1 := by
  have hspec : ∀ ρ ∈ Set.Icc r s, ConvergesAt (invDom a (lowIndex a r)) ρ ∧
      Laurent.cmul a (invDom a (lowIndex a r)) = Pi.single 0 1 := fun ρ hρ =>
    invDom_spec (hr.trans_le hρ.1) (ha.1 ρ hρ) ha.2.1
      (unique_dominant_of_lowIndex_eq_highIndex hr ha.1 ha.2.1 ha.2.2 hρ)
  have h1 := (hspec r ⟨le_rfl, hrs⟩).2
  exact ⟨(isUnitOn_of_cmul_eq_one hr hrs ha.1 (fun ρ hρ => (hspec ρ hρ).1) h1).2, h1⟩

/- English proof (translation)
The claim follows from `(isUnitOn_of_cmul_eq_one hr hrs (fun ρ _ => convergesAt_single 0 1 ρ) (fun ρ _ => convergesAt_single 0 1 ρ) (cmul_single_zero_one _)).1`.
-/
theorem isUnitOn_single_zero_one (hr : 0 < r) (hrs : r ≤ s) :
    IsUnitOn (Pi.single 0 (1 : K)) r s :=
  (isUnitOn_of_cmul_eq_one hr hrs (fun ρ _ => convergesAt_single 0 1 ρ)
    (fun ρ _ => convergesAt_single 0 1 ρ) (cmul_single_zero_one _)).1

/- English proof (translation)
Establish `hv : ConvergesAt (z - Pi.single 0 1) ρ` using `hz.sub hρ (convergesAt_single 0 1 ρ)`. Establish `hw : ∀ m : ℤ, ‖(z - (Pi.single 0 (1 : K) : ℤ → K)) m‖ * ρ ^ m < 1` using `fun m => (hv.le_gaussNorm m).trans_lt h1`. Establish `hz0 : ‖z 0‖ = 1`. Use `hw 0` as an intermediate fact. Simplify using `only [Pi.sub_apply, Pi.single_eq_same, zpow_zero, mul_one] at this`.

Establish `e : z 0 = 1 + (z 0 - 1)` using `by ring`. Rewrite using `[e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact this.ne'), norm_one, max_eq_left this.le]`. Use `le_antisymm (gaussNorm_le fun m => ?_) ?_` and prove the remaining obligations. Distinguish the cases in `hm : m = 0`. Substitute `hm` using the available equality.

Rewrite using `[hz0, zpow_zero, mul_one]`. Use `hw m` as an intermediate fact. Simplify using `only [Pi.sub_apply, Pi.single_eq_of_ne hm, sub_zero] at this`. Conclude with `this.le`. Use `hz.le_gaussNorm 0` as an intermediate fact.

Rewrite `this` using `[hz0, zpow_zero, mul_one]`. Then use the resulting hypothesis.
-/
theorem gaussNorm_eq_one_of_sub_lt_one {z : ℤ → K} {ρ : ℝ} (hρ : 0 < ρ) (hz : ConvergesAt z ρ)
    (h1 : gaussNorm (z - Pi.single 0 1) ρ < 1) : gaussNorm z ρ = 1 := by
  have hv : ConvergesAt (z - Pi.single 0 1) ρ := hz.sub hρ (convergesAt_single 0 1 ρ)
  have hw : ∀ m : ℤ, ‖(z - (Pi.single 0 (1 : K) : ℤ → K)) m‖ * ρ ^ m < 1 := fun m =>
    (hv.le_gaussNorm m).trans_lt h1
  have hz0 : ‖z 0‖ = 1 := by
    have := hw 0
    simp only [Pi.sub_apply, Pi.single_eq_same, zpow_zero, mul_one] at this
    have e : z 0 = 1 + (z 0 - 1) := by ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact this.ne'),
      norm_one, max_eq_left this.le]
  refine le_antisymm (gaussNorm_le fun m => ?_) ?_
  · by_cases hm : m = 0
    · subst hm; rw [hz0, zpow_zero, mul_one]
    · have := hw m
      simp only [Pi.sub_apply, Pi.single_eq_of_ne hm, sub_zero] at this
      exact this.le
  · have := hz.le_gaussNorm 0; rwa [hz0, zpow_zero, mul_one] at this

/- English proof (translation)
Establish `hρN : 0 < ρ ^ N` using `zpow_pos hρ N`. Establish `hw : ∀ m, ‖(b - a) m‖ * ρ ^ m < ‖a N‖ * ρ ^ N` using `fun m => (hδ.le_gaussNorm m).trans_lt hsmall`. Establish `e1 : ‖b N‖ * ρ ^ N = ‖a N‖ * ρ ^ N`. Establish `e : b N = a N + (b - a) N` using `by simp`. Establish `h1 : ‖(b - a) N‖ < ‖a N‖`.

Rewrite using `[← mul_lt_mul_iff_of_pos_right hρN]`. Conclude with `hw N`. Rewrite using `[e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1.ne', max_eq_left h1.le]`. Use `⟨e1, fun m hm => ?_⟩` and prove the remaining obligations. Rewrite using `[e1]`.

Establish `e : b m = a m + (b - a) m` using `by simp`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem unique_dominant_of_perturb {ρ : ℝ} (hρ : 0 < ρ) {N : ℤ}
    (hN : ∀ m, m ≠ N → ‖a m‖ * ρ ^ m < ‖a N‖ * ρ ^ N) (hδ : ConvergesAt (b - a) ρ)
    (hsmall : gaussNorm (b - a) ρ < ‖a N‖ * ρ ^ N) :
    ‖b N‖ * ρ ^ N = ‖a N‖ * ρ ^ N ∧ ∀ m, m ≠ N → ‖b m‖ * ρ ^ m < ‖b N‖ * ρ ^ N := by
  have hρN : 0 < ρ ^ N := zpow_pos hρ N
  have hw : ∀ m, ‖(b - a) m‖ * ρ ^ m < ‖a N‖ * ρ ^ N := fun m =>
    (hδ.le_gaussNorm m).trans_lt hsmall
  have e1 : ‖b N‖ * ρ ^ N = ‖a N‖ * ρ ^ N := by
    have e : b N = a N + (b - a) N := by simp
    have h1 : ‖(b - a) N‖ < ‖a N‖ := by
      rw [← mul_lt_mul_iff_of_pos_right hρN]; exact hw N
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1.ne', max_eq_left h1.le]
  refine ⟨e1, fun m hm => ?_⟩
  rw [e1]
  have e : b m = a m + (b - a) m := by simp
  rw [e]
  calc ‖a m + (b - a) m‖ * ρ ^ m ≤ max ‖a m‖ ‖(b - a) m‖ * ρ ^ m :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) (by positivity)
    _ = max (‖a m‖ * ρ ^ m) (‖(b - a) m‖ * ρ ^ m) := max_mul_of_nonneg _ _ (by positivity)
    _ < ‖a N‖ * ρ ^ N := max_lt (hN m hm) (hw m)

/- English proof (translation)
Establish `hg : gaussNorm a ρ = ‖a N‖ * ρ ^ N` using `le_antisymm (gaussNorm_le fun m => by`. Distinguish the cases in `hm : m = N`. Substitute `hm` using the available equality. Conclude with `le_rfl`. Conclude with `(hN m hm).le) (h.le_gaussNorm N)`.

Establish `hdom : domSet a ρ = {N}`. Use extensionality with `m`. Simplify using `only [domSet, Set.mem_setOf_eq, hg, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `e`.

Assume the negation of the conclusion as `hm`. Conclude with `(hN m hm).ne e`. Introduce and unpack `rfl`. Both sides reduce to the same expression. Conclude with `⟨by rw [lowIndex, hdom, csInf_singleton], by rw [highIndex, hdom, csSup_singleton]⟩`.
-/
theorem low_high_of_unique_dominant {ρ : ℝ} (hρ : 0 < ρ) (h : ConvergesAt a ρ) {N : ℤ}
    (hN : ∀ m, m ≠ N → ‖a m‖ * ρ ^ m < ‖a N‖ * ρ ^ N) (ha : a N ≠ 0) :
    lowIndex a ρ = N ∧ highIndex a ρ = N := by
  have hg : gaussNorm a ρ = ‖a N‖ * ρ ^ N :=
    le_antisymm (gaussNorm_le fun m => by
      by_cases hm : m = N
      · subst hm; exact le_rfl
      · exact (hN m hm).le) (h.le_gaussNorm N)
  have hdom : domSet a ρ = {N} := by
    ext m
    simp only [domSet, Set.mem_setOf_eq, hg, Set.mem_singleton_iff]
    constructor
    · intro e; by_contra hm; exact (hN m hm).ne e
    · rintro rfl; rfl
  exact ⟨by rw [lowIndex, hdom, csInf_singleton], by rw [highIndex, hdom, csSup_singleton]⟩

section Step

/- English proof (translation)
Establish `hrt : r ≤ t₁` using `h0.trans h01`. Take `⟨hvi, hvvi⟩` from `hv.inv hr hrt`. Use `set vi := invDom v (lowIndex v r)`. Use `set y := Laurent.cmul w vi with hydef`. Establish `hy : IsUnitOn y r t₁` using `hw.cmul hr hrt hvi`.

Take `⟨W, V, hWV, hWV1, happrox⟩` from `exists_unit_approx hr h0 h01 h1 hq' hbig hn₀ hy.1 hy.2.1 hy.2.2 hδ`. Take `⟨hyi, hyyi⟩` from `hy.inv hr hrt`. Use `set yi := invDom y (lowIndex y r)`. Establish `hWunit : ∀ s, r ≤ s → s < 1 → IsUnitOn W r s ∧ IsUnitOn V r s` using `fun s hs hs1 => isUnitOn_of_cmul_eq_one hr hs (fun ρ hρ => (hWV ρ hρ.1 (hρ.2.trans_lt hs1)).1) (fun ρ hρ => (hWV ρ hρ.1 (hρ.2.trans_lt hs1)).2) hWV1`. Establish `hWt` using `hWunit t₁ hrt h1`.

Use `⟨Laurent.cmul d' W, W, Laurent.cmul yi W, fun ρ h1' h2' => (hd' ρ (hr.trans_le h1')).cmul (hr.trans_le h1') (hWV ρ h1' h2').1, fun s hs hs1 => (hWunit s hs hs1).1, rfl, hyi.cmul hr hrt hWt.1, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `all_goals haveI : Fact (∃ ρ ∈ Set.Icc r t₁, 0 < ρ) := ⟨⟨r, ⟨le_rfl, hrt⟩, hr⟩⟩`. Use `all_goals`. Set `I` to `Set.Icc r t₁`. Set `ed : AnnulusRing K I` to `⟨d, fun ρ _ h => hd ρ h⟩`.

Set `ed' : AnnulusRing K I` to `⟨d', fun ρ _ h => hd' ρ h⟩`. Set `ev : AnnulusRing K I` to `⟨v, fun ρ hρ _ => hv.1 ρ hρ⟩`. Set `evi : AnnulusRing K I` to `⟨vi, fun ρ hρ _ => hvi.1 ρ hρ⟩`. Set `ew : AnnulusRing K I` to `⟨w, fun ρ hρ _ => hw.1 ρ hρ⟩`. Set `eyi : AnnulusRing K I` to `⟨yi, fun ρ hρ _ => hyi.1 ρ hρ⟩`.

Set `eW : AnnulusRing K I` to `⟨W, fun ρ hρ _ => hWt.1.1 ρ hρ⟩`. Set `eV : AnnulusRing K I` to `⟨V, fun ρ hρ _ => hWt.2.1 ρ hρ⟩`. Establish `k1 : ev * evi = 1` using `AnnulusRing.ext hvvi`. Establish `k2 : (ew * evi) * eyi = 1` using `AnnulusRing.ext hyyi`. Establish `k3 : eW * eV = 1` using `AnnulusRing.ext hWV1`.

Establish `k4 : ed * ev = ed'` using `AnnulusRing.ext hvd`. Establish `: ed' * eW = (ed * ew) * (eyi * eW)`. Take the linear combination `(ed * eW * ew * eyi) * k1 - (ed * eW * ev) * k2 - eW * k4`. Rewrite using `[hDw]`. Conclude with `congrArg AnnulusRing.coeff this`.

Introduce `ρ hρ`. Establish `hρ0 : 0 < ρ` using `hr.trans_le hρ.1`. Establish `hρ1 : ρ ∈ Set.Icc r t₁` using `⟨hρ.1, hρ.2.trans h01⟩`. Establish `hB'` using `happrox ρ hρ`. Establish `hyV : ConvergesAt (Laurent.cmul y V) ρ` using `(hy.1 ρ hρ1).cmul hρ0 (hWt.2.1 ρ hρ1)`.

Establish `hz : ConvergesAt (Laurent.cmul yi W) ρ` using `(hyi.1 ρ hρ1).cmul hρ0 (hWt.1.1 ρ hρ1)`. Establish `he : ConvergesAt (Laurent.cmul y V - Pi.single 0 1) ρ` using `hyV.sub hρ0 (convergesAt_single 0 1 ρ)`. Establish `hyV1 : gaussNorm (Laurent.cmul y V) ρ = 1` using `gaussNorm_eq_one_of_sub_lt_one hρ0 hyV (hB'.trans_lt hB)`. Establish `r1 : (eyi * eW) * ((ew * evi) * eV) = 1`. Take the linear combination `(eW * eV) * k2 + k3`.

Establish `r2 : (eyi * eW) - 1 = -((eyi * eW) * ((ew * evi) * eV - 1))`. Take the linear combination `r1`. Establish `c1 : Laurent.cmul (Laurent.cmul yi W) (Laurent.cmul y V) = Pi.single 0 1` using `congrArg AnnulusRing.coeff r1`. Establish `c2 : Laurent.cmul yi W - Pi.single 0 1 = -Laurent.cmul (Laurent.cmul yi W) (Laurent.cmul y V - Pi.single 0 1)` using `congrArg AnnulusRing.coeff r2`. Establish `hne : (Pi.single 0 (1 : K) : ℤ → K) ≠ 0` using `fun h0 => by simpa using congrFun h0 0`.

Establish `hz0 : Laurent.cmul yi W ≠ 0` using `fun h0 => hne (by rw [← c1, h0, zero_cmul])`. Establish `hyV0 : Laurent.cmul y V ≠ 0` using `fun h0 => hne (by rw [← c1, h0, cmul_zero])`. Establish `hz1 : gaussNorm (Laurent.cmul yi W) ρ = 1`. Use `gaussNorm_cmul hρ0 hz hyV hz0 hyV0` as an intermediate fact. Rewrite `this` using `[c1, gaussNorm_single_zero_one hρ0, hyV1, mul_one]`.

Conclude with `this.symm`. Rewrite using `[c2, gaussNorm_neg]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem divisor_step {t₀ t₁ q' δ : ℝ} {n₀ : ℕ} (hr : 0 < r) (h0 : r ≤ t₀) (h01 : t₀ ≤ t₁)
    (h1 : t₁ < 1) (hq' : 0 < q') (hbig : ∀ x : K, 1 < ‖x‖ → 1 ≤ q' * ‖x‖)
    (hn₀ : q' ≤ t₁ ^ n₀) (hδ : 0 < δ) (hB : max ((t₀ / t₁) ^ n₀) δ < 1)
    {d d' v D w : ℤ → K} (hd : ∀ ρ, 0 < ρ → ConvergesAt d ρ)
    (hd' : ∀ ρ, 0 < ρ → ConvergesAt d' ρ) (hv : IsUnitOn v r t₁) (hvd : Laurent.cmul d v = d')
    (hD : ∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt D ρ) (hw : IsUnitOn w r t₁)
    (hDw : D = Laurent.cmul d w) :
    ∃ D' w' z : ℤ → K, (∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt D' ρ) ∧
      (∀ s, r ≤ s → s < 1 → IsUnitOn w' r s) ∧ D' = Laurent.cmul d' w' ∧
      IsUnitOn z r t₁ ∧ D' = Laurent.cmul D z ∧
      ∀ ρ ∈ Set.Icc r t₀, gaussNorm (z - Pi.single 0 1) ρ ≤ max ((t₀ / t₁) ^ n₀) δ := by
  have hrt : r ≤ t₁ := h0.trans h01
  obtain ⟨hvi, hvvi⟩ := hv.inv hr hrt
  set vi := invDom v (lowIndex v r)
  set y := Laurent.cmul w vi with hydef
  have hy : IsUnitOn y r t₁ := hw.cmul hr hrt hvi
  obtain ⟨W, V, hWV, hWV1, happrox⟩ :=
    exists_unit_approx hr h0 h01 h1 hq' hbig hn₀ hy.1 hy.2.1 hy.2.2 hδ
  obtain ⟨hyi, hyyi⟩ := hy.inv hr hrt
  set yi := invDom y (lowIndex y r)
  have hWunit : ∀ s, r ≤ s → s < 1 → IsUnitOn W r s ∧ IsUnitOn V r s := fun s hs hs1 =>
    isUnitOn_of_cmul_eq_one hr hs (fun ρ hρ => (hWV ρ hρ.1 (hρ.2.trans_lt hs1)).1)
      (fun ρ hρ => (hWV ρ hρ.1 (hρ.2.trans_lt hs1)).2) hWV1
  have hWt := hWunit t₁ hrt h1
  refine ⟨Laurent.cmul d' W, W, Laurent.cmul yi W, fun ρ h1' h2' =>
    (hd' ρ (hr.trans_le h1')).cmul (hr.trans_le h1') (hWV ρ h1' h2').1,
    fun s hs hs1 => (hWunit s hs hs1).1, rfl, hyi.cmul hr hrt hWt.1, ?_, ?_⟩
  all_goals haveI : Fact (∃ ρ ∈ Set.Icc r t₁, 0 < ρ) := ⟨⟨r, ⟨le_rfl, hrt⟩, hr⟩⟩
  all_goals
    let I := Set.Icc r t₁
    let ed : AnnulusRing K I := ⟨d, fun ρ _ h => hd ρ h⟩
    let ed' : AnnulusRing K I := ⟨d', fun ρ _ h => hd' ρ h⟩
    let ev : AnnulusRing K I := ⟨v, fun ρ hρ _ => hv.1 ρ hρ⟩
    let evi : AnnulusRing K I := ⟨vi, fun ρ hρ _ => hvi.1 ρ hρ⟩
    let ew : AnnulusRing K I := ⟨w, fun ρ hρ _ => hw.1 ρ hρ⟩
    let eyi : AnnulusRing K I := ⟨yi, fun ρ hρ _ => hyi.1 ρ hρ⟩
    let eW : AnnulusRing K I := ⟨W, fun ρ hρ _ => hWt.1.1 ρ hρ⟩
    let eV : AnnulusRing K I := ⟨V, fun ρ hρ _ => hWt.2.1 ρ hρ⟩
    have k1 : ev * evi = 1 := AnnulusRing.ext hvvi
    have k2 : (ew * evi) * eyi = 1 := AnnulusRing.ext hyyi
    have k3 : eW * eV = 1 := AnnulusRing.ext hWV1
    have k4 : ed * ev = ed' := AnnulusRing.ext hvd
  ·
    have : ed' * eW = (ed * ew) * (eyi * eW) := by
      linear_combination (ed * eW * ew * eyi) * k1 - (ed * eW * ev) * k2 - eW * k4
    rw [hDw]
    exact congrArg AnnulusRing.coeff this
  · intro ρ hρ
    have hρ0 : 0 < ρ := hr.trans_le hρ.1
    have hρ1 : ρ ∈ Set.Icc r t₁ := ⟨hρ.1, hρ.2.trans h01⟩
    have hB' := happrox ρ hρ
    have hyV : ConvergesAt (Laurent.cmul y V) ρ := (hy.1 ρ hρ1).cmul hρ0 (hWt.2.1 ρ hρ1)
    have hz : ConvergesAt (Laurent.cmul yi W) ρ := (hyi.1 ρ hρ1).cmul hρ0 (hWt.1.1 ρ hρ1)
    have he : ConvergesAt (Laurent.cmul y V - Pi.single 0 1) ρ :=
      hyV.sub hρ0 (convergesAt_single 0 1 ρ)
    have hyV1 : gaussNorm (Laurent.cmul y V) ρ = 1 :=
      gaussNorm_eq_one_of_sub_lt_one hρ0 hyV (hB'.trans_lt hB)

    have r1 : (eyi * eW) * ((ew * evi) * eV) = 1 := by
      linear_combination (eW * eV) * k2 + k3
    have r2 : (eyi * eW) - 1 = -((eyi * eW) * ((ew * evi) * eV - 1)) := by
      linear_combination r1
    have c1 : Laurent.cmul (Laurent.cmul yi W) (Laurent.cmul y V) = Pi.single 0 1 :=
      congrArg AnnulusRing.coeff r1
    have c2 : Laurent.cmul yi W - Pi.single 0 1 =
        -Laurent.cmul (Laurent.cmul yi W) (Laurent.cmul y V - Pi.single 0 1) :=
      congrArg AnnulusRing.coeff r2
    have hne : (Pi.single 0 (1 : K) : ℤ → K) ≠ 0 := fun h0 => by simpa using congrFun h0 0
    have hz0 : Laurent.cmul yi W ≠ 0 := fun h0 => hne (by rw [← c1, h0, zero_cmul])
    have hyV0 : Laurent.cmul y V ≠ 0 := fun h0 => hne (by rw [← c1, h0, cmul_zero])
    have hz1 : gaussNorm (Laurent.cmul yi W) ρ = 1 := by
      have := gaussNorm_cmul hρ0 hz hyV hz0 hyV0
      rw [c1, gaussNorm_single_zero_one hρ0, hyV1, mul_one] at this
      exact this.symm
    rw [c2, gaussNorm_neg]
    calc gaussNorm (Laurent.cmul (Laurent.cmul yi W) (Laurent.cmul y V - Pi.single 0 1)) ρ
        ≤ gaussNorm (Laurent.cmul yi W) ρ * gaussNorm (Laurent.cmul y V - Pi.single 0 1) ρ :=
          gaussNorm_cmul_le hρ0 hz he
      _ ≤ _ := by rw [hz1, one_mul]; exact hB'

end Step

section Main

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, cmul_add hρ hx hy hz.neg, cmul_neg, ← sub_eq_add_neg]`.
-/
theorem cmul_sub_right {ρ : ℝ} (hρ : 0 < ρ) {x y z : ℤ → K} (hx : ConvergesAt x ρ)
    (hy : ConvergesAt y ρ) (hz : ConvergesAt z ρ) :
    Laurent.cmul x (y - z) = Laurent.cmul x y - Laurent.cmul x z := by
  rw [sub_eq_add_neg, cmul_add hρ hx hy hz.neg, cmul_neg, ← sub_eq_add_neg]

/- English proof (translation)
Use `choose v hvU hvd using hv`. Establish `hrt : ∀ k, r ≤ t k` using `fun k => ht0 ▸ hmono (Nat.zero_le k)`. Establish `pos : ∀ ρ, r ≤ ρ → 0 < ρ` using `fun ρ h => hr.trans_le h`. Establish `hhalf : ∀ k : ℕ, (1 / 2 : ℝ) ^ (k + 1) < 1` using `fun k => pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero k)`. Set `Spec : ℕ → (ℤ → K) → (ℤ → K) × (ℤ → K) × (ℤ → K) → Prop` to `fun k D p => (∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt p.1 ρ) ∧ (∀ s, r ≤ s → s < 1 → IsUnitOn p.2.1 r s) ∧ p.1 = Laurent.cmul (d (k + 1)) p.2.1 ∧ IsUnitOn p.2.2 r (t (k + 1)) ∧ p.1 = Laurent.cmul D p.2.2 ∧ ∀ ρ ∈ Set.Icc r (t k), gaussNorm (p.2.2 - Pi.single 0 1) ρ ≤ (1 / 2) ^ (k + 1)`.

Set `stepFn : ℕ → (ℤ → K) × (ℤ → K) × (ℤ → K) → (ℤ → K) × (ℤ → K) × (ℤ → K)` to `fun k p => if h : ∃ p', Spec k p.1 p' then h.choose else p`. Take `⟨S, S_zero, S_succ⟩ : ∃ S : ℕ → (ℤ → K) × (ℤ → K) × (ℤ → K), S 0 = (d 0, Pi.single 0 1, Pi.single 0 1) ∧ ∀ k, S (k + 1) = stepFn k (S k)` from `⟨fun k => Nat.rec (d 0, Pi.single 0 1, Pi.single 0 1) stepFn k, rfl, fun k => rfl⟩`. Set `Inv : ℕ → Prop` to `fun k => (∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt (S k).1 ρ) ∧ IsUnitOn (S k).2.1 r (t (k + 1)) ∧ (S k).1 = Laurent.cmul (d k) (S k).2.1`. Establish `spec_of_inv : ∀ k, Inv k → Spec k (S k).1 (S (k + 1))`. Introduce `k hk`.

Establish `hex : ∃ p', Spec k (S k).1 p'`. Take `⟨D', w', z, h1, h2, h3, h4, h5, h6⟩` from `divisor_step (δ := (1 / 2) ^ (k + 1)) hr (hrt k) (hmono (Nat.le_succ k)) (ht1 _) hq' hbig (hn₀ k) (by positivity) (max_lt ((hβ k).trans_lt (hhalf k)) (hhalf k)) (hd k) (hd (k + 1)) (hvU k) (hvd k) hk.1 hk.2.1 hk.2.2`. Conclude with `⟨(D', w', z), h1, h2, h3, h4, h5, fun ρ hρ => (h6 ρ hρ).trans (max_le (hβ k) le_rfl)⟩`. Rewrite using `[S_succ]`. Express the relevant statement in the definitionally equal form `Spec k (S k).1 (if h : ∃ p', Spec k (S k).1 p' then h.choose else S k)`.

Rewrite using `[dif_pos hex]`. Conclude with `hex.choose_spec`. Establish `inv : ∀ k, Inv k`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => show (∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt (S 0).1 ρ) ∧ IsUnitOn (S 0).2.1 r (t (0 + 1)) ∧ (S 0).1 = Laurent.cmul (d 0) (S 0).2.1`. Rewrite using `[S_zero]`. Conclude with `⟨fun ρ h1 _ => hd 0 ρ (pos ρ h1), isUnitOn_single_zero_one hr (hrt 1), (cmul_single_zero_one _).symm⟩`. Consider the case `succ k ih`. Take `⟨h1, h2, h3, -, -, -⟩` from `spec_of_inv k ih`.

Conclude with `⟨h1, h2 _ (hrt _) (ht1 _), h3⟩`. Establish `spec : ∀ k, Spec k (S k).1 (S (k + 1))` using `fun k => spec_of_inv k (inv k)`. Take `⟨Dk, hDk⟩ : ∃ Dk : ℕ → ℤ → K, ∀ k, Dk k = (S k).1` from `⟨fun k => (S k).1, fun k => rfl⟩`. Take `⟨zk, hzk⟩ : ∃ zk : ℕ → ℤ → K, ∀ k, zk k = (S (k + 1)).2.2` from `⟨fun k => (S (k + 1)).2.2, fun k => rfl⟩`. Establish `Dconv : ∀ k ρ, r ≤ ρ → ρ < 1 → ConvergesAt (Dk k) ρ` using `fun k => by`.

Rewrite using `[hDk]`. Conclude with `(inv k).1`. Establish `Dne : ∀ k, Dk k ≠ 0`. Introduce `k`. Rewrite using `[hDk, (inv k).2.2]`.

Conclude with `cmul_ne_zero hr (hd k r hr) ((inv k).2.1.1 r ⟨le_rfl, hrt _⟩) (hd0 k) (inv k).2.1.2.1`. Establish `zconv : ∀ k ρ, r ≤ ρ → ρ ≤ t (k + 1) → ConvergesAt (zk k) ρ` using `fun k ρ h1 h2 => by`. Rewrite using `[hzk]`. Conclude with `(spec k).2.2.2.1.1 ρ ⟨h1, h2⟩`. Establish `zsmall : ∀ k ρ, r ≤ ρ → ρ ≤ t k → gaussNorm (zk k - Pi.single 0 1) ρ ≤ (1 / 2) ^ (k + 1)` using `fun k ρ h1 h2 => by rw [hzk]; exact (spec k).2.2.2.2.2 ρ ⟨h1, h2⟩`.

Establish `zunit : ∀ k, IsUnitOn (zk k) r (t (k + 1))` using `fun k => by rw [hzk]; exact (spec k).2.2.2.1`. Establish `zone : ∀ k ρ, r ≤ ρ → ρ ≤ t k → gaussNorm (zk k) ρ = 1` using `fun k ρ h1 h2 => gaussNorm_eq_one_of_sub_lt_one (pos ρ h1) (zconv k ρ h1 (h2.trans (hmono (Nat.le_succ k)))) ((zsmall k ρ h1 h2).trans_lt (hhalf k))`. Establish `Dstep : ∀ k, Dk (k + 1) = Laurent.cmul (Dk k) (zk k)` using `fun k => by`. Rewrite using `[hDk, hDk, hzk]`. Conclude with `(spec k).2.2.2.2.1`.

Establish `Ddiff : ∀ k ρ, r ≤ ρ → ρ ≤ t k → gaussNorm (Dk (k + 1) - Dk k) ρ ≤ gaussNorm (Dk k) ρ * (1 / 2) ^ (k + 1)`. Introduce `k ρ h1 h2`. Establish `h0` using `pos ρ h1`. Establish `hρ1 : ρ < 1` using `h2.trans_lt (ht1 k)`. Establish `hz` using `zconv k ρ h1 (h2.trans (hmono (Nat.le_succ k)))`.

Establish `e : Dk (k + 1) - Dk k = Laurent.cmul (Dk k) (zk k - Pi.single 0 1)`. Rewrite using `[Dstep, cmul_sub_right h0 (Dconv k ρ h1 hρ1) hz (convergesAt_single 0 1 ρ), cmul_single_zero_one]`. Rewrite using `[e]`. Conclude with `(gaussNorm_cmul_le h0 (Dconv k ρ h1 hρ1) (hz.sub h0 (convergesAt_single 0 1 ρ))).trans (mul_le_mul_of_nonneg_left (zsmall k ρ h1 h2) (gaussNorm_nonneg h0))`. Establish `Dnorm : ∀ m k, m ≤ k → ∀ ρ, r ≤ ρ → ρ ≤ t m → gaussNorm (Dk k) ρ = gaussNorm (Dk m) ρ`.

Introduce `m k hmk ρ h1 h2`. Proceed by induction on `k, hmk using Nat.le_induction with`. Consider the case `base => rfl`. Consider the case `succ k hmk ih`. Establish `h0` using `pos ρ h1`.

Establish `hρk : ρ ≤ t k` using `h2.trans (hmono hmk)`. Establish `hz` using `zconv k ρ h1 (hρk.trans (hmono (Nat.le_succ k)))`. Establish `hzne : zk k ≠ 0` using `(zunit k).2.1`. Rewrite using `[Dstep, gaussNorm_cmul h0 (Dconv k ρ h1 (hρk.trans_lt (ht1 k))) hz (Dne k) hzne, zone k ρ h1 hρk, mul_one, ih]`. Establish `geom : ∀ G ≥ (0 : ℝ), ∀ e > (0 : ℝ), ∀ m : ℕ, ∃ K₀ ≥ m, ∀ j ≥ K₀, G * (1 / 2) ^ (j + 1) ≤ e`.

Introduce `G hG e he m`. Take `⟨N, hN⟩` from `exists_pow_lt_of_lt_one (div_pos he (by linarith : (0:ℝ) < G + 1)) (by norm_num : (1 / 2 : ℝ) < 1)`. Use `⟨max N m, le_max_right _ _, fun j hj => ?_⟩` and prove the remaining obligations. Establish `h1 : (1 / 2 : ℝ) ^ (j + 1) ≤ (1 / 2) ^ N` using `pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)`. Establish `h2 : (1 / 2 : ℝ) ^ (j + 1) ≤ e / (G + 1)` using `h1.trans hN.le`.

Combine the equalities or inequalities in the displayed calculation. Establish `Dcauchy : ∀ m ρ, r ≤ ρ → ρ ≤ t m → UCauchy Dk ρ`. Introduce `m ρ h1 h2 e he`. Take `⟨K₀, hK₀m, hK₀⟩` from `geom (gaussNorm (Dk m) ρ) (gaussNorm_nonneg (pos ρ h1)) e he m`. Use `⟨K₀, fun j hj n => ?_⟩` and prove the remaining obligations.

Establish `hρj : ρ ≤ t j` using `h2.trans (hmono (hK₀m.trans hj))`. Establish `hρ1 : ρ < 1` using `h2.trans_lt (ht1 m)`. Establish `hc : ConvergesAt (Dk (j + 1) - Dk j) ρ` using `(Dconv _ ρ h1 hρ1).sub (pos ρ h1) (Dconv j ρ h1 hρ1)`. Use `(hc.le_gaussNorm n).trans ((Ddiff j ρ h1 hρj).trans ?_)` and prove the remaining obligations. Rewrite using `[Dnorm m j (hK₀m.trans hj) ρ h1 h2]`.

Conclude with `hK₀ j hj`. Establish `Dlimconv : ∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt (limSeq Dk) ρ` using `fun ρ h1 h2 => by`. Take `⟨m, hm⟩` from `hlim ρ h2`. Conclude with `(Dcauchy m ρ h1 hm).convergesAt_of_eventually (pos ρ h1) (K₁ := 0) fun k _ => Dconv k ρ h1 h2`. Use `⟨limSeq Dk, Dlimconv, fun m => ?_⟩` and prove the remaining obligations.

Establish `hJ : ∀ j, t (m + 1) ≤ t (m + j + 1)` using `fun j => hmono (by omega)`. Establish `hm1 : r ≤ t (m + 1)` using `hrt _`. Establish `hwm : IsUnitOn (S m).2.1 r (t (m + 1))` using `(inv m).2.1`. Take `⟨U, U_zero, U_succ⟩ : ∃ U : ℕ → ℤ → K, U 0 = Laurent.cmul (S m).2.1 (zk m) ∧ ∀ j, U (j + 1) = Laurent.cmul (U j) (zk (m + j + 1))` from `⟨fun j => Nat.rec (Laurent.cmul (S m).2.1 (zk m)) (fun j x => Laurent.cmul x (zk (m + j + 1))) j, rfl, fun j => rfl⟩`. Establish `Uconv : ∀ j ρ, r ≤ ρ → ρ ≤ t (m + 1) → ConvergesAt (U j) ρ`.

Introduce `j ρ h1 h2`. Proceed by induction on `j with`. Consider the case `zero => rw [U_zero]`. Conclude with `(hwm.1 ρ ⟨h1, h2⟩).cmul (pos ρ h1) (zconv m ρ h1 h2)`. Consider the case `succ j ih`.

Rewrite using `[U_succ]`. Conclude with `ih.cmul (pos ρ h1) (zconv _ ρ h1 (h2.trans (hJ (j + 1))))`. Establish `DU : ∀ j, Dk (m + j + 1) = Laurent.cmul (d m) (U j)`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero`. Rewrite using `[show m + 0 + 1 = m + 1 by omega, Dstep, U_zero, hDk m, (inv m).2.2]`. Conclude with `cmul_assoc hr (hd m r hr) (hwm.1 r ⟨le_rfl, hm1⟩) (zconv m r le_rfl hm1)`. Consider the case `succ j ih`. Rewrite using `[show m + (j + 1) + 1 = (m + j + 1) + 1 by omega, Dstep, ih, U_succ]`.

Conclude with `cmul_assoc hr (hd m r hr) (Uconv j r le_rfl hm1) (zconv _ r le_rfl ((hrt _)))`. Establish `Une : ∀ j, U j ≠ 0` using `fun j h0 => Dne (m + j + 1) (by rw [DU j, h0, cmul_zero])`. Establish `Unorm : ∀ j ρ, r ≤ ρ → ρ ≤ t (m + 1) → gaussNorm (U j) ρ = gaussNorm (U 0) ρ`. Introduce `j ρ h1 h2`. Proceed by induction on `j with`.

Consider the case `zero => rfl`. Consider the case `succ j ih`. Establish `hρ' : ρ ≤ t (m + j + 1)` using `h2.trans (hJ j)`. Rewrite using `[U_succ, gaussNorm_cmul (pos ρ h1) (Uconv j ρ h1 h2) (zconv _ ρ h1 (hρ'.trans (hmono (Nat.le_succ _)))) (Une j) (zunit _).2.1, zone _ ρ h1 hρ', mul_one, ih]`. Establish `Udiff : ∀ j ρ, r ≤ ρ → ρ ≤ t (m + 1) → gaussNorm (U (j + 1) - U j) ρ ≤ gaussNorm (U 0) ρ * (1 / 2) ^ (m + j + 1 + 1)`.

Introduce `j ρ h1 h2`. Establish `h0` using `pos ρ h1`. Establish `hρ' : ρ ≤ t (m + j + 1)` using `h2.trans (hJ j)`. Establish `hz` using `zconv (m + j + 1) ρ h1 (hρ'.trans (hmono (Nat.le_succ _)))`. Establish `e : U (j + 1) - U j = Laurent.cmul (U j) (zk (m + j + 1) - Pi.single 0 1)`.

Rewrite using `[U_succ, cmul_sub_right h0 (Uconv j ρ h1 h2) hz (convergesAt_single 0 1 ρ), cmul_single_zero_one]`. Rewrite using `[e, ← Unorm j ρ h1 h2]`. Conclude with `(gaussNorm_cmul_le h0 (Uconv j ρ h1 h2) (hz.sub h0 (convergesAt_single 0 1 ρ))).trans (mul_le_mul_of_nonneg_left (zsmall _ ρ h1 hρ') (gaussNorm_nonneg h0))`. Establish `Ucauchy : ∀ ρ, r ≤ ρ → ρ ≤ t (m + 1) → UCauchy U ρ`. Introduce `ρ h1 h2 e he`.

Take `⟨K₀, -, hK₀⟩` from `geom (gaussNorm (U 0) ρ) (gaussNorm_nonneg (pos ρ h1)) e he 0`. Use `⟨K₀, fun j hj n => ?_⟩` and prove the remaining obligations. Establish `hc : ConvergesAt (U (j + 1) - U j) ρ` using `(Uconv _ ρ h1 h2).sub (pos ρ h1) (Uconv j ρ h1 h2)`. Use `(hc.le_gaussNorm n).trans ((Udiff j ρ h1 h2).trans ?_)` and prove the remaining obligations. Use `le_trans ?_ (hK₀ j hj)` and prove the remaining obligations.

Conclude with `mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) (gaussNorm_nonneg (pos ρ h1))`. Establish `uconv : ∀ ρ, r ≤ ρ → ρ ≤ t (m + 1) → ConvergesAt (limSeq U) ρ` using `fun ρ h1 h2 => (Ucauchy ρ h1 h2).convergesAt_of_eventually (pos ρ h1) (K₁ := 0) fun j _ => Uconv j ρ h1 h2`. Establish `Ubound : ∀ j ρ, r ≤ ρ → ρ ≤ t (m + 1) → gaussNorm (U j - U 0) ρ ≤ gaussNorm (U 0) ρ * (1 / 2) ^ (m + 2)`. Introduce `j ρ h1 h2`. Establish `h0` using `pos ρ h1`.

Establish `hG` using `gaussNorm_nonneg (a := U 0) h0`. Proceed by induction on `j with`. Consider the case `zero => rw [sub_self, gaussNorm_zero]`. Check the signs of the components of the expression. Consider the case `succ j ih`.

Rewrite using `[show U (j + 1) - U 0 = (U (j + 1) - U j) + (U j - U 0) by ring]`. Use `(gaussNorm_add_le h0 ((Uconv _ ρ h1 h2).sub h0 (Uconv j ρ h1 h2)) ((Uconv j ρ h1 h2).sub h0 (Uconv 0 ρ h1 h2))).trans (max_le ?_ ih)` and prove the remaining obligations. Use `(Udiff j ρ h1 h2).trans (mul_le_mul_of_nonneg_left ?_ hG)` and prove the remaining obligations. Conclude with `pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)`. Establish `ubound : ∀ ρ, r ≤ ρ → ρ ≤ t (m + 1) → gaussNorm (limSeq U - U 0) ρ ≤ gaussNorm (U 0) ρ * (1 / 2) ^ (m + 2)`.

Introduce `ρ h1 h2`. Use `gaussNorm_le fun n => ?_` and prove the remaining obligations. Establish `hlim' : Tendsto (fun j => ‖U j n - U 0 n‖ * ρ ^ n) atTop (𝓝 (‖limSeq U n - U 0 n‖ * ρ ^ n))` using `((((Ucauchy ρ h1 h2).tendsto (pos ρ h1) n).sub_const (U 0 n)).norm).mul_const _`. Use `le_of_tendsto' hlim' fun j => ?_` and prove the remaining obligations. Conclude with `(((Uconv j ρ h1 h2).sub (pos ρ h1) (Uconv 0 ρ h1 h2)).le_gaussNorm n).trans (Ubound j ρ h1 h2)`.

Establish `hU0 : IsUnitOn (U 0) r (t (m + 1))`. Rewrite using `[U_zero]`. Conclude with `hwm.cmul hr hm1 (zunit m)`. Use `set N := lowIndex (U 0) r`. Establish `udom : ∀ ρ, r ≤ ρ → ρ ≤ t (m + 1) → ‖limSeq U N‖ * ρ ^ N = ‖U 0 N‖ * ρ ^ N ∧ ∀ m', m' ≠ N → ‖limSeq U m'‖ * ρ ^ m' < ‖limSeq U N‖ * ρ ^ N`.

Introduce `ρ h1 h2`. Establish `h0` using `pos ρ h1`. Establish `hN` using `unique_dominant_of_lowIndex_eq_highIndex hr hU0.1 hU0.2.1 hU0.2.2 ⟨h1, h2⟩`. Establish `hg : gaussNorm (U 0) ρ = ‖U 0 N‖ * ρ ^ N` using `le_antisymm (gaussNorm_le fun m' => by`. Distinguish the cases in `hm' : m' = N`.

Rewrite using `[hm']`. Conclude with `(hN m' hm').le) ((Uconv 0 ρ h1 h2).le_gaussNorm N)`. Establish `hpos : 0 < gaussNorm (U 0) ρ` using `gaussNorm_pos h0 (Uconv 0 ρ h1 h2) (Une 0)`. Establish `hsmall : gaussNorm (limSeq U - U 0) ρ < ‖U 0 N‖ * ρ ^ N`. Rewrite using `[← hg]`.

Use `(ubound ρ h1 h2).trans_lt ?_` and prove the remaining obligations. Establish `: (1 / 2 : ℝ) ^ (m + 2) < 1` using `pow_lt_one₀ (by norm_num) (by norm_num) (by omega)`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `unique_dominant_of_perturb h0 hN ((uconv ρ h1 h2).sub h0 (Uconv 0 ρ h1 h2)) hsmall`. Establish `huN : limSeq U N ≠ 0`.

Introduce `h0`. Use `(udom r le_rfl hm1).1` as an intermediate fact. Rewrite `this` using `[h0, norm_zero, zero_mul]`. Establish `hpos` using `norm_pos_iff.2 (ne_zero_of_mem_domSet hr (Uconv 0 r le_rfl hm1) (Une 0) (lowIndex_mem hr (Uconv 0 r le_rfl hm1) (Une 0)))`. Use `zpow_pos hr N` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish `hu : IsUnitOn (limSeq U) r (t (m + 1))`. Use `⟨fun ρ hρ => uconv ρ hρ.1 hρ.2, fun h0 => huN (by rw [h0]; rfl), ?_⟩` and prove the remaining obligations. Establish `e1` using `(low_high_of_unique_dominant hr (uconv r le_rfl hm1) (udom r le_rfl hm1).2 huN).1`. Establish `e2` using `(low_high_of_unique_dominant (pos _ hm1) (uconv _ hm1 le_rfl) (udom _ hm1 le_rfl).2 huN).2`.

Rewrite using `[e1, e2]`. Use `⟨limSeq U, hu, ?_⟩` and prove the remaining obligations. Establish `hcr : ConvergesAt (limSeq Dk - Laurent.cmul (d m) (limSeq U)) r` using `(Dlimconv r le_rfl (hm1.trans_lt (ht1 _))).sub hr ((hd m r hr).cmul hr (uconv r le_rfl hm1))`. Establish `hbound : ∀ e > (0 : ℝ), gaussNorm (limSeq Dk - Laurent.cmul (d m) (limSeq U)) r ≤ e`. Introduce `e he`.

Establish `hG : 0 < 1 + gaussNorm (d m) r` using `by linarith [gaussNorm_nonneg (a := d m) hr]`. Take `⟨K₁, hK₁⟩` from `(Dcauchy 0 r le_rfl (hrt 0)).gaussNorm_sub_le hr he`. Take `⟨K₂, hK₂⟩` from `(Ucauchy r le_rfl hm1).gaussNorm_sub_le hr (div_pos he hG)`. Use `set j := max K₁ K₂`. Establish `e1 : limSeq Dk - Laurent.cmul (d m) (limSeq U) = (limSeq Dk - Dk (m + j + 1)) + Laurent.cmul (d m) (U j - limSeq U)`.

Rewrite using `[cmul_sub_right hr (hd m r hr) (Uconv j r le_rfl hm1) (uconv r le_rfl hm1), DU j]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Use `(gaussNorm_add_le hr ((Dlimconv r le_rfl (hm1.trans_lt (ht1 _))).sub hr (Dconv _ r le_rfl (hm1.trans_lt (ht1 _)))) ((hd m r hr).cmul hr ((Uconv j r le_rfl hm1).sub hr (uconv r le_rfl hm1)))).trans (max_le (hK₁ _ (by omega)) ?_)` and prove the remaining obligations. Use `(gaussNorm_cmul_le hr (hd m r hr) ((Uconv j r le_rfl hm1).sub hr (uconv r le_rfl hm1))).trans ?_` and prove the remaining obligations.

Rewrite using `[gaussNorm_sub_comm]`. Combine the equalities or inequalities in the displayed calculation. Establish `h0 : gaussNorm (limSeq Dk - Laurent.cmul (d m) (limSeq U)) r = 0` using `le_antisymm (le_of_forall_pos_le_add fun e he => by simpa using hbound e he) (gaussNorm_nonneg hr)`. Conclude with `sub_eq_zero.1 ((gaussNorm_eq_zero_iff hr hcr).1 h0)`.
-/
theorem exists_divisor [IsDiscreteValuationRing (normInteger K)] (hr : 0 < r) {t : ℕ → ℝ}
    (ht0 : t 0 = r) (hmono : Monotone t) (ht1 : ∀ k, t k < 1) (hlim : ∀ ρ < 1, ∃ k, ρ ≤ t k)
    {q' : ℝ} (hq' : 0 < q') (hbig : ∀ x : K, 1 < ‖x‖ → 1 ≤ q' * ‖x‖) {n₀ : ℕ → ℕ}
    (hn₀ : ∀ k, q' ≤ t (k + 1) ^ n₀ k) (hβ : ∀ k, (t k / t (k + 1)) ^ n₀ k ≤ (1 / 2) ^ (k + 1))
    {d : ℕ → ℤ → K} (hd : ∀ k ρ, 0 < ρ → ConvergesAt (d k) ρ) (hd0 : ∀ k, d k ≠ 0)
    (hv : ∀ k, ∃ v, IsUnitOn v r (t (k + 1)) ∧ Laurent.cmul (d k) v = d (k + 1)) :
    ∃ D : ℤ → K, (∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt D ρ) ∧
      ∀ m, ∃ u, IsUnitOn u r (t (m + 1)) ∧ D = Laurent.cmul (d m) u := by
  classical
  choose v hvU hvd using hv
  have hrt : ∀ k, r ≤ t k := fun k => ht0 ▸ hmono (Nat.zero_le k)
  have pos : ∀ ρ, r ≤ ρ → 0 < ρ := fun ρ h => hr.trans_le h
  have hhalf : ∀ k : ℕ, (1 / 2 : ℝ) ^ (k + 1) < 1 := fun k =>
    pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero k)

  let Spec : ℕ → (ℤ → K) → (ℤ → K) × (ℤ → K) × (ℤ → K) → Prop := fun k D p =>
    (∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt p.1 ρ) ∧ (∀ s, r ≤ s → s < 1 → IsUnitOn p.2.1 r s) ∧
      p.1 = Laurent.cmul (d (k + 1)) p.2.1 ∧ IsUnitOn p.2.2 r (t (k + 1)) ∧
      p.1 = Laurent.cmul D p.2.2 ∧
      ∀ ρ ∈ Set.Icc r (t k), gaussNorm (p.2.2 - Pi.single 0 1) ρ ≤ (1 / 2) ^ (k + 1)
  let stepFn : ℕ → (ℤ → K) × (ℤ → K) × (ℤ → K) → (ℤ → K) × (ℤ → K) × (ℤ → K) := fun k p =>
    if h : ∃ p', Spec k p.1 p' then h.choose else p
  obtain ⟨S, S_zero, S_succ⟩ : ∃ S : ℕ → (ℤ → K) × (ℤ → K) × (ℤ → K),
      S 0 = (d 0, Pi.single 0 1, Pi.single 0 1) ∧ ∀ k, S (k + 1) = stepFn k (S k) :=
    ⟨fun k => Nat.rec (d 0, Pi.single 0 1, Pi.single 0 1) stepFn k, rfl, fun k => rfl⟩
  let Inv : ℕ → Prop := fun k => (∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt (S k).1 ρ) ∧
    IsUnitOn (S k).2.1 r (t (k + 1)) ∧ (S k).1 = Laurent.cmul (d k) (S k).2.1
  have spec_of_inv : ∀ k, Inv k → Spec k (S k).1 (S (k + 1)) := by
    intro k hk
    have hex : ∃ p', Spec k (S k).1 p' := by
      obtain ⟨D', w', z, h1, h2, h3, h4, h5, h6⟩ := divisor_step (δ := (1 / 2) ^ (k + 1)) hr
        (hrt k) (hmono (Nat.le_succ k)) (ht1 _) hq' hbig (hn₀ k) (by positivity)
        (max_lt ((hβ k).trans_lt (hhalf k)) (hhalf k)) (hd k) (hd (k + 1)) (hvU k) (hvd k)
        hk.1 hk.2.1 hk.2.2
      exact ⟨(D', w', z), h1, h2, h3, h4, h5, fun ρ hρ =>
        (h6 ρ hρ).trans (max_le (hβ k) le_rfl)⟩
    rw [S_succ]
    change Spec k (S k).1 (if h : ∃ p', Spec k (S k).1 p' then h.choose else S k)
    rw [dif_pos hex]
    exact hex.choose_spec
  have inv : ∀ k, Inv k := by
    intro k
    induction k with
    | zero =>
      show (∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt (S 0).1 ρ) ∧ IsUnitOn (S 0).2.1 r (t (0 + 1)) ∧
        (S 0).1 = Laurent.cmul (d 0) (S 0).2.1
      rw [S_zero]
      exact ⟨fun ρ h1 _ => hd 0 ρ (pos ρ h1), isUnitOn_single_zero_one hr (hrt 1),
        (cmul_single_zero_one _).symm⟩
    | succ k ih =>
      obtain ⟨h1, h2, h3, -, -, -⟩ := spec_of_inv k ih
      exact ⟨h1, h2 _ (hrt _) (ht1 _), h3⟩
  have spec : ∀ k, Spec k (S k).1 (S (k + 1)) := fun k => spec_of_inv k (inv k)

  obtain ⟨Dk, hDk⟩ : ∃ Dk : ℕ → ℤ → K, ∀ k, Dk k = (S k).1 := ⟨fun k => (S k).1, fun k => rfl⟩
  obtain ⟨zk, hzk⟩ : ∃ zk : ℕ → ℤ → K, ∀ k, zk k = (S (k + 1)).2.2 :=
    ⟨fun k => (S (k + 1)).2.2, fun k => rfl⟩
  have Dconv : ∀ k ρ, r ≤ ρ → ρ < 1 → ConvergesAt (Dk k) ρ := fun k => by
    rw [hDk]; exact (inv k).1
  have Dne : ∀ k, Dk k ≠ 0 := by
    intro k
    rw [hDk, (inv k).2.2]
    exact cmul_ne_zero hr (hd k r hr) ((inv k).2.1.1 r ⟨le_rfl, hrt _⟩) (hd0 k) (inv k).2.1.2.1
  have zconv : ∀ k ρ, r ≤ ρ → ρ ≤ t (k + 1) → ConvergesAt (zk k) ρ := fun k ρ h1 h2 => by
    rw [hzk]; exact (spec k).2.2.2.1.1 ρ ⟨h1, h2⟩
  have zsmall : ∀ k ρ, r ≤ ρ → ρ ≤ t k → gaussNorm (zk k - Pi.single 0 1) ρ ≤ (1 / 2) ^ (k + 1) :=
    fun k ρ h1 h2 => by rw [hzk]; exact (spec k).2.2.2.2.2 ρ ⟨h1, h2⟩
  have zunit : ∀ k, IsUnitOn (zk k) r (t (k + 1)) := fun k => by rw [hzk]; exact (spec k).2.2.2.1
  have zone : ∀ k ρ, r ≤ ρ → ρ ≤ t k → gaussNorm (zk k) ρ = 1 := fun k ρ h1 h2 =>
    gaussNorm_eq_one_of_sub_lt_one (pos ρ h1) (zconv k ρ h1 (h2.trans (hmono (Nat.le_succ k))))
      ((zsmall k ρ h1 h2).trans_lt (hhalf k))
  have Dstep : ∀ k, Dk (k + 1) = Laurent.cmul (Dk k) (zk k) := fun k => by
    rw [hDk, hDk, hzk]; exact (spec k).2.2.2.2.1

  have Ddiff : ∀ k ρ, r ≤ ρ → ρ ≤ t k →
      gaussNorm (Dk (k + 1) - Dk k) ρ ≤ gaussNorm (Dk k) ρ * (1 / 2) ^ (k + 1) := by
    intro k ρ h1 h2
    have h0 := pos ρ h1
    have hρ1 : ρ < 1 := h2.trans_lt (ht1 k)
    have hz := zconv k ρ h1 (h2.trans (hmono (Nat.le_succ k)))
    have e : Dk (k + 1) - Dk k = Laurent.cmul (Dk k) (zk k - Pi.single 0 1) := by
      rw [Dstep, cmul_sub_right h0 (Dconv k ρ h1 hρ1) hz (convergesAt_single 0 1 ρ),
        cmul_single_zero_one]
    rw [e]
    exact (gaussNorm_cmul_le h0 (Dconv k ρ h1 hρ1) (hz.sub h0 (convergesAt_single 0 1 ρ))).trans
      (mul_le_mul_of_nonneg_left (zsmall k ρ h1 h2) (gaussNorm_nonneg h0))
  have Dnorm : ∀ m k, m ≤ k → ∀ ρ, r ≤ ρ → ρ ≤ t m → gaussNorm (Dk k) ρ = gaussNorm (Dk m) ρ := by
    intro m k hmk ρ h1 h2
    induction k, hmk using Nat.le_induction with
    | base => rfl
    | succ k hmk ih =>
      have h0 := pos ρ h1
      have hρk : ρ ≤ t k := h2.trans (hmono hmk)
      have hz := zconv k ρ h1 (hρk.trans (hmono (Nat.le_succ k)))
      have hzne : zk k ≠ 0 := (zunit k).2.1
      rw [Dstep, gaussNorm_cmul h0 (Dconv k ρ h1 (hρk.trans_lt (ht1 k))) hz (Dne k) hzne,
        zone k ρ h1 hρk, mul_one, ih]

  have geom : ∀ G ≥ (0 : ℝ), ∀ e > (0 : ℝ), ∀ m : ℕ, ∃ K₀ ≥ m, ∀ j ≥ K₀, G * (1 / 2) ^ (j + 1) ≤ e := by
    intro G hG e he m
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos he (by linarith : (0:ℝ) < G + 1))
      (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨max N m, le_max_right _ _, fun j hj => ?_⟩
    have h1 : (1 / 2 : ℝ) ^ (j + 1) ≤ (1 / 2) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h2 : (1 / 2 : ℝ) ^ (j + 1) ≤ e / (G + 1) := h1.trans hN.le
    calc G * (1 / 2) ^ (j + 1) ≤ (G + 1) * (e / (G + 1)) :=
          mul_le_mul (by linarith) h2 (by positivity) (by linarith)
      _ = e := mul_div_cancel₀ _ (by linarith)
  have Dcauchy : ∀ m ρ, r ≤ ρ → ρ ≤ t m → UCauchy Dk ρ := by
    intro m ρ h1 h2 e he
    obtain ⟨K₀, hK₀m, hK₀⟩ := geom (gaussNorm (Dk m) ρ) (gaussNorm_nonneg (pos ρ h1)) e he m
    refine ⟨K₀, fun j hj n => ?_⟩
    have hρj : ρ ≤ t j := h2.trans (hmono (hK₀m.trans hj))
    have hρ1 : ρ < 1 := h2.trans_lt (ht1 m)
    have hc : ConvergesAt (Dk (j + 1) - Dk j) ρ :=
      (Dconv _ ρ h1 hρ1).sub (pos ρ h1) (Dconv j ρ h1 hρ1)
    refine (hc.le_gaussNorm n).trans ((Ddiff j ρ h1 hρj).trans ?_)
    rw [Dnorm m j (hK₀m.trans hj) ρ h1 h2]
    exact hK₀ j hj

  have Dlimconv : ∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt (limSeq Dk) ρ := fun ρ h1 h2 => by
    obtain ⟨m, hm⟩ := hlim ρ h2
    exact (Dcauchy m ρ h1 hm).convergesAt_of_eventually (pos ρ h1) (K₁ := 0)
      fun k _ => Dconv k ρ h1 h2
  refine ⟨limSeq Dk, Dlimconv, fun m => ?_⟩
  have hJ : ∀ j, t (m + 1) ≤ t (m + j + 1) := fun j => hmono (by omega)
  have hm1 : r ≤ t (m + 1) := hrt _
  have hwm : IsUnitOn (S m).2.1 r (t (m + 1)) := (inv m).2.1
  obtain ⟨U, U_zero, U_succ⟩ : ∃ U : ℕ → ℤ → K, U 0 = Laurent.cmul (S m).2.1 (zk m) ∧
      ∀ j, U (j + 1) = Laurent.cmul (U j) (zk (m + j + 1)) :=
    ⟨fun j => Nat.rec (Laurent.cmul (S m).2.1 (zk m))
      (fun j x => Laurent.cmul x (zk (m + j + 1))) j, rfl, fun j => rfl⟩
  have Uconv : ∀ j ρ, r ≤ ρ → ρ ≤ t (m + 1) → ConvergesAt (U j) ρ := by
    intro j ρ h1 h2
    induction j with
    | zero => rw [U_zero]; exact (hwm.1 ρ ⟨h1, h2⟩).cmul (pos ρ h1) (zconv m ρ h1 h2)
    | succ j ih =>
      rw [U_succ]
      exact ih.cmul (pos ρ h1) (zconv _ ρ h1 (h2.trans (hJ (j + 1))))
  have DU : ∀ j, Dk (m + j + 1) = Laurent.cmul (d m) (U j) := by
    intro j
    induction j with
    | zero =>
      rw [show m + 0 + 1 = m + 1 by omega, Dstep, U_zero, hDk m, (inv m).2.2]
      exact cmul_assoc hr (hd m r hr) (hwm.1 r ⟨le_rfl, hm1⟩) (zconv m r le_rfl hm1)
    | succ j ih =>
      rw [show m + (j + 1) + 1 = (m + j + 1) + 1 by omega, Dstep, ih, U_succ]
      exact cmul_assoc hr (hd m r hr) (Uconv j r le_rfl hm1)
        (zconv _ r le_rfl ((hrt _)))
  have Une : ∀ j, U j ≠ 0 := fun j h0 => Dne (m + j + 1) (by rw [DU j, h0, cmul_zero])
  have Unorm : ∀ j ρ, r ≤ ρ → ρ ≤ t (m + 1) → gaussNorm (U j) ρ = gaussNorm (U 0) ρ := by
    intro j ρ h1 h2
    induction j with
    | zero => rfl
    | succ j ih =>
      have hρ' : ρ ≤ t (m + j + 1) := h2.trans (hJ j)
      rw [U_succ, gaussNorm_cmul (pos ρ h1) (Uconv j ρ h1 h2)
        (zconv _ ρ h1 (hρ'.trans (hmono (Nat.le_succ _)))) (Une j) (zunit _).2.1,
        zone _ ρ h1 hρ', mul_one, ih]
  have Udiff : ∀ j ρ, r ≤ ρ → ρ ≤ t (m + 1) →
      gaussNorm (U (j + 1) - U j) ρ ≤ gaussNorm (U 0) ρ * (1 / 2) ^ (m + j + 1 + 1) := by
    intro j ρ h1 h2
    have h0 := pos ρ h1
    have hρ' : ρ ≤ t (m + j + 1) := h2.trans (hJ j)
    have hz := zconv (m + j + 1) ρ h1 (hρ'.trans (hmono (Nat.le_succ _)))
    have e : U (j + 1) - U j = Laurent.cmul (U j) (zk (m + j + 1) - Pi.single 0 1) := by
      rw [U_succ, cmul_sub_right h0 (Uconv j ρ h1 h2) hz (convergesAt_single 0 1 ρ),
        cmul_single_zero_one]
    rw [e, ← Unorm j ρ h1 h2]
    exact (gaussNorm_cmul_le h0 (Uconv j ρ h1 h2) (hz.sub h0 (convergesAt_single 0 1 ρ))).trans
      (mul_le_mul_of_nonneg_left (zsmall _ ρ h1 hρ') (gaussNorm_nonneg h0))
  have Ucauchy : ∀ ρ, r ≤ ρ → ρ ≤ t (m + 1) → UCauchy U ρ := by
    intro ρ h1 h2 e he
    obtain ⟨K₀, -, hK₀⟩ := geom (gaussNorm (U 0) ρ) (gaussNorm_nonneg (pos ρ h1)) e he 0
    refine ⟨K₀, fun j hj n => ?_⟩
    have hc : ConvergesAt (U (j + 1) - U j) ρ :=
      (Uconv _ ρ h1 h2).sub (pos ρ h1) (Uconv j ρ h1 h2)
    refine (hc.le_gaussNorm n).trans ((Udiff j ρ h1 h2).trans ?_)
    refine le_trans ?_ (hK₀ j hj)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (by omega)) (gaussNorm_nonneg (pos ρ h1))
  have uconv : ∀ ρ, r ≤ ρ → ρ ≤ t (m + 1) → ConvergesAt (limSeq U) ρ := fun ρ h1 h2 =>
    (Ucauchy ρ h1 h2).convergesAt_of_eventually (pos ρ h1) (K₁ := 0)
      fun j _ => Uconv j ρ h1 h2
  have Ubound : ∀ j ρ, r ≤ ρ → ρ ≤ t (m + 1) →
      gaussNorm (U j - U 0) ρ ≤ gaussNorm (U 0) ρ * (1 / 2) ^ (m + 2) := by
    intro j ρ h1 h2
    have h0 := pos ρ h1
    have hG := gaussNorm_nonneg (a := U 0) h0
    induction j with
    | zero => rw [sub_self, gaussNorm_zero]; positivity
    | succ j ih =>
      rw [show U (j + 1) - U 0 = (U (j + 1) - U j) + (U j - U 0) by ring]
      refine (gaussNorm_add_le h0 ((Uconv _ ρ h1 h2).sub h0 (Uconv j ρ h1 h2))
        ((Uconv j ρ h1 h2).sub h0 (Uconv 0 ρ h1 h2))).trans (max_le ?_ ih)
      refine (Udiff j ρ h1 h2).trans (mul_le_mul_of_nonneg_left ?_ hG)
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have ubound : ∀ ρ, r ≤ ρ → ρ ≤ t (m + 1) →
      gaussNorm (limSeq U - U 0) ρ ≤ gaussNorm (U 0) ρ * (1 / 2) ^ (m + 2) := by
    intro ρ h1 h2
    refine gaussNorm_le fun n => ?_
    have hlim' : Tendsto (fun j => ‖U j n - U 0 n‖ * ρ ^ n) atTop
        (𝓝 (‖limSeq U n - U 0 n‖ * ρ ^ n)) :=
      ((((Ucauchy ρ h1 h2).tendsto (pos ρ h1) n).sub_const (U 0 n)).norm).mul_const _
    refine le_of_tendsto' hlim' fun j => ?_
    exact (((Uconv j ρ h1 h2).sub (pos ρ h1) (Uconv 0 ρ h1 h2)).le_gaussNorm n).trans
      (Ubound j ρ h1 h2)

  have hU0 : IsUnitOn (U 0) r (t (m + 1)) := by
    rw [U_zero]; exact hwm.cmul hr hm1 (zunit m)
  set N := lowIndex (U 0) r
  have udom : ∀ ρ, r ≤ ρ → ρ ≤ t (m + 1) →
      ‖limSeq U N‖ * ρ ^ N = ‖U 0 N‖ * ρ ^ N ∧
        ∀ m', m' ≠ N → ‖limSeq U m'‖ * ρ ^ m' < ‖limSeq U N‖ * ρ ^ N := by
    intro ρ h1 h2
    have h0 := pos ρ h1
    have hN := unique_dominant_of_lowIndex_eq_highIndex hr hU0.1 hU0.2.1 hU0.2.2 ⟨h1, h2⟩
    have hg : gaussNorm (U 0) ρ = ‖U 0 N‖ * ρ ^ N :=
      le_antisymm (gaussNorm_le fun m' => by
        by_cases hm' : m' = N
        · rw [hm']
        · exact (hN m' hm').le) ((Uconv 0 ρ h1 h2).le_gaussNorm N)
    have hpos : 0 < gaussNorm (U 0) ρ := gaussNorm_pos h0 (Uconv 0 ρ h1 h2) (Une 0)
    have hsmall : gaussNorm (limSeq U - U 0) ρ < ‖U 0 N‖ * ρ ^ N := by
      rw [← hg]
      refine (ubound ρ h1 h2).trans_lt ?_
      have : (1 / 2 : ℝ) ^ (m + 2) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
      nlinarith
    exact unique_dominant_of_perturb h0 hN ((uconv ρ h1 h2).sub h0 (Uconv 0 ρ h1 h2)) hsmall
  have huN : limSeq U N ≠ 0 := by
    intro h0
    have := (udom r le_rfl hm1).1
    rw [h0, norm_zero, zero_mul] at this
    have hpos := norm_pos_iff.2 (ne_zero_of_mem_domSet hr (Uconv 0 r le_rfl hm1) (Une 0)
      (lowIndex_mem hr (Uconv 0 r le_rfl hm1) (Une 0)))
    have := zpow_pos hr N
    nlinarith
  have hu : IsUnitOn (limSeq U) r (t (m + 1)) := by
    refine ⟨fun ρ hρ => uconv ρ hρ.1 hρ.2, fun h0 => huN (by rw [h0]; rfl), ?_⟩
    have e1 := (low_high_of_unique_dominant hr (uconv r le_rfl hm1) (udom r le_rfl hm1).2 huN).1
    have e2 := (low_high_of_unique_dominant (pos _ hm1) (uconv _ hm1 le_rfl)
      (udom _ hm1 le_rfl).2 huN).2
    rw [e1, e2]
  refine ⟨limSeq U, hu, ?_⟩

  have hcr : ConvergesAt (limSeq Dk - Laurent.cmul (d m) (limSeq U)) r :=
    (Dlimconv r le_rfl (hm1.trans_lt (ht1 _))).sub hr ((hd m r hr).cmul hr (uconv r le_rfl hm1))
  have hbound : ∀ e > (0 : ℝ), gaussNorm (limSeq Dk - Laurent.cmul (d m) (limSeq U)) r ≤ e := by
    intro e he
    have hG : 0 < 1 + gaussNorm (d m) r := by linarith [gaussNorm_nonneg (a := d m) hr]
    obtain ⟨K₁, hK₁⟩ := (Dcauchy 0 r le_rfl (hrt 0)).gaussNorm_sub_le hr he
    obtain ⟨K₂, hK₂⟩ := (Ucauchy r le_rfl hm1).gaussNorm_sub_le hr (div_pos he hG)
    set j := max K₁ K₂
    have e1 : limSeq Dk - Laurent.cmul (d m) (limSeq U) =
        (limSeq Dk - Dk (m + j + 1)) + Laurent.cmul (d m) (U j - limSeq U) := by
      rw [cmul_sub_right hr (hd m r hr) (Uconv j r le_rfl hm1) (uconv r le_rfl hm1), DU j]
      ring
    rw [e1]
    refine (gaussNorm_add_le hr ((Dlimconv r le_rfl (hm1.trans_lt (ht1 _))).sub hr
      (Dconv _ r le_rfl (hm1.trans_lt (ht1 _))))
      ((hd m r hr).cmul hr ((Uconv j r le_rfl hm1).sub hr (uconv r le_rfl hm1)))).trans
      (max_le (hK₁ _ (by omega)) ?_)
    refine (gaussNorm_cmul_le hr (hd m r hr) ((Uconv j r le_rfl hm1).sub hr
      (uconv r le_rfl hm1))).trans ?_
    rw [gaussNorm_sub_comm]
    calc gaussNorm (d m) r * gaussNorm (limSeq U - U j) r
        ≤ (1 + gaussNorm (d m) r) * (e / (1 + gaussNorm (d m) r)) :=
          mul_le_mul (by linarith) (hK₂ j (le_max_right _ _)) (gaussNorm_nonneg hr) hG.le
      _ = e := mul_div_cancel₀ _ hG.ne'
  have h0 : gaussNorm (limSeq Dk - Laurent.cmul (d m) (limSeq U)) r = 0 :=
    le_antisymm (le_of_forall_pos_le_add fun e he => by simpa using hbound e he)
      (gaussNorm_nonneg hr)
  exact sub_eq_zero.1 ((gaussNorm_eq_zero_iff hr hcr).1 h0)

end Main

end Laurent

end GroundTheory.PAdicHodge

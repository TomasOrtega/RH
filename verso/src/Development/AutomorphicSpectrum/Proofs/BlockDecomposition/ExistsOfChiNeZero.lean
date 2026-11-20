import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit

noncomputable section

open NumberField IsDedekindDomain
open scoped Classical

set_option synthInstance.maxSize 1000

namespace GlobalTheory.CompanionTheory.RgEisFin

open PositivityTheory.RgEis PositivityTheory.RgEis.TF GroundTheory.Global GroundTheory.Automorphic GroundTheory.Global.IdeleGroup

variable {k : Type} [Field k] [NumberField k]

/- English proof (translation)
The claim follows from `_root_.natCast_mem (OH k) M`.
-/
theorem natC_mem (M : ℕ) : (M : FiniteAdeleRing (𝓞 k) k) ∈ OH k := _root_.natCast_mem (OH k) M

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, zero_mem _, by simp⟩`.
-/
theorem inM_zero (M : ℕ) : InM M (0 : FiniteAdeleRing (𝓞 k) k) :=
  ⟨0, zero_mem _, by simp⟩

/- English proof (translation)
Take `⟨a, ha, rfl⟩` from `hx`. Take `⟨b, hb, rfl⟩` from `hy`. Conclude with `⟨a + b, add_mem ha hb, by ring⟩`.
-/
theorem inM_add {M : ℕ} {x y : FiniteAdeleRing (𝓞 k) k} (hx : InM M x) (hy : InM M y) :
    InM M (x + y) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨a + b, add_mem ha hb, by ring⟩

/- English proof (translation)
Take `⟨a, ha, rfl⟩` from `hx`. Conclude with `⟨-a, neg_mem ha, by ring⟩`.
-/
theorem inM_neg {M : ℕ} {x : FiniteAdeleRing (𝓞 k) k} (hx : InM M x) : InM M (-x) := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨-a, neg_mem ha, by ring⟩

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `inM_add hx (inM_neg hy)`.
-/
theorem inM_sub {M : ℕ} {x y : FiniteAdeleRing (𝓞 k) k} (hx : InM M x) (hy : InM M y) :
    InM M (x - y) := by
  rw [sub_eq_add_neg]
  exact inM_add hx (inM_neg hy)

/- English proof (translation)
Take `⟨b, hb, rfl⟩` from `hx`. Conclude with `⟨a * b, mul_mem ha hb, by ring⟩`.
-/
theorem inM_mul {M : ℕ} {a x : FiniteAdeleRing (𝓞 k) k} (ha : a ∈ OH k) (hx : InM M x) :
    InM M (a * x) := by
  obtain ⟨b, hb, rfl⟩ := hx
  exact ⟨a * b, mul_mem ha hb, by ring⟩

/- English proof (translation)
Take `⟨c, rfl⟩` from `h`. Take `⟨b, hb, rfl⟩` from `hx`. Conclude with `⟨(c : FiniteAdeleRing (𝓞 k) k) * b, mul_mem (natC_mem c) hb, by push_cast; ring⟩`.
-/
theorem inM_dvd {M₀ M : ℕ} (h : M₀ ∣ M) {x : FiniteAdeleRing (𝓞 k) k} (hx : InM M x) :
    InM M₀ x := by
  obtain ⟨c, rfl⟩ := h
  obtain ⟨b, hb, rfl⟩ := hx
  exact ⟨(c : FiniteAdeleRing (𝓞 k) k) * b, mul_mem (natC_mem c) hb, by push_cast; ring⟩

/- English proof (translation)
Take `⟨b, hb, rfl⟩` from `hx`. Conclude with `mul_mem (natC_mem M) hb`.
-/
theorem mem_of_inM {M : ℕ} {x : FiniteAdeleRing (𝓞 k) k} (hx : InM M x) : x ∈ OH k := by
  obtain ⟨b, hb, rfl⟩ := hx
  exact mul_mem (natC_mem M) hb

/- English proof (translation)
Introduce `v` and use `((mem_finiteIntegralUnits k).1 hu v).1`.
-/
theorem unit_mem {u : (FiniteAdeleRing (𝓞 k) k)ˣ} (hu : u ∈ finiteIntegralUnits k) :
    (u : FiniteAdeleRing (𝓞 k) k) ∈ OH k :=
  fun v => ((mem_finiteIntegralUnits k).1 hu v).1

def val (ω : HeckeCharacter k) (u : (FiniteAdeleRing (𝓞 k) k)ˣ) : ℂ := (ω.toIdele (ofFinite u) : ℂ)

/- English proof (translation)
Simplify using `[val, map_mul]`.
-/
theorem val_mul (ω : HeckeCharacter k) (u u' : (FiniteAdeleRing (𝓞 k) k)ˣ) :
    val ω (u * u') = val ω u * val ω u' := by
  simp [val, map_mul]

/- English proof (translation)
The claim follows from `Circle.coe_ne_zero _`.
-/
theorem val_ne_zero (ω : HeckeCharacter k) (u : (FiniteAdeleRing (𝓞 k) k)ˣ) : val ω u ≠ 0 :=
  Circle.coe_ne_zero _

/- English proof (translation)
The claim follows from `Circle.norm_coe _`.
-/
theorem norm_val (ω : HeckeCharacter k) (u : (FiniteAdeleRing (𝓞 k) k)ˣ) : ‖val ω u‖ = 1 :=
  Circle.norm_coe _

/- English proof (translation)
Establish `hw : u * u'⁻¹ ∈ finiteIntegralUnits k` using `mul_mem hu (inv_mem hu')`. Establish `h1 : InM M₀ (((u * u'⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) - 1)`. Establish `e : ((u * u'⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) - 1 = ((u'⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) * ((u : FiniteAdeleRing (𝓞 k) k) - (u' : FiniteAdeleRing (𝓞 k) k))`. Rewrite using `[mul_sub, Units.val_mul, mul_comm, Units.inv_mul]`. Rewrite using `[e]`.

Conclude with `inM_mul (unit_mem (inv_mem hu')) h`. Establish `h2 : val ω (u * u'⁻¹) = 1` using `by simp only [val]; rw [hc _ hw h1]; simp`. Establish `h3 : val ω (u * u'⁻¹) * val ω u' = val ω u`. Rewrite using `[← val_mul, inv_mul_cancel_right]`. Rewrite using `[← h3, h2, one_mul]`.
-/
theorem val_eq_of_inM {ω : HeckeCharacter k} {M₀ : ℕ}
    (hc : ∀ u ∈ finiteIntegralUnits k, InM M₀ ((u : FiniteAdeleRing (𝓞 k) k) - 1) →
      ω.toIdele (ofFinite u) = 1)
    {u u' : (FiniteAdeleRing (𝓞 k) k)ˣ} (hu : u ∈ finiteIntegralUnits k)
    (hu' : u' ∈ finiteIntegralUnits k)
    (h : InM M₀ ((u : FiniteAdeleRing (𝓞 k) k) - (u' : FiniteAdeleRing (𝓞 k) k))) :
    val ω u = val ω u' := by
  have hw : u * u'⁻¹ ∈ finiteIntegralUnits k := mul_mem hu (inv_mem hu')
  have h1 : InM M₀ (((u * u'⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) - 1) := by
    have e : ((u * u'⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) - 1 =
        ((u'⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) *
          ((u : FiniteAdeleRing (𝓞 k) k) - (u' : FiniteAdeleRing (𝓞 k) k)) := by
      rw [mul_sub, Units.val_mul, mul_comm, Units.inv_mul]
    rw [e]
    exact inM_mul (unit_mem (inv_mem hu')) h
  have h2 : val ω (u * u'⁻¹) = 1 := by simp only [val]; rw [hc _ hw h1]; simp
  have h3 : val ω (u * u'⁻¹) * val ω u' = val ω u := by
    rw [← val_mul, inv_mul_cancel_right]
  rw [← h3, h2, one_mul]

def chi (ω : HeckeCharacter k) (M : ℕ) (a : FiniteAdeleRing (𝓞 k) k) : ℂ :=
  if h : ∃ u ∈ finiteIntegralUnits k, InM M (a - (u : FiniteAdeleRing (𝓞 k) k)) then
    val ω h.choose else 0

structure Lvl (ω : HeckeCharacter k) (M₀ M : ℕ) : Prop where
  dvd : M₀ ∣ M
  cond : ∀ u ∈ finiteIntegralUnits k, InM M₀ ((u : FiniteAdeleRing (𝓞 k) k) - 1) →
    ω.toIdele (ofFinite u) = 1

/- English proof (translation)
Establish `hex : ∃ u ∈ finiteIntegralUnits k, InM M (a - (u : FiniteAdeleRing (𝓞 k) k))` using `⟨u, hu, h⟩`. Rewrite using `[chi, dif_pos hex]`. Take `⟨h1, h2⟩` from `hex.choose_spec`. Use `val_eq_of_inM hL.cond h1 hu (inM_dvd hL.dvd ?_)` and prove the remaining obligations. Use `inM_sub h h2` as an intermediate fact.

Rewrite `this` using `[sub_sub_sub_cancel_left]`. Then use the resulting hypothesis.
-/
theorem chi_eq {ω : HeckeCharacter k} {M₀ M : ℕ} (hL : Lvl ω M₀ M)
    {a : FiniteAdeleRing (𝓞 k) k} {u : (FiniteAdeleRing (𝓞 k) k)ˣ}
    (hu : u ∈ finiteIntegralUnits k) (h : InM M (a - (u : FiniteAdeleRing (𝓞 k) k))) :
    chi ω M a = val ω u := by
  have hex : ∃ u ∈ finiteIntegralUnits k, InM M (a - (u : FiniteAdeleRing (𝓞 k) k)) := ⟨u, hu, h⟩
  rw [chi, dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  refine val_eq_of_inM hL.cond h1 hu (inM_dvd hL.dvd ?_)
  have := inM_sub h h2
  rwa [sub_sub_sub_cancel_left] at this

/- English proof (translation)
Rewrite using `[chi, dif_neg h]`.
-/
theorem chi_eq_zero {ω : HeckeCharacter k} {M : ℕ} {a : FiniteAdeleRing (𝓞 k) k}
    (h : ¬ ∃ u ∈ finiteIntegralUnits k, InM M (a - (u : FiniteAdeleRing (𝓞 k) k))) :
    chi ω M a = 0 := by
  rw [chi, dif_neg h]

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Conclude with `h (chi_eq_zero hn)`.
-/
theorem exists_of_chi_ne_zero {ω : HeckeCharacter k} {M : ℕ} {a : FiniteAdeleRing (𝓞 k) k}
    (h : chi ω M a ≠ 0) :
    ∃ u ∈ finiteIntegralUnits k, InM M (a - (u : FiniteAdeleRing (𝓞 k) k)) := by
  by_contra hn
  exact h (chi_eq_zero hn)

/- English proof (translation)
Take `⟨u, hu, hM⟩` from `exists_of_chi_ne_zero h`. Use `add_mem (mem_of_inM hM) (unit_mem hu)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem mem_of_chi_ne_zero {ω : HeckeCharacter k} {M : ℕ} {a : FiniteAdeleRing (𝓞 k) k}
    (h : chi ω M a ≠ 0) : a ∈ OH k := by
  obtain ⟨u, hu, hM⟩ := exists_of_chi_ne_zero h
  have := add_mem (mem_of_inM hM) (unit_mem hu)
  rwa [sub_add_cancel] at this

/- English proof (translation)
Distinguish the cases in `hex : ∃ u ∈ finiteIntegralUnits k, InM M (a - (u : FiniteAdeleRing (𝓞 k) k))`. Take `⟨u, hu, hM⟩` from `hex`. Rewrite using `[chi_eq hL hu hM, chi_eq hL hu (a := a + h)]`. Use `inM_add hM hh` as an intermediate fact. Rewrite `this` using `[sub_add_eq_add_sub]`. Then use the resulting hypothesis.

Rewrite using `[chi_eq_zero hex, chi_eq_zero]`. Introduce and unpack `⟨u, hu, hM⟩`. Use `hex ⟨u, hu, ?_⟩` and prove the remaining obligations. Use `inM_sub hM hh` as an intermediate fact. Establish `e : a + h - (u : FiniteAdeleRing (𝓞 k) k) - h = a - u` using `by ring`.

Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem chi_add {ω : HeckeCharacter k} {M₀ M : ℕ} (hL : Lvl ω M₀ M)
    (a : FiniteAdeleRing (𝓞 k) k) {h : FiniteAdeleRing (𝓞 k) k} (hh : InM M h) :
    chi ω M (a + h) = chi ω M a := by
  by_cases hex : ∃ u ∈ finiteIntegralUnits k, InM M (a - (u : FiniteAdeleRing (𝓞 k) k))
  · obtain ⟨u, hu, hM⟩ := hex
    rw [chi_eq hL hu hM, chi_eq hL hu (a := a + h)]
    have := inM_add hM hh
    rwa [sub_add_eq_add_sub] at this
  · rw [chi_eq_zero hex, chi_eq_zero]
    rintro ⟨u, hu, hM⟩
    refine hex ⟨u, hu, ?_⟩
    have := inM_sub hM hh
    have e : a + h - (u : FiniteAdeleRing (𝓞 k) k) - h = a - u := by ring
    rwa [e] at this

/- English proof (translation)
Take `⟨u, hu, hu'⟩` from `exists_of_chi_ne_zero h`. Take `⟨u₁, h1, h2⟩` from `hU k M hM a ha b hb u hu hu'`. Rewrite using `[chi_eq hL h1 h2]`. Conclude with `val_ne_zero ω u₁`.
-/
theorem lift {ω : HeckeCharacter k} {M₀ M : ℕ} (hL : Lvl ω M₀ M) (hM : M ≠ 0) (hU : LiftUnit)
    {a b : FiniteAdeleRing (𝓞 k) k} (ha : a ∈ OH k) (hb : b ∈ OH k) (h : chi ω M (a * b) ≠ 0) :
    chi ω M a ≠ 0 := by
  obtain ⟨u, hu, hu'⟩ := exists_of_chi_ne_zero h
  obtain ⟨u₁, h1, h2⟩ := hU k M hM a ha b hb u hu hu'
  rw [chi_eq hL h1 h2]
  exact val_ne_zero ω u₁

/- English proof (translation)
Distinguish the cases in `h1 : chi ω M a = 0`. Rewrite using `[h1, zero_mul]`. Assume the negation of the conclusion as `hn`. Conclude with `lift hL hM hU ha hb hn h1`. Distinguish the cases in `h2 : chi ω M b = 0`.

Rewrite using `[h2, mul_zero]`. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[mul_comm]`. Conclude with `lift hL hM hU hb ha hn h2`. Take `⟨u, hu, hu'⟩` from `exists_of_chi_ne_zero h1`.

Take `⟨w, hw, hw'⟩` from `exists_of_chi_ne_zero h2`. Rewrite using `[chi_eq hL hu hu', chi_eq hL hw hw', ← val_mul]`. Use `chi_eq hL (mul_mem hu hw) ?_` and prove the remaining obligations. Establish `e : a * b - ((u * w : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) = a * (b - (w : FiniteAdeleRing (𝓞 k) k)) + (w : FiniteAdeleRing (𝓞 k) k) * (a - (u : FiniteAdeleRing (𝓞 k) k))`. Rewrite using `[Units.val_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `inM_add (inM_mul ha hw') (inM_mul (unit_mem hw) hu')`.
-/
theorem chi_mul {ω : HeckeCharacter k} {M₀ M : ℕ} (hL : Lvl ω M₀ M) (hM : M ≠ 0) (hU : LiftUnit)
    {a b : FiniteAdeleRing (𝓞 k) k} (ha : a ∈ OH k) (hb : b ∈ OH k) :
    chi ω M (a * b) = chi ω M a * chi ω M b := by
  by_cases h1 : chi ω M a = 0
  · rw [h1, zero_mul]
    by_contra hn
    exact lift hL hM hU ha hb hn h1
  by_cases h2 : chi ω M b = 0
  · rw [h2, mul_zero]
    by_contra hn
    rw [mul_comm] at hn
    exact lift hL hM hU hb ha hn h2
  obtain ⟨u, hu, hu'⟩ := exists_of_chi_ne_zero h1
  obtain ⟨w, hw, hw'⟩ := exists_of_chi_ne_zero h2
  rw [chi_eq hL hu hu', chi_eq hL hw hw', ← val_mul]
  refine chi_eq hL (mul_mem hu hw) ?_
  have e : a * b - ((u * w : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) =
      a * (b - (w : FiniteAdeleRing (𝓞 k) k)) +
        (w : FiniteAdeleRing (𝓞 k) k) * (a - (u : FiniteAdeleRing (𝓞 k) k)) := by
    rw [Units.val_mul]; ring
  rw [e]
  exact inM_add (inM_mul ha hw') (inM_mul (unit_mem hw) hu')

/- English proof (translation)
Use `(GJMatrix.mem_finiteSchwartzBruhatPi k).2 ⟨?_, ?_⟩` and prove the remaining obligations. Use `(IsLocallyConstant.iff_exists_open f).2 fun x => ?_` and prove the remaining obligations. Use `⟨Set.pi Set.univ fun j => {y | InM M (y - x j)}, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `isOpen_set_pi Set.finite_univ fun j _ => ?_` and prove the remaining obligations. Conclude with `hO.preimage (continuous_id.sub continuous_const)`.

Introduce `j _`. Simplify using `using inM_zero (k := k) M`. Introduce `y hy`. Use `hinv x (y - x) fun j => hy j (Set.mem_univ j)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis.

Use `HasCompactSupport.of_support_subset_isCompact (K := Set.pi Set.univ fun _ : ι => (OH k : Set (FiniteAdeleRing (𝓞 k) k))) (isCompact_univ_pi fun _ => isCompact_integralFiniteAdeles k) ?_` and prove the remaining obligations. Introduce `x hx j _`. Conclude with `hs x hx j`.
-/
theorem mem_schwartzBruhat {ι : Type} [Fintype ι] {M : ℕ}
    (hO : IsOpen {x : FiniteAdeleRing (𝓞 k) k | InM M x}) {f : (ι → FiniteAdeleRing (𝓞 k) k) → ℂ}
    (hinv : ∀ x h, (∀ j, InM M (h j)) → f (x + h) = f x)
    (hs : ∀ x, f x ≠ 0 → ∀ j, x j ∈ OH k) : f ∈ GJMatrix.finiteSchwartzBruhatPi k := by
  refine (GJMatrix.mem_finiteSchwartzBruhatPi k).2 ⟨?_, ?_⟩
  · refine (IsLocallyConstant.iff_exists_open f).2 fun x => ?_
    refine ⟨Set.pi Set.univ fun j => {y | InM M (y - x j)}, ?_, ?_, ?_⟩
    · refine isOpen_set_pi Set.finite_univ fun j _ => ?_
      exact hO.preimage (continuous_id.sub continuous_const)
    · intro j _
      simpa using inM_zero (k := k) M
    · intro y hy
      have := hinv x (y - x) fun j => hy j (Set.mem_univ j)
      rwa [add_sub_cancel] at this
  · refine HasCompactSupport.of_support_subset_isCompact
      (K := Set.pi Set.univ fun _ : ι => (OH k : Set (FiniteAdeleRing (𝓞 k) k)))
      (isCompact_univ_pi fun _ => isCompact_integralFiniteAdeles k) ?_
    intro x hx j _
    exact hs x hx j

def gFun {ι : Type} (ω : HeckeCharacter k) (M : ℕ) (i₀ : ι) (x : ι → FiniteAdeleRing (𝓞 k) k) : ℂ :=
  if (∀ j, x j ∈ OH k) ∧ (∀ j, j ≠ i₀ → InM M (x j)) then chi ω M (x i₀) else 0

/- English proof (translation)
Establish `e : ((∀ j, (x + h) j ∈ OH k) ∧ (∀ j, j ≠ i₀ → InM M ((x + h) j))) ↔ ((∀ j, x j ∈ OH k) ∧ (∀ j, j ≠ i₀ → InM M (x j)))`. Use `and_congr (forall_congr' fun j => ?_) (forall_congr' fun j => imp_congr_right fun _ => ?_)` and prove the remaining obligations. Use `⟨fun H => ?_, fun H => add_mem H (mem_of_inM (hh j))⟩` and prove the remaining obligations. Use `sub_mem H (mem_of_inM (hh j))` as an intermediate fact. Simplify using `using this`.

Use `⟨fun H => ?_, fun H => inM_add H (hh j)⟩` and prove the remaining obligations. Use `inM_sub H (hh j)` as an intermediate fact. Simplify using `using this`. Unfold `gFun`. Simplify using `only [e]`.

Use `split_ifs`. Conclude with `chi_add hL _ (hh i₀)`. Both sides reduce to the same expression.
-/
theorem gFun_add {ι : Type} {ω : HeckeCharacter k} {M₀ M : ℕ} (hL : Lvl ω M₀ M) (i₀ : ι)
    (x h : ι → FiniteAdeleRing (𝓞 k) k) (hh : ∀ j, InM M (h j)) :
    gFun ω M i₀ (x + h) = gFun ω M i₀ x := by
  have e : ((∀ j, (x + h) j ∈ OH k) ∧ (∀ j, j ≠ i₀ → InM M ((x + h) j))) ↔
      ((∀ j, x j ∈ OH k) ∧ (∀ j, j ≠ i₀ → InM M (x j))) := by
    refine and_congr (forall_congr' fun j => ?_) (forall_congr' fun j => imp_congr_right fun _ => ?_)
    · refine ⟨fun H => ?_, fun H => add_mem H (mem_of_inM (hh j))⟩
      have := sub_mem H (mem_of_inM (hh j))
      simpa using this
    · refine ⟨fun H => ?_, fun H => inM_add H (hh j)⟩
      have := inM_sub H (hh j)
      simpa using this
  unfold gFun
  simp only [e]
  split_ifs
  · exact chi_add hL _ (hh i₀)
  · rfl

/- English proof (translation)
Unfold `gFun at h`. Use `split_ifs at h with hc`. Conclude with `⟨hc.1, hc.2, h⟩`. Conclude with `absurd rfl h`.
-/
theorem gFun_supp {ι : Type} {ω : HeckeCharacter k} {M : ℕ} {i₀ : ι}
    {x : ι → FiniteAdeleRing (𝓞 k) k} (h : gFun ω M i₀ x ≠ 0) :
    (∀ j, x j ∈ OH k) ∧ (∀ j, j ≠ i₀ → InM M (x j)) ∧ chi ω M (x i₀) ≠ 0 := by
  unfold gFun at h
  split_ifs at h with hc
  · exact ⟨hc.1, hc.2, h⟩
  · exact absurd rfl h

/- English proof (translation)
Use `⟨fun H => ?_, inM_mul ht'⟩` and prove the remaining obligations. Establish `h1 : InM M (t * y - y * (t - (u : FiniteAdeleRing (𝓞 k) k)))` using `inM_sub H (inM_mul hy ht)`. Establish `h2` using `inM_mul (unit_mem (inv_mem hu)) h1`. Establish `e : ((u⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) * (t * y - y * (t - (u : FiniteAdeleRing (𝓞 k) k))) = y`. Establish `: t * y - y * (t - (u : FiniteAdeleRing (𝓞 k) k)) = (u : FiniteAdeleRing (𝓞 k) k) * y` using `by ring`.

Rewrite using `[this, Units.inv_mul_cancel_left]`. Rewrite `h2` using `[e]`. Then use the resulting hypothesis.
-/
theorem inM_mul_iff {M : ℕ} {t y : FiniteAdeleRing (𝓞 k) k} {u : (FiniteAdeleRing (𝓞 k) k)ˣ}
    (hu : u ∈ finiteIntegralUnits k) (ht : InM M (t - (u : FiniteAdeleRing (𝓞 k) k)))
    (hy : y ∈ OH k) (ht' : t ∈ OH k) : InM M (t * y) ↔ InM M y := by
  refine ⟨fun H => ?_, inM_mul ht'⟩
  have h1 : InM M (t * y - y * (t - (u : FiniteAdeleRing (𝓞 k) k))) := inM_sub H (inM_mul hy ht)
  have h2 := inM_mul (unit_mem (inv_mem hu)) h1
  have e : ((u⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) *
      (t * y - y * (t - (u : FiniteAdeleRing (𝓞 k) k))) = y := by
    have : t * y - y * (t - (u : FiniteAdeleRing (𝓞 k) k)) = (u : FiniteAdeleRing (𝓞 k) k) * y := by ring
    rw [this, Units.inv_mul_cancel_left]
  rwa [e] at h2

/- English proof (translation)
Take `⟨c, hc, hs⟩` from `hv.2`. Establish `e : t = ∑ j, c j * (t * v j)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e]`. Conclude with `sum_mem fun j _ => mul_mem (hc j) (h j)`.
-/
theorem mem_of_prim {ι : Type} [Fintype ι] {v : ι → FiniteAdeleRing (𝓞 k) k} (hv : Prim v)
    {t : FiniteAdeleRing (𝓞 k) k} (h : ∀ j, t * v j ∈ OH k) : t ∈ OH k := by
  obtain ⟨c, hc, hs⟩ := hv.2
  have e : t = ∑ j, c j * (t * v j) := by
    calc t = t * ∑ j, c j * v j := by rw [hs, mul_one]
      _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  exact sum_mem fun j _ => mul_mem (hc j) (h j)

/- English proof (translation)
Distinguish the cases in `h0 : chi ω M t = 0`. Rewrite using `[h0, zero_mul]`. Assume the negation of the conclusion as `hn`. Take `⟨h1, -, h3⟩` from `gFun_supp hn`. Establish `ht : t ∈ OH k` using `mem_of_prim hv h1`.

Conclude with `lift hL hM hU ht (hv.1 i₀) h3 h0`. Establish `ht` using `mem_of_chi_ne_zero h0`. Take `⟨u, hu, hu'⟩` from `exists_of_chi_ne_zero h0`. Establish `e : ((∀ j, (t • v) j ∈ OH k) ∧ (∀ j, j ≠ i₀ → InM M ((t • v) j))) ↔ ((∀ j, v j ∈ OH k) ∧ (∀ j, j ≠ i₀ → InM M (v j)))`. Use `and_congr ?_ (forall_congr' fun j => imp_congr_right fun _ => inM_mul_iff hu hu' (hv.1 j) ht)` and prove the remaining obligations.

Conclude with `⟨fun _ => hv.1, fun _ j => mul_mem ht (hv.1 j)⟩`. Unfold `gFun`. Simplify using `only [e]`. Use `split_ifs`. Conclude with `chi_mul hL hM hU ht (hv.1 i₀)`.

Rewrite using `[mul_zero]`.
-/
theorem gFun_smul {ι : Type} [Fintype ι] {ω : HeckeCharacter k} {M₀ M : ℕ} (hL : Lvl ω M₀ M)
    (hM : M ≠ 0) (hU : LiftUnit) (i₀ : ι) {v : ι → FiniteAdeleRing (𝓞 k) k} (hv : Prim v)
    (t : FiniteAdeleRing (𝓞 k) k) :
    gFun ω M i₀ (t • v) = chi ω M t * gFun ω M i₀ v := by
  by_cases h0 : chi ω M t = 0
  · rw [h0, zero_mul]
    by_contra hn
    obtain ⟨h1, -, h3⟩ := gFun_supp hn
    have ht : t ∈ OH k := mem_of_prim hv h1
    exact lift hL hM hU ht (hv.1 i₀) h3 h0
  have ht := mem_of_chi_ne_zero h0
  obtain ⟨u, hu, hu'⟩ := exists_of_chi_ne_zero h0
  have e : ((∀ j, (t • v) j ∈ OH k) ∧ (∀ j, j ≠ i₀ → InM M ((t • v) j))) ↔
      ((∀ j, v j ∈ OH k) ∧ (∀ j, j ≠ i₀ → InM M (v j))) := by
    refine and_congr ?_ (forall_congr' fun j => imp_congr_right fun _ => inM_mul_iff hu hu' (hv.1 j) ht)
    exact ⟨fun _ => hv.1, fun _ j => mul_mem ht (hv.1 j)⟩
  unfold gFun
  simp only [e]
  split_ifs
  · exact chi_mul hL hM hU ht (hv.1 i₀)
  · rw [mul_zero]

/- English proof (translation)
Introduce `k _ _ ω`. Take `⟨M₀, hM₀, hc⟩` from `hC k ω`. Use `⟨M₀, hM₀, fun M hM hd ι _ _ i₀ => ?_⟩` and prove the remaining obligations. Establish `hL : Lvl ω M₀ M` using `⟨hd, hc⟩`. Establish `hO` using `((hT k).1 M hM).1`.

Establish `hone : chi ω M 1 = 1`. Use `chi_eq hL (a := 1) (u := 1) (one_mem _) (by simpa using inM_zero (k := k) M)` as an intermediate fact. Rewrite using `[this]`. Simplify using `[val]`. Use `⟨gFun ω M i₀, fun x => chi ω M (x ()), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `mem_schwartzBruhat hO (fun x h hh => gFun_add hL i₀ x h hh) fun x hx => (gFun_supp hx).1`. Use `mem_schwartzBruhat hO (fun x h hh => chi_add hL _ (hh ())) fun x hx j => ?_` and prove the remaining obligations. Conclude with `mem_of_chi_ne_zero hx`. Unfold `gFun`. Rewrite using `[if_pos]`.

Simplify using `using hone`. Use `⟨fun j => ?_, fun j hj => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : j = i₀`. Substitute `h` using the available equality. Simplify using `using one_mem (OH k)`.

Simplify using `[Pi.single_eq_of_ne h, zero_mem]`. Simplify `inM_zero (k := k) M` using `[Pi.single_eq_of_ne hj]`. Introduce `u hu`. Conclude with `chi_eq hL hu (by simpa using inM_zero (k := k) M)`. Introduce `t`.

Use `⟨?_, mem_of_chi_ne_zero⟩` and prove the remaining obligations. Distinguish the cases in `h : chi ω M t = 0`. Simplify using `[h]`. Take `⟨u, hu, hu'⟩` from `exists_of_chi_ne_zero h show ‖chi ω M t‖ ≤ 1`. Rewrite using `[chi_eq hL hu hu', norm_val]`.

Introduce and unpack `rfl t`. Distinguish the cases in `h : chi (1 : HeckeCharacter k) M t = 0`. Conclude with `⟨0, le_rfl, by simp [h]⟩`. Take `⟨u, hu, hu'⟩` from `exists_of_chi_ne_zero h`. Use `⟨1, zero_le_one, ?_⟩` and prove the remaining obligations.

Use `show chi (1 : HeckeCharacter k) M t = ((1 : ℝ) : ℂ)`. Rewrite using `[chi_eq hL hu hu']`. Establish `: (1 : HeckeCharacter k).toIdele (ofFinite u) = 1` using `rfl`. Simplify using `[val, this]`. Introduce `v hv`.

Use `⟨fun t => gFun_smul hL hM hU i₀ hv t, fun h j hj => (gFun_supp h).2.1 j hj, fun h => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h0 : gFun ω M i₀ v = 0`. Conclude with `Or.inl h0`. Use `right`. Take `⟨h1, h2, h3⟩` from `gFun_supp h0`.

Take `⟨u, hu, hu'⟩` from `exists_of_chi_ne_zero h3`. Establish `hval : gFun ω M i₀ v = chi ω M (v i₀)`. Unfold `gFun`. Rewrite using `[if_pos ⟨h1, h2⟩]`. Rewrite using `[hval, chi_eq hL hu hu']`.

Establish `e : (u : FiniteAdeleRing (𝓞 k) k) - 1 = (v i₀ - 1) - (v i₀ - u)` using `by ring`. Establish `h4 : InM M₀ ((u : FiniteAdeleRing (𝓞 k) k) - 1)`. Rewrite using `[e]`. Conclude with `inM_sub h (inM_dvd hd hu')`. Simplify using `[val, hc u hu h4]`.
-/
theorem finFun (hC : CondM) (hU : LiftUnit) (hT : InMTop) : FinFun := by
  intro k _ _ ω
  obtain ⟨M₀, hM₀, hc⟩ := hC k ω
  refine ⟨M₀, hM₀, fun M hM hd ι _ _ i₀ => ?_⟩
  have hL : Lvl ω M₀ M := ⟨hd, hc⟩
  have hO := ((hT k).1 M hM).1
  have hone : chi ω M 1 = 1 := by
    have := chi_eq hL (a := 1) (u := 1) (one_mem _) (by simpa using inM_zero (k := k) M)
    rw [this]
    simp [val]
  refine ⟨gFun ω M i₀, fun x => chi ω M (x ()), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mem_schwartzBruhat hO (fun x h hh => gFun_add hL i₀ x h hh) fun x hx => (gFun_supp hx).1
  · refine mem_schwartzBruhat hO (fun x h hh => chi_add hL _ (hh ())) fun x hx j => ?_
    exact mem_of_chi_ne_zero hx
  · unfold gFun
    rw [if_pos]
    · simpa using hone
    · refine ⟨fun j => ?_, fun j hj => ?_⟩
      · by_cases h : j = i₀
        · subst h; simpa using one_mem (OH k)
        · simp [Pi.single_eq_of_ne h, zero_mem]
      · simpa [Pi.single_eq_of_ne hj] using inM_zero (k := k) M
  · intro u hu
    exact chi_eq hL hu (by simpa using inM_zero (k := k) M)
  · intro t
    refine ⟨?_, mem_of_chi_ne_zero⟩
    by_cases h : chi ω M t = 0
    · simp [h]
    · obtain ⟨u, hu, hu'⟩ := exists_of_chi_ne_zero h
      show ‖chi ω M t‖ ≤ 1
      rw [chi_eq hL hu hu', norm_val]
  · rintro rfl t
    by_cases h : chi (1 : HeckeCharacter k) M t = 0
    · exact ⟨0, le_rfl, by simp [h]⟩
    · obtain ⟨u, hu, hu'⟩ := exists_of_chi_ne_zero h
      refine ⟨1, zero_le_one, ?_⟩
      show chi (1 : HeckeCharacter k) M t = ((1 : ℝ) : ℂ)
      rw [chi_eq hL hu hu']
      have : (1 : HeckeCharacter k).toIdele (ofFinite u) = 1 := rfl
      simp [val, this]
  · intro v hv
    refine ⟨fun t => gFun_smul hL hM hU i₀ hv t, fun h j hj => (gFun_supp h).2.1 j hj, fun h => ?_⟩
    by_cases h0 : gFun ω M i₀ v = 0
    · exact Or.inl h0
    right
    obtain ⟨h1, h2, h3⟩ := gFun_supp h0
    obtain ⟨u, hu, hu'⟩ := exists_of_chi_ne_zero h3
    have hval : gFun ω M i₀ v = chi ω M (v i₀) := by
      unfold gFun; rw [if_pos ⟨h1, h2⟩]
    rw [hval, chi_eq hL hu hu']
    have e : (u : FiniteAdeleRing (𝓞 k) k) - 1 = (v i₀ - 1) - (v i₀ - u) := by ring
    have h4 : InM M₀ ((u : FiniteAdeleRing (𝓞 k) k) - 1) := by
      rw [e]; exact inM_sub h (inM_dvd hd hu')
    simp [val, hc u hu h4]

end GlobalTheory.CompanionTheory.RgEisFin

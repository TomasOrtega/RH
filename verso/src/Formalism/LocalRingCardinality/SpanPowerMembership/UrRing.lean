import Mathlib

noncomputable section

namespace Formalism.BasicNotions.Examples₂.Ur

open Polynomial IsLocalRing

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

def ball (M : Subfield C) : Subring C where
  carrier := {x | x ∈ M ∧ ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by rw [norm_mul]; exact mul_le_one₀ ha.2 (norm_nonneg _) hb.2⟩
  one_mem' := ⟨one_mem _, norm_one.le⟩
  add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha.2 hb.2)⟩
  zero_mem' := ⟨zero_mem _, by simp⟩
  neg_mem' := fun {a} ha => ⟨neg_mem ha.1, by rw [norm_neg]; exact ha.2⟩

variable (M : Subfield C)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩`. Rewrite using `[Subring.coe_mul, norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) c.2.2`. Introduce `h`.

Distinguish the cases in `ha : (a : C) = 0`. Establish `: b = 0` using `Subtype.ext (by rw [ha, norm_zero] at h; exact norm_le_zero_iff.mp h)`. Rewrite using `[this]`. Conclude with `dvd_zero _`. Use `⟨⟨b / a, div_mem b.2.1 a.2.1, ?_⟩, Subtype.ext ?_⟩` and prove the remaining obligations.

Rewrite using `[norm_div]`. Conclude with `div_le_one_of_le₀ h (norm_nonneg _)`. Use `show (b : C) = a * (b / a)`. Clear the denominators using the available nonvanishing facts.
-/
theorem dvd_iff (a b : ball M) : a ∣ b ↔ ‖(b : C)‖ ≤ ‖(a : C)‖ := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [Subring.coe_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) c.2.2
  · intro h
    by_cases ha : (a : C) = 0
    · have : b = 0 := Subtype.ext (by rw [ha, norm_zero] at h; exact norm_le_zero_iff.mp h)
      rw [this]; exact dvd_zero _
    · refine ⟨⟨b / a, div_mem b.2.1 a.2.1, ?_⟩, Subtype.ext ?_⟩
      · rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
      · show (b : C) = a * (b / a)
        field_simp

/- English proof (translation)
Rewrite using `[isUnit_iff_dvd_one, dvd_iff, Subring.coe_one, norm_one]`. Conclude with `⟨fun h => le_antisymm a.2.2 h, fun h => h.ge⟩`.
-/
theorem isUnit_iff (a : ball M) : IsUnit a ↔ ‖(a : C)‖ = 1 := by
  rw [isUnit_iff_dvd_one, dvd_iff, Subring.coe_one, norm_one]
  exact ⟨fun h => le_antisymm a.2.2 h, fun h => h.ge⟩

instance : IsLocalRing (ball M) := .of_nonunits_add fun a b ha hb => by
  rw [mem_nonunits_iff, isUnit_iff] at *
  exact ((IsUltrametricDist.norm_add_le_max (a : C) b).trans_lt
    (max_lt (lt_of_le_of_ne a.2.2 ha) (lt_of_le_of_ne b.2.2 hb))).ne

/- English proof (translation)
Rewrite using `[mem_maximalIdeal, mem_nonunits_iff, isUnit_iff]`. Conclude with `⟨fun h => lt_of_le_of_ne a.2.2 h, fun h => h.ne⟩`.
-/
theorem mem_max (a : ball M) : a ∈ maximalIdeal (ball M) ↔ ‖(a : C)‖ < 1 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff]
  exact ⟨fun h => lt_of_le_of_ne a.2.2 h, fun h => h.ne⟩

def toM : ball M →+* M := (ball M).subtype.codRestrict M.toSubring fun x => x.2.1

instance : Algebra (ball M) M := (toM M).toAlgebra

instance : IsScalarTower (ball M) M C := IsScalarTower.of_algebraMap_eq fun _ => rfl

instance : IsFractionRing (ball M) M := by
  have hinj : Function.Injective (algebraMap (ball M) M) := fun a b h =>
    Subtype.ext (congrArg (fun t : M => (t : C)) h)
  have : FaithfulSMul (ball M) M := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  refine IsFractionRing.of_field _ _ fun z => ?_
  by_cases h : ‖(z : C)‖ ≤ 1
  · exact ⟨⟨z, z.2, h⟩, 1, by rw [map_one, div_one]; rfl⟩
  · have h1 : ‖(z : C)⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ (not_le.mp h).le
    refine ⟨1, ⟨(z : C)⁻¹, inv_mem z.2, h1⟩, ?_⟩
    rw [map_one, one_div]
    exact Subtype.ext (inv_inv (z : C)).symm

def iC : FractionRing (ball M) →+* C := IsFractionRing.lift (g := (ball M).subtype) Subtype.val_injective

/- English proof (translation)
The claim follows from `IsFractionRing.lift_algebraMap _ a`.
-/
theorem iC_alg (a : ball M) : iC M (algebraMap _ _ a) = a := IsFractionRing.lift_algebraMap _ a

/- English proof (translation)
Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := ball M) x`. Rewrite using `[map_div₀, iC_alg, iC_alg]`. Conclude with `div_mem a.2.1 b.2.1`.
-/
theorem iC_mem (x : FractionRing (ball M)) : iC M x ∈ M := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := ball M) x
  rw [map_div₀, iC_alg, iC_alg]; exact div_mem a.2.1 b.2.1

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨⟨iC M x, iC_mem M x, h⟩, (iC M).injective (iC_alg M _)⟩, fun ⟨a, h⟩ => by rw [← h, iC_alg]; exact a.2.2⟩`.
-/
theorem iC_int (x : FractionRing (ball M)) :
    ‖iC M x‖ ≤ 1 ↔ x ∈ (algebraMap (ball M) (FractionRing (ball M))).range :=
  ⟨fun h => ⟨⟨iC M x, iC_mem M x, h⟩, (iC M).injective (iC_alg M _)⟩,
    fun ⟨a, h⟩ => by rw [← h, iC_alg]; exact a.2.2⟩

/- English proof (translation)
Set `V` to `(NormedField.valuation (K := C)).integer`. Set `_ : Algebra (ball M) V` to `(Subring.inclusion (S := ball M) (T := V) fun y hy => by show ‖y‖₊ ≤ 1`. Conclude with `hy.2).toAlgebra` after adjusting the coercions. Establish `: IsScalarTower (ball M) V C` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `h2` using `(Valuation.integer.integers (NormedField.valuation (K := C))).isIntegral_iff_v_le_one.mp (h.tower_top (A := V))`.

Conclude with `(show ‖x‖₊ ≤ 1 from h2)` after adjusting the coercions.
-/
theorem norm_le_of_integral {x : C} (h : IsIntegral (ball M) x) : ‖x‖ ≤ 1 := by
  let V := (NormedField.valuation (K := C)).integer
  let _ : Algebra (ball M) V := (Subring.inclusion (S := ball M) (T := V) fun y hy => by
    show ‖y‖₊ ≤ 1
    exact_mod_cast hy.2).toAlgebra
  have : IsScalarTower (ball M) V C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := C))).isIntegral_iff_v_le_one.mp
    (h.tower_top (A := V))
  exact_mod_cast (show ‖x‖₊ ≤ 1 from h2)

/- English proof (translation)
The claim follows from `(lifts_iff_coeff_lifts g).mpr fun n => ⟨⟨g.coeff n, (g.coeff n).2, h n⟩, rfl⟩`.
-/
theorem lifts_of_coeff (g : M[X]) (h : ∀ n, ‖(g.coeff n : C)‖ ≤ 1) : g ∈ lifts (algebraMap (ball M) M) :=
  (lifts_iff_coeff_lifts g).mpr fun n => ⟨⟨g.coeff n, (g.coeff n).2, h n⟩, rfl⟩

/- English proof (translation)
Rewrite using `[aeval_eq_sum_range]`. Establish `: (Finset.range (g.natDegree + 1)).Nonempty` using `⟨0, by simp⟩`. Take `⟨i, -, hi⟩` from `IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty this (fun i => g.coeff i • α ^ i)`. Use `hi.trans_lt ?_` and prove the remaining obligations. Establish `h1 : ‖(g.coeff i : C)‖ < 1` using `(mem_max M _).mp ((residue_eq_zero_iff _).mp (by`.

Rewrite using `[← coeff_map, h, coeff_zero]))`. Rewrite using `[Algebra.smul_def, norm_mul, norm_pow]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h1 (pow_le_one₀ (norm_nonneg _) hα)`.
-/
theorem norm_aeval_lt (g : (ball M)[X]) (h : g.map (residue (ball M)) = 0) {α : C} (hα : ‖α‖ ≤ 1) :
    ‖aeval α g‖ < 1 := by
  rw [aeval_eq_sum_range]
  have : (Finset.range (g.natDegree + 1)).Nonempty := ⟨0, by simp⟩
  obtain ⟨i, -, hi⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty this
    (fun i => g.coeff i • α ^ i)
  refine hi.trans_lt ?_
  have h1 : ‖(g.coeff i : C)‖ < 1 := (mem_max M _).mp ((residue_eq_zero_iff _).mp (by
    rw [← coeff_map, h, coeff_zero]))
  rw [Algebra.smul_def, norm_mul, norm_pow]
  exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h1 (pow_le_one₀ (norm_nonneg _) hα)

/- English proof (translation)
Rewrite using `[aeval_eq_sum_range]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, norm_mul, norm_pow]`. Conclude with `mul_le_one₀ (g.coeff i).2.2 (by positivity) (pow_le_one₀ (norm_nonneg _) hα)`.
-/
theorem norm_aeval_le (g : (ball M)[X]) {α : C} (hα : ‖α‖ ≤ 1) : ‖aeval α g‖ ≤ 1 := by
  rw [aeval_eq_sum_range]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [Algebra.smul_def, norm_mul, norm_pow]
  exact mul_le_one₀ (g.coeff i).2.2 (by positivity) (pow_le_one₀ (norm_nonneg _) hα)

def Disc (M : Subfield C) (π : C) : Prop := ∀ x ∈ M, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖π‖ ^ n

variable {M} {π : C} (hπ : π ∈ M) (h0 : π ≠ 0) (h1 : ‖π‖ < 1) (hD : Disc M π)

include h0 hD in
/- English proof (translation)
Use extensionality with `a`. Rewrite using `[mem_max, Ideal.mem_span_singleton, dvd_iff]`. Use `⟨fun h => ?_, fun h => h.trans_lt h1⟩` and prove the remaining obligations. Distinguish the cases in `ha : (a : C) = 0`. Rewrite using `[ha, norm_zero]`.

Conclude with `norm_nonneg _`. Take `⟨n, hn⟩` from `hD a a.2.1 ha`. Establish `hp : 0 < ‖π‖` using `norm_pos_iff.mpr h0`. Rewrite `h`, the goal using `[hn]`. Establish `: 0 < n` using `(zpow_lt_one_iff_right_of_lt_one₀ hp h1).mp h`.

Conclude with `(zpow_le_zpow_right_of_le_one₀ hp h1.le (show 1 ≤ n by omega)).trans (zpow_one _).le`.
-/
theorem max_eq : maximalIdeal (ball M) = Ideal.span {(⟨π, hπ, h1.le⟩ : ball M)} := by
  ext a
  rw [mem_max, Ideal.mem_span_singleton, dvd_iff]
  refine ⟨fun h => ?_, fun h => h.trans_lt h1⟩
  by_cases ha : (a : C) = 0
  · rw [ha, norm_zero]; exact norm_nonneg _
  obtain ⟨n, hn⟩ := hD a a.2.1 ha
  have hp : 0 < ‖π‖ := norm_pos_iff.mpr h0
  rw [hn] at h ⊢
  have : 0 < n := (zpow_lt_one_iff_right_of_lt_one₀ hp h1).mp h
  exact (zpow_le_zpow_right_of_le_one₀ hp h1.le (show 1 ≤ n by omega)).trans (zpow_one _).le

include hπ h0 h1 hD in
/- English proof (translation)
Establish `hp : 0 < ‖π‖` using `norm_pos_iff.mpr h0`. Use `IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨⟨π, hπ, h1.le⟩, IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ (fun h => h0 (congrArg Subtype.val h)) (max_eq hπ h0 h1 hD), fun {x} hx => ?_⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `hD x x.2.1 (fun h => hx (Subtype.ext h))`. Establish `: 0 ≤ n` using `(zpow_le_one_iff_right_of_lt_one₀ hp h1).mp (hn ▸ x.2.2)`. Use `lift n to ℕ using this`.

Rewrite `hn` using `[zpow_natCast, ← norm_pow]`. Conclude with `⟨n, associated_of_dvd_dvd ((dvd_iff M _ _).mpr hn.le) ((dvd_iff M _ _).mpr hn.ge)⟩`.
-/
theorem isDVR : IsDiscreteValuationRing (ball M) := by
  have hp : 0 < ‖π‖ := norm_pos_iff.mpr h0
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨⟨π, hπ, h1.le⟩,
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ (fun h => h0 (congrArg Subtype.val h))
      (max_eq hπ h0 h1 hD), fun {x} hx => ?_⟩
  obtain ⟨n, hn⟩ := hD x x.2.1 (fun h => hx (Subtype.ext h))
  have : 0 ≤ n := (zpow_le_one_iff_right_of_lt_one₀ hp h1).mp (hn ▸ x.2.2)
  lift n to ℕ using this
  rw [zpow_natCast, ← norm_pow] at hn
  exact ⟨n, associated_of_dvd_dvd ((dvd_iff M _ _).mpr hn.le) ((dvd_iff M _ _).mpr hn.ge)⟩

include hπ h0 h1 hD in
/- English proof (translation)
Establish `hp : 0 < ‖π‖` using `norm_pos_iff.mpr h0`. Establish `key : ∀ n : ℕ, ((maximalIdeal (ball M) ^ n : Ideal (ball M)) : Set (ball M)) = Metric.closedBall 0 (‖π‖ ^ n)` using `fun n => by`. Use extensionality with `a`. Rewrite using `[max_eq hπ h0 h1 hD, Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton, dvd_iff, Metric.mem_closedBall, Subtype.dist_eq, ZeroMemClass.coe_zero, dist_zero_right, ← norm_pow]`. Both sides reduce to the same expression.

Use `isAdic_iff.mpr ⟨fun n => ?_, fun s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[key]`. Conclude with `IsUltrametricDist.isOpen_closedBall _ (pow_pos hp n).ne'`. Take `⟨ε, hε, h⟩` from `Metric.mem_nhds_iff.mp hs`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one hε h1`.

Conclude with `⟨n, by rw [key]; exact (Metric.closedBall_subset_ball hn).trans h⟩`.
-/
theorem isAdic : IsAdic (maximalIdeal (ball M)) := by
  have hp : 0 < ‖π‖ := norm_pos_iff.mpr h0
  have key : ∀ n : ℕ, ((maximalIdeal (ball M) ^ n : Ideal (ball M)) : Set (ball M)) =
      Metric.closedBall 0 (‖π‖ ^ n) := fun n => by
    ext a
    rw [max_eq hπ h0 h1 hD, Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton, dvd_iff,
      Metric.mem_closedBall, Subtype.dist_eq, ZeroMemClass.coe_zero, dist_zero_right, ← norm_pow]
    rfl
  refine isAdic_iff.mpr ⟨fun n => ?_, fun s hs => ?_⟩
  · rw [key]; exact IsUltrametricDist.isOpen_closedBall _ (pow_pos hp n).ne'
  · obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.mp hs
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε h1
    exact ⟨n, by rw [key]; exact (Metric.closedBall_subset_ball hn).trans h⟩

/- English proof (translation)
The claim follows from `hc.inter (isClosed_le continuous_norm continuous_const)`.
-/
theorem ball_closed (hc : IsClosed (M : Set C)) : IsClosed (ball M : Set C) :=
  hc.inter (isClosed_le continuous_norm continuous_const)

include hπ h0 h1 hD in
/- English proof (translation)
Use `(ball_closed hc).completeSpace_coe` as an intermediate fact. Conclude with `(isAdic hπ h0 h1 hD).isAdicComplete_iff.mpr ⟨this, inferInstance⟩`.
-/
theorem isComplete [CompleteSpace C] (hc : IsClosed (M : Set C)) :
    IsAdicComplete (maximalIdeal (ball M)) (ball M) := by
  have := (ball_closed hc).completeSpace_coe
  exact (isAdic hπ h0 h1 hD).isAdicComplete_iff.mpr ⟨this, inferInstance⟩

/- English proof (translation)
Use `zorn_le_nonempty₀ {M | Disc M π} (fun c hc hch y hy => ⟨sSup c, fun x hx hx0 => ?_, fun z hz => le_sSup hz⟩) L hL` and prove the remaining obligations. Take `⟨S, hS, hxS⟩` from `(Subfield.mem_sSup_of_directedOn ⟨y, hy⟩ hch.directedOn).mp hx`. Conclude with `hc hS x hxS hx0`.
-/
theorem exists_max (L : Subfield C) (π : C) (hL : Disc L π) :
    ∃ M, L ≤ M ∧ Maximal (fun M => Disc M π) M := by
  refine zorn_le_nonempty₀ {M | Disc M π} (fun c hc hch y hy => ⟨sSup c, fun x hx hx0 => ?_,
    fun z hz => le_sSup hz⟩) L hL
  obtain ⟨S, hS, hxS⟩ := (Subfield.mem_sSup_of_directedOn ⟨y, hy⟩ hch.directedOn).mp hx
  exact hc hS x hxS hx0

/- English proof (translation)
Establish `: Disc M.topologicalClosure π` using `fun x hx hx0 => by`. Take `⟨y, hy, hxy⟩` from `Metric.mem_closure_iff.mp (show x ∈ closure (M : Set C) from hx) ‖x‖ (norm_pos_iff.mpr hx0)`. Rewrite `hxy` using `[dist_comm, dist_eq_norm]`. Establish `e : ‖y‖ = ‖x‖`. Use `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hxy.ne` as an intermediate fact.

Rewrite `this` using `[sub_add_cancel, max_eq_right hxy.le]`. Then use the resulting hypothesis. Take `⟨n, hn⟩` from `hM.1 y hy (by rintro rfl; exact hx0 (by simpa using e.symm))`. Conclude with `⟨n, e ▸ hn⟩`. Conclude with `isClosed_of_closure_subset (hM.2 this M.le_topologicalClosure)`.
-/
theorem closed_of_max (hM : Maximal (fun M => Disc M π) M) : IsClosed (M : Set C) := by
  have : Disc M.topologicalClosure π := fun x hx hx0 => by
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp (show x ∈ closure (M : Set C) from hx) ‖x‖
      (norm_pos_iff.mpr hx0)
    rw [dist_comm, dist_eq_norm] at hxy
    have e : ‖y‖ = ‖x‖ := by
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hxy.ne
      rwa [sub_add_cancel, max_eq_right hxy.le] at this
    obtain ⟨n, hn⟩ := hM.1 y hy (by rintro rfl; exact hx0 (by simpa using e.symm))
    exact ⟨n, e ▸ hn⟩
  exact isClosed_of_closure_subset (hM.2 this M.le_topologicalClosure)

/- English proof (translation)
Use `IsAlgClosed.of_exists_root _ fun fb hm hirr => ?_` and prove the remaining obligations. Take `⟨f, hf, hdeg, hfm⟩` from `lifts_and_degree_eq_and_monic (show fb ∈ lifts (residue (ball M)) from map_surjective _ residue_surjective fb) hm`. Establish `hd0 : f.degree ≠ 0` using `by rw [hdeg]; exact (degree_pos_of_irreducible hirr).ne'`. Take `⟨α, hα⟩` from `IsAlgClosed.exists_aeval_eq_zero_of_injective C Subtype.val_injective f hd0`. Establish `hint : IsIntegral (ball M) α` using `⟨f, hfm, hα⟩`.

Establish `hα1` using `norm_le_of_integral M hint`. Establish `unit : ∀ g : (ball M)[X], g.degree < f.degree → g.map (residue _) ≠ 0 → ‖aeval α g‖ = 1`. Introduce `g hg hg0`. Establish `hc : IsCoprime fb (g.map (residue _))` using `hirr.coprime_iff_not_dvd.mpr fun hdv => absurd ((degree_le_of_dvd hdv hg0).trans degree_map_le) (not_le.mpr (hdeg ▸ hg))`. Take `⟨a, b, hab⟩` from `hc`.

Take `⟨a, rfl⟩` from `map_surjective _ residue_surjective a`. Take `⟨b, rfl⟩` from `map_surjective _ residue_surjective b`. Establish `h2` using `norm_aeval_lt M (a * f + b * g - 1) (by rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, hf, hab]; simp) hα1`. Rewrite `h2` using `[map_sub, map_add, map_mul, map_mul, hα, mul_zero, zero_add, map_one]`. Establish `h3 : ‖aeval α b * aeval α g‖ = 1`.

Use `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := aeval α b * aeval α g - 1) (y := 1) (by rw [norm_one]; exact h2.ne)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, norm_one, max_eq_right h2.le]`. Then use the resulting hypothesis. Rewrite `h3` using `[norm_mul]`. Use `le_antisymm (norm_aeval_le M g hα1) ?_` and prove the remaining obligations. Use polynomial arithmetic with `[norm_aeval_le M b hα1, norm_nonneg (aeval α g), norm_nonneg (aeval α b)]`.

Establish `hintM : IsIntegral M α` using `hint.tower_top`. Establish `hDisc : Disc (IntermediateField.adjoin M {α}).toSubfield π` using `fun x hx hx0 => by`. Establish `hx' : x ∈ Algebra.adjoin M {α}`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hintM.isAlgebraic]`. Conclude with `hx`.

Rewrite `hx'` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨q, rfl⟩` from `hx'`. Set `F` to `f.map (algebraMap (ball M) M)`. Establish `hF : F.Monic` using `hfm.map _`. Set `g` to `q %ₘ F`.

Establish `hgx : aeval α g = aeval α q` using `aeval_modByMonic_eq_self_of_root (by rw [aeval_map_algebraMap, hα])`. Establish `hg0 : g ≠ 0` using `fun h => hx0 (by show aeval α q = 0`. Rewrite using `[← hgx, h, map_zero])`. Take `⟨i, hi, hmax⟩` from `g.support.exists_max_image (fun n => ‖(g.coeff n : C)‖) (support_nonempty.mpr hg0)`. Establish `hc0 : g.coeff i ≠ 0` using `mem_support_iff.mp hi`.

Establish `hc0' : (g.coeff i : C) ≠ 0` using `fun h => hc0 (Subtype.ext h)`. Take `⟨g0, hg0e, hg0d⟩` from `(mem_lifts_and_degree_eq (lifts_of_coeff M (Polynomial.C (g.coeff i)⁻¹ * g) fun n => by`. Rewrite using `[coeff_C_mul]`. Use `push_cast`. Rewrite using `[norm_mul, norm_inv, inv_mul_le_one₀ (norm_pos_iff.mpr hc0')]`.

Distinguish the cases in `hn : n ∈ g.support`. Conclude with `hmax n hn`. Rewrite using `[notMem_support_iff.mp hn]`. Use the proof step `simp))`. Establish `hco : g0.coeff i = 1` using `IsFractionRing.injective (ball M) M (by`.

Rewrite using `[← coeff_map, hg0e, coeff_C_mul, inv_mul_cancel₀ hc0, map_one])`. Establish `hu` using `unit g0 (by`. Rewrite using `[hg0d, degree_C_mul (inv_ne_zero hc0), ← hfm.degree_map (algebraMap (ball M) M)]`. Conclude with `degree_modByMonic_lt q hF) (fun h => by`. Use `congrArg (coeff · i) h` as an intermediate fact.

Simplify using `[hco] at this)`. Rewrite `hu` using `[← aeval_map_algebraMap M, hg0e, map_mul, aeval_C, norm_mul, hgx]`. Take `⟨n, hn⟩` from `hM.1 _ (g.coeff i).2 hc0'`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `e : ‖algebraMap M C (g.coeff i)⁻¹‖ = ‖(g.coeff i : C)‖⁻¹` using `by rw [map_inv₀, norm_inv]; rfl`.

Rewrite `hu` using `[e, inv_mul_eq_one₀ (norm_ne_zero_iff.mpr hc0')]`. Conclude with `hu.symm.trans hn`. Establish `hαM : α ∈ M` using `hM.2 hDisc (fun y hy => (IntermediateField.adjoin M {α}).algebraMap_mem ⟨y, hy⟩) (IntermediateField.mem_adjoin_simple_self M α)`. Use `⟨residue _ ⟨α, hαM, hα1⟩, ?_⟩` and prove the remaining obligations. Establish `: f.eval ⟨α, hαM, hα1⟩ = 0` using `Subtype.val_injective (by`.

Conclude with `(aeval_algebraMap_apply C (⟨α, hαM, hα1⟩ : ball M) f).symm.trans hα)`. Rewrite using `[← hf, eval_map, eval₂_at_apply, this, map_zero]`.
-/
theorem res_algClosed [IsAlgClosed C] (hM : Maximal (fun M => Disc M π) M) :
    IsAlgClosed (ResidueField (ball M)) := by
  refine IsAlgClosed.of_exists_root _ fun fb hm hirr => ?_
  obtain ⟨f, hf, hdeg, hfm⟩ := lifts_and_degree_eq_and_monic
    (show fb ∈ lifts (residue (ball M)) from map_surjective _ residue_surjective fb) hm
  have hd0 : f.degree ≠ 0 := by rw [hdeg]; exact (degree_pos_of_irreducible hirr).ne'
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_aeval_eq_zero_of_injective C Subtype.val_injective f hd0
  have hint : IsIntegral (ball M) α := ⟨f, hfm, hα⟩
  have hα1 := norm_le_of_integral M hint
  have unit : ∀ g : (ball M)[X], g.degree < f.degree → g.map (residue _) ≠ 0 → ‖aeval α g‖ = 1 := by
    intro g hg hg0
    have hc : IsCoprime fb (g.map (residue _)) := hirr.coprime_iff_not_dvd.mpr fun hdv =>
      absurd ((degree_le_of_dvd hdv hg0).trans degree_map_le) (not_le.mpr (hdeg ▸ hg))
    obtain ⟨a, b, hab⟩ := hc
    obtain ⟨a, rfl⟩ := map_surjective _ residue_surjective a
    obtain ⟨b, rfl⟩ := map_surjective _ residue_surjective b
    have h2 := norm_aeval_lt M (a * f + b * g - 1)
      (by rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, hf, hab]; simp) hα1
    rw [map_sub, map_add, map_mul, map_mul, hα, mul_zero, zero_add, map_one] at h2
    have h3 : ‖aeval α b * aeval α g‖ = 1 := by
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (x := aeval α b * aeval α g - 1) (y := 1) (by rw [norm_one]; exact h2.ne)
      rwa [sub_add_cancel, norm_one, max_eq_right h2.le] at this
    rw [norm_mul] at h3
    refine le_antisymm (norm_aeval_le M g hα1) ?_
    nlinarith [norm_aeval_le M b hα1, norm_nonneg (aeval α g), norm_nonneg (aeval α b)]
  have hintM : IsIntegral M α := hint.tower_top
  have hDisc : Disc (IntermediateField.adjoin M {α}).toSubfield π := fun x hx hx0 => by
    have hx' : x ∈ Algebra.adjoin M {α} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hintM.isAlgebraic]; exact hx
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hx'
    obtain ⟨q, rfl⟩ := hx'
    let F := f.map (algebraMap (ball M) M)
    have hF : F.Monic := hfm.map _
    let g := q %ₘ F
    have hgx : aeval α g = aeval α q := aeval_modByMonic_eq_self_of_root (by rw [aeval_map_algebraMap, hα])
    have hg0 : g ≠ 0 := fun h => hx0 (by
      show aeval α q = 0
      rw [← hgx, h, map_zero])
    obtain ⟨i, hi, hmax⟩ := g.support.exists_max_image (fun n => ‖(g.coeff n : C)‖) (support_nonempty.mpr hg0)
    have hc0 : g.coeff i ≠ 0 := mem_support_iff.mp hi
    have hc0' : (g.coeff i : C) ≠ 0 := fun h => hc0 (Subtype.ext h)
    obtain ⟨g0, hg0e, hg0d⟩ := (mem_lifts_and_degree_eq (lifts_of_coeff M (Polynomial.C (g.coeff i)⁻¹ * g) fun n => by
      rw [coeff_C_mul]
      push_cast
      rw [norm_mul, norm_inv, inv_mul_le_one₀ (norm_pos_iff.mpr hc0')]
      by_cases hn : n ∈ g.support
      · exact hmax n hn
      · rw [notMem_support_iff.mp hn]; simp))
    have hco : g0.coeff i = 1 := IsFractionRing.injective (ball M) M (by
      rw [← coeff_map, hg0e, coeff_C_mul, inv_mul_cancel₀ hc0, map_one])
    have hu := unit g0 (by
      rw [hg0d, degree_C_mul (inv_ne_zero hc0), ← hfm.degree_map (algebraMap (ball M) M)]
      exact degree_modByMonic_lt q hF) (fun h => by
      have := congrArg (coeff · i) h
      simp [hco] at this)
    rw [← aeval_map_algebraMap M, hg0e, map_mul, aeval_C, norm_mul, hgx] at hu
    obtain ⟨n, hn⟩ := hM.1 _ (g.coeff i).2 hc0'
    refine ⟨n, ?_⟩
    have e : ‖algebraMap M C (g.coeff i)⁻¹‖ = ‖(g.coeff i : C)‖⁻¹ := by rw [map_inv₀, norm_inv]; rfl
    rw [e, inv_mul_eq_one₀ (norm_ne_zero_iff.mpr hc0')] at hu
    exact hu.symm.trans hn
  have hαM : α ∈ M := hM.2 hDisc (fun y hy => (IntermediateField.adjoin M {α}).algebraMap_mem ⟨y, hy⟩)
    (IntermediateField.mem_adjoin_simple_self M α)
  refine ⟨residue _ ⟨α, hαM, hα1⟩, ?_⟩
  have : f.eval ⟨α, hαM, hα1⟩ = 0 := Subtype.val_injective (by
    exact (aeval_algebraMap_apply C (⟨α, hαM, hα1⟩ : ball M) f).symm.trans hα)
  rw [← hf, eval_map, eval₂_at_apply, this, map_zero]

section Ext

variable (M) (ζ : C)

def ext : Subfield C := (IntermediateField.adjoin M {ζ}).toSubfield

/- English proof (translation)
Introduce `y hy` and use `(IntermediateField.adjoin M {ζ}).algebraMap_mem ⟨y, hy⟩`.
-/
theorem le_ext : M ≤ ext M ζ := fun y hy => (IntermediateField.adjoin M {ζ}).algebraMap_mem ⟨y, hy⟩

instance : Algebra (ball M) (ball (ext M ζ)) :=
  (Subring.inclusion (S := ball M) (T := ball (ext M ζ)) fun _ h => ⟨le_ext M ζ h.1, h.2⟩).toAlgebra

/- English proof (translation)
Introduce `_ _ h` and use `Subtype.ext (congrArg (fun t : ball (ext M ζ) => (t : C)) h)`.
-/
theorem ext_inj : Function.Injective (algebraMap (ball M) (ball (ext M ζ))) :=
  fun _ _ h => Subtype.ext (congrArg (fun t : ball (ext M ζ) => (t : C)) h)

instance : IsScalarTower (ball M) (ball (ext M ζ)) C := IsScalarTower.of_algebraMap_eq fun _ => rfl

variable {M}

include hπ h0 h1 hD in
/- English proof (translation)
Use `isDVR hπ h0 h1 hD` as an intermediate fact. Set `K` to `IntermediateField.adjoin M {ζ}`. Establish `: FiniteDimensional M K` using `IntermediateField.adjoin.finiteDimensional hζ`. Set `_ : NontriviallyNormedField M` to `{ (inferInstance : NormedField M) with non_trivial := ⟨⟨π, hπ⟩⁻¹, by show 1 < ‖π⁻¹‖`. Rewrite using `[norm_inv]`.

Conclude with `(one_lt_inv₀ (norm_pos_iff.mpr h0)).mpr h1⟩ }`. Establish `: CompleteSpace M` using `hc.completeSpace_coe`. Set `_ : Algebra (ball (ext M ζ)) K` to `(toM (ext M ζ)).toAlgebra`. Establish `: IsScalarTower (ball M) (ball (ext M ζ)) K` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `: IsIntegralClosure (ball (ext M ζ)) (ball M) K` using `⟨fun a b h => Subtype.ext (congrArg (fun t : K => (t : C)) h), fun {x} => by`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨⟨x, x.2, norm_le_of_integral M (hx.map (K.val.restrictScalars (ball M)))⟩, rfl⟩`. Introduce and unpack `⟨y, rfl⟩`. Establish `hs` using `spectralNorm_unique_field_norm_ext (K := M) (L := K) (f := (NormedField.toAbsoluteValue C).comp (algebraMap K C).injective) (fun _ => rfl) (algebraMap _ K y)`.

Establish `hi : IsIntegral M (algebraMap _ K y)` using `Algebra.IsIntegral.isIntegral _`. Establish `hv : spectralValue (minpoly M (algebraMap _ K y)) ≤ 1` using `hs.symm.le.trans y.2.2`. Take `⟨q, hq, -, hqm⟩` from `lifts_and_degree_eq_and_monic (lifts_of_coeff M _ ((spectralValue_le_one_iff (minpoly.monic hi)).mp hv)) (minpoly.monic hi)`. Conclude with `⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap M, hq, minpoly.aeval]⟩⟩`. Establish `hfin` using `IsIntegralClosure.finite (ball M) M K (ball (ext M ζ))`.

Establish `hded` using `IsIntegralClosure.isDedekindDomain (ball M) M K (ball (ext M ζ))`. Establish `hnf : ¬ IsField (ball (ext M ζ))` using `fun hf => by`. Establish `hm : (⟨π, le_ext M ζ hπ, h1.le⟩ : ball (ext M ζ)) ∈ maximalIdeal _` using `(mem_max _ _).mpr h1`. Rewrite `hm` using `[isField_iff_maximalIdeal_eq.mp hf, Ideal.mem_bot]`. Conclude with `h0 (congrArg Subtype.val hm)`.

Conclude with `⟨hfin, ((IsDiscreteValuationRing.TFAE _ hnf).out 0 2).mpr hded⟩`.
-/
theorem ext_spec [CompleteSpace C] [CharZero C] (hc : IsClosed (M : Set C)) (hζ : IsIntegral M ζ) :
    Module.Finite (ball M) (ball (ext M ζ)) ∧ IsDiscreteValuationRing (ball (ext M ζ)) := by
  have := isDVR hπ h0 h1 hD
  let K := IntermediateField.adjoin M {ζ}
  have : FiniteDimensional M K := IntermediateField.adjoin.finiteDimensional hζ
  let _ : NontriviallyNormedField M := { (inferInstance : NormedField M) with
    non_trivial := ⟨⟨π, hπ⟩⁻¹, by
      show 1 < ‖π⁻¹‖
      rw [norm_inv]; exact (one_lt_inv₀ (norm_pos_iff.mpr h0)).mpr h1⟩ }
  have : CompleteSpace M := hc.completeSpace_coe
  let _ : Algebra (ball (ext M ζ)) K := (toM (ext M ζ)).toAlgebra
  have : IsScalarTower (ball M) (ball (ext M ζ)) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsIntegralClosure (ball (ext M ζ)) (ball M) K := ⟨fun a b h => Subtype.ext (congrArg (fun t : K => (t : C)) h), fun {x} => by
    constructor
    · intro hx
      exact ⟨⟨x, x.2, norm_le_of_integral M (hx.map (K.val.restrictScalars (ball M)))⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      have hs := spectralNorm_unique_field_norm_ext (K := M) (L := K)
        (f := (NormedField.toAbsoluteValue C).comp (algebraMap K C).injective) (fun _ => rfl) (algebraMap _ K y)
      have hi : IsIntegral M (algebraMap _ K y) := Algebra.IsIntegral.isIntegral _
      have hv : spectralValue (minpoly M (algebraMap _ K y)) ≤ 1 := hs.symm.le.trans y.2.2
      obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic
        (lifts_of_coeff M _ ((spectralValue_le_one_iff (minpoly.monic hi)).mp hv)) (minpoly.monic hi)
      exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap M, hq, minpoly.aeval]⟩⟩
  have hfin := IsIntegralClosure.finite (ball M) M K (ball (ext M ζ))
  have hded := IsIntegralClosure.isDedekindDomain (ball M) M K (ball (ext M ζ))
  have hnf : ¬ IsField (ball (ext M ζ)) := fun hf => by
    have hm : (⟨π, le_ext M ζ hπ, h1.le⟩ : ball (ext M ζ)) ∈ maximalIdeal _ := (mem_max _ _).mpr h1
    rw [isField_iff_maximalIdeal_eq.mp hf, Ideal.mem_bot] at hm
    exact h0 (congrArg Subtype.val hm)
  exact ⟨hfin, ((IsDiscreteValuationRing.TFAE _ hnf).out 0 2).mpr hded⟩

/- English proof (translation)
Establish `hx : iC _ x ∈ Algebra.adjoin M {ζ}`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζ.isAlgebraic]`. Conclude with `iC_mem _ x`. Rewrite `hx` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨q, hq⟩` from `hx`.

Take `⟨d, hd, e⟩` from `IsLocalization.integerNormalization_spec (nonZeroDivisors (ball M)) q`. Use `⟨IsLocalization.integerNormalization (nonZeroDivisors (ball M)) q, d, nonZeroDivisors.ne_zero hd, (iC _).injective ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, iC_alg, iC_alg, ← hq]`. Establish `h2 : ((aeval z (IsLocalization.integerNormalization (nonZeroDivisors (ball M)) q) : ball (ext M ζ)) : C) = aeval ζ (IsLocalization.integerNormalization (nonZeroDivisors (ball M)) q)` using `(aeval_algebraMap_apply C z _).symm.trans (congrArg (fun t => aeval t _) hz)`. Rewrite using `[h2, ← aeval_map_algebraMap M, e, Algebra.smul_def, map_mul, mul_comm]`.

Use `congr 1`. Conclude with `(aeval_C ζ (algebraMap (ball M) M d)).symm`.
-/
theorem ext_gen (hζ : IsIntegral M ζ) (z : ball (ext M ζ)) (hz : (z : C) = ζ)
    (x : FractionRing (ball (ext M ζ))) : ∃ p : (ball M)[X], ∃ d : ball M, d ≠ 0 ∧
    x * algebraMap (ball (ext M ζ)) _ (algebraMap (ball M) (ball (ext M ζ)) d) =
      algebraMap (ball (ext M ζ)) _ (aeval z p) := by
  have hx : iC _ x ∈ Algebra.adjoin M {ζ} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζ.isAlgebraic]; exact iC_mem _ x
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
  obtain ⟨q, hq⟩ := hx
  obtain ⟨d, hd, e⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors (ball M)) q
  refine ⟨IsLocalization.integerNormalization (nonZeroDivisors (ball M)) q, d, nonZeroDivisors.ne_zero hd,
    (iC _).injective ?_⟩
  rw [map_mul, iC_alg, iC_alg, ← hq]
  have h2 : ((aeval z (IsLocalization.integerNormalization (nonZeroDivisors (ball M)) q) : ball (ext M ζ)) : C) =
      aeval ζ (IsLocalization.integerNormalization (nonZeroDivisors (ball M)) q) :=
    (aeval_algebraMap_apply C z _).symm.trans (congrArg (fun t => aeval t _) hz)
  rw [h2, ← aeval_map_algebraMap M, e, Algebra.smul_def, map_mul, mul_comm]
  congr 1
  exact (aeval_C ζ (algebraMap (ball M) M d)).symm

end Ext

end Formalism.BasicNotions.Examples₂.Ur

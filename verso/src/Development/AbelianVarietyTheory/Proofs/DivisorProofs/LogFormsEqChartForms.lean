import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR.ChartStalk

section Algebra

variable {K : Type} [Field K]

def IsComb (A : Subring K) (H' : Set Ω[K⁄ℤ]) (v : Ω[K⁄ℤ]) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → K) (w : ι → Ω[K⁄ℤ]),
    (∀ k, c k ∈ A) ∧ (∀ k, w k ∈ H') ∧ v = ∑ k, c k • w k

/- English proof (translation)
Assemble the required witnesses or components as `⟨Unit, inferInstance, fun _ => c, fun _ => w, fun _ => hc, fun _ => hw, by simp [Finset.univ_unique, e]⟩`.
-/
theorem isComb_single {A : Subring K} {H' : Set Ω[K⁄ℤ]} {v w : Ω[K⁄ℤ]} {c : K} (hc : c ∈ A)
    (hw : w ∈ H') (e : v = c • w) : IsComb A H' v :=
  ⟨Unit, inferInstance, fun _ => c, fun _ => w, fun _ => hc, fun _ => hw, by
    simp [Finset.univ_unique, e]⟩

/- English proof (translation)
Unfold `spanForms`. Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `η ⟨c, hc, v, hv, rfl⟩`. Use `choose ι ft co w hco hw hv' using fun i => hH (v i) (hv i)`. Establish `e : ExteriorAlgebra.ιMulti K a v = ∑ r : ∀ i, ι i, (∏ i, co i (r i)) • ExteriorAlgebra.ιMulti K a (fun i => w i (r i))` using `by conv_lhs => rw [show v = fun i => ∑ k, co i k • w i k from funext hv']`.

Rewrite using `[← AlternatingMap.coe_multilinearMap, MultilinearMap.map_sum]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[MultilinearMap.map_smul_univ]`. Rewrite using `[e, Finset.smul_sum]`. Use `AddSubgroup.sum_mem _ fun r _ => AddSubgroup.subset_closure ⟨c * ∏ i, co i (r i), hM c hc _ (Subring.prod_mem _ fun i _ => hco i (r i)), fun i => w i (r i), fun i => hw i (r i), by rw [smul_smul]⟩` and prove the remaining obligations.
-/
theorem spanForms_le_of_isComb (A : Subring K) {M : Set K} {H H' : Set Ω[K⁄ℤ]} (a : ℕ)
    (hM : ∀ c ∈ M, ∀ b ∈ A, c * b ∈ M) (hH : ∀ v ∈ H, IsComb A H' v) :
    spanForms M H a ≤ spanForms M H' a := by
  unfold spanForms
  rw [AddSubgroup.closure_le]
  rintro η ⟨c, hc, v, hv, rfl⟩
  choose ι ft co w hco hw hv' using fun i => hH (v i) (hv i)
  have e : ExteriorAlgebra.ιMulti K a v = ∑ r : ∀ i, ι i,
      (∏ i, co i (r i)) • ExteriorAlgebra.ιMulti K a (fun i => w i (r i)) := by
    conv_lhs => rw [show v = fun i => ∑ k, co i k • w i k from funext hv']
    rw [← AlternatingMap.coe_multilinearMap, MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [MultilinearMap.map_smul_univ]
  rw [e, Finset.smul_sum]
  refine AddSubgroup.sum_mem _ fun r _ => AddSubgroup.subset_closure
    ⟨c * ∏ i, co i (r i), hM c hc _ (Subring.prod_mem _ fun i _ => hco i (r i)),
      fun i => w i (r i), fun i => hw i (r i), by rw [smul_smul]⟩

/- English proof (translation)
Simplify using `[dlog, dK]`.
-/
theorem dlog_one : dlog (1 : Kˣ) = 0 := by
  simp [dlog, dK]

/- English proof (translation)
Simplify using `only [dlog, dK, Units.val_mul, Derivation.leibniz, smul_add, smul_smul, mul_inv_rev, Units.val_inv_eq_inv_val]`. Rewrite using `[add_comm]`. Use `congr 2`. Clear the denominators using the available nonvanishing facts. Clear the denominators using the available nonvanishing facts.
-/
theorem dlog_mul (g h : Kˣ) : dlog (g * h) = dlog g + dlog h := by
  simp only [dlog, dK, Units.val_mul, Derivation.leibniz, smul_add, smul_smul, mul_inv_rev,
    Units.val_inv_eq_inv_val]
  rw [add_comm]
  congr 2
  · field_simp
  · field_simp

def dlogHom : Kˣ →* Multiplicative Ω[K⁄ℤ] where
  toFun g := Multiplicative.ofAdd (dlog g)
  map_one' := by rw [dlog_one]; rfl
  map_mul' g h := by rw [dlog_mul]; rfl

/- English proof (translation)
Use `map_zpow (dlogHom (K := K)) g m` as an intermediate fact. Conclude with `congrArg Multiplicative.toAdd this`.
-/
theorem dlog_zpow (g : Kˣ) (m : ℤ) : dlog (g ^ m) = m • dlog g := by
  have := map_zpow (dlogHom (K := K)) g m
  exact congrArg Multiplicative.toAdd this

/- English proof (translation)
Use `map_prod (dlogHom (K := K)) g s` as an intermediate fact. Conclude with `congrArg Multiplicative.toAdd this`.
-/
theorem dlog_prod {ι : Type} (s : Finset ι) (g : ι → Kˣ) : dlog (∏ i ∈ s, g i) = ∑ i ∈ s, dlog (g i) := by
  have := map_prod (dlogHom (K := K)) g s
  exact congrArg Multiplicative.toAdd this

/- English proof (translation)
Rewrite using `[dlog, smul_smul, Units.mul_inv, one_smul]`.
-/
theorem smul_dlog (g : Kˣ) : (g : K) • dlog g = dK (g : K) := by
  rw [dlog, smul_smul, Units.mul_inv, one_smul]

end Algebra

section Scheme

variable {X : Scheme.{0}} [IsIntegral X]

/- English proof (translation)
Unfold `frame`. Use `split_ifs with h`. Conclude with `(smul_dlog (x i)).symm`. Rewrite using `[one_smul]`.
-/
theorem dK_eq_frame {n : ℕ} (x : Fin n → X.functionFieldˣ) (J : Finset (Fin n)) (i : Fin n) :
    dK (x i : X.functionField) = (if i ∈ J then (x i : X.functionField) else 1) • frame x J i := by
  unfold frame
  split_ifs with h
  · exact (smul_dlog (x i)).symm
  · rw [one_smul]

/- English proof (translation)
Take `⟨u, m, hu, rfl⟩` from `(hc.logUnit y hy g).1 hg`. Take `⟨d, hd, hdu⟩` from `(hc.chart y hy).deriv (u : X.functionField) hu.regAt`. Use `⟨Fin n, inferInstance, fun i => (u : X.functionField)⁻¹ * d i * (if i ∈ J then (x i : X.functionField) else 1) + (if i ∈ J then ((m i : ℤ) : X.functionField) else 0), frame x J, fun i => ?_, fun i => ⟨i, rfl⟩, ?_⟩` and prove the remaining obligations. Use `add_mem (mul_mem (mul_mem hu.inv.regAt (hd i)) ?_) ?_` and prove the remaining obligations. Use `split_ifs`.

Conclude with `(hc.chart y hy).mem i`. Conclude with `one_mem _`. Use `split_ifs`. Conclude with `intCast_mem _ _`. Conclude with `zero_mem _`.

Simplify using `only [add_smul, Finset.sum_add_distrib, mul_smul, ← dK_eq_frame, ← Finset.smul_sum, ← hdu, ite_smul, zero_smul]`. Rewrite using `[dlog_mul, dlog_prod, Finset.sum_ite_mem, Finset.univ_inter]`. Use `congr 1`. Rewrite using `[dlog, Units.val_inv_eq_inv_val, hdu]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[dK_eq_frame x J j, ite_smul]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[dlog_zpow, frame, if_pos hj, Int.cast_smul_eq_zsmul]`.
-/
theorem isComb_dlog {Z : Set X} {U : X.Opens} {n : ℕ} {x : Fin n → X.functionFieldˣ} {J : Finset (Fin n)}
    (hc : IsLogChart Z U x J) {y : X} (hy : y ∈ U) {g : X.functionFieldˣ} (hg : LogUnit Z y g) :
    IsComb (locRing y) (Set.range (frame x J)) (dlog g) := by
  obtain ⟨u, m, hu, rfl⟩ := (hc.logUnit y hy g).1 hg
  obtain ⟨d, hd, hdu⟩ := (hc.chart y hy).deriv (u : X.functionField) hu.regAt
  refine ⟨Fin n, inferInstance,
    fun i => (u : X.functionField)⁻¹ * d i * (if i ∈ J then (x i : X.functionField) else 1) +
      (if i ∈ J then ((m i : ℤ) : X.functionField) else 0),
    frame x J, fun i => ?_, fun i => ⟨i, rfl⟩, ?_⟩
  · refine add_mem (mul_mem (mul_mem hu.inv.regAt (hd i)) ?_) ?_
    · split_ifs
      · exact (hc.chart y hy).mem i
      · exact one_mem _
    · split_ifs
      · exact intCast_mem _ _
      · exact zero_mem _
  · simp only [add_smul, Finset.sum_add_distrib, mul_smul, ← dK_eq_frame, ← Finset.smul_sum, ← hdu,
      ite_smul, zero_smul]
    rw [dlog_mul, dlog_prod, Finset.sum_ite_mem, Finset.univ_inter]
    congr 1
    · rw [dlog, Units.val_inv_eq_inv_val, hdu]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [dK_eq_frame x J j, ite_smul]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [dlog_zpow, frame, if_pos hj, Int.cast_smul_eq_zsmul]

/- English proof (translation)
Establish `hlog : ∀ w : X.functionFieldˣ, UnitAt y (w : X.functionField) → LogUnit Z y w` using `fun w hw => (hc.logUnit y hy w).2 ⟨w, 0, hw, by simp⟩`. Distinguish the cases in `hi : i ∈ J`. Use `isComb_single (one_mem _) ⟨x i, (hc.logUnit y hy _).2 ⟨1, Pi.single i 1, ?_, ?_⟩, rfl⟩ ?_` and prove the remaining obligations. Rewrite using `[Units.val_one]`. Conclude with `unitAt_one y`.

Rewrite using `[one_mul, Finset.prod_eq_single_of_mem i hi (fun j _ hj => by simp [Pi.single_apply, hj])]`. Simplify using the standard rewrite rules. Rewrite using `[frame, if_pos hi, one_smul]`. Establish `hm : RegAt y (x i : X.functionField)` using `(hc.chart y hy).mem i`. Take `⟨s, hs⟩` from `hm`.

Break down `IsLocalRing.isUnit_or_isUnit_one_sub_self s with h | h` into its components or cases. Establish `hu : UnitAt y (x i : X.functionField)` using `⟨s, h, hs⟩`. Use `isComb_single ((hc.chart y hy).mem i) ⟨x i, hlog _ hu, rfl⟩ ?_` and prove the remaining obligations. Rewrite using `[frame, if_neg hi, smul_dlog]`. Establish `hu : UnitAt y (1 - (x i : X.functionField))` using `⟨1 - s, h, by rw [map_sub, map_one, hs]⟩`.

Use `isComb_single (c := -(1 - (x i : X.functionField))) (neg_mem (sub_mem (one_mem _) ((hc.chart y hy).mem i))) ⟨Units.mk0 _ hu.ne_zero, hlog _ hu, rfl⟩ ?_` and prove the remaining obligations. Establish `h2` using `smul_dlog (Units.mk0 _ hu.ne_zero)`. Rewrite `h2` using `[Units.val_mk0]`. Rewrite using `[frame, if_neg hi, neg_smul, h2]`. Simplify using `[dK]`.
-/
theorem isComb_frame {Z : Set X} {U : X.Opens} {n : ℕ} {x : Fin n → X.functionFieldˣ} {J : Finset (Fin n)}
    (hc : IsLogChart Z U x J) {y : X} (hy : y ∈ U) (i : Fin n) :
    IsComb (locRing y) (dlog '' {g | LogUnit Z y g}) (frame x J i) := by
  have hlog : ∀ w : X.functionFieldˣ, UnitAt y (w : X.functionField) → LogUnit Z y w := fun w hw =>
    (hc.logUnit y hy w).2 ⟨w, 0, hw, by simp⟩
  by_cases hi : i ∈ J
  · refine isComb_single (one_mem _) ⟨x i, (hc.logUnit y hy _).2 ⟨1, Pi.single i 1, ?_, ?_⟩, rfl⟩ ?_
    · rw [Units.val_one]; exact unitAt_one y
    · rw [one_mul, Finset.prod_eq_single_of_mem i hi (fun j _ hj => by simp [Pi.single_apply, hj])]
      simp
    · rw [frame, if_pos hi, one_smul]
  · have hm : RegAt y (x i : X.functionField) := (hc.chart y hy).mem i
    obtain ⟨s, hs⟩ := hm
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self s with h | h
    · have hu : UnitAt y (x i : X.functionField) := ⟨s, h, hs⟩
      refine isComb_single ((hc.chart y hy).mem i) ⟨x i, hlog _ hu, rfl⟩ ?_
      rw [frame, if_neg hi, smul_dlog]
    · have hu : UnitAt y (1 - (x i : X.functionField)) := ⟨1 - s, h, by rw [map_sub, map_one, hs]⟩
      refine isComb_single (c := -(1 - (x i : X.functionField)))
        (neg_mem (sub_mem (one_mem _) ((hc.chart y hy).mem i)))
        ⟨Units.mk0 _ hu.ne_zero, hlog _ hu, rfl⟩ ?_
      have h2 := smul_dlog (Units.mk0 _ hu.ne_zero)
      rw [Units.val_mk0] at h2
      rw [frame, if_neg hi, neg_smul, h2]
      simp [dK]

end Scheme

/- English proof (translation)
Introduce `X _ Z U n x J G y t a hc hy ht`. Establish `hM : {c | G.RegularAt y c} = {c | c * (t : X.functionField) ∈ locRing y}` using `Set.ext fun c => ht.regularAt_iff`. Establish `hstab : ∀ c ∈ {c | c * (t : X.functionField) ∈ locRing y}, ∀ b ∈ locRing y, c * b ∈ {c | c * (t : X.functionField) ∈ locRing y}` using `fun c hc b hb => by`. Simplify using `only [Set.mem_setOf_eq] at hc ⊢`. Rewrite using `[mul_right_comm]`.

Conclude with `mul_mem hc hb`. Unfold `logAt chartForms`. Rewrite using `[hM]`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `spanForms_le_of_isComb _ a hstab fun v ⟨g, hg, e⟩ => e ▸ isComb_dlog hc hy hg`.

Conclude with `spanForms_le_of_isComb _ a hstab fun v ⟨i, e⟩ => e ▸ isComb_frame hc hy i`.
-/
theorem logAt_eq_chartForms : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : Set X) (U : X.Opens) {n : ℕ}
    (x : Fin n → X.functionFieldˣ) (J : Finset (Fin n)) (G : CartierDiv X) (y : X) (t : X.functionFieldˣ)
    (a : ℕ), IsLogChart Z U x J → y ∈ U → G.IsEqn y t → logAt Z G a y = chartForms (locRing y) x J t a := by
  intro X _ Z U n x J G y t a hc hy ht
  have hM : {c | G.RegularAt y c} = {c | c * (t : X.functionField) ∈ locRing y} :=
    Set.ext fun c => ht.regularAt_iff
  have hstab : ∀ c ∈ {c | c * (t : X.functionField) ∈ locRing y}, ∀ b ∈ locRing y,
      c * b ∈ {c | c * (t : X.functionField) ∈ locRing y} := fun c hc b hb => by
    simp only [Set.mem_setOf_eq] at hc ⊢
    rw [mul_right_comm]; exact mul_mem hc hb
  unfold logAt chartForms
  rw [hM]
  apply le_antisymm
  · exact spanForms_le_of_isComb _ a hstab fun v ⟨g, hg, e⟩ => e ▸ isComb_dlog hc hy hg
  · exact spanForms_le_of_isComb _ a hstab fun v ⟨i, e⟩ => e ▸ isComb_frame hc hy i

end GlobalTheory.LogDR.ChartStalk

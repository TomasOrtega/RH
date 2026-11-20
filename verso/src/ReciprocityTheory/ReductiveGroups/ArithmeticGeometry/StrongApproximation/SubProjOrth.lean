import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.EichAlongSub

namespace ReciprocityTheory.ChartRestriction.G.SA

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [hf]`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi, Finset.sum_insert hi, ← ih]`. Simplify using `only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]`.
-/
theorem hf_sum_left {α : Type*} (s : Finset α) (v : α → ι → K) (y : ι → K) :
    hf σ J (∑ i ∈ s, v i) y = ∑ i ∈ s, hf σ J (v i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hf]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [hf]`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi, Finset.sum_insert hi, ← ih]`. Simplify using `only [hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]`.
-/
theorem hf_sum_right {α : Type*} (s : Finset α) (v : α → ι → K) (x : ι → K) :
    hf σ J x (∑ i ∈ s, v i) = ∑ i ∈ s, hf σ J x (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hf]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    simp only [hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Establish `hv : Matrix.vecMul x J = 0`. Use function extensionality and compare the values at `k`. Establish `h1` using `h (Pi.single k (1 : K))`. Establish `hs : ∀ j, σ ((Pi.single k (1 : K) : ι → K) j) = (Pi.single k (1 : K) : ι → K) j`. Introduce `j`.

Distinguish the cases in `hj : j = k`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hj]`. Simplify using `only [hf, hs, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1`.

Simplify `h1` using `[Matrix.vecMul, dotProduct]`. Establish `h2` using `congrArg (fun v => Matrix.vecMul v J⁻¹) hv`. Simplify `h2` using `[Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv J hdet]`.
-/
theorem nondeg (hdet : IsUnit J.det) {x : ι → K} (h : ∀ z, hf σ J x z = 0) : x = 0 := by
  have hv : Matrix.vecMul x J = 0 := by
    funext k
    have h1 := h (Pi.single k (1 : K))
    have hs : ∀ j, σ ((Pi.single k (1 : K) : ι → K) j) = (Pi.single k (1 : K) : ι → K) j := by
      intro j
      by_cases hj : j = k
      · subst hj
        simp
      · simp [Pi.single_apply, hj]
    simp only [hf, hs, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h1
    simpa [Matrix.vecMul, dotProduct] using h1
  have h2 := congrArg (fun v => Matrix.vecMul v J⁻¹) hv
  simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv J hdet] using h2

variable (σ J) in

structure OFam (e f : ι → K) (r : ℕ) where
  a : Fin r → ι → K
  inv : Fin r → K
  ha_e : ∀ j, hf σ J (a j) e = 0
  ha_f : ∀ j, hf σ J (a j) f = 0
  ho : ∀ i j, i ≠ j → hf σ J (a i) (a j) = 0
  hinv : ∀ j, inv j * hf σ J (a j) (a j) = 1

variable {e f : ι → K}

def OFam.proj {r : ℕ} (F : OFam σ J e f r) (x : ι → K) : ι → K :=
  hf σ J x f • e + hf σ J x e • f + ∑ j, (hf σ J x (F.a j) * F.inv j) • F.a j

def OFam.Spans {r : ℕ} (F : OFam σ J e f r) : Prop := ∀ x, F.proj x = x

section
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) (he : hf σ J e e = 0) (hff : hf σ J f f = 0)
  (hef : hf σ J e f = 1)
include hσ hJ he hff hef

/- English proof (translation)
Establish `hadd : ∀ x y z, hf σ J (x + y) z = hf σ J x z + hf σ J y z`. Introduce `x y z`. Simplify using `only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]`. Establish `hsub : ∀ x y z, hf σ J (x - y) z = hf σ J x z - hf σ J y z`. Introduce `x y z`.

Simplify using `only [hf, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]`. Establish `hsmul : ∀ (c : K) x z, hf σ J (c • x) z = c * hf σ J x z`. Introduce `c x z`. Simplify using `only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Establish `hsym : ∀ x y, hf σ J y x = σ (hf σ J x y)`. Introduce `x y`. Simplify using `only [hf, map_sum, map_mul, hσ]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hJij : J j i = σ (J i j)` using `congrFun (congrFun hJ i) j`. Rewrite using `[hJij]`. Expand and normalize the polynomial expressions, which then agree. Establish `hfe : hf σ J f e = 1` using `by rw [hsym, hef, map_one]`.

Establish `hproj : ∀ z, hf σ J (F.proj x) z = hf σ J x f * hf σ J e z + hf σ J x e * hf σ J f z + ∑ j, hf σ J x (F.a j) * F.inv j * hf σ J (F.a j) z`. Introduce `z`. Simplify using `only [OFam.proj, hadd, hsmul, hf_sum_left]`. Use `⟨?_, ?_, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[hsub, hproj, he, hfe]`.

Simplify using `[F.ha_e]`. Rewrite using `[hsub, hproj, hef, hff]`. Simplify using `[F.ha_f]`. Rewrite using `[hsub, hproj, hsym (F.a k) e, hsym (F.a k) f, F.ha_e, F.ha_f, map_zero]`. Rewrite using `[Finset.sum_eq_single k]`.

Rewrite using `[mul_assoc (hf σ J x (F.a k)), F.hinv]`. Expand and normalize the polynomial expressions, which then agree. Introduce `j _ hjk`. Rewrite using `[F.ho j k hjk, mul_zero]`. Introduce `hk`.

Conclude with `absurd (Finset.mem_univ k) hk`.
-/
theorem OFam.sub_proj_orth {r : ℕ} (F : OFam σ J e f r) (x : ι → K) :
    hf σ J (x - F.proj x) e = 0 ∧ hf σ J (x - F.proj x) f = 0 ∧
      ∀ k, hf σ J (x - F.proj x) (F.a k) = 0 := by
  have hadd : ∀ x y z, hf σ J (x + y) z = hf σ J x z + hf σ J y z := by
    intro x y z
    simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hsub : ∀ x y z, hf σ J (x - y) z = hf σ J x z - hf σ J y z := by
    intro x y z
    simp only [hf, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have hsmul : ∀ (c : K) x z, hf σ J (c • x) z = c * hf σ J x z := by
    intro c x z
    simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsym : ∀ x y, hf σ J y x = σ (hf σ J x y) := by
    intro x y
    simp only [hf, map_sum, map_mul, hσ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hJij : J j i = σ (J i j) := congrFun (congrFun hJ i) j
    rw [hJij]
    ring
  have hfe : hf σ J f e = 1 := by rw [hsym, hef, map_one]
  have hproj : ∀ z, hf σ J (F.proj x) z = hf σ J x f * hf σ J e z + hf σ J x e * hf σ J f z +
      ∑ j, hf σ J x (F.a j) * F.inv j * hf σ J (F.a j) z := by
    intro z
    simp only [OFam.proj, hadd, hsmul, hf_sum_left]
  refine ⟨?_, ?_, fun k => ?_⟩
  · rw [hsub, hproj, he, hfe]
    simp [F.ha_e]
  · rw [hsub, hproj, hef, hff]
    simp [F.ha_f]
  · rw [hsub, hproj, hsym (F.a k) e, hsym (F.a k) f, F.ha_e, F.ha_f, map_zero]
    rw [Finset.sum_eq_single k]
    · rw [mul_assoc (hf σ J x (F.a k)), F.hinv]
      ring
    · intro j _ hjk
      rw [F.ho j k hjk, mul_zero]
    · intro hk
      exact absurd (Finset.mem_univ k) hk

end

/- English proof (translation)
Establish `hadd : ∀ z, hf σ J (x + y) z = hf σ J x z + hf σ J y z`. Introduce `z`. Simplify using `only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]`. Simplify using `only [OFam.proj, hadd, add_smul, add_mul, Finset.sum_add_distrib]`. Normalize the expressions using the abelian group laws.
-/
theorem OFam.proj_add {r : ℕ} (F : OFam σ J e f r) (x y : ι → K) :
    F.proj (x + y) = F.proj x + F.proj y := by
  have hadd : ∀ z, hf σ J (x + y) z = hf σ J x z + hf σ J y z := by
    intro z
    simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  simp only [OFam.proj, hadd, add_smul, add_mul, Finset.sum_add_distrib]
  abel

/- English proof (translation)
Establish `hsmul : ∀ z, hf σ J (c • x) z = c * hf σ J x z`. Introduce `z`. Simplify using `only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [OFam.proj, hsmul, smul_add, Finset.smul_sum, smul_smul, mul_assoc]`.
-/
theorem OFam.proj_smul {r : ℕ} (F : OFam σ J e f r) (c : K) (x : ι → K) :
    F.proj (c • x) = c • F.proj x := by
  have hsmul : ∀ z, hf σ J (c • x) z = c * hf σ J x z := by
    intro z
    simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [OFam.proj, hsmul, smul_add, Finset.smul_sum, smul_smul, mul_assoc]

section Ext
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) (he : hf σ J e e = 0) (hff : hf σ J f f = 0)
  (hef : hf σ J e f = 1) (hdet : IsUnit J.det) (hfix : ∀ x, σ x = x → x ≠ 0 → IsUnit x)
  (h2 : IsUnit (2 : K)) {δ : K} (hδ : IsUnit δ) (hσδ : σ δ = -δ)

include h2 hδ hσδ in
/- English proof (translation)
Establish `hadd1 : ∀ x y z, hf σ J (x + y) z = hf σ J x z + hf σ J y z`. Introduce `x y z`. Simplify using `only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]`. Establish `hadd2 : ∀ x y z, hf σ J x (y + z) = hf σ J x y + hf σ J x z`. Introduce `x y z`.

Simplify using `only [hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]`. Establish `hsm1 : ∀ (c : K) x y, hf σ J (c • x) y = c * hf σ J x y`. Introduce `c x y`. Simplify using `only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Establish `hsm2 : ∀ (c : K) x y, hf σ J x (c • y) = σ c * hf σ J x y`. Introduce `c x y`. Simplify using `only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hadd1, hadd2, hp, hp'] at h1`. Simplify using `only [hadd1, hadd2, hsm1, hsm2, hp, hp', hσδ] at h3`. Establish `e2 : δ * (hf σ J p' p - hf σ J p p') = 0` using `by linear_combination h3`. Establish `e3 : hf σ J p' p - hf σ J p p' = 0` using `hδ.mul_right_eq_zero.mp e2`.

Establish `e4 : 2 * hf σ J p p' = 0` using `by linear_combination h1 - e3`. Conclude with `h2.mul_right_eq_zero.mp e4`.
-/
theorem polar {p p' : ι → K} (hp : hf σ J p p = 0) (hp' : hf σ J p' p' = 0)
    (h1 : hf σ J (p + p') (p + p') = 0) (h3 : hf σ J (p + δ • p') (p + δ • p') = 0) :
    hf σ J p p' = 0 := by
  have hadd1 : ∀ x y z, hf σ J (x + y) z = hf σ J x z + hf σ J y z := by
    intro x y z
    simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hadd2 : ∀ x y z, hf σ J x (y + z) = hf σ J x y + hf σ J x z := by
    intro x y z
    simp only [hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  have hsm1 : ∀ (c : K) x y, hf σ J (c • x) y = c * hf σ J x y := by
    intro c x y
    simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsm2 : ∀ (c : K) x y, hf σ J x (c • y) = σ c * hf σ J x y := by
    intro c x y
    simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [hadd1, hadd2, hp, hp'] at h1
  simp only [hadd1, hadd2, hsm1, hsm2, hp, hp', hσδ] at h3
  have e2 : δ * (hf σ J p' p - hf σ J p p') = 0 := by linear_combination h3
  have e3 : hf σ J p' p - hf σ J p p' = 0 := hδ.mul_right_eq_zero.mp e2
  have e4 : 2 * hf σ J p p' = 0 := by linear_combination h1 - e3
  exact h2.mul_right_eq_zero.mp e4

include hσ hJ he hff hef hdet hfix h2 hδ hσδ in
/- English proof (translation)
Establish `hadd1 : ∀ x y z, hf σ J (x + y) z = hf σ J x z + hf σ J y z`. Introduce `x y z`. Simplify using `only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]`. Establish `hadd2 : ∀ x y z, hf σ J x (y + z) = hf σ J x y + hf σ J x z`. Introduce `x y z`.

Simplify using `only [hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]`. Establish `hsub2 : ∀ x y z, hf σ J x (y - z) = hf σ J x y - hf σ J x z`. Introduce `x y z`. Simplify using `only [hf, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]`. Establish `hsm1 : ∀ (c : K) x y, hf σ J (c • x) y = c * hf σ J x y`.

Introduce `c x y`. Simplify using `only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hsm2 : ∀ (c : K) x y, hf σ J x (c • y) = σ c * hf σ J x y`.

Introduce `c x y`. Simplify using `only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hsym : ∀ x y, hf σ J y x = σ (hf σ J x y)`.

Introduce `x y`. Simplify using `only [hf, map_sum, map_mul, hσ]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hJij : J j i = σ (J i j)` using `congrFun (congrFun hJ i) j`.

Rewrite using `[hJij]`. Expand and normalize the polynomial expressions, which then agree. Establish `horth` using `fun t => OFam.sub_proj_orth hσ hJ he hff hef F t`. Unfold `OFam.Spans at hns`. Use `push_neg at hns`.

Take `⟨x, hx⟩` from `hns`. Establish `key : ∃ t : ι → K, hf σ J (t - F.proj t) (t - F.proj t) ≠ 0`. Distinguish the cases in `hyy : hf σ J (x - F.proj x) (x - F.proj x) = 0`. Establish `hy0 : x - F.proj x ≠ 0` using `sub_ne_zero.mpr (Ne.symm hx)`. Establish `hz' : ∃ z', hf σ J (x - F.proj x) z' ≠ 0`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hy0 (nondeg hdet hcon)`. Take `⟨z', hz'⟩` from `hz'`. Establish `hyproj : ∀ t, hf σ J (x - F.proj x) (F.proj t) = 0`.

Introduce `t`. Take `⟨hye, hyf, hya⟩` from `horth x`. Generalize the expression as in `x - F.proj x = y at hye hyf hya ⊢`. Simplify using `only [OFam.proj, hadd2, hsm2, hf_sum_right, hye, hyf, hya, mul_zero, Finset.sum_const_zero, add_zero]`. Establish `hyz : hf σ J (x - F.proj x) (z' - F.proj z') ≠ 0`.

Rewrite using `[hsub2, hyproj, sub_zero]`. Conclude with `hz'`. Distinguish the cases in `hzz : hf σ J (z' - F.proj z') (z' - F.proj z') = 0`. Assume the negation of the conclusion as `hall push_neg at hall`. Apply `hyz` to reduce the goal to its premises.

Establish `e1 : (x + z') - F.proj (x + z') = (x - F.proj x) + (z' - F.proj z')`. Rewrite using `[OFam.proj_add]`. Normalize the expressions using the abelian group laws. Establish `e3 : (x + δ • z') - F.proj (x + δ • z') = (x - F.proj x) + δ • (z' - F.proj z')`. Rewrite using `[OFam.proj_add, OFam.proj_smul, smul_sub]`.

Normalize the expressions using the abelian group laws. Establish `h1` using `hall (x + z')`. Establish `h3` using `hall (x + δ • z')`. Rewrite `h1` using `[e1]`. Rewrite `h3` using `[e3]`.

Conclude with `polar h2 hδ hσδ hyy hzz h1 h3`. Conclude with `⟨z', hzz⟩`. Conclude with `⟨x, hyy⟩`. Take `⟨t, ht⟩` from `key`. Take `⟨hwe, hwf, hwa⟩` from `horth t`.

Establish `hfix' : σ (hf σ J (t - F.proj t) (t - F.proj t)) = hf σ J (t - F.proj t) (t - F.proj t)` using `(hsym _ _).symm`. Take `⟨u, hu⟩` from `hfix _ hfix' ht`. Use `⟨⟨Fin.snoc F.a (t - F.proj t), Fin.snoc F.inv (↑u⁻¹ : K), ?_, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `j`. Use `Fin.lastCases ?_ (fun i => ?_) j` and prove the remaining obligations.

Simplify using `only [Fin.snoc_last]`. Conclude with `hwe`. Simplify using `only [Fin.snoc_castSucc]`. Conclude with `F.ha_e i`. Introduce `j`.

Use `Fin.lastCases ?_ (fun i => ?_) j` and prove the remaining obligations. Simplify using `only [Fin.snoc_last]`. Conclude with `hwf`. Simplify using `only [Fin.snoc_castSucc]`. Conclude with `F.ha_f i`.

Introduce `i j`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>`. Introduce `hij`. Conclude with `absurd rfl hij`. Simplify using `only [Fin.snoc_last, Fin.snoc_castSucc]`.

Conclude with `hwa j'`. Simplify using `only [Fin.snoc_last, Fin.snoc_castSucc]`. Rewrite using `[hsym, hwa i', map_zero]`. Simplify using `only [Fin.snoc_castSucc]`. Conclude with `F.ho i' j' (fun h => hij (by rw [h]))`.

Introduce `j`. Use `Fin.lastCases ?_ (fun i => ?_) j` and prove the remaining obligations. Simplify using `only [Fin.snoc_last]`. Rewrite using `[← hu]`. Conclude with `Units.inv_mul u`.

Simplify using `only [Fin.snoc_castSucc]`. Conclude with `F.hinv i`.
-/
theorem OFam.extend {r : ℕ} (F : OFam σ J e f r) (hns : ¬ F.Spans) :
    Nonempty (OFam σ J e f (r + 1)) := by
  classical
  have hadd1 : ∀ x y z, hf σ J (x + y) z = hf σ J x z + hf σ J y z := by
    intro x y z
    simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hadd2 : ∀ x y z, hf σ J x (y + z) = hf σ J x y + hf σ J x z := by
    intro x y z
    simp only [hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  have hsub2 : ∀ x y z, hf σ J x (y - z) = hf σ J x y - hf σ J x z := by
    intro x y z
    simp only [hf, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]
  have hsm1 : ∀ (c : K) x y, hf σ J (c • x) y = c * hf σ J x y := by
    intro c x y
    simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsm2 : ∀ (c : K) x y, hf σ J x (c • y) = σ c * hf σ J x y := by
    intro c x y
    simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsym : ∀ x y, hf σ J y x = σ (hf σ J x y) := by
    intro x y
    simp only [hf, map_sum, map_mul, hσ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hJij : J j i = σ (J i j) := congrFun (congrFun hJ i) j
    rw [hJij]
    ring
  have horth := fun t => OFam.sub_proj_orth hσ hJ he hff hef F t
  unfold OFam.Spans at hns
  push_neg at hns
  obtain ⟨x, hx⟩ := hns
  have key : ∃ t : ι → K, hf σ J (t - F.proj t) (t - F.proj t) ≠ 0 := by
    by_cases hyy : hf σ J (x - F.proj x) (x - F.proj x) = 0
    · have hy0 : x - F.proj x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
      have hz' : ∃ z', hf σ J (x - F.proj x) z' ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hy0 (nondeg hdet hcon)
      obtain ⟨z', hz'⟩ := hz'
      have hyproj : ∀ t, hf σ J (x - F.proj x) (F.proj t) = 0 := by
        intro t
        obtain ⟨hye, hyf, hya⟩ := horth x
        generalize x - F.proj x = y at hye hyf hya ⊢
        simp only [OFam.proj, hadd2, hsm2, hf_sum_right, hye, hyf, hya, mul_zero,
          Finset.sum_const_zero, add_zero]
      have hyz : hf σ J (x - F.proj x) (z' - F.proj z') ≠ 0 := by
        rw [hsub2, hyproj, sub_zero]
        exact hz'
      by_cases hzz : hf σ J (z' - F.proj z') (z' - F.proj z') = 0
      · by_contra hall
        push_neg at hall
        apply hyz
        have e1 : (x + z') - F.proj (x + z') = (x - F.proj x) + (z' - F.proj z') := by
          rw [OFam.proj_add]
          abel
        have e3 : (x + δ • z') - F.proj (x + δ • z') = (x - F.proj x) + δ • (z' - F.proj z') := by
          rw [OFam.proj_add, OFam.proj_smul, smul_sub]
          abel
        have h1 := hall (x + z')
        have h3 := hall (x + δ • z')
        rw [e1] at h1
        rw [e3] at h3
        exact polar h2 hδ hσδ hyy hzz h1 h3
      · exact ⟨z', hzz⟩
    · exact ⟨x, hyy⟩
  obtain ⟨t, ht⟩ := key
  obtain ⟨hwe, hwf, hwa⟩ := horth t
  have hfix' : σ (hf σ J (t - F.proj t) (t - F.proj t)) = hf σ J (t - F.proj t) (t - F.proj t) :=
    (hsym _ _).symm
  obtain ⟨u, hu⟩ := hfix _ hfix' ht
  refine ⟨⟨Fin.snoc F.a (t - F.proj t), Fin.snoc F.inv (↑u⁻¹ : K), ?_, ?_, ?_, ?_⟩⟩
  · intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last]
      exact hwe
    · simp only [Fin.snoc_castSucc]
      exact F.ha_e i
  · intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last]
      exact hwf
    · simp only [Fin.snoc_castSucc]
      exact F.ha_f i
  · intro i j
    refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
      intro hij
    · exact absurd rfl hij
    · simp only [Fin.snoc_last, Fin.snoc_castSucc]
      exact hwa j'
    · simp only [Fin.snoc_last, Fin.snoc_castSucc]
      rw [hsym, hwa i', map_zero]
    · simp only [Fin.snoc_castSucc]
      exact F.ho i' j' (fun h => hij (by rw [h]))
  · intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last]
      rw [← hu]
      exact Units.inv_mul u
    · simp only [Fin.snoc_castSucc]
      exact F.hinv i

include hσ hJ he hff hef in
/- English proof (translation)
Establish `hadd1 : ∀ x y z, hf σ J (x + y) z = hf σ J x z + hf σ J y z`. Introduce `x y z`. Simplify using `only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]`. Establish `hadd2 : ∀ x y z, hf σ J x (y + z) = hf σ J x y + hf σ J x z`. Introduce `x y z`.

Simplify using `only [hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]`. Establish `hsub2 : ∀ x y z, hf σ J x (y - z) = hf σ J x y - hf σ J x z`. Introduce `x y z`. Simplify using `only [hf, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]`. Establish `hsm1 : ∀ (c : K) x y, hf σ J (c • x) y = c * hf σ J x y`.

Introduce `c x y`. Simplify using `only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hsm2 : ∀ (c : K) x y, hf σ J x (c • y) = σ c * hf σ J x y`.

Introduce `c x y`. Simplify using `only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hsym : ∀ x y, hf σ J y x = σ (hf σ J x y)`.

Introduce `x y`. Simplify using `only [hf, map_sum, map_mul, hσ]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hJij : J j i = σ (J i j)` using `congrFun (congrFun hJ i) j`.

Rewrite using `[hJij]`. Expand and normalize the polynomial expressions, which then agree. Establish `hfe : hf σ J f e = 1` using `by rw [hsym, hef, map_one]`. Set `v : Fin (r + 2) → ι → K` to `Fin.cons e (Fin.cons f F.a)`. Establish `hli : LinearIndependent K v`.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Establish `hpair : ∀ z, ∑ i, g i * hf σ J (v i) z = 0`. Introduce `z`. Establish `h1` using `congrArg (fun w => hf σ J w z) hg`.

Establish `h0 : hf σ J 0 z = 0` using `by simp [hf]`. Simplify using `only [hf_sum_left, hsm1] at h1`. Rewrite using `[h1, h0]`. Simplify using `only [Fin.sum_univ_succ, v, Fin.cons_zero, Fin.cons_succ] at hpair`. Establish `hg0 : g 0 = 0`.

Establish `h` using `hpair f`. Simplify using `only [hef, hff, F.ha_f, mul_zero, Finset.sum_const_zero, add_zero, mul_one] at h`. Conclude with `h`. Establish `hg1 : g (Fin.succ 0) = 0`. Establish `h` using `hpair e`.

Simplify using `only [he, hfe, F.ha_e, mul_zero, Finset.sum_const_zero, add_zero, mul_one, zero_add] at h`. Conclude with `h`. Establish `hgk : ∀ k : Fin r, g k.succ.succ = 0`. Introduce `k`. Establish `h` using `hpair (F.a k)`.

Establish `hek : hf σ J e (F.a k) = 0` using `by rw [hsym, F.ha_e, map_zero]`. Establish `hfk : hf σ J f (F.a k) = 0` using `by rw [hsym, F.ha_f, map_zero]`. Rewrite `h` using `[hek, hfk, Finset.sum_eq_single k]`. Establish `h2 : g k.succ.succ * hf σ J (F.a k) (F.a k) = 0` using `by simpa using h`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[F.hinv, mul_one]`. Use `_ = 0 := by rw [mul_comm (F.inv k), ← mul_assoc, h2, zero_mul]`. Introduce `j _ hjk`. Rewrite using `[F.ho j k hjk, mul_zero]`. Introduce `hk`.

Conclude with `absurd (Finset.mem_univ k) hk`. Introduce `i`. Use `Fin.cases hg0 (fun i' => ?_) i` and prove the remaining obligations. Conclude with `Fin.cases hg1 (fun k => hgk k) i'`. Establish `hcard` using `hli.fintype_card_le_finrank`.

Simplify `hcard` using `[Module.finrank_fintype_fun_eq_card]`.
-/
theorem OFam.card_le [Nontrivial K] {r : ℕ} (F : OFam σ J e f r) : r + 2 ≤ Fintype.card ι := by
  classical
  have hadd1 : ∀ x y z, hf σ J (x + y) z = hf σ J x z + hf σ J y z := by
    intro x y z
    simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hadd2 : ∀ x y z, hf σ J x (y + z) = hf σ J x y + hf σ J x z := by
    intro x y z
    simp only [hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  have hsub2 : ∀ x y z, hf σ J x (y - z) = hf σ J x y - hf σ J x z := by
    intro x y z
    simp only [hf, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]
  have hsm1 : ∀ (c : K) x y, hf σ J (c • x) y = c * hf σ J x y := by
    intro c x y
    simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsm2 : ∀ (c : K) x y, hf σ J x (c • y) = σ c * hf σ J x y := by
    intro c x y
    simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsym : ∀ x y, hf σ J y x = σ (hf σ J x y) := by
    intro x y
    simp only [hf, map_sum, map_mul, hσ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hJij : J j i = σ (J i j) := congrFun (congrFun hJ i) j
    rw [hJij]
    ring
  have hfe : hf σ J f e = 1 := by rw [hsym, hef, map_one]
  let v : Fin (r + 2) → ι → K := Fin.cons e (Fin.cons f F.a)
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hpair : ∀ z, ∑ i, g i * hf σ J (v i) z = 0 := by
      intro z
      have h1 := congrArg (fun w => hf σ J w z) hg
      have h0 : hf σ J 0 z = 0 := by simp [hf]
      simp only [hf_sum_left, hsm1] at h1
      rw [h1, h0]
    simp only [Fin.sum_univ_succ, v, Fin.cons_zero, Fin.cons_succ] at hpair
    have hg0 : g 0 = 0 := by
      have h := hpair f
      simp only [hef, hff, F.ha_f, mul_zero, Finset.sum_const_zero, add_zero, mul_one] at h
      exact h
    have hg1 : g (Fin.succ 0) = 0 := by
      have h := hpair e
      simp only [he, hfe, F.ha_e, mul_zero, Finset.sum_const_zero, add_zero, mul_one, zero_add] at h
      exact h
    have hgk : ∀ k : Fin r, g k.succ.succ = 0 := by
      intro k
      have h := hpair (F.a k)
      have hek : hf σ J e (F.a k) = 0 := by rw [hsym, F.ha_e, map_zero]
      have hfk : hf σ J f (F.a k) = 0 := by rw [hsym, F.ha_f, map_zero]
      rw [hek, hfk, Finset.sum_eq_single k] at h
      · have h2 : g k.succ.succ * hf σ J (F.a k) (F.a k) = 0 := by simpa using h
        calc g k.succ.succ = g k.succ.succ * (F.inv k * hf σ J (F.a k) (F.a k)) := by
              rw [F.hinv, mul_one]
          _ = 0 := by rw [mul_comm (F.inv k), ← mul_assoc, h2, zero_mul]
      · intro j _ hjk
        rw [F.ho j k hjk, mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    intro i
    refine Fin.cases hg0 (fun i' => ?_) i
    exact Fin.cases hg1 (fun k => hgk k) i'
  have hcard := hli.fintype_card_le_finrank
  simpa [Module.finrank_fintype_fun_eq_card] using hcard

include hσ hJ he hff hef hdet hfix h2 hδ hσδ in
/- English proof (translation)
Set `Pr : ℕ → Prop` to `fun r => Nonempty (OFam σ J e f r)`. Establish `h0 : Pr 0` using `⟨⟨Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, fun i => i.elim0, fun j => j.elim0⟩⟩`. Establish `hr : Pr (Nat.findGreatest Pr (Fintype.card ι))` using `Nat.findGreatest_spec (Nat.zero_le _) h0`. Take `⟨F⟩` from `hr`. Use `⟨_, F, ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hns`. Take `⟨F'⟩` from `OFam.extend hσ hJ he hff hef hdet hfix h2 hδ hσδ F hns`. Establish `hle` using `OFam.card_le hσ hJ he hff hef F'`. Establish `hlt : Nat.findGreatest Pr (Fintype.card ι) < Nat.findGreatest Pr (Fintype.card ι) + 1` using `Nat.lt_succ_self _`. Establish `hk : Nat.findGreatest Pr (Fintype.card ι) + 1 ≤ Fintype.card ι` using `by omega`.

Conclude with `Nat.findGreatest_is_greatest hlt hk (Nonempty.intro F')`.
-/
theorem exists_spans [Nontrivial K] : ∃ r, ∃ F : OFam σ J e f r, F.Spans := by
  classical
  let Pr : ℕ → Prop := fun r => Nonempty (OFam σ J e f r)
  have h0 : Pr 0 := ⟨⟨Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0,
    fun i => i.elim0, fun j => j.elim0⟩⟩
  have hr : Pr (Nat.findGreatest Pr (Fintype.card ι)) := Nat.findGreatest_spec (Nat.zero_le _) h0
  obtain ⟨F⟩ := hr
  refine ⟨_, F, ?_⟩
  by_contra hns
  obtain ⟨F'⟩ := OFam.extend hσ hJ he hff hef hdet hfix h2 hδ hσδ F hns
  have hle := OFam.card_le hσ hJ he hff hef F'
  have hlt : Nat.findGreatest Pr (Fintype.card ι) < Nat.findGreatest Pr (Fintype.card ι) + 1 :=
    Nat.lt_succ_self _
  have hk : Nat.findGreatest Pr (Fintype.card ι) + 1 ≤ Fintype.card ι := by omega
  exact Nat.findGreatest_is_greatest hlt hk (Nonempty.intro F')

end Ext

end ReciprocityTheory.ChartRestriction.G.SA

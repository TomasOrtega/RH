import Formalism.HermitianCurvature.HermitianCurvatureProofs.FourTermExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CvRhoOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfCVUnderIntOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellOrbitSet

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
  Formalism.FourierDecayAlt.P.FourTermExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Establish `hy' : yᴴ * Hpk k r * y = Hpk k r` using `hy`. Establish `hl : (Hpk k r * yᴴ * Hpk k r) * y = 1`. Combine the equalities or inequalities in the displayed calculation. Establish `hdet : IsUnit y.det` using `Matrix.isUnit_det_of_left_inverse hl`. Conclude with `⟨Matrix.mul_nonsing_inv y hdet, Matrix.nonsing_inv_mul y hdet⟩`.
-/
theorem gv_inv {y : Mat k r} (hy : y ∈ GV k r) : y * y⁻¹ = 1 ∧ y⁻¹ * y = 1 := by
  have hy' : yᴴ * Hpk k r * y = Hpk k r := hy
  have hl : (Hpk k r * yᴴ * Hpk k r) * y = 1 := by
    calc (Hpk k r * yᴴ * Hpk k r) * y = Hpk k r * (yᴴ * Hpk k r * y) := by simp only [mul_assoc]
      _ = 1 := by rw [hy', Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  have hdet : IsUnit y.det := Matrix.isUnit_det_of_left_inverse hl
  exact ⟨Matrix.mul_nonsing_inv y hdet, Matrix.nonsing_inv_mul y hdet⟩

/- English proof (translation)
Use `revert h`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Conclude with `loc_of_eq (by funext z; simp) (loc_zero m g)`. Introduce `j s hj ih h`.

Conclude with `loc_of_eq (by funext z; rw [Finset.sum_insert hj, add_comm]) (loc_add (ih fun i hi => h i (Finset.mem_insert_of_mem hi)) (h j (Finset.mem_insert_self j s)) (c j))`.
-/
theorem loc_finsum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (Φ : ι → Mat k r → E) {m : ℕ∞} {g : Mat k r}
    (h : ∀ i ∈ s, Loc m (Φ i) g) : Loc m (fun z => ∑ i ∈ s, c i • Φ i z) g := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    exact loc_of_eq (by funext z; simp) (loc_zero m g)
  · intro j s hj ih h
    exact loc_of_eq (by funext z; rw [Finset.sum_insert hj, add_comm])
      (loc_add (ih fun i hi => h i (Finset.mem_insert_of_mem hi)) (h j (Finset.mem_insert_self j s)) (c j))

/- English proof (translation)
Use `revert h`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Simplify using `[FourTermExpansion.top_apply'', FourTermExpansion.EZ_zero]`. Introduce `j s hj ih h`.

Establish `hs : ∀ i ∈ s, Loc 1 (Φ i) g` using `fun i hi => h i (Finset.mem_insert_of_mem hi)`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `z`. Rewrite using `[Finset.sum_insert hj, add_comm]`.

Use `_ = Top (FourTermExpansion.LT M) v a b (fun z => ∑ i ∈ s, c i • Φ i z) g + c j • Top (FourTermExpansion.LT M) v a b (Φ j) g := FourTermExpansion.top_lin M (loc_finsum s c Φ hs) (h j (Finset.mem_insert_self j s)) hg (c j) v a b`. Use `_ = _ := by rw [ih hs, Finset.sum_insert hj, add_comm]`.
-/
theorem top_finsum (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r) {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (Φ : ι → Mat k r → E) {g : Mat k r} (hg : g ∈ GV k r) (h : ∀ i ∈ s, Loc 1 (Φ i) g)
    (v : ℂ) (a b : Fin (2 * r + k + 1)) :
    Top (FourTermExpansion.LT M) v a b (fun z => ∑ i ∈ s, c i • Φ i z) g = ∑ i ∈ s, c i • Top (FourTermExpansion.LT M) v a b (Φ i) g := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp [FourTermExpansion.top_apply'', FourTermExpansion.EZ_zero]
  · intro j s hj ih h
    have hs : ∀ i ∈ s, Loc 1 (Φ i) g := fun i hi => h i (Finset.mem_insert_of_mem hi)
    calc Top (FourTermExpansion.LT M) v a b (fun z => ∑ i ∈ insert j s, c i • Φ i z) g
        = Top (FourTermExpansion.LT M) v a b (fun z => (∑ i ∈ s, c i • Φ i z) + c j • Φ j z) g := by
          congr 1; funext z; rw [Finset.sum_insert hj, add_comm]
      _ = Top (FourTermExpansion.LT M) v a b (fun z => ∑ i ∈ s, c i • Φ i z) g + c j • Top (FourTermExpansion.LT M) v a b (Φ j) g :=
          FourTermExpansion.top_lin M (loc_finsum s c Φ hs) (h j (Finset.mem_insert_self j s)) hg (c j) v a b
      _ = _ := by rw [ih hs, Finset.sum_insert hj, add_comm]

def Mc (y : Mat k r) (a b : Fin (2 * r + k + 1)) : Mat k r := y⁻¹ * Msg k r a b * y

/- English proof (translation)
Establish `hHH : Hpk k r * Hpk k r = 1` using `Formalism.QuantumDeterminants.GBasic.Hpk_sq k r`. Establish `hHH' : ∀ A : Mat k r, Hpk k r * (Hpk k r * A) = A` using `fun A => by rw [← mul_assoc, hHH, one_mul]`. Establish `hinvH : (Hpk k r)⁻¹ = Hpk k r` using `Matrix.inv_eq_left_inv hHH`. Establish `hy' : yᴴ * Hpk k r * y = Hpk k r` using `hy`. Establish `hinv : y⁻¹ = Hpk k r * yᴴ * Hpk k r`.

Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Simplify using `only [mul_assoc] at hy' ⊢`. Rewrite using `[hy', hHH]`. Rewrite using `[hinvH, hinv]`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Formalism.QuantumDeterminants.GBasic.Hpk_herm, mul_assoc, hHH, mul_one, hHH']`.
-/
private theorem Hpk_inv_conjTranspose_conj_eq_conj_of_mem_GV {y : Mat k r} (hy : y ∈ GV k r) (Z : Mat k r) :
    (Hpk k r)⁻¹ * (y⁻¹ * Z * y)ᴴ * Hpk k r = y⁻¹ * ((Hpk k r)⁻¹ * Zᴴ * Hpk k r) * y := by
  have hHH : Hpk k r * Hpk k r = 1 := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  have hHH' : ∀ A : Mat k r, Hpk k r * (Hpk k r * A) = A := fun A => by rw [← mul_assoc, hHH, one_mul]
  have hinvH : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv hHH
  have hy' : yᴴ * Hpk k r * y = Hpk k r := hy
  have hinv : y⁻¹ = Hpk k r * yᴴ * Hpk k r := by
    apply Matrix.inv_eq_left_inv
    simp only [mul_assoc] at hy' ⊢
    rw [hy', hHH]
  rw [hinvH, hinv]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Formalism.QuantumDeterminants.GBasic.Hpk_herm, mul_assoc,
    hHH, mul_one, hHH']

/- English proof (translation)
Unfold `hpart1`. Rewrite using `[Hpk_inv_conjTranspose_conj_eq_conj_of_mem_GV hy, Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul]`.
-/
private theorem hermitian_half_one_conj_of_mem_GV {y : Mat k r} (hy : y ∈ GV k r) (Z : Mat k r) :
    hpart1 (Hpk k r) (y⁻¹ * Z * y) = y⁻¹ * hpart1 (Hpk k r) Z * y := by
  unfold hpart1
  rw [Hpk_inv_conjTranspose_conj_eq_conj_of_mem_GV hy, Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul]

/- English proof (translation)
Unfold `hpart2`. Rewrite using `[Hpk_inv_conjTranspose_conj_eq_conj_of_mem_GV hy, Matrix.mul_smul, Matrix.smul_mul, mul_add, add_mul]`.
-/
private theorem hermitian_half_two_conj_of_mem_GV {y : Mat k r} (hy : y ∈ GV k r) (Z : Mat k r) :
    hpart2 (Hpk k r) (y⁻¹ * Z * y) = y⁻¹ * hpart2 (Hpk k r) Z * y := by
  unfold hpart2
  rw [Hpk_inv_conjTranspose_conj_eq_conj_of_mem_GV hy, Matrix.mul_smul, Matrix.smul_mul, mul_add, add_mul]

/- English proof (translation)
Use function extensionality and compare the values at `c d f g`. Use `show RdV (y⁻¹ * hpart1 (Hpk k r) (Matrix.single c d 1) * y) f g + Complex.I • RdV (y⁻¹ * hpart2 (Hpk k r) (Matrix.single c d 1) * y) f g = RdV (hpart1 (Hpk k r) (y⁻¹ * Matrix.single c d 1 * y)) f g + Complex.I • RdV (hpart2 (Hpk k r) (y⁻¹ * Matrix.single c d 1 * y)) f g`. Rewrite using `[hermitian_half_one_conj_of_mem_GV hy, hermitian_half_two_conj_of_mem_GV hy]`.
-/
theorem EHc_eq_LT (y : Mat k r) (hy : y ∈ GV k r) :
    Formalism.FourierDecayAlt.P.JFxB.EHc (E := E) k r y = FourTermExpansion.LT (Mc y) := by
  funext c d f g
  show RdV (y⁻¹ * hpart1 (Hpk k r) (Matrix.single c d 1) * y) f g +
      Complex.I • RdV (y⁻¹ * hpart2 (Hpk k r) (Matrix.single c d 1) * y) f g =
    RdV (hpart1 (Hpk k r) (y⁻¹ * Matrix.single c d 1 * y)) f g +
      Complex.I • RdV (hpart2 (Hpk k r) (y⁻¹ * Matrix.single c d 1 * y)) f g
  rw [hermitian_half_one_conj_of_mem_GV hy, hermitian_half_two_conj_of_mem_GV hy]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Mc, Msg, Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, Fintype.sum_prod_type, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']`.
-/
theorem Mc_expand (y : Mat k r) (a b : Fin (2 * r + k + 1)) :
    Mc y a b = ∑ ab : Fin (2 * r + k + 1) × Fin (2 * r + k + 1),
      ((y⁻¹) ab.1 a * y b ab.2) • Msg k r ab.1 ab.2 := by
  ext i j
  simp [Mc, Msg, Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, Fintype.sum_prod_type, ite_and,
    Finset.sum_ite_eq, Finset.sum_ite_eq']

/- English proof (translation)
Establish `hsum : ∑ ab : Fin (2 * r + k + 1) × Fin (2 * r + k + 1), ((y⁻¹) ab.1 a * y b ab.2) • (if ab.1 = ab.2 then v • Ψ g else 0) = if a = b then v • Ψ g else 0`. Apply the tactic sequence `have h1 : ∀ ab : Fin (2 * r + k + 1) × Fin (2 * r + k + 1), ((y⁻¹) ab.1 a * y b ab.2) • (if ab.1 = ab.2 then v • Ψ g else (0 : E)) = (if ab.1 = ab.2 then (y⁻¹) ab.1 a * y b ab.2 else 0) • (v • Ψ g) := fun ab => by split_ifs <;> simp`. Rewrite using `[Finset.sum_congr rfl (fun ab _ => h1 ab), ← Finset.sum_smul]`. Establish `h2 : ∑ ab : Fin (2 * r + k + 1) × Fin (2 * r + k + 1), (if ab.1 = ab.2 then (y⁻¹) ab.1 a * y b ab.2 else 0) = if a = b then 1 else 0`. Rewrite using `[Fintype.sum_prod_type]`.

Simplify using `only [Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Use `congrFun (congrFun (gv_inv hy).1 b) a` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply]`. Rewrite using `[Finset.sum_congr rfl (fun p _ => mul_comm _ _), this, Matrix.one_apply]`. Simplify using `only [eq_comm]`.

Rewrite using `[h2]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[FourTermExpansion.top_apply'' (Mc y), Mc_expand y a b, EZ_sum hΨ hg]`. Simplify using `only [FourTermExpansion.top_apply'', smul_add, Finset.sum_add_distrib, hsum]`.
-/
theorem conv (y : Mat k r) (hy : y ∈ GV k r) {Ψ : Mat k r → E} {g : Mat k r} (hΨ : Loc 1 Ψ g)
    (hg : g ∈ GV k r) (v : ℂ) (a b : Fin (2 * r + k + 1)) :
    Top (FourTermExpansion.LT (Mc y)) v a b Ψ g = ∑ ab : Fin (2 * r + k + 1) × Fin (2 * r + k + 1),
      ((y⁻¹) ab.1 a * y b ab.2) • Top (FourTermExpansion.LT (Msg k r)) v ab.1 ab.2 Ψ g := by
  have hsum : ∑ ab : Fin (2 * r + k + 1) × Fin (2 * r + k + 1),
      ((y⁻¹) ab.1 a * y b ab.2) • (if ab.1 = ab.2 then v • Ψ g else 0) = if a = b then v • Ψ g else 0 := by
    have h1 : ∀ ab : Fin (2 * r + k + 1) × Fin (2 * r + k + 1),
        ((y⁻¹) ab.1 a * y b ab.2) • (if ab.1 = ab.2 then v • Ψ g else (0 : E)) =
          (if ab.1 = ab.2 then (y⁻¹) ab.1 a * y b ab.2 else 0) • (v • Ψ g) := fun ab => by
      split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun ab _ => h1 ab), ← Finset.sum_smul]
    have h2 : ∑ ab : Fin (2 * r + k + 1) × Fin (2 * r + k + 1),
        (if ab.1 = ab.2 then (y⁻¹) ab.1 a * y b ab.2 else 0) = if a = b then 1 else 0 := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      have := congrFun (congrFun (gv_inv hy).1 b) a
      rw [Matrix.mul_apply] at this
      rw [Finset.sum_congr rfl (fun p _ => mul_comm _ _), this, Matrix.one_apply]
      simp only [eq_comm]
    rw [h2]
    split_ifs <;> simp
  rw [FourTermExpansion.top_apply'' (Mc y), Mc_expand y a b, EZ_sum hΨ hg]
  simp only [FourTermExpansion.top_apply'', smul_add, Finset.sum_add_distrib, hsum]

end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

namespace Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
  Formalism.FourierDecayAlt.P.FourTermExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Rewrite using `[← Fintype.sum_prod_type']`. Conclude with `(Fintype.sum_equiv (Fin.consEquiv fun _ => α) _ _ fun p => rfl).symm`.
-/
theorem sum_fun_succ {α M : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid M] {t : ℕ}
    (G : (Fin (t + 1) → α) → M) :
    ∑ C : Fin (t + 1) → α, G C = ∑ a : α, ∑ c : Fin t → α, G (Fin.cons a c) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => α) _ _ fun p => rfl).symm

/- English proof (translation)
Introduce `t`. Proceed by induction on `t with`. Consider the case `zero`. Introduce `f Φ x _ _`. Simplify using `[FourTermExpansion.fold_nil]`.

Consider the case `succ t ih`. Introduce `f Φ x hx hloc`. Take `⟨U, hU, hxU, hUl⟩` from `loc_spread hloc`. Establish `hle : ((t : ℕ) : ℕ∞) ≤ ((t + 1 : ℕ) : ℕ∞)` using `by exact_mod_cast Nat.le_succ t`. Establish `heq : ∀ z ∈ U, z ∈ GV k r → fold (Mc y) (List.ofFn fun j : Fin t => f j.succ) Φ z = (fun z => ∑ c : Fin t → Fin (2 * r + k + 1), ∑ d : Fin t → Fin (2 * r + k + 1), (∏ j, ((y⁻¹) (c j) (f j.succ).2.1 * y (f j.succ).2.2 (d j))) • fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j …` using `fun z hz hzG => ih (fun j => f j.succ) Φ z hzG (loc_mono hle (hUl z hz))`.

Establish `e1 : 1 + t = t + 1` using `by omega`. Establish `hF : ∀ c d : Fin t → Fin (2 * r + k + 1), Loc 1 (fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ) x`. Introduce `c d`. Use `FourTermExpansion.fold_loc (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) 1 Φ x (by rw [List.length_ofFn, e1]; exact hloc)` as an intermediate fact. Simplify using `using this`.

Establish `hin : ∀ (G : (Fin t → Fin (2 * r + k + 1)) → (Fin t → Fin (2 * r + k + 1)) → ℂ) (c : Fin t → Fin (2 * r + k + 1)), Loc 1 (fun z => ∑ d : Fin t → Fin (2 * r + k + 1), G c d • fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ z) x` using `fun G c => loc_finsum _ _ _ (fun d _ => hF c d)`. Establish `hΨ : ∀ G : (Fin t → Fin (2 * r + k + 1)) → (Fin t → Fin (2 * r + k + 1)) → ℂ, Loc 1 (fun z => ∑ c : Fin t → Fin (2 * r + k + 1), ∑ d : Fin t → Fin (2 * r + k + 1), G c d • fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ z) x` using `fun G => loc_of_eq (by funext z; simp) (loc_finsum Finset.univ (fun _ => (1 : ℂ)) (fun c z => ∑ d : Fin t → Fin (2 * r + k + 1), G c d • fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ z) (fun c _ => hin G c))`. Establish `hT : ∀ (G : (Fin t → Fin (2 * r + k + 1)) → (Fin t → Fin (2 * r + k + 1)) → ℂ) (v : ℂ) (a b : Fin (2 * r + k + 1)), Top (FourTermExpansion.LT (Msg k r)) v a b (fun z => ∑ c : Fin t → Fin (2 * r + k + 1), ∑ d : Fin t → Fin (2 * r + k + 1), G c d • fold (Msg k r) (List.ofFn fun j = …`. Introduce `G v a b`. Establish `e : (fun z => ∑ c : Fin t → Fin (2 * r + k + 1), ∑ d : Fin t → Fin (2 * r + k + 1), G c d • fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ z) = fun z => ∑ c ∈ Finset.univ, (1 : ℂ) • (fun c z => ∑ d : Fin t → Fin (2 * r + k + 1), G c d • fold (Msg k r) (List.ofFn f …`.

Use function extensionality and compare the values at `z`. Simplify using the standard rewrite rules. Rewrite using `[e, top_finsum (Msg k r) Finset.univ _ _ hx (fun c _ => hin G c)]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[one_smul, top_finsum (Msg k r) Finset.univ _ _ hx (fun d _ => hF c d)]`.

Rewrite using `[List.ofFn_succ, FourTermExpansion.fold_cons, FourTermExpansion.top_congr (Mc y) hU heq _ _ _ x hxU hx, conv y hy (hΨ _) hx]`. Simplify using `only [hT, sum_fun_succ, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, List.ofFn_succ, FourTermExpansion.fold_cons, Finset.smul_sum, smul_smul, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.
-/
theorem expandM (y : Mat k r) (hy : y ∈ GV k r) : ∀ (t : ℕ) (f : Fin t → ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))
    (Φ : Mat k r → E) (x : Mat k r), x ∈ GV k r → Loc (t : ℕ∞) Φ x →
    fold (Mc y) (List.ofFn f) Φ x = ∑ c : Fin t → Fin (2 * r + k + 1), ∑ d : Fin t → Fin (2 * r + k + 1),
      (∏ j, ((y⁻¹) (c j) (f j).2.1 * y (f j).2.2 (d j))) •
        fold (Msg k r) (List.ofFn fun j => ((f j).1, c j, d j)) Φ x := by
  intro t
  induction t with
  | zero =>
    intro f Φ x _ _
    simp [FourTermExpansion.fold_nil]
  | succ t ih =>
    intro f Φ x hx hloc
    obtain ⟨U, hU, hxU, hUl⟩ := loc_spread hloc
    have hle : ((t : ℕ) : ℕ∞) ≤ ((t + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_succ t
    have heq : ∀ z ∈ U, z ∈ GV k r → fold (Mc y) (List.ofFn fun j : Fin t => f j.succ) Φ z =
        (fun z => ∑ c : Fin t → Fin (2 * r + k + 1), ∑ d : Fin t → Fin (2 * r + k + 1),
          (∏ j, ((y⁻¹) (c j) (f j.succ).2.1 * y (f j.succ).2.2 (d j))) •
            fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ z) z :=
      fun z hz hzG => ih (fun j => f j.succ) Φ z hzG (loc_mono hle (hUl z hz))
    have e1 : 1 + t = t + 1 := by omega
    have hF : ∀ c d : Fin t → Fin (2 * r + k + 1),
        Loc 1 (fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ) x := by
      intro c d
      have := FourTermExpansion.fold_loc (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) 1 Φ x
        (by rw [List.length_ofFn, e1]; exact hloc)
      simpa using this
    have hin : ∀ (G : (Fin t → Fin (2 * r + k + 1)) → (Fin t → Fin (2 * r + k + 1)) → ℂ)
        (c : Fin t → Fin (2 * r + k + 1)),
        Loc 1 (fun z => ∑ d : Fin t → Fin (2 * r + k + 1), G c d •
          fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ z) x :=
      fun G c => loc_finsum _ _ _ (fun d _ => hF c d)
    have hΨ : ∀ G : (Fin t → Fin (2 * r + k + 1)) → (Fin t → Fin (2 * r + k + 1)) → ℂ,
        Loc 1 (fun z => ∑ c : Fin t → Fin (2 * r + k + 1), ∑ d : Fin t → Fin (2 * r + k + 1), G c d •
          fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ z) x := fun G =>
      loc_of_eq (by funext z; simp)
        (loc_finsum Finset.univ (fun _ => (1 : ℂ)) (fun c z => ∑ d : Fin t → Fin (2 * r + k + 1), G c d •
          fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ z) (fun c _ => hin G c))
    have hT : ∀ (G : (Fin t → Fin (2 * r + k + 1)) → (Fin t → Fin (2 * r + k + 1)) → ℂ) (v : ℂ)
        (a b : Fin (2 * r + k + 1)),
        Top (FourTermExpansion.LT (Msg k r)) v a b (fun z => ∑ c : Fin t → Fin (2 * r + k + 1),
          ∑ d : Fin t → Fin (2 * r + k + 1), G c d •
            fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ z) x =
        ∑ c : Fin t → Fin (2 * r + k + 1), ∑ d : Fin t → Fin (2 * r + k + 1), G c d •
          Top (FourTermExpansion.LT (Msg k r)) v a b (fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ) x := by
      intro G v a b
      have e : (fun z => ∑ c : Fin t → Fin (2 * r + k + 1), ∑ d : Fin t → Fin (2 * r + k + 1), G c d •
          fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ z) =
          fun z => ∑ c ∈ Finset.univ, (1 : ℂ) • (fun c z => ∑ d : Fin t → Fin (2 * r + k + 1), G c d •
            fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ z) c z := by
        funext z; simp
      rw [e, top_finsum (Msg k r) Finset.univ _ _ hx (fun c _ => hin G c)]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [one_smul, top_finsum (Msg k r) Finset.univ _ _ hx (fun d _ => hF c d)]
    rw [List.ofFn_succ, FourTermExpansion.fold_cons, FourTermExpansion.top_congr (Mc y) hU heq _ _ _ x hxU hx, conv y hy (hΨ _) hx]
    simp only [hT, sum_fun_succ, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, List.ofFn_succ, FourTermExpansion.fold_cons,
      Finset.smul_sum, smul_smul, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]

end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

namespace Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
  Formalism.FourierDecayAlt.P.FourTermExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Unfold `qminorOp`. Rewrite using `[Finset.sum_apply]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply]`. Simplify using `only [FourTermExpansion.fold, List.map_ofFn]`.

Both sides reduce to the same expression.
-/
theorem qm_eq' (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r) {t : ℕ}
    (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (Φ : Mat k r → E) (g : Mat k r) :
    qminorOp (FourTermExpansion.LT M) a b u Φ g = ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      fold M (List.ofFn fun j : Fin t => (u - ((j : ℕ) : ℂ), a (σ j), b j)) Φ g := by
  unfold qminorOp
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Pi.smul_apply]
  simp only [FourTermExpansion.fold, List.map_ofFn]
  rfl

/- English proof (translation)
Establish `hτ : ((Equiv.Perm.sign τ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) = 1`. Rewrite using `[← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]`. Simplify using the standard rewrite rules. Rewrite using `[FourTermExpansion.qm_eq, FourTermExpansion.qm_eq, Finset.smul_sum]`. Use `Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => ?_)` and prove the remaining obligations.

Use `show ((Equiv.Perm.sign σ : ℤ) : ℂ) • FourTermExpansion.PP a b u (τ * σ) Φ g = _`. Simplify using `only [Equiv.coe_mulLeft, smul_smul, Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul, ← mul_assoc, hτ, one_mul]`.
-/
theorem skewRow {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (Φ : Mat k r → E) (g : Mat k r)
    (τ : Equiv.Perm (Fin t)) :
    qminorOp (Q.EH k r) (a ∘ τ) b u Φ g = ((Equiv.Perm.sign τ : ℤ) : ℂ) • qminorOp (Q.EH k r) a b u Φ g := by
  have hτ : ((Equiv.Perm.sign τ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
  rw [FourTermExpansion.qm_eq, FourTermExpansion.qm_eq, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => ?_)
  show ((Equiv.Perm.sign σ : ℤ) : ℂ) • FourTermExpansion.PP a b u (τ * σ) Φ g = _
  simp only [Equiv.coe_mulLeft, smul_smul, Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul, ← mul_assoc, hτ,
    one_mul]

/- English proof (translation)
Unfold `Function.Injective at hc`. Use `push_neg at hc`. Take `⟨i, j, hij, hne⟩` from `hc`. Establish `hcτ : c ∘ Equiv.swap i j = c`. Use function extensionality and compare the values at `x`.

Simplify using `only [Function.comp_apply]`. Break down `eq_or_ne x i with rfl | hxi` into its components or cases. Simplify using `[hij]`. Break down `eq_or_ne x j with rfl | hxj` into its components or cases. Simplify using `[hij]`.

Rewrite using `[Equiv.swap_apply_of_ne_of_ne hxi hxj]`. Use `skewRow c b u Φ g (Equiv.swap i j)` as an intermediate fact. Rewrite `this` using `[hcτ, Equiv.Perm.sign_swap hne]`. Simplify using `only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul] at this`. Establish `h2` using `sub_eq_zero.mpr this`.

Rewrite `h2` using `[sub_neg_eq_add]`. Conclude with `FourTermExpansion.half _ h2`.
-/
theorem row_zero {t : ℕ} (c b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (Φ : Mat k r → E) (g : Mat k r)
    (hc : ¬ Function.Injective c) : qminorOp (Q.EH k r) c b u Φ g = 0 := by
  unfold Function.Injective at hc
  push_neg at hc
  obtain ⟨i, j, hij, hne⟩ := hc
  have hcτ : c ∘ Equiv.swap i j = c := by
    funext x
    simp only [Function.comp_apply]
    rcases eq_or_ne x i with rfl | hxi
    · simp [hij]
    rcases eq_or_ne x j with rfl | hxj
    · simp [hij]
    · rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]
  have := skewRow c b u Φ g (Equiv.swap i j)
  rw [hcτ, Equiv.Perm.sign_swap hne] at this
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul] at this
  have h2 := sub_eq_zero.mpr this
  rw [sub_neg_eq_add] at h2
  exact FourTermExpansion.half _ h2

/- English proof (translation)
Unfold `Function.Injective at hd`. Use `push_neg at hd`. Take `⟨i, j, hij, hne⟩` from `hd`. Establish `hdτ : d ∘ Equiv.swap i j = d`. Use function extensionality and compare the values at `x`.

Simplify using `only [Function.comp_apply]`. Break down `eq_or_ne x i with rfl | hxi` into its components or cases. Simplify using `[hij]`. Break down `eq_or_ne x j with rfl | hxj` into its components or cases. Simplify using `[hij]`.

Rewrite using `[Equiv.swap_apply_of_ne_of_ne hxi hxj]`. Use `FourTermExpansion.skewCol a u Φ g hg hloc d (Equiv.swap i j)` as an intermediate fact. Rewrite `this` using `[hdτ, Equiv.Perm.sign_swap hne]`. Simplify using `only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul] at this`. Establish `h2` using `sub_eq_zero.mpr this`.

Rewrite `h2` using `[sub_neg_eq_add]`. Conclude with `FourTermExpansion.half _ h2`.
-/
theorem col_zero {t : ℕ} (a d : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (Φ : Mat k r → E) (g : Mat k r)
    (hg : g ∈ GV k r) (hloc : Loc (t : ℕ∞) Φ g) (hd : ¬ Function.Injective d) :
    qminorOp (Q.EH k r) a d u Φ g = 0 := by
  unfold Function.Injective at hd
  push_neg at hd
  obtain ⟨i, j, hij, hne⟩ := hd
  have hdτ : d ∘ Equiv.swap i j = d := by
    funext x
    simp only [Function.comp_apply]
    rcases eq_or_ne x i with rfl | hxi
    · simp [hij]
    rcases eq_or_ne x j with rfl | hxj
    · simp [hij]
    · rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]
  have := FourTermExpansion.skewCol a u Φ g hg hloc d (Equiv.swap i j)
  rw [hdτ, Equiv.Perm.sign_swap hne] at this
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul] at this
  have h2 := sub_eq_zero.mpr this
  rw [sub_neg_eq_add] at h2
  exact FourTermExpansion.half _ h2

/- English proof (translation)
Rewrite using `[← Finset.sum_filter_of_ne (p := Function.Injective) (fun c _ hc => by`. Assume the negation of the conclusion as `h`. Conclude with `hc (hF c h))]`. Use `symm`. Use `Finset.sum_bij' (fun τ _ => e ∘ τ) (fun (c : Fin t → Fin n) (hc : c ∈ Finset.univ.filter (fun c : Fin t → Fin n => Function.Injective c)) => Equiv.ofBijective (e.symm ∘ c) ((Finite.injective_iff_bijective).mp (e.symm.injective.comp (Finset.mem_filter.mp hc).2))) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations.

Introduce `τ _`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `e.injective.comp τ.injective`. Introduce `c _`. Conclude with `Finset.mem_univ _`.

Introduce `τ _`. Use extensionality with `j`. Simplify using the standard rewrite rules. Introduce `c _`. Use function extensionality and compare the values at `j`.

Simplify using the standard rewrite rules. Introduce `τ _`. Both sides reduce to the same expression.
-/
theorem sum_inj {t n : ℕ} {M : Type*} [AddCommMonoid M] (e : Fin t ≃ Fin n) (F : (Fin t → Fin n) → M)
    (hF : ∀ c, ¬ Function.Injective c → F c = 0) :
    ∑ c, F c = ∑ τ : Equiv.Perm (Fin t), F (e ∘ τ) := by
  classical
  rw [← Finset.sum_filter_of_ne (p := Function.Injective) (fun c _ hc => by
    by_contra h
    exact hc (hF c h))]
  symm
  refine Finset.sum_bij' (fun τ _ => e ∘ τ)
    (fun (c : Fin t → Fin n) (hc : c ∈ Finset.univ.filter (fun c : Fin t → Fin n => Function.Injective c)) =>
      Equiv.ofBijective (e.symm ∘ c)
        ((Finite.injective_iff_bijective).mp (e.symm.injective.comp (Finset.mem_filter.mp hc).2)))
    ?_ ?_ ?_ ?_ ?_
  · intro τ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact e.injective.comp τ.injective
  · intro c _
    exact Finset.mem_univ _
  · intro τ _
    ext j
    simp
  · intro c _
    funext j
    simp
  · intro τ _
    rfl

end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

namespace Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
  Formalism.FourierDecayAlt.P.FourTermExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Use `Fintype.sum_equiv (Equiv.permCongr e) _ _ (fun τ => ?_)` and prove the remaining obligations. Rewrite using `[Equiv.Perm.sign_permCongr]`. Use `congr 1`. Conclude with `Fintype.prod_equiv e _ _ (fun j => by simp [Equiv.permCongr_apply])`.
-/
theorem det_sum {t n : ℕ} (e : Fin t ≃ Fin n) (A : Matrix (Fin n) (Fin n) ℂ) :
    ∑ τ : Equiv.Perm (Fin t), ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ j, A (e (τ j)) (e j) = A.det := by
  rw [Matrix.det_apply']
  refine Fintype.sum_equiv (Equiv.permCongr e) _ _ (fun τ => ?_)
  rw [Equiv.Perm.sign_permCongr]
  congr 1
  exact Fintype.prod_equiv e _ _ (fun j => by simp [Equiv.permCongr_apply])

/- English proof (translation)
Rewrite using `[← Matrix.det_transpose]`. Conclude with `det_sum e Aᵀ`.
-/
theorem det_sum' {t n : ℕ} (e : Fin t ≃ Fin n) (A : Matrix (Fin n) (Fin n) ℂ) :
    ∑ τ : Equiv.Perm (Fin t), ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ j, A (e j) (e (τ j)) = A.det := by
  rw [← Matrix.det_transpose]
  exact det_sum e Aᵀ

/- English proof (translation)
Establish `hn : Q.mdim k r 0 = 2 * r + k + 1` using `by unfold Q.mdim; simp`. Set `e : Fin (Q.mdim k r 0) ≃ Fin (2 * r + k + 1)` to `finCongr hn`. Establish `hP : Q.posL k r 0 = ⇑e` using `by funext j; ext; simp [Q.posL, e]`. Rewrite using `[hP, EHc_eq_LT y hy, qm_eq' (Mc y)]`. Establish `h1 : ∀ σ : Equiv.Perm (Fin (Q.mdim k r 0)), fold (Mc y) (List.ofFn fun j : Fin (Q.mdim k r 0) => (u - ((j : ℕ) : ℂ), e (σ j), e j)) f h = ∑ c : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1), ∑ d : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1), (∏ j, ((y⁻¹) (c j) (e (σ j)) * y (e j) (d j))) …` using `fun σ => expandM y hy _ _ f h hh hloc`.

Simplify using `only [h1]`. Establish `hA : ∀ σ : Equiv.Perm (Fin (Q.mdim k r 0)), (∑ c : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1), ∑ d : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1), (∏ j, ((y⁻¹) (c j) (e (σ j)) * y (e j) (d j))) • fold (Msg k r) (List.ofFn fun j => (u - ((j : ℕ) : ℂ), c j, d j)) f h) = ∑ c : Fin (Q.mdim …`. Introduce `σ`. Rewrite using `[← Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl (Fin (2 * r + k + 1))))]`. Use `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations.

Establish `hp : ∏ j, (y⁻¹) (c (σ j)) (e (σ j)) = ∏ j, (y⁻¹) (c j) (e j)` using `Equiv.prod_comp σ (fun i => (y⁻¹) (c i) (e i))`. Simplify using `only [Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl, Function.id_comp, Function.comp_apply, id_eq, Finset.prod_mul_distrib, hp]`. Both sides reduce to the same expression. Simplify using `only [hA]`. Rewrite using `[show (∑ σ : Equiv.Perm (Fin (Q.mdim k r 0)), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ∑ c : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1), ∑ d : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1), ((∏ j, (y⁻¹) (c j) (e j)) * ∏ j, y (e j) (d j)) • FourTermExpansion.PP c d u σ f h) = ∑ c : Fin (Q.mdim k …`.

Simplify using `only [FourTermExpansion.qm_eq, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Use `congr 1`. Use the proof step `ring]`. Establish `hC : ∀ c : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1), ∑ d : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1), ((∏ j, (y⁻¹) (c j) (e j)) * ∏ j, y (e j) (d j)) • qminorOp (Q.EH k r) c d u f h = ∑ τ : Equiv.Perm (Fin (Q.mdim k r 0)), ((∏ j, (y⁻¹) (c j) (e j)) * ∏ j, y (e j) ((e ∘ τ) j)) • qm …` using `fun c => sum_inj e _ (fun d hd => by rw [col_zero c d u f h hh hloc hd, smul_zero])`. Simplify using `only [hC]`. Rewrite using `[sum_inj e _ (fun c hc => Finset.sum_eq_zero fun τ _ => by rw [row_zero c _ u f h hc, smul_zero])]`.

Simplify using `only [skewRow, FourTermExpansion.skewCol (⇑e) u f h hh hloc]`. Establish `hdet : (∑ ρ : Equiv.Perm (Fin (Q.mdim k r 0)), ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ∏ j, (y⁻¹) (e (ρ j)) (e j)) * (∑ τ : Equiv.Perm (Fin (Q.mdim k r 0)), ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ j, y (e j) (e (τ j))) = 1`. Rewrite using `[det_sum e, det_sum' e, ← Matrix.det_mul, (gv_inv hy).2, Matrix.det_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_mul_sum, Finset.sum_smul]`.

Use `Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_smul]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, smul_smul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [hdet, one_smul]`.
-/
theorem capAdInv_loc (y : Mat k r) (hy : y ∈ GV k r) (u : ℂ) (f : Mat k r → E) (h : Mat k r) (hh : h ∈ GV k r)
    (hloc : Loc ((Q.mdim k r 0 : ℕ) : ℕ∞) f h) :
    qminorOp (Formalism.FourierDecayAlt.P.JFxB.EHc k r y) (Q.posL k r 0) (Q.posL k r 0) u f h =
      qminorOp (Q.EH k r) (Q.posL k r 0) (Q.posL k r 0) u f h := by
  have hn : Q.mdim k r 0 = 2 * r + k + 1 := by unfold Q.mdim; simp
  let e : Fin (Q.mdim k r 0) ≃ Fin (2 * r + k + 1) := finCongr hn
  have hP : Q.posL k r 0 = ⇑e := by funext j; ext; simp [Q.posL, e]
  rw [hP, EHc_eq_LT y hy, qm_eq' (Mc y)]
  have h1 : ∀ σ : Equiv.Perm (Fin (Q.mdim k r 0)),
      fold (Mc y) (List.ofFn fun j : Fin (Q.mdim k r 0) => (u - ((j : ℕ) : ℂ), e (σ j), e j)) f h =
        ∑ c : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1), ∑ d : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1),
          (∏ j, ((y⁻¹) (c j) (e (σ j)) * y (e j) (d j))) •
            fold (Msg k r) (List.ofFn fun j => (u - ((j : ℕ) : ℂ), c j, d j)) f h :=
    fun σ => expandM y hy _ _ f h hh hloc
  simp only [h1]
  have hA : ∀ σ : Equiv.Perm (Fin (Q.mdim k r 0)),
      (∑ c : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1), ∑ d : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1),
        (∏ j, ((y⁻¹) (c j) (e (σ j)) * y (e j) (d j))) •
          fold (Msg k r) (List.ofFn fun j => (u - ((j : ℕ) : ℂ), c j, d j)) f h) =
      ∑ c : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1), ∑ d : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1),
        ((∏ j, (y⁻¹) (c j) (e j)) * ∏ j, y (e j) (d j)) • FourTermExpansion.PP c d u σ f h := by
    intro σ
    rw [← Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl (Fin (2 * r + k + 1))))]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    have hp : ∏ j, (y⁻¹) (c (σ j)) (e (σ j)) = ∏ j, (y⁻¹) (c j) (e j) :=
      Equiv.prod_comp σ (fun i => (y⁻¹) (c i) (e i))
    simp only [Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl, Function.id_comp, Function.comp_apply,
      id_eq, Finset.prod_mul_distrib, hp]
    rfl
  simp only [hA]
  rw [show (∑ σ : Equiv.Perm (Fin (Q.mdim k r 0)), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ∑ c : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1), ∑ d : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1),
        ((∏ j, (y⁻¹) (c j) (e j)) * ∏ j, y (e j) (d j)) • FourTermExpansion.PP c d u σ f h) =
      ∑ c : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1), ∑ d : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1),
        ((∏ j, (y⁻¹) (c j) (e j)) * ∏ j, y (e j) (d j)) • qminorOp (Q.EH k r) c d u f h by
    simp only [FourTermExpansion.qm_eq, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    ring]
  have hC : ∀ c : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1),
      ∑ d : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1),
        ((∏ j, (y⁻¹) (c j) (e j)) * ∏ j, y (e j) (d j)) • qminorOp (Q.EH k r) c d u f h =
      ∑ τ : Equiv.Perm (Fin (Q.mdim k r 0)),
        ((∏ j, (y⁻¹) (c j) (e j)) * ∏ j, y (e j) ((e ∘ τ) j)) • qminorOp (Q.EH k r) c (e ∘ τ) u f h :=
    fun c => sum_inj e _ (fun d hd => by rw [col_zero c d u f h hh hloc hd, smul_zero])
  simp only [hC]
  rw [sum_inj e _ (fun c hc => Finset.sum_eq_zero fun τ _ => by rw [row_zero c _ u f h hc, smul_zero])]
  simp only [skewRow, FourTermExpansion.skewCol (⇑e) u f h hh hloc]
  have hdet : (∑ ρ : Equiv.Perm (Fin (Q.mdim k r 0)), ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ∏ j, (y⁻¹) (e (ρ j)) (e j)) *
      (∑ τ : Equiv.Perm (Fin (Q.mdim k r 0)), ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ j, y (e j) (e (τ j))) = 1 := by
    rw [det_sum e, det_sum' e, ← Matrix.det_mul, (gv_inv hy).2, Matrix.det_one]
  calc _ = ((∑ ρ : Equiv.Perm (Fin (Q.mdim k r 0)), ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ∏ j, (y⁻¹) (e (ρ j)) (e j)) *
      (∑ τ : Equiv.Perm (Fin (Q.mdim k r 0)), ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ j, y (e j) (e (τ j)))) •
        qminorOp (Q.EH k r) (⇑e) (⇑e) u f h := by
        rw [Finset.sum_mul_sum, Finset.sum_smul]
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun τ _ => ?_
        simp only [Function.comp_apply, smul_smul]
        congr 1
        ring
    _ = _ := by rw [hdet, one_smul]

end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

namespace Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `k r E _ _ y u f hy hf h hh`. Establish `hn : Q.mdim k r 0 = 2 * r + k + 1` using `by unfold Q.mdim; simp`. Conclude with `capAdInv_loc y hy u f h hh (by rw [hn]; exact hf h hh)`.
-/
theorem capAdInv : Formalism.FourierDecayAlt.P.JFxB.CapAdInv := by
  intro k r E _ _ y u f hy hf h hh
  have hn : Q.mdim k r 0 = 2 * r + k + 1 := by unfold Q.mdim; simp
  exact capAdInv_loc y hy u f h hh (by rw [hn]; exact hf h hh)

end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.capAdInv`.
-/
theorem Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.jf_capAdInv_alt : Formalism.FourierDecayAlt.P.JFxB.CapAdInv := Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.capAdInv

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.jf_cVRight_of Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.capAdInv`.
-/
theorem Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.jf_cVRight_alt : Formalism.FourierDecayAlt.JF.CVRight := Formalism.FourierDecayAlt.P.jf_cVRight_of Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.capAdInv

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.jf_cVRho_of Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.capAdInv`.
-/
theorem Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.jf_cVRho_alt : Formalism.FourierDecayAlt.JF.CVRho := Formalism.FourierDecayAlt.P.jf_cVRho_of Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.capAdInv

/- English proof (translation)
Introduce `_` and use `Formalism.FourierDecayAlt.P.big_cell_orbit_set`.
-/
theorem Formalism.FourierDecayAlt.P.big_cell_orbit_of_domain : Formalism.FourierDecayAlt.JF.GqOmOfDom := fun _ => Formalism.FourierDecayAlt.P.big_cell_orbit_set

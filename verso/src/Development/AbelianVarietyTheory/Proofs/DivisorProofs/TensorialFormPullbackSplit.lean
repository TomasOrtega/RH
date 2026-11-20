import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar

set_option autoImplicit false

noncomputable section

open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Pullback
open scoped ContDiff

namespace GlobalTheory.TorsionForm.Pullback.Tensorial

/- English proof (translation)
Unfold `sgn`. Establish `e : (S.erase i).filter (· < j) = (S.filter (· < j)).erase i`. Use extensionality with `x`. Simplify using `only [Finset.mem_filter, Finset.mem_erase]`. The claim follows by propositional logic.

Establish `hm : i ∈ S.filter (· < j)` using `by simp [hi, h]`. Rewrite using `[e, Finset.card_erase_of_mem hm]`. Take `⟨k, hk⟩` from `Nat.exists_eq_succ_of_ne_zero (Finset.card_pos.mpr ⟨i, hm⟩).ne'`. Rewrite using `[hk]`. Simplify using `[pow_succ]`.
-/
theorem sgn_erase_of_lt {m : ℕ} {i j : Fin m} {S : Finset (Fin m)} (hi : i ∈ S) (h : i < j) :
    sgn j (S.erase i) = -sgn j S := by
  unfold sgn
  have e : (S.erase i).filter (· < j) = (S.filter (· < j)).erase i := by
    ext x; simp only [Finset.mem_filter, Finset.mem_erase]; tauto
  have hm : i ∈ S.filter (· < j) := by simp [hi, h]
  rw [e, Finset.card_erase_of_mem hm]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_pos.mpr ⟨i, hm⟩).ne'
  rw [hk]; simp [pow_succ]

/- English proof (translation)
Unfold `sgn`. Use `congr 2`. Use extensionality with `x`. Simplify using `only [Finset.mem_filter, Finset.mem_erase]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨_, hx⟩, hx'⟩`. Conclude with `⟨hx, hx'⟩`. Introduce and unpack `⟨hx, hx'⟩`. Conclude with `⟨⟨(hx'.trans h).ne, hx⟩, hx'⟩`.
-/
theorem sgn_erase_of_gt {m : ℕ} {i j : Fin m} (S : Finset (Fin m)) (h : i < j) :
    sgn i (S.erase j) = sgn i S := by
  unfold sgn; congr 2; ext x; simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨_, hx⟩, hx'⟩; exact ⟨hx, hx'⟩
  · rintro ⟨hx, hx'⟩; exact ⟨⟨(hx'.trans h).ne, hx⟩, hx'⟩

/- English proof (translation)
Use function extensionality and compare the values at `S`. Simplify using `only [wedge, Pi.neg_apply, Finset.mem_erase]`. Apply the tactic sequence `by_cases hi : i ∈ S <;> by_cases hj : j ∈ S`. Simplify using `only [hi, hj, ne_eq, h.ne, h.ne', not_false_eq_true, and_self, if_true, sgn_erase_of_lt hi h, sgn_erase_of_gt S h, Finset.erase_right_comm (s := S) (a := i) (b := j)]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `[hi, hj]`. Simplify using `[hi, hj]`. Simplify using `[hi, hj]`.
-/
theorem wedge_anticomm_of_lt {m : ℕ} {i j : Fin m} (h : i < j) (w : Ext m) :
    wedge i (wedge j w) = -wedge j (wedge i w) := by
  funext S
  simp only [wedge, Pi.neg_apply, Finset.mem_erase]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · simp only [hi, hj, ne_eq, h.ne, h.ne', not_false_eq_true, and_self, if_true,
      sgn_erase_of_lt hi h, sgn_erase_of_gt S h, Finset.erase_right_comm (s := S) (a := i) (b := j)]
    ring
  · simp [hi, hj]
  · simp [hi, hj]
  · simp [hi, hj]

/- English proof (translation)
Break down `lt_trichotomy i j with h | rfl | h` into its components or cases. Conclude with `wedge_anticomm_of_lt h w`. Use function extensionality and compare the values at `S`. Simplify using `[wedge]`. Rewrite using `[wedge_anticomm_of_lt h w, neg_neg]`.
-/
theorem wedge_anticomm {m : ℕ} (i j : Fin m) (w : Ext m) :
    wedge i (wedge j w) = -wedge j (wedge i w) := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact wedge_anticomm_of_lt h w
  · funext S; simp [wedge]
  · rw [wedge_anticomm_of_lt h w, neg_neg]

/- English proof (translation)
The claim follows from `map_sum (AddMonoidHom.mk' (wedge i) (wedge_add i)) f s`.
-/
theorem wedge_sum {m : ℕ} {ι : Type} (s : Finset ι) (i : Fin m) (f : ι → Ext m) :
    wedge i (∑ x ∈ s, f x) = ∑ x ∈ s, wedge i (f x) :=
  map_sum (AddMonoidHom.mk' (wedge i) (wedge_add i)) f s

/- English proof (translation)
Simplify using `only [wedge_sum]`. Use `set S := ∑ k, ∑ i, wedge (e k) (wedge (e i) (F i k)) with hS`. Establish `h2 : S = -S` using `by conv_lhs => rw [hS, Finset.sum_comm]`. Rewrite using `[hS, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[wedge_anticomm, hF]`. Use function extensionality and compare the values at `x`. Use `congrFun h2 x` as an intermediate fact.

Simplify using `only [Pi.neg_apply] at this`. Use `show S x = 0`. Take the linear combination `(1 / 2 : ℂ) * this`.
-/
theorem sum_wedge_wedge_symm {m n : ℕ} (e : Fin n → Fin m) (F : Fin n → Fin n → Ext m)
    (hF : ∀ i k, F i k = F k i) :
    ∑ k, wedge (e k) (∑ i, wedge (e i) (F i k)) = 0 := by
  simp only [wedge_sum]
  set S := ∑ k, ∑ i, wedge (e k) (wedge (e i) (F i k)) with hS
  have h2 : S = -S := by
    conv_lhs => rw [hS, Finset.sum_comm]
    rw [hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [wedge_anticomm, hF]
  funext x
  have := congrFun h2 x
  simp only [Pi.neg_apply] at this
  show S x = 0
  linear_combination (1 / 2 : ℂ) * this

end GlobalTheory.TorsionForm.Pullback.Tensorial

namespace GlobalTheory.TorsionForm.Pullback.Tensorial

variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
  [NormedSpace ℂ E'] {g n : ℕ}

/- English proof (translation)
Establish `e1 : ∀ i, A (ψ i (Complex.I • w).1) = Complex.I • A (ψ i w.1)` using `fun i => by`. Rewrite using `[Prod.smul_fst, map_smul, hAI]`. Establish `e2 : ∀ i, Ab (ψ i (Complex.I • w).1) = -Complex.I • Ab (ψ i w.1)` using `fun i => by`. Rewrite using `[Prod.smul_fst, map_smul, hAbI]`. Unfold `d10 d01`.

Rewrite using `[hR, hR]`. Simplify using `only [e1, e2, wedge_smul, Finset.sum_add_distrib, ← Finset.smul_sum]`. Use `set X := ∑ i, wedge (dt g i) (A (ψ i w.1))`. Use `set Y := ∑ i, wedge (dtb g i) (Ab (ψ i w.1))`. Prove the components needed by the constructor for the conclusion.

Apply the tactic sequence `match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring`. Apply the tactic sequence `match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring`.
-/
theorem d10_and_d01_of_fderiv_eq_sum_wedge (R : Pt E' g → Ext (n + n + g)) (P : Pt E' g) (A Ab : E → Ext (n + n + g))
    (ψ : Fin n → E' →L[ℂ] E) (hAI : ∀ v, A (Complex.I • v) = Complex.I • A v)
    (hAbI : ∀ v, Ab (Complex.I • v) = -Complex.I • Ab v)
    (hR : ∀ w : Pt E' g, fderiv ℝ R P w =
      ∑ i, (wedge (dt g i) (A (ψ i w.1)) + wedge (dtb g i) (Ab (ψ i w.1)))) (w : Pt E' g) :
    d10 R P w = ∑ i, wedge (dt g i) (A (ψ i w.1)) ∧
      d01 R P w = ∑ i, wedge (dtb g i) (Ab (ψ i w.1)) := by
  have e1 : ∀ i, A (ψ i (Complex.I • w).1) = Complex.I • A (ψ i w.1) := fun i => by
    rw [Prod.smul_fst, map_smul, hAI]
  have e2 : ∀ i, Ab (ψ i (Complex.I • w).1) = -Complex.I • Ab (ψ i w.1) := fun i => by
    rw [Prod.smul_fst, map_smul, hAbI]
  unfold d10 d01
  rw [hR, hR]
  simp only [e1, e2, wedge_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
  set X := ∑ i, wedge (dt g i) (A (ψ i w.1))
  set Y := ∑ i, wedge (dtb g i) (Ab (ψ i w.1))
  constructor
  · match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring
  · match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

/- English proof (translation)
Establish `hA0 : A 0 = 0` using `by have := hA 0 0; simpa using this`. Establish `hAb0 : Ab 0 = 0` using `by have := hAb 0 0; simpa using this`. Establish `D` using `d10_and_d01_of_fderiv_eq_sum_wedge R P A Ab ψ hAI hAbI hR`. Establish `hv10 : ∀ a, d10 R P (vert E' a) = 0` using `fun a => by`. Rewrite using `[(D _).1]`.

Simplify using `[vert, hA0, wedge_zero]`. Establish `hv01 : ∀ a, d01 R P (vert E' a) = 0` using `fun a => by`. Rewrite using `[(D _).2]`. Simplify using `[vert, hAb0, wedge_zero]`. Establish `hdbar : dbarV R P = 0` using `by simp [dbarV, hv01, wedge_zero]`.

Establish `hadj : dbarAdj τ' h' R P = 0`. Simplify using `[dbarAdj, pointDifference, hv10, hR0, contr_zero]`. Establish `hnab : nablaE τ' h' β R P = 0`. Simplify using `only [nablaE, pointDifference, hR0, smul_zero, add_zero, connForm_zero, (D _).1, (D _).2]`. Rewrite using `[Finset.sum_add_distrib]`.

Establish `h1` using `sum_wedge_wedge_symm (dt g) (fun i k => A (ψ i (β k))) (fun i k => by rw [hψ])`. Establish `h2` using `sum_wedge_wedge_symm (dtb g) (fun i k => Ab (ψ i (β k))) (fun i k => by rw [hψ])`. Simplify `congrArg₂ (· + ·) h1 h2` using `[hor]`. Simplify using `[superconn, hnab, hdbar, hadj]`.
-/
theorem superconn_eq_zero (τ' : E' → Matrix (Fin g) (Fin g) ℂ) (h' : Pt E' g → ℝ) (β : Fin n → E')
    (u : ℝ) (R : Pt E' g → Ext (n + n + g)) (P : Pt E' g) (A Ab : E → Ext (n + n + g))
    (ψ : Fin n → E' →L[ℂ] E) (hA : ∀ v w, A (v + w) = A v + A w)
    (hAI : ∀ v, A (Complex.I • v) = Complex.I • A v) (hAb : ∀ v w, Ab (v + w) = Ab v + Ab w)
    (hAbI : ∀ v, Ab (Complex.I • v) = -Complex.I • Ab v) (hψ : ∀ i k, ψ i (β k) = ψ k (β i))
    (hR0 : R P = 0)
    (hR : ∀ w : Pt E' g, fderiv ℝ R P w =
      ∑ i, (wedge (dt g i) (A (ψ i w.1)) + wedge (dtb g i) (Ab (ψ i w.1)))) :
    superconn τ' h' β u R P = 0 := by
  have hA0 : A 0 = 0 := by have := hA 0 0; simpa using this
  have hAb0 : Ab 0 = 0 := by have := hAb 0 0; simpa using this
  have D := d10_and_d01_of_fderiv_eq_sum_wedge R P A Ab ψ hAI hAbI hR
  have hv10 : ∀ a, d10 R P (vert E' a) = 0 := fun a => by
    rw [(D _).1]; simp [vert, hA0, wedge_zero]
  have hv01 : ∀ a, d01 R P (vert E' a) = 0 := fun a => by
    rw [(D _).2]; simp [vert, hAb0, wedge_zero]
  have hdbar : dbarV R P = 0 := by simp [dbarV, hv01, wedge_zero]
  have hadj : dbarAdj τ' h' R P = 0 := by
    simp [dbarAdj, pointDifference, hv10, hR0, contr_zero]
  have hnab : nablaE τ' h' β R P = 0 := by
    simp only [nablaE, pointDifference, hR0, smul_zero, add_zero, connForm_zero, (D _).1, (D _).2]
    rw [Finset.sum_add_distrib]
    have h1 := sum_wedge_wedge_symm (dt g) (fun i k => A (ψ i (β k))) (fun i k => by rw [hψ])
    have h2 := sum_wedge_wedge_symm (dtb g) (fun i k => Ab (ψ i (β k))) (fun i k => by rw [hψ])
    simpa [hor] using congrArg₂ (· + ·) h1 h2
  simp [superconn, hnab, hdbar, hadj]

end GlobalTheory.TorsionForm.Pullback.Tensorial

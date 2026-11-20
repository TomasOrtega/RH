import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtXCastAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

noncomputable section
namespace GlobalTheory.RankOneMatrix

def stepAt (M : ℕ) {N : ℕ} (l : Fin N) : ℕ := if l.val < M then 1 else l.val - M + 1

variable {E : Type} [Field E] {M c : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `l`. Simplify using `only [Loc.eN, Pi.single_apply, Fin.ext_iff, Fin.val_mk]`.
-/
theorem eN_eq_single {N j : ℕ} (h : j < N) : Loc.eN E N j = Pi.single (⟨j, h⟩ : Fin N) 1 := by
  funext l
  simp only [Loc.eN, Pi.single_apply, Fin.ext_iff, Fin.val_mk]

/- English proof (translation)
Use function extensionality and compare the values at `l`. Establish `: l.val ≠ j` using `by have := l.isLt; omega`. Simplify using `[Loc.eN, this]`.
-/
theorem eN_eq_zero {N j : ℕ} (h : N ≤ j) : Loc.eN E N j = 0 := by
  funext l
  have : l.val ≠ j := by have := l.isLt; omega
  simp [Loc.eN, this]

/- English proof (translation)
Use `show (∀ l : Fin (M + c), l.1 ∉ {l | l < M + i} → v l = 0) ↔ _`. Simplify using `only [Set.mem_setOf_eq, not_lt]`.
-/
theorem mem_Ufl {v : Sp E (M + c)} {i : ℕ} :
    v ∈ Loc.Ufl E M c i ↔ ∀ l : Fin (M + c), M + i ≤ l.val → v l = 0 := by
  show (∀ l : Fin (M + c), l.1 ∉ {l | l < M + i} → v l = 0) ↔ _
  simp only [Set.mem_setOf_eq, not_lt]

def ColCond (x : Sp E (M + c) ≃ₗ[E] Sp E (M + c)) : Prop :=
  ∀ l m : Fin (M + c), stepAt M m ≤ stepAt M l → (M ≤ l.val ∨ M ≤ m.val) →
    x (Pi.single m 1) l = (Pi.single m 1 : Sp E (M + c)) l

/- English proof (translation)
Introduce `l m hlm hM`. Distinguish the cases in `hm : m.val < M`. Establish `hl : M ≤ l.val` using `hM.resolve_right (by omega)`. Establish `hv : (Pi.single m 1 : Sp E (M + c)) ∈ Loc.Ufl E M c 0`. Rewrite using `[mem_Ufl]`.

Introduce `l' hl'`. Establish `: l' ≠ m` using `by rintro rfl; omega`. Simplify using `[Pi.single_apply, this]`. Establish `h1` using `(mem_Ufl.1 (h.1 0 _ hv)) l (by omega)`. Establish `hne : l ≠ m` using `by rintro rfl; omega`.

Rewrite using `[h1]`. Simplify using `[Pi.single_apply, hne]`. Take `⟨j, hj⟩ : ∃ j, m.val = M + j` from `⟨m.val - M, by omega⟩`. Establish `hsingle : (Pi.single m 1 : Sp E (M + c)) = Loc.eN E (M + c) (M + j)`. Rewrite using `[eN_eq_single (by omega : M + j < M + c)]`.

Use `congr 1`. Conclude with `Fin.ext hj`. Distinguish the cases in `hl : l.val < M`. Establish `hj0 : j = 0`. Simplify using `only [stepAt, hl, hm, if_true, if_false] at hlm`.

Use linear arithmetic over natural numbers and integers. Substitute `hj0` using the available equality. Rewrite using `[hsingle, add_zero, h.2.1]`. Establish `hjl : M + j ≤ l.val`. Simplify using `only [stepAt, hl, hm, if_false] at hlm`.

Use linear arithmetic over natural numbers and integers. Establish `h3` using `(mem_Ufl.1 (h.2.2 j)) l hjl`. Rewrite `h3` using `[Pi.sub_apply, sub_eq_zero, ← hsingle]`. Conclude with `h3`.
-/
theorem colCond_of_R1cond {x : Sp E (M + c) ≃ₗ[E] Sp E (M + c)} (h : Loc.R1cond E M c x) : ColCond x := by
  intro l m hlm hM
  by_cases hm : m.val < M
  · have hl : M ≤ l.val := hM.resolve_right (by omega)
    have hv : (Pi.single m 1 : Sp E (M + c)) ∈ Loc.Ufl E M c 0 := by
      rw [mem_Ufl]
      intro l' hl'
      have : l' ≠ m := by rintro rfl; omega
      simp [Pi.single_apply, this]
    have h1 := (mem_Ufl.1 (h.1 0 _ hv)) l (by omega)
    have hne : l ≠ m := by rintro rfl; omega
    rw [h1]
    simp [Pi.single_apply, hne]
  · obtain ⟨j, hj⟩ : ∃ j, m.val = M + j := ⟨m.val - M, by omega⟩
    have hsingle : (Pi.single m 1 : Sp E (M + c)) = Loc.eN E (M + c) (M + j) := by
      rw [eN_eq_single (by omega : M + j < M + c)]
      congr 1
      exact Fin.ext hj
    by_cases hl : l.val < M
    · have hj0 : j = 0 := by
        simp only [stepAt, hl, hm, if_true, if_false] at hlm
        omega
      subst hj0
      rw [hsingle, add_zero, h.2.1]
    · have hjl : M + j ≤ l.val := by
        simp only [stepAt, hl, hm, if_false] at hlm
        omega
      have h3 := (mem_Ufl.1 (h.2.2 j)) l hjl
      rw [Pi.sub_apply, sub_eq_zero, ← hsingle] at h3
      exact h3

/- English proof (translation)
Use `⟨fun i v hv => ?_, ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite `hv`, the goal using `[mem_Ufl]`. Introduce `l hl`. Establish `hv' : v = ∑ m, v m • (Pi.single m 1 : Sp E (M + c))`. Use function extensionality and compare the values at `t`.

Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[hv', map_sum]`. Simplify using `only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Use `Finset.sum_eq_zero fun m _ => ?_` and prove the remaining obligations. Distinguish the cases in `hm : M + i ≤ m.val`.

Rewrite using `[hv m hm, zero_mul]`. Establish `hne : l ≠ m` using `by rintro rfl; omega`. Apply the tactic sequence `rw [h l m (by simp only [stepAt]; split_ifs <;> omega) (Or.inl (by omega))]`. Simplify using `[Pi.single_apply, hne]`. Distinguish the cases in `hc : M < M + c`.

Rewrite using `[eN_eq_single hc]`. Use function extensionality and compare the values at `l`. Apply the tactic sequence `exact h l _ (by simp only [stepAt, Fin.val_mk]; split_ifs <;> omega) (Or.inr le_rfl)`. Rewrite using `[eN_eq_zero (by omega), map_zero]`. Distinguish the cases in `hc : M + i < M + c`.

Rewrite using `[mem_Ufl, eN_eq_single hc]`. Introduce `l hl`. Apply the tactic sequence `rw [Pi.sub_apply, h l _ (by simp only [stepAt, Fin.val_mk]; split_ifs <;> omega) (Or.inr (by simp)), sub_self]`. Rewrite using `[eN_eq_zero (by omega), map_zero, sub_zero]`. Conclude with `zero_mem _`.
-/
theorem R1cond_of_colCond {x : Sp E (M + c) ≃ₗ[E] Sp E (M + c)} (h : ColCond x) : Loc.R1cond E M c x := by
  refine ⟨fun i v hv => ?_, ?_, fun i => ?_⟩
  · rw [mem_Ufl] at hv ⊢
    intro l hl
    have hv' : v = ∑ m, v m • (Pi.single m 1 : Sp E (M + c)) := by
      funext t
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv', map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : M + i ≤ m.val
    · rw [hv m hm, zero_mul]
    · have hne : l ≠ m := by rintro rfl; omega
      rw [h l m (by simp only [stepAt]; split_ifs <;> omega) (Or.inl (by omega))]
      simp [Pi.single_apply, hne]
  · by_cases hc : M < M + c
    · rw [eN_eq_single hc]
      funext l
      exact h l _ (by simp only [stepAt, Fin.val_mk]; split_ifs <;> omega) (Or.inr le_rfl)
    · rw [eN_eq_zero (by omega), map_zero]
  · by_cases hc : M + i < M + c
    · rw [mem_Ufl, eN_eq_single hc]
      intro l hl
      rw [Pi.sub_apply, h l _ (by simp only [stepAt, Fin.val_mk]; split_ifs <;> omega) (Or.inr (by simp)), sub_self]
    · rw [eN_eq_zero (by omega), map_zero, sub_zero]
      exact zero_mem _

/- English proof (translation)
Assemble the required witnesses or components as `⟨colCond_of_R1cond, R1cond_of_colCond⟩`.
-/
theorem R1cond_iff_colCond (x : Sp E (M + c) ≃ₗ[E] Sp E (M + c)) : Loc.R1cond E M c x ↔ ColCond x :=
  ⟨colCond_of_R1cond, R1cond_of_colCond⟩

section Matrix

variable {k : Type} [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A]
  (e : A ⊕ Fin c ≃ Fin (M + c)) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val)

include he in
/- English proof (translation)
Break down `r with a | i` into its components or cases. Use `eX_lt e rfl he a` as an intermediate fact. Simplify using `[lev, stepAt, this]`. Use `he i` as an intermediate fact. Simplify using `only [lev, Sum.elim_inr, stepAt, this]`.

Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem lev_eq_stepAt (r : A ⊕ Fin c) : lev 1 r = stepAt M (e r) := by
  rcases r with a | i
  · have := eX_lt e rfl he a
    simp [lev, stepAt, this]
  · have := he i
    simp only [lev, Sum.elim_inr, stepAt, this]
    split_ifs <;> omega

include he in
/- English proof (translation)
Break down `r with a | i` into its components or cases. Use `eX_lt e rfl he a` as an intermediate fact. Simplify using `only [Sum.isRight_inl, Bool.false_eq_true, false_iff, not_le]`. Conclude with `this`. Simplify using `[he i]`.
-/
theorem isRight_iff (r : A ⊕ Fin c) : r.isRight ↔ M ≤ (e r).val := by
  rcases r with a | i
  · have := eX_lt e rfl he a
    simp only [Sum.isRight_inl, Bool.false_eq_true, false_iff, not_le]
    exact this
  · simp [he i]

include he in

/- English proof (translation)
Establish `hval : ∀ r s, (locHom ι e x).val r s = ι (x (Pi.single (e s) 1) (e r))` using `fun r s => rfl`. Establish `hone : ∀ r s, (1 : Matrix (A ⊕ Fin c) (A ⊕ Fin c) k) r s = ι ((Pi.single (e s) (1 : E) : Sp E (M + c)) (e r))`. Introduce `r s`. Simplify using `only [Matrix.one_apply, Pi.single_apply, e.apply_eq_iff_eq]`. Apply the tactic sequence `split_ifs <;> simp`.

Prove the components needed by the constructor for the conclusion. Introduce `h l m hlm hM`. Use `h (e.symm l) (e.symm m) (by rw [lev_eq_stepAt e he, lev_eq_stepAt e he]; simpa using hlm) (by rw [isRight_iff e he, isRight_iff e he]; simpa using hM)` as an intermediate fact. Rewrite `this` using `[hval, hone]`. Simplify using `using ι.injective this`.

Introduce `h r s hrs hR`. Rewrite using `[hval, hone]`. Use `congr 1`. Apply `h` to reduce the goal to its premises. Rewrite using `[← lev_eq_stepAt e he, ← lev_eq_stepAt e he]`.

Conclude with `hrs`. Rewrite using `[← isRight_iff e he, ← isRight_iff e he]`. Conclude with `hR`.
-/
theorem inR_locHom_iff (x : Sp E (M + c) ≃ₗ[E] Sp E (M + c)) : VolN.InR 1 (locHom ι e x) ↔ ColCond x := by
  have hval : ∀ r s, (locHom ι e x).val r s = ι (x (Pi.single (e s) 1) (e r)) := fun r s => rfl
  have hone : ∀ r s, (1 : Matrix (A ⊕ Fin c) (A ⊕ Fin c) k) r s = ι ((Pi.single (e s) (1 : E) : Sp E (M + c)) (e r)) := by
    intro r s
    simp only [Matrix.one_apply, Pi.single_apply, e.apply_eq_iff_eq]
    split_ifs <;> simp
  constructor
  · intro h l m hlm hM
    have := h (e.symm l) (e.symm m) (by rw [lev_eq_stepAt e he, lev_eq_stepAt e he]; simpa using hlm)
      (by rw [isRight_iff e he, isRight_iff e he]; simpa using hM)
    rw [hval, hone] at this
    simpa using ι.injective this
  · intro h r s hrs hR
    rw [hval, hone]
    congr 1
    apply h
    · rw [← lev_eq_stepAt e he, ← lev_eq_stepAt e he]; exact hrs
    · rw [← isRight_iff e he, ← isRight_iff e he]; exact hR

end Matrix

/- English proof (translation)
Introduce `E k _ _ ι A _ _ M c c' e hcc he x`. Substitute `hcc` using the available equality. Rewrite using `[VolN.mem_R_iff, ← map_inv, inR_locHom_iff ι e he, inR_locHom_iff ι e he, ← R1cond_iff_colCond, ← R1cond_iff_colCond]`. Conclude with `Iff.rfl`.
-/
theorem mem_rationalFirstParabolic_iff_localGL_mem_rootExchange : ∀ {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ}
    (e : A ⊕ Fin c ≃ Fin (M + c')), c' = c → (∀ i : Fin c, (e (Sum.inr i)).val = M + i.val) →
    ∀ x : Sp E (M + c') ≃ₗ[E] Sp E (M + c'), x ∈ Loc.R1 E M c' ↔ locHom ι e x ∈ R k A c 1 := by
  intro E k _ _ ι A _ _ M c c' e hcc he x
  subst hcc
  rw [VolN.mem_R_iff, ← map_inv, inR_locHom_iff ι e he, inR_locHom_iff ι e he,
    ← R1cond_iff_colCond, ← R1cond_iff_colCond]
  exact Iff.rfl

end GlobalTheory.RankOneMatrix

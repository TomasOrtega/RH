import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientOfEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinSigmaFinEquivSymmStrictMonoToLex
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages

namespace GlobalTheory.JacStages

/- English proof (translation)
Use `show Sigma.Lex (· < ·) (fun _ => (· < ·)) (⟨a, b⟩ : Σ a, Fin (t a)) ⟨a, b'⟩ ↔ _`. Rewrite using `[Sigma.lex_iff]`. Simplify using the standard rewrite rules.
-/
theorem toLex_sigma_lt_iff_same {s : ℕ} {t : Fin s → ℕ} (a : Fin s) (b b' : Fin (t a)) :
    toLex (⟨a, b⟩ : Σ a, Fin (t a)) < toLex ⟨a, b'⟩ ↔ b < b' := by
  show Sigma.Lex (· < ·) (fun _ => (· < ·)) (⟨a, b⟩ : Σ a, Fin (t a)) ⟨a, b'⟩ ↔ _
  rw [Sigma.lex_iff]
  simp

/- English proof (translation)
Use `show Sigma.Lex (· < ·) (fun _ => (· < ·)) (⟨a, b⟩ : Σ a, Fin (t a)) ⟨a', b'⟩ ↔ _`. Rewrite using `[Sigma.lex_iff]`. Simplify using `[h]`.
-/
theorem toLex_sigma_lt_iff_ne {s : ℕ} {t : Fin s → ℕ} (a a' : Fin s) (b : Fin (t a)) (b' : Fin (t a'))
    (h : a ≠ a') : toLex (⟨a, b⟩ : Σ a, Fin (t a)) < toLex ⟨a', b'⟩ ↔ a < a' := by
  show Sigma.Lex (· < ·) (fun _ => (· < ·)) (⟨a, b⟩ : Σ a, Fin (t a)) ⟨a', b'⟩ ↔ _
  rw [Sigma.lex_iff]
  simp [h]

/- English proof (translation)
Rewrite using `[Fintype.sum_sigma, Fintype.sum_eq_add_sum_compl a, add_comm]`. Use `congr 1`. Rewrite using `[Finset.sum_filter, Fintype.sum_eq_add_sum_compl a, if_neg (lt_irrefl a), zero_add]`. Use `Finset.sum_congr rfl fun a' ha' => ?_` and prove the remaining obligations. Establish `hne : a ≠ a'` using `fun h => by simp [h] at ha'`.

Distinguish the cases in `hlt : a < a'`. Rewrite using `[if_pos hlt]`. Conclude with `Finset.sum_congr rfl fun b' _ => by rw [if_pos ((toLex_sigma_lt_iff_ne a a' b b' hne).2 hlt)]`. Rewrite using `[if_neg hlt]`. Conclude with `Finset.sum_eq_zero fun b' _ => by rw [if_neg (mt (toLex_sigma_lt_iff_ne a a' b b' hne).1 hlt)]`.

Rewrite using `[Finset.sum_filter]`. Conclude with `Finset.sum_congr rfl fun b' _ => by simp only [toLex_sigma_lt_iff_same]`.
-/
theorem sum_toLex_gt {s : ℕ} {t : Fin s → ℕ} (f : (Σ a, Fin (t a)) → ℤ) (a : Fin s) (b : Fin (t a)) :
    ∑ q, (if toLex (⟨a, b⟩ : Σ a, Fin (t a)) < toLex q then f q else 0) =
      (∑ a' with a < a', ∑ b', f ⟨a', b'⟩) + ∑ b' with b < b', f ⟨a, b'⟩ := by
  rw [Fintype.sum_sigma, Fintype.sum_eq_add_sum_compl a, add_comm]
  congr 1
  · rw [Finset.sum_filter, Fintype.sum_eq_add_sum_compl a, if_neg (lt_irrefl a), zero_add]
    refine Finset.sum_congr rfl fun a' ha' => ?_
    have hne : a ≠ a' := fun h => by simp [h] at ha'
    by_cases hlt : a < a'
    · rw [if_pos hlt]
      exact Finset.sum_congr rfl fun b' _ => by rw [if_pos ((toLex_sigma_lt_iff_ne a a' b b' hne).2 hlt)]
    · rw [if_neg hlt]
      exact Finset.sum_eq_zero fun b' _ => by rw [if_neg (mt (toLex_sigma_lt_iff_ne a a' b b' hne).1 hlt)]
  · rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun b' _ => by simp only [toLex_sigma_lt_iff_same]

/- English proof (translation)
Rewrite using `[Fintype.sum_sigma, Fintype.sum_eq_add_sum_compl a, add_comm]`. Use `congr 1`. Rewrite using `[Finset.sum_filter, Fintype.sum_eq_add_sum_compl a, if_neg (lt_irrefl a), zero_add]`. Use `Finset.sum_congr rfl fun a' ha' => ?_` and prove the remaining obligations. Establish `hne : a' ≠ a` using `fun h => by simp [h] at ha'`.

Distinguish the cases in `hlt : a' < a`. Rewrite using `[if_pos hlt]`. Conclude with `Finset.sum_congr rfl fun b' _ => by rw [if_pos ((toLex_sigma_lt_iff_ne a' a b' b hne).2 hlt)]`. Rewrite using `[if_neg hlt]`. Conclude with `Finset.sum_eq_zero fun b' _ => by rw [if_neg (mt (toLex_sigma_lt_iff_ne a' a b' b hne).1 hlt)]`.

Rewrite using `[Finset.sum_filter]`. Conclude with `Finset.sum_congr rfl fun b' _ => by simp only [toLex_sigma_lt_iff_same]`.
-/
theorem sum_toLex_lt {s : ℕ} {t : Fin s → ℕ} (f : (Σ a, Fin (t a)) → ℤ) (a : Fin s) (b : Fin (t a)) :
    ∑ q, (if toLex q < toLex (⟨a, b⟩ : Σ a, Fin (t a)) then f q else 0) =
      (∑ a' with a' < a, ∑ b', f ⟨a', b'⟩) + ∑ b' with b' < b, f ⟨a, b'⟩ := by
  rw [Fintype.sum_sigma, Fintype.sum_eq_add_sum_compl a, add_comm]
  congr 1
  · rw [Finset.sum_filter, Fintype.sum_eq_add_sum_compl a, if_neg (lt_irrefl a), zero_add]
    refine Finset.sum_congr rfl fun a' ha' => ?_
    have hne : a' ≠ a := fun h => by simp [h] at ha'
    by_cases hlt : a' < a
    · rw [if_pos hlt]
      exact Finset.sum_congr rfl fun b' _ => by rw [if_pos ((toLex_sigma_lt_iff_ne a' a b' b hne).2 hlt)]
    · rw [if_neg hlt]
      exact Finset.sum_eq_zero fun b' _ => by rw [if_neg (mt (toLex_sigma_lt_iff_ne a' a b' b hne).1 hlt)]
  · rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun b' _ => by simp only [toLex_sigma_lt_iff_same]

end GlobalTheory.JacStages

namespace GlobalTheory.JacStages

/- English proof (translation)
Establish `hiff : ∀ x y : Fin (∑ a, t a), toLex (finSigmaFinEquiv.symm x : Σ a, Fin (t a)) < toLex (finSigmaFinEquiv.symm y) ↔ x < y` using `fun x y => (finSigmaFinEquiv_symm_strictMono_lex s t).lt_iff_lt`. Establish `hd : ∀ a, ∑ b, (d' a b : ℤ) = d a` using `fun a => by`. Use `Fintype.card_congr (e' a)` as an intermediate fact. Simplify using `only [Fintype.card_sigma, Fintype.card_fin] at this`. Conclude with `this` after adjusting the coercions.

Use `set F : (Σ a, Fin (t a)) → ℤ := fun q => (d' q.1 q.2 : ℤ) with hF`. Establish `hgt : ∑ c' with c < c', (Fintype.card (Fin (d' (finSigmaFinEquiv.symm c').1 (finSigmaFinEquiv.symm c').2)) : ℤ) = ∑ q, if toLex (finSigmaFinEquiv.symm c) < toLex q then F q else 0`. Rewrite using `[Finset.sum_filter]`. Conclude with `Fintype.sum_equiv finSigmaFinEquiv.symm _ _ fun c' => by simp only [hiff, hF, Fintype.card_fin]`. Establish `hlt : ∑ c' with c' < c, (Fintype.card (Fin (d' (finSigmaFinEquiv.symm c').1 (finSigmaFinEquiv.symm c').2)) : ℤ) = ∑ q, if toLex q < toLex (finSigmaFinEquiv.symm c) then F q else 0`.

Rewrite using `[Finset.sum_filter]`. Conclude with `Fintype.sum_equiv finSigmaFinEquiv.symm _ _ fun c' => by simp only [hiff, hF, Fintype.card_fin]`. Unfold `modExp`. Rewrite using `[hgt, hlt]`. Generalize the expression as in `finSigmaFinEquiv.symm c = p`.

Take `⟨a, b⟩` from `p`. Rewrite using `[sum_toLex_gt, sum_toLex_lt]`. Simplify using `only [hF, Fintype.card_fin, hd]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem modExp_flat {s : ℕ} (d t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ)
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (c : Fin (∑ a, t a)) :
    modExp (fun c : Fin (∑ a, t a) => Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) c =
      modExp (fun a => Fin (d a)) (finSigmaFinEquiv.symm c).1 +
        modExp (fun b => Fin (d' (finSigmaFinEquiv.symm c).1 b)) (finSigmaFinEquiv.symm c).2 := by
  have hiff : ∀ x y : Fin (∑ a, t a),
      toLex (finSigmaFinEquiv.symm x : Σ a, Fin (t a)) < toLex (finSigmaFinEquiv.symm y) ↔ x < y :=
    fun x y => (finSigmaFinEquiv_symm_strictMono_lex s t).lt_iff_lt
  have hd : ∀ a, ∑ b, (d' a b : ℤ) = d a := fun a => by
    have := Fintype.card_congr (e' a)
    simp only [Fintype.card_sigma, Fintype.card_fin] at this
    exact_mod_cast this
  set F : (Σ a, Fin (t a)) → ℤ := fun q => (d' q.1 q.2 : ℤ) with hF
  have hgt : ∑ c' with c < c', (Fintype.card (Fin (d' (finSigmaFinEquiv.symm c').1 (finSigmaFinEquiv.symm c').2)) : ℤ) =
      ∑ q, if toLex (finSigmaFinEquiv.symm c) < toLex q then F q else 0 := by
    rw [Finset.sum_filter]
    exact Fintype.sum_equiv finSigmaFinEquiv.symm _ _ fun c' => by simp only [hiff, hF, Fintype.card_fin]
  have hlt : ∑ c' with c' < c, (Fintype.card (Fin (d' (finSigmaFinEquiv.symm c').1 (finSigmaFinEquiv.symm c').2)) : ℤ) =
      ∑ q, if toLex q < toLex (finSigmaFinEquiv.symm c) then F q else 0 := by
    rw [Finset.sum_filter]
    exact Fintype.sum_equiv finSigmaFinEquiv.symm _ _ fun c' => by simp only [hiff, hF, Fintype.card_fin]
  unfold modExp
  rw [hgt, hlt]
  generalize finSigmaFinEquiv.symm c = p
  obtain ⟨a, b⟩ := p
  rw [sum_toLex_gt, sum_toLex_lt]
  simp only [hF, Fintype.card_fin, hd]
  ring

end GlobalTheory.JacStages

namespace GlobalTheory.JacStages

/- English proof (translation)
Rewrite using `[deltaHalf_apply, deltaHalf_apply, relDeltaHalfD_apply]`. Simplify using `only [relEmbD_apply, det_leviEmb, map_prod, deltaHalf_apply, ← Finset.prod_mul_distrib, ← MonoidHom.mul_apply, ← absPow_add]`. Rewrite using `[← Fintype.prod_sigma (fun p : Σ a, Fin (t a) => absPow k ((modExp (fun a => Fin (d a)) p.1 : ℂ) / 2 + (modExp (fun b => Fin (d' p.1 b)) p.2 : ℂ) / 2) (Matrix.GeneralLinearGroup.det (g p.1 p.2))), ← Equiv.prod_comp finSigmaFinEquiv.symm]`. Use `Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[flatHom_apply, modExp_flat d t d' e' c]`.

Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deltaHalf_flatHom (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (d t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (g : ∀ a b, GL (Fin (d' a b)) k) :
    deltaHalf k (fun c : Fin (∑ a, t a) => Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2))
        (flatHom (fun a b => GL (Fin (d' a b)) k) g) =
      deltaHalf k (fun a => Fin (d a)) (relEmbD k e' g) * relDeltaHalfD k (fun a b => Fin (d' a b)) g := by
  rw [deltaHalf_apply, deltaHalf_apply, relDeltaHalfD_apply]
  simp only [relEmbD_apply, det_leviEmb, map_prod, deltaHalf_apply, ← Finset.prod_mul_distrib,
    ← MonoidHom.mul_apply, ← absPow_add]
  rw [← Fintype.prod_sigma (fun p : Σ a, Fin (t a) => absPow k ((modExp (fun a => Fin (d a)) p.1 : ℂ) / 2 +
      (modExp (fun b => Fin (d' p.1 b)) p.2 : ℂ) / 2) (Matrix.GeneralLinearGroup.det (g p.1 p.2))),
    ← Equiv.prod_comp finSigmaFinEquiv.symm]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [flatHom_apply, modExp_flat d t d' e' c]
  congr 2
  push_cast
  ring

end GlobalTheory.JacStages

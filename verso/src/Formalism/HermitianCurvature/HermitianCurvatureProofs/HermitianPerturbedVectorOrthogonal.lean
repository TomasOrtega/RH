import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianInsertionVectorOrthogonal

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants

noncomputable section

section N2d

variable {k : ℕ} (m : ℕ) (i : Fin (m + 1)) (ν : Fin (2 * (m + 1) + k + 1) → ℂ)

def VpF : Fin (2 * (m + 1) + k + 1) → ℂ := fun p =>
  bvec (esI k (m + 1) i) p - ν p + (-(herm (Hpk k (m + 1)) ν ν) / 2) * bvec (eI k (m + 1) i) p

/- English proof (translation)
Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `[eI, esI] at this`. Use `a.isLt` as an intermediate fact. Use `b.isLt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem eI_ne_esI (a b : Fin (m + 1)) : eI k (m + 1) a ≠ esI k (m + 1) b := by
  intro h; have := congrArg Fin.val h; simp [eI, esI] at this; have := a.isLt; have := b.isLt; omega

/- English proof (translation)
Unfold `VpF`. Rewrite using `[hν q (Or.inr hq)]`. Establish `hq2 : q ≠ eI k (m + 1) i` using `by intro h; rw [h] at hq; simp [eI] at hq; omega`. Distinguish the cases in `h : q = esI k (m + 1) i`. Rewrite using `[if_pos (by rw [sg_val', h]; simp [esI]; omega)]; simp [bvec, h, Pi.single_apply, hq2, Ne.symm (eI_ne_esI m i i)]`.

Rewrite using `[if_neg]`. Simplify using `[bvec, Pi.single_apply, h, hq2]`. Introduce `h'`. Apply `h` to reduce the goal to its premises. Use `ext`.

Rewrite `h'` using `[sg_val']`. Simplify using `[esI]`. Use linear arithmetic over natural numbers and integers.
-/
theorem VpF_star (hν : inWb k (m + 1) ν) (q : Fin (2 * (m + 1) + k + 1)) (hq : m + 1 + k < q.val) :
    VpF m i ν q = if (NFOne.sg k (m + 1) q).val = i.val then 1 else 0 := by
  unfold VpF
  rw [hν q (Or.inr hq)]
  have hq2 : q ≠ eI k (m + 1) i := by intro h; rw [h] at hq; simp [eI] at hq; omega
  by_cases h : q = esI k (m + 1) i
  · rw [if_pos (by rw [sg_val', h]; simp [esI]; omega)]; simp [bvec, h, Pi.single_apply, hq2, Ne.symm (eI_ne_esI m i i)]
  · rw [if_neg]
    · simp [bvec, Pi.single_apply, h, hq2]
    · intro h'; apply h; ext; rw [sg_val'] at h'; simp [esI]; omega

/- English proof (translation)
Establish `hi` using `i.isLt`. Use `set γ : ℂ := -(herm (Hpk k (m + 1)) ν ν) / 2 with hγ`. Establish `hpt : ∀ l, star (VpF m i ν l) * (WeylGroupFacts.sgn k (m + 1) l * VpF m i ν (WeylGroupFacts.tau k (m + 1) l)) = (if l = eI k (m + 1) i then star γ else 0) + (if l = esI k (m + 1) i then γ else 0) + star (ν l) * (WeylGroupFacts.sgn k (m + 1) l * ν (WeylGroupFacts.tau k (m + 1) l))`. Introduce `l`. Unfold `VpF`.

Rewrite using `[← hγ]`. Distinguish the cases in `h1 : l = eI k (m + 1) i`. Substitute `h1` using the available equality. Rewrite using `[tau_eI, hν (eI k (m + 1) i) (Or.inl (by simp only [eI]; omega)), hν (esI k (m + 1) i) (Or.inr (by simp [esI]; omega)), sgn_one _ (by simp [eI]; omega)]`. Simplify using `[bvec, Pi.single_apply, eI_ne_esI]`.

Distinguish the cases in `h2 : l = esI k (m + 1) i`. Substitute `h2` using the available equality. Rewrite using `[tau_esI, hν (eI k (m + 1) i) (Or.inl (by simp only [eI]; omega)), hν (esI k (m + 1) i) (Or.inr (by simp [esI]; omega)), sgn_one _ (by simp [esI]; omega)]`. Simplify using `[bvec, Pi.single_apply, Ne.symm (eI_ne_esI m i i)]`. Distinguish the cases in `hW : m + 1 ≤ l.val ∧ l.val ≤ m + 1 + k`.

Apply the tactic sequence `have ht : WeylGroupFacts.tau k (m + 1) l = l := by ext; rw [tau_val]; split_ifs <;> omega`. Rewrite using `[ht]`. Simplify using `[bvec, Pi.single_apply, h1, h2]`. Apply the tactic sequence `try ring`. Rewrite using `[hν l (by omega)]`.

Establish `ha : bvec (esI k (m + 1) i) l = 0` using `by simp [bvec, Pi.single_apply, h2]`. Establish `hb : bvec (eI k (m + 1) i) l = 0` using `by simp [bvec, Pi.single_apply, h1]`. Rewrite using `[ha, hb]`. Simplify using `[h1, h2]`. Rewrite using `[herm_expand, Finset.sum_congr rfl (fun l _ => hpt l), Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _), ← herm_expand]`.

Establish `hreal : star (herm (Hpk k (m + 1)) ν ν) = herm (Hpk k (m + 1)) ν ν` using `(herm_swap k (m + 1) ν ν).symm`. Rewrite using `[hγ, star_div₀, star_neg, hreal]`. Simplify using the standard rewrite rules. Apply the tactic sequence `try ring`.
-/
theorem VpF_iso (hν : inWb k (m + 1) ν) : herm (Hpk k (m + 1)) (VpF m i ν) (VpF m i ν) = 0 := by
  have hi := i.isLt
  set γ : ℂ := -(herm (Hpk k (m + 1)) ν ν) / 2 with hγ
  have hpt : ∀ l, star (VpF m i ν l) * (WeylGroupFacts.sgn k (m + 1) l * VpF m i ν (WeylGroupFacts.tau k (m + 1) l)) =
      (if l = eI k (m + 1) i then star γ else 0) + (if l = esI k (m + 1) i then γ else 0) +
        star (ν l) * (WeylGroupFacts.sgn k (m + 1) l * ν (WeylGroupFacts.tau k (m + 1) l)) := by
    intro l
    unfold VpF
    rw [← hγ]
    by_cases h1 : l = eI k (m + 1) i
    · subst h1
      rw [tau_eI, hν (eI k (m + 1) i) (Or.inl (by simp only [eI]; omega)), hν (esI k (m + 1) i) (Or.inr (by simp [esI]; omega)),
        sgn_one _ (by simp [eI]; omega)]
      simp [bvec, Pi.single_apply, eI_ne_esI]
    by_cases h2 : l = esI k (m + 1) i
    · subst h2
      rw [tau_esI, hν (eI k (m + 1) i) (Or.inl (by simp only [eI]; omega)), hν (esI k (m + 1) i) (Or.inr (by simp [esI]; omega)),
        sgn_one _ (by simp [esI]; omega)]
      simp [bvec, Pi.single_apply, Ne.symm (eI_ne_esI m i i)]
    by_cases hW : m + 1 ≤ l.val ∧ l.val ≤ m + 1 + k
    · have ht : WeylGroupFacts.tau k (m + 1) l = l := by ext; rw [tau_val]; split_ifs <;> omega
      rw [ht]
      simp [bvec, Pi.single_apply, h1, h2]
      try ring
    · rw [hν l (by omega)]
      have ha : bvec (esI k (m + 1) i) l = 0 := by simp [bvec, Pi.single_apply, h2]
      have hb : bvec (eI k (m + 1) i) l = 0 := by simp [bvec, Pi.single_apply, h1]
      rw [ha, hb]
      simp [h1, h2]
  rw [herm_expand, Finset.sum_congr rfl (fun l _ => hpt l), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _), ← herm_expand]
  have hreal : star (herm (Hpk k (m + 1)) ν ν) = herm (Hpk k (m + 1)) ν ν := (herm_swap k (m + 1) ν ν).symm
  rw [hγ, star_div₀, star_neg, hreal]
  simp
  try ring

/- English proof (translation)
Rewrite using `[herm_bvec_esI]`. Unfold `VpF`. Rewrite using `[hν _ (Or.inl (by simp only [eI]; omega))]`. Establish `h1 : eI k (m + 1) c ≠ eI k (m + 1) i`. Introduce `h`.

Apply `hc` to reduce the goal to its premises. Use `ext`. Use `congrArg Fin.val h` as an intermediate fact. Simplify `this` using `[eI]`. Simplify using `[bvec, Pi.single_apply, h1, eI_ne_esI]`.
-/
theorem VpF_esI (hν : inWb k (m + 1) ν) (c : Fin (m + 1)) (hc : c ≠ i) :
    herm (Hpk k (m + 1)) (VpF m i ν) (bvec (esI k (m + 1) c)) = 0 := by
  rw [herm_bvec_esI]
  unfold VpF
  rw [hν _ (Or.inl (by simp only [eI]; omega))]
  have h1 : eI k (m + 1) c ≠ eI k (m + 1) i := by
    intro h; apply hc; ext; have := congrArg Fin.val h; simpa [eI] using this
  simp [bvec, Pi.single_apply, h1, eI_ne_esI]

/- English proof (translation)
Establish `: herm (Hpk k (m + 1)) z' (VpF m i ν) = -herm (Hpk k (m + 1)) z' ν`. Rewrite using `[herm_expand, herm_expand, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl (fun l _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hW : m + 1 ≤ l.val ∧ l.val ≤ m + 1 + k`. Unfold `VpF`.

Establish `h1 : l ≠ eI k (m + 1) i` using `by intro h; rw [h] at hW; simp [eI] at hW; omega`. Establish `h2 : l ≠ esI k (m + 1) i` using `by intro h; rw [h] at hW; simp [esI] at hW; omega`. Simplify using `[bvec, Pi.single_apply, h1, h2]`. Apply the tactic sequence `rw [hz (WeylGroupFacts.tau k (m + 1) l) (by rw [tau_val]; split_ifs <;> omega)]; simp`. Rewrite using `[this, hzν, neg_zero]`.
-/
theorem hermitian_perturbed_vector_orthogonal (z' : Fin (2 * (m + 1) + k + 1) → ℂ) (hz : inWb k (m + 1) z') (hν : inWb k (m + 1) ν)
    (hzν : herm (Hpk k (m + 1)) z' ν = 0) : herm (Hpk k (m + 1)) z' (VpF m i ν) = 0 := by
  have : herm (Hpk k (m + 1)) z' (VpF m i ν) = -herm (Hpk k (m + 1)) z' ν := by
    rw [herm_expand, herm_expand, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    by_cases hW : m + 1 ≤ l.val ∧ l.val ≤ m + 1 + k
    · unfold VpF
      have h1 : l ≠ eI k (m + 1) i := by intro h; rw [h] at hW; simp [eI] at hW; omega
      have h2 : l ≠ esI k (m + 1) i := by intro h; rw [h] at hW; simp [esI] at hW; omega
      simp [bvec, Pi.single_apply, h1, h2]
    · rw [hz (WeylGroupFacts.tau k (m + 1) l) (by rw [tau_val]; split_ifs <;> omega)]; simp
  rw [this, hzν, neg_zero]

/- English proof (translation)
Rewrite using `[herm_bvec_esI]`. Simplify using `[bvec, Pi.single_apply, Ne.symm (eI_ne_esI m c b)]`.
-/
theorem bvec_esI_iso (b c : Fin (m + 1)) :
    herm (Hpk k (m + 1)) (bvec (esI k (m + 1) b)) (bvec (esI k (m + 1) c)) = 0 := by
  rw [herm_bvec_esI]; simp [bvec, Pi.single_apply, Ne.symm (eI_ne_esI m c b)]

/- English proof (translation)
Use `c.isLt` as an intermediate fact. Simplify using `only [bvec, Pi.single_apply]`. Distinguish the cases in `h : q = esI k (m + 1) c`. Rewrite using `[if_pos h, if_pos (by rw [sg_val', h]; simp [esI]; omega)]`. Rewrite using `[if_neg h, if_neg]`.

Introduce `h'`. Apply `h` to reduce the goal to its premises. Use `ext`. Rewrite `h'` using `[sg_val']`. Simplify using `[esI]`.

Use `q.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem bvec_esI_star (c : Fin (m + 1)) (q : Fin (2 * (m + 1) + k + 1)) :
    bvec (esI k (m + 1) c) q = if (NFOne.sg k (m + 1) q).val = c.val then 1 else 0 := by
  have := c.isLt
  simp only [bvec, Pi.single_apply]
  by_cases h : q = esI k (m + 1) c
  · rw [if_pos h, if_pos (by rw [sg_val', h]; simp [esI]; omega)]
  · rw [if_neg h, if_neg]; intro h'; apply h; ext; rw [sg_val'] at h'; simp [esI]; have := q.isLt; omega

end N2d

end

end Formalism.FourierDecayAlt.P.SignAntidiagonal

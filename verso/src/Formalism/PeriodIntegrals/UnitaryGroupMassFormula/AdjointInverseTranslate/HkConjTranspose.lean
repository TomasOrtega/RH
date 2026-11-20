import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.CoefLeftAAv

open Matrix Finset

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

def hkSig (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val, by split_ifs <;> omega⟩

def hkEps (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

/- English proof (translation)
Take `⟨i, hi⟩` from `i`. Take `⟨j, hj⟩` from `j`. Simplify using `only [Hpk, hkSig, hkEps, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem hk_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = hkSig k r i then hkEps k r i else 0 := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  simp only [Hpk, hkSig, hkEps, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [hkSig]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem hk_sig_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : hkSig k r (hkSig k r i) = i := by
  apply Fin.ext
  simp only [hkSig]
  split_ifs <;> omega

/- English proof (translation)
Simplify using `only [hkEps, hkSig]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem hk_eps_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : hkEps k r (hkSig k r i) = hkEps k r i := by
  simp only [hkEps, hkSig]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Unfold `hkEps`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem hk_eps_mul_self (k r : ℕ) (i : Fin (2 * r + k + 1)) : hkEps k r i * hkEps k r i = 1 := by
  unfold hkEps
  split_ifs <;> norm_num

/- English proof (translation)
Unfold `hkEps`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem hk_star_eps (k r : ℕ) (i : Fin (2 * r + k + 1)) : star (hkEps k r i) = hkEps k r i := by
  unfold hkEps
  split_ifs <;> simp

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[mul_apply]`. Repeatedly rewrite using `[hk_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, hk_sig_sig, hk_eps_sig]`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality.

Simplify using `[hk_eps_mul_self]`. Simplify using `[h, one_apply_ne' h]`.
-/
theorem hk_mul_self (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [mul_apply]
  simp_rw [hk_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    hk_sig_sig, hk_eps_sig]
  by_cases h : j = i
  · subst h; simp [hk_eps_mul_self]
  · simp [h, one_apply_ne' h]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[conjTranspose_apply, hk_apply, hk_apply]`. Distinguish the cases in `h : j = hkSig k r i`. Substitute `h` using the available equality. Simplify using `[hk_sig_sig, hk_eps_sig, hk_star_eps]`.

Establish `h' : i ≠ hkSig k r j` using `fun e => h (by rw [e, hk_sig_sig])`. Simplify using `[h, h']`.
-/
theorem hk_conjTranspose (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [conjTranspose_apply, hk_apply, hk_apply]
  by_cases h : j = hkSig k r i
  · subst h
    simp [hk_sig_sig, hk_eps_sig, hk_star_eps]
  · have h' : i ≠ hkSig k r j := fun e => h (by rw [e, hk_sig_sig])
    simp [h, h']

/- English proof (translation)
Introduce `k r` and use `⟨hk_conjTranspose k r, hk_mul_self k r⟩`.
-/
theorem hpk_involution : HpkInvol := fun k r => ⟨hk_conjTranspose k r, hk_mul_self k r⟩

end AAInvW

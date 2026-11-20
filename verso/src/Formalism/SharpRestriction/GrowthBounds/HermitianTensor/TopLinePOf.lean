import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DPsiMonomialIwh
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.BlockSubstitutionBlockEmb
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.QaNuNextAdd

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def vStar (m a b : ℕ) : XY (m + 1) →₀ ℕ :=
  Finsupp.single (Sum.inl 0) a + Finsupp.single (Sum.inr (Fin.last m)) b

/- English proof (translation)
Establish `e0` using `qtW_apply m v 0`. Establish `el` using `qtW_apply m v (Fin.last m)`. Establish `l0 : v (Sum.inl 0) ≤ xDeg v` using `Finset.single_le_sum (f := fun i : Fin (m + 1) => v (Sum.inl i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)`. Establish `ll : v (Sum.inr (Fin.last m)) ≤ yDeg v` using `Finset.single_le_sum (f := fun i : Fin (m + 1) => v (Sum.inr i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)`. Establish `a1 : v (Sum.inl 0) = a` using `by omega`.

Establish `a2 : v (Sum.inr (Fin.last m)) = b` using `by omega`. Establish `z1 : ∀ i : Fin (m + 1), i ≠ 0 → v (Sum.inl i) = 0`. Introduce `i hi`. Establish `h` using `Finset.add_sum_erase Finset.univ (fun i : Fin (m + 1) => v (Sum.inl i)) (Finset.mem_univ 0)`. Establish `h' : ∑ x ∈ Finset.univ.erase (0 : Fin (m + 1)), v (Sum.inl x) = 0`.

Establish `: ∑ x : Fin (m + 1), v (Sum.inl x) = a` using `hx`. Use linear arithmetic over natural numbers and integers. Conclude with `Finset.sum_eq_zero_iff.1 h' i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩)`. Establish `z2 : ∀ i : Fin (m + 1), i ≠ Fin.last m → v (Sum.inr i) = 0`. Introduce `i hi`.

Establish `h` using `Finset.add_sum_erase Finset.univ (fun i : Fin (m + 1) => v (Sum.inr i)) (Finset.mem_univ (Fin.last m))`. Establish `h' : ∑ x ∈ Finset.univ.erase (Fin.last m), v (Sum.inr x) = 0`. Establish `: ∑ x : Fin (m + 1), v (Sum.inr x) = b` using `hy`. Use linear arithmetic over natural numbers and integers. Conclude with `Finset.sum_eq_zero_iff.1 h' i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩)`.

Use extensionality with `w`. Unfold `vStar`. Rewrite using `[Finsupp.add_apply]`. Break down `w with i | i` into its components or cases. Distinguish the cases in `hi : i = 0`.

Substitute `hi` using the available equality. Simplify using `[a1]`. Establish `: (Sum.inl 0 : XY (m + 1)) ≠ Sum.inl i` using `fun h => hi (Sum.inl.inj h).symm`. Simplify using `[this, z1 i hi]`. Distinguish the cases in `hi : i = Fin.last m`.

Substitute `hi` using the available equality. Simplify using `[a2]`. Establish `: (Sum.inr (Fin.last m) : XY (m + 1)) ≠ Sum.inr i` using `fun h => hi (Sum.inr.inj h).symm`. Simplify using `[this, z2 i hi]`.
-/
theorem qt_comb (m a b : ℕ) (v : XY (m + 1) →₀ ℕ) (hx : xDeg v = a) (hy : yDeg v = b)
    (h0 : qtW m v 0 = a + b) (hl : qtW m v (Fin.last m) = 0) : v = vStar m a b := by
  classical
  have e0 := qtW_apply m v 0
  have el := qtW_apply m v (Fin.last m)
  have l0 : v (Sum.inl 0) ≤ xDeg v :=
    Finset.single_le_sum (f := fun i : Fin (m + 1) => v (Sum.inl i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
  have ll : v (Sum.inr (Fin.last m)) ≤ yDeg v :=
    Finset.single_le_sum (f := fun i : Fin (m + 1) => v (Sum.inr i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  have a1 : v (Sum.inl 0) = a := by omega
  have a2 : v (Sum.inr (Fin.last m)) = b := by omega
  have z1 : ∀ i : Fin (m + 1), i ≠ 0 → v (Sum.inl i) = 0 := by
    intro i hi
    have h := Finset.add_sum_erase Finset.univ (fun i : Fin (m + 1) => v (Sum.inl i)) (Finset.mem_univ 0)
    have h' : ∑ x ∈ Finset.univ.erase (0 : Fin (m + 1)), v (Sum.inl x) = 0 := by
      have : ∑ x : Fin (m + 1), v (Sum.inl x) = a := hx
      omega
    exact Finset.sum_eq_zero_iff.1 h' i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩)
  have z2 : ∀ i : Fin (m + 1), i ≠ Fin.last m → v (Sum.inr i) = 0 := by
    intro i hi
    have h := Finset.add_sum_erase Finset.univ (fun i : Fin (m + 1) => v (Sum.inr i)) (Finset.mem_univ (Fin.last m))
    have h' : ∑ x ∈ Finset.univ.erase (Fin.last m), v (Sum.inr x) = 0 := by
      have : ∑ x : Fin (m + 1), v (Sum.inr x) = b := hy
      omega
    exact Finset.sum_eq_zero_iff.1 h' i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩)
  ext w
  unfold vStar
  rw [Finsupp.add_apply]
  rcases w with i | i
  · by_cases hi : i = 0
    · subst hi; simp [a1]
    · have : (Sum.inl 0 : XY (m + 1)) ≠ Sum.inl i := fun h => hi (Sum.inl.inj h).symm
      simp [this, z1 i hi]
  · by_cases hi : i = Fin.last m
    · subst hi; simp [a2]
    · have : (Sum.inr (Fin.last m) : XY (m + 1)) ≠ Sum.inr i := fun h => hi (Sum.inr.inj h).symm
      simp [this, z2 i hi]

/- English proof (translation)
Establish `hne : (Fin.last m) ≠ 0`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.

Establish `e0` using `qtW_apply m (vStar m a b) 0`. Establish `el` using `qtW_apply m (vStar m a b) (Fin.last m)`. Establish `y : yDeg (vStar m a b) = b`. Unfold `yDeg vStar`. Simplify using `[Finsupp.single_apply]`.

Establish `v1 : vStar m a b (Sum.inr 0) = 0`. Unfold `vStar`. Simplify using `[hne]`. Establish `v2 : vStar m a b (Sum.inl 0) = a`. Unfold `vStar`.

Simplify using the standard rewrite rules. Establish `v3 : vStar m a b (Sum.inr (Fin.last m)) = b`. Unfold `vStar`. Simplify using the standard rewrite rules. Establish `v4 : vStar m a b (Sum.inl (Fin.last m)) = 0`.

Unfold `vStar`. Simplify using `[hne.symm]`. Apply the tactic sequence `constructor <;> omega`.
-/
theorem qtW_vStar (m a b : ℕ) (hm : 1 ≤ m) : qtW m (vStar m a b) 0 = a + b ∧ qtW m (vStar m a b) (Fin.last m) = 0 := by
  classical
  have hne : (Fin.last m) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have e0 := qtW_apply m (vStar m a b) 0
  have el := qtW_apply m (vStar m a b) (Fin.last m)
  have y : yDeg (vStar m a b) = b := by
    unfold yDeg vStar
    simp [Finsupp.single_apply]
  have v1 : vStar m a b (Sum.inr 0) = 0 := by
    unfold vStar
    simp [hne]
  have v2 : vStar m a b (Sum.inl 0) = a := by
    unfold vStar
    simp
  have v3 : vStar m a b (Sum.inr (Fin.last m)) = b := by
    unfold vStar
    simp
  have v4 : vStar m a b (Sum.inl (Fin.last m)) = 0 := by
    unfold vStar
    simp [hne.symm]
  constructor <;> omega

/- English proof (translation)
Rewrite `hΨ` using `[← tie3 h2 h5 hCO R m hm a b]`. Take `⟨f, hf, rfl⟩` from `hΨ`. Use `⟨coeff (vStar m a b) f, ?_⟩` and prove the remaining obligations. Establish `hT : coeff (vStar m a b) f • deltaB R.Kf m (PsiXY R.Kf m (monomial (vStar m a b) 1)) = deltaB R.Kf m (PsiXY R.Kf m (monomial (vStar m a b) (coeff (vStar m a b) f)))`. Rewrite using `[← map_smul, ← map_smul, smul_monomial, smul_eq_mul, mul_one]`.

Rewrite using `[hT]`. Establish `hsum : dPsi R.Kf m f = ∑ v ∈ f.support, deltaB R.Kf m (PsiXY R.Kf m (monomial v (coeff v f)))` using `by conv_lhs => rw [dPsi_apply, f.as_sum]`. Simplify using `only [map_sum]`. Take `⟨s0, sl⟩` from `qtW_vStar m a b hm`. Use extensionality with `u`.

Distinguish the cases in `hu : rowDeg u 0 = a + b ∧ rowDeg u (Fin.last m) = 0`. Rewrite using `[hsum, coeff_sum, Finset.sum_eq_single (vStar m a b)]`. Introduce `v hv hne`. Assume the negation of the conclusion as `hc`. Apply `hne` to reduce the goal to its premises.

Establish `w0` using `rowA_of_iwh (dPsi_monomial_iwh R.Kf m v (coeff v f)) 0 u hc`. Establish `wl` using `rowA_of_iwh (dPsi_monomial_iwh R.Kf m v (coeff v f)) (Fin.last m) u hc`. Conclude with `qt_comb m a b v (hf v hv).1 (hf v hv).2 (by rw [← w0, hu.1]) (by rw [← wl, hu.2])`. Introduce `hv`. Rewrite using `[notMem_support_iff.1 hv, monomial_zero, map_zero, map_zero, coeff_zero]`.

Establish `c1 : coeff u (dPsi R.Kf m f) = 0`. Assume the negation of the conclusion as `hc`. Conclude with `hu ⟨h0 u hc, hl u hc⟩`. Establish `c2 : coeff u (deltaB R.Kf m (PsiXY R.Kf m (monomial (vStar m a b) (coeff (vStar m a b) f)))) = 0`. Assume the negation of the conclusion as `hc`.

Establish `w0` using `rowA_of_iwh (dPsi_monomial_iwh R.Kf m _ _) 0 u hc`. Establish `wl` using `rowA_of_iwh (dPsi_monomial_iwh R.Kf m _ _) (Fin.last m) u hc`. Conclude with `hu ⟨by rw [w0, s0], by rw [wl, sl]⟩`. Rewrite using `[c1, c2]`.
-/
theorem topCore (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hCO : CartanOnto) {p n' : ℕ} (R : RS p n') (m : ℕ) (hm : 1 ≤ m) (a b : ℕ)
    (Ψ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) (hΨ : Ψ ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m a b)))
    (h0 : RowA 0 Ψ (a + b)) (hl : RowA (Fin.last m) Ψ 0) :
    ∃ c : R.Kf, Ψ = c • deltaB R.Kf m (PsiXY R.Kf m (monomial (vStar m a b) 1)) := by
  classical
  rw [← tie3 h2 h5 hCO R m hm a b] at hΨ
  obtain ⟨f, hf, rfl⟩ := hΨ
  refine ⟨coeff (vStar m a b) f, ?_⟩
  have hT : coeff (vStar m a b) f • deltaB R.Kf m (PsiXY R.Kf m (monomial (vStar m a b) 1)) =
      deltaB R.Kf m (PsiXY R.Kf m (monomial (vStar m a b) (coeff (vStar m a b) f))) := by
    rw [← map_smul, ← map_smul, smul_monomial, smul_eq_mul, mul_one]
  rw [hT]
  have hsum : dPsi R.Kf m f = ∑ v ∈ f.support, deltaB R.Kf m (PsiXY R.Kf m (monomial v (coeff v f))) := by
    conv_lhs => rw [dPsi_apply, f.as_sum]
    simp only [map_sum]
  obtain ⟨s0, sl⟩ := qtW_vStar m a b hm
  ext u
  by_cases hu : rowDeg u 0 = a + b ∧ rowDeg u (Fin.last m) = 0
  · rw [hsum, coeff_sum, Finset.sum_eq_single (vStar m a b)]
    · intro v hv hne
      by_contra hc
      apply hne
      have w0 := rowA_of_iwh (dPsi_monomial_iwh R.Kf m v (coeff v f)) 0 u hc
      have wl := rowA_of_iwh (dPsi_monomial_iwh R.Kf m v (coeff v f)) (Fin.last m) u hc
      exact qt_comb m a b v (hf v hv).1 (hf v hv).2 (by rw [← w0, hu.1]) (by rw [← wl, hu.2])
    · intro hv
      rw [notMem_support_iff.1 hv, monomial_zero, map_zero, map_zero, coeff_zero]
  · have c1 : coeff u (dPsi R.Kf m f) = 0 := by
      by_contra hc
      exact hu ⟨h0 u hc, hl u hc⟩
    have c2 : coeff u (deltaB R.Kf m (PsiXY R.Kf m (monomial (vStar m a b) (coeff (vStar m a b) f)))) = 0 := by
      by_contra hc
      have w0 := rowA_of_iwh (dPsi_monomial_iwh R.Kf m _ _) 0 u hc
      have wl := rowA_of_iwh (dPsi_monomial_iwh R.Kf m _ _) (Fin.last m) u hc
      exact hu ⟨by rw [w0, s0], by rw [wl, sl]⟩
    rw [c1, c2]

/- English proof (translation)
Introduce `p n' R r hr a b Ψ hΨ h0 hl`. Establish `hA : Antitone (nuOf (wtPQ (r + 1) a b))` using `nuOf_anti _ (wtPQ_anti (r + 1) a b (by omega))`. Take `⟨c, hc⟩` from `topCore h2 h5 hCO R (r + 1) (by omega) a b Ψ hΨ h0 hl`. Take `⟨c', hc'⟩` from `topCore h2 h5 hCO R (r + 1) (by omega) a b (hw R.Kf (le_refl (r + 1 + 1)) (nuOf (wtPQ (r + 1) a b))) (hwMem R.Kf _ _ le_rfl _ hA) (by have h := rowA_hw R.Kf _ _ hA 0; rwa [nuOf_wt_zero] at h) (by have h := rowA_hw R.Kf _ _ hA (Fin.last (r + 1)); rwa [nuOf_last] at h)`. Establish `he` using `(hwMulP R.Kf _ _ _ hA hA).2`.

Use `set Z := deltaB R.Kf (r + 1) (PsiXY R.Kf (r + 1) (monomial (vStar (r + 1) a b) 1)) with hZ`. Rewrite `he` using `[hc', smul_eq_C_mul, map_mul, eval_C]`. Rewrite using `[hc', hc, smul_eq_C_mul, smul_eq_C_mul, map_mul, eval_C, ← mul_assoc, ← C_mul]`. Use `congr 2`. Rewrite using `[mul_assoc, mul_comm _ c', he, mul_one]`.
-/
theorem topLineP_of (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hCO : CartanOnto) : TopLineP := by
  intro p n' R r hr a b Ψ hΨ h0 hl
  have hA : Antitone (nuOf (wtPQ (r + 1) a b)) := nuOf_anti _ (wtPQ_anti (r + 1) a b (by omega))
  obtain ⟨c, hc⟩ := topCore h2 h5 hCO R (r + 1) (by omega) a b Ψ hΨ h0 hl
  obtain ⟨c', hc'⟩ := topCore h2 h5 hCO R (r + 1) (by omega) a b (hw R.Kf (le_refl (r + 1 + 1)) (nuOf (wtPQ (r + 1) a b)))
    (hwMem R.Kf _ _ le_rfl _ hA)
    (by have h := rowA_hw R.Kf _ _ hA 0; rwa [nuOf_wt_zero] at h)
    (by have h := rowA_hw R.Kf _ _ hA (Fin.last (r + 1)); rwa [nuOf_last] at h)
  have he := (hwMulP R.Kf _ _ _ hA hA).2
  set Z := deltaB R.Kf (r + 1) (PsiXY R.Kf (r + 1) (monomial (vStar (r + 1) a b) 1)) with hZ
  rw [hc', smul_eq_C_mul, map_mul, eval_C] at he
  rw [hc', hc, smul_eq_C_mul, smul_eq_C_mul, map_mul, eval_C, ← mul_assoc, ← C_mul]
  congr 2
  rw [mul_assoc, mul_comm _ c', he, mul_one]

end Formalism.MainNotions.flipOneThree.Pf

end

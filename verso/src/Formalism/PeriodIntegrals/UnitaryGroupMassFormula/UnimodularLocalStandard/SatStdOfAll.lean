import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.ExistsGoodForm

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
variable {m : Type*} [Fintype m] [DecidableEq m]

/- English proof (translation)
Unfold `altE`. Rewrite using `[stdH_apply]`. Establish `hs : (∑ i, v i * conj ((n • Pi.single j w : m → ℂ) i)) = (n : ℂ) * (v j * conj w)`. Rewrite using `[Finset.sum_eq_single j]`. Simplify using `[nsmul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `i _ hi`. Simplify using `[hi]`. Simplify using the standard rewrite rules. Rewrite using `[hs, ← Complex.ofReal_inv, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, ← Complex.ofReal_natCast, Complex.im_ofReal_mul, div_eq_mul_inv]`.
-/
lemma altE_single (L : PeriodPair) (v : m → ℂ) (n : ℕ) (j : m) (w : ℂ) :
    altE (stdH L m) v (n • Pi.single j w) = (n : ℝ) * (v j * conj w).im / area L := by
  classical
  unfold altE
  rw [stdH_apply]
  have hs : (∑ i, v i * conj ((n • Pi.single j w : m → ℂ) i)) = (n : ℂ) * (v j * conj w) := by
    rw [Finset.sum_eq_single j]
    · simp [nsmul_eq_mul]
      ring
    · intro i _ hi
      simp [hi]
    · simp
  rw [hs, ← Complex.ofReal_inv, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    zero_add, ← Complex.ofReal_natCast, Complex.im_ofReal_mul, div_eq_mul_inv]

/- English proof (translation)
Rewrite using `[cmL_omega1, cmL_omega2]`. Simplify using `only [Complex.real_smul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma alpha_eq (x y : ℤ) :
    lam * ((x * a : ℂ) + y * cmTheta b d) =
      (x : ℝ) • (cmL a b d ha hd lam hlam).ω₁ + (y : ℝ) • (cmL a b d ha hd lam hlam).ω₂ := by
  rw [cmL_omega1, cmL_omega2]
  simp only [Complex.real_smul]
  push_cast
  ring

/- English proof (translation)
Rewrite using `[cmL_omega1, cmL_omega2]`. Simplify using `only [Complex.real_smul]`. Use `push_cast`. Take the linear combination `(-(lam * y)) * hn`.
-/
lemma theta_alpha_eq (hn : cmTheta b d * (b - cmTheta b d) = (a : ℂ) * c) (x y : ℤ) :
    cmTheta b d * (lam * ((x * a : ℂ) + y * cmTheta b d)) =
      ((-y * c : ℤ) : ℝ) • (cmL a b d ha hd lam hlam).ω₁ +
        ((x * a + y * b : ℤ) : ℝ) • (cmL a b d ha hd lam hlam).ω₂ := by
  rw [cmL_omega1, cmL_omega2]
  simp only [Complex.real_smul]
  push_cast
  linear_combination (-(lam * y)) * hn

/- English proof (translation)
Use `set L := cmL a b d ha hd lam hlam with hL`. Take `⟨s, t, hz⟩` from `coords L ((n : ℂ) * w)`. Take `⟨k1, hk1⟩` from `h1`. Take `⟨k2, hk2⟩` from `h2`. Establish `hnim : ∀ u : ℂ, (n : ℝ) * (w * u).im = (((n : ℂ) * w) * u).im`.

Introduce `u`. Rewrite using `[mul_assoc]`. Simplify using `[Complex.mul_im]`. Rewrite `hk1` using `[hnim, hz, alpha_eq (ha := ha) (hd := hd) (hlam := hlam), im_mul_conj]`. Rewrite `hk2` using `[hnim, hz, theta_alpha_eq (ha := ha) (hd := hd) (hlam := hlam) hn, im_mul_conj]`.

Take `⟨j1, hj1⟩` from `int_of_div L hk1`. Take `⟨j2, hj2⟩` from `int_of_div L hk2`. Move the coercions through the operations in `at hj1 hj2`. Establish `hQs : ((a * x ^ 2 + b * x * y + c * y ^ 2 : ℤ) : ℝ) * s = ((-(y * c * j1 + x * j2) : ℤ) : ℝ)`. Use `push_cast`.

Take the linear combination `(-((y : ℝ) * c)) * hj1 + (-(x : ℝ)) * hj2`. Establish `hQt : ((a * x ^ 2 + b * x * y + c * y ^ 2 : ℤ) : ℝ) * t = (((x * a + y * b) * j1 - y * j2 : ℤ) : ℝ)`. Use `push_cast`. Take the linear combination `((x : ℝ) * a + y * b) * hj1 + (-(y : ℝ)) * hj2`. Rewrite using `[show ((n * (a * x ^ 2 + b * x * y + c * y ^ 2) : ℤ) : ℂ) * w = ((a * x ^ 2 + b * x * y + c * y ^ 2 : ℤ) : ℂ) * ((n : ℂ) * w) by push_cast; ring, hz]`.

Use `(lattice_iff L _).mpr ⟨-(y * c * j1 + x * j2), (x * a + y * b) * j1 - y * j2, ?_⟩` and prove the remaining obligations. Establish `cs` using `congrArg (fun r : ℝ => (r : ℂ)) hQs`. Establish `ct` using `congrArg (fun r : ℝ => (r : ℂ)) hQt`. Simplify using `only [Complex.ofReal_mul, Complex.ofReal_intCast] at cs ct`. Simplify using `only [Complex.real_smul, Complex.ofReal_intCast]`.

Take the linear combination `L.ω₁ * cs + L.ω₂ * ct`.
-/
lemma coord_mem (hn : cmTheta b d * (b - cmTheta b d) = (a : ℂ) * c) (x y : ℤ) (n : ℕ) (w : ℂ)
    (h1 : ∃ k : ℤ, (n : ℝ) * (w * conj (lam * ((x * a : ℂ) + y * cmTheta b d))).im
      / area (cmL a b d ha hd lam hlam) = k)
    (h2 : ∃ k : ℤ, (n : ℝ) * (w * conj (cmTheta b d * (lam * ((x * a : ℂ) + y * cmTheta b d)))).im
      / area (cmL a b d ha hd lam hlam) = k) :
    ((n * (a * x ^ 2 + b * x * y + c * y ^ 2) : ℤ) : ℂ) * w ∈ (cmL a b d ha hd lam hlam).lattice := by
  set L := cmL a b d ha hd lam hlam with hL
  obtain ⟨s, t, hz⟩ := coords L ((n : ℂ) * w)
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  have hnim : ∀ u : ℂ, (n : ℝ) * (w * u).im = (((n : ℂ) * w) * u).im := by
    intro u
    rw [mul_assoc]
    simp [Complex.mul_im]
  rw [hnim, hz, alpha_eq (ha := ha) (hd := hd) (hlam := hlam), im_mul_conj] at hk1
  rw [hnim, hz, theta_alpha_eq (ha := ha) (hd := hd) (hlam := hlam) hn, im_mul_conj] at hk2
  obtain ⟨j1, hj1⟩ := int_of_div L hk1
  obtain ⟨j2, hj2⟩ := int_of_div L hk2
  push_cast at hj1 hj2
  have hQs : ((a * x ^ 2 + b * x * y + c * y ^ 2 : ℤ) : ℝ) * s = ((-(y * c * j1 + x * j2) : ℤ) : ℝ) := by
    push_cast
    linear_combination (-((y : ℝ) * c)) * hj1 + (-(x : ℝ)) * hj2
  have hQt : ((a * x ^ 2 + b * x * y + c * y ^ 2 : ℤ) : ℝ) * t =
      (((x * a + y * b) * j1 - y * j2 : ℤ) : ℝ) := by
    push_cast
    linear_combination ((x : ℝ) * a + y * b) * hj1 + (-(y : ℝ)) * hj2
  rw [show ((n * (a * x ^ 2 + b * x * y + c * y ^ 2) : ℤ) : ℂ) * w =
      ((a * x ^ 2 + b * x * y + c * y ^ 2 : ℤ) : ℂ) * ((n : ℂ) * w) by push_cast; ring, hz]
  refine (lattice_iff L _).mpr ⟨-(y * c * j1 + x * j2), (x * a + y * b) * j1 - y * j2, ?_⟩
  have cs := congrArg (fun r : ℝ => (r : ℂ)) hQs
  have ct := congrArg (fun r : ℝ => (r : ℂ)) hQt
  simp only [Complex.ofReal_mul, Complex.ofReal_intCast] at cs ct
  simp only [Complex.real_smul, Complex.ofReal_intCast]
  linear_combination L.ω₁ * cs + L.ω₂ * ct

/- English proof (translation)
Establish `hn` using `theta_norm hok.1`. Establish `hall' : ∀ j, ∃ N : ℕ, ¬ l ∣ N ∧ N • (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d)) : m → ℂ) ∈ Λ` using `hall`. Use `choose N hNl hNmem using hall'`. Use `set Q : ℤ := a * x ^ 2 + b * x * y + c * y ^ 2 with hQdef`. Use `⟨Q.natAbs * Q.natAbs * ∏ j, N j, ?_, ?_⟩` and prove the remaining obligations.

Introduce `hdvd`. Break down `(Nat.Prime.dvd_mul hl).mp hdvd with h | h` into its components or cases. Apply the tactic sequence `rcases (Nat.Prime.dvd_mul hl).mp h with h' | h' <;> exact hQ (Int.natCast_dvd.mpr h')`. Take `⟨j, _, hj⟩` from `(Prime.dvd_finset_prod_iff hl.prime _).mp h`. Conclude with `hNl j hj`.

Introduce `v hv`. Establish `hvd : v ∈ dualLat (stdH (cmL a b d ha hd lam hlam) m) Λ`. Rewrite using `[hsd]`. Conclude with `hv`. Rewrite `hvd` using `[mem_dualLat_iff]`.

Rewrite using `[mem_stdLat_iff]`. Introduce `i`. Establish `e1` using `hvd _ (hNmem i)`. Establish `e2` using `hvd _ (hθ _ (hNmem i))`. Establish `hsm : cmTheta b d • (N i • Pi.single i (lam * ((x * a : ℂ) + y * cmTheta b d)) : m → ℂ) = N i • Pi.single i (cmTheta b d * (lam * ((x * a : ℂ) + y * cmTheta b d)))`.

Use extensionality with `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `[nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `[hk]`. Rewrite `e1` using `[altE_single]`. Rewrite `e2` using `[hsm, altE_single]`. Establish `hm` using `coord_mem hn x y (N i) (v i) e1 e2`. Establish `hmem : ((N i : ℤ) * Q) • v i ∈ (cmL a b d ha hd lam hlam).lattice`.

Rewrite using `[zsmul_eq_mul]`. Conclude with `hm` after adjusting the coercions. Establish `hnZ : ((Q.natAbs * Q.natAbs * ∏ j, N j : ℕ) : ℤ) = (Q * ∏ j ∈ Finset.univ.erase i, (N j : ℤ)) * ((N i : ℤ) * Q)`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]`. Use `push_cast`.

Rewrite using `[abs_mul_abs_self]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Pi.smul_apply, ← natCast_zsmul, hnZ, mul_smul]`. Conclude with `Submodule.smul_mem _ _ hmem`.
-/
lemma sat_std_of_all (hok : CmOK a b c d) {l : ℕ} (hl : l.Prime) (x y : ℤ)
    (hQ : ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2) (Λ : AddSubgroup (m → ℂ))
    (hsd : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ) (hθ : ∀ v ∈ Λ, cmTheta b d • v ∈ Λ)
    (hall : ∀ j, SatMem l Λ (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d)))) :
    ∃ n : ℕ, ¬ l ∣ n ∧ ∀ v ∈ Λ, n • v ∈ stdLat (cmL a b d ha hd lam hlam) m := by
  classical
  have hn := theta_norm hok.1
  have hall' : ∀ j, ∃ N : ℕ, ¬ l ∣ N ∧
      N • (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d)) : m → ℂ) ∈ Λ := hall
  choose N hNl hNmem using hall'
  set Q : ℤ := a * x ^ 2 + b * x * y + c * y ^ 2 with hQdef
  refine ⟨Q.natAbs * Q.natAbs * ∏ j, N j, ?_, ?_⟩
  · intro hdvd
    rcases (Nat.Prime.dvd_mul hl).mp hdvd with h | h
    · rcases (Nat.Prime.dvd_mul hl).mp h with h' | h' <;> exact hQ (Int.natCast_dvd.mpr h')
    · obtain ⟨j, _, hj⟩ := (Prime.dvd_finset_prod_iff hl.prime _).mp h
      exact hNl j hj
  · intro v hv
    have hvd : v ∈ dualLat (stdH (cmL a b d ha hd lam hlam) m) Λ := by
      rw [hsd]
      exact hv
    rw [mem_dualLat_iff] at hvd
    rw [mem_stdLat_iff]
    intro i
    have e1 := hvd _ (hNmem i)
    have e2 := hvd _ (hθ _ (hNmem i))
    have hsm : cmTheta b d • (N i • Pi.single i (lam * ((x * a : ℂ) + y * cmTheta b d)) : m → ℂ) =
        N i • Pi.single i (cmTheta b d * (lam * ((x * a : ℂ) + y * cmTheta b d))) := by
      ext k
      by_cases hk : k = i
      · subst hk
        simp [nsmul_eq_mul]
        ring
      · simp [hk]
    rw [altE_single] at e1
    rw [hsm, altE_single] at e2
    have hm := coord_mem hn x y (N i) (v i) e1 e2
    have hmem : ((N i : ℤ) * Q) • v i ∈ (cmL a b d ha hd lam hlam).lattice := by
      rw [zsmul_eq_mul]
      exact_mod_cast hm
    have hnZ : ((Q.natAbs * Q.natAbs * ∏ j, N j : ℕ) : ℤ) =
        (Q * ∏ j ∈ Finset.univ.erase i, (N j : ℤ)) * ((N i : ℤ) * Q) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      push_cast
      rw [abs_mul_abs_self]
      ring
    rw [Pi.smul_apply, ← natCast_zsmul, hnZ, mul_smul]
    exact Submodule.smul_mem _ _ hmem

end PI.UnitaryGroupMassFormula.UnimodLocStd

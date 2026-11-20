import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.NsmulRelIdxMem

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnitDetRoot

open PI

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Conclude with `sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => h _ _)`.
-/
lemma det_mem_of_entries {m : Type} [Fintype m] [DecidableEq m] {S : IntermediateField ℚ ℂ}
    (U : Matrix m m ℂ) (h : ∀ i j, U i j ∈ S) : U.det ∈ S := by
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => h _ _)

/- English proof (translation)
The claim follows from `IntermediateField.mem_adjoin_simple_self ℚ (UnitDetRootDefs.cmTheta b d)`.
-/
lemma theta_mem (b : ℤ) (d : ℕ) : UnitDetRootDefs.cmTheta b d ∈ KF b d :=
    IntermediateField.mem_adjoin_simple_self ℚ (UnitDetRootDefs.cmTheta b d)

/- English proof (translation)
Rewrite using `[UnitDetRootDefs.stdLat, AddSubgroup.mem_pi]`. Introduce `i _`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[Pi.single_eq_same]`.

Conclude with `(UnitDetRootDefs.cmL a b d ha hd lam hlam).ω₁_mem_lattice`. Rewrite using `[Pi.single_eq_of_ne h]`. Conclude with `zero_mem _`.
-/
lemma single_mem_stdLat {a : ℕ} {b : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
    {m : Type} [DecidableEq m] (j : m) :
    Pi.single j (lam * a) ∈ UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m := by
  rw [UnitDetRootDefs.stdLat, AddSubgroup.mem_pi]
  intro i _
  by_cases h : i = j
  · subst h
    rw [Pi.single_eq_same]
    exact (UnitDetRootDefs.cmL a b d ha hd lam hlam).ω₁_mem_lattice
  · rw [Pi.single_eq_of_ne h]
    exact zero_mem _

/- English proof (translation)
Establish `he : Pi.single j (lam * a) ∈ UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m` using `single_mem_stdLat j`. Take `⟨n1, hn1, -, h1⟩` from `AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero hH.2.2.2.2 he`. Establish `h2 : (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (n1 • Pi.single j (lam * a)) ∈ UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa` using `AddSubgroup.mem_map_of_mem _ h1.1`. Take `⟨n2, hn2, -, h3⟩` from `AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero hA.2.1 h2`. Establish `h4` using `(AddSubgroup.mem_inf.mp h3).1`.

Rewrite `h4` using `[UnitDetRootDefs.stdLat, AddSubgroup.mem_pi]`. Establish `h5` using `h4 i (Set.mem_univ _)`. Rewrite `h5` using `[Submodule.mem_toAddSubgroup, PeriodPair.mem_lattice]`. Take `⟨p, q, hpq⟩` from `h5`. Establish `hs : Pi.single j (lam * (a : ℂ)) = (lam * (a : ℂ)) • Pi.single j (1 : ℂ)`.

Use extensionality with `k`. Simplify using `only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite `hpq` using `[hs, map_nsmul, map_smul, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]`. Express the relevant statement in the definitionally equal form `(p : ℂ) * (lam * a) + q * (lam * UnitDetRootDefs.cmTheta b d) = _ at hpq`.

Establish `ha0 : (a : ℂ) ≠ 0` using `by exact_mod_cast ha.ne'`. Establish `hN : (n2 : ℂ) * n1 * a ≠ 0` using `mul_ne_zero (mul_ne_zero (by exact_mod_cast hn2.ne') (by exact_mod_cast hn1.ne')) ha0`. Establish `hM : LinearMap.toMatrix' (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) i j = ((p : ℂ) * a + q * UnitDetRootDefs.cmTheta b d) / ((n2 : ℂ) * n1 * a)`. Rewrite using `[LinearMap.toMatrix'_apply, eq_div_iff hN]`. Apply `mul_left_cancel₀ hlam` to reduce the goal to its premises.

Simplify using `only [LinearEquiv.coe_coe] at hpq ⊢`. Take the linear combination `-hpq`. Rewrite using `[hM]`. Conclude with `div_mem (add_mem (mul_mem (intCast_mem _ _) (natCast_mem _ _)) (mul_mem (intCast_mem _ _) (theta_mem b d))) (mul_mem (mul_mem (natCast_mem _ _) (natCast_mem _ _)) (natCast_mem _ _))`.
-/
lemma entries_mem {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
    {m : Type} [Fintype m] [DecidableEq m] {Λa : AddSubgroup (m → ℂ)}
    (hH : Hyp a b c d ha hd lam hlam m Λa) {δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)} (hA : admitted a b d ha hd lam hlam m Λa δ)
    (i j : m) : LinearMap.toMatrix' (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) i j ∈ KF b d := by
  have he : Pi.single j (lam * a) ∈ UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m :=
    single_mem_stdLat j
  obtain ⟨n1, hn1, -, h1⟩ := AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero hH.2.2.2.2 he
  have h2 : (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (n1 • Pi.single j (lam * a)) ∈
      UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa :=
    AddSubgroup.mem_map_of_mem _ h1.1
  obtain ⟨n2, hn2, -, h3⟩ := AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero hA.2.1 h2
  have h4 := (AddSubgroup.mem_inf.mp h3).1
  rw [UnitDetRootDefs.stdLat, AddSubgroup.mem_pi] at h4
  have h5 := h4 i (Set.mem_univ _)
  rw [Submodule.mem_toAddSubgroup, PeriodPair.mem_lattice] at h5
  obtain ⟨p, q, hpq⟩ := h5
  have hs : Pi.single j (lam * (a : ℂ)) = (lam * (a : ℂ)) • Pi.single j (1 : ℂ) := by
    ext k
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hs, map_nsmul, map_smul, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
    nsmul_eq_mul, nsmul_eq_mul] at hpq
  change (p : ℂ) * (lam * a) + q * (lam * UnitDetRootDefs.cmTheta b d) = _ at hpq
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hN : (n2 : ℂ) * n1 * a ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by exact_mod_cast hn2.ne') (by exact_mod_cast hn1.ne')) ha0
  have hM : LinearMap.toMatrix' (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) i j =
      ((p : ℂ) * a + q * UnitDetRootDefs.cmTheta b d) / ((n2 : ℂ) * n1 * a) := by
    rw [LinearMap.toMatrix'_apply, eq_div_iff hN]
    apply mul_left_cancel₀ hlam
    simp only [LinearEquiv.coe_coe] at hpq ⊢
    linear_combination -hpq
  rw [hM]
  exact div_mem (add_mem (mul_mem (intCast_mem _ _) (natCast_mem _ _))
    (mul_mem (intCast_mem _ _) (theta_mem b d)))
    (mul_mem (mul_mem (natCast_mem _ _) (natCast_mem _ _)) (natCast_mem _ _))

/- English proof (translation)
Simplify using `only [UnitDetRootDefs.stdH, UnitDetRootDefs.matH, LinearMap.mk₂'ₛₗ_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[if_pos rfl]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `j _ hji`. Rewrite using `[if_neg (Ne.symm hji)]`. Expand and normalize the polynomial expressions, which then agree. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
private lemma stdH_apply_lemma (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (z w : m → ℂ) :
    UnitDetRootDefs.stdH L m z w = ((UnitDetRootDefs.area L : ℝ) : ℂ)⁻¹ * ∑ i, z i * conj (w i) := by
  simp only [UnitDetRootDefs.stdH, UnitDetRootDefs.matH, LinearMap.mk₂'ₛₗ_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
    ring
  · intro j _ hji
    rw [if_neg (Ne.symm hji)]
    ring
  · intro h
    exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Establish `hA0 : ((UnitDetRootDefs.area (UnitDetRootDefs.cmL a b d ha hd lam hlam) : ℝ) : ℂ) ≠ 0`. Rewrite using `[Complex.ofReal_ne_zero, UnitDetRootDefs.area, abs_ne_zero]`. Express the relevant statement in the definitionally equal form `(conj (lam * (a : ℂ)) * (lam * UnitDetRootDefs.cmTheta b d)).im ≠ 0`. Establish `e : conj (lam * (a : ℂ)) * (lam * UnitDetRootDefs.cmTheta b d) = ((Complex.normSq lam * a : ℝ) : ℂ) * UnitDetRootDefs.cmTheta b d`. Rewrite using `[map_mul, Complex.conj_natCast]`.

Use `push_cast`. Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Complex.im_ofReal_mul]`. Establish `hθ : (UnitDetRootDefs.cmTheta b d).im = Real.sqrt d / 2`.

Simplify using `[UnitDetRootDefs.cmTheta]`. Rewrite using `[hθ]`. Establish `h1 : 0 < Complex.normSq lam` using `Complex.normSq_pos.mpr hlam`. Establish `h2 : (0 : ℝ) < a` using `by exact_mod_cast ha`. Establish `h3 : 0 < Real.sqrt d` using `Real.sqrt_pos.mpr (by exact_mod_cast hd)`.

Conclude with `(mul_pos (mul_pos h1 h2) (by positivity)).ne'`. Establish `hU : (LinearMap.toMatrix' (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))).transpose * (LinearMap.toMatrix' (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))).map (starRingEnd ℂ) = 1`. Use extensionality with `k l`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.transpose_apply, Matrix.map_apply, LinearMap.toMatrix'_apply]`.

Establish `h` using `hiso (Pi.single k 1) (Pi.single l 1)`. Rewrite `h` using `[stdH_apply_lemma, stdH_apply_lemma]`. Rewrite using `[mul_left_cancel₀ (inv_ne_zero hA0) h]`. Rewrite using `[Finset.sum_eq_single k (fun i _ hik => by rw [Pi.single_eq_of_ne hik, zero_mul]) (fun hk => absurd (Finset.mem_univ k) hk), Pi.single_eq_same, one_mul, Pi.single_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hd'` using `congrArg Matrix.det hU`. Rewrite `hd'` using `[Matrix.det_mul, Matrix.det_transpose, Matrix.det_one]`. Rewrite using `[← LinearMap.det_toMatrix', RingHom.map_det, RingHom.mapMatrix_apply]`. Conclude with `hd'`.
-/
lemma unitary_det {a : ℕ} {b : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
    {m : Type} [Fintype m] [DecidableEq m] {δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)}
    (hiso : UnitDetRootDefs.IsIsom (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m)
      (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))) :
    LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) * conj (LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))) = 1 := by
  have hA0 : ((UnitDetRootDefs.area (UnitDetRootDefs.cmL a b d ha hd lam hlam) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, UnitDetRootDefs.area, abs_ne_zero]
    change (conj (lam * (a : ℂ)) * (lam * UnitDetRootDefs.cmTheta b d)).im ≠ 0
    have e : conj (lam * (a : ℂ)) * (lam * UnitDetRootDefs.cmTheta b d) =
        ((Complex.normSq lam * a : ℝ) : ℂ) * UnitDetRootDefs.cmTheta b d := by
      rw [map_mul, Complex.conj_natCast]
      push_cast
      rw [Complex.normSq_eq_conj_mul_self]
      ring
    rw [e, Complex.im_ofReal_mul]
    have hθ : (UnitDetRootDefs.cmTheta b d).im = Real.sqrt d / 2 := by
      simp [UnitDetRootDefs.cmTheta]
    rw [hθ]
    have h1 : 0 < Complex.normSq lam := Complex.normSq_pos.mpr hlam
    have h2 : (0 : ℝ) < a := by exact_mod_cast ha
    have h3 : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    exact (mul_pos (mul_pos h1 h2) (by positivity)).ne'
  have hU : (LinearMap.toMatrix' (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))).transpose *
      (LinearMap.toMatrix' (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))).map (starRingEnd ℂ) = 1 := by
    ext k l
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, Matrix.map_apply, LinearMap.toMatrix'_apply]
    have h := hiso (Pi.single k 1) (Pi.single l 1)
    rw [stdH_apply_lemma, stdH_apply_lemma] at h
    rw [mul_left_cancel₀ (inv_ne_zero hA0) h]
    rw [Finset.sum_eq_single k (fun i _ hik => by rw [Pi.single_eq_of_ne hik, zero_mul])
      (fun hk => absurd (Finset.mem_univ k) hk), Pi.single_eq_same, one_mul, Pi.single_apply,
      Matrix.one_apply]
    split_ifs <;> simp
  have hd' := congrArg Matrix.det hU
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd'
  rw [← LinearMap.det_toMatrix', RingHom.map_det, RingHom.mapMatrix_apply]
  exact hd'

/- English proof (translation)
Introduce `a b c d ha hd lam hlam m _ _ Λa hH δ hA`. Use `⟨?_, unitary_det hA.1⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.det_toMatrix']`. Conclude with `det_mem_of_entries _ (entries_mem hH hA)`.
-/
theorem detInK : DetInK := by
  intro a b c d ha hd lam hlam m _ _ Λa hH δ hA
  refine ⟨?_, unitary_det hA.1⟩
  rw [← LinearMap.det_toMatrix']
  exact det_mem_of_entries _ (entries_mem hH hA)

end PI.UnitaryGroupMassFormula.UnitDetRoot

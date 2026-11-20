import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.OneVecBinaryMassOf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteFieldQuadraticFormPointCount
open MeasureTheory Matrix ComplexConjugate

noncomputable section

namespace PositivityTheory.PfSWUS.HMass.SC

open GlobalTheory.CompanionTheory.SW.QuadricCount

variable {k : Type} [Field k] [Fintype k] [DecidableEq k]

/- English proof (translation)
Establish `h1 : ∑ y : k, ψ (a * y ^ 2) = ∑ u : k, ((Finset.univ.filter fun y : k => y ^ 2 = u).card : ℂ) * ψ (a * u)`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (g := fun y : k => y ^ 2) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl (fun y hy => by rw [(Finset.mem_filter.1 hy).2]), Finset.sum_const, nsmul_eq_mul]`. Rewrite using `[h1]`.

Establish `h2 : ∀ u : k, ((Finset.univ.filter fun y : k => y ^ 2 = u).card : ℂ) = (quadraticChar k u : ℂ) + 1`. Introduce `u`. Use `quadraticChar_card_sqrts hF u` as an intermediate fact. Establish `e : ({x : k | x ^ 2 = u}.toFinset) = Finset.univ.filter fun y : k => y ^ 2 = u` using `by ext; simp`. Rewrite `this` using `[e]`.

Conclude with `this` after adjusting the coercions. Repeatedly rewrite using `[h2, add_mul, one_mul, Finset.sum_add_distrib]`. Establish `h3 : ∑ u : k, ψ (a * u) = 0`. Establish `hp` using `AddChar.IsPrimitive.of_ne_one hψ`. Use `AddChar.sum_mulShift a hp` as an intermediate fact.

Simplify `this` using `[ha, mul_comm]`. Rewrite using `[h3, add_zero]`.
-/
theorem sum_sq_eq (hF : ringChar k ≠ 2) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (a : k) (ha : a ≠ 0) :
    ∑ y : k, ψ (a * y ^ 2) = ∑ u : k, (quadraticChar k u : ℂ) * ψ (a * u) := by
  have h1 : ∑ y : k, ψ (a * y ^ 2) =
      ∑ u : k, ((Finset.univ.filter fun y : k => y ^ 2 = u).card : ℂ) * ψ (a * u) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun y : k => y ^ 2) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_congr rfl (fun y hy => by rw [(Finset.mem_filter.1 hy).2]), Finset.sum_const,
      nsmul_eq_mul]
  rw [h1]
  have h2 : ∀ u : k, ((Finset.univ.filter fun y : k => y ^ 2 = u).card : ℂ) =
      (quadraticChar k u : ℂ) + 1 := by
    intro u
    have := quadraticChar_card_sqrts hF u
    have e : ({x : k | x ^ 2 = u}.toFinset) = Finset.univ.filter fun y : k => y ^ 2 = u := by
      ext; simp
    rw [e] at this
    exact_mod_cast this
  simp_rw [h2, add_mul, one_mul, Finset.sum_add_distrib]
  have h3 : ∑ u : k, ψ (a * u) = 0 := by
    have hp := AddChar.IsPrimitive.of_ne_one hψ
    have := AddChar.sum_mulShift a hp
    simpa [ha, mul_comm] using this
  rw [h3, add_zero]

/- English proof (translation)
Rewrite using `[sum_sq_eq hF ψ hψ (t * a) (mul_ne_zero ht ha), sum_sq_eq hF ψ hψ a ha, Finset.mul_sum]`. Establish `hsq : (quadraticChar k t : ℂ) * quadraticChar k t = 1`. Use `quadraticChar_sq_one ht` as an intermediate fact. Rewrite `this` using `[sq]`. Conclude with `this` after adjusting the coercions.

Use `Fintype.sum_equiv (Equiv.mulLeft₀ t ht) _ _ (fun u => ?_)` and prove the remaining obligations. Use `show (quadraticChar k u : ℂ) * ψ (t * a * u) = (quadraticChar k t : ℂ) * ((quadraticChar k (t * u) : ℂ) * ψ (a * (t * u)))`. Establish `hm : quadraticChar k (t * u) = quadraticChar k t * quadraticChar k u` using `map_mul _ _ _`. Rewrite using `[show a * (t * u) = t * a * u by ring, hm]`. Use `push_cast`.

Take the linear combination `(-(quadraticChar k u : ℂ) * ψ (t * a * u)) * hsq`.
-/
theorem sum_sq_scale (hF : ringChar k ≠ 2) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (a t : k) (ha : a ≠ 0)
    (ht : t ≠ 0) :
    ∑ y : k, ψ (t * a * y ^ 2) = (quadraticChar k t : ℂ) * ∑ y : k, ψ (a * y ^ 2) := by
  rw [sum_sq_eq hF ψ hψ (t * a) (mul_ne_zero ht ha), sum_sq_eq hF ψ hψ a ha, Finset.mul_sum]
  have hsq : (quadraticChar k t : ℂ) * quadraticChar k t = 1 := by
    have := quadraticChar_sq_one ht
    rw [sq] at this
    exact_mod_cast this
  refine Fintype.sum_equiv (Equiv.mulLeft₀ t ht) _ _ (fun u => ?_)
  show (quadraticChar k u : ℂ) * ψ (t * a * u) =
    (quadraticChar k t : ℂ) * ((quadraticChar k (t * u) : ℂ) * ψ (a * (t * u)))
  have hm : quadraticChar k (t * u) = quadraticChar k t * quadraticChar k u := map_mul _ _ _
  rw [show a * (t * u) = t * a * u by ring, hm]
  push_cast
  linear_combination (-(quadraticChar k u : ℂ) * ψ (t * a * u)) * hsq

/- English proof (translation)
The claim follows from `Finset.induction_on s (by simp) (fun a s ha ih => by rw [Finset.sum_insert ha, AddChar.map_add_eq_mul, ih, Finset.prod_insert ha])`.
-/
theorem addChar_sum (ψ : AddChar k ℂ) {α : Type} [DecidableEq α] (s : Finset α) (f : α → k) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) :=
  Finset.induction_on s (by simp) (fun a s ha ih => by
    rw [Finset.sum_insert ha, AddChar.map_add_eq_mul, ih, Finset.prod_insert ha])

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Establish `h2 : (2 : k) ≠ 0` using `Ring.two_ne_zero hF`. Use `letI : Invertible (2 : k) := invertibleOfNonzero h2`. Take `⟨β, hβ⟩ : ∃ β : LinearMap.BilinForm k (ι → k), β = Matrix.toBilin' B` from `⟨_, rfl⟩`. Establish `hβapp : ∀ x y, β x y = x ⬝ᵥ (B *ᵥ y)` using `fun x y => by rw [hβ]; exact Matrix.toBilin'_apply' B x y`. Establish `hsymm : β.IsSymm`.

Use `⟨fun x y => ?_⟩` and prove the remaining obligations. Simplify using `only [RingHom.id_apply, hβapp]`. Rewrite using `[Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hB.eq, dotProduct_comm]`. Take `⟨v, hv⟩` from `LinearMap.BilinForm.exists_orthogonal_basis (LinearMap.BilinForm.isSymm_iff.1 hsymm)`. Establish `hn2 : Module.finrank k (ι → k) = 2 * M` using `by rw [Module.finrank_fintype_fun_eq_card, hM]`.

Take `⟨w, hw⟩ : ∃ w : Fin (Module.finrank k (ι → k)) → k, w = fun i => β (v i) (v i)` from `⟨_, rfl⟩`. Establish `hdiag : ∀ c : Fin (Module.finrank k (ι → k)) → k, β (v.equivFun.symm c) (v.equivFun.symm c) = ∑ i, w i * c i ^ 2`. Introduce `c`. Rewrite using `[Module.Basis.equivFun_symm_apply]`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single i]`. Simplify using `only [hw]`. Expand and normalize the polynomial expressions, which then agree. Introduce `j _ hji`.

Establish `: β (v j) (v i) = 0` using `hv hji`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.

Establish `hw0 : ∀ i, w i ≠ 0`. Introduce `i hi`. Apply `v.ne_zero i` to reduce the goal to its premises. Establish `hall : ∀ y, β (v i) y = 0`. Introduce `y`.

Establish `hy` using `v.sum_equivFun y`. Rewrite using `[← hy]`. Simplify using `only [map_sum, map_smul, smul_eq_mul]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j = i`.

Substitute `hj; rw [show β (v j) (v j) = w j by rw [hw], hi, mul_zero]` using the available equality. Rewrite using `[show β (v i) (v j) = 0 from hv (Ne.symm hj), mul_zero]`. Establish `hB0 : B *ᵥ v i = 0`. Establish `h' : ∀ y, (B *ᵥ v i) ⬝ᵥ y = 0`. Introduce `y`.

Use `hall y` as an intermediate fact. Rewrite `this` using `[hβapp, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hB.eq]`. Rewrite `this`, the goal using `[dotProduct_comm]`. Simplify `this` using `[dotProduct_comm]`. Use function extensionality and compare the values at `j`.

Use `h' (Pi.single j 1)` as an intermediate fact. Simplify using `using this`. Conclude with `Matrix.eq_zero_of_mulVec_eq_zero hdet hB0`. Establish `hQ : ∀ (s : k) (c : Fin (Module.finrank k (ι → k)) → k), s * quadForm B (v.equivFun.symm c) = ∑ i, s * (2 : k)⁻¹ * w i * c i ^ 2`. Introduce `s c`.

Unfold `quadForm`. Rewrite using `[← hβapp, hdiag c, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hS : ∀ s : k, ∑ x, ψ (s * quadForm B x) = ∏ i, ∑ y : k, ψ (s * (2 : k)⁻¹ * w i * y ^ 2)`.

Introduce `s`. Rewrite using `[← Fintype.sum_equiv v.equivFun.symm (fun c => ψ (s * quadForm B (v.equivFun.symm c))) (fun x => ψ (s * quadForm B x)) (fun _ => rfl)]`. Repeatedly rewrite using `[hQ s, addChar_sum]`. Rewrite using `[Fintype.prod_sum]`. Rewrite using `[hS t, hS 1]`.

Establish `hfac : ∀ i, ∑ y : k, ψ (t * (2 : k)⁻¹ * w i * y ^ 2) = (quadraticChar k t : ℂ) * ∑ y : k, ψ (1 * (2 : k)⁻¹ * w i * y ^ 2)`. Introduce `i`. Use `sum_sq_scale hF ψ hψ ((2 : k)⁻¹ * w i) t (mul_ne_zero (inv_ne_zero h2) (hw0 i)) ht` as an intermediate fact. Simplify using `only [one_mul, mul_assoc] at this ⊢`. Conclude with `this`.

Establish `hsq : (quadraticChar k t : ℂ) ^ 2 = 1` using `by exact_mod_cast quadraticChar_sq_one ht`. Establish `hpow : (quadraticChar k t : ℂ) ^ Module.finrank k (ι → k) = 1` using `by rw [hn2, pow_mul, hsq, one_pow]`. Rewrite using `[Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hpow, one_mul]`.
-/
theorem gauss_const (hF : ringChar k ≠ 2) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) {M : ℕ}
    (hM : Fintype.card ι = 2 * M) (B : Matrix ι ι k) (hB : B.IsSymm) (hdet : B.det ≠ 0) (t : k)
    (ht : t ≠ 0) :
    ∑ x, ψ (t * quadForm B x) = ∑ x, ψ (1 * quadForm B x) := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hF
  letI : Invertible (2 : k) := invertibleOfNonzero h2
  obtain ⟨β, hβ⟩ : ∃ β : LinearMap.BilinForm k (ι → k), β = Matrix.toBilin' B := ⟨_, rfl⟩
  have hβapp : ∀ x y, β x y = x ⬝ᵥ (B *ᵥ y) := fun x y => by rw [hβ]; exact Matrix.toBilin'_apply' B x y
  have hsymm : β.IsSymm := by
    refine ⟨fun x y => ?_⟩
    simp only [RingHom.id_apply, hβapp]
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hB.eq, dotProduct_comm]
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (LinearMap.BilinForm.isSymm_iff.1 hsymm)
  have hn2 : Module.finrank k (ι → k) = 2 * M := by rw [Module.finrank_fintype_fun_eq_card, hM]
  obtain ⟨w, hw⟩ : ∃ w : Fin (Module.finrank k (ι → k)) → k, w = fun i => β (v i) (v i) := ⟨_, rfl⟩
  have hdiag : ∀ c : Fin (Module.finrank k (ι → k)) → k, β (v.equivFun.symm c) (v.equivFun.symm c) = ∑ i, w i * c i ^ 2 := by
    intro c
    rw [Module.Basis.equivFun_symm_apply]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp only [hw]; ring
    · intro j _ hji
      have : β (v j) (v i) = 0 := hv hji
      rw [this]; ring
    · intro h; exact absurd (Finset.mem_univ i) h
  have hw0 : ∀ i, w i ≠ 0 := by
    intro i hi
    apply v.ne_zero i
    have hall : ∀ y, β (v i) y = 0 := by
      intro y
      have hy := v.sum_equivFun y
      rw [← hy]
      simp only [map_sum, map_smul, smul_eq_mul]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : j = i
      · subst hj; rw [show β (v j) (v j) = w j by rw [hw], hi, mul_zero]
      · rw [show β (v i) (v j) = 0 from hv (Ne.symm hj), mul_zero]
    have hB0 : B *ᵥ v i = 0 := by
      have h' : ∀ y, (B *ᵥ v i) ⬝ᵥ y = 0 := by
        intro y
        have := hall y
        rw [hβapp, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hB.eq] at this
        rw [dotProduct_comm] at this ⊢
        simpa [dotProduct_comm] using this
      funext j
      have := h' (Pi.single j 1)
      simpa using this
    exact Matrix.eq_zero_of_mulVec_eq_zero hdet hB0
  have hQ : ∀ (s : k) (c : Fin (Module.finrank k (ι → k)) → k), s * quadForm B (v.equivFun.symm c) = ∑ i, s * (2 : k)⁻¹ * w i * c i ^ 2 := by
    intro s c
    unfold quadForm
    rw [← hβapp, hdiag c, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hS : ∀ s : k, ∑ x, ψ (s * quadForm B x) = ∏ i, ∑ y : k, ψ (s * (2 : k)⁻¹ * w i * y ^ 2) := by
    intro s
    rw [← Fintype.sum_equiv v.equivFun.symm (fun c => ψ (s * quadForm B (v.equivFun.symm c)))
      (fun x => ψ (s * quadForm B x)) (fun _ => rfl)]
    simp_rw [hQ s, addChar_sum]
    rw [Fintype.prod_sum]
  rw [hS t, hS 1]
  have hfac : ∀ i, ∑ y : k, ψ (t * (2 : k)⁻¹ * w i * y ^ 2) =
      (quadraticChar k t : ℂ) * ∑ y : k, ψ (1 * (2 : k)⁻¹ * w i * y ^ 2) := by
    intro i
    have := sum_sq_scale hF ψ hψ ((2 : k)⁻¹ * w i) t (mul_ne_zero (inv_ne_zero h2) (hw0 i)) ht
    simp only [one_mul, mul_assoc] at this ⊢
    exact this
  have hsq : (quadraticChar k t : ℂ) ^ 2 = 1 := by exact_mod_cast quadraticChar_sq_one ht
  have hpow : (quadraticChar k t : ℂ) ^ Module.finrank k (ι → k) = 1 := by rw [hn2, pow_mul, hsq, one_pow]
  rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, hpow, one_mul]

/- English proof (translation)
The claim follows from `|(Nat.card {x : ι → k // (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) = s} : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)| ≤ (Fintype.card k : ℝ) ^ (M - 1) := by have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hF obtain ⟨ψ, hψ⟩ : ∃ ψ : AddChar k ℂ, ψ 1 ≠ 1 := AddChar.exists_apply_ne_zero.mpr one_ne_zero hav …`.
-/
theorem sharp (hF : ringChar k ≠ 2) (M : ℕ) (hM : Fintype.card ι = 2 * M) (hM1 : 1 ≤ M)
    (B : Matrix ι ι k) (hB : B.IsSymm) (hdet : B.det ≠ 0) (s : k) (hs : s ≠ 0) :
    |(Nat.card {x : ι → k // (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) = s} : ℝ) -
      (Fintype.card k : ℝ) ^ (2 * M - 1)| ≤ (Fintype.card k : ℝ) ^ (M - 1) := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hF
  obtain ⟨ψ, hψ⟩ : ∃ ψ : AddChar k ℂ, ψ 1 ≠ 1 := AddChar.exists_apply_ne_zero.mpr one_ne_zero
  have hψ1 : ψ ≠ 1 := fun h => hψ (by simp [h])
  have hq : (0 : ℝ) < (Fintype.card k : ℝ) := by exact_mod_cast Fintype.card_pos
  set N : ℕ := Nat.card {x : ι → k // quadForm B x = s} with hNdef
  have hcount := count_mul_card ψ hψ1 B s
  rw [← hNdef, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : k))] at hcount
  have hzero : ψ (-((0 : k) * s)) * ∑ x, ψ ((0 : k) * quadForm B x) =
      (Fintype.card k : ℂ) ^ (2 * M) := by
    simp [hM]
  rw [hzero] at hcount
  set S1 : ℂ := ∑ x, ψ (1 * quadForm B x) with hS1
  have hrest : ∑ t ∈ Finset.univ.erase (0 : k), ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x) = -S1 := by
    rw [Finset.sum_congr rfl (fun t ht => by
      rw [gauss_const hF ψ hψ1 hM B hB hdet t (Finset.ne_of_mem_erase ht)])]
    rw [← Finset.sum_mul]
    have hall : ∑ t : k, ψ (-(t * s)) = 0 := by
      have hp := AddChar.IsPrimitive.of_ne_one hψ1
      have := AddChar.sum_mulShift (-s) hp
      simp only [neg_eq_zero, hs, if_false] at this
      simpa [mul_neg] using this
    have hsplit : ψ (-((0 : k) * s)) + ∑ t ∈ Finset.univ.erase (0 : k), ψ (-(t * s)) =
        ∑ t, ψ (-(t * s)) := Finset.add_sum_erase Finset.univ (fun t : k => ψ (-(t * s))) (Finset.mem_univ (0 : k))
    have h0 : ψ (-((0 : k) * s)) = 1 := by simp
    rw [h0, hall] at hsplit
    have : ∑ t ∈ Finset.univ.erase (0 : k), ψ (-(t * s)) = -1 := by
      linear_combination hsplit
    rw [this]
    ring
  rw [hrest] at hcount
  have hnorm : ‖S1‖ = (Fintype.card k : ℝ) ^ M := by
    have := norm_gauss ψ hψ1 h2 hB hdet hM (one_ne_zero)
    simpa [hS1] using this
  have hreal : (((N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M) : ℝ) : ℂ) = -S1 := by
    push_cast
    rw [hcount]
    ring
  have habs : |(N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M)| =
      (Fintype.card k : ℝ) ^ M := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hreal, norm_neg, hnorm]
  have hpow : (Fintype.card k : ℝ) ^ (2 * M) =
      (Fintype.card k : ℝ) ^ (2 * M - 1) * (Fintype.card k : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  have hpowM : (Fintype.card k : ℝ) ^ M = (Fintype.card k : ℝ) ^ (M - 1) * (Fintype.card k : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  have hfac : (N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M) =
      ((N : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)) * (Fintype.card k : ℝ) := by
    rw [hpow]
    ring
  rw [hfac, abs_mul, abs_of_pos hq, hpowM] at habs
  exact le_of_eq (mul_right_cancel₀ hq.ne' habs)

end PositivityTheory.PfSWUS.HMass.SC

namespace PositivityTheory.PfSWUS.HMass

/- English proof (translation)
Introduce `k _ _ hF ι _ _ M hM hM1 B hB hd s hs` and use `by classical exact SC.sharp hF M hM hM1 B hB hd s hs`.
-/
theorem sharpCount : SharpCount :=
  fun k _ _ hF ι _ _ M hM hM1 B hB hd s hs => by
    classical
    exact SC.sharp hF M hM hM1 B hB hd s hs

end PositivityTheory.PfSWUS.HMass

import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PSepFac

noncomputable section

open Polynomial

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac

section Comm

variable {B : Type} [CommRing B] [Algebra ℂ B]

/- English proof (translation)
Proceed by induction on `J using Finset.induction_on with`. Consider the case `empty => exact ⟨C e * P, by simp⟩`. Consider the case `insert β J hβ ih`. Take `⟨Rm, hRm⟩` from `ih fun α hα => h α (Finset.mem_insert_of_mem hα)`. Establish `hu : IsUnit (∏ α ∈ J, (algebraMap ℂ B β - algebraMap ℂ B α))`.

Establish `e0 : ∏ α ∈ J, (algebraMap ℂ B β - algebraMap ℂ B α) = algebraMap ℂ B (∏ α ∈ J, (β - α))`. Simplify using `[map_prod, map_sub]`. Rewrite using `[e0]`. Use `(IsUnit.mk0 _ ?_).map (algebraMap ℂ B)` and prove the remaining obligations. Conclude with `Finset.prod_ne_zero_iff.2 fun α hα => sub_ne_zero.2 fun h' => hβ (h' ▸ hα)`.

Establish `h0 : Rm.eval (algebraMap ℂ B β) = 0`. Establish `e1` using `congrArg (eval (algebraMap ℂ B β)) hRm`. Rewrite `e1` using `[eval_mul, eval_C, h β (Finset.mem_insert_self _ _), eval_mul, eval_prod]`. Simplify using `only [eval_sub, eval_X, eval_C] at e1`. Conclude with `hu.mul_right_eq_zero.1 e1.symm`.

Use `⟨Rm /ₘ (X - C (algebraMap ℂ B β)), ?_⟩` and prove the remaining obligations. Rewrite using `[hRm, Finset.prod_insert hβ]`. Use `conv_lhs => rw [← (mul_divByMonic_eq_iff_isRoot).2 h0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem factor_roots (e : B) (P : B[X]) (J : Finset ℂ) (h : ∀ α ∈ J, e * P.eval (algebraMap ℂ B α) = 0) :
    ∃ Rm : B[X], C e * P = (∏ α ∈ J, (X - C (algebraMap ℂ B α))) * Rm := by
  classical
  induction J using Finset.induction_on with
  | empty => exact ⟨C e * P, by simp⟩
  | insert β J hβ ih =>
    obtain ⟨Rm, hRm⟩ := ih fun α hα => h α (Finset.mem_insert_of_mem hα)
    have hu : IsUnit (∏ α ∈ J, (algebraMap ℂ B β - algebraMap ℂ B α)) := by
      have e0 : ∏ α ∈ J, (algebraMap ℂ B β - algebraMap ℂ B α) = algebraMap ℂ B (∏ α ∈ J, (β - α)) := by
        simp [map_prod, map_sub]
      rw [e0]
      refine (IsUnit.mk0 _ ?_).map (algebraMap ℂ B)
      exact Finset.prod_ne_zero_iff.2 fun α hα => sub_ne_zero.2 fun h' => hβ (h' ▸ hα)
    have h0 : Rm.eval (algebraMap ℂ B β) = 0 := by
      have e1 := congrArg (eval (algebraMap ℂ B β)) hRm
      rw [eval_mul, eval_C, h β (Finset.mem_insert_self _ _), eval_mul, eval_prod] at e1
      simp only [eval_sub, eval_X, eval_C] at e1
      exact hu.mul_right_eq_zero.1 e1.symm
    refine ⟨Rm /ₘ (X - C (algebraMap ℂ B β)), ?_⟩
    rw [hRm, Finset.prod_insert hβ]
    conv_lhs => rw [← (mul_divByMonic_eq_iff_isRoot).2 h0]
    ring

omit [Algebra ℂ B] in

/- English proof (translation)
Distinguish the cases in `hR : Rm = 0`. Establish `h0 : C e * P = 0` using `by rw [h, hR, mul_zero]`. Establish `he : e = 0`. Use `congrArg (fun F : B[X] => F.coeff P.natDegree) h0` as an intermediate fact. Simplify `this` using `[coeff_C_mul, hP.coeff_natDegree]`.

Conclude with `⟨Or.inr he, fun _ k => by simp [he]⟩`. Establish `hdeg : (Pi * Rm).natDegree = Pi.natDegree + Rm.natDegree` using `hPi.natDegree_mul' hR`. Establish `hle : (C e * P).natDegree ≤ P.natDegree` using `natDegree_C_mul_le e P`. Rewrite `hle` using `[h, hdeg]`. Use `⟨Or.inl (by omega), fun hm k => ?_⟩` and prove the remaining obligations.

Establish `hRC : Rm = C (Rm.coeff 0)` using `eq_C_of_natDegree_eq_zero (by omega)`. Establish `h2 : C e * P = Pi * C (Rm.coeff 0)`. Rewrite using `[h]`. Use `conv_lhs => rw [hRC]`. Establish `hb : e = Rm.coeff 0`.

Use `congrArg (fun F : B[X] => F.coeff P.natDegree) h2` as an intermediate fact. Simplify using `only [coeff_C_mul, coeff_mul_C, hP.coeff_natDegree, mul_one] at this`. Rewrite using `[this, ← hm, hPi.coeff_natDegree, one_mul]`. Use `congrArg (fun F : B[X] => F.coeff k) h2` as an intermediate fact. Simplify using `only [coeff_C_mul, coeff_mul_C] at this`.

Rewrite using `[this, ← hb]`.
-/
theorem factor_deg {e : B} {P Pi Rm : B[X]} (hP : P.Monic) (hPi : Pi.Monic) (h : C e * P = Pi * Rm) :
    (Pi.natDegree ≤ P.natDegree ∨ e = 0) ∧ (Pi.natDegree = P.natDegree → ∀ k, e * P.coeff k = Pi.coeff k * e) := by
  by_cases hR : Rm = 0
  · have h0 : C e * P = 0 := by rw [h, hR, mul_zero]
    have he : e = 0 := by
      have := congrArg (fun F : B[X] => F.coeff P.natDegree) h0
      simpa [coeff_C_mul, hP.coeff_natDegree] using this
    exact ⟨Or.inr he, fun _ k => by simp [he]⟩
  · have hdeg : (Pi * Rm).natDegree = Pi.natDegree + Rm.natDegree := hPi.natDegree_mul' hR
    have hle : (C e * P).natDegree ≤ P.natDegree := natDegree_C_mul_le e P
    rw [h, hdeg] at hle
    refine ⟨Or.inl (by omega), fun hm k => ?_⟩
    have hRC : Rm = C (Rm.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
    have h2 : C e * P = Pi * C (Rm.coeff 0) := by
      rw [h]
      conv_lhs => rw [hRC]
    have hb : e = Rm.coeff 0 := by
      have := congrArg (fun F : B[X] => F.coeff P.natDegree) h2
      simp only [coeff_C_mul, coeff_mul_C, hP.coeff_natDegree, mul_one] at this
      rw [this, ← hm, hPi.coeff_natDegree, one_mul]
    have := congrArg (fun F : B[X] => F.coeff k) h2
    simp only [coeff_C_mul, coeff_mul_C] at this
    rw [this, ← hb]

/- English proof (translation)
Break down `subsingleton_or_nontrivial B with hB | hB` into its components or cases. Conclude with `⟨∅, Subsingleton.elim _ _⟩`. Establish `hinj : Function.Injective (algebraMap ℂ B)` using `(algebraMap ℂ B).injective`. Establish `hp0 : p ≠ 0` using `hp.ne_zero`. Use `set R := p.roots.toFinset with hR`.

Establish `hdegPQ : P.natDegree + Q.natDegree = p.natDegree`. Rewrite using `[← hP.natDegree_mul hQ, hPQ, natDegree_map_eq_of_injective hinj]`. Establish `hcard : R.card = p.natDegree`. Rewrite using `[hR, Multiset.toFinset_card_of_nodup (nodup_roots hp)]`. Conclude with `IsAlgClosed.card_roots_eq_natDegree`.

Establish `hroot : ∀ α ∈ R, p.eval α = 0` using `fun α hα => by`. Rewrite `hα` using `[hR, Multiset.mem_toFinset, mem_roots hp0]`. Conclude with `hα`. Establish `hder : ∀ α ∈ R, p.derivative.eval α ≠ 0` using `fun α hα h0 => by`. Take `⟨u, v, huv⟩ : IsCoprime p (derivative p)` from `hp`.

Use `congrArg (eval α) huv` as an intermediate fact. Simplify using `[eval_add, eval_mul, hroot α hα, h0] at this`. Establish `hPQa : ∀ α ∈ R, P.eval (algebraMap ℂ B α) * Q.eval (algebraMap ℂ B α) = 0`. Introduce `α hα`. Rewrite using `[← eval_mul, hPQ, eval_map, eval₂_at_apply, hroot α hα, map_zero]`.

Establish `hDa : ∀ α ∈ R, (derivative P).eval (algebraMap ℂ B α) * Q.eval (algebraMap ℂ B α) + P.eval (algebraMap ℂ B α) * (derivative Q).eval (algebraMap ℂ B α) = algebraMap ℂ B (p.derivative.eval α)`. Introduce `α hα`. Rewrite using `[← eval_mul, ← eval_mul, ← eval_add, ← derivative_mul, hPQ, derivative_map, eval_map, eval₂_at_apply]`. Set `e : ℂ → B` to `fun α => P.eval (algebraMap ℂ B α) * (derivative Q).eval (algebraMap ℂ B α) * algebraMap ℂ B (p.derivative.eval α)⁻¹`. Establish `heQ : ∀ α ∈ R, e α * Q.eval (algebraMap ℂ B α) = 0`.

Introduce `α hα`. Take the linear combination `((derivative Q).eval (algebraMap ℂ B α) * algebraMap ℂ B (p.derivative.eval α)⁻¹) * hPQa α hα`. Establish `hfP : ∀ α ∈ R, (1 - e α) * P.eval (algebraMap ℂ B α) = 0`. Introduce `α hα`. Establish `hI : ((derivative P).eval (algebraMap ℂ B α) * Q.eval (algebraMap ℂ B α) + P.eval (algebraMap ℂ B α) * (derivative Q).eval (algebraMap ℂ B α)) * algebraMap ℂ B (p.derivative.eval α)⁻¹ = 1`.

Rewrite using `[hDa α hα, ← map_mul, mul_inv_cancel₀ (hder α hα), map_one]`. Take the linear combination `(-P.eval (algebraMap ℂ B α)) * hI + ((derivative P).eval (algebraMap ℂ B α) * algebraMap ℂ B (p.derivative.eval α)⁻¹) * hPQa α hα`. Set `E : Finset ℂ → B` to `fun I => (∏ α ∈ I, e α) * ∏ α ∈ R \ I, (1 - e α)`. Establish `hsum : ∑ I ∈ R.powerset, E I = 1`. Simplify using `only [E]`.

Rewrite using `[← Finset.prod_add]`. Simplify using the standard rewrite rules. Establish `hmonJ : ∀ J : Finset ℂ, (∏ α ∈ J, (X - C (algebraMap ℂ B α))).Monic` using `fun J => monic_prod_of_monic _ _ fun α _ => monic_X_sub_C _`. Establish `hdegJ : ∀ J : Finset ℂ, (∏ α ∈ J, (X - C (algebraMap ℂ B α))).natDegree = J.card`. Introduce `J`.

Rewrite using `[natDegree_prod_of_monic _ _ fun α _ => monic_X_sub_C _]`. Simplify using the standard rewrite rules. Establish `hmapJ : ∀ J : Finset ℂ, (∏ α ∈ J, (X - C (algebraMap ℂ B α))) = (∏ α ∈ J, (X - C α)).map (algebraMap ℂ B)`. Introduce `J`. Simplify using `[Polynomial.map_prod]`.

Use `isSS_of_decomp R.powerset E (fun I => (∏ α ∈ R \ I, (X - C α)).coeff k) hsum fun I hI => ?_` and prove the remaining obligations. Rewrite `hI` using `[Finset.mem_powerset]`. Distinguish the cases in `hE : E I = 0`. Rewrite using `[hE, mul_zero, smul_zero]`. Establish `hEQ : ∀ α ∈ I, E I * Q.eval (algebraMap ℂ B α) = 0`.

Introduce `α hα`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [E]`. Rewrite using `[← Finset.mul_prod_erase I e hα]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = 0 := by rw [heQ α (hI hα), zero_mul]`. Establish `hEP : ∀ α ∈ R \ I, E I * P.eval (algebraMap ℂ B α) = 0`. Introduce `α hα`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [E]`.

Rewrite using `[← Finset.mul_prod_erase (R \ I) (fun β => 1 - e β) hα]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = 0 := by rw [hfP α (Finset.mem_sdiff.1 hα).1, zero_mul]`. Take `⟨R₁, hR₁⟩` from `factor_roots (E I) P (R \ I) hEP`. Take `⟨R₂, hR₂⟩` from `factor_roots (E I) Q I hEQ`.

Take `⟨h1, h2⟩` from `factor_deg hP (hmonJ _) hR₁`. Take `⟨h3, -⟩` from `factor_deg hQ (hmonJ _) hR₂`. Rewrite `h1`, `h2`, `h3` using `[hdegJ]`. Establish `hsd` using `Finset.card_sdiff_add_card_eq_card hI`. Establish `heq : (R \ I).card = P.natDegree`.

Break down `h1 with h1 | h1` into its components or cases. Break down `h3 with h3 | h3` into its components or cases. Use linear arithmetic over natural numbers and integers. Conclude with `absurd h3 hE`. Conclude with `absurd h1 hE`.

Use `h2 heq k` as an intermediate fact. Rewrite `this` using `[hmapJ, coeff_map]`. Rewrite using `[mul_comm, this, Algebra.smul_def, mul_comm]`.
-/
theorem isSS_coeff (p : ℂ[X]) (hp : p.Separable) (P Q : B[X]) (hP : P.Monic) (hQ : Q.Monic)
    (hPQ : P * Q = p.map (algebraMap ℂ B)) (k : ℕ) : IsSS (P.coeff k) := by
  classical
  rcases subsingleton_or_nontrivial B with hB | hB
  · exact ⟨∅, Subsingleton.elim _ _⟩
  have hinj : Function.Injective (algebraMap ℂ B) := (algebraMap ℂ B).injective
  have hp0 : p ≠ 0 := hp.ne_zero
  set R := p.roots.toFinset with hR
  have hdegPQ : P.natDegree + Q.natDegree = p.natDegree := by
    rw [← hP.natDegree_mul hQ, hPQ, natDegree_map_eq_of_injective hinj]
  have hcard : R.card = p.natDegree := by
    rw [hR, Multiset.toFinset_card_of_nodup (nodup_roots hp)]
    exact IsAlgClosed.card_roots_eq_natDegree
  have hroot : ∀ α ∈ R, p.eval α = 0 := fun α hα => by
    rw [hR, Multiset.mem_toFinset, mem_roots hp0] at hα
    exact hα
  have hder : ∀ α ∈ R, p.derivative.eval α ≠ 0 := fun α hα h0 => by
    obtain ⟨u, v, huv⟩ : IsCoprime p (derivative p) := hp
    have := congrArg (eval α) huv
    simp [eval_add, eval_mul, hroot α hα, h0] at this
  have hPQa : ∀ α ∈ R, P.eval (algebraMap ℂ B α) * Q.eval (algebraMap ℂ B α) = 0 := by
    intro α hα
    rw [← eval_mul, hPQ, eval_map, eval₂_at_apply, hroot α hα, map_zero]
  have hDa : ∀ α ∈ R, (derivative P).eval (algebraMap ℂ B α) * Q.eval (algebraMap ℂ B α) +
      P.eval (algebraMap ℂ B α) * (derivative Q).eval (algebraMap ℂ B α) = algebraMap ℂ B (p.derivative.eval α) := by
    intro α hα
    rw [← eval_mul, ← eval_mul, ← eval_add, ← derivative_mul, hPQ, derivative_map, eval_map, eval₂_at_apply]
  let e : ℂ → B := fun α =>
    P.eval (algebraMap ℂ B α) * (derivative Q).eval (algebraMap ℂ B α) * algebraMap ℂ B (p.derivative.eval α)⁻¹
  have heQ : ∀ α ∈ R, e α * Q.eval (algebraMap ℂ B α) = 0 := by
    intro α hα
    linear_combination ((derivative Q).eval (algebraMap ℂ B α) * algebraMap ℂ B (p.derivative.eval α)⁻¹) * hPQa α hα
  have hfP : ∀ α ∈ R, (1 - e α) * P.eval (algebraMap ℂ B α) = 0 := by
    intro α hα
    have hI : ((derivative P).eval (algebraMap ℂ B α) * Q.eval (algebraMap ℂ B α) +
        P.eval (algebraMap ℂ B α) * (derivative Q).eval (algebraMap ℂ B α)) *
          algebraMap ℂ B (p.derivative.eval α)⁻¹ = 1 := by
      rw [hDa α hα, ← map_mul, mul_inv_cancel₀ (hder α hα), map_one]
    linear_combination (-P.eval (algebraMap ℂ B α)) * hI +
      ((derivative P).eval (algebraMap ℂ B α) * algebraMap ℂ B (p.derivative.eval α)⁻¹) * hPQa α hα
  let E : Finset ℂ → B := fun I => (∏ α ∈ I, e α) * ∏ α ∈ R \ I, (1 - e α)
  have hsum : ∑ I ∈ R.powerset, E I = 1 := by
    simp only [E]
    rw [← Finset.prod_add]
    simp
  have hmonJ : ∀ J : Finset ℂ, (∏ α ∈ J, (X - C (algebraMap ℂ B α))).Monic := fun J =>
    monic_prod_of_monic _ _ fun α _ => monic_X_sub_C _
  have hdegJ : ∀ J : Finset ℂ, (∏ α ∈ J, (X - C (algebraMap ℂ B α))).natDegree = J.card := by
    intro J
    rw [natDegree_prod_of_monic _ _ fun α _ => monic_X_sub_C _]
    simp
  have hmapJ : ∀ J : Finset ℂ, (∏ α ∈ J, (X - C (algebraMap ℂ B α))) = (∏ α ∈ J, (X - C α)).map (algebraMap ℂ B) := by
    intro J
    simp [Polynomial.map_prod]
  refine isSS_of_decomp R.powerset E (fun I => (∏ α ∈ R \ I, (X - C α)).coeff k) hsum fun I hI => ?_
  rw [Finset.mem_powerset] at hI
  by_cases hE : E I = 0
  · rw [hE, mul_zero, smul_zero]
  have hEQ : ∀ α ∈ I, E I * Q.eval (algebraMap ℂ B α) = 0 := by
    intro α hα
    calc E I * Q.eval (algebraMap ℂ B α) =
        (e α * Q.eval (algebraMap ℂ B α)) * ((∏ β ∈ I.erase α, e β) * ∏ β ∈ R \ I, (1 - e β)) := by
          simp only [E]
          rw [← Finset.mul_prod_erase I e hα]
          ring
      _ = 0 := by rw [heQ α (hI hα), zero_mul]
  have hEP : ∀ α ∈ R \ I, E I * P.eval (algebraMap ℂ B α) = 0 := by
    intro α hα
    calc E I * P.eval (algebraMap ℂ B α) =
        ((1 - e α) * P.eval (algebraMap ℂ B α)) * ((∏ β ∈ I, e β) * ∏ β ∈ (R \ I).erase α, (1 - e β)) := by
          simp only [E]
          rw [← Finset.mul_prod_erase (R \ I) (fun β => 1 - e β) hα]
          ring
      _ = 0 := by rw [hfP α (Finset.mem_sdiff.1 hα).1, zero_mul]
  obtain ⟨R₁, hR₁⟩ := factor_roots (E I) P (R \ I) hEP
  obtain ⟨R₂, hR₂⟩ := factor_roots (E I) Q I hEQ
  obtain ⟨h1, h2⟩ := factor_deg hP (hmonJ _) hR₁
  obtain ⟨h3, -⟩ := factor_deg hQ (hmonJ _) hR₂
  rw [hdegJ] at h1 h2 h3
  have hsd := Finset.card_sdiff_add_card_eq_card hI
  have heq : (R \ I).card = P.natDegree := by
    rcases h1 with h1 | h1
    · rcases h3 with h3 | h3
      · omega
      · exact absurd h3 hE
    · exact absurd h1 hE
  have := h2 heq k
  rw [hmapJ, coeff_map] at this
  rw [mul_comm, this, Algebra.smul_def, mul_comm]

/- English proof (translation)
Use extensionality with `k`. Rewrite using `[coeff_zero]`. Use `(Module.forall_dual_apply_eq_zero_iff ℂ (D.coeff k)).1 fun φ => ?_` and prove the remaining obligations. Set `q : ℂ[X]` to `∑ i ∈ Finset.range (D.natDegree + 1), monomial i (φ (D.coeff i))`. Establish `hq : q = 0`.

Use `Polynomial.funext fun u => ?_` and prove the remaining obligations. Establish `h1 : φ (D.eval (algebraMap ℂ B u)) = 0` using `by rw [h u, map_zero]`. Rewrite `h1` using `[eval_eq_sum_range, map_sum]`. Rewrite using `[eval_zero, ← h1, eval_finsetSum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[eval_monomial, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]`. Establish `hc : q.coeff k = φ (D.coeff k)`. Simplify using `only [q, finsetSum_coeff, coeff_monomial]`. Distinguish the cases in `hk : k ∈ Finset.range (D.natDegree + 1)`. Rewrite using `[Finset.sum_ite_eq']`.

Simplify using `[hk]`. Rewrite using `[Finset.sum_eq_zero]`. Establish `: D.coeff k = 0` using `coeff_eq_zero_of_natDegree_lt (by simpa [Nat.lt_succ_iff] using hk)`. Simplify using `[this]`. Introduce `i hi`.

Rewrite using `[if_neg]`. Introduce and unpack `rfl`. Conclude with `hk hi`. Rewrite using `[← hc, hq, coeff_zero]`.
-/
theorem eq_zero_of_eval_algebraMap (D : B[X]) (h : ∀ u : ℂ, D.eval (algebraMap ℂ B u) = 0) : D = 0 := by
  ext k
  rw [coeff_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ (D.coeff k)).1 fun φ => ?_
  let q : ℂ[X] := ∑ i ∈ Finset.range (D.natDegree + 1), monomial i (φ (D.coeff i))
  have hq : q = 0 := by
    refine Polynomial.funext fun u => ?_
    have h1 : φ (D.eval (algebraMap ℂ B u)) = 0 := by rw [h u, map_zero]
    rw [eval_eq_sum_range, map_sum] at h1
    rw [eval_zero, ← h1, eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [eval_monomial, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have hc : q.coeff k = φ (D.coeff k) := by
    simp only [q, finsetSum_coeff, coeff_monomial]
    by_cases hk : k ∈ Finset.range (D.natDegree + 1)
    · rw [Finset.sum_ite_eq']
      simp [hk]
    · rw [Finset.sum_eq_zero]
      · have : D.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by simpa [Nat.lt_succ_iff] using hk)
        simp [this]
      · intro i hi
        rw [if_neg]
        rintro rfl
        exact hk hi
  rw [← hc, hq, coeff_zero]

end Comm

section Fun

variable {A : Type} [Ring A] [Algebra ℂ A]

/- English proof (translation)
Establish `hcomm : ∀ x ∈ Algebra.adjoin ℂ s, ∀ y ∈ Algebra.adjoin ℂ s, Commute x y`. Introduce `x hx y hy`. Use `Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy fun b hb => ?_` and prove the remaining obligations. Conclude with `(Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx fun a ha => hc b hb a ha).symm`. Introduce `y hy`.

Proceed by induction on `hy using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact hs x hx`. Consider the case `algebraMap c => exact isSS_algebraMap c`. Consider the case `add x y hx hy ihx ihy => exact ihx.add ihy (hcomm x hx y hy)`. Consider the case `mul x y hx hy ihx ihy => exact ihx.mul ihy (hcomm x hx y hy)`.
-/
theorem IsSS.adjoin {s : Set A} (hs : ∀ x ∈ s, IsSS x) (hc : ∀ x ∈ s, ∀ y ∈ s, Commute x y) :
    ∀ y ∈ Algebra.adjoin ℂ s, IsSS y := by
  have hcomm : ∀ x ∈ Algebra.adjoin ℂ s, ∀ y ∈ Algebra.adjoin ℂ s, Commute x y := by
    intro x hx y hy
    refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy fun b hb => ?_
    exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx fun a ha => hc b hb a ha).symm
  intro y hy
  induction hy using Algebra.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap c => exact isSS_algebraMap c
  | add x y hx hy ihx ihy => exact ihx.add ihy (hcomm x hx y hy)
  | mul x y hx hy ihx ihy => exact ihx.mul ihy (hcomm x hx y hy)

set_option linter.deprecated false in

/- English proof (translation)
Set `S : Set A` to `Set.range a ∪ Set.range b`. Establish `hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x`. Introduce and unpack `x (⟨i, rfl⟩ | ⟨i, rfl⟩) y (⟨j, rfl⟩ | ⟨j, rfl⟩)`. Conclude with `(hcomm i j).1.eq`. Conclude with `(hcomm i j).2.1.eq`.

Conclude with `((hcomm j i).2.1.eq).symm`. Conclude with `(hcomm i j).2.2.eq`. Use `letI : CommRing (Algebra.adjoin ℂ S) := Algebra.adjoinCommRingOfComm ℂ hS`. Set `a' : ℕ → Algebra.adjoin ℂ S` to `fun i => ⟨a i, Algebra.subset_adjoin (Or.inl ⟨i, rfl⟩)⟩`. Set `b' : ℕ → Algebra.adjoin ℂ S` to `fun i => ⟨b i, Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)⟩`.

Establish `key : ∀ (n : ℕ) (a' : ℕ → Algebra.adjoin ℂ S), a' n = 1 → ∃ P : (Algebra.adjoin ℂ S)[X], P.Monic ∧ (∀ k ≤ n, P.coeff k = a' k) ∧ ∀ y : ℂ, P.eval (algebraMap ℂ _ y) = ∑ k ∈ Finset.range (n + 1), y ^ k • a' k`. Introduce `n a' hn`. Use `⟨X ^ n + ∑ i ∈ Finset.range n, C (a' i) * X ^ i, monic_X_pow_add ?_, fun k hk => ?_, fun y => ?_⟩` and prove the remaining obligations. Use `mem_degreeLT.1 (Submodule.sum_mem _ fun i hi => mem_degreeLT.2 ?_)` and prove the remaining obligations. Conclude with `(degree_C_mul_X_pow_le i (a' i)).trans_lt (by exact_mod_cast Finset.mem_range.1 hi)`.

Simplify using `only [coeff_add, coeff_X_pow, finsetSum_coeff, coeff_C_mul_X_pow]`. Break down `hk.lt_or_eq with hk | rfl` into its components or cases. Rewrite using `[if_neg hk.ne, zero_add, Finset.sum_ite_eq]`. Simplify using `[Finset.mem_range.2 hk]`. Rewrite using `[if_pos rfl, Finset.sum_ite_eq]`.

Simplify using `[hn]`. Simplify using `only [eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C]`. Rewrite using `[Finset.sum_range_succ, hn, add_comm]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← map_pow, mul_comm, ← Algebra.smul_def]`. Rewrite using `[← map_pow, Algebra.algebraMap_eq_smul_one]`. Take `⟨P, hPm, hPc, hPe⟩` from `key r a' (Subtype.ext ha)`. Take `⟨Q, hQm, hQc, hQe⟩` from `key s b' (Subtype.ext hb)`. Set `p : ℂ[X]` to `(m.map fun x => X + C x).prod`.

Establish `hpe : p = ∏ x ∈ m.toFinset, (X - C (-x))`. Simplify using `only [p]`. Rewrite using `[Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hm]`. Use `congr 1`. Use `Multiset.map_congr rfl fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[map_neg, sub_neg_eq_add]`. Establish `hps : p.Separable`. Rewrite using `[hpe]`. Conclude with `separable_prod_X_sub_C_iff'.2 fun x _ y _ h => neg_inj.1 h`. Establish `hval : ∀ u : ℂ, p.eval u = (m.map (u + ·)).prod`.

Introduce `u`. Simplify using `only [p, eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_add, eval_X, eval_C]`. Establish `hrelP : P.comp (X + C (algebraMap ℂ _ c₁)) * Q.comp (X + C (algebraMap ℂ _ c₂)) = p.map (algebraMap ℂ (Algebra.adjoin ℂ S))`. Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_eval_algebraMap _ fun u => ?_` and prove the remaining obligations.

Rewrite using `[eval_sub, eval_mul, eval_comp, eval_comp, eval_map, eval₂_at_apply, hval]`. Simplify using `only [eval_add, eval_X, eval_C, ← map_add]`. Rewrite using `[hPe, hQe, sub_eq_zero]`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `hv : ∀ x y : Algebra.adjoin ℂ S, ((x * y : Algebra.adjoin ℂ S) : A) = (x : A) * y` using `fun x y => rfl`.

Establish `hsm : ∀ (c : ℂ) (x : Algebra.adjoin ℂ S), ((c • x : Algebra.adjoin ℂ S) : A) = c • (x : A)` using `fun c x => rfl`. Establish `halg : ∀ c : ℂ, ((algebraMap ℂ (Algebra.adjoin ℂ S) c : Algebra.adjoin ℂ S) : A) = algebraMap ℂ A c` using `fun c => rfl`. Establish `hsum : ∀ (t : Finset ℕ) (g : ℕ → Algebra.adjoin ℂ S), ((∑ i ∈ t, g i : Algebra.adjoin ℂ S) : A) = ∑ i ∈ t, (g i : A)`. Introduce `t g`. Proceed by induction on `t using Finset.induction_on with`.

Consider the case `empty => rfl`. Consider the case `insert j t hj ih`. Rewrite using `[Finset.sum_insert hj, Finset.sum_insert hj, ← ih]`. Both sides reduce to the same expression. Rewrite using `[hv, hsum, hsum, halg]`.

Simplify using `only [hsm]`. Conclude with `hrel u`. Set `P₁` to `P.comp (X + C (algebraMap ℂ (Algebra.adjoin ℂ S) c₁))`. Set `Q₁` to `Q.comp (X + C (algebraMap ℂ (Algebra.adjoin ℂ S) c₂))`. Establish `hP₁ : P₁.Monic` using `hPm.comp_X_add_C _`.

Establish `hQ₁ : Q₁.Monic` using `hQm.comp_X_add_C _`. Establish `hss₁ : ∀ j, IsSS (P₁.coeff j)` using `isSS_coeff p hps P₁ Q₁ hP₁ hQ₁ hrelP`. Establish `hss₂ : ∀ j, IsSS (Q₁.coeff j)` using `isSS_coeff p hps Q₁ P₁ hQ₁ hP₁ (by rw [mul_comm]; exact hrelP)`. Establish `unshift : ∀ (P₁ : (Algebra.adjoin ℂ S)[X]) (c : ℂ), (∀ j, IsSS (P₁.coeff j)) → ∀ k, IsSS ((P₁.comp (X - C (algebraMap ℂ _ c))).coeff k)`. Introduce `P₁ c h k`.

Rewrite using `[comp_eq_sum_left, Polynomial.sum, finsetSum_coeff]`. Use `IsSS.sum _ _ (fun j _ => ?_) fun i _ j _ => Commute.all _ _` and prove the remaining obligations. Rewrite using `[coeff_C_mul]`. Establish `hmap : (X - C (algebraMap ℂ (Algebra.adjoin ℂ S) c)) ^ j = ((X - C c) ^ j).map (algebraMap ℂ _)`. Simplify using `[Polynomial.map_pow]`.

Rewrite using `[hmap, coeff_map, mul_comm, ← Algebra.smul_def]`. Conclude with `(h j).smul _`. Establish `hPP : P = P₁.comp (X - C (algebraMap ℂ (Algebra.adjoin ℂ S) c₁))`. Simplify using `only [P₁, comp_assoc, add_comp, X_comp, C_comp, sub_add_cancel, comp_X]`. Establish `hQQ : Q = Q₁.comp (X - C (algebraMap ℂ (Algebra.adjoin ℂ S) c₂))`.

Simplify using `only [Q₁, comp_assoc, add_comp, X_comp, C_comp, sub_add_cancel, comp_X]`. Establish `toA : ∀ x : Algebra.adjoin ℂ S, IsSS x → IsSS (x : A)`. Introduce and unpack `x ⟨t, ht⟩`. Use `⟨t, ?_⟩` and prove the remaining obligations. Use `aeval_algHom_apply (Algebra.adjoin ℂ S).val x (∏ v ∈ t, (X - C v))` as an intermediate fact.

Rewrite `this` using `[Subalgebra.coe_val]`. Rewrite using `[this, ht]`. Both sides reduce to the same expression. Use `⟨fun hk => ?_, fun hk => ?_⟩` and prove the remaining obligations. Establish `h1` using `unshift P₁ c₁ hss₁ k`.

Rewrite `h1` using `[← hPP, hPc k hk]`. Conclude with `toA _ h1`. Establish `h1` using `unshift Q₁ c₂ hss₂ k`. Rewrite `h1` using `[← hQQ, hQc k hk]`. Conclude with `toA _ h1`.
-/
theorem isSS_coeff_fun (m : Multiset ℂ) (hm : m.Nodup) (r s : ℕ) (_hrs : Multiset.card m = r + s) (c₁ c₂ : ℂ)
    (a b : ℕ → A) (ha : a r = 1) (hb : b s = 1)
    (hcomm : ∀ i j, Commute (a i) (a j) ∧ Commute (a i) (b j) ∧ Commute (b i) (b j))
    (hrel : ∀ u : ℂ, (∑ k ∈ Finset.range (r + 1), (u + c₁) ^ k • a k) *
      (∑ k ∈ Finset.range (s + 1), (u + c₂) ^ k • b k) = algebraMap ℂ A (m.map (u + ·)).prod) (k : ℕ) :
    (k ≤ r → IsSS (a k)) ∧ (k ≤ s → IsSS (b k)) := by
  classical
  let S : Set A := Set.range a ∪ Set.range b
  have hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩) y (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact (hcomm i j).1.eq
    · exact (hcomm i j).2.1.eq
    · exact ((hcomm j i).2.1.eq).symm
    · exact (hcomm i j).2.2.eq
  letI : CommRing (Algebra.adjoin ℂ S) := Algebra.adjoinCommRingOfComm ℂ hS
  let a' : ℕ → Algebra.adjoin ℂ S := fun i => ⟨a i, Algebra.subset_adjoin (Or.inl ⟨i, rfl⟩)⟩
  let b' : ℕ → Algebra.adjoin ℂ S := fun i => ⟨b i, Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)⟩

  have key : ∀ (n : ℕ) (a' : ℕ → Algebra.adjoin ℂ S), a' n = 1 →
      ∃ P : (Algebra.adjoin ℂ S)[X], P.Monic ∧ (∀ k ≤ n, P.coeff k = a' k) ∧
        ∀ y : ℂ, P.eval (algebraMap ℂ _ y) = ∑ k ∈ Finset.range (n + 1), y ^ k • a' k := by
    intro n a' hn
    refine ⟨X ^ n + ∑ i ∈ Finset.range n, C (a' i) * X ^ i, monic_X_pow_add ?_, fun k hk => ?_, fun y => ?_⟩
    · refine mem_degreeLT.1 (Submodule.sum_mem _ fun i hi => mem_degreeLT.2 ?_)
      exact (degree_C_mul_X_pow_le i (a' i)).trans_lt (by exact_mod_cast Finset.mem_range.1 hi)
    · simp only [coeff_add, coeff_X_pow, finsetSum_coeff, coeff_C_mul_X_pow]
      rcases hk.lt_or_eq with hk | rfl
      · rw [if_neg hk.ne, zero_add, Finset.sum_ite_eq]
        simp [Finset.mem_range.2 hk]
      · rw [if_pos rfl, Finset.sum_ite_eq]
        simp [hn]
    · simp only [eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C]
      rw [Finset.sum_range_succ, hn, add_comm]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [← map_pow, mul_comm, ← Algebra.smul_def]
      · rw [← map_pow, Algebra.algebraMap_eq_smul_one]
  obtain ⟨P, hPm, hPc, hPe⟩ := key r a' (Subtype.ext ha)
  obtain ⟨Q, hQm, hQc, hQe⟩ := key s b' (Subtype.ext hb)
  let p : ℂ[X] := (m.map fun x => X + C x).prod
  have hpe : p = ∏ x ∈ m.toFinset, (X - C (-x)) := by
    simp only [p]
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hm]
    congr 1
    refine Multiset.map_congr rfl fun x _ => ?_
    rw [map_neg, sub_neg_eq_add]
  have hps : p.Separable := by
    rw [hpe]
    exact separable_prod_X_sub_C_iff'.2 fun x _ y _ h => neg_inj.1 h
  have hval : ∀ u : ℂ, p.eval u = (m.map (u + ·)).prod := by
    intro u
    simp only [p, eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_add, eval_X, eval_C]

  have hrelP : P.comp (X + C (algebraMap ℂ _ c₁)) * Q.comp (X + C (algebraMap ℂ _ c₂)) =
      p.map (algebraMap ℂ (Algebra.adjoin ℂ S)) := by
    rw [← sub_eq_zero]
    refine eq_zero_of_eval_algebraMap _ fun u => ?_
    rw [eval_sub, eval_mul, eval_comp, eval_comp, eval_map, eval₂_at_apply, hval]
    simp only [eval_add, eval_X, eval_C, ← map_add]
    rw [hPe, hQe, sub_eq_zero]
    apply Subtype.ext
    have hv : ∀ x y : Algebra.adjoin ℂ S, ((x * y : Algebra.adjoin ℂ S) : A) = (x : A) * y := fun x y => rfl
    have hsm : ∀ (c : ℂ) (x : Algebra.adjoin ℂ S), ((c • x : Algebra.adjoin ℂ S) : A) = c • (x : A) :=
      fun c x => rfl
    have halg : ∀ c : ℂ, ((algebraMap ℂ (Algebra.adjoin ℂ S) c : Algebra.adjoin ℂ S) : A) = algebraMap ℂ A c :=
      fun c => rfl
    have hsum : ∀ (t : Finset ℕ) (g : ℕ → Algebra.adjoin ℂ S),
        ((∑ i ∈ t, g i : Algebra.adjoin ℂ S) : A) = ∑ i ∈ t, (g i : A) := by
      intro t g
      induction t using Finset.induction_on with
      | empty => rfl
      | insert j t hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj, ← ih]
        rfl
    rw [hv, hsum, hsum, halg]
    simp only [hsm]
    exact hrel u

  let P₁ := P.comp (X + C (algebraMap ℂ (Algebra.adjoin ℂ S) c₁))
  let Q₁ := Q.comp (X + C (algebraMap ℂ (Algebra.adjoin ℂ S) c₂))
  have hP₁ : P₁.Monic := hPm.comp_X_add_C _
  have hQ₁ : Q₁.Monic := hQm.comp_X_add_C _
  have hss₁ : ∀ j, IsSS (P₁.coeff j) := isSS_coeff p hps P₁ Q₁ hP₁ hQ₁ hrelP
  have hss₂ : ∀ j, IsSS (Q₁.coeff j) := isSS_coeff p hps Q₁ P₁ hQ₁ hP₁ (by rw [mul_comm]; exact hrelP)

  have unshift : ∀ (P₁ : (Algebra.adjoin ℂ S)[X]) (c : ℂ), (∀ j, IsSS (P₁.coeff j)) →
      ∀ k, IsSS ((P₁.comp (X - C (algebraMap ℂ _ c))).coeff k) := by
    intro P₁ c h k
    rw [comp_eq_sum_left, Polynomial.sum, finsetSum_coeff]
    refine IsSS.sum _ _ (fun j _ => ?_) fun i _ j _ => Commute.all _ _
    rw [coeff_C_mul]
    have hmap : (X - C (algebraMap ℂ (Algebra.adjoin ℂ S) c)) ^ j = ((X - C c) ^ j).map (algebraMap ℂ _) := by
      simp [Polynomial.map_pow]
    rw [hmap, coeff_map, mul_comm, ← Algebra.smul_def]
    exact (h j).smul _
  have hPP : P = P₁.comp (X - C (algebraMap ℂ (Algebra.adjoin ℂ S) c₁)) := by
    simp only [P₁, comp_assoc, add_comp, X_comp, C_comp, sub_add_cancel, comp_X]
  have hQQ : Q = Q₁.comp (X - C (algebraMap ℂ (Algebra.adjoin ℂ S) c₂)) := by
    simp only [Q₁, comp_assoc, add_comp, X_comp, C_comp, sub_add_cancel, comp_X]
  have toA : ∀ x : Algebra.adjoin ℂ S, IsSS x → IsSS (x : A) := by
    rintro x ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have := aeval_algHom_apply (Algebra.adjoin ℂ S).val x (∏ v ∈ t, (X - C v))
    rw [Subalgebra.coe_val] at this
    rw [this, ht]
    rfl
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · have h1 := unshift P₁ c₁ hss₁ k
    rw [← hPP, hPc k hk] at h1
    exact toA _ h1
  · have h1 := unshift Q₁ c₂ hss₂ k
    rw [← hQQ, hQc k hk] at h1
    exact toA _ h1

end Fun

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac

end

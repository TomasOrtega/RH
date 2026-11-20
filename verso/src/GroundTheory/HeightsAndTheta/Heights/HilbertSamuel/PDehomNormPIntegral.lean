import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDehomNormPIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDehomCharpolyForms
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

namespace DehomNormPIntegral

/- English proof (translation)
Rewrite `hq` using `[Valuation.mem_valuationSubring_iff, Rat.padicValuation_le_one_iff]`. Rewrite using `[padicValRat_def, padicValNat.eq_zero_of_not_dvd hq]`. Simplify using the standard rewrite rules.
-/
theorem padicValRat_nonneg_of_mem {p : ℕ} [Fact p.Prime] {q : ℚ}
    (hq : q ∈ (Rat.padicValuation p).valuationSubring) : 0 ≤ padicValRat p q := by
  rw [Valuation.mem_valuationSubring_iff, Rat.padicValuation_le_one_iff] at hq
  rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hq]
  simp

/- English proof (translation)
Establish `hM0 : M ≠ 0` using `fun h => hM (h ▸ dvd_zero p)`. Rewrite using `[Valuation.mem_valuationSubring_iff, Rat.padicValuation_le_one_iff, Rat.inv_natCast_den, if_neg hM0]`. Conclude with `hM`.
-/
theorem inv_natCast_mem {p : ℕ} [Fact p.Prime] {M : ℕ} (hM : ¬ p ∣ M) :
    ((M : ℚ)⁻¹) ∈ (Rat.padicValuation p).valuationSubring := by
  have hM0 : M ≠ 0 := fun h => hM (h ▸ dvd_zero p)
  rw [Valuation.mem_valuationSubring_iff, Rat.padicValuation_le_one_iff, Rat.inv_natCast_den, if_neg hM0]
  exact hM

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨F', rfl⟩ ν`. Rewrite using `[coeff_map]`. Conclude with `(F'.coeff ν).2`. Introduce `h`.

Use `⟨∑ ν ∈ F.support, monomial ν ⟨F.coeff ν, h ν⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum]`. Simplify using `only [map_monomial]`. Conclude with `F.support_sum_monomial_coeff`.
-/
theorem mem_range_map_iff {τ : Type*} (V : Subring ℚ) (F : MvPolynomial τ ℚ) :
    F ∈ (map V.subtype).range ↔ ∀ ν, F.coeff ν ∈ V := by
  classical
  constructor
  · rintro ⟨F', rfl⟩ ν
    rw [coeff_map]
    exact (F'.coeff ν).2
  · intro h
    refine ⟨∑ ν ∈ F.support, monomial ν ⟨F.coeff ν, h ν⟩, ?_⟩
    rw [map_sum]
    simp only [map_monomial]
    exact F.support_sum_monomial_coeff

/- English proof (translation)
Take `⟨Q, hQm, hQ⟩` from `hx`. Establish `hl : Q.map (algebraMap B Ω) ∈ Polynomial.lifts (algebraMap R Ω)`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `k`. Rewrite using `[Polynomial.coeff_map]`.

Conclude with `hB _ (Q.coeff k).2`. Take `⟨Q', hQ', -, hQ'm⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic hl (hQm.map _)`. Use `⟨Q', hQ'm, ?_⟩` and prove the remaining obligations. Rewrite using `[← Polynomial.eval_map, hQ', Polynomial.eval_map]`. Conclude with `hQ`.
-/
theorem isIntegral_of_le_range {R Ω : Type*} [CommRing R] [CommRing Ω] [Algebra R Ω] (B : Subalgebra ℤ Ω)
    (hB : ∀ b ∈ B, ∃ r, algebraMap R Ω r = b) {x : Ω} (hx : IsIntegral B x) : IsIntegral R x := by
  obtain ⟨Q, hQm, hQ⟩ := hx
  have hl : Q.map (algebraMap B Ω) ∈ Polynomial.lifts (algebraMap R Ω) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro k
    rw [Polynomial.coeff_map]
    exact hB _ (Q.coeff k).2
  obtain ⟨Q', hQ', -, hQ'm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (hQm.map _)
  refine ⟨Q', hQ'm, ?_⟩
  rw [← Polynomial.eval_map, hQ', Polynomial.eval_map]
  exact hQ

/- English proof (translation)
Establish `hl` using `DehomCharpolyForms.ne_zero_of_generic hgen`. Establish `hlj` using `hl j`. Use `set H := rename Subtype.val (PullFormsGeneric.dehom j F) with hHdef`. Use `set N2 := max N H.totalDegree with hN2`. Establish `hHW : H ∈ (map V.subtype).range`.

Take `⟨G', hG'⟩` from `(mem_range_map_iff V _).mpr hG`. Conclude with `⟨rename Subtype.val G', by rw [map_rename, hG']⟩`. Establish `hK : DehomCharpolyForms.homog j N2 H = X j ^ (N2 - N) * F`. Establish `hF2 : (X j ^ (N2 - N) * F).IsHomogeneous N2`. Use `(isHomogeneous_X_pow (R := ℚ) j (N2 - N)).mul hF` as an intermediate fact.

Rewrite `this` using `[Nat.sub_add_cancel (le_max_left _ _)]`. Then use the resulting hypothesis. Use `sub_eq_zero.mp (hgen N2 _ ((DehomCharpolyForms.isHomogeneous_homog j N2 H).sub hF2) ?_)` and prove the remaining obligations. Establish `hfun : (fun i => if h : i = j then (1 : Ω) else ((fun i => l i / l j) ∘ (Subtype.val : {i // i ≠ j} → Fin (D + 1))) ⟨i, h⟩) = fun i => l i / l j`. Use function extensionality and compare the values at `i`. Use `split_ifs with h`.

Substitute `h` using the available equality. Conclude with `(div_self (hl _)).symm`. Both sides reduce to the same expression. Establish `hval : aeval (fun i => l i / l j) H = aeval (fun i => l i / l j) F`. Rewrite using `[hHdef, aeval_rename, PullFormsGeneric.aeval_dehom, hfun]`.

Rewrite using `[map_sub, DehomCharpolyForms.aeval_homog l j hlj H (le_max_right _ _), hval, DehomCharpolyForms.aeval_div_of_isHomogeneous l j hF, map_mul, map_pow, aeval_X, sub_eq_zero]`. Establish `: l j ^ N2 = l j ^ (N2 - N) * l j ^ N` using `by rw [← pow_add, Nat.sub_add_cancel (le_max_left _ _)]`. Rewrite using `[this, inv_pow]`. Clear the denominators using the available nonvanishing facts. Establish `hKW : X j ^ (N2 - N) * F ∈ (map V.subtype).range`.

Rewrite using `[← hK, DehomCharpolyForms.homog]`. Use `Subring.sum_mem _ fun e _ => Subring.mul_mem _ ⟨X j ^ (N2 - e), by simp⟩ ?_` and prove the remaining obligations. Rewrite using `[mem_range_map_iff]`. Introduce `ν`. Rewrite using `[coeff_homogeneousComponent]`.

Use `split_ifs`. Conclude with `(mem_range_map_iff V H).mp hHW ν`. Conclude with `V.zero_mem`. Establish `h1 : coeff (μ + Finsupp.single j (N2 - N)) (X j ^ (N2 - N) * F) = coeff μ F`. Rewrite using `[X_pow_eq_monomial, mul_comm, coeff_mul_monomial, mul_one]`.

Rewrite using `[← h1]`. Conclude with `(mem_range_map_iff V _).mp hKW _`.
-/
theorem coeff_mem_of_dehom_coeff_mem {Ω : Type} [Field Ω] [CharZero Ω] {D : ℕ} {l : Fin (D + 1) → Ω}
    (hgen : ∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0)
    (j : Fin (D + 1)) {N : ℕ} {F : MvPolynomial (Fin (D + 1)) ℚ} (hF : F.IsHomogeneous N) (V : Subring ℚ)
    (hG : ∀ ν, (PullFormsGeneric.dehom j F).coeff ν ∈ V) (μ : Fin (D + 1) →₀ ℕ) : F.coeff μ ∈ V := by
  classical
  have hl := DehomCharpolyForms.ne_zero_of_generic hgen
  have hlj := hl j
  set H := rename Subtype.val (PullFormsGeneric.dehom j F) with hHdef
  set N2 := max N H.totalDegree with hN2
  have hHW : H ∈ (map V.subtype).range := by
    obtain ⟨G', hG'⟩ := (mem_range_map_iff V _).mpr hG
    exact ⟨rename Subtype.val G', by rw [map_rename, hG']⟩
  have hK : DehomCharpolyForms.homog j N2 H = X j ^ (N2 - N) * F := by
    have hF2 : (X j ^ (N2 - N) * F).IsHomogeneous N2 := by
      have := (isHomogeneous_X_pow (R := ℚ) j (N2 - N)).mul hF
      rwa [Nat.sub_add_cancel (le_max_left _ _)] at this
    refine sub_eq_zero.mp (hgen N2 _ ((DehomCharpolyForms.isHomogeneous_homog j N2 H).sub hF2) ?_)
    have hfun : (fun i => if h : i = j then (1 : Ω) else ((fun i => l i / l j) ∘ (Subtype.val : {i // i ≠ j} → Fin (D + 1))) ⟨i, h⟩) =
        fun i => l i / l j := by
      funext i
      split_ifs with h
      · subst h
        exact (div_self (hl _)).symm
      · rfl
    have hval : aeval (fun i => l i / l j) H = aeval (fun i => l i / l j) F := by
      rw [hHdef, aeval_rename, PullFormsGeneric.aeval_dehom, hfun]
    rw [map_sub, DehomCharpolyForms.aeval_homog l j hlj H (le_max_right _ _), hval,
      DehomCharpolyForms.aeval_div_of_isHomogeneous l j hF, map_mul, map_pow, aeval_X, sub_eq_zero]
    have : l j ^ N2 = l j ^ (N2 - N) * l j ^ N := by rw [← pow_add, Nat.sub_add_cancel (le_max_left _ _)]
    rw [this, inv_pow]
    field_simp
  have hKW : X j ^ (N2 - N) * F ∈ (map V.subtype).range := by
    rw [← hK, DehomCharpolyForms.homog]
    refine Subring.sum_mem _ fun e _ => Subring.mul_mem _ ⟨X j ^ (N2 - e), by simp⟩ ?_
    rw [mem_range_map_iff]
    intro ν
    rw [coeff_homogeneousComponent]
    split_ifs
    · exact (mem_range_map_iff V H).mp hHW ν
    · exact V.zero_mem
  have h1 : coeff (μ + Finsupp.single j (N2 - N)) (X j ^ (N2 - N) * F) = coeff μ F := by
    rw [X_pow_eq_monomial, mul_comm, coeff_mul_monomial, mul_one]
  rw [← h1]
  exact (mem_range_map_iff V _).mp hKW _

end DehomNormPIntegral

open DehomCharpolyForms DehomNormPIntegral in

/- English proof (translation)
Introduce `Ω _ _ D l P _ hP hgen p hp M hM j m u hu c hchom hcp μ`. Use `Fact.mk hp` as an intermediate fact. Establish `hl` using `ne_zero_of_generic hgen`. Use `set n := Module.finrank P Ω with hn`. Use `set f := LinearMap.charpoly (Algebra.lmul P Ω u) with hf`.

Establish `h0 : algebraMap P Ω (f.coeff 0) = aeval (fun i => l i / l j) (c n)`. Use `congrArg (fun g => Polynomial.coeff g 0) hcp` as an intermediate fact. Simplify using `only [Polynomial.coeff_map, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow] at this`. Rewrite using `[this, Finset.sum_eq_single n]`. Simplify using the standard rewrite rules.

Introduce `b hb hbn`. Establish `: b < n` using `lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)) hbn`. Rewrite using `[if_neg (by omega)]`. Introduce `h`. Simplify using `at h`.

Establish `hdet` using `LinearMap.det_eq_sign_charpoly_coeff (Algebra.lmul P Ω u)`. Rewrite `hdet` using `[← Algebra.norm_apply, ← hf]`. Establish `hc0 : f.coeff 0 = (-1) ^ n * Algebra.norm P u`. Rewrite using `[hdet, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]`. Set `V` to `(Rat.padicValuation p).valuationSubring`.

Set `σ` to `{i // i ≠ j}`. Establish `hmemP : ∀ i, l i / l j ∈ P` using `fun i => hP ▸ IntermediateField.subset_adjoin ℚ _ ⟨i, j, hl j, rfl⟩`. Set `tP : σ → P` to `fun i => ⟨l i / l j, hmemP i⟩`. Set `ω : σ → Ω` to `fun i => l i / l j`. Set `_ : Algebra (MvPolynomial σ V) (MvPolynomial σ ℚ)` to `MvPolynomial.algebraMvPolynomial`.

Set `ψP : MvPolynomial σ V →+* P` to `(aeval tP : MvPolynomial σ ℚ →ₐ[ℚ] P).toRingHom.comp (algebraMap (MvPolynomial σ V) (MvPolynomial σ ℚ))`. Set `_ : Algebra (MvPolynomial σ V) P` to `ψP.toAlgebra`. Set `_ : Algebra (MvPolynomial σ V) Ω` to `(P.val.toRingHom.comp ψP).toAlgebra`. Establish `_ : IsScalarTower (MvPolynomial σ V) P Ω` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Set `fA : MvPolynomial σ ℚ →ₐ[MvPolynomial σ V] Ω` to `{ (aeval ω : MvPolynomial σ ℚ →ₐ[ℚ] Ω).toRingHom with commutes' := fun r => by show aeval ω _ = P.val (aeval tP _)`.

Conclude with `(DFunLike.congr_fun (comp_aeval (f := tP) P.val) _).symm }`. Establish `hfA : ∀ G, fA G = aeval ω G` using `fun _ => rfl`. Establish `hinj : Function.Injective fA`. Introduce `a b hab`. Conclude with `injective_chart hgen j (by rw [← hfA, ← hfA]; exact hab)`.

Establish `halg : ∀ r, algebraMap (MvPolynomial σ V) Ω r = aeval ω (map (algebraMap V ℚ) r)` using `fun r => ((fA.commutes r).symm.trans (hfA _)).trans rfl`. Establish `hB : ∀ b ∈ Algebra.adjoin ℤ (insert ((M : Ω)⁻¹) (Set.range fun i => l i / l j)), ∃ r, algebraMap (MvPolynomial σ V) Ω r = b`. Introduce `b hb`. Establish `hle : Algebra.adjoin ℤ (insert ((M : Ω)⁻¹) (Set.range fun i => l i / l j)) ≤ ((Algebra.ofId (MvPolynomial σ V) Ω).range).restrictScalars ℤ`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations.

Introduce and unpack `_ (rfl | ⟨i, rfl⟩)`. Use `⟨C ⟨(M : ℚ)⁻¹, inv_natCast_mem hM⟩, ?_⟩ show algebraMap _ Ω _ = _` and prove the remaining obligations. Rewrite using `[halg]`. Simplify using the standard rewrite rules. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Use `⟨1, ?_⟩` and prove the remaining obligations. Use `show algebraMap _ Ω _ = _`. Rewrite using `[map_one]`. Conclude with `(div_self (hl i)).symm`.

Use `⟨X ⟨i, h⟩, ?_⟩ show algebraMap _ Ω _ = _` and prove the remaining obligations. Rewrite using `[halg]`. Simplify using `[ω]`. Take `⟨r, hr⟩` from `hle hb`. Conclude with `⟨r, hr⟩`.

Establish `hu' : IsIntegral (MvPolynomial σ V) u` using `isIntegral_of_le_range _ hB ((mem_integralClosure_iff _ _).mp hu)`. Establish `hN : IsIntegral (MvPolynomial σ V) (algebraMap P Ω (Algebra.norm P u))` using `(Algebra.isIntegral_norm P hu').algebraMap`. Establish `hx : IsIntegral (MvPolynomial σ V) (aeval (fun i => l i / l j) (c n))`. Rewrite using `[← h0, hc0, map_mul, map_pow, map_neg, map_one]`. Conclude with `(isIntegral_one.neg.pow n).mul hN`.

Establish `hdeh : aeval ω (PullFormsGeneric.dehom j (c n)) = aeval (fun i => l i / l j) (c n)`. Rewrite using `[PullFormsGeneric.aeval_dehom]`. Use `congrArg (fun g => aeval g (c n)) (funext fun i => ?_)` and prove the remaining obligations. Use `split_ifs with h`. Substitute `h` using the available equality.

Conclude with `(div_self (hl _)).symm`. Both sides reduce to the same expression. Establish `hG : IsIntegral (MvPolynomial σ V) (PullFormsGeneric.dehom j (c n))` using `(isIntegral_algHom_iff fA hinj).mp (by rw [hfA, hdeh]; exact hx)`. Establish `hGc : ∀ ν, (PullFormsGeneric.dehom j (c n)).coeff ν ∈ V.toSubring`. Introduce `ν`.

Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.mp (MvPolynomial.isIntegral_iff_isIntegral_coeff.mp hG ν)`. Rewrite using `[← hy]`. Conclude with `y.2`. Conclude with `padicValRat_nonneg_of_mem (coeff_mem_of_dehom_coeff_mem hgen j (hchom) V.toSubring hGc μ)`.
-/
theorem DehomNormPIntegral.proof : DehomNormPIntegral.Statement := by
  intro Ω _ _ D l P _ hP hgen p hp M hM j m u hu c hchom hcp μ
  classical
  have := Fact.mk hp
  have hl := ne_zero_of_generic hgen
  set n := Module.finrank P Ω with hn
  set f := LinearMap.charpoly (Algebra.lmul P Ω u) with hf

  have h0 : algebraMap P Ω (f.coeff 0) = aeval (fun i => l i / l j) (c n) := by
    have := congrArg (fun g => Polynomial.coeff g 0) hcp
    simp only [Polynomial.coeff_map, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow] at this
    rw [this, Finset.sum_eq_single n]
    · simp
    · intro b hb hbn
      have : b < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)) hbn
      rw [if_neg (by omega)]
    · intro h
      simp at h

  have hdet := LinearMap.det_eq_sign_charpoly_coeff (Algebra.lmul P Ω u)
  rw [← Algebra.norm_apply, ← hf] at hdet
  have hc0 : f.coeff 0 = (-1) ^ n * Algebra.norm P u := by
    rw [hdet, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

  let V := (Rat.padicValuation p).valuationSubring
  let σ := {i // i ≠ j}
  have hmemP : ∀ i, l i / l j ∈ P := fun i => hP ▸ IntermediateField.subset_adjoin ℚ _ ⟨i, j, hl j, rfl⟩
  let tP : σ → P := fun i => ⟨l i / l j, hmemP i⟩
  let ω : σ → Ω := fun i => l i / l j
  let _ : Algebra (MvPolynomial σ V) (MvPolynomial σ ℚ) := MvPolynomial.algebraMvPolynomial
  let ψP : MvPolynomial σ V →+* P :=
    (aeval tP : MvPolynomial σ ℚ →ₐ[ℚ] P).toRingHom.comp (algebraMap (MvPolynomial σ V) (MvPolynomial σ ℚ))
  let _ : Algebra (MvPolynomial σ V) P := ψP.toAlgebra
  let _ : Algebra (MvPolynomial σ V) Ω := (P.val.toRingHom.comp ψP).toAlgebra
  have _ : IsScalarTower (MvPolynomial σ V) P Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let fA : MvPolynomial σ ℚ →ₐ[MvPolynomial σ V] Ω :=
    { (aeval ω : MvPolynomial σ ℚ →ₐ[ℚ] Ω).toRingHom with
      commutes' := fun r => by
        show aeval ω _ = P.val (aeval tP _)
        exact (DFunLike.congr_fun (comp_aeval (f := tP) P.val) _).symm }
  have hfA : ∀ G, fA G = aeval ω G := fun _ => rfl
  have hinj : Function.Injective fA := by
    intro a b hab
    exact injective_chart hgen j (by rw [← hfA, ← hfA]; exact hab)
  have halg : ∀ r, algebraMap (MvPolynomial σ V) Ω r =
      aeval ω (map (algebraMap V ℚ) r) := fun r => ((fA.commutes r).symm.trans (hfA _)).trans rfl

  have hB : ∀ b ∈ Algebra.adjoin ℤ (insert ((M : Ω)⁻¹) (Set.range fun i => l i / l j)),
      ∃ r, algebraMap (MvPolynomial σ V) Ω r = b := by
    intro b hb
    have hle : Algebra.adjoin ℤ (insert ((M : Ω)⁻¹) (Set.range fun i => l i / l j)) ≤
        ((Algebra.ofId (MvPolynomial σ V) Ω).range).restrictScalars ℤ := by
      refine Algebra.adjoin_le ?_
      rintro _ (rfl | ⟨i, rfl⟩)
      · refine ⟨C ⟨(M : ℚ)⁻¹, inv_natCast_mem hM⟩, ?_⟩
        show algebraMap _ Ω _ = _
        rw [halg]
        simp
      · by_cases h : i = j
        · subst h
          refine ⟨1, ?_⟩
          show algebraMap _ Ω _ = _
          rw [map_one]
          exact (div_self (hl i)).symm
        · refine ⟨X ⟨i, h⟩, ?_⟩
          show algebraMap _ Ω _ = _
          rw [halg]
          simp [ω]
    obtain ⟨r, hr⟩ := hle hb
    exact ⟨r, hr⟩
  have hu' : IsIntegral (MvPolynomial σ V) u := isIntegral_of_le_range _ hB ((mem_integralClosure_iff _ _).mp hu)
  have hN : IsIntegral (MvPolynomial σ V) (algebraMap P Ω (Algebra.norm P u)) :=
    (Algebra.isIntegral_norm P hu').algebraMap
  have hx : IsIntegral (MvPolynomial σ V) (aeval (fun i => l i / l j) (c n)) := by
    rw [← h0, hc0, map_mul, map_pow, map_neg, map_one]
    exact (isIntegral_one.neg.pow n).mul hN

  have hdeh : aeval ω (PullFormsGeneric.dehom j (c n)) = aeval (fun i => l i / l j) (c n) := by
    rw [PullFormsGeneric.aeval_dehom]
    refine congrArg (fun g => aeval g (c n)) (funext fun i => ?_)
    split_ifs with h
    · subst h
      exact (div_self (hl _)).symm
    · rfl
  have hG : IsIntegral (MvPolynomial σ V) (PullFormsGeneric.dehom j (c n)) :=
    (isIntegral_algHom_iff fA hinj).mp (by rw [hfA, hdeh]; exact hx)
  have hGc : ∀ ν, (PullFormsGeneric.dehom j (c n)).coeff ν ∈ V.toSubring := by
    intro ν
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (MvPolynomial.isIntegral_iff_isIntegral_coeff.mp hG ν)
    rw [← hy]
    exact y.2
  exact padicValRat_nonneg_of_mem (coeff_mem_of_dehom_coeff_mem hgen j (hchom) V.toSubring hGc μ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

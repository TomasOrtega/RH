import Formalism.LocalToGlobal.AlgebraicTheory.StatementB
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.AnalyticTransOfAdd

open PowerSeries

noncomputable section

namespace Formalism.L2.AlgTh

namespace EtPowerP

open Formalism.L2.Th1.E Formalism.L2.Th1.E.Main

/- English proof (translation)
Use `revert h`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Conclude with `⟨0, by simpa using (Main.unitAt_one : UnitAt 0 (1 : K⟦X⟧))⟩`. Introduce `a s ha ih h`.

Take `⟨e, he⟩` from `h a (Finset.mem_insert_self a s)`. Take `⟨E, hE⟩` from `ih (fun j hj => h j (Finset.mem_insert_of_mem hj))`. Take `⟨hmul, hpow, -⟩` from `unitAtRules K`. Rewrite using `[Finset.prod_insert ha]`. Conclude with `⟨e * m a + E, hmul _ _ _ _ (hpow _ _ _ he) hE⟩`.
-/
private theorem exists_unitAt_prod_pow {K : Type} [NormedField K] [IsUltrametricDist K]
    (s : Finset ℕ) (F : ℕ → K⟦X⟧) (m : ℕ → ℕ) (h : ∀ j ∈ s, ∃ e, UnitAt e (F j)) :
    ∃ E, UnitAt E (∏ j ∈ s, F j ^ m j) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    exact ⟨0, by simpa using (Main.unitAt_one : UnitAt 0 (1 : K⟦X⟧))⟩
  · intro a s ha ih h
    obtain ⟨e, he⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨E, hE⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    obtain ⟨hmul, hpow, -⟩ := unitAtRules K
    rw [Finset.prod_insert ha]
    exact ⟨e * m a + E, hmul _ _ _ _ (hpow _ _ _ he) hE⟩

/- English proof (translation)
Establish `h1` using `congrArg (coeff E) heq`. Rewrite `h1` using `[coeff_C_mul_X_pow, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply, hh]`. Use `split_ifs at h1 with hE`. Conclude with `⟨hE, h1⟩`. Conclude with `absurd h1 zero_ne_one`.
-/
private theorem eq_and_eq_one_of_C_mul_X_pow_eq {K : Type} [Field K] {E n : ℕ} {b : K} {h : K⟦X⟧}
    (hh : constantCoeff h = 1) (heq : C b * X ^ n = X ^ E * h) : E = n ∧ b = 1 := by
  have h1 := congrArg (coeff E) heq
  rw [coeff_C_mul_X_pow, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    coeff_zero_eq_constantCoeff_apply, hh] at h1
  split_ifs at h1 with hE
  · exact ⟨hE, h1⟩
  · exact absurd h1 zero_ne_one

/- English proof (translation)
Establish `hG' : (∀ s : T, π s = 0 → ∃ ε : K, ‖ε‖ = 1 ∧ G s = C ε * X) ∧ (∀ s : T, π s ≠ 0 → constantCoeff (G s) ≠ 0) ∧ _` using `hG`. Take `⟨c, hc_eq⟩ : ∃ c, constantCoeff (G t) = c` from `⟨_, rfl⟩`. Establish `hc : c ≠ 0` using `hc_eq ▸ hG'.2.1 t ht`. Rewrite using `[hc_eq]`. Establish `hfin : IsOfFinAddOrder (π t)` using `isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨N, hN, hNt⟩`.

Establish `hpos : 0 < addOrderOf (π t)` using `hfin.addOrderOf_pos`. Take `⟨k, hk⟩ : ∃ k, addOrderOf (π t) = k + 1` from `⟨addOrderOf (π t) - 1, by omega⟩`. Establish `hne : ∀ j : ℕ, 1 ≤ j → j ≤ k → π (j • t) ≠ 0`. Introduce `j hj1 hjk`. Rewrite using `[map_nsmul]`.

Conclude with `nsmul_ne_zero_of_lt_addOrderOf (by omega) (by omega)`. Take `⟨ε, hε1, hε⟩` from `hG'.1 0 (map_zero π)`. Take `⟨ε', hε'1, hε'⟩` from `hG'.1 ((k + 1) • t) (by rw [map_nsmul, ← hk]; exact addOrderOf_nsmul_eq_zero _)`. Establish `hP` using `transPower K W T π G hG ε hε t k hne`. Establish `hF : ∀ j ∈ Finset.range k, ∃ e, UnitAt e (C (px W (π t)) - xT W (π ((j + 1) • t)))`.

Introduce `j hj`. Rewrite `hj` using `[Finset.mem_range]`. Conclude with `fac_exists facShape W hW π hI ((j + 1) • t) t (hne (j + 1) (by omega) (by omega)) ht`. Take `⟨E, a, V, ha, hV, hPi⟩` from `exists_unitAt_prod_pow (Finset.range k) (fun j => C (px W (π t)) - xT W (π ((j + 1) • t))) (fun j => k - j) hF`. Establish `hV' : constantCoeff V = 1 ∧ IntS V` using `hV`.

Establish `ha0 : a ≠ 0` using `fun h0 => by simp [h0] at ha`. Use `set m := ∑ j ∈ Finset.range k, (k - j) with hm`. Establish `hprod : ∏ j ∈ Finset.range k, (C (c ^ 2) * (C (px W (π t)) - xT W (π ((j + 1) • t)))) ^ (k - j) = C ((c ^ 2) ^ m) * ∏ j ∈ Finset.range k, (C (px W (π t)) - xT W (π ((j + 1) • t))) ^ (k - j)`. Rewrite using `[← Finset.prod_pow_eq_pow_sum, map_prod, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun j _ => by simp only [mul_pow, map_pow]`.

Establish `hGt : G t = C c * (C c⁻¹ * G t)`. Rewrite using `[← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]`. Establish `hf0 : constantCoeff (C c⁻¹ * G t) = 1`. Rewrite using `[map_mul, constantCoeff_C, hc_eq, inv_mul_cancel₀ hc]`. Rewrite `hP` using `[hc_eq, hprod, hPi, hε', hGt]`.

Establish `hmain : C ε ^ k * C ε' * X ^ (k + 1) = C c ^ (k + 1) * (C c ^ 2) ^ m * C a * (X ^ E * ((C c⁻¹ * G t) ^ (k + 1) * V))`. Simplify using `only [map_pow] at hP`. Take the linear combination `hP`. Establish `hD : c ^ (k + 1) * (c ^ 2) ^ m * a ≠ 0`. Conclude with `mul_ne_zero (mul_ne_zero (pow_ne_zero _ hc) (pow_ne_zero _ (pow_ne_zero _ hc))) ha0`.

Establish `hh : constantCoeff ((C c⁻¹ * G t) ^ (k + 1) * V) = 1`. Rewrite using `[map_mul, map_pow, hf0, hV'.1, one_pow, one_mul]`. Establish `key : C ((c ^ (k + 1) * (c ^ 2) ^ m * a)⁻¹ * (ε ^ k * ε')) * X ^ (k + 1) = X ^ E * ((C c⁻¹ * G t) ^ (k + 1) * V)`. Establish `hD1 : C (c ^ (k + 1) * (c ^ 2) ^ m * a)⁻¹ * C (c ^ (k + 1) * (c ^ 2) ^ m * a) = (1 : K⟦X⟧)`. Rewrite using `[← map_mul, inv_mul_cancel₀ hD, map_one]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [map_mul, map_pow]`. Apply the tactic sequence `try ring`. Use `_ = C (c ^ (k + 1) * (c ^ 2) ^ m * a)⁻¹ * (C (c ^ (k + 1) * (c ^ 2) ^ m * a) * (X ^ E * ((C c⁻¹ * G t) ^ (k + 1) * V))) := by`. Rewrite using `[hmain]`.

Simplify using `only [map_mul, map_pow]`. Apply the tactic sequence `try ring`. Use `_ = X ^ E * ((C c⁻¹ * G t) ^ (k + 1) * V) := by rw [← mul_assoc, hD1, one_mul]`. Take `⟨hE, hb⟩` from `eq_and_eq_one_of_C_mul_X_pow_eq hh key`. Substitute `hE` using the available equality.

Establish `hDeq : c ^ (k + 1) * (c ^ 2) ^ m * a = ε ^ k * ε'` using `(inv_mul_eq_one₀ hD).1 hb`. Establish `hcn : ‖c‖ = 1`. Establish `h1 : ‖c ^ (k + 1) * (c ^ 2) ^ m * a‖ = 1`. Rewrite using `[hDeq, norm_mul, norm_pow, hε1, hε'1, one_pow, one_mul]`. Rewrite `h1` using `[norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, ha, mul_one, ← pow_mul, ← pow_add]`.

Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg c) (by omega)).1 h1`. Use `⟨hcn, ?_⟩` and prove the remaining obligations. Establish `hh1 : (C c⁻¹ * G t) ^ (k + 1) * V = 1`. Apply `mul_left_cancel₀ (pow_ne_zero (k + 1) (X_ne_zero : (X : K⟦X⟧) ≠ 0))` to reduce the goal to its premises. Rewrite using `[mul_one, ← key, hb, map_one, one_mul]`.

Take `⟨-, -, -, -, -, -, -, hpowU, hinvU, -⟩` from `intRules K`. Establish `hU : OneUnit ((C c⁻¹ * G t) ^ (k + 1))` using `hinvU V _ hV (by rw [mul_comm]; exact hh1)`. Take `⟨q, hq⟩ : k + 1 ∣ N` from `hk ▸ addOrderOf_dvd_of_nsmul_eq_zero hNt`. Rewrite using `[hq, pow_mul]`. Conclude with `hpowU _ q hU`.
-/
theorem transPow {K : Type} [NormedField K] [IsUltrametricDist K] [DecidableEq K]
    (W : WeierstrassCurve K) (hW : IntCurve W) {T : Type} [AddCommGroup T]
    (π : T →+ W.toAffine.Point) (G : T → K⟦X⟧) (hI : IntPts W π) (hG : IsTransSys W π G)
    (t : T) (N : ℕ) (hN : 0 < N) (hNt : N • π t = 0) (ht : π t ≠ 0) :
    ‖constantCoeff (G t)‖ = 1 ∧ OneUnit ((C (constantCoeff (G t))⁻¹ * G t) ^ N) := by
  have hG' : (∀ s : T, π s = 0 → ∃ ε : K, ‖ε‖ = 1 ∧ G s = C ε * X) ∧
      (∀ s : T, π s ≠ 0 → constantCoeff (G s) ≠ 0) ∧ _ := hG
  obtain ⟨c, hc_eq⟩ : ∃ c, constantCoeff (G t) = c := ⟨_, rfl⟩
  have hc : c ≠ 0 := hc_eq ▸ hG'.2.1 t ht
  rw [hc_eq]
  have hfin : IsOfFinAddOrder (π t) := isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨N, hN, hNt⟩
  have hpos : 0 < addOrderOf (π t) := hfin.addOrderOf_pos
  obtain ⟨k, hk⟩ : ∃ k, addOrderOf (π t) = k + 1 := ⟨addOrderOf (π t) - 1, by omega⟩
  have hne : ∀ j : ℕ, 1 ≤ j → j ≤ k → π (j • t) ≠ 0 := by
    intro j hj1 hjk
    rw [map_nsmul]
    exact nsmul_ne_zero_of_lt_addOrderOf (by omega) (by omega)
  obtain ⟨ε, hε1, hε⟩ := hG'.1 0 (map_zero π)
  obtain ⟨ε', hε'1, hε'⟩ := hG'.1 ((k + 1) • t) (by rw [map_nsmul, ← hk]; exact addOrderOf_nsmul_eq_zero _)
  have hP := transPower K W T π G hG ε hε t k hne
  have hF : ∀ j ∈ Finset.range k, ∃ e, UnitAt e (C (px W (π t)) - xT W (π ((j + 1) • t))) := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact fac_exists facShape W hW π hI ((j + 1) • t) t (hne (j + 1) (by omega) (by omega)) ht
  obtain ⟨E, a, V, ha, hV, hPi⟩ := exists_unitAt_prod_pow (Finset.range k)
    (fun j => C (px W (π t)) - xT W (π ((j + 1) • t))) (fun j => k - j) hF
  have hV' : constantCoeff V = 1 ∧ IntS V := hV
  have ha0 : a ≠ 0 := fun h0 => by simp [h0] at ha
  set m := ∑ j ∈ Finset.range k, (k - j) with hm
  have hprod : ∏ j ∈ Finset.range k, (C (c ^ 2) * (C (px W (π t)) - xT W (π ((j + 1) • t)))) ^ (k - j) =
      C ((c ^ 2) ^ m) * ∏ j ∈ Finset.range k, (C (px W (π t)) - xT W (π ((j + 1) • t))) ^ (k - j) := by
    rw [← Finset.prod_pow_eq_pow_sum, map_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by simp only [mul_pow, map_pow]
  have hGt : G t = C c * (C c⁻¹ * G t) := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
  have hf0 : constantCoeff (C c⁻¹ * G t) = 1 := by
    rw [map_mul, constantCoeff_C, hc_eq, inv_mul_cancel₀ hc]
  rw [hc_eq, hprod, hPi, hε', hGt] at hP
  have hmain : C ε ^ k * C ε' * X ^ (k + 1) =
      C c ^ (k + 1) * (C c ^ 2) ^ m * C a * (X ^ E * ((C c⁻¹ * G t) ^ (k + 1) * V)) := by
    simp only [map_pow] at hP
    linear_combination hP
  have hD : c ^ (k + 1) * (c ^ 2) ^ m * a ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hc) (pow_ne_zero _ (pow_ne_zero _ hc))) ha0
  have hh : constantCoeff ((C c⁻¹ * G t) ^ (k + 1) * V) = 1 := by
    rw [map_mul, map_pow, hf0, hV'.1, one_pow, one_mul]
  have key : C ((c ^ (k + 1) * (c ^ 2) ^ m * a)⁻¹ * (ε ^ k * ε')) * X ^ (k + 1) =
      X ^ E * ((C c⁻¹ * G t) ^ (k + 1) * V) := by
    have hD1 : C (c ^ (k + 1) * (c ^ 2) ^ m * a)⁻¹ * C (c ^ (k + 1) * (c ^ 2) ^ m * a) = (1 : K⟦X⟧) := by
      rw [← map_mul, inv_mul_cancel₀ hD, map_one]
    calc C ((c ^ (k + 1) * (c ^ 2) ^ m * a)⁻¹ * (ε ^ k * ε')) * X ^ (k + 1)
        = C (c ^ (k + 1) * (c ^ 2) ^ m * a)⁻¹ * (C ε ^ k * C ε' * X ^ (k + 1)) := by
          simp only [map_mul, map_pow]; try ring
      _ = C (c ^ (k + 1) * (c ^ 2) ^ m * a)⁻¹ * (C (c ^ (k + 1) * (c ^ 2) ^ m * a) *
            (X ^ E * ((C c⁻¹ * G t) ^ (k + 1) * V))) := by
          rw [hmain]; simp only [map_mul, map_pow]; try ring
      _ = X ^ E * ((C c⁻¹ * G t) ^ (k + 1) * V) := by rw [← mul_assoc, hD1, one_mul]
  obtain ⟨hE, hb⟩ := eq_and_eq_one_of_C_mul_X_pow_eq hh key
  subst hE
  have hDeq : c ^ (k + 1) * (c ^ 2) ^ m * a = ε ^ k * ε' := (inv_mul_eq_one₀ hD).1 hb
  have hcn : ‖c‖ = 1 := by
    have h1 : ‖c ^ (k + 1) * (c ^ 2) ^ m * a‖ = 1 := by
      rw [hDeq, norm_mul, norm_pow, hε1, hε'1, one_pow, one_mul]
    rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, ha, mul_one, ← pow_mul, ← pow_add] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) (by omega)).1 h1
  refine ⟨hcn, ?_⟩
  have hh1 : (C c⁻¹ * G t) ^ (k + 1) * V = 1 := by
    apply mul_left_cancel₀ (pow_ne_zero (k + 1) (X_ne_zero : (X : K⟦X⟧) ≠ 0))
    rw [mul_one, ← key, hb, map_one, one_mul]
  obtain ⟨-, -, -, -, -, -, -, hpowU, hinvU, -⟩ := intRules K
  have hU : OneUnit ((C c⁻¹ * G t) ^ (k + 1)) := hinvU V _ hV (by rw [mul_comm]; exact hh1)
  obtain ⟨q, hq⟩ : k + 1 ∣ N := hk ▸ addOrderOf_dvd_of_nsmul_eq_zero hNt
  rw [hq, pow_mul]
  exact hpowU _ q hU

end EtPowerP

open Formalism.L2.Th1.E EtPowerP

open Classical in

/- English proof (translation)
Introduce `dK L hsq hd hCM p _ ι hp2 hpd hW α t M hα hαu hαt ht hM hMt`. Establish `hZ` using `ptOfZero p L ι`. Set `π₀` to `Tor.piOf p L ι ptOfAdd`. Set `π` to `π₀.comp (AddSubgroup.zmultiples t).subtype`. Set `G : AddSubgroup.zmultiples t → PowerSeries ℂ_[p]` to `fun s => gT p L ι (s : ℂ)`.

Establish `hS : IsTransSys (curveL p L ι) π₀ (gT p L ι)` using `analyticSys p L ι π₀ (fun _ => rfl)`. Establish `hS' : (∀ s : ℂ, π₀ s = 0 → ∃ ε : ℂ_[p], ‖ε‖ = 1 ∧ gT p L ι s = PowerSeries.C ε * PowerSeries.X) ∧ (∀ s : ℂ, π₀ s ≠ 0 → PowerSeries.constantCoeff (gT p L ι s) ≠ 0) ∧ ∀ P Q : ℂ, π₀ Q ≠ 0 → PowerSeries.X ^ 2 * (gT p L ι (P + Q) * gT p L ι (P - Q)) = PowerSeries.C (PowerSeries.consta …` using `hS`. Establish `hGs : IsTransSys (curveL p L ι) π G`. Use `⟨fun s hs => hS'.1 s hs, fun s hs => hS'.2.1 s hs, fun P Q hQ => ?_⟩` and prove the remaining obligations. Use `hS'.2.2 P Q hQ` as an intermediate fact.

Simplify `this` using `[G, π]`. Establish `hIs : IntPts (curveL p L ι) π`. Introduce `s hs`. Take `⟨s, j, rfl⟩` from `s`. Establish `hs' : ptOf p L ι ((j • t : ℂ)) ≠ 0` using `hs`.

Establish `hnl : (j • t : ℂ) ∉ L.lattice` using `fun hm => hs' ((hZ _).2 hm)`. Establish `hαs : α * (j • t : ℂ) ∈ L.lattice`. Rewrite using `[zsmul_eq_mul, mul_left_comm]`. Conclude with `Tor.int_mul_mem L j hαt`. Conclude with `h dK L hsq hd hCM p ι hp2 hpd hW α (j • t) hα hαu hαs hnl`.

Establish `ht0 : ptOf p L ι t ≠ 0` using `fun h0 => ht ((hZ t).1 h0)`. Establish `hMt0 : M • π ⟨t, AddSubgroup.mem_zmultiples t⟩ = 0`. Express the relevant statement in the definitionally equal form `M • ptOf p L ι t = 0`. Rewrite using `[Tor.nsmul_ptOf p L ι ptOfAdd ptOfZero t M]`. Conclude with `(hZ _).2 hMt`.

Take `⟨hn, hV⟩` from `transPow (curveL p L ι) hW π G hIs hGs ⟨t, AddSubgroup.mem_zmultiples t⟩ M hM hMt0 ht0`. Establish `hcc : PowerSeries.constantCoeff (G ⟨t, AddSubgroup.mem_zmultiples t⟩) = ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L) 0)` using `Tor.cc_gT p L ι t`. Rewrite `hn`, `hV` using `[hcc]`. Use `⟨hn, _, hV, ?_⟩` and prove the remaining obligations. Establish `hc0 : ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L) 0) ≠ 0`.

Introduce `h0`. Rewrite `hn` using `[h0, norm_zero]`. Conclude with `zero_ne_one hn`. Generalize the expression as in `ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L) 0) = c at hc0 ⊢`. Express the relevant statement in the definitionally equal form `gT p L ι t ^ M = PowerSeries.C (c ^ M) * (PowerSeries.C c⁻¹ * gT p L ι t) ^ M`.

Rewrite using `[mul_pow, ← mul_assoc, ← map_pow PowerSeries.C, ← map_mul, ← mul_pow, mul_inv_cancel₀ hc0, one_pow, map_one, one_mul]`.
-/
theorem etPower_of (h : UnitKerInt) : EtPower := by
  intro dK L hsq hd hCM p _ ι hp2 hpd hW α t M hα hαu hαt ht hM hMt
  classical
  have hZ := ptOfZero p L ι
  let π₀ := Tor.piOf p L ι ptOfAdd
  let π := π₀.comp (AddSubgroup.zmultiples t).subtype
  let G : AddSubgroup.zmultiples t → PowerSeries ℂ_[p] := fun s => gT p L ι (s : ℂ)
  have hS : IsTransSys (curveL p L ι) π₀ (gT p L ι) := analyticSys p L ι π₀ (fun _ => rfl)
  have hS' : (∀ s : ℂ, π₀ s = 0 → ∃ ε : ℂ_[p], ‖ε‖ = 1 ∧ gT p L ι s = PowerSeries.C ε * PowerSeries.X) ∧
      (∀ s : ℂ, π₀ s ≠ 0 → PowerSeries.constantCoeff (gT p L ι s) ≠ 0) ∧
      ∀ P Q : ℂ, π₀ Q ≠ 0 →
        PowerSeries.X ^ 2 * (gT p L ι (P + Q) * gT p L ι (P - Q)) =
          PowerSeries.C (PowerSeries.constantCoeff (gT p L ι Q) ^ 2) *
            (PowerSeries.C (px (curveL p L ι) (π₀ Q)) * PowerSeries.X ^ 2 - x2 (curveL p L ι) (π₀ P)) *
            gT p L ι P ^ 2 := hS
  have hGs : IsTransSys (curveL p L ι) π G := by
    refine ⟨fun s hs => hS'.1 s hs, fun s hs => hS'.2.1 s hs, fun P Q hQ => ?_⟩
    have := hS'.2.2 P Q hQ
    simpa [G, π] using this
  have hIs : IntPts (curveL p L ι) π := by
    intro s hs
    obtain ⟨s, j, rfl⟩ := s
    have hs' : ptOf p L ι ((j • t : ℂ)) ≠ 0 := hs
    have hnl : (j • t : ℂ) ∉ L.lattice := fun hm => hs' ((hZ _).2 hm)
    have hαs : α * (j • t : ℂ) ∈ L.lattice := by
      rw [zsmul_eq_mul, mul_left_comm]
      exact Tor.int_mul_mem L j hαt
    exact h dK L hsq hd hCM p ι hp2 hpd hW α (j • t) hα hαu hαs hnl
  have ht0 : ptOf p L ι t ≠ 0 := fun h0 => ht ((hZ t).1 h0)
  have hMt0 : M • π ⟨t, AddSubgroup.mem_zmultiples t⟩ = 0 := by
    change M • ptOf p L ι t = 0
    rw [Tor.nsmul_ptOf p L ι ptOfAdd ptOfZero t M]
    exact (hZ _).2 hMt
  obtain ⟨hn, hV⟩ := transPow (curveL p L ι) hW π G hIs hGs ⟨t, AddSubgroup.mem_zmultiples t⟩ M hM hMt0 ht0
  have hcc : PowerSeries.constantCoeff (G ⟨t, AddSubgroup.mem_zmultiples t⟩) =
      ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L) 0) := Tor.cc_gT p L ι t
  rw [hcc] at hn hV
  refine ⟨hn, _, hV, ?_⟩
  have hc0 : ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L) 0) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hn; exact zero_ne_one hn
  generalize ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L) 0) = c at hc0 ⊢
  change gT p L ι t ^ M = PowerSeries.C (c ^ M) * (PowerSeries.C c⁻¹ * gT p L ι t) ^ M
  rw [mul_pow, ← mul_assoc, ← map_pow PowerSeries.C, ← map_mul, ← mul_pow, mul_inv_cancel₀ hc0, one_pow,
    map_one, one_mul]

end Formalism.L2.AlgTh

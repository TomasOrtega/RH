import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetOpIntegral
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastTwoStepsGuarded

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.TopStep GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator GlobalTheory.LastSteps

noncomputable section

namespace GlobalTheory.ColPeriod.TopTwist

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Establish `h1` using `one_lt_pow₀ (not_le.1 hn) hk`. Rewrite `h1` using `[← map_pow, h, map_one]`. Conclude with `lt_irrefl _ h1`.
-/
theorem valuation_le_one_of_pow {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {x : K} {k : ℕ}
    (hk : k ≠ 0) (h : x ^ k = 1) : w.valuation K x ≤ 1 := by
  by_contra hn
  have h1 := one_lt_pow₀ (not_le.1 hn) hk
  rw [← map_pow, h, map_one] at h1
  exact lt_irrefl _ h1

section Phi

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

omit [StarRing E] in
/- English proof (translation)
Introduce `h` and use `(qOf_ne_zero (P := P)) (by rw [h, Nat.cast_zero])`.
-/
theorem qOf_nat_ne_zero : qOf P ≠ 0 := fun h => (qOf_ne_zero (P := P)) (by rw [h, Nat.cast_zero])

omit [StarRing E] in
/- English proof (translation)
Introduce `h`. Establish `h0` using `qOf_nat_ne_zero (P := P)`. Establish `h1 : qOf P = 1` using `by omega`. Establish `h2` using `qOf_mem (P := P)`. Rewrite `h2` using `[h1, Nat.cast_one]`.

Conclude with `P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)`.
-/
theorem qOf_pred_ne_zero : qOf P - 1 ≠ 0 := by
  intro h
  have h0 := qOf_nat_ne_zero (P := P)
  have h1 : qOf P = 1 := by omega
  have h2 := qOf_mem (P := P)
  rw [h1, Nat.cast_one] at h2
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)

omit [StarRing E] in
/- English proof (translation)
Unfold `LocE.PhiQ LocE.unitV`. Use `split_ifs`. Conclude with `valuation_le_one_of_pow w qOf_pred_ne_zero (char_pow ξ _)`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem valuation_PhiQ [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (q k₀ r c' n' c n : ℕ)
    (x : HomE E (n' + c') (n + c)) : w.valuation K (LocE.PhiQ q ξ k₀ r c' n' c n x) ≤ 1 := by
  unfold LocE.PhiQ LocE.unitV
  split_ifs
  · exact valuation_le_one_of_pow w qOf_pred_ne_zero (char_pow ξ _)
  · simp
  · simp

/- English proof (translation)
Establish `hZ` using `entB_int k₀ hz`. Unfold `LocE.PhiQ`. Rewrite using `[entB_add_smul]`. Generalize the expression as in `LocE.entB (qOf P) k₀ c' n' c n 0 0 z = Z at hZ`. Generalize the expression as in `LocE.entB (qOf P) k₀ c' n' c n 0 0 x = M`.

Establish `e1` using `fun a p p' => intAt_add_q (a := a) (hZ p p')`. Establish `e2` using `fun a p p' => intAt_add_q_div (a := a) (hZ p p')`. Use `ite_eq_ite_zero (by simp only [e1, e2]) fun h => ?_` and prove the remaining obligations. Conclude with `unitV_congr _ (redP_det_add_q (fun s s' => h.1 _ _ (by have := s.2; omega) (by have := s'.2; omega)) fun _ _ => hZ _ _)`.
-/
theorem PhiQ_add (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ r c' n' c n : ℕ} (h1 : r ≤ n' + c') (h2 : r ≤ n + c)
    (x z : HomE E (n' + c') (n + c)) (hz : z ∈ homS (LocE.lamY P (qOf P) n' c' 0) (LocE.lamY P (qOf P) n c 0)) :
    LocE.PhiQ (qOf P) ξ k₀ r c' n' c n (x + (qOf P : E) • z) = LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x := by
  have hZ := entB_int k₀ hz
  unfold LocE.PhiQ
  rw [entB_add_smul]
  generalize LocE.entB (qOf P) k₀ c' n' c n 0 0 z = Z at hZ
  generalize LocE.entB (qOf P) k₀ c' n' c n 0 0 x = M
  have e1 := fun a p p' => intAt_add_q (a := a) (hZ p p')
  have e2 := fun a p p' => intAt_add_q_div (a := a) (hZ p p')
  refine ite_eq_ite_zero (by simp only [e1, e2]) fun h => ?_
  exact unitV_congr _ (redP_det_add_q (fun s s' => h.1 _ _ (by have := s.2; omega) (by have := s'.2; omega)) fun _ _ => hZ _ _)

end Phi

section Psi

variable {X : Fields} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {c : LocCst X SB}

/- English proof (translation)
Rewrite using `[hc.psi_add P a b ha ((intAt_pow (intAt_nat _) _).mul hb), hc.psi_int P b hb, mul_one]`.
-/
theorem psi_add_int' (hc : c.Ok) (P : SB) {a b : X.E} (ha : IntAt P.1 ((qOf P.1 : X.E) ^ c.D P * a)) (hb : IntAt P.1 b) :
    c.psi P (a + b) = c.psi P a := by
  rw [hc.psi_add P a b ha ((intAt_pow (intAt_nat _) _).mul hb), hc.psi_int P b hb, mul_one]

/- English proof (translation)
Establish `h : ∀ k : ℕ, c.psi P a ^ k = c.psi P ((k : X.E) * a)` using `fun k => by`. Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero, Nat.cast_zero, zero_mul, hc.psi_int P 0 intAt_zero]`. Consider the case `succ k ih`. Rewrite using `[pow_succ, ih, Nat.cast_succ, add_mul, one_mul, hc.psi_add P _ _ _ ha]`.

Rewrite using `[mul_left_comm]`. Conclude with `(intAt_nat _).mul ha`. Rewrite using `[h, Nat.cast_pow, hc.psi_int P _ ha]`.
-/
theorem psi_pow (hc : c.Ok) (P : SB) {a : X.E} (ha : IntAt P.1 ((qOf P.1 : X.E) ^ c.D P * a)) :
    c.psi P a ^ (qOf P.1 ^ c.D P) = 1 := by
  have h : ∀ k : ℕ, c.psi P a ^ k = c.psi P ((k : X.E) * a) := fun k => by
    induction k with
    | zero => rw [pow_zero, Nat.cast_zero, zero_mul, hc.psi_int P 0 intAt_zero]
    | succ k ih =>
      rw [pow_succ, ih, Nat.cast_succ, add_mul, one_mul, hc.psi_add P _ _ _ ha]
      rw [mul_left_comm]
      exact (intAt_nat _).mul ha
  rw [h, Nat.cast_pow, hc.psi_int P _ ha]

end Psi

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

/- English proof (translation)
Establish `he : IntAt P.1 (epsSg : X.E)` using `by simpa [epsSg] using intAt_neg intAt_one`. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le hD`. Establish `h1` using `(inDual_iff (((qOf P.1 : X.E) ^ cst.M) • η)).2 h _ hy`. Rewrite `h1` using `[map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]`. Use `(he.mul (intAt_pow (intAt_nat (qOf P.1)) k)).mul h1 using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[hk]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem intAt_arg (P : rowSG Pr sel mu) (hD : 2 * cst.M ≤ cst.D P) {n : ℕ} {y : Sp X.E n}
    (hy : ((qOf P.1 : X.E) ^ cst.M) • y ∈ stdAt X.E n P.1) (η : Sp X.E n →ₗ[X.E] X.E)
    (h : ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * η (Pi.single i 1))) :
    IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * ((epsSg : X.E) * η y)) := by
  have he : IntAt P.1 (epsSg : X.E) := by simpa [epsSg] using intAt_neg intAt_one
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hD
  have h1 := (inDual_iff (((qOf P.1 : X.E) ^ cst.M) • η)).2 h _ hy
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h1
  convert (he.mul (intAt_pow (intAt_nat (qOf P.1)) k)).mul h1 using 1
  rw [hk]
  ring

/- English proof (translation)
Unfold `ftY`. Rewrite using `[if_neg hP]`. Use `split_ifs with h`. Establish `h2 : w.valuation X.K (algebraMap (𝓞 X.K) X.K (qOf P.1 : 𝓞 X.K)) = 1` using `(w.valuation_eq_one_iff_notMem (K := X.K)).2 hw`. Rewrite `h2` using `[map_natCast]`.

Rewrite using `[map_mul, map_inv₀, map_pow, h2, one_pow, inv_one, one_mul]`. Conclude with `valuation_le_one_of_pow w (pow_ne_zero _ qOf_nat_ne_zero) (psi_pow hc P (intAt_arg sel mu cst P hD hy η h))`. Simplify using the standard rewrite rules.
-/
theorem valuation_ftY (hc : cst.Ok) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) (hD : 2 * cst.M ≤ cst.D P)
    (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((qOf P.1 : ℕ) : 𝓞 X.K) ∉ w.asIdeal) {n : ℕ} {y : Sp X.E n}
    (hy : ((qOf P.1 : X.E) ^ cst.M) • y ∈ stdAt X.E n P.1) (η : Sp X.E n →ₗ[X.E] X.E) :
    w.valuation X.K (ftY sel mu cst P η y) ≤ 1 := by
  unfold ftY
  rw [if_neg hP]
  split_ifs with h
  · have h2 : w.valuation X.K (algebraMap (𝓞 X.K) X.K (qOf P.1 : 𝓞 X.K)) = 1 :=
      (w.valuation_eq_one_iff_notMem (K := X.K)).2 hw
    rw [map_natCast] at h2
    rw [map_mul, map_inv₀, map_pow, h2, one_pow, inv_one, one_mul]
    exact valuation_le_one_of_pow w (pow_ne_zero _ qOf_nat_ne_zero) (psi_pow hc P (intAt_arg sel mu cst P hD hy η h))
  · simp

/- English proof (translation)
Establish `he : IntAt P.1 (epsSg : X.E)` using `by simpa [epsSg] using intAt_neg intAt_one`. Establish `hz'` using `(inDual_iff z).1 hz`. Unfold `ftY`. Simplify using `only [if_neg hP]`. Use `ite_eq_ite_zero (forall_congr' fun i => ?_) fun h => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, mul_add]`. Conclude with `intAt_add_iff ((intAt_pow (intAt_nat _) _).mul ((intAt_pow (intAt_nat _) _).mul (hz' i)))`. Rewrite using `[LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, mul_add, psi_add_int' hc P (intAt_arg sel mu cst P hD hy η h)]`. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le hc.M_le_B`. Establish `h1` using `hz _ hy`.

Rewrite `h1` using `[map_smul, smul_eq_mul]`. Use `(he.mul (intAt_pow (intAt_nat (qOf P.1)) k)).mul h1 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hk]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ftY_add (hc : cst.Ok) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) (hD : 2 * cst.M ≤ cst.D P) {n : ℕ} {y : Sp X.E n}
    (hy : ((qOf P.1 : X.E) ^ cst.M) • y ∈ stdAt X.E n P.1) (η z : Sp X.E n →ₗ[X.E] X.E) (hz : InDual P.1 z) :
    ftY sel mu cst P (η + ((qOf P.1 : X.E) ^ cst.B) • z) y = ftY sel mu cst P η y := by
  have he : IntAt P.1 (epsSg : X.E) := by simpa [epsSg] using intAt_neg intAt_one
  have hz' := (inDual_iff z).1 hz
  unfold ftY
  simp only [if_neg hP]
  refine ite_eq_ite_zero (forall_congr' fun i => ?_) fun h => ?_
  · rw [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, mul_add]
    exact intAt_add_iff ((intAt_pow (intAt_nat _) _).mul ((intAt_pow (intAt_nat _) _).mul (hz' i)))
  · rw [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, mul_add,
      psi_add_int' hc P (intAt_arg sel mu cst P hD hy η h)]
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hc.M_le_B
    have h1 := hz _ hy
    rw [map_smul, smul_eq_mul] at h1
    convert (he.mul (intAt_pow (intAt_nat (qOf P.1)) k)).mul h1 using 1
    rw [hk]
    ring

/- English proof (translation)
Unfold `frsF`. Rewrite using `[dif_neg hP]`. Establish `h : ∀ Q : QE sel (mu : Chr X.F X.E X.K), p.fr Q x ∈ localization₂ Q.1.asIdeal p.deco.1.N ↔ x ∈ stdAt X.E (R.N j) Q.1` using `fun Q => p.2 Q x`. Conclude with `h ⟨P.1, (Finset.mem_union.mp P.2).resolve_left hP⟩`.
-/
theorem frsF_mem' {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (x : Sp X.E (R.N j)) : frsF sel mu p P x ∈ localization₂ P.1.asIdeal p.deco.1.N ↔ x ∈ stdAt X.E (R.N j) P.1 := by
  classical
  unfold frsF
  rw [dif_neg hP]
  have h : ∀ Q : QE sel (mu : Chr X.F X.E X.K), p.fr Q x ∈ localization₂ Q.1.asIdeal p.deco.1.N ↔ x ∈ stdAt X.E (R.N j) Q.1 :=
    fun Q => p.2 Q x
  exact h ⟨P.1, (Finset.mem_union.mp P.2).resolve_left hP⟩

/- English proof (translation)
Take `⟨y, hy, hY⟩` from `hY`. Establish `h0 : repY Y ∈ Y` using `Classical.epsilon_spec (p := fun y => y ∈ Y) ⟨y, by rw [hY]; simp⟩`. Generalize the expression as in `repY Y = y' at h0`. Rewrite `h0` using `[hY]`. Establish `h1` using `(mem_locLat _ _ _ _).1 hy P`.

Establish `h2` using `(mem_locLat _ _ _ _).1 h0 P`. Rewrite `h1`, `h2` using `[if_neg hP]`. Simplify using `only [zpow_neg, inv_inv, zpow_natCast] at h1 h2`. Establish `hq : ((qOf P.1 : X.E) ^ cst.M) ≠ 0` using `pow_ne_zero _ qOf_ne_zero`. Establish `hi : IntAt P.1 ((qOf P.1 : X.E) ^ cst.M)` using `intAt_pow (intAt_nat _) _`.

Establish `h3` using `smul_mem_locP hi (smul_mem_locP hi h2)`. Rewrite `h3` using `[smul_inv_smul₀ hq]`. Establish `h4` using `add_mem h3 h1`. Rewrite `h4` using `[← smul_add, sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem pow_smul_repY {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} {Y : Set (Sp X.E n)} (hY : Y ∈ ybSet sel mu cst N)
    (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) : ((qOf P.1 : X.E) ^ cst.M) • repY Y ∈ localization₂ P.1.asIdeal N := by
  obtain ⟨y, hy, hY⟩ := hY
  have h0 : repY Y ∈ Y := Classical.epsilon_spec (p := fun y => y ∈ Y) ⟨y, by rw [hY]; simp⟩
  generalize repY Y = y' at h0
  rw [hY] at h0
  have h1 := (mem_locLat _ _ _ _).1 hy P
  have h2 := (mem_locLat _ _ _ _).1 h0 P
  rw [if_neg hP] at h1 h2
  simp only [zpow_neg, inv_inv, zpow_natCast] at h1 h2
  have hq : ((qOf P.1 : X.E) ^ cst.M) ≠ 0 := pow_ne_zero _ qOf_ne_zero
  have hi : IntAt P.1 ((qOf P.1 : X.E) ^ cst.M) := intAt_pow (intAt_nat _) _
  have h3 := smul_mem_locP hi (smul_mem_locP hi h2)
  rw [smul_inv_smul₀ hq] at h3
  have h4 := add_mem h3 h1
  rwa [← smul_add, sub_add_cancel] at h4

end Chain

/- English proof (translation)
Introduce `X Pr R Ch sel S mu cst L G m2 u hPr hsel hS hL P w hP _ hw p d Y hY`. Establish `hc` using `hL.cst_ok`. Establish `hm` using `hL.hm`. Establish `hD` using `hL.depthQ P hP`. Establish `hu` using `piT_notMem_rowSG sel mu hPr hsel u hS`.

Establish `hy : ((qOf P.1 : X.E) ^ cst.M) • (frsF sel mu p P).symm (repY Y) ∈ stdAt X.E _ P.1`. Rewrite using `[← map_smul, ← frsF_mem' sel mu p P hP, LinearEquiv.apply_symm_apply]`. Conclude with `pow_smul_repY sel mu cst hY P hP`. Use `⟨fun x => ?_, fun x z hz => ?_⟩` and prove the remaining obligations. Unfold `facTop PhiTop`.

Rewrite using `[if_neg hP, map_mul]`. Conclude with `mul_le_one' (valuation_PhiQ w _ _ _ _ _ _ _ _ _) (valuation_ftY sel mu cst hc P hP hD w hw hy _)`. Establish `key : ∀ y ∈ stdAt X.E (R.N (m2 + 1)) P.1, (d.1.liftFr P).symm (prXp X.E R (z (frsF sel mu p P y))) ∈ stdAt X.E (R.N R.m - 1) P.1 ∧ IntAt P.1 (((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ * atNL X.E (R.N R.m) (R.N R.m - 1) (z (frsF sel mu p P y)))` using `fun y hy => by`. Establish `h` using `(mem_tilH (N_m_succ R) d (conj_piT_notMem hPr u) hu P.1 _).1 (hz P.1 (Finset.mem_singleton_self _) _ ((frsF_mem' sel mu p P hP y).2 hy))`. Rewrite using `[atNL_last, ← (liftFr_spec d.2 P).1, LinearEquiv.apply_symm_apply, inv_mul_eq_div]`.

Conclude with `⟨h.1, h.2.div_of_notMem (hu P)⟩`. Establish `h1 : R.r ≤ R.N (m2 + 1) + cOf R (m2 + 1)`. Unfold `Ranks.r Ranks.N cOf`. Rewrite using `[hm, mul_add (m2 + 1)]`. Use linear arithmetic over natural numbers and integers.

Establish `h4 : R.N (m2 + 1) + cOf R (m2 + 1) ≤ R.N R.m - 1 + 0`. Unfold `Ranks.N cOf`. Rewrite using `[hm, show m2 + 2 = m2 + 1 + 1 from rfl, add_mul (m2 + 1)]`. Use linear arithmetic over natural numbers and integers. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le' hc.B_pos`.

Unfold `facTop PhiTop`. Rewrite using `[if_neg hP]`. Use `congr 1`. Establish `e : (d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ (x + ((qOf P.1 : X.E) ^ cst.B) • z) ∘ₗ (frsF sel mu p P).toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) = (d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap ∘ₗ LinearMap …`. Rewrite using `[hk, pow_succ', mul_smul]`.

Simplify using `only [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.comp_assoc]`. Rewrite using `[e]`. Use `PhiQ_add _ h1 (h1.trans h4) _ _ ?_` and prove the remaining obligations. Rewrite using `[comp_funLeft_mem (cOf_top hm), lamY_zero]`. Conclude with `fun y hy => smul_mem_locP (intAt_pow (intAt_nat _) _) (key y hy).1`.

Rewrite using `[LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp ((qOf P.1 : X.E) ^ cst.B), LinearMap.comp_smul]`. Conclude with `ftY_add sel mu cst hc P hP hD hy _ _ fun y hy => (key y hy).2`.
-/
theorem topAtQ : GlobalTheory.ColPeriod.TopAtQ := by
  intro X Pr R Ch sel S mu cst L G m2 u hPr hsel hS hL P w hP _ hw p d Y hY
  have hc := hL.cst_ok
  have hm := hL.hm
  have hD := hL.depthQ P hP
  have hu := piT_notMem_rowSG sel mu hPr hsel u hS
  have hy : ((qOf P.1 : X.E) ^ cst.M) • (frsF sel mu p P).symm (repY Y) ∈ stdAt X.E _ P.1 := by
    rw [← map_smul, ← frsF_mem' sel mu p P hP, LinearEquiv.apply_symm_apply]
    exact pow_smul_repY sel mu cst hY P hP
  refine ⟨fun x => ?_, fun x z hz => ?_⟩
  · unfold facTop PhiTop
    rw [if_neg hP, map_mul]
    exact mul_le_one' (valuation_PhiQ w _ _ _ _ _ _ _ _ _) (valuation_ftY sel mu cst hc P hP hD w hw hy _)
  · have key : ∀ y ∈ stdAt X.E (R.N (m2 + 1)) P.1,
        (d.1.liftFr P).symm (prXp X.E R (z (frsF sel mu p P y))) ∈ stdAt X.E (R.N R.m - 1) P.1 ∧
          IntAt P.1 (((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ * atNL X.E (R.N R.m) (R.N R.m - 1) (z (frsF sel mu p P y))) := fun y hy => by
      have h := (mem_tilH (N_m_succ R) d (conj_piT_notMem hPr u) hu P.1 _).1
        (hz P.1 (Finset.mem_singleton_self _) _ ((frsF_mem' sel mu p P hP y).2 hy))
      rw [atNL_last, ← (liftFr_spec d.2 P).1, LinearEquiv.apply_symm_apply, inv_mul_eq_div]
      exact ⟨h.1, h.2.div_of_notMem (hu P)⟩
    have h1 : R.r ≤ R.N (m2 + 1) + cOf R (m2 + 1) := by
      unfold Ranks.r Ranks.N cOf
      rw [hm, mul_add (m2 + 1)]
      omega
    have h4 : R.N (m2 + 1) + cOf R (m2 + 1) ≤ R.N R.m - 1 + 0 := by
      unfold Ranks.N cOf
      rw [hm, show m2 + 2 = m2 + 1 + 1 from rfl, add_mul (m2 + 1)]
      omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hc.B_pos
    unfold facTop PhiTop
    rw [if_neg hP]
    congr 1
    · have e : (d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ (x + ((qOf P.1 : X.E) ^ cst.B) • z) ∘ₗ
            (frsF sel mu p P).toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) =
          (d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ x ∘ₗ
            (frsF sel mu p P).toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) +
          (qOf P.1 : X.E) • ((((qOf P.1 : X.E) ^ k) • ((d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ z ∘ₗ
            (frsF sel mu p P).toLinearMap)) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) := by
        rw [hk, pow_succ', mul_smul]
        simp only [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.comp_assoc]
      rw [e]
      refine PhiQ_add _ h1 (h1.trans h4) _ _ ?_
      rw [comp_funLeft_mem (cOf_top hm), lamY_zero]
      exact fun y hy => smul_mem_locP (intAt_pow (intAt_nat _) _) (key y hy).1
    · rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp ((qOf P.1 : X.E) ^ cst.B), LinearMap.comp_smul]
      exact ftY_add sel mu cst hc P hP hD hy _ _ fun y hy => (key y hy).2

end GlobalTheory.ColPeriod.TopTwist

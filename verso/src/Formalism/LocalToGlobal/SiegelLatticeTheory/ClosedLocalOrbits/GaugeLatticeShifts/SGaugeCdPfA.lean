import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeCdPfB

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.MainNotions.S.Gauge

/- English proof (translation)
Use `⟨Fintype.card {i // ε i = true}, Fintype.card {i // ¬ ε i = true}, (Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm).trans (Equiv.sumCompl (fun i : Fin n => ε i = true)), fun i => ?_, fun j => ?_⟩` and prove the remaining obligations. Simplify using `only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]`. Conclude with `((Fintype.equivFin {i // ε i = true}).symm i).2`. Simplify using `only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]`. Conclude with `Bool.eq_false_iff.2 ((Fintype.equivFin {i // ¬ ε i = true}).symm j).2`.
-/
theorem exists_split {n : ℕ} (ε : Fin n → Bool) : ∃ (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
    (∀ i, ε (e (Sum.inl i)) = true) ∧ (∀ j, ε (e (Sum.inr j)) = false) := by
  refine ⟨Fintype.card {i // ε i = true}, Fintype.card {i // ¬ ε i = true},
    (Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm).trans
      (Equiv.sumCompl (fun i : Fin n => ε i = true)), fun i => ?_, fun j => ?_⟩
  · simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    exact ((Fintype.equivFin {i // ε i = true}).symm i).2
  · simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    exact Bool.eq_false_iff.2 ((Fintype.equivFin {i // ¬ ε i = true}).symm j).2

/- English proof (translation)
Take `⟨lam, hlam, ht⟩` from `hc`. Take `⟨s, hs, hMs⟩` from `hM`. Establish `hcongr : ∀ᶠ r in 𝓝[>] (0 : ℝ), (D.s.cdScale n ε : ℝ≥0∞) * (Formalism.REAL.muG ε (expC ε '' l1B ε r) / volume (l1B ε r)) = D.cd.cd P Q {g | ∃ X ∈ Formalism.BasicNotions.ballU P Q r, Formalism.BasicNotions.UpqT.mat g = NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)} …` using `by filter_upwards [Ioo_mem_nhdsGT hs] with r hr`. Rewrite using `[hL h1 h2 lam hlam r, ← hS h1 h2 r, ← hcd n ε P Q e h1 h2 _ (hMs r hr.2.le), Measure.smul_apply, smul_eq_mul, mul_div_assoc]`. Conclude with `tendsto_nhds_unique ht ((ENNReal.Tendsto.const_mul hD (Or.inr ENNReal.coe_ne_top)).congr' hcongr)`.
-/
theorem cd_density (D : Formalism.BasicNotions.D7) (hcd : Formalism.BasicNotions.cdScaleTie D) {n P Q : ℕ} (ε : Fin n → Bool)
    (e : Fin P ⊕ Fin Q ≃ Fin n) (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)
    (hD : L1BallDensity ε) (hM : L1BallMeasurable ε) (hL : LamVol ε e) (hS : SetEq ε e)
    {c : ℝ≥0∞} (hc : Formalism.BasicNotions.OmegaDensity (D.cd.cd P Q) c) :
    c = (D.s.cdScale n ε : ℝ≥0∞) * ENNReal.ofReal (gaugeU ε) := by
  obtain ⟨lam, hlam, ht⟩ := hc
  obtain ⟨s, hs, hMs⟩ := hM
  have hcongr : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (D.s.cdScale n ε : ℝ≥0∞) * (Formalism.REAL.muG ε (expC ε '' l1B ε r) / volume (l1B ε r)) =
      D.cd.cd P Q {g | ∃ X ∈ Formalism.BasicNotions.ballU P Q r,
        Formalism.BasicNotions.UpqT.mat g = NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)} /
        lam (Formalism.BasicNotions.ballU P Q r) := by
    filter_upwards [Ioo_mem_nhdsGT hs] with r hr
    rw [hL h1 h2 lam hlam r, ← hS h1 h2 r, ← hcd n ε P Q e h1 h2 _ (hMs r hr.2.le), Measure.smul_apply,
      smul_eq_mul, mul_div_assoc]
  exact tendsto_nhds_unique ht ((ENNReal.Tendsto.const_mul hD (Or.inr ENNReal.coe_ne_top)).congr' hcongr)

/- English proof (translation)
Establish `h1 : ∀ i : Fin m, (fun _ : Fin m => true) (Equiv.sumEmpty (Fin m) (Fin 0) (Sum.inl i)) = true` using `fun _ => rfl`. Establish `h2 : ∀ j : Fin 0, (fun _ : Fin m => true) (Equiv.sumEmpty (Fin m) (Fin 0) (Sum.inr j)) = false` using `fun j => j.elim0`. Establish `h` using `hcd m (fun _ => true) m 0 (Equiv.sumEmpty _ _) h1 h2 univ MeasurableSet.univ`. Rewrite `h` using `[Measure.smul_apply, smul_eq_mul]`. Rewrite using `[h]`.

Establish `hu : {g : Formalism.BasicNotions.UpqT m 0 | ∃ a ∈ (univ : Set (Formalism.REAL.UJ (fun _ : Fin m => true))), umat a = Matrix.reindex (Equiv.sumEmpty (Fin m) (Fin 0)) (Equiv.sumEmpty (Fin m) (Fin 0)) (Formalism.BasicNotions.UpqT.mat g)} = univ`. Use extensionality with `g`. Simplify using `only [mem_ofPred_eq, mem_univ, true_and, iff_true]`. Conclude with `hU h1 h2 g`. Rewrite using `[hu]`.

Use `D.cd.prob m` as an intermediate fact. Conclude with `measure_univ`.
-/
theorem cdScale_mass (D : Formalism.BasicNotions.D7) (hcd : Formalism.BasicNotions.cdScaleTie D) (m : ℕ)
    (hU : UpqIn (fun _ : Fin m => true) (Equiv.sumEmpty (Fin m) (Fin 0))) :
    (D.s.cdScale m (fun _ => true) : ℝ≥0∞) * Formalism.REAL.muG (fun _ : Fin m => true) univ = 1 := by
  have h1 : ∀ i : Fin m, (fun _ : Fin m => true) (Equiv.sumEmpty (Fin m) (Fin 0) (Sum.inl i)) = true :=
    fun _ => rfl
  have h2 : ∀ j : Fin 0, (fun _ : Fin m => true) (Equiv.sumEmpty (Fin m) (Fin 0) (Sum.inr j)) = false :=
    fun j => j.elim0
  have h := hcd m (fun _ => true) m 0 (Equiv.sumEmpty _ _) h1 h2 univ MeasurableSet.univ
  rw [Measure.smul_apply, smul_eq_mul] at h
  rw [h]
  have hu : {g : Formalism.BasicNotions.UpqT m 0 | ∃ a ∈ (univ : Set (Formalism.REAL.UJ (fun _ : Fin m => true))),
      umat a = Matrix.reindex (Equiv.sumEmpty (Fin m) (Fin 0)) (Equiv.sumEmpty (Fin m) (Fin 0))
        (Formalism.BasicNotions.UpqT.mat g)} = univ := by
    ext g
    simp only [mem_ofPred_eq, mem_univ, true_and, iff_true]
    exact hU h1 h2 g
  rw [hu]
  have := D.cd.prob m
  exact measure_univ

/- English proof (translation)
Take `⟨P, Q, e, h1, h2⟩` from `exists_split ε`. Take `⟨c, -, -, hcPQ, hcN⟩` from `D.cd.trick P Q`. Establish `hA` using `cd_density D hcd ε e h1 h2 (hD ε) (hM ε) (hL ε e) (hS ε e) hcPQ`. Establish `hn : P + Q = n` using `by simpa using Fintype.card_congr e`. Substitute `hn` using the available equality.

Establish `h1t : ∀ i : Fin (P + Q), (fun _ : Fin (P + Q) => true) (Equiv.sumEmpty (Fin (P + Q)) (Fin 0) (Sum.inl i)) = true` using `fun _ => rfl`. Establish `h2t : ∀ j : Fin 0, (fun _ : Fin (P + Q) => true) (Equiv.sumEmpty (Fin (P + Q)) (Fin 0) (Sum.inr j)) = false` using `fun j => j.elim0`. Establish `hB` using `cd_density D hcd (fun _ : Fin (P + Q) => true) (Equiv.sumEmpty _ _) h1t h2t (hD _) (hM _) (hL _ _) (hS _ _) hcN`. Establish `hmass` using `cdScale_mass D hcd (P + Q) (hU _ _)`. Establish `hu` using `(gauge_density_exists _ ε).2`.

Establish `hv` using `(gauge_density_exists _ (fun _ : Fin (P + Q) => true)).2`. Establish `hab : (D.s.cdScale (P + Q) ε : ℝ) * gaugeU ε = (D.s.cdScale (P + Q) (fun _ => true) : ℝ) * gaugeU (fun _ : Fin (P + Q) => true)`. Establish `h` using `congrArg ENNReal.toReal (hA.symm.trans hB)`. Rewrite `h` using `[ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hu.le, ENNReal.toReal_ofReal hv.le, ENNReal.coe_toReal, ENNReal.coe_toReal]`. Then use the resulting hypothesis. Establish `hb0 : (D.s.cdScale (P + Q) (fun _ => true) : ℝ≥0∞) ≠ 0`.

Introduce `h`. Rewrite `hmass` using `[h, zero_mul]`. Conclude with `zero_ne_one hmass`. Establish `hb : (D.s.cdScale (P + Q) (fun _ => true) : ℝ) ≠ 0` using `NNReal.coe_ne_zero.2 (ENNReal.coe_ne_zero.1 hb0)`. Establish `hMe : Formalism.REAL.muG (fun _ : Fin (P + Q) => true) univ = (D.s.cdScale (P + Q) (fun _ => true) : ℝ≥0∞)⁻¹` using `ENNReal.eq_inv_of_mul_eq_one_left (by rwa [mul_comm])`.

Establish `hMr : (Formalism.REAL.muG (fun _ : Fin (P + Q) => true) univ).toReal = ((D.s.cdScale (P + Q) (fun _ => true) : ℝ))⁻¹`. Rewrite using `[hMe, ENNReal.toReal_inv, ENNReal.coe_toReal]`. Unfold `CdGauge muGauge`. Rewrite using `[Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 hv.le), hMr, hab]`. Clear the denominators using the available nonvanishing facts.
-/
theorem cdGauge_of_parts (D : Formalism.BasicNotions.D7) (hcd : Formalism.BasicNotions.cdScaleTie D)
    (hD : ∀ {m : ℕ} (ε : Fin m → Bool), L1BallDensity ε) (hM : ∀ {m : ℕ} (ε : Fin m → Bool), L1BallMeasurable ε)
    (hL : ∀ {m P Q : ℕ} (ε : Fin m → Bool) (e : Fin P ⊕ Fin Q ≃ Fin m), LamVol ε e)
    (hS : ∀ {m P Q : ℕ} (ε : Fin m → Bool) (e : Fin P ⊕ Fin Q ≃ Fin m), SetEq ε e)
    (hU : ∀ {m P Q : ℕ} (ε : Fin m → Bool) (e : Fin P ⊕ Fin Q ≃ Fin m), UpqIn ε e)
    (n : ℕ) (ε : Fin n → Bool) : CdGauge D n ε := by
  obtain ⟨P, Q, e, h1, h2⟩ := exists_split ε
  obtain ⟨c, -, -, hcPQ, hcN⟩ := D.cd.trick P Q
  have hA := cd_density D hcd ε e h1 h2 (hD ε) (hM ε) (hL ε e) (hS ε e) hcPQ
  have hn : P + Q = n := by simpa using Fintype.card_congr e
  subst hn
  have h1t : ∀ i : Fin (P + Q),
      (fun _ : Fin (P + Q) => true) (Equiv.sumEmpty (Fin (P + Q)) (Fin 0) (Sum.inl i)) = true := fun _ => rfl
  have h2t : ∀ j : Fin 0,
      (fun _ : Fin (P + Q) => true) (Equiv.sumEmpty (Fin (P + Q)) (Fin 0) (Sum.inr j)) = false := fun j => j.elim0
  have hB := cd_density D hcd (fun _ : Fin (P + Q) => true) (Equiv.sumEmpty _ _) h1t h2t (hD _) (hM _) (hL _ _)
    (hS _ _) hcN
  have hmass := cdScale_mass D hcd (P + Q) (hU _ _)
  have hu := (gauge_density_exists _ ε).2
  have hv := (gauge_density_exists _ (fun _ : Fin (P + Q) => true)).2
  have hab : (D.s.cdScale (P + Q) ε : ℝ) * gaugeU ε =
      (D.s.cdScale (P + Q) (fun _ => true) : ℝ) * gaugeU (fun _ : Fin (P + Q) => true) := by
    have h := congrArg ENNReal.toReal (hA.symm.trans hB)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hu.le, ENNReal.toReal_ofReal hv.le,
      ENNReal.coe_toReal, ENNReal.coe_toReal] at h
  have hb0 : (D.s.cdScale (P + Q) (fun _ => true) : ℝ≥0∞) ≠ 0 := by
    intro h; rw [h, zero_mul] at hmass; exact zero_ne_one hmass
  have hb : (D.s.cdScale (P + Q) (fun _ => true) : ℝ) ≠ 0 :=
    NNReal.coe_ne_zero.2 (ENNReal.coe_ne_zero.1 hb0)
  have hMe : Formalism.REAL.muG (fun _ : Fin (P + Q) => true) univ = (D.s.cdScale (P + Q) (fun _ => true) : ℝ≥0∞)⁻¹ :=
    ENNReal.eq_inv_of_mul_eq_one_left (by rwa [mul_comm])
  have hMr : (Formalism.REAL.muG (fun _ : Fin (P + Q) => true) univ).toReal =
      ((D.s.cdScale (P + Q) (fun _ => true) : ℝ))⁻¹ := by
    rw [hMe, ENNReal.toReal_inv, ENNReal.coe_toReal]
  unfold CdGauge muGauge
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 hv.le), hMr, hab]
  field_simp

end Formalism.MainNotions.S.Gauge

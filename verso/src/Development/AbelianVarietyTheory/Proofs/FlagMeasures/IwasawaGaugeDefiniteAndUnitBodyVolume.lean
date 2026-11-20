import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceCmbMulCmbStar
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfSumSqEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeShearedBalls
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

/- English proof (translation)
Introduce `n dN dM dK dL EN EM EK EL hN hM hK hL hR hd`. Take `⟨Q, ι, hQ, hh⟩` from `GlobalTheory.IwConst.Adapted.exists_adapted n dN dM dK dL EN EM EK EL hN hM hK hL hR hd`. Establish `sq0 : ∀ {d : ℕ} (f : Fin d → ℝ), ∑ i, f i ^ 2 ≤ 0 → f = 0`. Introduce `d f hf`. Use function extensionality and compare the values at `i`.

Establish `h0 : ∑ i, f i ^ 2 = 0` using `le_antisymm hf (by positivity)`. Use `(Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (f i))).1 h0 i (Finset.mem_univ i)` as an intermediate fact. Simplify using `using this`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, y, z⟩ hv`.

Take `⟨h1, h2⟩` from `hh x y z`. Establish `a1 : nrm (cmb EN x + cmb EM y + cmb EK z) ≤ 0` using `(le_max_left _ _).trans hv.le`. Establish `a2 : len (crd EL (cmb EK z)) ≤ 0` using `(le_max_right _ _).trans hv.le`. Establish `b1 : Formalism.REAL.hs (cmb EN x + cmb EM y + cmb EK z) = 0`. Rewrite using `[← nrm_sq, le_antisymm a1 (nrm_nonneg _)]`.

Simplify using the standard rewrite rules. Establish `b2 : ∑ i, (Q z).2 i ^ 2 = 0`. Rewrite using `[← h2, ← len_sq, le_antisymm a2 (len_nonneg _)]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[b1]`.

Establish `p1 : 0 ≤ ∑ i, (x i + (Q z).1 i / Real.sqrt 2) ^ 2` using `by positivity`. Establish `p2 : 0 ≤ ∑ i, (y i + ι (Q z).2 i) ^ 2` using `by positivity`. Establish `p3 : 0 ≤ ∑ i, (Q z).1 i ^ 2` using `by positivity`. Rewrite `h1` using `[← Finset.sum_div]`. Establish `hz : z = 0` using `sq0 z (by rw [← hQ z]; linarith)`.

Substitute `hz` using the available equality. Establish `hx : x = 0` using `sq0 x (by`. Simplify using `only [map_zero, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, zero_div, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero] at h1 p1 p2`. Use the proof step `linarith)`. Establish `hy : y = 0` using `sq0 y (by`.

Simplify using `only [map_zero, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, zero_div, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero] at h1 p1 p2`. Use the proof step `linarith)`. Substitute `hx hy` using the available equality. Both sides reduce to the same expression. Establish `hmp` using `GlobalTheory.IwConst.measurePreserving_of_sum_sq_eq dK dN dL hd Q hQ`.

Establish `hmp2 : MeasurePreserving (Prod.map id (Prod.map id Q) : (Fin dN → ℝ) × (Fin dM → ℝ) × (Fin dK → ℝ) → (Fin dN → ℝ) × (Fin dM → ℝ) × ((Fin dN → ℝ) × (Fin dL → ℝ))) volume volume` using `(MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod hmp)`. Rewrite using `[← GlobalTheory.IwConst.Shear.volume_sheared_balls dN dM dL ι, ← hmp2.measure_preimage]`. Use `congr 1`. Use extensionality with `⟨x, y, z⟩`. Take `⟨h1, h2⟩` from `hh x y z`.

Simplify using `only [Set.mem_ofPred_eq, Set.mem_preimage, Prod.map, id, gau, max_le_iff, nrm, len, Real.sqrt_le_one, h1, h2]`. Use `(IsClosed.measurableSet ?_).nullMeasurableSet` and prove the remaining obligations. Establish `hι : Continuous ι` using `ι.continuous_of_finiteDimensional`. Use `IsClosed.and (isClosed_le ?_ continuous_const) (isClosed_le ?_ continuous_const)` and prove the remaining obligations. Use `fun_prop`.

Use `fun_prop`.
-/
theorem gau_definite_and_volume : ∀ (n : ℕ), ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsON EN → IsON EM → IsON EK → IsON EL → LieRel EN EM EK EL → dK = dN + dL → (∀ v, gau EN EM EK EL v = 0 → v = 0) ∧ volume {v | gau EN EM EK EL v ≤ 1} = ENNReal.ofReal ((2 : ℝ) ^ ((dN : ℝ) / 2)) * ballVol (2 * dN + dM) * ballVol dL := by
  intro n dN dM dK dL EN EM EK EL hN hM hK hL hR hd
  obtain ⟨Q, ι, hQ, hh⟩ := GlobalTheory.IwConst.Adapted.exists_adapted n dN dM dK dL EN EM EK EL hN hM hK hL hR hd
  have sq0 : ∀ {d : ℕ} (f : Fin d → ℝ), ∑ i, f i ^ 2 ≤ 0 → f = 0 := by
    intro d f hf
    funext i
    have h0 : ∑ i, f i ^ 2 = 0 := le_antisymm hf (by positivity)
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (f i))).1 h0 i (Finset.mem_univ i)
    simpa using this
  constructor
  · rintro ⟨x, y, z⟩ hv
    obtain ⟨h1, h2⟩ := hh x y z
    have a1 : nrm (cmb EN x + cmb EM y + cmb EK z) ≤ 0 := (le_max_left _ _).trans hv.le
    have a2 : len (crd EL (cmb EK z)) ≤ 0 := (le_max_right _ _).trans hv.le
    have b1 : Formalism.REAL.hs (cmb EN x + cmb EM y + cmb EK z) = 0 := by
      rw [← nrm_sq, le_antisymm a1 (nrm_nonneg _)]; simp
    have b2 : ∑ i, (Q z).2 i ^ 2 = 0 := by
      rw [← h2, ← len_sq, le_antisymm a2 (len_nonneg _)]; simp
    rw [b1] at h1
    have p1 : 0 ≤ ∑ i, (x i + (Q z).1 i / Real.sqrt 2) ^ 2 := by positivity
    have p2 : 0 ≤ ∑ i, (y i + ι (Q z).2 i) ^ 2 := by positivity
    have p3 : 0 ≤ ∑ i, (Q z).1 i ^ 2 := by positivity
    rw [← Finset.sum_div] at h1
    have hz : z = 0 := sq0 z (by rw [← hQ z]; linarith)
    subst hz
    have hx : x = 0 := sq0 x (by
      simp only [map_zero, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, zero_div, add_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero] at h1 p1 p2
      linarith)
    have hy : y = 0 := sq0 y (by
      simp only [map_zero, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, zero_div, add_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero] at h1 p1 p2
      linarith)
    subst hx hy
    rfl
  · have hmp := GlobalTheory.IwConst.measurePreserving_of_sum_sq_eq dK dN dL hd Q hQ
    have hmp2 : MeasurePreserving (Prod.map id (Prod.map id Q) :
        (Fin dN → ℝ) × (Fin dM → ℝ) × (Fin dK → ℝ) →
          (Fin dN → ℝ) × (Fin dM → ℝ) × ((Fin dN → ℝ) × (Fin dL → ℝ))) volume volume :=
      (MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod hmp)
    rw [← GlobalTheory.IwConst.Shear.volume_sheared_balls dN dM dL ι, ← hmp2.measure_preimage]
    · congr 1
      ext ⟨x, y, z⟩
      obtain ⟨h1, h2⟩ := hh x y z
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Prod.map, id, gau, max_le_iff, nrm, len,
        Real.sqrt_le_one, h1, h2]
    · refine (IsClosed.measurableSet ?_).nullMeasurableSet
      have hι : Continuous ι := ι.continuous_of_finiteDimensional
      refine IsClosed.and (isClosed_le ?_ continuous_const) (isClosed_le ?_ continuous_const)
      · fun_prop
      · fun_prop

end GlobalTheory.IwConst

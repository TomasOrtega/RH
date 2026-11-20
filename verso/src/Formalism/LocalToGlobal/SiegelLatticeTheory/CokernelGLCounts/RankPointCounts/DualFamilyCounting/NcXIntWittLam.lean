import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXIntWittSt
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXIntWittOEv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TensTop

noncomputable section

namespace Formalism.L2.SG.Pf.NcX.IntWittPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Filter
open scoped TensorProduct

/- English proof (translation)
Take the linear combination `(q * b * (2 * (B - p * a) + q * b * (Θ ^ 2 + D)) - (q * a - p * b) ^ 2) * h`.
-/
theorem norm_id {S : Type} [CommRing S] (B p q a b D Θ : S) (h : Θ ^ 2 = D) :
    (B - (p - q * Θ) * (a + b * Θ)) * (B - (p + q * Θ) * (a - b * Θ)) =
      (B - p * a + q * b * D) ^ 2 - D * (q * a - p * b) ^ 2 := by
  linear_combination (q * b * (2 * (B - p * a) + q * b * (Θ ^ 2 + D)) - (q * a - p * b) ^ 2) * h

/- English proof (translation)
Take the linear combination `(-q ^ 2) * h`.
-/
theorem norm_one {S : Type} [CommRing S] (p q D Θ : S) (h : Θ ^ 2 = D) :
    (p + q * Θ) * (p - q * Θ) = p ^ 2 - D * q ^ 2 := by
  linear_combination (-q ^ 2) * h

/- English proof (translation)
Set `pp : Fin 4 → R` to `![1, -1, P, -P]`. Set `qq : Fin 4 → R` to `![0, 0, Q, -Q]`. Set `f : Fin 4 → R` to `fun i => (Bt - pp i * a + qq i * b * D) ^ 2 - D * (qq i * a - pp i * b) ^ 2`. Apply the tactic sequence `have ef0 : f 0 = (Bt - a) ^ 2 - D * b ^ 2 := by simp [f, pp, qq] <;> ring`. Apply the tactic sequence `have ef1 : f 1 = (Bt + a) ^ 2 - D * b ^ 2 := by simp [f, pp, qq] <;> ring`.

Apply the tactic sequence `have ef2 : f 2 = (Bt - P * a + Q * b * D) ^ 2 - D * (Q * a - P * b) ^ 2 := by simp [f, pp, qq] <;> ring`. Apply the tactic sequence `have ef3 : f 3 = (Bt + P * a - Q * b * D) ^ 2 - D * (Q * a - P * b) ^ 2 := by simp [f, pp, qq] <;> ring`. Establish `hspanTop : Ideal.span (Set.range f) = ⊤`. Establish `mem : ∀ i, f i ∈ Ideal.span (Set.range f)` using `fun i => Ideal.subset_span ⟨i, rfl⟩`. Establish `ha : a ∈ Ideal.span (Set.range f)`.

Establish `: a = i4 * Bi * (f 1 - f 0)`. Rewrite using `[ef1, ef0]`. Take the linear combination `(-a) * h4 + (-4 * i4 * a) * hB`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_left _ _ (sub_mem (mem 1) (mem 0))`.

Establish `hm : P * a - Q * D * b ∈ Ideal.span (Set.range f)`. Establish `: P * a - Q * D * b = i4 * Bi * (f 3 - f 2)`. Rewrite using `[ef3, ef2]`. Take the linear combination `(-(P * a - Q * D * b)) * h4 + (-4 * i4 * (P * a - Q * D * b)) * hB`. Rewrite using `[this]`.

Conclude with `Ideal.mul_mem_left _ _ (sub_mem (mem 3) (mem 2))`. Establish `hb : b ∈ Ideal.span (Set.range f)`. Establish `: b = K * (P * a - (P * a - Q * D * b))` using `by linear_combination (-b) * hK`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_left _ _ (sub_mem (Ideal.mul_mem_left _ _ ha) hm)`.

Establish `hN : a ^ 2 - D * b ^ 2 ∈ Ideal.span (Set.range f)`. Establish `: a ^ 2 - D * b ^ 2 = a * a - (D * b) * b` using `by ring`. Rewrite using `[this]`. Conclude with `sub_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)`. Establish `hB2 : Bt ^ 2 ∈ Ideal.span (Set.range f)`.

Establish `: Bt ^ 2 = f 0 + (2 * Bt) * a - (a ^ 2 - D * b ^ 2)` using `by rw [ef0]; ring`. Rewrite using `[this]`. Conclude with `sub_mem (add_mem (mem 0) (Ideal.mul_mem_left _ _ ha)) hN`. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `: (1 : R) = Bi ^ 2 * Bt ^ 2` using `by linear_combination (-(Bt * Bi + 1)) * hB`.

Rewrite using `[this]`. Conclude with `Ideal.mul_mem_left _ _ hB2`. Establish `hnorm : ∀ i, pp i ^ 2 - D * qq i ^ 2 = 1`. Apply the tactic sequence `intro i; fin_cases i <;> simp [pp, qq] <;> linear_combination hPQ`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, IsUnit (f i) := by`.

Assume the negation of the conclusion as `H`. Use `push Not at H`. Establish `hle : Ideal.span (Set.range f) ≤ IsLocalRing.maximalIdeal R`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `(IsLocalRing.mem_maximalIdeal _).2 (H i)`. Rewrite `hle` using `[hspanTop]`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.1 hle)`. Use `set L : S := ι (pp i) + ι (qq i) * Θ with hL`. Use `set M : S := ι (pp i) - ι (qq i) * Θ with hM`.

Establish `hsL : s L = M` using `by rw [hL, hM, map_add, map_mul, hsι, hsι, hsΘ]; ring`. Establish `hsM : s M = L` using `by rw [hL, hM, map_sub, map_mul, hsι, hsι, hsΘ]; ring`. Establish `hLM : L * M = 1`. Rewrite using `[hL, hM, norm_one _ _ _ _ hΘ, ← map_pow, ← map_pow, ← map_mul, ← map_sub, hnorm i, map_one]`. Use `set c : S := ι Bt - M * (ι a + ι b * Θ) with hc`.

Use `set sc : S := ι Bt - L * (ι a - ι b * Θ) with hsc`. Establish `hcc : c * sc = ι (f i)`. Rewrite using `[hc, hsc, hL, hM]`. Simplify using `only [f, map_sub, map_add, map_mul, map_pow]`. Conclude with `norm_id _ _ _ _ _ _ _ hΘ`.

Take `⟨u, hu⟩` from `hi`. Establish `hLO : L ∈ O` using `O.add_mem (hιO _) (O.mul_mem (hιO _) hΘO)`. Establish `hMO : M ∈ O` using `O.sub_mem (hιO _) (O.mul_mem (hιO _) hΘO)`. Use `⟨L, hLO, by rw [hsL]; exact hLM, sc * ι ((u⁻¹ : Rˣ) : R), ?_, ?_⟩` and prove the remaining obligations. Conclude with `O.mul_mem (O.sub_mem (hιO _) (O.mul_mem hLO (O.sub_mem (hιO _) (O.mul_mem (hιO _) hΘO)))) (hιO _)`.

Rewrite using `[hsL, ← hc, ← mul_assoc, hcc, ← hu, ← map_mul, Units.mul_inv, map_one]`.
-/
theorem core_loc {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] (ι : R →+* S) (s : S →+* S)
    (O : Subring S) (hιO : ∀ r, ι r ∈ O) (Θ : S) (hΘO : Θ ∈ O) (D Bt P Q a b : R)
    (hΘ : Θ ^ 2 = ι D) (hsΘ : s Θ = -Θ) (hsι : ∀ r, s (ι r) = ι r) (hPQ : P ^ 2 - D * Q ^ 2 = 1)
    (Bi K i4 : R) (hB : Bt * Bi = 1) (hK : Q * D * K = 1) (h4 : (4 : R) * i4 = 1) :
    ∃ lam ∈ O, lam * s lam = 1 ∧ ∃ c' ∈ O, (ι Bt - s lam * (ι a + ι b * Θ)) * c' = 1 := by
  let pp : Fin 4 → R := ![1, -1, P, -P]
  let qq : Fin 4 → R := ![0, 0, Q, -Q]
  let f : Fin 4 → R := fun i => (Bt - pp i * a + qq i * b * D) ^ 2 - D * (qq i * a - pp i * b) ^ 2
  have ef0 : f 0 = (Bt - a) ^ 2 - D * b ^ 2 := by simp [f, pp, qq] <;> ring
  have ef1 : f 1 = (Bt + a) ^ 2 - D * b ^ 2 := by simp [f, pp, qq] <;> ring
  have ef2 : f 2 = (Bt - P * a + Q * b * D) ^ 2 - D * (Q * a - P * b) ^ 2 := by simp [f, pp, qq] <;> ring
  have ef3 : f 3 = (Bt + P * a - Q * b * D) ^ 2 - D * (Q * a - P * b) ^ 2 := by simp [f, pp, qq] <;> ring
  have hspanTop : Ideal.span (Set.range f) = ⊤ := by
    have mem : ∀ i, f i ∈ Ideal.span (Set.range f) := fun i => Ideal.subset_span ⟨i, rfl⟩
    have ha : a ∈ Ideal.span (Set.range f) := by
      have : a = i4 * Bi * (f 1 - f 0) := by
        rw [ef1, ef0]; linear_combination (-a) * h4 + (-4 * i4 * a) * hB
      rw [this]; exact Ideal.mul_mem_left _ _ (sub_mem (mem 1) (mem 0))
    have hm : P * a - Q * D * b ∈ Ideal.span (Set.range f) := by
      have : P * a - Q * D * b = i4 * Bi * (f 3 - f 2) := by
        rw [ef3, ef2]
        linear_combination (-(P * a - Q * D * b)) * h4 + (-4 * i4 * (P * a - Q * D * b)) * hB
      rw [this]; exact Ideal.mul_mem_left _ _ (sub_mem (mem 3) (mem 2))
    have hb : b ∈ Ideal.span (Set.range f) := by
      have : b = K * (P * a - (P * a - Q * D * b)) := by linear_combination (-b) * hK
      rw [this]; exact Ideal.mul_mem_left _ _ (sub_mem (Ideal.mul_mem_left _ _ ha) hm)
    have hN : a ^ 2 - D * b ^ 2 ∈ Ideal.span (Set.range f) := by
      have : a ^ 2 - D * b ^ 2 = a * a - (D * b) * b := by ring
      rw [this]; exact sub_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)
    have hB2 : Bt ^ 2 ∈ Ideal.span (Set.range f) := by
      have : Bt ^ 2 = f 0 + (2 * Bt) * a - (a ^ 2 - D * b ^ 2) := by rw [ef0]; ring
      rw [this]; exact sub_mem (add_mem (mem 0) (Ideal.mul_mem_left _ _ ha)) hN
    rw [Ideal.eq_top_iff_one]
    have : (1 : R) = Bi ^ 2 * Bt ^ 2 := by linear_combination (-(Bt * Bi + 1)) * hB
    rw [this]; exact Ideal.mul_mem_left _ _ hB2
  have hnorm : ∀ i, pp i ^ 2 - D * qq i ^ 2 = 1 := by
    intro i; fin_cases i <;> simp [pp, qq] <;> linear_combination hPQ
  obtain ⟨i, hi⟩ : ∃ i, IsUnit (f i) := by
    by_contra H
    push Not at H
    have hle : Ideal.span (Set.range f) ≤ IsLocalRing.maximalIdeal R := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact (IsLocalRing.mem_maximalIdeal _).2 (H i)
    rw [hspanTop] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.1 hle)
  set L : S := ι (pp i) + ι (qq i) * Θ with hL
  set M : S := ι (pp i) - ι (qq i) * Θ with hM
  have hsL : s L = M := by rw [hL, hM, map_add, map_mul, hsι, hsι, hsΘ]; ring
  have hsM : s M = L := by rw [hL, hM, map_sub, map_mul, hsι, hsι, hsΘ]; ring
  have hLM : L * M = 1 := by
    rw [hL, hM, norm_one _ _ _ _ hΘ, ← map_pow, ← map_pow, ← map_mul, ← map_sub, hnorm i, map_one]
  set c : S := ι Bt - M * (ι a + ι b * Θ) with hc
  set sc : S := ι Bt - L * (ι a - ι b * Θ) with hsc
  have hcc : c * sc = ι (f i) := by
    rw [hc, hsc, hL, hM]
    simp only [f, map_sub, map_add, map_mul, map_pow]
    exact norm_id _ _ _ _ _ _ _ hΘ
  obtain ⟨u, hu⟩ := hi
  have hLO : L ∈ O := O.add_mem (hιO _) (O.mul_mem (hιO _) hΘO)
  have hMO : M ∈ O := O.sub_mem (hιO _) (O.mul_mem (hιO _) hΘO)
  refine ⟨L, hLO, by rw [hsL]; exact hLM, sc * ι ((u⁻¹ : Rˣ) : R), ?_, ?_⟩
  · exact O.mul_mem (O.sub_mem (hιO _) (O.mul_mem hLO (O.sub_mem (hιO _) (O.mul_mem (hιO _) hΘO)))) (hιO _)
  · rw [hsL, ← hc, ← mul_assoc, hcc, ← hu, ← map_mul, Units.mul_inv, map_one]

end Formalism.L2.SG.Pf.NcX.IntWittPf

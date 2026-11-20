import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsCuspHom
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepresentationUnitaryMulContinuous

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev GlobalTheory.RowLev.Inhab
open scoped InnerProductSpace Classical

noncomputable section

namespace GlobalTheory.LevelIdem

section Conv

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end Conv

section Alg

variable {Q : Type} [Group Q] [Fintype Q]

end Alg

section Lev

variable {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q)

/- English proof (translation)
Take `⟨-, -, -, hK, -, -, hKg⟩` from `GlobalTheory.CongTop.adelic_topology I`. Take `⟨hopen, ⟨S, hS⟩, -⟩` from `hKg g hg`. Establish `hsub : I.Kg g ⊆ I.Kset` using `fun x hx => hx.1`. Establish `hfin : μf (I.Kg g) ≠ ⊤` using `((measure_mono hsub).trans_lt hK.measure_lt_top).ne`. Establish `h1 : (1 : I.Gf) ∈ I.Kg g` using `by rw [← hS]; exact S.one_mem`.

Establish `hpos : μf (I.Kg g) ≠ 0` using `(hopen.measure_pos μf ⟨1, h1⟩).ne'`. Conclude with `⟨hfin, Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hpos hfin).ne'⟩`.
-/
theorem vol_ne_zero (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] {g : ℕ} (hg : 1 ≤ g) :
    μf (I.Kg g) ≠ ⊤ ∧ ((μf (I.Kg g)).toReal : ℂ) ≠ 0 := by
  obtain ⟨-, -, -, hK, -, -, hKg⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨hopen, ⟨S, hS⟩, -⟩ := hKg g hg
  have hsub : I.Kg g ⊆ I.Kset := fun x hx => hx.1
  have hfin : μf (I.Kg g) ≠ ⊤ := ((measure_mono hsub).trans_lt hK.measure_lt_top).ne
  have h1 : (1 : I.Gf) ∈ I.Kg g := by rw [← hS]; exact S.one_mem
  have hpos : μf (I.Kg g) ≠ 0 := (hopen.measure_pos μf ⟨1, h1⟩).ne'
  exact ⟨hfin, Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hpos hfin).ne'⟩

/- English proof (translation)
Establish `hmul : ∀ a ∈ I.Kset, ∀ b ∈ I.Kset, a * b ∈ I.Kset` using `fun a ha b hb => (mem_Ksub I _).1 ((Ksub I).mul_mem ((mem_Ksub I a).2 ha) ((mem_Ksub I b).2 hb))`. Establish `hinv : ∀ a ∈ I.Kset, a⁻¹ ∈ I.Kset` using `fun a ha => (mem_Ksub I _).1 ((Ksub I).inv_mem ((mem_Ksub I a).2 ha))`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hk : s⁻¹ * x ∈ I.Kset` using `(show s⁻¹ * x ∈ I.Kset ∧ _ from h).1`.

Establish `hx : x ∈ I.Kset` using `by simpa using hmul s hs _ hk`. Use `⟨hx, ?_⟩` and prove the remaining obligations. Establish `hm` using `ρ.map_mul s hs _ hk`. Rewrite `hm` using `[mul_inv_cancel_left, (ρ.ker _ hk).2 h, mul_one]`. Then use the resulting hypothesis. Introduce and unpack `⟨hx, hxs⟩`.

Establish `hk` using `hmul _ (hinv s hs) x hx`. Use `(ρ.ker _ hk).1 ?_` and prove the remaining obligations. Rewrite using `[ρ.map_mul _ (hinv s hs) x hx, ρ.map_inv hs, hxs, inv_mul_cancel]`.
-/
theorem mem_fibre {s : I.Gf} (hs : s ∈ I.Kset) (x : I.Gf) :
    s⁻¹ * x ∈ I.Kg g ↔ x ∈ I.Kset ∧ ρ.toFun x = ρ.toFun s := by
  have hmul : ∀ a ∈ I.Kset, ∀ b ∈ I.Kset, a * b ∈ I.Kset := fun a ha b hb =>
    (mem_Ksub I _).1 ((Ksub I).mul_mem ((mem_Ksub I a).2 ha) ((mem_Ksub I b).2 hb))
  have hinv : ∀ a ∈ I.Kset, a⁻¹ ∈ I.Kset := fun a ha =>
    (mem_Ksub I _).1 ((Ksub I).inv_mem ((mem_Ksub I a).2 ha))
  constructor
  · intro h
    have hk : s⁻¹ * x ∈ I.Kset := (show s⁻¹ * x ∈ I.Kset ∧ _ from h).1
    have hx : x ∈ I.Kset := by simpa using hmul s hs _ hk
    refine ⟨hx, ?_⟩
    have hm := ρ.map_mul s hs _ hk
    rwa [mul_inv_cancel_left, (ρ.ker _ hk).2 h, mul_one] at hm
  · rintro ⟨hx, hxs⟩
    have hk := hmul _ (hinv s hs) x hx
    refine (ρ.ker _ hk).1 ?_
    rw [ρ.map_mul _ (hinv s hs) x hx, ρ.map_inv hs, hxs, inv_mul_cancel]

/- English proof (translation)
Take `⟨hfin, hvol⟩` from `vol_ne_zero I μf hg`. Establish `hopen` using `((GlobalTheory.CongTop.adelic_topology I).2.2.2.2.2.2 g hg).1`. Establish `hSm : ∀ q, MeasurableSet ((fun y => (s q)⁻¹ * y) ⁻¹' I.Kg g)` using `fun q => (hopen.preimage (continuous_mul_left _)).measurableSet`. Establish `hpt : ∀ x, ρ.lift μf a x * φ x = ∑ q, ((fun y => (s q)⁻¹ * y) ⁻¹' I.Kg g).indicator (fun _ => a.coeff q * φ (s q) / ((μf (I.Kg g)).toReal : ℂ)) x`. Introduce `x`.

Distinguish the cases in `hx : x ∈ I.Kset`. Rewrite using `[ρ.lift_of_mem μf a hx, Finset.sum_eq_single (ρ.toFun x)]`. Establish `hmem : (s (ρ.toFun x))⁻¹ * x ∈ I.Kg g` using `(mem_fibre ρ (hs _).1 x).2 ⟨hx, (hs _).2.symm⟩`. Rewrite using `[Set.indicator_of_mem (show x ∈ (fun y => (s (ρ.toFun x))⁻¹ * y) ⁻¹' I.Kg g from hmem)]`. Establish `hφx : φ x = φ (s (ρ.toFun x))`.

Establish `h'` using `hφ (s (ρ.toFun x)) _ hmem`. Rewrite `h'` using `[mul_inv_cancel_left]`. Then use the resulting hypothesis. Rewrite using `[hφx]`. Expand and normalize the polynomial expressions, which then agree. Introduce `q _ hq`.

Use `Set.indicator_of_notMem (fun hmem => hq ?_) _` and prove the remaining obligations. Conclude with `((((mem_fibre ρ (hs q).1 x).1 hmem).2).trans (hs q).2).symm`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[ρ.lift_of_notMem μf a hx, zero_mul]`.

Use `(Finset.sum_eq_zero fun q _ => Set.indicator_of_notMem (fun hmem => hx ?_) _).symm` and prove the remaining obligations. Conclude with `((mem_fibre ρ (hs q).1 x).1 hmem).1`. Repeatedly rewrite using `[hpt]`. Rewrite using `[integral_finset_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations.

Rewrite using `[integral_indicator_const _ (hSm q), measureReal_def, measure_preimage_mul, Complex.real_smul]`. Clear the denominators using the available nonvanishing facts. Introduce `q _`. Use `(integrable_indicator_iff (hSm q)).2 (integrableOn_const ?_)` and prove the remaining obligations. Rewrite using `[measure_preimage_mul]`.

Conclude with `hfin`.
-/
theorem integral_lift [Fintype Q] (μf : Measure I.Gf) [μf.IsHaarMeasure] (hg : 1 ≤ g) (a : MonoidAlgebra ℂ Q)
    (s : Q → I.Gf) (hs : ∀ q, s q ∈ I.Kset ∧ ρ.toFun (s q) = q) (φ : I.Gf → ℂ)
    (hφ : ∀ x, ∀ k ∈ I.Kg g, φ (x * k) = φ x) :
    ∫ x, ρ.lift μf a x * φ x ∂μf = ∑ q, a.coeff q * φ (s q) := by
  classical
  obtain ⟨hfin, hvol⟩ := vol_ne_zero I μf hg
  have hopen := ((GlobalTheory.CongTop.adelic_topology I).2.2.2.2.2.2 g hg).1
  have hSm : ∀ q, MeasurableSet ((fun y => (s q)⁻¹ * y) ⁻¹' I.Kg g) := fun q =>
    (hopen.preimage (continuous_mul_left _)).measurableSet
  have hpt : ∀ x, ρ.lift μf a x * φ x = ∑ q, ((fun y => (s q)⁻¹ * y) ⁻¹' I.Kg g).indicator
      (fun _ => a.coeff q * φ (s q) / ((μf (I.Kg g)).toReal : ℂ)) x := by
    intro x
    by_cases hx : x ∈ I.Kset
    · rw [ρ.lift_of_mem μf a hx, Finset.sum_eq_single (ρ.toFun x)]
      · have hmem : (s (ρ.toFun x))⁻¹ * x ∈ I.Kg g :=
          (mem_fibre ρ (hs _).1 x).2 ⟨hx, (hs _).2.symm⟩
        rw [Set.indicator_of_mem (show x ∈ (fun y => (s (ρ.toFun x))⁻¹ * y) ⁻¹' I.Kg g from hmem)]
        have hφx : φ x = φ (s (ρ.toFun x)) := by
          have h' := hφ (s (ρ.toFun x)) _ hmem
          rwa [mul_inv_cancel_left] at h'
        rw [hφx]
        ring
      · intro q _ hq
        refine Set.indicator_of_notMem (fun hmem => hq ?_) _
        exact ((((mem_fibre ρ (hs q).1 x).1 hmem).2).trans (hs q).2).symm
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [ρ.lift_of_notMem μf a hx, zero_mul]
      refine (Finset.sum_eq_zero fun q _ => Set.indicator_of_notMem (fun hmem => hx ?_) _).symm
      exact ((mem_fibre ρ (hs q).1 x).1 hmem).1
  simp_rw [hpt]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_indicator_const _ (hSm q), measureReal_def, measure_preimage_mul, Complex.real_smul]
    field_simp
  · intro q _
    refine (integrable_indicator_iff (hSm q)).2 (integrableOn_const ?_)
    rw [measure_preimage_mul]
    exact hfin

end Lev

end GlobalTheory.LevelIdem

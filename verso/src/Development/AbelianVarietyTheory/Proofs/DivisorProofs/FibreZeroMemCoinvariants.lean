import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankSB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoinvariantOfLocallyConstantTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralVanishesOfFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankIffNonzeroMinorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFirstMaximalMinorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionInverseIntoSliceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstMaximalMinorLocallyConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceStabilizerTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSliceSectionMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSliceSectionIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceSectionHaarDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactCoveredByOpenCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralOverCosetRepresentativesStatement

noncomputable section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil

namespace GlobalTheory.RankFibreKer

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Break down `lt_trichotomy (idx J) (idx J') with hl | he | hl` into its components or cases. Conclude with `absurd ((h'.2 J).2 hl) (fun H => lt_irrefl _ (H.trans_le ((h.2 J').1)))`. Conclude with `idx.injective he`. Conclude with `absurd ((h.2 J').2 hl) (fun H => lt_irrefl _ (H.trans_le ((h'.2 J).1)))`.
-/
theorem isFirstMax_unique {a d : ℕ} {Y : Matrix (Fin a) (Fin d) k} {J J' : Fin a ↪ Fin d} (h : IsFirstMax Y J)
    (h' : IsFirstMax Y J') : J = J' := by
  rcases lt_trichotomy (idx J) (idx J') with hl | he | hl
  · exact absurd ((h'.2 J).2 hl) (fun H => lt_irrefl _ (H.trans_le ((h.2 J').1)))
  · exact idx.injective he
  · exact absurd ((h.2 J').2 hl) (fun H => lt_irrefl _ (H.trans_le ((h'.2 J).1)))

/- English proof (translation)
Establish `hex : ∃ J, IsFirstMax Y J` using `⟨J, h⟩`. Rewrite using `[sec, dif_pos hex]`. Use `show Y.submatrix id hex.choose = _`. Rewrite using `[isFirstMax_unique hex.choose_spec h]`.
-/
theorem sec_val {a d : ℕ} {Y : Matrix (Fin a) (Fin d) k} {J : Fin a ↪ Fin d} (h : IsFirstMax Y J) :
    (sec Y).val = Y.submatrix id J := by
  have hex : ∃ J, IsFirstMax Y J := ⟨J, h⟩
  rw [sec, dif_pos hex]
  show Y.submatrix id hex.choose = _
  rw [isFirstMax_unique hex.choose_spec h]

/- English proof (translation)
Introduce `Y hY`. Take `⟨J, hJ⟩` from `GlobalTheory.T.exists_first_maximal_minor k a d Y ((GlobalTheory.T.full_rank_iff_nonzero_minor k a d Y).1 hY)`. Rewrite using `[isEmbedding_val_GL.isInducing.continuousWithinAt_iff]`. Use `ContinuousAt.continuousWithinAt ?_` and prove the remaining obligations. Establish `hc : Continuous fun Y : Matrix (Fin a) (Fin d) k => Y.submatrix id J` using `(continuous_id.matrix_submatrix id J)`.

Use `hc.continuousAt.congr ?_` and prove the remaining obligations. Use `filter_upwards [GlobalTheory.T.first_maximal_minor_locally_constant k a d Y J hJ] with Y' hY'`. Conclude with `(sec_val hY').symm`.
-/
theorem continuousOn_sec {a d : ℕ} : ContinuousOn (sec (k := k) (a := a) (d := d)) {Y | Y.rank = a} := by
  intro Y hY
  obtain ⟨J, hJ⟩ := GlobalTheory.T.exists_first_maximal_minor k a d Y ((GlobalTheory.T.full_rank_iff_nonzero_minor k a d Y).1 hY)
  rw [isEmbedding_val_GL.isInducing.continuousWithinAt_iff]
  refine ContinuousAt.continuousWithinAt ?_
  have hc : Continuous fun Y : Matrix (Fin a) (Fin d) k => Y.submatrix id J :=
    (continuous_id.matrix_submatrix id J)
  refine hc.continuousAt.congr ?_
  filter_upwards [GlobalTheory.T.first_maximal_minor_locally_constant k a d Y J hJ] with Y' hY'
  exact (sec_val hY').symm

/- English proof (translation)
Take `⟨J, hJ⟩` from `GlobalTheory.T.exists_first_maximal_minor k a d Y ((GlobalTheory.T.full_rank_iff_nonzero_minor k a d Y).1 hY)`. Conclude with `GlobalTheory.T.section_inverse_into_slice k a d Y J hJ`.
-/
theorem sec_mem_slice {a d : ℕ} (Y : Matrix (Fin a) (Fin d) k) (hY : Y.rank = a) :
    ((sec Y)⁻¹).val * Y ∈ slice k a d := by
  obtain ⟨J, hJ⟩ := GlobalTheory.T.exists_first_maximal_minor k a d Y ((GlobalTheory.T.full_rank_iff_nonzero_minor k a d Y).1 hY)
  exact GlobalTheory.T.section_inverse_into_slice k a d Y J hJ

/- English proof (translation)
Establish `h0 : haarVol (KO k (Fin a)) (K : Set (GL (Fin a) k)) ≠ 0` using `(hK.measure_pos (haarVol (KO k (Fin a))) ⟨1, K.one_mem⟩).ne'`. Establish `h1 : haarVol (KO k (Fin a)) (K : Set (GL (Fin a) k)) ≠ ⊤` using `((measure_mono (μ := haarVol (KO k (Fin a))) (show (K : Set (GL (Fin a) k)) ⊆ KO k (Fin a) from hKO)).trans_lt (by rw [haarVol_self isOpen_KO le_rfl]; exact ENNReal.one_lt_top)).ne`. Conclude with `ENNReal.toReal_ne_zero.2 ⟨h0, h1⟩`.
-/
theorem vol_ne_zero [MeasurableSpace k] [BorelSpace k] {a : ℕ} (K : Subgroup (GL (Fin a) k))
    (hK : IsOpen (K : Set (GL (Fin a) k))) (hKO : K ≤ KO k (Fin a)) :
    (haarVol (KO k (Fin a))).real (K : Set (GL (Fin a) k)) ≠ 0 := by
  have h0 : haarVol (KO k (Fin a)) (K : Set (GL (Fin a) k)) ≠ 0 :=
    (hK.measure_pos (haarVol (KO k (Fin a))) ⟨1, K.one_mem⟩).ne'
  have h1 : haarVol (KO k (Fin a)) (K : Set (GL (Fin a) k)) ≠ ⊤ :=
    ((measure_mono (μ := haarVol (KO k (Fin a))) (show (K : Set (GL (Fin a) k)) ⊆ KO k (Fin a) from hKO)).trans_lt
      (by rw [haarVol_self isOpen_KO le_rfl]; exact ENNReal.one_lt_top)).ne
  exact ENNReal.toReal_ne_zero.2 ⟨h0, h1⟩

/- English proof (translation)
Introduce `k _ _ _ _ _ _ a b ν β hν _ Φ hΦ hfib`. Establish `hun : ∀ (Z : Matrix (Fin a) (Fin (a + b)) k) (g : GL (Fin a) k), Z ∈ slice k a (a + b) → g.val * Z ∈ slice k a (a + b) → g = 1` using `GlobalTheory.T.slice_stabilizer_trivial k a (a + b)`. Establish `hsc` using `continuousOn_sec (k := k) (a := a) (d := a + b)`. Establish `hsl` using `sec_mem_slice (k := k) (a := a) (d := a + b)`. Take `⟨U, hU, hUf⟩` from `GlobalTheory.T.continuous_slice_section_integral k a (a + b) Φ hΦ sec hsc hsl hun`.

Set `Kf : Subgroup (GL (Fin a) k)` to `{ carrier := {x | ∀ g : GL (Fin a) k, ∀ Z ∈ slice k a (a + b), Φ (g.val * x.val * Z) = Φ (g.val * Z)} one_mem' := fun g Z _ => by simp mul_mem' := fun {x y} hx hy g Z hZ => by`. Rewrite using `[Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul, hy (g * x) Z hZ, Units.val_mul, hx g Z hZ]`. Use the proof step `inv_mem' := fun {x} hx g Z hZ => by`. Use `hx (g * x⁻¹) Z hZ` as an intermediate fact. Rewrite `this` using `[Units.val_mul, Matrix.mul_assoc (g.val), ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]`.

Conclude with `this.symm }`. Establish `hKf : IsOpen (Kf : Set (GL (Fin a) k))` using `Subgroup.isOpen_of_mem_nhds Kf (g := 1) (Filter.mem_of_superset hU fun x hx g Z hZ => hUf x hx g Z hZ)`. Set `K : Subgroup (GL (Fin a) k)` to `KO k (Fin a) ⊓ (detChar (Fin a) ν).ker ⊓ Kf`. Establish `hK : IsOpen (K : Set (GL (Fin a) k))` using `(isOpen_KO.inter hν.detChar).inter hKf`. Establish `hKO : K ≤ KO k (Fin a)` using `le_trans inf_le_left inf_le_left`.

Establish `htw : ∀ x ∈ K, tw ν (a + b) x = 1` using `fun x hx => by`. Establish `h1 : ν (gdet x) = 1` using `hx.1.2`. Simplify using `[tw, h1, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hx.1.1)]`. Establish `hright : ∀ (g x : GL (Fin a) k) (Z : Matrix (Fin a) (Fin (a + b)) k), x ∈ K → Z ∈ slice k a (a + b) → Φ (g.val * x.val * Z) = Φ (g.val * Z)` using `fun g x Z hx hZ => hx.2 g Z hZ`. Take `⟨C, hC, hEC⟩` from `GlobalTheory.T.continuous_slice_section_measure k a (a + b) Φ hΦ sec hsc hsl hun`.

Take `⟨R, hRd, hRc⟩` from `GlobalTheory.T.compact_covered_by_open_cosets (GL (Fin a) k) K hK C hC`. Use `set T : Set (Matrix (Fin a) (Fin (a + b)) k) := {Y | ∃ x ∈ K, ∃ Z ∈ slice k a (a + b), Y = x.val * Z} with hT`. Establish `hrank : ∀ Y, Φ Y ≠ 0 → Y.rank = a` using `fun Y hY => by`. Assume the negation of the conclusion as `h`. Conclude with `hY (hΦ.2 Y h)`.

Use `GlobalTheory.T.coinvariant_of_locally_constant_twist k ν β a b Φ (T.indicator 1) R hΦ.1 (GlobalTheory.T.isLocallyConstant_indicator_mul_slice k a (a + b) K hK hKO (GlobalTheory.T.full_rank_iff_nonzero_minor k a (a + b)) sec hsc hsl hun) (fun Y => ?_) (fun Y => ?_)` and prove the remaining obligations. Distinguish the cases in `hY : Φ Y = 0`. Simplify using `[hY]`. Take `⟨g, hg⟩ : ∃ g : GL (Fin a) k, (g⁻¹).val * Y ∈ slice k a (a + b)` from `⟨sec Y, hsl Y (hrank Y hY)⟩`. Use `set Z := (g⁻¹).val * Y with hZdef`.

Establish `hYZ : Y = g.val * Z` using `by rw [hZdef, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]`. Take `⟨r, hr, hrg⟩` from `hRc g (hEC g Z hg (hYZ ▸ hY))`. Rewrite using `[Finset.sum_eq_single r]`. Rewrite using `[Set.indicator_of_mem, Pi.one_apply, one_mul]`. Conclude with `⟨r⁻¹ * g, hrg, Z, hg, by rw [hYZ, Units.val_mul, Matrix.mul_assoc]⟩`.

Introduce `r' hr' hne`. Rewrite using `[Set.indicator_of_notMem, zero_mul]`. Introduce and unpack `⟨x', hx', Z', hZ', he⟩`. Establish `h1 : ((x'⁻¹ * r'⁻¹ * g : GL (Fin a) k)).val * Z ∈ slice k a (a + b)`. Establish `: ((x'⁻¹ * r'⁻¹ * g : GL (Fin a) k)).val * Z = Z'`.

Simplify using `only [Units.val_mul, Matrix.mul_assoc]`. Rewrite using `[← hYZ, he, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]`. Rewrite using `[this]`. Conclude with `hZ'`. Establish `h2` using `hun Z _ hg h1`.

Establish `h3 : g = r' * x'`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hne (hRd r hr r' hr' (by`. Establish `: r⁻¹ * r' = (r⁻¹ * g) * x'⁻¹` using `by rw [h3]; group`. Rewrite using `[this]`.

Conclude with `K.mul_mem hrg (K.inv_mem hx'))).symm`. Introduce `h`. Conclude with `absurd hr h`. Distinguish the cases in `hY : Y ∈ T`. Take `⟨x, hx, Z, hZ, rfl⟩` from `hY`.

Rewrite using `[Set.indicator_of_mem (show x.val * Z ∈ T from ⟨x, hx, Z, hZ, rfl⟩), Pi.one_apply, one_mul]`. Establish `e1 : ∀ r : GL (Fin a) k, Φ (r.val * (x.val * Z)) = Φ (r.val * Z)` using `fun r => by`. Rewrite using `[← Matrix.mul_assoc]`. Conclude with `hright r x Z hx hZ`. Simplify using `only [e1]`.

Establish `hZr : Z.rank = a`. Take `⟨J, hJ, -⟩` from `hZ`. Conclude with `(GlobalTheory.T.full_rank_iff_nonzero_minor k a (a + b) Z).2 ⟨J, by simp [minor, hJ]⟩`. Establish `hint` using `GlobalTheory.T.haar_integral_over_coset_representatives k a K hK hKO (fun g => Φ (g.val * Z) * tw ν (a + b) g) (fun g x' hx' => by`. Simplify using `only [Units.val_mul, tw_mul, htw x' hx', mul_one]`.

Rewrite using `[hright g x' Z hx' hZ])`. Use `R hRd (fun g hg => hRc g (hEC g Z hZ (left_ne_zero_of_mul hg)))`. Rewrite `hint` using `[GlobalTheory.T.orbital_integral_vanishes_of_fibre k ν β a b Φ hfib Z hZr]`. Establish `hv` using `vol_ne_zero K hK hKO`. Use `(mul_eq_zero.1 hint.symm).resolve_left (by exact_mod_cast hv)` as an intermediate fact.

Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun r _ => mul_comm _ _`. Simplify using `[Set.indicator_of_notMem hY]`.
-/
theorem fibre_ker : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν →
    GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB k a (a + b),
    GlobalTheory.RankFibre.fibre ν β a b Φ = 0 → Φ ∈ GlobalTheory.RankFibre.coinv ν β a (a + b) := by
  intro k _ _ _ _ _ _ a b ν β hν _ Φ hΦ hfib
  have hun : ∀ (Z : Matrix (Fin a) (Fin (a + b)) k) (g : GL (Fin a) k), Z ∈ slice k a (a + b) →
      g.val * Z ∈ slice k a (a + b) → g = 1 := GlobalTheory.T.slice_stabilizer_trivial k a (a + b)
  have hsc := continuousOn_sec (k := k) (a := a) (d := a + b)
  have hsl := sec_mem_slice (k := k) (a := a) (d := a + b)
  obtain ⟨U, hU, hUf⟩ := GlobalTheory.T.continuous_slice_section_integral k a (a + b) Φ hΦ sec hsc hsl hun
  let Kf : Subgroup (GL (Fin a) k) :=
    { carrier := {x | ∀ g : GL (Fin a) k, ∀ Z ∈ slice k a (a + b), Φ (g.val * x.val * Z) = Φ (g.val * Z)}
      one_mem' := fun g Z _ => by simp
      mul_mem' := fun {x y} hx hy g Z hZ => by
        rw [Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul, hy (g * x) Z hZ, Units.val_mul, hx g Z hZ]
      inv_mem' := fun {x} hx g Z hZ => by
        have := hx (g * x⁻¹) Z hZ
        rw [Units.val_mul, Matrix.mul_assoc (g.val), ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.mul_one] at this
        exact this.symm }
  have hKf : IsOpen (Kf : Set (GL (Fin a) k)) := Subgroup.isOpen_of_mem_nhds Kf (g := 1)
    (Filter.mem_of_superset hU fun x hx g Z hZ => hUf x hx g Z hZ)
  let K : Subgroup (GL (Fin a) k) := KO k (Fin a) ⊓ (detChar (Fin a) ν).ker ⊓ Kf
  have hK : IsOpen (K : Set (GL (Fin a) k)) := (isOpen_KO.inter hν.detChar).inter hKf
  have hKO : K ≤ KO k (Fin a) := le_trans inf_le_left inf_le_left
  have htw : ∀ x ∈ K, tw ν (a + b) x = 1 := fun x hx => by
    have h1 : ν (gdet x) = 1 := hx.1.2
    simp [tw, h1, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hx.1.1)]
  have hright : ∀ (g x : GL (Fin a) k) (Z : Matrix (Fin a) (Fin (a + b)) k), x ∈ K → Z ∈ slice k a (a + b) →
      Φ (g.val * x.val * Z) = Φ (g.val * Z) := fun g x Z hx hZ => hx.2 g Z hZ
  obtain ⟨C, hC, hEC⟩ := GlobalTheory.T.continuous_slice_section_measure k a (a + b) Φ hΦ sec hsc hsl hun
  obtain ⟨R, hRd, hRc⟩ := GlobalTheory.T.compact_covered_by_open_cosets (GL (Fin a) k) K hK C hC
  set T : Set (Matrix (Fin a) (Fin (a + b)) k) := {Y | ∃ x ∈ K, ∃ Z ∈ slice k a (a + b), Y = x.val * Z} with hT
  have hrank : ∀ Y, Φ Y ≠ 0 → Y.rank = a := fun Y hY => by
    by_contra h; exact hY (hΦ.2 Y h)
  refine GlobalTheory.T.coinvariant_of_locally_constant_twist k ν β a b Φ (T.indicator 1) R hΦ.1
    (GlobalTheory.T.isLocallyConstant_indicator_mul_slice k a (a + b) K hK hKO (GlobalTheory.T.full_rank_iff_nonzero_minor k a (a + b)) sec hsc hsl hun) (fun Y => ?_) (fun Y => ?_)
  · by_cases hY : Φ Y = 0
    · simp [hY]
    obtain ⟨g, hg⟩ : ∃ g : GL (Fin a) k, (g⁻¹).val * Y ∈ slice k a (a + b) := ⟨sec Y, hsl Y (hrank Y hY)⟩
    set Z := (g⁻¹).val * Y with hZdef
    have hYZ : Y = g.val * Z := by rw [hZdef, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul]
    obtain ⟨r, hr, hrg⟩ := hRc g (hEC g Z hg (hYZ ▸ hY))
    rw [Finset.sum_eq_single r]
    · rw [Set.indicator_of_mem, Pi.one_apply, one_mul]
      exact ⟨r⁻¹ * g, hrg, Z, hg, by rw [hYZ, Units.val_mul, Matrix.mul_assoc]⟩
    · intro r' hr' hne
      rw [Set.indicator_of_notMem, zero_mul]
      rintro ⟨x', hx', Z', hZ', he⟩
      have h1 : ((x'⁻¹ * r'⁻¹ * g : GL (Fin a) k)).val * Z ∈ slice k a (a + b) := by
        have : ((x'⁻¹ * r'⁻¹ * g : GL (Fin a) k)).val * Z = Z' := by
          simp only [Units.val_mul, Matrix.mul_assoc]
          rw [← hYZ, he, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
        rw [this]; exact hZ'
      have h2 := hun Z _ hg h1
      have h3 : g = r' * x' := by
        calc g = r' * x' * (x'⁻¹ * r'⁻¹ * g) := by group
          _ = r' * x' := by rw [h2, mul_one]
      exact hne (hRd r hr r' hr' (by
        have : r⁻¹ * r' = (r⁻¹ * g) * x'⁻¹ := by rw [h3]; group
        rw [this]; exact K.mul_mem hrg (K.inv_mem hx'))).symm
    · intro h; exact absurd hr h
  · by_cases hY : Y ∈ T
    · obtain ⟨x, hx, Z, hZ, rfl⟩ := hY
      rw [Set.indicator_of_mem (show x.val * Z ∈ T from ⟨x, hx, Z, hZ, rfl⟩), Pi.one_apply, one_mul]
      have e1 : ∀ r : GL (Fin a) k, Φ (r.val * (x.val * Z)) = Φ (r.val * Z) := fun r => by
        rw [← Matrix.mul_assoc]; exact hright r x Z hx hZ
      simp only [e1]
      have hZr : Z.rank = a := by
        obtain ⟨J, hJ, -⟩ := hZ
        exact (GlobalTheory.T.full_rank_iff_nonzero_minor k a (a + b) Z).2 ⟨J, by simp [minor, hJ]⟩
      have hint := GlobalTheory.T.haar_integral_over_coset_representatives k a K hK hKO (fun g => Φ (g.val * Z) * tw ν (a + b) g)
        (fun g x' hx' => by
          simp only [Units.val_mul, tw_mul, htw x' hx', mul_one]
          rw [hright g x' Z hx' hZ])
        R hRd (fun g hg => hRc g (hEC g Z hZ (left_ne_zero_of_mul hg)))
      rw [GlobalTheory.T.orbital_integral_vanishes_of_fibre k ν β a b Φ hfib Z hZr] at hint
      have hv := vol_ne_zero K hK hKO
      have := (mul_eq_zero.1 hint.symm).resolve_left (by exact_mod_cast hv)
      rw [← this]
      exact Finset.sum_congr rfl fun r _ => mul_comm _ _
    · simp [Set.indicator_of_notMem hY]

end GlobalTheory.RankFibreKer

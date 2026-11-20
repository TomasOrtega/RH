import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDeterminant.SpanSingletonAlgebraMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDeterminant.LocalPi

noncomputable section

namespace PI.IsoDetW.Loc

open PI.IsoDetDefs IsDedekindDomain

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "FI" => FractionalIdeal (nonZeroDivisors R) K

def std : Submodule R (ι → K) := Submodule.pi Set.univ (fun _ => (1 : Submodule R K))

def sc (a : K) : Submodule R (ι → K) :=
  Submodule.pi Set.univ (fun _ => ((FractionalIdeal.spanSingleton (nonZeroDivisors R) a : FI) : Submodule R K))

def IsLat (A : Submodule R (ι → K)) : Prop :=
  ∃ r : R, r ≠ 0 ∧ sc (algebraMap R K r) ≤ A ∧ A ≤ sc (algebraMap R K r)⁻¹

omit [IsDedekindDomain R] [DecidableEq ι] in
/- English proof (translation)
Simplify using `[sc, Submodule.mem_pi, Submodule.mem_span_singleton]`.
-/
theorem mem_sc {a : K} {v : ι → K} :
    v ∈ (sc a : Submodule R (ι → K)) ↔ ∀ i, ∃ z : R, z • a = v i := by
  simp [sc, Submodule.mem_pi, Submodule.mem_span_singleton]

omit [IsDedekindDomain R] in
/- English proof (translation)
Rewrite using `[FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_spanSingleton]`. Conclude with `⟨t, by rw [Algebra.smul_def, h]⟩`.
-/
theorem span_le_span {a b : K} (t : R) (h : a = algebraMap R K t * b) :
    FractionalIdeal.spanSingleton (nonZeroDivisors R) a ≤ FractionalIdeal.spanSingleton (nonZeroDivisors R) b := by
  rw [FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_spanSingleton]
  exact ⟨t, by rw [Algebra.smul_def, h]⟩

omit [IsDedekindDomain R] [DecidableEq ι] in
/- English proof (translation)
The claim follows from `Submodule.pi_mono fun _ _ => FractionalIdeal.coe_le_coe.2 h`.
-/
theorem sc_mono {a b : K}
    (h : FractionalIdeal.spanSingleton (nonZeroDivisors R) a ≤ FractionalIdeal.spanSingleton (nonZeroDivisors R) b) :
    (sc a : Submodule R (ι → K)) ≤ sc b :=
  Submodule.pi_mono fun _ _ => FractionalIdeal.coe_le_coe.2 h

omit [IsDedekindDomain R] in
/- English proof (translation)
Rewrite using `[ne_eq, IsFractionRing.to_map_eq_zero_iff]`. Conclude with `hr`.
-/
theorem algebraMap_ne_zero' {r : R} (hr : r ≠ 0) : algebraMap R K r ≠ 0 := by
  rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact hr

omit [IsDedekindDomain R] in
/- English proof (translation)
Rewrite using `[ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff]`. Conclude with `ha`.
-/
theorem spanSingleton_ne_zero' {a : K} (ha : a ≠ 0) :
    FractionalIdeal.spanSingleton (nonZeroDivisors R) a ≠ 0 := by
  rw [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff]; exact ha

omit [DecidableEq ι] in
/- English proof (translation)
Unfold `sc`. Rewrite using `[localization_pi, localization_pi, rlen_pi, ENat.sum_ne_top]`. Introduce `i _`. Use `rlen_ne_top P (spanSingleton_ne_zero' (algebraMap_ne_zero' hr)) (span_le_span (r * s) ?_)` and prove the remaining obligations. Rewrite using `[map_mul, mul_assoc, mul_inv_cancel₀ (algebraMap_ne_zero' hs), mul_one]`.
-/
theorem rlen_sc_ne_top (P : HeightOneSpectrum R) {r s : R} (hr : r ≠ 0) (hs : s ≠ 0) :
    relative₂ (localization₂ P.asIdeal (sc (algebraMap R K r) : Submodule R (ι → K)))
      (localization₂ P.asIdeal (sc (algebraMap R K s)⁻¹)) ≠ ⊤ := by
  unfold sc
  rw [localization_pi, localization_pi, rlen_pi, ENat.sum_ne_top]
  intro i _
  refine rlen_ne_top P (spanSingleton_ne_zero' (algebraMap_ne_zero' hr)) (span_le_span (r * s) ?_)
  rw [map_mul, mul_assoc, mul_inv_cancel₀ (algebraMap_ne_zero' hs), mul_one]

omit [DecidableEq ι] in
/- English proof (translation)
Take `⟨s, hs, -, hA2⟩` from `hA`. Conclude with `ne_top_of_le_ne_top (rlen_sc_ne_top P hr hs) (rlen_mono le_rfl (localization_mono _ hrA) (localization_mono _ hA2))`.
-/
theorem rlen_lat_ne_top (P : HeightOneSpectrum R) {A : Submodule R (ι → K)} (hA : IsLat A) {r : R}
    (hr : r ≠ 0) (hrA : sc (algebraMap R K r) ≤ A) :
    relative₂ (localization₂ P.asIdeal (sc (algebraMap R K r))) (localization₂ P.asIdeal A) ≠ ⊤ := by
  obtain ⟨s, hs, -, hA2⟩ := hA
  exact ne_top_of_le_ne_top (rlen_sc_ne_top P hr hs)
    (rlen_mono le_rfl (localization_mono _ hrA) (localization_mono _ hA2))

omit [DecidableEq ι] in
/- English proof (translation)
Take `⟨a, ha, hA1, -⟩` from `id hA`. Take `⟨b, hb, hB1, -⟩` from `id hB`. Take `⟨c, hc, hC1, -⟩` from `id hC`. Establish `hr : a * b * c ≠ 0` using `mul_ne_zero (mul_ne_zero ha hb) hc`. Apply the tactic sequence `have hDA : sc (algebraMap R K (a * b * c)) ≤ A := (sc_mono (span_le_span (b * c) (by simp only [map_mul]; try ring))).trans hA1`.

Apply the tactic sequence `have hDB : sc (algebraMap R K (a * b * c)) ≤ B := (sc_mono (span_le_span (a * c) (by simp only [map_mul]; try ring))).trans hB1`. Apply the tactic sequence `have hDC : sc (algebraMap R K (a * b * c)) ≤ C := (sc_mono (span_le_span (a * b) (by simp only [map_mul]; try ring))).trans hC1`. Conclude with `lidx_cocycle P.asIdeal hDA hDB hDC (rlen_lat_ne_top P hA hr hDA) (rlen_lat_ne_top P hB hr hDB) (rlen_lat_ne_top P hC hr hDC)`.
-/
theorem lat_cocycle (P : HeightOneSpectrum R) {A B C : Submodule R (ι → K)} (hA : IsLat A) (hB : IsLat B)
    (hC : IsLat C) : lidx P.asIdeal A C = lidx P.asIdeal A B + lidx P.asIdeal B C := by
  obtain ⟨a, ha, hA1, -⟩ := id hA
  obtain ⟨b, hb, hB1, -⟩ := id hB
  obtain ⟨c, hc, hC1, -⟩ := id hC
  have hr : a * b * c ≠ 0 := mul_ne_zero (mul_ne_zero ha hb) hc
  have hDA : sc (algebraMap R K (a * b * c)) ≤ A :=
    (sc_mono (span_le_span (b * c) (by simp only [map_mul]; try ring))).trans hA1
  have hDB : sc (algebraMap R K (a * b * c)) ≤ B :=
    (sc_mono (span_le_span (a * c) (by simp only [map_mul]; try ring))).trans hB1
  have hDC : sc (algebraMap R K (a * b * c)) ≤ C :=
    (sc_mono (span_le_span (a * b) (by simp only [map_mul]; try ring))).trans hC1
  exact lidx_cocycle P.asIdeal hDA hDB hDC (rlen_lat_ne_top P hA hr hDA) (rlen_lat_ne_top P hB hr hDB)
    (rlen_lat_ne_top P hC hr hDC)

omit [DecidableEq ι] in
/- English proof (translation)
Use `choose r hr hr1 hr2 using fun i => exists_sandwich (c i) (hc i)`. Establish `hP : ∀ i, (∏ j ∈ Finset.univ.erase i, r j) ≠ 0` using `fun i => Finset.prod_ne_zero_iff.2 fun j _ => hr j`. Use `⟨∏ i, r i, Finset.prod_ne_zero_iff.2 fun i _ => hr i, ?_, ?_⟩` and prove the remaining obligations. Use `Submodule.pi_mono fun i _ => ?_` and prove the remaining obligations. Use `FractionalIdeal.coe_le_coe.2 ((span_le_span (∏ j ∈ Finset.univ.erase i, r j) ?_).trans (hr1 i))` and prove the remaining obligations.

Rewrite using `[← map_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]`. Use `Submodule.pi_mono fun i _ => ?_` and prove the remaining obligations. Use `FractionalIdeal.coe_le_coe.2 ((hr2 i).trans (span_le_span (∏ j ∈ Finset.univ.erase i, r j) ?_))` and prove the remaining obligations. Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ i), map_mul, mul_inv, ← mul_assoc, mul_inv_cancel₀ (algebraMap_ne_zero' (hP i)), one_mul]`.
-/
theorem isLat_pi (c : ι → FI) (hc : ∀ i, c i ≠ 0) :
    IsLat (Submodule.pi Set.univ (fun i => (c i : Submodule R K))) := by
  classical
  choose r hr hr1 hr2 using fun i => exists_sandwich (c i) (hc i)
  have hP : ∀ i, (∏ j ∈ Finset.univ.erase i, r j) ≠ 0 :=
    fun i => Finset.prod_ne_zero_iff.2 fun j _ => hr j
  refine ⟨∏ i, r i, Finset.prod_ne_zero_iff.2 fun i _ => hr i, ?_, ?_⟩
  · refine Submodule.pi_mono fun i _ => ?_
    refine FractionalIdeal.coe_le_coe.2 ((span_le_span (∏ j ∈ Finset.univ.erase i, r j) ?_).trans (hr1 i))
    rw [← map_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  · refine Submodule.pi_mono fun i _ => ?_
    refine FractionalIdeal.coe_le_coe.2 ((hr2 i).trans (span_le_span (∏ j ∈ Finset.univ.erase i, r j) ?_))
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), map_mul, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ (algebraMap_ne_zero' (hP i)), one_mul]

omit [IsDedekindDomain R] in
/- English proof (translation)
Introduce and unpack `_ ⟨v, hv, rfl⟩`. Rewrite `hv` using `[SetLike.mem_coe, mem_sc]`. Rewrite using `[mem_sc]`. Use `choose z hz using hv`. Use `choose m hm using hd`.

Establish `had` using `algebraMap_ne_zero' (K := K) hd0`. Introduce `k`. Use `⟨∑ j, m k j * z j, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]`. Rewrite using `[Algebra.smul_def, map_sum, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← hz j, map_mul, hm k j, Algebra.smul_def, Algebra.smul_def]`. Clear the denominators using the available nonvanishing facts.
-/
theorem map_sc_le (M : Matrix ι ι K) {d : R} (hd0 : d ≠ 0)
    (hd : ∀ i j, IsLocalization.IsInteger R (d • M i j)) (a : K) :
    (sc a : Submodule R (ι → K)).map (M.mulVecLin.restrictScalars R) ≤ sc (a * (algebraMap R K d)⁻¹) := by
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, mem_sc] at hv
  rw [mem_sc]
  choose z hz using hv
  choose m hm using hd
  have had := algebraMap_ne_zero' (K := K) hd0
  intro k
  refine ⟨∑ j, m k j * z j, ?_⟩
  simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  rw [Algebra.smul_def, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hz j, map_mul, hm k j, Algebra.smul_def, Algebra.smul_def]
  field_simp

/- English proof (translation)
Take `⟨s, hs, hA1, hA2⟩` from `hA`. Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors R) (Finset.univ : Finset ((ι × ι) ⊕ (ι × ι))) (Sum.elim (fun p => g p.1 p.2) (fun p => g⁻¹ p.1 p.2))`. Establish `hd0 : (d : R) ≠ 0` using `nonZeroDivisors.coe_ne_zero d`. Establish `hg1 : ∀ i j, IsLocalization.IsInteger R ((d : R) • g i j)` using `fun i j => hd (Sum.inl (i, j)) (Finset.mem_univ _)`. Establish `hg2 : ∀ i j, IsLocalization.IsInteger R ((d : R) • g⁻¹ i j)` using `fun i j => hd (Sum.inr (i, j)) (Finset.mem_univ _)`.

Establish `had` using `algebraMap_ne_zero' (K := K) hd0`. Establish `has` using `algebraMap_ne_zero' (K := K) hs`. Use `⟨s * d, mul_ne_zero hs hd0, ?_, ?_⟩` and prove the remaining obligations. Introduce `v hv`. Establish `hu` using `map_sc_le g⁻¹ hd0 hg2 _ (Submodule.mem_map_of_mem (f := g⁻¹.mulVecLin.restrictScalars R) hv)`.

Rewrite `hu` using `[map_mul, mul_inv_cancel_right₀ had]`. Use `⟨g⁻¹.mulVec v, hA1 hu, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv g (isUnit_iff_ne_zero.2 hg), Matrix.one_mulVec]`. Use `(Submodule.map_mono hA2).trans ((map_sc_le g hd0 hg1 _).trans ?_)` and prove the remaining obligations. Rewrite using `[map_mul, mul_inv]`.
-/
theorem isLat_map (g : Matrix ι ι K) (hg : g.det ≠ 0) {A : Submodule R (ι → K)} (hA : IsLat A) :
    IsLat (A.map (g.mulVecLin.restrictScalars R)) := by
  obtain ⟨s, hs, hA1, hA2⟩ := hA
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R)
    (Finset.univ : Finset ((ι × ι) ⊕ (ι × ι))) (Sum.elim (fun p => g p.1 p.2) (fun p => g⁻¹ p.1 p.2))
  have hd0 : (d : R) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hg1 : ∀ i j, IsLocalization.IsInteger R ((d : R) • g i j) :=
    fun i j => hd (Sum.inl (i, j)) (Finset.mem_univ _)
  have hg2 : ∀ i j, IsLocalization.IsInteger R ((d : R) • g⁻¹ i j) :=
    fun i j => hd (Sum.inr (i, j)) (Finset.mem_univ _)
  have had := algebraMap_ne_zero' (K := K) hd0
  have has := algebraMap_ne_zero' (K := K) hs
  refine ⟨s * d, mul_ne_zero hs hd0, ?_, ?_⟩
  · intro v hv
    have hu := map_sc_le g⁻¹ hd0 hg2 _ (Submodule.mem_map_of_mem (f := g⁻¹.mulVecLin.restrictScalars R) hv)
    rw [map_mul, mul_inv_cancel_right₀ had] at hu
    refine ⟨g⁻¹.mulVec v, hA1 hu, ?_⟩
    simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv g (isUnit_iff_ne_zero.2 hg), Matrix.one_mulVec]
  · refine (Submodule.map_mono hA2).trans ((map_sc_le g hd0 hg1 _).trans ?_)
    rw [map_mul, mul_inv]

omit [DecidableEq ι] in
/- English proof (translation)
Use extensionality with `v`. Simplify using `[Submodule.mem_pi, forall_and]`.
-/
theorem pi_inf_pi (X Z : ι → Submodule R K) :
    Submodule.pi Set.univ X ⊓ Submodule.pi Set.univ Z = Submodule.pi Set.univ (fun i => X i ⊓ Z i) := by
  ext v
  simp [Submodule.mem_pi, forall_and]

omit [DecidableEq ι] in
/- English proof (translation)
Establish `: (∑ i, f i) = ((∑ i, (f i).toNat : ℕ) : ℕ∞)`. Use `push_cast`. Conclude with `Finset.sum_congr rfl fun i _ => (ENat.natCast_toNat (hf i)).symm`. Rewrite using `[this, ENat.toNat_natCast]`.
-/
theorem toNat_sum (f : ι → ℕ∞) (hf : ∀ i, f i ≠ ⊤) : (∑ i, f i).toNat = ∑ i, (f i).toNat := by
  have : (∑ i, f i) = ((∑ i, (f i).toNat : ℕ) : ℕ∞) := by
    push_cast
    exact Finset.sum_congr rfl fun i _ => (ENat.natCast_toNat (hf i)).symm
  rw [this, ENat.toNat_natCast]

omit [DecidableEq ι] in
/- English proof (translation)
Establish `hinf : ∀ i, c i ⊓ b i ≠ 0`. Introduce `i`. Take `⟨r, hr, hr1, -⟩` from `exists_sandwich (c i) (hc i)`. Take `⟨t, ht, ht1, -⟩` from `exists_sandwich (b i) (hb i)`. Establish `hle : FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K (r * t)) ≤ c i ⊓ b i` using `le_inf ((span_le_span t (by rw [map_mul, mul_comm])).trans hr1) ((span_le_span r (by rw [map_mul])).trans ht1)`.

Introduce `h0`. Rewrite `hle` using `[h0, FractionalIdeal.le_zero_iff]`. Conclude with `spanSingleton_ne_zero' (algebraMap_ne_zero' (mul_ne_zero hr ht)) hle`. Establish `hf1 : ∀ i, relative₂ (localization₂ P.asIdeal ((c i : Submodule R K) ⊓ (b i : Submodule R K))) (localization₂ P.asIdeal (c i : Submodule R K)) ≠ ⊤`. Introduce `i`.

Use `rlen_ne_top P (hinf i) (inf_le_left : c i ⊓ b i ≤ c i)` as an intermediate fact. Rewrite `this` using `[FractionalIdeal.coe_inf]`. Then use the resulting hypothesis. Establish `hf2 : ∀ i, relative₂ (localization₂ P.asIdeal ((c i : Submodule R K) ⊓ (b i : Submodule R K))) (localization₂ P.asIdeal (b i : Submodule R K)) ≠ ⊤`. Introduce `i`. Use `rlen_ne_top P (hinf i) (inf_le_right : c i ⊓ b i ≤ b i)` as an intermediate fact.

Rewrite `this` using `[FractionalIdeal.coe_inf]`. Then use the resulting hypothesis. Rewrite using `[lidx_eq, pi_inf_pi, localization_pi, localization_pi, localization_pi, rlen_pi, rlen_pi, toNat_sum _ hf1, toNat_sum _ hf2]`. Use `push_cast`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← lidx_frac P (hc i) (hb i), lidx_eq]`.
-/
theorem lidx_pi_frac (P : HeightOneSpectrum R) (c b : ι → FI) (hc : ∀ i, c i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    lidx P.asIdeal (Submodule.pi Set.univ (fun i => (c i : Submodule R K)))
      (Submodule.pi Set.univ (fun i => (b i : Submodule R K))) =
      ∑ i, (FractionalIdeal.count K P (b i) - FractionalIdeal.count K P (c i)) := by
  have hinf : ∀ i, c i ⊓ b i ≠ 0 := by
    intro i
    obtain ⟨r, hr, hr1, -⟩ := exists_sandwich (c i) (hc i)
    obtain ⟨t, ht, ht1, -⟩ := exists_sandwich (b i) (hb i)
    have hle : FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K (r * t)) ≤ c i ⊓ b i :=
      le_inf ((span_le_span t (by rw [map_mul, mul_comm])).trans hr1)
        ((span_le_span r (by rw [map_mul])).trans ht1)
    intro h0
    rw [h0, FractionalIdeal.le_zero_iff] at hle
    exact spanSingleton_ne_zero' (algebraMap_ne_zero' (mul_ne_zero hr ht)) hle
  have hf1 : ∀ i, relative₂ (localization₂ P.asIdeal ((c i : Submodule R K) ⊓ (b i : Submodule R K)))
      (localization₂ P.asIdeal (c i : Submodule R K)) ≠ ⊤ := by
    intro i
    have := rlen_ne_top P (hinf i) (inf_le_left : c i ⊓ b i ≤ c i)
    rwa [FractionalIdeal.coe_inf] at this
  have hf2 : ∀ i, relative₂ (localization₂ P.asIdeal ((c i : Submodule R K) ⊓ (b i : Submodule R K)))
      (localization₂ P.asIdeal (b i : Submodule R K)) ≠ ⊤ := by
    intro i
    have := rlen_ne_top P (hinf i) (inf_le_right : c i ⊓ b i ≤ b i)
    rwa [FractionalIdeal.coe_inf] at this
  rw [lidx_eq, pi_inf_pi, localization_pi, localization_pi, localization_pi, rlen_pi, rlen_pi, toNat_sum _ hf1, toNat_sum _ hf2]
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← lidx_frac P (hc i) (hb i), lidx_eq]

end PI.IsoDetW.Loc

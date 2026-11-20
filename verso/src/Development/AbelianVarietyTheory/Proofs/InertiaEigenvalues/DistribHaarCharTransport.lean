import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR MeasureTheory Filter Topology
open scoped Pointwise

namespace GlobalTheory.JR.ModuleNorm

/- English proof (translation)
Use `borelize A B`. Take `⟨K, hK, hK0⟩` from `exists_compact_mem_nhds (0 : A)`. Establish `h0 : (Measure.addHaar : Measure A) K ≠ 0` using `(Measure.measure_pos_of_mem_nhds _ hK0).ne'`. Establish `hT : (Measure.addHaar : Measure A) K ≠ ⊤` using `hK.measure_lt_top.ne`. Establish `hmap : ∀ s : Set B, ((Measure.addHaar : Measure A).map e) s = (Measure.addHaar : Measure A) (e ⁻¹' s)` using `fun s => e.toHomeomorph.toMeasurableEquiv.map_apply s`.

Establish `key : ∀ x, h⁻¹ • e x = e (g⁻¹ • x)` using `fun x => by`. Rewrite using `[inv_smul_eq_iff, ← he, smul_inv_smul]`. Establish `hpre : e ⁻¹' (e.symm ⁻¹' K) = K`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Establish `hpre2 : e ⁻¹' (h • e.symm ⁻¹' K) = g • K`. Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, key]`. Simplify using the standard rewrite rules. Establish `h0' : ((Measure.addHaar : Measure A).map e) (e.symm ⁻¹' K) ≠ 0` using `by rw [hmap, hpre]; exact h0`.

Establish `hT' : ((Measure.addHaar : Measure A).map e) (e.symm ⁻¹' K) ≠ ⊤` using `by rw [hmap, hpre]; exact hT`. Apply `ENNReal.coe_injective` to reduce the goal to its premises. Rewrite using `[distribHaarChar_eq_div h0' hT', distribHaarChar_eq_div h0 hT, hmap, hmap, hpre, hpre2]`.
-/
theorem distribHaarChar_transport {G H A B : Type} [Group G] [Group H]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    [T2Space A] [SecondCountableTopology A] [DistribMulAction G A] [ContinuousConstSMul G A]
    [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] [LocallyCompactSpace B]
    [T2Space B] [SecondCountableTopology B] [DistribMulAction H B] [ContinuousConstSMul H B]
    (e : A ≃ₜ+ B) (g : G) (h : H) (he : ∀ x, e (g • x) = h • e x) :
    distribHaarChar B h = distribHaarChar A g := by
  borelize A B
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : A)
  have h0 : (Measure.addHaar : Measure A) K ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hK0).ne'
  have hT : (Measure.addHaar : Measure A) K ≠ ⊤ := hK.measure_lt_top.ne
  have hmap : ∀ s : Set B, ((Measure.addHaar : Measure A).map e) s = (Measure.addHaar : Measure A) (e ⁻¹' s) :=
    fun s => e.toHomeomorph.toMeasurableEquiv.map_apply s
  have key : ∀ x, h⁻¹ • e x = e (g⁻¹ • x) := fun x => by
    rw [inv_smul_eq_iff, ← he, smul_inv_smul]
  have hpre : e ⁻¹' (e.symm ⁻¹' K) = K := by
    ext x; simp
  have hpre2 : e ⁻¹' (h • e.symm ⁻¹' K) = g • K := by
    ext x
    simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, key]
    simp
  have h0' : ((Measure.addHaar : Measure A).map e) (e.symm ⁻¹' K) ≠ 0 := by rw [hmap, hpre]; exact h0
  have hT' : ((Measure.addHaar : Measure A).map e) (e.symm ⁻¹' K) ≠ ⊤ := by rw [hmap, hpre]; exact hT
  apply ENNReal.coe_injective
  rw [distribHaarChar_eq_div h0' hT', distribHaarChar_eq_div h0 hT, hmap, hmap, hpre, hpre2]

/- English proof (translation)
Use `borelize A`. Take `⟨K, hK, hK0⟩` from `exists_compact_mem_nhds (0 : A)`. Establish `h0 : (Measure.addHaar : Measure A) K ≠ 0` using `(Measure.measure_pos_of_mem_nhds _ hK0).ne'`. Establish `hT : (Measure.addHaar : Measure A) K ≠ ⊤` using `hK.measure_lt_top.ne`. Establish `hg : (Measure.addHaar : Measure A) (g • K) = distribHaarChar A g * Measure.addHaar K`.

Rewrite using `[distribHaarChar_eq_div h0 hT, ENNReal.div_mul_cancel h0 hT]`. Apply `distribHaarChar_eq_of_measure_smul_eq_mul (μ := Measure.pi fun _ : Fin 2 => (Measure.addHaar : Measure A)) (s := Set.univ.pi fun _ => K)` to reduce the goal to its premises. Rewrite using `[Measure.pi_pi]`. Simplify using `[h0]`. Rewrite using `[Measure.pi_pi]`.

Simplify using `[hT]`. Rewrite using `[Set.smul_set_univ_pi, Measure.pi_pi, Measure.pi_pi]`. Simplify using `only [Pi.smul_apply, Fin.prod_univ_two, hg]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem distribHaarChar_pi_two {G A : Type} [Group G]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    [T2Space A] [SecondCountableTopology A] [DistribMulAction G A] [ContinuousConstSMul G A]
    (g : G) : distribHaarChar (Fin 2 → A) g = distribHaarChar A g ^ 2 := by
  borelize A
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : A)
  have h0 : (Measure.addHaar : Measure A) K ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hK0).ne'
  have hT : (Measure.addHaar : Measure A) K ≠ ⊤ := hK.measure_lt_top.ne
  have hg : (Measure.addHaar : Measure A) (g • K) = distribHaarChar A g * Measure.addHaar K := by
    rw [distribHaarChar_eq_div h0 hT, ENNReal.div_mul_cancel h0 hT]
  apply distribHaarChar_eq_of_measure_smul_eq_mul
    (μ := Measure.pi fun _ : Fin 2 => (Measure.addHaar : Measure A)) (s := Set.univ.pi fun _ => K)
  · rw [Measure.pi_pi]; simp [h0]
  · rw [Measure.pi_pi]; simp [hT]
  · rw [Set.smul_set_univ_pi, Measure.pi_pi, Measure.pi_pi]
    simp only [Pi.smul_apply, Fin.prod_univ_two, hg]
    push_cast
    ring

/- English proof (translation)
Set `eC : (Fin 2 → K) ≃ₜ+ L` to `{ e.toAddEquiv with continuous_toFun := he, continuous_invFun := hes }`. Set `kL : Lˣ` to `Units.map (algebraMap K L).toMonoidHom k`. Establish `h1 : distribHaarChar L kL = distribHaarChar (Fin 2 → K) k` using `distribHaarChar_transport eC k kL (fun x => by show e (k • x) = kL • e x`. Simplify using `only [Units.smul_def]`. Rewrite using `[map_smul, Algebra.smul_def, smul_eq_mul]`.

Use the proof step `rfl)`. Establish `h2` using `distribHaarChar_pi_two (A := K) k`. Set `yS : Lˣ` to `Units.map (starRingEnd L).toMonoidHom y`. Set `sC : L ≃ₜ+ L` to `{ starAddEquiv with continuous_toFun := continuous_star, continuous_invFun := continuous_star }`. Establish `h3 : distribHaarChar L yS = distribHaarChar L y` using `distribHaarChar_transport sC y yS (fun x => by show star (y • x) = yS • star x`.

Rewrite using `[Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, star_mul']`. Use the proof step `rfl)`. Establish `h4 : kL = y * yS` using `Units.ext (by simp [kL, yS, h, starRingEnd_apply])`. Establish `hsq : distribHaarChar L y ^ 2 = distribHaarChar K k ^ 2`. Rewrite using `[← h2, ← h1, h4, map_mul, h3, sq]`.

Conclude with `(pow_left_inj₀ zero_le zero_le two_ne_zero).mp hsq`.
-/
theorem distribHaarChar_eq_norm (K L : Type) [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] [T2Space K] [LocallyCompactSpace K] [SecondCountableTopology K]
    [CommRing L] [TopologicalSpace L] [IsTopologicalRing L] [T2Space L] [LocallyCompactSpace L]
    [SecondCountableTopology L] [StarRing L] [ContinuousStar L] [Algebra K L]
    (e : (Fin 2 → K) ≃ₗ[K] L) (he : Continuous e) (hes : Continuous e.symm) (y : Lˣ) (k : Kˣ)
    (h : algebraMap K L k = y * star (y : L)) :
    distribHaarChar L y = distribHaarChar K k := by
  let eC : (Fin 2 → K) ≃ₜ+ L :=
    { e.toAddEquiv with continuous_toFun := he, continuous_invFun := hes }
  let kL : Lˣ := Units.map (algebraMap K L).toMonoidHom k
  have h1 : distribHaarChar L kL = distribHaarChar (Fin 2 → K) k :=
    distribHaarChar_transport eC k kL (fun x => by
      show e (k • x) = kL • e x
      simp only [Units.smul_def]
      rw [map_smul, Algebra.smul_def, smul_eq_mul]
      rfl)
  have h2 := distribHaarChar_pi_two (A := K) k
  let yS : Lˣ := Units.map (starRingEnd L).toMonoidHom y
  let sC : L ≃ₜ+ L :=
    { starAddEquiv with continuous_toFun := continuous_star, continuous_invFun := continuous_star }
  have h3 : distribHaarChar L yS = distribHaarChar L y :=
    distribHaarChar_transport sC y yS (fun x => by
      show star (y • x) = yS • star x
      rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, star_mul']
      rfl)
  have h4 : kL = y * yS := Units.ext (by simp [kL, yS, h, starRingEnd_apply])
  have hsq : distribHaarChar L y ^ 2 = distribHaarChar K k ^ 2 := by
    rw [← h2, ← h1, h4, map_mul, h3, sq]
  exact (pow_left_inj₀ zero_le zero_le two_ne_zero).mp hsq

end GlobalTheory.JR.ModuleNorm

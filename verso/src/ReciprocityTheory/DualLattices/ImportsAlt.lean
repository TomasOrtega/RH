import ReciprocityTheory.DualLattices.DualHopfOrderStatement
import ReciprocityTheory.DualLattices.MemDualLatMapFourier

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.L2

/- English proof (translation)
Introduce `v hv N H _ _ _ _ _ _ e he hcard AA`. Take `⟨B, hB, hAA⟩` from `AA.lat`. Establish `σ : H ≃ N` using `Fintype.equivOfCardEq hcard`. Take `⟨M, hMdef⟩ : ∃ M : Matrix H H C, M = ((tableM e σ)ᵀ * (B⁻¹)ᵀ).submatrix σ σ` from `⟨_, rfl⟩`. Establish `hdual : dualLat AA.carrier = Submodule.span R (Set.range fun j x => (B⁻¹)ᵀ x j)`.

Rewrite using `[hAA]`. Conclude with `dualLat_spanCols B hB`. Establish `hmap : (dualLat AA.carrier).map (fourier (R` using `R) fun h a => e h a) = Submodule.span R (Set.range fun k h => M h k) := by`. Rewrite using `[hdual, hMdef]`. Conclude with `map_fourier_spanCols e σ _`.

Establish `hBB : B.det * B⁻¹.det = 1`. Rewrite using `[← Matrix.det_mul, Matrix.mul_nonsing_inv B hB, Matrix.det_one]`. Establish `hBinv : IsUnit B⁻¹.det` using `⟨⟨B⁻¹.det, B.det, by rw [mul_comm]; exact hBB, hBB⟩, rfl⟩`. Establish `hdetM : M.det = (tableM e σ).det * B⁻¹.det`. Rewrite using `[hMdef, Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose]`.

Establish `hMunit : IsUnit M.det`. Rewrite using `[hdetM]`. Conclude with `(tableM_isUnit e σ).mul hBinv`. Establish `hdd : dualLat (dualLat AA.carrier) = AA.carrier`. Rewrite using `[hAA]`.

Conclude with `dualLat_dualLat_spanCols B hB`. Use `⟨{ carrier := (dualLat AA.carrier).map (fourier (R := R) fun h a => e h a) lat := ⟨M, hMunit, hmap⟩ le_int := by` and prove the remaining obligations. Introduce and unpack `w ⟨u, hu, rfl⟩ h`. Conclude with `hv.exists_of_le_one (valuation_fourier_le_one v hv (fun h => e h) AA hu h)`. Use `one_mem := Submodule.mem_map.mpr ⟨(Pi.single 0 1 : N → C), single_mem_dualLat AA,`.

Use function extensionality and compare the values at `fun h => fourier_single (R := R) (fun h => e h) h⟩`. Use `mul_mem := by`. Introduce and unpack `f g ⟨u, hu, rfl⟩ ⟨w, hw, rfl⟩`. Conclude with `Submodule.mem_map.mpr ⟨conv u w, conv_mem_dualLat AA hu hw,`. Use function extensionality and compare the values at `fun h => fourier_conv (R := R) (fun h => e h) u w h⟩`.

Use `comul := by`. Introduce and unpack `f ⟨u, hu, rfl⟩`. Conclude with `comul_fourier e he AA B hB hAA u hu`. Use `antipode := by`. Introduce and unpack `f ⟨u, hu, rfl⟩`.

Conclude with `antipode_fourier e he AA u hu }, rfl, ?_, ?_⟩`. Use extensionality with `f`. Rewrite using `[Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`.

Establish `h1` using `(mem_dualLat_map_fourier e (dualLat AA.carrier) w).mp hw`. Rewrite `h1` using `[hdd]`. Then use the resulting hypothesis. Introduce `hf`. Take `⟨w, hw⟩` from `fourier'_surjective (R := R) e σ f`. Use `⟨w, (mem_dualLat_map_fourier e (dualLat AA.carrier) w).mpr ?_, hw⟩` and prove the remaining obligations.

Rewrite using `[hw, hdd]`. Conclude with `hf`. Introduce `c c' hc hc'`. Take `⟨B₀, hB₀, rfl⟩` from `hc`. Take `⟨B₁, hB₁, rfl⟩` from `hc'`.

Establish `e0 : v B₀.det = v B.det` using `valuation_det_eq_of_span_eq v hv B₀ B (hB₀.symm.trans hAA)`. Establish `e1 : v B₁.det = v M.det` using `valuation_det_eq_of_span_eq v hv B₁ M (hB₁.symm.trans hmap)`. Establish `key : v B.det * v M.det = v (tableM e σ).det`. Rewrite using `[← map_mul, hdetM, mul_left_comm, hBB, mul_one]`. Establish `h2 : (tableM e σ).det ^ 2 = (Fintype.card N : C) ^ Fintype.card N ∨ (tableM e σ).det ^ 2 = -(Fintype.card N : C) ^ Fintype.card N` using `ReciprocityTheory.PGsh.charTable C N (σ.symm.trans e)`.

Rewrite using `[e0, e1, key]`. Combine the equalities or inequalities in the displayed calculation. Apply the tactic sequence `rcases h2 with h | h <;> rw [h] <;> simp [Valuation.map_neg, map_pow]`.
-/
theorem h1 (C R : Type) [Field C] [CommRing R] [Algebra R C] :
    DualHopfOrderStatement (C := C) (R := R) := by
  intro v hv N H _ _ _ _ _ _ e he hcard AA
  obtain ⟨B, hB, hAA⟩ := AA.lat
  have σ : H ≃ N := Fintype.equivOfCardEq hcard
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix H H C,
      M = ((tableM e σ)ᵀ * (B⁻¹)ᵀ).submatrix σ σ := ⟨_, rfl⟩
  have hdual : dualLat AA.carrier = Submodule.span R (Set.range fun j x => (B⁻¹)ᵀ x j) := by
    rw [hAA]; exact dualLat_spanCols B hB
  have hmap : (dualLat AA.carrier).map (fourier (R := R) fun h a => e h a) =
      Submodule.span R (Set.range fun k h => M h k) := by
    rw [hdual, hMdef]; exact map_fourier_spanCols e σ _
  have hBB : B.det * B⁻¹.det = 1 := by
    rw [← Matrix.det_mul, Matrix.mul_nonsing_inv B hB, Matrix.det_one]
  have hBinv : IsUnit B⁻¹.det := ⟨⟨B⁻¹.det, B.det, by rw [mul_comm]; exact hBB, hBB⟩, rfl⟩
  have hdetM : M.det = (tableM e σ).det * B⁻¹.det := by
    rw [hMdef, Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_transpose,
      Matrix.det_transpose]
  have hMunit : IsUnit M.det := by
    rw [hdetM]; exact (tableM_isUnit e σ).mul hBinv
  have hdd : dualLat (dualLat AA.carrier) = AA.carrier := by
    rw [hAA]; exact dualLat_dualLat_spanCols B hB
  refine ⟨{ carrier := (dualLat AA.carrier).map (fourier (R := R) fun h a => e h a)
            lat := ⟨M, hMunit, hmap⟩
            le_int := by
              rintro w ⟨u, hu, rfl⟩ h
              exact hv.exists_of_le_one (valuation_fourier_le_one v hv (fun h => e h) AA hu h)
            one_mem := Submodule.mem_map.mpr ⟨(Pi.single 0 1 : N → C),
              single_mem_dualLat AA,
              funext fun h => fourier_single (R := R) (fun h => e h) h⟩
            mul_mem := by
              rintro f g ⟨u, hu, rfl⟩ ⟨w, hw, rfl⟩
              exact Submodule.mem_map.mpr ⟨conv u w,
                conv_mem_dualLat AA hu hw,
                funext fun h => fourier_conv (R := R) (fun h => e h) u w h⟩
            comul := by
              rintro f ⟨u, hu, rfl⟩
              exact comul_fourier e he AA B hB hAA u hu
            antipode := by
              rintro f ⟨u, hu, rfl⟩
              exact antipode_fourier e he AA u hu }, rfl, ?_, ?_⟩
  · ext f
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have h1 := (mem_dualLat_map_fourier e (dualLat AA.carrier) w).mp hw
      rwa [hdd] at h1
    · intro hf
      obtain ⟨w, hw⟩ := fourier'_surjective (R := R) e σ f
      refine ⟨w, (mem_dualLat_map_fourier e (dualLat AA.carrier) w).mpr ?_, hw⟩
      rw [hw, hdd]; exact hf
  · intro c c' hc hc'
    obtain ⟨B₀, hB₀, rfl⟩ := hc
    obtain ⟨B₁, hB₁, rfl⟩ := hc'
    have e0 : v B₀.det = v B.det :=
      valuation_det_eq_of_span_eq v hv B₀ B (hB₀.symm.trans hAA)
    have e1 : v B₁.det = v M.det :=
      valuation_det_eq_of_span_eq v hv B₁ M (hB₁.symm.trans hmap)
    have key : v B.det * v M.det = v (tableM e σ).det := by
      rw [← map_mul, hdetM, mul_left_comm, hBB, mul_one]
    have h2 : (tableM e σ).det ^ 2 = (Fintype.card N : C) ^ Fintype.card N ∨
        (tableM e σ).det ^ 2 = -(Fintype.card N : C) ^ Fintype.card N :=
      ReciprocityTheory.PGsh.charTable C N (σ.symm.trans e)
    rw [e0, e1, key]
    calc v (tableM e σ).det ^ 2 = v ((tableM e σ).det ^ 2) :=
          (map_pow v _ 2).symm
      _ = v (Fintype.card N : C) ^ Fintype.card N := by
        rcases h2 with h | h <;> rw [h] <;> simp [Valuation.map_neg, map_pow]

end ReciprocityTheory.PGsh.L2

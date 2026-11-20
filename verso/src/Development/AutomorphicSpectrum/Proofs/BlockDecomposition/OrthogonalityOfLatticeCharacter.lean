import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
open PositivityTheory.JacquetShalikaLocal
open MeasureTheory ValuativeRel

namespace GlobalTheory.CompanionTheory.SatakeBound

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Establish `hb0 : b ≠ 0`. Introduce and unpack `rfl`. Conclude with `hb (zero_mem _)`. Establish `hvb : 1 < valuation F b`. Rewrite `hb` using `[Valuation.mem_integer_iff, not_le]`.

Conclude with `hb`. Establish `hvinv : valuation F b⁻¹ < 1` using `((valuation F).one_lt_val_iff hb0).mp hvb`. Establish `hinvO : b⁻¹ ∈ (valuation F).integer`. Rewrite using `[Valuation.mem_integer_iff]`. Conclude with `hvinv.le`.

Establish `hynu : (⟨b⁻¹, hinvO⟩ : (valuation F).integer) ∈ IsLocalRing.maximalIdeal (valuation F).integer`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Conclude with `(ne_of_lt hvinv) ((Valuation.integer.integers (valuation F)).isUnit_iff_valuation_eq_one.mp hu)`. Establish `hmax` using `GroundTheory.Automorphic.GLnLocal.maximalIdeal_pow_eq F 1`.

Rewrite `hmax` using `[pow_one, pow_one]`. Rewrite `hynu` using `[hmax, Ideal.mem_span_singleton]`. Take `⟨u, hu⟩` from `hynu`. Take `⟨x, hx, hψx⟩` from `hψ.2.1`. Use `⟨(↑(GroundTheory.Automorphic.GLnLocal.uniformizer F) * x) * (u : F), mul_mem hx u.2, ?_⟩` and prove the remaining obligations.

Establish `hu' : b⁻¹ = (GroundTheory.Automorphic.GLnLocal.uniformizer F : F) * (u : F)`. Establish `h` using `congrArg Subtype.val hu`. Simplify using `using h`. Establish `hx' : (↑(GroundTheory.Automorphic.GLnLocal.uniformizer F) * x) * (u : F) * b = x`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hx']`. Conclude with `hψx`.
-/
theorem exists_integer_psi_mul_ne_one {ψ : AddChar F ℂ} (hψ : PsiOK ψ) {b : F}
    (hb : b ∉ (valuation F).integer) :
    ∃ t ∈ (valuation F).integer, ψ (t * b) ≠ 1 := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hb (zero_mem _)
  have hvb : 1 < valuation F b := by
    rw [Valuation.mem_integer_iff, not_le] at hb
    exact hb
  have hvinv : valuation F b⁻¹ < 1 := ((valuation F).one_lt_val_iff hb0).mp hvb
  have hinvO : b⁻¹ ∈ (valuation F).integer := by
    rw [Valuation.mem_integer_iff]
    exact hvinv.le
  have hynu : (⟨b⁻¹, hinvO⟩ : (valuation F).integer) ∈ IsLocalRing.maximalIdeal (valuation F).integer := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (ne_of_lt hvinv) ((Valuation.integer.integers (valuation F)).isUnit_iff_valuation_eq_one.mp hu)
  have hmax := GroundTheory.Automorphic.GLnLocal.maximalIdeal_pow_eq F 1
  rw [pow_one, pow_one] at hmax
  rw [hmax, Ideal.mem_span_singleton] at hynu
  obtain ⟨u, hu⟩ := hynu
  obtain ⟨x, hx, hψx⟩ := hψ.2.1
  refine ⟨(↑(GroundTheory.Automorphic.GLnLocal.uniformizer F) * x) * (u : F), mul_mem hx u.2, ?_⟩
  have hu' : b⁻¹ = (GroundTheory.Automorphic.GLnLocal.uniformizer F : F) * (u : F) := by
    have h := congrArg Subtype.val hu
    simpa using h
  have hx' : (↑(GroundTheory.Automorphic.GLnLocal.uniformizer F) * x) * (u : F) * b = x := by
    calc (↑(GroundTheory.Automorphic.GLnLocal.uniformizer F) * x) * (u : F) * b
        = x * ((GroundTheory.Automorphic.GLnLocal.uniformizer F : F) * u) * b := by ring
      _ = x * b⁻¹ * b := by rw [hu']
      _ = x := by rw [mul_assoc, inv_mul_cancel₀ hb0, mul_one]
  rw [hx']
  exact hψx

/- English proof (translation)
Simplify using `only [lat, Set.mem_ofPred_eq, pow_zero, one_mul]`.
-/
theorem mem_lat_zero {m : ℕ} {x : Fin m → F} :
    x ∈ lat F m 0 ↔ ∀ i, x i ∈ (valuation F).integer := by
  simp only [lat, Set.mem_ofPred_eq, pow_zero, one_mul]

/- English proof (translation)
Unfold `L0 L1 ForF`. Introduce `hL0 F _ _ _ _ _ _ μ _ ψ hψ m y`. Establish `hL` using `hL0 F μ ψ hψ`. Simplify using `only at hL ⊢`. Distinguish the cases in `hy : ∀ i, y i ∈ (valuation F).integer`.

Rewrite using `[if_pos hy]`. Establish `hmeas : MeasurableSet (lat F m 0)` using `((hL.2 m).1 0).2.2.1`. Establish `h1 : Set.EqOn (fun ξ : Fin m → F => ψ (ξ ⬝ᵥ y)) (fun _ => (1 : ℂ)) (lat F m 0)`. Introduce `ξ hξ`. Rewrite `hξ` using `[mem_lat_zero]`.

Use `hψ.1 _ ?_` and prove the remaining obligations. Unfold `dotProduct`. Conclude with `sum_mem fun j _ => mul_mem (hξ j) (hy j)`. Rewrite using `[setIntegral_congr_fun hmeas h1, setIntegral_const]`. Simplify using the standard rewrite rules.

Rewrite using `[if_neg hy]`. Simplify using `only [not_forall] at hy`. Take `⟨i, hi⟩` from `hy`. Take `⟨t, ht, hne⟩` from `exists_integer_psi_mul_ne_one hψ hi`. Establish `hsO : ∀ j, (Pi.single i t : Fin m → F) j ∈ (valuation F).integer`.

Introduce `j`. Distinguish the cases in `hj : j = i`. Rewrite using `[hj, Pi.single_eq_same]`. Conclude with `ht`. Rewrite using `[Pi.single_eq_of_ne hj]`.

Conclude with `zero_mem _`. Establish `hinv : (fun ξ : Fin m → F => Pi.single i t + ξ) ⁻¹' lat F m 0 = lat F m 0`. Use extensionality with `ξ`. Simplify using `only [Set.mem_preimage, mem_lat_zero, Pi.add_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce `h j`. Establish `h2` using `sub_mem (h j) (hsO j)`. Simplify using `using h2`. Introduce `h j`. Conclude with `add_mem (hsO j) (h j)`.

Establish `hsd : (Pi.single i t : Fin m → F) ⬝ᵥ y = t * y i` using `by first`. Consider the case `exact single_dotProduct t i`. Consider the case `simp [dotProduct, Pi.single_apply]`. Establish `hmp` using `measurePreserving_add_left (Measure.pi fun _ : Fin m => μ) (Pi.single i t : Fin m → F)`. Establish `hemb` using `measurableEmbedding_addLeft (Pi.single i t : Fin m → F)`.

Establish `hshift` using `hmp.setIntegral_preimage_emb hemb (fun ξ => ψ (ξ ⬝ᵥ y)) (lat F m 0)`. Rewrite `hshift` using `[hinv]`. Simplify using `only [add_dotProduct, AddChar.map_add_eq_mul, hsd] at hshift`. Rewrite `hshift` using `[integral_const_mul]`. Establish `h0 : (∫ ξ in lat F m 0, ψ (ξ ⬝ᵥ y) ∂Measure.pi fun _ => μ) * (ψ (t * y i) - 1) = 0`.

Take the linear combination `hshift`. Conclude with `(mul_eq_zero.mp h0).resolve_right (sub_ne_zero.mpr hne)`.
-/
theorem orthogonality_of_lattice_character : L0 → L1 := by
  unfold L0 L1 ForF
  intro hL0 F _ _ _ _ _ _ μ _ ψ hψ m y
  have hL := hL0 F μ ψ hψ
  dsimp only at hL ⊢
  by_cases hy : ∀ i, y i ∈ (valuation F).integer
  · rw [if_pos hy]
    have hmeas : MeasurableSet (lat F m 0) := ((hL.2 m).1 0).2.2.1
    have h1 : Set.EqOn (fun ξ : Fin m → F => ψ (ξ ⬝ᵥ y)) (fun _ => (1 : ℂ)) (lat F m 0) := by
      intro ξ hξ
      rw [mem_lat_zero] at hξ
      refine hψ.1 _ ?_
      unfold dotProduct
      exact sum_mem fun j _ => mul_mem (hξ j) (hy j)
    rw [setIntegral_congr_fun hmeas h1, setIntegral_const]
    simp
  · rw [if_neg hy]
    simp only [not_forall] at hy
    obtain ⟨i, hi⟩ := hy
    obtain ⟨t, ht, hne⟩ := exists_integer_psi_mul_ne_one hψ hi
    have hsO : ∀ j, (Pi.single i t : Fin m → F) j ∈ (valuation F).integer := by
      intro j
      by_cases hj : j = i
      · rw [hj, Pi.single_eq_same]
        exact ht
      · rw [Pi.single_eq_of_ne hj]
        exact zero_mem _
    have hinv : (fun ξ : Fin m → F => Pi.single i t + ξ) ⁻¹' lat F m 0 = lat F m 0 := by
      ext ξ
      simp only [Set.mem_preimage, mem_lat_zero, Pi.add_apply]
      constructor
      · intro h j
        have h2 := sub_mem (h j) (hsO j)
        simpa using h2
      · intro h j
        exact add_mem (hsO j) (h j)
    have hsd : (Pi.single i t : Fin m → F) ⬝ᵥ y = t * y i := by
      first
        | exact single_dotProduct t i
        | simp [dotProduct, Pi.single_apply]
    have hmp := measurePreserving_add_left (Measure.pi fun _ : Fin m => μ) (Pi.single i t : Fin m → F)
    have hemb := measurableEmbedding_addLeft (Pi.single i t : Fin m → F)
    have hshift := hmp.setIntegral_preimage_emb hemb (fun ξ => ψ (ξ ⬝ᵥ y)) (lat F m 0)
    rw [hinv] at hshift
    simp only [add_dotProduct, AddChar.map_add_eq_mul, hsd] at hshift
    rw [integral_const_mul] at hshift
    have h0 : (∫ ξ in lat F m 0, ψ (ξ ⬝ᵥ y) ∂Measure.pi fun _ => μ) * (ψ (t * y i) - 1) = 0 := by
      linear_combination hshift
    exact (mul_eq_zero.mp h0).resolve_right (sub_ne_zero.mpr hne)

end GlobalTheory.CompanionTheory.SatakeBound

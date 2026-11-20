import Mathlib
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.StSmallFormsFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionLatticeFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRealFormsOnPoints
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComplexFormsOnPoints
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPrimeComplexRadical
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComplexMinimalPrimesContract
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIndependentModBaseChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel MvPolynomial

noncomputable section

/- English proof (translation)
Introduce `K _ ι _ Ω _ y D hV m R`. Establish `hRF : RealFormsOnPoints.Statement` using `RealFormsOnPoints.proof (ComplexFormsOnPoints.proof PrimeComplexRadical.proof ComplexMinimalPrimesContract.proof) IndependentModBaseChange.proof`. Establish `: CharZero Ω` using `charZero_of_inj_zero fun n hn => by`. Establish `hmem : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι)` using `by show C (n : ℤ) ∈ RingHom.ker (mConeMap y)`. Rewrite using `[RingHom.mem_ker, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, eq_intCast, Int.cast_natCast, ← map_natCast (C : Ω →+* MvPolynomial K Ω), hn, map_zero]`.

Rewrite `hmem` using `[hV.2.2.1, Ideal.mem_bot]`. Conclude with `hmem` after adjusting the coercions. Use `set d : K → ℕ := fun _ => m with hd`. Use `set N : Submodule ℤ Ω := Submodule.span ℤ {s | ∃ g : MRing ι, IsMultiHomog g d ∧ aeval y g = s} with hN`. Establish `: Module.Finite ℤ N` using `Module.Finite.iff_fg.mpr ((Submodule.fg_iff_addSubgroup_fg N).mpr (SectionLatticeFinite.secM_fg y d))`.

Establish `hrep : ∀ σ ∈ N, ∃ g : MRing ι, IsMultiHomog g d ∧ aeval y g = σ`. Introduce `σ hσ`. Proceed by induction on `hσ using Submodule.span_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `zero => exact ⟨0, SectionLatticeFinite.homog_zero d, map_zero _⟩`.

Consider the case `add x x' _ _ h h'`. Take `⟨g, hg, rfl⟩` from `h`. Take `⟨g', hg', rfl⟩` from `h'`. Conclude with `⟨g + g', SectionLatticeFinite.homog_add hg hg', map_add _ _ _⟩`. Consider the case `smul n x _ h`.

Take `⟨g, hg, rfl⟩` from `h`. Use `⟨n • g, fun s hs k => hg s (MvPolynomial.support_smul hs) k, map_zsmul _ _ _⟩` and prove the remaining obligations. Set `b` to `Module.finBasis ℤ N`. Use `set r := Module.finrank ℤ N`. Use `choose g hg hgy using fun i => hrep (b i) (b i).2`.

Establish `hsum : ∀ n : Fin r → ℤ, IsMultiHomog (∑ i, n i • g i) d`. Introduce `n s hs k`. Take `⟨i, -, hi⟩` from `Finset.mem_biUnion.mp (MvPolynomial.support_sum hs)`. Conclude with `hg i s (MvPolynomial.support_smul hi) k`. Establish `hli : LinearIndependent ℤ (fun i => aeval y (g i))`.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `n hn`. Use `(Fintype.linearIndependent_iff.mp b.linearIndependent) n (Subtype.ext ?_)` and prove the remaining obligations. Simplify `hn` using `[hgy]`. Set `G : Fin r → ((Σ k, ι k) → ℂ) → ℂ` to `fun i z => eval z (map (Int.castRingHom ℂ) (g i))`.

Set `ψ : ((Σ k, ι k) → ℂ) → (Fin r → ℝ) →ₗ[ℝ] ℂ` to `fun z => ∑ i, (LinearMap.proj i : (Fin r → ℝ) →ₗ[ℝ] ℝ).smulRight (G i z)`. Establish `hψ : ∀ z c, ψ z c = ∑ i, (c i : ℂ) * G i z`. Introduce `z c`. Simplify using `[ψ, Complex.real_smul]`. Take `⟨N0, ⟨F0, hF0, rfl⟩, hmin⟩` from `IsArtinian.set_has_minimal {L : Submodule ℝ (Fin r → ℝ) | ∃ F : Finset ((Σ k, ι k) → ℂ), (↑F ⊆ mcPts (mCoordIdeal y)) ∧ L = ⨅ z ∈ F, LinearMap.ker (ψ z)} ⟨_, ∅, by simp, rfl⟩`.

Set `Φ : (Fin r → ℝ) →ₗ[ℝ] (F0 → ℂ)` to `LinearMap.pi fun z => ψ z`. Establish `hker : LinearMap.ker Φ = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `c hc`. Rewrite using `[Submodule.mem_bot]`.

Use `hRF K ι Ω y (D + 1) d r g hV hg hli c fun z hz => ?_` and prove the remaining obligations. Establish `hle : (⨅ w ∈ insert z F0, LinearMap.ker (ψ w)) ≤ ⨅ w ∈ F0, LinearMap.ker (ψ w)` using `le_iInf₂ fun w hw => iInf₂_le w (Finset.mem_insert_of_mem hw)`. Establish `heq` using `(eq_of_le_of_not_lt hle (hmin _ ⟨insert z F0, by`. Simplify `⟨hz, hF0⟩, rfl⟩))` using `[Set.insert_subset_iff]`. Establish `hc' : c ∈ ⨅ w ∈ F0, LinearMap.ker (ψ w)`.

Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker]`. Introduce `w hw`. Conclude with `congrFun (LinearMap.mem_ker.mp hc) ⟨w, hw⟩`. Rewrite `hc'` using `[← heq]`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker] at hc'`.

Rewrite using `[← hψ]`. Conclude with `hc' z (Finset.mem_insert_self _ _)`. Take `⟨Kc, -, hK⟩` from `Φ.exists_antilipschitzWith hker`. Use `set B : ℝ := ∑ z ∈ F0, |R * (fsH ι).h z ^ m| with hB`. Use `set T : ℝ := Kc * B`.

Establish `hbox : ∀ n : Fin r → ℤ, (∀ z ∈ mcPts (mCoordIdeal y), ‖∑ i, (n i : ℂ) * G i z‖ ≤ R * (fsH ι).h z ^ m) → ∀ i, |(n i : ℝ)| ≤ T`. Introduce `n hn i`. Use `set c : Fin r → ℝ := fun i => (n i : ℝ)`. Establish `hΦ : ‖Φ c‖ ≤ B`. Use `(pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)).mpr fun z => ?_` and prove the remaining obligations.

Establish `h1 : ‖Φ c z‖ ≤ R * (fsH ι).h z ^ m`. Use `hn z (hF0 z.2)` as an intermediate fact. Simplify `this` using `[Φ, hψ, c]`. Conclude with `h1.trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun z => |R * (fsH ι).h z ^ m|) (fun _ _ => abs_nonneg _) z.2))`. Establish `hc : ‖c‖ ≤ Kc * ‖Φ c‖`.

Simplify using `using hK.le_mul_dist c 0`. Combine the equalities or inequalities in the displayed calculation. Establish `hfin : (Set.pi Set.univ fun _ : Fin r => Set.Icc (-⌈T⌉) ⌈T⌉).Finite` using `Set.Finite.pi fun _ => Set.finite_Icc _ _`. Use `(hfin.image fun n => ∑ i, n i • aeval y (g i)).subset ?_` and prove the remaining obligations. Introduce and unpack `σ ⟨hσ, hsmall⟩`.

Use `set n : Fin r → ℤ := fun i => b.repr ⟨σ, hσ⟩ i`. Establish `hσn : aeval y (∑ i, n i • g i) = σ`. Rewrite using `[map_sum]`. Repeatedly rewrite using `[map_zsmul, hgy]`. Use `congrArg Subtype.val (b.sum_repr ⟨σ, hσ⟩)` as an intermediate fact.

Rewrite `this` using `[Submodule.coe_sum]`. Simplify `this` using `only [Submodule.coe_smul]`. Establish `hb` using `hbox n fun z hz => by`. Use `hsmall _ (hsum n) hσn z hz` as an intermediate fact. Simplify `this` using `[G, map_sum, zsmul_eq_mul]`.

Use `⟨n, fun i _ => ?_, by simpa [map_sum] using hσn⟩` and prove the remaining obligations. Use `abs_le.mp (hb i)` as an intermediate fact. Prove the components needed by the constructor for the conclusion. Establish `h` using `Int.le_ceil T`. Conclude with `(show (-(⌈T⌉ : ℝ)) ≤ n i by linarith [this.1])` after adjusting the coercions.

Establish `h` using `Int.le_ceil T`. Conclude with `(show (n i : ℝ) ≤ ⌈T⌉ by linarith [this.2])` after adjusting the coercions.
-/
theorem SmallFormsFinite.proof : SmallFormsFinite.Statement := by
  intro K _ ι _ Ω _ y D hV m R
  classical
  have hRF : RealFormsOnPoints.Statement := RealFormsOnPoints.proof
    (ComplexFormsOnPoints.proof PrimeComplexRadical.proof ComplexMinimalPrimesContract.proof)
    IndependentModBaseChange.proof

  have : CharZero Ω := charZero_of_inj_zero fun n hn => by
    have hmem : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
      show C (n : ℤ) ∈ RingHom.ker (mConeMap y)
      rw [RingHom.mem_ker, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, eq_intCast, Int.cast_natCast,
        ← map_natCast (C : Ω →+* MvPolynomial K Ω), hn, map_zero]
    rw [hV.2.2.1, Ideal.mem_bot] at hmem
    exact_mod_cast hmem
  set d : K → ℕ := fun _ => m with hd
  set N : Submodule ℤ Ω := Submodule.span ℤ {s | ∃ g : MRing ι, IsMultiHomog g d ∧ aeval y g = s} with hN
  have : Module.Finite ℤ N :=
    Module.Finite.iff_fg.mpr ((Submodule.fg_iff_addSubgroup_fg N).mpr (SectionLatticeFinite.secM_fg y d))

  have hrep : ∀ σ ∈ N, ∃ g : MRing ι, IsMultiHomog g d ∧ aeval y g = σ := by
    intro σ hσ
    induction hσ using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, SectionLatticeFinite.homog_zero d, map_zero _⟩
    | add x x' _ _ h h' =>
      obtain ⟨g, hg, rfl⟩ := h
      obtain ⟨g', hg', rfl⟩ := h'
      exact ⟨g + g', SectionLatticeFinite.homog_add hg hg', map_add _ _ _⟩
    | smul n x _ h =>
      obtain ⟨g, hg, rfl⟩ := h
      refine ⟨n • g, fun s hs k => hg s (MvPolynomial.support_smul hs) k, map_zsmul _ _ _⟩
  let b := Module.finBasis ℤ N
  set r := Module.finrank ℤ N
  choose g hg hgy using fun i => hrep (b i) (b i).2
  have hsum : ∀ n : Fin r → ℤ, IsMultiHomog (∑ i, n i • g i) d := by
    intro n s hs k
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hs)
    exact hg i s (MvPolynomial.support_smul hi) k
  have hli : LinearIndependent ℤ (fun i => aeval y (g i)) := by
    rw [Fintype.linearIndependent_iff]
    intro n hn
    refine (Fintype.linearIndependent_iff.mp b.linearIndependent) n (Subtype.ext ?_)
    simpa [hgy] using hn

  let G : Fin r → ((Σ k, ι k) → ℂ) → ℂ := fun i z => eval z (map (Int.castRingHom ℂ) (g i))
  let ψ : ((Σ k, ι k) → ℂ) → (Fin r → ℝ) →ₗ[ℝ] ℂ := fun z =>
    ∑ i, (LinearMap.proj i : (Fin r → ℝ) →ₗ[ℝ] ℝ).smulRight (G i z)
  have hψ : ∀ z c, ψ z c = ∑ i, (c i : ℂ) * G i z := by
    intro z c
    simp [ψ, Complex.real_smul]

  obtain ⟨N0, ⟨F0, hF0, rfl⟩, hmin⟩ := IsArtinian.set_has_minimal
    {L : Submodule ℝ (Fin r → ℝ) | ∃ F : Finset ((Σ k, ι k) → ℂ), (↑F ⊆ mcPts (mCoordIdeal y)) ∧
      L = ⨅ z ∈ F, LinearMap.ker (ψ z)} ⟨_, ∅, by simp, rfl⟩
  let Φ : (Fin r → ℝ) →ₗ[ℝ] (F0 → ℂ) := LinearMap.pi fun z => ψ z
  have hker : LinearMap.ker Φ = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [Submodule.mem_bot]
    refine hRF K ι Ω y (D + 1) d r g hV hg hli c fun z hz => ?_
    have hle : (⨅ w ∈ insert z F0, LinearMap.ker (ψ w)) ≤ ⨅ w ∈ F0, LinearMap.ker (ψ w) :=
      le_iInf₂ fun w hw => iInf₂_le w (Finset.mem_insert_of_mem hw)
    have heq := (eq_of_le_of_not_lt hle (hmin _ ⟨insert z F0, by
      simpa [Set.insert_subset_iff] using ⟨hz, hF0⟩, rfl⟩))
    have hc' : c ∈ ⨅ w ∈ F0, LinearMap.ker (ψ w) := by
      simp only [Submodule.mem_iInf, LinearMap.mem_ker]
      intro w hw
      exact congrFun (LinearMap.mem_ker.mp hc) ⟨w, hw⟩
    rw [← heq] at hc'
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hc'
    rw [← hψ]
    exact hc' z (Finset.mem_insert_self _ _)
  obtain ⟨Kc, -, hK⟩ := Φ.exists_antilipschitzWith hker
  set B : ℝ := ∑ z ∈ F0, |R * (fsH ι).h z ^ m| with hB
  set T : ℝ := Kc * B

  have hbox : ∀ n : Fin r → ℤ, (∀ z ∈ mcPts (mCoordIdeal y),
      ‖∑ i, (n i : ℂ) * G i z‖ ≤ R * (fsH ι).h z ^ m) → ∀ i, |(n i : ℝ)| ≤ T := by
    intro n hn i
    set c : Fin r → ℝ := fun i => (n i : ℝ)
    have hΦ : ‖Φ c‖ ≤ B := by
      refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)).mpr fun z => ?_
      have h1 : ‖Φ c z‖ ≤ R * (fsH ι).h z ^ m := by
        have := hn z (hF0 z.2)
        simpa [Φ, hψ, c] using this
      exact h1.trans ((le_abs_self _).trans
        (Finset.single_le_sum (f := fun z => |R * (fsH ι).h z ^ m|) (fun _ _ => abs_nonneg _) z.2))
    have hc : ‖c‖ ≤ Kc * ‖Φ c‖ := by
      simpa using hK.le_mul_dist c 0
    calc |(n i : ℝ)| = ‖c i‖ := by simp [c]
      _ ≤ ‖c‖ := norm_le_pi_norm c i
      _ ≤ Kc * ‖Φ c‖ := hc
      _ ≤ T := mul_le_mul_of_nonneg_left hΦ Kc.2
  have hfin : (Set.pi Set.univ fun _ : Fin r => Set.Icc (-⌈T⌉) ⌈T⌉).Finite :=
    Set.Finite.pi fun _ => Set.finite_Icc _ _
  refine (hfin.image fun n => ∑ i, n i • aeval y (g i)).subset ?_
  rintro σ ⟨hσ, hsmall⟩
  set n : Fin r → ℤ := fun i => b.repr ⟨σ, hσ⟩ i
  have hσn : aeval y (∑ i, n i • g i) = σ := by
    rw [map_sum]
    simp_rw [map_zsmul, hgy]
    have := congrArg Subtype.val (b.sum_repr ⟨σ, hσ⟩)
    rw [Submodule.coe_sum] at this
    simpa only [Submodule.coe_smul] using this
  have hb := hbox n fun z hz => by
    have := hsmall _ (hsum n) hσn z hz
    simpa [G, map_sum, zsmul_eq_mul] using this
  refine ⟨n, fun i _ => ?_, by simpa [map_sum] using hσn⟩
  have := abs_le.mp (hb i)
  constructor
  · have h := Int.le_ceil T
    exact_mod_cast (show (-(⌈T⌉ : ℝ)) ≤ n i by linarith [this.1])
  · have h := Int.le_ceil T
    exact_mod_cast (show (n i : ℝ) ≤ ⌈T⌉ by linarith [this.2])

end

end GroundTheory.Heights₂.Heights.ForSecondHalf

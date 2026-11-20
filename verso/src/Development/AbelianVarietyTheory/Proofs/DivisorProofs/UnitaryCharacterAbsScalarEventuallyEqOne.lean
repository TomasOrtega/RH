import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenNormClosedBallQuadraticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadExtTopologyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar

noncomputable section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary ValuativeRel Filter
open scoped Topology
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ _ c δ hE m χ hχ`. Take `⟨hfd, htr, hinv, ht2, -, hN, -, -⟩` from `GlobalTheory.T.quadExt_topological_properties F E c δ hE`. Take `⟨L, hL, hLc, hLo⟩` from `GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic F E c δ hE 1`. Establish `h0 : {t : Eˣ | ‖(χ t : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : Eˣ)` using `(isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)`. Rewrite `h0` using `[Units.isEmbedding_val₀.nhds_eq_comap, mem_comap]`.

Take `⟨U, hU, hUV⟩` from `h0`. Establish `h1 : ∀ᶠ π in 𝓝 (0 : F), ∀ a ∈ (L : Set E), 1 + π • a ∈ U`. Use `hLc.eventually_forall_of_forall_eventually fun a _ => ?_` and prove the remaining obligations. Establish `: Tendsto (fun q : F × E => 1 + q.1 • q.2) (𝓝 (0, a)) (𝓝 1)` using `Continuous.tendsto' (by fun_prop) _ _ (by simp)`. Conclude with `this hU`.

Establish `h2 : {x : F | valuation F x < 1} ∈ 𝓝 (0 : F)` using `(IsValuativeTopology.mem_nhds_zero_iff _).mpr ⟨1, fun _ h => h⟩`. Take `⟨s, hs⟩` from `GlobalTheory.SplitWeil.exists_cball_subset (inter_mem h1 h2)`. Take `⟨hsU, hsv⟩` from `hs (show (s : F) ∈ GlobalTheory.SplitWeil.cball s from show valuation F (s : F) ≤ valuation F (s : F) from le_rfl)`. Use `set π : F := (s : F) with hπdef`. Establish `hπ : π ≠ 0` using `s.ne_zero`.

Establish `hmul : ∀ a ∈ (L : Set E), ∀ b ∈ (L : Set E), a * b ∈ (L : Set E)`. Introduce `a ha b hb`. Rewrite `ha`, `hb`, the goal using `[hL]`. Use `show valuation F (Algebra.norm F (a * b)) ≤ valuation F ((1 : Fˣ) : F)`. Establish `ha' : valuation F (Algebra.norm F a) ≤ 1` using `by simpa [GlobalTheory.SplitWeil.cball] using ha`.

Establish `hb' : valuation F (Algebra.norm F b) ≤ 1` using `by simpa [GlobalTheory.SplitWeil.cball] using hb`. Rewrite using `[map_mul, map_mul]`. Simplify using `using mul_le_one' ha' hb'`. Establish `hsm : ∀ a ∈ (L : Set E), π • a ∈ (L : Set E)`. Introduce `a ha`.

Rewrite `ha`, the goal using `[hL]`. Use `show valuation F (Algebra.norm F (π • a)) ≤ valuation F ((1 : Fˣ) : F)`. Establish `ha' : valuation F (Algebra.norm F a) ≤ 1` using `by simpa [GlobalTheory.SplitWeil.cball] using ha`. Rewrite using `[Algebra.smul_def, map_mul, Algebra.norm_algebraMap, map_mul, map_pow]`. Simplify using `using mul_le_one' (pow_le_one' hsv.le _) ha'`.

Use `set V : Set E := {z | π⁻¹ • (z - 1) ∈ (L : Set E)} with hVdef`. Establish `hVo : IsOpen V` using `hLo.preimage (by fun_prop)`. Establish `hV1 : (1 : E) ∈ V` using `by simp [V, L.zero_mem]`. Establish `hVU : V ⊆ U`. Introduce `z hz`.

Use `hsU _ hz` as an intermediate fact. Rewrite `this` using `[smul_smul, mul_inv_cancel₀ hπ, one_smul, add_sub_cancel]`. Then use the resulting hypothesis. Establish `hVpow : ∀ z ∈ V, ∀ n : ℕ, z ^ n ∈ V`. Introduce `z hz n`. Proceed by induction on `n with`.

Consider the case `zero => simpa using hV1`. Consider the case `succ n ih => show π⁻¹ • (z ^ (n + 1) - 1) ∈ (L : Set E)`. Establish `hz' : z = 1 + π • (π⁻¹ • (z - 1))`. Rewrite using `[smul_smul, mul_inv_cancel₀ hπ, one_smul, add_sub_cancel]`. Establish `e : π⁻¹ • (z ^ (n + 1) - 1) = π⁻¹ • (z ^ n - 1) + π • ((π⁻¹ • (z - 1)) * (π⁻¹ • (z ^ n - 1))) + π⁻¹ • (z - 1)`.

Establish `hp : algebraMap F E π ≠ 0` using `(map_ne_zero _).mpr hπ`. Simplify using `only [Algebra.smul_def, map_inv₀]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `L.add_mem (L.add_mem ih (hsm _ (hmul _ hz _ ih))) hz`. Establish `h3 : Tendsto (fun z : E => Algebra.norm F z - 1) (𝓝 1) (𝓝 0)` using `Continuous.tendsto' (by fun_prop) _ _ (by simp)`. Use `filter_upwards [hVo.mem_nhds hV1, eventually_ne_nhds (one_ne_zero : (1 : E) ≠ 0), h3.eventually h2] with z hz hz0 hzN`. Establish `hv : valuation F (Algebra.norm F z) = 1`. Simplify using `using (valuation F).map_one_add_of_lt hzN`.

Establish `hχz : χ (Units.mk0 z hz0) = 1`. Use `Circle.coe_eq_one.mp (GlobalTheory.WeilM.eq_one_of_forall_pow_near fun n => ?_)` and prove the remaining obligations. Establish `: (Units.mk0 z hz0) ^ n ∈ Units.val ⁻¹' U` using `by simpa using hVU (hVpow z hz n)`. Simplify using `using hUV this`. Establish `hn : nabs F (Units.map (Algebra.norm F : E →* F) (Units.mk0 z hz0)) = 1` using `GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one (by simpa using hv)`.

Simplify using `[sc, hz0, hχz, hn]`.
-/
theorem sc_eventually_eq_one : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (m : ℕ) (χ : Eˣ →* Circle) (_ : Continuous χ),
    ∀ᶠ z in nhds (1 : E), sc F χ m z = 1 := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE m χ hχ
  obtain ⟨hfd, htr, hinv, ht2, -, hN, -, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  obtain ⟨L, hL, hLc, hLo⟩ := GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic F E c δ hE 1

  have h0 : {t : Eˣ | ‖(χ t : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : Eˣ) :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
  rw [Units.isEmbedding_val₀.nhds_eq_comap, mem_comap] at h0
  obtain ⟨U, hU, hUV⟩ := h0

  have h1 : ∀ᶠ π in 𝓝 (0 : F), ∀ a ∈ (L : Set E), 1 + π • a ∈ U := by
    refine hLc.eventually_forall_of_forall_eventually fun a _ => ?_
    have : Tendsto (fun q : F × E => 1 + q.1 • q.2) (𝓝 (0, a)) (𝓝 1) :=
      Continuous.tendsto' (by fun_prop) _ _ (by simp)
    exact this hU
  have h2 : {x : F | valuation F x < 1} ∈ 𝓝 (0 : F) := (IsValuativeTopology.mem_nhds_zero_iff _).mpr ⟨1, fun _ h => h⟩
  obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset (inter_mem h1 h2)
  obtain ⟨hsU, hsv⟩ := hs (show (s : F) ∈ GlobalTheory.SplitWeil.cball s from show valuation F (s : F) ≤ valuation F (s : F) from le_rfl)
  set π : F := (s : F) with hπdef
  have hπ : π ≠ 0 := s.ne_zero

  have hmul : ∀ a ∈ (L : Set E), ∀ b ∈ (L : Set E), a * b ∈ (L : Set E) := by
    intro a ha b hb
    rw [hL] at ha hb ⊢
    show valuation F (Algebra.norm F (a * b)) ≤ valuation F ((1 : Fˣ) : F)
    have ha' : valuation F (Algebra.norm F a) ≤ 1 := by simpa [GlobalTheory.SplitWeil.cball] using ha
    have hb' : valuation F (Algebra.norm F b) ≤ 1 := by simpa [GlobalTheory.SplitWeil.cball] using hb
    rw [map_mul, map_mul]
    simpa using mul_le_one' ha' hb'
  have hsm : ∀ a ∈ (L : Set E), π • a ∈ (L : Set E) := by
    intro a ha
    rw [hL] at ha ⊢
    show valuation F (Algebra.norm F (π • a)) ≤ valuation F ((1 : Fˣ) : F)
    have ha' : valuation F (Algebra.norm F a) ≤ 1 := by simpa [GlobalTheory.SplitWeil.cball] using ha
    rw [Algebra.smul_def, map_mul, Algebra.norm_algebraMap, map_mul, map_pow]
    simpa using mul_le_one' (pow_le_one' hsv.le _) ha'

  set V : Set E := {z | π⁻¹ • (z - 1) ∈ (L : Set E)} with hVdef
  have hVo : IsOpen V := hLo.preimage (by fun_prop)
  have hV1 : (1 : E) ∈ V := by simp [V, L.zero_mem]
  have hVU : V ⊆ U := by
    intro z hz
    have := hsU _ hz
    rwa [smul_smul, mul_inv_cancel₀ hπ, one_smul, add_sub_cancel] at this
  have hVpow : ∀ z ∈ V, ∀ n : ℕ, z ^ n ∈ V := by
    intro z hz n
    induction n with
    | zero => simpa using hV1
    | succ n ih =>
      show π⁻¹ • (z ^ (n + 1) - 1) ∈ (L : Set E)
      have hz' : z = 1 + π • (π⁻¹ • (z - 1)) := by
        rw [smul_smul, mul_inv_cancel₀ hπ, one_smul, add_sub_cancel]
      have e : π⁻¹ • (z ^ (n + 1) - 1) =
          π⁻¹ • (z ^ n - 1) + π • ((π⁻¹ • (z - 1)) * (π⁻¹ • (z ^ n - 1))) + π⁻¹ • (z - 1) := by
        have hp : algebraMap F E π ≠ 0 := (map_ne_zero _).mpr hπ
        simp only [Algebra.smul_def, map_inv₀]
        field_simp
        ring
      rw [e]
      exact L.add_mem (L.add_mem ih (hsm _ (hmul _ hz _ ih))) hz

  have h3 : Tendsto (fun z : E => Algebra.norm F z - 1) (𝓝 1) (𝓝 0) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  filter_upwards [hVo.mem_nhds hV1, eventually_ne_nhds (one_ne_zero : (1 : E) ≠ 0), h3.eventually h2] with z hz hz0 hzN
  have hv : valuation F (Algebra.norm F z) = 1 := by
    simpa using (valuation F).map_one_add_of_lt hzN
  have hχz : χ (Units.mk0 z hz0) = 1 := by
    refine Circle.coe_eq_one.mp (GlobalTheory.WeilM.eq_one_of_forall_pow_near fun n => ?_)
    have : (Units.mk0 z hz0) ^ n ∈ Units.val ⁻¹' U := by simpa using hVU (hVpow z hz n)
    simpa using hUV this
  have hn : nabs F (Units.map (Algebra.norm F : E →* F) (Units.mk0 z hz0)) = 1 :=
    GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one (by simpa using hv)
  simp [sc, hz0, hχz, hn]

end GlobalTheory.KSp

end

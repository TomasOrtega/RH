import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorUnitaryAdelicL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledCosetIndicatorSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaledIntegralFiniteAdelePointsSubsetNhds

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.LagrFormNZ

/- English proof (translation)
Establish `hinj : Function.Injective (Fintype.linearCombination F a)` using `linearIndependent_iff_injective_fintypeLinearCombination.mp ha`. Take `⟨L, hL⟩` from `LinearMap.exists_leftInverse_of_injective (Fintype.linearCombination F a) (LinearMap.ker_eq_bot.2 hinj)`. Use `⟨LinearMap.toMatrix' L, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.toMatrix'_mulVec]`. Use `LinearMap.congr_fun hL (Pi.single j 1)` as an intermediate fact.

Simplify `this` using `[Fintype.linearCombination_apply_single]`.
-/
theorem exists_leftInv {F : Type} [Field F] {κ : Type} [Fintype κ] {r : ℕ} (a : Fin r → κ → F)
    (ha : LinearIndependent F a) : ∃ C : Matrix (Fin r) κ F, ∀ j, C *ᵥ a j = Pi.single j 1 := by
  have hinj : Function.Injective (Fintype.linearCombination F a) :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp ha
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective (Fintype.linearCombination F a)
    (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' L, fun j => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  have := LinearMap.congr_fun hL (Pi.single j 1)
  simpa [Fintype.linearCombination_apply_single] using this

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `h1 : ∀ j, (C.map (algebraMap F (AF F)) *ᵥ fun k => algebraMap F (AF F) (a j k)) i = algebraMap F (AF F) ((Pi.single j (1 : F) : Fin r → F) i)` using `fun j => by`. Rewrite using `[← hC j, RingHom.map_mulVec]`. Both sides reduce to the same expression. Rewrite using `[Matrix.mulVec_sum, Finset.sum_apply]`.

Simplify using `only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, h1]`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[Pi.single_apply, Ne.symm hj]`.

Simplify using the standard rewrite rules.
-/
theorem mulVec_sum_eq {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {r : ℕ} (a : Fin r → κ → F)
    (C : Matrix (Fin r) κ F) (hC : ∀ j, C *ᵥ a j = Pi.single j 1) (x : Fin r → AF F) :
    C.map (algebraMap F (AF F)) *ᵥ (∑ j, x j • fun k => algebraMap F (AF F) (a j k)) = x := by
  funext i
  have h1 : ∀ j, (C.map (algebraMap F (AF F)) *ᵥ fun k => algebraMap F (AF F) (a j k)) i =
      algebraMap F (AF F) ((Pi.single j (1 : F) : Fin r → F) i) := fun j => by
    rw [← hC j, RingHom.map_mulVec]; rfl
  rw [Matrix.mulVec_sum, Finset.sum_apply]
  simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, h1]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_apply, Ne.symm hj]
  · simp

end GlobalTheory.LagrFormNZ

namespace GlobalTheory.LagrFormNZ

/- English proof (translation)
Introduce `F _ _ ψ hψ κ _ r u hu μ hμ`. Use `letI : MeasurableSpace (Fin r → AF F) := borel _`. Use `haveI : BorelSpace (Fin r → AF F) := ⟨rfl⟩`. Use `haveI := hμ`. Take `⟨C, hC⟩` from `exists_leftInv (fun j => (u j).1) hu`.

Use `set U : Fin r → (κ → AF F) × (κ → AF F) := fun j => ((fun k => algebraMap F (AF F) ((u j).1 k)), (fun k => algebraMap F (AF F) ((u j).2 k))) with hU`. Use `set Cm : Matrix (Fin r) κ (AF F) := C.map (algebraMap F (AF F)) with hCm`. Establish `hfst : ∀ x : Fin r → AF F, (∑ j, x j • U j).1 = ∑ j, x j • fun k => algebraMap F (AF F) ((u j).1 k)`. Introduce `x`. Simplify using `[U, Prod.fst_sum]`.

Establish `hleft : ∀ x : Fin r → AF F, Cm *ᵥ (∑ j, x j • U j).1 = x` using `fun x => by`. Rewrite using `[hfst]`. Conclude with `mulVec_sum_eq (fun j => (u j).1) C hC x`. Establish `hXc : Continuous fun x : Fin r → AF F => ∑ j, x j • U j` using `continuous_finset_sum _ fun j _ => (continuous_apply j).smul continuous_const`. Use `set H : (Fin r → AF F) → ℂ := fun x => ψ (0 ⬝ᵥ (∑ j, x j • U j).2 + ⅟(2 : AF F) * ((∑ j, x j • U j).1 ⬝ᵥ (∑ j, x j • U j).2)) with hH`.

Establish `hHc : Continuous H` using `hψ.1.comp ((continuous_const.dotProduct (continuous_snd.comp hXc)).add (continuous_const.mul ((continuous_fst.comp hXc).dotProduct (continuous_snd.comp hXc))))`. Use `set G : (κ → AF F) → ℂ := fun y => H (Cm *ᵥ y) with hGdef`. Establish `hGc : Continuous G` using `hHc.comp (Continuous.matrix_mulVec continuous_const continuous_id)`. Establish `hG0 : G 0 = 1` using `by simp [G, H]`. Establish `hV : {y | 0 < (G y).re} ∈ 𝓝 (0 : κ → AF F)` using `(isOpen_lt continuous_const (Complex.continuous_re.comp hGc)).mem_nhds (by simp [hG0])`.

Use `set e := GlobalTheory.ArchimedeanL2.splitEquiv F κ with he`. Establish `he0 : e.symm (0, 0) = 0` using `map_zero e.symm`. Establish `hW : e.symm ⁻¹' {y | 0 < (G y).re} ∈ 𝓝 ((0 : κ → mixedEmbedding.mixedSpace F), (0 : κ → Af F))`. Establish `hV' : {y | 0 < (G y).re} ∈ 𝓝 (e.symm (0, 0))` using `by rw [he0]; exact hV`. Conclude with `e.symm.continuous.tendsto (0, 0) hV'`.

Take `⟨U1, hU1, U2, hU2, hsub⟩` from `mem_nhds_prod_iff.1 hW`. Take `⟨δ, hδ, hball⟩` from `Metric.mem_nhds_iff.1 hU1`. Take `⟨c, hc0, hcs⟩` from `GlobalTheory.EvAdm.exists_scaledInt_subset_of_mem_nhds F κ U2 hU2`. Set `b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F)` to `⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩`. Establish `h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ))` using `b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)`.

Set `f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ` to `h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)`. Establish `hf : ∀ x, f x = ((b x : ℝ) : ℂ)` using `fun x => rfl`. Use `set S : Set (κ → Af F) := {y | y - 0 ∈ GlobalTheory.EvAdm.scaledInt F κ c} with hS`. Use `set g : (κ → Af F) → ℂ := S.indicator (fun _ => (1 : ℂ)) with hg`. Establish `hgSB : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)` using `GlobalTheory.EvAdm.indicator_coset_scaledInt_mem_SB F κ c hc0 0`.

Use `set φ := pureA F f g with hφ`. Establish `hφmem : φ ∈ schA F κ` using `Submodule.subset_span ⟨f, g, hgSB, rfl⟩`. Establish `hφe : ∀ y, φ y = f (e y).1 * g (e y).2` using `fun y => rfl`. Use `⟨φ, hφmem, ?_⟩` and prove the remaining obligations. Establish `hφcases : ∀ y, φ y = ((b (e y).1 : ℝ) : ℂ) ∧ (e y).2 ∈ S ∨ φ y = 0 ∧ (e y).2 ∉ S`.

Introduce `y`. Rewrite using `[hφe, hf]`. Distinguish the cases in `hq : (e y).2 ∈ S`. Use `left`. Simplify using `[g, Set.indicator_of_mem hq, hq]`.

Use `right`. Simplify using `[g, Set.indicator_of_notMem hq, hq]`. Establish `hφim : ∀ y, (φ y).im = 0` using `fun y => by`. Apply the tactic sequence `rcases hφcases y with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]`. Establish `hφre : ∀ y, 0 ≤ (φ y).re` using `fun y => by`.

Apply the tactic sequence `rcases hφcases y with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h, b.nonneg]`. Establish `hφmemK : ∀ y, φ y ≠ 0 → (e y).1 ∈ Metric.ball (0 : κ → mixedEmbedding.mixedSpace F) δ ∧ (e y).2 ∈ (GlobalTheory.EvAdm.scaledInt F κ c : Set (κ → Af F))`. Introduce `y hy`. Break down `hφcases y with ⟨h, hq⟩ | ⟨h, _⟩` into its components or cases. Use `⟨?_, by simpa [S] using hq⟩` and prove the remaining obligations.

Establish `: b (e y).1 ≠ 0`. Introduce `h0`. Apply `hy` to reduce the goal to its premises. Rewrite using `[h, h0]`. Simplify using the standard rewrite rules.

Establish `hs : (e y).1 ∈ Function.support b` using `this`. Rewrite `hs` using `[b.support_eq]`. Conclude with `hs`. Conclude with `absurd h hy`. Establish `hφV : ∀ y, φ y ≠ 0 → 0 < (G y).re`.

Introduce `y hy`. Take `⟨h1, h2⟩` from `hφmemK y hy`. Establish `: e y ∈ U1 ×ˢ U2` using `⟨hball h1, hcs h2⟩`. Use `hsub this` as an intermediate fact. Simplify using `using this`.

Establish `hφ0 : φ 0 = 1`. Establish `e0 : e 0 = (0, 0)` using `map_zero e`. Rewrite using `[hφe, e0, hf]`. Establish `hb : b 0 = 1` using `b.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hδ).le)`. Establish `h0S : (0 : κ → Af F) ∈ S` using `by simp [S]`.

Simplify using `[g, Set.indicator_of_mem h0S, hb]`. Establish `hφc : Continuous φ`. Establish `hg : Continuous g` using `hgSB.1.continuous`. Conclude with `(f.continuous.comp (continuous_fst.comp e.continuous)).mul (hg.comp (continuous_snd.comp e.continuous))`. Use `set I : (Fin r → AF F) → ℂ := fun x => schr ψ (∑ j, x j • U j) φ 0 with hIdef`.

Establish `hI : ∀ x, I x = G (∑ j, x j • U j).1 * φ (∑ j, x j • U j).1`. Introduce `x`. Use `show ψ _ * φ (0 + _) = H (Cm *ᵥ _) * _`. Rewrite using `[hleft, zero_add]`. Establish `hIc : Continuous I`.

Establish `: I = fun x => G (∑ j, x j • U j).1 * φ (∑ j, x j • U j).1` using `funext hI`. Rewrite using `[this]`. Conclude with `(hGc.comp (continuous_fst.comp hXc)).mul (hφc.comp (continuous_fst.comp hXc))`. Use `set K : Set ((κ → mixedEmbedding.mixedSpace F) × (κ → Af F)) := Metric.closedBall 0 δ ×ˢ (GlobalTheory.EvAdm.scaledInt F κ c : Set (κ → Af F)) with hK`. Establish `hKc : IsCompact K` using `(isCompact_closedBall _ _).prod (GlobalTheory.EvAdm.isCompact_scaledInt_of_ne_zero hc0)`.

Establish `hKcl : IsClosed K` using `Metric.isClosed_closedBall.prod ((GlobalTheory.EvAdm.scaledInt F κ c).isClosed_of_isOpen (GlobalTheory.EvAdm.isOpen_scaledInt c))`. Use `set T : Set (Fin r → AF F) := {x | e (∑ j, x j • U j).1 ∈ K} with hT`. Establish `hTcl : IsClosed T` using `hKcl.preimage (e.continuous.comp (continuous_fst.comp hXc))`. Establish `hTsub : T ⊆ (fun p => Cm *ᵥ e.symm p) '' K`. Introduce `x hx`.

Conclude with `⟨_, hx, by simp only [e.symm_apply_apply, hleft]⟩`. Establish `hes : Continuous (e.symm : _ → _)` using `e.symm.continuous`. Establish `hcm : Continuous fun p => Cm *ᵥ e.symm p` using `Continuous.matrix_mulVec continuous_const hes`. Establish `hTc : IsCompact T` using `(hKc.image hcm).of_isClosed_subset hTcl hTsub`. Establish `hsupp : Function.support I ⊆ T`.

Introduce `x hx`. Establish `hne : φ (∑ j, x j • U j).1 ≠ 0`. Introduce `h0`. Apply `hx` to reduce the goal to its premises. Rewrite using `[hI, h0, mul_zero]`.

Take `⟨h1, h2⟩` from `hφmemK _ hne`. Conclude with `⟨Metric.ball_subset_closedBall h1, h2⟩`. Establish `hIcs : HasCompactSupport I` using `hTc.of_isClosed_subset (isClosed_tsupport I) (closure_minimal hsupp hTcl)`. Establish `hIint : Integrable I μ` using `hIc.integrable_of_hasCompactSupport hIcs`. Establish `hre : ∀ x, (I x).re = (G (∑ j, x j • U j).1).re * (φ (∑ j, x j • U j).1).re`.

Introduce `x`. Rewrite using `[hI, Complex.mul_re, hφim, mul_zero, sub_zero]`. Establish `hnn : 0 ≤ fun x => (I x).re`. Introduce `x`. Use `show 0 ≤ (I x).re`.

Rewrite using `[hre]`. Distinguish the cases in `h0 : φ (∑ j, x j • U j).1 = 0`. Simplify using `[h0]`. Conclude with `mul_nonneg (hφV _ h0).le (hφre _)`. Establish `hI0 : (I 0).re = 1`.

Rewrite using `[hre]`. Establish `: (∑ j, (0 : Fin r → AF F) j • U j).1 = 0` using `by simp`. Rewrite using `[this, hG0, hφ0]`. Simplify using the standard rewrite rules. Establish `hpos : 0 < ∫ x, (I x).re ∂μ`.

Rewrite using `[integral_pos_iff_support_of_nonneg hnn hIint.re]`. Conclude with `(Complex.continuous_re.comp hIc).isOpen_support.measure_pos μ ⟨0, by simp [Function.mem_support, hI0]⟩`. Introduce `hzero`. Use `integral_re hIint` as an intermediate fact. Express the relevant statement in the definitionally equal form `∫ x, (I x).re ∂μ = (∫ x, I x ∂μ).re at this`.

Rewrite `this` using `[show (∫ x, I x ∂μ) = 0 from hzero, Complex.zero_re]`. Conclude with `hpos.ne' this`.
-/
theorem lagrForm_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (r : ℕ) (u : Fin r → (κ → F) × (κ → F)), LinearIndependent F (fun j => (u j).1) →
    ∀ μ : @Measure (Fin r → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ φ ∈ schA F κ, ∫ x, schr ψ (∑ j, x j • ((fun k => algebraMap F (AF F) ((u j).1 k)),
      (fun k => algebraMap F (AF F) ((u j).2 k)))) φ 0 ∂μ ≠ 0 := by
  intro F _ _ ψ hψ κ _ r u hu μ hμ
  letI : MeasurableSpace (Fin r → AF F) := borel _
  haveI : BorelSpace (Fin r → AF F) := ⟨rfl⟩
  haveI := hμ
  obtain ⟨C, hC⟩ := exists_leftInv (fun j => (u j).1) hu
  set U : Fin r → (κ → AF F) × (κ → AF F) := fun j => ((fun k => algebraMap F (AF F) ((u j).1 k)),
    (fun k => algebraMap F (AF F) ((u j).2 k))) with hU
  set Cm : Matrix (Fin r) κ (AF F) := C.map (algebraMap F (AF F)) with hCm
  have hfst : ∀ x : Fin r → AF F, (∑ j, x j • U j).1 = ∑ j, x j • fun k => algebraMap F (AF F) ((u j).1 k) := by
    intro x; simp [U, Prod.fst_sum]
  have hleft : ∀ x : Fin r → AF F, Cm *ᵥ (∑ j, x j • U j).1 = x := fun x => by
    rw [hfst]; exact mulVec_sum_eq (fun j => (u j).1) C hC x
  have hXc : Continuous fun x : Fin r → AF F => ∑ j, x j • U j :=
    continuous_finset_sum _ fun j _ => (continuous_apply j).smul continuous_const
  set H : (Fin r → AF F) → ℂ := fun x => ψ (0 ⬝ᵥ (∑ j, x j • U j).2 +
    ⅟(2 : AF F) * ((∑ j, x j • U j).1 ⬝ᵥ (∑ j, x j • U j).2)) with hH
  have hHc : Continuous H := hψ.1.comp ((continuous_const.dotProduct (continuous_snd.comp hXc)).add
    (continuous_const.mul ((continuous_fst.comp hXc).dotProduct (continuous_snd.comp hXc))))
  set G : (κ → AF F) → ℂ := fun y => H (Cm *ᵥ y) with hGdef
  have hGc : Continuous G := hHc.comp (Continuous.matrix_mulVec continuous_const continuous_id)
  have hG0 : G 0 = 1 := by simp [G, H]
  have hV : {y | 0 < (G y).re} ∈ 𝓝 (0 : κ → AF F) :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp hGc)).mem_nhds (by simp [hG0])
  set e := GlobalTheory.ArchimedeanL2.splitEquiv F κ with he
  have he0 : e.symm (0, 0) = 0 := map_zero e.symm
  have hW : e.symm ⁻¹' {y | 0 < (G y).re} ∈ 𝓝 ((0 : κ → mixedEmbedding.mixedSpace F), (0 : κ → Af F)) := by
    have hV' : {y | 0 < (G y).re} ∈ 𝓝 (e.symm (0, 0)) := by rw [he0]; exact hV
    exact e.symm.continuous.tendsto (0, 0) hV'
  obtain ⟨U1, hU1, U2, hU2, hsub⟩ := mem_nhds_prod_iff.1 hW
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU1
  obtain ⟨c, hc0, hcs⟩ := GlobalTheory.EvAdm.exists_scaledInt_subset_of_mem_nhds F κ U2 hU2
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
    h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hf : ∀ x, f x = ((b x : ℝ) : ℂ) := fun x => rfl
  set S : Set (κ → Af F) := {y | y - 0 ∈ GlobalTheory.EvAdm.scaledInt F κ c} with hS
  set g : (κ → Af F) → ℂ := S.indicator (fun _ => (1 : ℂ)) with hg
  have hgSB : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := GlobalTheory.EvAdm.indicator_coset_scaledInt_mem_SB F κ c hc0 0
  set φ := pureA F f g with hφ
  have hφmem : φ ∈ schA F κ := Submodule.subset_span ⟨f, g, hgSB, rfl⟩
  have hφe : ∀ y, φ y = f (e y).1 * g (e y).2 := fun y => rfl
  refine ⟨φ, hφmem, ?_⟩
  have hφcases : ∀ y, φ y = ((b (e y).1 : ℝ) : ℂ) ∧ (e y).2 ∈ S ∨ φ y = 0 ∧ (e y).2 ∉ S := by
    intro y
    rw [hφe, hf]
    by_cases hq : (e y).2 ∈ S
    · left; simp [g, Set.indicator_of_mem hq, hq]
    · right; simp [g, Set.indicator_of_notMem hq, hq]
  have hφim : ∀ y, (φ y).im = 0 := fun y => by
    rcases hφcases y with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have hφre : ∀ y, 0 ≤ (φ y).re := fun y => by
    rcases hφcases y with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h, b.nonneg]
  have hφmemK : ∀ y, φ y ≠ 0 → (e y).1 ∈ Metric.ball (0 : κ → mixedEmbedding.mixedSpace F) δ ∧
      (e y).2 ∈ (GlobalTheory.EvAdm.scaledInt F κ c : Set (κ → Af F)) := by
    intro y hy
    rcases hφcases y with ⟨h, hq⟩ | ⟨h, _⟩
    · refine ⟨?_, by simpa [S] using hq⟩
      have : b (e y).1 ≠ 0 := by
        intro h0; apply hy; rw [h, h0]; simp
      have hs : (e y).1 ∈ Function.support b := this
      rw [b.support_eq] at hs
      exact hs
    · exact absurd h hy
  have hφV : ∀ y, φ y ≠ 0 → 0 < (G y).re := by
    intro y hy
    obtain ⟨h1, h2⟩ := hφmemK y hy
    have : e y ∈ U1 ×ˢ U2 := ⟨hball h1, hcs h2⟩
    have := hsub this
    simpa using this
  have hφ0 : φ 0 = 1 := by
    have e0 : e 0 = (0, 0) := map_zero e
    rw [hφe, e0, hf]
    have hb : b 0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hδ).le)
    have h0S : (0 : κ → Af F) ∈ S := by simp [S]
    simp [g, Set.indicator_of_mem h0S, hb]
  have hφc : Continuous φ := by
    have hg : Continuous g := hgSB.1.continuous
    exact (f.continuous.comp (continuous_fst.comp e.continuous)).mul (hg.comp (continuous_snd.comp e.continuous))
  set I : (Fin r → AF F) → ℂ := fun x => schr ψ (∑ j, x j • U j) φ 0 with hIdef
  have hI : ∀ x, I x = G (∑ j, x j • U j).1 * φ (∑ j, x j • U j).1 := by
    intro x
    show ψ _ * φ (0 + _) = H (Cm *ᵥ _) * _
    rw [hleft, zero_add]
  have hIc : Continuous I := by
    have : I = fun x => G (∑ j, x j • U j).1 * φ (∑ j, x j • U j).1 := funext hI
    rw [this]
    exact (hGc.comp (continuous_fst.comp hXc)).mul (hφc.comp (continuous_fst.comp hXc))

  set K : Set ((κ → mixedEmbedding.mixedSpace F) × (κ → Af F)) :=
    Metric.closedBall 0 δ ×ˢ (GlobalTheory.EvAdm.scaledInt F κ c : Set (κ → Af F)) with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod (GlobalTheory.EvAdm.isCompact_scaledInt_of_ne_zero hc0)
  have hKcl : IsClosed K := Metric.isClosed_closedBall.prod
    ((GlobalTheory.EvAdm.scaledInt F κ c).isClosed_of_isOpen (GlobalTheory.EvAdm.isOpen_scaledInt c))
  set T : Set (Fin r → AF F) := {x | e (∑ j, x j • U j).1 ∈ K} with hT
  have hTcl : IsClosed T := hKcl.preimage (e.continuous.comp (continuous_fst.comp hXc))
  have hTsub : T ⊆ (fun p => Cm *ᵥ e.symm p) '' K := by
    intro x hx
    exact ⟨_, hx, by simp only [e.symm_apply_apply, hleft]⟩
  have hes : Continuous (e.symm : _ → _) := e.symm.continuous
  have hcm : Continuous fun p => Cm *ᵥ e.symm p := Continuous.matrix_mulVec continuous_const hes
  have hTc : IsCompact T := (hKc.image hcm).of_isClosed_subset hTcl hTsub
  have hsupp : Function.support I ⊆ T := by
    intro x hx
    have hne : φ (∑ j, x j • U j).1 ≠ 0 := by
      intro h0; apply hx; rw [hI, h0, mul_zero]
    obtain ⟨h1, h2⟩ := hφmemK _ hne
    exact ⟨Metric.ball_subset_closedBall h1, h2⟩
  have hIcs : HasCompactSupport I := hTc.of_isClosed_subset (isClosed_tsupport I) (closure_minimal hsupp hTcl)
  have hIint : Integrable I μ := hIc.integrable_of_hasCompactSupport hIcs
  have hre : ∀ x, (I x).re = (G (∑ j, x j • U j).1).re * (φ (∑ j, x j • U j).1).re := by
    intro x; rw [hI, Complex.mul_re, hφim, mul_zero, sub_zero]
  have hnn : 0 ≤ fun x => (I x).re := by
    intro x
    show 0 ≤ (I x).re
    rw [hre]
    by_cases h0 : φ (∑ j, x j • U j).1 = 0
    · simp [h0]
    · exact mul_nonneg (hφV _ h0).le (hφre _)
  have hI0 : (I 0).re = 1 := by
    rw [hre]
    have : (∑ j, (0 : Fin r → AF F) j • U j).1 = 0 := by simp
    rw [this, hG0, hφ0]; simp
  have hpos : 0 < ∫ x, (I x).re ∂μ := by
    rw [integral_pos_iff_support_of_nonneg hnn hIint.re]
    exact (Complex.continuous_re.comp hIc).isOpen_support.measure_pos μ ⟨0, by simp [Function.mem_support, hI0]⟩
  intro hzero
  have := integral_re hIint
  change ∫ x, (I x).re ∂μ = (∫ x, I x ∂μ).re at this
  rw [show (∫ x, I x ∂μ) = 0 from hzero, Complex.zero_re] at this
  exact hpos.ne' this

end GlobalTheory.LagrFormNZ

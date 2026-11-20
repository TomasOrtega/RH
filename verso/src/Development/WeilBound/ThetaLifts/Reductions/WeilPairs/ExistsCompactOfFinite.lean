import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceSiegelLawDiagonalLagrangianCharacterIm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceThetaFunctionVacuumConjugatePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousPlaceAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactShellNsmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSymplecticTraceFormAlternatingSwap
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.SplitLagrF

open GlobalTheory.SplitInvFormF

/- English proof (translation)
Set `P : Matrix (Fin nS) (Fin nS) (AEF F E)` to `(JS⁻¹).map (incAF F E)`. Set `Q : Matrix (Fin nT) (Fin nT) (AEF F E)` to `JT.map (incAF F E)`. Set `Y : Matrix (Fin nS) (Fin nT) (AEF F E)` to `(y.map (cAF σ))ᵀ`. Establish `hP : IsUnit P.det`. Use `(Matrix.isUnit_nonsing_inv_det JS (Ne.isUnit hS.2)).map (incAF F E)` as an intermediate fact.

Rewrite `this` using `[RingHom.map_det]`. Then use the resulting hypothesis. Establish `hQ : IsUnit Q.det`. Use `(Ne.isUnit hT.2).map (incAF F E)` as an intermediate fact. Rewrite `this` using `[RingHom.map_det]`. Then use the resulting hypothesis. Establish `hm : P * Y * Q ≠ 0`.

Introduce `h0`. Apply `hy0` to reduce the goal to its premises. Establish `h1 : Y = 0`. Rewrite using `[← Matrix.nonsing_inv_mul_cancel_left P Y hP, ← Matrix.mul_nonsing_inv_cancel_right Q (P * Y) hQ, h0, Matrix.zero_mul, Matrix.mul_zero]`. Use extensionality with `i j`.

Establish `h2 : cAF σ (y i j) = 0` using `congrFun (congrFun h1 j) i`. Rewrite using `[← GlobalTheory.SymplSkew.cAF_cAF σ hσ (y i j), h2, map_zero]`. Both sides reduce to the same expression. Choose the witnesses or unpack the hypotheses as in `⟨a, d, had⟩ : ∃ a d, (P * Y * Q) a d ≠ 0 := by`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Conclude with `hm (Matrix.ext hc)`. Establish `hval : (P * Y * Q) a d = ∑ b, ∑ c, incAF F E (JS⁻¹ a b) * cAF σ (y c b) * incAF F E (JT c d)`. Simplify using `only [Matrix.mul_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Both sides reduce to the same expression. Establish `hem : (P * Y * Q) a d * e = (P * Y * Q) a d`. Rewrite using `[hval, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Establish `e1 : cAF σ (y c b) = e * cAF σ (y c b)` using `by conv_lhs => rw [← hy c b]`. Rewrite using `[map_mul, cAF_cAF he]`. Take the linear combination `(-(incAF F E (JS⁻¹ a b) * incAF F E (JT c d))) * e1`. Establish `hξm : incAF F E ξ₀ * (P * Y * Q) a d ≠ 0` using `fun h => had (((Ne.isUnit hξ).map (incAF F E)).mul_right_eq_zero.1 h)`.

Take `⟨z, hz⟩` from `GlobalTheory.AdelicTraceNondeg.trace_pairing_nondeg F E ψ hψ _ hξm`. Use `⟨Matrix.single d a (e * z), fun i j => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.single_apply] split_ifs`. Rewrite using `[← mul_assoc, he.1]`. Rewrite using `[mul_zero]`.

Establish `hh : hOF σ JS JT (Matrix.single d a (e * z)) y = (P * Y * Q) a d * z`. Rewrite using `[← hem, mul_assoc, hval]`. Unfold `hOF`. Rewrite using `[Finset.sum_eq_single a (fun a' _ ha => by simp [Matrix.single_apply, Ne.symm ha]) (fun h => absurd (Finset.mem_univ a) h), Finset.sum_mul]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single d (fun d' _ hd => by simp [Matrix.single_apply, Ne.symm hd]) (fun h => absurd (Finset.mem_univ d) h), Matrix.single_apply_same]`. Establish `h2 : algebraMap F (AF F) (1 / 2) + algebraMap F (AF F) (1 / 2) = 1`. Rewrite using `[← map_add, show (1 / 2 : F) + 1 / 2 = 1 by norm_num, map_one]`.

Unfold `symplOHF`. Rewrite using `[GlobalTheory.SymplSkew.symplOF_swap F E σ hσ nS nT JS JT hS hT ξ₀ hσξ (Matrix.single d a (e * z)) y, mul_neg, sub_neg_eq_add, ← add_mul, h2, one_mul, symplOF, hh, ← mul_assoc]`. Conclude with `hz`.
-/
theorem exists_detect {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hσ : ∀ x, σ (σ x) = x) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E}
    {JT : Matrix (Fin nT) (Fin nT) E} (hS : IsHermND σ JS) (hT : IsHermND σ JT) {ξ₀ : E} (hξ : ξ₀ ≠ 0)
    (hσξ : σ ξ₀ = -ξ₀) {e : AEF F E} (he : IsSplitIdemF σ e) (y : WOF F E nS nT)
    (hy : ∀ i j, cAF σ e * y i j = y i j) (hy0 : y ≠ 0) :
    ∃ g : WOF F E nS nT, (∀ i j, e * g i j = g i j) ∧
      ψ (symplOHF σ JS JT ξ₀ g y - symplOHF σ JS JT ξ₀ y g) ≠ 1 := by
  classical
  let P : Matrix (Fin nS) (Fin nS) (AEF F E) := (JS⁻¹).map (incAF F E)
  let Q : Matrix (Fin nT) (Fin nT) (AEF F E) := JT.map (incAF F E)
  let Y : Matrix (Fin nS) (Fin nT) (AEF F E) := (y.map (cAF σ))ᵀ
  have hP : IsUnit P.det := by
    have := (Matrix.isUnit_nonsing_inv_det JS (Ne.isUnit hS.2)).map (incAF F E)
    rwa [RingHom.map_det] at this
  have hQ : IsUnit Q.det := by
    have := (Ne.isUnit hT.2).map (incAF F E)
    rwa [RingHom.map_det] at this
  have hm : P * Y * Q ≠ 0 := by
    intro h0
    apply hy0
    have h1 : Y = 0 := by
      rw [← Matrix.nonsing_inv_mul_cancel_left P Y hP, ← Matrix.mul_nonsing_inv_cancel_right Q (P * Y) hQ, h0,
        Matrix.zero_mul, Matrix.mul_zero]
    ext i j
    have h2 : cAF σ (y i j) = 0 := congrFun (congrFun h1 j) i
    rw [← GlobalTheory.SymplSkew.cAF_cAF σ hσ (y i j), h2, map_zero]
    rfl
  obtain ⟨a, d, had⟩ : ∃ a d, (P * Y * Q) a d ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hm (Matrix.ext hc)
  have hval : (P * Y * Q) a d = ∑ b, ∑ c, incAF F E (JS⁻¹ a b) * cAF σ (y c b) * incAF F E (JT c d) := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    rfl
  have hem : (P * Y * Q) a d * e = (P * Y * Q) a d := by
    rw [hval, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    have e1 : cAF σ (y c b) = e * cAF σ (y c b) := by
      conv_lhs => rw [← hy c b]
      rw [map_mul, cAF_cAF he]
    linear_combination (-(incAF F E (JS⁻¹ a b) * incAF F E (JT c d))) * e1
  have hξm : incAF F E ξ₀ * (P * Y * Q) a d ≠ 0 := fun h =>
    had (((Ne.isUnit hξ).map (incAF F E)).mul_right_eq_zero.1 h)
  obtain ⟨z, hz⟩ := GlobalTheory.AdelicTraceNondeg.trace_pairing_nondeg F E ψ hψ _ hξm
  refine ⟨Matrix.single d a (e * z), fun i j => ?_, ?_⟩
  · simp only [Matrix.single_apply]
    split_ifs
    · rw [← mul_assoc, he.1]
    · rw [mul_zero]
  · have hh : hOF σ JS JT (Matrix.single d a (e * z)) y = (P * Y * Q) a d * z := by
      rw [← hem, mul_assoc, hval]
      unfold hOF
      rw [Finset.sum_eq_single a (fun a' _ ha => by simp [Matrix.single_apply, Ne.symm ha])
        (fun h => absurd (Finset.mem_univ a) h), Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_eq_single d (fun d' _ hd => by simp [Matrix.single_apply, Ne.symm hd])
        (fun h => absurd (Finset.mem_univ d) h), Matrix.single_apply_same]
    have h2 : algebraMap F (AF F) (1 / 2) + algebraMap F (AF F) (1 / 2) = 1 := by
      rw [← map_add, show (1 / 2 : F) + 1 / 2 = 1 by norm_num, map_one]
    unfold symplOHF
    rw [GlobalTheory.SymplSkew.symplOF_swap F E σ hσ nS nT JS JT hS hT ξ₀ hσξ (Matrix.single d a (e * z)) y, mul_neg,
      sub_neg_eq_add, ← add_mul, h2, one_mul, symplOF, hh, ← mul_assoc]
    exact hz

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he U hU`. Use `haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)`. Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F`. Take `⟨eh⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)`.

Use `haveI : T2Space (AEF F E) := eh.isEmbedding.t2Space`. Establish `hψ : Continuous B.ψ` using `hB.std.1`. Take `⟨he1, he2, v, ε, hpl, hsum⟩` from `id he`. Take `⟨N, Φ, hΦc, hΦi, hΦr⟩` from `GlobalTheory.PlaceCoordsF.coords_at_place F E v ε hpl nS nT`. Establish `hV : (Φ ⁻¹' (U : Set (WOF F E nS nT))) ∈ nhds (0 : Fin N → v.adicCompletion F)` using `(hU.preimage hΦc).mem_nhds (by rw [Set.mem_preimage, map_zero]; exact U.zero_mem)`.

Take `⟨K, hK, hK0, hKn⟩` from `GlobalTheory.NonarchShell.exists_compact_shell_nsmul F v N _ hV`. Set `Y : Set (WOF F E nS nT)` to `{y | ∀ i j, cAF σ e * y i j = y i j}`. Establish `hYc : IsClosed Y`. Simplify using `only [Y, Set.setOf_forall]`. Conclude with `isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (continuous_const.mul ((continuous_apply j).comp (continuous_apply i))) ((continuous_apply j).comp (continuous_apply i))`.

Establish `hcc : cAF σ e * cAF σ e = cAF σ e` using `by rw [← map_mul, he1]`. Establish `hYε : ∀ y ∈ Y, ∀ i j, algebraMap (AF F) (AEF F E) ε * y i j = y i j`. Introduce `y hy i j`. Rewrite using `[← hsum, ← hy i j]`. Take the linear combination `(y i j) * he2 + (y i j) * hcc`.

Establish `hYn : ∀ y ∈ Y, ∀ n : ℕ, n • y ∈ Y`. Introduce `y hy n i j`. Use `show cAF σ e * (n • y i j) = n • y i j`. Rewrite using `[mul_smul_comm, hy i j]`. Set `χ : WOF F E nS nT → WOF F E nS nT → ℂ` to `fun g y => B.ψ (symplOHF σ JS JT ξ₀ g y - symplOHF σ JS JT ξ₀ y g)`.

Establish `hχc : ∀ g, Continuous (χ g)` using `fun g => hψ.comp ((GlobalTheory.HeisThetaF.continuous_symplOHF_right g).sub (GlobalTheory.HeisThetaF.continuous_symplOHF_left g))`. Establish `hχn : ∀ g y (n : ℕ), χ g (n • y) = χ g y ^ n`. Introduce `g y n`. Proceed by induction on `n with`. Consider the case `zero`.

Simplify using `only [χ, zero_smul, GlobalTheory.HeisThetaF.symplOHF_zero_left, GlobalTheory.HeisThetaF.symplOHF_zero_right, sub_zero, AddChar.map_zero_eq_one, pow_zero]`. Consider the case `succ n ih`. Rewrite using `[succ_nsmul, pow_succ, ← ih]`. Simplify using `only [χ]`. Rewrite using `[GlobalTheory.HeisThetaF.symplOHF_add_left, GlobalTheory.HeisThetaF.symplOHF_add_right, ← AddChar.map_add_eq_mul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Set `S : Set (WOF F E nS nT)` to `Φ '' K ∩ Y`. Establish `hSc : IsCompact S` using `(hK.image hΦc).inter_right hYc`. Establish `hSdet : ∀ s ∈ S, ∃ g : WOF F E nS nT, (∀ i j, e * g i j = g i j) ∧ χ g s ≠ 1`.

Introduce and unpack `s ⟨⟨k, hk, rfl⟩, hsY⟩`. Use `exists_detect (GlobalTheory.SplitDetCharF.sig_invol hB.cm) hB.std hS hT hξ hσξ he _ hsY ?_` and prove the remaining obligations. Introduce `h0`. Apply `hK0` to reduce the goal to its premises. Rewrite `h0` using `[← map_zero Φ]`.

Rewrite `hk` using `[hΦi h0]`. Then use the resulting hypothesis. Use `choose! gs hgsX hgsχ using hSdet`. Take `⟨t, ht⟩` from `hSc.elim_finite_subcover (fun s : S => {y | χ (gs s.1) y ≠ 1}) (fun s => isOpen_ne_fun (hχc _) continuous_const) (fun s hs => Set.mem_iUnion.2 ⟨⟨s, hs⟩, hgsχ s hs⟩)`. Use `⟨t.image (fun s : S => gs s.1), ?_, ?_⟩` and prove the remaining obligations. Introduce `g hg`.

Take `⟨s, -, rfl⟩` from `Finset.mem_image.1 hg`. Conclude with `hgsX s.1 s.2`. Introduce `y hy hG`. Assume the negation of the conclusion as `hyU`. Take `⟨t0, rfl⟩` from `hΦr _ (hYε _ hy)`.

Take `⟨n, hn⟩` from `hKn t0 hyU`. Establish `hmem : Φ (n • t0) ∈ S` using `⟨⟨_, hn, rfl⟩, by rw [map_nsmul]; exact hYn _ hy n⟩`. Take `⟨s, hs, hsy⟩` from `Set.mem_iUnion₂.1 (ht hmem)`. Apply `hsy` to reduce the goal to its premises. Use `show χ (gs s.1) (Φ (n • t0)) = 1`.

Rewrite using `[map_nsmul, hχn]`. Use `hG (gs s.1) (Finset.mem_image_of_mem (fun s : S => gs s.1) hs)` as an intermediate fact. Simplify using `only [χ] at this ⊢`. Rewrite using `[this, one_pow]`.
-/
theorem exists_finset_ann_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) →
        ∃ G : Finset (WOF F E nS nT), (∀ g ∈ G, ∀ i j, e * g i j = g i j) ∧
          ∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) →
            (∀ g ∈ G, B.ψ (symplOHF σ JS JT ξ₀ g y - symplOHF σ JS JT ξ₀ y g) = 1) → y ∈ U := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he U hU
  classical
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨eh⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AEF F E) := eh.isEmbedding.t2Space
  have hψ : Continuous B.ψ := hB.std.1
  obtain ⟨he1, he2, v, ε, hpl, hsum⟩ := id he
  obtain ⟨N, Φ, hΦc, hΦi, hΦr⟩ := GlobalTheory.PlaceCoordsF.coords_at_place F E v ε hpl nS nT
  have hV : (Φ ⁻¹' (U : Set (WOF F E nS nT))) ∈ nhds (0 : Fin N → v.adicCompletion F) :=
    (hU.preimage hΦc).mem_nhds (by rw [Set.mem_preimage, map_zero]; exact U.zero_mem)
  obtain ⟨K, hK, hK0, hKn⟩ := GlobalTheory.NonarchShell.exists_compact_shell_nsmul F v N _ hV
  let Y : Set (WOF F E nS nT) := {y | ∀ i j, cAF σ e * y i j = y i j}
  have hYc : IsClosed Y := by
    simp only [Y, Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (continuous_const.mul ((continuous_apply j).comp (continuous_apply i)))
        ((continuous_apply j).comp (continuous_apply i))
  have hcc : cAF σ e * cAF σ e = cAF σ e := by rw [← map_mul, he1]
  have hYε : ∀ y ∈ Y, ∀ i j, algebraMap (AF F) (AEF F E) ε * y i j = y i j := by
    intro y hy i j
    rw [← hsum, ← hy i j]
    linear_combination (y i j) * he2 + (y i j) * hcc
  have hYn : ∀ y ∈ Y, ∀ n : ℕ, n • y ∈ Y := by
    intro y hy n i j
    show cAF σ e * (n • y i j) = n • y i j
    rw [mul_smul_comm, hy i j]
  let χ : WOF F E nS nT → WOF F E nS nT → ℂ := fun g y =>
    B.ψ (symplOHF σ JS JT ξ₀ g y - symplOHF σ JS JT ξ₀ y g)
  have hχc : ∀ g, Continuous (χ g) := fun g =>
    hψ.comp ((GlobalTheory.HeisThetaF.continuous_symplOHF_right g).sub (GlobalTheory.HeisThetaF.continuous_symplOHF_left g))
  have hχn : ∀ g y (n : ℕ), χ g (n • y) = χ g y ^ n := by
    intro g y n
    induction n with
    | zero =>
      simp only [χ, zero_smul, GlobalTheory.HeisThetaF.symplOHF_zero_left, GlobalTheory.HeisThetaF.symplOHF_zero_right, sub_zero,
        AddChar.map_zero_eq_one, pow_zero]
    | succ n ih =>
      rw [succ_nsmul, pow_succ, ← ih]
      simp only [χ]
      rw [GlobalTheory.HeisThetaF.symplOHF_add_left, GlobalTheory.HeisThetaF.symplOHF_add_right, ← AddChar.map_add_eq_mul]
      congr 1
      ring
  let S : Set (WOF F E nS nT) := Φ '' K ∩ Y
  have hSc : IsCompact S := (hK.image hΦc).inter_right hYc
  have hSdet : ∀ s ∈ S, ∃ g : WOF F E nS nT, (∀ i j, e * g i j = g i j) ∧ χ g s ≠ 1 := by
    rintro s ⟨⟨k, hk, rfl⟩, hsY⟩
    refine exists_detect (GlobalTheory.SplitDetCharF.sig_invol hB.cm) hB.std hS hT hξ hσξ he _ hsY ?_
    intro h0
    apply hK0
    rw [← map_zero Φ] at h0
    rwa [hΦi h0] at hk
  choose! gs hgsX hgsχ using hSdet
  obtain ⟨t, ht⟩ := hSc.elim_finite_subcover (fun s : S => {y | χ (gs s.1) y ≠ 1})
    (fun s => isOpen_ne_fun (hχc _) continuous_const) (fun s hs => Set.mem_iUnion.2 ⟨⟨s, hs⟩, hgsχ s hs⟩)
  refine ⟨t.image (fun s : S => gs s.1), ?_, ?_⟩
  · intro g hg
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hg
    exact hgsX s.1 s.2
  · intro y hy hG
    by_contra hyU
    obtain ⟨t0, rfl⟩ := hΦr _ (hYε _ hy)
    obtain ⟨n, hn⟩ := hKn t0 hyU
    have hmem : Φ (n • t0) ∈ S := ⟨⟨_, hn, rfl⟩, by rw [map_nsmul]; exact hYn _ hy n⟩
    obtain ⟨s, hs, hsy⟩ := Set.mem_iUnion₂.1 (ht hmem)
    apply hsy
    show χ (gs s.1) (Φ (n • t0)) = 1
    rw [map_nsmul, hχn]
    have := hG (gs s.1) (Finset.mem_image_of_mem (fun s : S => gs s.1) hs)
    simp only [χ] at this ⊢
    rw [this, one_pow]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}

/- English proof (translation)
Establish `hc : ∀ c : AEF F E, Continuous fun x : AEF F E => c * x`. Introduce `c`. Establish `: IsModuleTopology (AF F) (AEF F E)` using `⟨rfl⟩`. Establish `: ContinuousAdd (AEF F E)` using `IsModuleTopology.toContinuousAdd (AF F) (AEF F E)`. Conclude with `IsModuleTopology.continuous_of_linearMap (LinearMap.mulLeft (AF F) c)`.

Establish `hs : (conjHalf σ e nS nT : Set (WOF F E nS nT)) = {u | cAF σ e • u = u}`. Use extensionality with `u`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use function extensionality and compare the values at `i j`.

Conclude with `h i j`. Introduce `h i j`. Conclude with `congrFun (congrFun h i) j`. Establish `hT2 : T2Space (WOF F E nS nT)` using `(GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT).2.2.2.1`. Establish `hcs : Continuous (fun u : WOF F E nS nT => cAF σ e • u)` using `continuous_pi fun i => continuous_pi fun j => (hc _).comp ((continuous_apply j).comp (continuous_apply i))`.

Rewrite using `[hs]`. Conclude with `isClosed_eq hcs continuous_id`.
-/
theorem isClosed_conjHalf (e : AEF F E) : IsClosed (conjHalf σ e nS nT : Set (WOF F E nS nT)) := by
  have hc : ∀ c : AEF F E, Continuous fun x : AEF F E => c * x := by
    intro c
    have : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
    have : ContinuousAdd (AEF F E) := IsModuleTopology.toContinuousAdd (AF F) (AEF F E)
    exact IsModuleTopology.continuous_of_linearMap (LinearMap.mulLeft (AF F) c)
  have hs : (conjHalf σ e nS nT : Set (WOF F E nS nT)) = {u | cAF σ e • u = u} := by
    ext u
    constructor
    · intro h
      funext i j
      exact h i j
    · intro h i j
      exact congrFun (congrFun h i) j
  have hT2 : T2Space (WOF F E nS nT) := (GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT).2.2.2.1
  have hcs : Continuous (fun u : WOF F E nS nT => cAF σ e • u) :=
    continuous_pi fun i => continuous_pi fun j => (hc _).comp ((continuous_apply j).comp (continuous_apply i))
  rw [hs]
  exact isClosed_eq hcs continuous_id

variable (σ nS nT) in

def projH {e : AEF F E} (he : e * e = e) : WOF F E nS nT →+ conjHalf σ e nS nT where
  toFun y := ⟨cAF σ e • y, fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← map_mul, he]⟩
  map_zero' := Subtype.ext (smul_zero _)
  map_add' a b := Subtype.ext (smul_add _ a b)

/- English proof (translation)
Conclude with `Subtype.ext (by funext i j; exact y.2 i j)`.
-/
theorem projH_coe {e : AEF F E} (he : e * e = e) (y : conjHalf σ e nS nT) : projH σ nS nT he y = y := by
  exact Subtype.ext (by funext i j; exact y.2 i j)

/- English proof (translation)
Establish `hc : ∀ c : AEF F E, Continuous fun x : AEF F E => c * x`. Introduce `c`. Establish `: IsModuleTopology (AF F) (AEF F E)` using `⟨rfl⟩`. Establish `: ContinuousAdd (AEF F E)` using `IsModuleTopology.toContinuousAdd (AF F) (AEF F E)`. Conclude with `IsModuleTopology.continuous_of_linearMap (LinearMap.mulLeft (AF F) c)`.

Conclude with `(continuous_pi fun i => continuous_pi fun j => (hc _).comp ((continuous_apply j).comp (continuous_apply i))).subtype_mk _`.
-/
theorem continuous_projH {e : AEF F E} (he : e * e = e) : Continuous (projH σ nS nT he) := by
  have hc : ∀ c : AEF F E, Continuous fun x : AEF F E => c * x := by
    intro c
    have : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
    have : ContinuousAdd (AEF F E) := IsModuleTopology.toContinuousAdd (AF F) (AEF F E)
    exact IsModuleTopology.continuous_of_linearMap (LinearMap.mulLeft (AF F) c)
  exact (continuous_pi fun i => continuous_pi fun j => (hc _).comp ((continuous_apply j).comp (continuous_apply i))).subtype_mk _

/- English proof (translation)
Take `⟨i1, i2, i3, i4, -⟩` from `GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT`. Take `⟨he1, he2, v, ε, hpl, hsum⟩` from `id he`. Take `⟨N, Φ, hΦc, -, hΦr⟩` from `GlobalTheory.PlaceCoordsF.coords_at_place F E v ε hpl nS nT`. Use `haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v`. Establish `hcc : cAF σ e * cAF σ e = cAF σ e` using `by rw [← map_mul, he1]`.

Set `J : (Fin N → v.adicCompletion F) →+ conjHalf σ e nS nT` to `(projH σ nS nT he1).comp Φ`. Establish `hJ : Continuous J` using `(continuous_projH he1).comp hΦc`. Establish `hJs : Function.Surjective J` using `fun y => by`. Take `⟨t, ht⟩` from `hΦr y.1 fun i j => by`. Rewrite using `[← hsum, ← y.2 i j]`.

Take the linear combination `(y.1 i j) * he2 + (y.1 i j) * hcc`. Conclude with `⟨t, by show projH σ nS nT he1 (Φ t) = y; rw [ht, projH_coe]⟩`. Use `haveI : LocallyCompactSpace (conjHalf σ e nS nT) := (isClosed_conjHalf e).isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : T2Space (conjHalf σ e nS nT) := inferInstance`. Use `haveI : R1Space (conjHalf σ e nS nT) := T2Space.r1Space`.

Use `haveI : BaireSpace (conjHalf σ e nS nT) := BaireSpace.of_t2Space_locallyCompactSpace`. Establish `hopen : IsOpenMap J` using `AddMonoidHom.isOpenMap_of_sigmaCompact J hJs hJ`. Set `Bl : AddSubgroup (Fin N → v.adicCompletion F)` to `{ carrier := Metric.closedBall 0 1 add_mem' := fun {a b} ha hb => by`. Rewrite `ha`, `hb`, the goal using `[mem_closedBall_zero_iff]`. Conclude with `(IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)`.

Use the proof step `zero_mem' := Metric.mem_closedBall_self zero_le_one`. Use the proof step `neg_mem' := fun {a} ha => by`. Rewrite `ha`, the goal using `[mem_closedBall_zero_iff]`. Rewrite using `[norm_neg] }` and apply the resulting hypothesis. Use `⟨Bl.map J, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[AddSubgroup.coe_map]`. Conclude with `hopen _ (IsUltrametricDist.isOpen_closedBall 0 one_ne_zero)`. Rewrite using `[AddSubgroup.coe_map]`. Conclude with `(isCompact_closedBall 0 1).image hJ`.
-/
theorem exists_compact_open {e : AEF F E} (he : IsSplitIdemF σ e) :
    ∃ K : AddSubgroup (conjHalf σ e nS nT), IsOpen (K : Set (conjHalf σ e nS nT)) ∧
      IsCompact (K : Set (conjHalf σ e nS nT)) := by
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  obtain ⟨he1, he2, v, ε, hpl, hsum⟩ := id he
  obtain ⟨N, Φ, hΦc, -, hΦr⟩ := GlobalTheory.PlaceCoordsF.coords_at_place F E v ε hpl nS nT
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  have hcc : cAF σ e * cAF σ e = cAF σ e := by rw [← map_mul, he1]
  let J : (Fin N → v.adicCompletion F) →+ conjHalf σ e nS nT := (projH σ nS nT he1).comp Φ
  have hJ : Continuous J := (continuous_projH he1).comp hΦc
  have hJs : Function.Surjective J := fun y => by
    obtain ⟨t, ht⟩ := hΦr y.1 fun i j => by
      rw [← hsum, ← y.2 i j]
      linear_combination (y.1 i j) * he2 + (y.1 i j) * hcc
    exact ⟨t, by show projH σ nS nT he1 (Φ t) = y; rw [ht, projH_coe]⟩
  haveI : LocallyCompactSpace (conjHalf σ e nS nT) :=
    (isClosed_conjHalf e).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : T2Space (conjHalf σ e nS nT) := inferInstance
  haveI : R1Space (conjHalf σ e nS nT) := T2Space.r1Space
  haveI : BaireSpace (conjHalf σ e nS nT) := BaireSpace.of_t2Space_locallyCompactSpace
  have hopen : IsOpenMap J := AddMonoidHom.isOpenMap_of_sigmaCompact J hJs hJ
  let Bl : AddSubgroup (Fin N → v.adicCompletion F) :=
    { carrier := Metric.closedBall 0 1
      add_mem' := fun {a b} ha hb => by
        rw [mem_closedBall_zero_iff] at ha hb ⊢
        exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
      zero_mem' := Metric.mem_closedBall_self zero_le_one
      neg_mem' := fun {a} ha => by
        rw [mem_closedBall_zero_iff] at ha ⊢
        rwa [norm_neg] }
  refine ⟨Bl.map J, ?_, ?_⟩
  · rw [AddSubgroup.coe_map]
    exact hopen _ (IsUltrametricDist.isOpen_closedBall 0 one_ne_zero)
  · rw [AddSubgroup.coe_map]
    exact (isCompact_closedBall 0 1).image hJ

/- English proof (translation)
Set `r : T → Y` to `fun t => if ht : t ∈ φ '' A then Classical.choose ht else 0`. Establish `hr : ∀ t ∈ φ '' A, φ (r t) = t`. Introduce `t ht`. Simplify using `only [r, dif_pos ht]`. Conclude with `(Classical.choose_spec ht).2`.

Use `⟨⋃ t ∈ φ '' A, (fun k => r t + k) '' K₀, hfin.isCompact_biUnion fun t _ => hK.image (continuous_const.add continuous_id), ?_⟩` and prove the remaining obligations. Introduce `y hy`. Establish `ht : φ y ∈ φ '' A` using `⟨y, hy, rfl⟩`. Conclude with `Set.mem_biUnion ht ⟨y - r (φ y), h y (r (φ y)) (hr _ ht).symm, by simp⟩`.
-/
theorem exists_compact_of_finite {Y T : Type} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    {K₀ : Set Y} (hK : IsCompact K₀) (φ : Y → T) (A : Set Y) (hfin : (φ '' A).Finite)
    (h : ∀ y y', φ y = φ y' → y - y' ∈ K₀) : ∃ K, IsCompact K ∧ A ⊆ K := by
  classical
  let r : T → Y := fun t => if ht : t ∈ φ '' A then Classical.choose ht else 0
  have hr : ∀ t ∈ φ '' A, φ (r t) = t := by
    intro t ht
    simp only [r, dif_pos ht]
    exact (Classical.choose_spec ht).2
  refine ⟨⋃ t ∈ φ '' A, (fun k => r t + k) '' K₀, hfin.isCompact_biUnion fun t _ => hK.image (continuous_const.add continuous_id), ?_⟩
  intro y hy
  have ht : φ y ∈ φ '' A := ⟨y, hy, rfl⟩
  exact Set.mem_biUnion ht ⟨y - r (φ y), h y (r (φ y)) (hr _ ht).symm, by simp⟩

variable {B : Base F E}

/- English proof (translation)
Take `⟨G, hG1, hG2⟩` from `exists_finset_ann_le F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he (U.comap (projH σ nS nT he.1)) (hU.preimage (continuous_projH he.1))`. Use `⟨G, fun g hg => GlobalTheory.SplitVacF.mem_conjHalf_conj he (hG1 g hg), fun y hy => ?_⟩` and prove the remaining obligations. Use `hG2 y.1 y.2 hy` as an intermediate fact. Rewrite `this` using `[AddSubgroup.mem_comap, projH_coe]`. Then use the resulting hypothesis.
-/
theorem exists_open_sep (hB : B.IsGood σ) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠ 0) (hσξ : σ ξ₀ = -ξ₀)
    {e : AEF F E} (he : IsSplitIdemF σ e) (U : AddSubgroup (conjHalf σ e nS nT))
    (hU : IsOpen (U : Set (conjHalf σ e nS nT))) :
    ∃ G : Finset (WOF F E nS nT), (∀ g ∈ G, g ∈ conjHalf σ (cAF σ e) nS nT) ∧
      ∀ y : conjHalf σ e nS nT, (∀ g ∈ G, commF σ JS JT ξ₀ B.ψ g y = 1) → y ∈ U := by
  obtain ⟨G, hG1, hG2⟩ := exists_finset_ann_le F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he
    (U.comap (projH σ nS nT he.1)) (hU.preimage (continuous_projH he.1))
  refine ⟨G, fun g hg => GlobalTheory.SplitVacF.mem_conjHalf_conj he (hG1 g hg), fun y hy => ?_⟩
  have := hG2 y.1 y.2 hy
  rwa [AddSubgroup.mem_comap, projH_coe] at this

/- English proof (translation)
Take `⟨i1, -⟩` from `GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT`. Take `⟨K₀, hKo, hKc⟩` from `exists_compact_open (nS := nS) (nT := nT) he`. Take `⟨G, hG1, hG2⟩` from `exists_open_sep hB hS hT hξ hσξ he K₀ hKo`. Use `choose! k hk0 hk using hP`. Use `(exists_compact_of_finite hKc (fun (y : conjHalf σ e nS nT) (g : G) => commF σ JS JT ξ₀ B.ψ g y) {y | ∀ g, P g → commF σ JS JT ξ₀ B.ψ g y = 1} ?_ ?_).imp fun K h => ⟨h.1, fun y hy => h.2 hy⟩` and prove the remaining obligations.

Use `(Set.Finite.pi' (t := fun g : G => ((Polynomial.nthRoots (k g) (1 : ℂ)).toFinset : Set ℂ)) fun g => Finset.finite_toSet _).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩ g`. Rewrite using `[Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots (hk0 _ (hG1 _ g.2)), ← GlobalTheory.SplitVacF.commF_nsmul_left]`. Conclude with `hy _ (hk _ (hG1 _ g.2))`. Introduce `y y' h`.

Use `hG2 _ fun g hg => ?_` and prove the remaining obligations. Establish `h1 : commF σ JS JT ξ₀ B.ψ g y = commF σ JS JT ξ₀ B.ψ g y'` using `congrFun h ⟨g, hg⟩`. Rewrite using `[sub_eq_neg_add, AddSubgroup.coe_add, AddSubgroup.coe_neg, GlobalTheory.SplitVacF.commF_add_right, h1, GlobalTheory.SplitVacF.commF_neg_right]`.
-/
theorem exists_compact_ann (hB : B.IsGood σ) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠ 0) (hσξ : σ ξ₀ = -ξ₀)
    {e : AEF F E} (he : IsSplitIdemF σ e) (P : WOF F E nS nT → Prop)
    (hP : ∀ g ∈ conjHalf σ (cAF σ e) nS nT, ∃ k : ℕ, 0 < k ∧ P (k • g)) :
    ∃ K : Set (conjHalf σ e nS nT), IsCompact K ∧
      ∀ y : conjHalf σ e nS nT, (∀ g, P g → commF σ JS JT ξ₀ B.ψ g y = 1) → y ∈ K := by
  obtain ⟨i1, -⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  obtain ⟨K₀, hKo, hKc⟩ := exists_compact_open (nS := nS) (nT := nT) he
  obtain ⟨G, hG1, hG2⟩ := exists_open_sep hB hS hT hξ hσξ he K₀ hKo
  choose! k hk0 hk using hP
  refine (exists_compact_of_finite hKc
    (fun (y : conjHalf σ e nS nT) (g : G) => commF σ JS JT ξ₀ B.ψ g y)
    {y | ∀ g, P g → commF σ JS JT ξ₀ B.ψ g y = 1} ?_ ?_).imp fun K h => ⟨h.1, fun y hy => h.2 hy⟩
  · refine (Set.Finite.pi' (t := fun g : G => ((Polynomial.nthRoots (k g) (1 : ℂ)).toFinset : Set ℂ))
      fun g => Finset.finite_toSet _).subset ?_
    rintro _ ⟨y, hy, rfl⟩ g
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots (hk0 _ (hG1 _ g.2)),
      ← GlobalTheory.SplitVacF.commF_nsmul_left]
    exact hy _ (hk _ (hG1 _ g.2))
  · intro y y' h
    refine hG2 _ fun g hg => ?_
    have h1 : commF σ JS JT ξ₀ B.ψ g y = commF σ JS JT ξ₀ B.ψ g y' := congrFun h ⟨g, hg⟩
    rw [sub_eq_neg_add, AddSubgroup.coe_add, AddSubgroup.coe_neg, GlobalTheory.SplitVacF.commF_add_right, h1,
      GlobalTheory.SplitVacF.commF_neg_right]

end GlobalTheory.SplitLagrF

end

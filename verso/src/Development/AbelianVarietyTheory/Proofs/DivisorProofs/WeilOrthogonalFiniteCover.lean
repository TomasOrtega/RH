import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulFix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigmaSigmaOfCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousPlaceAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactShellNsmul
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace GlobalTheory.SplitAnnF

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he U hU`. Use `haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)`. Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F`. Take `⟨eh⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)`.

Use `haveI : T2Space (AEF F E) := eh.isEmbedding.t2Space`. Establish `hψ : Continuous B.ψ` using `hB.std.1`. Take `⟨he1, he2, v, ε, hpl, hsum⟩` from `id he`. Take `⟨N, Φ, hΦc, hΦi, hΦr⟩` from `GlobalTheory.PlaceCoordsF.coords_at_place F E v ε hpl nS nT`. Establish `hV : (Φ ⁻¹' (U : Set (WOF F E nS nT))) ∈ nhds (0 : Fin N → v.adicCompletion F)` using `(hU.preimage hΦc).mem_nhds (by rw [Set.mem_preimage, map_zero]; exact U.zero_mem)`.

Take `⟨K, hK, hK0, hKn⟩` from `GlobalTheory.NonarchShell.exists_compact_shell_nsmul F v N _ hV`. Set `Y : Set (WOF F E nS nT)` to `{y | ∀ i j, cAF σ e * y i j = y i j}`. Establish `hYc : IsClosed Y`. Simplify using `only [Y, Set.setOf_forall]`. Conclude with `isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (continuous_const.mul ((continuous_apply j).comp (continuous_apply i))) ((continuous_apply j).comp (continuous_apply i))`.

Establish `hcc : cAF σ e * cAF σ e = cAF σ e` using `by rw [← map_mul, he1]`. Establish `hYε : ∀ y ∈ Y, ∀ i j, algebraMap (AF F) (AEF F E) ε * y i j = y i j`. Introduce `y hy i j`. Rewrite using `[← hsum, ← hy i j]`. Take the linear combination `(y i j) * he2 + (y i j) * hcc`.

Establish `hYn : ∀ y ∈ Y, ∀ n : ℕ, n • y ∈ Y`. Introduce `y hy n i j`. Use `show cAF σ e * (n • y i j) = n • y i j`. Rewrite using `[mul_smul_comm, hy i j]`. Set `χ : WOF F E nS nT → WOF F E nS nT → ℂ` to `fun g y => B.ψ (symplOHF σ JS JT ξ₀ g y - symplOHF σ JS JT ξ₀ y g)`.

Establish `hχc : ∀ g, Continuous (χ g)` using `fun g => hψ.comp ((GlobalTheory.HeisThetaF.continuous_symplOHF_right g).sub (GlobalTheory.HeisThetaF.continuous_symplOHF_left g))`. Establish `hχn : ∀ g y (n : ℕ), χ g (n • y) = χ g y ^ n`. Introduce `g y n`. Proceed by induction on `n with`. Consider the case `zero`.

Simplify using `only [χ, zero_smul, GlobalTheory.HeisThetaF.symplOHF_zero_left, GlobalTheory.HeisThetaF.symplOHF_zero_right, sub_zero, AddChar.map_zero_eq_one, pow_zero]`. Consider the case `succ n ih`. Rewrite using `[succ_nsmul, pow_succ, ← ih]`. Simplify using `only [χ]`. Rewrite using `[GlobalTheory.HeisThetaF.symplOHF_add_left, GlobalTheory.HeisThetaF.symplOHF_add_right, ← AddChar.map_add_eq_mul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Set `S : Set (WOF F E nS nT)` to `Φ '' K ∩ Y`. Establish `hSc : IsCompact S` using `(hK.image hΦc).inter_right hYc`. Establish `hSdet : ∀ s ∈ S, ∃ g : WOF F E nS nT, (∀ i j, e * g i j = g i j) ∧ χ g s ≠ 1`.

Introduce and unpack `s ⟨⟨k, hk, rfl⟩, hsY⟩`. Use `GlobalTheory.SplitPairNondegF.detect_conj_half F E σ (GlobalTheory.SplitPairNondegF.sigma_sigma_of_cm hB.cm) B.ψ hB.std nS nT JS JT hS hT ξ₀ hξ hσξ e he _ hsY ?_` and prove the remaining obligations. Introduce `h0`. Apply `hK0` to reduce the goal to its premises. Rewrite `h0` using `[← map_zero Φ]`.

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
    refine GlobalTheory.SplitPairNondegF.detect_conj_half F E σ (GlobalTheory.SplitPairNondegF.sigma_sigma_of_cm hB.cm) B.ψ hB.std nS nT JS JT hS hT ξ₀ hξ hσξ e he _ hsY ?_
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

end GlobalTheory.SplitAnnF

end

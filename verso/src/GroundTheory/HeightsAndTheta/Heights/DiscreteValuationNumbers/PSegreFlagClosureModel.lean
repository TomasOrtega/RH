import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagClosure
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagClosureTrdeg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDvrConeDimTrdeg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensExpress
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreFlagClosureModel

/- English proof (translation)
Establish `hN : 0 < N` using `by omega`. Use `by_contra! h0`. Set `θ : Fin P → Module.Dual Ω E` to `fun l => ∑ j : Fin N, (if (j : ℕ) < k then ψ l (w j) else 0) • w.coord j`. Establish `hθe : ∀ l i, θ l (e i) = ∑ j : Fin N, (if (j : ℕ) < k then ψ l (w j) else 0) * w.repr (e i) j`. Introduce `l i`.

Simplify using `only [θ, LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]`. Establish `hθ : ∀ l, θ l = 0`. Introduce `l`. Use `e.ext fun i => ?_` and prove the remaining obligations. Establish `key` using `Fintype.linearIndependent_iff.1 ht (fun i => θ l (e i)) (by`.

Rewrite using `[← h0 l]`. Simplify using `only [hθe, Algebra.smul_def, map_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [flagCoord]`.

Use `split_ifs`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Use the proof step `simp)`. Simplify using `using key i`. Establish `hw0 : ∀ l, ψ l (w ⟨0, hN⟩) = 0`. Introduce `l`. Establish `h` using `congrArg (fun f : Module.Dual Ω E => f (w ⟨0, hN⟩)) (hθ l)`.

Simplify using `only [θ, LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self, LinearMap.zero_apply] at h`. Rewrite `h` using `[Finset.sum_eq_single ⟨0, hN⟩ (fun j _ hj => by simp [Ne.symm hj]) (by simp)]`. Simplify `h` using `[show (0 : ℕ) < k by omega]`. Establish `hall : ∀ f ∈ Submodule.span Ω (Set.range ψ), f (w ⟨0, hN⟩) = 0`. Introduce `f hf`.

Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨l, rfl⟩ := hx`. Conclude with `hw0 l`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp [hx, hy]`.

Consider the case `smul a x _ hx => simp [hx]`. Use `hall (w.coord ⟨0, hN⟩) (hψ ▸ Submodule.mem_top)` as an intermediate fact. Simplify using `at this`.
-/
theorem exists_flag_ne_zero {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
    {Φ : Type*} [Field Φ] [Algebra Ω Φ] {N P : ℕ} (w e : Module.Basis (Fin N) Ω E)
    {t : Fin N → Φ} (ht : LinearIndependent Ω t) (ψ : Fin P → Module.Dual Ω E)
    (hψ : Submodule.span Ω (Set.range ψ) = ⊤) {k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    ∃ l, ∑ j, flagCoord w e t k j * algebraMap Ω Φ (ψ l (w j)) ≠ 0 := by
  have hN : 0 < N := by omega
  by_contra! h0

  let θ : Fin P → Module.Dual Ω E := fun l =>
    ∑ j : Fin N, (if (j : ℕ) < k then ψ l (w j) else 0) • w.coord j
  have hθe : ∀ l i, θ l (e i) = ∑ j : Fin N, (if (j : ℕ) < k then ψ l (w j) else 0) * w.repr (e i) j := by
    intro l i
    simp only [θ, LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
  have hθ : ∀ l, θ l = 0 := by
    intro l
    refine e.ext fun i => ?_
    have key := Fintype.linearIndependent_iff.1 ht (fun i => θ l (e i)) (by
      rw [← h0 l]
      simp only [hθe, Algebra.smul_def, map_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [flagCoord]
      split_ifs
      · rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul]
        ring
      · simp)
    simpa using key i
  have hw0 : ∀ l, ψ l (w ⟨0, hN⟩) = 0 := by
    intro l
    have h := congrArg (fun f : Module.Dual Ω E => f (w ⟨0, hN⟩)) (hθ l)
    simp only [θ, LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
      Module.Basis.repr_self, LinearMap.zero_apply] at h
    rw [Finset.sum_eq_single ⟨0, hN⟩ (fun j _ hj => by simp [Ne.symm hj])
      (by simp)] at h
    simpa [show (0 : ℕ) < k by omega] using h
  have hall : ∀ f ∈ Submodule.span Ω (Set.range ψ), f (w ⟨0, hN⟩) = 0 := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx => obtain ⟨l, rfl⟩ := hx; exact hw0 l
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  have := hall (w.coord ⟨0, hN⟩) (hψ ▸ Submodule.mem_top)
  simp at this

end SegreFlagClosureModel

open GenericProjClosureDim GenericProjClosureDivisor SegreFlagClosureModel in

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht k hk hkN`. Establish `hpt : flagClosurePt y w e φ φ' t k = pairProjCoord y w φ φ' (flagCoord w e t k)` using `rfl`. Establish `hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0` using `fun k => by`. Take `⟨j, hj⟩` from `hV.multiProj.relevant k`. Use `⟨j, fun h0 => hj ?_⟩` and prove the remaining obligations.

Rewrite using `[pointIdeal, RingHom.mem_ker]`. Simplify using `[pointConeMap, h0]`. Use `choose c hc using hne`. Establish `hyc : segreVec y c ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => hc k`. Establish `hli` using `ht.linearIndependent`.

Establish `hz : ∀ o, ∃ i, flagClosurePt y w e φ φ' t k ⟨o, i⟩ ≠ 0`. Introduce and unpack `(_ | _ | k')`. Conclude with `exists_flag_ne_zero w e hli φ' (TwistedDualGensSpan.proof O Ω K ι y N E B' a₀' M' φ' hφ' c hyc) hk hkN`. Conclude with `exists_flag_ne_zero w e hli φ (TwistedDualGensSpan.proof O Ω K ι y N E B a₀ M φ hφ c hyc) hk hkN`. Conclude with `⟨c k', fun h0 => hc k' ((FaithfulSMul.algebraMap_injective Ω Φ) (by simpa [flagClosurePt, pairProjCoord, projCoord] using h0))⟩`.

Establish `hP` using `isMultiProjPrime_pointIdeal (R := O) _ hz`. Establish `hnt : (pointIdeal O (flagClosurePt y w e φ φ' t k)).comap (C : O →+* _) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `a ha`. Rewrite `ha` using `[Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, C_eq_zero, IsScalarTower.algebraMap_apply O Ω Φ, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective Ω Φ)]`.

Establish `hy : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O)`. Rewrite using `[Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, ha, map_zero]`. Rewrite `hy` using `[hV.noTorsion]`. Simplify using `using hy`. Establish `hdy` using `DvrConeDimTrdeg.proof O K ι (pointIdeal O y) hV.multiProj hV.noTorsion`.

Rewrite `hdy` using `[hV.dim]`. Establish `hty : Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) = ((d + Fintype.card K : ℕ) : Cardinal)`. Establish `h1 : (((d + Fintype.card K : ℕ) : ℕ∞) + 1) = (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat + 1`. Use `WithBot.coe_injective hdy` as an intermediate fact. Rewrite using `[← this]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Conclude with `(Cardinal.toENat_eq_natCast.1 (WithTop.add_right_cancel ENat.one_ne_top h1).symm)`. Establish `hZ : IsModelOver (pointIdeal O (flagClosurePt y w e φ φ' t k)) (d + (k - 1))`. Use `⟨hP, hnt, ?_⟩` and prove the remaining obligations.

Rewrite using `[DvrConeDimTrdeg.proof _ _ _ _ hP hnt, hTr O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk hkN, hty, ← Nat.cast_add, Cardinal.toENat_nat, Fintype.card_option, Fintype.card_option, show d + (k - 1) + 1 + (Fintype.card K + 1 + 1) = d + Fintyp …`. Use `norm_cast`. Use `⟨hZ, ?_⟩` and prove the remaining obligations. Rewrite `hZ`, the goal using `[hpt]`. Establish `hP' : (pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t k))).IsPrime` using `hZ.multiProj.isPrime`.

Establish `hϖP : (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t k))`. Introduce `hm`. Establish `h1 : ϖ ∈ (pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t k))).comap (C : O →+* MRing (bundleIdx (bundleIdx ι M) M') O)` using `hm`. Rewrite `h1` using `[hZ.noTorsion, Ideal.mem_bot]`. Conclude with `hϖ.ne_zero h1`.

Establish `pairs` using `pairs_at TwistedDualGensExpress.proof y B B' hB a₀ a₀' φ φ' hφ hφ' w (flagCoord w e t k)`. Take `⟨⟨f₀, g₀, hp₀, hg₀⟩, -⟩` from `pairs _ hP' le_rfl hZ.multiProj.relevant hϖP`. Establish `hf₀ : f₀ ∉ pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t k))`. Introduce `hm`. Take `⟨⟨bf, bg, -, hg, -⟩, hv⟩` from `hp₀`.

Conclude with `hg₀ (mem_of_homog hg (by rw [← hv]; exact aeval_eq_zero_of_mem hm))`. Use `⟨f₀, g₀, IsVerticalDivisor.of_unit_off_special hp₀.1 hf₀ hg₀ ?_, hp₀.2⟩` and prove the remaining obligations. Introduce `W hW hPW hWr hϖW`. Take `⟨⟨f₁, g₁, hp₁, hg₁⟩, ⟨f₂, g₂, hp₂, hf₂⟩⟩` from `pairs W hW hPW hWr hϖW`. Establish `h12` using `hPW (hp₁.cross hp₂)`.

Use `⟨g₁, f₁, hg₁, fun hf₁ => ?_, ?_⟩` and prove the remaining obligations. Establish `h' : f₁ * g₂ - (f₁ * g₂ - f₂ * g₁) ∈ W` using `W.sub_mem (W.mul_mem_right _ hf₁) h12`. Rewrite `h'` using `[sub_sub_cancel]`. Break down `hW.mem_or_mem h' with h | h` into its components or cases. Conclude with `hf₂ h`.

Conclude with `hg₁ h`. Rewrite using `[show g₁ * f₀ - f₁ * g₀ = f₀ * g₁ - f₁ * g₀ by ring]`. Conclude with `hp₀.cross hp₁`.
-/
theorem SegreFlagClosureModel.proof (hTr : SegreFlagClosureTrdeg.Statement) :
    SegreFlagClosureModel.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk hkN
  have hpt : flagClosurePt y w e φ φ' t k = pairProjCoord y w φ φ' (flagCoord w e t k) := rfl

  have hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0 := fun k => by
    obtain ⟨j, hj⟩ := hV.multiProj.relevant k
    refine ⟨j, fun h0 => hj ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h0]
  choose c hc using hne
  have hyc : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hli := ht.linearIndependent

  have hz : ∀ o, ∃ i, flagClosurePt y w e φ φ' t k ⟨o, i⟩ ≠ 0 := by
    rintro (_ | _ | k')
    · exact exists_flag_ne_zero w e hli φ'
        (TwistedDualGensSpan.proof O Ω K ι y N E B' a₀' M' φ' hφ' c hyc) hk hkN
    · exact exists_flag_ne_zero w e hli φ
        (TwistedDualGensSpan.proof O Ω K ι y N E B a₀ M φ hφ c hyc) hk hkN
    · exact ⟨c k', fun h0 => hc k' ((FaithfulSMul.algebraMap_injective Ω Φ)
        (by simpa [flagClosurePt, pairProjCoord, projCoord] using h0))⟩
  have hP := isMultiProjPrime_pointIdeal (R := O) _ hz

  have hnt : (pointIdeal O (flagClosurePt y w e φ φ' t k)).comap (C : O →+* _) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply,
      C_eq_zero, IsScalarTower.algebraMap_apply O Ω Φ, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective Ω Φ)] at ha
    have hy : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, ha,
        map_zero]
    rw [hV.noTorsion] at hy
    simpa using hy

  have hdy := DvrConeDimTrdeg.proof O K ι (pointIdeal O y) hV.multiProj hV.noTorsion
  rw [hV.dim] at hdy
  have hty : Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) = ((d + Fintype.card K : ℕ) : Cardinal) := by
    have h1 : (((d + Fintype.card K : ℕ) : ℕ∞) + 1) =
        (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat + 1 := by
      have := WithBot.coe_injective hdy
      rw [← this]
      push_cast
      ring
    exact (Cardinal.toENat_eq_natCast.1 (WithTop.add_right_cancel ENat.one_ne_top h1).symm)
  have hZ : IsModelOver (pointIdeal O (flagClosurePt y w e φ φ' t k)) (d + (k - 1)) := by
    refine ⟨hP, hnt, ?_⟩
    rw [DvrConeDimTrdeg.proof _ _ _ _ hP hnt,
      hTr O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk hkN, hty,
      ← Nat.cast_add, Cardinal.toENat_nat, Fintype.card_option, Fintype.card_option,
      show d + (k - 1) + 1 + (Fintype.card K + 1 + 1) = d + Fintype.card K + (k + 1) + 1 by omega]
    norm_cast
  refine ⟨hZ, ?_⟩

  rw [hpt] at hZ ⊢
  have hP' : (pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t k))).IsPrime := hZ.multiProj.isPrime
  have hϖP : (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉
      pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t k)) := by
    intro hm
    have h1 : ϖ ∈ (pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t k))).comap
        (C : O →+* MRing (bundleIdx (bundleIdx ι M) M') O) := hm
    rw [hZ.noTorsion, Ideal.mem_bot] at h1
    exact hϖ.ne_zero h1
  have pairs := pairs_at TwistedDualGensExpress.proof y B B' hB a₀ a₀' φ φ' hφ hφ' w (flagCoord w e t k)
  obtain ⟨⟨f₀, g₀, hp₀, hg₀⟩, -⟩ := pairs _ hP' le_rfl hZ.multiProj.relevant hϖP
  have hf₀ : f₀ ∉ pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t k)) := by
    intro hm
    obtain ⟨⟨bf, bg, -, hg, -⟩, hv⟩ := hp₀
    exact hg₀ (mem_of_homog hg (by rw [← hv]; exact aeval_eq_zero_of_mem hm))
  refine ⟨f₀, g₀, IsVerticalDivisor.of_unit_off_special hp₀.1 hf₀ hg₀ ?_, hp₀.2⟩
  intro W hW hPW hWr hϖW
  obtain ⟨⟨f₁, g₁, hp₁, hg₁⟩, ⟨f₂, g₂, hp₂, hf₂⟩⟩ := pairs W hW hPW hWr hϖW
  have h12 := hPW (hp₁.cross hp₂)
  refine ⟨g₁, f₁, hg₁, fun hf₁ => ?_, ?_⟩
  · have h' : f₁ * g₂ - (f₁ * g₂ - f₂ * g₁) ∈ W := W.sub_mem (W.mul_mem_right _ hf₁) h12
    rw [sub_sub_cancel] at h'
    rcases hW.mem_or_mem h' with h | h
    · exact hf₂ h
    · exact hg₁ h
  · rw [show g₁ * f₀ - f₁ * g₀ = f₀ * g₁ - f₁ * g₀ by ring]
    exact hp₀.cross hp₁

end

end GroundTheory.Heights₂.Heights.NumbersDVR

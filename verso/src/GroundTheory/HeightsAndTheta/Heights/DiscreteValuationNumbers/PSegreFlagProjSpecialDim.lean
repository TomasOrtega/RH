import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagProjSpecialDimSteps
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDvrConeDimTrdeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

/- English proof (translation)
Use extensionality with `a`. Simplify using `only [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, C_eq_zero, Submodule.mem_bot]`. Conclude with `⟨fun ha => h (by rw [ha, map_zero]), fun ha => by rw [ha, map_zero]⟩`.
-/
theorem comap_C_pointIdeal {R : Type*} [CommRing R] {Φ : Type*} [Field Φ] [Algebra R Φ] {K : Type*}
    {ι : K → Type*} (h : Function.Injective (algebraMap R Φ)) (pt : (Σ k, ι k) → Φ) :
    (pointIdeal R pt).comap (C : R →+* MvPolynomial (Σ k, ι k) R) = ⊥ := by
  ext a
  simp only [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C,
    MvPolynomial.algebraMap_apply, C_eq_zero, Submodule.mem_bot]
  exact ⟨fun ha => h (by rw [ha, map_zero]), fun ha => by rw [ha, map_zero]⟩

/- English proof (translation)
Use `set φ : MvPolynomial (Σ k, ι k) O →+* MvPolynomial (Σ k, ι k) (IsLocalRing.ResidueField O) := MvPolynomial.map (IsLocalRing.residue O) with hφdef`. Establish `hφ : Function.Surjective φ` using `MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective`. Establish `hker : RingHom.ker φ = Ideal.span {(C ϖ : MvPolynomial (Σ k, ι k) O)}`. Rewrite using `[hφdef, MvPolynomial.ker_map, IsLocalRing.ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]`. Use `set g := (Ideal.Quotient.mk (P.map φ)).comp φ with hgdef`.

Establish `hg : Function.Surjective g` using `Ideal.Quotient.mk_surjective.comp hφ`. Establish `hkg : RingHom.ker g = P ⊔ Ideal.span {(C ϖ : MvPolynomial (Σ k, ι k) O)}`. Rewrite using `[hgdef, ← RingHom.comap_ker, Ideal.mk_ker, Ideal.comap_map_of_surjective _ hφ, ← RingHom.ker_eq_comap_bot, hker]`. Establish `e1` using `(Ideal.quotEquivOfEq hkg.symm).trans (RingHom.quotientKerEquivOfSurjective hg)`. Use `set r : MvPolynomial (Σ k, ι k) O ⧸ P := Ideal.Quotient.mk P (C ϖ) with hrdef`.

Establish `hspan : (Ideal.span {(C ϖ : MvPolynomial (Σ k, ι k) O)}).map (Ideal.Quotient.mk P) = Ideal.span {r}`. Rewrite using `[Ideal.map_span, Set.image_singleton]`. Establish `e2` using `(Ideal.quotEquivOfEq hspan.symm).trans (DoubleQuot.quotQuotEquivQuotSup P (Ideal.span {(C ϖ : MvPolynomial (Σ k, ι k) O)}))`. Establish `hr0 : r ≠ 0`. Introduce `h0`.

Rewrite `h0` using `[hrdef, Ideal.Quotient.eq_zero_iff_mem]`. Establish `hmem : ϖ ∈ P.comap (C : O →+* MvPolynomial (Σ k, ι k) O)` using `h0`. Rewrite `hmem` using `[hPC, Ideal.mem_bot]`. Conclude with `hϖ.ne_zero hmem`. Establish `hle` using `ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hr0)`.

Rewrite `hle` using `[ringKrullDim_eq_of_ringEquiv e2, ringKrullDim_eq_of_ringEquiv e1]`. Then use the resulting hypothesis.
-/
theorem specialIdeal_dim_add_one_le {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {K : Type*} {ι : K → Type*} (P : Ideal (MvPolynomial (Σ k, ι k) O)) [P.IsPrime]
    (hPC : P.comap (C : O →+* MvPolynomial (Σ k, ι k) O) = ⊥) :
    ringKrullDim (MvPolynomial (Σ k, ι k) (IsLocalRing.ResidueField O) ⧸
        P.map (MvPolynomial.map (IsLocalRing.residue O))) + 1 ≤
      ringKrullDim (MvPolynomial (Σ k, ι k) O ⧸ P) := by
  set φ : MvPolynomial (Σ k, ι k) O →+* MvPolynomial (Σ k, ι k) (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O) with hφdef
  have hφ : Function.Surjective φ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker φ = Ideal.span {(C ϖ : MvPolynomial (Σ k, ι k) O)} := by
    rw [hφdef, MvPolynomial.ker_map, IsLocalRing.ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton]
  set g := (Ideal.Quotient.mk (P.map φ)).comp φ with hgdef
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hφ
  have hkg : RingHom.ker g = P ⊔ Ideal.span {(C ϖ : MvPolynomial (Σ k, ι k) O)} := by
    rw [hgdef, ← RingHom.comap_ker, Ideal.mk_ker, Ideal.comap_map_of_surjective _ hφ,
      ← RingHom.ker_eq_comap_bot, hker]
  have e1 := (Ideal.quotEquivOfEq hkg.symm).trans (RingHom.quotientKerEquivOfSurjective hg)
  set r : MvPolynomial (Σ k, ι k) O ⧸ P := Ideal.Quotient.mk P (C ϖ) with hrdef
  have hspan : (Ideal.span {(C ϖ : MvPolynomial (Σ k, ι k) O)}).map (Ideal.Quotient.mk P) = Ideal.span {r} := by
    rw [Ideal.map_span, Set.image_singleton]
  have e2 := (Ideal.quotEquivOfEq hspan.symm).trans (DoubleQuot.quotQuotEquivQuotSup P
    (Ideal.span {(C ϖ : MvPolynomial (Σ k, ι k) O)}))
  have hr0 : r ≠ 0 := by
    intro h0
    rw [hrdef, Ideal.Quotient.eq_zero_iff_mem] at h0
    have hmem : ϖ ∈ P.comap (C : O →+* MvPolynomial (Σ k, ι k) O) := h0
    rw [hPC, Ideal.mem_bot] at hmem
    exact hϖ.ne_zero hmem
  have hle := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hr0)
  rwa [ringKrullDim_eq_of_ringEquiv e2, ringKrullDim_eq_of_ringEquiv e1] at hle

/- English proof (translation)
Establish `h` using `(specialIdeal_dim_add_one_le hϖ P hPC).trans hdim`. Unfold `FieldNumbers.relDim specialIdeal`. Generalize the expression as in `ringKrullDim (MvPolynomial (Σ k, ι k) (IsLocalRing.ResidueField O) ⧸ P.map (MvPolynomial.map (IsLocalRing.residue O))) = a at h ⊢`. Proceed by induction on `a using WithBot.recBotCoe with`. Consider the case `bot => exact WithBot.bot_lt_coe _`.

Consider the case `coe a`. Proceed by induction on `a using ENat.recTopCoe with`. Consider the case `top`. It suffices to derive a contradiction. Establish `h' : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ((n + Fintype.card K : ℕ) : ℕ∞)` using `by exact_mod_cast h`.

Simplify using `at h'`. Consider the case `coe m`. Establish `h' : ((m + 1 : ℕ) : ℕ∞) ≤ ((n + Fintype.card K : ℕ) : ℕ∞)` using `by exact_mod_cast h`. Establish `h'' : m + 1 ≤ n + Fintype.card K` using `by exact_mod_cast h'`. Establish `hlt : (m : ℤ) - Fintype.card K < n` using `by omega`.

Express the relevant statement in the definitionally equal form `(((((m : ℤ) - Fintype.card K : ℤ) : WithTop ℤ)) : WithBot (WithTop ℤ)) < (((n : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))`. Conclude with `hlt` after adjusting the coercions.
-/
theorem relDim_specialIdeal_lt {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} (P : Ideal (MRing ι O)) [P.IsPrime]
    (hPC : P.comap (C : O →+* MRing ι O) = ⊥) (n : ℕ)
    (hdim : ringKrullDim (MRing ι O ⧸ P) ≤ ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    FieldNumbers.relDim (specialIdeal P) < ((n : ℕ) : WithBot (WithTop ℤ)) := by
  have h := (specialIdeal_dim_add_one_le hϖ P hPC).trans hdim
  unfold FieldNumbers.relDim specialIdeal
  generalize ringKrullDim (MvPolynomial (Σ k, ι k) (IsLocalRing.ResidueField O) ⧸
    P.map (MvPolynomial.map (IsLocalRing.residue O))) = a at h ⊢
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ((n + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast h
      simp at h'
    | coe m =>
      have h' : ((m + 1 : ℕ) : ℕ∞) ≤ ((n + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast h
      have h'' : m + 1 ≤ n + Fintype.card K := by exact_mod_cast h'
      have hlt : (m : ℤ) - Fintype.card K < n := by omega
      change (((((m : ℤ) - Fintype.card K : ℤ) : WithTop ℤ)) : WithBot (WithTop ℤ)) < (((n : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
      exact_mod_cast hlt

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hBB' w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht k hk`. Take `⟨h1, h2⟩` from `hTr O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk`. Establish `hVt : (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat = ((d + Fintype.card K : ℕ) : ℕ∞)`. Establish `h` using `DvrConeDimTrdeg.proof O K ι _ hV.multiProj hV.noTorsion`. Rewrite `h` using `[hV.dim]`.

Establish `h0 : ((d + 1 + Fintype.card K : ℕ) : ℕ∞) = (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat + 1`. Conclude with `h` after adjusting the coercions. Establish `h' : ((d + Fintype.card K : ℕ) : ℕ∞) + 1 = (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat + 1`. Rewrite using `[← h0]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `(WithTop.add_right_cancel ENat.one_ne_top h').symm`. Establish `hOΩ : Function.Injective (algebraMap O Ω)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`.

Establish `hmem : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O)`. Simplify using `[Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, ha]`. Rewrite `hmem` using `[hV.noTorsion, Ideal.mem_bot]`. Then use the resulting hypothesis. Establish `hOΦ : Function.Injective (algebraMap O Φ)`. Rewrite using `[IsScalarTower.algebraMap_eq O Ω Φ]`.

Conclude with `(algebraMap Ω Φ).injective.comp hOΩ`. Establish `key : ∀ {K' : Type} [Fintype K'] [DecidableEq K'] (j : K' ↪ Option (Option K)), Fintype.card K' = Fintype.card K + 1 → Algebra.trdeg O (MRing (fun o => bundleIdx (bundleIdx ι M) M' (j o)) O ⧸ pointIdeal O (flagProjPt j y w e φ φ' t k)) ≤ Algebra.trdeg O (MRing ι O ⧸ pointIdeal O …`. Introduce `K' _ _ j hcard hle`. Establish `hP : (pointIdeal O (flagProjPt j y w e φ φ' t k)).IsPrime`. Unfold `pointIdeal`.

Conclude with `RingHom.ker_isPrime _`. Establish `hPC` using `comap_C_pointIdeal hOΦ (flagProjPt j y w e φ φ' t k)`. Use `relDim_specialIdeal_lt hϖ _ hPC (d + k) ((hDim O K' _ _ hP hPC).trans ?_)` and prove the remaining obligations. Establish `ht : Cardinal.toENat _ ≤ Cardinal.toENat _` using `OrderHomClass.mono Cardinal.toENat hle`. Simplify using `only [map_add, map_natCast, hVt] at ht`.

Establish `: ((Algebra.trdeg O (MRing (fun o => bundleIdx (bundleIdx ι M) M' (j o)) O ⧸ pointIdeal O (flagProjPt j y w e φ φ' t k))).toENat + 1 : ℕ∞) ≤ ((d + k + Fintype.card K' : ℕ) : ℕ∞)`. Rewrite using `[hcard]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `this` after adjusting the coercions. Conclude with `⟨key Function.Embedding.some (by simp) h1, key secondFactorBlocks (by simp) h2⟩`.
-/
theorem SegreFlagProjSpecialDim.proof (hDim : PrimeDimLeTrdeg.Statement) (hTr : FlagProjTrdegLe.Statement) :
    SegreFlagProjSpecialDim.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hBB' w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _
    e t ht k hk
  obtain ⟨h1, h2⟩ := hTr O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk

  have hVt : (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat = ((d + Fintype.card K : ℕ) : ℕ∞) := by
    have h := DvrConeDimTrdeg.proof O K ι _ hV.multiProj hV.noTorsion
    rw [hV.dim] at h
    have h0 : ((d + 1 + Fintype.card K : ℕ) : ℕ∞) = (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat + 1 := by
      exact_mod_cast h
    have h' : ((d + Fintype.card K : ℕ) : ℕ∞) + 1 = (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat + 1 := by
      rw [← h0]; push_cast; ring
    exact (WithTop.add_right_cancel ENat.one_ne_top h').symm

  have hOΩ : Function.Injective (algebraMap O Ω) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hmem : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      simp [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, ha]
    rwa [hV.noTorsion, Ideal.mem_bot] at hmem
  have hOΦ : Function.Injective (algebraMap O Φ) := by
    rw [IsScalarTower.algebraMap_eq O Ω Φ]
    exact (algebraMap Ω Φ).injective.comp hOΩ

  have key : ∀ {K' : Type} [Fintype K'] [DecidableEq K'] (j : K' ↪ Option (Option K)), Fintype.card K' = Fintype.card K + 1 →
      Algebra.trdeg O (MRing (fun o => bundleIdx (bundleIdx ι M) M' (j o)) O ⧸
          pointIdeal O (flagProjPt j y w e φ φ' t k)) ≤ Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) + (k : Cardinal) →
      FieldNumbers.relDim (specialIdeal (pointIdeal O (flagProjPt j y w e φ φ' t k))) <
        ((d + k : ℕ) : WithBot (WithTop ℤ)) := by
    intro K' _ _ j hcard hle
    have hP : (pointIdeal O (flagProjPt j y w e φ φ' t k)).IsPrime := by
      unfold pointIdeal
      exact RingHom.ker_isPrime _
    have hPC := comap_C_pointIdeal hOΦ (flagProjPt j y w e φ φ' t k)
    refine relDim_specialIdeal_lt hϖ _ hPC (d + k) ((hDim O K' _ _ hP hPC).trans ?_)
    have ht : Cardinal.toENat _ ≤ Cardinal.toENat _ := OrderHomClass.mono Cardinal.toENat hle
    simp only [map_add, map_natCast, hVt] at ht
    have : ((Algebra.trdeg O (MRing (fun o => bundleIdx (bundleIdx ι M) M' (j o)) O ⧸
        pointIdeal O (flagProjPt j y w e φ φ' t k))).toENat + 1 : ℕ∞) ≤ ((d + k + Fintype.card K' : ℕ) : ℕ∞) := by
      rw [hcard]
      calc _ ≤ ((d + Fintype.card K : ℕ) : ℕ∞) + (k : ℕ∞) + 1 := by gcongr
        _ = _ := by push_cast; ring
    exact_mod_cast this
  exact ⟨key Function.Embedding.some (by simp) h1, key secondFactorBlocks (by simp) h2⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR

import Formalism.WachLatticeTwists.RamifiedBlockRings.RightIdealImageOfSurjective
import Formalism.CharacterColumnKernels.IdempotentNormalForms.GlobalModuleOf

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

/- English proof (translation)
Unfold `StatResConst`. Introduce `O _ _ X T hT f hf x y`. Use `set g : T := ⟨f, hf⟩ - algebraMap O T (f x) with hg`. Establish `hgnu : ¬ IsUnit g`. Introduce `hu`.

Use `hu.map ((Pi.evalRingHom (fun _ : X => O) x).comp T.val.toRingHom)` as an intermediate fact. Simplify using `[hg] at this`. Set `ψ : T →+* IsLocalRing.ResidueField O` to `(IsLocalRing.residue O).comp ((Pi.evalRingHom (fun _ : X => O) y).comp T.val.toRingHom)`. Establish `hsurj : Function.Surjective ψ`. Introduce `z`.

Take `⟨c, rfl⟩` from `IsLocalRing.residue_surjective z`. Conclude with `⟨algebraMap O T c, by simp [ψ]⟩`. Establish `hmax : (RingHom.ker ψ).IsMaximal` using `RingHom.ker_isMaximal_of_surjective ψ hsurj`. Establish `hker : RingHom.ker ψ = IsLocalRing.maximalIdeal T` using `IsLocalRing.eq_maximalIdeal hmax`. Establish `hgm : g ∈ RingHom.ker ψ`.

Rewrite using `[hker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `hgnu`. Rewrite `hgm` using `[RingHom.mem_ker]`. Simplify using `[ψ, hg, sub_eq_zero] at hgm`. Conclude with `hgm.symm`.
-/
theorem resConst : StatResConst := by
  unfold StatResConst
  intro O _ _ X T hT f hf x y
  set g : T := ⟨f, hf⟩ - algebraMap O T (f x) with hg
  have hgnu : ¬ IsUnit g := by
    intro hu
    have := hu.map ((Pi.evalRingHom (fun _ : X => O) x).comp T.val.toRingHom)
    simp [hg] at this
  let ψ : T →+* IsLocalRing.ResidueField O :=
    (IsLocalRing.residue O).comp ((Pi.evalRingHom (fun _ : X => O) y).comp T.val.toRingHom)
  have hsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective z
    exact ⟨algebraMap O T c, by simp [ψ]⟩
  have hmax : (RingHom.ker ψ).IsMaximal := RingHom.ker_isMaximal_of_surjective ψ hsurj
  have hker : RingHom.ker ψ = IsLocalRing.maximalIdeal T := IsLocalRing.eq_maximalIdeal hmax
  have hgm : g ∈ RingHom.ker ψ := by
    rw [hker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hgnu
  rw [RingHom.mem_ker] at hgm
  simp [ψ, hg, sub_eq_zero] at hgm
  exact hgm.symm

/- English proof (translation)
Unfold `StatSepPoint`. Introduce `O _ _ X _ T hsep x`. Establish `hy : ∀ y, ∃ g ∈ T, y ≠ x → g y = 0 ∧ g x ≠ 0`. Introduce `y`. Distinguish the cases in `hyx : y = x`.

Conclude with `⟨1, T.one_mem, fun h => absurd hyx h⟩`. Take `⟨f, hf, hne⟩` from `hsep x y (Ne.symm hyx)`. Use `⟨f - algebraMap O (X → O) (f y), T.sub_mem hf (T.algebraMap_mem _), fun _ => ⟨by simp, ?_⟩⟩` and prove the remaining obligations. Simplify `hne` using `[sub_eq_zero]`. Use `choose g hgT hg using hy`.

Use `⟨∏ y ∈ Finset.univ.erase x, g y, prod_mem fun y _ => hgT y, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.prod_apply, Finset.prod_ne_zero_iff]`. Introduce `y hy`. Conclude with `(hg y (Finset.ne_of_mem_erase hy)).2`. Introduce `z hz`.

Rewrite using `[Finset.prod_apply]`. Conclude with `Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hz, Finset.mem_univ z⟩) (hg z hz).1`.
-/
theorem sepPoint : StatSepPoint := by
  unfold StatSepPoint
  intro O _ _ X _ T hsep x
  classical
  have hy : ∀ y, ∃ g ∈ T, y ≠ x → g y = 0 ∧ g x ≠ 0 := by
    intro y
    by_cases hyx : y = x
    · exact ⟨1, T.one_mem, fun h => absurd hyx h⟩
    · obtain ⟨f, hf, hne⟩ := hsep x y (Ne.symm hyx)
      refine ⟨f - algebraMap O (X → O) (f y), T.sub_mem hf (T.algebraMap_mem _), fun _ => ⟨by simp, ?_⟩⟩
      simpa [sub_eq_zero] using hne
  choose g hgT hg using hy
  refine ⟨∏ y ∈ Finset.univ.erase x, g y, prod_mem fun y _ => hgT y, ?_, ?_⟩
  · rw [Finset.prod_apply, Finset.prod_ne_zero_iff]
    intro y hy
    exact (hg y (Finset.ne_of_mem_erase hy)).2
  · intro z hz
    rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hz, Finset.mem_univ z⟩) (hg z hz).1

/- English proof (translation)
Unfold `DvrArtinReesInclusion`. Introduce `O _ _ _ M _ _ _ _ R`. Take `⟨k, hk⟩` from `Ideal.exists_pow_inf_eq_pow_smul (IsLocalRing.maximalIdeal O) R`. Use `⟨k + 1, fun a ha haN => ?_⟩` and prove the remaining obligations. Establish `hmem : a ∈ (IsLocalRing.maximalIdeal O) ^ (k + 1) • (⊤ : Submodule O M) ⊓ R` using `Submodule.mem_inf.2 ⟨haN, ha⟩`.

Rewrite `hmem` using `[hk (k + 1) (Nat.le_succ k), Nat.add_sub_cancel_left, pow_one]`. Conclude with `Submodule.smul_mono le_rfl inf_le_right hmem`.
-/
theorem satur : DvrArtinReesInclusion := by
  unfold DvrArtinReesInclusion
  intro O _ _ _ M _ _ _ _ R
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (IsLocalRing.maximalIdeal O) R
  refine ⟨k + 1, fun a ha haN => ?_⟩
  have hmem : a ∈ (IsLocalRing.maximalIdeal O) ^ (k + 1) • (⊤ : Submodule O M) ⊓ R :=
    Submodule.mem_inf.2 ⟨haN, ha⟩
  rw [hk (k + 1) (Nat.le_succ k), Nat.add_sub_cancel_left, pow_one] at hmem
  exact Submodule.smul_mono le_rfl inf_le_right hmem

/- English proof (translation)
Unfold `StatIdemSmall`. Introduce `O _ _ _ n _ _ e he h0`. Establish `h1 : (IsLocalRing.residue O).mapMatrix (1 - e) = 1`. Rewrite using `[map_sub, map_one, RingHom.mapMatrix_apply, h0, sub_zero]`. Establish `hres : IsLocalRing.residue O (1 - e).det = 1`.

Rewrite using `[RingHom.map_det, h1, Matrix.det_one]`. Establish `hdet : IsUnit (1 - e).det`. Assume the negation of the conclusion as `hnu`. Establish `hm : (1 - e).det ∈ IsLocalRing.maximalIdeal O` using `hnu`. Rewrite `hm` using `[← IsLocalRing.residue_eq_zero_iff]`.

Rewrite `hres` using `[hm]`. Conclude with `zero_ne_one hres`. Establish `hmul : e * (1 - e) = 0`. Rewrite using `[Matrix.mul_sub, Matrix.mul_one, he, sub_self]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]`. Use `_ = 0 := by rw [hmul, Matrix.zero_mul]`.
-/
theorem idemSmall : StatIdemSmall := by
  unfold StatIdemSmall
  intro O _ _ _ n _ _ e he h0
  have h1 : (IsLocalRing.residue O).mapMatrix (1 - e) = 1 := by
    rw [map_sub, map_one, RingHom.mapMatrix_apply, h0, sub_zero]
  have hres : IsLocalRing.residue O (1 - e).det = 1 := by
    rw [RingHom.map_det, h1, Matrix.det_one]
  have hdet : IsUnit (1 - e).det := by
    by_contra hnu
    have hm : (1 - e).det ∈ IsLocalRing.maximalIdeal O := hnu
    rw [← IsLocalRing.residue_eq_zero_iff] at hm
    rw [hm] at hres
    exact zero_ne_one hres
  have hmul : e * (1 - e) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, he, sub_self]
  calc e = e * (1 - e) * (1 - e)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
    _ = 0 := by rw [hmul, Matrix.zero_mul]

/- English proof (translation)
Unfold `StatCommonNonzero`. Introduce `O _ _ _ σ ι _ D hD`. Establish `hprod : (∏ i, D i) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i _ => hD i`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Apply `hprod` to reduce the goal to its premises. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `z`. Take `⟨i, hi⟩` from `hcon z`. Rewrite using `[map_prod, map_zero]`.

Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) hi`.
-/
theorem commonNonzero : StatCommonNonzero := by
  unfold StatCommonNonzero
  intro O _ _ _ σ ι _ D hD
  classical
  have hprod : (∏ i, D i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hD i
  by_contra hcon
  push_neg at hcon
  apply hprod
  apply MvPolynomial.funext
  intro z
  obtain ⟨i, hi⟩ := hcon z
  rw [map_prod, map_zero]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

/- English proof (translation)
Unfold `RightIdealImageOfSurjective`. Introduce `O R' _ _ _ n _ _ ρ hρ e₁ A`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨B, rfl⟩`. Take `⟨b, rfl⟩` from `hρ B`.

Conclude with `⟨b, by rw [map_mul]⟩`. Introduce and unpack `⟨a, rfl⟩`. Conclude with `⟨ρ a, by rw [map_mul]⟩`.
-/
theorem idempotent_image_surjective : RightIdealImageOfSurjective := by
  unfold RightIdealImageOfSurjective
  intro O R' _ _ _ n _ _ ρ hρ e₁ A
  constructor
  · rintro ⟨B, rfl⟩
    obtain ⟨b, rfl⟩ := hρ B
    exact ⟨b, by rw [map_mul]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨ρ a, by rw [map_mul]⟩

/- English proof (translation)
Unfold `StatRootsInt`. Introduce `O _ _ _ P t α hP`. Establish `hinj : Function.Injective (algebraMap O (FractionRing O))` using `IsFractionRing.injective O (FractionRing O)`. Establish `hmon : (P.map (algebraMap O (FractionRing O))).Monic`. Rewrite using `[hP]`.

Conclude with `Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _`. Establish `hPm : P.Monic` using `by first`. Consider the case `exact Polynomial.monic_of_injective hinj hmon`. Consider the case `(rw [Polynomial.Monic, ← hinj.eq_iff, map_one, ← Polynomial.leadingCoeff_map_of_injective hinj]`. Conclude with `hmon)`.

Establish `hint : ∀ i, ∃ b : O, algebraMap O (FractionRing O) b = α i`. Introduce `i`. Establish `hroot : Polynomial.eval₂ (algebraMap O (FractionRing O)) (α i) P = 0`. Rewrite using `[Polynomial.eval₂_eq_eval_map, hP, Polynomial.eval_prod]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by simp)`.

Conclude with `IsIntegrallyClosed.isIntegral_iff.1 ⟨P, hPm, hroot⟩`. Use `choose β hβ using hint`. Use `⟨β, hβ, ?_⟩` and prove the remaining obligations. Apply `Polynomial.map_injective _ hinj` to reduce the goal to its premises. Rewrite using `[hP, Polynomial.map_prod]`.

Simplify using `[hβ]`.
-/
theorem rootsInt : StatRootsInt := by
  unfold StatRootsInt
  intro O _ _ _ P t α hP
  have hinj : Function.Injective (algebraMap O (FractionRing O)) :=
    IsFractionRing.injective O (FractionRing O)
  have hmon : (P.map (algebraMap O (FractionRing O))).Monic := by
    rw [hP]
    exact Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hPm : P.Monic := by
    first
    | exact Polynomial.monic_of_injective hinj hmon
    | (rw [Polynomial.Monic, ← hinj.eq_iff, map_one, ← Polynomial.leadingCoeff_map_of_injective hinj]
       exact hmon)
  have hint : ∀ i, ∃ b : O, algebraMap O (FractionRing O) b = α i := by
    intro i
    have hroot : Polynomial.eval₂ (algebraMap O (FractionRing O)) (α i) P = 0 := by
      rw [Polynomial.eval₂_eq_eval_map, hP, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    exact IsIntegrallyClosed.isIntegral_iff.1 ⟨P, hPm, hroot⟩
  choose β hβ using hint
  refine ⟨β, hβ, ?_⟩
  apply Polynomial.map_injective _ hinj
  rw [hP, Polynomial.map_prod]
  simp [hβ]

/- English proof (translation)
Unfold `BlockRingDecompositionLemma`. Introduce `O _ _ _ X d G _ _ _ t ht bl T D _ _ hTop Z NN _ _ g₀ n hspan hZ hcard`. Unfold `RingData.Top RingTop at hTop`. Take `⟨h1, h2, h3, -, -, -, h7, h8, h9, h10, -⟩` from `hTop`. Establish `hsum : ∑ k : Fin (t + 1), Fintype.card {a // bl a = k} = Fintype.card d`.

Rewrite using `[← Fintype.card_sigma]`. Conclude with `Fintype.card_congr (Equiv.sigmaFiberEquiv bl)`. Establish `hcard' : ((g₀ * ∑ k : Fin (t + 1), Fintype.card {a // bl a = k} : ℕ) : Cardinal) < Cardinal.mk (IsLocalRing.ResidueField O)`. Rewrite using `[hsum]`. Conclude with `hcard`.

Establish `hmain` using `Formalism.NG.globalModule O X D.X' T D.T' Z D.p D.q D.b h1 (fun x _ => h2 x) d D.R' h3 NN g₀ n hspan hZ D.π' D.ρπ h7 (Fin (t + 1)) bl h8 D.ρk h9 h10 hcard'`. Conclude with `hmain.trans (Finset.sum_le_sum_of_subset (Finset.subset_univ _))`.
-/
theorem lemma_five_three_holds : BlockRingDecompositionLemma := by
  unfold BlockRingDecompositionLemma
  intro O _ _ _ X d G _ _ _ t ht bl T D _ _ hTop Z NN _ _ g₀ n hspan hZ hcard
  unfold RingData.Top RingTop at hTop
  obtain ⟨h1, h2, h3, -, -, -, h7, h8, h9, h10, -⟩ := hTop

  have hsum : ∑ k : Fin (t + 1), Fintype.card {a // bl a = k} = Fintype.card d := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv bl)
  have hcard' : ((g₀ * ∑ k : Fin (t + 1), Fintype.card {a // bl a = k} : ℕ) : Cardinal) <
      Cardinal.mk (IsLocalRing.ResidueField O) := by
    rw [hsum]; exact hcard

  have hmain := Formalism.NG.globalModule O X D.X' T D.T' Z D.p D.q D.b h1 (fun x _ => h2 x) d D.R' h3
    NN g₀ n hspan hZ D.π' D.ρπ h7 (Fin (t + 1)) bl h8 D.ρk h9 h10 hcard'
  exact hmain.trans (Finset.sum_le_sum_of_subset (Finset.subset_univ _))

end Formalism.RepresentationBoundsCohomology.ringDataObjects

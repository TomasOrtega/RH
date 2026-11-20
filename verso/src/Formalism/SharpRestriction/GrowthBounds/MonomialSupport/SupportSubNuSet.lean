import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.NoOpStep
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.MaxTwistDegreePderivLeAddOne

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.LetterSubstitution

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.PairMembershipBlocks

section Coef

variable {σ τ Kf : Type} [Field Kf]

/- English proof (translation)
Unfold `oneT`. Rewrite using `[MvPolynomial.coeff_sum]`. Simplify using `only [MvPolynomial.coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq']`. Use `split_ifs with h`.

Both sides reduce to the same expression. Rewrite using `[MvPolynomial.notMem_support_iff.1 h, map_zero]`.
-/
theorem coeff_oneT (A : Module.End Kf (MvPolynomial τ Kf)) (F : MvPolynomial σ (MvPolynomial τ Kf)) (mo : σ →₀ ℕ) :
    (oneT A F).coeff mo = A (F.coeff mo) := by
  unfold oneT
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.1 h, map_zero]

/- English proof (translation)
Unfold `planeCoeff`. Rewrite using `[MvPolynomial.coeff_sum]`. Simplify using `only [MvPolynomial.coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq']`. Use `split_ifs with h`.

Both sides reduce to the same expression. Rewrite using `[MvPolynomial.notMem_support_iff.1 h, MvPolynomial.coeff_zero]`.
-/
theorem coeff_planeCoeff (nu : τ →₀ ℕ) (F : MvPolynomial σ (MvPolynomial τ Kf)) (mo : σ →₀ ℕ) :
    (planeCoeff nu F).coeff mo = (F.coeff mo).coeff nu := by
  unfold planeCoeff
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.1 h, MvPolynomial.coeff_zero]

def nuSet (F : MvPolynomial σ (MvPolynomial τ Kf)) : Finset (τ →₀ ℕ) :=
  F.support.biUnion fun mo => (F.coeff mo).support

/- English proof (translation)
Introduce `nu h`. Unfold `nuSet`. Rewrite using `[Finset.mem_biUnion]`. Use `⟨mo, ?_, h⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.mem_support_iff]`.

Introduce `h0`. Rewrite `h` using `[h0, MvPolynomial.support_zero]`. Conclude with `Finset.notMem_empty _ h`.
-/
theorem support_sub_nuSet (F : MvPolynomial σ (MvPolynomial τ Kf)) (mo : σ →₀ ℕ) :
    (F.coeff mo).support ⊆ nuSet F := by
  intro nu h
  unfold nuSet
  rw [Finset.mem_biUnion]
  refine ⟨mo, ?_, h⟩
  rw [MvPolynomial.mem_support_iff]
  intro h0
  rw [h0, MvPolynomial.support_zero] at h
  exact Finset.notMem_empty _ h

/- English proof (translation)
Repeatedly rewrite using `[MvPolynomial.smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[← Finset.sum_subset hN]`. Conclude with `(MvPolynomial.support_sum_monomial_coeff y).symm`. Introduce `x _ hx`. Rewrite using `[MvPolynomial.notMem_support_iff.1 hx, MvPolynomial.monomial_zero]`.
-/
theorem expand_sub (y : MvPolynomial τ Kf) (N : Finset (τ →₀ ℕ)) (hN : y.support ⊆ N) :
    y = ∑ nu' ∈ N, y.coeff nu' • monomial nu' (1 : Kf) := by
  simp_rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [← Finset.sum_subset hN]
  · exact (MvPolynomial.support_sum_monomial_coeff y).symm
  · intro x _ hx
    rw [MvPolynomial.notMem_support_iff.1 hx, MvPolynomial.monomial_zero]

/- English proof (translation)
Use extensionality with `mo : 1`. Rewrite using `[coeff_planeCoeff, coeff_oneT, MvPolynomial.coeff_sum]`. Simplify using `only [MvPolynomial.coeff_smul, coeff_planeCoeff, smul_eq_mul]`. Use `conv_lhs => rw [expand_sub (F.coeff mo) (nuSet F) (support_sub_nuSet F mo)]`. Rewrite using `[map_sum, MvPolynomial.coeff_sum]`.

Use `Finset.sum_congr rfl fun nu' _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, MvPolynomial.coeff_smul, smul_eq_mul, mul_comm]`.
-/
theorem planeCoeff_oneT (A : Module.End Kf (MvPolynomial τ Kf)) (F : MvPolynomial σ (MvPolynomial τ Kf))
    (nu : τ →₀ ℕ) :
    planeCoeff nu (oneT A F) = ∑ nu' ∈ nuSet F, (A (monomial nu' 1)).coeff nu • planeCoeff nu' F := by
  ext mo : 1
  rw [coeff_planeCoeff, coeff_oneT, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_smul, coeff_planeCoeff, smul_eq_mul]
  conv_lhs => rw [expand_sub (F.coeff mo) (nuSet F) (support_sub_nuSet F mo)]
  rw [map_sum, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun nu' _ => ?_
  rw [map_smul, MvPolynomial.coeff_smul, smul_eq_mul, mul_comm]

/- English proof (translation)
Use extensionality with `mo : 1`. Rewrite using `[coeff_oneT, coeff_oneT, coeff_oneT, Module.End.mul_apply]`.
-/
theorem oneT_mul (A B : Module.End Kf (MvPolynomial τ Kf)) (F : MvPolynomial σ (MvPolynomial τ Kf)) :
    oneT (A * B) F = oneT A (oneT B F) := by
  ext mo : 1
  rw [coeff_oneT, coeff_oneT, coeff_oneT, Module.End.mul_apply]

/- English proof (translation)
Use extensionality with `mo : 1`. Rewrite using `[coeff_oneT, h, MvPolynomial.coeff_zero]`.
-/
theorem oneT_eq_zero (A : Module.End Kf (MvPolynomial τ Kf)) (F : MvPolynomial σ (MvPolynomial τ Kf))
    (h : ∀ mo, A (F.coeff mo) = 0) : oneT A F = 0 := by
  ext mo : 1
  rw [coeff_oneT, h, MvPolynomial.coeff_zero]

/- English proof (translation)
Unfold `planeCoeff`. Simplify using the standard rewrite rules.
-/
theorem planeCoeff_zero' (nu : τ →₀ ℕ) : planeCoeff nu (0 : MvPolynomial σ (MvPolynomial τ Kf)) = 0 := by
  unfold planeCoeff
  simp

/- English proof (translation)
Use extensionality with `mo : 1`. Rewrite using `[coeff_planeCoeff, MvPolynomial.coeff_sum, MvPolynomial.coeff_sum, MvPolynomial.coeff_sum]`. Simplify using `only [coeff_planeCoeff]`.
-/
theorem planeCoeff_sum {κ : Type} (S : Finset κ) (f : κ → MvPolynomial σ (MvPolynomial τ Kf)) (nu : τ →₀ ℕ) :
    planeCoeff nu (∑ k ∈ S, f k) = ∑ k ∈ S, planeCoeff nu (f k) := by
  ext mo : 1
  rw [coeff_planeCoeff, MvPolynomial.coeff_sum, MvPolynomial.coeff_sum, MvPolynomial.coeff_sum]
  simp only [coeff_planeCoeff]

end Coef

section XXLin

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} [NeZero J] [NeZero r]
  (Dt : SignedChainData p O r J) (d : TL J Dt.nL r → ℕ) (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ)

/- English proof (translation)
Introduce `k hk`. Substitute `hk` using the available equality. Proceed by induction on `a using WithTop.recTopCoe with`. Consider the case `top => exact absurd hab (by simp)`. Consider the case `coe a`.

Establish `h1` using `ha a rfl`. Establish `h2 : a ≤ k` using `WithTop.coe_le_coe.1 hab`. Conclude with `le_trans h1 (by exact_mod_cast h2)`.
-/
private theorem geZ_of_le {a b : WithTop ℤ} {t : ℝ} (ha : geZ a t) (hab : a ≤ b) : geZ b t := by
  intro k hk
  subst hk
  induction a using WithTop.recTopCoe with
  | top => exact absurd hab (by simp)
  | coe a =>
    have h1 := ha a rfl
    have h2 : a ≤ k := WithTop.coe_le_coe.1 hab
    exact le_trans h1 (by exact_mod_cast h2)

/- English proof (translation)
Break down `le_total a b with h | h` into its components or cases. Rewrite using `[inf_of_le_left h]`. Conclude with `ha`. Rewrite using `[inf_of_le_right h]`. Conclude with `hb`.
-/
private theorem geZ_inf {a b : WithTop ℤ} {t : ℝ} (ha : geZ a t) (hb : geZ b t) : geZ (a ⊓ b) t := by
  rcases le_total a b with h | h
  · rw [inf_of_le_left h]
    exact ha
  · rw [inf_of_le_right h]
    exact hb

/- English proof (translation)
Unfold `valS`. Rewrite using `[← Finset.inf_union]`. Apply `Finset.inf_mono` to reduce the goal to its premises. Introduce `k hk`. Unfold `sDegs at hk ⊢`.

Rewrite `hk` using `[map_add]`. Rewrite using `[Finset.mem_union, Finset.mem_biUnion, Finset.mem_biUnion]`. Rewrite `hk` using `[Finset.mem_biUnion]`. Take `⟨m, -, hk⟩` from `hk`. Rewrite `hk` using `[MvPolynomial.coeff_add, AddMonoidAlgebra.coeff_add]`.

Break down `Finset.mem_union.1 (Finsupp.support_add hk) with h | h` into its components or cases. Use `Or.inl ⟨m, ?_, h⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.mem_support_iff]`. Introduce `h0`. Rewrite `h` using `[h0, AddMonoidAlgebra.coeff_zero]`.

Simplify using `at h`. Use `Or.inr ⟨m, ?_, h⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.mem_support_iff]`. Introduce `h0`. Rewrite `h` using `[h0, AddMonoidAlgebra.coeff_zero]`.

Simplify using `at h`.
-/
private theorem valS_inf_le_valS_add {R : Type} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : valS LL S F ⊓ valS LL S G ≤ valS LL S (F + G) := by
  unfold valS
  rw [← Finset.inf_union]
  apply Finset.inf_mono
  intro k hk
  unfold sDegs at hk ⊢
  rw [map_add] at hk
  rw [Finset.mem_union, Finset.mem_biUnion, Finset.mem_biUnion]
  rw [Finset.mem_biUnion] at hk
  obtain ⟨m, -, hk⟩ := hk
  rw [MvPolynomial.coeff_add, AddMonoidAlgebra.coeff_add] at hk
  rcases Finset.mem_union.1 (Finsupp.support_add hk) with h | h
  · refine Or.inl ⟨m, ?_, h⟩
    rw [MvPolynomial.mem_support_iff]
    intro h0
    rw [h0, AddMonoidAlgebra.coeff_zero] at h
    simp at h
  · refine Or.inr ⟨m, ?_, h⟩
    rw [MvPolynomial.mem_support_iff]
    intro h0
    rw [h0, AddMonoidAlgebra.coeff_zero] at h
    simp at h

/- English proof (translation)
Unfold `valS`. Apply `Finset.inf_mono` to reduce the goal to its premises. Introduce `k hk`. Unfold `sDegs at hk ⊢`. Rewrite `hk` using `[map_mul]`.

Rewrite `hk`, the goal using `[Finset.mem_biUnion]`. Take `⟨m, -, hk⟩` from `hk`. Establish `hC : twistSub LL S (lastIdx n) (MvPolynomial.C c) = MvPolynomial.C (coefL R n c)`. Unfold `twistSub`. Rewrite using `[MvPolynomial.eval₂Hom_C, RingHom.comp_apply]`.

Rewrite `hk` using `[hC, MvPolynomial.coeff_C_mul]`. Unfold `coefL at hk`. Rewrite `hk` using `[RingHom.comp_apply, ← LaurentPolynomial.single_eq_C]`. Establish `hk2` using `Finsupp.mem_support_iff.1 hk`. Rewrite `hk2` using `[AddMonoidAlgebra.coeff_single_zero_mul]`.

Establish `hk3` using `right_ne_zero_of_mul hk2`. Use `⟨m, ?_, Finsupp.mem_support_iff.2 hk3⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.mem_support_iff]`. Introduce `h0`. Rewrite `hk3` using `[h0, AddMonoidAlgebra.coeff_zero]`.

Conclude with `hk3 rfl`.
-/
private theorem valS_le_valS_C_mul {R : Type} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (c : R) (F : MvPolynomial (ι × Fin n) R) : valS LL S F ≤ valS LL S (MvPolynomial.C c * F) := by
  unfold valS
  apply Finset.inf_mono
  intro k hk
  unfold sDegs at hk ⊢
  rw [map_mul] at hk
  rw [Finset.mem_biUnion] at hk ⊢
  obtain ⟨m, -, hk⟩ := hk
  have hC : twistSub LL S (lastIdx n) (MvPolynomial.C c) = MvPolynomial.C (coefL R n c) := by
    unfold twistSub
    rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
  rw [hC, MvPolynomial.coeff_C_mul] at hk
  unfold coefL at hk
  rw [RingHom.comp_apply, ← LaurentPolynomial.single_eq_C] at hk
  have hk2 := Finsupp.mem_support_iff.1 hk
  rw [AddMonoidAlgebra.coeff_single_zero_mul] at hk2
  have hk3 := right_ne_zero_of_mul hk2
  refine ⟨m, ?_, Finsupp.mem_support_iff.2 hk3⟩
  rw [MvPolynomial.mem_support_iff]
  intro h0
  rw [h0, AddMonoidAlgebra.coeff_zero] at hk3
  exact hk3 rfl

/- English proof (translation)
Unfold `SignedChainData.Fdig`. Apply `Finset.sum_subset (Finset.filter_subset_filter _ hT)` to reduce the goal to its premises. Introduce `x hx hnx`. Establish `hxF : x ∉ F.support` using `fun h => hnx (Finset.mem_filter.2 ⟨h, (Finset.mem_filter.1 hx).2⟩)`. Rewrite using `[MvPolynomial.notMem_support_iff.1 hxF, MvPolynomial.C_0, zero_mul]`.
-/
private theorem fdig_eq_sum_filter_digOK_of_support_subset (rho : (ZMod J × Fin r) × Fin r → ℕ) (F : MvPolynomial (TL J Dt.nL r × Fin r) (KK O))
    (T : Finset (TL J Dt.nL r × Fin r →₀ ℕ)) (hT : F.support ⊆ T) :
    Dt.Fdig rho F = ∑ mo ∈ T with Dt.digOK rho mo,
      MvPolynomial.C (MvPolynomial.coeff mo F) * ∏ v ∈ mo.support, MvPolynomial.X (Dt.liftVar v) ^ Dt.liftExp mo v := by
  unfold SignedChainData.Fdig
  apply Finset.sum_subset (Finset.filter_subset_filter _ hT)
  intro x hx hnx
  have hxF : x ∉ F.support := fun h => hnx (Finset.mem_filter.2 ⟨h, (Finset.mem_filter.1 hx).2⟩)
  rw [MvPolynomial.notMem_support_iff.1 hxF, MvPolynomial.C_0, zero_mul]

/- English proof (translation)
Rewrite using `[fdig_eq_sum_filter_digOK_of_support_subset Dt rho (F + G) (F.support ∪ G.support) MvPolynomial.support_add, fdig_eq_sum_filter_digOK_of_support_subset Dt rho F (F.support ∪ G.support) Finset.subset_union_left, fdig_eq_sum_filter_digOK_of_support_subset Dt rho G (F.support ∪ G.su …`. Use `Finset.sum_congr rfl fun mo _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_add, MvPolynomial.C_add, add_mul]`.
-/
private theorem fdig_add (rho : (ZMod J × Fin r) × Fin r → ℕ) (F G : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) :
    Dt.Fdig rho (F + G) = Dt.Fdig rho F + Dt.Fdig rho G := by
  rw [fdig_eq_sum_filter_digOK_of_support_subset Dt rho (F + G) (F.support ∪ G.support) MvPolynomial.support_add,
    fdig_eq_sum_filter_digOK_of_support_subset Dt rho F (F.support ∪ G.support) Finset.subset_union_left,
    fdig_eq_sum_filter_digOK_of_support_subset Dt rho G (F.support ∪ G.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun mo _ => ?_
  rw [MvPolynomial.coeff_add, MvPolynomial.C_add, add_mul]

/- English proof (translation)
Rewrite using `[fdig_eq_sum_filter_digOK_of_support_subset Dt rho (c • F) F.support MvPolynomial.support_smul, fdig_eq_sum_filter_digOK_of_support_subset Dt rho F F.support subset_rfl, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun mo _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_smul, smul_eq_mul, MvPolynomial.C_mul, mul_assoc]`.
-/
private theorem fdig_smul (rho : (ZMod J × Fin r) × Fin r → ℕ) (c : KK O)
    (F : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) :
    Dt.Fdig rho (c • F) = MvPolynomial.C c * Dt.Fdig rho F := by
  rw [fdig_eq_sum_filter_digOK_of_support_subset Dt rho (c • F) F.support MvPolynomial.support_smul,
    fdig_eq_sum_filter_digOK_of_support_subset Dt rho F F.support subset_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun mo _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, MvPolynomial.C_mul, mul_assoc]

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hF`. Take `⟨g1, g2, g3⟩` from `hG`. Use `⟨Submodule.add_mem _ h1 g1, fun rho j i => ?_, fun j m hm => ?_⟩` and prove the remaining obligations. Rewrite using `[fdig_add]`. Conclude with `geZ_of_le (geZ_inf (h2 rho j i) (g2 rho j i)) (valS_inf_le_valS_add _ _ _ _)`.

Conclude with `geZ_of_le (geZ_inf (h3 j m hm) (g3 j m hm)) (valS_inf_le_valS_add _ _ _ _)`.
-/
theorem XXg_add {F G : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)} (hF : XXg Dt d th thL F)
    (hG : XXg Dt d th thL G) : XXg Dt d th thL (F + G) := by
  obtain ⟨h1, h2, h3⟩ := hF
  obtain ⟨g1, g2, g3⟩ := hG
  refine ⟨Submodule.add_mem _ h1 g1, fun rho j i => ?_, fun j m hm => ?_⟩
  · rw [fdig_add]
    exact geZ_of_le (geZ_inf (h2 rho j i) (g2 rho j i)) (valS_inf_le_valS_add _ _ _ _)
  · exact geZ_of_le (geZ_inf (h3 j m hm) (g3 j m hm)) (valS_inf_le_valS_add _ _ _ _)

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hF`. Use `⟨Submodule.smul_mem _ c h1, fun rho j i => ?_, fun j m hm => ?_⟩` and prove the remaining obligations. Rewrite using `[fdig_smul]`. Conclude with `geZ_of_le (h2 rho j i) (valS_le_valS_C_mul _ _ _ _)`. Rewrite using `[MvPolynomial.smul_eq_C_mul]`.

Conclude with `geZ_of_le (h3 j m hm) (valS_le_valS_C_mul _ _ _ _)`.
-/
theorem XXg_smul (c : KK O) {F : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)} (hF : XXg Dt d th thL F) :
    XXg Dt d th thL (c • F) := by
  obtain ⟨h1, h2, h3⟩ := hF
  refine ⟨Submodule.smul_mem _ c h1, fun rho j i => ?_, fun j m hm => ?_⟩
  · rw [fdig_smul]
    exact geZ_of_le (h2 rho j i) (valS_le_valS_C_mul _ _ _ _)
  · rw [MvPolynomial.smul_eq_C_mul]
    exact geZ_of_le (h3 j m hm) (valS_le_valS_C_mul _ _ _ _)

/- English proof (translation)
Use `⟨Submodule.zero_mem _, fun rho j i => ?_, fun j m hm => ?_⟩` and prove the remaining obligations. Introduce `k hk`. Simplify using `[valS, sDegs, SignedChainData.Fdig] at hk`. Introduce `k hk`. Simplify using `[valS, sDegs] at hk`.
-/
theorem XXg_zero : XXg Dt d th thL (0 : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) := by
  refine ⟨Submodule.zero_mem _, fun rho j i => ?_, fun j m hm => ?_⟩
  · intro k hk
    simp [valS, sDegs, SignedChainData.Fdig] at hk
  · intro k hk
    simp [valS, sDegs] at hk

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => rw [Finset.sum_empty]`. Conclude with `XXg_zero Dt d th thL`. Consider the case `insert a S ha ih`. Rewrite using `[Finset.sum_insert ha]`.

Conclude with `XXg_add Dt d th thL (h a (Finset.mem_insert_self a S)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))`.
-/
theorem XXg_sum {κ : Type} (S : Finset κ) (f : κ → MvPolynomial (TL J Dt.nL r × Fin r) (KK O))
    (h : ∀ k ∈ S, XXg Dt d th thL (f k)) : XXg Dt d th thL (∑ k ∈ S, f k) := by
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact XXg_zero Dt d th thL
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact XXg_add Dt d th thL (h a (Finset.mem_insert_self a S))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

end XXLin

section Dec

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (E : ι → GLOps n K V) (ee : ι → (Fin n → ℤ) → Module.End K V)

def isoOn (I : Finset ι) : Set V := {x | ∃ ka : ι → Fin n → ℤ, ∀ i ∈ I, x ∈ isoSub (E i) (ka i)}

/- English proof (translation)
Proceed by induction on `I using Finset.induction_on with`. Consider the case `empty`. Introduce `y`. Conclude with `Submodule.subset_span ⟨fun _ => 0, fun i hi => absurd hi (Finset.notMem_empty i)⟩`. Consider the case `insert i0 I hi0 ih`.

Establish `key : ∀ x ∈ isoOn E I, x ∈ Submodule.span K (isoOn E (insert i0 I))`. Introduce and unpack `x ⟨ka, hka⟩`. Take `⟨T, hT, hmem⟩` from `hdec i0 x`. Rewrite using `[hT]`. Use `Submodule.sum_mem _ fun mu _ => Submodule.subset_span ⟨Function.update ka i0 mu, fun i hi => ?_⟩` and prove the remaining obligations.

Break down `Finset.mem_insert.1 hi with rfl | hi'` into its components or cases. Rewrite using `[Function.update_self]`. Conclude with `hmem mu`. Establish `hne : i ≠ i0` using `fun h => hi0 (h ▸ hi')`. Rewrite using `[Function.update_of_ne hne]`.

Establish `hfix : ee i (ka i) x = x` using `(hee i (ka i)).1 x (hka i hi')`. Establish `: ee i0 mu x = ee i (ka i) (ee i0 mu x)` using `by conv_lhs => rw [← hfix]`. Rewrite using `[← Module.End.mul_apply, hcomm i0 i mu (ka i), Module.End.mul_apply]`. Rewrite using `[this]`. Take `⟨_, _, h3⟩` from `hdec i (ee i0 mu x)`.

Conclude with `h3 (ka i)`. Introduce `y`. Conclude with `(Submodule.span_le.2 key) (ih y)`.
-/
theorem span_isoOn (hee : ∀ i mu, IsIsoProj (E i) mu (ee i mu))
    (hcomm : ∀ i i' mu mu', ee i mu * ee i' mu' = ee i' mu' * ee i mu)
    (hdec : ∀ i (G : V), ∃ T : Finset (Fin n → ℤ), G = ∑ mu ∈ T, ee i mu G ∧ ∀ mu, ee i mu G ∈ isoSub (E i) mu)
    (I : Finset ι) : ∀ y : V, y ∈ Submodule.span K (isoOn E I) := by
  induction I using Finset.induction_on with
  | empty =>
    intro y
    exact Submodule.subset_span ⟨fun _ => 0, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert i0 I hi0 ih =>
    have key : ∀ x ∈ isoOn E I, x ∈ Submodule.span K (isoOn E (insert i0 I)) := by
      rintro x ⟨ka, hka⟩
      obtain ⟨T, hT, hmem⟩ := hdec i0 x
      rw [hT]
      refine Submodule.sum_mem _ fun mu _ => Submodule.subset_span ⟨Function.update ka i0 mu, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi'
      · rw [Function.update_self]; exact hmem mu
      · have hne : i ≠ i0 := fun h => hi0 (h ▸ hi')
        rw [Function.update_of_ne hne]
        have hfix : ee i (ka i) x = x := (hee i (ka i)).1 x (hka i hi')
        have : ee i0 mu x = ee i (ka i) (ee i0 mu x) := by
          conv_lhs => rw [← hfix]
          rw [← Module.End.mul_apply, hcomm i0 i mu (ka i), Module.End.mul_apply]
        rw [this]
        obtain ⟨_, _, h3⟩ := hdec i (ee i0 mu x)
        exact h3 (ka i)
    intro y
    exact (Submodule.span_le.2 key) (ih y)

/- English proof (translation)
Establish `hall` using `span_isoOn E ee hee hcomm hdec Finset.univ y`. Take `⟨N, f, g, hy⟩` from `(Submodule.mem_span_set').1 hall`. Establish `hg : ∀ j, ∃ ka : ι → Fin n → ℤ, ∀ i, (g j : V) ∈ isoSub (E i) (ka i)`. Introduce `j`. Take `⟨ka, hka⟩` from `(g j).2`.

Conclude with `⟨ka, fun i => hka i (Finset.mem_univ i)⟩`. Use `choose kx hkx using hg`. Establish `key : ∀ (x : V) (ka : ι → Fin n → ℤ), (∀ i, x ∈ isoSub (E i) (ka i)) → ∀ ka' : ι → Fin n → ℤ, jointE ee ka' x = if ka' = ka then x else 0`. Introduce `x ka hx ka'`. Unfold `jointE`.

Establish `hL : ∀ L : List ι, (L.map fun i => ee i (ka' i)).prod x = if ∀ i ∈ L, ka' i = ka i then x else 0`. Introduce `L`. Proceed by induction on `L with`. Consider the case `nil => simp`. Consider the case `cons a L ih`.

Rewrite using `[List.map_cons, List.prod_cons, Module.End.mul_apply, ih]`. Distinguish the cases in `hL : ∀ i ∈ L, ka' i = ka i`. Rewrite using `[if_pos hL]`. Distinguish the cases in `ha : ka' a = ka a`. Rewrite using `[ha, (hee a (ka a)).1 x (hx a), if_pos]`.

Introduce `i hi`. Break down `List.mem_cons.1 hi with rfl | hi` into its components or cases. Conclude with `ha`. Conclude with `hL i hi`. Rewrite using `[(hee a (ka' a)).2 (ka a) (Ne.symm ha) x (hx a), if_neg]`.

Introduce `h`. Conclude with `ha (h a List.mem_cons_self)`. Rewrite using `[if_neg hL, map_zero, if_neg]`. Introduce `h`. Conclude with `hL fun i hi => h i (List.mem_cons_of_mem _ hi)`.

Rewrite using `[hL]`. Use `congr 1`. Apply `propext` to reduce the goal to its premises. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use function extensionality and compare the values at `i`. Conclude with `h i (Finset.mem_toList.2 (Finset.mem_univ i))`. Introduce `h i _`. Rewrite using `[h]`. Use `⟨Finset.univ.image kx, fun S' hS' => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hy]`. Repeatedly rewrite using `[map_sum, map_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.smul_sum]`.

Use `congr 1`. Rewrite using `[Finset.sum_congr rfl fun ka _ => key _ _ (hkx j) ka, Finset.sum_ite_eq']`. Rewrite using `[if_pos (hS' (Finset.mem_image_of_mem kx (Finset.mem_univ j)))]`.
-/
theorem joint_dec (hee : ∀ i mu, IsIsoProj (E i) mu (ee i mu))
    (hcomm : ∀ i i' mu mu', ee i mu * ee i' mu' = ee i' mu' * ee i mu)
    (hdec : ∀ i (G : V), ∃ T : Finset (Fin n → ℤ), G = ∑ mu ∈ T, ee i mu G ∧ ∀ mu, ee i mu G ∈ isoSub (E i) mu)
    (y : V) : ∃ S : Finset (ι → Fin n → ℤ), ∀ S', S ⊆ S' → y = ∑ ka ∈ S', jointE ee ka y := by
  have hall := span_isoOn E ee hee hcomm hdec Finset.univ y
  obtain ⟨N, f, g, hy⟩ := (Submodule.mem_span_set').1 hall
  have hg : ∀ j, ∃ ka : ι → Fin n → ℤ, ∀ i, (g j : V) ∈ isoSub (E i) (ka i) := by
    intro j
    obtain ⟨ka, hka⟩ := (g j).2
    exact ⟨ka, fun i => hka i (Finset.mem_univ i)⟩
  choose kx hkx using hg
  have key : ∀ (x : V) (ka : ι → Fin n → ℤ), (∀ i, x ∈ isoSub (E i) (ka i)) →
      ∀ ka' : ι → Fin n → ℤ, jointE ee ka' x = if ka' = ka then x else 0 := by
    intro x ka hx ka'
    unfold jointE
    have hL : ∀ L : List ι, (L.map fun i => ee i (ka' i)).prod x = if ∀ i ∈ L, ka' i = ka i then x else 0 := by
      intro L
      induction L with
      | nil => simp
      | cons a L ih =>
        rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih]
        by_cases hL : ∀ i ∈ L, ka' i = ka i
        · rw [if_pos hL]
          by_cases ha : ka' a = ka a
          · rw [ha, (hee a (ka a)).1 x (hx a), if_pos]
            intro i hi
            rcases List.mem_cons.1 hi with rfl | hi
            · exact ha
            · exact hL i hi
          · rw [(hee a (ka' a)).2 (ka a) (Ne.symm ha) x (hx a), if_neg]
            intro h
            exact ha (h a List.mem_cons_self)
        · rw [if_neg hL, map_zero, if_neg]
          intro h
          exact hL fun i hi => h i (List.mem_cons_of_mem _ hi)
    rw [hL]
    congr 1
    apply propext
    constructor
    · intro h
      funext i
      exact h i (Finset.mem_toList.2 (Finset.mem_univ i))
    · intro h i _
      rw [h]
  refine ⟨Finset.univ.image kx, fun S' hS' => ?_⟩
  rw [← hy]
  simp_rw [map_sum, map_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.smul_sum]
  congr 1
  rw [Finset.sum_congr rfl fun ka _ => key _ _ (hkx j) ka, Finset.sum_ite_eq']
  rw [if_pos (hS' (Finset.mem_image_of_mem kx (Finset.mem_univ j)))]

end Dec

end Formalism.MainNotions.LetterSubstitution

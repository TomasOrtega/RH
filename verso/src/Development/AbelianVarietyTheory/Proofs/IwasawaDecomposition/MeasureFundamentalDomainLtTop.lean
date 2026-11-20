import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffIntegrableContinuous
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfTwoMem
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BesselConvDefinite

/- English proof (translation)
Rewrite using `[GlobalTheory.BesselCompare.isAniso_iff]`. Introduce `v hv`. Assume the negation of the conclusion as `hne`. Establish `hc` using `D.sp.cm.cmUnram`. Use `hc.1` as an intermediate fact.

Take `⟨τ⟩ : Nonempty (D.host.E →+* ℂ)` from `inferInstance`. Break down `hd τ with h | h` into its components or cases. Use `(GlobalTheory.BaseChangeExistsCompare.sig_pos_iff A hs τ (hc.2.1 τ)).1 h v hne` as an intermediate fact. Simplify using `[hv] at this`. Use `(GlobalTheory.BaseChangeExistsCompare.sig_neg_iff A hs τ (hc.2.1 τ)).1 h v hne` as an intermediate fact.

Simplify using `[hv] at this`.
-/
theorem isAniso_of_isDefinite {D : D7} (A : HSp D) (hs : A.SigOK) (hd : A.IsDefinite) : IsAniso A := by
  rw [GlobalTheory.BesselCompare.isAniso_iff]
  intro v hv
  by_contra hne
  have hc := D.sp.cm.cmUnram
  have := hc.1
  obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  rcases hd τ with h | h
  · have := (GlobalTheory.BaseChangeExistsCompare.sig_pos_iff A hs τ (hc.2.1 τ)).1 h v hne
    simp [hv] at this
  · have := (GlobalTheory.BaseChangeExistsCompare.sig_neg_iff A hs τ (hc.2.1 τ)).1 h v hne
    simp [hv] at this

open Pointwise in

/- English proof (translation)
Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ` as an intermediate fact. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ` as an intermediate fact. Establish `hsub : F ⊆ ⋃ γ : Γ, ((γ • K) ∩ F)`. Introduce `g hg`. Take `⟨γ, hγ, k, hk, e⟩` from `hcov g`.

Conclude with `Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ), ⟨k, hk, e.symm⟩, hg⟩`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem measure_fundamentalDomain_lt_top {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] {K : Set G} (hK : IsCompact K)
    (hcov : ∀ g : G, ∃ γ ∈ Γ, ∃ k ∈ K, g = γ * k) (μ : Measure G) [μ.IsHaarMeasure] {F : Set G}
    (hF : IsFundamentalDomain Γ F μ) : μ F < ⊤ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ
  have hsub : F ⊆ ⋃ γ : Γ, ((γ • K) ∩ F) := by
    intro g hg
    obtain ⟨γ, hγ, k, hk, e⟩ := hcov g
    exact Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ), ⟨k, hk, e.symm⟩, hg⟩
  calc μ F ≤ μ (⋃ γ : Γ, ((γ • K) ∩ F)) := measure_mono hsub
    _ ≤ ∑' γ : Γ, μ ((γ • K) ∩ F) := measure_iUnion_le _
    _ = μ K := (hF.measure_eq_tsum K).symm
    _ < ⊤ := hK.measure_lt_top

section Conj

open GlobalTheory.BesselCompare

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

/- English proof (translation)
Rewrite using `[iA, frameMat_eq, eMat_mulVec]`.
-/
theorem iA_eq_sum (t : Fin A.rank → AE D) : iA ι t = ∑ l, t l • vecA B (ι (A.frame l)) := by
  rw [iA, frameMat_eq, eMat_mulVec]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[vecA]`.
-/
theorem vecA_add (x y : B.V) : vecA B (x + y) = vecA B x + vecA B y := by
  funext k; simp [vecA]

/- English proof (translation)
Rewrite using `[iA_eq_sum]`. Use function extensionality and compare the values at `k`. Establish `h : B.frame.repr (ι a) k = ∑ c, A.frame.repr a c * B.frame.repr (ι (A.frame c)) k` using `by conv_lhs => rw [← A.frame.sum_repr a]`. Simplify using `only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]`. Simplify using `only [vecA, h, map_sum, map_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`.
-/
theorem vecA_iota (a : A.V) : vecA B (ι a) = iA ι (vecA A a) := by
  rw [iA_eq_sum]
  funext k
  have h : B.frame.repr (ι a) k = ∑ c, A.frame.repr a c * B.frame.repr (ι (A.frame c)) k := by
    conv_lhs => rw [← A.frame.sum_repr a]
    simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
  simp only [vecA, h, map_sum, map_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/- English proof (translation)
The claim follows from `e.2 (co B w) (by funext i; rw [frameMat_eq, cT_mulVec]; exact hw _)`.
-/
theorem embRel_fix {g : GA D B} {h : GA D A} (e : EmbRel B A ι g h) {w : B.V} (hw : ∀ x, B.hD w (ι x) = 0) :
    (mt B g).mulVec (vecA B w) = vecA B w :=
  e.2 (co B w) (by funext i; rw [frameMat_eq, cT_mulVec]; exact hw _)

/- English proof (translation)
Rewrite using `[iA, iA, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`. Conclude with `congrArg (fun M => Matrix.mulVec M t) e.1`.
-/
theorem embRel_iA {g : GA D B} {h : GA D A} (e : EmbRel B A ι g h) (t : Fin A.rank → AE D) :
    (mt B g).mulVec (iA ι t) = iA ι ((mt A h).mulVec t) := by
  rw [iA, iA, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  exact congrArg (fun M => Matrix.mulVec M t) e.1

/- English proof (translation)
Establish `hinv : ∀ {x y}, (mt B g).mulVec x = y → (mt B g⁻¹).mulVec y = x` using `fun hxy => by`. Rewrite using `[← hxy, mulVec_inv_cancel]`. Establish `he : ∀ l, (mt B g).mulVec (vecA B (d.e l)) = vecA B (d.e l)` using `fun l => embRel_fix e (d.eA l)`. Establish `hsum : ∀ c : Fin d.ρ → AE D, (mt B g).mulVec (∑ l, c l • vecA B (d.e l)) = ∑ l, c l • vecA B (d.e l)` using `fun c => by simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, he]`. Use `⟨fun i => ?_, fun x hx => ?_⟩` and prove the remaining obligations.

Take `⟨c, hc, h1⟩` from `hn.1 i`. Use `⟨c, hc, ?_⟩` and prove the remaining obligations. Unfold `actV at h1 ⊢`. Rewrite using `[mulVec_mul, mulVec_mul, hinv (he i), h1, Matrix.mulVec_add, he, hsum]`. Take `⟨a, ha⟩` from `exists_rep A (B.hT x ∘ₗ ι)`.

Establish `hw : ∀ y, B.hD (x - ι a) (ι y) = 0` using `fun y => hD_swap_zero (by`. Unfold `HSpace.hD`. Rewrite using `[map_sub, LinearMap.sub_apply, d.isom, ha]`. Conclude with `sub_self _)`. Establish `hιe : ∀ y i, B.hD (ι y) (d.e i) = 0` using `fun y i => hD_swap_zero (d.eA i y)`.

Establish `hwe : ∀ i, B.hD (x - ι a) (d.e i) = 0` using `fun i => by`. Establish `h1` using `hx i`. Establish `h2` using `hιe a i`. Unfold `HSpace.hD at h1 h2 ⊢`. Rewrite using `[map_sub, h1, h2, sub_zero]`.

Take `⟨c₀, hc₀⟩` from `hn.2 _ hwe`. Use `choose c hc using fun k => hn.2 _ (hιe (A.frame k))`. Unfold `actV at hc₀ hc ⊢`. Use `set t := (mt A h⁻¹).mulVec (vecA A a) with ht`. Establish `hx1 : vecA B x = vecA B (x - ι a) + iA ι (vecA A a)` using `by rw [← vecA_iota, ← vecA_add, sub_add_cancel]`.

Establish `hg : (mt B g).mulVec (vecA B (x - ι a) + iA ι t) = vecA B x`. Rewrite using `[Matrix.mulVec_add, embRel_fix e hw, embRel_iA e, ht, mulVec_cancel_inv, hx1]`. Establish `hn1 : (mt B n).mulVec (vecA B (x - ι a) + iA ι t) = (vecA B (x - ι a) + iA ι t) + ∑ l, (c₀ l + ∑ k, t k * c k l) • vecA B (d.e l)`. Rewrite using `[Matrix.mulVec_add, hc₀, iA_eq_sum]`. Simplify using `only [Matrix.mulVec_sum, Matrix.mulVec_smul, hc, smul_add, add_smul, Finset.sum_add_distrib, Finset.smul_sum, Finset.sum_smul, mul_smul]`.

Rewrite using `[Finset.sum_comm (f := fun k l => t k • c k l • vecA B (d.e l))]`. Normalize the expressions using the abelian group laws. Conclude with `⟨_, by rw [mulVec_mul, mulVec_mul, hinv hg, hn1, Matrix.mulVec_add, hg, hsum]⟩`.
-/
theorem conj_mem_NSet (d : BesselDatum A B ι) {g : GA D B} {h : GA D A} (e : EmbRel B A ι g h) {n : GA D B}
    (hn : n ∈ d.NSet) : g * n * g⁻¹ ∈ d.NSet := by
  have hinv : ∀ {x y}, (mt B g).mulVec x = y → (mt B g⁻¹).mulVec y = x := fun hxy => by
    rw [← hxy, mulVec_inv_cancel]
  have he : ∀ l, (mt B g).mulVec (vecA B (d.e l)) = vecA B (d.e l) := fun l => embRel_fix e (d.eA l)
  have hsum : ∀ c : Fin d.ρ → AE D, (mt B g).mulVec (∑ l, c l • vecA B (d.e l)) = ∑ l, c l • vecA B (d.e l) :=
    fun c => by simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, he]
  refine ⟨fun i => ?_, fun x hx => ?_⟩
  · obtain ⟨c, hc, h1⟩ := hn.1 i
    refine ⟨c, hc, ?_⟩
    unfold actV at h1 ⊢
    rw [mulVec_mul, mulVec_mul, hinv (he i), h1, Matrix.mulVec_add, he, hsum]
  · obtain ⟨a, ha⟩ := exists_rep A (B.hT x ∘ₗ ι)
    have hw : ∀ y, B.hD (x - ι a) (ι y) = 0 := fun y => hD_swap_zero (by
      unfold HSpace.hD
      rw [map_sub, LinearMap.sub_apply, d.isom, ha]; exact sub_self _)
    have hιe : ∀ y i, B.hD (ι y) (d.e i) = 0 := fun y i => hD_swap_zero (d.eA i y)
    have hwe : ∀ i, B.hD (x - ι a) (d.e i) = 0 := fun i => by
      have h1 := hx i
      have h2 := hιe a i
      unfold HSpace.hD at h1 h2 ⊢
      rw [map_sub, h1, h2, sub_zero]
    obtain ⟨c₀, hc₀⟩ := hn.2 _ hwe
    choose c hc using fun k => hn.2 _ (hιe (A.frame k))
    unfold actV at hc₀ hc ⊢
    set t := (mt A h⁻¹).mulVec (vecA A a) with ht
    have hx1 : vecA B x = vecA B (x - ι a) + iA ι (vecA A a) := by rw [← vecA_iota, ← vecA_add, sub_add_cancel]
    have hg : (mt B g).mulVec (vecA B (x - ι a) + iA ι t) = vecA B x := by
      rw [Matrix.mulVec_add, embRel_fix e hw, embRel_iA e, ht, mulVec_cancel_inv, hx1]
    have hn1 : (mt B n).mulVec (vecA B (x - ι a) + iA ι t) =
        (vecA B (x - ι a) + iA ι t) + ∑ l, (c₀ l + ∑ k, t k * c k l) • vecA B (d.e l) := by
      rw [Matrix.mulVec_add, hc₀, iA_eq_sum]
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, hc, smul_add, add_smul, Finset.sum_add_distrib,
        Finset.smul_sum, Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm (f := fun k l => t k • c k l • vecA B (d.e l))]
      abel
    exact ⟨_, by rw [mulVec_mul, mulVec_mul, hinv hg, hn1, Matrix.mulVec_add, hg, hsum]⟩

/- English proof (translation)
The claim follows from `(Subgroup.closure_le (d.N.comap (MulAut.conj g).toMonoidHom)).2 (fun _ hm => Subgroup.subset_closure (conj_mem_NSet d e hm)) hn`.
-/
theorem conj_mem_N (d : BesselDatum A B ι) {g : GA D B} {h : GA D A} (e : EmbRel B A ι g h) {n : GA D B}
    (hn : n ∈ d.N) : g * n * g⁻¹ ∈ d.N :=
  (Subgroup.closure_le (d.N.comap (MulAut.conj g).toMonoidHom)).2
    (fun _ hm => Subgroup.subset_closure (conj_mem_NSet d e hm)) hn

end Conj

/- English proof (translation)
Introduce `D A B ι d ψ hψ hs hd μ 𝓕 hμ ν 𝓝 hν s hs' φ F hφ hF g`. Take `⟨K, hK, hcov⟩` from `GlobalTheory.Mem.AnisoQuotient.exists_compact D A (isAniso_of_isDefinite A hs hd)`. Take `⟨s₀, hcont, hrel, hQ⟩` from `GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι d.isom`. Take `rfl : s = s₀` from `funext fun h => (hrel h _).1 (hs' h)`. Take `⟨_, _, _, _, _, _, _⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A`.

Take `⟨_, _, _, _, _, _, _⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B`. Use `hμ.1.1` as an intermediate fact. Establish `hfin : μ 𝓕 < ⊤` using `measure_fundamentalDomain_lt_top (GQ A) hK hcov μ hμ.2`. Establish `hFc : Continuous (rTr B g F)` using `hF.cont.comp (continuous_id.mul continuous_const)`. Establish `hFl : ∀ γ ∈ GQ B, ∀ x, rTr B g F (γ * x) = rTr B g F x` using `fun γ hγ x => by`.

Simplify using `only [rTr, mul_assoc]`. Conclude with `hF.left γ hγ _`. Take `⟨-, hc, hb⟩` from `GlobalTheory.RootExch.CoefInt.coeff_integrable_continuous D A B ι d ψ hψ ν 𝓝 hν (rTr B g F) hFc hFl`. Take `⟨M, hM⟩` from `hb (s₀ '' K) (hK.image hcont)`. Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn hφ.cont.continuousOn`.

Establish `hcontI : Continuous fun h => φ h * d.coeff ψ ν 𝓝 (rTr B g F) (s₀ h)` using `hφ.cont.mul (hc.comp hcont)`. Use `Measure.integrableOn_of_bounded (M := C * M) hfin.ne hcontI.aestronglyMeasurable (Filter.Eventually.of_forall fun h => ?_)` and prove the remaining obligations. Take `⟨γ, hγ, k, hk, rfl⟩` from `hcov h`. Rewrite using `[norm_mul, hφ.left γ hγ]`. Use `mul_le_mul (hC k hk) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hC k hk))` and prove the remaining obligations.

Establish `h1 : ν 𝓝 < ⊤` using `by rw [hν.2.2]; exact ENNReal.one_lt_top`. Establish `h2` using `norm_setIntegral_le_of_norm_le_const (μ := ν) (s := 𝓝) (C := M) (f := fun n : d.N => rTr B g F ((n : GA D B) * s₀ (γ * k)) * star (d.psiN ψ (n : GA D B))) h1 (fun n _ => by`. Establish `hn : s₀ γ⁻¹ * n * (s₀ γ⁻¹)⁻¹ ∈ d.N` using `conj_mem_N d ((hrel _ _).2 rfl) n.2`. Establish `e : (n : GA D B) * s₀ (γ * k) = s₀ γ * (s₀ γ⁻¹ * n * (s₀ γ⁻¹)⁻¹ * s₀ k)`. Simplify using `only [map_mul, map_inv, inv_inv, mul_assoc, mul_inv_cancel_left]`.

Rewrite using `[norm_mul, norm_star, e, hFl _ (hQ γ hγ), BesselDatum.psiN, hψ.2.1, mul_one]`. Conclude with `hM _ hn _ ⟨k, hk, rfl⟩)`. Rewrite `h2` using `[Measure.real, hν.2.2, ENNReal.toReal_one, mul_one]`. Then use the resulting hypothesis.
-/
theorem convergesDef : ∀ D : D7, ConvergesDef D := by
  intro D A B ι d ψ hψ hs hd μ 𝓕 hμ ν 𝓝 hν s hs' φ F hφ hF g
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact D A (isAniso_of_isDefinite A hs hd)
  obtain ⟨s₀, hcont, hrel, hQ⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι d.isom
  obtain rfl : s = s₀ := funext fun h => (hrel h _).1 (hs' h)
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have := hμ.1.1
  have hfin : μ 𝓕 < ⊤ := measure_fundamentalDomain_lt_top (GQ A) hK hcov μ hμ.2
  have hFc : Continuous (rTr B g F) := hF.cont.comp (continuous_id.mul continuous_const)
  have hFl : ∀ γ ∈ GQ B, ∀ x, rTr B g F (γ * x) = rTr B g F x := fun γ hγ x => by
    simp only [rTr, mul_assoc]; exact hF.left γ hγ _
  obtain ⟨-, hc, hb⟩ := GlobalTheory.RootExch.CoefInt.coeff_integrable_continuous D A B ι d ψ hψ ν 𝓝 hν (rTr B g F) hFc hFl
  obtain ⟨M, hM⟩ := hb (s₀ '' K) (hK.image hcont)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hφ.cont.continuousOn
  have hcontI : Continuous fun h => φ h * d.coeff ψ ν 𝓝 (rTr B g F) (s₀ h) := hφ.cont.mul (hc.comp hcont)
  refine Measure.integrableOn_of_bounded (M := C * M) hfin.ne hcontI.aestronglyMeasurable
    (Filter.Eventually.of_forall fun h => ?_)
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov h
  rw [norm_mul, hφ.left γ hγ]
  refine mul_le_mul (hC k hk) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hC k hk))
  have h1 : ν 𝓝 < ⊤ := by rw [hν.2.2]; exact ENNReal.one_lt_top
  have h2 := norm_setIntegral_le_of_norm_le_const (μ := ν) (s := 𝓝) (C := M)
    (f := fun n : d.N => rTr B g F ((n : GA D B) * s₀ (γ * k)) * star (d.psiN ψ (n : GA D B))) h1 (fun n _ => by
      have hn : s₀ γ⁻¹ * n * (s₀ γ⁻¹)⁻¹ ∈ d.N := conj_mem_N d ((hrel _ _).2 rfl) n.2
      have e : (n : GA D B) * s₀ (γ * k) = s₀ γ * (s₀ γ⁻¹ * n * (s₀ γ⁻¹)⁻¹ * s₀ k) := by
        simp only [map_mul, map_inv, inv_inv, mul_assoc, mul_inv_cancel_left]
      rw [norm_mul, norm_star, e, hFl _ (hQ γ hγ), BesselDatum.psiN, hψ.2.1, mul_one]
      exact hM _ hn _ ⟨k, hk, rfl⟩)
  rwa [Measure.real, hν.2.2, ENNReal.toReal_one, mul_one] at h2

end GlobalTheory.BesselConvDefinite

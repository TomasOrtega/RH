import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemberDatumOfFlagTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NEqAndIsClosed
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.BesselCoeffIndep

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G)
    [Countable Γ]

/- English proof (translation)
Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ` as an intermediate fact. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ'` as an intermediate fact. Establish `e : μ' = (μ'.haarScalarFactor μ : ℝ≥0∞) • μ` using `Measure.isMulLeftInvariant_eq_smul μ' μ`. Establish `h2 : IsFundamentalDomain Γ 𝓕 μ'` using `h.mono (by rw [e]; exact Measure.smul_absolutelyContinuous)`. Establish `h3 : μ' 𝓕 = 1` using `(h2.measure_eq h').trans h1'`.

Rewrite `h3` using `[e, Measure.smul_apply, h1, smul_eq_mul, mul_one]`. Rewrite using `[e, h3, one_smul]`.
-/
theorem haar_eq_of_covolume_one (μ μ' : Measure G) [μ.IsHaarMeasure] [μ'.IsHaarMeasure] {𝓕 𝓕' : Set G}
    (h : IsFundamentalDomain Γ 𝓕 μ) (h' : IsFundamentalDomain Γ 𝓕' μ') (h1 : μ 𝓕 = 1) (h1' : μ' 𝓕' = 1) :
    μ' = μ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ'
  have e : μ' = (μ'.haarScalarFactor μ : ℝ≥0∞) • μ := Measure.isMulLeftInvariant_eq_smul μ' μ
  have h2 : IsFundamentalDomain Γ 𝓕 μ' := h.mono (by rw [e]; exact Measure.smul_absolutelyContinuous)
  have h3 : μ' 𝓕 = 1 := (h2.measure_eq h').trans h1'
  rw [e, Measure.smul_apply, h1, smul_eq_mul, mul_one] at h3
  rw [e, h3, one_smul]

/- English proof (translation)
Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ` as an intermediate fact. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ` as an intermediate fact. Establish `e : μ.map (· * g) = ((μ.map (· * g)).haarScalarFactor μ : ℝ≥0∞) • μ` using `Measure.isMulLeftInvariant_eq_smul _ μ`. Establish `h' : IsFundamentalDomain Γ ((· * g) ⁻¹' 𝓕) μ` using `h.preimage_of_equiv (f := (· * g)) ⟨measurable_mul_const g, by rw [e]; exact Measure.smul_absolutelyContinuous⟩ Function.bijective_id fun γ x => mul_assoc _ _ _`. Establish `h1 : μ.map (· * g) 𝓕 = μ 𝓕` using `((MeasurableEquiv.mulRight g).map_apply 𝓕).trans (h'.measure_eq h)`.

Rewrite `h1` using `[e, Measure.smul_apply, smul_eq_mul]`. Establish `h2` using `(ENNReal.mul_left_inj (h.measure_ne_zero (NeZero.ne μ)) hfin).1 (h1.trans (one_mul _).symm)`. Rewrite `e` using `[h2, one_smul]`. Establish `hp : MeasurePreserving (· * g) μ μ` using `⟨measurable_mul_const g, e⟩`. Rewrite using `[← hp.setIntegral_preimage_emb (MeasurableEquiv.mulRight g).measurableEmbedding f 𝓕]`.

Conclude with `h.setIntegral_eq h' (f := fun x => f (x * g)) fun γ x => by show f ((γ : G) * x * g) = _`. Rewrite using `[mul_assoc, hf _ γ.2]`.
-/
theorem setIntegral_mul_right (μ : Measure G) [μ.IsHaarMeasure] {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    (hfin : μ 𝓕 ≠ ⊤) (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (g : G) :
    ∫ x in 𝓕, f (x * g) ∂μ = ∫ x in 𝓕, f x ∂μ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ
  have e : μ.map (· * g) = ((μ.map (· * g)).haarScalarFactor μ : ℝ≥0∞) • μ :=
    Measure.isMulLeftInvariant_eq_smul _ μ
  have h' : IsFundamentalDomain Γ ((· * g) ⁻¹' 𝓕) μ :=
    h.preimage_of_equiv (f := (· * g)) ⟨measurable_mul_const g, by rw [e]; exact Measure.smul_absolutelyContinuous⟩
      Function.bijective_id fun γ x => mul_assoc _ _ _
  have h1 : μ.map (· * g) 𝓕 = μ 𝓕 :=
    ((MeasurableEquiv.mulRight g).map_apply 𝓕).trans (h'.measure_eq h)
  rw [e, Measure.smul_apply, smul_eq_mul] at h1
  have h2 := (ENNReal.mul_left_inj (h.measure_ne_zero (NeZero.ne μ)) hfin).1 (h1.trans (one_mul _).symm)
  rw [h2, one_smul] at e
  have hp : MeasurePreserving (· * g) μ μ := ⟨measurable_mul_const g, e⟩
  rw [← hp.setIntegral_preimage_emb (MeasurableEquiv.mulRight g).measurableEmbedding f 𝓕]
  exact h.setIntegral_eq h' (f := fun x => f (x * g)) fun γ x => by
    show f ((γ : G) * x * g) = _
    rw [mul_assoc, hf _ γ.2]

end General

section Character

open GlobalTheory.BesselCompare (hA_add hA_smul hA_sum hA_vec hA_coeff hD_swap_zero co co_surj)

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

/- English proof (translation)
Take `⟨c, hc, e⟩` from `hn.1 l`. Rewrite using `[e, hA_add, hA_coeff B d.e d.f d.ef, hc i h, add_zero, hA_vec, d.ef]`. Use `split_ifs`. Conclude with `map_one _`. Conclude with `map_zero _`.
-/
theorem hA_act_e (d : BesselDatum A B ι) {n : GA D B} (hn : n ∈ d.NSet) {l i : Fin d.ρ} (h : l ≤ i) :
    hA B (actV B n (d.e l)) (vecA B (d.f i)) = if l = i then 1 else 0 := by
  obtain ⟨c, hc, e⟩ := hn.1 l
  rw [e, hA_add, hA_coeff B d.e d.f d.ef, hc i h, add_zero, hA_vec, d.ef]
  split_ifs
  · exact map_one _
  · exact map_zero _

/- English proof (translation)
Unfold `BesselDatum.aux`. Distinguish the cases in `hi : i.1 + 1 = d.ρ`. Establish `: i.succ = Fin.last d.ρ` using `Fin.ext hi`. Rewrite using `[this, Fin.snoc_last]`. Take `⟨c, e⟩` from `hn.2 d.z fun j => hD_swap_zero (d.ez j)`.

Conclude with `⟨hD_swap_zero (d.fz i), c, fun l hl => absurd (show i.1 < l.1 from hl) (by have := l.2; omega), e⟩`. Establish `hlt : i.1 + 1 < d.ρ` using `by have := i.2; omega`. Establish `: i.succ = Fin.castSucc (⟨i.1 + 1, hlt⟩ : Fin d.ρ)` using `Fin.ext rfl`. Rewrite using `[this, Fin.snoc_castSucc]`. Take `⟨c, hc, e⟩` from `hn.1 ⟨i.1 + 1, hlt⟩`.

Use `⟨?_, c, fun l hl => hc l (show i.1 + 1 ≤ l.1 from hl), e⟩` and prove the remaining obligations. Rewrite using `[d.ef, if_neg (fun h => by have : i.1 + 1 = i.1 := congrArg Fin.val h; omega)]`.
-/
theorem actE_eq_of_conj_related (d : BesselDatum A B ι) {n : GA D B} (hn : n ∈ d.NSet) (i : Fin d.ρ) :
    B.hD (d.aux i.succ) (d.f i) = 0 ∧ ∃ c : Fin d.ρ → AE D, (∀ l, i < l → c l = 0) ∧
      actV B n (d.aux i.succ) = vecA B (d.aux i.succ) + ∑ l, c l • vecA B (d.e l) := by
  unfold BesselDatum.aux
  by_cases hi : i.1 + 1 = d.ρ
  · have : i.succ = Fin.last d.ρ := Fin.ext hi
    rw [this, Fin.snoc_last]
    obtain ⟨c, e⟩ := hn.2 d.z fun j => hD_swap_zero (d.ez j)
    exact ⟨hD_swap_zero (d.fz i), c, fun l hl => absurd (show i.1 < l.1 from hl) (by have := l.2; omega), e⟩
  · have hlt : i.1 + 1 < d.ρ := by have := i.2; omega
    have : i.succ = Fin.castSucc (⟨i.1 + 1, hlt⟩ : Fin d.ρ) := Fin.ext rfl
    rw [this, Fin.snoc_castSucc]
    obtain ⟨c, hc, e⟩ := hn.1 ⟨i.1 + 1, hlt⟩
    refine ⟨?_, c, fun l hl => hc l (show i.1 + 1 ≤ l.1 from hl), e⟩
    rw [d.ef, if_neg (fun h => by have : i.1 + 1 = i.1 := congrArg Fin.val h; omega)]

/- English proof (translation)
Unfold `BesselDatum.simpleSum`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Take `⟨h0, c, hc, e⟩` from `actE_eq_of_conj_related d hn' i`. Establish `e1 : actV B (n * n') (d.aux i.succ) = actV B n (d.aux i.succ) + ∑ l, c l • actV B n (d.e l)`.

Establish `: actV B (n * n') (d.aux i.succ) = (mt B n).mulVec (actV B n' (d.aux i.succ))` using `mulVec_mul _ _ _`. Rewrite using `[this, e, Matrix.mulVec_add, Matrix.mulVec_sum]`. Simplify using `only [Matrix.mulVec_smul]`. Both sides reduce to the same expression. Rewrite using `[e1, e, hA_add, hA_add, hA_coeff B d.e d.f d.ef, hA_vec, h0, RingHom.map_zero, zero_add, hA_sum, Finset.sum_eq_single i]`.

Rewrite using `[hA_smul, hA_act_e d hn le_rfl, if_pos rfl, mul_one]`. Introduce `l _ hl`. Rewrite using `[hA_smul]`. Break down `lt_or_ge i l with h | h` into its components or cases. Rewrite using `[hc l h, zero_mul]`.

Rewrite using `[hA_act_e d hn h, if_neg hl, mul_zero]`. Conclude with `fun h => absurd (Finset.mem_univ _) h`.
-/
theorem simpleSum_mul (d : BesselDatum A B ι) {n n' : GA D B} (hn : n ∈ d.NSet) (hn' : n' ∈ d.NSet) :
    d.simpleSum (n * n') = d.simpleSum n + d.simpleSum n' := by
  unfold BesselDatum.simpleSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨h0, c, hc, e⟩ := actE_eq_of_conj_related d hn' i
  have e1 : actV B (n * n') (d.aux i.succ) = actV B n (d.aux i.succ) + ∑ l, c l • actV B n (d.e l) := by
    have : actV B (n * n') (d.aux i.succ) = (mt B n).mulVec (actV B n' (d.aux i.succ)) := mulVec_mul _ _ _
    rw [this, e, Matrix.mulVec_add, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
    rfl
  rw [e1, e, hA_add, hA_add, hA_coeff B d.e d.f d.ef, hA_vec, h0, RingHom.map_zero, zero_add, hA_sum,
    Finset.sum_eq_single i]
  · rw [hA_smul, hA_act_e d hn le_rfl, if_pos rfl, mul_one]
  · intro l _ hl
    rw [hA_smul]
    rcases lt_or_ge i l with h | h
    · rw [hc l h, zero_mul]
    · rw [hA_act_e d hn h, if_neg hl, mul_zero]
  · exact fun h => absurd (Finset.mem_univ _) h

/- English proof (translation)
Unfold `BesselDatum.psiN`. Rewrite using `[simpleSum_mul d hn hn', mul_add, LinearMap.map_add, AddChar.map_add_eq_mul]`.
-/
theorem psiN_mul (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) {n n' : GA D B} (hn : n ∈ d.NSet)
    (hn' : n' ∈ d.NSet) : d.psiN ψ (n * n') = d.psiN ψ n * d.psiN ψ n' := by
  unfold BesselDatum.psiN
  rw [simpleSum_mul d hn hn', mul_add, LinearMap.map_add, AddChar.map_add_eq_mul]

/- English proof (translation)
Take `⟨g, -, hg⟩` from `Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hn)`. Establish `h1 : mt B n = (g : Matrix _ _ D.host.E).map (incA D)` using `(congrArg Units.val hg).symm`. Establish `h2 : ∀ v, ∃ w, actV B n v = vecA B w` using `fun v => by`. Take `⟨w, hw⟩` from `co_surj B ((g : Matrix _ _ D.host.E).mulVec (co B v))`. Use `⟨w, funext fun k => ?_⟩` and prove the remaining obligations.

Establish `: vecA B w k = incA D (co B w k)` using `rfl`. Rewrite using `[this, hw, RingHom.map_mulVec, actV, h1]`. Both sides reduce to the same expression. Use `choose w hw using h2`. Establish `h3 : ∀ e : D.host.E, Algebra.trace (AF D.host.F) (AE D) (incA D e) = algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e)` using `fun e => by show Algebra.trace (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) (1 ⊗ₜ e) = _`.

Rewrite using `[Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]`. Unfold `BesselDatum.psiN BesselDatum.simpleSum`. Simplify using `only [hw, hA_vec]`. Rewrite using `[← map_sum (incA D), ← RingHom.map_mul, h3, hψ.2.2.1]`.
-/
theorem psiN_rat (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) {n : GA D B}
    (hn : n ∈ GQ B) : d.psiN ψ n = 1 := by
  obtain ⟨g, -, hg⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hn)
  have h1 : mt B n = (g : Matrix _ _ D.host.E).map (incA D) := (congrArg Units.val hg).symm
  have h2 : ∀ v, ∃ w, actV B n v = vecA B w := fun v => by
    obtain ⟨w, hw⟩ := co_surj B ((g : Matrix _ _ D.host.E).mulVec (co B v))
    refine ⟨w, funext fun k => ?_⟩
    have : vecA B w k = incA D (co B w k) := rfl
    rw [this, hw, RingHom.map_mulVec, actV, h1]
    rfl
  choose w hw using h2
  have h3 : ∀ e : D.host.E, Algebra.trace (AF D.host.F) (AE D) (incA D e) =
      algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e) := fun e => by
    show Algebra.trace (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) (1 ⊗ₜ e) = _
    rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
  unfold BesselDatum.psiN BesselDatum.simpleSum
  simp only [hw, hA_vec]
  rw [← map_sum (incA D), ← RingHom.map_mul, h3, hψ.2.2.1]

end Character

/- English proof (translation)
Introduce `D A B ι d ψ hψ F hF ν 𝓝 ⟨hν, h𝓝, h1⟩`. Take `⟨i1, i2, i3, i4, i5, -, i7⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B`. Establish `hcl` using `(GlobalTheory.BesselClosed.N_eq_and_isClosed D A B ι d).2`. Establish `: LocallyCompactSpace d.N` using `hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Establish `: SecondCountableTopology d.N` using `TopologicalSpace.Subtype.secondCountableTopology _`.

Establish `: BorelSpace d.N` using `Subtype.borelSpace _`. Establish `: Countable d.NQ` using `Function.Injective.countable (f := fun γ : d.NQ => (⟨γ.1.1, γ.2⟩ : GQ B)) fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun t : GQ B => (t : GA D B)) hab))`. Establish `hS : ∀ n ∈ d.N, n ∈ d.NSet` using `fun n hn => (GlobalTheory.BesselClosed.N_eq_and_isClosed D A B ι d).1 ▸ SetLike.mem_coe.2 hn`. Establish `hmul : ∀ n ∈ d.N, ∀ n' ∈ d.N, d.psiN ψ (n * n') = d.psiN ψ n * d.psiN ψ n'` using `fun n hn n' hn' => psiN_mul d ψ (hS n hn) (hS n' hn')`. Establish `hrat : ∀ n ∈ d.N, n ∈ GQ B → d.psiN ψ n = 1` using `fun n _ hn' => psiN_rat d ψ hψ.1 hn'`.

Establish `hinv : ∀ g, ∀ γ ∈ d.NQ, ∀ x : d.N, F (((γ * x : d.N) : GA D B) * g) * star (d.psiN ψ ((γ * x : d.N) : GA D B)) = F ((x : GA D B) * g) * star (d.psiN ψ (x : GA D B))` using `fun g γ hγ x => by`. Rewrite using `[Subgroup.coe_mul, mul_assoc, hF (γ : GA D B) hγ, hmul _ γ.2 _ x.2, hrat _ γ.2 hγ, one_mul]`. Use `⟨fun ν' 𝓝' ⟨hν', h𝓝', h1'⟩ => ?_, fun n hn g => ?_⟩` and prove the remaining obligations. Take `rfl` from `haar_eq_of_covolume_one d.NQ ν ν' h𝓝 h𝓝' h1 h1'`. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup d.NQ` as an intermediate fact.

Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup d.NQ ν'` as an intermediate fact. Use function extensionality and compare the values at `g`. Conclude with `h𝓝'.setIntegral_eq h𝓝 (f := fun x : d.N => F ((x : GA D B) * g) * star (d.psiN ψ (x : GA D B))) fun γ x => hinv g γ γ.2 x`. Establish `key` using `setIntegral_mul_right d.NQ ν h𝓝 (by rw [h1]; exact ENNReal.one_ne_top) (fun x : d.N => F ((x : GA D B) * g) * star (d.psiN ψ (x : GA D B))) (hinv g) ⟨n, hn⟩`. Unfold `BesselDatum.coeff`.

Rewrite using `[← key, ← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Establish `hu : d.psiN ψ n * star (d.psiN ψ n) = 1`. Establish `: ‖d.psiN ψ n‖ = 1` using `hψ.1.2.1 _`. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, this]`.

Simplify using the standard rewrite rules. Simplify using `only [Subgroup.coe_mul]`. Rewrite using `[hmul _ x.2 _ hn, star_mul', mul_assoc (x : GA D B)]`. Take the linear combination `(-(F (x * (n * g)) * star (d.psiN ψ x))) * hu`.
-/
theorem coeff_indep_and_equivariant : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ F : GA D B → ℂ, (∀ γ ∈ GQ B, ∀ g, F (γ * g) = F g) → ∀ ν 𝓝, d.IsUnitPair ν 𝓝 → (∀ ν' 𝓝', d.IsUnitPair ν' 𝓝' → d.coeff ψ ν' 𝓝' F = d.coeff ψ ν 𝓝 F) ∧ ∀ n ∈ d.N, ∀ g, d.coeff ψ ν 𝓝 F (n * g) = d.psiN ψ n * d.coeff ψ ν 𝓝 F g := by
  intro D A B ι d ψ hψ F hF ν 𝓝 ⟨hν, h𝓝, h1⟩
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have hcl := (GlobalTheory.BesselClosed.N_eq_and_isClosed D A B ι d).2
  have : LocallyCompactSpace d.N := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology d.N := TopologicalSpace.Subtype.secondCountableTopology _
  have : BorelSpace d.N := Subtype.borelSpace _
  have : Countable d.NQ :=
    Function.Injective.countable (f := fun γ : d.NQ => (⟨γ.1.1, γ.2⟩ : GQ B)) fun a b hab =>
      Subtype.ext (Subtype.ext (congrArg (fun t : GQ B => (t : GA D B)) hab))
  have hS : ∀ n ∈ d.N, n ∈ d.NSet := fun n hn => (GlobalTheory.BesselClosed.N_eq_and_isClosed D A B ι d).1 ▸ SetLike.mem_coe.2 hn
  have hmul : ∀ n ∈ d.N, ∀ n' ∈ d.N, d.psiN ψ (n * n') = d.psiN ψ n * d.psiN ψ n' := fun n hn n' hn' =>
    psiN_mul d ψ (hS n hn) (hS n' hn')
  have hrat : ∀ n ∈ d.N, n ∈ GQ B → d.psiN ψ n = 1 := fun n _ hn' => psiN_rat d ψ hψ.1 hn'
  have hinv : ∀ g, ∀ γ ∈ d.NQ, ∀ x : d.N,
      F (((γ * x : d.N) : GA D B) * g) * star (d.psiN ψ ((γ * x : d.N) : GA D B)) =
        F ((x : GA D B) * g) * star (d.psiN ψ (x : GA D B)) := fun g γ hγ x => by
    rw [Subgroup.coe_mul, mul_assoc, hF (γ : GA D B) hγ, hmul _ γ.2 _ x.2, hrat _ γ.2 hγ, one_mul]
  refine ⟨fun ν' 𝓝' ⟨hν', h𝓝', h1'⟩ => ?_, fun n hn g => ?_⟩
  · obtain rfl := haar_eq_of_covolume_one d.NQ ν ν' h𝓝 h𝓝' h1 h1'
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup d.NQ
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup d.NQ ν'
    funext g
    exact h𝓝'.setIntegral_eq h𝓝 (f := fun x : d.N => F ((x : GA D B) * g) * star (d.psiN ψ (x : GA D B)))
      fun γ x => hinv g γ γ.2 x
  · have key := setIntegral_mul_right d.NQ ν h𝓝 (by rw [h1]; exact ENNReal.one_ne_top)
      (fun x : d.N => F ((x : GA D B) * g) * star (d.psiN ψ (x : GA D B))) (hinv g) ⟨n, hn⟩
    unfold BesselDatum.coeff
    rw [← key, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hu : d.psiN ψ n * star (d.psiN ψ n) = 1 := by
      have : ‖d.psiN ψ n‖ = 1 := hψ.1.2.1 _
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, this]; simp
    simp only [Subgroup.coe_mul]
    rw [hmul _ x.2 _ hn, star_mul', mul_assoc (x : GA D B)]
    linear_combination (-(F (x * (n * g)) * star (d.psiN ψ x))) * hu

end GlobalTheory.Mem.BesselCoeffIndep

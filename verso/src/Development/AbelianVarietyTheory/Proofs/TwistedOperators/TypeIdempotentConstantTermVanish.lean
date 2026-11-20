import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumRepSubgroupEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemStdMaxParabolicOfBlockParabolicLeConjStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StdMaxParabolicRadicalLeBlockUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionMaxCompactInterConjRadicalContainsConjStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompactOpenTypeIdempotentUnipotentEqZeroStatement

open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

noncomputable section

namespace GlobalTheory.TypeConstTerm

/- English proof (translation)
Introduce `k _ _ _ _ r P N hPN`. Take `⟨s, d, hd, g, -, rfl⟩` from `hPN`. Use `haveI : T2Space k := by`. Use `letI := IsTopologicalAddGroup.rightUniformSpace k`. Use `haveI := isUniformAddGroup_of_addCommGroup (G := k)`.

Use `infer_instance`. Establish `hU : IsClosed (unipRad k (stdBlocks d hd) : Set (GL (Fin r) k))`. Establish `: (unipRad k (stdBlocks d hd) : Set (GL (Fin r) k)) = (⋂ i, ⋂ j, ⋂ (_ : blk (stdBlocks d hd) j < blk (stdBlocks d hd) i), {x : GL (Fin r) k | (x : Matrix (Fin r) (Fin r) k) i j = 0}) ∩ ⋂ c, ⋂ i, ⋂ j, {x : GL (Fin r) k | (x : Matrix (Fin r) (Fin r) k) (stdBlocks d hd ⟨c, i⟩) (stdB …`. Use extensionality with `x`. Simplify using `only [SetLike.mem_coe, mem_unipRad, mem_parab, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]`.

Rewrite using `[this]`. Use `IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq ?_ continuous_const) (isClosed_iInter fun c => isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq ?_ continuous_const)` and prove the remaining obligations. Conclude with `Units.continuous_val.matrix_elem _ _`. Conclude with `Units.continuous_val.matrix_elem _ _`. Establish `: (conjBy g (unipRad k (stdBlocks d hd)) : Set (GL (Fin r) k)) = (fun x => g⁻¹ * x * g) ⁻¹' (unipRad k (stdBlocks d hd) : Set (GL (Fin r) k))`.

Use extensionality with `x`. Conclude with `mem_conjBy`. Rewrite using `[this]`. Conclude with `hU.preimage (by fun_prop)`.
-/
theorem isClosed_of_isParabRad : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r : ℕ}
    (P N : Subgroup (GL (Fin r) k)), IsParabRad P N → IsClosed (N : Set (GL (Fin r) k)) := by
  intro k _ _ _ _ r P N hPN
  obtain ⟨s, d, hd, g, -, rfl⟩ := hPN
  haveI : T2Space k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  have hU : IsClosed (unipRad k (stdBlocks d hd) : Set (GL (Fin r) k)) := by
    have : (unipRad k (stdBlocks d hd) : Set (GL (Fin r) k)) =
        (⋂ i, ⋂ j, ⋂ (_ : blk (stdBlocks d hd) j < blk (stdBlocks d hd) i),
          {x : GL (Fin r) k | (x : Matrix (Fin r) (Fin r) k) i j = 0}) ∩
        ⋂ c, ⋂ i, ⋂ j, {x : GL (Fin r) k | (x : Matrix (Fin r) (Fin r) k) (stdBlocks d hd ⟨c, i⟩)
          (stdBlocks d hd ⟨c, j⟩) = (1 : Matrix (Fin (d c)) (Fin (d c)) k) i j} := by
      ext x
      simp only [SetLike.mem_coe, mem_unipRad, mem_parab, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [this]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq ?_ continuous_const) (isClosed_iInter fun c => isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq ?_ continuous_const)
    · exact Units.continuous_val.matrix_elem _ _
    · exact Units.continuous_val.matrix_elem _ _
  have : (conjBy g (unipRad k (stdBlocks d hd)) : Set (GL (Fin r) k)) =
      (fun x => g⁻¹ * x * g) ⁻¹' (unipRad k (stdBlocks d hd) : Set (GL (Fin r) k)) := by
    ext x; exact mem_conjBy
  rw [this]
  exact hU.preimage (by fun_prop)

/- English proof (translation)
Introduce `G _ _ _ _ _ _ μ _ N hN ν _ Φ hΦ C D hC hD hsupp`. Use `(integral_integral_swap_of_hasCompactSupport (f := fun (z : G) (u : N) => Φ z u) (μ := μ) (ν := ν) (hΦ.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) ?_).symm` and prove the remaining obligations. Use `HasCompactSupport.intro (hC.prod (hN.isClosedEmbedding_subtypeVal.isCompact_preimage hD)) fun p hp => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Take `⟨h1, h2⟩` from `hsupp _ _ hne`.

Conclude with `hp ⟨h1, h2⟩`.
-/
theorem integral_swap_of_support : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (N : Subgroup G), IsClosed (N : Set G) →
    ∀ (ν : Measure N) [IsFiniteMeasureOnCompacts ν] (Φ : G → G → ℂ), Continuous (Function.uncurry Φ) →
    ∀ (C D : Set G), IsCompact C → IsCompact D → (∀ z u, Φ z u ≠ 0 → z ∈ C ∧ u ∈ D) →
    ∫ u : N, (∫ z, Φ z u ∂μ) ∂ν = ∫ z, (∫ u : N, Φ z u ∂ν) ∂μ := by
  intro G _ _ _ _ _ _ μ _ N hN ν _ Φ hΦ C D hC hD hsupp
  refine (integral_integral_swap_of_hasCompactSupport (f := fun (z : G) (u : N) => Φ z u) (μ := μ) (ν := ν)
    (hΦ.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) ?_).symm
  refine HasCompactSupport.intro (hC.prod (hN.isClosedEmbedding_subtypeVal.isCompact_preimage hD)) fun p hp => ?_
  by_contra hne
  obtain ⟨h1, h2⟩ := hsupp _ _ hne
  exact hp ⟨h1, h2⟩

/- English proof (translation)
Introduce `G _ _ _ _ _ _ N hN ν _ f hf x y`. Use `Continuous.integrable_of_hasCompactSupport (hf.1.continuous.comp (by fun_prop)) ?_` and prove the remaining obligations. Use `HasCompactSupport.intro (hN.isClosedEmbedding_subtypeVal.isCompact_preimage (hf.2.isCompact.image (f := fun g => x⁻¹ * g * y⁻¹) (by fun_prop))) fun u hu => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Conclude with `hu ⟨x * u * y, subset_tsupport _ hne, by group⟩`.
-/
theorem integrable_comp_of_SB : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (N : Subgroup G), IsClosed (N : Set G) → ∀ (ν : Measure N) [IsFiniteMeasureOnCompacts ν] (f : G → ℂ),
    f ∈ SB G → ∀ x y : G, Integrable (fun u : N => f (x * u * y)) ν := by
  intro G _ _ _ _ _ _ N hN ν _ f hf x y
  refine Continuous.integrable_of_hasCompactSupport (hf.1.continuous.comp (by fun_prop)) ?_
  refine HasCompactSupport.intro (hN.isClosedEmbedding_subtypeVal.isCompact_preimage
    (hf.2.isCompact.image (f := fun g => x⁻¹ * g * y⁻¹) (by fun_prop))) fun u hu => ?_
  by_contra hne
  exact hu ⟨x * u * y, subset_tsupport _ hne, by group⟩

/- English proof (translation)
Take `⟨s, d, hd, g, rfl, rfl⟩` from `hPN`. Establish `h1 : parab F (stdBlocks d hd) ≤ conjBy (g⁻¹ * g₀) (stdMaxParab F h)`. Introduce `x hx`. Establish `hx' : g * x * g⁻¹ ∈ conjBy g (parab F (stdBlocks d hd))` using `mem_conjBy.2 (by simpa [mul_assoc] using hx)`. Use `mem_conjBy.1 (hP hx')` as an intermediate fact.

Rewrite using `[mem_conjBy]`. Simplify `this` using `[mul_assoc]`. Establish `hc` using `GlobalTheory.T.mem_stdMaxParabolic_of_blockParabolic_le_conj F h d hd _ h1`. Establish `h2 : parab F (stdBlocks d hd) ≤ stdMaxParab F h`. Introduce `x hx`.

Use `mem_conjBy.1 (h1 hx)` as an intermediate fact. Establish `e : x = (g⁻¹ * g₀) * ((g⁻¹ * g₀)⁻¹ * x * (g⁻¹ * g₀)) * (g⁻¹ * g₀)⁻¹` using `by group`. Rewrite using `[e]`. Conclude with `mul_mem (mul_mem hc this) (inv_mem hc)`. Establish `h3` using `GlobalTheory.T.stdMaxParabolicRadical_le_blockUnipotentRadical F h d hd h2`.

Introduce `y hy`. Rewrite `hy`, the goal using `[mem_conjBy]`. Establish `hn : (g⁻¹ * g₀) * (g₀⁻¹ * y * g₀) * (g⁻¹ * g₀)⁻¹ ∈ stdMaxRad F h` using `(Subgroup.mem_normalizer_iff.1 (parab_le_normalizer F _ hc) _).1 hy`. Establish `e : g⁻¹ * y * g = (g⁻¹ * g₀) * (g₀⁻¹ * y * g₀) * (g⁻¹ * g₀)⁻¹` using `by group`. Rewrite using `[e]`.

Conclude with `h3 hn`.
-/
theorem conj_stdMaxRad_le (F : Type) [Field F] {r a b : ℕ} (h : a + b = r) (P N : Subgroup (GL (Fin r) F))
    (hPN : IsParabRad P N) (g₀ : GL (Fin r) F) (hP : P ≤ conjBy g₀ (stdMaxParab F h)) :
    conjBy g₀ (stdMaxRad F h) ≤ N := by
  obtain ⟨s, d, hd, g, rfl, rfl⟩ := hPN
  have h1 : parab F (stdBlocks d hd) ≤ conjBy (g⁻¹ * g₀) (stdMaxParab F h) := by
    intro x hx
    have hx' : g * x * g⁻¹ ∈ conjBy g (parab F (stdBlocks d hd)) := mem_conjBy.2 (by simpa [mul_assoc] using hx)
    have := mem_conjBy.1 (hP hx')
    rw [mem_conjBy]
    simpa [mul_assoc] using this
  have hc := GlobalTheory.T.mem_stdMaxParabolic_of_blockParabolic_le_conj F h d hd _ h1
  have h2 : parab F (stdBlocks d hd) ≤ stdMaxParab F h := by
    intro x hx
    have := mem_conjBy.1 (h1 hx)
    have e : x = (g⁻¹ * g₀) * ((g⁻¹ * g₀)⁻¹ * x * (g⁻¹ * g₀)) * (g⁻¹ * g₀)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hc this) (inv_mem hc)
  have h3 := GlobalTheory.T.stdMaxParabolicRadical_le_blockUnipotentRadical F h d hd h2
  intro y hy
  rw [mem_conjBy] at hy ⊢
  have hn : (g⁻¹ * g₀) * (g₀⁻¹ * y * g₀) * (g⁻¹ * g₀)⁻¹ ∈ stdMaxRad F h :=
    (Subgroup.mem_normalizer_iff.1 (parab_le_normalizer F _ hc) _).1 hy
  have e : g⁻¹ * y * g = (g⁻¹ * g₀) * (g₀⁻¹ * y * g₀) * (g⁻¹ * g₀)⁻¹ := by group
  rw [e]
  exact h3 hn

/- English proof (translation)
Introduce `k _ _ _ _ r a b h _ _ W _ _ _ τ _ hfix _ _ μ _ φ hφ f hf P N hPN hP ν _ x y`. Take `⟨g₀, hP⟩` from `hP`. Use `haveI : T2Space k := by`. Use `letI := IsTopologicalAddGroup.rightUniformSpace k`. Use `haveI := isUniformAddGroup_of_addCommGroup (G := k)`.

Use `infer_instance`. Establish `hNa` using `conj_stdMaxRad_le k h P N hPN g₀ hP`. Establish `hNc` using `isClosed_of_isParabRad k P N hPN`. Use `set e := idemGL k μ τ with he_def`. Establish `key : ∀ x' w : GL (Fin r) k, ∫ u : N, e (x' * u * w) ∂ν = 0`.

Introduce `x' w`. Take `⟨c, hc⟩` from `GlobalTheory.T.reduction_maxCompact_inter_conjRadical_contains_conj k h (x' * g₀)`. Use `GlobalTheory.T.integral_compactOpenTypeIdempotent_unipotent_eq_zero k τ μ N ν (conjBy c (stdMaxRad 𝓀[k] h)) ?_ x' ?_ w` and prove the remaining obligations. Introduce `v hv`. Establish `h0 : τ c⁻¹ v = 0` using `hfix _ fun u hu => by`.

Use `hv (c * u * c⁻¹) (mem_conjBy.2 (by simpa [mul_assoc] using hu))` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Establish `: v = τ c (τ c⁻¹ v)` using `by rw [← Module.End.mul_apply, ← map_mul]; simp`. Rewrite using `[this, h0, map_zero]`. Introduce `v hv`.

Take `⟨u, hu, hu2, hred⟩` from `hc _ (mem_conjBy.1 hv)`. Use `⟨x'⁻¹ * u * x', hNa (mem_conjBy.2 ?_), ?_, ?_⟩` and prove the remaining obligations. Use `mem_conjBy.1 hu2` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Simplify `hu` using `[mul_assoc]`.

Establish `e1 : x' * (x'⁻¹ * u * x') * x'⁻¹ = u` using `by group`. Establish `: (⟨x' * (x'⁻¹ * u * x') * x'⁻¹, by rw [e1]; exact hu⟩ : KO k (Fin r)) = ⟨u, hu⟩` using `Subtype.ext e1`. Rewrite using `[this, hred]`. Use `group`. Establish `heSB : e ∈ SB (GL (Fin r) k)` using `GlobalTheory.Orb.typeIdem_mem_SB μ _ τ GlobalTheory.SplitFlip.isOpen_KO GlobalTheory.SplitFlip.isCompact_KO (by`.

Establish `: ((GlobalTheory.LocGL.redK k (Fin r)).ker : Set (KO k (Fin r))) = Subtype.val ⁻¹' (KOne k (Fin r) : Set _)`. Use extensionality with `g`. Conclude with `GlobalTheory.LocGL.redK_eq_one_iff g`. Rewrite using `[this]`. Conclude with `GlobalTheory.StepData.isOpen_KOne.preimage continuous_subtype_val)`.

Establish `hfSB : f ∈ SB (GL (Fin r) k)`. Break down `hf with rfl | rfl` into its components or cases. Conclude with `GlobalTheory.Orb.conv_mem_SB heSB hφ`. Conclude with `GlobalTheory.Orb.conv_mem_SB hφ heSB`. Use `⟨integrable_comp_of_SB _ N hNc ν f hfSB x y, ?_⟩` and prove the remaining obligations.

Establish `hec : Continuous e` using `heSB.1.continuous`. Establish `hφc : Continuous φ` using `hφ.1.continuous`. Break down `hf with rfl | rfl` into its components or cases. Establish `h1 : ∀ u : N, GlobalTheory.AutomorphicL2Unitary.conv μ e φ (x * u * y) = ∫ z, e (x * u * (y * z)) * φ z⁻¹ ∂μ`. Introduce `u`.

Rewrite using `[GlobalTheory.AutomorphicL2Unitary.conv, ← integral_mul_left_eq_self _ (x * u * y)]`. Simplify using `[mul_assoc]`. Repeatedly rewrite using `[h1]`. Rewrite using `[integral_swap_of_support _ μ N hNc ν (fun z u => e (x * u * (y * z)) * φ z⁻¹) (by fun_prop) ((tsupport φ)⁻¹) ((fun p : GL (Fin r) k × GL (Fin r) k => x⁻¹ * p.1 * p.2 * y⁻¹) '' ((KO k (Fin r) : Set _) ×ˢ tsupport φ)) hφ.2.isCompact.inv ((GlobalTheory.SplitFlip.isCompact_KO.prod h …`. Repeatedly rewrite using `[integral_mul_const]`.

Simplify using `[key]`. Introduce `z u hz`. Establish `h1` using `left_ne_zero_of_mul hz`. Establish `h2` using `subset_tsupport _ (right_ne_zero_of_mul hz)`. Use `⟨by simpa using h2, ⟨(x * u * (y * z), z⁻¹), ⟨?_, h2⟩, by group⟩⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hK`. Conclude with `h1 (GlobalTheory.Orb.typeIdem_of_notMem μ _ τ hK)`. Establish `h1 : ∀ u : N, GlobalTheory.AutomorphicL2Unitary.conv μ φ e (x * u * y) = ∫ z, φ z * e (z⁻¹ * x * u * y) ∂μ`. Introduce `u`. Simplify using `[GlobalTheory.AutomorphicL2Unitary.conv, mul_assoc]`.

Repeatedly rewrite using `[h1]`. Rewrite using `[integral_swap_of_support _ μ N hNc ν (fun z u => φ z * e (z⁻¹ * x * u * y)) (by fun_prop) (tsupport φ) ((fun p : GL (Fin r) k × GL (Fin r) k => x⁻¹ * p.1 * p.2 * y⁻¹) '' (tsupport φ ×ˢ (KO k (Fin r) : Set _))) hφ.2.isCompact ((hφ.2.isCompact.prod GlobalTheory.SplitFlip.isCompact …`. Repeatedly rewrite using `[integral_const_mul]`. Simplify using `[key]`. Introduce `z u hz`.

Establish `h1` using `subset_tsupport _ (left_ne_zero_of_mul hz)`. Establish `h2` using `right_ne_zero_of_mul hz`. Use `⟨h1, ⟨(z, z⁻¹ * x * u * y), ⟨h1, ?_⟩, by group⟩⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hK`. Conclude with `h2 (GlobalTheory.Orb.typeIdem_of_notMem μ _ τ hK)`.
-/
theorem typeConstTermVanish : TypeConstTermVanish := by
  intro k _ _ _ _ r a b h _ _ W _ _ _ τ _ hfix _ _ μ _ φ hφ f hf P N hPN hP ν _ x y
  obtain ⟨g₀, hP⟩ := hP
  haveI : T2Space k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  have hNa := conj_stdMaxRad_le k h P N hPN g₀ hP
  have hNc := isClosed_of_isParabRad k P N hPN
  set e := idemGL k μ τ with he_def
  have key : ∀ x' w : GL (Fin r) k, ∫ u : N, e (x' * u * w) ∂ν = 0 := by
    intro x' w
    obtain ⟨c, hc⟩ := GlobalTheory.T.reduction_maxCompact_inter_conjRadical_contains_conj k h (x' * g₀)
    refine GlobalTheory.T.integral_compactOpenTypeIdempotent_unipotent_eq_zero k τ μ N ν (conjBy c (stdMaxRad 𝓀[k] h)) ?_ x' ?_ w
    · intro v hv
      have h0 : τ c⁻¹ v = 0 := hfix _ fun u hu => by
        have := hv (c * u * c⁻¹) (mem_conjBy.2 (by simpa [mul_assoc] using hu))
        calc τ u (τ c⁻¹ v) = τ (u * c⁻¹) v := by rw [map_mul]; rfl
          _ = τ (c⁻¹ * (c * u * c⁻¹)) v := by rw [show u * c⁻¹ = c⁻¹ * (c * u * c⁻¹) by group]
          _ = τ c⁻¹ (τ (c * u * c⁻¹) v) := by rw [map_mul]; rfl
          _ = τ c⁻¹ v := by rw [this]
      have : v = τ c (τ c⁻¹ v) := by rw [← Module.End.mul_apply, ← map_mul]; simp
      rw [this, h0, map_zero]
    · intro v hv
      obtain ⟨u, hu, hu2, hred⟩ := hc _ (mem_conjBy.1 hv)
      refine ⟨x'⁻¹ * u * x', hNa (mem_conjBy.2 ?_), ?_, ?_⟩
      · have := mem_conjBy.1 hu2
        simpa [mul_assoc] using this
      · simpa [mul_assoc] using hu
      · have e1 : x' * (x'⁻¹ * u * x') * x'⁻¹ = u := by group
        have : (⟨x' * (x'⁻¹ * u * x') * x'⁻¹, by rw [e1]; exact hu⟩ : KO k (Fin r)) = ⟨u, hu⟩ := Subtype.ext e1
        rw [this, hred]
        group
  have heSB : e ∈ SB (GL (Fin r) k) :=
    GlobalTheory.Orb.typeIdem_mem_SB μ _ τ GlobalTheory.SplitFlip.isOpen_KO GlobalTheory.SplitFlip.isCompact_KO
      (by
        have : ((GlobalTheory.LocGL.redK k (Fin r)).ker : Set (KO k (Fin r))) = Subtype.val ⁻¹' (KOne k (Fin r) : Set _) := by
          ext g; exact GlobalTheory.LocGL.redK_eq_one_iff g
        rw [this]; exact GlobalTheory.StepData.isOpen_KOne.preimage continuous_subtype_val)
  have hfSB : f ∈ SB (GL (Fin r) k) := by
    rcases hf with rfl | rfl
    · exact GlobalTheory.Orb.conv_mem_SB heSB hφ
    · exact GlobalTheory.Orb.conv_mem_SB hφ heSB
  refine ⟨integrable_comp_of_SB _ N hNc ν f hfSB x y, ?_⟩
  have hec : Continuous e := heSB.1.continuous
  have hφc : Continuous φ := hφ.1.continuous
  rcases hf with rfl | rfl
  · have h1 : ∀ u : N, GlobalTheory.AutomorphicL2Unitary.conv μ e φ (x * u * y) = ∫ z, e (x * u * (y * z)) * φ z⁻¹ ∂μ := by
      intro u
      rw [GlobalTheory.AutomorphicL2Unitary.conv, ← integral_mul_left_eq_self _ (x * u * y)]
      simp [mul_assoc]
    simp_rw [h1]
    rw [integral_swap_of_support _ μ N hNc ν (fun z u => e (x * u * (y * z)) * φ z⁻¹) (by fun_prop) ((tsupport φ)⁻¹)
      ((fun p : GL (Fin r) k × GL (Fin r) k => x⁻¹ * p.1 * p.2 * y⁻¹) '' ((KO k (Fin r) : Set _) ×ˢ tsupport φ))
      hφ.2.isCompact.inv ((GlobalTheory.SplitFlip.isCompact_KO.prod hφ.2.isCompact).image (by fun_prop)) ?_]
    · simp_rw [integral_mul_const]
      simp [key]
    · intro z u hz
      have h1 := left_ne_zero_of_mul hz
      have h2 := subset_tsupport _ (right_ne_zero_of_mul hz)
      refine ⟨by simpa using h2, ⟨(x * u * (y * z), z⁻¹), ⟨?_, h2⟩, by group⟩⟩
      by_contra hK
      exact h1 (GlobalTheory.Orb.typeIdem_of_notMem μ _ τ hK)
  · have h1 : ∀ u : N, GlobalTheory.AutomorphicL2Unitary.conv μ φ e (x * u * y) = ∫ z, φ z * e (z⁻¹ * x * u * y) ∂μ := by
      intro u
      simp [GlobalTheory.AutomorphicL2Unitary.conv, mul_assoc]
    simp_rw [h1]
    rw [integral_swap_of_support _ μ N hNc ν (fun z u => φ z * e (z⁻¹ * x * u * y)) (by fun_prop) (tsupport φ)
      ((fun p : GL (Fin r) k × GL (Fin r) k => x⁻¹ * p.1 * p.2 * y⁻¹) '' (tsupport φ ×ˢ (KO k (Fin r) : Set _)))
      hφ.2.isCompact ((hφ.2.isCompact.prod GlobalTheory.SplitFlip.isCompact_KO).image (by fun_prop)) ?_]
    · simp_rw [integral_const_mul]
      simp [key]
    · intro z u hz
      have h1 := subset_tsupport _ (left_ne_zero_of_mul hz)
      have h2 := right_ne_zero_of_mul hz
      refine ⟨h1, ⟨(z, z⁻¹ * x * u * y), ⟨h1, ?_⟩, by group⟩⟩
      by_contra hK
      exact h2 (GlobalTheory.Orb.typeIdem_of_notMem μ _ τ hK)

end GlobalTheory.TypeConstTerm

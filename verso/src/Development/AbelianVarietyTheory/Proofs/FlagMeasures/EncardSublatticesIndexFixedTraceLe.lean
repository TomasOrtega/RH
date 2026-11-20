import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexCongruenceSubgroupLeAbsNormPow
import Formalism.HyperbolicPlaceProducts.SecondLevelArithmeticNorm

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.TraceCount

/- English proof (translation)
Take `⟨⟨v, hv⟩, -⟩` from `GlobalTheory.CongIndex.quot_smul_top_span_card (R := R) (N := C) (Ideal.span {(m : R)})`. Use `choose c hc using fun i => Submodule.Quotient.mk_surjective _ (v i)`. Use `⟨fun i => c i, fun i => (c i).2, fun y hy => ?_⟩` and prove the remaining obligations. Establish `h1 : (Submodule.Quotient.mk ⟨y, hy⟩ : C ⧸ (Ideal.span {(m : R)} • (⊤ : Submodule R C))) ∈ Submodule.span R (Set.range v)` using `hv ▸ Submodule.mem_top`. Take `⟨r, hr⟩` from `(Submodule.mem_span_range_iff_exists_fun R).1 h1`.

Establish `h2 : (Submodule.Quotient.mk (∑ i, r i • c i) : C ⧸ (Ideal.span {(m : R)} • (⊤ : Submodule R C))) = Submodule.Quotient.mk ⟨y, hy⟩`. Rewrite using `[← hr, ← Submodule.mkQ_apply, map_sum]`. Simplify using `[hc]`. Establish `h3` using `(Submodule.Quotient.eq _).1 h2.symm`. Rewrite `h3` using `[Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`.

Take `⟨d, -, hd⟩` from `h3`. Use `⟨r, d, d.2, ?_⟩` and prove the remaining obligations. Establish `h4` using `congrArg Subtype.val hd`. Simplify using `only [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_sum, Nat.cast_smul_eq_nsmul] at h4`. Rewrite `h4` using `[eq_sub_iff_add_eq]`.

Rewrite using `[← h4, add_comm]`. Simplify using the standard rewrite rules.
-/
theorem exists_gen_mod {R W : Type} [CommRing R] [IsDomain R] [AddCommGroup W] [Module R W] (C : Submodule R W)
    [Module.Finite R C] [Module.Projective R C] (m : ℕ) [Finite (R ⧸ Ideal.span {(m : R)})] :
    ∃ c : Fin (Module.finrank R C) → W, (∀ i, c i ∈ C) ∧
      ∀ y ∈ C, ∃ (r : Fin (Module.finrank R C) → R) (d : W), d ∈ C ∧ y = ∑ i, r i • c i + m • d := by
  obtain ⟨⟨v, hv⟩, -⟩ := GlobalTheory.CongIndex.quot_smul_top_span_card (R := R) (N := C) (Ideal.span {(m : R)})
  choose c hc using fun i => Submodule.Quotient.mk_surjective _ (v i)
  refine ⟨fun i => c i, fun i => (c i).2, fun y hy => ?_⟩
  have h1 : (Submodule.Quotient.mk ⟨y, hy⟩ : C ⧸ (Ideal.span {(m : R)} • (⊤ : Submodule R C))) ∈
      Submodule.span R (Set.range v) := hv ▸ Submodule.mem_top
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 h1
  have h2 : (Submodule.Quotient.mk (∑ i, r i • c i) : C ⧸ (Ideal.span {(m : R)} • (⊤ : Submodule R C))) =
      Submodule.Quotient.mk ⟨y, hy⟩ := by
    rw [← hr, ← Submodule.mkQ_apply, map_sum]
    simp [hc]
  have h3 := (Submodule.Quotient.eq _).1 h2.symm
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
  obtain ⟨d, -, hd⟩ := h3
  refine ⟨r, d, d.2, ?_⟩
  have h4 := congrArg Subtype.val hd
  simp only [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_sum, Nat.cast_smul_eq_nsmul] at h4
  rw [eq_sub_iff_add_eq] at h4
  rw [← h4, add_comm]
  simp

/- English proof (translation)
Use `set S := {La : Submodule R V | La ≤ L ∧ La.map f = C ∧ La ⊓ LinearMap.ker f = M} with hS`. Break down `S.eq_empty_or_nonempty with h0 | ⟨L₁, hL₁⟩` into its components or cases. Simplify using `[h0]`. Establish `hlift : ∀ La : S, ∀ y ∈ C, ∃ a ∈ La.1, f a = y` using `fun La y hy => by`. Establish `: y ∈ La.1.map f` using `La.2.2.1.symm ▸ hy`.

Conclude with `this`. Use `choose a ha hfa using fun (La : S) (i : Fin s) => hlift La (c i) (hc i)`. Use `set K₀ := (L ⊓ LinearMap.ker f).toAddSubgroup with hK₀`. Establish `hmem : ∀ (La : S) i, a La i - a ⟨L₁, hL₁⟩ i ∈ K₀` using `fun La i => ⟨sub_mem (La.2.1 (ha La i)) (hL₁.1 (ha ⟨L₁, hL₁⟩ i)), by simp [hfa]⟩`. Set `Φ : S → (Fin s → K₀ ⧸ M.toAddSubgroup.addSubgroupOf K₀)` to `fun La i => QuotientAddGroup.mk ⟨_, hmem La i⟩`.

Establish `hle : ∀ La La' : S, Φ La = Φ La' → La.1 ≤ La'.1`. Introduce `La La' h y hy`. Establish `hML : M ≤ La'.1` using `La'.2.2.2 ▸ inf_le_left`. Establish `h1 : ∀ i, a La i ∈ La'.1` using `fun i => by`. Establish `h2` using `QuotientAddGroup.eq.1 (congrFun h i)`.

Rewrite `h2` using `[AddSubgroup.mem_addSubgroupOf]`. Establish `h3 : -(a La i - a ⟨L₁, hL₁⟩ i) + (a La' i - a ⟨L₁, hL₁⟩ i) ∈ La'.1` using `hML h2`. Establish `h4` using `sub_mem (ha La' i) h3`. Use `h4 using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws.

Establish `hfy : f y ∈ C` using `La.2.2.1 ▸ Submodule.mem_map_of_mem hy`. Take `⟨r, d, hd, hyd⟩` from `hgen _ hfy`. Take `⟨b, hb, hfb⟩` from `hlift La d hd`. Take `⟨b', hb', hfb'⟩` from `hlift La' d hd`. Establish `h5 : y - (∑ i, r i • a La i + m • b) ∈ M`.

Rewrite using `[← La.2.2.2]`. Use `⟨sub_mem hy (add_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (ha La i)) (nsmul_mem hb _)), ?_⟩` and prove the remaining obligations. Simplify using `[hfa, hfb, ← hyd]`. Establish `h6 : m • (b - b') ∈ M`. Establish `h7 : b - b' ∈ K₀` using `⟨sub_mem (La.2.1 hb) (La'.2.1 hb'), by simp [hfb, hfb']⟩`.

Establish `h8` using `AddSubgroup.nsmul_index_mem (M.toAddSubgroup.addSubgroupOf K₀) ⟨_, h7⟩`. Rewrite `h8` using `[AddSubgroup.mem_addSubgroupOf]`. Establish `h9 : (M.toAddSubgroup.addSubgroupOf K₀).index = m` using `hm`. Rewrite `h8` using `[h9]`. Conclude with `h8`.

Establish `h10` using `add_mem (hML h5) (add_mem (Submodule.sum_mem _ fun i (_ : i ∈ Finset.univ) => Submodule.smul_mem _ (r i) (h1 i)) (add_mem (hML h6) (nsmul_mem hb' m)))`. Use `h10 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[smul_sub]`. Normalize the expressions using the abelian group laws. Establish `hΦ : Function.Injective Φ` using `fun La La' h => Subtype.ext (le_antisymm (hle _ _ h) (hle _ _ h.symm))`.

Establish `hcard : Nat.card (K₀ ⧸ M.toAddSubgroup.addSubgroupOf K₀) = m` using `hm`. Establish `: Finite (K₀ ⧸ M.toAddSubgroup.addSubgroupOf K₀)` using `Nat.finite_of_card_ne_zero (hcard ▸ hm0)`. Establish `hfin : Finite S` using `Finite.of_injective Φ hΦ`. Establish `h11` using `Nat.card_le_card_of_injective Φ hΦ`. Rewrite `h11` using `[Nat.card_fun, hcard, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]`.

Rewrite using `[← (Set.toFinite S).cast_ncard_eq]`. Conclude with `h11` after adjusting the coercions.
-/
theorem fibre_count {R V W : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (f : V →ₗ[R] W) (L M : Submodule R V) (C : Submodule R W) (m s : ℕ)
    (hm : M.toAddSubgroup.relIndex (L ⊓ LinearMap.ker f).toAddSubgroup = m) (hm0 : m ≠ 0)
    (c : Fin s → W) (hc : ∀ i, c i ∈ C)
    (hgen : ∀ y ∈ C, ∃ (r : Fin s → R) (d : W), d ∈ C ∧ y = ∑ i, r i • c i + m • d) :
    {La : Submodule R V | La ≤ L ∧ La.map f = C ∧ La ⊓ LinearMap.ker f = M}.encard ≤ (m ^ s : ℕ) := by
  set S := {La : Submodule R V | La ≤ L ∧ La.map f = C ∧ La ⊓ LinearMap.ker f = M} with hS
  rcases S.eq_empty_or_nonempty with h0 | ⟨L₁, hL₁⟩
  · simp [h0]
  have hlift : ∀ La : S, ∀ y ∈ C, ∃ a ∈ La.1, f a = y := fun La y hy => by
    have : y ∈ La.1.map f := La.2.2.1.symm ▸ hy
    exact this
  choose a ha hfa using fun (La : S) (i : Fin s) => hlift La (c i) (hc i)
  set K₀ := (L ⊓ LinearMap.ker f).toAddSubgroup with hK₀
  have hmem : ∀ (La : S) i, a La i - a ⟨L₁, hL₁⟩ i ∈ K₀ := fun La i =>
    ⟨sub_mem (La.2.1 (ha La i)) (hL₁.1 (ha ⟨L₁, hL₁⟩ i)), by simp [hfa]⟩
  let Φ : S → (Fin s → K₀ ⧸ M.toAddSubgroup.addSubgroupOf K₀) := fun La i => QuotientAddGroup.mk ⟨_, hmem La i⟩
  have hle : ∀ La La' : S, Φ La = Φ La' → La.1 ≤ La'.1 := by
    intro La La' h y hy
    have hML : M ≤ La'.1 := La'.2.2.2 ▸ inf_le_left
    have h1 : ∀ i, a La i ∈ La'.1 := fun i => by
      have h2 := QuotientAddGroup.eq.1 (congrFun h i)
      rw [AddSubgroup.mem_addSubgroupOf] at h2
      have h3 : -(a La i - a ⟨L₁, hL₁⟩ i) + (a La' i - a ⟨L₁, hL₁⟩ i) ∈ La'.1 := hML h2
      have h4 := sub_mem (ha La' i) h3
      convert h4 using 1
      abel
    have hfy : f y ∈ C := La.2.2.1 ▸ Submodule.mem_map_of_mem hy
    obtain ⟨r, d, hd, hyd⟩ := hgen _ hfy
    obtain ⟨b, hb, hfb⟩ := hlift La d hd
    obtain ⟨b', hb', hfb'⟩ := hlift La' d hd
    have h5 : y - (∑ i, r i • a La i + m • b) ∈ M := by
      rw [← La.2.2.2]
      refine ⟨sub_mem hy (add_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (ha La i))
        (nsmul_mem hb _)), ?_⟩
      simp [hfa, hfb, ← hyd]
    have h6 : m • (b - b') ∈ M := by
      have h7 : b - b' ∈ K₀ := ⟨sub_mem (La.2.1 hb) (La'.2.1 hb'), by simp [hfb, hfb']⟩
      have h8 := AddSubgroup.nsmul_index_mem (M.toAddSubgroup.addSubgroupOf K₀) ⟨_, h7⟩
      rw [AddSubgroup.mem_addSubgroupOf] at h8
      have h9 : (M.toAddSubgroup.addSubgroupOf K₀).index = m := hm
      rw [h9] at h8
      exact h8
    have h10 := add_mem (hML h5) (add_mem (Submodule.sum_mem _ fun i (_ : i ∈ Finset.univ) =>
      Submodule.smul_mem _ (r i) (h1 i)) (add_mem (hML h6) (nsmul_mem hb' m)))
    convert h10 using 1
    rw [smul_sub]
    abel
  have hΦ : Function.Injective Φ := fun La La' h => Subtype.ext (le_antisymm (hle _ _ h) (hle _ _ h.symm))
  have hcard : Nat.card (K₀ ⧸ M.toAddSubgroup.addSubgroupOf K₀) = m := hm
  have : Finite (K₀ ⧸ M.toAddSubgroup.addSubgroupOf K₀) := Nat.finite_of_card_ne_zero (hcard ▸ hm0)
  have hfin : Finite S := Finite.of_injective Φ hΦ
  have h11 := Nat.card_le_card_of_injective Φ hΦ
  rw [Nat.card_fun, hcard, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin] at h11
  rw [← (Set.toFinite S).cast_ncard_eq]
  exact_mod_cast h11

/- English proof (translation)
Establish `h1` using `AddSubgroup.relIndex_mul_relIndex A (A ⊔ (L ⊓ f.ker)) L le_sup_left (sup_le h inf_le_left)`. Rewrite using `[← h1, AddSubgroup.relIndex_sup_left, AddSubgroup.relIndex_map_map]`. Use `congr 1`. Rewrite using `[← AddSubgroup.inf_relIndex_right A, ← AddSubgroup.inf_relIndex_right (A ⊓ f.ker), inf_assoc, inf_eq_right.2 (inf_le_right : L ⊓ f.ker ≤ f.ker)]`. Establish `h2 : L ⊔ f.ker = L ⊔ (A ⊔ f.ker)` using `by rw [← sup_assoc, sup_eq_left.2 h]`.

Rewrite using `[h2, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right (A ⊔ f.ker), sup_inf_assoc_of_le _ h, inf_comm]`.
-/
theorem relIndex_eq_mul {V W : Type} [AddCommGroup V] [AddCommGroup W] (f : V →+ W) (A L : AddSubgroup V)
    (h : A ≤ L) : A.relIndex L = (A ⊓ f.ker).relIndex (L ⊓ f.ker) * (A.map f).relIndex (L.map f) := by
  have h1 := AddSubgroup.relIndex_mul_relIndex A (A ⊔ (L ⊓ f.ker)) L le_sup_left (sup_le h inf_le_left)
  rw [← h1, AddSubgroup.relIndex_sup_left, AddSubgroup.relIndex_map_map]
  congr 1
  · rw [← AddSubgroup.inf_relIndex_right A, ← AddSubgroup.inf_relIndex_right (A ⊓ f.ker), inf_assoc,
      inf_eq_right.2 (inf_le_right : L ⊓ f.ker ≤ f.ker)]
  · have h2 : L ⊔ f.ker = L ⊔ (A ⊔ f.ker) := by rw [← sup_assoc, sup_eq_left.2 h]
    rw [h2, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right (A ⊔ f.ker), sup_inf_assoc_of_le _ h,
      inf_comm]

/- English proof (translation)
Establish `hfin : S.Finite`. Use `(hT.biUnion fun b hb => Set.finite_of_encard_le_coe (hk b hb)).subset fun a ha => ?_` and prove the remaining obligations. Conclude with `Set.mem_biUnion (hg a ha) ⟨ha, rfl⟩`. Rewrite using `[← hfin.cast_ncard_eq, Nat.cast_le, Set.ncard_eq_toFinset_card _ hfin, Set.ncard_eq_toFinset_card _ hT, mul_comm]`. Use `Finset.card_le_mul_card_image_of_maps_to (f := g) (fun a ha => by simpa using hg a (by simpa using ha)) k fun b hb => ?_` and prove the remaining obligations.

Establish `h1` using `hk b (by simpa using hb)`. Establish `h2 : {a | a ∈ S ∧ g a = b} = ((hfin.toFinset.filter fun a => g a = b : Finset α) : Set α)`. Use extensionality with `a`. Simplify using the standard rewrite rules. Rewrite `h1` using `[h2, Set.encard_coe_eq_coe_finsetCard]`.

Conclude with `h1` after adjusting the coercions.
-/
theorem encard_le_mul {α β : Type} (g : α → β) (S : Set α) (T : Set β) (hT : T.Finite) (k : ℕ)
    (hg : ∀ a ∈ S, g a ∈ T) (hk : ∀ b ∈ T, {a | a ∈ S ∧ g a = b}.encard ≤ k) :
    S.encard ≤ (T.ncard * k : ℕ) := by
  have hfin : S.Finite := by
    refine (hT.biUnion fun b hb => Set.finite_of_encard_le_coe (hk b hb)).subset fun a ha => ?_
    exact Set.mem_biUnion (hg a ha) ⟨ha, rfl⟩
  rw [← hfin.cast_ncard_eq, Nat.cast_le, Set.ncard_eq_toFinset_card _ hfin, Set.ncard_eq_toFinset_card _ hT,
    mul_comm]
  refine Finset.card_le_mul_card_image_of_maps_to (f := g) (fun a ha => by simpa using hg a (by simpa using ha)) k
    fun b hb => ?_
  have h1 := hk b (by simpa using hb)
  have h2 : {a | a ∈ S ∧ g a = b} = ((hfin.toFinset.filter fun a => g a = b : Finset α) : Set α) := by
    ext a; simp
  rw [h2, Set.encard_coe_eq_coe_finsetCard] at h1
  exact_mod_cast h1

/- English proof (translation)
Establish `: Module.Finite (𝓞 K) C` using `Module.Finite.iff_fg.2 hC`. Establish `: Module.IsTorsionFree (𝓞 K) W` using `Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K W`. Establish `: Module.Flat (𝓞 K) C` using `inferInstance`. Establish `: Module.FinitePresentation (𝓞 K) C` using `Module.finitePresentation_of_finite _ _`. Conclude with `⟨inferInstance, Module.Flat.projective_of_finitePresentation, (GlobalTheory.CongIndex.finrank_le_finrank_span C).trans (Submodule.finrank_le _)⟩`.
-/
theorem proj_rank {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (C : Submodule (𝓞 K) W) (hC : C.FG) :
    Module.Finite (𝓞 K) C ∧ Module.Projective (𝓞 K) C ∧ Module.finrank (𝓞 K) C ≤ Module.finrank K W := by
  have : Module.Finite (𝓞 K) C := Module.Finite.iff_fg.2 hC
  have : Module.IsTorsionFree (𝓞 K) W := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K W
  have : Module.Flat (𝓞 K) C := inferInstance
  have : Module.FinitePresentation (𝓞 K) C := Module.finitePresentation_of_finite _ _
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation,
    (GlobalTheory.CongIndex.finrank_le_finrank_span C).trans (Submodule.finrank_le _)⟩

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `proj_rank C hC`. Take `⟨h4, h5⟩` from `Formalism.SLP.Final.submoduleIndexCountO K C j hj`. Establish `h6` using `Formalism.SLP.Final.omegaPow (Module.finrank ℚ K) j Module.finrank_pos hj`. Establish `hsub : {N : Submodule (𝓞 K) W | N ≤ C ∧ N.toAddSubgroup.relIndex C.toAddSubgroup = j} ⊆ (fun N : Submodule (𝓞 K) C => N.map C.subtype) '' {N | N.toAddSubgroup.index = j}`. Introduce and unpack `N ⟨hN, hNj⟩`.

Use `⟨N.comap C.subtype, hNj, ?_⟩` and prove the remaining obligations. Simplify using `only [Submodule.map_comap_subtype]`. Conclude with `inf_eq_right.2 hN`. Use `⟨(h4.image _).subset hsub, ?_⟩` and prove the remaining obligations. Establish `h7` using `((Set.ncard_le_ncard hsub (h4.image _)).trans (Set.ncard_image_le h4)).trans h5`.

Establish `hj1 : (1 : ℝ) ≤ j` using `by exact_mod_cast hj`. Combine the equalities or inequalities in the displayed calculation. Conclude with `h7` after adjusting the coercions. Use `_ ≤ _ := mul_le_mul h6 (pow_le_pow_right₀ hj1 h3) (by positivity) (by positivity)`.
-/
theorem sub_count {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (C : Submodule (𝓞 K) W) (hC : C.FG) (j : ℕ) (hj : 1 ≤ j) :
    {N : Submodule (𝓞 K) W | N ≤ C ∧ N.toAddSubgroup.relIndex C.toAddSubgroup = j}.Finite ∧
    (({N : Submodule (𝓞 K) W | N ≤ C ∧ N.toAddSubgroup.relIndex C.toAddSubgroup = j}.ncard : ℕ) : ℝ) ≤
      (j : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (j : ℝ) ^ Module.finrank K W := by
  obtain ⟨h1, h2, h3⟩ := proj_rank C hC
  obtain ⟨h4, h5⟩ := Formalism.SLP.Final.submoduleIndexCountO K C j hj
  have h6 := Formalism.SLP.Final.omegaPow (Module.finrank ℚ K) j Module.finrank_pos hj
  have hsub : {N : Submodule (𝓞 K) W | N ≤ C ∧ N.toAddSubgroup.relIndex C.toAddSubgroup = j} ⊆
      (fun N : Submodule (𝓞 K) C => N.map C.subtype) '' {N | N.toAddSubgroup.index = j} := by
    rintro N ⟨hN, hNj⟩
    refine ⟨N.comap C.subtype, hNj, ?_⟩
    simp only [Submodule.map_comap_subtype]
    exact inf_eq_right.2 hN
  refine ⟨(h4.image _).subset hsub, ?_⟩
  have h7 := ((Set.ncard_le_ncard hsub (h4.image _)).trans (Set.ncard_image_le h4)).trans h5
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  calc _ ≤ ((Module.finrank ℚ K : ℕ) : ℝ) ^ (Nat.primeFactorsList j).length * (j : ℝ) ^ Module.finrank (𝓞 K) C := by
        exact_mod_cast h7
    _ ≤ _ := mul_le_mul h6 (pow_le_pow_right₀ hj1 h3) (by positivity) (by positivity)

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ _ L₀ M U x hL hx`. Use `set S := {La : Submodule (𝓞 K) V | La ≤ L₀ ∧ idx L₀ La = x ∧ La ⊓ rs (𝓞 K) U = M} with hS`. Break down `S.eq_empty_or_nonempty with h0 | ⟨L₁, hL₁⟩` into its components or cases. Simplify using `[h0]`. Set `f : V →ₗ[𝓞 K] (V ⧸ U)` to `U.mkQ.restrictScalars (𝓞 K)`.

Establish `hker : LinearMap.ker f = rs (𝓞 K) U`. Use extensionality with `v`. Simplify using `[f]`. Establish `hker' : f.toAddMonoidHom.ker = (LinearMap.ker f).toAddSubgroup` using `rfl`. Use `set m := M.toAddSubgroup.relIndex (L₀ ⊓ LinearMap.ker f).toAddSubgroup with hm`.

Establish `hidx : ∀ La ∈ S, x = m * (La.map f).toAddSubgroup.relIndex (L₀.map f).toAddSubgroup`. Introduce `La hLa`. Establish `h1` using `relIndex_eq_mul f.toAddMonoidHom La.toAddSubgroup L₀.toAddSubgroup hLa.1`. Establish `h2 : La.toAddSubgroup.relIndex L₀.toAddSubgroup = x` using `hLa.2.1`. Establish `h3 : La ⊓ LinearMap.ker f = M` using `hker ▸ hLa.2.2`.

Rewrite using `[← h2, h1, hm, ← h3]`. Both sides reduce to the same expression. Use `set j := (L₁.map f).toAddSubgroup.relIndex (L₀.map f).toAddSubgroup with hj`. Establish `hxj : x = m * j` using `hidx L₁ hL₁`. Establish `hm0 : m ≠ 0` using `fun h => by rw [h] at hxj; omega`.

Establish `hj0 : j ≠ 0` using `fun h => by rw [h] at hxj; omega`. Establish `hC : (L₀.map f).FG` using `(Submodule.IsLattice.fg (self := hL)).map f`. Establish `hs : Module.finrank K (V ⧸ U) = Module.finrank K V - Module.finrank K U`. Use `U.finrank_quotient_add_finrank` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `set s := Module.finrank K V - Module.finrank K U with hsdef`. Take `⟨hT, hTc⟩` from `sub_count (L₀.map f) hC j (Nat.one_le_iff_ne_zero.2 hj0)`. Rewrite `hTc` using `[hs]`. Establish `hfinq : Finite (𝓞 K ⧸ Ideal.span {(m : 𝓞 K)})` using `Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hm0)`. Establish `hcount` using `encard_le_mul (fun La : Submodule (𝓞 K) V => La.map f) S _ hT (m ^ s) (fun La hLa => ⟨Submodule.map_mono hLa.1, Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm0) ((hidx La hLa).symm.trans hxj)⟩) (fun N hN => by`.

Establish `hCf : Module.Finite (𝓞 K) (L₀.map f)` using `Module.Finite.iff_fg.2 hC`. Establish `hNfg : N.FG` using `Submodule.FG.of_le_of_isNoetherian hN.1`. Take `⟨h1, h2, h3⟩` from `proj_rank N hNfg`. Take `⟨c, hc, hgen⟩` from `exists_gen_mod N m`. Establish `h4` using `fibre_count f L₀ M N m _ hm.symm hm0 c hc hgen`.

Use `le_trans (Set.encard_le_encard ?_) (h4.trans ?_)` and prove the remaining obligations. Introduce and unpack `La ⟨hLa, hN'⟩`. Conclude with `⟨hLa.1, hN', hker ▸ hLa.2.2⟩`. Conclude with `Nat.pow_le_pow_right (Nat.pos_of_ne_zero hm0) (hs ▸ h3))` after adjusting the coercions. Use `le_trans (ENat.toENNReal_le.2 hcount) ?_` and prove the remaining obligations.

Rewrite using `[ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Establish `hx1 : (1 : ℝ) ≤ x` using `by exact_mod_cast hx`. Establish `hjx : (j : ℝ) ≤ x` using `by exact_mod_cast hxj ▸ Nat.le_mul_of_pos_left j (Nat.pos_of_ne_zero hm0)`. Establish `hlog : 0 ≤ Real.logb 2 (Module.finrank ℚ K)` using `Real.logb_nonneg one_lt_two (by exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K))`.

Establish `hxr : (x : ℝ) = m * j` using `by exact_mod_cast hxj`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.rpow_add (by positivity), Real.rpow_natCast]`. Use `_ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by`.

Establish `: (0 : ℝ) ≤ s` using `Nat.cast_nonneg _`. Unfold `cf`. Use the proof step `linarith)`.
-/
theorem main : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L₀ M : Submodule (𝓞 K) V) (U : Submodule K V) (x : ℕ), Submodule.IsLattice K L₀ → 1 ≤ x → ((({La : Submodule (𝓞 K) V | La ≤ L₀ ∧ idx L₀ La = x ∧ La ⊓ rs (𝓞 K) U = M}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((x : ℝ) ^ (2 * (((Module.finrank K V) - Module.finrank K U : ℕ) : ℝ) + cf K)) := by
  intro K V _ _ _ _ _ _ _ _ L₀ M U x hL hx
  set S := {La : Submodule (𝓞 K) V | La ≤ L₀ ∧ idx L₀ La = x ∧ La ⊓ rs (𝓞 K) U = M} with hS
  rcases S.eq_empty_or_nonempty with h0 | ⟨L₁, hL₁⟩
  · simp [h0]
  let f : V →ₗ[𝓞 K] (V ⧸ U) := U.mkQ.restrictScalars (𝓞 K)
  have hker : LinearMap.ker f = rs (𝓞 K) U := by
    ext v
    simp [f]
  have hker' : f.toAddMonoidHom.ker = (LinearMap.ker f).toAddSubgroup := rfl
  set m := M.toAddSubgroup.relIndex (L₀ ⊓ LinearMap.ker f).toAddSubgroup with hm
  have hidx : ∀ La ∈ S, x = m * (La.map f).toAddSubgroup.relIndex (L₀.map f).toAddSubgroup := by
    intro La hLa
    have h1 := relIndex_eq_mul f.toAddMonoidHom La.toAddSubgroup L₀.toAddSubgroup hLa.1
    have h2 : La.toAddSubgroup.relIndex L₀.toAddSubgroup = x := hLa.2.1
    have h3 : La ⊓ LinearMap.ker f = M := hker ▸ hLa.2.2
    rw [← h2, h1, hm, ← h3]
    rfl
  set j := (L₁.map f).toAddSubgroup.relIndex (L₀.map f).toAddSubgroup with hj
  have hxj : x = m * j := hidx L₁ hL₁
  have hm0 : m ≠ 0 := fun h => by rw [h] at hxj; omega
  have hj0 : j ≠ 0 := fun h => by rw [h] at hxj; omega
  have hC : (L₀.map f).FG := (Submodule.IsLattice.fg (self := hL)).map f
  have hs : Module.finrank K (V ⧸ U) = Module.finrank K V - Module.finrank K U := by
    have := U.finrank_quotient_add_finrank
    omega
  set s := Module.finrank K V - Module.finrank K U with hsdef
  obtain ⟨hT, hTc⟩ := sub_count (L₀.map f) hC j (Nat.one_le_iff_ne_zero.2 hj0)
  rw [hs] at hTc
  have hfinq : Finite (𝓞 K ⧸ Ideal.span {(m : 𝓞 K)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hm0)
  have hcount := encard_le_mul (fun La : Submodule (𝓞 K) V => La.map f) S _ hT (m ^ s)
    (fun La hLa => ⟨Submodule.map_mono hLa.1,
      Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm0) ((hidx La hLa).symm.trans hxj)⟩)
    (fun N hN => by
      have hCf : Module.Finite (𝓞 K) (L₀.map f) := Module.Finite.iff_fg.2 hC
      have hNfg : N.FG := Submodule.FG.of_le_of_isNoetherian hN.1
      obtain ⟨h1, h2, h3⟩ := proj_rank N hNfg
      obtain ⟨c, hc, hgen⟩ := exists_gen_mod N m
      have h4 := fibre_count f L₀ M N m _ hm.symm hm0 c hc hgen
      refine le_trans (Set.encard_le_encard ?_) (h4.trans ?_)
      · rintro La ⟨hLa, hN'⟩
        exact ⟨hLa.1, hN', hker ▸ hLa.2.2⟩
      · exact_mod_cast Nat.pow_le_pow_right (Nat.pos_of_ne_zero hm0) (hs ▸ h3))
  refine le_trans (ENat.toENNReal_le.2 hcount) ?_
  rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  refine ENNReal.ofReal_le_ofReal ?_
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hjx : (j : ℝ) ≤ x := by exact_mod_cast hxj ▸ Nat.le_mul_of_pos_left j (Nat.pos_of_ne_zero hm0)
  have hlog : 0 ≤ Real.logb 2 (Module.finrank ℚ K) :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K))
  have hxr : (x : ℝ) = m * j := by exact_mod_cast hxj
  push_cast
  calc _ ≤ ((j : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (j : ℝ) ^ s) * (m : ℝ) ^ s :=
        mul_le_mul_of_nonneg_right hTc (by positivity)
    _ = (j : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (x : ℝ) ^ s := by rw [hxr, mul_pow]; ring
    _ ≤ (x : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (x : ℝ) ^ s :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) hjx hlog) (by positivity)
    _ = (x : ℝ) ^ (Real.logb 2 (Module.finrank ℚ K) + (s : ℝ)) := by
        rw [Real.rpow_add (by positivity), Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by
        have : (0 : ℝ) ≤ s := Nat.cast_nonneg _
        unfold cf
        linarith)

end GlobalTheory.TraceCount

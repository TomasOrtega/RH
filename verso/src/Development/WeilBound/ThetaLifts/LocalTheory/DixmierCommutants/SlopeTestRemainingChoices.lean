import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.FullOfSoLoc

noncomputable section

namespace PositivityTheory.ThKG.LocalRamifiedLeviRestriction

section
open Polynomial

/- English proof (translation)
Establish `hs` using `C_leadingCoeff_mul_prod_multiset_X_sub_C (p := p) IsAlgClosed.card_roots_eq_natDegree`. Establish `hlin : ∀ a : ℂ, aeval T (X - C a) = T - a • 1`. Introduce `a`. Simplify using `[Algebra.algebraMap_eq_smul_one]`. Establish `key : ∀ m : Multiset ℂ, Function.Injective (aeval T (m.map fun a => X - C a).prod)`.

Introduce `m`. Proceed by induction on `m using Multiset.induction_on with`. Consider the case `empty`. Simplify using `only [Multiset.map_zero, Multiset.prod_zero, map_one, Module.End.one_eq_id, LinearMap.id_coe]`. Conclude with `Function.injective_id`.

Consider the case `cons a m ih`. Rewrite using `[Multiset.map_cons, Multiset.prod_cons, map_mul, Module.End.mul_eq_comp, LinearMap.coe_comp]`. Use `Function.Injective.comp ?_ ih` and prove the remaining obligations. Rewrite using `[hlin]`. Conclude with `hT a`.

Rewrite using `[← hs, map_mul, Module.End.mul_eq_comp, LinearMap.coe_comp]`. Use `Function.Injective.comp ?_ (key _)` and prove the remaining obligations. Rewrite using `[aeval_C, Algebra.algebraMap_eq_smul_one]`. Introduce `x y hxy`. Simplify using `only [LinearMap.smul_apply, Module.End.one_apply] at hxy`.

Conclude with `smul_right_injective V (leadingCoeff_ne_zero.mpr hp) hxy`.
-/
theorem dixmier_aeval_injective {V : Type} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V)
    (hT : ∀ c : ℂ, Function.Injective ⇑(T - c • (1 : Module.End ℂ V))) (p : ℂ[X]) (hp : p ≠ 0) :
    Function.Injective (aeval T p) := by
  have hs := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := p) IsAlgClosed.card_roots_eq_natDegree
  have hlin : ∀ a : ℂ, aeval T (X - C a) = T - a • 1 := by
    intro a; simp [Algebra.algebraMap_eq_smul_one]
  have key : ∀ m : Multiset ℂ, Function.Injective (aeval T (m.map fun a => X - C a).prod) := by
    intro m
    induction m using Multiset.induction_on with
    | empty =>
      simp only [Multiset.map_zero, Multiset.prod_zero, map_one, Module.End.one_eq_id, LinearMap.id_coe]
      exact Function.injective_id
    | cons a m ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, map_mul, Module.End.mul_eq_comp, LinearMap.coe_comp]
      refine Function.Injective.comp ?_ ih
      rw [hlin]; exact hT a
  rw [← hs, map_mul, Module.End.mul_eq_comp, LinearMap.coe_comp]
  refine Function.Injective.comp ?_ (key _)
  rw [aeval_C, Algebra.algebraMap_eq_smul_one]
  intro x y hxy
  simp only [LinearMap.smul_apply, Module.End.one_apply] at hxy
  exact smul_right_injective V (leadingCoeff_ne_zero.mpr hp) hxy

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hcomm : ∀ c : ℂ, ∀ i, (T - c • 1) * ρ i = ρ i * (T - c • 1)`. Introduce `c i`. Rewrite using `[sub_mul, mul_sub, hT i, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]`.

Establish `hinj : ∀ c : ℂ, Function.Injective ⇑(T - c • (1 : Module.End ℂ V))`. Introduce `c`. Rewrite using `[← LinearMap.ker_eq_bot]`. Break down `hirr (LinearMap.ker (T - c • 1)) (fun i x hx => by` into its components or cases. Rewrite `hx`, the goal using `[LinearMap.mem_ker]`.

Rewrite using `[← Module.End.mul_apply, hcomm c i, Module.End.mul_apply, hx, map_zero]) with h | h`. Conclude with `h`. Conclude with `absurd (sub_eq_zero.mp (LinearMap.ker_eq_top.mp h)) (hne c)`. Choose the witnesses or unpack the hypotheses as in `⟨v₀, hv₀⟩ : ∃ v : V, v ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hne 0 (LinearMap.ext fun v => (h _).trans (h _).symm)`. Establish `hsurj : ∀ c : ℂ, Function.Surjective ⇑(T - c • (1 : Module.End ℂ V))`. Introduce `c`. Rewrite using `[← LinearMap.range_eq_top]`.

Break down `hirr (LinearMap.range (T - c • 1)) (fun i x hx => by` into its components or cases. Take `⟨y, rfl⟩` from `hx`. Conclude with `⟨ρ i y, by rw [← Module.End.mul_apply, hcomm c i, Module.End.mul_apply]⟩) with h | h`. It suffices to derive a contradiction. Establish `h1 : (T - c • 1) v₀ ∈ LinearMap.range (T - c • 1)` using `LinearMap.mem_range_self _ _`.

Rewrite `h1` using `[h, Submodule.mem_bot]`. Conclude with `hv₀ (hinj c (by rw [h1, map_zero]))`. Conclude with `h`. Set `S : ℂ → V ≃ₗ[ℂ] V` to `fun c => LinearEquiv.ofBijective (T - c • 1) ⟨hinj c, hsurj c⟩`. Set `w : ℂ → V` to `fun c => (S c).symm v₀`.

Establish `hw : ∀ c, (T - c • (1 : Module.End ℂ V)) (w c) = v₀` using `fun c => (S c).apply_symm_apply v₀`. Establish `hlin : ∀ a : ℂ, aeval T (X - C a) = T - a • 1`. Introduce `a`. Simplify using `[Algebra.algebraMap_eq_smul_one]`. Establish `hli : LinearIndependent ℂ w`.

Rewrite using `[linearIndependent_iff']`. Introduce `s g hsum i hi`. Set `q : ℂ → ℂ[X]` to `fun c => ∏ d ∈ s.erase c, (X - C d)`. Establish `hq : ∀ c ∈ s, aeval T (∏ d ∈ s, (X - C d)) (w c) = aeval T (q c) v₀`. Introduce `c hc`.

Rewrite using `[← Finset.mul_prod_erase s _ hc, mul_comm, map_mul, Module.End.mul_apply, hlin, hw]`. Establish `h0 : aeval T (∑ c ∈ s, g c • q c) v₀ = 0`. Establish `h2` using `congrArg (aeval T (∏ d ∈ s, (X - C d))) hsum`. Rewrite `h2` using `[map_zero, map_sum]`. Rewrite using `[map_sum, LinearMap.sum_apply, ← h2]`.

Use `Finset.sum_congr rfl fun c hc => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smul, hq c hc, map_smul, LinearMap.smul_apply]`. Establish `hp0 : ∑ c ∈ s, g c • q c = 0`. Assume the negation of the conclusion as `hp`. Conclude with `hv₀ (dixmier_aeval_injective T hinj _ hp (by rw [h0, map_zero]))`.

Establish `h3` using `congrArg (Polynomial.eval i) hp0`. Rewrite `h3` using `[eval_finset_sum, Finset.sum_eq_single i]`. Simplify using `only [eval_smul, q, eval_prod, eval_sub, eval_X, eval_C, smul_eq_mul, eval_zero] at h3`. Break down `mul_eq_zero.mp h3 with h | h` into its components or cases. Conclude with `h`.

It suffices to derive a contradiction. Rewrite `h` using `[Finset.prod_eq_zero_iff]`. Take `⟨d, hd, hd0⟩` from `h`. Conclude with `(Finset.ne_of_mem_erase hd) (sub_eq_zero.mp hd0).symm`. Introduce `c hc hci`.

Simplify using `only [eval_smul, q, eval_prod, eval_sub, eval_X, eval_C, smul_eq_mul]`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hci, hi⟩) (sub_self i), mul_zero]`. Introduce `h`. Conclude with `absurd hi h`. Establish `h4` using `hli.cardinal_le_rank`.

Rewrite `h4` using `[Cardinal.mk_complex]`. Conclude with `absurd (h4.trans hrank) (not_le.mpr Cardinal.aleph0_lt_continuum)`.
-/
theorem dixmier_commutant_scalar (ι V : Type) [AddCommGroup V] [Module ℂ V] (ρ : ι → Module.End ℂ V)
    (hrank : Module.rank ℂ V ≤ Cardinal.aleph0)
    (hirr : ∀ N : Submodule ℂ V, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤)
    (T : Module.End ℂ V) (hT : ∀ i, T * ρ i = ρ i * T) : ∃ c : ℂ, T = c • 1 := by
  by_contra hne
  push_neg at hne
  have hcomm : ∀ c : ℂ, ∀ i, (T - c • 1) * ρ i = ρ i * (T - c • 1) := by
    intro c i; rw [sub_mul, mul_sub, hT i, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have hinj : ∀ c : ℂ, Function.Injective ⇑(T - c • (1 : Module.End ℂ V)) := by
    intro c
    rw [← LinearMap.ker_eq_bot]
    rcases hirr (LinearMap.ker (T - c • 1)) (fun i x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [← Module.End.mul_apply, hcomm c i, Module.End.mul_apply, hx, map_zero]) with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp (LinearMap.ker_eq_top.mp h)) (hne c)
  obtain ⟨v₀, hv₀⟩ : ∃ v : V, v ≠ 0 := by
    by_contra h; push_neg at h
    exact hne 0 (LinearMap.ext fun v => (h _).trans (h _).symm)
  have hsurj : ∀ c : ℂ, Function.Surjective ⇑(T - c • (1 : Module.End ℂ V)) := by
    intro c
    rw [← LinearMap.range_eq_top]
    rcases hirr (LinearMap.range (T - c • 1)) (fun i x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact ⟨ρ i y, by rw [← Module.End.mul_apply, hcomm c i, Module.End.mul_apply]⟩) with h | h
    · exfalso
      have h1 : (T - c • 1) v₀ ∈ LinearMap.range (T - c • 1) := LinearMap.mem_range_self _ _
      rw [h, Submodule.mem_bot] at h1
      exact hv₀ (hinj c (by rw [h1, map_zero]))
    · exact h
  let S : ℂ → V ≃ₗ[ℂ] V := fun c => LinearEquiv.ofBijective (T - c • 1) ⟨hinj c, hsurj c⟩
  let w : ℂ → V := fun c => (S c).symm v₀
  have hw : ∀ c, (T - c • (1 : Module.End ℂ V)) (w c) = v₀ := fun c => (S c).apply_symm_apply v₀
  have hlin : ∀ a : ℂ, aeval T (X - C a) = T - a • 1 := by
    intro a; simp [Algebra.algebraMap_eq_smul_one]
  have hli : LinearIndependent ℂ w := by
    rw [linearIndependent_iff']
    intro s g hsum i hi
    let q : ℂ → ℂ[X] := fun c => ∏ d ∈ s.erase c, (X - C d)
    have hq : ∀ c ∈ s, aeval T (∏ d ∈ s, (X - C d)) (w c) = aeval T (q c) v₀ := by
      intro c hc
      rw [← Finset.mul_prod_erase s _ hc, mul_comm, map_mul, Module.End.mul_apply, hlin, hw]
    have h0 : aeval T (∑ c ∈ s, g c • q c) v₀ = 0 := by
      have h2 := congrArg (aeval T (∏ d ∈ s, (X - C d))) hsum
      rw [map_zero, map_sum] at h2
      rw [map_sum, LinearMap.sum_apply, ← h2]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [LinearMap.map_smul, hq c hc, map_smul, LinearMap.smul_apply]
    have hp0 : ∑ c ∈ s, g c • q c = 0 := by
      by_contra hp
      exact hv₀ (dixmier_aeval_injective T hinj _ hp (by rw [h0, map_zero]))
    have h3 := congrArg (Polynomial.eval i) hp0
    rw [eval_finset_sum, Finset.sum_eq_single i] at h3
    · simp only [eval_smul, q, eval_prod, eval_sub, eval_X, eval_C, smul_eq_mul, eval_zero] at h3
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exfalso
        rw [Finset.prod_eq_zero_iff] at h
        obtain ⟨d, hd, hd0⟩ := h
        exact (Finset.ne_of_mem_erase hd) (sub_eq_zero.mp hd0).symm
    · intro c hc hci
      simp only [eval_smul, q, eval_prod, eval_sub, eval_X, eval_C, smul_eq_mul]
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hci, hi⟩) (sub_self i), mul_zero]
    · intro h; exact absurd hi h
  have h4 := hli.cardinal_le_rank
  rw [Cardinal.mk_complex] at h4
  exact absurd (h4.trans hrank) (not_le.mpr Cardinal.aleph0_lt_continuum)

end

section
open PositivityTheory.KCo GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

/- English proof (translation)
Take `⟨t, rfl⟩` from `Nat.exists_eq_add_of_le hnd`. Establish `hμ : IsSmoothChar ν⁻¹` using `IsSmoothChar.inv hν.2`. Take `⟨E⟩` from `GlobalTheory.T.omega_equiv_induced_fibre k (Fin n) (Fin (n + t)) (Fin n) (Fin t) (stdSum rfl) n (Fintype.card_fin n).symm ν⁻¹ hμ`. Establish `hR : twRel ((omegaOn (Fin n) (Fin (n + t)) ν⁻¹ {n}).comp (MonoidHom.inl _ _)) 1 ≤ (augF n (n + t) ν α).comap extZ` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨g, φ, rfl⟩`.

Use `Submodule.subset_span ⟨g, extZ φ, ⟨extZ_mem φ, fun Y hY => extZ_neg φ (by rwa [rank_transpose])⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.one_apply, Units.val_one, one_smul, map_sub]`. Use `congr 1`. Use `funext fun Y => (extZ_act _ g 1 φ Y).trans ?_` and prove the remaining obligations. Establish `n1 : nabs k 1 = 1` using `by simp [nabs]`.

Simplify using `[omB, omChar, apow, val_absPow, n1])`. Break down `irr_equiv E (irr_ind hB n t hμ (fun y => by simp [hν.1 y])) (N.comap extZ) (hR.trans (Submodule.comap_mono hA)) (by` into its components or cases. Introduce `h φ hf`. Establish `h1` using `hN (invT h) _ hf (extZ_mem φ)`. Rewrite using `[Submodule.mem_comap]`.

Establish `c0 : (α (gdet (invT h)) : ℂ) * apow (gdet (invT h)) ((n : ℂ) / 2) ≠ 0` using `mul_ne_zero (Units.ne_zero _) (Units.ne_zero (absPow k ((n : ℂ) / 2) (gdet (invT h))))`. Use `N.smul_mem ((omChar (Fin n) (Fin (n + t)) ν⁻¹ (1, h) : ℂ) / ((α (gdet (invT h)) : ℂ) * apow (gdet (invT h)) ((n : ℂ) / 2))) h1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `Y`. Establish `e1 : omB ν α 1 (invT h) (extZ φ) Y = (α (gdet (invT h)) : ℂ) * apow (gdet (invT h)) ((n : ℂ) / 2) * extZ φ ((1 : GL (Fin n) k).valᵀ * Y * (invT h).val)`. Simplify using `[omB, apow, nabs]`.

Rewrite using `[extZ_act, Pi.smul_apply, e1, smul_eq_mul, ← mul_assoc, div_mul_cancel₀ _ c0]) with h | h`. Use `Or.inl fun Φ hΦ => ?_` and prove the remaining obligations. Take `⟨φ, rfl⟩` from `exists_extZ hΦ`. Conclude with `(h ▸ Submodule.mem_top : φ ∈ N.comap extZ)`. Use `Or.inr fun Φ hm hΦ => ?_` and prove the remaining obligations.

Take `⟨φ, rfl⟩` from `exists_extZ hΦ`. Conclude with `hR (h hm)`.
-/
theorem irrF' (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) {ν α : kˣ →* ℂˣ} (hnd : n ≤ d) (hν : USm ν)
    (N : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ)) (hA : augF n d ν α ≤ N)
    (hN : ∀ h : GL (Fin d) k, ∀ Φ ∈ N, Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) → omB ν α 1 h Φ ∈ N) :
    (∀ Φ, Full Φ → Φ ∈ N) ∨ ∀ Φ ∈ N, Full Φ → Φ ∈ augF n d ν α := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hnd
  have hμ : IsSmoothChar ν⁻¹ := IsSmoothChar.inv hν.2
  obtain ⟨E⟩ := GlobalTheory.T.omega_equiv_induced_fibre k (Fin n) (Fin (n + t)) (Fin n) (Fin t) (stdSum rfl) n (Fintype.card_fin n).symm ν⁻¹ hμ
  have hR : twRel ((omegaOn (Fin n) (Fin (n + t)) ν⁻¹ {n}).comp (MonoidHom.inl _ _)) 1 ≤
      (augF n (n + t) ν α).comap extZ := Submodule.span_le.2 (by
    rintro _ ⟨g, φ, rfl⟩
    refine Submodule.subset_span ⟨g, extZ φ, ⟨extZ_mem φ, fun Y hY => extZ_neg φ (by rwa [rank_transpose])⟩, ?_⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
    congr 1
    refine funext fun Y => (extZ_act _ g 1 φ Y).trans ?_
    have n1 : nabs k 1 = 1 := by simp [nabs]
    simp [omB, omChar, apow, val_absPow, n1])
  rcases irr_equiv E (irr_ind hB n t hμ (fun y => by simp [hν.1 y])) (N.comap extZ) (hR.trans (Submodule.comap_mono hA)) (by
    intro h φ hf
    have h1 := hN (invT h) _ hf (extZ_mem φ)
    rw [Submodule.mem_comap]
    have c0 : (α (gdet (invT h)) : ℂ) * apow (gdet (invT h)) ((n : ℂ) / 2) ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) (Units.ne_zero (absPow k ((n : ℂ) / 2) (gdet (invT h))))
    convert N.smul_mem ((omChar (Fin n) (Fin (n + t)) ν⁻¹ (1, h) : ℂ) /
      ((α (gdet (invT h)) : ℂ) * apow (gdet (invT h)) ((n : ℂ) / 2))) h1 using 1
    funext Y
    have e1 : omB ν α 1 (invT h) (extZ φ) Y = (α (gdet (invT h)) : ℂ) * apow (gdet (invT h)) ((n : ℂ) / 2) *
        extZ φ ((1 : GL (Fin n) k).valᵀ * Y * (invT h).val) := by
      simp [omB, apow, nabs]
    rw [extZ_act, Pi.smul_apply, e1, smul_eq_mul, ← mul_assoc, div_mul_cancel₀ _ c0]) with h | h
  · refine Or.inl fun Φ hΦ => ?_
    obtain ⟨φ, rfl⟩ := exists_extZ hΦ
    exact (h ▸ Submodule.mem_top : φ ∈ N.comap extZ)
  · refine Or.inr fun Φ hm hΦ => ?_
    obtain ⟨φ, rfl⟩ := exists_extZ hΦ
    exact hR (h hm)

end

/- English proof (translation)
Establish `hc : {K : Set V | IsCompact K ∧ IsOpen K}.Countable`. Use `((Set.countable_setOf_finite_subset (TopologicalSpace.countable_countableBasis V)).image Set.sUnion).mono ?_` and prove the remaining obligations. Introduce and unpack `K ⟨h1, h2⟩`. Take `⟨S, hS, rfl⟩` from `(TopologicalSpace.isBasis_countableBasis V).open_eq_sUnion h2`. Take `⟨T, hT, hf, hcov⟩` from `h1.elim_finite_subcover_image (b := S) (c := id) (fun s hs => (TopologicalSpace.isBasis_countableBasis V).isOpen (hS hs)) (by rw [Set.sUnion_eq_biUnion]; rfl)`.

Use `⟨T, ⟨hf, hT.trans hS⟩, subset_antisymm (Set.sUnion_mono hT) ?_⟩` and prove the remaining obligations. Rewrite using `[Set.sUnion_eq_biUnion (s := T)]`. Conclude with `hcov`. Establish `hle : GlobalTheory.WeilM.SB V ≤ Submodule.span ℂ ((fun K : Set V => K.indicator (1 : V → ℂ)) '' {K | IsCompact K ∧ IsOpen K})`. Introduce `f hf`.

Establish `hfin : (f '' tsupport f).Finite` using `by haveI : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hf.2.isCompact`. Establish `h2` using `(hf.1.comp_continuous (continuous_subtype_val (p := (· ∈ tsupport f)))).range_finite`. Rewrite `h2` using `[Set.range_comp, Subtype.range_coe_subtype, Set.setOf_mem_eq]`. Then use the resulting hypothesis. Establish `e : f = ∑ c ∈ hfin.toFinset.erase 0, c • (f ⁻¹' {c}).indicator (1 : V → ℂ)`. Use function extensionality and compare the values at `y`.

Rewrite using `[Finset.sum_apply, Finset.sum_eq_single (f y)]`. Simplify using the standard rewrite rules. Introduce `c _ hc`. Simplify using `[Set.indicator_apply, hc.symm]`. Introduce `h`.

Establish `: f y = 0`. Assume the negation of the conclusion as `h0`. Conclude with `h (Finset.mem_erase.2 ⟨h0, hfin.mem_toFinset.2 ⟨y, subset_tsupport _ h0, rfl⟩⟩)`. Simplify using `[this]`. Rewrite using `[e]`.

Use `Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨?_, hf.1 _⟩, rfl⟩)` and prove the remaining obligations. Use `hf.2.isCompact.of_isClosed_subset (hf.1.isClopen_fiber c).1 fun y hy => subset_tsupport _ ?_` and prove the remaining obligations. Rewrite using `[Function.mem_support, show f y = c from hy]`. Conclude with `(Finset.mem_erase.1 hc).1`. Conclude with `(Submodule.rank_mono hle).trans ((rank_span_le _).trans (Cardinal.mk_le_aleph0_iff.2 (hc.image _).to_subtype))`.
-/
theorem rank_SB (V : Type) [TopologicalSpace V] [SecondCountableTopology V] [T2Space V] :
    Module.rank ℂ (GlobalTheory.WeilM.SB V) ≤ Cardinal.aleph0 := by
  classical
  have hc : {K : Set V | IsCompact K ∧ IsOpen K}.Countable := by
    refine ((Set.countable_setOf_finite_subset (TopologicalSpace.countable_countableBasis V)).image Set.sUnion).mono ?_
    rintro K ⟨h1, h2⟩
    obtain ⟨S, hS, rfl⟩ := (TopologicalSpace.isBasis_countableBasis V).open_eq_sUnion h2
    obtain ⟨T, hT, hf, hcov⟩ := h1.elim_finite_subcover_image (b := S) (c := id)
      (fun s hs => (TopologicalSpace.isBasis_countableBasis V).isOpen (hS hs)) (by rw [Set.sUnion_eq_biUnion]; rfl)
    refine ⟨T, ⟨hf, hT.trans hS⟩, subset_antisymm (Set.sUnion_mono hT) ?_⟩
    rw [Set.sUnion_eq_biUnion (s := T)]; exact hcov
  have hle : GlobalTheory.WeilM.SB V ≤ Submodule.span ℂ ((fun K : Set V => K.indicator (1 : V → ℂ)) '' {K | IsCompact K ∧ IsOpen K}) := by
    intro f hf
    have hfin : (f '' tsupport f).Finite := by
      haveI : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hf.2.isCompact
      have h2 := (hf.1.comp_continuous (continuous_subtype_val (p := (· ∈ tsupport f)))).range_finite
      rwa [Set.range_comp, Subtype.range_coe_subtype, Set.setOf_mem_eq] at h2
    have e : f = ∑ c ∈ hfin.toFinset.erase 0, c • (f ⁻¹' {c}).indicator (1 : V → ℂ) := by
      funext y
      rw [Finset.sum_apply, Finset.sum_eq_single (f y)]
      · simp
      · intro c _ hc
        simp [Set.indicator_apply, hc.symm]
      · intro h
        have : f y = 0 := by
          by_contra h0
          exact h (Finset.mem_erase.2 ⟨h0, hfin.mem_toFinset.2 ⟨y, subset_tsupport _ h0, rfl⟩⟩)
        simp [this]
    rw [e]
    refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨?_, hf.1 _⟩, rfl⟩)
    refine hf.2.isCompact.of_isClosed_subset (hf.1.isClopen_fiber c).1 fun y hy => subset_tsupport _ ?_
    rw [Function.mem_support, show f y = c from hy]
    exact (Finset.mem_erase.1 hc).1
  exact (Submodule.rank_mono hle).trans ((rank_span_le _).trans (Cardinal.mk_le_aleph0_iff.2 (hc.image _).to_subtype))

end PositivityTheory.ThKG.LocalRamifiedLeviRestriction

import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.CommonField
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SsDescend
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.GrpQuotBc
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

/- English proof (translation)
Establish `h : TwoSidedIdeal.span I ≤ TwoSidedIdeal.comap F (TwoSidedIdeal.span (F '' I))`. Rewrite using `[TwoSidedIdeal.span_le]`. Introduce `a ha`. Conclude with `(TwoSidedIdeal.mem_comap F).2 (TwoSidedIdeal.subset_span ⟨a, ha, rfl⟩)`. Conclude with `(TwoSidedIdeal.mem_comap F).1 (h hx)`.
-/
private theorem span_map_mem {A B : Type} [Ring A] [Ring B] (F : A →+* B) (I : Set A) (x : A)
    (hx : x ∈ TwoSidedIdeal.span I) : F x ∈ TwoSidedIdeal.span (F '' I) := by
  have h : TwoSidedIdeal.span I ≤ TwoSidedIdeal.comap F (TwoSidedIdeal.span (F '' I)) := by
    rw [TwoSidedIdeal.span_le]
    intro a ha
    exact (TwoSidedIdeal.mem_comap F).2 (TwoSidedIdeal.subset_span ⟨a, ha, rfl⟩)
  exact (TwoSidedIdeal.mem_comap F).1 (h hx)

/- English proof (translation)
Take `⟨s, hs⟩` from `hs`. Use `set J := TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G ψ '' I) with hJ`. Set `π : MonoidAlgebra κ G →ₗ[κ] J.ringCon.Quotient` to `{ toFun := J.ringCon.mk' map_add' := fun a b => map_add _ a b map_smul' := fun a b => rfl }`. Establish `hπ : Function.Surjective π` using `J.ringCon.mk'_surjective`. Use `⟨⟨s.image (fun g => π (MonoidAlgebra.single g 1)), ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[eq_top_iff]`. Introduce `z hz`. Use `clear hz`. Take `⟨y, rfl⟩` from `hπ z`. Establish `key : ∀ (g : G) (k : κ), π (MonoidAlgebra.single g k) = k • π (MonoidAlgebra.single g 1)`.

Introduce `g k`. Rewrite using `[← map_smul, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]`. Proceed by induction on `y using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => rw [map_add]`.

Conclude with `Submodule.add_mem _ ha hb`. Consider the case `single g k`. Rewrite using `[key]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `hs (MonoidAlgebra.single g 1)`.

Establish `h1` using `span_map_mem (MonoidAlgebra.mapRingHom G ψ) I _ hc`. Rewrite `h1` using `[map_sub, map_sum]`. Simplify using `only [MonoidAlgebra.mapRingHom_single, map_one] at h1`. Establish `h2 : π (MonoidAlgebra.single g 1) = π (∑ g ∈ s, MonoidAlgebra.single g (ψ (c g)))` using `by show J.ringCon.mk' _ = J.ringCon.mk' _`. Conclude with `J.ringCon.eq.2 ((TwoSidedIdeal.rel_iff J _ _).2 h1)`.

Rewrite using `[h2, map_sum]`. Use `Submodule.sum_mem _ fun a ha => ?_` and prove the remaining obligations. Rewrite using `[key]`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations. Conclude with `Finset.mem_coe.2 (Finset.mem_image.2 ⟨a, ha, rfl⟩)`.
-/
private theorem fin_quot {R κ G : Type} [CommRing R] [Field κ] [Group G] (I : Set (MonoidAlgebra R G))
    (ψ : R →+* κ)
    (hs : ∃ s : Finset G, ∀ y : MonoidAlgebra R G, ∃ c : G → R,
      y - ∑ g ∈ s, MonoidAlgebra.single g (c g) ∈ TwoSidedIdeal.span I) :
    Module.Finite κ (TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G ψ '' I)).ringCon.Quotient := by
  classical
  obtain ⟨s, hs⟩ := hs
  set J := TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G ψ '' I) with hJ
  let π : MonoidAlgebra κ G →ₗ[κ] J.ringCon.Quotient :=
    { toFun := J.ringCon.mk'
      map_add' := fun a b => map_add _ a b
      map_smul' := fun a b => rfl }
  have hπ : Function.Surjective π := J.ringCon.mk'_surjective
  refine ⟨⟨s.image (fun g => π (MonoidAlgebra.single g 1)), ?_⟩⟩
  rw [eq_top_iff]
  intro z hz
  clear hz
  obtain ⟨y, rfl⟩ := hπ z
  have key : ∀ (g : G) (k : κ), π (MonoidAlgebra.single g k) = k • π (MonoidAlgebra.single g 1) := by
    intro g k
    rw [← map_smul, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | single g k =>
    rw [key]
    refine Submodule.smul_mem _ _ ?_
    obtain ⟨c, hc⟩ := hs (MonoidAlgebra.single g 1)
    have h1 := span_map_mem (MonoidAlgebra.mapRingHom G ψ) I _ hc
    rw [map_sub, map_sum] at h1
    simp only [MonoidAlgebra.mapRingHom_single, map_one] at h1
    have h2 : π (MonoidAlgebra.single g 1) = π (∑ g ∈ s, MonoidAlgebra.single g (ψ (c g))) := by
      show J.ringCon.mk' _ = J.ringCon.mk' _
      exact J.ringCon.eq.2 ((TwoSidedIdeal.rel_iff J _ _).2 h1)
    rw [h2, map_sum]
    refine Submodule.sum_mem _ fun a ha => ?_
    rw [key]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨a, ha, rfl⟩)

/- English proof (translation)
Introduce `R S S' G _ _ _ _ I φ φ' Q Q' hQ' hc hs hN`. Take `⟨κ, _, f, hf, hns⟩` from `hN`. Set `f' : S' →+* FractionRing (S' ⧸ Q')` to `(algebraMap (S' ⧸ Q') (FractionRing (S' ⧸ Q'))).comp (Ideal.Quotient.mk Q')`. Establish `hf' : RingHom.ker f' = Q'`. Rewrite using `[RingHom.ker_comp_of_injective _ (IsFractionRing.injective _ _), Ideal.mk_ker]`.

Establish `hk : RingHom.ker (f.comp φ) = RingHom.ker (f'.comp φ')`. Rewrite using `[← RingHom.comap_ker, ← RingHom.comap_ker, hf, hf', hc]`. Take `⟨K, _, j₁, j₂, hj⟩` from `UpperTheory.V.Pa.BC.common_field R κ _ _ _ hk`. Use `⟨K, inferInstance, j₂.comp f', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.ker_comp_of_injective _ j₂.injective, hf']`.

Introduce `hss`. Apply `hns` to reduce the goal to its premises. Use `letI : Algebra κ K := j₁.toAlgebra`. Use `haveI := fin_quot I (f.comp φ) hs`. Take `⟨e⟩` from `UpperTheory.V.Pa.BC.grp_quot_bc κ K G (MonoidAlgebra.mapRingHom G (f.comp φ) '' I)`.

Establish `him : MonoidAlgebra.mapRingHom G (algebraMap κ K) '' (MonoidAlgebra.mapRingHom G (f.comp φ) '' I) = MonoidAlgebra.mapRingHom G ((j₂.comp f').comp φ') '' I`. Rewrite using `[RingHom.comp_assoc, ← hj, MonoidAlgebra.mapRingHom_comp j₁, RingHom.coe_comp, Set.image_comp]`. Both sides reduce to the same expression. Rewrite `hss` using `[← him]`. Conclude with `UpperTheory.V.Pa.BC.ss_descend κ K _ e.symm.isSemisimpleRing`.
-/
theorem UpperTheory.V.Pa.BC.nonSS_field :
    ∀ (R S S' G : Type) [CommRing R] [CommRing S] [CommRing S'] [Group G] (I : Set (MonoidAlgebra R G)) (φ : R →+* S) (φ' : R →+* S') (Q : Ideal S) (Q' : Ideal S'), Q'.IsPrime → Q'.comap φ' = Q.comap φ → (∃ s : Finset G, ∀ y : MonoidAlgebra R G, ∃ c : G → R, y - ∑ g ∈ s, MonoidAlgebra.single g (c g) ∈ TwoSidedIdeal.span I) → NonSS I φ Q → NonSS I φ' Q' := by
  intro R S S' G _ _ _ _ I φ φ' Q Q' hQ' hc hs hN
  obtain ⟨κ, _, f, hf, hns⟩ := hN
  let f' : S' →+* FractionRing (S' ⧸ Q') :=
    (algebraMap (S' ⧸ Q') (FractionRing (S' ⧸ Q'))).comp (Ideal.Quotient.mk Q')
  have hf' : RingHom.ker f' = Q' := by
    rw [RingHom.ker_comp_of_injective _ (IsFractionRing.injective _ _), Ideal.mk_ker]
  have hk : RingHom.ker (f.comp φ) = RingHom.ker (f'.comp φ') := by
    rw [← RingHom.comap_ker, ← RingHom.comap_ker, hf, hf', hc]
  obtain ⟨K, _, j₁, j₂, hj⟩ := UpperTheory.V.Pa.BC.common_field R κ _ _ _ hk
  refine ⟨K, inferInstance, j₂.comp f', ?_, ?_⟩
  · rw [RingHom.ker_comp_of_injective _ j₂.injective, hf']
  · intro hss
    apply hns
    letI : Algebra κ K := j₁.toAlgebra
    haveI := fin_quot I (f.comp φ) hs
    obtain ⟨e⟩ := UpperTheory.V.Pa.BC.grp_quot_bc κ K G (MonoidAlgebra.mapRingHom G (f.comp φ) '' I)
    have him : MonoidAlgebra.mapRingHom G (algebraMap κ K) '' (MonoidAlgebra.mapRingHom G (f.comp φ) '' I)
        = MonoidAlgebra.mapRingHom G ((j₂.comp f').comp φ') '' I := by
      rw [RingHom.comp_assoc, ← hj, MonoidAlgebra.mapRingHom_comp j₁, RingHom.coe_comp, Set.image_comp]
      rfl
    rw [← him] at hss
    exact UpperTheory.V.Pa.BC.ss_descend κ K _ e.symm.isSemisimpleRing

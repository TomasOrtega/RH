import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatCokerOfInjectiveModMaximalIdeal
open IsLocalRing TensorProduct

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[← Submodule.range_mkQ J, LinearMap.range_eq_map, ← Submodule.map_smul'', ← Submodule.mem_comap, Submodule.comap_map_mkQ, smul_eq_mul, Ideal.mul_top]`.
-/
theorem mkQ_mem_smul_top_iff_mem_sup {A : Type} [CommRing A] (J I : Ideal A) (a : A) :
    Submodule.mkQ J a ∈ (I • ⊤ : Submodule A (A ⧸ J)) ↔ a ∈ J ⊔ I := by
  rw [← Submodule.range_mkQ J, LinearMap.range_eq_map, ← Submodule.map_smul'',
    ← Submodule.mem_comap, Submodule.comap_map_mkQ, smul_eq_mul, Ideal.mul_top]

/- English proof (translation)
Set `u : (A ⧸ J) →ₗ[A] (A ⧸ J)` to `LinearMap.lsmul A (A ⧸ J) r`. Establish `h` using `flat_coker_of_injective_mod_maximalIdeal V A (A ⧸ J) (A ⧸ J) u (by`. Introduce `x hx`. Take `⟨a, rfl⟩` from `Submodule.mkQ_surjective J x`. Rewrite using `[mkQ_mem_smul_top_iff_mem_sup]`.

Apply `hr` to reduce the goal to its premises. Rewrite using `[← mkQ_mem_smul_top_iff_mem_sup]`. Conclude with `hx)`. Establish `hu : LinearMap.range u = Submodule.map (Submodule.mkQ J) (Ideal.span {r})`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Take `⟨a, rfl⟩` from `Submodule.mkQ_surjective J y`. Conclude with `⟨r * a, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self r), rfl⟩`. Introduce and unpack `⟨b, hb, rfl⟩`.

Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton.1 hb`. Conclude with `⟨Submodule.mkQ J a, rfl⟩`. Set `e : ((A ⧸ J) ⧸ LinearMap.range u) ≃ₗ[A] (A ⧸ (J ⊔ Ideal.span {r}))` to `(Submodule.quotEquivOfEq _ _ hu).trans (Submodule.quotientQuotientEquivQuotientSup J (Ideal.span {r}))`. Conclude with `Module.Flat.of_linearEquiv (e.restrictScalars V).symm`.
-/
theorem flat_quotient_sup_span_singleton (V A : Type) [CommRing V] [IsNoetherianRing V]
    [IsLocalRing V] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra V A]
    [IsLocalHom (algebraMap V A)] (J : Ideal A) [Module.Flat V (A ⧸ J)] (r : A)
    (hr : ∀ a : A, r * a ∈ J ⊔ (maximalIdeal V).map (algebraMap V A) →
      a ∈ J ⊔ (maximalIdeal V).map (algebraMap V A)) :
    Module.Flat V (A ⧸ (J ⊔ Ideal.span {r})) := by
  let u : (A ⧸ J) →ₗ[A] (A ⧸ J) := LinearMap.lsmul A (A ⧸ J) r
  have h := flat_coker_of_injective_mod_maximalIdeal V A (A ⧸ J) (A ⧸ J) u (by
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective J x
    rw [mkQ_mem_smul_top_iff_mem_sup]
    apply hr
    rw [← mkQ_mem_smul_top_iff_mem_sup]
    exact hx)
  have hu : LinearMap.range u = Submodule.map (Submodule.mkQ J) (Ideal.span {r}) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective J y
      exact ⟨r * a, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self r), rfl⟩
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.1 hb
      exact ⟨Submodule.mkQ J a, rfl⟩
  let e : ((A ⧸ J) ⧸ LinearMap.range u) ≃ₗ[A] (A ⧸ (J ⊔ Ideal.span {r})) :=
    (Submodule.quotEquivOfEq _ _ hu).trans
      (Submodule.quotientQuotientEquivQuotientSup J (Ideal.span {r}))
  exact Module.Flat.of_linearEquiv (e.restrictScalars V).symm

/- English proof (translation)
Rewrite `ha`, the goal using `[sup_comm, ← mkQ_mem_smul_top_iff_mem_sup, ← Submodule.Quotient.mk_eq_zero]`. Apply `h` to reduce the goal to its premises. Simplify using `only [smul_zero]`. Conclude with `ha`.
-/
theorem mem_sup_of_isSMulRegular_quotient_quotient {A : Type} [CommRing A] (I J : Ideal A) (r : A)
    (h : IsSMulRegular ((A ⧸ I) ⧸ (J • ⊤ : Submodule A (A ⧸ I))) r) (a : A)
    (ha : r * a ∈ J ⊔ I) : a ∈ J ⊔ I := by
  rw [sup_comm, ← mkQ_mem_smul_top_iff_mem_sup, ← Submodule.Quotient.mk_eq_zero] at ha ⊢
  apply h
  simp only [smul_zero]
  exact ha

/- English proof (translation)
Introduce `V A _ _ _ _ _ _ _ _ _ rs _ hreg`. Establish `key : ∀ i, i ≤ rs.length → Module.Flat V (A ⧸ Ideal.ofList (rs.take i))`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`.

Introduce `_`. Rewrite using `[List.take_zero, Ideal.ofList_nil]`. Conclude with `Module.Flat.of_linearEquiv ((Submodule.quotEquivOfEqBot (⊥ : Ideal A) rfl).restrictScalars V)`. Consider the case `succ i ih`. Introduce `hi`.

Establish `hi' : i < rs.length` using `hi`. Use `haveI := ih hi'.le`. Rewrite using `[List.take_succ_eq_append_getElem hi', Ideal.ofList_append, Ideal.ofList_singleton]`. Conclude with `flat_quotient_sup_span_singleton V A _ _ (mem_sup_of_isSMulRegular_quotient_quotient _ _ _ (hreg.regular_mod_prev i hi'))`. Establish `h` using `key rs.length le_rfl`.

Rewrite `h` using `[List.take_length]`. Then use the resulting hypothesis.
-/
theorem flat_quotient_ofList_of_isWeaklyRegular_closedFibre : ∀ (V A : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra V A] [IsLocalHom (algebraMap V A)] [Module.Flat V A] (rs : List A), (∀ r ∈ rs, r ∈ maximalIdeal A) → RingTheory.Sequence.IsWeaklyRegular (A ⧸ (maximalIdeal V).map (algebraMap V A)) rs → Module.Flat V (A ⧸ Ideal.ofList rs) := by
  intro V A _ _ _ _ _ _ _ _ _ rs _ hreg
  have key : ∀ i, i ≤ rs.length → Module.Flat V (A ⧸ Ideal.ofList (rs.take i)) := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [List.take_zero, Ideal.ofList_nil]
      exact Module.Flat.of_linearEquiv
        ((Submodule.quotEquivOfEqBot (⊥ : Ideal A) rfl).restrictScalars V)
    | succ i ih =>
      intro hi
      have hi' : i < rs.length := hi
      haveI := ih hi'.le
      rw [List.take_succ_eq_append_getElem hi', Ideal.ofList_append, Ideal.ofList_singleton]
      exact flat_quotient_sup_span_singleton V A _ _
        (mem_sup_of_isSMulRegular_quotient_quotient _ _ _ (hreg.regular_mod_prev i hi'))
  have h := key rs.length le_rfl
  rwa [List.take_length] at h

end GlobalTheory

import Mathlib

open TensorProduct in
/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Proceed by induction. Treat this case separately.

Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Treat this case separately.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
private theorem precomplete_of_finite {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨z, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r x =>
    obtain ⟨c, rfl⟩ := AdicCompletion.of_surjective I R r
    refine ⟨c • x, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
    exact (algebraMap_smul (AdicCompletion I R) c (AdicCompletion.of I M x)).symm
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩

open Polynomial in
/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Take a linear combination of the given relations to obtain the conclusion.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
private theorem lift_idem {T : Type} [CommRing T] (I : Ideal T) [HenselianRing T I]
    (f : T ⧸ I) (hf : IsIdempotentElem f) :
    ∃ e : T, IsIdempotentElem e ∧ Ideal.Quotient.mk I e = f := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective f
  have hm : (X ^ 2 - X : T[X]).Monic := by
    nontriviality T
    apply monic_X_pow_sub
    simp
  have hf' : Ideal.Quotient.mk I a * Ideal.Quotient.mk I a = Ideal.Quotient.mk I a := hf
  obtain ⟨e, he, hea⟩ := HenselianRing.is_henselian (I := I) (X ^ 2 - X : T[X]) hm a
    (by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp only [eval_sub, eval_pow, eval_X, map_sub, pow_two, map_mul, eval_mul]
      rw [hf', sub_self])
    (by
      have h : eval a (derivative (X ^ 2 - X : T[X])) = 2 * a - 1 := by
        simp
        ring
      rw [h, map_sub, map_mul, map_one, map_ofNat]
      refine IsUnit.of_mul_eq_one (2 * Ideal.Quotient.mk I a - 1) ?_
      linear_combination 4 * hf')
  refine ⟨e, ?_, Ideal.Quotient.eq.mpr hea⟩
  have : e ^ 2 - e = 0 := by simpa using he
  show e * e = e
  linear_combination this

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
private theorem artin_idem {A : Type} [CommRing A] [IsArtinianRing A] (J : Ideal A) :
    ∃ (e : A) (n : ℕ), IsIdempotentElem e ∧ 1 - e ∈ J ∧ ∀ x ∈ J, x ^ n * e = 0 := by
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes (R := A) (M := A)
    ⟨fun n => OrderDual.toDual (J ^ n), fun _ _ h => Ideal.pow_le_pow_right h⟩
  have h1 : J ^ n = J ^ (n + 1) := hn (n + 1) (by omega)
  have h2 : J ^ n = J ^ (n + n) := hn (n + n) (by omega)
  have hid : IsIdempotentElem (J ^ n) := by
    show J ^ n * J ^ n = J ^ n
    rw [← pow_add, ← h2]
  obtain ⟨f, hf, hJ⟩ := (Ideal.isIdempotentElem_iff_of_fg _ (IsNoetherian.noetherian _)).mp hid
  refine ⟨1 - f, n, hf.one_sub, ?_, ?_⟩
  · have : f ∈ J ^ (n + 1) := by
      rw [← h1, hJ]
      exact Submodule.mem_span_singleton_self f
    simpa using Ideal.pow_le_self (by omega) this
  · intro x hx
    have : x ^ n ∈ J ^ n := Ideal.pow_mem_pow hx n
    rw [hJ] at this
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
    have hf' : f * f = f := hf
    rw [← hc, smul_eq_mul]
    linear_combination (-c) * hf'

/- English proof (translation)
Establish an intermediate fact. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Treat this case separately.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem exists_scalar {Λ T : Type} [CommRing Λ] [CommRing T] [Algebra Λ T]
    {ι : Type} (t : ι → T) (a : ι → Λ) (h : Algebra.adjoin Λ (Set.range t) = ⊤) (J : Ideal T)
    (hJ : ∀ i, t i - algebraMap Λ T (a i) ∈ J) (s : T) :
    ∃ c : Λ, s - algebraMap Λ T c ∈ J := by
  have hs : s ∈ Algebra.adjoin Λ (Set.range t) := h ▸ Algebra.mem_top
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨a i, hJ i⟩
  | algebraMap r => exact ⟨r, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    refine ⟨c + d, ?_⟩
    have := J.add_mem hc hd
    convert this using 1
    rw [map_add]; ring
  | mul x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    refine ⟨c * d, ?_⟩
    have := J.add_mem (J.mul_mem_right y hc) (J.mul_mem_left (algebraMap Λ T c) hd)
    convert this using 1
    rw [map_mul]; ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. It suffices to derive a contradiction. Establish an intermediate fact. Establish an intermediate fact.

A detailed English derivation is pending.
-/
private theorem maximal_of_scalar {Λ T : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing T]
    [Algebra Λ T] (J : Ideal T) (hne : J ≠ ⊤)
    (hm : Ideal.map (algebraMap Λ T) (IsLocalRing.maximalIdeal Λ) ≤ J)
    (hs : ∀ s : T, ∃ c : Λ, s - algebraMap Λ T c ∈ J) : J.IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h => hne ((Ideal.eq_top_iff_one J).mpr h), fun K x hJK hxJ hxK => ?_⟩
  obtain ⟨c, hc⟩ := hs x
  by_cases hu : IsUnit c
  · have h1 : algebraMap Λ T c ∈ K := by
      have := K.sub_mem hxK (hJK hc)
      simpa using this
    exact (Ideal.eq_top_iff_one K).mp (K.eq_top_of_isUnit_mem h1 (hu.map _))
  · exfalso
    have h1 : algebraMap Λ T c ∈ J := hm (Ideal.mem_map_of_mem _ hu)
    have := J.add_mem hc h1
    exact hxJ (by simpa using this)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Supply the required witnesses or components.

Establish an intermediate fact. Equip the data with the indicated structure. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.Qe2.locAbs :
    ∀ (Λ T : Type) [inst : CommRing Λ] [inst_1 : IsLocalRing Λ] [IsNoetherianRing Λ]
    [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ] [inst_4 : CommRing T] [inst_5 : Algebra Λ T] [Module.Finite Λ T]
    (ι : Type) (t : ι → T) (a : ι → Λ),
    Algebra.adjoin Λ (Set.range t) = ⊤ →
      ∃ (e : T),
        IsIdempotentElem e ∧
          (∀ (i : ι),
              ∃ (n : ℕ),
                (t i - (Algebra.algebraMap Λ T : Λ → T) (a i)) ^ n * e ∈
                  Ideal.map (Algebra.algebraMap Λ T) (IsLocalRing.maximalIdeal Λ)) ∧
            (1 : T) - e ∈
                Ideal.map (Algebra.algebraMap Λ T) (IsLocalRing.maximalIdeal Λ) ⊔
                  Ideal.span (Set.range fun (i : ι) ↦ t i - (Algebra.algebraMap Λ T : Λ → T) (a i)) ∧
              (∀ (s : T),
                  ∃ (c : Λ),
                    s - (Algebra.algebraMap Λ T : Λ → T) c ∈
                      Ideal.map (Algebra.algebraMap Λ T) (IsLocalRing.maximalIdeal Λ) ⊔
                        Ideal.span (Set.range fun (i : ι) ↦ t i - (Algebra.algebraMap Λ T : Λ → T) (a i))) ∧
                (e ≠ (0 : T) →
                  (Ideal.map (Algebra.algebraMap Λ T) (IsLocalRing.maximalIdeal Λ) ⊔
                      Ideal.span (Set.range fun (i : ι) ↦ t i - (Algebra.algebraMap Λ T : Λ → T) (a i))).IsMaximal) := by
  intro Λ T _ _ _ _ _ _ _ ι t a h
  set I : Ideal T := Ideal.map (algebraMap Λ T) (IsLocalRing.maximalIdeal Λ) with hI
  set J : Ideal T := I ⊔ Ideal.span (Set.range fun i : ι ↦ t i - algebraMap Λ T (a i)) with hJ
  have hmem : ∀ i, t i - algebraMap Λ T (a i) ∈ J := fun i =>
    Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
  have hs := exists_scalar t a h J hmem
  by_cases htop : J = ⊤
  · exact ⟨0, IsIdempotentElem.zero, fun i => ⟨0, by simp⟩, by simp [htop], hs,
      fun h0 => absurd rfl h0⟩
  have hmax : J.IsMaximal := maximal_of_scalar J htop le_sup_left hs
  haveI : IsPrecomplete (IsLocalRing.maximalIdeal Λ) T := precomplete_of_finite _ T
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal Λ) T := {}
  haveI : IsAdicComplete I T := (IsAdicComplete.map_algebraMap_iff _ _).mpr this
  haveI : IsArtinianRing (T ⧸ I) := by
    letI : Field (Λ ⧸ IsLocalRing.maximalIdeal Λ) := Ideal.Quotient.field _
    haveI : Module.Finite (Λ ⧸ IsLocalRing.maximalIdeal Λ) (T ⧸ I) :=
      Module.Finite.of_restrictScalars_finite Λ _ _
    exact IsArtinianRing.of_finite (Λ ⧸ IsLocalRing.maximalIdeal Λ) (T ⧸ I)
  obtain ⟨f, n, hf, hfJ, hfn⟩ := artin_idem (J.map (Ideal.Quotient.mk I))
  obtain ⟨e, he, rfl⟩ := lift_idem I f hf
  refine ⟨e, he, fun i => ⟨n, ?_⟩, ?_, hs, fun _ => hmax⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow]
    exact hfn _ (Ideal.mem_map_of_mem _ (hmem i))
  · have h1 : Ideal.Quotient.mk I (1 - e) ∈ J.map (Ideal.Quotient.mk I) := by
      rwa [map_sub, map_one]
    have h2 := Ideal.mem_quotient_iff_mem (I := I) (J := J) le_sup_left (x := 1 - e)
    exact h2.mp h1

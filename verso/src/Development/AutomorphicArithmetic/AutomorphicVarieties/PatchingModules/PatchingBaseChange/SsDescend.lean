import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

/- English proof (translation)
Take `⟨C, hC⟩` from `exists_isCompl L`. Establish `h1 : (1 : R) ∈ L ⊔ C` using `by rw [hC.sup_eq_top]; trivial`. Take `⟨e, he, f, hf, hef⟩` from `Submodule.mem_sup.mp h1`. Establish `key : ∀ l ∈ L, l * f = 0`. Introduce `l hl`.

Establish `hl1 : l * e ∈ L` using `L.smul_mem l he`. Establish `hl2 : l * f ∈ C` using `C.smul_mem l hf`. Establish `hsub : l * f = l - l * e`. Rewrite using `[eq_sub_iff_add_eq, add_comm, ← mul_add, hef, mul_one]`. Establish `hL : l * f ∈ L` using `by rw [hsub]; exact L.sub_mem hl hl1`.

Conclude with `(Submodule.disjoint_def.mp hC.disjoint) _ hL hl2`. Establish `hee : IsIdempotentElem e` using `by show e * e = e`. Combine the equalities or inequalities in the displayed calculation. Establish `he0 : e = 0` using `hee.eq_zero_of_isNilpotent (h e he)`. Rewrite using `[eq_bot_iff]`.

Introduce `l hl`. Establish `hl' : l = l * e + l * f` using `by rw [← mul_add, hef, mul_one]`. Rewrite using `[Submodule.mem_bot, hl', key l hl, he0, mul_zero, add_zero]`.
-/
private theorem eq_bot_of_forall_isNilpotent_of_isSemisimple {R : Type*} [Ring R] [IsSemisimpleRing R] (L : Submodule R R)
    (h : ∀ z ∈ L, IsNilpotent z) : L = ⊥ := by
  obtain ⟨C, hC⟩ := exists_isCompl L
  have h1 : (1 : R) ∈ L ⊔ C := by rw [hC.sup_eq_top]; trivial
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.mp h1
  have key : ∀ l ∈ L, l * f = 0 := by
    intro l hl
    have hl1 : l * e ∈ L := L.smul_mem l he
    have hl2 : l * f ∈ C := C.smul_mem l hf
    have hsub : l * f = l - l * e := by
      rw [eq_sub_iff_add_eq, add_comm, ← mul_add, hef, mul_one]
    have hL : l * f ∈ L := by rw [hsub]; exact L.sub_mem hl hl1
    exact (Submodule.disjoint_def.mp hC.disjoint) _ hL hl2
  have hee : IsIdempotentElem e := by
    show e * e = e
    calc e * e = e * (e + f) := by rw [mul_add, key e he, add_zero]
      _ = e := by rw [hef, mul_one]
  have he0 : e = 0 := hee.eq_zero_of_isNilpotent (h e he)
  rw [eq_bot_iff]
  intro l hl
  have hl' : l = l * e + l * f := by rw [← mul_add, hef, mul_one]
  rw [Submodule.mem_bot, hl', key l hl, he0, mul_zero, add_zero]

/- English proof (translation)
Introduce `κ κ' E _ _ _ _ _ _ hT`. Use `haveI : IsArtinianRing E := IsArtinianRing.of_finite κ E`. Rewrite using `[IsArtinianRing.isSemisimpleRing_iff_jacobson, eq_bot_iff]`. Introduce `x hx`. Rewrite using `[Submodule.mem_bot]`.

Take `⟨n, hn⟩` from `IsSemiprimaryRing.isNilpotent (R := E)`. Use `set J := Ring.jacobson E with hJ`. Set `S : ℕ → Submodule κ (κ' ⊗[κ] E)` to `fun k => Submodule.span κ {z | ∃ c : κ', ∃ a ∈ J ^ k, z = c ⊗ₜ[κ] a}`. Establish `hgen : ∀ k (c : κ') (a : E), a ∈ J ^ k → c ⊗ₜ[κ] a ∈ S k` using `fun k c a ha => Submodule.subset_span ⟨c, a, ha, rfl⟩`. Establish `hmul : ∀ a (z w : κ' ⊗[κ] E), z ∈ S a → w ∈ S 1 → z * w ∈ S (a + 1)`.

Introduce `a z w hz hw`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w hw`.

Take `⟨c, u, hu, rfl⟩` from `hz`. Take `⟨c', v, hv, rfl⟩` from `hw`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul]`. Use `hgen _ _ _ ?_` and prove the remaining obligations. Rewrite using `[Submodule.pow_succ]`.

Rewrite `hv` using `[Submodule.pow_one]`. Conclude with `Ideal.mul_mem_mul hu hv`. Consider the case `zero => rw [mul_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add w₁ w₂ _ _ h₁ h₂ => rw [mul_add]`.

Conclude with `Submodule.add_mem _ h₁ h₂`. Consider the case `smul r w _ h => rw [mul_smul_comm]`. Conclude with `Submodule.smul_mem _ r h`. Consider the case `zero => rw [zero_mul]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add z₁ z₂ _ _ h₁ h₂ => rw [add_mul]`. Conclude with `Submodule.add_mem _ h₁ h₂`. Consider the case `smul r z _ h => rw [smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ r h`. Establish `hbot : S n = ⊥`.

Rewrite using `[eq_bot_iff, Submodule.span_le]`. Introduce and unpack `z ⟨c, a, ha, rfl⟩`. Rewrite `ha` using `[hn, Ideal.zero_eq_bot, Submodule.mem_bot]`. Use `show _ ∈ (⊥ : Submodule κ (κ' ⊗[κ] E))`. Rewrite using `[Submodule.mem_bot, ha, TensorProduct.tmul_zero]`.

Establish `h1 : ∀ t : κ' ⊗[κ] E, t * ((1 : κ') ⊗ₜ[κ] x) ∈ S 1`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => rw [zero_mul]`. Conclude with `Submodule.zero_mem _`.

Consider the case `tmul c a`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one]`. Use `hgen 1 c _ ?_` and prove the remaining obligations. Rewrite using `[Submodule.pow_one]`. Conclude with `J.mul_mem_left a hx`.

Consider the case `add t₁ t₂ h₁ h₂ => rw [add_mul]`. Conclude with `Submodule.add_mem _ h₁ h₂`. Establish `hpow : ∀ z ∈ S 1, ∀ k, z ^ k ∈ S k`. Introduce `z hz k`. Proceed by induction on `k with`.

Consider the case `zero`. Rewrite using `[pow_zero, Algebra.TensorProduct.one_def]`. Conclude with `hgen 0 1 1 (Submodule.one_le.mp fun _ h => h)`. Consider the case `succ k ih => rw [pow_succ]`. Conclude with `hmul k _ _ ih hz`.

Establish `hL : Submodule.span (κ' ⊗[κ] E) {(1 : κ') ⊗ₜ[κ] x} = ⊥`. Apply `eq_bot_of_forall_isNilpotent_of_isSemisimple` to reduce the goal to its premises. Introduce `z hz`. Take `⟨t, rfl⟩` from `Submodule.mem_span_singleton.mp hz`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Establish `hz'` using `hpow _ (h1 t) n`. Rewrite `hz'` using `[hbot, Submodule.mem_bot]`. Rewrite using `[smul_eq_mul]`. Conclude with `hz'`. Establish `hy : (1 : κ') ⊗ₜ[κ] x = 0`.

Establish `hm : (1 : κ') ⊗ₜ[κ] x ∈ Submodule.span (κ' ⊗[κ] E) {(1 : κ') ⊗ₜ[κ] x}` using `Submodule.mem_span_singleton_self _`. Rewrite `hm` using `[hL, Submodule.mem_bot]`. Conclude with `hm`. Apply `Algebra.TensorProduct.includeRight_injective (R := κ) (A := κ') (B := E) (algebraMap κ κ').injective` to reduce the goal to its premises. Rewrite using `[Algebra.TensorProduct.includeRight_apply, map_zero, hy]`.
-/
theorem UpperTheory.V.Pa.BC.ss_descend :
    ∀ (κ κ' E : Type) [Field κ] [Field κ'] [Algebra κ κ'] [Ring E] [Algebra κ E] [Module.Finite κ E], IsSemisimpleRing (κ' ⊗[κ] E) → IsSemisimpleRing E := by
  intro κ κ' E _ _ _ _ _ _ hT
  haveI : IsArtinianRing E := IsArtinianRing.of_finite κ E
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson, eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  obtain ⟨n, hn⟩ := IsSemiprimaryRing.isNilpotent (R := E)
  set J := Ring.jacobson E with hJ
  let S : ℕ → Submodule κ (κ' ⊗[κ] E) := fun k =>
    Submodule.span κ {z | ∃ c : κ', ∃ a ∈ J ^ k, z = c ⊗ₜ[κ] a}
  have hgen : ∀ k (c : κ') (a : E), a ∈ J ^ k → c ⊗ₜ[κ] a ∈ S k :=
    fun k c a ha => Submodule.subset_span ⟨c, a, ha, rfl⟩
  have hmul : ∀ a (z w : κ' ⊗[κ] E), z ∈ S a → w ∈ S 1 → z * w ∈ S (a + 1) := by
    intro a z w hz hw
    induction hz using Submodule.span_induction with
    | mem z hz =>
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨c, u, hu, rfl⟩ := hz
        obtain ⟨c', v, hv, rfl⟩ := hw
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        refine hgen _ _ _ ?_
        rw [Submodule.pow_succ]
        rw [Submodule.pow_one] at hv
        exact Ideal.mul_mem_mul hu hv
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add w₁ w₂ _ _ h₁ h₂ => rw [mul_add]; exact Submodule.add_mem _ h₁ h₂
      | smul r w _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ r h
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add z₁ z₂ _ _ h₁ h₂ => rw [add_mul]; exact Submodule.add_mem _ h₁ h₂
    | smul r z _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r h
  have hbot : S n = ⊥ := by
    rw [eq_bot_iff, Submodule.span_le]
    rintro z ⟨c, a, ha, rfl⟩
    rw [hn, Ideal.zero_eq_bot, Submodule.mem_bot] at ha
    show _ ∈ (⊥ : Submodule κ (κ' ⊗[κ] E))
    rw [Submodule.mem_bot, ha, TensorProduct.tmul_zero]
  have h1 : ∀ t : κ' ⊗[κ] E, t * ((1 : κ') ⊗ₜ[κ] x) ∈ S 1 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | tmul c a =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      refine hgen 1 c _ ?_
      rw [Submodule.pow_one]
      exact J.mul_mem_left a hx
    | add t₁ t₂ h₁ h₂ => rw [add_mul]; exact Submodule.add_mem _ h₁ h₂
  have hpow : ∀ z ∈ S 1, ∀ k, z ^ k ∈ S k := by
    intro z hz k
    induction k with
    | zero =>
      rw [pow_zero, Algebra.TensorProduct.one_def]
      exact hgen 0 1 1 (Submodule.one_le.mp fun _ h => h)
    | succ k ih => rw [pow_succ]; exact hmul k _ _ ih hz
  have hL : Submodule.span (κ' ⊗[κ] E) {(1 : κ') ⊗ₜ[κ] x} = ⊥ := by
    apply eq_bot_of_forall_isNilpotent_of_isSemisimple
    intro z hz
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
    refine ⟨n, ?_⟩
    have hz' := hpow _ (h1 t) n
    rw [hbot, Submodule.mem_bot] at hz'
    rw [smul_eq_mul]
    exact hz'
  have hy : (1 : κ') ⊗ₜ[κ] x = 0 := by
    have hm : (1 : κ') ⊗ₜ[κ] x ∈ Submodule.span (κ' ⊗[κ] E) {(1 : κ') ⊗ₜ[κ] x} :=
      Submodule.mem_span_singleton_self _
    rw [hL, Submodule.mem_bot] at hm
    exact hm
  apply Algebra.TensorProduct.includeRight_injective (R := κ) (A := κ') (B := E)
    (algebraMap κ κ').injective
  rw [Algebra.TensorProduct.includeRight_apply, map_zero, hy]

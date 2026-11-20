import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

/- English proof (translation)
Rewrite `hj` using `[← Ideal.jacobson_bot, Ideal.mem_jacobson_iff]`. Take `⟨z, hz⟩` from `hj (-1)`. Rewrite `hz` using `[Ideal.mem_bot]`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero, ← hz]`.

Use `noncomm_ring`.
-/
private theorem dli_left_inv {E : Type} [Ring E] {j : E} (hj : j ∈ Ring.jacobson E) :
    ∃ z : E, z * (1 - j) = 1 := by
  rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff] at hj
  obtain ⟨z, hz⟩ := hj (-1)
  rw [Ideal.mem_bot] at hz
  refine ⟨z, ?_⟩
  rw [← sub_eq_zero, ← hz]
  noncomm_ring

/- English proof (translation)
Take `⟨z, hz⟩` from `dli_left_inv hj`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem dli_idem_zero {E : Type} [Ring E] {u : E} (hu : IsIdempotentElem u)
    (hj : u ∈ Ring.jacobson E) : u = 0 := by
  obtain ⟨z, hz⟩ := dli_left_inv hj
  calc u = z * (1 - u) * u := by rw [hz, one_mul]
    _ = 0 := by rw [mul_assoc, sub_mul, one_mul, hu.eq, sub_self, mul_zero]

/- English proof (translation)
Assume the negation of the conclusion as `hyM`. Take `⟨b, m, hm, hbm⟩` from `hM.exists_inv hyM`. Establish `h1 : ι (b * y) ∈ Ring.jacobson E`. Rewrite using `[map_mul]`. Conclude with `Ideal.mul_mem_left _ _ hy`.

Take `⟨z, hz⟩` from `dli_left_inv h1`. Establish `hm' : 1 - ι (b * y) = ι m`. Rewrite using `[← map_one ι, ← map_sub, ← hbm]`. Simplify using the standard rewrite rules. Rewrite `hz` using `[hm']`.

Take `⟨p, hp, hp0⟩` from `Algebra.IsIntegral.isIntegral (R := A) z`. Establish `hpow : ∀ i : ℕ, z ^ i * ι m ^ i = 1`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => simp`.

Consider the case `succ i ih => rw [pow_succ z, pow_succ' (ι m), mul_assoc, ← mul_assoc z, hz, one_mul, ih]`. Rewrite `hp0` using `[← aeval_def, aeval_eq_sum_range]`. Establish `h2 : ι (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • m ^ (p.natDegree - i)) = ι 0`. Rewrite using `[map_zero, ← zero_mul (ι m ^ p.natDegree), ← hp0, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations.

Establish `hi' : i ≤ p.natDegree` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)`. Rewrite using `[map_smul, map_pow, smul_mul_assoc]`. Use `congr 1`. Use `conv_rhs => rw [← Nat.add_sub_cancel' hi', pow_add, ← mul_assoc, hpow, one_mul]`. Establish `h3` using `hι h2`.

Rewrite `h3` using `[Finset.sum_range_succ, hp.coeff_natDegree, Nat.sub_self, pow_zero, one_smul]`. Apply `hM.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, eq_neg_of_add_eq_zero_right h3]`. Use `M.neg_mem (M.sum_mem fun i hi => ?_)` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`.

Conclude with `M.mul_mem_left _ (M.pow_mem_of_mem hm _ (Nat.sub_pos_of_lt (Finset.mem_range.1 hi)))`.
-/
private theorem dli_mem_max {A B E : Type} [CommRing A] [CommRing B] [Ring E] [Algebra A B] [Algebra A E]
    [Algebra.IsIntegral A E] (ι : B →ₐ[A] E) (hι : Function.Injective ι) {y : B}
    (hy : ι y ∈ Ring.jacobson E) (M : Ideal B) (hM : M.IsMaximal) : y ∈ M := by
  by_contra hyM
  obtain ⟨b, m, hm, hbm⟩ := hM.exists_inv hyM
  have h1 : ι (b * y) ∈ Ring.jacobson E := by
    rw [map_mul]; exact Ideal.mul_mem_left _ _ hy
  obtain ⟨z, hz⟩ := dli_left_inv h1
  have hm' : 1 - ι (b * y) = ι m := by
    rw [← map_one ι, ← map_sub, ← hbm]; simp
  rw [hm'] at hz
  obtain ⟨p, hp, hp0⟩ := Algebra.IsIntegral.isIntegral (R := A) z
  have hpow : ∀ i : ℕ, z ^ i * ι m ^ i = 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ z, pow_succ' (ι m), mul_assoc, ← mul_assoc z, hz, one_mul, ih]
  rw [← aeval_def, aeval_eq_sum_range] at hp0
  have h2 : ι (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • m ^ (p.natDegree - i)) = ι 0 := by
    rw [map_zero, ← zero_mul (ι m ^ p.natDegree), ← hp0, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [map_smul, map_pow, smul_mul_assoc]
    congr 1
    conv_rhs => rw [← Nat.add_sub_cancel' hi', pow_add, ← mul_assoc, hpow, one_mul]
  have h3 := hι h2
  rw [Finset.sum_range_succ, hp.coeff_natDegree, Nat.sub_self, pow_zero, one_smul] at h3
  apply hM.ne_top
  rw [Ideal.eq_top_iff_one, eq_neg_of_add_eq_zero_right h3]
  refine M.neg_mem (M.sum_mem fun i hi => ?_)
  rw [Algebra.smul_def]
  exact M.mul_mem_left _ (M.pow_mem_of_mem hm _ (Nat.sub_pos_of_lt (Finset.mem_range.1 hi)))

/- English proof (translation)
Use `set K : Ideal B := (maximalIdeal A).map (algebraMap A B) with hK`. Use `haveI : IsAdicComplete K B := GlobalTheory.isAdicComplete_map_of_finite _ B`. Establish `hrad : x - x ^ 2 ∈ K.radical`. Rewrite using `[Ideal.radical_eq_sInf, Ideal.mem_sInf]`. Introduce and unpack `P ⟨hKP, hP⟩`.

Use `hy P (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) P ?_)` and prove the remaining obligations. Establish `: maximalIdeal A = P.comap (algebraMap A B)` using `(maximalIdeal.isMaximal A).eq_of_le (Ideal.comap_ne_top _ hP.ne_top) (Ideal.map_le_iff_le_comap.1 hKP)`. Rewrite using `[← this]`. Conclude with `maximalIdeal.isMaximal A`. Take `⟨n, hn⟩` from `hrad`.

Establish `hn' : (x - x ^ 2) ^ (n + 1) ∈ K` using `by rw [pow_succ]; exact K.mul_mem_right _ hn`. Use `set a : B := 1 - (1 - x ^ (n + 1)) ^ (n + 1) with ha`. Establish `hφa : φ a = φ x`. Simplify using `only [ha, map_sub, map_one, map_pow, hx.pow_succ_eq, hx.one_sub.pow_succ_eq, sub_sub_cancel]`. Establish `h0 : a ^ 2 - a ∈ K`.

Use `isIdempotentElem_one_sub_one_sub_pow_pow (Ideal.Quotient.mk K x) (n + 1) (by` as an intermediate fact. Rewrite using `[← map_pow, ← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hn')`. Rewrite using `[← Ideal.Quotient.eq, sq, map_mul]`. Simplify `this.eq` using `[ha]`.

Take `⟨e, he, he'⟩` from `HenselianRing.is_henselian (I := K) (Polynomial.X ^ 2 - Polynomial.X : B[X]) (by nontriviality B; monicity!) a (by simpa using h0) (by`. Use `IsUnit.of_mul_eq_one (Ideal.Quotient.mk K (2 * a - 1)) ?_` and prove the remaining obligations. Rewrite using `[← map_mul, ← map_one (Ideal.Quotient.mk K), Ideal.Quotient.eq]`. Use `K.mul_mem_left 4 h0 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [derivative_sub, derivative_X_pow, derivative_X, eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_one]`.

Use `push_cast`. Use the proof step `ring)`. Establish `he2 : e * e - e = 0` using `by simpa [sq] using he`. Use `⟨e, sub_eq_zero.1 he2, ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit ((e - a) * (-(e - a)) + 1)` using `Ideal.mem_jacobson_bot.1 (HenselianRing.jac he') _`.

Establish `hk : a ^ 2 - a ∈ RingHom.ker φ`. Rewrite using `[RingHom.mem_ker, map_sub, map_pow, hφa, sq, hx.eq, sub_self]`. Establish `hd : (e - a) * ((e - a) * (-(e - a)) + 1) ∈ RingHom.ker φ`. Establish `: (e - a) * ((e - a) * (-(e - a)) + 1) = -(3 * e - a - 1) * (a ^ 2 - a)`. Take the linear combination `(-(e + 1 - 3 * a)) * he2`.

Rewrite using `[this]`. Conclude with `Ideal.mul_mem_left _ _ hk`. Rewrite `hd` using `[Ideal.mul_unit_mem_iff_mem _ hu, RingHom.mem_ker, map_sub, sub_eq_zero]`. Rewrite using `[hd, hφa]`.
-/
private theorem dli_comm {A B F : Type} [CommRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    [IsNoetherianRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Ring F] (φ : B →+* F) (x : B)
    (hx : IsIdempotentElem (φ x)) (hy : ∀ M : Ideal B, M.IsMaximal → x - x ^ 2 ∈ M) :
    ∃ e : B, IsIdempotentElem e ∧ φ e = φ x := by
  set K : Ideal B := (maximalIdeal A).map (algebraMap A B) with hK
  haveI : IsAdicComplete K B := GlobalTheory.isAdicComplete_map_of_finite _ B
  have hrad : x - x ^ 2 ∈ K.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hKP, hP⟩
    refine hy P (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) P ?_)
    have : maximalIdeal A = P.comap (algebraMap A B) :=
      (maximalIdeal.isMaximal A).eq_of_le (Ideal.comap_ne_top _ hP.ne_top) (Ideal.map_le_iff_le_comap.1 hKP)
    rw [← this]; exact maximalIdeal.isMaximal A
  obtain ⟨n, hn⟩ := hrad
  have hn' : (x - x ^ 2) ^ (n + 1) ∈ K := by rw [pow_succ]; exact K.mul_mem_right _ hn
  set a : B := 1 - (1 - x ^ (n + 1)) ^ (n + 1) with ha
  have hφa : φ a = φ x := by
    simp only [ha, map_sub, map_one, map_pow, hx.pow_succ_eq, hx.one_sub.pow_succ_eq, sub_sub_cancel]
  have h0 : a ^ 2 - a ∈ K := by
    have := isIdempotentElem_one_sub_one_sub_pow_pow (Ideal.Quotient.mk K x) (n + 1) (by
      rw [← map_pow, ← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hn')
    rw [← Ideal.Quotient.eq, sq, map_mul]
    simpa [ha] using this.eq
  obtain ⟨e, he, he'⟩ := HenselianRing.is_henselian (I := K) (Polynomial.X ^ 2 - Polynomial.X : B[X])
    (by nontriviality B; monicity!) a (by simpa using h0) (by
      refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk K (2 * a - 1)) ?_
      rw [← map_mul, ← map_one (Ideal.Quotient.mk K), Ideal.Quotient.eq]
      convert K.mul_mem_left 4 h0 using 1
      simp only [derivative_sub, derivative_X_pow, derivative_X, eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_one]
      push_cast
      ring)
  have he2 : e * e - e = 0 := by simpa [sq] using he
  refine ⟨e, sub_eq_zero.1 he2, ?_⟩
  have hu : IsUnit ((e - a) * (-(e - a)) + 1) := Ideal.mem_jacobson_bot.1 (HenselianRing.jac he') _
  have hk : a ^ 2 - a ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker, map_sub, map_pow, hφa, sq, hx.eq, sub_self]
  have hd : (e - a) * ((e - a) * (-(e - a)) + 1) ∈ RingHom.ker φ := by
    have : (e - a) * ((e - a) * (-(e - a)) + 1) = -(3 * e - a - 1) * (a ^ 2 - a) := by
      linear_combination (-(e + 1 - 3 * a)) * he2
    rw [this]; exact Ideal.mul_mem_left _ _ hk
  rw [Ideal.mul_unit_mem_iff_mem _ hu, RingHom.mem_ker, map_sub, sub_eq_zero] at hd
  rw [hd, hφa]

section

variable {A E F : Type} [CommRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A] [IsNoetherianRing A]
  [Ring E] [Algebra A E] [Algebra.IsIntegral A E] [Ring F] [Algebra A F] (π : E →ₐ[A] F)

/- English proof (translation)
Use `haveI : Module.Finite A (Algebra.adjoin A {x}) := Module.Finite.iff_fg.2 (Algebra.IsIntegral.isIntegral (R := A) x).fg_adjoin_singleton`. Take `⟨e, he, he'⟩` from `dli_comm (A := A) (B := Algebra.adjoin A {x}) (π.comp (Algebra.adjoin A {x}).val).toRingHom ⟨x, Algebra.self_mem_adjoin_singleton A x⟩ hx (dli_mem_max (Algebra.adjoin A {x}).val Subtype.val_injective (hk _ (by`. Simplify using `[sq, hx.eq])))`. Conclude with `⟨e, e.2, congrArg Subtype.val he.eq, he'⟩`.
-/
private theorem dli_one (hk : ∀ x, π x = 0 → x ∈ Ring.jacobson E) (x : E) (hx : IsIdempotentElem (π x)) :
    ∃ e ∈ Algebra.adjoin A {x}, IsIdempotentElem e ∧ π e = π x := by
  haveI : Module.Finite A (Algebra.adjoin A {x}) :=
    Module.Finite.iff_fg.2 (Algebra.IsIntegral.isIntegral (R := A) x).fg_adjoin_singleton
  obtain ⟨e, he, he'⟩ := dli_comm (A := A) (B := Algebra.adjoin A {x})
    (π.comp (Algebra.adjoin A {x}).val).toRingHom ⟨x, Algebra.self_mem_adjoin_singleton A x⟩ hx
    (dli_mem_max (Algebra.adjoin A {x}).val Subtype.val_injective (hk _ (by
      simp [sq, hx.eq])))
  exact ⟨e, e.2, congrArg Subtype.val he.eq, he'⟩

/- English proof (translation)
Take `⟨y, rfl⟩` from `hs e₁`. Establish `hx : π ((1 - e₂) * y * (1 - e₂)) = π y`. Simplify using `only [map_mul, map_sub, map_one, sub_mul, mul_sub, one_mul, mul_one, h₁, h₂, zero_mul, sub_zero]`. Take `⟨e, hm, he, he'⟩` from `dli_one π hk ((1 - e₂) * y * (1 - e₂)) (hx ▸ he₁)`. Rewrite `he'` using `[hx]`.

Establish `hc0 : Commute e₂ ((1 - e₂) * y * (1 - e₂))`. Rewrite using `[Commute, SemiconjBy, ← mul_assoc, ← mul_assoc, he₂.mul_one_sub_self, mul_assoc _ (1 - e₂), he₂.one_sub_mul_self]`. Simplify using the standard rewrite rules. Establish `hc : Commute e₂ e` using `Algebra.commute_of_mem_adjoin_singleton_of_commute hm hc0`. Establish `h0 : e₂ * e = 0` using `dli_idem_zero (he₂.mul_of_commute hc he) (hk _ (by rw [map_mul, he', h₂]))`.

Conclude with `⟨e, he, he', by rw [← hc.eq, h0], h0⟩`.
-/
private theorem dli_orth (hs : Function.Surjective π) (hk : ∀ x, π x = 0 → x ∈ Ring.jacobson E)
    (e₁ : F) (he₁ : IsIdempotentElem e₁) (e₂ : E) (he₂ : IsIdempotentElem e₂)
    (h₁ : e₁ * π e₂ = 0) (h₂ : π e₂ * e₁ = 0) :
    ∃ e' : E, IsIdempotentElem e' ∧ π e' = e₁ ∧ e' * e₂ = 0 ∧ e₂ * e' = 0 := by
  obtain ⟨y, rfl⟩ := hs e₁
  have hx : π ((1 - e₂) * y * (1 - e₂)) = π y := by
    simp only [map_mul, map_sub, map_one, sub_mul, mul_sub, one_mul, mul_one, h₁, h₂, zero_mul, sub_zero]
  obtain ⟨e, hm, he, he'⟩ := dli_one π hk ((1 - e₂) * y * (1 - e₂)) (hx ▸ he₁)
  rw [hx] at he'
  have hc0 : Commute e₂ ((1 - e₂) * y * (1 - e₂)) := by
    rw [Commute, SemiconjBy, ← mul_assoc, ← mul_assoc, he₂.mul_one_sub_self, mul_assoc _ (1 - e₂),
      he₂.one_sub_mul_self]
    simp
  have hc : Commute e₂ e := Algebra.commute_of_mem_adjoin_singleton_of_commute hm hc0
  have h0 : e₂ * e = 0 := dli_idem_zero (he₂.mul_of_commute hc he) (hk _ (by rw [map_mul, he', h₂]))
  exact ⟨e, he, he', by rw [← hc.eq, h0], h0⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, ⟨finZeroElim, finZeroElim⟩, funext finZeroElim⟩`. Consider the case `succ n IH`. Take `⟨e', h₁, h₂⟩` from `IH (he.embedding (Fin.succEmb n))`. Establish `h₂' (i) : π (e' i) = e i.succ` using `congr_fun h₂ i`.

Take `⟨e₀, h₃, h₄, h₅, h₆⟩` from `dli_orth π hs hk _ (he.idem 0) _ h₁.isIdempotentElem_sum (by simp [Finset.mul_sum, h₂', he.mul_eq, eq_comm]) (by simp [Finset.sum_mul, h₂', he.mul_eq])`. Use `⟨_, (h₁.option _ h₃ h₅ h₆).embedding (finSuccEquiv n).toEmbedding, funext fun i ↦ ?_⟩` and prove the remaining obligations. Apply the tactic sequence `obtain ⟨_ | i, rfl⟩ := (finSuccEquiv n).symm.surjective i <;> simp [*]`.
-/
private theorem dli_fin (hs : Function.Surjective π) (hk : ∀ x, π x = 0 → x ∈ Ring.jacobson E)
    {n : ℕ} {e : Fin n → F} (he : OrthogonalIdempotents e) :
    ∃ e' : Fin n → E, OrthogonalIdempotents e' ∧ π ∘ e' = e := by
  induction n with
  | zero => exact ⟨0, ⟨finZeroElim, finZeroElim⟩, funext finZeroElim⟩
  | succ n IH =>
    obtain ⟨e', h₁, h₂⟩ := IH (he.embedding (Fin.succEmb n))
    have h₂' (i) : π (e' i) = e i.succ := congr_fun h₂ i
    obtain ⟨e₀, h₃, h₄, h₅, h₆⟩ := dli_orth π hs hk _ (he.idem 0) _ h₁.isIdempotentElem_sum
      (by simp [Finset.mul_sum, h₂', he.mul_eq, eq_comm])
      (by simp [Finset.sum_mul, h₂', he.mul_eq])
    refine ⟨_, (h₁.option _ h₃ h₅ h₆).embedding (finSuccEquiv n).toEmbedding, funext fun i ↦ ?_⟩
    obtain ⟨_ | i, rfl⟩ := (finSuccEquiv n).symm.surjective i <;> simp [*]

end

/- English proof (translation)
Introduce `A E F ι _ _ _ _ _ _ _ _ _ _ _ π hs hk f hf`. Take `⟨e', h₁, h₂⟩` from `dli_fin π hs hk (hf.toOrthogonalIdempotents.embedding (Fintype.equivFin ι).symm.toEmbedding)`. Establish `ho` using `h₁.embedding (Fintype.equivFin ι).toEmbedding`. Establish `hv : ∀ i, π ((e' ∘ (Fintype.equivFin ι).toEmbedding) i) = f i` using `fun i => by`. Simplify using `using congr_fun h₂ (Fintype.equivFin ι i)`.

Use `⟨_, ⟨ho, ?_⟩, hv⟩` and prove the remaining obligations. Use `dli_idem_zero ho.isIdempotentElem_sum.one_sub (hk _ (by` as an intermediate fact. Rewrite using `[map_sub, map_one, map_sum, Finset.sum_congr rfl fun i _ => hv i, hf.complete, sub_self]))`. Conclude with `(sub_eq_zero.1 this).symm`.
-/
theorem UpperTheory.V.CA.d_lift_idem :
    ∀ {A E F ι : Type} [CommRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A] [IsNoetherianRing A] [Ring E] [Algebra A E] [Algebra.IsIntegral A E] [Ring F] [Algebra A F] [Fintype ι] [DecidableEq ι] (π : E →ₐ[A] F), Function.Surjective π → (∀ x, π x = 0 → x ∈ Ring.jacobson E) → ∀ f : ι → F, CompleteOrthogonalIdempotents f → ∃ e : ι → E, CompleteOrthogonalIdempotents e ∧ ∀ i, π (e i) = f i := by
  intro A E F ι _ _ _ _ _ _ _ _ _ _ _ π hs hk f hf
  obtain ⟨e', h₁, h₂⟩ := dli_fin π hs hk
    (hf.toOrthogonalIdempotents.embedding (Fintype.equivFin ι).symm.toEmbedding)
  have ho := h₁.embedding (Fintype.equivFin ι).toEmbedding
  have hv : ∀ i, π ((e' ∘ (Fintype.equivFin ι).toEmbedding) i) = f i := fun i => by
    simpa using congr_fun h₂ (Fintype.equivFin ι i)
  refine ⟨_, ⟨ho, ?_⟩, hv⟩
  have := dli_idem_zero ho.isIdempotentElem_sum.one_sub (hk _ (by
    rw [map_sub, map_one, map_sum, Finset.sum_congr rfl fun i _ => hv i, hf.complete, sub_self]))
  exact (sub_eq_zero.1 this).symm

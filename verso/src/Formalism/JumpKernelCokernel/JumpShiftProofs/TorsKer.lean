import Formalism.JumpKernelCokernel.Statement

noncomputable section

namespace Formalism.KernelCokernelLengths.TorsionKernelLengthLemmas

open PowerSeries

/- English proof (translation)
Rewrite using `[Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]`. Conclude with `IsDiscreteValuationRing.length_quotient_pow_maximalIdeal (R := O) v`.
-/
theorem len_quot_pow {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) (u : Oˣ) (v : ℕ) :
    Module.length O (O ⧸ Ideal.span {(u : O) * ϖ ^ v}) = v := by
  rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
    ← hϖ.maximalIdeal_eq]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal (R := O) v

/- English proof (translation)
Establish `h1 : Module.length O M = Module.length O (LinearMap.ker f) + Module.length O (LinearMap.range f)` using `Module.length_eq_add_of_exact (LinearMap.ker f).subtype f.rangeRestrict (Submodule.subtype_injective _) f.surjective_rangeRestrict (LinearMap.exact_iff.mpr (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))`. Establish `h2 : Module.length O M = Module.length O (LinearMap.range f) + Module.length O (M ⧸ LinearMap.range f)` using `Module.length_eq_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)`. Establish `hR : Module.length O (LinearMap.range f) ≠ ⊤` using `ne_top_of_le_ne_top hM (Module.length_le_of_injective _ (Submodule.subtype_injective (LinearMap.range f)))`. Establish `h5 : Module.length O (LinearMap.ker f) + Module.length O (LinearMap.range f) = Module.length O (M ⧸ LinearMap.range f) + Module.length O (LinearMap.range f)`. Rewrite using `[← h1, h2, add_comm]`.

Conclude with `WithTop.add_right_cancel hR h5`.
-/
theorem ker_eq_coker {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (hM : Module.length O M ≠ ⊤) (f : Module.End O M) :
    Module.length O (LinearMap.ker f) = Module.length O (M ⧸ LinearMap.range f) := by
  have h1 : Module.length O M =
      Module.length O (LinearMap.ker f) + Module.length O (LinearMap.range f) :=
    Module.length_eq_add_of_exact (LinearMap.ker f).subtype f.rangeRestrict
      (Submodule.subtype_injective _) f.surjective_rangeRestrict
      (LinearMap.exact_iff.mpr (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))
  have h2 : Module.length O M =
      Module.length O (LinearMap.range f) + Module.length O (M ⧸ LinearMap.range f) :=
    Module.length_eq_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ
      (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have hR : Module.length O (LinearMap.range f) ≠ ⊤ :=
    ne_top_of_le_ne_top hM
      (Module.length_le_of_injective _ (Submodule.subtype_injective (LinearMap.range f)))
  have h5 : Module.length O (LinearMap.ker f) + Module.length O (LinearMap.range f) =
      Module.length O (M ⧸ LinearMap.range f) + Module.length O (LinearMap.range f) := by
    rw [← h1, h2, add_comm]
  exact WithTop.add_right_cancel hR h5

variable {O : Type} [CommRing O] (ℓ : O) (n k : ℕ)

abbrev J : Ideal (PowerSeries O) := Ideal.span {(X : PowerSeries O) ^ n, C (ℓ ^ k)}

noncomputable abbrev ψ : Polynomial O →+* (PowerSeries O ⧸ J ℓ n k) :=
  Polynomial.eval₂RingHom (algebraMap O (PowerSeries O ⧸ J ℓ n k)) (Ideal.Quotient.mk (J ℓ n k) X)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem psi_apply (P : Polynomial O) :
    ψ ℓ n k P = P.eval₂ (algebraMap O (PowerSeries O ⧸ J ℓ n k)) (Ideal.Quotient.mk (J ℓ n k) X) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem alg_eq (a : O) :
    algebraMap O (PowerSeries O ⧸ J ℓ n k) a = Ideal.Quotient.mk (J ℓ n k) (C a) := rfl

/- English proof (translation)
Establish `h : ψ ℓ n k = (Ideal.Quotient.mk (J ℓ n k)).comp (Polynomial.coeToPowerSeries.ringHom)`. Apply `Polynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[alg_eq]`. Simplify using the standard rewrite rules.

Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem psi_eq (P : Polynomial O) : ψ ℓ n k P = Ideal.Quotient.mk (J ℓ n k) (P : PowerSeries O) := by
  have h : ψ ℓ n k = (Ideal.Quotient.mk (J ℓ n k)).comp (Polynomial.coeToPowerSeries.ringHom) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [alg_eq]
    · simp
  rw [h]
  rfl

/- English proof (translation)
Rewrite using `[psi_eq, Ideal.Quotient.eq]`. Choose the witnesses or unpack the hypotheses as in `⟨q, hq⟩ : (X : PowerSeries O) ^ n ∣ p - (trunc n p : PowerSeries O) := by`. Rewrite using `[PowerSeries.X_pow_dvd_iff]`. Introduce `m hm`. Simplify using `[Polynomial.coeff_coe, PowerSeries.coeff_trunc, hm]`.

Rewrite using `[hq]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))`.
-/
theorem mk_eq_psi (p : PowerSeries O) :
    Ideal.Quotient.mk (J ℓ n k) p = ψ ℓ n k (trunc n p) := by
  rw [psi_eq, Ideal.Quotient.eq]
  obtain ⟨q, hq⟩ : (X : PowerSeries O) ^ n ∣ p - (trunc n p : PowerSeries O) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    simp [Polynomial.coeff_coe, PowerSeries.coeff_trunc, hm]
  rw [hq]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

/- English proof (translation)
Rewrite using `[alg_eq, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.subset_span (by simp)`.
-/
theorem algebraMap_pow_k :
    algebraMap O (PowerSeries O ⧸ J ℓ n k) (ℓ ^ k) = 0 := by
  rw [alg_eq, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp)

/- English proof (translation)
Rewrite using `[Algebra.smul_def, algebraMap_pow_k, zero_mul]`.
-/
theorem smul_pow_k (b : PowerSeries O ⧸ J ℓ n k) : ℓ ^ k • b = 0 := by
  rw [Algebra.smul_def, algebraMap_pow_k, zero_mul]

/- English proof (translation)
Set `e : Fin n → (PowerSeries O ⧸ J ℓ n k)` to `fun j => (Ideal.Quotient.mk (J ℓ n k) X) ^ (j : ℕ)`. Establish `hker : ∀ j, Ideal.span {ℓ ^ k} ≤ LinearMap.ker (LinearMap.toSpanSingleton O _ (e j))`. Introduce `j`. Rewrite using `[Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]`. Conclude with `smul_pow_k ℓ n k _`.

Set `Φ : (Fin n → O ⧸ Ideal.span {ℓ ^ k}) →ₗ[O] (PowerSeries O ⧸ J ℓ n k)` to `∑ j : Fin n, (Submodule.liftQ _ (LinearMap.toSpanSingleton O _ (e j)) (hker j)).comp (LinearMap.proj j)`. Establish `hΦ : Function.Surjective Φ`. Introduce `b`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Use `⟨fun j => Ideal.Quotient.mk _ (coeff (j : ℕ) p), ?_⟩` and prove the remaining obligations.

Rewrite using `[mk_eq_psi, psi_apply, eval₂_trunc_eq_sum_range, ← Fin.sum_univ_eq_sum_range]`. Simplify using `only [Φ]`. Rewrite using `[LinearMap.sum_apply]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Use `show (Submodule.liftQ _ (LinearMap.toSpanSingleton O _ (e j)) (hker j)) (Submodule.Quotient.mk (coeff (j : ℕ) p)) = _`.

Rewrite using `[Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, Algebra.smul_def]`. Conclude with `Module.length_le_of_surjective Φ hΦ`.
-/
theorem len_B_le :
    Module.length O (PowerSeries O ⧸ J ℓ n k) ≤
      Module.length O (Fin n → O ⧸ Ideal.span {ℓ ^ k}) := by
  let e : Fin n → (PowerSeries O ⧸ J ℓ n k) := fun j => (Ideal.Quotient.mk (J ℓ n k) X) ^ (j : ℕ)
  have hker : ∀ j, Ideal.span {ℓ ^ k} ≤ LinearMap.ker (LinearMap.toSpanSingleton O _ (e j)) := by
    intro j
    rw [Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    exact smul_pow_k ℓ n k _
  let Φ : (Fin n → O ⧸ Ideal.span {ℓ ^ k}) →ₗ[O] (PowerSeries O ⧸ J ℓ n k) :=
    ∑ j : Fin n, (Submodule.liftQ _ (LinearMap.toSpanSingleton O _ (e j)) (hker j)).comp
      (LinearMap.proj j)
  have hΦ : Function.Surjective Φ := by
    intro b
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨fun j => Ideal.Quotient.mk _ (coeff (j : ℕ) p), ?_⟩
    rw [mk_eq_psi, psi_apply, eval₂_trunc_eq_sum_range,
      ← Fin.sum_univ_eq_sum_range]
    simp only [Φ]
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    show (Submodule.liftQ _ (LinearMap.toSpanSingleton O _ (e j)) (hker j))
      (Submodule.Quotient.mk (coeff (j : ℕ) p)) = _
    rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, Algebra.smul_def]
  exact Module.length_le_of_surjective Φ hΦ

/- English proof (translation)
Use `set R := LinearMap.range (LinearMap.mulLeft O (Ideal.Quotient.mk (J ℓ n k) ((X : PowerSeries O) - C ℓ))) with hR`. Establish `hker : Ideal.span {ℓ ^ k} ≤ LinearMap.ker (LinearMap.toSpanSingleton O _ (R.mkQ (1 : PowerSeries O ⧸ J ℓ n k)))`. Rewrite using `[Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← LinearMap.map_smul, smul_pow_k, map_zero]`. Set `Ψ` to `Submodule.liftQ _ (LinearMap.toSpanSingleton O _ (R.mkQ (1 : PowerSeries O ⧸ J ℓ n k))) hker`. Establish `hΨ : Function.Surjective Ψ`.

Introduce `z`. Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective R z`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Take `⟨Q, hQ⟩` from `Polynomial.X_sub_C_dvd_sub_C_eval (a := ℓ) (p := trunc n p)`. Use `⟨Submodule.Quotient.mk ((trunc n p).eval ℓ), ?_⟩` and prove the remaining obligations.

Rewrite using `[Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, ← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.eq]`. Use `⟨-ψ ℓ n k Q, ?_⟩` and prove the remaining obligations. Establish `hX : Ideal.Quotient.mk (J ℓ n k) ((X : PowerSeries O) - C ℓ) = ψ ℓ n k (Polynomial.X - Polynomial.C ℓ)`. Rewrite using `[psi_eq, Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C]`. Rewrite using `[map_neg, LinearMap.mulLeft_apply, hX, ← map_mul, ← hQ, map_sub, mk_eq_psi ℓ n k p, psi_apply ℓ n k (Polynomial.C _), Polynomial.eval₂_C, Algebra.algebraMap_eq_smul_one, neg_sub]`.

Conclude with `Module.length_le_of_surjective Ψ hΨ`.
-/
theorem len_coker_le :
    Module.length O ((PowerSeries O ⧸ J ℓ n k) ⧸ LinearMap.range (LinearMap.mulLeft O
      (Ideal.Quotient.mk (J ℓ n k) ((X : PowerSeries O) - C ℓ)))) ≤
      Module.length O (O ⧸ Ideal.span {ℓ ^ k}) := by
  set R := LinearMap.range (LinearMap.mulLeft O
      (Ideal.Quotient.mk (J ℓ n k) ((X : PowerSeries O) - C ℓ))) with hR
  have hker : Ideal.span {ℓ ^ k} ≤
      LinearMap.ker (LinearMap.toSpanSingleton O _ (R.mkQ (1 : PowerSeries O ⧸ J ℓ n k))) := by
    rw [Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply,
      ← LinearMap.map_smul, smul_pow_k, map_zero]
  let Ψ := Submodule.liftQ _ (LinearMap.toSpanSingleton O _ (R.mkQ (1 : PowerSeries O ⧸ J ℓ n k)))
    hker
  have hΨ : Function.Surjective Ψ := by
    intro z
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective R z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨Q, hQ⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (a := ℓ) (p := trunc n p)
    refine ⟨Submodule.Quotient.mk ((trunc n p).eval ℓ), ?_⟩
    rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, ← LinearMap.map_smul,
      Submodule.mkQ_apply, Submodule.Quotient.eq]
    refine ⟨-ψ ℓ n k Q, ?_⟩
    have hX : Ideal.Quotient.mk (J ℓ n k) ((X : PowerSeries O) - C ℓ) =
        ψ ℓ n k (Polynomial.X - Polynomial.C ℓ) := by
      rw [psi_eq, Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C]
    rw [map_neg, LinearMap.mulLeft_apply, hX, ← map_mul, ← hQ, map_sub, mk_eq_psi ℓ n k p,
      psi_apply ℓ n k (Polynomial.C _), Polynomial.eval₂_C,
      Algebra.algebraMap_eq_smul_one, neg_sub]
  exact Module.length_le_of_surjective Ψ hΨ

end Formalism.KernelCokernelLengths.TorsionKernelLengthLemmas

open Formalism.KernelCokernelLengths.TorsionKernelLengthLemmas in
/- English proof (translation)
Introduce `O _ _ _ ℓ hℓ n k`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨v, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hℓ hϖ`. Establish `hl1 : Module.length O (O ⧸ Ideal.span {ℓ}) = v`. Rewrite using `[hu]`.

Conclude with `len_quot_pow hϖ u v`. Establish `hlk : Module.length O (O ⧸ Ideal.span {ℓ ^ k}) = ((v * k : ℕ) : ℕ∞)`. Rewrite using `[hu, mul_pow, ← pow_mul, ← Units.val_pow_eq_pow_val]`. Conclude with `len_quot_pow hϖ (u ^ k) (v * k)`. Establish `hB : Module.length O (PowerSeries O ⧸ J ℓ n k) ≠ ⊤`.

Use `ne_top_of_le_ne_top ?_ (len_B_le ℓ n k)` and prove the remaining obligations. Rewrite using `[Module.length_pi, hlk, ENat.card_eq_coe_fintype_card, Fintype.card_fin, ← Nat.cast_mul]`. Conclude with `ENat.natCast_ne_top _`. Rewrite using `[ker_eq_coker hB, hl1]`. Use `(len_coker_le ℓ n k).trans ?_` and prove the remaining obligations.

Rewrite using `[hlk]`. Use `push_cast`. Rewrite using `[mul_comm]`.
-/
theorem Formalism.KernelCokernelLengths.torsion_kernel_length : Formalism.KernelCokernelLengths.TorsKer := by
  intro O _ _ _ ℓ hℓ n k
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨v, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hℓ hϖ
  have hl1 : Module.length O (O ⧸ Ideal.span {ℓ}) = v := by
    rw [hu]; exact len_quot_pow hϖ u v
  have hlk : Module.length O (O ⧸ Ideal.span {ℓ ^ k}) = ((v * k : ℕ) : ℕ∞) := by
    rw [hu, mul_pow, ← pow_mul, ← Units.val_pow_eq_pow_val]
    exact len_quot_pow hϖ (u ^ k) (v * k)
  have hB : Module.length O (PowerSeries O ⧸ J ℓ n k) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (len_B_le ℓ n k)
    rw [Module.length_pi, hlk, ENat.card_eq_coe_fintype_card, Fintype.card_fin, ← Nat.cast_mul]
    exact ENat.natCast_ne_top _
  rw [ker_eq_coker hB, hl1]
  refine (len_coker_le ℓ n k).trans ?_
  rw [hlk]
  push_cast
  rw [mul_comm]

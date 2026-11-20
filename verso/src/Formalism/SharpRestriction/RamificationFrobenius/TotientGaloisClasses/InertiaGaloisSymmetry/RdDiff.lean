import Mathlib

open NumberField IntermediateField Polynomial ArithmeticFunction

noncomputable section

namespace Formalism.HC.Der.Rd

/- English proof (translation)
Distinguish the cases in `h : IsPrimePow m`. Take `⟨p, k, hp, hk, rfl⟩` from `(isPrimePow_nat_iff m).1 h`. Break down `k with _ | j` into its components or cases. Use linear arithmetic over natural numbers and integers. Use `haveI := Fact.mk hp`.

Rewrite using `[eval_one_cyclotomic_prime_pow, vonMangoldt_apply_pow (Nat.succ_ne_zero j), vonMangoldt_apply_prime hp]`. Simplify using the standard rewrite rules. Rewrite using `[eval_one_cyclotomic_not_prime_pow, vonMangoldt_eq_zero_iff.2 h]`. Simplify using the standard rewrite rules. Introduce `p hp k hk`.

Apply `h` to reduce the goal to its premises. Rewrite using `[← hk]`. Use `hp.isPrimePow.pow ?_` and prove the remaining obligations. Introduce and unpack `rfl`. Rewrite `hk` using `[pow_zero]`.

Use linear arithmetic over natural numbers and integers.
-/
private theorem log_abs_eval_one_cyclotomic_eq_vonMangoldt {m : ℕ} (hm : 1 < m) :
    Real.log |((eval 1 (cyclotomic m ℚ) : ℚ) : ℝ)| = vonMangoldt m := by
  by_cases h : IsPrimePow m
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff m).1 h
    rcases k with _ | j
    · omega
    haveI := Fact.mk hp
    rw [eval_one_cyclotomic_prime_pow, vonMangoldt_apply_pow (Nat.succ_ne_zero j),
      vonMangoldt_apply_prime hp]
    simp
  · rw [eval_one_cyclotomic_not_prime_pow, vonMangoldt_eq_zero_iff.2 h]
    · simp
    · intro p hp k hk
      apply h
      rw [← hk]
      refine hp.isPrimePow.pow ?_
      rintro rfl
      rw [pow_zero] at hk
      omega

/- English proof (translation)
Establish `hm0 : 0 < m` using `by omega`. Establish `hint_r : IsIntegral ℚ η` using `.of_finite ℚ η`. Establish `hx : IsIntegral ℚ (η - 1)` using `.of_finite ℚ _`. Establish `hmin : minpoly ℚ (η - 1) = (cyclotomic m ℚ).comp (X + C 1)`. Establish `h0 : minpoly ℚ (η - algebraMap ℚ L 1) = (minpoly ℚ η).comp (X + C 1)`.

Conclude with `minpoly.sub_algebraMap η (1 : ℚ)`. Rewrite `h0` using `[map_one]`. Rewrite using `[h0, ← cyclotomic_eq_minpoly_rat hη hm0]`. Establish `hdeg : Module.finrank ℚ ℚ⟮η - 1⟯ = m.totient`. Rewrite using `[IntermediateField.adjoin.finrank hx, hmin, natDegree_comp, natDegree_cyclotomic, natDegree_X_add_C, mul_one]`.

Establish `hnormval : Algebra.norm ℚ (η - 1) = ((-1) ^ m.totient * eval 1 (cyclotomic m ℚ)) ^ Module.finrank ℚ⟮η - 1⟯ L`. Rewrite using `[Algebra.norm_eq_norm_adjoin ℚ (η - 1)]`. Use `congr 1`. Establish `h` using `Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (IntermediateField.adjoin.powerBasis hx)`. Rewrite `h` using `[IntermediateField.adjoin.powerBasis_dim]`.

Rewrite using `[show IntermediateField.AdjoinSimple.gen ℚ (η - 1) = (IntermediateField.adjoin.powerBasis hx).gen from rfl, h, IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen, hmin, coeff_zero_eq_eval_zero, eval_comp, natDegree_comp, natDegree_cyclotomic, natDegree_X_add_C …`. Simplify using the standard rewrite rules. Establish `habs : |((Algebra.norm ℚ (η - 1) : ℚ) : ℝ)| = |((eval 1 (cyclotomic m ℚ) : ℚ) : ℝ)| ^ Module.finrank ℚ⟮η - 1⟯ L`. Rewrite using `[hnormval]`. Use `push_cast`.

Rewrite using `[abs_pow, abs_mul, abs_pow]`. Simplify using the standard rewrite rules. Use `haveI : Module.Free ℚ ℚ⟮η - 1⟯ := Module.Free.of_divisionRing _ _`. Rewrite using `[habs, Real.log_pow, log_abs_eval_one_cyclotomic_eq_vonMangoldt hm, ← Module.finrank_mul_finrank ℚ ℚ⟮η - 1⟯ L, hdeg]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem log_abs_norm_sub_one_mul_totient_eq {m : ℕ} (hm : 1 < m) {L : Type*} [Field L] [NumberField L] {η : L}
    (hη : IsPrimitiveRoot η m) :
    Real.log |((Algebra.norm ℚ (η - 1) : ℚ) : ℝ)| * (m.totient : ℝ) = (Module.finrank ℚ L : ℝ) * vonMangoldt m := by
  have hm0 : 0 < m := by omega
  have hint_r : IsIntegral ℚ η := .of_finite ℚ η
  have hx : IsIntegral ℚ (η - 1) := .of_finite ℚ _
  have hmin : minpoly ℚ (η - 1) = (cyclotomic m ℚ).comp (X + C 1) := by
    have h0 : minpoly ℚ (η - algebraMap ℚ L 1) = (minpoly ℚ η).comp (X + C 1) := by
      exact minpoly.sub_algebraMap η (1 : ℚ)
    rw [map_one] at h0
    rw [h0, ← cyclotomic_eq_minpoly_rat hη hm0]
  have hdeg : Module.finrank ℚ ℚ⟮η - 1⟯ = m.totient := by
    rw [IntermediateField.adjoin.finrank hx, hmin, natDegree_comp, natDegree_cyclotomic, natDegree_X_add_C,
      mul_one]
  have hnormval : Algebra.norm ℚ (η - 1) =
      ((-1) ^ m.totient * eval 1 (cyclotomic m ℚ)) ^ Module.finrank ℚ⟮η - 1⟯ L := by
    rw [Algebra.norm_eq_norm_adjoin ℚ (η - 1)]
    congr 1
    have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (IntermediateField.adjoin.powerBasis hx)
    rw [IntermediateField.adjoin.powerBasis_dim] at h
    rw [show IntermediateField.AdjoinSimple.gen ℚ (η - 1) = (IntermediateField.adjoin.powerBasis hx).gen from rfl,
      h, IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen, hmin, coeff_zero_eq_eval_zero,
      eval_comp, natDegree_comp, natDegree_cyclotomic, natDegree_X_add_C, mul_one]
    simp
  have habs : |((Algebra.norm ℚ (η - 1) : ℚ) : ℝ)| =
      |((eval 1 (cyclotomic m ℚ) : ℚ) : ℝ)| ^ Module.finrank ℚ⟮η - 1⟯ L := by
    rw [hnormval]; push_cast; rw [abs_pow, abs_mul, abs_pow]; simp
  haveI : Module.Free ℚ ℚ⟮η - 1⟯ := Module.Free.of_divisionRing _ _
  rw [habs, Real.log_pow, log_abs_eval_one_cyclotomic_eq_vonMangoldt hm, ← Module.finrank_mul_finrank ℚ ℚ⟮η - 1⟯ L, hdeg]
  push_cast; ring

/- English proof (translation)
Use `haveI : NeZero m := ⟨by omega⟩`. Establish `h` using `log_abs_norm_sub_one_mul_totient_eq hm hη`. Rewrite `h` using `[IsCyclotomicExtension.finrank F (cyclotomic.irreducible_rat (by omega : 0 < m))]`. Establish `ht : (0 : ℝ) < m.totient` using `by exact_mod_cast Nat.totient_pos.2 (by omega)`. Conclude with `mul_right_cancel₀ ht.ne' (h.trans (mul_comm _ _))`.
-/
theorem log_norm_cyc {m : ℕ} (hm : 1 < m) {F : Type*} [Field F] [NumberField F] [IsCyclotomicExtension {m} ℚ F]
    {η : F} (hη : IsPrimitiveRoot η m) : Real.log |((Algebra.norm ℚ (η - 1) : ℚ) : ℝ)| = vonMangoldt m := by
  haveI : NeZero m := ⟨by omega⟩
  have h := log_abs_norm_sub_one_mul_totient_eq hm hη
  rw [IsCyclotomicExtension.finrank F (cyclotomic.irreducible_rat (by omega : 0 < m))] at h
  have ht : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  exact mul_right_cancel₀ ht.ne' (h.trans (mul_comm _ _))

/- English proof (translation)
Establish `hr : Module.finrank (𝓞 E) (𝓞 L) = Module.finrank E L`. Conclude with `(IsFractionRing.finrank_eq (𝓞 E) E (𝓞 L) L).symm`. Rewrite using `[Ideal.absNorm_algebraMap (𝓞 E) (𝓞 L) I, hr]`.
-/
private theorem absNorm_map_algebraMap_eq_pow_finrank {L E : Type*} [Field L] [NumberField L] [Field E] [NumberField E]
    [Algebra E L] (I : Ideal (𝓞 E)) :
    Ideal.absNorm (I.map (algebraMap (𝓞 E) (𝓞 L))) = Ideal.absNorm I ^ Module.finrank E L := by
  have hr : Module.finrank (𝓞 E) (𝓞 L) = Module.finrank E L := by
    exact (IsFractionRing.finrank_eq (𝓞 E) E (𝓞 L) L).symm
  rw [Ideal.absNorm_algebraMap (𝓞 E) (𝓞 L) I, hr]

/- English proof (translation)
Conclude with `log_abs_norm_sub_one_mul_totient_eq hm hη`.
-/
theorem log_norm_root {m : ℕ} (hm : 1 < m) {L : Type*} [Field L] [NumberField L] {η : L}
    (hη : IsPrimitiveRoot η m) :
    Real.log |((Algebra.norm ℚ (η - 1) : ℚ) : ℝ)| * (m.totient : ℝ) = (Module.finrank ℚ L : ℝ) * vonMangoldt m := by
  exact log_abs_norm_sub_one_mul_totient_eq hm hη

variable {N : ℕ} [NeZero N] {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {N} ℚ L] {ζ : L}
  (hζ : IsPrimitiveRoot ζ N) (E : Type*) [Field E] [NumberField E] [Algebra E L]
include hζ

set_option maxHeartbeats 800000 in

/- English proof (translation)
Establish `h1 : Algebra.adjoin ℚ ({ζ} : Set L) = ⊤` using `IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ`. Use `eq_top_iff.2 fun x hxt => ?_` and prove the remaining obligations. Use `clear hxt`. Establish `hx : x ∈ Algebra.adjoin ℚ ({ζ} : Set L)` using `by rw [h1]; exact Algebra.mem_top`. Proceed by induction on `hx using Algebra.adjoin_induction with`.

Consider the case `mem x hx => exact Algebra.subset_adjoin hx`. Consider the case `algebraMap r`. Rewrite using `[eq_ratCast (algebraMap ℚ L) r, ← map_ratCast (algebraMap E L) r]`. Conclude with `Subalgebra.algebraMap_mem _ _`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`.

Consider the case `mul x y _ _ hx hy => exact mul_mem hx hy`.
-/
theorem adjoin_top : Algebra.adjoin E {ζ} = ⊤ := by
  have h1 : Algebra.adjoin ℚ ({ζ} : Set L) = ⊤ := IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
  refine eq_top_iff.2 fun x hxt => ?_
  clear hxt
  have hx : x ∈ Algebra.adjoin ℚ ({ζ} : Set L) := by rw [h1]; exact Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap r =>
    rw [eq_ratCast (algebraMap ℚ L) r, ← map_ratCast (algebraMap E L) r]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

/- English proof (translation)
Introduce `σ τ h`. Use `AlgHom.ext_of_adjoin_eq_top (adjoin_top hζ E) (φ₁ := (σ : L →ₐ[E] L)) (φ₂ := (τ : L →ₐ[E] L)) (by simpa using h)` as an intermediate fact. Conclude with `AlgEquiv.coe_algHom_injective this`.
-/
theorem gal_inj : Function.Injective fun σ : L ≃ₐ[E] L => σ ζ := by
  intro σ τ h
  have := AlgHom.ext_of_adjoin_eq_top (adjoin_top hζ E)
    (φ₁ := (σ : L →ₐ[E] L)) (φ₂ := (τ : L →ₐ[E] L)) (by simpa using h)
  exact AlgEquiv.coe_algHom_injective this

/- English proof (translation)
Use `haveI : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite ℚ E L`. Use `haveI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {N} ℚ L`. Use `haveI : IsGalois E L := IsGalois.tower_top_of_isGalois ℚ E L`. Establish `hint_r : IsIntegral E ζ` using `.of_finite E ζ`. Establish `htop : E⟮ζ⟯ = ⊤`.

Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `hx : x ∈ Algebra.adjoin E ({ζ} : Set L)`. Rewrite using `[adjoin_top hζ E]`. Conclude with `Algebra.mem_top`.

Use `first`. Consider the case `exact IntermediateField.algebra_adjoin_le_adjoin E ({ζ} : Set L) hx`. Consider the case `exact IntermediateField.algebra_adjoin_le_adjoin (F := E) (S := ({ζ} : Set L)) hx`. Establish `hcard : Fintype.card (L ≃ₐ[E] L) = Module.finrank E L`. Rewrite using `[← IsGalois.card_aut_eq_finrank E L, Nat.card_eq_fintype_card]`.

Establish `hinj` using `gal_inj hζ E`. Apply `Polynomial.eq_of_monic_of_dvd_of_natDegree_le Lagrange.nodal_monic` to reduce the goal to its premises. Conclude with `(minpoly.monic hint_r).map _`. Unfold `Lagrange.nodal`. Use `Finset.prod_dvd_of_coprime ((Polynomial.pairwise_coprime_X_sub_C hinj).set_pairwise _) fun σ _ => ?_` and prove the remaining obligations.

Rewrite using `[Polynomial.dvd_iff_isRoot, IsRoot.def, eval_map, ← aeval_def]`. Use `Polynomial.aeval_algHom_apply (σ : L →ₐ[E] L) ζ (minpoly E ζ)` as an intermediate fact. Rewrite `this` using `[minpoly.aeval, _root_.map_zero]`. Conclude with `this`. Use `le_of_eq ?_` and prove the remaining obligations.

Rewrite using `[natDegree_map, ← IntermediateField.adjoin.finrank hint_r, htop, IntermediateField.finrank_top', Lagrange.natDegree_nodal, Finset.card_univ, hcard]`.
-/
theorem minpoly_map : (minpoly E ζ).map (algebraMap E L) = Lagrange.nodal Finset.univ fun σ : L ≃ₐ[E] L => σ ζ := by
  haveI : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite ℚ E L
  haveI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {N} ℚ L
  haveI : IsGalois E L := IsGalois.tower_top_of_isGalois ℚ E L
  have hint_r : IsIntegral E ζ := .of_finite E ζ
  have htop : E⟮ζ⟯ = ⊤ := by
    rw [eq_top_iff]; intro x _
    have hx : x ∈ Algebra.adjoin E ({ζ} : Set L) := by
      rw [adjoin_top hζ E]; exact Algebra.mem_top
    first
    | exact IntermediateField.algebra_adjoin_le_adjoin E ({ζ} : Set L) hx
    | exact IntermediateField.algebra_adjoin_le_adjoin (F := E) (S := ({ζ} : Set L)) hx
  have hcard : Fintype.card (L ≃ₐ[E] L) = Module.finrank E L := by
    rw [← IsGalois.card_aut_eq_finrank E L, Nat.card_eq_fintype_card]
  have hinj := gal_inj hζ E
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le Lagrange.nodal_monic
  · exact (minpoly.monic hint_r).map _
  · unfold Lagrange.nodal
    refine Finset.prod_dvd_of_coprime ((Polynomial.pairwise_coprime_X_sub_C hinj).set_pairwise _)
      fun σ _ => ?_
    rw [Polynomial.dvd_iff_isRoot, IsRoot.def, eval_map, ← aeval_def]
    have := Polynomial.aeval_algHom_apply (σ : L →ₐ[E] L) ζ (minpoly E ζ)
    rw [minpoly.aeval, _root_.map_zero] at this
    exact this
  · refine le_of_eq ?_
    rw [natDegree_map, ← IntermediateField.adjoin.finrank hint_r, htop, IntermediateField.finrank_top',
      Lagrange.natDegree_nodal, Finset.card_univ, hcard]

open Classical in
/- English proof (translation)
Use `haveI : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite ℚ E L`. Establish `hζL : algebraMap (𝓞 L) L hζ.toInteger = ζ` using `hζ.coe_toInteger`. Establish `hadjZ : Algebra.adjoin ℤ ({hζ.toInteger} : Set (𝓞 L)) = ⊤` using `IsCyclotomicExtension.Rat.adjoin_singleton_eq_top hζ`. Generalize the expression as in `hζ.toInteger = z at hζL hadjZ`. Establish `hadj : Algebra.adjoin (𝓞 E) ({z} : Set (𝓞 L)) = ⊤`.

Use `eq_top_iff.2 fun x hxt => ?_` and prove the remaining obligations. Use `clear hxt`. Establish `hx : x ∈ Algebra.adjoin ℤ ({z} : Set (𝓞 L))` using `by rw [hadjZ]; exact Algebra.mem_top`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact Algebra.subset_adjoin hx`.

Consider the case `algebraMap r`. Rewrite using `[IsScalarTower.algebraMap_apply ℤ (𝓞 E) (𝓞 L)]`. Conclude with `Subalgebra.algebraMap_mem _ _`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`. Consider the case `mul x y _ _ hx hy => exact mul_mem hx hy`.

Establish `hK : Algebra.adjoin E {algebraMap (𝓞 L) L z} = ⊤`. Rewrite using `[hζL]`. Conclude with `adjoin_top hζ E`. Establish `hD` using `conductor_mul_differentIdeal (𝓞 E) E L z hK`. Establish `hc : conductor (𝓞 E) z = ⊤` using `by first`.

Consider the case `exact conductor_eq_top_of_adjoin_eq_top hadj`. Consider the case `exact conductor_eq_top_of_adjoin_eq_top _ hadj`. Consider the case `exact conductor_eq_top_of_adjoin_eq_top (𝓞 E) hadj`. Rewrite `hD` using `[hc, Ideal.top_mul]`. Establish `hint_r : IsIntegral (𝓞 E) ζ` using `(hζ.isIntegral (NeZero.pos N)).tower_top`.

Establish `hminE : minpoly E ζ = (minpoly (𝓞 E) z).map (algebraMap (𝓞 E) E)`. Rewrite using `[← minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective (𝓞 L) L) z, hζL]`. Use `first`. Consider the case `exact minpoly.isIntegrallyClosed_eq_field_fractions' E hint_r`. Consider the case `exact minpoly.isIntegrallyClosed_eq_field_fractions' (K := E) hint_r`.

Establish `hmapL : (minpoly (𝓞 E) z).map (algebraMap (𝓞 E) L) = Lagrange.nodal Finset.univ (fun σ : L ≃ₐ[E] L => σ ζ)`. Rewrite using `[← minpoly_map hζ E, hminE, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]`. Establish `hy : algebraMap (𝓞 L) L (aeval z (derivative (minpoly (𝓞 E) z))) = ∏ σ ∈ (Finset.univ : Finset (L ≃ₐ[E] L)).erase 1, (ζ - σ ζ)`. Rewrite using `[← aeval_algebraMap_apply, hζL, aeval_def, eval₂_eq_eval_map, ← derivative_map, hmapL]`. Establish `h1` using `Lagrange.eval_nodal_derivative_eval_node_eq (s := (Finset.univ : Finset (L ≃ₐ[E] L))) (v := fun σ : L ≃ₐ[E] L => σ ζ) (Finset.mem_univ 1)`.

Rewrite `h1` using `[Lagrange.eval_nodal]`. Conclude with `h1`. Establish `hnormR : ((Algebra.norm ℤ (aeval z (derivative (minpoly (𝓞 E) z))) : ℤ) : ℝ) = ((Algebra.norm ℚ (∏ σ ∈ (Finset.univ : Finset (L ≃ₐ[E] L)).erase 1, (ζ - σ ζ)) : ℚ) : ℝ)`. Rewrite using `[← hy, ← Algebra.coe_norm_int]`. Use `norm_cast`.

Rewrite using `[hD, Ideal.absNorm_span_singleton]`. Simplify using `only [Nat.cast_natAbs, Int.cast_abs]`. Rewrite using `[hnormR, map_prod, Rat.cast_prod, Finset.abs_prod]`.
-/
theorem absNorm_diff : ((Ideal.absNorm (differentIdeal (𝓞 E) (𝓞 L)) : ℕ) : ℝ) =
    ∏ σ ∈ (Finset.univ : Finset (L ≃ₐ[E] L)).erase 1, |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| := by
  haveI : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite ℚ E L
  have hζL : algebraMap (𝓞 L) L hζ.toInteger = ζ := hζ.coe_toInteger
  have hadjZ : Algebra.adjoin ℤ ({hζ.toInteger} : Set (𝓞 L)) = ⊤ :=
    IsCyclotomicExtension.Rat.adjoin_singleton_eq_top hζ
  generalize hζ.toInteger = z at hζL hadjZ
  have hadj : Algebra.adjoin (𝓞 E) ({z} : Set (𝓞 L)) = ⊤ := by
    refine eq_top_iff.2 fun x hxt => ?_
    clear hxt
    have hx : x ∈ Algebra.adjoin ℤ ({z} : Set (𝓞 L)) := by rw [hadjZ]; exact Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin hx
    | algebraMap r =>
      rw [IsScalarTower.algebraMap_apply ℤ (𝓞 E) (𝓞 L)]; exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  have hK : Algebra.adjoin E {algebraMap (𝓞 L) L z} = ⊤ := by
    rw [hζL]; exact adjoin_top hζ E
  have hD := conductor_mul_differentIdeal (𝓞 E) E L z hK
  have hc : conductor (𝓞 E) z = ⊤ := by
    first
    | exact conductor_eq_top_of_adjoin_eq_top hadj
    | exact conductor_eq_top_of_adjoin_eq_top _ hadj
    | exact conductor_eq_top_of_adjoin_eq_top (𝓞 E) hadj
  rw [hc, Ideal.top_mul] at hD
  have hint_r : IsIntegral (𝓞 E) ζ := (hζ.isIntegral (NeZero.pos N)).tower_top
  have hminE : minpoly E ζ = (minpoly (𝓞 E) z).map (algebraMap (𝓞 E) E) := by
    rw [← minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective (𝓞 L) L) z, hζL]
    first
    | exact minpoly.isIntegrallyClosed_eq_field_fractions' E hint_r
    | exact minpoly.isIntegrallyClosed_eq_field_fractions' (K := E) hint_r
  have hmapL : (minpoly (𝓞 E) z).map (algebraMap (𝓞 E) L) =
      Lagrange.nodal Finset.univ (fun σ : L ≃ₐ[E] L => σ ζ) := by
    rw [← minpoly_map hζ E, hminE, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hy : algebraMap (𝓞 L) L (aeval z (derivative (minpoly (𝓞 E) z))) =
      ∏ σ ∈ (Finset.univ : Finset (L ≃ₐ[E] L)).erase 1, (ζ - σ ζ) := by
    rw [← aeval_algebraMap_apply, hζL, aeval_def, eval₂_eq_eval_map, ← derivative_map, hmapL]
    have h1 := Lagrange.eval_nodal_derivative_eval_node_eq (s := (Finset.univ : Finset (L ≃ₐ[E] L)))
      (v := fun σ : L ≃ₐ[E] L => σ ζ) (Finset.mem_univ 1)
    rw [Lagrange.eval_nodal] at h1
    exact h1
  have hnormR : ((Algebra.norm ℤ (aeval z (derivative (minpoly (𝓞 E) z))) : ℤ) : ℝ) =
      ((Algebra.norm ℚ (∏ σ ∈ (Finset.univ : Finset (L ≃ₐ[E] L)).erase 1, (ζ - σ ζ)) : ℚ) : ℝ) := by
    rw [← hy, ← Algebra.coe_norm_int]; norm_cast
  rw [hD, Ideal.absNorm_span_singleton]
  simp only [Nat.cast_natAbs, Int.cast_abs]
  rw [hnormR, map_prod, Rat.cast_prod,
    Finset.abs_prod]

open Classical in
/- English proof (translation)
Use `haveI : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite ℚ E L`. Establish `hD` using `differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 E) (𝓞 L)`. Establish `h1 : ((Ideal.absNorm (differentIdeal ℤ (𝓞 L)) : ℕ) : ℝ) = |(discr L : ℝ)|`. Rewrite using `[NumberField.absNorm_differentIdeal L (𝓞 L)]`. Simplify using `only [Nat.cast_natAbs, Int.cast_abs]`.

Establish `hE : ((Ideal.absNorm (differentIdeal ℤ (𝓞 E)) : ℕ) : ℝ) = |(discr E : ℝ)|`. Rewrite using `[NumberField.absNorm_differentIdeal E (𝓞 E)]`. Simplify using `only [Nat.cast_natAbs, Int.cast_abs]`. Establish `hne : ∀ σ ∈ (Finset.univ : Finset (L ≃ₐ[E] L)).erase 1, |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| ≠ 0`. Introduce `σ hσ`.

Establish `hσ1 : σ ≠ 1` using `Finset.ne_of_mem_erase hσ`. Establish `hne : ζ - σ ζ ≠ 0`. Introduce `h`. Apply `hσ1` to reduce the goal to its premises. Apply `gal_inj hζ E` to reduce the goal to its premises.

Conclude with `(sub_eq_zero.1 h).symm`. Rewrite using `[abs_ne_zero, Rat.cast_ne_zero]`. Conclude with `Algebra.norm_ne_zero_iff.2 hne`. Establish `hdE : |(discr E : ℝ)| ≠ 0` using `abs_ne_zero.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E))`. Rewrite using `[← h1, hD, map_mul, absNorm_map_algebraMap_eq_pow_finrank, Nat.cast_mul, Nat.cast_pow, absNorm_diff hζ E, hE, Real.log_mul (Finset.prod_ne_zero_iff.2 hne) (pow_ne_zero _ hdE), Real.log_prod hne, Real.log_pow]`.
-/
theorem log_discr_tower : Real.log |(discr L : ℝ)| =
    ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[E] L)).erase 1, Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| +
      Module.finrank E L * Real.log |(discr E : ℝ)| := by
  haveI : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite ℚ E L
  have hD := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 E) (𝓞 L)
  have h1 : ((Ideal.absNorm (differentIdeal ℤ (𝓞 L)) : ℕ) : ℝ) = |(discr L : ℝ)| := by
    rw [NumberField.absNorm_differentIdeal L (𝓞 L)]
    simp only [Nat.cast_natAbs, Int.cast_abs]
  have hE : ((Ideal.absNorm (differentIdeal ℤ (𝓞 E)) : ℕ) : ℝ) = |(discr E : ℝ)| := by
    rw [NumberField.absNorm_differentIdeal E (𝓞 E)]
    simp only [Nat.cast_natAbs, Int.cast_abs]
  have hne : ∀ σ ∈ (Finset.univ : Finset (L ≃ₐ[E] L)).erase 1,
      |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| ≠ 0 := by
    intro σ hσ
    have hσ1 : σ ≠ 1 := Finset.ne_of_mem_erase hσ
    have hne : ζ - σ ζ ≠ 0 := by
      intro h
      apply hσ1
      apply gal_inj hζ E
      exact (sub_eq_zero.1 h).symm
    rw [abs_ne_zero, Rat.cast_ne_zero]
    exact Algebra.norm_ne_zero_iff.2 hne
  have hdE : |(discr E : ℝ)| ≠ 0 := abs_ne_zero.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E))
  rw [← h1, hD, map_mul, absNorm_map_algebraMap_eq_pow_finrank, Nat.cast_mul, Nat.cast_pow, absNorm_diff hζ E,
    hE, Real.log_mul (Finset.prod_ne_zero_iff.2 hne) (pow_ne_zero _ hdE), Real.log_prod hne, Real.log_pow]

open Classical in
/- English proof (translation)
Establish `sum_log_aut_eq_sum_filter_lemma_4 {N : ℕ} [NeZero N] {L : Type _} [Field L] [NumberField L] [IsCyclotomicExtension {N} ℚ L] {ζ : L} (hζ : IsPrimitiveRoot ζ N) (E : Type _) [Field E] [NumberField E] [Algebra E L] : ∑ τ : L ≃ₐ[E] L, Real.log |((Algebra.norm ℚ (ζ - τ ζ) : ℚ) : ℝ)| = …`. Use `Finset.sum_bij (fun τ _ => τ.restrictScalars ℚ) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `τ _`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Introduce `x`.

Conclude with `τ.commutes x`. Introduce `a _ b _ h`. Conclude with `AlgEquiv.restrictScalars_injective ℚ h`. Introduce `σ hσ`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ`.

Conclude with `⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) hσ, Finset.mem_univ _, by ext x; rfl⟩`. Introduce `τ _`. Both sides reduce to the same expression. Establish `h1` using `log_discr_tower hζ E`. Establish `h2` using `log_discr_tower hζ ℚ`.

Rewrite `h2` using `[NumberField.discr_rat]`. Simplify using `only [Int.cast_one, abs_one, Real.log_one, mul_zero, add_zero] at h2`. Establish `e1 : ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[E] L)).erase 1, Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| = ∑ σ : L ≃ₐ[E] L, Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)|` using `Finset.sum_erase _ (by simp [Algebra.norm_zero])`. Establish `e2 : ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[ℚ] L)).erase 1, Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| = ∑ σ : L ≃ₐ[ℚ] L, Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)|` using `Finset.sum_erase _ (by simp [Algebra.norm_zero])`. Establish `hsplit : ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[ℚ] L)).filter (fun σ => ∀ x : E, σ (algebraMap E L x) = algebraMap E L x), Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| + ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[ℚ] L)).filter (fun σ => ¬ ∀ x : E, σ (algebraMap E L x) = algebraMap E L x), R …` using `Finset.sum_filter_add_sum_filter_not _ _ _`.

Establish `hsub` using `sum_log_aut_eq_sum_filter_lemma_4 hζ E`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_discr_sub : Module.finrank E L * Real.log |(discr E : ℝ)| =
    ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[ℚ] L)).filter (fun σ => ¬ ∀ x : E, σ (algebraMap E L x) = algebraMap E L x),
      Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| := by
  have sum_log_aut_eq_sum_filter_lemma_4 {N : ℕ} [NeZero N] {L : Type _} [Field L] [NumberField L] [IsCyclotomicExtension {N} ℚ L] {ζ : L} (hζ : IsPrimitiveRoot ζ N) (E : Type _) [Field E] [NumberField E] [Algebra E L] :
      ∑ τ : L ≃ₐ[E] L, Real.log |((Algebra.norm ℚ (ζ - τ ζ) : ℚ) : ℝ)| =
        ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[ℚ] L)).filter
          (fun σ => ∀ x : E, σ (algebraMap E L x) = algebraMap E L x),
          Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| := by
    refine Finset.sum_bij (fun τ _ => τ.restrictScalars ℚ) ?_ ?_ ?_ ?_
    · intro τ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro x; exact τ.commutes x
    · intro a _ b _ h; exact AlgEquiv.restrictScalars_injective ℚ h
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      exact ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) hσ, Finset.mem_univ _, by ext x; rfl⟩
    · intro τ _; rfl
  have h1 := log_discr_tower hζ E
  have h2 := log_discr_tower hζ ℚ
  rw [NumberField.discr_rat] at h2
  simp only [Int.cast_one, abs_one, Real.log_one, mul_zero, add_zero] at h2
  have e1 : ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[E] L)).erase 1, Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| =
      ∑ σ : L ≃ₐ[E] L, Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| :=
    Finset.sum_erase _ (by simp [Algebra.norm_zero])
  have e2 : ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[ℚ] L)).erase 1, Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| =
      ∑ σ : L ≃ₐ[ℚ] L, Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| :=
    Finset.sum_erase _ (by simp [Algebra.norm_zero])
  have hsplit : ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[ℚ] L)).filter
        (fun σ => ∀ x : E, σ (algebraMap E L x) = algebraMap E L x),
        Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| +
      ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[ℚ] L)).filter
        (fun σ => ¬ ∀ x : E, σ (algebraMap E L x) = algebraMap E L x),
        Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| =
      ∑ σ : L ≃ₐ[ℚ] L, Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hsub := sum_log_aut_eq_sum_filter_lemma_4 hζ E
  linarith

omit E in
/- English proof (translation)
Establish `hN : N ≠ 0` using `NeZero.ne N`. Establish `hw : (1 - u).val ≠ 0`. Rewrite using `[Ne, ZMod.val_eq_zero, sub_eq_zero]`. Conclude with `Ne.symm hu`. Establish `hmod : ζ ^ (u.val + (1 - u).val) = ζ`.

Establish `h1 : (u.val + (1 - u).val) % orderOf ζ = 1 % orderOf ζ`. Rewrite using `[← hζ.eq_orderOf, ← ZMod.val_add, show u + (1 - u) = 1 by ring, ZMod.val_one_eq_one_mod]`. Rewrite using `[← pow_mod_orderOf, h1, pow_mod_orderOf, pow_one]`. Establish `hfac : ζ - ζ ^ u.val = ζ ^ u.val * (ζ ^ (1 - u).val - 1)`. Combine the equalities or inequalities in the displayed calculation.

Establish `hnz : |((Algebra.norm ℚ ζ : ℚ) : ℝ)| = 1`. Establish `h : (Algebra.norm ℚ ζ) ^ N = 1` using `by rw [← map_pow, hζ.pow_eq_one, map_one]`. Establish `h' : |((Algebra.norm ℚ ζ : ℚ) : ℝ)| ^ N = 1`. Rewrite using `[← abs_pow, ← Rat.cast_pow, h, Rat.cast_one, abs_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (abs_nonneg _) hN).1 h'`.

Establish `hd : orderOf (ζ ^ (1 - u).val) = addOrderOf (u - 1)`. Rewrite using `[orderOf_pow' ζ hw, ← hζ.eq_orderOf, show u - 1 = -(((1 - u).val : ℕ) : ZMod N) by rw [ZMod.natCast_zmod_val]; ring, addOrderOf_neg, ZMod.addOrderOf_coe _ hN]`. Establish `hη : IsPrimitiveRoot (ζ ^ (1 - u).val) (addOrderOf (u - 1))`. Rewrite using `[← hd]`. Conclude with `IsPrimitiveRoot.orderOf _`.

Establish `hd1 : 1 < addOrderOf (u - 1)`. Establish `h0 : 0 < addOrderOf (u - 1)` using `addOrderOf_pos _`. Establish `h1 : addOrderOf (u - 1) ≠ 1`. Introduce `h`. Use `addOrderOf_nsmul_eq_zero (u - 1)` as an intermediate fact.

Rewrite `this` using `[h, one_nsmul, sub_eq_zero]`. Conclude with `hu this`. Use linear arithmetic over natural numbers and integers. Establish `key` using `log_abs_norm_sub_one_mul_totient_eq hd1 hη`. Rewrite `key` using `[IsCyclotomicExtension.finrank L (cyclotomic.irreducible_rat (NeZero.pos N))]`.

Rewrite using `[hfac, map_mul, map_pow, Rat.cast_mul, Rat.cast_pow, abs_mul, abs_pow, hnz, one_pow, one_mul]`. Establish `ht : (0 : ℝ) < (addOrderOf (u - 1)).totient` using `by exact_mod_cast Nat.totient_pos.2 (by omega)`. Rewrite using `[mul_div_assoc', eq_div_iff ht.ne']`. Conclude with `key`.
-/
theorem log_norm_weight (u : ZMod N) (hu : u ≠ 1) :
    Real.log |((Algebra.norm ℚ (ζ - ζ ^ u.val) : ℚ) : ℝ)| =
      (N.totient : ℝ) * (vonMangoldt (addOrderOf (u - 1)) / ((addOrderOf (u - 1)).totient : ℝ)) := by
  have hN : N ≠ 0 := NeZero.ne N
  have hw : (1 - u).val ≠ 0 := by
    rw [Ne, ZMod.val_eq_zero, sub_eq_zero]; exact Ne.symm hu
  have hmod : ζ ^ (u.val + (1 - u).val) = ζ := by
    have h1 : (u.val + (1 - u).val) % orderOf ζ = 1 % orderOf ζ := by
      rw [← hζ.eq_orderOf, ← ZMod.val_add, show u + (1 - u) = 1 by ring, ZMod.val_one_eq_one_mod]
    rw [← pow_mod_orderOf, h1, pow_mod_orderOf, pow_one]
  have hfac : ζ - ζ ^ u.val = ζ ^ u.val * (ζ ^ (1 - u).val - 1) := by
    calc ζ - ζ ^ u.val = ζ ^ (u.val + (1 - u).val) - ζ ^ u.val := by rw [hmod]
      _ = ζ ^ u.val * (ζ ^ (1 - u).val - 1) := by ring
  have hnz : |((Algebra.norm ℚ ζ : ℚ) : ℝ)| = 1 := by
    have h : (Algebra.norm ℚ ζ) ^ N = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    have h' : |((Algebra.norm ℚ ζ : ℚ) : ℝ)| ^ N = 1 := by
      rw [← abs_pow, ← Rat.cast_pow, h, Rat.cast_one, abs_one]
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) hN).1 h'
  have hd : orderOf (ζ ^ (1 - u).val) = addOrderOf (u - 1) := by
    rw [orderOf_pow' ζ hw, ← hζ.eq_orderOf,
      show u - 1 = -(((1 - u).val : ℕ) : ZMod N) by rw [ZMod.natCast_zmod_val]; ring,
      addOrderOf_neg, ZMod.addOrderOf_coe _ hN]
  have hη : IsPrimitiveRoot (ζ ^ (1 - u).val) (addOrderOf (u - 1)) := by
    rw [← hd]; exact IsPrimitiveRoot.orderOf _
  have hd1 : 1 < addOrderOf (u - 1) := by
    have h0 : 0 < addOrderOf (u - 1) := addOrderOf_pos _
    have h1 : addOrderOf (u - 1) ≠ 1 := by
      intro h
      have := addOrderOf_nsmul_eq_zero (u - 1)
      rw [h, one_nsmul, sub_eq_zero] at this
      exact hu this
    omega
  have key := log_abs_norm_sub_one_mul_totient_eq hd1 hη
  rw [IsCyclotomicExtension.finrank L (cyclotomic.irreducible_rat (NeZero.pos N))] at key
  rw [hfac, map_mul, map_pow, Rat.cast_mul, Rat.cast_pow, abs_mul, abs_pow, hnz, one_pow, one_mul]
  have ht : (0 : ℝ) < (addOrderOf (u - 1)).totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  rw [mul_div_assoc', eq_div_iff ht.ne']
  exact key

open Classical in

/- English proof (translation)
Use `haveI : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite ℚ E L`. Use `haveI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {N} ℚ L`. Establish `hφ : Module.finrank ℚ L = N.totient` using `IsCyclotomicExtension.finrank L (cyclotomic.irreducible_rat (NeZero.pos N))`. Establish `hcard : Fintype.card (L ≃ₐ[ℚ] L) = Fintype.card (ZMod N)ˣ`. Rewrite using `[ZMod.card_units_eq_totient, ← hφ, ← IsGalois.card_aut_eq_finrank ℚ L, Nat.card_eq_fintype_card]`.

Establish `hinj : Function.Injective (hζ.autToPow ℚ)`. Introduce `a b h`. Apply `gal_inj hζ ℚ` to reduce the goal to its premises. Use `show a ζ = b ζ`. Rewrite using `[← hζ.autToPow_spec ℚ a, ← hζ.autToPow_spec ℚ b, h]`.

Establish `hbij : Function.Bijective (hζ.autToPow ℚ)` using `(Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, hcard⟩`. Establish `hsum : ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[ℚ] L)).filter (fun σ => ¬ ∀ x : E, σ (algebraMap E L x) = algebraMap E L x), Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| = (N.totient : ℝ) * ∑ u ∈ (Finset.univ : Finset (ZMod N)ˣ).filter (fun u => u ∉ U), vonMangoldt (addOrderOf ((u : …`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_equiv (Equiv.ofBijective _ hbij) ?_ ?_` and prove the remaining obligations. Introduce `σ`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.ofBijective_apply]`. Rewrite using `[hU σ _ (hζ.autToPow_spec ℚ σ).symm]`. Introduce `σ hσ`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ`. Establish `hu : hζ.autToPow ℚ σ ∉ U` using `by rwa [← hU σ _ (hζ.autToPow_spec ℚ σ).symm]`.

Establish `hu1 : ((hζ.autToPow ℚ σ : (ZMod N)ˣ) : ZMod N) ≠ 1`. Introduce `h`. Apply `hu` to reduce the goal to its premises. Rewrite using `[Units.val_eq_one.1 h]`. Conclude with `U.one_mem`.

Simplify using `only [Equiv.ofBijective_apply]`. Rewrite using `[← hζ.autToPow_spec ℚ σ, log_norm_weight hζ _ hu1]`. Establish `key` using `log_discr_sub hζ E`. Rewrite `key` using `[hsum]`. Establish `hEQ : (0 : ℝ) < Module.finrank ℚ E` using `by exact_mod_cast Module.finrank_pos`.

Establish `hLE : (0 : ℝ) < Module.finrank E L` using `by exact_mod_cast Module.finrank_pos`. Establish `htow : (Module.finrank ℚ E : ℝ) * Module.finrank E L = N.totient`. Rewrite using `[← Nat.cast_mul, Module.finrank_mul_finrank ℚ E L, hφ]`. Rewrite using `[div_eq_iff hEQ.ne']`. Apply `mul_left_cancel₀ hLE.ne'` to reduce the goal to its premises.

Rewrite using `[key, ← htow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_rd (U : Subgroup (ZMod N)ˣ)
    (hU : ∀ (σ : L ≃ₐ[ℚ] L) (u : (ZMod N)ˣ), σ ζ = ζ ^ (u : ZMod N).val →
      ((∀ x : E, σ (algebraMap E L x) = algebraMap E L x) ↔ u ∈ U)) :
    Real.log |(discr E : ℝ)| / Module.finrank ℚ E =
      ∑ u ∈ (Finset.univ : Finset (ZMod N)ˣ).filter (fun u => u ∉ U),
        vonMangoldt (addOrderOf ((u : ZMod N) - 1)) / ((addOrderOf ((u : ZMod N) - 1)).totient : ℝ) := by
  haveI : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite ℚ E L
  haveI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {N} ℚ L
  have hφ : Module.finrank ℚ L = N.totient :=
    IsCyclotomicExtension.finrank L (cyclotomic.irreducible_rat (NeZero.pos N))
  have hcard : Fintype.card (L ≃ₐ[ℚ] L) = Fintype.card (ZMod N)ˣ := by
    rw [ZMod.card_units_eq_totient, ← hφ, ← IsGalois.card_aut_eq_finrank ℚ L, Nat.card_eq_fintype_card]
  have hinj : Function.Injective (hζ.autToPow ℚ) := by
    intro a b h
    apply gal_inj hζ ℚ
    show a ζ = b ζ
    rw [← hζ.autToPow_spec ℚ a, ← hζ.autToPow_spec ℚ b, h]
  have hbij : Function.Bijective (hζ.autToPow ℚ) :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, hcard⟩
  have hsum : ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[ℚ] L)).filter
        (fun σ => ¬ ∀ x : E, σ (algebraMap E L x) = algebraMap E L x),
        Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| =
      (N.totient : ℝ) * ∑ u ∈ (Finset.univ : Finset (ZMod N)ˣ).filter (fun u => u ∉ U),
        vonMangoldt (addOrderOf ((u : ZMod N) - 1)) / ((addOrderOf ((u : ZMod N) - 1)).totient : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_equiv (Equiv.ofBijective _ hbij) ?_ ?_
    · intro σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.ofBijective_apply]
      rw [hU σ _ (hζ.autToPow_spec ℚ σ).symm]
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      have hu : hζ.autToPow ℚ σ ∉ U := by rwa [← hU σ _ (hζ.autToPow_spec ℚ σ).symm]
      have hu1 : ((hζ.autToPow ℚ σ : (ZMod N)ˣ) : ZMod N) ≠ 1 := by
        intro h; apply hu; rw [Units.val_eq_one.1 h]; exact U.one_mem
      simp only [Equiv.ofBijective_apply]
      rw [← hζ.autToPow_spec ℚ σ, log_norm_weight hζ _ hu1]
  have key := log_discr_sub hζ E
  rw [hsum] at key
  have hEQ : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have hLE : (0 : ℝ) < Module.finrank E L := by exact_mod_cast Module.finrank_pos
  have htow : (Module.finrank ℚ E : ℝ) * Module.finrank E L = N.totient := by
    rw [← Nat.cast_mul, Module.finrank_mul_finrank ℚ E L, hφ]
  rw [div_eq_iff hEQ.ne']
  apply mul_left_cancel₀ hLE.ne'
  rw [key, ← htow]; ring

end Formalism.HC.Der.Rd

end

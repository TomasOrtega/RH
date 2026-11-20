import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe

noncomputable section

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial IntermediateField

namespace GlobalTheory.EigDecomp

/- English proof (translation)
Take `⟨α0, hα0⟩` from `Field.exists_primitive_element ℚ E`. Take `⟨d, hd, hint⟩` from `exists_integral_multiples ℤ ℚ ({α0} : Finset E)`. Establish `hi : IsIntegral ℤ (d • α0)` using `hint α0 (Finset.mem_singleton_self _)`. Set `α : 𝓞 E` to `⟨d • α0, hi⟩`. Establish `hαE : (α : E) = d • α0` using `rfl`.

Establish `hadjF : ℚ⟮(α : E)⟯ = ⊤`. Use `top_le_iff.mp (hα0 ▸ IntermediateField.adjoin_simple_le_iff.mpr ?_)` and prove the remaining obligations. Establish `h1 : α0 = ((d : ℚ)⁻¹) • (α : E)`. Rewrite using `[hαE, zsmul_eq_mul, Algebra.smul_def, ← mul_assoc, ← map_intCast (algebraMap ℚ E) d, ← map_mul, inv_mul_cancel₀ (Int.cast_ne_zero.mpr hd), map_one, one_mul]`. Rewrite using `[h1]`.

Conclude with `IntermediateField.smul_mem _ (IntermediateField.mem_adjoin_simple_self ℚ _)`. Establish `hadj : Algebra.adjoin ℚ {(α : E)} = ⊤`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (α : E)), hadjF, IntermediateField.top_toSubalgebra]`. Use `⟨α, fun τ τ' h => ?_, fun a => ?_⟩` and prove the remaining obligations. Use `AlgHom.ext_of_adjoin_eq_top hadj (φ₁ := τ.toRatAlgHom) (φ₂ := τ'.toRatAlgHom) (by rintro x rfl; exact h)` as an intermediate fact.

Use extensionality with `x`. Conclude with `congrArg (fun f : E →ₐ[ℚ] ℂ => f x) this`. Establish `ha : (a : E) ∈ Algebra.adjoin ℚ {(α : E)}` using `hadj ▸ Algebra.mem_top`. Rewrite `ha` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨g, hg⟩` from `ha`.

Take `⟨b, hbM, hb⟩` from `IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) g`. Use `⟨b, nonZeroDivisors.ne_zero hbM, IsLocalization.integerNormalization (nonZeroDivisors ℤ) g, ?_⟩` and prove the remaining obligations. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Establish `hg' : aeval (algebraMap (𝓞 E) E α) g = algebraMap (𝓞 E) E a` using `hg`. Rewrite using `[← aeval_algebraMap_apply, ← aeval_map_algebraMap ℚ, hb, map_zsmul, hg', map_zsmul]`.
-/
theorem exists_integral_separating (E : Type) [Field E] [NumberField E] :
    ∃ α : 𝓞 E, (∀ τ τ' : E →+* ℂ, τ (α : E) = τ' (α : E) → τ = τ') ∧
      ∀ a : 𝓞 E, ∃ N : ℤ, N ≠ 0 ∧ ∃ g : ℤ[X], aeval α g = N • a := by
  obtain ⟨α0, hα0⟩ := Field.exists_primitive_element ℚ E
  obtain ⟨d, hd, hint⟩ := exists_integral_multiples ℤ ℚ ({α0} : Finset E)
  have hi : IsIntegral ℤ (d • α0) := hint α0 (Finset.mem_singleton_self _)
  let α : 𝓞 E := ⟨d • α0, hi⟩
  have hαE : (α : E) = d • α0 := rfl
  have hadjF : ℚ⟮(α : E)⟯ = ⊤ := by
    refine top_le_iff.mp (hα0 ▸ IntermediateField.adjoin_simple_le_iff.mpr ?_)
    have h1 : α0 = ((d : ℚ)⁻¹) • (α : E) := by
      rw [hαE, zsmul_eq_mul, Algebra.smul_def, ← mul_assoc, ← map_intCast (algebraMap ℚ E) d, ← map_mul,
        inv_mul_cancel₀ (Int.cast_ne_zero.mpr hd), map_one, one_mul]
    rw [h1]
    exact IntermediateField.smul_mem _ (IntermediateField.mem_adjoin_simple_self ℚ _)
  have hadj : Algebra.adjoin ℚ {(α : E)} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (α : E)), hadjF, IntermediateField.top_toSubalgebra]
  refine ⟨α, fun τ τ' h => ?_, fun a => ?_⟩
  · have := AlgHom.ext_of_adjoin_eq_top hadj (φ₁ := τ.toRatAlgHom) (φ₂ := τ'.toRatAlgHom)
      (by rintro x rfl; exact h)
    ext x
    exact congrArg (fun f : E →ₐ[ℚ] ℂ => f x) this
  · have ha : (a : E) ∈ Algebra.adjoin ℚ {(α : E)} := hadj ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨g, hg⟩ := ha
    obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) g
    refine ⟨b, nonZeroDivisors.ne_zero hbM, IsLocalization.integerNormalization (nonZeroDivisors ℤ) g, ?_⟩
    apply RingOfIntegers.coe_injective
    have hg' : aeval (algebraMap (𝓞 E) E α) g = algebraMap (𝓞 E) E a := hg
    rw [← aeval_algebraMap_apply, ← aeval_map_algebraMap ℚ, hb, map_zsmul, hg', map_zsmul]

end GlobalTheory.EigDecomp

namespace GlobalTheory.EigDecomp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

/- English proof (translation)
Establish `hint : IsIntegral ℤ α` using `Algebra.IsIntegral.isIntegral α`. Establish `hintE : IsIntegral ℤ (α : E)` using `RingOfIntegers.isIntegral_coe α`. Use `symm`. Use `eq_of_monic_of_dvd_of_natDegree_le Lagrange.nodal_monic ((minpoly.monic hint).map _) ?_ ?_` and prove the remaining obligations. Rewrite using `[Lagrange.nodal]`.

Use `Finset.prod_dvd_of_coprime ((pairwise_coprime_X_sub_C hinj).set_pairwise _) fun τ _ => dvd_iff_isRoot.mpr ?_` and prove the remaining obligations. Establish `h` using `aeval_algHom_apply (embK c τ).toIntAlgHom α (minpoly ℤ α)`. Rewrite `h` using `[minpoly.aeval, map_zero]`. Rewrite using `[IsRoot.def, eval_map, ← algebraMap_int_eq, ← aeval_def]`. Conclude with `h`.

Rewrite using `[natDegree_map_eq_of_injective (RingHom.injective_int _), Lagrange.natDegree_nodal, Finset.card_univ, NumberField.Embeddings.card E ℂ, ← RingOfIntegers.minpoly_coe, ← natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int, ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ …`. Conclude with `minpoly.natDegree_le _`.
-/
theorem nodal_eq_minpoly_map (c : Coeff l) (α : 𝓞 E)
    (hinj : Function.Injective fun τ : E →+* ℂ => embK c τ α) :
    Lagrange.nodal Finset.univ (fun τ : E →+* ℂ => embK c τ α) = (minpoly ℤ α).map (Int.castRingHom c.F) := by
  have hint : IsIntegral ℤ α := Algebra.IsIntegral.isIntegral α
  have hintE : IsIntegral ℤ (α : E) := RingOfIntegers.isIntegral_coe α
  symm
  refine eq_of_monic_of_dvd_of_natDegree_le Lagrange.nodal_monic ((minpoly.monic hint).map _) ?_ ?_
  · rw [Lagrange.nodal]
    refine Finset.prod_dvd_of_coprime ((pairwise_coprime_X_sub_C hinj).set_pairwise _) fun τ _ => dvd_iff_isRoot.mpr ?_
    have h := aeval_algHom_apply (embK c τ).toIntAlgHom α (minpoly ℤ α)
    rw [minpoly.aeval, map_zero] at h
    rw [IsRoot.def, eval_map, ← algebraMap_int_eq, ← aeval_def]
    exact h
  · rw [natDegree_map_eq_of_injective (RingHom.injective_int _), Lagrange.natDegree_nodal, Finset.card_univ,
      NumberField.Embeddings.card E ℂ, ← RingOfIntegers.minpoly_coe,
      ← natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int,
      ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hintE]
    exact minpoly.natDegree_le _

end GlobalTheory.EigDecomp

namespace GlobalTheory.EigDecomp

/- English proof (translation)
Rewrite using `[Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hi, mul_left_comm]`. Use `congr 1`. Conclude with `EuclideanDomain.mul_div_cancel' (X_sub_C_ne_zero _) (Lagrange.X_sub_C_dvd_nodal v hi)`.
-/
theorem X_sub_C_mul_basis {ι F : Type*} [Field F] [DecidableEq ι] {s : Finset ι} {v : ι → F} {i : ι}
    (hi : i ∈ s) :
    (X - C (v i)) * Lagrange.basis s v i = C (Lagrange.nodalWeight s v i) * Lagrange.nodal s v := by
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hi, mul_left_comm]
  congr 1
  exact EuclideanDomain.mul_div_cancel' (X_sub_C_ne_zero _) (Lagrange.X_sub_C_dvd_nodal v hi)

/- English proof (translation)
Introduce `E _ _ _ H l c R V _ _ _ φ ρ v`. Take `⟨α, hinj, hden⟩` from `exists_integral_separating E`. Set `lam : (E →+* ℂ) → c.F` to `fun τ => embK c τ α`. Establish `hlinj : Function.Injective lam` using `fun τ τ' h => hinj τ τ' (by`. Use `congrArg (fun x : c.F => (x : ℂ)) h` as an intermediate fact.

Simplify `this)` using `[lam, embK_coe]`. Set `A : Module.End R V` to `ρ α`. Set `ψ : c.F →+* Module.End R V` to `(algebraMap R (Module.End R V)).comp φ`. Establish `hc : ∀ x, Commute (ψ x) A` using `fun x => Algebra.commute_algebraMap_left (φ x) A`. Set `ev : Polynomial c.F →+* Module.End R V` to `eval₂RingHom' ψ A hc`.

Establish `hev : ∀ p, ev p = p.eval₂ ψ A` using `fun p => rfl`. Establish `hev_int : ∀ g : ℤ[X], ev (g.map (Int.castRingHom c.F)) = aeval A g`. Introduce `g`. Rewrite using `[hev, eval₂_map, aeval_def]`. Use `congr 1`.

Conclude with `RingHom.ext_int _ _`. Establish `heig : ∀ (μ : c.F) (x : V), A x = φ μ • x → ∀ p : Polynomial c.F, ev p x = φ (p.eval μ) • x`. Introduce `μ x hx p`. Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => rw [map_add, LinearMap.add_apply, hp, hq, eval_add, map_add, add_smul]`.

Consider the case `monomial k a`. Establish `hk : ∀ k : ℕ, (A ^ k) x = φ μ ^ k • x`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`.

Consider the case `succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hx, smul_smul, pow_succ, mul_comm]`. Rewrite using `[hev, eval₂_monomial, eval_monomial, Module.End.mul_apply, hk, map_mul, map_pow]`. Simplify using `[ψ, smul_smul, mul_comm]`. Establish `hnodal : ev (Lagrange.nodal Finset.univ lam) = 0`. Rewrite using `[nodal_eq_minpoly_map c α hlinj, hev_int]`.

Establish `h` using `aeval_algHom_apply ρ.toIntAlgHom α (minpoly ℤ α)`. Rewrite `h` using `[minpoly.aeval, map_zero]`. Conclude with `h`. Set `P : (E →+* ℂ) → Module.End R V` to `fun τ => ev (Lagrange.basis Finset.univ lam τ)`. Establish `hPeig : ∀ τ x, A (P τ x) = φ (lam τ) • P τ x`.

Introduce `τ x`. Establish `h` using `congrArg (fun p => ev p x) (X_sub_C_mul_basis (s := Finset.univ) (v := lam) (Finset.mem_univ τ))`. Simplify using `only [map_mul, map_sub, hnodal, mul_zero, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.zero_apply] at h`. Rewrite `h` using `[hev X, eval₂_X, hev (C _), eval₂_C]`. Simplify `h` using `[ψ, sub_eq_zero, P]`.

Establish `hsum : ∑ τ, P τ = 1`. Simplify using `only [P]`. Rewrite using `[← map_sum, Lagrange.sum_basis hlinj.injOn Finset.univ_nonempty, map_one]`. Establish `hall : ∀ τ x, A x = φ (lam τ) • x → ∀ a, ρ a x = φ (embK c τ a) • x`. Introduce `τ x hx a`.

Take `⟨N, hN, g, hg⟩` from `hden a`. Establish `h1 : ρ (N • a) x = φ (embK c τ (N • a)) • x`. Rewrite using `[← hg]`. Establish `e1` using `aeval_algHom_apply ρ.toIntAlgHom α g`. Establish `e2` using `aeval_algHom_apply (embK c τ).toIntAlgHom α g`.

Express the relevant statement in the definitionally equal form `ρ (aeval α g) x = φ (embK c τ (aeval α g)) • x`. Rewrite using `[← show aeval A g = ρ (aeval α g) from e1, ← show aeval (lam τ) g = embK c τ (aeval α g) from e2, ← hev_int, heig _ _ hx, eval_map, ← algebraMap_int_eq, ← aeval_def]`. Establish `hu : IsUnit (N : R)`. Rewrite using `[← map_intCast φ]`. Conclude with `(isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hN)).map φ`.

Rewrite `h1` using `[map_zsmul, map_zsmul, map_zsmul, LinearMap.smul_apply, ← Int.cast_smul_eq_zsmul R, ← Int.cast_smul_eq_zsmul R, smul_assoc]`. Conclude with `hu.smul_left_cancel.mp h1`. Use `⟨fun τ => P τ v, ⟨fun τ a => hall τ _ (hPeig τ v) a, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show ∑ τ, P τ v = v`. Rewrite using `[← LinearMap.sum_apply, hsum, Module.End.one_apply]`.

Introduce and unpack `w ⟨hw, hws⟩`. Use function extensionality and compare the values at `τ`. Use `show w τ = P τ v`. Rewrite using `[← hws, map_sum, Finset.sum_eq_single τ]`. Rewrite using `[heig (lam τ) _ (hw τ α), Lagrange.eval_basis_self hlinj.injOn (Finset.mem_univ τ), map_one, one_smul]`.

Introduce `τ' _ hne`. Rewrite using `[heig (lam τ') _ (hw τ' α), Lagrange.eval_basis_of_ne (Ne.symm hne) (Finset.mem_univ τ'), map_zero, zero_smul]`. Simplify using the standard rewrite rules.
-/
theorem exists_unique_eigen_sum : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {l : Level H} (c : Coeff l) {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (φ : c.F →+* R)
    (ρ : 𝓞 E →+* Module.End R V) (v : V), ∃! w : (E →+* ℂ) → V,
      (∀ τ a, ρ a (w τ) = φ (embK c τ a) • w τ) ∧ ∑ τ, w τ = v := by
  intro E _ _ _ H l c R V _ _ _ φ ρ v
  classical
  obtain ⟨α, hinj, hden⟩ := exists_integral_separating E
  let lam : (E →+* ℂ) → c.F := fun τ => embK c τ α
  have hlinj : Function.Injective lam := fun τ τ' h => hinj τ τ' (by
    have := congrArg (fun x : c.F => (x : ℂ)) h
    simpa [lam, embK_coe] using this)
  let A : Module.End R V := ρ α
  let ψ : c.F →+* Module.End R V := (algebraMap R (Module.End R V)).comp φ
  have hc : ∀ x, Commute (ψ x) A := fun x => Algebra.commute_algebraMap_left (φ x) A
  let ev : Polynomial c.F →+* Module.End R V := eval₂RingHom' ψ A hc
  have hev : ∀ p, ev p = p.eval₂ ψ A := fun p => rfl
  have hev_int : ∀ g : ℤ[X], ev (g.map (Int.castRingHom c.F)) = aeval A g := by
    intro g
    rw [hev, eval₂_map, aeval_def]
    congr 1
    exact RingHom.ext_int _ _
  have heig : ∀ (μ : c.F) (x : V), A x = φ μ • x → ∀ p : Polynomial c.F, ev p x = φ (p.eval μ) • x := by
    intro μ x hx p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add, LinearMap.add_apply, hp, hq, eval_add, map_add, add_smul]
    | monomial k a =>
      have hk : ∀ k : ℕ, (A ^ k) x = φ μ ^ k • x := by
        intro k
        induction k with
        | zero => simp
        | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hx, smul_smul, pow_succ, mul_comm]
      rw [hev, eval₂_monomial, eval_monomial, Module.End.mul_apply, hk, map_mul, map_pow]
      simp [ψ, smul_smul, mul_comm]
  have hnodal : ev (Lagrange.nodal Finset.univ lam) = 0 := by
    rw [nodal_eq_minpoly_map c α hlinj, hev_int]
    have h := aeval_algHom_apply ρ.toIntAlgHom α (minpoly ℤ α)
    rw [minpoly.aeval, map_zero] at h
    exact h
  let P : (E →+* ℂ) → Module.End R V := fun τ => ev (Lagrange.basis Finset.univ lam τ)
  have hPeig : ∀ τ x, A (P τ x) = φ (lam τ) • P τ x := by
    intro τ x
    have h := congrArg (fun p => ev p x) (X_sub_C_mul_basis (s := Finset.univ) (v := lam) (Finset.mem_univ τ))
    simp only [map_mul, map_sub, hnodal, mul_zero, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.zero_apply] at h
    rw [hev X, eval₂_X, hev (C _), eval₂_C] at h
    simpa [ψ, sub_eq_zero, P] using h
  have hsum : ∑ τ, P τ = 1 := by
    simp only [P]
    rw [← map_sum, Lagrange.sum_basis hlinj.injOn Finset.univ_nonempty, map_one]
  have hall : ∀ τ x, A x = φ (lam τ) • x → ∀ a, ρ a x = φ (embK c τ a) • x := by
    intro τ x hx a
    obtain ⟨N, hN, g, hg⟩ := hden a
    have h1 : ρ (N • a) x = φ (embK c τ (N • a)) • x := by
      rw [← hg]
      have e1 := aeval_algHom_apply ρ.toIntAlgHom α g
      have e2 := aeval_algHom_apply (embK c τ).toIntAlgHom α g
      change ρ (aeval α g) x = φ (embK c τ (aeval α g)) • x
      rw [← show aeval A g = ρ (aeval α g) from e1, ← show aeval (lam τ) g = embK c τ (aeval α g) from e2,
        ← hev_int, heig _ _ hx, eval_map, ← algebraMap_int_eq, ← aeval_def]
    have hu : IsUnit (N : R) := by
      rw [← map_intCast φ]
      exact (isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hN)).map φ
    rw [map_zsmul, map_zsmul, map_zsmul, LinearMap.smul_apply, ← Int.cast_smul_eq_zsmul R,
      ← Int.cast_smul_eq_zsmul R, smul_assoc] at h1
    exact hu.smul_left_cancel.mp h1
  refine ⟨fun τ => P τ v, ⟨fun τ a => hall τ _ (hPeig τ v) a, ?_⟩, ?_⟩
  · show ∑ τ, P τ v = v
    rw [← LinearMap.sum_apply, hsum, Module.End.one_apply]
  · rintro w ⟨hw, hws⟩
    funext τ
    show w τ = P τ v
    rw [← hws, map_sum, Finset.sum_eq_single τ]
    · rw [heig (lam τ) _ (hw τ α), Lagrange.eval_basis_self hlinj.injOn (Finset.mem_univ τ), map_one, one_smul]
    · intro τ' _ hne
      rw [heig (lam τ') _ (hw τ' α), Lagrange.eval_basis_of_ne (Ne.symm hne) (Finset.mem_univ τ'), map_zero, zero_smul]
    · simp

end GlobalTheory.EigDecomp

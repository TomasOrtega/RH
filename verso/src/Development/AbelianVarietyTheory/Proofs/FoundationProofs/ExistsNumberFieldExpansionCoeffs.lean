import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES.NF
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

/- English proof (translation)
The claim follows from `(X.exp : X.K →+* HahnSeries ℚ Ω).injective`.
-/
theorem exp_inj (X : Tower Ω ε) : Function.Injective X.exp :=
  (X.exp : X.K →+* HahnSeries ℚ Ω).injective

/- English proof (translation)
Apply `exp_inj X` to reduce the goal to its premises. Use extensionality with `r`. Rewrite using `[X.gal_exp, AlgHom.commutes, AlgHom.commutes, HahnSeries.algebraMap_apply', HahnSeries.algebraMap_apply']`. Apply the tactic sequence `by_cases h : r = 0 <;> simp [h, HahnSeries.coeff_single]`.
-/
theorem gal_alg (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (c : Ω) :
    X.gal s (algebraMap Ω X.K c) = algebraMap Ω X.K (s c) := by
  apply exp_inj X
  ext r
  rw [X.gal_exp, AlgHom.commutes, AlgHom.commutes, HahnSeries.algebraMap_apply', HahnSeries.algebraMap_apply']
  by_cases h : r = 0 <;> simp [h, HahnSeries.coeff_single]

/- English proof (translation)
Apply `exp_inj X` to reduce the goal to its premises. Use extensionality with `r`. Rewrite using `[X.gal_exp]`. Take `⟨n, hn⟩` from `X.j_exp.2.2 r`. Rewrite using `[hn, map_intCast]`.
-/
theorem gal_j (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) : X.gal s X.jK = X.jK := by
  apply exp_inj X
  ext r
  rw [X.gal_exp]
  obtain ⟨n, hn⟩ := X.j_exp.2.2 r
  rw [hn, map_intCast]

/- English proof (translation)
Rewrite using `[Polynomial.aeval_eq_sum_range, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul, map_pow, gal_j, gal_alg]`. Distinguish the cases in `h0 : p.coeff i = 0`. Simplify using `[h0]`.

Rewrite using `[h _ (Polynomial.coeff_mem_coeffs h0)]`.
-/
theorem gal_aeval (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (p : Polynomial Ω) (h : ∀ c ∈ p.coeffs, s c = c) :
    X.gal s (Polynomial.aeval X.jK p) = Polynomial.aeval X.jK p := by
  rw [Polynomial.aeval_eq_sum_range, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, map_mul, map_pow, gal_j, gal_alg]
  by_cases h0 : p.coeff i = 0
  · simp [h0]
  · rw [h _ (Polynomial.coeff_mem_coeffs h0)]

/- English proof (translation)
Take `⟨p, hp, hf⟩` from `X.alg_j f`. Establish `key : ∀ i : ℕ, ∃ u v : Polynomial Ω, (p.coeff i : X.K) = Polynomial.aeval X.jK u / Polynomial.aeval X.jK v` using `fun i => (IntermediateField.mem_adjoin_simple_iff Ω _).1 (p.coeff i).2`. Use `choose u v huv using key`. Use `⟨⋃ i ∈ p.support, ((u i).coeffs ∪ (v i).coeffs : Set Ω), p.map (algebraMap _ X.K), ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Set.Finite.biUnion (Finset.finite_toSet _) fun i _ => (Finset.finite_toSet _).union (Finset.finite_toSet _)`.

Conclude with `Polynomial.map_ne_zero hp`. Introduce `s hs`. Establish `hP : (p.map (algebraMap _ X.K)).map (X.gal s : X.K →+* X.K) = p.map (algebraMap _ X.K)`. Use extensionality with `i`. Rewrite using `[Polynomial.coeff_map, Polynomial.coeff_map]`.

Distinguish the cases in `h0 : p.coeff i = 0`. Simplify using `[h0]`. Establish `hi : i ∈ p.support` using `Polynomial.mem_support_iff.2 h0 show X.gal s (p.coeff i : X.K) = (p.coeff i : X.K)`. Rewrite using `[huv, map_div₀, gal_aeval X s _ fun c hc => hs c (Set.mem_biUnion hi (Or.inl hc)), gal_aeval X s _ fun c hc => hs c (Set.mem_biUnion hi (Or.inr hc))]`. Establish `h1 : (p.map (algebraMap _ X.K)).IsRoot f`.

Rewrite using `[Polynomial.IsRoot, Polynomial.eval_map_algebraMap, hf]`. Rewrite using `[← hP]`. Conclude with `Polynomial.IsRoot.map (f := (X.gal s : X.K →+* X.K)) h1`.
-/
theorem exists_poly (X : Tower Ω ε) (f : X.K) : ∃ (C : Set Ω) (P : Polynomial X.K), C.Finite ∧ P ≠ 0 ∧
    ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ c ∈ C, s c = c) → P.IsRoot (X.gal s f) := by
  obtain ⟨p, hp, hf⟩ := X.alg_j f
  have key : ∀ i : ℕ, ∃ u v : Polynomial Ω, (p.coeff i : X.K) = Polynomial.aeval X.jK u / Polynomial.aeval X.jK v :=
    fun i => (IntermediateField.mem_adjoin_simple_iff Ω _).1 (p.coeff i).2
  choose u v huv using key
  refine ⟨⋃ i ∈ p.support, ((u i).coeffs ∪ (v i).coeffs : Set Ω), p.map (algebraMap _ X.K), ?_, ?_, ?_⟩
  · exact Set.Finite.biUnion (Finset.finite_toSet _) fun i _ => (Finset.finite_toSet _).union (Finset.finite_toSet _)
  · exact Polynomial.map_ne_zero hp
  · intro s hs
    have hP : (p.map (algebraMap _ X.K)).map (X.gal s : X.K →+* X.K) = p.map (algebraMap _ X.K) := by
      ext i
      rw [Polynomial.coeff_map, Polynomial.coeff_map]
      by_cases h0 : p.coeff i = 0
      · simp [h0]
      · have hi : i ∈ p.support := Polynomial.mem_support_iff.2 h0
        show X.gal s (p.coeff i : X.K) = (p.coeff i : X.K)
        rw [huv, map_div₀, gal_aeval X s _ fun c hc => hs c (Set.mem_biUnion hi (Or.inl hc)),
          gal_aeval X s _ fun c hc => hs c (Set.mem_biUnion hi (Or.inr hc))]
    have h1 : (p.map (algebraMap _ X.K)).IsRoot f := by
      rw [Polynomial.IsRoot, Polynomial.eval_map_algebraMap, hf]
    rw [← hP]
    exact Polynomial.IsRoot.map (f := (X.gal s : X.K →+* X.K)) h1

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Take `⟨C, P, hC, hP, hroot⟩` from `exists_poly X f`. Use `haveI := hC.to_subtype`. Set `F₀ : IntermediateField ℚ Ω` to `IntermediateField.adjoin ℚ C`. Use `haveI : FiniteDimensional ℚ F₀ := IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x`.

Use `haveI : @IsScalarTower ℚ F₀ Ω Algebra.toSMul Algebra.toSMul Algebra.toSMul := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)`. Use `haveI : Normal F₀ Ω := IntermediateField.normal ℚ Ω F₀`. Set `L : Finset ℚ → IntermediateField F₀ Ω` to `fun T => IntermediateField.adjoin F₀ ((T.image fun r => (X.exp f).coeff r : Finset Ω) : Set Ω)`. Establish `hfin : ∀ T, FiniteDimensional F₀ (L T)` using `fun T => IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x`. Establish `hb : ∀ T, Module.finrank F₀ (L T) ≤ P.natDegree`.

Introduce `T`. Use `haveI := hfin T`. Use `haveI : Algebra.IsSeparable F₀ (L T) := by haveI : CharZero F₀ := algebraRat.charZero F₀ infer_instance`. Rewrite using `[← AlgHom.card F₀ (L T) Ω]`. Set `e : (L T →ₐ[F₀] Ω) → (Ω ≃ₐ[ℚ] Ω)` to `fun σ => (AlgEquiv.ofBijective (σ.liftNormal Ω) (Algebra.IsAlgebraic.algHom_bijective _)).restrictScalars ℚ`.

Establish `he : ∀ σ (x : L T), e σ x = σ x` using `fun σ x => σ.liftNormal_commutes Ω x`. Establish `hm : ∀ σ, X.gal (e σ) f ∈ P.roots.toFinset`. Introduce `σ`. Rewrite using `[Multiset.mem_toFinset, Polynomial.mem_roots hP]`. Conclude with `hroot _ fun c hc => (σ.liftNormal Ω).commutes (⟨c, IntermediateField.subset_adjoin ℚ C hc⟩ : F₀)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.card_univ]`. Use `Finset.card_le_card_of_injOn (fun σ => X.gal (e σ) f) (fun σ _ => hm σ) ?_` and prove the remaining obligations. Introduce `σ _ τ _ h`. Apply `IntermediateField.adjoin_algHom_ext` to reduce the goal to its premises.

Introduce `x hx`. Rewrite using `[← he, ← he]`. Take `⟨r, -, rfl⟩` from `Finset.mem_image.1 hx`. Use `show e σ ((X.exp f).coeff r) = e τ ((X.exp f).coeff r)`. Rewrite using `[← X.gal_exp, ← X.gal_exp]`.

Conclude with `congrArg (fun g => (X.exp g).coeff r) h`. Use `_ ≤ _ := (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' P)`. Establish `hB : BddAbove (Set.range fun T => Module.finrank F₀ (L T))` using `⟨P.natDegree, by rintro _ ⟨T, rfl⟩; exact hb T⟩`. Take `⟨T, hT⟩` from `Nat.sSup_mem (Set.range_nonempty fun T => Module.finrank F₀ (L T)) hB`. Use `haveI := hfin T`.

Use `⟨(L T).restrictScalars ℚ, FiniteDimensional.trans ℚ F₀ (L T), fun r => ?_⟩` and prove the remaining obligations. Use `haveI := hfin (insert r T)`. Establish `h : L T = L (insert r T)`. Use `IntermediateField.eq_of_le_of_finrank_le (IntermediateField.adjoin.mono _ _ _ ?_) ?_` and prove the remaining obligations. Conclude with `Finset.coe_subset.2 (Finset.image_subset_image (Finset.subset_insert _ _))`.

Conclude with `(le_csSup hB ⟨_, rfl⟩).trans hT.ge`. Rewrite using `[IntermediateField.mem_restrictScalars, h]`. Conclude with `IntermediateField.subset_adjoin _ _ (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _)))`.
-/
theorem coeff_numberField {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (f : X.K) :
    ∃ F : IntermediateField ℚ Ω, FiniteDimensional ℚ F ∧ ∀ r : ℚ, (X.exp f).coeff r ∈ F := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨C, P, hC, hP, hroot⟩ := exists_poly X f
  haveI := hC.to_subtype
  let F₀ : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ C
  haveI : FiniteDimensional ℚ F₀ :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  haveI : @IsScalarTower ℚ F₀ Ω Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Normal F₀ Ω := IntermediateField.normal ℚ Ω F₀
  let L : Finset ℚ → IntermediateField F₀ Ω := fun T =>
    IntermediateField.adjoin F₀ ((T.image fun r => (X.exp f).coeff r : Finset Ω) : Set Ω)
  have hfin : ∀ T, FiniteDimensional F₀ (L T) := fun T =>
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hb : ∀ T, Module.finrank F₀ (L T) ≤ P.natDegree := by
    intro T
    haveI := hfin T
    haveI : Algebra.IsSeparable F₀ (L T) := by
      haveI : CharZero F₀ := algebraRat.charZero F₀
      infer_instance
    rw [← AlgHom.card F₀ (L T) Ω]
    let e : (L T →ₐ[F₀] Ω) → (Ω ≃ₐ[ℚ] Ω) := fun σ =>
      (AlgEquiv.ofBijective (σ.liftNormal Ω) (Algebra.IsAlgebraic.algHom_bijective _)).restrictScalars ℚ
    have he : ∀ σ (x : L T), e σ x = σ x := fun σ x => σ.liftNormal_commutes Ω x
    have hm : ∀ σ, X.gal (e σ) f ∈ P.roots.toFinset := by
      intro σ
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
      exact hroot _ fun c hc => (σ.liftNormal Ω).commutes (⟨c, IntermediateField.subset_adjoin ℚ C hc⟩ : F₀)
    calc Fintype.card (L T →ₐ[F₀] Ω) ≤ P.roots.toFinset.card := by
          rw [← Finset.card_univ]
          refine Finset.card_le_card_of_injOn (fun σ => X.gal (e σ) f) (fun σ _ => hm σ) ?_
          intro σ _ τ _ h
          apply IntermediateField.adjoin_algHom_ext
          intro x hx
          rw [← he, ← he]
          obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hx
          show e σ ((X.exp f).coeff r) = e τ ((X.exp f).coeff r)
          rw [← X.gal_exp, ← X.gal_exp]
          exact congrArg (fun g => (X.exp g).coeff r) h
      _ ≤ _ := (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' P)
  have hB : BddAbove (Set.range fun T => Module.finrank F₀ (L T)) := ⟨P.natDegree, by rintro _ ⟨T, rfl⟩; exact hb T⟩
  obtain ⟨T, hT⟩ := Nat.sSup_mem (Set.range_nonempty fun T => Module.finrank F₀ (L T)) hB
  haveI := hfin T
  refine ⟨(L T).restrictScalars ℚ, FiniteDimensional.trans ℚ F₀ (L T), fun r => ?_⟩
  haveI := hfin (insert r T)
  have h : L T = L (insert r T) := by
    refine IntermediateField.eq_of_le_of_finrank_le (IntermediateField.adjoin.mono _ _ _ ?_) ?_
    · exact Finset.coe_subset.2 (Finset.image_subset_image (Finset.subset_insert _ _))
    · exact (le_csSup hB ⟨_, rfl⟩).trans hT.ge
  rw [IntermediateField.mem_restrictScalars, h]
  exact IntermediateField.subset_adjoin _ _ (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _)))

end GlobalTheory.KZ.ES.NF

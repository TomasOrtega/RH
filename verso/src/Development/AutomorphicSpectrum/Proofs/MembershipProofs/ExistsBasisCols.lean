import Mathlib
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.OrderOKOneInert
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.MatSat

/- English proof (translation)
Take `⟨n, S⟩` from `Submodule.smithNormalForm (Pi.basisFun O (β ⊕ γ)) (LinearMap.range A.mulVecLin)`. Take `⟨φ⟩ : Nonempty (Fin n ≃ β)` from `⟨S.bN.indexEquiv ((Pi.basisFun O β).map (LinearEquiv.ofInjective A.mulVecLin hA))⟩`. Take `⟨f', hf'⟩ : ∃ f' : β ↪ β ⊕ γ, ∀ b, f' b = S.f (φ.symm b)` from `⟨φ.symm.toEmbedding.trans S.f, fun _ => rfl⟩`. Establish `hcard : Fintype.card γ = Fintype.card ((Set.range f')ᶜ : Set (β ⊕ γ))`. Rewrite using `[Fintype.card_compl_set, Set.card_range_of_injective f'.injective, Fintype.card_sum]`.

Use linear arithmetic over natural numbers and integers. Take `⟨e, he⟩ : ∃ e : β ⊕ γ ≃ β ⊕ γ, ∀ b, e (Sum.inl b) = f' b` from `⟨(Equiv.sumCongr (Equiv.ofInjective f' f'.injective) (Fintype.equivOfCardEq hcard)).trans (Equiv.Set.sumCompl (Set.range f')), fun b => by simp⟩`. Take `⟨P, hPdef⟩ : ∃ P : Matrix (β ⊕ γ) (β ⊕ γ) O, P = (Pi.basisFun O (β ⊕ γ)).toMatrix (S.bM.reindex e.symm)` from `⟨_, rfl⟩`. Establish `hPdet : IsUnit P.det`. Use `letI := (Pi.basisFun O (β ⊕ γ)).invertibleToMatrix (S.bM.reindex e.symm)`.

Rewrite using `[hPdef]`. Conclude with `Matrix.isUnit_det_of_invertible _`. Establish `hP1 : ∀ i b, P.toCols₁ i b = S.bM (f' b) i`. Introduce `i b`. Use `show P i (Sum.inl b) = _`.

Rewrite using `[hPdef, Module.Basis.toMatrix_apply, Pi.basisFun_repr, Module.Basis.reindex_apply, Equiv.symm_symm, he]`. Establish `hpre : ∀ b, ∃ v : β → O, A *ᵥ v = (S.bN (φ.symm b) : β ⊕ γ → O)`. Introduce `b`. Take `⟨v, hv⟩` from `LinearMap.mem_range.1 (S.bN (φ.symm b)).2`. Conclude with `⟨v, hv⟩`.

Use `choose pre hpre using hpre`. Take `⟨s, hs⟩ : ∃ s : Matrix β β O, ∀ i b, s i b = pre b i` from `⟨Matrix.of fun i b => pre b i, fun _ _ => rfl⟩`. Establish `ha : ∀ b, S.a (φ.symm b) ≠ 0`. Introduce `b h`. Establish `h1` using `S.snf (φ.symm b)`.

Rewrite `h1` using `[h, zero_smul]`. Conclude with `S.bN.ne_zero _ ((Submodule.coe_eq_zero).1 h1)`. Take `⟨u, hu⟩ : ∃ u : Matrix β β O, ∀ b' b, u b' b = S.bN.repr ⟨A.mulVecLin (Pi.single b 1), LinearMap.mem_range_self _ _⟩ (φ.symm b') * S.a (φ.symm b')` from `⟨Matrix.of fun b' b => S.bN.repr ⟨A.mulVecLin (Pi.single b 1), LinearMap.mem_range_self _ _⟩ (φ.symm b') * S.a (φ.symm b'), fun _ _ => rfl⟩`. Use `⟨P, fun b => S.a (φ.symm b), s, u, hPdet, ha, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `i b`.

Rewrite using `[Matrix.mul_diagonal, hP1, Matrix.mul_apply]`. Establish `h1` using `congrFun (hpre b) i`. Simplify using `only [Matrix.mulVec, dotProduct] at h1`. Simplify using `only [hs]`. Rewrite using `[h1, S.snf, hf']`.

Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Use extensionality with `i b`. Establish `hw` using `S.bN.sum_repr ⟨A.mulVecLin (Pi.single b 1), LinearMap.mem_range_self _ _⟩`. Establish `hw'` using `congrArg (fun v : LinearMap.range A.mulVecLin => (v : β ⊕ γ → O) i) hw`.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, S.snf] at hw'`. Establish `hcol : (A.mulVecLin (Pi.single b 1)) i = A i b`. Simplify using `[Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]`. Rewrite using `[Matrix.mul_apply]`. Use `hcol.symm.trans (hw'.symm.trans ?_)` and prove the remaining obligations.

Simplify using `only [hP1, hu, hf']`. Use `Fintype.sum_equiv φ _ _ fun k => ?_` and prove the remaining obligations. Simplify using `only [Equiv.symm_apply_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_basis_cols {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (A : Matrix (β ⊕ γ) β O) (hA : Function.Injective A.mulVecLin) :
    ∃ (P : Matrix (β ⊕ γ) (β ⊕ γ) O) (a : β → O) (s u : Matrix β β O),
      IsUnit P.det ∧ (∀ j, a j ≠ 0) ∧ A * s = P.toCols₁ * Matrix.diagonal a ∧
        A = P.toCols₁ * u := by
  classical
  obtain ⟨n, S⟩ := Submodule.smithNormalForm (Pi.basisFun O (β ⊕ γ)) (LinearMap.range A.mulVecLin)
  obtain ⟨φ⟩ : Nonempty (Fin n ≃ β) :=
    ⟨S.bN.indexEquiv ((Pi.basisFun O β).map (LinearEquiv.ofInjective A.mulVecLin hA))⟩
  obtain ⟨f', hf'⟩ : ∃ f' : β ↪ β ⊕ γ, ∀ b, f' b = S.f (φ.symm b) :=
    ⟨φ.symm.toEmbedding.trans S.f, fun _ => rfl⟩
  have hcard : Fintype.card γ = Fintype.card ((Set.range f')ᶜ : Set (β ⊕ γ)) := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective f'.injective, Fintype.card_sum]
    omega
  obtain ⟨e, he⟩ : ∃ e : β ⊕ γ ≃ β ⊕ γ, ∀ b, e (Sum.inl b) = f' b :=
    ⟨(Equiv.sumCongr (Equiv.ofInjective f' f'.injective) (Fintype.equivOfCardEq hcard)).trans
      (Equiv.Set.sumCompl (Set.range f')), fun b => by simp⟩
  obtain ⟨P, hPdef⟩ : ∃ P : Matrix (β ⊕ γ) (β ⊕ γ) O,
      P = (Pi.basisFun O (β ⊕ γ)).toMatrix (S.bM.reindex e.symm) := ⟨_, rfl⟩
  have hPdet : IsUnit P.det := by
    letI := (Pi.basisFun O (β ⊕ γ)).invertibleToMatrix (S.bM.reindex e.symm)
    rw [hPdef]
    exact Matrix.isUnit_det_of_invertible _
  have hP1 : ∀ i b, P.toCols₁ i b = S.bM (f' b) i := by
    intro i b
    show P i (Sum.inl b) = _
    rw [hPdef, Module.Basis.toMatrix_apply, Pi.basisFun_repr, Module.Basis.reindex_apply,
      Equiv.symm_symm, he]
  have hpre : ∀ b, ∃ v : β → O, A *ᵥ v = (S.bN (φ.symm b) : β ⊕ γ → O) := by
    intro b
    obtain ⟨v, hv⟩ := LinearMap.mem_range.1 (S.bN (φ.symm b)).2
    exact ⟨v, hv⟩
  choose pre hpre using hpre
  obtain ⟨s, hs⟩ : ∃ s : Matrix β β O, ∀ i b, s i b = pre b i :=
    ⟨Matrix.of fun i b => pre b i, fun _ _ => rfl⟩
  have ha : ∀ b, S.a (φ.symm b) ≠ 0 := by
    intro b h
    have h1 := S.snf (φ.symm b)
    rw [h, zero_smul] at h1
    exact S.bN.ne_zero _ ((Submodule.coe_eq_zero).1 h1)
  obtain ⟨u, hu⟩ : ∃ u : Matrix β β O, ∀ b' b, u b' b =
      S.bN.repr ⟨A.mulVecLin (Pi.single b 1), LinearMap.mem_range_self _ _⟩ (φ.symm b') *
        S.a (φ.symm b') :=
    ⟨Matrix.of fun b' b => S.bN.repr ⟨A.mulVecLin (Pi.single b 1), LinearMap.mem_range_self _ _⟩
      (φ.symm b') * S.a (φ.symm b'), fun _ _ => rfl⟩
  refine ⟨P, fun b => S.a (φ.symm b), s, u, hPdet, ha, ?_, ?_⟩
  · ext i b
    rw [Matrix.mul_diagonal, hP1, Matrix.mul_apply]
    have h1 := congrFun (hpre b) i
    simp only [Matrix.mulVec, dotProduct] at h1
    simp only [hs]
    rw [h1, S.snf, hf']
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · ext i b
    have hw := S.bN.sum_repr ⟨A.mulVecLin (Pi.single b 1), LinearMap.mem_range_self _ _⟩
    have hw' := congrArg (fun v : LinearMap.range A.mulVecLin => (v : β ⊕ γ → O) i) hw
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, S.snf] at hw'
    have hcol : (A.mulVecLin (Pi.single b 1)) i = A i b := by
      simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [Matrix.mul_apply]
    refine hcol.symm.trans (hw'.symm.trans ?_)
    simp only [hP1, hu, hf']
    refine Fintype.sum_equiv φ _ _ fun k => ?_
    simp only [Equiv.symm_apply_apply]
    ring

/- English proof (translation)
Take `⟨L, hL⟩` from `hC`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) (fun p : (β ⊕ γ) × β => C p.1 p.2)`. Establish `hb' : ∀ p : (β ⊕ γ) × β, ∃ x : O, algebraMap O K x = algebraMap O K (b : O) * C p.1 p.2`. Introduce `p`. Take `⟨x, hx⟩` from `RingHom.mem_rangeS.1 (hb p)`.

Conclude with `⟨x, by rw [hx, Algebra.smul_def]⟩`. Use `choose c hc using hb'`. Establish `hbne : algebraMap O K (b : O) ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2`. Take `⟨C₁, hC₁⟩ : ∃ C₁ : Matrix (β ⊕ γ) β O, C₁.map (algebraMap O K) = algebraMap O K (b : O) • C` from `⟨Matrix.of fun i j => c (i, j), by ext i j; simp [hc]⟩`. Establish `hinj : Function.Injective C₁.mulVecLin`.

Introduce `v w hvw`. Establish `h1 : C₁ *ᵥ v = C₁ *ᵥ w` using `hvw`. Establish `h2 : ∀ x : β → O, (algebraMap O K) ∘ (C₁ *ᵥ x) = algebraMap O K (b : O) • (C *ᵥ ((algebraMap O K) ∘ x))`. Introduce `x`. Use function extensionality and compare the values at `i`.

Rewrite using `[Function.comp_apply, RingHom.map_mulVec, hC₁]`. Use `first`. Consider the case `rw [Matrix.smul_mulVec]`. Consider the case `simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]`. Establish `e1` using `h2 v`.

Establish `e2` using `h2 w`. Rewrite `e1` using `[h1]`. Establish `h3 : C *ᵥ ((algebraMap O K) ∘ v) = C *ᵥ ((algebraMap O K) ∘ w)` using `smul_right_injective (β ⊕ γ → K) hbne (e1.symm.trans e2)`. Establish `h4 : (algebraMap O K) ∘ v = (algebraMap O K) ∘ w`. Use `congrArg (fun z => L *ᵥ z) h3` as an intermediate fact.

Simplify `this` using `only [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]`. Use function extensionality and compare the values at `i`. Conclude with `IsFractionRing.injective O K (congrFun h4 i)`. Take `⟨P, a, s, u, hP, -, -, hu⟩` from `exists_basis_cols C₁ hinj`. Establish `hCw : C = (P.toCols₁.map (algebraMap O K)) * ((algebraMap O K (b : O))⁻¹ • u.map (algebraMap O K))`.

Establish `e1 : algebraMap O K (b : O) • C = (P.toCols₁.map (algebraMap O K)) * (u.map (algebraMap O K))`. Rewrite using `[← hC₁, hu, Matrix.map_mul]`. Rewrite using `[Matrix.mul_smul, ← e1, smul_smul, inv_mul_cancel₀ hbne, one_smul]`. Establish `hLw : (L * P.toCols₁.map (algebraMap O K)) * ((algebraMap O K (b : O))⁻¹ • u.map (algebraMap O K)) = 1`. Rewrite using `[Matrix.mul_assoc, ← hCw, hL]`.

Establish `hwL : ((algebraMap O K (b : O))⁻¹ • u.map (algebraMap O K)) * (L * P.toCols₁.map (algebraMap O K)) = 1` using `by first`. Consider the case `exact mul_eq_one_comm.1 hLw`. Consider the case `exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) |>.1 hLw`. Use `⟨⟨L * P.toCols₁.map (algebraMap O K), (algebraMap O K (b : O))⁻¹ • u.map (algebraMap O K), hLw, hwL⟩, P.toCols₁, P.toCols₂, ?_, ?_⟩` and prove the remaining obligations. Use `show C * (L * P.toCols₁.map (algebraMap O K)) = P.toCols₁.map (algebraMap O K)`.

Rewrite using `[hCw, Matrix.mul_assoc, hwL, Matrix.mul_one]`. Rewrite using `[Matrix.fromCols_toCols]`. Conclude with `hP`.
-/
theorem exists_saturation {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] {β γ : Type} [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] (C : Matrix (β ⊕ γ) β K)
    (hC : ∃ L : Matrix β (β ⊕ γ) K, L * C = 1) :
    ∃ (t : GL β K) (C₀ : Matrix (β ⊕ γ) β O) (D : Matrix (β ⊕ γ) γ O),
      C * (t : Matrix β β K) = C₀.map (algebraMap O K) ∧
        IsUnit (Matrix.fromCols C₀ D).det := by
  classical
  obtain ⟨L, hL⟩ := hC
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
    (fun p : (β ⊕ γ) × β => C p.1 p.2)
  have hb' : ∀ p : (β ⊕ γ) × β, ∃ x : O,
      algebraMap O K x = algebraMap O K (b : O) * C p.1 p.2 := by
    intro p
    obtain ⟨x, hx⟩ := RingHom.mem_rangeS.1 (hb p)
    exact ⟨x, by rw [hx, Algebra.smul_def]⟩
  choose c hc using hb'
  have hbne : algebraMap O K (b : O) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : Matrix (β ⊕ γ) β O,
      C₁.map (algebraMap O K) = algebraMap O K (b : O) • C :=
    ⟨Matrix.of fun i j => c (i, j), by ext i j; simp [hc]⟩
  have hinj : Function.Injective C₁.mulVecLin := by
    intro v w hvw
    have h1 : C₁ *ᵥ v = C₁ *ᵥ w := hvw
    have h2 : ∀ x : β → O, (algebraMap O K) ∘ (C₁ *ᵥ x) =
        algebraMap O K (b : O) • (C *ᵥ ((algebraMap O K) ∘ x)) := by
      intro x
      funext i
      rw [Function.comp_apply, RingHom.map_mulVec, hC₁]
      first
      | rw [Matrix.smul_mulVec]
      | simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    have e1 := h2 v
    have e2 := h2 w
    rw [h1] at e1
    have h3 : C *ᵥ ((algebraMap O K) ∘ v) = C *ᵥ ((algebraMap O K) ∘ w) :=
      smul_right_injective (β ⊕ γ → K) hbne (e1.symm.trans e2)
    have h4 : (algebraMap O K) ∘ v = (algebraMap O K) ∘ w := by
      have := congrArg (fun z => L *ᵥ z) h3
      simpa only [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec] using this
    funext i
    exact IsFractionRing.injective O K (congrFun h4 i)
  obtain ⟨P, a, s, u, hP, -, -, hu⟩ := exists_basis_cols C₁ hinj
  have hCw : C = (P.toCols₁.map (algebraMap O K)) *
      ((algebraMap O K (b : O))⁻¹ • u.map (algebraMap O K)) := by
    have e1 : algebraMap O K (b : O) • C = (P.toCols₁.map (algebraMap O K)) * (u.map (algebraMap O K)) := by
      rw [← hC₁, hu, Matrix.map_mul]
    rw [Matrix.mul_smul, ← e1, smul_smul, inv_mul_cancel₀ hbne, one_smul]
  have hLw : (L * P.toCols₁.map (algebraMap O K)) *
      ((algebraMap O K (b : O))⁻¹ • u.map (algebraMap O K)) = 1 := by
    rw [Matrix.mul_assoc, ← hCw, hL]
  have hwL : ((algebraMap O K (b : O))⁻¹ • u.map (algebraMap O K)) *
      (L * P.toCols₁.map (algebraMap O K)) = 1 := by
    first
    | exact mul_eq_one_comm.1 hLw
    | exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) |>.1 hLw
  refine ⟨⟨L * P.toCols₁.map (algebraMap O K),
    (algebraMap O K (b : O))⁻¹ • u.map (algebraMap O K), hLw, hwL⟩, P.toCols₁, P.toCols₂, ?_, ?_⟩
  · show C * (L * P.toCols₁.map (algebraMap O K)) = P.toCols₁.map (algebraMap O K)
    rw [hCw, Matrix.mul_assoc, hwL, Matrix.mul_one]
  · rw [Matrix.fromCols_toCols]
    exact hP

end GlobalTheory.CompanionTheory.MatSat

import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open Polynomial

namespace GlobalTheory

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Establish `hx' : x ∈ maximalIdeal A` using `(mem_maximalIdeal x).2 hx`. Establish `hy' : y ∈ maximalIdeal A`. Use `Ideal.sub_mem _ hx' h` as an intermediate fact. Simplify using `using this`.

Conclude with `(mem_maximalIdeal y).1 hy' hy`.
-/
theorem isUnit_of_sub_mem_maximalIdeal' {A : Type*} [CommRing A] [IsLocalRing A] {x y : A}
    (h : x - y ∈ maximalIdeal A) (hy : IsUnit y) : IsUnit x := by
  by_contra hx
  have hx' : x ∈ maximalIdeal A := (mem_maximalIdeal x).2 hx
  have hy' : y ∈ maximalIdeal A := by
    have := Ideal.sub_mem _ hx' h
    simpa using this
  exact (mem_maximalIdeal y).1 hy' hy

/- English proof (translation)
Use `set h := f /ₘ (X - C b) with hh`. Establish `hf : f = (X - C b) * h` using `(mul_divByMonic_eq_iff_isRoot.2 hb).symm`. Establish `hd : f.derivative.eval b = h.eval b`. Rewrite using `[hf]`. Simplify using `[derivative_mul]`.

Establish `hub : IsUnit (h.eval b)`. Rewrite using `[← hd]`. Use `isUnit_of_sub_mem_maximalIdeal' ?_ hu` and prove the remaining obligations. Take `⟨c, hc⟩` from `sub_dvd_eval_sub b a₀ f.derivative`. Rewrite using `[hc]`.

Conclude with `Ideal.mul_mem_right _ _ h1`. Establish `hub' : IsUnit (h.eval b')`. Use `isUnit_of_sub_mem_maximalIdeal' ?_ hub` and prove the remaining obligations. Take `⟨c, hc⟩` from `sub_dvd_eval_sub b' b h`. Rewrite using `[hc]`.

Apply `Ideal.mul_mem_right` to reduce the goal to its premises. Use `Ideal.sub_mem _ h2 h1` as an intermediate fact. Simplify using `using this`. Establish `e : (b' - b) * h.eval b' = 0`. Use `hb'` as an intermediate fact.

Rewrite `this` using `[IsRoot, hf]`. Simplify using `using this`. Break down `mul_eq_zero.1 e with e | e` into its components or cases. Conclude with `sub_eq_zero.1 e`. Conclude with `absurd e hub'.ne_zero`.
-/
theorem eq_of_isRoot_of_sub_mem_maximalIdeal {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    {f : A[X]} {a₀ b b' : A} (hu : IsUnit (f.derivative.eval a₀)) (hb : f.IsRoot b) (hb' : f.IsRoot b')
    (h1 : b - a₀ ∈ maximalIdeal A) (h2 : b' - a₀ ∈ maximalIdeal A) : b' = b := by
  set h := f /ₘ (X - C b) with hh
  have hf : f = (X - C b) * h := (mul_divByMonic_eq_iff_isRoot.2 hb).symm
  have hd : f.derivative.eval b = h.eval b := by
    rw [hf]
    simp [derivative_mul]
  have hub : IsUnit (h.eval b) := by
    rw [← hd]
    refine isUnit_of_sub_mem_maximalIdeal' ?_ hu
    obtain ⟨c, hc⟩ := sub_dvd_eval_sub b a₀ f.derivative
    rw [hc]
    exact Ideal.mul_mem_right _ _ h1
  have hub' : IsUnit (h.eval b') := by
    refine isUnit_of_sub_mem_maximalIdeal' ?_ hub
    obtain ⟨c, hc⟩ := sub_dvd_eval_sub b' b h
    rw [hc]
    apply Ideal.mul_mem_right
    have := Ideal.sub_mem _ h2 h1
    simpa using this
  have e : (b' - b) * h.eval b' = 0 := by
    have := hb'
    rw [IsRoot, hf] at this
    simpa using this
  rcases mul_eq_zero.1 e with e | e
  · exact sub_eq_zero.1 e
  · exact absurd e hub'.ne_zero

end GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Take `⟨W, rfl⟩` from `exists_valuationSubring_comap_eq V (algebraMap Ω (AlgebraicClosure Ω))`. Use `@HenselianLocalRing.mk _ _ inferInstance ?_` and prove the remaining obligations. Introduce `f hf a₀ h₁ h₂`. Use `set ψ := comapToValuationSubring W (algebraMap Ω (AlgebraicClosure Ω))`. Use `set ιW := algebraMap W (AlgebraicClosure Ω)`.

Use `set G := f.map ψ with hG`. Use `set F := G.map ιW with hF`. Establish `hFm : F.Monic` using `(hf.map ψ).map ιW`. Establish `hint : ∀ r ∈ F.roots, ∃ r' : W, ιW r' = r`. Introduce `r hr`.

Establish `hi : IsIntegral W r` using `⟨G, hf.map ψ, by`. Rewrite using `[← Polynomial.eval_map]`. Conclude with `(mem_roots hFm.ne_zero).1 hr⟩`. Conclude with `IsIntegrallyClosed.isIntegral_iff.1 hi`. Establish `hψm : ψ (f.eval a₀) ∈ maximalIdeal W` using `(mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 h₁ (IsUnit.of_map ψ _ hu)`.

Choose the witnesses or unpack the hypotheses as in `⟨r, hr, hrv⟩ : ∃ r ∈ F.roots, W.valuation (ιW (ψ a₀) - r) < 1 := by`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hprod : F.eval (ιW (ψ a₀)) = (F.roots.map fun r => ιW (ψ a₀) - r).prod` using `by conv_lhs => rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hFm IsAlgClosed.card_roots_eq_natDegree]`. Rewrite using `[eval_multiset_prod, Multiset.map_map]`.

Simplify using the standard rewrite rules. Establish `h1 : W.valuation (F.eval (ιW (ψ a₀))) = 1`. Rewrite using `[hprod, map_multiset_prod, Multiset.map_map]`. Apply `Multiset.prod_eq_one` to reduce the goal to its premises. Introduce `x hx`.

Take `⟨y, hy, rfl⟩` from `Multiset.mem_map.1 hx`. Establish `hle` using `hne y hy`. Take `⟨y', rfl⟩` from `hint y hy`. Use `le_antisymm ?_ hle` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`.

Rewrite using `[← map_sub]`. Conclude with `W.valuation_le_one (ψ a₀ - y')`. Establish `h2 : W.valuation (F.eval (ιW (ψ a₀))) < 1`. Rewrite using `[hF, Polynomial.eval_map, eval₂_at_apply, hG, Polynomial.eval_map, eval₂_at_apply]`. Conclude with `(W.valuation_lt_one_iff _).1 hψm`.

Conclude with `absurd h1 h2.ne`. Take `⟨r', rfl⟩` from `hint r hr`. Establish `hr'm : r' - ψ a₀ ∈ maximalIdeal W`. Rewrite using `[← neg_sub, Ideal.neg_mem_iff, W.valuation_lt_one_iff]`. Simplify `hrv` using `[ιW]`.

Establish `hGd : IsUnit (G.derivative.eval r')`. Use `isUnit_of_sub_mem_maximalIdeal' ?_ (y := G.derivative.eval (ψ a₀)) ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `sub_dvd_eval_sub r' (ψ a₀) G.derivative`. Rewrite using `[hc]`. Conclude with `Ideal.mul_mem_right _ _ hr'm`.

Rewrite using `[hG, derivative_map, Polynomial.eval_map, eval₂_at_apply]`. Conclude with `h₂.map ψ`. Establish `hFd : F.derivative.eval (ιW r') ≠ 0`. Rewrite using `[hF, derivative_map, Polynomial.eval_map, eval₂_at_apply]`. Conclude with `fun e => hGd.ne_zero ((injective_iff_map_eq_zero ιW).1 (FaithfulSMul.algebraMap_injective W (AlgebraicClosure Ω)) _ e)`.

Establish `hιinj : Function.Injective ιW` using `FaithfulSMul.algebraMap_injective W (AlgebraicClosure Ω)`. Establish `hψinj : Function.Injective ψ` using `fun x y e => Subtype.ext ((algebraMap Ω (AlgebraicClosure Ω)).injective (congrArg Subtype.val e))`. Use `set F₀ : Polynomial Ω := f.map (W.comap (algebraMap Ω (AlgebraicClosure Ω))).subtype with hF₀`. Establish `hF₀F : F₀.map (algebraMap Ω (AlgebraicClosure Ω)) = F`. Rewrite using `[hF₀, hF, hG, Polynomial.map_map, Polynomial.map_map]`.

Both sides reduce to the same expression. Establish `hintΩ : IsIntegral Ω (ιW r')` using `Algebra.IsIntegral.isIntegral _`. Establish `hroot0 : aeval (ιW r') F₀ = 0`. Rewrite using `[aeval_def, ← Polynomial.eval_map, hF₀F]`. Conclude with `(mem_roots hFm.ne_zero).1 hr`.

Take `⟨h, hh⟩` from `minpoly.dvd Ω (ιW r') hroot0`. Establish `hq : aeval (ιW r') (derivative (minpoly Ω (ιW r'))) ≠ 0`. Introduce `e`. Apply `hFd` to reduce the goal to its premises. Establish `: aeval (ιW r') (derivative F₀) = 0`.

Rewrite using `[hh, derivative_mul, map_add, map_mul, map_mul, e, minpoly.aeval]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `this` using `[aeval_def, ← Polynomial.eval_map, ← Polynomial.derivative_map, hF₀F]`. Conclude with `this`. Establish `hsep : (minpoly Ω (ιW r')).Separable` using `(Polynomial.separable_iff_derivative_ne_zero (minpoly.irreducible hintΩ)).2 (fun e => hq (by rw [e, map_zero]))`.

Establish `hdeg` using `IsSepClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible hintΩ) hsep`. Take `⟨b, hb⟩` from `minpoly.natDegree_eq_one_iff.1 (natDegree_eq_of_degree_eq_some hdeg)`. Establish `hbW : b ∈ W.comap (algebraMap Ω (AlgebraicClosure Ω))`. Rewrite using `[ValuationSubring.mem_comap, hb]`. Conclude with `r'.2`.

Establish `hψb : ψ ⟨b, hbW⟩ = r'` using `Subtype.ext hb`. Establish `hGr : G.eval r' = 0`. Apply `hιinj` to reduce the goal to its premises. Rewrite using `[map_zero, ← eval₂_at_apply, ← Polynomial.eval_map, ← hF]`. Conclude with `(mem_roots hFm.ne_zero).1 hr`.

Use `⟨⟨b, hbW⟩, ?_, ?_⟩` and prove the remaining obligations. Apply `hψinj` to reduce the goal to its premises. Rewrite using `[map_zero, ← eval₂_at_apply, ← Polynomial.eval_map, hψb, ← hG]`. Conclude with `hGr`. Use `(mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 hr'm ?_` and prove the remaining obligations.

Use `hu.map ψ` as an intermediate fact. Rewrite `this` using `[map_sub, hψb]`. Then use the resulting hypothesis.
-/
theorem henselianLocalRing_of_isSepClosed {Ω : Type} [Field Ω] [IsSepClosed Ω] (V : ValuationSubring Ω) :
    HenselianLocalRing V := by
  classical
  obtain ⟨W, rfl⟩ := exists_valuationSubring_comap_eq V (algebraMap Ω (AlgebraicClosure Ω))
  refine @HenselianLocalRing.mk _ _ inferInstance ?_
  intro f hf a₀ h₁ h₂
  set ψ := comapToValuationSubring W (algebraMap Ω (AlgebraicClosure Ω))
  set ιW := algebraMap W (AlgebraicClosure Ω)
  set G := f.map ψ with hG
  set F := G.map ιW with hF
  have hFm : F.Monic := (hf.map ψ).map ιW
  have hint : ∀ r ∈ F.roots, ∃ r' : W, ιW r' = r := by
    intro r hr
    have hi : IsIntegral W r := ⟨G, hf.map ψ, by
      rw [← Polynomial.eval_map]
      exact (mem_roots hFm.ne_zero).1 hr⟩
    exact IsIntegrallyClosed.isIntegral_iff.1 hi
  have hψm : ψ (f.eval a₀) ∈ maximalIdeal W :=
    (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 h₁ (IsUnit.of_map ψ _ hu)

  obtain ⟨r, hr, hrv⟩ : ∃ r ∈ F.roots, W.valuation (ιW (ψ a₀) - r) < 1 := by
    by_contra hne
    push_neg at hne
    have hprod : F.eval (ιW (ψ a₀)) = (F.roots.map fun r => ιW (ψ a₀) - r).prod := by
      conv_lhs => rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hFm
        IsAlgClosed.card_roots_eq_natDegree]
      rw [eval_multiset_prod, Multiset.map_map]
      simp
    have h1 : W.valuation (F.eval (ιW (ψ a₀))) = 1 := by
      rw [hprod, map_multiset_prod, Multiset.map_map]
      apply Multiset.prod_eq_one
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
      have hle := hne y hy
      obtain ⟨y', rfl⟩ := hint y hy
      refine le_antisymm ?_ hle
      simp only [Function.comp_apply]
      rw [← map_sub]
      exact W.valuation_le_one (ψ a₀ - y')
    have h2 : W.valuation (F.eval (ιW (ψ a₀))) < 1 := by
      rw [hF, Polynomial.eval_map, eval₂_at_apply, hG, Polynomial.eval_map, eval₂_at_apply]
      exact (W.valuation_lt_one_iff _).1 hψm
    exact absurd h1 h2.ne
  obtain ⟨r', rfl⟩ := hint r hr
  have hr'm : r' - ψ a₀ ∈ maximalIdeal W := by
    rw [← neg_sub, Ideal.neg_mem_iff, W.valuation_lt_one_iff]
    simpa [ιW] using hrv
  have hGd : IsUnit (G.derivative.eval r') := by
    refine isUnit_of_sub_mem_maximalIdeal' ?_ (y := G.derivative.eval (ψ a₀)) ?_
    · obtain ⟨c, hc⟩ := sub_dvd_eval_sub r' (ψ a₀) G.derivative
      rw [hc]
      exact Ideal.mul_mem_right _ _ hr'm
    · rw [hG, derivative_map, Polynomial.eval_map, eval₂_at_apply]
      exact h₂.map ψ
  have hFd : F.derivative.eval (ιW r') ≠ 0 := by
    rw [hF, derivative_map, Polynomial.eval_map, eval₂_at_apply]
    exact fun e => hGd.ne_zero ((injective_iff_map_eq_zero ιW).1 (FaithfulSMul.algebraMap_injective W (AlgebraicClosure Ω)) _ e)
  have hιinj : Function.Injective ιW := FaithfulSMul.algebraMap_injective W (AlgebraicClosure Ω)
  have hψinj : Function.Injective ψ := fun x y e =>
    Subtype.ext ((algebraMap Ω (AlgebraicClosure Ω)).injective (congrArg Subtype.val e))

  set F₀ : Polynomial Ω := f.map (W.comap (algebraMap Ω (AlgebraicClosure Ω))).subtype with hF₀
  have hF₀F : F₀.map (algebraMap Ω (AlgebraicClosure Ω)) = F := by
    rw [hF₀, hF, hG, Polynomial.map_map, Polynomial.map_map]
    rfl
  have hintΩ : IsIntegral Ω (ιW r') := Algebra.IsIntegral.isIntegral _
  have hroot0 : aeval (ιW r') F₀ = 0 := by
    rw [aeval_def, ← Polynomial.eval_map, hF₀F]
    exact (mem_roots hFm.ne_zero).1 hr
  obtain ⟨h, hh⟩ := minpoly.dvd Ω (ιW r') hroot0
  have hq : aeval (ιW r') (derivative (minpoly Ω (ιW r'))) ≠ 0 := by
    intro e
    apply hFd
    have : aeval (ιW r') (derivative F₀) = 0 := by
      rw [hh, derivative_mul, map_add, map_mul, map_mul, e, minpoly.aeval]
      ring
    rw [aeval_def, ← Polynomial.eval_map, ← Polynomial.derivative_map, hF₀F] at this
    exact this
  have hsep : (minpoly Ω (ιW r')).Separable :=
    (Polynomial.separable_iff_derivative_ne_zero (minpoly.irreducible hintΩ)).2 (fun e => hq (by rw [e, map_zero]))
  have hdeg := IsSepClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible hintΩ) hsep
  obtain ⟨b, hb⟩ := minpoly.natDegree_eq_one_iff.1 (natDegree_eq_of_degree_eq_some hdeg)
  have hbW : b ∈ W.comap (algebraMap Ω (AlgebraicClosure Ω)) := by
    rw [ValuationSubring.mem_comap, hb]
    exact r'.2
  have hψb : ψ ⟨b, hbW⟩ = r' := Subtype.ext hb
  have hGr : G.eval r' = 0 := by
    apply hιinj
    rw [map_zero, ← eval₂_at_apply, ← Polynomial.eval_map, ← hF]
    exact (mem_roots hFm.ne_zero).1 hr
  refine ⟨⟨b, hbW⟩, ?_, ?_⟩
  · apply hψinj
    rw [map_zero, ← eval₂_at_apply, ← Polynomial.eval_map, hψb, ← hG]
    exact hGr
  · refine (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 hr'm ?_
    have := hu.map ψ
    rwa [map_sub, hψb] at this

end GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Use `haveI := henselianLocalRing_of_isSepClosed V`. Use `set K' := IntermediateField.fixedField (inertia K V)`. Use `set j := comapToValuationSubring V (algebraMap K' Ω)`. Establish `hjinj : Function.Injective j` using `fun x y e => Subtype.ext ((algebraMap K' Ω).injective (congrArg (fun z : V => (z : Ω)) e))`. Use `@HenselianLocalRing.mk _ _ inferInstance ?_` and prove the remaining obligations.

Introduce `f hf a₀ h₁ h₂`. Establish `h₁' : (f.map j).eval (j a₀) ∈ maximalIdeal V`. Rewrite using `[Polynomial.eval_map, eval₂_at_apply]`. Conclude with `(mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 h₁ (IsUnit.of_map j _ hu)`. Establish `h₂' : IsUnit ((f.map j).derivative.eval (j a₀))`.

Rewrite using `[derivative_map, Polynomial.eval_map, eval₂_at_apply]`. Conclude with `h₂.map j`. Take `⟨b, hb, hba⟩` from `HenselianLocalRing.is_henselian (f.map j) (hf.map j) (j a₀) h₁' h₂'`. Use `set κ : V.comap (algebraMap K' Ω) →+* Ω := V.subtype.comp j with hκ`. Establish `hbΩ : f.eval₂ κ (b : Ω) = 0`.

Establish `: V.subtype ((f.map j).eval b) = 0` using `by rw [hb.eq_zero, map_zero]`. Rewrite `this` using `[Polynomial.eval_map, hom_eval₂]`. Conclude with `this`. Establish `hfix : ∀ σ ∈ inertia K V, σ (b : Ω) = b`. Introduce `σ hσ`.

Take `⟨hσV, hσv⟩` from `(mem_inertia_iff V σ).1 hσ`. Establish `hmem : σ (b : Ω) ∈ V`. Use `ValuationSubring.smul_mem_pointwise_smul σ (b : Ω) V b.2` as an intermediate fact. Rewrite `this` using `[hσV]`. Then use the resulting hypothesis. Establish `hσκ : (σ : Ω →+* Ω).comp κ = κ`.

Use extensionality with `x`. Conclude with `(IntermediateField.mem_fixedField_iff _ _).1 (x : K').2 σ hσ`. Establish `hc : (f.map j).IsRoot ⟨σ b, hmem⟩`. Apply `V.subtype_injective` to reduce the goal to its premises. Rewrite using `[map_zero, Polynomial.eval_map, hom_eval₂]`.

Establish `e` using `congrArg (σ : Ω →+* Ω) hbΩ`. Rewrite `e` using `[map_zero, hom_eval₂, hσκ]`. Conclude with `e`. Establish `hcm : (⟨σ b, hmem⟩ : V) - j a₀ ∈ maximalIdeal V`. Establish `hd : (⟨σ b, hmem⟩ : V) - b ∈ maximalIdeal V`.

Rewrite using `[V.valuation_lt_one_iff]`. Conclude with `hσv b b.2`. Use `Ideal.add_mem _ hd hba` as an intermediate fact. Simplify using `using this`. Use `eq_of_isRoot_of_sub_mem_maximalIdeal h₂' hb hc hba hcm` as an intermediate fact.

Conclude with `congrArg Subtype.val this`. Establish `hbK : (b : Ω) ∈ K'` using `(IntermediateField.mem_fixedField_iff _ _).2 hfix`. Establish `hbV : (⟨b, hbK⟩ : K') ∈ V.comap (algebraMap K' Ω)` using `b.2`. Establish `hjb : j ⟨⟨b, hbK⟩, hbV⟩ = b` using `Subtype.ext rfl`. Use `⟨⟨⟨b, hbK⟩, hbV⟩, ?_, ?_⟩` and prove the remaining obligations.

Apply `hjinj` to reduce the goal to its premises. Rewrite using `[map_zero, ← eval₂_at_apply, ← Polynomial.eval_map, hjb]`. Conclude with `hb`. Use `(mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 hba ?_` and prove the remaining obligations. Use `hu.map j` as an intermediate fact.

Rewrite `this` using `[map_sub, hjb]`. Then use the resulting hypothesis.
-/
theorem henselianLocalRing_comap_fixedField_inertia (K : Type) {Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    [IsSepClosed Ω] (V : ValuationSubring Ω) :
    HenselianLocalRing (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) := by
  classical
  haveI := henselianLocalRing_of_isSepClosed V
  set K' := IntermediateField.fixedField (inertia K V)
  set j := comapToValuationSubring V (algebraMap K' Ω)
  have hjinj : Function.Injective j := fun x y e =>
    Subtype.ext ((algebraMap K' Ω).injective (congrArg (fun z : V => (z : Ω)) e))
  refine @HenselianLocalRing.mk _ _ inferInstance ?_
  intro f hf a₀ h₁ h₂
  have h₁' : (f.map j).eval (j a₀) ∈ maximalIdeal V := by
    rw [Polynomial.eval_map, eval₂_at_apply]
    exact (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 h₁ (IsUnit.of_map j _ hu)
  have h₂' : IsUnit ((f.map j).derivative.eval (j a₀)) := by
    rw [derivative_map, Polynomial.eval_map, eval₂_at_apply]
    exact h₂.map j
  obtain ⟨b, hb, hba⟩ := HenselianLocalRing.is_henselian (f.map j) (hf.map j) (j a₀) h₁' h₂'

  set κ : V.comap (algebraMap K' Ω) →+* Ω := V.subtype.comp j with hκ
  have hbΩ : f.eval₂ κ (b : Ω) = 0 := by
    have : V.subtype ((f.map j).eval b) = 0 := by rw [hb.eq_zero, map_zero]
    rw [Polynomial.eval_map, hom_eval₂] at this
    exact this
  have hfix : ∀ σ ∈ inertia K V, σ (b : Ω) = b := by
    intro σ hσ
    obtain ⟨hσV, hσv⟩ := (mem_inertia_iff V σ).1 hσ
    have hmem : σ (b : Ω) ∈ V := by
      have := ValuationSubring.smul_mem_pointwise_smul σ (b : Ω) V b.2
      rwa [hσV] at this
    have hσκ : (σ : Ω →+* Ω).comp κ = κ := by
      ext x
      exact (IntermediateField.mem_fixedField_iff _ _).1 (x : K').2 σ hσ
    have hc : (f.map j).IsRoot ⟨σ b, hmem⟩ := by
      apply V.subtype_injective
      rw [map_zero, Polynomial.eval_map, hom_eval₂]
      have e := congrArg (σ : Ω →+* Ω) hbΩ
      rw [map_zero, hom_eval₂, hσκ] at e
      exact e
    have hcm : (⟨σ b, hmem⟩ : V) - j a₀ ∈ maximalIdeal V := by
      have hd : (⟨σ b, hmem⟩ : V) - b ∈ maximalIdeal V := by
        rw [V.valuation_lt_one_iff]
        exact hσv b b.2
      have := Ideal.add_mem _ hd hba
      simpa using this
    have := eq_of_isRoot_of_sub_mem_maximalIdeal h₂' hb hc hba hcm
    exact congrArg Subtype.val this
  have hbK : (b : Ω) ∈ K' := (IntermediateField.mem_fixedField_iff _ _).2 hfix
  have hbV : (⟨b, hbK⟩ : K') ∈ V.comap (algebraMap K' Ω) := b.2
  have hjb : j ⟨⟨b, hbK⟩, hbV⟩ = b := Subtype.ext rfl
  refine ⟨⟨⟨b, hbK⟩, hbV⟩, ?_, ?_⟩
  · apply hjinj
    rw [map_zero, ← eval₂_at_apply, ← Polynomial.eval_map, hjb]
    exact hb
  · refine (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 hba ?_
    have := hu.map j
    rwa [map_sub, hjb] at this

/- English proof (translation)
Introduce `R K Ω _ _ _ _ _ _ _ _ _ _ V _`. Use `haveI : IsSepClosed Ω := IsSepClosure.sep_closed K`. Conclude with `henselianLocalRing_comap_fixedField_inertia K V`.
-/
theorem henselianLocalRing_fixedField_inertia : ∀ (R K Ω : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring →
    HenselianLocalRing (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V _
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  exact henselianLocalRing_comap_fixedField_inertia K V

end GlobalTheory

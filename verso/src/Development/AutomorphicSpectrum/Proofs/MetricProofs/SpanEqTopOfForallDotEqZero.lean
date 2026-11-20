import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChart
import Mathlib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par

open MvPolynomial ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.JacobianCriterionAlt IsLocalRing

variable {m : ℕ}

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨f, hf0, hle⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)`. Establish `hv : (fun j => f (fun k => if j = k then (1 : ℂ) else 0)) = 0`. Apply `hS` to reduce the goal to its premises. Introduce `w hw`.

Establish `h1 : f w = 0` using `LinearMap.mem_ker.mp (hle (Submodule.subset_span hw))`. Rewrite `h1` using `[LinearMap.pi_apply_eq_sum_univ f w]`. Use `Eq.trans ?_ h1` and prove the remaining obligations. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul, mul_comm]`.

Apply `hf0` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Rewrite using `[LinearMap.pi_apply_eq_sum_univ f x, LinearMap.zero_apply]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations.

Use `congrFun hv j` as an intermediate fact. Simplify using `only [Pi.zero_apply] at this`. Rewrite using `[this, smul_zero]`.
-/
theorem span_eq_top_of_forall_dot_eq_zero (S : Set (Fin m → ℂ))
    (hS : ∀ v : Fin m → ℂ, (∀ w ∈ S, ∑ j, v j * w j = 0) → v = 0) :
    Submodule.span ℂ S = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hv : (fun j => f (fun k => if j = k then (1 : ℂ) else 0)) = 0 := by
    apply hS
    intro w hw
    have h1 : f w = 0 := LinearMap.mem_ker.mp (hle (Submodule.subset_span hw))
    rw [LinearMap.pi_apply_eq_sum_univ f w] at h1
    refine Eq.trans ?_ h1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul, mul_comm]
  apply hf0
  apply LinearMap.ext
  intro x
  rw [LinearMap.pi_apply_eq_sum_univ f x, LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  have := congrFun hv j
  simp only [Pi.zero_apply] at this
  rw [this, smul_zero]

/- English proof (translation)
Establish `h` using `hJ (ReciprocityTheory.AnForm.R.JacobianCriterionAlt.taylor t a)`. Rewrite `h` using `[h0, map_zero, sub_zero]`. Establish `h2` using `J.sub_mem ha h`. Rewrite `h2` using `[sub_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem lin_mem_of_eval_eq_zero (t : Fin m → ℂ) (J : Ideal (MvPolynomial (Fin m) ℂ))
    (hJ : ptI t ^ 2 ≤ J) {a : MvPolynomial (Fin m) ℂ} (ha : a ∈ J) (h0 : eval t a = 0) :
    ∑ i, C (gradP t a i) * (X i - C (t i)) ∈ J := by
  have h := hJ (ReciprocityTheory.AnForm.R.JacobianCriterionAlt.taylor t a)
  rw [h0, map_zero, sub_zero] at h
  have h2 := J.sub_mem ha h
  rwa [sub_sub_cancel] at h2

/- English proof (translation)
Set `φ : (Fin m → ℂ) →ₗ[ℂ] MvPolynomial (Fin m) ℂ` to `{ toFun := fun v => ∑ i, C (v i) * (X i - C (t i)) map_add' := fun v w => by`. Simplify using `only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`. Use the proof step `map_smul' := fun c v => by`. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Finset.smul_sum, MvPolynomial.smul_eq_C_mul, mul_assoc] }`. Establish `hφ : ∀ v, φ v = ∑ i, C (v i) * (X i - C (t i))` using `fun v => rfl`.

Establish `hspan : Submodule.span ℂ (gradP t '' A) ≤ Submodule.comap φ (J.restrictScalars ℂ)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, haA, rfl⟩`. Use `show φ (gradP t a) ∈ J`. Rewrite using `[hφ]`.

Conclude with `lin_mem_of_eval_eq_zero t J hJ (hAJ haA) (hA0 a haA)`. Establish `key : ∀ i, X i - C (t i) ∈ J`. Introduce `i`. Establish `hmem : (Pi.single i 1 : Fin m → ℂ) ∈ Submodule.comap φ (J.restrictScalars ℂ)` using `hspan (by rw [hA]; exact Submodule.mem_top)`. Establish `h2 : φ (Pi.single i 1) ∈ J` using `hmem`.

Rewrite `h2` using `[hφ, Finset.sum_eq_single i]`. Simplify using `using h2`. Introduce `j _ hji`. Rewrite using `[Pi.single_eq_of_ne hji, map_zero, zero_mul]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ i) h`. Rewrite using `[ReciprocityTheory.AnForm.R.JacobianCriterionAlt.ptIdeal_eq_span, Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `key i`.
-/
theorem ptI_le_of_span_grad_eq_top (t : Fin m → ℂ) (J : Ideal (MvPolynomial (Fin m) ℂ))
    (hJ : ptI t ^ 2 ≤ J) (A : Set (MvPolynomial (Fin m) ℂ)) (hAJ : A ⊆ J)
    (hA0 : ∀ a ∈ A, eval t a = 0) (hA : Submodule.span ℂ (gradP t '' A) = ⊤) :
    ptI t ≤ J := by
  let φ : (Fin m → ℂ) →ₗ[ℂ] MvPolynomial (Fin m) ℂ :=
    { toFun := fun v => ∑ i, C (v i) * (X i - C (t i))
      map_add' := fun v w => by
        simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Finset.smul_sum,
          MvPolynomial.smul_eq_C_mul, mul_assoc] }
  have hφ : ∀ v, φ v = ∑ i, C (v i) * (X i - C (t i)) := fun v => rfl
  have hspan : Submodule.span ℂ (gradP t '' A) ≤ Submodule.comap φ (J.restrictScalars ℂ) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, haA, rfl⟩
    show φ (gradP t a) ∈ J
    rw [hφ]
    exact lin_mem_of_eval_eq_zero t J hJ (hAJ haA) (hA0 a haA)
  have key : ∀ i, X i - C (t i) ∈ J := by
    intro i
    have hmem : (Pi.single i 1 : Fin m → ℂ) ∈ Submodule.comap φ (J.restrictScalars ℂ) :=
      hspan (by rw [hA]; exact Submodule.mem_top)
    have h2 : φ (Pi.single i 1) ∈ J := hmem
    rw [hφ, Finset.sum_eq_single i] at h2
    · simpa using h2
    · intro j _ hji
      rw [Pi.single_eq_of_ne hji, map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [ReciprocityTheory.AnForm.R.JacobianCriterionAlt.ptIdeal_eq_span, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact key i

/- English proof (translation)
Proceed by induction on `a using MvPolynomial.induction_on`. Use `next c =>`. Rewrite using `[ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_C, pderiv_C, map_zero, Pi.zero_apply]`. Use `next p q hp hq =>`. Rewrite using `[ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_add, Pi.add_apply, hp, hq, map_add, map_add]`.

Use `next p i hp =>`. Establish `hX : gradP t (X i) = Pi.single i 1`. Establish `h2 : (X i : MvPolynomial (Fin m) ℂ) = (X i - C (t i)) + C (t i)` using `by ring`. Rewrite using `[h2, ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_add, ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_lin, ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_C, add_zero]`. Rewrite using `[ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_mul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, hp, hX, Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, eval_X]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hij, Ne.symm hij]`.
-/
private theorem gradP_eq_eval_pderiv (t : Fin m → ℂ) (a : MvPolynomial (Fin m) ℂ) (j : Fin m) :
    gradP t a j = eval t (pderiv j a) := by
  induction a using MvPolynomial.induction_on
  next c =>
    rw [ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_C, pderiv_C, map_zero, Pi.zero_apply]
  next p q hp hq =>
    rw [ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_add, Pi.add_apply, hp, hq, map_add, map_add]
  next p i hp =>
    have hX : gradP t (X i) = Pi.single i 1 := by
      have h2 : (X i : MvPolynomial (Fin m) ℂ) = (X i - C (t i)) + C (t i) := by ring
      rw [h2, ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_add, ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_lin,
        ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_C, add_zero]
    rw [ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_mul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul, hp, hX, Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul, map_add, map_mul,
      map_mul, eval_X]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Pi.single_apply, hij, Ne.symm hij]

/- English proof (translation)
Take `⟨hloc, hnoeth⟩` from `locRing_isLocalRing_isNoetherian I t hI`. Establish `hpt : ptI t = ptIdeal t`. Use extensionality with `a`. Rewrite using `[ReciprocityTheory.AnForm.R.JacobianCriterionAlt.mem_ptIdeal]`. Unfold `ptIdeal`.

Rewrite using `[RingHom.mem_ker]`. Establish `hmemPt : ∀ a, eval t a = 0 → a ∈ ptIdeal t` using `fun a ha => by`. Rewrite using `[← hpt, ReciprocityTheory.AnForm.R.JacobianCriterionAlt.mem_ptIdeal]`. Conclude with `ha`. Establish `hφ : ∀ a, algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) a = Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) I) (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t) a)` using `fun a => rfl`.

Establish `hI0 : ∀ a ∈ I, algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) a = 0`. Introduce `a ha`. Rewrite using `[hφ, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mem_map_of_mem _ ha`. Use `set N : Ideal (locRing I t) := Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) with hN`.

Use `set M : Ideal (locRing I t) := Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) with hM`. Establish `hNM : N ≤ M`. Rewrite using `[hN, Ideal.span_le]`. Introduce and unpack `_ ⟨l, rfl⟩`. Conclude with `Ideal.mem_map_of_mem _ (hmemPt _ (hr l))`.

Establish `key : ptI t ≤ Ideal.comap (algebraMap _ (locRing I t)) (N ⊔ M ^ 2)`. Use `ptI_le_of_span_grad_eq_top t _ ?_ ((I : Set (MvPolynomial (Fin m) ℂ)) ∪ Set.range r) ?_ ?_ ?_` and prove the remaining obligations. Introduce `a ha`. Rewrite using `[Ideal.mem_comap]`. Apply `Ideal.mem_sup_right` to reduce the goal to its premises.

Rewrite using `[hM, ← Ideal.map_pow]`. Conclude with `Ideal.mem_map_of_mem _ (by rw [← hpt]; exact ha)`. Introduce and unpack `a (ha | ⟨l, rfl⟩)`. Rewrite using `[SetLike.mem_coe, Ideal.mem_comap, hI0 a ha]`. Conclude with `Submodule.zero_mem _`.

Rewrite using `[SetLike.mem_coe, Ideal.mem_comap]`. Conclude with `Ideal.mem_sup_left (Ideal.subset_span ⟨l, rfl⟩)`. Introduce and unpack `a (ha | ⟨l, rfl⟩)`. Conclude with `hI a ha`. Conclude with `hr l`.

Apply `span_eq_top_of_forall_dot_eq_zero` to reduce the goal to its premises. Introduce `v hvS`. Apply `hv v` to reduce the goal to its premises. Introduce `h hh`. Establish `h3` using `hvS _ ⟨h, Or.inl hh, rfl⟩`.

Simplify `h3` using `only [gradP_eq_eval_pderiv]`. Introduce `l`. Establish `h3` using `hvS _ ⟨r l, Or.inr ⟨l, rfl⟩, rfl⟩`. Simplify `h3` using `only [gradP_eq_eval_pderiv]`. Establish `hMle : M ≤ N ⊔ M ^ 2` using `Ideal.map_le_iff_le_comap.mpr (hpt.symm.le.trans key)`.

Use `haveI := hloc`. Use `haveI := hnoeth`. Establish `hMtop : M ≠ ⊤` using `by haveI : (ptIdeal t).IsPrime := ptIdeal_isPrime t`. Introduce `htop`. Establish `hmax : Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) (ptIdeal t) = IsLocalRing.maximalIdeal (Localization.AtPrime (ptIdeal t))` using `Localization.AtPrime.map_eq_maximalIdeal`.

Establish `hMeq : M = Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) I)) (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) (ptIdeal t))`. Rewrite using `[hM, Ideal.map_map]`. Conclude with `congrArg (fun f => Ideal.map f (ptIdeal t)) (RingHom.ext fun a => rfl)`. Establish `hc` using `Ideal.comap_map_of_surjective (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) I)) Ideal.Quotient.mk_surjective (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) (ptIdeal t))`. Rewrite `hc` using `[← hMeq, htop, Ideal.comap_top]`.

Establish `hb : Ideal.comap (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) I)) ⊥ ≤ Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) (ptIdeal t)`. Introduce `x hx`. Rewrite `hx` using `[Ideal.mem_comap, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.map_mono (fun a ha => hmemPt a (hI a ha)) hx`. Rewrite `hc` using `[sup_eq_left.mpr hb, hmax]`.

Conclude with `(IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime (ptIdeal t))).ne_top hc.symm`. Establish `hMj : M ≤ Ideal.jacobson ⊥`. Rewrite using `[IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]`. Conclude with `IsLocalRing.le_maximalIdeal hMtop`. Establish `hle : M ≤ N`.

Use `Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian M) hMj ?_` and prove the remaining obligations. Rewrite using `[Ideal.smul_eq_mul, ← pow_two]`. Conclude with `hMle`. Conclude with `le_antisymm hNM hle`.
-/
theorem span_algebraMap_eq_map_ptIdeal (e : ℕ) (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    (r : Fin e → MvPolynomial (Fin m) ℂ) (hI : ∀ h ∈ I, eval t h = 0) (hr : ∀ l, eval t (r l) = 0)
    (hv : ∀ v : Fin m → ℂ, (∀ h ∈ I, ∑ j, v j * eval t (pderiv j h) = 0) →
      (∀ l, ∑ j, v j * eval t (pderiv j (r l)) = 0) → v = 0) :
    Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) =
      Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) := by
  obtain ⟨hloc, hnoeth⟩ := locRing_isLocalRing_isNoetherian I t hI
  have hpt : ptI t = ptIdeal t := by
    ext a
    rw [ReciprocityTheory.AnForm.R.JacobianCriterionAlt.mem_ptIdeal]
    unfold ptIdeal
    rw [RingHom.mem_ker]
  have hmemPt : ∀ a, eval t a = 0 → a ∈ ptIdeal t := fun a ha => by
    rw [← hpt, ReciprocityTheory.AnForm.R.JacobianCriterionAlt.mem_ptIdeal]
    exact ha
  have hφ : ∀ a, algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) a =
      Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) I)
        (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t) a) := fun a => rfl
  have hI0 : ∀ a ∈ I, algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) a = 0 := by
    intro a ha
    rw [hφ, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ha
  set N : Ideal (locRing I t) := Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l))
    with hN
  set M : Ideal (locRing I t) := Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) with hM
  have hNM : N ≤ M := by
    rw [hN, Ideal.span_le]
    rintro _ ⟨l, rfl⟩
    exact Ideal.mem_map_of_mem _ (hmemPt _ (hr l))
  have key : ptI t ≤ Ideal.comap (algebraMap _ (locRing I t)) (N ⊔ M ^ 2) := by
    refine ptI_le_of_span_grad_eq_top t _ ?_ ((I : Set (MvPolynomial (Fin m) ℂ)) ∪ Set.range r)
      ?_ ?_ ?_
    · intro a ha
      rw [Ideal.mem_comap]
      apply Ideal.mem_sup_right
      rw [hM, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ (by rw [← hpt]; exact ha)
    · rintro a (ha | ⟨l, rfl⟩)
      · rw [SetLike.mem_coe, Ideal.mem_comap, hI0 a ha]
        exact Submodule.zero_mem _
      · rw [SetLike.mem_coe, Ideal.mem_comap]
        exact Ideal.mem_sup_left (Ideal.subset_span ⟨l, rfl⟩)
    · rintro a (ha | ⟨l, rfl⟩)
      · exact hI a ha
      · exact hr l
    · apply span_eq_top_of_forall_dot_eq_zero
      intro v hvS
      apply hv v
      · intro h hh
        have h3 := hvS _ ⟨h, Or.inl hh, rfl⟩
        simpa only [gradP_eq_eval_pderiv] using h3
      · intro l
        have h3 := hvS _ ⟨r l, Or.inr ⟨l, rfl⟩, rfl⟩
        simpa only [gradP_eq_eval_pderiv] using h3
  have hMle : M ≤ N ⊔ M ^ 2 := Ideal.map_le_iff_le_comap.mpr (hpt.symm.le.trans key)
  haveI := hloc
  haveI := hnoeth
  have hMtop : M ≠ ⊤ := by
    haveI : (ptIdeal t).IsPrime := ptIdeal_isPrime t
    intro htop
    have hmax : Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) (ptIdeal t) =
        IsLocalRing.maximalIdeal (Localization.AtPrime (ptIdeal t)) :=
      Localization.AtPrime.map_eq_maximalIdeal
    have hMeq : M = Ideal.map
        (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) I))
        (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) (ptIdeal t)) := by
      rw [hM, Ideal.map_map]
      exact congrArg (fun f => Ideal.map f (ptIdeal t)) (RingHom.ext fun a => rfl)
    have hc := Ideal.comap_map_of_surjective
      (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) I))
      Ideal.Quotient.mk_surjective (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) (ptIdeal t))
    rw [← hMeq, htop, Ideal.comap_top] at hc
    have hb : Ideal.comap
        (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) I)) ⊥ ≤
        Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) (ptIdeal t) := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hx
      exact Ideal.map_mono (fun a ha => hmemPt a (hI a ha)) hx
    rw [sup_eq_left.mpr hb, hmax] at hc
    exact (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime (ptIdeal t))).ne_top hc.symm
  have hMj : M ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal hMtop
  have hle : M ≤ N := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian M) hMj ?_
    rw [Ideal.smul_eq_mul, ← pow_two]
    exact hMle
  exact le_antisymm hNM hle

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par

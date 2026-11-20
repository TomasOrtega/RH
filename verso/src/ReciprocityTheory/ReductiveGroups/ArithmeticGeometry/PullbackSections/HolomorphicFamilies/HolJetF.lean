import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetE

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff

variable {Y : Scheme.{0}}

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Establish `e0 : (Spec.map χ ≫ q).appLE U ⊤ h = q.app U ≫ (Spec.map χ).appLE (q ⁻¹ᵁ U) ⊤ h` using `by first`. Consider the case `exact Scheme.Hom.comp_appLE _ _ _ _ _`. Consider the case `(simp only [Scheme.Hom.appLE, Scheme.comp_app, Category.assoc]; rfl)`. Consider the case `(simp only [Scheme.Hom.appLE, Scheme.Hom.comp_app, Category.assoc]; rfl)`. Consider the case `(unfold Scheme.Hom.appLE; simp [Category.assoc])`.

Rewrite using `[e0]`. Establish `e1 : (Spec.map χ).appLE (q ⁻¹ᵁ U) ⊤ h = (Spec A).presheaf.map (homOfLE hq).op ≫ (Spec.map χ).app ⊤`. Rewrite using `[Scheme.Hom.naturality]`. Both sides reduce to the same expression. Rewrite using `[e1]`.

Simplify using `only [Scheme.Hom.appLE, Category.assoc]`. Use `congr 2`. Conclude with `Scheme.ΓSpecIso_naturality χ`.
-/
theorem specMap_comp_appLE {A B : CommRingCat.{0}} (χ : A ⟶ B) (q : Spec A ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ (Spec.map χ ≫ q) ⁻¹ᵁ U) (hq : ⊤ ≤ q ⁻¹ᵁ U) :
    (Spec.map χ ≫ q).appLE U ⊤ h ≫ (Scheme.ΓSpecIso B).hom =
      q.appLE U ⊤ hq ≫ (Scheme.ΓSpecIso A).hom ≫ χ := by
  have e0 : (Spec.map χ ≫ q).appLE U ⊤ h = q.app U ≫ (Spec.map χ).appLE (q ⁻¹ᵁ U) ⊤ h := by
    first
    | exact Scheme.Hom.comp_appLE _ _ _ _ _
    | (simp only [Scheme.Hom.appLE, Scheme.comp_app, Category.assoc]; rfl)
    | (simp only [Scheme.Hom.appLE, Scheme.Hom.comp_app, Category.assoc]; rfl)
    | (unfold Scheme.Hom.appLE; simp [Category.assoc])
  rw [e0]
  have e1 : (Spec.map χ).appLE (q ⁻¹ᵁ U) ⊤ h =
      (Spec A).presheaf.map (homOfLE hq).op ≫ (Spec.map χ).app ⊤ := by
    rw [Scheme.Hom.naturality]
    rfl
  rw [e1]
  simp only [Scheme.Hom.appLE, Category.assoc]
  congr 2
  exact Scheme.ΓSpecIso_naturality χ

section Tan

variable {K : Type} [Field K] {ι : Type} [DecidableEq ι]

/- English proof (translation)
Proceed by induction on `q using MvPolynomial.induction_on`. Use `next a =>`. Establish `hs : (0 : ι →₀ ℕ) ≠ Finsupp.single ℓ 1` using `(Finsupp.single_ne_zero.2 one_ne_zero).symm`. Apply the tactic sequence `ext <;> simp [MvPolynomial.coeff_C, hs, TrivSqZeroExt.algebraMap_eq_inl]`. Use `next p q hp hq =>`.

Simplify using `only [map_add, hp, hq, MvPolynomial.coeff_add, TrivSqZeroExt.inl_add, TrivSqZeroExt.inr_add]`. Normalize the expressions using the abelian group laws. Use `next p i hp =>`. Rewrite using `[map_mul, hp, MvPolynomial.aeval_X]`. Distinguish the cases in `h : i = ℓ`.

Substitute `h` using the available equality. Establish `hc : MvPolynomial.coeff (Finsupp.single i 1) (p * MvPolynomial.X i) = MvPolynomial.constantCoeff p`. Use `MvPolynomial.coeff_mul_X (0 : ι →₀ ℕ) i p` as an intermediate fact. Rewrite `this` using `[zero_add]`. Conclude with `this`.

Rewrite using `[hc]`. Apply the tactic sequence `ext <;> simp`. Establish `h' : ℓ ≠ i` using `Ne.symm h`. Establish `hc : MvPolynomial.coeff (Finsupp.single ℓ 1) (p * MvPolynomial.X i) = 0`. Rewrite using `[MvPolynomial.coeff_mul_X']`.

Simplify using `[Finsupp.single_apply, h', h]`. Rewrite using `[hc]`. Apply the tactic sequence `ext <;> simp [h]`.
-/
theorem aeval_tan (ℓ : ι) (q : MvPolynomial ι K) :
    MvPolynomial.aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber K) else 0) q =
      TrivSqZeroExt.inl (MvPolynomial.constantCoeff q) +
        TrivSqZeroExt.inr (MvPolynomial.coeff (Finsupp.single ℓ 1) q) := by
  induction q using MvPolynomial.induction_on
  next a =>
    have hs : (0 : ι →₀ ℕ) ≠ Finsupp.single ℓ 1 := (Finsupp.single_ne_zero.2 one_ne_zero).symm
    ext <;> simp [MvPolynomial.coeff_C, hs, TrivSqZeroExt.algebraMap_eq_inl]
  next p q hp hq =>
    simp only [map_add, hp, hq, MvPolynomial.coeff_add, TrivSqZeroExt.inl_add, TrivSqZeroExt.inr_add]
    abel
  next p i hp =>
    rw [map_mul, hp, MvPolynomial.aeval_X]
    by_cases h : i = ℓ
    · subst h
      have hc : MvPolynomial.coeff (Finsupp.single i 1) (p * MvPolynomial.X i) =
          MvPolynomial.constantCoeff p := by
        have := MvPolynomial.coeff_mul_X (0 : ι →₀ ℕ) i p
        rw [zero_add] at this
        exact this
      rw [hc]
      ext <;> simp
    · have h' : ℓ ≠ i := Ne.symm h
      have hc : MvPolynomial.coeff (Finsupp.single ℓ 1) (p * MvPolynomial.X i) = 0 := by
        rw [MvPolynomial.coeff_mul_X']
        simp [Finsupp.single_apply, h', h]
      rw [hc]
      ext <;> simp [h]

end Tan

variable {g : ℕ}

/- English proof (translation)
Unfold `psTrunc`. Rewrite using `[MvPolynomial.coeff_sum]`. Simplify using `[MvPolynomial.coeff_monomial, hn]`.
-/
private theorem coeff_psTrunc_lemma {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ)
    (f : MvPowerSeries ι ℂ) (n : ι →₀ ℕ) (hn : n ∈ degLE (ι := ι) m) :
    MvPolynomial.coeff n (psTrunc m f) = MvPowerSeries.coeff n f := by
  unfold psTrunc
  rw [MvPolynomial.coeff_sum]
  simp [MvPolynomial.coeff_monomial, hn]

/- English proof (translation)
Unfold `degLE`. Use `Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨fun i => ⟨n i, Nat.lt_succ_of_le (hb i)⟩, Finset.mem_univ _, ?_⟩, hs⟩` and prove the remaining obligations. Use extensionality with `i`. Simplify using the standard rewrite rules.
-/
private theorem mem_degLE_lemma_2 {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (n : ι →₀ ℕ)
    (hb : ∀ i, n i ≤ m) (hs : (n.sum fun _ k => k) ≤ m) : n ∈ degLE (ι := ι) m := by
  unfold degLE
  refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨fun i => ⟨n i, Nat.lt_succ_of_le (hb i)⟩,
    Finset.mem_univ _, ?_⟩, hs⟩
  ext i
  simp

/- English proof (translation)
Establish `h1 : (jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) (jetOf (0 + 1) θ) = MvPolynomial.aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber ℂ) else 0) (psTrunc (0 + 1) (tay θ 0))` using `rfl`. Establish `hc : ∀ n, MvPowerSeries.coeff n (tay θ 0) = mD θ 0 (dirs n + 0) / fct n` using `fun n => rfl`. Establish `hb0 : ∀ i, (0 : Fin 1 × Fin g →₀ ℕ) i ≤ 0 + 1` using `by simp`. Establish `hs0 : ((0 : Fin 1 × Fin g →₀ ℕ).sum fun _ k => k) ≤ 0 + 1` using `by simp`. Establish `h0 : MvPolynomial.constantCoeff (psTrunc (0 + 1) (tay θ 0)) = θ 0`.

Establish `hd0 : dirs (0 : Fin 1 × Fin g →₀ ℕ) = 0` using `by simp [dirs]`. Establish `hf0 : fct (0 : Fin 1 × Fin g →₀ ℕ) = 1` using `by simp [fct]`. Establish `hm0 : mD θ 0 (0 : Multiset (Fin g → ℂ)) = θ 0`. Unfold `mD`. Rewrite using `[Multiset.toList_zero]`.

Unfold `lD`. Conclude with `iteratedFDeriv_zero_apply _`. Rewrite using `[MvPolynomial.constantCoeff_eq, coeff_psTrunc_lemma (0 + 1) (tay θ 0) 0 (mem_degLE_lemma_2 (0 + 1) 0 hb0 hs0), hc, hd0, add_zero, hf0, div_one, hm0]`. Establish `hb1 : ∀ i, (Finsupp.single ℓ 1 : Fin 1 × Fin g →₀ ℕ) i ≤ 0 + 1`. Introduce `i`.

Rewrite using `[Finsupp.single_apply]`. Apply the tactic sequence `split_ifs <;> omega`. Establish `hs1 : ((Finsupp.single ℓ 1 : Fin 1 × Fin g →₀ ℕ).sum fun _ k => k) ≤ 0 + 1`. Simplify using `[Finsupp.sum_single_index]`. Establish `hd : dirs (Finsupp.single ℓ 1) = {(Pi.single ℓ.2 1 : Fin g → ℂ)}`.

Simplify using `[dirs, Finsupp.toMultiset_single]`. Establish `hf : fct (Finsupp.single ℓ 1) = 1`. Unfold `fct`. Use `Finset.prod_eq_one fun p _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.single_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hm : mD θ 0 {(Pi.single ℓ.2 1 : Fin g → ℂ)} = fderiv ℂ θ 0 (Pi.single ℓ.2 1)`. Unfold `mD`. Rewrite using `[Multiset.toList_singleton]`. Unfold `lD`.

Use `show iteratedFDeriv ℂ 1 θ 0 (fun i => [(Pi.single ℓ.2 1 : Fin g → ℂ)].get i) = _`. Rewrite using `[iteratedFDeriv_one_apply]`. Both sides reduce to the same expression. Establish `hl : MvPolynomial.coeff (Finsupp.single ℓ 1) (psTrunc (0 + 1) (tay θ 0)) = fderiv ℂ θ 0 (Pi.single ℓ.2 1)`. Rewrite using `[coeff_psTrunc_lemma (0 + 1) (tay θ 0) (Finsupp.single ℓ 1) (mem_degLE_lemma_2 (0 + 1) (Finsupp.single ℓ 1) hb1 hs1), hc, hd, add_zero, hf, div_one, hm]`.

Rewrite using `[h1, aeval_tan, h0, hl]`.
-/
theorem jetTan_jetOf (ℓ : Fin 1 × Fin g) (θ : (Fin g → ℂ) → ℂ) :
    (jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) (jetOf (0 + 1) θ) =
      TrivSqZeroExt.inl (θ 0) + TrivSqZeroExt.inr (fderiv ℂ θ 0 (Pi.single ℓ.2 1)) := by
  have h1 : (jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) (jetOf (0 + 1) θ) =
      MvPolynomial.aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber ℂ) else 0)
        (psTrunc (0 + 1) (tay θ 0)) := rfl
  have hc : ∀ n, MvPowerSeries.coeff n (tay θ 0) = mD θ 0 (dirs n + 0) / fct n := fun n => rfl
  have hb0 : ∀ i, (0 : Fin 1 × Fin g →₀ ℕ) i ≤ 0 + 1 := by simp
  have hs0 : ((0 : Fin 1 × Fin g →₀ ℕ).sum fun _ k => k) ≤ 0 + 1 := by simp
  have h0 : MvPolynomial.constantCoeff (psTrunc (0 + 1) (tay θ 0)) = θ 0 := by
    have hd0 : dirs (0 : Fin 1 × Fin g →₀ ℕ) = 0 := by simp [dirs]
    have hf0 : fct (0 : Fin 1 × Fin g →₀ ℕ) = 1 := by simp [fct]
    have hm0 : mD θ 0 (0 : Multiset (Fin g → ℂ)) = θ 0 := by
      unfold mD
      rw [Multiset.toList_zero]
      unfold lD
      exact iteratedFDeriv_zero_apply _
    rw [MvPolynomial.constantCoeff_eq,
      coeff_psTrunc_lemma (0 + 1) (tay θ 0) 0 (mem_degLE_lemma_2 (0 + 1) 0 hb0 hs0), hc,
      hd0, add_zero, hf0, div_one, hm0]
  have hb1 : ∀ i, (Finsupp.single ℓ 1 : Fin 1 × Fin g →₀ ℕ) i ≤ 0 + 1 := by
    intro i
    rw [Finsupp.single_apply]
    split_ifs <;> omega
  have hs1 : ((Finsupp.single ℓ 1 : Fin 1 × Fin g →₀ ℕ).sum fun _ k => k) ≤ 0 + 1 := by
    simp [Finsupp.sum_single_index]
  have hd : dirs (Finsupp.single ℓ 1) = {(Pi.single ℓ.2 1 : Fin g → ℂ)} := by
    simp [dirs, Finsupp.toMultiset_single]
  have hf : fct (Finsupp.single ℓ 1) = 1 := by
    unfold fct
    refine Finset.prod_eq_one fun p _ => ?_
    rw [Finsupp.single_apply]
    split_ifs <;> simp
  have hm : mD θ 0 {(Pi.single ℓ.2 1 : Fin g → ℂ)} = fderiv ℂ θ 0 (Pi.single ℓ.2 1) := by
    unfold mD
    rw [Multiset.toList_singleton]
    unfold lD
    show iteratedFDeriv ℂ 1 θ 0 (fun i => [(Pi.single ℓ.2 1 : Fin g → ℂ)].get i) = _
    rw [iteratedFDeriv_one_apply]
    rfl
  have hl : MvPolynomial.coeff (Finsupp.single ℓ 1) (psTrunc (0 + 1) (tay θ 0)) =
      fderiv ℂ θ 0 (Pi.single ℓ.2 1) := by
    rw [coeff_psTrunc_lemma (0 + 1) (tay θ 0) (Finsupp.single ℓ 1)
      (mem_degLE_lemma_2 (0 + 1) (Finsupp.single ℓ 1) hb1 hs1), hc, hd, add_zero, hf, div_one, hm]
  rw [h1, aeval_tan, h0, hl]

/- English proof (translation)
Substitute `hq` using the available equality. Both sides reduce to the same expression.
-/
theorem appLE_congr_hom {A : CommRingCat.{0}} {q q' : Spec A ⟶ Y} (hq : q = q') (U : Y.Opens) (h : ⊤ ≤ q ⁻¹ᵁ U)
    (h' : ⊤ ≤ q' ⁻¹ᵁ U) : q.appLE U ⊤ h = q'.appLE U ⊤ h' := by
  subst hq
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x hx`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Establish `hx' : IsUnit (MvPolynomial.aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber ℂ) else 0) p)` using `hx`. Rewrite `hx'` using `[aeval_tan]`.

Establish `hc : MvPolynomial.constantCoeff p ≠ 0`. Introduce `h0`. Take `⟨u, hu⟩` from `hx'`. Use `congrArg TrivSqZeroExt.fst u.mul_inv` as an intermediate fact. Rewrite `this` using `[TrivSqZeroExt.fst_mul, hu]`.

Simplify using `[h0] at this`. Establish `hq : p - MvPolynomial.C (MvPolynomial.constantCoeff p) ∈ orig ℂ (Fin 1 × Fin g)`. Unfold `orig`. Rewrite using `[← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]`. Introduce `m hm`.

Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`. Rewrite `hm` using `[MvPolynomial.mem_support_iff]`. Apply `hm` to reduce the goal to its premises. Rewrite using `[MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_pos rfl]`.

Conclude with `sub_self _`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, m i ≠ 0 := by`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Conclude with `hm0 (Finsupp.ext hne)`.

Conclude with `⟨i, Set.mem_univ _, hi⟩`. Establish `hnil : IsNilpotent (Ideal.Quotient.mk (orig ℂ (Fin 1 × Fin g) ^ (0 + 1 + 1)) (p - MvPolynomial.C (MvPolynomial.constantCoeff p)))`. Use `⟨0 + 1 + 1, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.pow_mem_pow hq _`.

Establish `hu : IsUnit (Ideal.Quotient.mk (orig ℂ (Fin 1 × Fin g) ^ (0 + 1 + 1)) (MvPolynomial.C (MvPolynomial.constantCoeff p)))` using `((isUnit_iff_ne_zero.2 hc).map MvPolynomial.C).map _`. Use `hnil.isUnit_add_left_of_commute hu (Commute.all _ _)` as an intermediate fact. Simplify using `using this`.
-/
theorem isLocalHom_jetTan (ℓ : Fin 1 × Fin g) :
    IsLocalHom ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
      Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ) := by
  constructor
  intro x hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hx' : IsUnit (MvPolynomial.aeval
      (fun i => if i = ℓ then (DualNumber.eps : DualNumber ℂ) else 0) p) := hx
  rw [aeval_tan] at hx'
  have hc : MvPolynomial.constantCoeff p ≠ 0 := by
    intro h0
    obtain ⟨u, hu⟩ := hx'
    have := congrArg TrivSqZeroExt.fst u.mul_inv
    rw [TrivSqZeroExt.fst_mul, hu] at this
    simp [h0] at this
  have hq : p - MvPolynomial.C (MvPolynomial.constantCoeff p) ∈ orig ℂ (Fin 1 × Fin g) := by
    unfold orig
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [MvPolynomial.mem_support_iff] at hm
      apply hm
      rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_pos rfl]
      exact sub_self _
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hm0 (Finsupp.ext hne)
    exact ⟨i, Set.mem_univ _, hi⟩
  have hnil : IsNilpotent (Ideal.Quotient.mk (orig ℂ (Fin 1 × Fin g) ^ (0 + 1 + 1))
      (p - MvPolynomial.C (MvPolynomial.constantCoeff p))) := by
    refine ⟨0 + 1 + 1, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hq _
  have hu : IsUnit (Ideal.Quotient.mk (orig ℂ (Fin 1 × Fin g) ^ (0 + 1 + 1))
      (MvPolynomial.C (MvPolynomial.constantCoeff p))) :=
    ((isUnit_iff_ne_zero.2 hc).map MvPolynomial.C).map _
  have := hnil.isUnit_add_left_of_commute hu (Commute.all _ _)
  simpa using this

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Use `haveI := isLocalHom_jetTan (g := g) ℓ`. Use `haveI hfl : IsLocalHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom := ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩`. Unfold `jetPt`. Rewrite using `[spMap, spec_comp_nbhdPt]`. Establish `hres : ∀ (U V : Y.Opens) (hU : e 0 cpt ∈ U) (hV : e 0 cpt ∈ V) (h : V ≤ U), Y.presheaf.map (homOfLE h).op ≫ (jetψ e hol (0 + 1) V hV ≫ CommRingCat.ofHom ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) : Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ)) = jetψ e hol …` using `fun U V hU hV h => by rw [← Category.assoc, jetψ_res]`.

Establish `hloc : ∀ (U : Y.Opens) (hU : e 0 cpt ∈ U) (f : Γ(Y, U)), IsUnit ((jetψ e hol (0 + 1) U hU ≫ CommRingCat.ofHom ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) : Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ)) f) → e 0 cpt ∈ Y.basicOpen f`. Introduce `U hU f hf`. Rewrite `hf` using `[CommRingCat.comp_apply]`. Conclude with `jetψ_loc e hol _ U hU f ((isLocalHom_jetTan ℓ).map_nonunit _ hf)`. Establish `hpt` using `nbhdPt_closedPoint _ hres hloc`.

Establish `hv : v (IsLocalRing.closedPoint _) = e 0 cpt`. Rewrite using `[← hd.1, Scheme.Hom.comp_apply, spMap, Spec_closedPoint]`. Use `hom_ext_of_local (hpt.trans hv.symm) fun U h₁ h₂ => ?_` and prove the remaining obligations. Establish `hU : e 0 cpt ∈ U`. Establish `: nbhdPt _ hres (IsLocalRing.closedPoint _) ∈ U` using `h₁ (show IsLocalRing.closedPoint _ ∈ (⊤ : (Spec _).Opens) from trivial)`.

Rewrite `this` using `[hpt]`. Then use the resulting hypothesis. Rewrite using `[nbhdPt_appLE _ hres hloc U hU h₁, Iso.comp_inv_eq]`. Establish `h0 : ⊤ ≤ (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ v) ⁻¹ᵁ U`. Use `top_le_of_mem hU` as an intermediate fact. Rewrite `this` using `[← hd.1]`. Then use the resulting hypothesis.

Establish `hfst` using `specMap_comp_appLE (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) v U h0 h₂`. Rewrite `hfst` using `[appLE_congr_hom hd.1 U h0 (top_le_of_mem hU)]`. Establish `hf1 : ∀ f, (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((e 0).appLE U ⊤ (top_le_of_mem hU) f) = TrivSqZeroExt.fst ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom (v.appLE U ⊤ h₂ f))` using `fun f => by`. Use `ConcreteCategory.congr_hom hfst f` as an intermediate fact. Rewrite `this` using `[ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]`.

Conclude with `this`. Use extensionality with `f`. Rewrite using `[CommRingCat.comp_apply, jetψ_apply]`. Express the relevant statement in the definitionally equal form `((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) (jetOf (0 + 1) _)).fst = _`. Rewrite using `[jetTan_jetOf, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, valAt'_of _ _ (top_le_of_mem hU)]`.

Conclude with `hf1 f`. Rewrite using `[CommRingCat.comp_apply, jetψ_apply]`. Express the relevant statement in the definitionally equal form `((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) (jetOf (0 + 1) _)).snd = _`. Rewrite using `[jetTan_jetOf, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]`. Conclude with `(hd.2 U h₂ f).symm`.
-/
theorem jetPt_tan (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (ℓ : Fin 1 × Fin g)
    (v : Sp (DualNumber ℂ) ⟶ Y) (hd : IsDerivAt0 e (Pi.single ℓ.2 1) v) :
    spMap ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
      Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ) ≫ jetPt e hol (0 + 1) = v := by
  haveI := isLocalHom_jetTan (g := g) ℓ
  haveI hfl : IsLocalHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom :=
    ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩
  unfold jetPt
  rw [spMap, spec_comp_nbhdPt]
  have hres : ∀ (U V : Y.Opens) (hU : e 0 cpt ∈ U) (hV : e 0 cpt ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ (jetψ e hol (0 + 1) V hV ≫ CommRingCat.ofHom
        ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
          Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ)) =
      jetψ e hol (0 + 1) U hU ≫ CommRingCat.ofHom
        ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
          Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ) :=
    fun U V hU hV h => by rw [← Category.assoc, jetψ_res]
  have hloc : ∀ (U : Y.Opens) (hU : e 0 cpt ∈ U) (f : Γ(Y, U)),
      IsUnit ((jetψ e hol (0 + 1) U hU ≫ CommRingCat.ofHom
        ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
          Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ)) f) → e 0 cpt ∈ Y.basicOpen f := by
    intro U hU f hf
    rw [CommRingCat.comp_apply] at hf
    exact jetψ_loc e hol _ U hU f ((isLocalHom_jetTan ℓ).map_nonunit _ hf)
  have hpt := nbhdPt_closedPoint _ hres hloc
  have hv : v (IsLocalRing.closedPoint _) = e 0 cpt := by
    rw [← hd.1, Scheme.Hom.comp_apply, spMap, Spec_closedPoint]
  refine hom_ext_of_local (hpt.trans hv.symm) fun U h₁ h₂ => ?_
  have hU : e 0 cpt ∈ U := by
    have : nbhdPt _ hres (IsLocalRing.closedPoint _) ∈ U :=
      h₁ (show IsLocalRing.closedPoint _ ∈ (⊤ : (Spec _).Opens) from trivial)
    rwa [hpt] at this
  rw [nbhdPt_appLE _ hres hloc U hU h₁, Iso.comp_inv_eq]
  have h0 : ⊤ ≤ (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ v) ⁻¹ᵁ U := by
    have := top_le_of_mem hU
    rwa [← hd.1] at this
  have hfst := specMap_comp_appLE (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) v U h0 h₂
  rw [appLE_congr_hom hd.1 U h0 (top_le_of_mem hU)] at hfst
  have hf1 : ∀ f, (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((e 0).appLE U ⊤ (top_le_of_mem hU) f) =
      TrivSqZeroExt.fst ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom (v.appLE U ⊤ h₂ f)) := fun f => by
    have := ConcreteCategory.congr_hom hfst f
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
    exact this
  ext f
  · rw [CommRingCat.comp_apply, jetψ_apply]
    change ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) (jetOf (0 + 1) _)).fst = _
    rw [jetTan_jetOf, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
      valAt'_of _ _ (top_le_of_mem hU)]
    exact hf1 f
  · rw [CommRingCat.comp_apply, jetψ_apply]
    change ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) (jetOf (0 + 1) _)).snd = _
    rw [jetTan_jetOf, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
    exact (hd.2 U h₂ f).symm

end ReciprocityTheory.ChartRestriction.G.PullbackSections

import Formalism.SharpRestriction.CuspSpanNormBounds.KTwoMinorIntegrality

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.MinorIntegralityTorus

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

/- English proof (translation)
Establish `h` using `Algebra.norm_eq_prod_embeddings ℚ ℂ x`. Establish `h2 : ∏ σ : K →+* ℂ, σ x = ∏ σ : K →ₐ[ℚ] ℂ, σ x` using `Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => rfl)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem prod_norm_emb_eq_abs_norm {K : Type*} [Field K] [NumberField K] (x : K) :
    ∏ σ : K →+* ℂ, ‖σ x‖ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  have h2 : ∏ σ : K →+* ℂ, σ x = ∏ σ : K →ₐ[ℚ] ℂ, σ x :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => rfl)
  calc ∏ σ : K →+* ℂ, ‖σ x‖ = ‖∏ σ : K →+* ℂ, σ x‖ := (norm_prod _ _).symm
    _ = ‖algebraMap ℚ ℂ (Algebra.norm ℚ x)‖ := by rw [h2, h]
    _ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by simp

/- English proof (translation)
Use `set y : 𝓞 K := ⟨x, hx⟩ with hy_def`. Establish `hy : y ≠ 0`. Introduce `h`. Apply `h0` to reduce the goal to its premises. Use `first`.

Consider the case `exact congrArg Subtype.val h`. Consider the case `simpa [y] using congrArg (algebraMap (𝓞 K) K) h`. Establish `hN : Algebra.norm ℤ y ≠ 0` using `Algebra.norm_ne_zero_iff.mpr hy`. Establish `hc : ((Algebra.norm ℤ y : ℤ) : ℚ) = Algebra.norm ℚ x` using `Algebra.coe_norm_int y`. Rewrite using `[← hc]`.

Establish `h1 : (1 : ℤ) ≤ |Algebra.norm ℤ y|` using `Int.one_le_abs hN`. Conclude with `h1` after adjusting the coercions.
-/
theorem one_le_abs_norm {K : Type*} [Field K] [NumberField K] (x : K) (hx : IsIntegral ℤ x) (h0 : x ≠ 0) :
    1 ≤ |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  set y : 𝓞 K := ⟨x, hx⟩ with hy_def
  have hy : y ≠ 0 := by
    intro h
    apply h0
    first
    | exact congrArg Subtype.val h
    | simpa [y] using congrArg (algebraMap (𝓞 K) K) h
  have hN : Algebra.norm ℤ y ≠ 0 := Algebra.norm_ne_zero_iff.mpr hy
  have hc : ((Algebra.norm ℤ y : ℤ) : ℚ) = Algebra.norm ℚ x := Algebra.coe_norm_int y
  rw [← hc]
  have h1 : (1 : ℤ) ≤ |Algebra.norm ℤ y| := Int.one_le_abs hN
  exact_mod_cast h1

/- English proof (translation)
Establish `cc : ∀ σ : K →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ) = σ`. Introduce `σ`. Use extensionality with `z`. Simplify using the standard rewrite rules. Establish `hinj : Set.InjOn (fun φ : K →+* ℂ => (starRingEnd ℂ).comp φ) ↑(Finset.univ.filter (· ∈ Φ))`.

Introduce `a _ c _ hab`. Use extensionality with `z`. Establish `h1` using `congrArg (fun ψ : K →+* ℂ => ψ z) hab`. Simplify using `only [RingHom.comp_apply] at h1`. Conclude with `(starRingEnd ℂ).injective h1`.

Establish `hc : (Finset.univ.filter (· ∈ Φ))ᶜ = (Finset.univ.filter (· ∈ Φ)).image (fun φ : K →+* ℂ => (starRingEnd ℂ).comp φ)`. Use extensionality with `σ`. Simplify using `only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce `hσ`.

Use `⟨(starRingEnd ℂ).comp σ, ?_, cc σ⟩` and prove the remaining obligations. Rewrite using `[hΦ, cc]`. Conclude with `hσ`. Introduce and unpack `⟨τ, hτ, rfl⟩`. Conclude with `(hΦ τ).1 hτ`.

Rewrite using `[← Finset.prod_mul_prod_compl (Finset.univ.filter (· ∈ Φ)), hc, Finset.prod_image hinj, Finset.prod_pow, sq]`. Use `congr 1`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `σ _`. Simplify using the standard rewrite rules.
-/
theorem prod_cm {K : Type*} [Field K] [NumberField K] (Φ : Set (K →+* ℂ))
    (hΦ : ∀ φ : K →+* ℂ, φ ∈ Φ ↔ (starRingEnd ℂ).comp φ ∉ Φ) (x : K) :
    ∏ σ : K →+* ℂ, ‖σ x‖ = ∏ σ ∈ Finset.univ.filter (· ∈ Φ), ‖σ x‖ ^ 2 := by
  have cc : ∀ σ : K →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ) = σ := by
    intro σ
    ext z
    simp
  have hinj : Set.InjOn (fun φ : K →+* ℂ => (starRingEnd ℂ).comp φ)
      ↑(Finset.univ.filter (· ∈ Φ)) := by
    intro a _ c _ hab
    ext z
    have h1 := congrArg (fun ψ : K →+* ℂ => ψ z) hab
    simp only [RingHom.comp_apply] at h1
    exact (starRingEnd ℂ).injective h1
  have hc : (Finset.univ.filter (· ∈ Φ))ᶜ =
      (Finset.univ.filter (· ∈ Φ)).image (fun φ : K →+* ℂ => (starRingEnd ℂ).comp φ) := by
    ext σ
    simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hσ
      refine ⟨(starRingEnd ℂ).comp σ, ?_, cc σ⟩
      rw [hΦ, cc]
      exact hσ
    · rintro ⟨τ, hτ, rfl⟩
      exact (hΦ τ).1 hτ
  rw [← Finset.prod_mul_prod_compl (Finset.univ.filter (· ∈ Φ)), hc, Finset.prod_image hinj,
    Finset.prod_pow, sq]
  congr 1
  apply Finset.prod_congr rfl
  intro σ _
  simp

/- English proof (translation)
Introduce `D x hx h0`. Establish `hcm` using `D.host.der.cmType`. Establish `hemb` using `Formalism.BasicNotions.factEmb D.R D.host`. Establish `hre : ∏ τ : D.what₂.Tau, ‖embS D τ x‖ ^ 2 = ∏ σ ∈ Finset.univ.filter (· ∈ D.host.cmType), ‖σ x‖ ^ 2`. Use `Finset.prod_bij (fun τ _ => embS D τ) ?_ ?_ ?_ ?_` and prove the remaining obligations.

Introduce `τ _`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `(hemb.2 _).2 (D.eTau τ).2`. Introduce `τ₁ _ τ₂ _ h`. Establish `h'` using `hemb.1.1 h`.

Conclude with `D.eTau.injective (Subtype.ext h')`. Introduce `σ hσ`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ`. Take `⟨g, rfl⟩` from `hemb.1.2 σ`. Establish `hg : g ∈ D.R.Psi` using `(hemb.2 g).1 hσ`.

Conclude with `⟨D.eTau.symm ⟨g, hg⟩, Finset.mem_univ _, by simp [embS]⟩`. Introduce `τ _`. Both sides reduce to the same expression. Rewrite using `[hre, ← prod_cm _ hcm.1 x, prod_norm_emb_eq_abs_norm]`. Conclude with `one_le_abs_norm x hx h0`.
-/
theorem NormLB_holds : Formalism.MainNotions.KTwoMinorIntegrality.NormLB := by
  intro D x hx h0
  have hcm := D.host.der.cmType
  have hemb := Formalism.BasicNotions.factEmb D.R D.host
  have hre : ∏ τ : D.what₂.Tau, ‖embS D τ x‖ ^ 2 =
      ∏ σ ∈ Finset.univ.filter (· ∈ D.host.cmType), ‖σ x‖ ^ 2 := by
    refine Finset.prod_bij (fun τ _ => embS D τ) ?_ ?_ ?_ ?_
    · intro τ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hemb.2 _).2 (D.eTau τ).2
    · intro τ₁ _ τ₂ _ h
      have h' := hemb.1.1 h
      exact D.eTau.injective (Subtype.ext h')
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      obtain ⟨g, rfl⟩ := hemb.1.2 σ
      have hg : g ∈ D.R.Psi := (hemb.2 g).1 hσ
      exact ⟨D.eTau.symm ⟨g, hg⟩, Finset.mem_univ _, by simp [embS]⟩
    · intro τ _
      rfl
  rw [hre, ← prod_cm _ hcm.1 x, prod_norm_emb_eq_abs_norm]
  exact one_le_abs_norm x hx h0

/- English proof (translation)
Rewrite using `[zpow_neg, zpow_natCast]`. Establish `hne : ((I : FractionalIdeal (nonZeroDivisors R) K) ^ n) ≠ 0` using `pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr hI)`. Rewrite using `[FractionalIdeal.mem_inv_iff hne]`. Introduce `y hy`. Rewrite using `[one_mul]`.

Establish `hle : ((I : FractionalIdeal (nonZeroDivisors R) K) ^ n) ≤ 1`. Rewrite using `[← FractionalIdeal.coeIdeal_pow]`. Conclude with `FractionalIdeal.coeIdeal_le_one`. Conclude with `hle hy`.
-/
theorem one_mem_zpow {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (I : Ideal R) (hI : I ≠ ⊥) (n : ℕ) :
    (1 : K) ∈ ((I : FractionalIdeal (nonZeroDivisors R) K) ^ (-(n : ℤ))) := by
  rw [zpow_neg, zpow_natCast]
  have hne : ((I : FractionalIdeal (nonZeroDivisors R) K) ^ n) ≠ 0 :=
    pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr hI)
  rw [FractionalIdeal.mem_inv_iff hne]
  intro y hy
  rw [one_mul]
  have hle : ((I : FractionalIdeal (nonZeroDivisors R) K) ^ n) ≤ 1 := by
    rw [← FractionalIdeal.coeIdeal_pow]
    exact FractionalIdeal.coeIdeal_le_one
  exact hle hy

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fr

variable (D : D7)

/- English proof (translation)
Conclude with `Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot`.
-/
theorem ddS_ideal_ne : (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) :
    Ideal (𝓞 D.host.E)) ≠ ⊥ := by
  exact Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot

/- English proof (translation)
Unfold `XS ddS`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨a, 1, ?_, (one_smul _ _).symm⟩` and prove the remaining obligations. Use `one_mem_zpow _ (ddS_ideal_ne D) (D.R.rS - (a : ℕ))` and compare the differences between its conclusion and the goal. Use `a.isLt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem e_mem_XS {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (a : Fin D.R.rS) : F0.e a ∈ XS D F0 := by
  unfold XS ddS
  apply Submodule.subset_span
  refine ⟨a, 1, ?_, (one_smul _ _).symm⟩
  convert one_mem_zpow _ (ddS_ideal_ne D) (D.R.rS - (a : ℕ))
  have := a.isLt
  omega

/- English proof (translation)
Unfold `XLam at hX`. Establish `h` using `e_mem_XS D F.fl a`. Rewrite `h` using `[← hX]`. Conclude with `(Submodule.mem_inf.mp h).1`.
-/
theorem e_mem_lam {T : D.host.E} (Λ : Submodule (𝓞 D.host.E) (hS D).V) (F : LFlag (hS D) D.R.rS T)
    (hX : XLam Λ F = XS D F.fl) (a : Fin D.R.rS) : F.fl.e a ∈ Λ := by
  unfold XLam at hX
  have h := e_mem_XS D F.fl a
  rw [← hX] at h
  exact (Submodule.mem_inf.mp h).1

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.IsUnimodular at hU`. Rewrite `hx` using `[← hU]`. Unfold `Formalism.HermitianLatticesTheory.dual Formalism.E.hdual at hx`. Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap] at hx`. Take `⟨r, hr⟩` from `Submodule.mem_one.mp (hx y hy)`.

Establish `hr' : ((hS D).hT y) x = algebraMap (𝓞 D.host.E) D.host.E r` using `hr.symm`. Rewrite using `[hr']`. Use `first`. Consider the case `exact r.2`. Consider the case `exact RingOfIntegers.isIntegral_coe r`.

Consider the case `exact RingOfIntegers.isIntegral r`.
-/
theorem pair_int {Λ : Submodule (𝓞 D.host.E) (hS D).V} (hU : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ)
    {x y : (hS D).V} (hx : x ∈ Λ) (hy : y ∈ Λ) : IsIntegral ℤ ((hS D).hT y x) := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodular at hU
  rw [← hU] at hx
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual at hx
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hx
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hx y hy)
  have hr' : ((hS D).hT y) x = algebraMap (𝓞 D.host.E) D.host.E r := hr.symm
  rw [hr']
  first
  | exact r.2
  | exact RingOfIntegers.isIntegral_coe r
  | exact RingOfIntegers.isIntegral r

end Fr

/- English proof (translation)
Set `M' : Matrix n n (integralClosure ℤ E)` to `fun i j => ⟨M i j, h i j⟩`. Establish `hM : (integralClosure ℤ E).val.toRingHom.mapMatrix M' = M`. Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite using `[← hM, ← RingHom.map_det]`.

Conclude with `(M'.det).2`.
-/
theorem det_isIntegral {E : Type*} [Field E] {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n E)
    (h : ∀ i j, IsIntegral ℤ (M i j)) : IsIntegral ℤ M.det := by
  let M' : Matrix n n (integralClosure ℤ E) := fun i j => ⟨M i j, h i j⟩
  have hM : (integralClosure ℤ E).val.toRingHom.mapMatrix M' = M := by
    ext i j
    rfl
  rw [← hM, ← RingHom.map_det]
  exact (M'.det).2

/- English proof (translation)
Introduce `D X u t hF l hl`. Take `⟨-, -, hRow, hOK⟩` from `hF`. Establish `hU : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT (X.abelian₂ t)` using `hRow.2.1.2.1`. Establish `he : ∀ a, (X.fl t).fl.e a ∈ X.abelian₂ t` using `e_mem_lam D (X.abelian₂ t) (lf D (X.fl t).fl) hRow.2.2`. Establish `he' : ∀ a, (X.fl' t).fl.e a ∈ X.abelian₂ t` using `e_mem_lam D (X.abelian₂ t) (X.fl' t) hOK.2`.

Establish `hl' : l ≤ D.R.rS + 1` using `by omega`. Unfold `Dl leadMinorE`. Rewrite using `[dif_pos hl']`. Apply `det_isIntegral` to reduce the goal to its premises. Introduce `i j`.

Establish `hi : Fin.castLE hl' i = Fin.castSucc ⟨i, by omega⟩` using `Fin.ext rfl`. Establish `hj : Fin.castLE hl' j = Fin.castSucc ⟨j, by omega⟩` using `Fin.ext rfl`. Simplify using `only [Matrix.submatrix_apply, Zhat, brS]`. Rewrite using `[hi, hj]`. Simplify using `only [FlagG.fvec, Fin.snoc_castSucc]`.

Conclude with `pair_int D hU (he' _) (he _)`.
-/
theorem MinorInt_holds : Formalism.MainNotions.KTwoMinorIntegrality.MinorInt := by
  intro D X u t hF l hl
  obtain ⟨-, -, hRow, hOK⟩ := hF
  have hU : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT (X.abelian₂ t) := hRow.2.1.2.1
  have he : ∀ a, (X.fl t).fl.e a ∈ X.abelian₂ t := e_mem_lam D (X.abelian₂ t) (lf D (X.fl t).fl) hRow.2.2
  have he' : ∀ a, (X.fl' t).fl.e a ∈ X.abelian₂ t := e_mem_lam D (X.abelian₂ t) (X.fl' t) hOK.2
  have hl' : l ≤ D.R.rS + 1 := by omega
  unfold Dl leadMinorE
  rw [dif_pos hl']
  apply det_isIntegral
  intro i j
  have hi : Fin.castLE hl' i = Fin.castSucc ⟨i, by omega⟩ := Fin.ext rfl
  have hj : Fin.castLE hl' j = Fin.castSucc ⟨j, by omega⟩ := Fin.ext rfl
  simp only [Matrix.submatrix_apply, Zhat, brS]
  rw [hi, hj]
  simp only [FlagG.fvec, Fin.snoc_castSucc]
  exact pair_int D hU (he' _) (he _)

end Formalism.MainNotions.MinorIntegralityTorus

end

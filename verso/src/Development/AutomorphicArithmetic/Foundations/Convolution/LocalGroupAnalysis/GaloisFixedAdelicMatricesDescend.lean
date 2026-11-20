import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import Development.AutomorphicArithmetic.AdelicQuotients.TwNormConjDiagonalEqConjNormGL
import Development.AutomorphicArithmetic.AdelicQuotients.AdelicGLGaloisBaseChangeDiagonalCompat
import Development.AutomorphicArithmetic.AdelicQuotients.CentralizerCommutativeOfSeparableCharpoly
open PositivityTheory.Rg.Tf.Geo
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc
open scoped NumberField.AdeleRing TensorProduct

section
variable {F E : Type} [Field F] [Field E] [Algebra F E]

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul l a`. Simplify using `only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, AlgHom.coe_coe]`. Establish `h : ∑ τ : E ≃ₐ[F] E, ((τ : E →ₐ[F] E) : E → E) l = algebraMap F E (Algebra.trace F E l)` using `(trace_eq_sum_automorphisms l).symm`.

Rewrite using `[← TensorProduct.sum_tmul, h, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`. Consider the case `add a b ha hb`. Simplify using `only [map_add, Finset.sum_add_distrib, ha, hb, TensorProduct.tmul_add]`.
-/
private theorem sum_map_tensor [FiniteDimensional F E] [IsGalois F E] {A : Type} [CommRing A] [Algebra F A]
    (t : E ⊗[F] A) :
    ∑ τ : E ≃ₐ[F] E, Algebra.TensorProduct.map (τ : E →ₐ[F] E) (AlgHom.id F A) t =
      (1 : E) ⊗ₜ[F] (TensorProduct.lid F A (LinearMap.rTensor A (Algebra.trace F E) t)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul l a =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, LinearMap.rTensor_tmul,
      TensorProduct.lid_tmul, AlgHom.coe_coe]
    have h : ∑ τ : E ≃ₐ[F] E, ((τ : E →ₐ[F] E) : E → E) l = algebraMap F E (Algebra.trace F E l) :=
      (trace_eq_sum_automorphisms l).symm
    rw [← TensorProduct.sum_tmul, h, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add a b ha hb =>
    simp only [map_add, Finset.sum_add_distrib, ha, hb, TensorProduct.tmul_add]

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul l a => simp [Algebra.TensorProduct.map_tmul]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
private theorem map_mul_tensor {A : Type} [CommRing A] [Algebra F A] (τ τ' : E ≃ₐ[F] E) (t : E ⊗[F] A) :
    Algebra.TensorProduct.map ((τ * τ' : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F A) t =
      Algebra.TensorProduct.map (τ : E →ₐ[F] E) (AlgHom.id F A)
        (Algebra.TensorProduct.map (τ' : E →ₐ[F] E) (AlgHom.id F A) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul l a => simp [Algebra.TensorProduct.map_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]

/- English proof (translation)
Establish `hpow : ∀ k : ℕ, Algebra.TensorProduct.map ((σ ^ k : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F A) T = T`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Rewrite using `[pow_zero]`.

Establish `: ((1 : E ≃ₐ[F] E) : E →ₐ[F] E) = AlgHom.id F E` using `rfl`. Rewrite using `[this, Algebra.TensorProduct.map_id]`. Both sides reduce to the same expression. Consider the case `succ k ih => rw [pow_succ, map_mul_tensor, h, ih]`. Establish `hall : ∀ τ : E ≃ₐ[F] E, Algebra.TensorProduct.map (τ : E →ₐ[F] E) (AlgHom.id F A) T = T`.

Introduce `τ`. Take `⟨k, rfl⟩` from `(mem_powers_iff_mem_zpowers).2 (hσ τ)`. Conclude with `hpow k`. Establish `hs` using `sum_map_tensor (F := F) (E := E) T`. Simplify using `only [hall, Finset.sum_const, Finset.card_univ] at hs`.

Establish `hc : ((Fintype.card (E ≃ₐ[F] E) : ℕ) : F) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Use `⟨((Fintype.card (E ≃ₐ[F] E) : ℕ) : F)⁻¹ • TensorProduct.lid F A (LinearMap.rTensor A (Algebra.trace F E) T), ?_⟩` and prove the remaining obligations. Rewrite using `[TensorProduct.tmul_smul, ← hs, ← Nat.cast_smul_eq_nsmul F, smul_smul, inv_mul_cancel₀ hc, one_smul]`.
-/
private theorem fixed_tensor [FiniteDimensional F E] [IsGalois F E] {A : Type} [CommRing A] [Algebra F A]
    (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) (T : E ⊗[F] A)
    (h : Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F A) T = T) [CharZero F] :
    ∃ a : A, (1 : E) ⊗ₜ[F] a = T := by
  have hpow : ∀ k : ℕ, Algebra.TensorProduct.map ((σ ^ k : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F A) T = T := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero]
      have : ((1 : E ≃ₐ[F] E) : E →ₐ[F] E) = AlgHom.id F E := rfl
      rw [this, Algebra.TensorProduct.map_id]
      rfl
    | succ k ih => rw [pow_succ, map_mul_tensor, h, ih]
  have hall : ∀ τ : E ≃ₐ[F] E, Algebra.TensorProduct.map (τ : E →ₐ[F] E) (AlgHom.id F A) T = T := by
    intro τ
    obtain ⟨k, rfl⟩ := (mem_powers_iff_mem_zpowers).2 (hσ τ)
    exact hpow k
  have hs := sum_map_tensor (F := F) (E := E) T
  simp only [hall, Finset.sum_const, Finset.card_univ] at hs
  have hc : ((Fintype.card (E ≃ₐ[F] E) : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨((Fintype.card (E ≃ₐ[F] E) : ℕ) : F)⁻¹ • TensorProduct.lid F A (LinearMap.rTensor A (Algebra.trace F E) T), ?_⟩
  rw [TensorProduct.tmul_smul, ← hs, ← Nat.cast_smul_eq_nsmul F, smul_smul, inv_mul_cancel₀ hc, one_smul]
end

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Establish `h1 : Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F]) ((adeleTensorEquiv F E).symm y) = (adeleTensorEquiv F E).symm y`. Apply `(adeleTensorEquiv F E).injective` to reduce the goal to its premises. Rewrite using `[AlgEquiv.apply_symm_apply]`. Conclude with `hy`.

Take `⟨a, ha⟩` from `fixed_tensor σ hσ _ h1`. Use `⟨a, ?_⟩` and prove the remaining obligations. Use `congrArg (adeleTensorEquiv F E) ha` as an intermediate fact. Rewrite `this` using `[AlgEquiv.apply_symm_apply, adeleTensorEquiv_tmul, map_one, one_mul]`. Then use the resulting hypothesis.
-/
private theorem fixed_adele [IsGalois F E] (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ)
    (y : 𝔸[E]) (hy : galAd σ y = y) : ∃ a, adeleMap F E a = y := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h1 : Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F]) ((adeleTensorEquiv F E).symm y) =
      (adeleTensorEquiv F E).symm y := by
    apply (adeleTensorEquiv F E).injective
    rw [AlgEquiv.apply_symm_apply]
    exact hy
  obtain ⟨a, ha⟩ := fixed_tensor σ hσ _ h1
  refine ⟨a, ?_⟩
  have := congrArg (adeleTensorEquiv F E) ha
  rwa [AlgEquiv.apply_symm_apply, adeleTensorEquiv_tmul, map_one, one_mul] at this

/- English proof (translation)
Express the relevant statement in the definitionally equal form `adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F]) ((adeleTensorEquiv F E).symm (adeleMap F E a))) = _`. Rewrite using `[adeleTensorEquiv_symm_adeleMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul, map_one, map_one, one_mul]`. Both sides reduce to the same expression.
-/
private theorem galAd_adeleMap (σ : E ≃ₐ[F] E) (a : 𝔸[F]) : galAd σ (adeleMap F E a) = adeleMap F E a := by
  change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
    ((adeleTensorEquiv F E).symm (adeleMap F E a))) = _
  rw [adeleTensorEquiv_symm_adeleMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul, map_one, map_one, one_mul]
  rfl

/- English proof (translation)
Establish `: ∀ i j, ∃ a, adeleMap F E a = (y : Matrix (Fin n) (Fin n) 𝔸[E]) i j` using `fun i j => fixed_adele σ hσ _ (congrArg (fun u : AdelicGLn.AdelicGL E n => (u : Matrix (Fin n) (Fin n) 𝔸[E]) i j) hy)`. Use `choose M hM using this`. Conclude with `⟨Matrix.of M, Matrix.ext hM⟩`.
-/
private theorem fixed_mat [IsGalois F E] (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) {n : ℕ}
    (y : AdelicGLn.AdelicGL E n) (hy : mapGL n (galAd σ) y = y) :
    ∃ M : Matrix (Fin n) (Fin n) 𝔸[F], M.map (adeleMap F E) = (y : Matrix (Fin n) (Fin n) 𝔸[E]) := by
  have : ∀ i j, ∃ a, adeleMap F E a = (y : Matrix (Fin n) (Fin n) 𝔸[E]) i j := fun i j =>
    fixed_adele σ hσ _ (congrArg (fun u : AdelicGLn.AdelicGL E n => (u : Matrix (Fin n) (Fin n) 𝔸[E]) i j) hy)
  choose M hM using this
  exact ⟨Matrix.of M, Matrix.ext hM⟩
end

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ σ hσ n hn δ γ hγ hN x`. Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Establish `hp : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank F E = 1`. Rewrite using `[← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]`. Establish `hfix : sigmaGL σ (incl γ : GL (Fin n) E) = incl γ`.

Use extensionality with `i j`. Conclude with `σ.commutes _`. Establish `hδ : δ * incl γ = incl γ * δ`. Establish `h` using `map_twNorm_of_pow_eq_one (sigmaGL σ) hp δ`. Express the relevant statement in the definitionally equal form `sigmaGL σ (normGL σ δ) = δ⁻¹ * normGL σ δ * δ at h`.

Rewrite `h` using `[hN, hfix]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨-, hmapd, -⟩` from `UpperTheory.adelicGL_galois_baseChange_diagonal_compat F E σ n`. Establish `hDΓ : AdelicGLn.diagonal E n δ * AdelicGLn.diagonal E n (incl γ) = AdelicGLn.diagonal E n (incl γ) * AdelicGLn.diagonal E n δ`. Rewrite using `[← map_mul, ← map_mul, hδ]`.

Establish `hC : ∀ s t : AdelicGLn.AdelicGL E n, s * AdelicGLn.diagonal E n (incl γ) = AdelicGLn.diagonal E n (incl γ) * s → t * AdelicGLn.diagonal E n (incl γ) = AdelicGLn.diagonal E n (incl γ) * t → s * t = t * s`. Introduce `s t hs ht`. Establish `hD : ((AdelicGLn.diagonal E n (incl γ) : AdelicGLn.AdelicGL E n) : Matrix (Fin n) (Fin n) 𝔸[E]) = (γ : Matrix (Fin n) (Fin n) F).map ((algebraMap E 𝔸[E]).comp (algebraMap F E))`. Use extensionality with `a b`. Both sides reduce to the same expression.

Establish `hs' : (s : Matrix (Fin n) (Fin n) 𝔸[E]) * (γ : Matrix (Fin n) (Fin n) F).map ((algebraMap E 𝔸[E]).comp (algebraMap F E)) = (γ : Matrix (Fin n) (Fin n) F).map ((algebraMap E 𝔸[E]).comp (algebraMap F E)) * (s : Matrix (Fin n) (Fin n) 𝔸[E])`. Rewrite using `[← hD]`. Conclude with `congrArg Units.val hs`. Establish `ht' : (t : Matrix (Fin n) (Fin n) 𝔸[E]) * (γ : Matrix (Fin n) (Fin n) F).map ((algebraMap E 𝔸[E]).comp (algebraMap F E)) = (γ : Matrix (Fin n) (Fin n) F).map ((algebraMap E 𝔸[E]).comp (algebraMap F E)) * (t : Matrix (Fin n) (Fin n) 𝔸[E])`. Rewrite using `[← hD]`.

Conclude with `congrArg Units.val ht`. Conclude with `Units.ext (UpperTheory.centralizer_commutative_of_separable_charpoly F 𝔸[E] _ n _ hγ _ _ hs' ht')`. Establish `hinjM : Function.Injective (fun M : Matrix (Fin n) (Fin n) 𝔸[F] => M.map (adeleMap F E))` using `Matrix.map_injective adeleMap_injective`. Establish `hinjG : Function.Injective (mapGL n (adeleMap F E) : AdelicGLn.AdelicGL F n → AdelicGLn.AdelicGL E n)` using `fun a b h => Units.ext (hinjM (congrArg Units.val h))`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Establish `h1` using `UpperTheory.twNorm_conj_diagonal_eq_conj_normGL F E σ n δ x`. Establish `h0` using `UpperTheory.twNorm_conj_diagonal_eq_conj_normGL F E σ n δ 1`. Rewrite `h1` using `[hx]`. Simplify using `only [inv_one, one_mul, map_one, mul_one] at h0`.

Rewrite `h1` using `[h0, hN]`. Establish `hcom : x * AdelicGLn.diagonal E n (incl γ) = AdelicGLn.diagonal E n (incl γ) * x`. Combine the equalities or inequalities in the displayed calculation. Establish `hxD` using `hC x _ hcom hDΓ`. Establish `hθ : mapGL n (galAd σ) x = x`.

Combine the equalities or inequalities in the displayed calculation. Establish `hθ' : mapGL n (galAd σ) x⁻¹ = x⁻¹` using `by rw [map_inv, hθ]`. Take `⟨M, hM⟩` from `fixed_mat σ hσ x hθ`. Take `⟨N, hN'⟩` from `fixed_mat σ hσ x⁻¹ hθ'`. Establish `hMN : M * N = 1` using `hinjM (by`.

Express the relevant statement in the definitionally equal form `(M * N).map (adeleMap F E) = (1 : Matrix (Fin n) (Fin n) 𝔸[F]).map (adeleMap F E)`. Rewrite using `[Matrix.map_mul, hM, hN', Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `congrArg Units.val (mul_inv_cancel x))`. Establish `hNM : N * M = 1` using `hinjM (by`. Express the relevant statement in the definitionally equal form `(N * M).map (adeleMap F E) = (1 : Matrix (Fin n) (Fin n) 𝔸[F]).map (adeleMap F E)`.

Rewrite using `[Matrix.map_mul, hM, hN', Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `congrArg Units.val (inv_mul_cancel x))`. Establish `he : mapGL n (adeleMap F E) (⟨M, N, hMN, hNM⟩ : AdelicGLn.AdelicGL F n) = x` using `Units.ext hM`. Use `⟨⟨M, N, hMN, hNM⟩, hinjG ?_, he.symm⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, hmapd, he]`.

Conclude with `hcom`. Introduce and unpack `⟨t, ht, rfl⟩`. Establish `hcomm : mapGL n (adeleMap F E) t * AdelicGLn.diagonal E n (incl γ) = AdelicGLn.diagonal E n (incl γ) * mapGL n (adeleMap F E) t`. Rewrite using `[← hmapd, ← map_mul, ← map_mul, ht]`. Establish `hθ : mapGL n (galAd σ) (mapGL n (adeleMap F E) t) = mapGL n (adeleMap F E) t` using `Units.ext (Matrix.ext fun i j => galAd_adeleMap σ _)`.

Rewrite using `[hθ, mul_assoc, ← hC _ _ hcomm hDΓ]`. Use `group`.
-/
theorem UpperTheory.ConvolutionTheory.G.galois_fixed_adelic_matrices_descend :
    N3 := by
  intro F E _ _ _ _ _ _ σ hσ n hn δ γ hγ hN x
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hp : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank F E = 1 := by
    rw [← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]
  have hfix : sigmaGL σ (incl γ : GL (Fin n) E) = incl γ := by
    ext i j
    exact σ.commutes _
  have hδ : δ * incl γ = incl γ * δ := by
    have h := map_twNorm_of_pow_eq_one (sigmaGL σ) hp δ
    change sigmaGL σ (normGL σ δ) = δ⁻¹ * normGL σ δ * δ at h
    rw [hN, hfix] at h
    calc δ * incl γ = δ * (δ⁻¹ * incl γ * δ) := by rw [← h]
      _ = incl γ * δ := by group
  obtain ⟨-, hmapd, -⟩ := UpperTheory.adelicGL_galois_baseChange_diagonal_compat F E σ n
  have hDΓ : AdelicGLn.diagonal E n δ * AdelicGLn.diagonal E n (incl γ) =
      AdelicGLn.diagonal E n (incl γ) * AdelicGLn.diagonal E n δ := by
    rw [← map_mul, ← map_mul, hδ]
  have hC : ∀ s t : AdelicGLn.AdelicGL E n, s * AdelicGLn.diagonal E n (incl γ) = AdelicGLn.diagonal E n (incl γ) * s →
      t * AdelicGLn.diagonal E n (incl γ) = AdelicGLn.diagonal E n (incl γ) * t → s * t = t * s := by
    intro s t hs ht
    have hD : ((AdelicGLn.diagonal E n (incl γ) : AdelicGLn.AdelicGL E n) : Matrix (Fin n) (Fin n) 𝔸[E]) =
        (γ : Matrix (Fin n) (Fin n) F).map ((algebraMap E 𝔸[E]).comp (algebraMap F E)) := by
      ext a b
      rfl
    have hs' : (s : Matrix (Fin n) (Fin n) 𝔸[E]) * (γ : Matrix (Fin n) (Fin n) F).map ((algebraMap E 𝔸[E]).comp (algebraMap F E)) =
        (γ : Matrix (Fin n) (Fin n) F).map ((algebraMap E 𝔸[E]).comp (algebraMap F E)) * (s : Matrix (Fin n) (Fin n) 𝔸[E]) := by
      rw [← hD]
      exact congrArg Units.val hs
    have ht' : (t : Matrix (Fin n) (Fin n) 𝔸[E]) * (γ : Matrix (Fin n) (Fin n) F).map ((algebraMap E 𝔸[E]).comp (algebraMap F E)) =
        (γ : Matrix (Fin n) (Fin n) F).map ((algebraMap E 𝔸[E]).comp (algebraMap F E)) * (t : Matrix (Fin n) (Fin n) 𝔸[E]) := by
      rw [← hD]
      exact congrArg Units.val ht
    exact Units.ext (UpperTheory.centralizer_commutative_of_separable_charpoly F 𝔸[E] _ n _ hγ _ _ hs' ht')
  have hinjM : Function.Injective (fun M : Matrix (Fin n) (Fin n) 𝔸[F] => M.map (adeleMap F E)) :=
    Matrix.map_injective adeleMap_injective
  have hinjG : Function.Injective (mapGL n (adeleMap F E) : AdelicGLn.AdelicGL F n → AdelicGLn.AdelicGL E n) := fun a b h =>
    Units.ext (hinjM (congrArg Units.val h))
  constructor
  · intro hx
    have h1 := UpperTheory.twNorm_conj_diagonal_eq_conj_normGL F E σ n δ x
    have h0 := UpperTheory.twNorm_conj_diagonal_eq_conj_normGL F E σ n δ 1
    rw [hx] at h1
    simp only [inv_one, one_mul, map_one, mul_one] at h0
    rw [h0, hN] at h1
    have hcom : x * AdelicGLn.diagonal E n (incl γ) = AdelicGLn.diagonal E n (incl γ) * x := by
      calc x * AdelicGLn.diagonal E n (incl γ) = x * (x⁻¹ * AdelicGLn.diagonal E n (incl γ) * x) := by rw [← h1]
        _ = AdelicGLn.diagonal E n (incl γ) * x := by group
    have hxD := hC x _ hcom hDΓ
    have hθ : mapGL n (galAd σ) x = x := by
      calc mapGL n (galAd σ) x = (AdelicGLn.diagonal E n δ)⁻¹ * x * (x⁻¹ * AdelicGLn.diagonal E n δ * mapGL n (galAd σ) x) := by group
        _ = (AdelicGLn.diagonal E n δ)⁻¹ * (x * AdelicGLn.diagonal E n δ) := by rw [hx, mul_assoc]
        _ = x := by rw [hxD]; group
    have hθ' : mapGL n (galAd σ) x⁻¹ = x⁻¹ := by rw [map_inv, hθ]
    obtain ⟨M, hM⟩ := fixed_mat σ hσ x hθ
    obtain ⟨N, hN'⟩ := fixed_mat σ hσ x⁻¹ hθ'
    have hMN : M * N = 1 := hinjM (by
      change (M * N).map (adeleMap F E) = (1 : Matrix (Fin n) (Fin n) 𝔸[F]).map (adeleMap F E)
      rw [Matrix.map_mul, hM, hN', Matrix.map_one _ (map_zero _) (map_one _)]
      exact congrArg Units.val (mul_inv_cancel x))
    have hNM : N * M = 1 := hinjM (by
      change (N * M).map (adeleMap F E) = (1 : Matrix (Fin n) (Fin n) 𝔸[F]).map (adeleMap F E)
      rw [Matrix.map_mul, hM, hN', Matrix.map_one _ (map_zero _) (map_one _)]
      exact congrArg Units.val (inv_mul_cancel x))
    have he : mapGL n (adeleMap F E) (⟨M, N, hMN, hNM⟩ : AdelicGLn.AdelicGL F n) = x := Units.ext hM
    refine ⟨⟨M, N, hMN, hNM⟩, hinjG ?_, he.symm⟩
    rw [map_mul, map_mul, hmapd, he]
    exact hcom
  · rintro ⟨t, ht, rfl⟩
    have hcomm : mapGL n (adeleMap F E) t * AdelicGLn.diagonal E n (incl γ) =
        AdelicGLn.diagonal E n (incl γ) * mapGL n (adeleMap F E) t := by
      rw [← hmapd, ← map_mul, ← map_mul, ht]
    have hθ : mapGL n (galAd σ) (mapGL n (adeleMap F E) t) = mapGL n (adeleMap F E) t :=
      Units.ext (Matrix.ext fun i j => galAd_adeleMap σ _)
    rw [hθ, mul_assoc, ← hC _ _ hcomm hDΓ]
    group

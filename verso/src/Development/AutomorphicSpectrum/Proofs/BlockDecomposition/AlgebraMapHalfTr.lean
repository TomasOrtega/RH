import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2

open PositivityTheory.RgEis PositivityTheory.RgEis.So

noncomputable section

namespace GlobalTheory.CompanionTheory.RgEisFix

open scoped TensorProduct
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨-, -, -, hτ⟩` from `h`. Set `τ : E →+* ℂ` to `Classical.arbitrary _`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hτ, hτ, star_star]`.
-/
theorem conj_conj (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, hτ⟩ := h
  let τ : E →+* ℂ := Classical.arbitrary _
  apply τ.injective
  rw [hτ, hτ, star_star]

/- English proof (translation)
Take `⟨-, hC, -, hτ⟩` from `h`. Assume the negation of the conclusion as `hno`. Use `push Not at hno`. Set `τ : E →+* ℂ` to `Classical.arbitrary _`. Establish `hR : ComplexEmbedding.IsReal τ`.

Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `x`. Conclude with `((hτ τ x).symm.trans (congrArg τ (hno x)) : _)`. Conclude with `(InfinitePlace.not_isReal_iff_isComplex.2 (hC.isComplex (InfinitePlace.mk τ))) (InfinitePlace.isReal_mk_iff.2 hR)`.
-/
theorem exists_moved (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ y, σ y ≠ y := by
  obtain ⟨-, hC, -, hτ⟩ := h
  by_contra hno
  push Not at hno
  let τ : E →+* ℂ := Classical.arbitrary _
  have hR : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    exact ((hτ τ x).symm.trans (congrArg τ (hno x)) : _)
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (hC.isComplex (InfinitePlace.mk τ)))
    (InfinitePlace.isReal_mk_iff.2 hR)

/- English proof (translation)
Set `S : Submodule F E` to `LinearMap.eqLocus σ.toLinearMap LinearMap.id`. Establish `hS : S ≠ ⊤`. Take `⟨y, hy⟩` from `exists_moved σ h`. Introduce `hT`. Establish `hyS : y ∈ S` using `hT ▸ Submodule.mem_top`.

Conclude with `hy hyS`. Establish `h1 : Submodule.span F {(1 : E)} ≤ S`. Rewrite using `[Submodule.span_singleton_le_iff_mem]`. Conclude with `map_one σ`. Establish `hlt : Module.finrank F S < 2` using `h.2.2.1 ▸ Submodule.finrank_lt hS`.

Establish `hone : Module.finrank F (Submodule.span F {(1 : E)}) = 1` using `finrank_span_singleton one_ne_zero`. Establish `heq : Submodule.span F {(1 : E)} = S` using `Submodule.eq_of_le_of_finrank_le h1 (by omega)`. Establish `hmem : e + σ e ∈ S`. Express the relevant statement in the definitionally equal form `σ (e + σ e) = e + σ e`. Rewrite using `[map_add, conj_conj σ h, add_comm]`.

Rewrite `hmem` using `[← heq, Submodule.mem_span_singleton]`. Take `⟨c, hc⟩` from `hmem`. Conclude with `⟨c, by rw [← hc, Algebra.algebraMap_eq_smul_one]⟩`.
-/
theorem add_conj_mem (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (e : E) :
    ∃ c : F, e + σ e = algebraMap F E c := by
  let S : Submodule F E := LinearMap.eqLocus σ.toLinearMap LinearMap.id
  have hS : S ≠ ⊤ := by
    obtain ⟨y, hy⟩ := exists_moved σ h
    intro hT
    have hyS : y ∈ S := hT ▸ Submodule.mem_top
    exact hy hyS
  have h1 : Submodule.span F {(1 : E)} ≤ S := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact map_one σ
  have hlt : Module.finrank F S < 2 := h.2.2.1 ▸ Submodule.finrank_lt hS
  have hone : Module.finrank F (Submodule.span F {(1 : E)}) = 1 :=
    finrank_span_singleton one_ne_zero
  have heq : Submodule.span F {(1 : E)} = S :=
    Submodule.eq_of_le_of_finrank_le h1 (by omega)
  have hmem : e + σ e ∈ S := by
    change σ (e + σ e) = e + σ e
    rw [map_add, conj_conj σ h, add_comm]
  rw [← heq, Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, by rw [← hc, Algebra.algebraMap_eq_smul_one]⟩

def halfTr (σ : E →ₐ[F] E) : E →ₗ[F] F :=
  (4⁻¹ : F) • (Algebra.trace F E ∘ₗ (LinearMap.id + σ.toLinearMap))

/- English proof (translation)
Take `⟨c, hc⟩` from `add_conj_mem σ h e`. Establish `hval : halfTr σ e = 2⁻¹ * c`. Simplify using `only [halfTr, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply, AlgHom.toLinearMap_apply, smul_eq_mul]`. Rewrite using `[hc, Algebra.trace_algebraMap, h.2.2.1, nsmul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hval, hc, Algebra.smul_def, map_mul]`.
-/
theorem algebraMap_halfTr (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (e : E) :
    algebraMap F E (halfTr σ e) = (2⁻¹ : F) • (e + σ e) := by
  obtain ⟨c, hc⟩ := add_conj_mem σ h e
  have hval : halfTr σ e = 2⁻¹ * c := by
    simp only [halfTr, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.id_apply, AlgHom.toLinearMap_apply, smul_eq_mul]
    rw [hc, Algebra.trace_algebraMap, h.2.2.1, nsmul_eq_mul]
    push_cast
    ring
  rw [hval, hc, Algebra.smul_def, map_mul]

/- English proof (translation)
Apply `(algebraMap F E).injective` to reduce the goal to its premises. Rewrite using `[algebraMap_halfTr σ h, map_one, map_one, Algebra.smul_def, map_inv₀, map_ofNat]`. Establish `h2 : (2 : E) ≠ 0` using `two_ne_zero`. Clear the denominators using the available nonvanishing facts. Evaluate the numerical expressions.
-/
theorem halfTr_one (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : halfTr σ (1 : E) = 1 := by
  apply (algebraMap F E).injective
  rw [algebraMap_halfTr σ h, map_one, map_one, Algebra.smul_def, map_inv₀, map_ofNat]
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  field_simp
  norm_num

def rr (σ : E →ₐ[F] E) : AE F E →ₗ[AF F] AF F :=
  (TensorProduct.AlgebraTensorModule.rid F (AF F) (AF F)).toLinearMap ∘ₗ
    TensorProduct.AlgebraTensorModule.lTensor (AF F) (AF F) (halfTr σ)

/- English proof (translation)
Simplify using `[rr]`.
-/
theorem rr_tmul (σ : E →ₐ[F] E) (a : AF F) (e : E) : rr σ (a ⊗ₜ[F] e) = halfTr σ e • a := by
  simp [rr]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem nu_apply (x : AF F) : nuCM F E x = x ⊗ₜ[F] (1 : E) := rfl

/- English proof (translation)
Rewrite using `[nu_apply, rr_tmul, halfTr_one σ h, one_smul]`.
-/
theorem rr_nu (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : AF F) : rr σ (nuCM F E x) = x := by
  rw [nu_apply, rr_tmul, halfTr_one σ h, one_smul]

/- English proof (translation)
Simplify using `[nu_apply, cA]`.
-/
theorem cA_nu (σ : E →ₐ[F] E) (x : AF F) : cA σ (nuCM F E x) = nuCM F E x := by
  simp [nu_apply, cA]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy`. Rewrite using `[map_add, map_add, hx, hy, map_add, ← smul_add]`. Use `congr 1`.

Normalize the expressions using the abelian group laws. Consider the case `tmul a e`. Establish `hc : cA σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e` using `by simp [cA]`. Rewrite using `[rr_tmul, nu_apply, hc, ← TensorProduct.tmul_add, ← TensorProduct.tmul_smul, ← algebraMap_halfTr σ h, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']`.
-/
theorem nu_rr (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (z : AE F E) :
    nuCM F E (rr σ z) = (2⁻¹ : F) • (z + cA σ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add, ← smul_add]
    congr 1
    abel
  | tmul a e =>
    have hc : cA σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := by simp [cA]
    rw [rr_tmul, nu_apply, hc, ← TensorProduct.tmul_add, ← TensorProduct.tmul_smul,
      ← algebraMap_halfTr σ h, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']

/- English proof (translation)
Establish `h : (nuCM F E : AF F → AE F E) = fun x => x • (1 : AE F E)`. Use function extensionality and compare the values at `x`. Rewrite using `[nu_apply, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[h]`. Conclude with `Continuous.smul (f := fun x : AF F => x) (g := fun _ => (1 : AE F E)) continuous_id continuous_const`.
-/
theorem continuous_nu : Continuous (nuCM F E) := by
  have h : (nuCM F E : AF F → AE F E) = fun x => x • (1 : AE F E) := by
    funext x
    rw [nu_apply, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h]
  exact Continuous.smul (f := fun x : AF F => x) (g := fun _ => (1 : AE F E)) continuous_id continuous_const

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ χ c hCM _ _ _`. Use `⟨continuous_nu, Function.LeftInverse.injective (rr_nu σ hCM), cA_nu σ, rr σ, IsModuleTopology.continuous_of_linearMap (rr σ), fun x hx => ?_⟩` and prove the remaining obligations. Establish `hx' : cA σ x = x` using `hx`. Rewrite using `[nu_rr σ hCM, hx', ← two_smul F x, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]`.
-/
theorem bFix : BFix := by
  intro F E _ _ _ _ _ σ χ c hCM _ _ _
  refine ⟨continuous_nu, Function.LeftInverse.injective (rr_nu σ hCM), cA_nu σ, rr σ,
    IsModuleTopology.continuous_of_linearMap (rr σ), fun x hx => ?_⟩
  have hx' : cA σ x = x := hx
  rw [nu_rr σ hCM, hx', ← two_smul F x, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

end GlobalTheory.CompanionTheory.RgEisFix

import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.PetEx
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Rewrite using `[rt_mulChi, map_smul, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]`.
-/
private theorem tw_rt (χ : HChar E) (g : GA E a) (φ : Sm E a) :
    mulChi a χ (rt E a g φ) = ((chiDet a χ g : ℂˣ) : ℂ)⁻¹ • rt E a g (mulChi a χ φ) := by
  rw [rt_mulChi, map_smul, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons X l ih`. Rewrite using `[List.map_cons, List.prod_cons, Module.End.mul_apply, Module.End.mul_apply, ih]`. Conclude with `LinearMap.congr_fun (lie_rt_fin X x) _`.
-/
private theorem prod_fin (x : GL (Fin a) (Af E)) (φ : Sm E a) (l : List (Lie E a)) :
    (l.map (lie E a)).prod (act (.fin x) φ) = act (.fin x) ((l.map (lie E a)).prod φ) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, Module.End.mul_apply, ih]
    exact LinearMap.congr_fun (lie_rt_fin X x) _

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact h`. Consider the case `cons X l ih`. Rewrite using `[List.map_cons, List.prod_cons, Module.End.mul_apply]`. Conclude with `(sqLie E a r).1 X _ ih`.
-/
private theorem prod_sq {r : ℝ} {φ : Sm E a} (h : IsSq r φ) (l : List (Lie E a)) :
    IsSq r ((l.map (lie E a)).prod φ) := by
  induction l with
  | nil => exact h
  | cons X l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    exact (sqLie E a r).1 X _ ih

/- English proof (translation)
Take `⟨χ, hχ⟩` from `twEx E a ha r`. Take `⟨s, hs⟩` from `hχ.1`. Set `μ : Measure (GA E a)` to `Measure.haar`. Use `haveI : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ`. Take `⟨h1, h2⟩` from `sqMem E a ha μ r χ hχ φ (Submodule.subset_span h)`.

Establish `h3` using `(sqUniq E a ha r χ hχ φ h.one (h.sq [])).1`. Establish `hc : Continuous (mulChi a χ φ).1` using `ContAut.continuous_of_isOpen_stab E a _ h1`. Use `⟨s, χ, hs, ?_⟩` and prove the remaining obligations. Establish `e : (fun g => ((chiDet a χ g : ℂˣ) : ℂ) * (act (.fin x) φ).1 g) = ((chiDet a χ (finGL E a x) : ℂˣ) : ℂ)⁻¹ • fun g => (mulChi a χ φ).1 (g * finGL E a x)`. Use function extensionality and compare the values at `g`.

Conclude with `(mul_comm _ _).trans (congrFun (congrArg Subtype.val (tw_rt χ (finGL E a x) φ)) g)`. Rewrite using `[e]`. Establish `h4` using `h2.mul_right (finGL E a x)`. Generalize the expression as in `((chiDet a χ (finGL E a x) : ℂˣ) : ℂ)⁻¹ = c`. Establish `hc' : Continuous fun g => (mulChi a χ φ).1 (g * finGL E a x)` using `hc.comp (continuous_id.mul continuous_const)`.

Use `(CuspidalL2GL.memL2_iff_isSqInt (μ := μ) (hc'.const_smul c) (fun γ g => ?_) (fun t g => ?_)).1 ⟨fun γ hγ g => congrArg (c • ·) (h4.1 γ hγ g), h4.2.const_smul c⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, mul_assoc]`. Rewrite using `[mulChi_apply, mulChi_apply, map_mul (chiDet a χ) (ratGL E a γ), chiDet_ratGL, one_mul, h.left]`. Simplify using `only [Pi.smul_apply, mul_assoc, h3]`.
-/
private theorem sqInt_fin (ha : 1 ≤ a) {r : ℝ} {φ : Sm E a} (h : IsSq r φ) (x : GL (Fin a) (Af E)) :
    IsSqIntMod (act (.fin x) φ) := by
  obtain ⟨χ, hχ⟩ := twEx E a ha r
  obtain ⟨s, hs⟩ := hχ.1
  let μ : Measure (GA E a) := Measure.haar
  haveI : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  obtain ⟨h1, h2⟩ := sqMem E a ha μ r χ hχ φ (Submodule.subset_span h)
  have h3 := (sqUniq E a ha r χ hχ φ h.one (h.sq [])).1
  have hc : Continuous (mulChi a χ φ).1 := ContAut.continuous_of_isOpen_stab E a _ h1
  refine ⟨s, χ, hs, ?_⟩
  have e : (fun g => ((chiDet a χ g : ℂˣ) : ℂ) * (act (.fin x) φ).1 g) =
      ((chiDet a χ (finGL E a x) : ℂˣ) : ℂ)⁻¹ • fun g => (mulChi a χ φ).1 (g * finGL E a x) := by
    funext g
    exact (mul_comm _ _).trans (congrFun (congrArg Subtype.val (tw_rt χ (finGL E a x) φ)) g)
  rw [e]
  have h4 := h2.mul_right (finGL E a x)
  generalize ((chiDet a χ (finGL E a x) : ℂˣ) : ℂ)⁻¹ = c
  have hc' : Continuous fun g => (mulChi a χ φ).1 (g * finGL E a x) := hc.comp (continuous_id.mul continuous_const)
  refine (CuspidalL2GL.memL2_iff_isSqInt (μ := μ) (hc'.const_smul c) (fun γ g => ?_)
    (fun t g => ?_)).1 ⟨fun γ hγ g => congrArg (c • ·) (h4.1 γ hγ g), h4.2.const_smul c⟩
  · simp only [Pi.smul_apply, mul_assoc]
    rw [mulChi_apply, mulChi_apply, map_mul (chiDet a χ) (ratGL E a γ), chiDet_ratGL, one_mul, h.left]
  · simp only [Pi.smul_apply, mul_assoc, h3]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `φ.1 (ratGL E a γ * g * finGL E a x) = φ.1 (g * finGL E a x)`. Rewrite using `[mul_assoc, h.left]`. Use `level := by`. Establish `e : {k | act (.fin k) (act (.fin x) φ) = act (.fin x) φ} = (fun k => x⁻¹ * k * x) ⁻¹' {k | act (.fin k) φ = φ}`. Use extensionality with `k`.

Express the relevant statement in the definitionally equal form `finRep E a k (finRep E a x φ) = finRep E a x φ ↔ finRep E a (x⁻¹ * k * x) φ = φ`. Rewrite using `[map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `hk`. Rewrite using `[hk, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`.

Introduce `hk`. Use `congrArg (finRep E a x) hk` as an intermediate fact. Rewrite `this` using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Then use the resulting hypothesis. Rewrite using `[e]`. Conclude with `h.level.preimage (by fun_prop)`.

Use `one := by`. Establish `e : lie E a (oneL E a) (act (.fin x) φ) = act (.fin x) (lie E a (oneL E a) φ)` using `LinearMap.congr_fun (lie_rt_fin _ x) φ`. Rewrite using `[e, h.one, map_smul]`. Use `sq l := by`. Rewrite using `[prod_fin]`.

Conclude with `sqInt_fin ha (prod_sq h l) x`.
-/
private theorem isSq_fin (ha : 1 ≤ a) {r : ℝ} (x : GL (Fin a) (Af E)) (φ : Sm E a) (h : IsSq r φ) :
    IsSq r (act (.fin x) φ) where
  left γ g := by
    change φ.1 (ratGL E a γ * g * finGL E a x) = φ.1 (g * finGL E a x)
    rw [mul_assoc, h.left]
  level := by
    have e : {k | act (.fin k) (act (.fin x) φ) = act (.fin x) φ} =
        (fun k => x⁻¹ * k * x) ⁻¹' {k | act (.fin k) φ = φ} := by
      ext k
      change finRep E a k (finRep E a x φ) = finRep E a x φ ↔ finRep E a (x⁻¹ * k * x) φ = φ
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      constructor
      · intro hk
        rw [hk, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      · intro hk
        have := congrArg (finRep E a x) hk
        rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
    rw [e]
    exact h.level.preimage (by fun_prop)
  one := by
    have e : lie E a (oneL E a) (act (.fin x) φ) = act (.fin x) (lie E a (oneL E a) φ) :=
      LinearMap.congr_fun (lie_rt_fin _ x) φ
    rw [e, h.one, map_smul]
  sq l := by
    rw [prod_fin]
    exact sqInt_fin ha (prod_sq h l) x

end

/- English proof (translation)
Introduce `E _ _ _ a ha r`. Use `⟨isSq_fin ha, ?_⟩` and prove the remaining obligations. Take `⟨χ, hχ⟩` from `twEx E a ha r`. Set `μ : Measure (GA E a)` to `Measure.haar`. Use `haveI : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ`.

Establish `hs` using `sqMem E a ha μ r χ hχ`. Establish `hm : ∀ φ ∈ (sqSub E a r).map (mulChi a χ).toLinearMap, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (latticeGL E a) μ φ.1`. Introduce and unpack `_ ⟨φ, hφ, rfl⟩`. Conclude with `(hs φ hφ).2`. Take `⟨p, hp⟩` from `LinearMap.exists_leftInverse_of_injective (sqSub E a r).subtype (Submodule.ker_subtype _)`.

Choose the witnesses or unpack the hypotheses as in `⟨T, hT⟩ : ∃ T : Sm E a →ₗ[ℂ] GlobalTheory.AutomorphicL2Unitary.L2 (latticeGL E a) μ, ∀ φ (hφ : φ ∈ sqSub E a r), T φ = (hs φ hφ).2.toL2 := by`. Use `⟨CuspidalL2GL.toL2ₗ μ _ hm ∘ₗ (mulChi a χ).toLinearMap.submoduleMap (sqSub E a r) ∘ₗ p, fun φ hφ => ?_⟩` and prove the remaining obligations. Establish `e : p φ = ⟨φ, hφ⟩` using `LinearMap.congr_fun hp ⟨φ, hφ⟩`. Simplify using `only [LinearMap.comp_apply, e]`. Both sides reduce to the same expression.

Use `⟨((innerₛₗ ℂ) ∘ₛₗ T).compl₂ T, ⟨fun x y => ?_, fun x _ => ?_, fun x hx h0 => ?_⟩, fun x => ?_⟩` and prove the remaining obligations. Conclude with `(inner_conj_symm (T y) (T x)).symm`. Conclude with `inner_self_nonneg (𝕜 := ℂ) (x := T x)`. Establish `h1 : T x = 0` using `inner_self_eq_zero.1 (show inner ℂ (T x) (T x) = 0 from h0)`. Rewrite `h1` using `[hT x hx]`.

Assume the negation of the conclusion as `hne`. Use `CuspidalL2GL.toL2_ne_zero (hs x hx).2 (ContAut.continuous_of_isOpen_stab E a _ (hs x hx).1) (fun e => hne ?_) h1` and prove the remaining obligations. Conclude with `(mulChi a χ).map_eq_zero_iff.1 (Subtype.ext e)`. Use `set c : ℂ := ((chiDet a χ (finGL E a x) : ℂˣ) : ℂ)⁻¹ with hc`. Establish `hst : sqSub E a r ≤ (sqSub E a r).comap (act (.fin x))` using `Submodule.span_le.2 fun ψ hψ => Submodule.subset_span (isSq_fin ha x ψ hψ)`.

Establish `key : ∀ φ ∈ sqSub E a r, T (act (.fin x) φ) = c • GlobalTheory.AutomorphicL2Unitary.R (latticeGL E a) μ (finGL E a x) (T φ)` using `fun φ hφ => by`. Rewrite using `[hT _ (hst hφ), hT φ hφ, GlobalTheory.AutomorphicL2Unitary.right_translate_toL2]`. Establish `h4` using `(hs φ hφ).2.mul_right (finGL E a x)`. Establish `h5 : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (latticeGL E a) μ (c • fun g => (mulChi a χ φ).1 (g * finGL E a x))` using `⟨fun γ hγ g => congrArg (c • ·) (h4.1 γ hγ g), h4.2.const_smul c⟩`. Use `Eq.trans ?_ (show h5.toL2 = c • h4.toL2 from MemLp.toLp_const_smul c h4.2)` and prove the remaining obligations.

Conclude with `(GlobalTheory.AutomorphicL2Unitary.MemL2Quotient.toL2_eq_iff_ae_eq _ h5).2 (.of_forall fun g => congrFun (congrArg Subtype.val (tw_rt χ (finGL E a x) φ)) g)`. Use `⟨starRingEnd ℂ c * c, fun φ hφ ψ hψ => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `inner ℂ (T (act (.fin x) φ)) (T (act (.fin x) ψ)) = _ * inner ℂ (T φ) (T ψ)`. Establish `hi : inner ℂ (GlobalTheory.AutomorphicL2Unitary.R (latticeGL E a) μ (finGL E a x) (T φ)) (GlobalTheory.AutomorphicL2Unitary.R (latticeGL E a) μ (finGL E a x) (T ψ)) = inner ℂ (T φ) (T ψ)` using `(LinearIsometry.mk (GlobalTheory.AutomorphicL2Unitary.R (latticeGL E a) μ (finGL E a x)).toLinearMap (GlobalTheory.AutomorphicL2Unitary.norm_R _)).inner_map_map _ _`. Rewrite using `[key φ hφ, key ψ hψ, inner_smul_left, inner_smul_right, hi, mul_assoc]`.
-/
theorem UpperTheory.V.Cj.H.petInv :
    UpperTheory.V.Cj.H.PetInv := by
  intro E _ _ _ a ha r
  refine ⟨isSq_fin ha, ?_⟩
  obtain ⟨χ, hχ⟩ := twEx E a ha r
  let μ : Measure (GA E a) := Measure.haar
  haveI : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  have hs := sqMem E a ha μ r χ hχ
  have hm : ∀ φ ∈ (sqSub E a r).map (mulChi a χ).toLinearMap, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (latticeGL E a) μ φ.1 := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact (hs φ hφ).2
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (sqSub E a r).subtype (Submodule.ker_subtype _)
  obtain ⟨T, hT⟩ : ∃ T : Sm E a →ₗ[ℂ] GlobalTheory.AutomorphicL2Unitary.L2 (latticeGL E a) μ, ∀ φ (hφ : φ ∈ sqSub E a r),
      T φ = (hs φ hφ).2.toL2 := by
    refine ⟨CuspidalL2GL.toL2ₗ μ _ hm ∘ₗ (mulChi a χ).toLinearMap.submoduleMap (sqSub E a r) ∘ₗ p, fun φ hφ => ?_⟩
    have e : p φ = ⟨φ, hφ⟩ := LinearMap.congr_fun hp ⟨φ, hφ⟩
    simp only [LinearMap.comp_apply, e]
    rfl
  refine ⟨((innerₛₗ ℂ) ∘ₛₗ T).compl₂ T, ⟨fun x y => ?_, fun x _ => ?_, fun x hx h0 => ?_⟩, fun x => ?_⟩
  · exact (inner_conj_symm (T y) (T x)).symm
  · exact inner_self_nonneg (𝕜 := ℂ) (x := T x)
  · have h1 : T x = 0 := inner_self_eq_zero.1 (show inner ℂ (T x) (T x) = 0 from h0)
    rw [hT x hx] at h1
    by_contra hne
    refine CuspidalL2GL.toL2_ne_zero (hs x hx).2 (ContAut.continuous_of_isOpen_stab E a _ (hs x hx).1) (fun e => hne ?_) h1
    exact (mulChi a χ).map_eq_zero_iff.1 (Subtype.ext e)
  · set c : ℂ := ((chiDet a χ (finGL E a x) : ℂˣ) : ℂ)⁻¹ with hc
    have hst : sqSub E a r ≤ (sqSub E a r).comap (act (.fin x)) :=
      Submodule.span_le.2 fun ψ hψ => Submodule.subset_span (isSq_fin ha x ψ hψ)
    have key : ∀ φ ∈ sqSub E a r,
        T (act (.fin x) φ) = c • GlobalTheory.AutomorphicL2Unitary.R (latticeGL E a) μ (finGL E a x) (T φ) := fun φ hφ => by
      rw [hT _ (hst hφ), hT φ hφ, GlobalTheory.AutomorphicL2Unitary.right_translate_toL2]
      have h4 := (hs φ hφ).2.mul_right (finGL E a x)
      have h5 : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (latticeGL E a) μ (c • fun g => (mulChi a χ φ).1 (g * finGL E a x)) :=
        ⟨fun γ hγ g => congrArg (c • ·) (h4.1 γ hγ g), h4.2.const_smul c⟩
      refine Eq.trans ?_ (show h5.toL2 = c • h4.toL2 from MemLp.toLp_const_smul c h4.2)
      exact (GlobalTheory.AutomorphicL2Unitary.MemL2Quotient.toL2_eq_iff_ae_eq _ h5).2
        (.of_forall fun g => congrFun (congrArg Subtype.val (tw_rt χ (finGL E a x) φ)) g)
    refine ⟨starRingEnd ℂ c * c, fun φ hφ ψ hψ => ?_⟩
    change inner ℂ (T (act (.fin x) φ)) (T (act (.fin x) ψ)) = _ * inner ℂ (T φ) (T ψ)
    have hi : inner ℂ (GlobalTheory.AutomorphicL2Unitary.R (latticeGL E a) μ (finGL E a x) (T φ))
        (GlobalTheory.AutomorphicL2Unitary.R (latticeGL E a) μ (finGL E a x) (T ψ)) = inner ℂ (T φ) (T ψ) :=
      (LinearIsometry.mk (GlobalTheory.AutomorphicL2Unitary.R (latticeGL E a) μ (finGL E a x)).toLinearMap
        (GlobalTheory.AutomorphicL2Unitary.norm_R _)).inner_map_map _ _
    rw [key φ hφ, key ψ hψ, inner_smul_left, inner_smul_right, hi, mul_assoc]

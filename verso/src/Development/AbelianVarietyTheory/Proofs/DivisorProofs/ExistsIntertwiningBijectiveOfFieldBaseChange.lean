import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionOfIsPushout

noncomputable section

namespace GlobalTheory.FieldBaseChange

variable {K F : Type} [Field K] [Field F] [Algebra K F]

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
theorem exists_functional_det_map_ne_zero [Infinite K] {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n F) (hM : M.det ≠ 0) : ∃ ℓ : F →ₗ[K] K, (M.map ℓ).det ≠ 0 := by
  classical
  let e := Module.Basis.ofVectorSpace K F
  let φ : F →ₗ[K] MvPolynomial (Module.Basis.ofVectorSpaceIndex K F) K := e.constr K MvPolynomial.X
  by_contra h
  push Not at h
  have hP : (M.map φ).det = 0 := by
    refine MvPolynomial.funext fun c => ?_
    have hc : ∀ x, MvPolynomial.aeval c (φ x) = e.constr K c x := fun x =>
      LinearMap.congr_fun (e.ext (f₁ := (MvPolynomial.aeval c).toLinearMap ∘ₗ φ) (f₂ := e.constr K c)
        (fun i => by simp [φ])) x
    rw [map_zero, ← h (e.constr K c), RingHom.map_det]
    congr 1
    ext i j
    exact hc _
  have hc : ∀ x, MvPolynomial.aeval e (φ x) = x := fun x =>
    LinearMap.congr_fun (e.ext (f₁ := (MvPolynomial.aeval e).toLinearMap ∘ₗ φ) (f₂ := LinearMap.id)
      (fun i => by simp [φ])) x
  apply hM
  have := congrArg (MvPolynomial.aeval (R := K) e) hP
  rw [map_zero, AlgHom.map_det] at this
  rw [← this]
  congr 1
  ext i j
  exact (hc _).symm

variable {V W V' W' : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup V'] [Module F V'] [AddCommGroup W'] [Module F W']

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Proceed by induction. Treat this case separately. Treat this case separately.

Treat this case separately. Treat this case separately. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem IsExtension.exists_basis {a : V →ₛₗ[algebraMap K F] V'} (h : IsExtension a) {ι : Type}
    (v : Module.Basis ι K V) : ∃ v' : Module.Basis ι F V', ∀ i, v' i = a (v i) := by
  have li : LinearIndependent F (fun i => a (v i)) := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    refine (Module.forall_dual_apply_eq_zero_iff K (g i)).1 fun ℓ => ?_
    obtain ⟨Λ, hΛ⟩ := h.coord ℓ
    have := congrArg Λ hg
    rw [map_sum, map_zero] at this
    simp only [hΛ _ _] at this
    exact linearIndependent_iff'.1 v.linearIndependent s (fun j => ℓ (g j)) this i hi
  have sp : ⊤ ≤ Submodule.span F (Set.range fun i => a (v i)) := by
    rw [← h.span, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ Submodule.span K (Set.range v) := v.span_eq ▸ Submodule.mem_top
    show a x ∈ Submodule.span F _
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul d y _ hy => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hy
  exact ⟨Module.Basis.mk li sp, fun i => by simp⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IsCoord.map_algebraMap_smul {a : V →ₛₗ[algebraMap K F] V'}
    (h : Submodule.span F (Set.range a) = ⊤) {ℓ : F →ₗ[K] K} {Λ : V' →+ V} (hΛ : IsCoord a ℓ Λ)
    (k : K) (x : V') : Λ (algebraMap K F k • x) = k • Λ x :=
  IsCoord.natural h hΛ hΛ (k • LinearMap.id) (algebraMap K F k • LinearMap.id)
    (fun v => by simp [map_smulₛₗ]) x

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Introduce a local definition for the expression.

Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Equip the data with the indicated structure. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_intertwining_bijective_of_extension (K F : Type) [Field K] [Field F] [Algebra K F]
    [Infinite K] (V W V' W' : Type) [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module F V'] [AddCommGroup W'] [Module F W'] [FiniteDimensional F V']
    (iV : V →ₛₗ[algebraMap K F] V') (iW : W →ₛₗ[algebraMap K F] W')
    (hV : IsExtension iV) (hW : IsExtension iW)
    (J : Type) (a : J → V →ₗ[K] V) (b : J → W →ₗ[K] W) (a' : J → V' →ₗ[F] V') (b' : J → W' →ₗ[F] W')
    (ha : ∀ i v, a' i (iV v) = iV (a i v)) (hb : ∀ i w, b' i (iW w) = iW (b i w))
    (E' : V' →ₗ[F] W') (hE' : Function.Bijective E') (hc : ∀ i v, E' (a' i v) = b' i (E' v)) :
    ∃ E : V →ₗ[K] W, Function.Bijective E ∧ ∀ i v, E (a i v) = b i (E v) := by
  classical
  let v := Module.Basis.ofVectorSpace K V
  let w₀ := Module.Basis.ofVectorSpace K W
  obtain ⟨v', hv'⟩ := hV.exists_basis v
  obtain ⟨w₀', -⟩ := hW.exists_basis w₀
  let e := LinearEquiv.ofBijective E' hE'
  let w := w₀.reindex (w₀'.indexEquiv (v'.map e))
  obtain ⟨w', hw'⟩ := hW.exists_basis w
  haveI := Module.Finite.finite_basis v'
  letI := Fintype.ofFinite (Module.Basis.ofVectorSpaceIndex K V)
  have hdet : (LinearMap.toMatrix v' w' E').det ≠ 0 := (LinearEquiv.isUnit_det e v' w').ne_zero
  obtain ⟨ℓ, hℓ⟩ := exists_functional_det_map_ne_zero (K := K) _ hdet
  obtain ⟨Λ, hΛ⟩ := hW.coord ℓ
  let E : V →ₗ[K] W :=
    { toFun := fun x => Λ (E' (iV x))
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun k x => by
        rw [map_smulₛₗ, map_smul, hΛ.map_algebraMap_smul hW.span]; rfl }
  have hM : LinearMap.toMatrix v w E = (LinearMap.toMatrix v' w' E').map ℓ := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]
    have : E (v j) = ∑ k, ℓ (w'.repr (E' (v' j)) k) • w k := by
      show Λ (E' (iV (v j))) = _
      rw [← hv']
      conv_lhs => rw [← w'.sum_repr (E' (v' j)), map_sum]
      simp only [hw', hΛ _ _]
    rw [this, w.repr_sum_self]
  refine ⟨E, ?_, fun i x => ?_⟩
  · have hu : IsUnit (LinearMap.toMatrix v w E).det := by rw [hM]; exact hℓ.isUnit
    exact (LinearEquiv.ofIsUnitDet hu).bijective
  · show Λ (E' (iV (a i x))) = b i (Λ (E' (iV x)))
    rw [← ha, hc]
    exact IsCoord.natural hW.span hΛ hΛ (b i) (b' i) (hb i) _

end GlobalTheory.FieldBaseChange

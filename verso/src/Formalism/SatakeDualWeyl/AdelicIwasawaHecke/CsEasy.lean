import Formalism.SatakeDualWeyl.DefsCS
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge

noncomputable section

open Matrix NumberField

namespace Formalism.UG.P

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ e`. Set `τ : E →+* ℂ` to `(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom`. Establish `h : ∀ x, τ (σ x) = starRingEnd ℂ (τ x)` using `fun x => by`. Simplify using `using RingHom.congr_fun (hσ τ) x`. Apply `τ.injective` to reduce the goal to its premises.

Rewrite using `[h, h, Complex.conj_conj]`.
-/
theorem sigma_involution_holds : Formalism.UG.CS.SigmaInvol := by
  intro F E _ _ _ _ _ σ hσ e
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  have h : ∀ x, τ (σ x) = starRingEnd ℂ (τ x) := fun x => by
    simpa using RingHom.congr_fun (hσ τ) x
  apply τ.injective
  rw [h, h, Complex.conj_conj]

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce `h choose y hy using h`. Conclude with `⟨y, funext fun i => by simpa using hy i⟩`.

Introduce and unpack `⟨y, rfl⟩ i`. Conclude with `⟨y i, by simp⟩`.
-/
theorem csEasy_stdLat_eq_range (E : Type) [Field E] [NumberField E] (n : Type) [Fintype n]
    [DecidableEq n] :
    Formalism.UG.stdLat (n := n) (A := E) (𝓞 E) =
      LinearMap.range (LinearMap.pi (fun i : n =>
        (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj i))) := by
  ext x
  simp only [Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range]
  constructor
  · intro h
    choose y hy using h
    exact ⟨y, funext fun i => by simpa using hy i⟩
  · rintro ⟨y, rfl⟩ i
    exact ⟨y i, by simp⟩

/- English proof (translation)
Introduce `E _ _ n _ _`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[csEasy_stdLat_eq_range] infer_instance`. Rewrite using `[eq_top_iff, ← (Pi.basisFun E n).span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Apply `Submodule.subset_span` to reduce the goal to its premises. Use `show Pi.basisFun E n i ∈ Formalism.UG.stdLat (n := n) (A := E) (𝓞 E)`. Simplify using `only [Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range, Pi.basisFun_apply]`. Introduce `j`. Rewrite using `[Pi.single_apply]`.

Use `split_ifs`. Conclude with `⟨1, by simp⟩`. Conclude with `⟨0, by simp⟩`.
-/
theorem standard_lattice_full_holds : Formalism.UG.CS.StdLatFull := by
  intro E _ _ n _ _
  refine ⟨?_, ?_⟩
  · rw [csEasy_stdLat_eq_range]
    infer_instance
  · rw [eq_top_iff, ← (Pi.basisFun E n).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    show Pi.basisFun E n i ∈ Formalism.UG.stdLat (n := n) (A := E) (𝓞 E)
    simp only [Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range,
      Pi.basisFun_apply]
    intro j
    rw [Pi.single_apply]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩

/- English proof (translation)
Unfold `Formalism.UG.CS.formJ Formalism.UG.hform`. Rewrite using `[Matrix.toLinearMapₛₗ₂'_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Use `show σ (x i) * (y j * (c * J i j)) = c * (σ (x i) * J i j * y j)`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem csEasy_formJ_apply {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ e, σ (σ e) = e)
    {n : Type} [Fintype n] [DecidableEq n] (J : Matrix n n E) (c : E) (x y : n → E) :
    Formalism.UG.CS.formJ σ hσ J c x y = c * Formalism.UG.hform σ J x y := by
  unfold Formalism.UG.CS.formJ Formalism.UG.hform
  rw [Matrix.toLinearMapₛₗ₂'_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show σ (x i) * (y j * (c * J i j)) = c * (σ (x i) * J i j * y j)
  ring

/- English proof (translation)
Introduce `E _ σ hσ n _ _ J c hc hJ`. Establish `hJ' : ∀ i j, σ (J i j) = J j i` using `fun i j => by`. Use `congrFun (congrFun hJ j) i` as an intermediate fact. Simplify `this` using `[Formalism.UG.cT]`. Use `⟨?_, fun x y => csEasy_formJ_apply σ hσ J c x y⟩` and prove the remaining obligations.

Prove the components needed by the constructor for the conclusion. Introduce `x y`. Rewrite using `[csEasy_formJ_apply, csEasy_formJ_apply]`. Use `show σ (c * Formalism.UG.hform σ J x y) = c * Formalism.UG.hform σ J y x`. Rewrite using `[map_mul, hc]`.

Use `congr 1`. Unfold `Formalism.UG.hform`. Simplify using `only [map_sum, map_mul, hσ, hJ']`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermitian_form_symmetry_holds : Formalism.UG.CS.FormSymm := by
  intro E _ σ hσ n _ _ J c hc hJ
  have hJ' : ∀ i j, σ (J i j) = J j i := fun i j => by
    have := congrFun (congrFun hJ j) i
    simpa [Formalism.UG.cT] using this
  refine ⟨?_, fun x y => csEasy_formJ_apply σ hσ J c x y⟩
  constructor
  intro x y
  rw [csEasy_formJ_apply, csEasy_formJ_apply]
  show σ (c * Formalism.UG.hform σ J x y) = c * Formalism.UG.hform σ J y x
  rw [map_mul, hc]
  congr 1
  unfold Formalism.UG.hform
  simp only [map_sum, map_mul, hσ, hJ']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Establish `e : ∀ (A : Matrix n n E) (u v : n → E), Formalism.UG.hform σ A u v = (fun i => σ (u i)) ⬝ᵥ (A *ᵥ v)`. Introduce `A u v`. Simplify using `only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]`. Establish `hs : (fun i => σ ((M *ᵥ x) i)) = (M.map σ) *ᵥ (fun i => σ (x i))`. Use function extensionality and compare the values at `i`.

Simplify using `[mulVec, dotProduct, map_sum]`. Rewrite using `[e, e, hs, ← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Formalism.UG.cT]`. Simplify using `only [Matrix.mul_assoc]`.
-/
private lemma hform_mulVec_mulVec_of_cT_mul_mul_eq {E : Type} [Field E] (σ : E →+* E) {n : Type} [Fintype n]
    [DecidableEq n] (J M : Matrix n n E) (x y : n → E) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M) x y := by
  have e : ∀ (A : Matrix n n E) (u v : n → E),
      Formalism.UG.hform σ A u v = (fun i => σ (u i)) ⬝ᵥ (A *ᵥ v) := by
    intro A u v
    simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have hs : (fun i => σ ((M *ᵥ x) i)) = (M.map σ) *ᵥ (fun i => σ (x i)) := by
    funext i
    simp [mulVec, dotProduct, map_sum]
  rw [e, e, hs, ← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Formalism.UG.cT]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Simplify using `[Formalism.UG.hform, Pi.single_apply]`.
-/
private lemma hform_single_single_stabilizer_orbit_volume {E : Type} [Field E] (σ : E →+* E) {n : Type} [Fintype n]
    [DecidableEq n] (A : Matrix n n E) (i j : n) :
    Formalism.UG.hform σ A (Pi.single i 1) (Pi.single j 1) = A i j := by
  simp [Formalism.UG.hform, Pi.single_apply]

/- English proof (translation)
Introduce `E _ σ hσ n _ _ J c hc hcσ g`. Establish `hg : ∀ x, Formalism.UG.glEquiv g x = (g : Matrix n n E) *ᵥ x` using `fun x => rfl`. Use `show Formalism.UG.cT σ (g : Matrix n n E) * J * (g : Matrix n n E) = J ↔ _`. Use `show _ ↔ ∀ x y, _ = _`. Simplify using `only [hg, csEasy_formJ_apply, hform_mulVec_mulVec_of_cT_mul_mul_eq, mul_right_inj' hc]`.

Prove the components needed by the constructor for the conclusion. Introduce `h x y`. Rewrite using `[h]`. Introduce `h`. Use extensionality with `i j`.

Use `h (Pi.single i 1) (Pi.single j 1)` as an intermediate fact. Rewrite `this` using `[hform_single_single_stabilizer_orbit_volume, hform_single_single_stabilizer_orbit_volume]`. Then use the resulting hypothesis.
-/
theorem unitary_isometry_lattice_holds : Formalism.UG.CS.IsomUJ := by
  intro E _ σ hσ n _ _ J c hc hcσ g
  have hg : ∀ x, Formalism.UG.glEquiv g x = (g : Matrix n n E) *ᵥ x := fun x => rfl
  show Formalism.UG.cT σ (g : Matrix n n E) * J * (g : Matrix n n E) = J ↔ _
  show _ ↔ ∀ x y, _ = _
  simp only [hg, csEasy_formJ_apply, hform_mulVec_mulVec_of_cT_mul_mul_eq, mul_right_inj' hc]
  constructor
  · intro h x y
    rw [h]
  · intro h
    ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    rwa [hform_single_single_stabilizer_orbit_volume, hform_single_single_stabilizer_orbit_volume] at this

end Formalism.UG.P

import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish

noncomputable section

open Matrix Module PositivityTheory.Rg.BcB

namespace GlobalTheory.CompanionTheory.IwaDecomp

section Isometry

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]

def isoOfFinrank (h : finrank ℂ F = finrank ℂ G) : F ≃ₗᵢ[ℂ] G :=
  (stdOrthonormalBasis ℂ F).equiv (stdOrthonormalBasis ℂ G) (finCongr h)

/- English proof (translation)
Set `e` to `isoOfFinrank h`. Set `L : S →ₗᵢ[ℂ] F` to `e.symm.toLinearIsometry.comp φ`. Use `⟨e.toLinearIsometry.comp L.extend, fun s => ?_⟩` and prove the remaining obligations. Simplify using `[L, LinearIsometry.extend_apply]`.
-/
theorem exists_extend (h : finrank ℂ F = finrank ℂ G) (S : Submodule ℂ F) (φ : S →ₗᵢ[ℂ] G) :
    ∃ ψ : F →ₗᵢ[ℂ] G, ∀ s : S, ψ s = φ s := by
  let e := isoOfFinrank h
  let L : S →ₗᵢ[ℂ] F := e.symm.toLinearIsometry.comp φ
  refine ⟨e.toLinearIsometry.comp L.extend, fun s => ?_⟩
  simp [L, LinearIsometry.extend_apply]

/- English proof (translation)
The claim follows from `(LinearEquiv.finrank_eq (Submodule.equivMapOfInjective K.toLinearMap K.injective A)).symm`.
-/
theorem finrank_map_isometry (K : E →ₗᵢ[ℂ] E) (A : Submodule ℂ E) :
    finrank ℂ (A.map K.toLinearMap) = finrank ℂ A :=
  (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective K.toLinearMap K.injective A)).symm

/- English proof (translation)
Set `φ : A₁ ≃ₗᵢ[ℂ] B₁` to `isoOfFinrank h₁`. Set `S : Submodule ℂ A₂` to `A₁.comap A₂.subtype`. Set `ι : S →ₗᵢ[ℂ] A₁` to `⟨LinearMap.codRestrict A₁ (A₂.subtype ∘ₗ S.subtype) (fun x => x.2), fun x => rfl⟩`. Set `j : B₁ →ₗᵢ[ℂ] B₂` to `⟨Submodule.inclusion hB, fun x => rfl⟩`. Take `⟨ψ, hψ⟩` from `exists_extend h₂ S (j.comp (φ.toLinearIsometry.comp ι))`.

Set `L : A₂ →ₗᵢ[ℂ] E` to `B₂.subtypeₗᵢ.comp ψ`. Establish `hK : ∀ a : A₂, L.extend a = ψ a` using `fun a => by`. Simplify `LinearIsometry.extend_apply L a` using `[L]`. Use `⟨L.extend, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `refine Submodule.eq_of_le_of_finrank_eq ?_ ((finrank_map_isometry _ _).trans h₁)`.

Introduce and unpack `_ ⟨a, ha, rfl⟩`. Establish `h` using `hK ⟨a, hA ha⟩`. Establish `h2` using `hψ ⟨⟨a, hA ha⟩, ha⟩`. Express the relevant statement in the definitionally equal form `L.extend a ∈ B₁`. Rewrite using `[show L.extend a = ((ψ ⟨a, hA ha⟩ : B₂) : E) from h, show ψ ⟨a, hA ha⟩ = _ from h2]`.

Conclude with `(φ (ι ⟨⟨a, hA ha⟩, ha⟩)).2`. Apply the tactic sequence `refine Submodule.eq_of_le_of_finrank_eq ?_ ((finrank_map_isometry _ _).trans h₂)`. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Express the relevant statement in the definitionally equal form `L.extend a ∈ B₂`. Rewrite using `[show L.extend a = ((ψ ⟨a, ha⟩ : B₂) : E) from hK ⟨a, ha⟩]`.

Conclude with `(ψ ⟨a, ha⟩).2`.
-/
theorem exists_isometry_flag {A₁ A₂ B₁ B₂ : Submodule ℂ E} (hA : A₁ ≤ A₂) (hB : B₁ ≤ B₂)
    (h₁ : finrank ℂ A₁ = finrank ℂ B₁) (h₂ : finrank ℂ A₂ = finrank ℂ B₂) :
    ∃ K : E →ₗᵢ[ℂ] E, A₁.map K.toLinearMap = B₁ ∧ A₂.map K.toLinearMap = B₂ := by
  let φ : A₁ ≃ₗᵢ[ℂ] B₁ := isoOfFinrank h₁
  let S : Submodule ℂ A₂ := A₁.comap A₂.subtype
  let ι : S →ₗᵢ[ℂ] A₁ :=
    ⟨LinearMap.codRestrict A₁ (A₂.subtype ∘ₗ S.subtype) (fun x => x.2), fun x => rfl⟩
  let j : B₁ →ₗᵢ[ℂ] B₂ := ⟨Submodule.inclusion hB, fun x => rfl⟩
  obtain ⟨ψ, hψ⟩ := exists_extend h₂ S (j.comp (φ.toLinearIsometry.comp ι))
  let L : A₂ →ₗᵢ[ℂ] E := B₂.subtypeₗᵢ.comp ψ
  have hK : ∀ a : A₂, L.extend a = ψ a := fun a => by
    simpa [L] using LinearIsometry.extend_apply L a
  refine ⟨L.extend, ?_, ?_⟩
  · refine Submodule.eq_of_le_of_finrank_eq ?_ ((finrank_map_isometry _ _).trans h₁)
    rintro _ ⟨a, ha, rfl⟩
    have h := hK ⟨a, hA ha⟩
    have h2 := hψ ⟨⟨a, hA ha⟩, ha⟩
    change L.extend a ∈ B₁
    rw [show L.extend a = ((ψ ⟨a, hA ha⟩ : B₂) : E) from h, show ψ ⟨a, hA ha⟩ = _ from h2]
    exact (φ (ι ⟨⟨a, hA ha⟩, ha⟩)).2
  · refine Submodule.eq_of_le_of_finrank_eq ?_ ((finrank_map_isometry _ _).trans h₂)
    rintro _ ⟨a, ha, rfl⟩
    change L.extend a ∈ B₂
    rw [show L.extend a = ((ψ ⟨a, ha⟩ : B₂) : E) from hK ⟨a, ha⟩]
    exact (ψ ⟨a, ha⟩).2

/- English proof (translation)
Establish `hT : ∀ W : Submodule ℂ V, finrank ℂ (W.map (e : V →ₗ[ℂ] E)) = finrank ℂ W` using `fun W => LinearEquiv.finrank_map_eq e W`. Conclude with `exists_isometry_flag (Submodule.map_mono hA) (Submodule.map_mono hB) (by rw [hT, hT, h₁]) (by rw [hT, hT, h₂])`.
-/
theorem exists_isometry_flag_of_equiv {V : Type*} [AddCommGroup V] [Module ℂ V] (e : V ≃ₗ[ℂ] E)
    {A₁ A₂ B₁ B₂ : Submodule ℂ V} (hA : A₁ ≤ A₂) (hB : B₁ ≤ B₂)
    (h₁ : finrank ℂ A₁ = finrank ℂ B₁) (h₂ : finrank ℂ A₂ = finrank ℂ B₂) :
    ∃ K : E →ₗᵢ[ℂ] E, (A₁.map (e : V →ₗ[ℂ] E)).map K.toLinearMap = B₁.map (e : V →ₗ[ℂ] E) ∧
      (A₂.map (e : V →ₗ[ℂ] E)).map K.toLinearMap = B₂.map (e : V →ₗ[ℂ] E) := by
  have hT : ∀ W : Submodule ℂ V, finrank ℂ (W.map (e : V →ₗ[ℂ] E)) = finrank ℂ W :=
    fun W => LinearEquiv.finrank_map_eq e W
  exact exists_isometry_flag (Submodule.map_mono hA) (Submodule.map_mono hB)
    (by rw [hT, hT, h₁]) (by rw [hT, hT, h₂])

end Isometry

variable {n : ℕ}

/- English proof (translation)
Simplify using `[img]`.
-/
theorem img_one (W : Submodule ℂ (Fin n → ℂ)) : img (1 : GL (Fin n) ℂ) W = W := by
  simp [img]

/- English proof (translation)
Simplify using `only [img, Units.val_mul, Matrix.toLin'_mul, Submodule.map_comp]`.
-/
theorem img_mul (a b : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) : img (a * b) W = img a (img b W) := by
  simp only [img, Units.val_mul, Matrix.toLin'_mul, Submodule.map_comp]

/- English proof (translation)
The claim follows from `Submodule.map_mono h`.
-/
theorem img_mono (a : GL (Fin n) ℂ) {W W' : Submodule ℂ (Fin n → ℂ)} (h : W ≤ W') : img a W ≤ img a W' :=
  Submodule.map_mono h

def linEquiv (g : GL (Fin n) ℂ) : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
  Matrix.toLin'OfInv (M := (g⁻¹ : GL (Fin n) ℂ).val) (M' := g.val) (by simp) (by simp)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem img_eq_map_linEquiv (g : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) :
    img g W = W.map (linEquiv g : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) := by
  rfl

/- English proof (translation)
Rewrite using `[img_eq_map_linEquiv]`. Conclude with `LinearEquiv.finrank_map_eq (linEquiv g) W`.
-/
theorem finrank_img (g : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) : finrank ℂ (img g W) = finrank ℂ W := by
  rw [img_eq_map_linEquiv]
  exact LinearEquiv.finrank_map_eq (linEquiv g) W

/- English proof (translation)
Establish `h : (thetaR (starRingEnd ℂ) n k).val = (k⁻¹ : GL (Fin n) ℂ).val.conjTranspose`. Rewrite using `[thetaR_val]`. Use extensionality with `i j`. Simplify using `[Matrix.conjTranspose_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce `e`. Establish `h'` using `congrArg Units.val e`. Rewrite `h'` using `[h]`. Rewrite using `[← h', Matrix.conjTranspose_conjTranspose]`. Introduce `e`.

Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[h, ← e, Matrix.conjTranspose_conjTranspose]`.
-/
theorem thetaR_eq_self_iff (k : GL (Fin n) ℂ) :
    thetaR (starRingEnd ℂ) n k = k ↔ k.val.conjTranspose = (k⁻¹ : GL (Fin n) ℂ).val := by
  have h : (thetaR (starRingEnd ℂ) n k).val = (k⁻¹ : GL (Fin n) ℂ).val.conjTranspose := by
    rw [thetaR_val]; ext i j; simp [Matrix.conjTranspose_apply]
  constructor
  · intro e
    have h' := congrArg Units.val e
    rw [h] at h'
    rw [← h', Matrix.conjTranspose_conjTranspose]
  · intro e
    refine Units.ext ?_
    rw [h, ← e, Matrix.conjTranspose_conjTranspose]

abbrev eu (n : ℕ) : (Fin n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) := (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm

/- English proof (translation)
Set `f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)` to `((eu n).symm : _ →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ K.toLinearMap ∘ₗ (eu n : (Fin n → ℂ) →ₗ[ℂ] _)`. Set `M : Matrix (Fin n) (Fin n) ℂ` to `LinearMap.toMatrix' f`. Establish `hM : Matrix.toLin' M = f` using `Matrix.toLin'_toMatrix' f`. Establish `key : ∀ x y : Fin n → ℂ, f y ⬝ᵥ star (f x) = y ⬝ᵥ star x` using `fun x y => by`. Use `K.inner_map_map (eu n x) (eu n y)` as an intermediate fact.

Rewrite `this` using `[EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]`. Conclude with `this`. Establish `hc : ∀ i l, M l i = f (Pi.single i 1) l` using `fun i l => by`. Rewrite using `[← hM, Matrix.toLin'_apply, Matrix.mulVec_single_one]`. Both sides reduce to the same expression.

Establish `h1 : M.conjTranspose * M = 1`. Use extensionality with `i j`. Establish `h` using `key (Pi.single i 1) (Pi.single j 1)`. Establish `e : (Pi.single j 1 : Fin n → ℂ) ⬝ᵥ star (Pi.single i 1 : Fin n → ℂ) = (1 : Matrix (Fin n) (Fin n) ℂ) i j`. Rewrite using `[single_one_dotProduct]`.

Simplify using `[Pi.single_apply, Matrix.one_apply, eq_comm]`. Rewrite using `[← e, ← h]`. Simplify using `only [dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, hc, Pi.star_apply, mul_comm]`. Establish `h2 : M * M.conjTranspose = 1` using `mul_eq_one_comm.1 h1`. Set `k : GL (Fin n) ℂ` to `⟨M, M.conjTranspose, h2, h1⟩`.

Use `⟨k, (thetaR_eq_self_iff k).2 rfl, fun W => ?_⟩` and prove the remaining obligations. Establish `: (k.val : Matrix (Fin n) (Fin n) ℂ) = M` using `rfl`. Express the relevant statement in the definitionally equal form `Submodule.map _ (Submodule.map (Matrix.toLin' M) W) = _`. Rewrite using `[hM, ← Submodule.map_comp, ← Submodule.map_comp]`. Use `congrArg (fun t => Submodule.map t W) (LinearMap.ext fun x => ?_)` and prove the remaining obligations.

Simplify using `[f]`.
-/
theorem unitary_of_isometry (K : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    ∃ k : GL (Fin n) ℂ, thetaR (starRingEnd ℂ) n k = k ∧
      ∀ W : Submodule ℂ (Fin n → ℂ), (img k W).map (eu n : (Fin n → ℂ) →ₗ[ℂ] _) =
        (W.map (eu n : (Fin n → ℂ) →ₗ[ℂ] _)).map K.toLinearMap := by
  let f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    ((eu n).symm : _ →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ K.toLinearMap ∘ₗ (eu n : (Fin n → ℂ) →ₗ[ℂ] _)
  let M : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' f
  have hM : Matrix.toLin' M = f := Matrix.toLin'_toMatrix' f
  have key : ∀ x y : Fin n → ℂ, f y ⬝ᵥ star (f x) = y ⬝ᵥ star x := fun x y => by
    have := K.inner_map_map (eu n x) (eu n y)
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct] at this
    exact this
  have hc : ∀ i l, M l i = f (Pi.single i 1) l := fun i l => by
    rw [← hM, Matrix.toLin'_apply, Matrix.mulVec_single_one]
    rfl
  have h1 : M.conjTranspose * M = 1 := by
    ext i j
    have h := key (Pi.single i 1) (Pi.single j 1)
    have e : (Pi.single j 1 : Fin n → ℂ) ⬝ᵥ star (Pi.single i 1 : Fin n → ℂ) = (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
      rw [single_one_dotProduct]
      simp [Pi.single_apply, Matrix.one_apply, eq_comm]
    rw [← e, ← h]
    simp only [dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, hc, Pi.star_apply, mul_comm]
  have h2 : M * M.conjTranspose = 1 := mul_eq_one_comm.1 h1
  let k : GL (Fin n) ℂ := ⟨M, M.conjTranspose, h2, h1⟩
  refine ⟨k, (thetaR_eq_self_iff k).2 rfl, fun W => ?_⟩
  have : (k.val : Matrix (Fin n) (Fin n) ℂ) = M := rfl
  change Submodule.map _ (Submodule.map (Matrix.toLin' M) W) = _
  rw [hM, ← Submodule.map_comp, ← Submodule.map_comp]
  refine congrArg (fun t => Submodule.map t W) (LinearMap.ext fun x => ?_)
  simp [f]

/- English proof (translation)
Use `conv_lhs => rw [← h]`. Rewrite using `[← img_mul, ← img_mul, show g * k⁻¹ * k * g⁻¹ = 1 by group, img_one]`.
-/
theorem img_mul_inv_eq {g k : GL (Fin n) ℂ} {W : Submodule ℂ (Fin n → ℂ)} (h : img k (img g⁻¹ W) = W) :
    img (g * k⁻¹) W = W := by
  conv_lhs => rw [← h]
  rw [← img_mul, ← img_mul, show g * k⁻¹ * k * g⁻¹ = 1 by group, img_one]

/- English proof (translation)
Take `⟨K, hK₁, hK₂⟩` from `exists_isometry_flag_of_equiv (eu n) (img_mono g⁻¹ h) h (finrank_img g⁻¹ W₁) (finrank_img g⁻¹ W₂)`. Apply the tactic sequence `obtain ⟨k, hk, hkK⟩ := unitary_of_isometry K`. Establish `hinj : Function.Injective (eu n : (Fin n → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))` using `(eu n).injective`. Establish `inj` using `Submodule.map_injective_of_injective hinj`. Conclude with `⟨k, hk, inj ((hkK _).trans hK₁), inj ((hkK _).trans hK₂)⟩`.
-/
theorem exists_flag_unitary (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (h : W₁ ≤ W₂) (g : GL (Fin n) ℂ) :
    ∃ k : GL (Fin n) ℂ, thetaR (starRingEnd ℂ) n k = k ∧ img k (img g⁻¹ W₁) = W₁ ∧ img k (img g⁻¹ W₂) = W₂ := by
  obtain ⟨K, hK₁, hK₂⟩ := exists_isometry_flag_of_equiv (eu n) (img_mono g⁻¹ h) h
    (finrank_img g⁻¹ W₁) (finrank_img g⁻¹ W₂)
  obtain ⟨k, hk, hkK⟩ := unitary_of_isometry K
  have hinj : Function.Injective (eu n : (Fin n → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := (eu n).injective
  have inj := Submodule.map_injective_of_injective hinj
  exact ⟨k, hk, inj ((hkK _).trans hK₁), inj ((hkK _).trans hK₂)⟩

/- English proof (translation)
Take `⟨k, hk, h₁, h₂⟩` from `exists_flag_unitary W₁ W₂ h g`. Conclude with `⟨g * k⁻¹, k, by group, hk, img_mul_inv_eq h₁, img_mul_inv_eq h₂⟩`.
-/
theorem exists_eq_mul_unitary (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (h : W₁ ≤ W₂) (g : GL (Fin n) ℂ) :
    ∃ q k : GL (Fin n) ℂ, g = q * k ∧ thetaR (starRingEnd ℂ) n k = k ∧ img q W₁ = W₁ ∧ img q W₂ = W₂ := by
  obtain ⟨k, hk, h₁, h₂⟩ := exists_flag_unitary W₁ W₂ h g
  exact ⟨g * k⁻¹, k, by group, hk, img_mul_inv_eq h₁, img_mul_inv_eq h₂⟩

/- English proof (translation)
Introduce `_ W₁ W₂ h g` and use `by obtain ⟨q, k, e, hk, h₁, h₂⟩ := exists_eq_mul_unitary W₁ W₂ h g exact ⟨q, ⟨h₁, h₂⟩, k, hk, e⟩`.
-/
theorem iwaFlag : PositivityTheory.Rg.BcB.D4.IwaFlag := fun _ W₁ W₂ h g => by
  obtain ⟨q, k, e, hk, h₁, h₂⟩ := exists_eq_mul_unitary W₁ W₂ h g
  exact ⟨q, ⟨h₁, h₂⟩, k, hk, e⟩

end GlobalTheory.CompanionTheory.IwaDecomp

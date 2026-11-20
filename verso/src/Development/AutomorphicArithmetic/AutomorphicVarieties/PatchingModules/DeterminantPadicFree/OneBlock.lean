import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.LatInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SelfdualRamified
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.OrthonormalLocal
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.AdicCompletion.Completeness

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Establish `hR : HenselianRing (PowerSeries K) (Ideal.span {PowerSeries.X})` using `inferInstance`. Use `{ toIsLocalRing := inferInstance, is_henselian := fun f hf a₀ h₁ h₂ => ?_ }` and prove the remaining obligations. Rewrite `h₁`, the goal using `[PowerSeries.maximalIdeal_eq_span_X]`. Conclude with `hR.is_henselian f hf a₀ h₁ (h₂.map _)`.
-/
private theorem henselian_powerSeries (K : Type) [Field K] : HenselianLocalRing (PowerSeries K) := by
  have hR : HenselianRing (PowerSeries K) (Ideal.span {PowerSeries.X}) := inferInstance
  refine { toIsLocalRing := inferInstance, is_henselian := fun f hf a₀ h₁ h₂ => ?_ }
  rw [PowerSeries.maximalIdeal_eq_span_X] at h₁ ⊢
  exact hR.is_henselian f hf a₀ h₁ (h₂.map _)

/- English proof (translation)
Use extensionality with `i j`. Conclude with `GeneralLinearGroup.map_apply f i j g`.
-/
private theorem coe_generalLinearGroup_map_eq_map {R S : Type} [CommRing R] [CommRing S] {m : ℕ} (f : R →+* S)
    (g : GL (Fin m) R) :
    ((GeneralLinearGroup.map f g : GL (Fin m) S) : Matrix (Fin m) (Fin m) S) =
      (g : Matrix (Fin m) (Fin m) R).map f := by
  ext i j
  exact GeneralLinearGroup.map_apply f i j g

/- English proof (translation)
Simplify using `[Matrix.map_mul, Matrix.transpose_map]`.
-/
private theorem map_transpose_mul_mul_eq {R S : Type} [CommRing R] [CommRing S] {m : ℕ} (φ : R →+* S)
    (X Y Z : Matrix (Fin m) (Fin m) R) :
    (Xᵀ * Y * Z).map φ = (X.map φ)ᵀ * Y.map φ * Z.map φ := by
  simp [Matrix.map_mul, Matrix.transpose_map]

/- English proof (translation)
Introduce `K K' G _ _ _ m j₁ f₁ j₂ f₂ r H σ u d h2 hf₁ hf₂ hj₁ hsq hd hdr hHs hdet hσ hsim`. Take `⟨Q₀, r₀, hQ₀⟩` from `Det.latInt r d hd hdr`. Establish `hQ₀m : ∀ g, (r g).1 * Q₀.1 = Q₀.1 * (r₀ g).1.map (algebraMap _ _)`. Introduce `g`. Use `congr_arg Units.val (hQ₀ g)` as an intermediate fact.

Simplify `this` using `only [Units.val_mul, pushRep, MonoidHom.comp_apply, coe_generalLinearGroup_map_eq_map]`. Take `⟨H₁, hH₁⟩ : ∃ H₁ : Matrix (Fin m) (Fin m) (FractionRing (PowerSeries K)), H₁ = Q₀.1ᵀ * H * Q₀` from `⟨_, rfl⟩`. Establish `hH₁s : H₁ᵀ = H₁`. Rewrite using `[hH₁, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hHs, Matrix.mul_assoc]`. Establish `hQdet : Q₀.1.det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det _).1 Q₀.isUnit).ne_zero`.

Establish `hH₁det : H₁.det ≠ 0`. Rewrite using `[hH₁, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]`. Conclude with `mul_ne_zero (mul_ne_zero hQdet hdet) hQdet`. Establish `hsim₀ : ∀ g, ((r₀ g).1.map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))ᵀ * H₁ * (r₀ (σ g)).1.map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) = algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (u g) • H₁`. Introduce `g`.

Establish `key` using `hsim g`. Simplify using `only [mat, MonoidHom.comp_apply, Units.coeHom_apply] at key`. Rewrite using `[hH₁]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.transpose_mul, Matrix.mul_assoc]`.

Use `_ = ((r g).1 * Q₀.1)ᵀ * H * ((r (σ g)).1 * Q₀.1) := by`. Rewrite using `[← hQ₀m, ← hQ₀m]`. Use `_ = Q₀.1ᵀ * ((r g).1ᵀ * H * (r (σ g)).1) * Q₀.1 := by`. Simplify using `only [Matrix.transpose_mul, Matrix.mul_assoc]`. Use `_ = _ := by rw [key, Matrix.mul_smul, Matrix.smul_mul]`.

Take `⟨P, H', r', hP, hr'⟩` from `UpperTheory.V.AlgebraTools.selfdual_ramified (A := PowerSeries K) (F := FractionRing (PowerSeries K)) H₁ r₀ σ u (A' := PowerSeries K) (F' := FractionRing (PowerSeries K)) j₁ f₁ PowerSeries.X PowerSeries.X PowerSeries.X_irreducible hj₁.symm hf₁ (IsFractionRing.injective _ _) hH₁s …`. Establish `h2u : IsUnit (2 : PowerSeries K)`. Rewrite using `[← map_ofNat (PowerSeries.C (R := K)) 2]`. Conclude with `(isUnit_iff_ne_zero.2 h2).map _`. Establish `hH's : H'.1ᵀ = H'`.

Establish `e : (H'.1.map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))ᵀ = H'.1.map (algebraMap _ _)`. Rewrite using `[← hP, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.transpose_map, hH₁s, Matrix.mul_assoc]`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Conclude with `IsFractionRing.injective _ (FractionRing (PowerSeries K)) (congr_fun (congr_fun e i) j)`. Establish `hH'det : IsUnit H'.1.det` using `(Matrix.isUnit_iff_isUnit_det _).1 H'.isUnit`.

Use `haveI := henselian_powerSeries K'`. Take `⟨P₂, hP₂⟩` from `UpperTheory.V.AlgebraTools.orthonormal_local j₂ H'.1 h2u hH's hH'det hsq`. Use `⟨GeneralLinearGroup.map (f₂.comp f₁) Q₀ * GeneralLinearGroup.map f₂ P * GeneralLinearGroup.map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) P₂, (MulAut.conj P₂⁻¹).toMonoidHom.comp (pushRep j₂ r'), ?_, ?_⟩` and prove the remaining obligations. Establish `s1 : (Q₀.1.map (f₂.comp f₁))ᵀ * H.map (f₂.comp f₁) * Q₀.1.map (f₂.comp f₁) = (H₁.map f₁).map f₂`. Rewrite using `[← map_transpose_mul_mul_eq, ← hH₁, Matrix.map_map]`.

Both sides reduce to the same expression. Establish `s2 : (P.1.map f₂)ᵀ * (H₁.map f₁).map f₂ * P.1.map f₂ = (H'.1.map j₂).map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K')))`. Rewrite using `[← map_transpose_mul_mul_eq, hP, Matrix.map_map, Matrix.map_map]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Conclude with `hf₂ a`. Establish `s3 : (P₂.1.map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))))ᵀ * (H'.1.map j₂).map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) * P₂.1.map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) = 1`. Rewrite using `[← map_transpose_mul_mul_eq, hP₂, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[Units.val_mul, Units.val_mul, coe_generalLinearGroup_map_eq_map, coe_generalLinearGroup_map_eq_map, coe_generalLinearGroup_map_eq_map]`. Rewrite using `[← s3, ← s2, ← s1]`.

Simplify using `only [Matrix.transpose_mul, Matrix.mul_assoc]`. Introduce `g`. Establish `t1` using `congr_arg (GeneralLinearGroup.map (f₂.comp f₁)) (hQ₀ g)`. Rewrite `t1` using `[map_mul, map_mul]`. Establish `t2 : GeneralLinearGroup.map (f₂.comp f₁) (GeneralLinearGroup.map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) (r₀ g)) * GeneralLinearGroup.map f₂ P = GeneralLinearGroup.map f₂ P * GeneralLinearGroup.map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) …`.

Apply `Units.ext` to reduce the goal to its premises. Establish `t2m` using `congr_arg (fun M => Matrix.map M f₂) (hr' g)`. Simplify using `only [Matrix.map_mul, Matrix.map_map] at t2m`. Simplify using `only [Units.val_mul, pushRep, MonoidHom.comp_apply, coe_generalLinearGroup_map_eq_map, Matrix.map_map]`. Establish `fe1 : (⇑(f₂.comp f₁) ∘ ⇑(algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))) = (⇑f₂ ∘ fun a => algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (j₁ a))`.

Use function extensionality and compare the values at `fun a => by simp [hf₁]`. Establish `fe2 : (⇑(algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) ∘ ⇑j₂) = (⇑f₂ ∘ ⇑(algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))`. Use function extensionality and compare the values at `fun a => by simp [hf₂]`. Rewrite using `[fe1, fe2]`. Conclude with `t2m`.

Simplify using `only [pushRep, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_inv_apply, map_mul, map_inv, inv_inv] at t1 ⊢`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = _ := by`. Rewrite using `[t1, mul_assoc (GeneralLinearGroup.map (f₂.comp f₁) Q₀), t2]`.

Use `group`.
-/
theorem UpperTheory.V.Pa.Det.oneBlock :
    ∀ {K K' G : Type} [Field K] [Field K'] [Group G] {m : ℕ} (j₁ : PowerSeries K →+* PowerSeries K) (f₁ : FractionRing (PowerSeries K) →+* FractionRing (PowerSeries K)) (j₂ : PowerSeries K →+* PowerSeries K') (f₂ : FractionRing (PowerSeries K) →+* FractionRing (PowerSeries K')) (r : G →* GL (Fin m) (FractionRing (PowerSeries K))) (H : Matrix (Fin m) (Fin m) (FractionRing (PowerSeries K))) (σ : G → G) (u : G → PowerSeries K) (d : PowerSeries K), (2 : K) ≠ 0 → (∀ y, f₁ (algebraMap _ _ y) = algebraMap _ _ (j₁ y)) → (∀ y, f₂ (algebraMap _ _ y) = algebraMap _ _ (j₂ y)) → j₁ PowerSeries.X = PowerSeries.X ^ 2 → (∀ c : (PowerSeries K)ˣ, IsSquare (residue (PowerSeries K') (j₂ c))) → d ≠ 0 → (∀ g i i', ∃ y : PowerSeries K, algebraMap _ (FractionRing (PowerSeries K)) d * r g i i' = algebraMap _ (FractionRing (PowerSeries K)) y) → Hᵀ = H → H.det ≠ 0 → Function.Surjective σ → (∀ g, (mat r g)ᵀ * H * mat r (σ g) = algebraMap _ (FractionRing (PowerSeries K)) (u g) • H) → ∃ (Q : GL (Fin m) (FractionRing (PowerSeries K'))) (r' : G →* GL (Fin m) (PowerSeries K')), (Q : Matrix (Fin m) (Fin m) (FractionRing (PowerSeries K')))ᵀ * H.map (f₂.comp f₁) * Q = 1 ∧ (∀ g, pushRep (f₂.comp f₁) r g * Q = Q * pushRep (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) r' g) := by
  intro K K' G _ _ _ m j₁ f₁ j₂ f₂ r H σ u d h2 hf₁ hf₂ hj₁ hsq hd hdr hHs hdet hσ hsim
  obtain ⟨Q₀, r₀, hQ₀⟩ := Det.latInt r d hd hdr
  have hQ₀m : ∀ g, (r g).1 * Q₀.1 =
      Q₀.1 * (r₀ g).1.map (algebraMap _ _) := by
    intro g
    have := congr_arg Units.val (hQ₀ g)
    simpa only [Units.val_mul, pushRep, MonoidHom.comp_apply, coe_generalLinearGroup_map_eq_map] using this
  obtain ⟨H₁, hH₁⟩ : ∃ H₁ : Matrix (Fin m) (Fin m) (FractionRing (PowerSeries K)),
      H₁ = Q₀.1ᵀ * H * Q₀ := ⟨_, rfl⟩
  have hH₁s : H₁ᵀ = H₁ := by
    rw [hH₁, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hHs, Matrix.mul_assoc]
  have hQdet : Q₀.1.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 Q₀.isUnit).ne_zero
  have hH₁det : H₁.det ≠ 0 := by
    rw [hH₁, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hQdet hdet) hQdet
  have hsim₀ : ∀ g, ((r₀ g).1.map
      (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))ᵀ * H₁ *
      (r₀ (σ g)).1.map
      (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) =
      algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (u g) • H₁ := by
    intro g
    have key := hsim g
    simp only [mat, MonoidHom.comp_apply, Units.coeHom_apply] at key
    rw [hH₁]
    calc _ = (Q₀.1 *
            (r₀ g).1.map (algebraMap _ _))ᵀ * H *
          (Q₀.1 *
            (r₀ (σ g)).1.map (algebraMap _ _)) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = ((r g).1 * Q₀.1)ᵀ * H *
          ((r (σ g)).1 * Q₀.1) := by
          rw [← hQ₀m, ← hQ₀m]
      _ = Q₀.1ᵀ *
          ((r g).1ᵀ * H *
            (r (σ g)).1) * Q₀.1 := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [key, Matrix.mul_smul, Matrix.smul_mul]
  obtain ⟨P, H', r', hP, hr'⟩ := UpperTheory.V.AlgebraTools.selfdual_ramified (A := PowerSeries K)
    (F := FractionRing (PowerSeries K)) H₁ r₀ σ u (A' := PowerSeries K)
    (F' := FractionRing (PowerSeries K)) j₁ f₁ PowerSeries.X PowerSeries.X PowerSeries.X_irreducible
    hj₁.symm hf₁ (IsFractionRing.injective _ _) hH₁s hH₁det hσ hsim₀
  have h2u : IsUnit (2 : PowerSeries K) := by
    rw [← map_ofNat (PowerSeries.C (R := K)) 2]
    exact (isUnit_iff_ne_zero.2 h2).map _
  have hH's : H'.1ᵀ = H' := by
    have e : (H'.1.map
        (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))ᵀ =
        H'.1.map (algebraMap _ _) := by
      rw [← hP, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        ← Matrix.transpose_map, hH₁s, Matrix.mul_assoc]
    refine Matrix.ext fun i j => ?_
    exact IsFractionRing.injective _ (FractionRing (PowerSeries K)) (congr_fun (congr_fun e i) j)
  have hH'det : IsUnit H'.1.det :=
    (Matrix.isUnit_iff_isUnit_det _).1 H'.isUnit
  haveI := henselian_powerSeries K'
  obtain ⟨P₂, hP₂⟩ := UpperTheory.V.AlgebraTools.orthonormal_local j₂ H'.1
    h2u hH's hH'det hsq
  refine ⟨GeneralLinearGroup.map (f₂.comp f₁) Q₀ * GeneralLinearGroup.map f₂ P *
      GeneralLinearGroup.map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) P₂,
    (MulAut.conj P₂⁻¹).toMonoidHom.comp (pushRep j₂ r'), ?_, ?_⟩
  · have s1 : (Q₀.1.map (f₂.comp f₁))ᵀ *
        H.map (f₂.comp f₁) * Q₀.1.map (f₂.comp f₁) =
        (H₁.map f₁).map f₂ := by
      rw [← map_transpose_mul_mul_eq, ← hH₁, Matrix.map_map]
      rfl
    have s2 : (P.1.map f₂)ᵀ * (H₁.map f₁).map f₂ *
        P.1.map f₂ =
        (H'.1.map j₂).map
          (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) := by
      rw [← map_transpose_mul_mul_eq, hP, Matrix.map_map, Matrix.map_map]
      congr 1
      funext a
      exact hf₂ a
    have s3 : (P₂.1.map
        (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))))ᵀ *
        (H'.1.map j₂).map
          (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) *
        P₂.1.map
          (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) = 1 := by
      rw [← map_transpose_mul_mul_eq, hP₂, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [Units.val_mul, Units.val_mul, coe_generalLinearGroup_map_eq_map, coe_generalLinearGroup_map_eq_map, coe_generalLinearGroup_map_eq_map]
    rw [← s3, ← s2, ← s1]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  · intro g
    have t1 := congr_arg (GeneralLinearGroup.map (f₂.comp f₁)) (hQ₀ g)
    rw [map_mul, map_mul] at t1
    have t2 : GeneralLinearGroup.map (f₂.comp f₁) (GeneralLinearGroup.map (algebraMap (PowerSeries K)
        (FractionRing (PowerSeries K))) (r₀ g)) * GeneralLinearGroup.map f₂ P =
        GeneralLinearGroup.map f₂ P * GeneralLinearGroup.map
          (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) (GeneralLinearGroup.map j₂ (r' g)) := by
      apply Units.ext
      have t2m := congr_arg (fun M => Matrix.map M f₂) (hr' g)
      simp only [Matrix.map_mul, Matrix.map_map] at t2m
      simp only [Units.val_mul, pushRep, MonoidHom.comp_apply, coe_generalLinearGroup_map_eq_map, Matrix.map_map]
      have fe1 : (⇑(f₂.comp f₁) ∘ ⇑(algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))) =
          (⇑f₂ ∘ fun a => algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (j₁ a)) :=
        funext fun a => by simp [hf₁]
      have fe2 : (⇑(algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) ∘ ⇑j₂) =
          (⇑f₂ ∘ ⇑(algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))) :=
        funext fun a => by simp [hf₂]
      rw [fe1, fe2]
      exact t2m
    simp only [pushRep, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_inv_apply, map_mul, map_inv,
      inv_inv] at t1 ⊢
    calc _ = (GeneralLinearGroup.map (f₂.comp f₁) (r g) * GeneralLinearGroup.map (f₂.comp f₁) Q₀) *
          GeneralLinearGroup.map f₂ P *
          GeneralLinearGroup.map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) P₂ := by
          simp only [mul_assoc]
      _ = _ := by
          rw [t1, mul_assoc (GeneralLinearGroup.map (f₂.comp f₁) Q₀), t2]
          group

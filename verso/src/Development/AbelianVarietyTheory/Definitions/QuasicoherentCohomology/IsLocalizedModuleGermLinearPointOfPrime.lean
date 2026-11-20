import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapFOneInjectiveOfSectionsSurjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing

universe u

noncomputable section

namespace GlobalTheory.QCoh

variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}

section Maps

/- English proof (translation)
The claim follows from `TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx φ.mapPresheaf s`.
-/
theorem stalkFunctor_map_germ (φ : F ⟶ G) (x : X) (hx : x ∈ U) (s : Γ(F, U)) :
    (TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf (F.presheaf.germ U x hx s) =
      G.presheaf.germ U x hx (φ.app U s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx φ.mapPresheaf s

def stalkLinear (φ : F ⟶ G) (x : X) :
    (F.presheaf.stalk x :) →ₗ[X.presheaf.stalk x] (G.presheaf.stalk x :) where
  toFun := (TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf
  map_add' := map_add _
  map_smul' r t := by
    obtain ⟨U, hU, a, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hV, s, rfl⟩ := F.presheaf.exists_germ_eq t
    have hx : x ∈ U ⊓ V := ⟨hU, hV⟩
    rw [← X.presheaf.germ_res_apply (homOfLE (inf_le_left : U ⊓ V ≤ U)) x hx,
      ← F.presheaf.germ_res_apply (homOfLE (inf_le_right : U ⊓ V ≤ V)) x hx, RingHom.id_apply,
      ← germ_smul, stalkFunctor_map_germ, stalkFunctor_map_germ, φ.app_smul, germ_smul]

@[simp]
/- English proof (translation)
The claim follows from `stalkFunctor_map_germ φ x hx s @[simp]`.
-/
theorem stalkLinear_germ (φ : F ⟶ G) (x : X) (hx : x ∈ U) (s : Γ(F, U)) :
    stalkLinear φ x (F.presheaf.germ U x hx s) = G.presheaf.germ U x hx (φ.app U s) :=
  stalkFunctor_map_germ φ x hx s

@[simp]
/- English proof (translation)
Use extensionality with `t`. Take `⟨V, hV, s, rfl⟩` from `F.presheaf.exists_germ_eq t`. Rewrite using `[stalkLinear_germ]`. Both sides reduce to the same expression. Use the proof step `@[simp]`.
-/
theorem stalkLinear_id (F : X.Modules) (x : X) : stalkLinear (𝟙 F) x = LinearMap.id := by
  ext t
  obtain ⟨V, hV, s, rfl⟩ := F.presheaf.exists_germ_eq t
  rw [stalkLinear_germ]; rfl

@[simp]
/- English proof (translation)
Use extensionality with `t`. Take `⟨V, hV, s, rfl⟩` from `F.presheaf.exists_germ_eq t`. Rewrite using `[LinearMap.comp_apply, stalkLinear_germ, stalkLinear_germ, stalkLinear_germ]`. Both sides reduce to the same expression. Use the proof step `@[simp]`.
-/
theorem stalkLinear_comp (φ : F ⟶ G) (ψ : G ⟶ H) (x : X) :
    stalkLinear (φ ≫ ψ) x = stalkLinear ψ x ∘ₗ stalkLinear φ x := by
  ext t
  obtain ⟨V, hV, s, rfl⟩ := F.presheaf.exists_germ_eq t
  rw [LinearMap.comp_apply, stalkLinear_germ, stalkLinear_germ, stalkLinear_germ]; rfl

@[simp]
/- English proof (translation)
Use extensionality with `t`. Take `⟨V, hV, s, rfl⟩` from `F.presheaf.exists_germ_eq t`. Rewrite using `[LinearMap.add_apply, stalkLinear_germ, stalkLinear_germ, stalkLinear_germ, ← map_add]`. Both sides reduce to the same expression. Use the proof step `@[simp]`.
-/
theorem stalkLinear_add (φ ψ : F ⟶ G) (x : X) :
    stalkLinear (φ + ψ) x = stalkLinear φ x + stalkLinear ψ x := by
  ext t
  obtain ⟨V, hV, s, rfl⟩ := F.presheaf.exists_germ_eq t
  rw [LinearMap.add_apply, stalkLinear_germ, stalkLinear_germ, stalkLinear_germ, ← map_add]; rfl

@[simp]
/- English proof (translation)
Use extensionality with `t`. Take `⟨V, hV, s, rfl⟩` from `F.presheaf.exists_germ_eq t`. Rewrite using `[stalkLinear_germ]`. Conclude with `map_zero _`.
-/
theorem stalkLinear_zero (x : X) : stalkLinear (0 : F ⟶ G) x = 0 := by
  ext t
  obtain ⟨V, hV, s, rfl⟩ := F.presheaf.exists_germ_eq t
  rw [stalkLinear_germ]; exact map_zero _

def stalkLinearEquiv (e : F ≅ G) (x : X) :
    (F.presheaf.stalk x :) ≃ₗ[X.presheaf.stalk x] (G.presheaf.stalk x :) :=
  LinearEquiv.ofLinearMap (stalkLinear e.hom x) (stalkLinear e.inv x)
    (by rw [← stalkLinear_comp, e.inv_hom_id, stalkLinear_id])
    (by rw [← stalkLinear_comp, e.hom_inv_id, stalkLinear_id])

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem stalkLinearEquiv_apply (e : F ≅ G) (x : X) (t : (F.presheaf.stalk x :)) :
    stalkLinearEquiv e x t = stalkLinear e.hom x t := rfl

/- English proof (translation)
Rewrite using `[← SheafLES.exact_map_toAbSheaf_iff, TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]`. Conclude with `forall_congr' fun x ↦ ShortComplex.ab_exact_iff_function_exact _`.
-/
theorem exact_iff_stalkLinear (S : ShortComplex X.Modules) :
    S.Exact ↔ ∀ x : X, Function.Exact (stalkLinear S.f x) (stalkLinear S.g x) := by
  rw [← SheafLES.exact_map_toAbSheaf_iff, TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  exact forall_congr' fun x ↦ ShortComplex.ab_exact_iff_function_exact _

/- English proof (translation)
Rewrite using `[← ShortComplex.exact_iff_mono (ShortComplex.mk (0 : F ⟶ F) φ (by simp)) rfl, exact_iff_stalkLinear]`. Use `forall_congr' fun x ↦ ?_` and prove the remaining obligations. Rewrite using `[stalkLinear_zero]`. Conclude with `LinearMap.exact_zero_iff_injective _ _`.
-/
theorem mono_iff_stalkLinear_injective (φ : F ⟶ G) :
    Mono φ ↔ ∀ x : X, Function.Injective (stalkLinear φ x) := by
  rw [← ShortComplex.exact_iff_mono (ShortComplex.mk (0 : F ⟶ F) φ (by simp)) rfl,
    exact_iff_stalkLinear]
  refine forall_congr' fun x ↦ ?_
  rw [stalkLinear_zero]
  exact LinearMap.exact_zero_iff_injective _ _

/- English proof (translation)
Rewrite using `[← ShortComplex.exact_iff_epi (ShortComplex.mk φ (0 : G ⟶ G) (by simp)) rfl, exact_iff_stalkLinear]`. Use `forall_congr' fun x ↦ ?_` and prove the remaining obligations. Rewrite using `[stalkLinear_zero]`. Conclude with `LinearMap.exact_zero_iff_surjective _ _`.
-/
theorem epi_iff_stalkLinear_surjective (φ : F ⟶ G) :
    Epi φ ↔ ∀ x : X, Function.Surjective (stalkLinear φ x) := by
  rw [← ShortComplex.exact_iff_epi (ShortComplex.mk φ (0 : G ⟶ G) (by simp)) rfl,
    exact_iff_stalkLinear]
  refine forall_congr' fun x ↦ ?_
  rw [stalkLinear_zero]
  exact LinearMap.exact_zero_iff_surjective _ _

/- English proof (translation)
The claim follows from `(mono_iff_stalkLinear_injective φ).1 inferInstance x`.
-/
theorem stalkLinear_injective (φ : F ⟶ G) [Mono φ] (x : X) :
    Function.Injective (stalkLinear φ x) :=
  (mono_iff_stalkLinear_injective φ).1 inferInstance x

/- English proof (translation)
The claim follows from `(epi_iff_stalkLinear_surjective φ).1 inferInstance x`.
-/
theorem stalkLinear_surjective (φ : F ⟶ G) [Epi φ] (x : X) :
    Function.Surjective (stalkLinear φ x) :=
  (epi_iff_stalkLinear_surjective φ).1 inferInstance x

/- English proof (translation)
The claim follows from `TopCat.Presheaf.section_ext ⟨F.presheaf, F.isSheaf⟩ U s 0 fun x hx ↦ by rw [map_zero]; exact h x hx`.
-/
theorem section_eq_zero_of_germ (s : Γ(F, U))
    (h : ∀ (x : X) (hx : x ∈ U), F.presheaf.germ U x hx s = 0) : s = 0 :=
  TopCat.Presheaf.section_ext ⟨F.presheaf, F.isSheaf⟩ U s 0 fun x hx ↦ by
    rw [map_zero]; exact h x hx

def pointOfPrime (hU : IsAffineOpen U) (P : PrimeSpectrum Γ(X, U)) : U :=
  ⟨hU.fromSpec P, hU.range_fromSpec.le ⟨P, rfl⟩⟩

@[simp]
/- English proof (translation)
The claim follows from `hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _) @[simp]`.
-/
theorem primeIdealOf_pointOfPrime (hU : IsAffineOpen U) (P : PrimeSpectrum Γ(X, U)) :
    hU.primeIdealOf (pointOfPrime hU P) = P :=
  hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)

@[simp]
/- English proof (translation)
The claim follows from `Subtype.ext (hU.fromSpec_primeIdealOf x)`.
-/
theorem pointOfPrime_primeIdealOf (hU : IsAffineOpen U) (x : U) :
    pointOfPrime hU (hU.primeIdealOf x) = x :=
  Subtype.ext (hU.fromSpec_primeIdealOf x)

/- English proof (translation)
Use `isLocalizedModule_germLinear F hU (pointOfPrime hU ⟨P, hP⟩)` as an intermediate fact. Simplify using `only [primeIdealOf_pointOfPrime] at this`. Conclude with `this`.
-/
theorem isLocalizedModule_germLinear_pointOfPrime (F : X.Modules) [F.IsQuasicoherent]
    (hU : IsAffineOpen U) (P : Ideal Γ(X, U)) [hP : P.IsPrime] :
    IsLocalizedModule P.primeCompl (germLinear F (pointOfPrime hU ⟨P, hP⟩)) := by
  have := isLocalizedModule_germLinear F hU (pointOfPrime hU ⟨P, hP⟩)
  simp only [primeIdealOf_pointOfPrime] at this
  exact this

end Maps

end GlobalTheory.QCoh

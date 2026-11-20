import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHyp
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChart

namespace ReciprocityTheory.AnForm.R

open MvPolynomial IsLocalRing

noncomputable section

variable {σ : Type} [Fintype σ]

abbrev renC (σ : Type) [Fintype σ] : MvPolynomial σ ℂ ≃ₐ[ℂ] MvPolynomial (Fin (Fintype.card σ)) ℂ :=
  renameEquiv ℂ (Fintype.equivFin σ)

abbrev renR (σ : Type) [Fintype σ] : MvPolynomial σ ℂ ≃+* MvPolynomial (Fin (Fintype.card σ)) ℂ :=
  (renC σ).toRingEquiv

abbrev renPt (z : σ → ℂ) : Fin (Fintype.card σ) → ℂ := z ∘ (Fintype.equivFin σ).symm

/- English proof (translation)
Simplify using `only [renC, renPt, renameEquiv_apply, eval_rename]`. Rewrite using `[Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]`.
-/
theorem eval_renC (z : σ → ℂ) (h : MvPolynomial σ ℂ) : eval (renPt z) (renC σ h) = eval z h := by
  simp only [renC, renPt, renameEquiv_apply, eval_rename]
  rw [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]

/- English proof (translation)
Establish `key : ∀ x : MvPolynomial σ ℂ, eval (renPt z) ((renR σ).toMonoidHom x) = eval z x` using `fun x => eval_renC z x`. Establish `key' : ∀ y, (renR σ).toMonoidHom ((renR σ).symm y) = y` using `fun y => (renR σ).apply_symm_apply y`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`.

Introduce `hy`. Apply `hx` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `x ∈ RingHom.ker _`. Express the relevant statement in the definitionally equal form `_ ∈ RingHom.ker _ at hy`. Rewrite `hy`, the goal using `[RingHom.mem_ker]`.

Rewrite using `[← key x]`. Conclude with `hy`. Introduce `hy`. Use `⟨(renR σ).symm y, ?_, key' y⟩` and prove the remaining obligations. Introduce `hx`.

Apply `hy` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `y ∈ RingHom.ker _`. Express the relevant statement in the definitionally equal form `_ ∈ RingHom.ker _ at hx`. Rewrite `hx`, the goal using `[RingHom.mem_ker]`. Rewrite using `[← key' y, key]`.

Conclude with `hx`.
-/
theorem map_primeCompl_renC (z : σ → ℂ) :
    Submonoid.map (renR σ).toMonoidHom (ptIdealOf z).primeCompl = (ptIdeal (renPt z)).primeCompl := by
  have key : ∀ x : MvPolynomial σ ℂ, eval (renPt z) ((renR σ).toMonoidHom x) = eval z x :=
    fun x => eval_renC z x
  have key' : ∀ y, (renR σ).toMonoidHom ((renR σ).symm y) = y := fun y => (renR σ).apply_symm_apply y
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    intro hy
    apply hx
    change x ∈ RingHom.ker _
    change _ ∈ RingHom.ker _ at hy
    rw [RingHom.mem_ker] at hy ⊢
    rw [← key x]
    exact hy
  · intro hy
    refine ⟨(renR σ).symm y, ?_, key' y⟩
    intro hx
    apply hy
    change y ∈ RingHom.ker _
    change _ ∈ RingHom.ker _ at hx
    rw [RingHom.mem_ker] at hx ⊢
    rw [← key' y, key]
    exact hx

def locPtEquiv (z : σ → ℂ) : Localization.AtPrime (ptIdealOf z) ≃+* locPt (renPt z) :=
  IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime (ptIdealOf z)) (locPt (renPt z))
    (renR σ) (map_primeCompl_renC z)

/- English proof (translation)
Unfold `locPtEquiv`. Conclude with `IsLocalization.ringEquivOfRingEquiv_eq _ x`.
-/
theorem locPtEquiv_algebraMap (z : σ → ℂ) (x : MvPolynomial σ ℂ) :
    locPtEquiv z (algebraMap _ _ x) = algebraMap _ (locPt (renPt z)) (renC σ x) := by
  unfold locPtEquiv
  exact IsLocalization.ringEquivOfRingEquiv_eq _ x

def locAtEquiv (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) :
    locAt I z ≃+* locRing (I.map (renR σ : MvPolynomial σ ℂ →+* _)) (renPt z) :=
  Ideal.quotientEquiv _ _ (locPtEquiv z) (by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    refine RingHom.ext fun x => ?_
    exact (locPtEquiv_algebraMap z x).symm)

/- English proof (translation)
Rewrite using `[Ideal.map_comap_of_equiv]`. Conclude with `Iff.rfl`.
-/
theorem mem_map_renR_iff (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial (Fin (Fintype.card σ)) ℂ) :
    h ∈ I.map (renR σ : MvPolynomial σ ℂ →+* _) ↔ (renR σ).symm h ∈ I := by
  rw [Ideal.map_comap_of_equiv]
  exact Iff.rfl

/- English proof (translation)
Introduce `h hh`. Rewrite `hh` using `[mem_map_renR_iff]`. Establish `e` using `eval_renC z ((renR σ).symm h)`. Rewrite `e` using `[show renC σ ((renR σ).symm h) = h from (renR σ).apply_symm_apply h]`. Rewrite using `[e]`.

Conclude with `hz _ hh`.
-/
theorem renPt_zero (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) (hz : ∀ h ∈ I, eval z h = 0) :
    ∀ h ∈ I.map (renR σ : MvPolynomial σ ℂ →+* _), eval (renPt z) h = 0 := by
  intro h hh
  rw [mem_map_renR_iff] at hh
  have e := eval_renC z ((renR σ).symm h)
  rw [show renC σ ((renR σ).symm h) = h from (renR σ).apply_symm_apply h] at e
  rw [e]
  exact hz _ hh

/- English proof (translation)
Set `g : A →ₐ[ℤ] B` to `f.toRingHom.toIntAlgHom`. Set `g' : B →ₐ[ℤ] A` to `f.symm.toRingHom.toIntAlgHom`. Establish `hmax : ∀ x : A, f x ∈ maximalIdeal B ↔ x ∈ maximalIdeal A`. Introduce `x`. Simplify using `only [mem_maximalIdeal, mem_nonunits_iff]`.

Conclude with `not_congr (isUnit_map_iff f x)`. Establish `hA : maximalIdeal A ≤ (maximalIdeal B).comap g` using `fun x hx => (hmax x).2 hx`. Establish `hB : maximalIdeal B ≤ (maximalIdeal A).comap g'` using `fun y hy => by show f.symm y ∈ maximalIdeal A`. Rewrite using `[← hmax, f.apply_symm_apply]`. Conclude with `hy`.

Set `j₁` to `Ideal.mapCotangent (maximalIdeal A) (maximalIdeal B) g hA`. Set `j₂` to `Ideal.mapCotangent (maximalIdeal B) (maximalIdeal A) g' hB`. Set `j : CotangentSpace A ≃+ CotangentSpace B` to `{ toFun := j₁ invFun := j₂ left_inv := fun m => by`. Take `⟨x, rfl⟩` from `(maximalIdeal A).toCotangent_surjective m`. Simplify using `only [j₁, j₂, Ideal.mapCotangent_toCotangent]`.

Use `congr 1`. Conclude with `Subtype.ext (f.symm_apply_apply (x : A))`. Use `right_inv := fun m => by`. Take `⟨y, rfl⟩` from `(maximalIdeal B).toCotangent_surjective m`. Simplify using `only [j₁, j₂, Ideal.mapCotangent_toCotangent]`.

Use `congr 1`. Conclude with `Subtype.ext (f.apply_symm_apply (y : B))`. Use the proof step `map_add' := j₁.map_add }`. Set `i : ResidueField A ≃+* ResidueField B` to `ResidueField.mapEquiv f`. Establish `hc : ∀ (r : ResidueField A) (m : CotangentSpace A), j (r • m) = i r • j m`.

Introduce `r m`. Take `⟨a, rfl⟩` from `residue_surjective r`. Take `⟨x, rfl⟩` from `(maximalIdeal A).toCotangent_surjective m`. Establish `e1 : (residue A a : ResidueField A) • ((maximalIdeal A).toCotangent x : CotangentSpace A) = (maximalIdeal A).toCotangent (a • x)`. Rewrite using `[map_smul]`.

Conclude with `algebraMap_smul (ResidueField A) a _`. Establish `e3 : (residue B (f a) : ResidueField B) • ((maximalIdeal B).toCotangent ⟨g x, hA x.2⟩ : CotangentSpace B) = (maximalIdeal B).toCotangent (f a • ⟨g x, hA x.2⟩)`. Rewrite using `[map_smul]`. Conclude with `algebraMap_smul (ResidueField B) (f a) _`. Establish `e2 : i (residue A a) = residue B (f a)` using `by first`.

Consider the case `rfl`. Consider the case `exact IsLocalRing.ResidueField.map_residue (f : A →+* B) a`. Consider the case `simp [i]`. Establish `hj : ∀ m, j m = j₁ m` using `fun _ => rfl`. Rewrite using `[hj, hj, e1, e2, Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent, e3]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show f (a * (x : A)) = f a * f x`. Conclude with `map_mul f a x`. Establish `h2` using `congrArg Cardinal.toNat (lift_rank_eq_of_equiv_equiv (⇑i) j i.bijective hc)`.

Rewrite `h2` using `[Cardinal.toNat_lift, Cardinal.toNat_lift]`. Conclude with `h2`.
-/
theorem finrank_cotangentSpace_eq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] (f : A ≃+* B) :
    Module.finrank (ResidueField A) (CotangentSpace A) =
      Module.finrank (ResidueField B) (CotangentSpace B) := by
  classical
  let g : A →ₐ[ℤ] B := f.toRingHom.toIntAlgHom
  let g' : B →ₐ[ℤ] A := f.symm.toRingHom.toIntAlgHom
  have hmax : ∀ x : A, f x ∈ maximalIdeal B ↔ x ∈ maximalIdeal A := by
    intro x
    simp only [mem_maximalIdeal, mem_nonunits_iff]
    exact not_congr (isUnit_map_iff f x)
  have hA : maximalIdeal A ≤ (maximalIdeal B).comap g := fun x hx => (hmax x).2 hx
  have hB : maximalIdeal B ≤ (maximalIdeal A).comap g' := fun y hy => by
    show f.symm y ∈ maximalIdeal A
    rw [← hmax, f.apply_symm_apply]
    exact hy
  let j₁ := Ideal.mapCotangent (maximalIdeal A) (maximalIdeal B) g hA
  let j₂ := Ideal.mapCotangent (maximalIdeal B) (maximalIdeal A) g' hB
  let j : CotangentSpace A ≃+ CotangentSpace B :=
    { toFun := j₁
      invFun := j₂
      left_inv := fun m => by
        obtain ⟨x, rfl⟩ := (maximalIdeal A).toCotangent_surjective m
        simp only [j₁, j₂, Ideal.mapCotangent_toCotangent]
        congr 1
        exact Subtype.ext (f.symm_apply_apply (x : A))
      right_inv := fun m => by
        obtain ⟨y, rfl⟩ := (maximalIdeal B).toCotangent_surjective m
        simp only [j₁, j₂, Ideal.mapCotangent_toCotangent]
        congr 1
        exact Subtype.ext (f.apply_symm_apply (y : B))
      map_add' := j₁.map_add }
  let i : ResidueField A ≃+* ResidueField B := ResidueField.mapEquiv f
  have hc : ∀ (r : ResidueField A) (m : CotangentSpace A), j (r • m) = i r • j m := by
    intro r m
    obtain ⟨a, rfl⟩ := residue_surjective r
    obtain ⟨x, rfl⟩ := (maximalIdeal A).toCotangent_surjective m
    have e1 : (residue A a : ResidueField A) • ((maximalIdeal A).toCotangent x : CotangentSpace A) =
        (maximalIdeal A).toCotangent (a • x) := by
      rw [map_smul]
      exact algebraMap_smul (ResidueField A) a _
    have e3 : (residue B (f a) : ResidueField B) •
        ((maximalIdeal B).toCotangent ⟨g x, hA x.2⟩ : CotangentSpace B) =
        (maximalIdeal B).toCotangent (f a • ⟨g x, hA x.2⟩) := by
      rw [map_smul]
      exact algebraMap_smul (ResidueField B) (f a) _
    have e2 : i (residue A a) = residue B (f a) := by
      first
        | rfl
        | exact IsLocalRing.ResidueField.map_residue (f : A →+* B) a
        | simp [i]
    have hj : ∀ m, j m = j₁ m := fun _ => rfl
    rw [hj, hj, e1, e2, Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent, e3]
    congr 1
    apply Subtype.ext
    show f (a * (x : A)) = f a * f x
    exact map_mul f a x
  have h2 := congrArg Cardinal.toNat (lift_rank_eq_of_equiv_equiv (⇑i) j i.bijective hc)
  rw [Cardinal.toNat_lift, Cardinal.toNat_lift] at h2
  exact h2

end

end ReciprocityTheory.AnForm.R

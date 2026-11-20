import Development.EtaleCohomology.EtaleSheaves.EmbedNonDeg

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing LateralTheory.E.ChartsGeom_vpaPf

namespace LateralTheory.E.GeometricData

/- English proof (translation)
Establish `h : p.appLE ⊤ ⊤ le_top = p.appTop` using `p.appLE_eq_app (U := ⊤)`. Rewrite using `[rA, h]`.
-/
theorem rA_top {A : Type} [CommRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) :
    rA p ⊤ = p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom := by
  have h : p.appLE ⊤ ⊤ le_top = p.appTop := p.appLE_eq_app (U := ⊤)
  rw [rA, h]

/- English proof (translation)
Introduce `A _ _ Z p hIL`. Take `⟨L, u, l, hu, hl, rfl⟩` from `hIL`. Establish `: UniversallyClosed u` using `(IsIntegralHom.iff_universallyClosed_and_isAffineHom.mp hu).1`. Establish `: UniversallyClosed l` using `hl.1.toUniversallyClosed`. Establish `h1` using `isIntegral_appTop_of_universallyClosed (u ≫ l)`.

Rewrite using `[rA_top]`. Use `RingHom.IsIntegral.trans _ _ ?_ h1` and prove the remaining obligations. Conclude with `RingHom.isIntegral_of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm.surjective`.
-/
theorem topInt : TopInt := by
  intro A _ _ Z p hIL
  obtain ⟨L, u, l, hu, hl, rfl⟩ := hIL
  have : UniversallyClosed u := (IsIntegralHom.iff_universallyClosed_and_isAffineHom.mp hu).1
  have : UniversallyClosed l := hl.1.toUniversallyClosed
  have h1 := isIntegral_appTop_of_universallyClosed (u ≫ l)
  rw [rA_top]
  refine RingHom.IsIntegral.trans _ _ ?_ h1
  exact RingHom.isIntegral_of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm.surjective

/- English proof (translation)
Simplify using `only [Scheme.germToFunctionField]`. Conclude with `TopCat.Presheaf.germ_res_apply _ _ _ _ _`.
-/
theorem germ_res_eq {Z : Scheme.{0}} [IsIntegral Z] (U W : Z.Opens) (h : W ≤ U) [Nonempty U] [Nonempty W]
    (s : Γ(Z, U)) : Z.germToFunctionField W (Z.presheaf.map (homOfLE h).op s) = Z.germToFunctionField U s := by
  simp only [Scheme.germToFunctionField]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/- English proof (translation)
Introduce `A _ _ Z p hI hTop hAff`. Take `⟨z⟩ : Nonempty Z` from `inferInstance`. Establish `: Nonempty (⊤ : Z.Opens)` using `⟨⟨z, trivial⟩⟩`. Establish `: Nonempty (⊤ ⊓ ⊤ : Z.Opens)` using `⟨⟨z, trivial, trivial⟩⟩`. Set `φ : Γ(Z, ⊤) →+* Z.functionField` to `(Z.germToFunctionField ⊤).hom`.

Set `_ : Algebra A Z.functionField` to `(φ.comp (rA p ⊤)).toAlgebra`. Set `B : Subalgebra A Z.functionField` to `{ toSubsemiring := φ.rangeS, algebraMap_mem' := fun a => ⟨rA p ⊤ a, rfl⟩ }`. Establish `hBint : ∀ x ∈ B, IsIntegral A x`. Introduce and unpack `x ⟨g, rfl⟩`. Take `⟨P, hP, hP0⟩` from `hTop g`.

Use `⟨P, hP, ?_⟩` and prove the remaining obligations. Establish `: Polynomial.eval₂ (algebraMap A Z.functionField) (φ g) P = φ (Polynomial.eval₂ (rA p ⊤) g P)`. Rewrite using `[Polynomial.hom_eval₂]`. Both sides reduce to the same expression. Rewrite using `[this, hP0, map_zero]`.

Establish `hDov : AdjoinInv B 1 = B`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[AdjoinInv, Algebra.adjoin_le_iff]`. Introduce and unpack `x (hx | hx)`. Conclude with `hx`.

Rewrite using `[Set.mem_singleton_iff.mp hx, inv_one]`. Conclude with `B.one_mem`. Introduce `x hx`. Conclude with `Algebra.subset_adjoin (Or.inl hx)`. Use `⟨Z.functionField, inferInstance, inferInstance, B, B, 1, ?_, fun x hx _ => hBint x hx, ?_⟩` and prove the remaining obligations.

Use `⟨one_ne_zero, B.one_mem, by rw [inv_one]; exact B.one_mem, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `b hb`. Conclude with `(hBint b hb).tower_top`. Introduce `b hb`. Conclude with `(hBint b hb).tower_top`.

Rewrite using `[hDov]`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Conclude with `Algebra.subset_adjoin (Or.inl hx)`. Rewrite using `[Algebra.adjoin_le_iff]`.

Introduce and unpack `x (hx | hx)`. Conclude with `hx`. Rewrite using `[Set.mem_singleton_iff.mp hx]`. Conclude with `B.one_mem`. Use `⟨⊤, ⊤, φ, φ, (Z.germToFunctionField (⊤ ⊓ ⊤)).hom, hAff, hAff, by simpa using hAff, sup_idem _, Z.germToFunctionField_injective _, Z.germToFunctionField_injective _, Z.germToFunctionField_injective _, rfl, rfl, ?_, ?_, ?_, fun a => rfl, fun a => rfl⟩` and prove the remaining obligations.

Rewrite using `[hDov]`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, rfl⟩`. Conclude with `⟨_, germ_res_eq (⊤ ⊓ ⊤) ⊤ (le_inf le_rfl le_rfl) s⟩`.

Introduce and unpack `⟨s, rfl⟩`. Conclude with `⟨Z.presheaf.map (homOfLE inf_le_left).op s, germ_res_eq _ _ _ s⟩`. Introduce `s`. Conclude with `germ_res_eq _ _ _ s`. Introduce `s`.

Conclude with `germ_res_eq _ _ _ s`.
-/
theorem embedAffine : EmbedAffine := by
  intro A _ _ Z p hI hTop hAff
  obtain ⟨z⟩ : Nonempty Z := inferInstance
  have : Nonempty (⊤ : Z.Opens) := ⟨⟨z, trivial⟩⟩
  have : Nonempty (⊤ ⊓ ⊤ : Z.Opens) := ⟨⟨z, trivial, trivial⟩⟩
  let φ : Γ(Z, ⊤) →+* Z.functionField := (Z.germToFunctionField ⊤).hom
  let _ : Algebra A Z.functionField := (φ.comp (rA p ⊤)).toAlgebra
  let B : Subalgebra A Z.functionField :=
    { toSubsemiring := φ.rangeS, algebraMap_mem' := fun a => ⟨rA p ⊤ a, rfl⟩ }
  have hBint : ∀ x ∈ B, IsIntegral A x := by
    rintro x ⟨g, rfl⟩
    obtain ⟨P, hP, hP0⟩ := hTop g
    refine ⟨P, hP, ?_⟩
    have : Polynomial.eval₂ (algebraMap A Z.functionField) (φ g) P = φ (Polynomial.eval₂ (rA p ⊤) g P) := by
      rw [Polynomial.hom_eval₂]; rfl
    rw [this, hP0, map_zero]
  have hDov : AdjoinInv B 1 = B := by
    apply le_antisymm
    · rw [AdjoinInv, Algebra.adjoin_le_iff]
      rintro x (hx | hx)
      · exact hx
      · rw [Set.mem_singleton_iff.mp hx, inv_one]; exact B.one_mem
    · intro x hx
      exact Algebra.subset_adjoin (Or.inl hx)
  refine ⟨Z.functionField, inferInstance, inferInstance, B, B, 1, ?_, fun x hx _ => hBint x hx, ?_⟩
  · refine ⟨one_ne_zero, B.one_mem, by rw [inv_one]; exact B.one_mem, ?_, ?_, ?_⟩
    · intro b hb; exact (hBint b hb).tower_top
    · intro b hb; exact (hBint b hb).tower_top
    · rw [hDov]
      apply le_antisymm
      · intro x hx; exact Algebra.subset_adjoin (Or.inl hx)
      · rw [Algebra.adjoin_le_iff]
        rintro x (hx | hx)
        · exact hx
        · rw [Set.mem_singleton_iff.mp hx]; exact B.one_mem
  · refine ⟨⊤, ⊤, φ, φ, (Z.germToFunctionField (⊤ ⊓ ⊤)).hom, hAff, hAff, by simpa using hAff, sup_idem _,
      Z.germToFunctionField_injective _, Z.germToFunctionField_injective _, Z.germToFunctionField_injective _,
      rfl, rfl, ?_, ?_, ?_, fun a => rfl, fun a => rfl⟩
    · rw [hDov]
      ext x
      constructor
      · rintro ⟨s, rfl⟩
        exact ⟨_, germ_res_eq (⊤ ⊓ ⊤) ⊤ (le_inf le_rfl le_rfl) s⟩
      · rintro ⟨s, rfl⟩
        exact ⟨Z.presheaf.map (homOfLE inf_le_left).op s, germ_res_eq _ _ _ s⟩
    · intro s; exact germ_res_eq _ _ _ s
    · intro s; exact germ_res_eq _ _ _ s

end LateralTheory.E.GeometricData

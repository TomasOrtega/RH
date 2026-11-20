import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPair

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

/- English proof (translation)
Use `haveI : Finite H := Nat.finite_of_card_ne_zero (by omega)`. Use `haveI := Fintype.ofFinite H`. Rewrite `hH` using `[Nat.card_eq_fintype_card]`. Assume the negation of the conclusion as `hxy`. Establish `h3 : ({1, x, x * y} : Finset H).card = 3`.

Use `Finset.card_eq_three.mpr ⟨1, x, x * y, fun h => hx h.symm, fun h => hxy h.symm, ?_, rfl⟩` and prove the remaining obligations. Introduce `h`. Conclude with `hy (mul_left_cancel (a := x) (by rw [mul_one]; exact h.symm))`. Use `Finset.card_le_univ ({1, x, x * y} : Finset H)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private theorem mul_eq_one_of_card_eq_two_of_ne_one {H : Type*} [Group H] (hH : Nat.card H = 2)
    (x y : H) (hx : x ≠ 1) (hy : y ≠ 1) : x * y = 1 := by
  classical
  haveI : Finite H := Nat.finite_of_card_ne_zero (by omega)
  haveI := Fintype.ofFinite H
  rw [Nat.card_eq_fintype_card] at hH
  by_contra hxy
  have h3 : ({1, x, x * y} : Finset H).card = 3 := by
    refine Finset.card_eq_three.mpr ⟨1, x, x * y, fun h => hx h.symm, fun h => hxy h.symm, ?_, rfl⟩
    intro h
    exact hy (mul_left_cancel (a := x) (by rw [mul_one]; exact h.symm))
  have := Finset.card_le_univ ({1, x, x * y} : Finset H)
  omega

set_option maxHeartbeats 400000 in
/- English proof (translation)
Introduce `Ω _ _ _ l _ c D T`. Establish `hKL : T.K ≤ T.L`. Rewrite using `[T.hL]`. Conclude with `le_sup_right`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Unfold `UpperTheory.V.Ws.Tower.GalL`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨g, rfl⟩`. Rewrite using `[Subgroup.mem_comap, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`.

Conclude with `g.commutes ⟨x, hKL hx⟩`. Introduce `a ha`. Rewrite `ha` using `[Subgroup.mem_comap]`. Establish `hF : resQ T.F a ∈ T.F.fixingSubgroup`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`.

Introduce `x hx`. Conclude with `a.commutes ⟨x, hx⟩`. Establish `hL : resQ T.F a ∈ T.L.fixingSubgroup`. Rewrite using `[T.hL, IntermediateField.fixingSubgroup_sup]`. Conclude with `⟨hF, ha⟩`.

Rewrite `hL` using `[IntermediateField.mem_fixingSubgroup_iff]`. Conclude with `⟨{ a.toRingEquiv with commutes' := fun x => hL x x.2 }, by ext z; rfl⟩`. Introduce `g₁ g₂ h`. Use extensionality with `z`. Conclude with `congrArg (fun k => k z) h`.

Use `letI : Algebra T.F T.L := (IntermediateField.inclusion T.F_le).toRingHom.toAlgebra haveI : IsScalarTower T.F T.L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Establish `he : (resLe T.F_le : G T.L Ω → G T.F Ω) = AlgEquiv.restrictScalarsHom T.F`. Use function extensionality and compare the values at `g`. Use `ext`. Both sides reduce to the same expression.

Rewrite using `[he]`. Conclude with `UpperTheory.V.Af.continuous_restrictScalarsHom _ _ _`. Unfold `UpperTheory.V.Ws.Tower.GalL haveI : Algebra.IsQuadraticExtension ℚ T.K := ⟨T.degK⟩ haveI hN : Normal ℚ T.K := Algebra.IsQuadraticExtension.normal ℚ T.K haveI : IsGalois ℚ T.K := {}`. Establish `hcard : Nat.card (T.K ≃ₐ[ℚ] T.K) = 2`. Rewrite using `[IsGalois.card_aut_eq_finrank, T.degK]`.

Establish `hker` using `@IntermediateField.restrictNormalHom_ker ℚ Ω _ _ _ T.K (by convert hN; exact Subsingleton.elim _ _)`. Introduce `a b ha hb`. Rewrite `ha`, `hb`, the goal using `[Subgroup.mem_comap, ← hker, MonoidHom.mem_ker]`. Rewrite using `[map_mul, map_mul]`. Apply the tactic sequence `exact mul_eq_one_of_card_eq_two_of_ne_one (by convert hcard <;> first | rfl | exact Subsingleton.elim _ _) _ _ ha hb`.

Introduce `g`. Conclude with `⟨by ext; rfl, rfl, rfl⟩`. Introduce `A g`. Conclude with `⟨Iff.rfl, Iff.rfl⟩`.
-/
theorem UpperTheory.V.Ws.P1.towerGal :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), (resLe T.F_le).range = T.GalL ∧ Function.Injective (resLe T.F_le) ∧ Continuous (resLe T.F_le) ∧
          (∀ a b : G T.F Ω, a ∉ T.GalL → b ∉ T.GalL → a * b ∈ T.GalL) ∧
          (∀ g : G T.L Ω, resQ T.F (resLe T.F_le g) = resQ T.L g ∧ cycZ T.F Ω l (resLe T.F_le g) = cycZ T.L Ω l g ∧ cycZ ℚ Ω l (resQ T.L g) = cycZ T.L Ω l g) ∧
          ∀ (A : ValuationSubring Ω) (g : G T.L Ω), (resLe T.F_le g ∈ Dec (F := T.F) A ↔ g ∈ Dec (F := T.L) A) ∧ (resLe T.F_le g ∈ Ine (F := T.F) A ↔ g ∈ Ine (F := T.L) A) := by
  intro Ω _ _ _ l _ c D T
  have hKL : T.K ≤ T.L := by
    rw [T.hL]
    exact le_sup_right
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold UpperTheory.V.Ws.Tower.GalL
    apply le_antisymm
    · rintro _ ⟨g, rfl⟩
      rw [Subgroup.mem_comap, IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact g.commutes ⟨x, hKL hx⟩
    · intro a ha
      rw [Subgroup.mem_comap] at ha
      have hF : resQ T.F a ∈ T.F.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        exact a.commutes ⟨x, hx⟩
      have hL : resQ T.F a ∈ T.L.fixingSubgroup := by
        rw [T.hL, IntermediateField.fixingSubgroup_sup]
        exact ⟨hF, ha⟩
      rw [IntermediateField.mem_fixingSubgroup_iff] at hL
      exact ⟨{ a.toRingEquiv with commutes' := fun x => hL x x.2 }, by ext z; rfl⟩
  · intro g₁ g₂ h
    ext z
    exact congrArg (fun k => k z) h
  · letI : Algebra T.F T.L := (IntermediateField.inclusion T.F_le).toRingHom.toAlgebra
    haveI : IsScalarTower T.F T.L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have he : (resLe T.F_le : G T.L Ω → G T.F Ω) = AlgEquiv.restrictScalarsHom T.F := by
      funext g
      ext
      rfl
    rw [he]
    exact UpperTheory.V.Af.continuous_restrictScalarsHom _ _ _
  · unfold UpperTheory.V.Ws.Tower.GalL
    haveI : Algebra.IsQuadraticExtension ℚ T.K := ⟨T.degK⟩
    haveI hN : Normal ℚ T.K := Algebra.IsQuadraticExtension.normal ℚ T.K
    haveI : IsGalois ℚ T.K := {}
    have hcard : Nat.card (T.K ≃ₐ[ℚ] T.K) = 2 := by
      rw [IsGalois.card_aut_eq_finrank, T.degK]
    have hker := @IntermediateField.restrictNormalHom_ker ℚ Ω _ _ _ T.K
      (by convert hN; exact Subsingleton.elim _ _)
    intro a b ha hb
    rw [Subgroup.mem_comap, ← hker, MonoidHom.mem_ker] at ha hb ⊢
    rw [map_mul, map_mul]
    exact mul_eq_one_of_card_eq_two_of_ne_one (by convert hcard <;> first | rfl | exact Subsingleton.elim _ _) _ _ ha hb
  · intro g
    exact ⟨by ext; rfl, rfl, rfl⟩
  · intro A g
    exact ⟨Iff.rfl, Iff.rfl⟩

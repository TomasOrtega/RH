import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

/- English proof (translation)
Use `haveI : Infinite K := CharZero.infinite K`. Apply `Polynomial.eq_of_infinite_eval_eq` to reduce the goal to its premises. Use `Set.infinite_univ.mono ?_` and prove the remaining obligations. Introduce `t _`. Simplify using `only [Set.mem_setOf_eq]`.

Establish `ht : t = c * (c⁻¹ * t)` using `by field_simp`. Rewrite using `[ht, Polynomial.scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, Matrix.eval_charpoly, Matrix.eval_charpoly]`. Establish `hs` using `Matrix.det_smul (Matrix.scalar (Fin n) (c⁻¹ * t) - M) c`. Rewrite `hs` using `[Fintype.card_fin]`. Rewrite using `[← hs]`.

Use `congr 1`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[Matrix.scalar_apply, Matrix.diagonal_apply_eq, mul_sub]`.

Simplify using `[Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h, mul_sub]`.
-/
private theorem charpoly_smul_scale {K : Type} [Field K] [CharZero K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {c : K}
    (hc : c ≠ 0) : (c • M).charpoly = M.charpoly.scaleRoots c := by
  haveI : Infinite K := CharZero.infinite K
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.infinite_univ.mono ?_
  intro t _
  simp only [Set.mem_setOf_eq]
  have ht : t = c * (c⁻¹ * t) := by field_simp
  rw [ht, Polynomial.scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
    Matrix.eval_charpoly, Matrix.eval_charpoly]
  have hs := Matrix.det_smul (Matrix.scalar (Fin n) (c⁻¹ * t) - M) c
  rw [Fintype.card_fin] at hs
  rw [← hs]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.scalar_apply, Matrix.diagonal_apply_eq, mul_sub]
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h, mul_sub]

/- English proof (translation)
Simplify using `[W.GDet.chi, W.GDet.comap, MonoidAlgebra.mapRingHom_single]`. Rewrite using `[← MonoidAlgebra.mapDomainRingHom_apply, map_sub, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapDomain_single, map_one]`.
-/
private theorem chi_comap_single {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (g : H) : (D.comap φ).chi (MonoidAlgebra.single g 1) = D.chi (MonoidAlgebra.single (φ g) 1) := by
  simp [W.GDet.chi, W.GDet.comap, MonoidAlgebra.mapRingHom_single]
  rw [← MonoidAlgebra.mapDomainRingHom_apply, map_sub, MonoidAlgebra.mapDomainRingHom_apply,
    MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapDomain_single,
    map_one]

/- English proof (translation)
Use `letI : Algebra A B[X] := ((algebraMap B B[X]).comp f).toAlgebra`. Set `F : A[X] →ₐ[A] B[X]` to `{ Polynomial.mapRingHom f with commutes' := fun a => by simp [RingHom.algebraMap_toAlgebra] }`. Establish `h` using `D.nat A[X] B[X] F (MonoidAlgebra.single 1 X - MonoidAlgebra.single g 1)`. Establish `e : MonoidAlgebra.mapRingHom G (F : A[X] →+* B[X]) (MonoidAlgebra.single 1 X - MonoidAlgebra.single g 1) = MonoidAlgebra.single 1 X - MonoidAlgebra.single g 1`. Simplify using `[F]`.

Rewrite `h` using `[e]`. Simplify using `only [W.GDet.chi, W.GDet.map, map_sub, MonoidAlgebra.mapRingHom_single, map_one]`. Conclude with `h`.
-/
private theorem chi_map_single {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : W.GDet n A G) (f : A →+* B)
    (g : G) : (D.map f).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map f := by
  letI : Algebra A B[X] := ((algebraMap B B[X]).comp f).toAlgebra
  let F : A[X] →ₐ[A] B[X] :=
    { Polynomial.mapRingHom f with commutes' := fun a => by simp [RingHom.algebraMap_toAlgebra] }
  have h := D.nat A[X] B[X] F (MonoidAlgebra.single 1 X - MonoidAlgebra.single g 1)
  have e : MonoidAlgebra.mapRingHom G (F : A[X] →+* B[X])
      (MonoidAlgebra.single 1 X - MonoidAlgebra.single g 1) =
      MonoidAlgebra.single 1 X - MonoidAlgebra.single g 1 := by
    simp [F]
  rw [e] at h
  simp only [W.GDet.chi, W.GDet.map, map_sub, MonoidAlgebra.mapRingHom_single, map_one]
  exact h

/- English proof (translation)
Use `haveI : Nontrivial A := y.domain_nontrivial`. Establish `hlc : i p.leadingCoeff = 1`. Rewrite using `[← Polynomial.leadingCoeff_map_of_injective hi, hp]`. Conclude with `(Matrix.charpoly_monic M).leadingCoeff`. Rewrite using `[Polynomial.map_scaleRoots _ _ _ (by simp [hlc]), ← Polynomial.map_map, hp, ← Matrix.charpoly_map, RingHom.comp_apply, charpoly_smul_scale _ hb]`.
-/
private theorem scale_point {A B K : Type} [CommRing A] [CommRing B] [Field K] [CharZero K] {n : ℕ} (i : B →+* A)
    (hi : Function.Injective i) (y : A →+* K) (p : B[X]) (M : Matrix (Fin n) (Fin n) A) (hp : p.map i = M.charpoly)
    (b : B) (hb : y (i b) ≠ 0) : (p.scaleRoots b).map (y.comp i) = (y (i b) • M.map y).charpoly := by
  haveI : Nontrivial A := y.domain_nontrivial
  have hlc : i p.leadingCoeff = 1 := by
    rw [← Polynomial.leadingCoeff_map_of_injective hi, hp]
    exact (Matrix.charpoly_monic M).leadingCoeff
  rw [Polynomial.map_scaleRoots _ _ _ (by simp [hlc]), ← Polynomial.map_map, hp, ← Matrix.charpoly_map,
    RingHom.comp_apply, charpoly_smul_scale _ hb]

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D T c' h K X B n φ hφ y x hx`. Unfold `W.UniversalOrdinaryDeterminantRing.Pt.IsRep`. Rewrite using `[W.UniversalOrdinaryDeterminantRing.Pt.D.eq_1]`. Apply `CA.d_gext` to reduce the goal to its premises. Introduce `g i _ _`.

Rewrite using `[W.GDet.lam.eq_1, W.GDet.lam.eq_1, (AlgebraTools.Det.repApi _).2.1]`. Use `erw [chi_comap_single, chi_map_single]`. Use `congr 2`. Establish `hxφ : (x : B.B →+* PadicAlgCl l) = ((y : X.A →+* PadicAlgCl l).comp (algebraMap X.B X.A)).comp (φ : B.B →+* X.B)`. Use extensionality with `b`.

Conclude with `hx b`. Establish `e : (y : X.A →+* PadicAlgCl l) (algebraMap X.B X.A (algebraMap c'.O X.B (↑(K.κ g) * ↑(K.β g) ^ n))) = algebraMap c'.O (PadicAlgCl l) (↑(K.κ g) * ↑(K.β g) ^ n)`. Rewrite using `[← IsScalarTower.algebraMap_apply]`. Conclude with `y.commutes _`. Rewrite using `[hxφ, ← Polynomial.map_map]`.

Use `erw [hφ.1 g]`. Rewrite using `[scale_point (algebraMap X.B X.A) X.inj (y : X.A →+* PadicAlgCl l) _ (X.P.r _) (X.cp_map _), e]`. Use `congr 1`. Simplify using `[W.mat.eq_1, Af.tw_val, W.pushCh.eq_1, PD.map.eq_1]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Establish `u` using `(Units.map (algebraMap c'.O (PadicAlgCl l) : c'.O →* PadicAlgCl l) (K.κ g * K.β g ^ n)).ne_zero`. Simplify using `using u`.
-/
theorem UpperTheory.V.Ws.auRep :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (n : ℕ) (φ : B.B →ₐ[c'.O] X.B), K.IsPhi X n B φ → ∀ (y : X.A →ₐ[c'.O] PadicAlgCl l) (x : B.Pt), (∀ b, x b = y (algebraMap X.B X.A (φ b))) → x.IsRep (Af.tw ((X.P.map (y : X.A →+* PadicAlgCl l)).r.comp (resLe T.F_le)).toHomUnits (W.pushCh (algebraMap c'.O (PadicAlgCl l)) (K.κ * K.β ^ n))) := by
  intro Ω _ _ _ l _ c D T c' h K X B n φ hφ y x hx
  unfold W.UniversalOrdinaryDeterminantRing.Pt.IsRep
  rw [W.UniversalOrdinaryDeterminantRing.Pt.D.eq_1]
  apply CA.d_gext
  intro g i _ _
  rw [W.GDet.lam.eq_1, W.GDet.lam.eq_1, (AlgebraTools.Det.repApi _).2.1]
  erw [chi_comap_single, chi_map_single]
  congr 2
  have hxφ : (x : B.B →+* PadicAlgCl l) =
      ((y : X.A →+* PadicAlgCl l).comp (algebraMap X.B X.A)).comp (φ : B.B →+* X.B) := by
    ext b
    exact hx b
  have e : (y : X.A →+* PadicAlgCl l) (algebraMap X.B X.A (algebraMap c'.O X.B
      (↑(K.κ g) * ↑(K.β g) ^ n))) = algebraMap c'.O (PadicAlgCl l) (↑(K.κ g) * ↑(K.β g) ^ n) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact y.commutes _
  rw [hxφ, ← Polynomial.map_map]
  erw [hφ.1 g]
  rw [scale_point (algebraMap X.B X.A) X.inj (y : X.A →+* PadicAlgCl l) _ (X.P.r _) (X.cp_map _), e]
  · congr 1
    simp [W.mat.eq_1, Af.tw_val, W.pushCh.eq_1, PD.map.eq_1]
    rfl
  · rw [e]
    have u := (Units.map (algebraMap c'.O (PadicAlgCl l) : c'.O →* PadicAlgCl l) (K.κ g * K.β g ^ n)).ne_zero
    simpa using u

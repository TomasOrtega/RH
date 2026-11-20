import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.UnivEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RtCompl
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RtPoints
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsEps
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDiag
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial

section

variable {O G : Type} [CommRing O] [Group G]

private def Cond (Ψ : G →* Oˣ) (I : Subgroup G) {C : Type} [CommRing C] [Algebra O C] (r : G →* GG 3 C) : Prop :=
  (∀ s ∈ I, (r s).mat.charpoly = ∏ a, (X - Polynomial.C (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ a s)))) ∧
    ∀ s : Fin 3 → G, (∀ a, s a ∈ I) →
      ((r (s 0)).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ 0 (s 0)))) *
        ((r (s 1)).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ 1 (s 1)))) *
        ((r (s 2)).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ 2 (s 2)))) = 0

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem scalar_map {R C : Type} [CommRing R] [CommRing C] (f : R →+* C) (c : R) :
    f.mapMatrix (Matrix.scalar (Fin 3) c) = Matrix.scalar (Fin 3) (f c) := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

/- English proof (translation)
Set `P : G → R[X]` to `fun s => (r s).mat.charpoly - ∏ a, (X - Polynomial.C (algebraMap O R (UpperTheory.V.UnitaryThreeInertia.psi Ψ a s)))`. Set `M : (Fin 3 → G) → Matrix (Fin 3) (Fin 3) R` to `fun s => ((r (s 0)).mat - Matrix.scalar _ (algebraMap O R (UpperTheory.V.UnitaryThreeInertia.psi Ψ 0 (s 0)))) * ((r (s 1)).mat - Matrix.scalar _ (algebraMap O R (UpperTheory.V.UnitaryThreeInertia.psi Ψ 1 (s 1)))) * ((r (s 2)).mat - Matrix.scalar _ (algebraMap O R (UpperTheory.V.U …`. Use `⟨{a | (∃ s ∈ I, ∃ k, a = (P s).coeff k) ∨ ∃ s : Fin 3 → G, (∀ a, s a ∈ I) ∧ ∃ i j, a = M s i j}, fun C _ _ f => ?_⟩` and prove the remaining obligations. Establish `hm : ∀ s, (push f r s).mat = (f : R →+* C).mapMatrix (r s).mat` using `fun _ => rfl`. Establish `hc : ∀ o, (f : R →+* C) (algebraMap O R o) = algebraMap O C o` using `f.commutes`.

Establish `hP : ∀ s, (P s).map (f : R →+* C) = (push f r s).mat.charpoly - ∏ a, (X - Polynomial.C (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ a s)))` using `fun s => by`. Simplify using `only [P, hm, RingHom.mapMatrix_apply, Matrix.charpoly_map, Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_X, Polynomial.map_C, hc]`. Establish `hM : ∀ s, (f : R →+* C).mapMatrix (M s) = ((push f r (s 0)).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ 0 (s 0)))) * ((push f r (s 1)).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ 1 (s 1)))) * ((push f r (s 2)). …` using `fun s => by`. Simplify using `only [M, hm, map_mul, map_sub, scalar_map, hc]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩ a (⟨s, hs, k, rfl⟩ | ⟨s, hs, i, j, rfl⟩)`. Use `hP s` as an intermediate fact. Rewrite `this` using `[h1 s hs, sub_self]`. Simplify using `using congrArg (fun p => p.coeff k) this`. Use `hM s` as an intermediate fact.

Rewrite `this` using `[h2 s hs]`. Simplify using `using congrFun (congrFun this i) j`. Introduce `h`. Use `⟨fun s hs => ?_, fun s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero, ← hP]`.

Use extensionality with `k`. Simplify using `using h _ (Or.inl ⟨s, hs, k, rfl⟩)`. Rewrite using `[← hM]`. Use extensionality with `i j`. Simplify using `using h _ (Or.inr ⟨s, hs, i, j, rfl⟩)`.
-/
private theorem cond_eqs (Ψ : G →* Oˣ) (I : Subgroup G) {R : Type} [CommRing R] [Algebra O R] (r : G →* GG 3 R) :
    ∃ S : Set R, ∀ (C : Type) [CommRing C] [Algebra O C] (f : R →ₐ[O] C),
      Cond Ψ I (push f r) ↔ ∀ a ∈ S, f a = 0 := by
  let P : G → R[X] := fun s =>
    (r s).mat.charpoly - ∏ a, (X - Polynomial.C (algebraMap O R (UpperTheory.V.UnitaryThreeInertia.psi Ψ a s)))
  let M : (Fin 3 → G) → Matrix (Fin 3) (Fin 3) R := fun s =>
    ((r (s 0)).mat - Matrix.scalar _ (algebraMap O R (UpperTheory.V.UnitaryThreeInertia.psi Ψ 0 (s 0)))) *
        ((r (s 1)).mat - Matrix.scalar _ (algebraMap O R (UpperTheory.V.UnitaryThreeInertia.psi Ψ 1 (s 1)))) *
        ((r (s 2)).mat - Matrix.scalar _ (algebraMap O R (UpperTheory.V.UnitaryThreeInertia.psi Ψ 2 (s 2))))
  refine ⟨{a | (∃ s ∈ I, ∃ k, a = (P s).coeff k) ∨ ∃ s : Fin 3 → G, (∀ a, s a ∈ I) ∧ ∃ i j, a = M s i j},
    fun C _ _ f => ?_⟩
  have hm : ∀ s, (push f r s).mat = (f : R →+* C).mapMatrix (r s).mat := fun _ => rfl
  have hc : ∀ o, (f : R →+* C) (algebraMap O R o) = algebraMap O C o := f.commutes
  have hP : ∀ s, (P s).map (f : R →+* C) = (push f r s).mat.charpoly -
      ∏ a, (X - Polynomial.C (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ a s))) := fun s => by
    simp only [P, hm, RingHom.mapMatrix_apply, Matrix.charpoly_map, Polynomial.map_sub, Polynomial.map_prod,
      Polynomial.map_X, Polynomial.map_C, hc]
  have hM : ∀ s, (f : R →+* C).mapMatrix (M s) =
      ((push f r (s 0)).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ 0 (s 0)))) *
        ((push f r (s 1)).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ 1 (s 1)))) *
        ((push f r (s 2)).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ 2 (s 2)))) := fun s => by
    simp only [M, hm, map_mul, map_sub, scalar_map, hc]
  constructor
  · rintro ⟨h1, h2⟩ a (⟨s, hs, k, rfl⟩ | ⟨s, hs, i, j, rfl⟩)
    · have := hP s
      rw [h1 s hs, sub_self] at this
      simpa using congrArg (fun p => p.coeff k) this
    · have := hM s
      rw [h2 s hs] at this
      simpa using congrFun (congrFun this i) j
  · intro h
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · rw [← sub_eq_zero, ← hP]
      ext k
      simpa using h _ (Or.inl ⟨s, hs, k, rfl⟩)
    · rw [← hM]
      ext i j
      simpa using h _ (Or.inr ⟨s, hs, i, j, rfl⟩)

/- English proof (translation)
Use `⟨fun s hs => ?_, fun s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.charpoly_of_upperTriangular]`. Simplify using `only [hd s hs]`. Introduce `a b hab`. Apply `ht` to reduce the goal to its premises.

Establish `: (b : ℕ) < a` using `hab`. Simplify using `only [wt, wt1]`. Use linear arithmetic over natural numbers and integers. Establish `h10` using `fun g => ht g 1 0 (by decide)`. Establish `h20` using `fun g => ht g 2 0 (by decide)`.

Establish `h21` using `fun g => ht g 2 1 (by decide)`. Establish `e0` using `hd _ (hs 0) 0`. Establish `e1` using `hd _ (hs 1) 1`. Establish `e2` using `hd _ (hs 2) 2`. Use extensionality with `i j`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21, e0, e1, e2]`.
-/
private theorem cond_tri (Ψ : G →* Oˣ) (I : Subgroup G) {C : Type} [CommRing C] [Algebra O C] (u : G →* GG 3 C)
    (ht : ∀ g a b, wt a b < 0 → (u g).mat a b = 0)
    (hd : ∀ s ∈ I, ∀ a, (u s).mat a a = algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ a s)) : Cond Ψ I u := by
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · rw [Matrix.charpoly_of_upperTriangular]
    · simp only [hd s hs]
    · intro a b hab
      apply ht
      have : (b : ℕ) < a := hab
      simp only [wt, wt1]
      omega
  · have h10 := fun g => ht g 1 0 (by decide)
    have h20 := fun g => ht g 2 0 (by decide)
    have h21 := fun g => ht g 2 1 (by decide)
    have e0 := hd _ (hs 0) 0
    have e1 := hd _ (hs 1) 1
    have e2 := hd _ (hs 2) 2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21, e0, e1, e2]

/- English proof (translation)
Establish `hm : ∀ s ∈ I, (conjBy n u s).mat = (n : Matrix (Fin 3) (Fin 3) C) * (u s).mat * ((n⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)`. Introduce `s hs`. Establish `: (conjBy n u s).left = n * (u s).left * n⁻¹`. Simplify using `[conjBy, hu s hs]`. Simplify using `only [GG.mat, this, Units.val_mul]`.

Establish `hc : ∀ (A : Matrix (Fin 3) (Fin 3) C) (c : C), (n : Matrix (Fin 3) (Fin 3) C) * A * ((n⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) - Matrix.scalar _ c = (n : Matrix (Fin 3) (Fin 3) C) * (A - Matrix.scalar _ c) * ((n⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)`. Introduce `A c`. Rewrite using `[mul_sub, sub_mul, ← (Matrix.scalar_commute c (fun _ => Commute.all _ _) _).eq, mul_assoc (Matrix.scalar _ c), Units.mul_inv, mul_one]`. Use `⟨fun s hs => ?_, fun s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[hm s hs, ← h.1 s hs, Matrix.coe_units_inv, Matrix.charpoly_units_conj]`.

Rewrite using `[hm _ (hs 0), hm _ (hs 1), hm _ (hs 2), hc, hc, hc]`. Use `h.2 s hs` as an intermediate fact. Generalize the expression as in `(u (s 0)).mat - _ = A at *`. Generalize the expression as in `(u (s 1)).mat - _ = B at *`. Generalize the expression as in `(u (s 2)).mat - _ = D at *`.

Simplify using `only [mul_assoc, Units.inv_mul_cancel_left]`. Rewrite using `[← mul_assoc B, ← mul_assoc A, ← mul_assoc A, this, zero_mul, mul_zero]`.
-/
private theorem cond_conj (Ψ : G →* Oˣ) (I : Subgroup G) {C : Type} [CommRing C] [Algebra O C] (u : G →* GG 3 C)
    (hu : ∀ s ∈ I, (u s).right = 1) (n : GL (Fin 3) C) (h : Cond Ψ I u) : Cond Ψ I (conjBy n u) := by
  have hm : ∀ s ∈ I, (conjBy n u s).mat =
      (n : Matrix (Fin 3) (Fin 3) C) * (u s).mat * ((n⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
    intro s hs
    have : (conjBy n u s).left = n * (u s).left * n⁻¹ := by
      simp [conjBy, hu s hs]
    simp only [GG.mat, this, Units.val_mul]
  have hc : ∀ (A : Matrix (Fin 3) (Fin 3) C) (c : C),
      (n : Matrix (Fin 3) (Fin 3) C) * A * ((n⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) - Matrix.scalar _ c =
      (n : Matrix (Fin 3) (Fin 3) C) * (A - Matrix.scalar _ c) *
        ((n⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
    intro A c
    rw [mul_sub, sub_mul, ← (Matrix.scalar_commute c (fun _ => Commute.all _ _) _).eq, mul_assoc (Matrix.scalar _ c),
      Units.mul_inv, mul_one]
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · rw [hm s hs, ← h.1 s hs, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  · rw [hm _ (hs 0), hm _ (hs 1), hm _ (hs 2), hc, hc, hc]
    have := h.2 s hs
    generalize (u (s 0)).mat - _ = A at *
    generalize (u (s 1)).mat - _ = B at *
    generalize (u (s 2)).mat - _ = D at *
    simp only [mul_assoc, Units.inv_mul_cancel_left]
    rw [← mul_assoc B, ← mul_assoc A, ← mul_assoc A, this, zero_mul, mul_zero]

end

/- English proof (translation)
Establish `hi : Function.Injective (algebraMap ℤ_[l] O)`. Rewrite using `[RingHom.injective_iff_ker_eq_bot]`. Assume the negation of the conclusion as `h`. Establish `hp : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsPrime` using `inferInstance`. Establish `hm : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsMaximal` using `hp.isMaximal h`.

Establish `h2 : (⊥ : Ideal O).IsMaximal` using `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ_[l]) _ hm`. Conclude with `IsDiscreteValuationRing.not_a_field O (IsLocalRing.eq_maximalIdeal h2).symm`. Use `haveI : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 hi`. Establish `hi2 : Function.Injective (algebraMap ℤ_[l] (FractionRing O))`. Rewrite using `[IsScalarTower.algebraMap_eq ℤ_[l] O (FractionRing O)]`.

Conclude with `(IsFractionRing.injective O _).comp hi`. Use `letI : Algebra ℚ_[l] (FractionRing O) := (IsFractionRing.lift hi2).toAlgebra`. Use `haveI : IsScalarTower ℤ_[l] ℚ_[l] (FractionRing O) := IsScalarTower.of_algebraMap_eq fun x => (IsFractionRing.lift_algebraMap hi2 x).symm`. Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors ℤ_[l])) (FractionRing O) := inferInstance`. Conclude with `⟨inferInstance, inferInstance, Module.Finite.of_isLocalization ℤ_[l] O (nonZeroDivisors ℤ_[l])⟩`.
-/
private theorem frac_alg (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] :
    ∃ _ : Algebra ℚ_[l] (FractionRing O), IsScalarTower ℤ_[l] ℚ_[l] (FractionRing O) ∧
      Module.Finite ℚ_[l] (FractionRing O) := by
  have hi : Function.Injective (algebraMap ℤ_[l] O) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra h
    have hp : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsPrime := inferInstance
    have hm : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsMaximal := hp.isMaximal h
    have h2 : (⊥ : Ideal O).IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ_[l]) _ hm
    exact IsDiscreteValuationRing.not_a_field O (IsLocalRing.eq_maximalIdeal h2).symm
  haveI : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hi2 : Function.Injective (algebraMap ℤ_[l] (FractionRing O)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] O (FractionRing O)]
    exact (IsFractionRing.injective O _).comp hi
  letI : Algebra ℚ_[l] (FractionRing O) := (IsFractionRing.lift hi2).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] (FractionRing O) :=
    IsScalarTower.of_algebraMap_eq fun x => (IsFractionRing.lift_algebraMap hi2 x).symm
  haveI : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors ℤ_[l])) (FractionRing O) := inferInstance
  exact ⟨inferInstance, inferInstance,
    Module.Finite.of_isLocalization ℤ_[l] O (nonZeroDivisors ℤ_[l])⟩

/- English proof (translation)
Establish `hm : ∀ a : MvPowerSeries (Fin 12) E, a ∈ maximalIdeal _ ↔ MvPowerSeries.constantCoeff a = 0` using `fun a => by`. Rewrite using `[mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]`. Set `c : MvPowerSeries (Fin 12) E →ₐ[E] E` to `{ (MvPowerSeries.constantCoeff : MvPowerSeries (Fin 12) E →+* E) with commutes' := fun x => by simp [MvPowerSeries.algebraMap_apply] }`. Set `π` to `Ideal.Quotient.liftₐ (maximalIdeal (MvPowerSeries (Fin 12) E) ^ (n + 1)) c fun a ha => (hm a).1 (Ideal.pow_le_self n.succ_ne_zero ha)`. Establish `hπ : ∀ a, π (Ideal.Quotient.mk _ a) = MvPowerSeries.constantCoeff a` using `fun _ => rfl`.

Establish `hn : ∀ a, π a = 0 → IsNilpotent a`. Introduce `a ha`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Use `⟨n + 1, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `Ideal.pow_mem_pow ((hm a).2 ha) _`. Use `⟨π, hπ, hn, Module.finite_of_surjective_of_ker_le_nilradical π (fun x => ⟨algebraMap _ _ x, π.commutes x⟩) (fun a ha => hn a ha) (IsNoetherian.noetherian _)⟩` and prove the remaining obligations.
-/
private theorem trunc_data (E : Type) [Field E] (n : ℕ) :
    ∃ π : (MvPowerSeries (Fin 12) E ⧸ maximalIdeal (MvPowerSeries (Fin 12) E) ^ (n + 1)) →ₐ[E] E,
      (∀ a, π (Ideal.Quotient.mk _ a) = MvPowerSeries.constantCoeff a) ∧ (∀ a, π a = 0 → IsNilpotent a) ∧
      Module.Finite E (MvPowerSeries (Fin 12) E ⧸ maximalIdeal (MvPowerSeries (Fin 12) E) ^ (n + 1)) := by
  have hm : ∀ a : MvPowerSeries (Fin 12) E, a ∈ maximalIdeal _ ↔ MvPowerSeries.constantCoeff a = 0 := fun a => by
    rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]
  let c : MvPowerSeries (Fin 12) E →ₐ[E] E :=
    { (MvPowerSeries.constantCoeff : MvPowerSeries (Fin 12) E →+* E) with
      commutes' := fun x => by simp [MvPowerSeries.algebraMap_apply] }
  let π := Ideal.Quotient.liftₐ (maximalIdeal (MvPowerSeries (Fin 12) E) ^ (n + 1)) c
    fun a ha => (hm a).1 (Ideal.pow_le_self n.succ_ne_zero ha)
  have hπ : ∀ a, π (Ideal.Quotient.mk _ a) = MvPowerSeries.constantCoeff a := fun _ => rfl
  have hn : ∀ a, π a = 0 → IsNilpotent a := by
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨n + 1, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow ((hm a).2 ha) _
  refine ⟨π, hπ, hn, Module.finite_of_surjective_of_ker_le_nilradical π (fun x => ⟨algebraMap _ _ x, π.commutes x⟩)
    (fun a ha => hn a ha) (IsNoetherian.noetherian _)⟩

/- English proof (translation)
Introduce `hL l _ O _ _ _ _ _ _ _ D U C _ _ r hr`. Take `⟨f, rfl, hf⟩` from `hr`. Use `show Cond D.Ψ (Iq l) (push f U.r.hom)`. Take `⟨S, hS⟩` from `cond_eqs D.Ψ (Iq l) U.r.hom`. Take `⟨_, _, _⟩` from `frac_alg l O`.

Take `⟨x, hx, -⟩` from `univEx D U`. Take `⟨-, φ, hφ⟩` from `rtCompl hL D U (FractionRing O) x hx`. Use `(hS C f).2 fun a ha => hf ?_` and prove the remaining obligations. Rewrite using `[← hφ.ker, RingHom.mem_ker, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (MvPowerSeries (Fin 12) (FractionRing O))) (maximalIdeal.isMaximal _).ne_top, Ideal.mem_iInf]`. Introduce `n`.

Use `Ideal.pow_le_pow_right n.le_succ ?_` and prove the remaining obligations. Take `⟨π, hπ, hn, hfin⟩` from `trunc_data (FractionRing O) n`. Set `B` to `MvPowerSeries (Fin 12) (FractionRing O) ⧸ maximalIdeal (MvPowerSeries (Fin 12) (FractionRing O)) ^ (n + 1)`. Use `haveI : Module.Finite ℚ_[l] B := Module.Finite.trans (FractionRing O) B`. Set `g : U.R →ₐ[O] B` to `(Ideal.Quotient.mkₐ O _).comp φ`.

Establish `hon : D.On U (push g U.r.hom)` using `⟨g, rfl, fun y hy => by`. Rewrite `hy` using `[← hφ.ker, RingHom.mem_ker]`. Use `show Ideal.Quotient.mkₐ O _ (φ y) = 0`. Rewrite using `[hy, map_zero]⟩`. Take `⟨hc, -, hcr⟩` from `rtPoints hL D U B _ hon`.

Establish `hred : (GG.map (π : B →+* FractionRing O)).comp (push g U.r.hom) = D.rz (FractionRing O)`. Establish `e : (π : B →+* FractionRing O).comp (g : U.R →+* B) = (algebraMap O (FractionRing O)).comp (x : U.R →+* O)` using `RingHom.ext fun y => (hπ (φ y)).trans (hφ.const y)`. Unfold `Dat3.rz`. Rewrite using `[← show push x U.r.hom = r0 D.η D.Ψ from hx]`. Use `MonoidHom.ext fun s => ?_` and prove the remaining obligations.

Simplify using `only [push, MonoidHom.comp_apply, GG.map_map, e]`. Take `⟨u, m, hu, -, -, hum⟩` from `(ordEq hL D (FractionRing O) B π hn _).1 ⟨U.r.hasMult, hred, hc, hcr⟩`. Establish `hcond : Cond D.Ψ (Iq l) (push g U.r.hom)`. Rewrite using `[hum]`. Conclude with `cond_conj _ _ u (fun s hs => (hu.mult s).trans (D.η_unr s hs)) m (cond_tri _ _ u hu.tri (triDiag D (FractionRing O) B π hn u hu))`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 ((hS B g).1 hcond a ha)`.
-/
theorem UpperTheory.V.Loc.lemma2a :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ) (C : Type) [CommRing C] [Algebra O C] (r : GQ l →* GG 3 C), D.On U r → (∀ s ∈ Iq l, (r s).mat.charpoly = ∏ a, (X - Polynomial.C (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s)))) ∧ ∀ s : Fin 3 → GQ l, (∀ a, s a ∈ Iq l) → ((r (s 0)).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ 0 (s 0)))) * ((r (s 1)).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ 1 (s 1)))) * ((r (s 2)).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ 2 (s 2)))) = 0 := by
  intro hL l _ O _ _ _ _ _ _ _ D U C _ _ r hr
  obtain ⟨f, rfl, hf⟩ := hr
  show Cond D.Ψ (Iq l) (push f U.r.hom)
  obtain ⟨S, hS⟩ := cond_eqs D.Ψ (Iq l) U.r.hom
  obtain ⟨_, _, _⟩ := frac_alg l O
  obtain ⟨x, hx, -⟩ := univEx D U
  obtain ⟨-, φ, hφ⟩ := rtCompl hL D U (FractionRing O) x hx
  refine (hS C f).2 fun a ha => hf ?_
  rw [← hφ.ker, RingHom.mem_ker, ← Ideal.mem_bot,
    ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (MvPowerSeries (Fin 12) (FractionRing O)))
      (maximalIdeal.isMaximal _).ne_top, Ideal.mem_iInf]
  intro n
  refine Ideal.pow_le_pow_right n.le_succ ?_
  obtain ⟨π, hπ, hn, hfin⟩ := trunc_data (FractionRing O) n
  let B := MvPowerSeries (Fin 12) (FractionRing O) ⧸ maximalIdeal (MvPowerSeries (Fin 12) (FractionRing O)) ^ (n + 1)
  haveI : Module.Finite ℚ_[l] B := Module.Finite.trans (FractionRing O) B
  let g : U.R →ₐ[O] B := (Ideal.Quotient.mkₐ O _).comp φ
  have hon : D.On U (push g U.r.hom) := ⟨g, rfl, fun y hy => by
    rw [← hφ.ker, RingHom.mem_ker] at hy
    show Ideal.Quotient.mkₐ O _ (φ y) = 0
    rw [hy, map_zero]⟩
  obtain ⟨hc, -, hcr⟩ := rtPoints hL D U B _ hon
  have hred : (GG.map (π : B →+* FractionRing O)).comp (push g U.r.hom) = D.rz (FractionRing O) := by
    have e : (π : B →+* FractionRing O).comp (g : U.R →+* B) =
        (algebraMap O (FractionRing O)).comp (x : U.R →+* O) := RingHom.ext fun y => (hπ (φ y)).trans (hφ.const y)
    unfold Dat3.rz
    rw [← show push x U.r.hom = r0 D.η D.Ψ from hx]
    refine MonoidHom.ext fun s => ?_
    simp only [push, MonoidHom.comp_apply, GG.map_map, e]
  obtain ⟨u, m, hu, -, -, hum⟩ := (ordEq hL D (FractionRing O) B π hn _).1 ⟨U.r.hasMult, hred, hc, hcr⟩
  have hcond : Cond D.Ψ (Iq l) (push g U.r.hom) := by
    rw [hum]
    exact cond_conj _ _ u (fun s hs => (hu.mult s).trans (D.η_unr s hs)) m
      (cond_tri _ _ u hu.tri (triDiag D (FractionRing O) B π hn u hu))
  exact Ideal.Quotient.eq_zero_iff_mem.1 ((hS B g).1 hcond a ha)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub

open scoped TensorProduct

namespace GlobalTheory.SplittingIdempotents

open GlobalTheory.EigenSplit

/- English proof (translation)
Set `F : R ⊗[ℤ] A →ₐ[R] (Unit → R)` to `splitMap (fun _ : Unit => χ)`. Establish `h1 : ∑ i, F (idem h i) () = 1`. Rewrite using `[← Finset.sum_apply, ← map_sum, (completeOrthogonalIdempotents_idem h).complete, map_one]`. Both sides reduce to the same expression. Take `⟨i, -, hi⟩` from `Finset.exists_ne_zero_of_sum_ne_zero (h1 ▸ one_ne_zero : ∑ i, F (idem h i) () ≠ 0)`.

Use `⟨i, RingHom.ext fun a => ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg (fun t => F t ()) (one_tmul_mul_idem h i a)`. Simplify using `only [map_mul, map_smul, Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at h2`. Establish `h3 : F (1 ⊗ₜ a) () = χ a` using `by simp [F]`. Rewrite `h2` using `[h3]`.

Conclude with `(mul_right_cancel₀ hi h2).symm`.
-/
private theorem exists_eq_of_isSplitting {A R ι : Type} [CommRing A] [CommRing R] [IsDomain R]
    [Fintype ι] {σ : ι → A →+* R} (h : IsSplitting σ) (χ : A →+* R) : ∃ i, σ i = χ := by
  classical
  let F : R ⊗[ℤ] A →ₐ[R] (Unit → R) := splitMap (fun _ : Unit => χ)
  have h1 : ∑ i, F (idem h i) () = 1 := by
    rw [← Finset.sum_apply, ← map_sum, (completeOrthogonalIdempotents_idem h).complete, map_one]
    rfl
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h1 ▸ one_ne_zero :
    ∑ i, F (idem h i) () ≠ 0)
  refine ⟨i, RingHom.ext fun a => ?_⟩
  have h2 := congrArg (fun t => F t ()) (one_tmul_mul_idem h i a)
  simp only [map_mul, map_smul, Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at h2
  have h3 : F (1 ⊗ₜ a) () = χ a := by simp [F]
  rw [h3] at h2
  exact (mul_right_cancel₀ hi h2).symm

/- English proof (translation)
Establish `: IsScalarTower ℤ OE K` using `AddCommGroup.intIsScalarTower`. Establish `: IsLocalization (Algebra.algebraMapSubmonoid OE (nonZeroDivisors ℤ)) K` using `inferInstance`. Use `set b := Module.Free.chooseBasis ℤ OE with hb`. Set `bK` to `b.localizationLocalization ℚ (nonZeroDivisors ℤ) K`. Establish `: Module.Finite ℚ K` using `Module.Finite.of_basis bK`.

Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ OE) = Fintype.card (K →ₐ[ℚ] C)`. Rewrite using `[AlgHom.card, Module.finrank_eq_card_basis bK]`. Set `e` to `Fintype.equivOfCardEq hcard`. Establish `h1` using `Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ C bK e`. Rewrite `h1` using `[Algebra.discr_localizationLocalization]`.

Establish `hent : ∀ j a, ∃ r : R, algebraMap R C r = e j (algebraMap OE K a)`. Introduce `j a`. Apply `hv.exists_of_le_one` to reduce the goal to its premises. Apply `hv.mem_of_integral` to reduce the goal to its premises. Establish `: IsIntegral ℤ (e j (algebraMap OE K a))` using `(Algebra.IsIntegral.isIntegral (R := ℤ) a).map ((e j).toRingHom.comp (algebraMap OE K)).toIntAlgHom`.

Conclude with `this.tower_top`. Use `choose N hN using hent`. Set `σ : Module.Free.ChooseBasisIndex ℤ OE → OE →+* R` to `fun j => { toFun := N j map_one' := hv.hom_inj (by simp [hN]) map_mul' := fun x y => hv.hom_inj (by simp [hN]) map_zero' := hv.hom_inj (by simp [hN]) map_add' := fun x y => hv.hom_inj (by simp [hN]) }`. Use `⟨σ, ?_⟩` and prove the remaining obligations. Establish `hM : Algebra.embeddingsMatrixReindex ℚ C bK e = (algebraMap R C).mapMatrix (Matrix.of fun i j => σ i (b j)).transpose`.

Use extensionality with `i j`. Simplify using `[Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, hN, bK, σ]`. Rewrite `h1` using `[hM, ← RingHom.map_det, ← map_pow, Matrix.det_transpose]`. Apply `hv.hom_inj` to reduce the goal to its premises. Rewrite using `[← h1]`.

Simplify using the standard rewrite rules.
-/
private theorem exists_det_sq (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE]
    [Module.Free ℤ OE] [Module.Finite ℤ OE] [DecidableEq (Module.Free.ChooseBasisIndex ℤ OE)]
    (K : Type) [Field K] [CharZero K] [Algebra OE K] [IsFractionRing OE K]
    (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (R : Type) [CommRing R] [Algebra R C] (hv : v.Integers R) :
    ∃ σ : Module.Free.ChooseBasisIndex ℤ OE → OE →+* R,
      ((Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE) : ℤ) : R) =
        (Matrix.of fun i j => σ i (Module.Free.chooseBasis ℤ OE j)).det ^ 2 := by
  have : IsScalarTower ℤ OE K := AddCommGroup.intIsScalarTower
  have : IsLocalization (Algebra.algebraMapSubmonoid OE (nonZeroDivisors ℤ)) K := inferInstance
  set b := Module.Free.chooseBasis ℤ OE with hb
  let bK := b.localizationLocalization ℚ (nonZeroDivisors ℤ) K
  have : Module.Finite ℚ K := Module.Finite.of_basis bK
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ OE) = Fintype.card (K →ₐ[ℚ] C) := by
    rw [AlgHom.card, Module.finrank_eq_card_basis bK]
  let e := Fintype.equivOfCardEq hcard
  have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ C bK e
  rw [Algebra.discr_localizationLocalization] at h1
  have hent : ∀ j a, ∃ r : R, algebraMap R C r = e j (algebraMap OE K a) := by
    intro j a
    apply hv.exists_of_le_one
    apply hv.mem_of_integral
    have : IsIntegral ℤ (e j (algebraMap OE K a)) :=
      (Algebra.IsIntegral.isIntegral (R := ℤ) a).map
        ((e j).toRingHom.comp (algebraMap OE K)).toIntAlgHom
    exact this.tower_top
  choose N hN using hent
  let σ : Module.Free.ChooseBasisIndex ℤ OE → OE →+* R := fun j =>
    { toFun := N j
      map_one' := hv.hom_inj (by simp [hN])
      map_mul' := fun x y => hv.hom_inj (by simp [hN])
      map_zero' := hv.hom_inj (by simp [hN])
      map_add' := fun x y => hv.hom_inj (by simp [hN]) }
  refine ⟨σ, ?_⟩
  have hM : Algebra.embeddingsMatrixReindex ℚ C bK e =
      (algebraMap R C).mapMatrix (Matrix.of fun i j => σ i (b j)).transpose := by
    ext i j
    simp [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, hN, bK, σ]
  rw [hM, ← RingHom.map_det, ← map_pow, Matrix.det_transpose] at h1
  apply hv.hom_inj
  rw [← h1]
  simp

/- English proof (translation)
Take `⟨σ, hσ⟩` from `exists_det_sq OE (FractionRing OE) C v O hv`. Use `⟨σ, (isSplitting_iff_isUnit_det σ (Module.Free.chooseBasis ℤ OE)).2 ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hdet`. Establish `hdm : ((Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE) : ℤ) : O) ∈ IsLocalRing.maximalIdeal O`. Rewrite using `[hσ]`.

Conclude with `Ideal.pow_mem_of_mem _ (by exact hdet) 2 (by norm_num)`. Establish `hpm : (p : O) ∈ IsLocalRing.maximalIdeal O` using `hp`. Establish `hcop : IsCoprime (p : ℤ) (Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE))` using `(Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.1 Fact.out)).2 hd`. Take `⟨a, b, hab⟩` from `hcop`. Establish `h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O`.

Use `congrArg (Int.cast : ℤ → O) hab` as an intermediate fact. Move the coercions through the operations in `at this`. Rewrite using `[← this]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpm) (Ideal.mul_mem_left _ _ hdm)`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1)`.
-/
private theorem exists_isSplitting (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    (hv : v.Integers O) (hp : ¬IsUnit (p : O)) [IsLocalRing O] (OE : Type) [CommRing OE]
    [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE]
    (hd : ¬ ((p : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE))) :
    ∃ σ : Module.Free.ChooseBasisIndex ℤ OE → OE →+* O, IsSplitting σ := by
  classical
  obtain ⟨σ, hσ⟩ := exists_det_sq OE (FractionRing OE) C v O hv
  refine ⟨σ, (isSplitting_iff_isUnit_det σ (Module.Free.chooseBasis ℤ OE)).2 ?_⟩
  by_contra hdet
  have hdm : ((Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE) : ℤ) : O) ∈
      IsLocalRing.maximalIdeal O := by
    rw [hσ]
    exact Ideal.pow_mem_of_mem _ (by exact hdet) 2 (by norm_num)
  have hpm : (p : O) ∈ IsLocalRing.maximalIdeal O := hp
  have hcop : IsCoprime (p : ℤ) (Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE)) :=
    (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.1 Fact.out)).2 hd
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    have := congrArg (Int.cast : ℤ → O) hab
    push_cast at this
    rw [← this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpm) (Ideal.mul_mem_left _ _ hdm)
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ hv hp _ _ OE _ _ _ _ _ hd`. Take `⟨σ, hσ⟩` from `exists_isSplitting p C v O hv hp.out OE hd`. Establish `: IsDomain O` using `hv.hom_inj.isDomain`. Set `ι` to `Module.Free.ChooseBasisIndex ℤ OE`. Set `k` to `IsLocalRing.ResidueField O`.

Set `r : O →+* k` to `IsLocalRing.residue O`. Establish `hσk : IsSplitting (fun i => r.comp (σ i))` using `hσ.map r`. Establish `hinj` using `hσk.injective`. Establish `hpk : (p : k) = 0`. Rewrite using `[← map_natCast r]`.

Conclude with `(IsLocalRing.residue_eq_zero_iff _).2 hp.out`. Establish `: CharP k p` using `(CharP.charP_iff_prime_eq_zero Fact.out).2 hpk`. Establish `hbij : Function.Bijective σ` using `⟨hσ.injective, fun χ => exists_eq_of_isSplitting hσ χ⟩`. Use `choose f hf using fun i => exists_eq_of_isSplitting hσk ((frobenius k p).comp (r.comp (σ i)))`. Establish `hfi : Function.Injective f`.

Introduce `i j hij`. Apply `hinj` to reduce the goal to its premises. Use extensionality with `a`. Apply `frobenius_inj k p` to reduce the goal to its premises. Establish `h1` using `DFunLike.congr_fun (hf i) a`.

Establish `h2` using `DFunLike.congr_fun (hf j) a`. Rewrite `h1` using `[hij]`. Conclude with `h1.symm.trans h2`. Set `φ : Equiv.Perm ι` to `Equiv.ofBijective f (Finite.injective_iff_bijective.1 hfi)`. Set `e : Fin (Fintype.card ι) ≃ ι` to `(Fintype.equivFin ι).symm`.

Use `⟨Fintype.card ι, e.trans (Equiv.ofBijective σ hbij), idem hσ ∘ e, (e.trans φ).trans e.symm, ?_, fun i a => ?_, fun i j hij => ?_, fun i a => ?_⟩` and prove the remaining obligations. Conclude with `(CompleteOrthogonalIdempotents.equiv e).2 (completeOrthogonalIdempotents_idem hσ)`. Conclude with `one_tmul_mul_idem hσ (e i) a`. Assume the negation of the conclusion as `hne push Not at hne`. Apply `hij` to reduce the goal to its premises.

Apply `e.injective` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises. Use extensionality with `a`. Conclude with `Ideal.Quotient.eq.2 (hne a)`. Establish `h1` using `DFunLike.congr_fun (hf (e i)) a`.

Simplify using `only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.ofBijective_apply, φ]`. Apply `Ideal.Quotient.eq.1` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `r _ = r _`. Rewrite using `[map_pow]`. Conclude with `h1`.
-/
theorem exists_splitting_idempotents_frobenius : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsLocalRing O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE], ¬ ((p : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE)) → ∃ (m : ℕ) (τ : Fin m ≃ (OE →+* O)) (ε : Fin m → O ⊗[ℤ] OE) (φ : Equiv.Perm (Fin m)), CompleteOrthogonalIdempotents ε ∧ (∀ i a, (1 ⊗ₜ[ℤ] a) * ε i = τ i a • ε i) ∧ (∀ i j, i ≠ j → ∃ a, IsUnit (τ i a - τ j a)) ∧ ∀ i a, τ (φ i) a - τ i a ^ p ∈ IsLocalRing.maximalIdeal O := by
  intro p _ C _ _ _ v O _ _ hv hp _ _ OE _ _ _ _ _ hd
  classical
  obtain ⟨σ, hσ⟩ := exists_isSplitting p C v O hv hp.out OE hd
  have : IsDomain O := hv.hom_inj.isDomain
  let ι := Module.Free.ChooseBasisIndex ℤ OE
  let k := IsLocalRing.ResidueField O
  let r : O →+* k := IsLocalRing.residue O
  have hσk : IsSplitting (fun i => r.comp (σ i)) := hσ.map r
  have hinj := hσk.injective
  have hpk : (p : k) = 0 := by
    rw [← map_natCast r]
    exact (IsLocalRing.residue_eq_zero_iff _).2 hp.out
  have : CharP k p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hpk
  have hbij : Function.Bijective σ :=
    ⟨hσ.injective, fun χ => exists_eq_of_isSplitting hσ χ⟩
  choose f hf using fun i => exists_eq_of_isSplitting hσk ((frobenius k p).comp (r.comp (σ i)))
  have hfi : Function.Injective f := by
    intro i j hij
    apply hinj
    ext a
    apply frobenius_inj k p
    have h1 := DFunLike.congr_fun (hf i) a
    have h2 := DFunLike.congr_fun (hf j) a
    rw [hij] at h1
    exact h1.symm.trans h2
  let φ : Equiv.Perm ι := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hfi)
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, e.trans (Equiv.ofBijective σ hbij), idem hσ ∘ e,
    (e.trans φ).trans e.symm, ?_, fun i a => ?_, fun i j hij => ?_, fun i a => ?_⟩
  · exact (CompleteOrthogonalIdempotents.equiv e).2 (completeOrthogonalIdempotents_idem hσ)
  · exact one_tmul_mul_idem hσ (e i) a
  · by_contra hne
    push Not at hne
    apply hij
    apply e.injective
    apply hinj
    ext a
    exact Ideal.Quotient.eq.2 (hne a)
  · have h1 := DFunLike.congr_fun (hf (e i)) a
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.ofBijective_apply, φ]
    apply Ideal.Quotient.eq.1
    change r _ = r _
    rw [map_pow]
    exact h1

end GlobalTheory.SplittingIdempotents

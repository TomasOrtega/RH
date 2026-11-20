import Mathlib
open TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `S A C _ _ _ _ _ u _ Q₁ _ hle h2`. Set `p` to `u.comap (algebraMap A (A ⊗[S] C))`. Set `p₁` to `u.comap (algebraMap S (A ⊗[S] C))`. Establish `hp : p₁ = p.comap (algebraMap S A)`. Simplify using `only [p, p₁, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]`.

Set `K₁` to `p₁.ResidueField`. Set `K` to `p.ResidueField`. Use `letI : Algebra K₁ K := (Ideal.ResidueField.mapₐ p₁ p (Algebra.ofId S A) hp).toAlgebra`. Use `haveI : IsScalarTower S K₁ K := IsScalarTower.of_algebraMap_eq (fun s => ((Ideal.ResidueField.mapₐ p₁ p (Algebra.ofId S A) hp).commutes s).symm)`. Set `F₁` to `p₁.Fiber C`.

Set `E` to `F₁ ⊗[K₁] K`. Set `e1 : p.Fiber (A ⊗[S] C) ≃ₐ[K] K ⊗[S] C` to `Algebra.TensorProduct.cancelBaseChange S A K K C`. Set `e2 : K ⊗[K₁] F₁ ≃ₐ[K] K ⊗[S] C` to `Algebra.TensorProduct.cancelBaseChange S K₁ K K C`. Set `e3 : K ⊗[K₁] F₁ ≃ₐ[K₁] E` to `Algebra.TensorProduct.comm K₁ K F₁`. Use `haveI : Module.Flat F₁ E := inferInstance`.

Use `haveI : Algebra.HasGoingDown F₁ E := inferInstance`. Set `Φ : p.Fiber (A ⊗[S] C) ≃+* E` to `(e1.toRingEquiv.trans e2.symm.toRingEquiv).trans e3.toRingEquiv`. Establish `hΦ : ∀ c : C, Φ (Algebra.TensorProduct.includeRight (Algebra.TensorProduct.includeRight c : A ⊗[S] C)) = algebraMap F₁ E (Algebra.TensorProduct.includeRight c)`. Introduce `c`. Simplify using `only [Φ, e1, e2, e3, Algebra.TensorProduct.includeRight_apply, RingEquiv.trans_apply, AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]`.

Use `erw [Algebra.TensorProduct.cancelBaseChange_symm_tmul]`. Both sides reduce to the same expression. Use `haveI : u.LiesOver p := ⟨rfl⟩`. Set `isoA` to `PrimeSpectrum.primesOverOrderIsoFiber A (A ⊗[S] C) p`. Set `ub` to `isoA ⟨u, inferInstance, inferInstance⟩`.

Establish `hub : ub.asIdeal.comap (Algebra.TensorProduct.includeRight : A ⊗[S] C →ₐ[A] p.Fiber (A ⊗[S] C)) = u`. Use `congrArg Subtype.val (isoA.symm_apply_apply ⟨u, inferInstance, inferInstance⟩)` as an intermediate fact. Conclude with `this`. Establish `hmem : ∀ y : A ⊗[S] C, (Algebra.TensorProduct.includeRight : A ⊗[S] C →ₐ[A] p.Fiber (A ⊗[S] C)) y ∈ ub.asIdeal ↔ y ∈ u` using `fun y => Iff.of_eq (congrArg (y ∈ ·) hub)`. Use `haveI : Q₁.LiesOver p₁ := ⟨h2.symm⟩`.

Set `iso₁` to `PrimeSpectrum.primesOverOrderIsoFiber S C p₁`. Set `Qb` to `iso₁ ⟨Q₁, inferInstance, inferInstance⟩`. Establish `hQb : Qb.asIdeal.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] F₁) = Q₁`. Use `congrArg Subtype.val (iso₁.symm_apply_apply ⟨Q₁, inferInstance, inferInstance⟩)` as an intermediate fact. Conclude with `this`.

Set `ue : Ideal E` to `ub.asIdeal.comap (Φ.symm : E →+* p.Fiber (A ⊗[S] C))`. Use `haveI : ue.IsPrime := Ideal.comap_isPrime _ _`. Set `w : Ideal F₁` to `ue.comap (algebraMap F₁ E)`. Use `haveI : w.IsPrime := Ideal.comap_isPrime _ _`. Use `haveI : ue.LiesOver w := ⟨rfl⟩`.

Establish `hw : w.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] F₁) = u.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] A ⊗[S] C)`. Use extensionality with `c`. Express the relevant statement in the definitionally equal form `Φ.symm (algebraMap F₁ E (Algebra.TensorProduct.includeRight c)) ∈ ub.asIdeal ↔ _`. Rewrite using `[← hΦ, RingEquiv.symm_apply_apply]`. Conclude with `hmem _`.

Establish `hwle : Qb.asIdeal ≤ w`. Set `u₁` to `u.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] A ⊗[S] C)`. Use `haveI : u₁.IsPrime := Ideal.comap_isPrime _ _`. Use `haveI : u₁.LiesOver p₁ := ⟨by show p₁ = u₁.comap (algebraMap S C)`. Use extensionality with `s`.

Simplify using `[u₁, p₁]⟩`. Set `wP : PrimeSpectrum F₁` to `⟨w, inferInstance⟩`. Establish `hsym : (iso₁.symm wP).1 = u₁` using `hw`. Establish `key : iso₁.symm Qb ≤ iso₁.symm wP` using `by show (iso₁.symm Qb).1 ≤ (iso₁.symm wP).1`. Rewrite using `[hsym, iso₁.symm_apply_apply]`.

Conclude with `hle`. Conclude with `(iso₁.symm.le_iff_le.mp key : Qb ≤ wP)`. Take `⟨P, hPle, hPprime, hPover⟩` from `Ideal.exists_ideal_le_liesOver_of_le (p := Qb.asIdeal) (q := w) ue hwle`. Use `⟨(P.comap (Φ : p.Fiber (A ⊗[S] C) →+* E)).comap (Algebra.TensorProduct.includeRight : A ⊗[S] C →ₐ[A] p.Fiber (A ⊗[S] C)), inferInstance, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Rewrite using `[← hmem]`. Use `hPle hx` as an intermediate fact. Simplify `this` using `[ue]`. Use extensionality with `c`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap]`.

Use `erw [hΦ c]`. Rewrite using `[← hQb, Ideal.mem_comap, ← Ideal.mem_comap, ← Ideal.under_def, ← hPover.over]`. Use extensionality with `a`. Set `J : Ideal K` to `(P.comap (Φ : p.Fiber (A ⊗[S] C) →+* E)).comap (algebraMap K (p.Fiber (A ⊗[S] C)))`. Use `haveI : J.IsPrime := Ideal.comap_isPrime _ _`.

Establish `hJ : J = ⊥` using `Ideal.eq_bot_of_prime J`. Establish `hx : (Algebra.TensorProduct.includeRight : A ⊗[S] C →ₐ[A] p.Fiber (A ⊗[S] C)) (algebraMap A (A ⊗[S] C) a) = algebraMap K (p.Fiber (A ⊗[S] C)) (algebraMap A K a)`. Rewrite using `[AlgHom.commutes, ← IsScalarTower.algebraMap_apply]`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, hx]`. Express the relevant statement in the definitionally equal form `algebraMap A K a ∈ J ↔ _`.

Rewrite using `[hJ, Ideal.mem_bot, Ideal.algebraMap_residueField_eq_zero]`.
-/
theorem fibre_going_down_tensor : ∀ (S A C : Type) [CommRing S] [CommRing A] [CommRing C] [Algebra S A] [Algebra S C]
    (u : Ideal (TensorProduct S A C)) [u.IsPrime] (Q₁ : Ideal C) [Q₁.IsPrime],
    Q₁ ≤ u.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] TensorProduct S A C) →
    Q₁.comap (algebraMap S C) = u.comap (algebraMap S (TensorProduct S A C)) →
    ∃ Q : Ideal (TensorProduct S A C), Q.IsPrime ∧ Q ≤ u ∧
      Q.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] TensorProduct S A C) = Q₁ ∧
      Q.comap (algebraMap A (TensorProduct S A C)) = u.comap (algebraMap A (TensorProduct S A C)) := by
  intro S A C _ _ _ _ _ u _ Q₁ _ hle h2
  let p := u.comap (algebraMap A (A ⊗[S] C))
  let p₁ := u.comap (algebraMap S (A ⊗[S] C))
  have hp : p₁ = p.comap (algebraMap S A) := by
    simp only [p, p₁, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  let K₁ := p₁.ResidueField
  let K := p.ResidueField
  letI : Algebra K₁ K := (Ideal.ResidueField.mapₐ p₁ p (Algebra.ofId S A) hp).toAlgebra
  haveI : IsScalarTower S K₁ K := IsScalarTower.of_algebraMap_eq
    (fun s => ((Ideal.ResidueField.mapₐ p₁ p (Algebra.ofId S A) hp).commutes s).symm)
  let F₁ := p₁.Fiber C
  let E := F₁ ⊗[K₁] K
  let e1 : p.Fiber (A ⊗[S] C) ≃ₐ[K] K ⊗[S] C := Algebra.TensorProduct.cancelBaseChange S A K K C
  let e2 : K ⊗[K₁] F₁ ≃ₐ[K] K ⊗[S] C := Algebra.TensorProduct.cancelBaseChange S K₁ K K C
  let e3 : K ⊗[K₁] F₁ ≃ₐ[K₁] E := Algebra.TensorProduct.comm K₁ K F₁
  haveI : Module.Flat F₁ E := inferInstance
  haveI : Algebra.HasGoingDown F₁ E := inferInstance
  let Φ : p.Fiber (A ⊗[S] C) ≃+* E :=
    (e1.toRingEquiv.trans e2.symm.toRingEquiv).trans e3.toRingEquiv
  have hΦ : ∀ c : C, Φ (Algebra.TensorProduct.includeRight (Algebra.TensorProduct.includeRight c : A ⊗[S] C))
      = algebraMap F₁ E (Algebra.TensorProduct.includeRight c) := by
    intro c
    simp only [Φ, e1, e2, e3, Algebra.TensorProduct.includeRight_apply, RingEquiv.trans_apply,
      AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
    erw [Algebra.TensorProduct.cancelBaseChange_symm_tmul]
    rfl

  haveI : u.LiesOver p := ⟨rfl⟩
  let isoA := PrimeSpectrum.primesOverOrderIsoFiber A (A ⊗[S] C) p
  let ub := isoA ⟨u, inferInstance, inferInstance⟩
  have hub : ub.asIdeal.comap (Algebra.TensorProduct.includeRight : A ⊗[S] C →ₐ[A] p.Fiber (A ⊗[S] C)) = u := by
    have := congrArg Subtype.val (isoA.symm_apply_apply ⟨u, inferInstance, inferInstance⟩)
    exact this
  have hmem : ∀ y : A ⊗[S] C, (Algebra.TensorProduct.includeRight : A ⊗[S] C →ₐ[A] p.Fiber (A ⊗[S] C)) y
      ∈ ub.asIdeal ↔ y ∈ u := fun y => Iff.of_eq (congrArg (y ∈ ·) hub)

  haveI : Q₁.LiesOver p₁ := ⟨h2.symm⟩
  let iso₁ := PrimeSpectrum.primesOverOrderIsoFiber S C p₁
  let Qb := iso₁ ⟨Q₁, inferInstance, inferInstance⟩
  have hQb : Qb.asIdeal.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] F₁) = Q₁ := by
    have := congrArg Subtype.val (iso₁.symm_apply_apply ⟨Q₁, inferInstance, inferInstance⟩)
    exact this

  let ue : Ideal E := ub.asIdeal.comap (Φ.symm : E →+* p.Fiber (A ⊗[S] C))
  haveI : ue.IsPrime := Ideal.comap_isPrime _ _
  let w : Ideal F₁ := ue.comap (algebraMap F₁ E)
  haveI : w.IsPrime := Ideal.comap_isPrime _ _
  haveI : ue.LiesOver w := ⟨rfl⟩
  have hw : w.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] F₁) =
      u.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] A ⊗[S] C) := by
    ext c
    change Φ.symm (algebraMap F₁ E (Algebra.TensorProduct.includeRight c)) ∈ ub.asIdeal ↔ _
    rw [← hΦ, RingEquiv.symm_apply_apply]
    exact hmem _
  have hwle : Qb.asIdeal ≤ w := by
    let u₁ := u.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] A ⊗[S] C)
    haveI : u₁.IsPrime := Ideal.comap_isPrime _ _
    haveI : u₁.LiesOver p₁ := ⟨by
      show p₁ = u₁.comap (algebraMap S C)
      ext s
      simp [u₁, p₁]⟩
    let wP : PrimeSpectrum F₁ := ⟨w, inferInstance⟩
    have hsym : (iso₁.symm wP).1 = u₁ := hw
    have key : iso₁.symm Qb ≤ iso₁.symm wP := by
      show (iso₁.symm Qb).1 ≤ (iso₁.symm wP).1
      rw [hsym, iso₁.symm_apply_apply]
      exact hle
    exact (iso₁.symm.le_iff_le.mp key : Qb ≤ wP)
  obtain ⟨P, hPle, hPprime, hPover⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := Qb.asIdeal) (q := w) ue hwle
  refine ⟨(P.comap (Φ : p.Fiber (A ⊗[S] C) →+* E)).comap
    (Algebra.TensorProduct.includeRight : A ⊗[S] C →ₐ[A] p.Fiber (A ⊗[S] C)), inferInstance, ?_, ?_, ?_⟩
  · intro x hx
    rw [← hmem]
    have := hPle hx
    simpa [ue] using this
  · ext c
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap]
    erw [hΦ c]
    rw [← hQb, Ideal.mem_comap, ← Ideal.mem_comap, ← Ideal.under_def, ← hPover.over]
  · ext a
    let J : Ideal K := (P.comap (Φ : p.Fiber (A ⊗[S] C) →+* E)).comap (algebraMap K (p.Fiber (A ⊗[S] C)))
    haveI : J.IsPrime := Ideal.comap_isPrime _ _
    have hJ : J = ⊥ := Ideal.eq_bot_of_prime J
    have hx : (Algebra.TensorProduct.includeRight : A ⊗[S] C →ₐ[A] p.Fiber (A ⊗[S] C))
        (algebraMap A (A ⊗[S] C) a) = algebraMap K (p.Fiber (A ⊗[S] C)) (algebraMap A K a) := by
      rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
    rw [Ideal.mem_comap, Ideal.mem_comap, hx]
    change algebraMap A K a ∈ J ↔ _
    rw [hJ, Ideal.mem_bot, Ideal.algebraMap_residueField_eq_zero]

end GlobalTheory

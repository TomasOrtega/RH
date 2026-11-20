import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresGr
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.GrMIff

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section Av

variable {O C' C : Type} [CommRing O] [CommRing C'] [Algebra O C'] [CommRing C] [Algebra O C]

private def av (h : O) (σ' : C' →ₐ[O] C') (j : ZMod 2) (x : C') : C' := h • (x + sg C' j * σ' x)

/- English proof (translation)
Simplify using `[sg]`.
-/
private theorem sg_map (p : C' →ₐ[O] C) (j : ZMod 2) : p (sg C' j) = sg C j := by
  simp [sg]

/- English proof (translation)
Simplify using `[av]`.
-/
private theorem av_zero (h : O) (σ' : C' →ₐ[O] C') (j : ZMod 2) : av h σ' j 0 = 0 := by
  simp [av]

variable [IsLocalRing O] [IsCO O C']

variable [IsCO O C]

end Av

/- English proof (translation)
Take `rfl | rfl : j = 0 ∨ j = 1` from `by revert j; decide`. Apply the tactic sequence `all_goals obtain rfl | rfl : k = 0 ∨ k = 1 := by revert k; decide`. Apply the tactic sequence `all_goals simp [sg, show (0:ZMod 2) - 1 = 1 from rfl, show (1:ZMod 2) - 1 = 0 from rfl, ZMod.val_one]`.
-/
private theorem sg_sub_eq_mul {R : Type} [CommRing R] (j k : ZMod 2) : sg R (j - k) = sg R j * sg R k := by
  obtain rfl | rfl : j = 0 ∨ j = 1 := by revert j; decide
  all_goals obtain rfl | rfl : k = 0 ∨ k = 1 := by revert k; decide
  all_goals simp [sg, show (0:ZMod 2) - 1 = 1 from rfl, show (1:ZMod 2) - 1 = 0 from rfl, ZMod.val_one]

/- English proof (translation)
Unfold `sg`. Rewrite using `[← pow_add, ← two_mul, pow_mul]`. Simplify using the standard rewrite rules.
-/
private theorem sg_mul_self_eq_one {R : Type} [CommRing R] (j : ZMod 2) : sg R j * sg R j = 1 := by
  unfold sg
  rw [← pow_add, ← two_mul, pow_mul]
  simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hM`. Use extensionality with `a b`. Establish `e : σ (M a b) = sg R (α a - β b) * M a b` using `hM a b`. Simplify using `only [Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, e, sg_sub_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `hM a b`. Establish `e` using `congrFun (congrFun hM a) b`. Simplify using `only [Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] at e`. Use `show σ (M a b) = sg R (α a - β b) * M a b`.

Rewrite using `[e, sg_sub_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem grM_iff_map_eq_diagonal_mul_mul_diagonal {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β : Fin 3 → ZMod 2) (M : Matrix (Fin 3) (Fin 3) R) :
    GrM σ α β M ↔ M.map σ = Matrix.diagonal (fun a => sg R (α a)) * M * Matrix.diagonal (fun b => sg R (β b)) := by
  constructor
  · intro hM
    ext a b
    have e : σ (M a b) = sg R (α a - β b) * M a b := hM a b
    simp only [Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, e, sg_sub_eq_mul]
    ring
  · intro hM a b
    have e := congrFun (congrFun hM a) b
    simp only [Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
    show σ (M a b) = sg R (α a - β b) * M a b
    rw [e, sg_sub_eq_mul]
    ring

/- English proof (translation)
Rewrite using `[← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]`. Simplify using `only [sg_mul_self_eq_one]`. Rewrite using `[Matrix.diagonal_one, Matrix.one_mul]`.
-/
private theorem diagonal_sg_mul_diagonal_sg_mul_cancel {R : Type} [CommRing R] (α : Fin 3 → ZMod 2) (X : Matrix (Fin 3) (Fin 3) R) :
    Matrix.diagonal (fun a => sg R (α a)) * (Matrix.diagonal (fun a => sg R (α a)) * X) = X := by
  rw [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  simp only [sg_mul_self_eq_one]
  rw [Matrix.diagonal_one, Matrix.one_mul]

/- English proof (translation)
Rewrite `hM`, `hN`, the goal using `[grM_iff_map_eq_diagonal_mul_mul_diagonal]`. Establish `e : (M * N).map σ = M.map σ * N.map σ` using `Matrix.map_mul (f := (σ : R →+* R))`. Rewrite using `[e, hM, hN]`. Simplify using `only [Matrix.mul_assoc, diagonal_sg_mul_diagonal_sg_mul_cancel]`.
-/
private theorem grM_mul_of_grM_of_grM {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β γ : Fin 3 → ZMod 2) (M N : Matrix (Fin 3) (Fin 3) R) (hM : GrM σ α β M) (hN : GrM σ β γ N) :
    GrM σ α γ (M * N) := by
  rw [grM_iff_map_eq_diagonal_mul_mul_diagonal] at hM hN ⊢
  have e : (M * N).map σ = M.map σ * N.map σ := Matrix.map_mul (f := (σ : R →+* R))
  rw [e, hM, hN]
  simp only [Matrix.mul_assoc, diagonal_sg_mul_diagonal_sg_mul_cancel]

/- English proof (translation)
Rewrite `hg`, the goal using `[grM_iff_map_eq_diagonal_mul_mul_diagonal]`. Use `set G : Matrix (Fin 3) (Fin 3) R := (g : Matrix (Fin 3) (Fin 3) R) with hG`. Use `set Gi : Matrix (Fin 3) (Fin 3) R := ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) with hGi`. Establish `hGiG : Gi * G = 1` using `by rw [hG, hGi]; simp`. Establish `hGGi : G * Gi = 1` using `by rw [hG, hGi]; simp`.

Establish `e : (Gi * G).map σ = Gi.map σ * G.map σ` using `Matrix.map_mul (f := (σ : R →+* R))`. Establish `e1 : Gi.map σ * G.map σ = 1`. Rewrite using `[← e, hGiG]`. Simplify using the standard rewrite rules. Establish `key : Matrix.diagonal (fun a => sg R (α a)) * G * Matrix.diagonal (fun b => sg R (β b)) * (Matrix.diagonal (fun b => sg R (β b)) * Gi * Matrix.diagonal (fun a => sg R (α a))) = 1`.

Simplify using `only [Matrix.mul_assoc, diagonal_sg_mul_diagonal_sg_mul_cancel]`. Rewrite using `[← Matrix.mul_assoc G, hGGi, Matrix.one_mul, Matrix.diagonal_mul_diagonal]`. Simplify using `only [sg_mul_self_eq_one]`. Conclude with `Matrix.diagonal_one`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hg, key, Matrix.mul_one]`. Use `_ = _ := by rw [← Matrix.mul_assoc, e1, Matrix.one_mul]`.
-/
private theorem grM_gl_inv_of_grM {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β : Fin 3 → ZMod 2) (g : GL (Fin 3) R) (hg : GrM σ α β (g : Matrix (Fin 3) (Fin 3) R)) :
    GrM σ β α ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  rw [grM_iff_map_eq_diagonal_mul_mul_diagonal] at hg ⊢
  set G : Matrix (Fin 3) (Fin 3) R := (g : Matrix (Fin 3) (Fin 3) R) with hG
  set Gi : Matrix (Fin 3) (Fin 3) R := ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) with hGi
  have hGiG : Gi * G = 1 := by rw [hG, hGi]; simp
  have hGGi : G * Gi = 1 := by rw [hG, hGi]; simp
  have e : (Gi * G).map σ = Gi.map σ * G.map σ := Matrix.map_mul (f := (σ : R →+* R))
  have e1 : Gi.map σ * G.map σ = 1 := by
    rw [← e, hGiG]
    simp
  have key : Matrix.diagonal (fun a => sg R (α a)) * G * Matrix.diagonal (fun b => sg R (β b)) *
      (Matrix.diagonal (fun b => sg R (β b)) * Gi * Matrix.diagonal (fun a => sg R (α a))) = 1 := by
    simp only [Matrix.mul_assoc, diagonal_sg_mul_diagonal_sg_mul_cancel]
    rw [← Matrix.mul_assoc G, hGGi, Matrix.one_mul, Matrix.diagonal_mul_diagonal]
    simp only [sg_mul_self_eq_one]
    exact Matrix.diagonal_one
  calc Gi.map σ
      = Gi.map σ * (G.map σ *
        (Matrix.diagonal (fun b => sg R (β b)) * Gi * Matrix.diagonal (fun a => sg R (α a)))) := by
        rw [hg, key, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, e1, Matrix.one_mul]

/- English proof (translation)
Use `show σ' (av h σ' j x) = sg R j * av h σ' j x`. Simplify using `only [av, map_smul, map_add, map_mul, hinv, sg_map σ' j]`. Rewrite using `[mul_smul_comm]`. Use `congr 1`. Take the linear combination `(-(σ' x)) * sg_mul_self_eq_one (R := R) j`.
-/
private theorem av_mem_evp_of_involutive {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (h : O) (σ' : R →ₐ[O] R)
    (hinv : ∀ y, σ' (σ' y) = y) (j : ZMod 2) (x : R) : av h σ' j x ∈ evp σ' j := by
  show σ' (av h σ' j x) = sg R j * av h σ' j x
  simp only [av, map_smul, map_add, map_mul, hinv, sg_map σ' j]
  rw [mul_smul_comm]
  congr 1
  linear_combination (-(σ' x)) * sg_mul_self_eq_one (R := R) j

/- English proof (translation)
Establish `hx' : σ (p x) = sg C j * p x` using `hx`. Simplify using `only [av, map_smul, map_add, map_mul, hcomm, hx', sg_map p j]`. Rewrite using `[Algebra.smul_def]`. Establish `h2 : algebraMap O C h * 2 = 1`. Rewrite using `[← map_ofNat (algebraMap O C) 2, ← map_mul, hh, map_one]`.

Take the linear combination `(p x) * h2 + (algebraMap O C h * p x) * sg_mul_self_eq_one (R := C) j`.
-/
private theorem map_av_eq_map_of_map_mem_evp {O C' C : Type} [CommRing O] [CommRing C'] [Algebra O C'] [CommRing C] [Algebra O C]
    (p : C' →ₐ[O] C) (σ' : C' →ₐ[O] C') (σ : C →ₐ[O] C) (hcomm : ∀ y, p (σ' y) = σ (p y)) (h : O) (hh : h * 2 = 1)
    (j : ZMod 2) (x : C') (hx : p x ∈ evp σ j) : p (av h σ' j x) = p x := by
  have hx' : σ (p x) = sg C j * p x := hx
  simp only [av, map_smul, map_add, map_mul, hcomm, hx', sg_map p j]
  rw [Algebra.smul_def]
  have h2 : algebraMap O C h * 2 = 1 := by
    rw [← map_ofNat (algebraMap O C) 2, ← map_mul, hh, map_one]
  linear_combination (p x) * h2 + (algebraMap O C h * p x) * sg_mul_self_eq_one (R := C) j

/- English proof (translation)
Assume the negation of the conclusion as `hx'`. Establish `hxm : x ∈ maximalIdeal C'` using `(IsLocalRing.mem_maximalIdeal x).mpr hx'`. Take `⟨a, ha⟩` from `IsCO.res_surj (O := O) (R := C) (p x)`. Establish `hau : IsUnit (algebraMap O C a)`. Assume the negation of the conclusion as `hna`.

Establish `h1 : algebraMap O C a ∈ maximalIdeal C` using `(IsLocalRing.mem_maximalIdeal _).mpr hna`. Establish `h2 : p x ∈ maximalIdeal C` using `by simpa using Ideal.add_mem _ ha h1`. Conclude with `((IsLocalRing.mem_maximalIdeal _).mp h2) hx`. Use `haveI := IsCO.isLocalHom (O := O) (R := C)`. Take `⟨u, rfl⟩` from `isUnit_of_map_unit (algebraMap O C) a hau`.

Establish `h1 : IsUnit (1 - algebraMap O C' ↑u⁻¹ * x)` using `IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_left _ _ hxm))`. Establish `h2` using `h1.map p`. Establish `h3 : p (1 - algebraMap O C' ↑u⁻¹ * x) = -(algebraMap O C ↑u⁻¹ * (p x - algebraMap O C ↑u))`. Rewrite using `[map_sub, map_one, map_mul, AlgHom.commutes]`. Establish `: algebraMap O C ↑u⁻¹ * algebraMap O C ↑u = 1` using `by rw [← map_mul, Units.inv_mul, map_one]`.

Take the linear combination `(-1 : C) * this`. Rewrite `h2` using `[h3]`. Establish `h4 : -(algebraMap O C ↑u⁻¹ * (p x - algebraMap O C ↑u)) ∈ maximalIdeal C` using `(Ideal.neg_mem_iff _).mpr (Ideal.mul_mem_left _ _ ha)`. Conclude with `((IsLocalRing.mem_maximalIdeal _).mp h4) h2`.
-/
private theorem isUnit_of_isUnit_algHom_map_of_isCO {O C' C : Type} [CommRing O] [IsLocalRing O] [CommRing C'] [Algebra O C'] [IsCO O C']
    [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (x : C') (hx : IsUnit (p x)) : IsUnit x := by
  by_contra hx'
  have hxm : x ∈ maximalIdeal C' := (IsLocalRing.mem_maximalIdeal x).mpr hx'
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) (R := C) (p x)
  have hau : IsUnit (algebraMap O C a) := by
    by_contra hna
    have h1 : algebraMap O C a ∈ maximalIdeal C := (IsLocalRing.mem_maximalIdeal _).mpr hna
    have h2 : p x ∈ maximalIdeal C := by simpa using Ideal.add_mem _ ha h1
    exact ((IsLocalRing.mem_maximalIdeal _).mp h2) hx
  haveI := IsCO.isLocalHom (O := O) (R := C)
  obtain ⟨u, rfl⟩ := isUnit_of_map_unit (algebraMap O C) a hau
  have h1 : IsUnit (1 - algebraMap O C' ↑u⁻¹ * x) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_left _ _ hxm))
  have h2 := h1.map p
  have h3 : p (1 - algebraMap O C' ↑u⁻¹ * x) = -(algebraMap O C ↑u⁻¹ * (p x - algebraMap O C ↑u)) := by
    rw [map_sub, map_one, map_mul, AlgHom.commutes]
    have : algebraMap O C ↑u⁻¹ * algebraMap O C ↑u = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    linear_combination (-1 : C) * this
  rw [h3] at h2
  have h4 : -(algebraMap O C ↑u⁻¹ * (p x - algebraMap O C ↑u)) ∈ maximalIdeal C :=
    (Ideal.neg_mem_iff _).mpr (Ideal.mul_mem_left _ _ ha)
  exact ((IsLocalRing.mem_maximalIdeal _).mp h4) h2

/- English proof (translation)
Establish `hm : Ideal.map σ' (maximalIdeal C') ≤ maximalIdeal C'`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `z hz`. Rewrite using `[Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Rewrite `hz` using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`.

Introduce `hu`. Apply `hz` to reduce the goal to its premises. Use `hu.map σ'` as an intermediate fact. Rewrite `this` using `[hinv]`. Then use the resulting hypothesis. Establish `hmN : Ideal.map σ' (maximalIdeal C' ^ N) ≤ maximalIdeal C' ^ N`.

Rewrite using `[Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono hm N`. Establish `hσ : σ' (x - y) ∈ maximalIdeal C' ^ N` using `hmN (Ideal.mem_map_of_mem _ hxy)`. Establish `e : av h σ' j x - av h σ' j y = algebraMap O C' h * ((x - y) + sg C' j * σ' (x - y))`. Simplify using `only [av, Algebra.smul_def, map_sub]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.add_mem _ hxy (Ideal.mul_mem_left _ _ hσ))`.
-/
private theorem av_sub_av_mem_maximalIdeal_pow {O C' : Type} [CommRing O] [IsLocalRing O] [CommRing C'] [Algebra O C'] [IsCO O C']
    (h : O) (σ' : C' →ₐ[O] C') (hinv : ∀ y, σ' (σ' y) = y) (j : ZMod 2) (N : ℕ) (x y : C')
    (hxy : x - y ∈ maximalIdeal C' ^ N) : av h σ' j x - av h σ' j y ∈ maximalIdeal C' ^ N := by
  have hm : Ideal.map σ' (maximalIdeal C') ≤ maximalIdeal C' := by
    rw [Ideal.map_le_iff_le_comap]
    intro z hz
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hz
    intro hu
    apply hz
    have := hu.map σ'
    rwa [hinv] at this
  have hmN : Ideal.map σ' (maximalIdeal C' ^ N) ≤ maximalIdeal C' ^ N := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hm N
  have hσ : σ' (x - y) ∈ maximalIdeal C' ^ N := hmN (Ideal.mem_map_of_mem _ hxy)
  have e : av h σ' j x - av h σ' j y = algebraMap O C' h * ((x - y) + sg C' j * σ' (x - y)) := by
    simp only [av, Algebra.smul_def, map_sub]
    ring
  rw [e]
  exact Ideal.mul_mem_left _ _ (Ideal.add_mem _ hxy (Ideal.mul_mem_left _ _ hσ))

/- English proof (translation)
Introduce `N`. Establish `hs` using `Ideal.Quotient.mk_surjective (I := maximalIdeal C' ^ N)`. Establish `e : (fun g => Ideal.Quotient.mk (maximalIdeal C' ^ N) (av h σ' j (f g))) = (fun q => Ideal.Quotient.mk (maximalIdeal C' ^ N) (av h σ' j (Function.surjInv hs q))) ∘ (fun g => Ideal.Quotient.mk (maximalIdeal C' ^ N) (f g))`. Use function extensionality and compare the values at `g`. Simplify using `only [Function.comp]`.

Rewrite using `[Ideal.Quotient.eq]`. Apply `av_sub_av_mem_maximalIdeal_pow h σ' hinv j N` to reduce the goal to its premises. Rewrite using `[← Ideal.Quotient.eq]`. Conclude with `(Function.surjInv_eq hs _).symm`. Rewrite using `[e]`.

Conclude with `(hf N).comp _`.
-/
private theorem adicCont_av_comp {Γ O C' : Type} [TopologicalSpace Γ] [CommRing O] [IsLocalRing O] [CommRing C']
    [Algebra O C'] [IsCO O C'] (h : O) (σ' : C' →ₐ[O] C') (hinv : ∀ y, σ' (σ' y) = y) (j : ZMod 2) (f : Γ → C')
    (hf : AdicCont (maximalIdeal C') f) : AdicCont (maximalIdeal C') (fun s => av h σ' j (f s)) := by
  intro N
  have hs := Ideal.Quotient.mk_surjective (I := maximalIdeal C' ^ N)
  have e : (fun g => Ideal.Quotient.mk (maximalIdeal C' ^ N) (av h σ' j (f g))) =
      (fun q => Ideal.Quotient.mk (maximalIdeal C' ^ N) (av h σ' j (Function.surjInv hs q))) ∘
        (fun g => Ideal.Quotient.mk (maximalIdeal C' ^ N) (f g)) := by
    funext g
    simp only [Function.comp]
    rw [Ideal.Quotient.eq]
    apply av_sub_av_mem_maximalIdeal_pow h σ' hinv j N
    rw [← Ideal.Quotient.eq]
    exact (Function.surjInv_eq hs _).symm
  rw [e]
  exact (hf N).comp _

/- English proof (translation)
Use `set M : Matrix (Fin 3) (Fin 3) C' := Matrix.of (fun a b => av h σ' (α a - β b) ((X : Matrix (Fin 3) (Fin 3) C') a b)) with hM`. Establish `hmap : M.map p = (X : Matrix (Fin 3) (Fin 3) C').map p`. Use extensionality with `a b`. Conclude with `map_av_eq_map_of_map_mem_evp p σ' σ hcomm h hh _ _ (hX a b)`. Establish `hXu : IsUnit (X : Matrix (Fin 3) (Fin 3) C').det` using `(Matrix.isUnit_iff_isUnit_det _).mp X.isUnit`.

Establish `hdet : IsUnit M.det`. Apply `isUnit_of_isUnit_algHom_map_of_isCO p` to reduce the goal to its premises. Rewrite using `[AlgHom.map_det, AlgHom.mapMatrix_apply, hmap, ← AlgHom.mapMatrix_apply, ← AlgHom.map_det]`. Conclude with `hXu.map p`. Use `⟨Matrix.nonsingInvUnit M hdet, rfl, ?_⟩` and prove the remaining obligations.

Conclude with `Units.ext hmap`.
-/
private theorem exists_gl_eq_av_entries_and_map_eq {O C' C : Type} [CommRing O] [IsLocalRing O] [CommRing C'] [Algebra O C'] [IsCO O C']
    [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (σ' : C' →ₐ[O] C') (σ : C →ₐ[O] C)
    (hcomm : ∀ y, p (σ' y) = σ (p y)) (h : O) (hh : h * 2 = 1) (α β : Fin 3 → ZMod 2) (X : GL (Fin 3) C')
    (hX : GrM σ α β ((X : Matrix (Fin 3) (Fin 3) C').map p)) :
    ∃ Y : GL (Fin 3) C', (Y : Matrix (Fin 3) (Fin 3) C') =
        Matrix.of (fun a b => av h σ' (α a - β b) ((X : Matrix (Fin 3) (Fin 3) C') a b)) ∧
      Matrix.GeneralLinearGroup.map (p : C' →+* C) Y = Matrix.GeneralLinearGroup.map (p : C' →+* C) X := by
  set M : Matrix (Fin 3) (Fin 3) C' := Matrix.of (fun a b => av h σ' (α a - β b) ((X : Matrix (Fin 3) (Fin 3) C') a b)) with hM
  have hmap : M.map p = (X : Matrix (Fin 3) (Fin 3) C').map p := by
    ext a b
    exact map_av_eq_map_of_map_mem_evp p σ' σ hcomm h hh _ _ (hX a b)
  have hXu : IsUnit (X : Matrix (Fin 3) (Fin 3) C').det := (Matrix.isUnit_iff_isUnit_det _).mp X.isUnit
  have hdet : IsUnit M.det := by
    apply isUnit_of_isUnit_algHom_map_of_isCO p
    rw [AlgHom.map_det, AlgHom.mapMatrix_apply, hmap, ← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
    exact hXu.map p
  refine ⟨Matrix.nonsingInvUnit M hdet, rfl, ?_⟩
  exact Units.ext hmap

/- English proof (translation)
Introduce `l _ k _ F O _ _ _ _ h2 C' _ _ _ C _ _ _ p σ' σ hinv hcomm B π hB D`. Take `⟨h, hh⟩ : ∃ h : O, h * 2 = 1` from `⟨_, h2.val_inv_mul⟩`. Establish `gr_r : ∀ s, GrM σ pq pq ((D.r s : Matrix (Fin 3) (Fin 3) C').map p)`. Introduce `s`. Establish `e : (D.r s : Matrix (Fin 3) (Fin 3) C').map p = ((B.r s).left : Matrix (Fin 3) (Fin 3) C)`.

Rewrite using `[← D.r_map s]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `hB.r s`. Establish `gr_g : ∀ v, GrM σ (π v) pq ((D.g v : Matrix (Fin 3) (Fin 3) C').map p)`.

Introduce `v`. Establish `e : (D.g v : Matrix (Fin 3) (Fin 3) C').map p = ((B.g v : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)`. Rewrite using `[← D.g_map v]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `hB.g v`. Establish `gr_t : ∀ v s, GrM σ (π v) (π v) ((D.t v s : Matrix (Fin 3) (Fin 3) C').map p)`. Introduce `v s`. Establish `e : (D.t v s : Matrix (Fin 3) (Fin 3) C').map p = ((B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)`. Rewrite using `[← D.t_map v s]`.

Both sides reduce to the same expression. Rewrite using `[e, Units.val_mul, Units.val_mul]`. Conclude with `grM_mul_of_grM_of_grM σ _ _ _ _ _ (grM_mul_of_grM_of_grM σ _ _ _ _ _ (hB.g v) (hB.r _)) (grM_gl_inv_of_grM σ _ _ _ (hB.g v))`. Use `choose r' hr' hr'm using fun s => exists_gl_eq_av_entries_and_map_eq p σ' σ hcomm h hh pq pq (D.r s) (gr_r s)`. Use `choose g' hg' hg'm using fun v => exists_gl_eq_av_entries_and_map_eq p σ' σ hcomm h hh (π v) pq (D.g v) (gr_g v)`.

Use `choose t' ht' ht'm using fun v s => exists_gl_eq_av_entries_and_map_eq p σ' σ hcomm h hh (π v) (π v) (D.t v s) (gr_t v s)`. Use `⟨⟨r', ?_, fun s => (hr'm s).trans (D.r_map s), g', fun v => (hg'm v).trans (D.g_map v), t', ?_, ?_, fun v s => (ht'm v s).trans (D.t_map v s)⟩, ⟨?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `i j`. Simplify using `only [hr', Matrix.of_apply]`. Conclude with `adicCont_av_comp h σ' hinv _ (fun s => (D.r s : Matrix (Fin 3) (Fin 3) C') i j) (D.r_cont i j)`.

Introduce `v i j`. Simplify using `only [ht', Matrix.of_apply]`. Conclude with `adicCont_av_comp h σ' hinv _ (fun s => (D.t v s : Matrix (Fin 3) (Fin 3) C') i j) (D.t_cont v i j)`. Introduce `v s i j hij`. Rewrite using `[ht', Matrix.of_apply, D.t_tri v s i j hij]`.

Conclude with `av_zero h σ' _`. Introduce `s a b`. Rewrite using `[hr', Matrix.of_apply]`. Conclude with `av_mem_evp_of_involutive h σ' hinv _ _`. Introduce `v a b`.

Rewrite using `[hg', Matrix.of_apply]`. Conclude with `av_mem_evp_of_involutive h σ' hinv _ _`. Introduce `v s a b`. Rewrite using `[ht', Matrix.of_apply]`. Conclude with `av_mem_evp_of_involutive h σ' hinv _ _`.
-/
theorem UpperTheory.V.Fr.ep_glift :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (σ' : C' →ₐ[O] C') (σ : C →ₐ[O] C), (∀ y, σ' (σ' y) = y) → (∀ y, p (σ' y) = σ (p y)) → ∀ (B : Box F 3 C) (π : F.V → Fin 3 → ZMod 2), B.Gr σ π → SetLift p B → ∃ D : SetLift p B, D.Gr σ' π := by
  intro l _ k _ F O _ _ _ _ h2 C' _ _ _ C _ _ _ p σ' σ hinv hcomm B π hB D
  obtain ⟨h, hh⟩ : ∃ h : O, h * 2 = 1 := ⟨_, h2.val_inv_mul⟩
  have gr_r : ∀ s, GrM σ pq pq ((D.r s : Matrix (Fin 3) (Fin 3) C').map p) := by
    intro s
    have e : (D.r s : Matrix (Fin 3) (Fin 3) C').map p = ((B.r s).left : Matrix (Fin 3) (Fin 3) C) := by
      rw [← D.r_map s]
      rfl
    rw [e]
    exact hB.r s
  have gr_g : ∀ v, GrM σ (π v) pq ((D.g v : Matrix (Fin 3) (Fin 3) C').map p) := by
    intro v
    have e : (D.g v : Matrix (Fin 3) (Fin 3) C').map p = ((B.g v : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
      rw [← D.g_map v]
      rfl
    rw [e]
    exact hB.g v
  have gr_t : ∀ v s, GrM σ (π v) (π v) ((D.t v s : Matrix (Fin 3) (Fin 3) C').map p) := by
    intro v s
    have e : (D.t v s : Matrix (Fin 3) (Fin 3) C').map p =
        ((B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
      rw [← D.t_map v s]
      rfl
    rw [e, Units.val_mul, Units.val_mul]
    exact grM_mul_of_grM_of_grM σ _ _ _ _ _ (grM_mul_of_grM_of_grM σ _ _ _ _ _ (hB.g v) (hB.r _)) (grM_gl_inv_of_grM σ _ _ _ (hB.g v))
  choose r' hr' hr'm using fun s => exists_gl_eq_av_entries_and_map_eq p σ' σ hcomm h hh pq pq (D.r s) (gr_r s)
  choose g' hg' hg'm using fun v => exists_gl_eq_av_entries_and_map_eq p σ' σ hcomm h hh (π v) pq (D.g v) (gr_g v)
  choose t' ht' ht'm using fun v s => exists_gl_eq_av_entries_and_map_eq p σ' σ hcomm h hh (π v) (π v) (D.t v s) (gr_t v s)
  refine ⟨⟨r', ?_, fun s => (hr'm s).trans (D.r_map s), g', fun v => (hg'm v).trans (D.g_map v), t', ?_, ?_,
    fun v s => (ht'm v s).trans (D.t_map v s)⟩, ⟨?_, ?_, ?_⟩⟩
  · intro i j
    simp only [hr', Matrix.of_apply]
    exact adicCont_av_comp h σ' hinv _ (fun s => (D.r s : Matrix (Fin 3) (Fin 3) C') i j) (D.r_cont i j)
  · intro v i j
    simp only [ht', Matrix.of_apply]
    exact adicCont_av_comp h σ' hinv _ (fun s => (D.t v s : Matrix (Fin 3) (Fin 3) C') i j) (D.t_cont v i j)
  · intro v s i j hij
    rw [ht', Matrix.of_apply, D.t_tri v s i j hij]
    exact av_zero h σ' _
  · intro s a b
    rw [hr', Matrix.of_apply]
    exact av_mem_evp_of_involutive h σ' hinv _ _
  · intro v a b
    rw [hg', Matrix.of_apply]
    exact av_mem_evp_of_involutive h σ' hinv _ _
  · intro v s a b
    rw [ht', Matrix.of_apply]
    exact av_mem_evp_of_involutive h σ' hinv _ _

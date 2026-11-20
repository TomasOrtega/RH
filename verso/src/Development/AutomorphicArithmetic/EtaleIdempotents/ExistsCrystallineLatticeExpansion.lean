import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.VecZero
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitOnOfDisj

set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct UpperTheory.Gal.crystallineComparison UpperTheory.Ru.crystallineComparison

/- English proof (translation)
Establish `hi : φ t * Ring.inverse (φ t) = 1` using `Ring.mul_inverse_cancel _ ht`. Rewrite using `[map_mul, map_pow, pow_add]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hi, one_pow, mul_one]`. Use `_ = _ := by rw [mul_pow]; ring`.
-/
private theorem inverse_pow_raise {A C : Type*} [CommRing A] [CommRing C] (φ : A →+* C) (t a : A) (ht : IsUnit (φ t)) (r s : ℕ) :
    φ a * Ring.inverse (φ t) ^ r = φ (t ^ s * a) * Ring.inverse (φ t) ^ (r + s) := by
  have hi : φ t * Ring.inverse (φ t) = 1 := Ring.mul_inverse_cancel _ ht
  rw [map_mul, map_pow, pow_add]
  calc φ a * Ring.inverse (φ t) ^ r
      = φ a * Ring.inverse (φ t) ^ r * (φ t * Ring.inverse (φ t)) ^ s := by
        rw [hi, one_pow, mul_one]
    _ = _ := by rw [mul_pow]; ring

/- English proof (translation)
Establish `hi : φ t * Ring.inverse (φ t) = 1` using `Ring.mul_inverse_cancel _ ht`. Rewrite using `[← h]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem eq_mul_inverse_pow {A C : Type*} [CommRing A] [CommRing C] (φ : A →+* C) (t a : A) (ht : IsUnit (φ t)) (r : ℕ) (y : C)
    (h : φ t ^ r * y = φ a) : y = φ a * Ring.inverse (φ t) ^ r := by
  have hi : φ t * Ring.inverse (φ t) = 1 := Ring.mul_inverse_cancel _ ht
  rw [← h]
  calc y = (φ t * Ring.inverse (φ t)) ^ r * y := by rw [hi, one_pow, one_mul]
    _ = _ := by rw [mul_pow]; ring

/- English proof (translation)
Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Conclude with `congrArg (fun z => M.toV j (v k) ⊗ₜ[ℚ_[l]] z) (inverse_pow_raise B.c (tA l) (c k) B.t_unit r s)`.
-/
private theorem vec_raise {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (B : PB l K) (M : Model l K)
    (j r s : ℕ) {ι : Type} [Fintype ι] (v : ι → M.T j) (c : ι → Acris l) :
    vec B M j r v c = vec B M j (r + s) v (fun k => tA l ^ s * c k) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  exact congrArg (fun z => M.toV j (v k) ⊗ₜ[ℚ_[l]] z) (inverse_pow_raise B.c (tA l) (c k) B.t_unit r s)

/- English proof (translation)
The claim follows from `(Fintype.sum_sum_type (fun x => M.toV j (Sum.elim v₁ v₂ x) ⊗ₜ[ℚ_[l]] (B.c (Sum.elim c₁ c₂ x) * Ring.inverse (B.c (tA l)) ^ r))).symm`.
-/
private theorem vec_sum {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (B : PB l K) (M : Model l K)
    (j r : ℕ) {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] (v₁ : ι₁ → M.T j) (v₂ : ι₂ → M.T j)
    (c₁ : ι₁ → Acris l) (c₂ : ι₂ → Acris l) :
    vec B M j r v₁ c₁ + vec B M j r v₂ c₂ = vec B M j r (Sum.elim v₁ v₂) (Sum.elim c₁ c₂) :=
  (Fintype.sum_sum_type (fun x => M.toV j (Sum.elim v₁ v₂ x) ⊗ₜ[ℚ_[l]]
    (B.c (Sum.elim c₁ c₂ x) * Ring.inverse (B.c (tA l)) ^ r))).symm

/- English proof (translation)
Establish `e₁ : vec B M j r₁ v₁ c₁ = vec B M j (r₁ + r₂) v₁ (fun k => tA l ^ r₂ * c₁ k)` using `vec_raise B M j r₁ r₂ v₁ c₁`. Establish `e₂ : vec B M j r₂ v₂ c₂ = vec B M j (r₁ + r₂) v₂ (fun k => tA l ^ r₁ * c₂ k)` using `(Nat.add_comm r₂ r₁) ▸ vec_raise B M j r₂ r₁ v₂ c₂`. Conclude with `(congrArg₂ HAdd.hAdd e₁ e₂).trans (vec_sum B M j (r₁ + r₂) v₁ v₂ (fun k => tA l ^ r₂ * c₁ k) (fun k => tA l ^ r₁ * c₂ k))`.
-/
private theorem vec_add_sum_elim {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (B : PB l K) (M : Model l K)
    (j r₁ r₂ : ℕ) {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] (v₁ : ι₁ → M.T j) (v₂ : ι₂ → M.T j)
    (c₁ : ι₁ → Acris l) (c₂ : ι₂ → Acris l) :
    vec B M j r₁ v₁ c₁ + vec B M j r₂ v₂ c₂ = vec B M j (r₁ + r₂) (Sum.elim v₁ v₂)
      (Sum.elim (fun k => tA l ^ r₂ * c₁ k) (fun k => tA l ^ r₁ * c₂ k)) := by
  have e₁ : vec B M j r₁ v₁ c₁ = vec B M j (r₁ + r₂) v₁ (fun k => tA l ^ r₂ * c₁ k) :=
    vec_raise B M j r₁ r₂ v₁ c₁
  have e₂ : vec B M j r₂ v₂ c₂ = vec B M j (r₁ + r₂) v₂ (fun k => tA l ^ r₁ * c₂ k) :=
    (Nat.add_comm r₂ r₁) ▸ vec_raise B M j r₂ r₁ v₂ c₂
  exact (congrArg₂ HAdd.hAdd e₁ e₂).trans
    (vec_sum B M j (r₁ + r₂) v₁ v₂ (fun k => tA l ^ r₂ * c₁ k) (fun k => tA l ^ r₁ * c₂ k))

/- English proof (translation)
Take `⟨ι₁, i₁, v₁, c₁, r₁, h₁⟩` from `hx`. Take `⟨ι₂, i₂, v₂, c₂, r₂, h₂⟩` from `hy`. Conclude with `⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim v₁ v₂, Sum.elim (fun k => tA l ^ r₂ * c₁ k) (fun k => tA l ^ r₁ * c₂ k), r₁ + r₂, (congrArg₂ HAdd.hAdd h₁ h₂).trans (vec_add_sum_elim B M j r₁ r₂ v₁ v₂ c₁ c₂)⟩`.
-/
private theorem vec_add {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (B : PB l K) (M : Model l K)
    (j : ℕ) (x y : M.V j ⊗[ℚ_[l]] B.C)
    (hx : ∃ (ι : Type) (_ : Fintype ι) (v : ι → M.T j) (c : ι → Acris l) (r : ℕ), x = vec B M j r v c)
    (hy : ∃ (ι : Type) (_ : Fintype ι) (v : ι → M.T j) (c : ι → Acris l) (r : ℕ), y = vec B M j r v c) :
    ∃ (ι : Type) (_ : Fintype ι) (v : ι → M.T j) (c : ι → Acris l) (r : ℕ), x + y = vec B M j r v c := by
  obtain ⟨ι₁, i₁, v₁, c₁, r₁, h₁⟩ := hx
  obtain ⟨ι₂, i₂, v₂, c₂, r₂, h₂⟩ := hy
  exact ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim v₁ v₂,
    Sum.elim (fun k => tA l ^ r₂ * c₁ k) (fun k => tA l ^ r₁ * c₂ k), r₁ + r₂,
    (congrArg₂ HAdd.hAdd h₁ h₂).trans (vec_add_sum_elim B M j r₁ r₂ v₁ v₂ c₁ c₂)⟩

/- English proof (translation)
Take `⟨r, a, ha⟩` from `B.loc y`. Use `⟨Unit, inferInstance, fun _ => h, fun _ => a, r, ?_⟩` and prove the remaining obligations. Establish `hy : y = B.c a * Ring.inverse (B.c (tA l)) ^ r` using `eq_mul_inverse_pow B.c (tA l) a B.t_unit r y ha`. Establish `e : vec B M j r (fun _ : Unit => h) (fun _ => a) = M.toV j h ⊗ₜ[ℚ_[l]] (B.c a * Ring.inverse (B.c (tA l)) ^ r)` using `Fintype.sum_unique _`. Rewrite using `[e, ← hy]`.
-/
private theorem vec_pure {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (B : PB l K) (M : Model l K)
    (j : ℕ) (h : M.T j) (y : B.C) :
    ∃ (ι : Type) (_ : Fintype ι) (v : ι → M.T j) (c : ι → Acris l) (r : ℕ),
      M.toV j h ⊗ₜ[ℚ_[l]] y = vec B M j r v c := by
  obtain ⟨r, a, ha⟩ := B.loc y
  refine ⟨Unit, inferInstance, fun _ => h, fun _ => a, r, ?_⟩
  have hy : y = B.c a * Ring.inverse (B.c (tA l)) ^ r := eq_mul_inverse_pow B.c (tA l) a B.t_unit r y ha
  have e : vec B M j r (fun _ : Unit => h) (fun _ => a) = M.toV j h ⊗ₜ[ℚ_[l]] (B.c a * Ring.inverse (B.c (tA l)) ^ r) :=
    Fintype.sum_unique _
  rw [e, ← hy]

/- English proof (translation)
Assemble the required witnesses or components as `⟨Empty, inferInstance, fun e => e.elim, fun e => e.elim, 0, (Fintype.sum_empty _).symm⟩`.
-/
private theorem vec_zero {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (B : PB l K) (M : Model l K)
    (j : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (v : ι → M.T j) (c : ι → Acris l) (r : ℕ),
      (0 : M.V j ⊗[ℚ_[l]] B.C) = vec B M j r v c :=
  ⟨Empty, inferInstance, fun e => e.elim, fun e => e.elim, 0, (Fintype.sum_empty _).symm⟩

/- English proof (translation)
Establish `key : ∀ a' : ℚ_[l] ⊗[ℤ_[l]] GlobalTheory.EtC.Hl l M.spc j 0, ∀ y : B.C, ∃ (ι : Type) (_ : Fintype ι) (v : ι → M.T j) (c : ι → Acris l) (r : ℕ), (show M.V j from a') ⊗ₜ[ℚ_[l]] y = vec B M j r v c`. Introduce `a'`. Proceed by induction on `a' using TensorProduct.induction_on with`. Consider the case `zero`. Introduce `y`.

Establish `e : (show M.V j from (0 : ℚ_[l] ⊗[ℤ_[l]] GlobalTheory.EtC.Hl l M.spc j 0)) ⊗ₜ[ℚ_[l]] y = 0` using `TensorProduct.zero_tmul _ _`. Rewrite using `[e]`. Conclude with `vec_zero B M j`. Consider the case `tmul q h`. Introduce `y`.

Establish `e : (show M.V j from (q ⊗ₜ[ℤ_[l]] h : ℚ_[l] ⊗[ℤ_[l]] GlobalTheory.EtC.Hl l M.spc j 0)) = q • M.toV j (show M.T j from h)`. Express the relevant statement in the definitionally equal form `(q ⊗ₜ[ℤ_[l]] h : ℚ_[l] ⊗[ℤ_[l]] GlobalTheory.EtC.Hl l M.spc j 0) = q • ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] h : ℚ_[l] ⊗[ℤ_[l]] GlobalTheory.EtC.Hl l M.spc j 0)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[e, TensorProduct.smul_tmul]`. Conclude with `vec_pure B M j _ _`.

Consider the case `add a₁ a₂ h₁ h₂`. Introduce `y`. Establish `e : (show M.V j from (a₁ + a₂ : ℚ_[l] ⊗[ℤ_[l]] GlobalTheory.EtC.Hl l M.spc j 0)) ⊗ₜ[ℚ_[l]] y = (show M.V j from a₁) ⊗ₜ[ℚ_[l]] y + (show M.V j from a₂) ⊗ₜ[ℚ_[l]] y` using `TensorProduct.add_tmul _ _ _`. Rewrite using `[e]`. Conclude with `vec_add B M j _ _ (h₁ y) (h₂ y)`.

Conclude with `key a`.
-/
private theorem vec_tmul {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (B : PB l K) (M : Model l K)
    (j : ℕ) (a : M.V j) :
    ∀ y : B.C, ∃ (ι : Type) (_ : Fintype ι) (v : ι → M.T j) (c : ι → Acris l) (r : ℕ),
      a ⊗ₜ[ℚ_[l]] y = vec B M j r v c := by
  have key : ∀ a' : ℚ_[l] ⊗[ℤ_[l]] GlobalTheory.EtC.Hl l M.spc j 0, ∀ y : B.C,
      ∃ (ι : Type) (_ : Fintype ι) (v : ι → M.T j) (c : ι → Acris l) (r : ℕ),
        (show M.V j from a') ⊗ₜ[ℚ_[l]] y = vec B M j r v c := by
    intro a'
    induction a' using TensorProduct.induction_on with
    | zero =>
      intro y
      have e : (show M.V j from (0 : ℚ_[l] ⊗[ℤ_[l]] GlobalTheory.EtC.Hl l M.spc j 0)) ⊗ₜ[ℚ_[l]] y = 0 :=
        TensorProduct.zero_tmul _ _
      rw [e]
      exact vec_zero B M j
    | tmul q h =>
      intro y
      have e : (show M.V j from (q ⊗ₜ[ℤ_[l]] h : ℚ_[l] ⊗[ℤ_[l]] GlobalTheory.EtC.Hl l M.spc j 0)) =
          q • M.toV j (show M.T j from h) := by
        change (q ⊗ₜ[ℤ_[l]] h : ℚ_[l] ⊗[ℤ_[l]] GlobalTheory.EtC.Hl l M.spc j 0) =
          q • ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] h : ℚ_[l] ⊗[ℤ_[l]] GlobalTheory.EtC.Hl l M.spc j 0)
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e, TensorProduct.smul_tmul]
      exact vec_pure B M j _ _
    | add a₁ a₂ h₁ h₂ =>
      intro y
      have e : (show M.V j from (a₁ + a₂ : ℚ_[l] ⊗[ℤ_[l]] GlobalTheory.EtC.Hl l M.spc j 0)) ⊗ₜ[ℚ_[l]] y =
          (show M.V j from a₁) ⊗ₜ[ℚ_[l]] y + (show M.V j from a₂) ⊗ₜ[ℚ_[l]] y :=
        TensorProduct.add_tmul _ _ _
      rw [e]
      exact vec_add B M j _ _ (h₁ y) (h₂ y)
  exact key a

/- English proof (translation)
Introduce `l _ K B M j x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact vec_zero B M j`. Consider the case `tmul a y => exact vec_tmul B M j a y`. Consider the case `add x y hx hy => exact vec_add B M j x y hx hy`.
-/
theorem UpperTheory.exists_crystalline_lattice_expansion :
    ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (B : PB l K) (M : Model l K) (j : ℕ) (x : M.V j ⊗[ℚ_[l]] B.C),
        ∃ (ι : Type) (_ : Fintype ι) (v : ι → M.T j) (c : ι → Acris l) (r : ℕ), x = vec B M j r v c := by
  intro l _ K B M j x
  induction x using TensorProduct.induction_on with
  | zero => exact vec_zero B M j
  | tmul a y => exact vec_tmul B M j a y
  | add x y hx hy => exact vec_add B M j x y hx hy

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelLat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerBasisOfCharpolySeparable
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.CentTorusModel

variable {K : UQ} (B : InvAlg K) {n : ℕ} (ψ : B.A ≃ₗ[K.E] (Fin n → K.E))

def mulMat (a : B.A) : Matrix (Fin n) (Fin n) K.E :=
  LinearMap.toMatrix' (ψ.toLinearMap ∘ₗ LinearMap.mulLeft K.E a ∘ₗ ψ.symm.toLinearMap)

/- English proof (translation)
Simplify using `[mulMat, LinearMap.toMatrix'_mulVec]`.
-/
theorem mulMat_mulVec (a y : B.A) : mulMat B ψ a *ᵥ ψ y = ψ (a * y) := by
  simp [mulMat, LinearMap.toMatrix'_mulVec]

/- English proof (translation)
Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Take `⟨y, rfl⟩` from `ψ.surjective v`. Simplify using `only [Matrix.toLin'_apply, h, mulMat_mulVec]`.
-/
theorem eq_mulMat {M : Matrix (Fin n) (Fin n) K.E} {a : B.A} (h : ∀ y, M *ᵥ ψ y = ψ (a * y)) :
    M = mulMat B ψ a := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  obtain ⟨y, rfl⟩ := ψ.surjective v
  simp only [Matrix.toLin'_apply, h, mulMat_mulVec]

/- English proof (translation)
The claim follows from `(eq_mulMat B ψ (fun y => by simp)).symm`.
-/
theorem mulMat_one : mulMat B ψ 1 = 1 :=
  (eq_mulMat B ψ (fun y => by simp)).symm

/- English proof (translation)
The claim follows from `(eq_mulMat B ψ (fun y => by rw [← Matrix.mulVec_mulVec, mulMat_mulVec, mulMat_mulVec, mul_assoc])).symm`.
-/
theorem mulMat_mul (a b : B.A) : mulMat B ψ (a * b) = mulMat B ψ a * mulMat B ψ b :=
  (eq_mulMat B ψ (fun y => by rw [← Matrix.mulVec_mulVec, mulMat_mulVec, mulMat_mulVec, mul_assoc])).symm

def mulHom : B.A →* Matrix (Fin n) (Fin n) K.E where
  toFun := mulMat B ψ
  map_one' := mulMat_one B ψ
  map_mul' := mulMat_mul B ψ

/- English proof (translation)
Take `⟨b, hb⟩` from `exists_basis_pow_of_separable K B hs`. Establish `key : f = LinearMap.mulRight K.E (f 1)`. Use `b.ext fun i => ?_` and prove the remaining obligations. Rewrite using `[hb i, LinearMap.mulRight_apply]`. Generalize the expression as in `(i : ℕ) = k`.

Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ', hf, ih, mul_assoc]`. Rewrite using `[key, LinearMap.mulRight_apply, LinearMap.mulRight_apply, one_mul, mul_comm]`.
-/
theorem commutant (hs : B.P.Separable) (f : B.A →ₗ[K.E] B.A) (hf : ∀ y, f (B.g * y) = B.g * f y) (y : B.A) :
    f y = f 1 * y := by
  obtain ⟨b, hb⟩ := exists_basis_pow_of_separable K B hs
  have key : f = LinearMap.mulRight K.E (f 1) := by
    refine b.ext fun i => ?_
    rw [hb i, LinearMap.mulRight_apply]
    generalize (i : ℕ) = k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', hf, ih, mul_assoc]
  rw [key, LinearMap.mulRight_apply, LinearMap.mulRight_apply, one_mul, mul_comm]

/- English proof (translation)
Establish `h1 : (fun k => K.c ((M *ᵥ v) k)) = M.map K.c *ᵥ fun k => K.c (v k)`. Use function extensionality and compare the values at `k`. Simplify using `[Matrix.mulVec, dotProduct, map_sum]`. Establish `h2 : stdH K n (M *ᵥ u) (M *ᵥ v) = (M *ᵥ u) ⬝ᵥ fun k => K.c ((M *ᵥ v) k)` using `rfl`. Rewrite using `[h2, h1, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm, Matrix.mulVec_mulVec]`.
-/
theorem stdH_mulVec_eq (M : Matrix (Fin n) (Fin n) K.E) (u v : Fin n → K.E) :
    stdH K n (M *ᵥ u) (M *ᵥ v) = u ⬝ᵥ ((Mᵀ * M.map K.c) *ᵥ fun k => K.c (v k)) := by
  have h1 : (fun k => K.c ((M *ᵥ v) k)) = M.map K.c *ᵥ fun k => K.c (v k) := by
    funext k
    simp [Matrix.mulVec, dotProduct, map_sum]
  have h2 : stdH K n (M *ᵥ u) (M *ᵥ v) = (M *ᵥ u) ⬝ᵥ fun k => K.c ((M *ᵥ v) k) := rfl
  rw [h2, h1, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm,
    Matrix.mulVec_mulVec]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `i j`. Use `h (Pi.single j 1) (Pi.single i 1)` as an intermediate fact. Simplify using `[InertUnitOrb.stdH, Pi.single_apply] at this`.

Rewrite using `[Matrix.mul_apply, Matrix.one_apply, ← this]`. Conclude with `Finset.sum_congr rfl fun k _ => by simp [mul_comm]`. Introduce `h u v`. Establish `h' : Mᵀ * M.map K.c = 1`. Use `congrArg (fun X => X.map K.c) h` as an intermediate fact.

Simplify using `only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.map_one _ (map_zero K.c) (map_one K.c)] at this`. Use `this using 2` and compare the differences between its conclusion and the goal. Use extensionality with `a b`. Simplify using `[K.c_c]`. Rewrite using `[stdH_mulVec_eq, h', Matrix.one_mulVec]`.

Both sides reduce to the same expression.
-/
theorem stdH_mulVec_iff (M : Matrix (Fin n) (Fin n) K.E) :
    (∀ u v, stdH K n (M *ᵥ u) (M *ᵥ v) = stdH K n u v) ↔ (M.map K.c)ᵀ * M = 1 := by
  constructor
  · intro h
    ext i j
    have := h (Pi.single j 1) (Pi.single i 1)
    simp [InertUnitOrb.stdH, Pi.single_apply] at this
    rw [Matrix.mul_apply, Matrix.one_apply, ← this]
    exact Finset.sum_congr rfl fun k _ => by simp [mul_comm]
  · intro h u v
    have h' : Mᵀ * M.map K.c = 1 := by
      have := congrArg (fun X => X.map K.c) h
      simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.map_one _ (map_zero K.c) (map_one K.c)] at this
      convert this using 2
      ext a b; simp [K.c_c]
    rw [stdH_mulVec_eq, h', Matrix.one_mulVec]
    rfl

/- English proof (translation)
Establish `hh` using `hm.2.2`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h2 : ∀ y z, B.herm x (a * y) (a * z) = B.herm x y z`. Introduce `y z`.

Rewrite using `[← hh, ← hh, ← mulMat_mulVec, ← mulMat_mulVec]`. Conclude with `h _ _`. Establish `h3 : ∀ z, B.herm x (a * B.σ a - 1) z = 0`. Introduce `z`. Use `h2 1 z` as an intermediate fact.

Simplify using `only [InvAlg.herm] at this ⊢`. Rewrite using `[show (x : B.A) * (a * B.σ a - 1) * B.σ z = (x : B.A) * (a * 1) * B.σ (a * z) - x * 1 * B.σ z by`. Rewrite using `[map_mul]`. Use the proof step `ring, map_sub, this, sub_self]`. Establish `h4 : ψ (a * B.σ a - 1) = 0`.

Use function extensionality and compare the values at `k`. Use `h3 (ψ.symm (Pi.single k 1))` as an intermediate fact. Rewrite `this` using `[← hh, ψ.apply_symm_apply]`. Simplify `this` using `[InertUnitOrb.stdH, Pi.single_apply]`. Conclude with `sub_eq_zero.mp ((LinearEquiv.map_eq_zero_iff ψ).mp h4)`.

Introduce `h u v`. Take `⟨y, rfl⟩` from `ψ.surjective u`. Take `⟨z, rfl⟩` from `ψ.surjective v`. Rewrite using `[mulMat_mulVec, mulMat_mulVec, hh, hh]`. Simplify using `only [InvAlg.herm, map_mul]`.

Use `congr 1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem isom_iff {γ' : Matrix (Fin n) (Fin n) K.E} {x : B.Aˣ} (hm : IsModel B γ' x ψ) (a : B.A) :
    (∀ u v, stdH K n (mulMat B ψ a *ᵥ u) (mulMat B ψ a *ᵥ v) = stdH K n u v) ↔ a * B.σ a = 1 := by
  have hh := hm.2.2
  constructor
  · intro h
    have h2 : ∀ y z, B.herm x (a * y) (a * z) = B.herm x y z := by
      intro y z
      rw [← hh, ← hh, ← mulMat_mulVec, ← mulMat_mulVec]
      exact h _ _
    have h3 : ∀ z, B.herm x (a * B.σ a - 1) z = 0 := by
      intro z
      have := h2 1 z
      simp only [InvAlg.herm] at this ⊢
      rw [show (x : B.A) * (a * B.σ a - 1) * B.σ z = (x : B.A) * (a * 1) * B.σ (a * z) - x * 1 * B.σ z by
        rw [map_mul]; ring, map_sub, this, sub_self]
    have h4 : ψ (a * B.σ a - 1) = 0 := by
      funext k
      have := h3 (ψ.symm (Pi.single k 1))
      rw [← hh, ψ.apply_symm_apply] at this
      simpa [InertUnitOrb.stdH, Pi.single_apply] using this
    exact sub_eq_zero.mp ((LinearEquiv.map_eq_zero_iff ψ).mp h4)
  · intro h u v
    obtain ⟨y, rfl⟩ := ψ.surjective u
    obtain ⟨z, rfl⟩ := ψ.surjective v
    rw [mulMat_mulVec, mulMat_mulVec, hh, hh]
    simp only [InvAlg.herm, map_mul]
    congr 1
    calc (x : B.A) * (a * y) * (B.σ a * B.σ z) = x * y * B.σ z * (a * B.σ a) := by ring
      _ = _ := by rw [h, mul_one]

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem map_map_symm {R S : Type} [Ring R] [Ring S] (e : R ≃+* S) (M : Matrix (Fin n) (Fin n) R) :
    (M.map e).map e.symm = M := by
  ext i j; simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem map_symm_map {R S : Type} [Ring R] [Ring S] (e : R ≃+* S) (M : Matrix (Fin n) (Fin n) S) :
    (M.map e.symm).map e = M := by
  ext i j; simp

/- English proof (translation)
Establish `h1 : cT (cj w) (M.map e) = ((M.map K.c)ᵀ).map e`. Use extensionality with `i j`. Simplify using `[cT, he]`. Rewrite using `[h1, mul_one, ← Matrix.map_mul]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `: ((((M.map K.c)ᵀ * M).map e).map e.symm) = (1 : Matrix (Fin n) (Fin n) _).map e.symm` using `by rw [h]`. Rewrite `this` using `[map_map_symm]`. Simplify using `using this`. Introduce `h`.

Rewrite using `[h]`. Simplify using the standard rewrite rules.
-/
theorem unitary_map {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E}
    (e : K.E ≃+* w.adicCompletion E) (he : ∀ x, e (K.c x) = cj w (e x)) (M : Matrix (Fin n) (Fin n) K.E) :
    cT (cj w) (M.map e) * 1 * M.map e = 1 ↔ (M.map K.c)ᵀ * M = 1 := by
  have h1 : cT (cj w) (M.map e) = ((M.map K.c)ᵀ).map e := by
    ext i j; simp [cT, he]
  rw [h1, mul_one, ← Matrix.map_mul]
  constructor
  · intro h
    have : ((((M.map K.c)ᵀ * M).map e).map e.symm) = (1 : Matrix (Fin n) (Fin n) _).map e.symm := by rw [h]
    rw [map_map_symm] at this
    simpa using this
  · intro h
    rw [h]; simp

/- English proof (translation)
Introduce `E _ _ _ _ w hw K e he _ n B ψ x γ hm hs`. Establish `hUL : UL n w = UJ (cj w) 1` using `by simp [UL, hw]`. Set `ρ : B.A →* Matrix (Fin n) (Fin n) (w.adicCompletion E)` to `(e.toRingHom.mapMatrix : Matrix (Fin n) (Fin n) K.E →+* _).toMonoidHom.comp (mulHom B ψ)`. Establish `hρa : ∀ a, ρ a = (mulMat B ψ a).map e` using `fun a => rfl`. Establish `hγ'` using `eq_mulMat B ψ (fun y => (hm.2.1 y).symm)`.

Establish `hγ : (((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = ρ B.g`. Rewrite using `[hρa, ← hγ', map_symm_map]`. Establish `hmem : ∀ u : B.Aˣ, u ∈ B.T → (Units.map ρ u : GLw n w) ∈ UL n w`. Introduce `u hu`. Rewrite using `[hUL]`.

Use `show cT (cj w) (((Units.map ρ u : GLw n w)) : Matrix (Fin n) (Fin n) _) * 1 * _ = 1`. Rewrite using `[Units.coe_map, hρa, unitary_map e he, ← stdH_mulVec_iff, isom_iff B ψ hm]`. Conclude with `hu`. Establish `hcent : ∀ (u : B.Aˣ) (hu : u ∈ B.T), (⟨Units.map ρ u, hmem u hu⟩ : UL n w) ∈ twCent (MonoidHom.id (UL n w)) γ`. Introduce `u hu`.

Use `show _ * γ = γ * _`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Subgroup.coe_mul, Units.val_mul, MonoidHom.id_apply, Units.coe_map, hγ]`. Rewrite using `[← map_mul, ← map_mul, mul_comm]`.

Set `φ : B.T →* twCent (MonoidHom.id (UL n w)) γ` to `{ toFun := fun u => ⟨⟨Units.map ρ u, hmem u u.2⟩, hcent u u.2⟩ map_one' := by`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules.

Use the proof step `map_mul' := by`. Introduce `a b`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Simplify using `}`. Establish `hφ : ∀ u : B.T, ((((φ u : twCent (MonoidHom.id (UL n w)) γ) : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = (mulMat B ψ ((u : B.Aˣ) : B.A)).map e` using `fun u => rfl`. Establish `hinj : Function.Injective φ`. Introduce `a b hab`. Establish `h1` using `congrArg (fun t : twCent (MonoidHom.id (UL n w)) γ => (((t : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) hab`.

Simplify using `only [hφ, map_map_symm] at h1`. Establish `h2 : ψ (((a : B.Aˣ) : B.A) * 1) = ψ (((b : B.Aˣ) : B.A) * 1)`. Rewrite using `[← mulMat_mulVec, ← mulMat_mulVec, h1]`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Simplify using `using ψ.injective h2`. Establish `hsurj : Function.Surjective φ`. Introduce `t`. Use `set T : Matrix (Fin n) (Fin n) (w.adicCompletion E) := (((t : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hT`. Use `set T' := T.map e.symm with hT'`.

Establish `hc : T * (((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) _) = (((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) _) * T`. Use `t.2` as an intermediate fact. Express the relevant statement in the definitionally equal form `(t : UL n w) * γ = γ * (t : UL n w) at this`. Use `congrArg (fun s : UL n w => ((s : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))) this` as an intermediate fact. Simplify using `using this`.

Establish `hc' : T' * mulMat B ψ B.g = mulMat B ψ B.g * T'`. Rewrite using `[← hγ', hT', ← Matrix.map_mul, ← Matrix.map_mul, hc]`. Set `f : B.A →ₗ[K.E] B.A` to `ψ.symm.toLinearMap ∘ₗ Matrix.toLin' T' ∘ₗ ψ.toLinearMap`. Establish `hfa : ∀ y, ψ (f y) = T' *ᵥ ψ y`. Introduce `y`.

Simplify using `[f]`. Establish `hf : ∀ y, f (B.g * y) = B.g * f y`. Introduce `y`. Apply `ψ.injective` to reduce the goal to its premises. Rewrite using `[hfa, ← mulMat_mulVec, ← mulMat_mulVec, hfa, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc']`.

Establish `ha : ∀ y, T' *ᵥ ψ y = ψ (f 1 * y)`. Introduce `y`. Rewrite using `[← hfa, commutant B hs f hf y]`. Establish `hM` using `eq_mulMat B ψ ha`. Establish `hTu : cT (cj w) T * 1 * T = 1`.

Establish `hULmem : ∀ g : GLw n w, g ∈ UL n w → g ∈ UJ (cj w) 1` using `fun g hg => by rwa [hUL] at hg`. Conclude with `hULmem _ (t : UL n w).2`. Establish `hu : f 1 * B.σ (f 1) = 1`. Rewrite using `[← isom_iff B ψ hm, stdH_mulVec_iff, ← hM, ← unitary_map e he, hT', map_symm_map]`. Conclude with `hTu`.

Set `u : B.Aˣ` to `⟨f 1, B.σ (f 1), hu, by rw [mul_comm]; exact hu⟩`. Use `⟨⟨u, hu⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `(mulMat B ψ (f 1)).map e = T`. Rewrite using `[← hM, hT', map_symm_map]`. Use `⟨(MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm, fun t y => ?_⟩` and prove the remaining obligations. Establish `h1 : φ ((MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm t) = t` using `(MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).apply_symm_apply t`. Use `conv_rhs => rw [← h1]`.

Rewrite using `[hφ, map_map_symm, mulMat_mulVec]`.
-/
theorem cent_equiv_torus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ) (γ : UL n w), IsModel B ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) x ψ → B.P.Separable → ∃ τ : twCent (MonoidHom.id (UL n w)) γ ≃* B.T, ∀ (t : twCent (MonoidHom.id (UL n w)) γ) (y : B.A), ψ (((τ t : B.Aˣ) : B.A) * y) = (((((t : UL n w) : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y := by
  intro E _ _ _ _ w hw K e he _ n B ψ x γ hm hs
  have hUL : UL n w = UJ (cj w) 1 := by simp [UL, hw]
  let ρ : B.A →* Matrix (Fin n) (Fin n) (w.adicCompletion E) :=
    (e.toRingHom.mapMatrix : Matrix (Fin n) (Fin n) K.E →+* _).toMonoidHom.comp (mulHom B ψ)
  have hρa : ∀ a, ρ a = (mulMat B ψ a).map e := fun a => rfl
  have hγ' := eq_mulMat B ψ (fun y => (hm.2.1 y).symm)
  have hγ : (((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = ρ B.g := by
    rw [hρa, ← hγ', map_symm_map]
  have hmem : ∀ u : B.Aˣ, u ∈ B.T → (Units.map ρ u : GLw n w) ∈ UL n w := by
    intro u hu
    rw [hUL]
    show cT (cj w) (((Units.map ρ u : GLw n w)) : Matrix (Fin n) (Fin n) _) * 1 * _ = 1
    rw [Units.coe_map, hρa, unitary_map e he, ← stdH_mulVec_iff, isom_iff B ψ hm]
    exact hu
  have hcent : ∀ (u : B.Aˣ) (hu : u ∈ B.T),
      (⟨Units.map ρ u, hmem u hu⟩ : UL n w) ∈ twCent (MonoidHom.id (UL n w)) γ := by
    intro u hu
    show _ * γ = γ * _
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, MonoidHom.id_apply, Units.coe_map, hγ]
    rw [← map_mul, ← map_mul, mul_comm]
  let φ : B.T →* twCent (MonoidHom.id (UL n w)) γ :=
    { toFun := fun u => ⟨⟨Units.map ρ u, hmem u u.2⟩, hcent u u.2⟩
      map_one' := by
        apply Subtype.ext; apply Subtype.ext; apply Units.ext
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext; apply Subtype.ext; apply Units.ext
        simp }
  have hφ : ∀ u : B.T, ((((φ u : twCent (MonoidHom.id (UL n w)) γ) : UL n w) : GLw n w) :
      Matrix (Fin n) (Fin n) (w.adicCompletion E)) = (mulMat B ψ ((u : B.Aˣ) : B.A)).map e := fun u => rfl
  have hinj : Function.Injective φ := by
    intro a b hab
    have h1 := congrArg (fun t : twCent (MonoidHom.id (UL n w)) γ =>
      (((t : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) hab
    simp only [hφ, map_map_symm] at h1
    have h2 : ψ (((a : B.Aˣ) : B.A) * 1) = ψ (((b : B.Aˣ) : B.A) * 1) := by
      rw [← mulMat_mulVec, ← mulMat_mulVec, h1]
    apply Subtype.ext; apply Units.ext
    simpa using ψ.injective h2
  have hsurj : Function.Surjective φ := by
    intro t
    set T : Matrix (Fin n) (Fin n) (w.adicCompletion E) := (((t : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hT
    set T' := T.map e.symm with hT'
    have hc : T * (((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) _) =
        (((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) _) * T := by
      have := t.2
      change (t : UL n w) * γ = γ * (t : UL n w) at this
      have := congrArg (fun s : UL n w => ((s : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))) this
      simpa using this
    have hc' : T' * mulMat B ψ B.g = mulMat B ψ B.g * T' := by
      rw [← hγ', hT', ← Matrix.map_mul, ← Matrix.map_mul, hc]
    let f : B.A →ₗ[K.E] B.A := ψ.symm.toLinearMap ∘ₗ Matrix.toLin' T' ∘ₗ ψ.toLinearMap
    have hfa : ∀ y, ψ (f y) = T' *ᵥ ψ y := by
      intro y; simp [f]
    have hf : ∀ y, f (B.g * y) = B.g * f y := by
      intro y
      apply ψ.injective
      rw [hfa, ← mulMat_mulVec, ← mulMat_mulVec, hfa, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc']
    have ha : ∀ y, T' *ᵥ ψ y = ψ (f 1 * y) := by
      intro y; rw [← hfa, commutant B hs f hf y]
    have hM := eq_mulMat B ψ ha
    have hTu : cT (cj w) T * 1 * T = 1 := by
      have hULmem : ∀ g : GLw n w, g ∈ UL n w → g ∈ UJ (cj w) 1 := fun g hg => by rwa [hUL] at hg
      exact hULmem _ (t : UL n w).2
    have hu : f 1 * B.σ (f 1) = 1 := by
      rw [← isom_iff B ψ hm, stdH_mulVec_iff, ← hM, ← unitary_map e he, hT', map_symm_map]
      exact hTu
    let u : B.Aˣ := ⟨f 1, B.σ (f 1), hu, by rw [mul_comm]; exact hu⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    change (mulMat B ψ (f 1)).map e = T
    rw [← hM, hT', map_symm_map]
  refine ⟨(MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm, fun t y => ?_⟩
  have h1 : φ ((MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm t) = t :=
    (MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).apply_symm_apply t
  conv_rhs => rw [← h1]
  rw [hφ, map_map_symm, mulMat_mulVec]

end GlobalTheory.CentTorusModel

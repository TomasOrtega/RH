import Mathlib

open TensorProduct in
/- English proof (translation)
Use `haveI : Module.Free A (A ⊗[B] Ω[B⁄A]) := Module.free_of_flat_of_isLocalRing`. Set `e` to `Module.finBasis A (A ⊗[B] Ω[B⁄A])`. Set `D0 : Derivation A B (A ⊗[B] Ω[B⁄A])` to `(TensorProduct.mk B A Ω[B⁄A] 1).compDer (KaehlerDifferential.D A B)`. Establish `hD0 : ∀ b, D0 b = 1 ⊗ₜ KaehlerDifferential.D A B b` using `fun b => rfl`. Establish `hsurj : Function.Surjective D0`.

Establish `h1 : ∀ (w : Ω[B⁄A]) (a : A), a ⊗ₜ[B] w ∈ LinearMap.range D0.toLinearMap`. Introduce `w`. Establish `hw : w ∈ Submodule.span B (Set.range (KaehlerDifferential.D A B))`. Rewrite using `[KaehlerDifferential.span_range_derivation]`. Discharge the goal by the elementary cases of `trivial`.

Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨b, rfl⟩` from `hx`. Introduce `a`. Establish `: a ⊗ₜ[B] KaehlerDifferential.D A B b = a • D0 b`.

Rewrite using `[hD0, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ ⟨b, rfl⟩`. Consider the case `zero => intro a`. Simplify using the standard rewrite rules.

Consider the case `add x y _ _ hx hy`. Introduce `a`. Rewrite using `[TensorProduct.tmul_add]`. Conclude with `add_mem (hx a) (hy a)`. Consider the case `smul b x _ hx`.

Introduce `a`. Rewrite using `[← TensorProduct.smul_tmul]`. Conclude with `hx _`. Introduce `x`. Express the relevant statement in the definitionally equal form `x ∈ LinearMap.range D0.toLinearMap`.

Proceed by induction on `x with`. Consider the case `zero => simp`. Consider the case `tmul a w => exact h1 w a`. Consider the case `add x y hx hy => exact add_mem hx hy`. Use `⟨_, (e.equivFun.toLinearMap.restrictScalars B).compDer D0, e.equivFun.surjective.comp hsurj, ?_⟩` and prove the remaining obligations.

Introduce `R _ _ _ _ δ`. Use `haveI : IsScalarTower A B R := ⟨fun a b r => by`. Rewrite using `[← algebraMap_smul A (a • b) r, ← algebraMap_smul A b r, ← mul_smul]`. Use `congr 1`. Rewrite using `[Algebra.algebraMap_eq_smul_one, smul_assoc, ← Algebra.algebraMap_eq_smul_one, smul_eq_mul]⟩`.

Set `f : A ⊗[B] Ω[B⁄A] →ₗ[A] R` to `δ.liftKaehlerDifferential.liftBaseChange A`. Use `⟨fun i => f (e i), fun b => ?_⟩` and prove the remaining obligations. Establish `h2 : δ b = f (D0 b)`. Simplify using `[f, hD0]`. Rewrite using `[h2]`.

Use `conv_lhs => rw [← e.sum_equivFun (D0 b), map_sum]`. Simplify using `only [map_smul]`. Both sides reduce to the same expression.
-/
private theorem UpperTheory.universal_derivation_surjective {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B]
    [Algebra A B] [Algebra B A] [IsScalarTower A B A]
    [Algebra.FormallySmooth A B] [Algebra.EssFiniteType A B] :
    ∃ (n : ℕ) (d : Derivation A B (Fin n → A)), Function.Surjective d ∧
      ∀ (R : Type) [AddCommGroup R] [Module A R] [Module B R] [IsScalarTower B A R]
        (δ : Derivation A B R), ∃ c : Fin n → R, ∀ b, δ b = ∑ i, d b i • c i := by
  haveI : Module.Free A (A ⊗[B] Ω[B⁄A]) := Module.free_of_flat_of_isLocalRing
  let e := Module.finBasis A (A ⊗[B] Ω[B⁄A])
  let D0 : Derivation A B (A ⊗[B] Ω[B⁄A]) :=
    (TensorProduct.mk B A Ω[B⁄A] 1).compDer (KaehlerDifferential.D A B)
  have hD0 : ∀ b, D0 b = 1 ⊗ₜ KaehlerDifferential.D A B b := fun b => rfl
  have hsurj : Function.Surjective D0 := by
    have h1 : ∀ (w : Ω[B⁄A]) (a : A), a ⊗ₜ[B] w ∈ LinearMap.range D0.toLinearMap := by
      intro w
      have hw : w ∈ Submodule.span B (Set.range (KaehlerDifferential.D A B)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, rfl⟩ := hx
        intro a
        have : a ⊗ₜ[B] KaehlerDifferential.D A B b = a • D0 b := by
          rw [hD0, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this]
        exact Submodule.smul_mem _ _ ⟨b, rfl⟩
      | zero => intro a; simp
      | add x y _ _ hx hy =>
        intro a
        rw [TensorProduct.tmul_add]
        exact add_mem (hx a) (hy a)
      | smul b x _ hx =>
        intro a
        rw [← TensorProduct.smul_tmul]
        exact hx _
    intro x
    change x ∈ LinearMap.range D0.toLinearMap
    induction x with
    | zero => simp
    | tmul a w => exact h1 w a
    | add x y hx hy => exact add_mem hx hy
  refine ⟨_, (e.equivFun.toLinearMap.restrictScalars B).compDer D0,
    e.equivFun.surjective.comp hsurj, ?_⟩
  intro R _ _ _ _ δ
  haveI : IsScalarTower A B R := ⟨fun a b r => by
    rw [← algebraMap_smul A (a • b) r, ← algebraMap_smul A b r, ← mul_smul]
    congr 1
    rw [Algebra.algebraMap_eq_smul_one, smul_assoc, ← Algebra.algebraMap_eq_smul_one, smul_eq_mul]⟩
  let f : A ⊗[B] Ω[B⁄A] →ₗ[A] R := δ.liftKaehlerDifferential.liftBaseChange A
  refine ⟨fun i => f (e i), fun b => ?_⟩
  have h2 : δ b = f (D0 b) := by
    simp [f, hD0]
  rw [h2]
  conv_lhs => rw [← e.sum_equivFun (D0 b), map_sum]
  simp only [map_smul]
  rfl

/- English proof (translation)
Introduce `A B _ _ _ α σ hσ hfs hft`. Establish `hσ' : ∀ a, σ (α a) = a` using `fun a => RingHom.congr_fun hσ a`. Use `letI : Algebra A B := α.toAlgebra`. Use `letI : Algebra B A := σ.toAlgebra`. Use `haveI : IsScalarTower A B A := IsScalarTower.of_algebraMap_eq fun a => (hσ' a).symm`.

Use `haveI : Algebra.FormallySmooth A B := hfs`. Use `haveI : Algebra.EssFiniteType A B := hft`. Take `⟨n, d, hd, H⟩` from `UpperTheory.universal_derivation_surjective (A := A) (B := B)`. Establish `hmul : ∀ x y i, d (x * y) i = σ x * d y i + σ y * d x i` using `fun x y i => by`. Rewrite using `[d.leibniz]`.

Both sides reduce to the same expression. Establish `hα : ∀ a, d (α a) = 0` using `fun a => d.map_algebraMap a`. Use `⟨n, d, hd, fun R _ φ => ⟨fun c => ?_, fun g hg1 hg2 => ?_⟩⟩` and prove the remaining obligations. Use `⟨{ toFun := fun b => TrivSqZeroExt.inl (φ (σ b)) + TrivSqZeroExt.inr (∑ i, φ (d b i) * c i) map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp`.

Introduce `x y`. Use `ext`. Simplify using the standard rewrite rules. Simplify using `[hmul, -Derivation.leibniz, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, mul_add, add_comm]`. Apply the tactic sequence `ext <;> simp`.

Introduce `x y`. Apply the tactic sequence `ext <;> simp [add_mul, Finset.sum_add_distrib]`. Introduce `a`. Simplify using `[hα, hσ']`. Introduce `b`.

Simplify using the standard rewrite rules. Introduce `b`. Simplify using the standard rewrite rules. Use `letI : Algebra A R := φ.toAlgebra`. Use `letI : Algebra B R := (φ.comp σ).toAlgebra`.

Use `haveI : IsScalarTower B A R := IsScalarTower.of_algebraMap_eq fun b => rfl`. Set `δ : Derivation A B R` to `Derivation.mk' { toFun := fun b => (g b).snd map_add' := fun x y => by simp map_smul' := fun a b => by`. Express the relevant statement in the definitionally equal form `(g (α a * b)).snd = φ a * (g b).snd`. Simplify using `[hg1] }`. Use the proof step `(fun x y => by`.

Express the relevant statement in the definitionally equal form `(g (x * y)).snd = φ (σ x) * (g y).snd + φ (σ y) * (g x).snd`. Simplify using `[hg2, mul_comm])`. Conclude with `H R δ`.
-/
theorem UpperTheory.formally_smooth_surjective_derivation :
    ∀ {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] (α : A →+* B) (σ : B →+* A),
        σ.comp α = RingHom.id A → α.FormallySmooth → α.EssFiniteType →
          ∃ (n : ℕ) (d : B → Fin n → A), Function.Surjective d ∧
            ∀ (R : Type) [CommRing R] (φ : A →+* R),
              (∀ c : Fin n → R, ∃ g : B →+* DualNumber R,
                (∀ a, g (α a) = TrivSqZeroExt.inl (φ a)) ∧ (∀ b, (g b).fst = φ (σ b)) ∧
                  ∀ b, (g b).snd = ∑ i, φ (d b i) * c i) ∧
              ∀ g : B →+* DualNumber R, (∀ a, g (α a) = TrivSqZeroExt.inl (φ a)) → (∀ b, (g b).fst = φ (σ b)) →
                ∃ c : Fin n → R, ∀ b, (g b).snd = ∑ i, φ (d b i) * c i := by
  intro A B _ _ _ α σ hσ hfs hft
  have hσ' : ∀ a, σ (α a) = a := fun a => RingHom.congr_fun hσ a
  letI : Algebra A B := α.toAlgebra
  letI : Algebra B A := σ.toAlgebra
  haveI : IsScalarTower A B A := IsScalarTower.of_algebraMap_eq fun a => (hσ' a).symm
  haveI : Algebra.FormallySmooth A B := hfs
  haveI : Algebra.EssFiniteType A B := hft
  obtain ⟨n, d, hd, H⟩ := UpperTheory.universal_derivation_surjective (A := A) (B := B)
  have hmul : ∀ x y i, d (x * y) i = σ x * d y i + σ y * d x i := fun x y i => by
    rw [d.leibniz]; rfl
  have hα : ∀ a, d (α a) = 0 := fun a => d.map_algebraMap a
  refine ⟨n, d, hd, fun R _ φ => ⟨fun c => ?_, fun g hg1 hg2 => ?_⟩⟩
  · refine ⟨{ toFun := fun b => TrivSqZeroExt.inl (φ (σ b)) +
                TrivSqZeroExt.inr (∑ i, φ (d b i) * c i)
              map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_, ?_, ?_⟩
    · ext <;> simp
    · intro x y
      ext
      · simp
      · simp [hmul, -Derivation.leibniz, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
          Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, mul_add, add_comm]
    · ext <;> simp
    · intro x y
      ext <;> simp [add_mul, Finset.sum_add_distrib]
    · intro a
      simp [hα, hσ']
    · intro b
      simp
    · intro b
      simp
  · letI : Algebra A R := φ.toAlgebra
    letI : Algebra B R := (φ.comp σ).toAlgebra
    haveI : IsScalarTower B A R := IsScalarTower.of_algebraMap_eq fun b => rfl
    let δ : Derivation A B R := Derivation.mk'
      { toFun := fun b => (g b).snd
        map_add' := fun x y => by simp
        map_smul' := fun a b => by
          change (g (α a * b)).snd = φ a * (g b).snd
          simp [hg1] }
      (fun x y => by
        change (g (x * y)).snd = φ (σ x) * (g y).snd + φ (σ y) * (g x).snd
        simp [hg2, mul_comm])
    exact H R δ

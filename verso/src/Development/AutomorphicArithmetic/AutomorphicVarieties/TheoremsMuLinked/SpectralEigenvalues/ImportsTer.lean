import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.Msp

open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

/- English proof (translation)
Introduce `O R B M V _ _ _ _ _ _ _ _ _ q n β x P act f α I t₀ hβ hTM hP hker a ha v`. Take `⟨φ, ψ, h1, h2, h3, h4⟩` from `hTM`. Establish `hπC : ∀ b : B, (Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.C b) = algebraMap B (MSplitAlg P n) b` using `fun b => rfl`. Establish `key : ∀ i ∈ I, ∀ w : MSplitAlg P n ⊗[B] M, φ ((β i) • w) ∈ (I • ⊤ : Submodule R V)`. Introduce `i hi w`.

Establish `e1 : (β i) • w = (Ideal.Quotient.mk (mSplitIdeal P n)) ((MvPolynomial.map β.toRingHom) (MvPolynomial.C i)) • w`. Rewrite using `[MvPolynomial.map_C, hπC, algebraMap_smul]`. Both sides reduce to the same expression. Rewrite using `[e1, h1, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, Module.algebraMap_end_apply]`. Conclude with `Submodule.smul_mem_smul hi trivial`.

Establish `claim : ∀ b : B, x b = 0 → ∀ z : MSplitAlg P n ⊗[B] M, φ (algebraMap B (MSplitAlg P n) (β t₀ * b) • z) ∈ (I • ⊤ : Submodule R V)`. Introduce `b hb z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul s m`.

Rewrite using `[algebraMap_smul, ← TensorProduct.tmul_smul]`. Use `Submodule.smul_induction_on (p := fun y => φ (s ⊗ₜ[B] y) ∈ (I • ⊤ : Submodule R V)) (hker b hb m) ?_ ?_` and prove the remaining obligations. Introduce `r hr m' _`. Take `⟨i, hi, rfl⟩` from `(Ideal.mem_map_iff_of_surjective β hβ).mp hr`. Rewrite using `[TensorProduct.tmul_smul]`.

Conclude with `key i hi _`. Introduce `y1 y2 k1 k2`. Rewrite using `[TensorProduct.tmul_add, map_add]`. Conclude with `add_mem k1 k2`. Consider the case `add z1 z2 k1 k2`.

Rewrite using `[smul_add, map_add]`. Conclude with `add_mem k1 k2`. Establish `gen : ∀ y ∈ Ideal.map (algebraMap B (MSplitAlg P n)) (RingHom.ker x), ∀ z : MSplitAlg P n ⊗[B] M, φ ((algebraMap B (MSplitAlg P n) (β t₀) * y) • z) ∈ (I • ⊤ : Submodule R V)`. Introduce `y hy`. Unfold `Ideal.map at hy`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨b, hb, rfl⟩` from `hy`. Introduce `z`. Rewrite using `[← map_mul]`.

Conclude with `claim b (RingHom.mem_ker.mp hb) z`. Consider the case `zero => intro z`. Simplify using the standard rewrite rules. Consider the case `add y1 y2 _ _ k1 k2`. Introduce `z`.

Rewrite using `[mul_add, add_smul, map_add]`. Conclude with `add_mem (k1 z) (k2 z)`. Consider the case `smul r y _ k`. Introduce `z`. Rewrite using `[smul_eq_mul, mul_left_comm, mul_comm r, mul_smul]`.

Conclude with `k _`. Establish `hE : MvPolynomial.map β.toRingHom (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i, (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k))) : PU R q n) = ∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i, (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k)))`. Simplify using `[map_prod]`. Establish `hmem` using `Sp.msp O B (Fin q) n x P α hP (MvPolynomial.map β.toRingHom a) (by rw [MvPolynomial.eval₂_map]; exact ha)`. Establish `e3 : act (MvPolynomial.C t₀ * (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i, (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k)))) * f * a) v = φ (((Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.map β.toRingHom (MvPolynomial.C t₀ * (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i, ( …`.

Rewrite using `[mul_smul, ← h2, h1, h3]`. Simplify using `only [map_mul, Module.End.mul_apply]`. Rewrite using `[e3]`. Establish `e4 : (Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.map β.toRingHom (MvPolynomial.C t₀ * (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i, (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k)))))) * (Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.map β.toRingHom a) = alge …`. Rewrite using `[map_mul (MvPolynomial.map β.toRingHom), hE, MvPolynomial.map_C, ← hπC, ← map_mul, ← map_mul, mul_assoc]`.

Both sides reduce to the same expression. Rewrite using `[e4]`. Conclude with `gen _ hmem _`.
-/
theorem UpperTheory.V.Th.Sp.kill :
    ∀ (O R B M V : Type) [CommRing O] [CommRing R] [CommRing B] [Algebra O R] [Algebra O B] [AddCommGroup M] [Module B M] [AddCommGroup V] [Module R V] (q n : ℕ) (β : R →ₐ[O] B) (x : B →ₐ[O] O) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) (f : PU R q n) (α : Fin q → Fin n → O) (I : Ideal R) (t₀ : R), Function.Surjective β → TwoMaps (M := M) β.toRingHom P act f → (∀ j, (P j).map (x : B →+* O) = ∏ i, (Polynomial.X - Polynomial.C (α j i))) → (∀ a : B, x a = 0 → ∀ m : M, (β t₀ * a) • m ∈ (I.map β • ⊤ : Submodule B M)) → ∀ a : PU R q n, MvPolynomial.eval₂ ((x.comp β : R →ₐ[O] O) : R →+* O) (fun p => α p.1 p.2) a = 0 → ∀ v : V, act (MvPolynomial.C t₀ * (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i, (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k)))) * f * a) v ∈ (I • ⊤ : Submodule R V) := by
  intro O R B M V _ _ _ _ _ _ _ _ _ q n β x P act f α I t₀ hβ hTM hP hker a ha v
  obtain ⟨φ, ψ, h1, h2, h3, h4⟩ := hTM
  have hπC : ∀ b : B, (Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.C b) =
      algebraMap B (MSplitAlg P n) b := fun b => rfl
  have key : ∀ i ∈ I, ∀ w : MSplitAlg P n ⊗[B] M, φ ((β i) • w) ∈ (I • ⊤ : Submodule R V) := by
    intro i hi w
    have e1 : (β i) • w = (Ideal.Quotient.mk (mSplitIdeal P n))
        ((MvPolynomial.map β.toRingHom) (MvPolynomial.C i)) • w := by
      rw [MvPolynomial.map_C, hπC, algebraMap_smul]
      rfl
    rw [e1, h1, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, Module.algebraMap_end_apply]
    exact Submodule.smul_mem_smul hi trivial
  have claim : ∀ b : B, x b = 0 → ∀ z : MSplitAlg P n ⊗[B] M,
      φ (algebraMap B (MSplitAlg P n) (β t₀ * b) • z) ∈ (I • ⊤ : Submodule R V) := by
    intro b hb z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
      rw [algebraMap_smul, ← TensorProduct.tmul_smul]
      refine Submodule.smul_induction_on (p := fun y => φ (s ⊗ₜ[B] y) ∈ (I • ⊤ : Submodule R V))
        (hker b hb m) ?_ ?_
      · intro r hr m' _
        obtain ⟨i, hi, rfl⟩ := (Ideal.mem_map_iff_of_surjective β hβ).mp hr
        rw [TensorProduct.tmul_smul]
        exact key i hi _
      · intro y1 y2 k1 k2
        rw [TensorProduct.tmul_add, map_add]
        exact add_mem k1 k2
    | add z1 z2 k1 k2 =>
      rw [smul_add, map_add]
      exact add_mem k1 k2
  have gen : ∀ y ∈ Ideal.map (algebraMap B (MSplitAlg P n)) (RingHom.ker x), ∀ z : MSplitAlg P n ⊗[B] M,
      φ ((algebraMap B (MSplitAlg P n) (β t₀) * y) • z) ∈ (I • ⊤ : Submodule R V) := by
    intro y hy
    unfold Ideal.map at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      intro z
      rw [← map_mul]
      exact claim b (RingHom.mem_ker.mp hb) z
    | zero => intro z; simp
    | add y1 y2 _ _ k1 k2 =>
      intro z
      rw [mul_add, add_smul, map_add]
      exact add_mem (k1 z) (k2 z)
    | smul r y _ k =>
      intro z
      rw [smul_eq_mul, mul_left_comm, mul_comm r, mul_smul]
      exact k _
  have hE : MvPolynomial.map β.toRingHom (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
      (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k))) : PU R q n) =
      ∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
      (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k))) := by
    simp [map_prod]
  have hmem := Sp.msp O B (Fin q) n x P α hP (MvPolynomial.map β.toRingHom a)
    (by rw [MvPolynomial.eval₂_map]; exact ha)
  have e3 : act (MvPolynomial.C t₀ * (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
      (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k)))) * f * a) v =
      φ (((Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.map β.toRingHom (MvPolynomial.C t₀ *
        (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k)))))) *
        (Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.map β.toRingHom a)) • ψ v) := by
    rw [mul_smul, ← h2, h1, h3]
    simp only [map_mul, Module.End.mul_apply]
  rw [e3]
  have e4 : (Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.map β.toRingHom (MvPolynomial.C t₀ *
        (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k)))))) *
        (Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.map β.toRingHom a) =
      algebraMap B (MSplitAlg P n) (β t₀) * (Ideal.Quotient.mk (mSplitIdeal P n))
        ((∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k)))) *
          MvPolynomial.map β.toRingHom a) := by
    rw [map_mul (MvPolynomial.map β.toRingHom), hE, MvPolynomial.map_C, ← hπC, ← map_mul, ← map_mul,
      mul_assoc]
    rfl
  rw [e4]
  exact gen _ hmem _

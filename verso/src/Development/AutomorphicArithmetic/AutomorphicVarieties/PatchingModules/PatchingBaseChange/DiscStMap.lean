import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
private theorem tr_map {n : ℕ} {R R' G : Type} [CommRing R] [CommRing R'] [Group G] (D : GDet n R G)
    (f : R →+* R') (x : G) :
    (D.map f).tr (MonoidAlgebra.single x 1) = f (D.tr (MonoidAlgebra.single x 1)) := by
  have h := ((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single x 1)).2 1
  rw [MonoidAlgebra.mapRingHom_single, map_one] at h
  exact h

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
private theorem tr_comap {n : ℕ} {R G G' : Type} [CommRing R] [Group G] [Group G'] (D : GDet n R G)
    (p : G' →* G) (x : G') :
    (D.comap p).tr (MonoidAlgebra.single x 1) = D.tr (MonoidAlgebra.single (p x) 1) := by
  unfold GDet.tr GDet.lam GDet.comap GDet.chi
  simp only [MonoidAlgebra.mapRingHom_single, map_one, MonoidHom.coe_comp, Function.comp_apply]
  have hY : ((MonoidAlgebra.mapDomainRingHom (Polynomial R) p :
        MonoidAlgebra (Polynomial R) G' →+* MonoidAlgebra (Polynomial R) G) :
        MonoidAlgebra (Polynomial R) G' →* MonoidAlgebra (Polynomial R) G)
      (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.single x 1) =
      MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.single (p x) 1 := by
    change (MonoidAlgebra.mapDomainRingHom (Polynomial R) p)
      (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.single x 1) = _
    rw [map_sub, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapDomain_single, map_one]
  exact congrArg (fun y => (-1) ^ 1 * ((D.D (Polynomial R)) y).coeff (n - 1)) hY

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Replace the relevant objects with their definitions. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Pa.BC.discSt_map :
    ∀ (n : ℕ) (R R' G : Type) [CommRing R] [CommRing R'] [Group G] (D : GDet n R G), (∀ (g : R →+* R') (Q : Ideal R'), DiscSt (D.map g) Q ↔ DiscSt D (Q.comap g)) ∧ (∀ (G' : Type) [Group G'] (p : G' →* G), Function.Surjective p → ∀ Q : Ideal R, DiscSt (D.comap p) Q ↔ DiscSt D Q) ∧ ∀ Q Q' : Ideal R, Q ≤ Q' → DiscSt D Q' → DiscSt D Q := by
  intro n R R' G _ _ _ D
  refine ⟨fun g Q => ?_, fun G' _ p hp Q => ?_, fun Q Q' hQ hD => ?_⟩
  · unfold DiscSt
    have key : ∀ a b : Fin (n * n) → G,
        (Matrix.of fun i j => (D.map g).tr (MonoidAlgebra.single (a i * b j) 1)).det =
        g ((Matrix.of fun i j => D.tr (MonoidAlgebra.single (a i * b j) 1)).det) := by
      intro a b
      rw [RingHom.map_det]
      congr 1
      ext i j
      simp [RingHom.mapMatrix_apply, tr_map]
    simp only [key, Ideal.mem_comap]
  · unfold DiscSt
    have key : ∀ a b : Fin (n * n) → G',
        (Matrix.of fun i j => (D.comap p).tr (MonoidAlgebra.single (a i * b j) 1)) =
        Matrix.of fun i j => D.tr (MonoidAlgebra.single (p (a i) * p (b j)) 1) := by
      intro a b
      ext i j
      simp [tr_comap]
    constructor
    · rintro ⟨a, b, h⟩
      exact ⟨fun i => p (a i), fun j => p (b j), by simpa only [key] using h⟩
    · rintro ⟨a, b, h⟩
      refine ⟨fun i => Function.surjInv hp (a i), fun j => Function.surjInv hp (b j), ?_⟩
      simp only [key, Function.surjInv_eq hp]
      exact h
  · obtain ⟨a, b, h⟩ := hD
    exact ⟨a, b, fun hq => h (hQ hq)⟩

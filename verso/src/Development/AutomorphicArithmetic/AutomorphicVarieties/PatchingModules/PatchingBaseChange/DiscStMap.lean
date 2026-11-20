import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

/- English proof (translation)
Establish `h` using `((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single x 1)).2 1`. Rewrite `h` using `[MonoidAlgebra.mapRingHom_single, map_one]`. Conclude with `h`.
-/
private theorem tr_map {n : ℕ} {R R' G : Type} [CommRing R] [CommRing R'] [Group G] (D : GDet n R G)
    (f : R →+* R') (x : G) :
    (D.map f).tr (MonoidAlgebra.single x 1) = f (D.tr (MonoidAlgebra.single x 1)) := by
  have h := ((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single x 1)).2 1
  rw [MonoidAlgebra.mapRingHom_single, map_one] at h
  exact h

/- English proof (translation)
Unfold `GDet.tr GDet.lam GDet.comap GDet.chi`. Simplify using `only [MonoidAlgebra.mapRingHom_single, map_one, MonoidHom.coe_comp, Function.comp_apply]`. Establish `hY : ((MonoidAlgebra.mapDomainRingHom (Polynomial R) p : MonoidAlgebra (Polynomial R) G' →+* MonoidAlgebra (Polynomial R) G) : MonoidAlgebra (Polynomial R) G' →* MonoidAlgebra (Polynomial R) G) (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.single x 1) = MonoidAlgebra.singl …`. Express the relevant statement in the definitionally equal form `(MonoidAlgebra.mapDomainRingHom (Polynomial R) p) (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.single x 1) = _`. Rewrite using `[map_sub, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapDomain_single, map_one]`.

Conclude with `congrArg (fun y => (-1) ^ 1 * ((D.D (Polynomial R)) y).coeff (n - 1)) hY`.
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
Introduce `n R R' G _ _ _ D`. Use `⟨fun g Q => ?_, fun G' _ p hp Q => ?_, fun Q Q' hQ hD => ?_⟩` and prove the remaining obligations. Unfold `DiscSt`. Establish `key : ∀ a b : Fin (n * n) → G, (Matrix.of fun i j => (D.map g).tr (MonoidAlgebra.single (a i * b j) 1)).det = g ((Matrix.of fun i j => D.tr (MonoidAlgebra.single (a i * b j) 1)).det)`. Introduce `a b`.

Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[RingHom.mapMatrix_apply, tr_map]`. Simplify using `only [key, Ideal.mem_comap]`.

Unfold `DiscSt`. Establish `key : ∀ a b : Fin (n * n) → G', (Matrix.of fun i j => (D.comap p).tr (MonoidAlgebra.single (a i * b j) 1)) = Matrix.of fun i j => D.tr (MonoidAlgebra.single (p (a i) * p (b j)) 1)`. Introduce `a b`. Use extensionality with `i j`. Simplify using `[tr_comap]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, b, h⟩`. Conclude with `⟨fun i => p (a i), fun j => p (b j), by simpa only [key] using h⟩`. Introduce and unpack `⟨a, b, h⟩`. Use `⟨fun i => Function.surjInv hp (a i), fun j => Function.surjInv hp (b j), ?_⟩` and prove the remaining obligations.

Simplify using `only [key, Function.surjInv_eq hp]`. Conclude with `h`. Take `⟨a, b, h⟩` from `hD`. Conclude with `⟨a, b, fun hq => h (hQ hq)⟩`.
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

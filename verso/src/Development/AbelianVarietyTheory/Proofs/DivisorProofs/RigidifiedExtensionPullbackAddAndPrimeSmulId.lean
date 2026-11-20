import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

noncomputable section

namespace GlobalTheory.PDiv

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]

variable (R A) in

def restrZeroLeft : A ⊗[R] A →ₗ[R] A :=
  (TensorProduct.lid R A).toLinearMap ∘ₗ (counit (R := R) (A := A)).rTensor A

/- English proof (translation)
Simplify using `[restrZeroLeft]`.
-/
theorem restrZeroLeft_tmul (a b : A) : restrZeroLeft R A (a ⊗ₜ b) = counit (R := R) a • b := by
  simp [restrZeroLeft]

/- English proof (translation)
Simplify using `[restrZeroLeft, Coalgebra.rTensor_counit_comul]`.
-/
theorem restrZeroLeft_comul (a : A) : restrZeroLeft R A (comul a) = a := by
  simp [restrZeroLeft, Coalgebra.rTensor_counit_comul]

variable (R A) in

def restrZeroZero : A ⊗[R] (A ⊗[R] A) →ₗ[R] A :=
  (TensorProduct.lid R A).toLinearMap ∘ₗ TensorProduct.map (counit (R := R) (A := A))
    (restrZeroLeft R A)

/- English proof (translation)
Simplify using `[restrZeroZero]`.
-/
theorem restrZeroZero_tmul (a : A) (t : A ⊗[R] A) :
    restrZeroZero R A (a ⊗ₜ t) = counit (R := R) a • restrZeroLeft R A t := by
  simp [restrZeroZero]

/- English proof (translation)
Proceed by induction on `u with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [add_tmul, map_add, hx, hy, add_smul]`. Consider the case `tmul x y`. Rewrite using `[TensorProduct.assoc_tmul, restrZeroZero_tmul, restrZeroLeft_tmul, restrZeroLeft_tmul, map_smul, smul_eq_mul, mul_smul]`.
-/
theorem restrZeroZero_assoc (u : A ⊗[R] A) (b : A) :
    restrZeroZero R A (TensorProduct.assoc R A A A (u ⊗ₜ b)) =
      counit (R := R) (restrZeroLeft R A u) • b := by
  induction u with
  | zero => simp
  | add x y hx hy => simp only [add_tmul, map_add, hx, hy, add_smul]
  | tmul x y =>
    rw [TensorProduct.assoc_tmul, restrZeroZero_tmul, restrZeroLeft_tmul, restrZeroLeft_tmul,
      map_smul, smul_eq_mul, mul_smul]

/- English proof (translation)
Establish `key : ∀ t : A ⊗[R] A, restrZeroZero R A (cobTwo R A t) = restrZeroLeft R A t - algebraMap R A (TensorProduct.lid R R (TensorProduct.map (counit (R` using `R) (A := A)) (counit (R := R) (A := A)) t)) := fun t => by`. Proceed by induction on `t with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Normalize the expressions using the abelian group laws.

Consider the case `tmul a b`. Rewrite using `[cobTwo_apply]`. Simplify using `only [map_sub, map_add, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, LinearMap.flip_apply, TensorProduct.mk_apply, restrZeroZero_assoc, restrZeroZero_tmul, restrZeroLeft_comul, restrZeroLeft_tmul, Bialgebra.counit_one, one_smul, TensorProduct.map_tmul, TensorProduct.lid_tmul, …`. Normalize the expressions using the abelian group laws. Use `key c` as an intermediate fact.

Rewrite `this` using `[hc, map_zero]`. Conclude with `(sub_eq_zero.1 this.symm)`.
-/
theorem restrZeroLeft_of_cobTwo_eq_zero {c : A ⊗[R] A} (hc : cobTwo R A c = 0) :
    restrZeroLeft R A c =
      algebraMap R A (TensorProduct.lid R R (TensorProduct.map (counit (R := R) (A := A))
        (counit (R := R) (A := A)) c)) := by
  have key : ∀ t : A ⊗[R] A, restrZeroZero R A (cobTwo R A t) = restrZeroLeft R A t -
      algebraMap R A (TensorProduct.lid R R (TensorProduct.map (counit (R := R) (A := A))
        (counit (R := R) (A := A)) t)) := fun t => by
    induction t with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]; abel
    | tmul a b =>
      rw [cobTwo_apply]
      simp only [map_sub, map_add, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, LinearMap.flip_apply,
        TensorProduct.mk_apply, restrZeroZero_assoc, restrZeroZero_tmul, restrZeroLeft_comul,
        restrZeroLeft_tmul, Bialgebra.counit_one, one_smul, TensorProduct.map_tmul,
        TensorProduct.lid_tmul, smul_eq_mul, Algebra.algebraMap_eq_smul_one, mul_smul]
      abel
  have := key c
  rw [hc, map_zero] at this
  exact (sub_eq_zero.1 this.symm)

end GlobalTheory.PDiv

namespace GlobalTheory.PDiv

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]

/- English proof (translation)
Proceed by induction on `t with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Normalize the expressions using the abelian group laws. Consider the case `tmul a b`.

Establish `e1 : dUnit R (counit (R` using `R) a • b) = counit (R := R) a • dUnit R b := map_smul (AugCot.d _) _ _`. Establish `e2 : dUnit R (counit (R` using `R) b • a) = counit (R := R) b • dUnit R a := map_smul (AugCot.d _) _ _`. Rewrite using `[TensorProduct.map_tmul, LinearMap.mul'_apply, TensorProduct.comm_tmul, restrZeroLeft_tmul, restrZeroLeft_tmul, e1, e2, map_smul, map_smul, cotMap_d, cotMap_d, dUnit, AugCot.d_mul]`. Establish `c1 : counitAlgHom R B (f a) = counit (R` using `R) a := CoalgHomClass.counit_comp_apply f a`. Establish `c2 : counitAlgHom R B (g b) = counit (R` using `R) b := CoalgHomClass.counit_comp_apply g b`.

Conclude with `congrArg₂ (· + ·) (congrArg₂ (· • ·) c1 rfl) (congrArg₂ (· • ·) c2 rfl)`.
-/
theorem dUnit_mul'_map (f g : A →ₐc[R] B) (t : A ⊗[R] A) :
    dUnit R (LinearMap.mul' R B (TensorProduct.map (f : A →ₗ[R] B) (g : A →ₗ[R] B) t)) =
      cotMap g (dUnit R (restrZeroLeft R A t)) +
        cotMap f (dUnit R (restrZeroLeft R A (TensorProduct.comm R A A t))) := by
  induction t with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | tmul a b =>
    have e1 : dUnit R (counit (R := R) a • b) = counit (R := R) a • dUnit R b :=
      map_smul (AugCot.d _) _ _
    have e2 : dUnit R (counit (R := R) b • a) = counit (R := R) b • dUnit R a :=
      map_smul (AugCot.d _) _ _
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply, TensorProduct.comm_tmul, restrZeroLeft_tmul,
      restrZeroLeft_tmul, e1, e2, map_smul, map_smul, cotMap_d, cotMap_d, dUnit, AugCot.d_mul]
    have c1 : counitAlgHom R B (f a) = counit (R := R) a := CoalgHomClass.counit_comp_apply f a
    have c2 : counitAlgHom R B (g b) = counit (R := R) b := CoalgHomClass.counit_comp_apply g b
    exact congrArg₂ (· + ·) (congrArg₂ (· • ·) c1 rfl) (congrArg₂ (· • ·) c2 rfl)

/- English proof (translation)
Take `⟨h1, h2⟩` from `mem_symCocycles.1 hc`. Rewrite using `[dUnit_mul'_map, h2, restrZeroLeft_of_cobTwo_eq_zero h1, dUnit, AugCot.d_algebraMap, map_zero, map_zero, zero_add]`.
-/
theorem dUnit_mul'_map_of_mem (f g : A →ₐc[R] B) {c : A ⊗[R] A} (hc : c ∈ symCocycles R A) :
    dUnit R (LinearMap.mul' R B (TensorProduct.map (f : A →ₗ[R] B) (g : A →ₗ[R] B) c)) = 0 := by
  obtain ⟨h1, h2⟩ := mem_symCocycles.1 hc
  rw [dUnit_mul'_map, h2, restrZeroLeft_of_cobTwo_eq_zero h1, dUnit, AugCot.d_algebraMap,
    map_zero, map_zero, zero_add]

end GlobalTheory.PDiv

namespace GlobalTheory.PDivGroup

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] {G H : PDivGroup p R}

/- English proof (translation)
Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Take `⟨⟨c, w⟩, rfl⟩` from `Submodule.mkQ_surjective _ x`. Set `B : G.funs` to `⟨fun n => LinearMap.mul' R _ (TensorProduct.map (f.app n : H.A n →ₗ[R] G.A n) (g.app n : H.A n →ₗ[R] G.A n) (c.1 n)), fun n => by dsimp only`. Rewrite using `[← (c.2 n).2]`. Generalize the expression as in `c.1 (n + 1) = t`.

Proceed by induction on `t with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul x y => simp [res_app]⟩`. Establish `hB : G.dFun B = 0` using `Subtype.ext (funext fun n => dUnit_mul'_map_of_mem (f.app n) (g.app n) (c.2 n).1)`.

Establish `hc : cocyclesMap (f + g) c = cocyclesMap f c + cocyclesMap g c + G.cob B` using `Subtype.ext (funext fun n => T.bialgebraPullbackTwo_convMul_symmetricCocycle (f.app n) (g.app n) (c.1 n) (c.2 n).1)`. Express the relevant statement in the definitionally equal form `G.rigMk (cocyclesMap (f + g) c, omegaMap G H (f + g) w) = G.rigMk (cocyclesMap f c, omegaMap G H f w) + G.rigMk (cocyclesMap g c, omegaMap G H g w)`. Rewrite using `[← map_add, Prod.mk_add_mk, map_add (omegaMap G H) f g, LinearMap.add_apply, hc]`. Use `(Submodule.Quotient.eq _).2 ⟨B, Prod.ext ?_ ?_⟩` and prove the remaining obligations. Use `show G.cob B = _`.

Simplify using the standard rewrite rules. Use `show G.dFun B = _`. Rewrite using `[hB]`. Simplify using the standard rewrite rules.
-/
theorem rigExtMap_add (f g : G ⟶ H) : rigExtMap (f + g) = rigExtMap f + rigExtMap g := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨⟨c, w⟩, rfl⟩ := Submodule.mkQ_surjective _ x
  let B : G.funs := ⟨fun n => LinearMap.mul' R _ (TensorProduct.map (f.app n : H.A n →ₗ[R] G.A n)
      (g.app n : H.A n →ₗ[R] G.A n) (c.1 n)), fun n => by
    dsimp only
    rw [← (c.2 n).2]
    generalize c.1 (n + 1) = t
    induction t with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => simp [res_app]⟩
  have hB : G.dFun B = 0 :=
    Subtype.ext (funext fun n => dUnit_mul'_map_of_mem (f.app n) (g.app n) (c.2 n).1)
  have hc : cocyclesMap (f + g) c = cocyclesMap f c + cocyclesMap g c + G.cob B :=
    Subtype.ext (funext fun n => T.bialgebraPullbackTwo_convMul_symmetricCocycle (f.app n) (g.app n) (c.1 n) (c.2 n).1)
  change G.rigMk (cocyclesMap (f + g) c, omegaMap G H (f + g) w) =
    G.rigMk (cocyclesMap f c, omegaMap G H f w) + G.rigMk (cocyclesMap g c, omegaMap G H g w)
  rw [← map_add, Prod.mk_add_mk, map_add (omegaMap G H) f g, LinearMap.add_apply, hc]
  refine (Submodule.Quotient.eq _).2 ⟨B, Prod.ext ?_ ?_⟩
  · show G.cob B = _
    simp
  · show G.dFun B = _
    rw [hB]
    simp

variable (G) in

/- English proof (translation)
Set `φ : (G ⟶ G) →+ (G.RigExt →ₗ[R] G.RigExt)` to `AddMonoidHom.mk' (fun f => rigExtMap f) (fun f g => rigExtMap_add f g)`. Establish `h : φ (p • 𝟙 G) = p • φ (𝟙 G)` using `map_nsmul φ p (𝟙 G)`. Rewrite `h` using `[← Nat.cast_smul_eq_nsmul ℤ_[p], ← Nat.cast_smul_eq_nsmul R, hp, zero_smul]`. Conclude with `h`.
-/
theorem rigExtMap_natCast_smul_id (hp : (p : R) = 0) : rigExtMap ((p : ℤ_[p]) • 𝟙 G) = 0 := by
  let φ : (G ⟶ G) →+ (G.RigExt →ₗ[R] G.RigExt) :=
    AddMonoidHom.mk' (fun f => rigExtMap f) (fun f g => rigExtMap_add f g)
  have h : φ (p • 𝟙 G) = p • φ (𝟙 G) := map_nsmul φ p (𝟙 G)
  rw [← Nat.cast_smul_eq_nsmul ℤ_[p], ← Nat.cast_smul_eq_nsmul R, hp, zero_smul] at h
  exact h

/- English proof (translation)
Introduce `_ _ _ _ h G _` and use `⟨rigExtMap_add, G.rigExtMap_natCast_smul_id h⟩`.
-/
theorem rigExtMap_add_and_natCast_smul_id : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G H : PDivGroup p R),
    (∀ f g : G ⟶ H, rigExtMap (f + g) = rigExtMap f + rigExtMap g) ∧
      rigExtMap ((p : ℤ_[p]) • 𝟙 G) = 0 :=
  fun _ _ _ _ h G _ => ⟨rigExtMap_add, G.rigExtMap_natCast_smul_id h⟩

end GlobalTheory.PDivGroup

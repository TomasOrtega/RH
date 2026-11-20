import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveBaseChangeDescendsFilteredColimitStatement
open CategoryTheory Limits TensorProduct

namespace GlobalTheory.TorsorColim

/- English proof (translation)
Use `haveI : NeZero q := ⟨hq.ne'⟩`. Set `e1 : (T ⊗[R] A) ⊗[T] (T ⊗[R] A) ≃ₐ[T] T ⊗[R] (A ⊗[R] A)` to `(Algebra.TensorProduct.cancelBaseChange R T T (T ⊗[R] A) A).trans (Algebra.TensorProduct.assoc R R T T A A)`. Set `e2 : T ⊗[R] (Multiplicative (ZMod q) → A) ≃ₐ[T] (Multiplicative (ZMod q) → T ⊗[R] A)` to `Algebra.TensorProduct.piRight R T T (fun _ : Multiplicative (ZMod q) => A)`. Establish `key : ∀ x, prodMapOf T (T ⊗[R] A) q (bcAct T act) x = e2 (Algebra.TensorProduct.map (AlgHom.id T T) (prodMapOf R A q act) (e1 x))`. Introduce `x`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add, hx, hy, map_add, map_add, map_add]`. Consider the case `tmul u v`. Proceed by induction on `u using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add u u' hu hu' => rw [TensorProduct.add_tmul, map_add, hu, hu', map_add, map_add, map_add]`. Consider the case `tmul t a`. Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add v v' hv hv' => rw [TensorProduct.tmul_add, map_add, hv, hv', map_add, map_add, map_add]`. Consider the case `tmul t' a'`. Use function extensionality and compare the values at `g`. Simplify using `[e1, e2, Algebra.TensorProduct.cancelBaseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.piRight_tmul, mul_comm]`. Establish `hf : ⇑(prodMapOf T (T ⊗[R] A) q (bcAct T act)) = e2 ∘ (Algebra.TensorProduct.map (AlgHom.id T T) (prodMapOf R A q act)) ∘ e1` using `funext key`.

Rewrite using `[hf]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `(e2.symm.bijective.comp h).comp e1.symm.bijective` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `y`. Simplify using the standard rewrite rules. Introduce `h`. Conclude with `e2.bijective.comp (h.comp e1.bijective)`.
-/
theorem bc_prodMapOf_bijective_iff (R T A : Type) [CommRing R] [CommRing T] [CommRing A] [Algebra R T]
    [Algebra R A] (q : ℕ) (hq : 0 < q) (act : Multiplicative (ZMod q) →* (A ≃ₐ[R] A)) :
    Function.Bijective (prodMapOf T (T ⊗[R] A) q (bcAct T act)) ↔
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id T T) (prodMapOf R A q act)) := by
  haveI : NeZero q := ⟨hq.ne'⟩
  classical
  let e1 : (T ⊗[R] A) ⊗[T] (T ⊗[R] A) ≃ₐ[T] T ⊗[R] (A ⊗[R] A) :=
    (Algebra.TensorProduct.cancelBaseChange R T T (T ⊗[R] A) A).trans
      (Algebra.TensorProduct.assoc R R T T A A)
  let e2 : T ⊗[R] (Multiplicative (ZMod q) → A) ≃ₐ[T] (Multiplicative (ZMod q) → T ⊗[R] A) :=
    Algebra.TensorProduct.piRight R T T (fun _ : Multiplicative (ZMod q) => A)
  have key : ∀ x, prodMapOf T (T ⊗[R] A) q (bcAct T act) x =
      e2 (Algebra.TensorProduct.map (AlgHom.id T T) (prodMapOf R A q act) (e1 x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add, map_add]
    | tmul u v =>
      induction u using TensorProduct.induction_on with
      | zero => simp
      | add u u' hu hu' => rw [TensorProduct.add_tmul, map_add, hu, hu', map_add, map_add, map_add]
      | tmul t a =>
        induction v using TensorProduct.induction_on with
        | zero => simp
        | add v v' hv hv' => rw [TensorProduct.tmul_add, map_add, hv, hv', map_add, map_add, map_add]
        | tmul t' a' =>
          funext g
          simp [e1, e2, Algebra.TensorProduct.cancelBaseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul,
            Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.piRight_tmul, mul_comm]
  have hf : ⇑(prodMapOf T (T ⊗[R] A) q (bcAct T act)) =
      e2 ∘ (Algebra.TensorProduct.map (AlgHom.id T T) (prodMapOf R A q act)) ∘ e1 := funext key
  rw [hf]
  constructor
  · intro h
    have := (e2.symm.bijective.comp h).comp e1.symm.bijective
    convert this using 1
    funext y; simp
  · intro h
    exact e2.bijective.comp (h.comp e1.bijective)

/- English proof (translation)
Use `haveI : NeZero q := ⟨hq.ne'⟩`. Establish `hc : ((prodMapOf R A q act).toRingHom.comp (Algebra.TensorProduct.includeLeft (S` using `R) (A := A) (B := A)).toRingHom) = algebraMap A (Multiplicative (ZMod q) → A) := by`. Use extensionality with `x g`. Simplify using `[prodMapOf]`. Establish `: (algebraMap A (Multiplicative (ZMod q) → A)).Finite`.

Conclude with `RingHom.finite_algebraMap.2 inferInstance`. Conclude with `RingHom.Finite.of_comp_finite (hc ▸ this)`.
-/
theorem prodMapOf_finite (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (q : ℕ) (hq : 0 < q)
    (act : Multiplicative (ZMod q) →* (A ≃ₐ[R] A)) : (prodMapOf R A q act).toRingHom.Finite := by
  haveI : NeZero q := ⟨hq.ne'⟩
  have hc : ((prodMapOf R A q act).toRingHom.comp
      (Algebra.TensorProduct.includeLeft (S := R) (A := A) (B := A)).toRingHom) =
      algebraMap A (Multiplicative (ZMod q) → A) := by
    ext x g
    simp [prodMapOf]
  have : (algebraMap A (Multiplicative (ZMod q) → A)).Finite := by
    exact RingHom.finite_algebraMap.2 inferInstance
  exact RingHom.Finite.of_comp_finite (hc ▸ this)

/- English proof (translation)
Introduce `J _ _ F c hc q hq j A _ _ _ actA hT`. Use `haveI : NeZero q := ⟨hq.ne'⟩`. Use `haveI : Algebra.FinitePresentation (F.obj j) (A ⊗[F.obj j] A) := Algebra.FinitePresentation.trans (F.obj j) A (A ⊗[F.obj j] A)`. Establish `hb : letI : Algebra (F.obj j) c.pt` using `(c.ι.app j).hom.toAlgebra; Function.Bijective (Algebra.TensorProduct.map (AlgHom.id c.pt c.pt) (prodMapOf (F.obj j) A q actA)) := by`. Use `letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra`.

Conclude with `(bc_prodMapOf_bijective_iff (F.obj j) c.pt A q hq actA).1 hT.2.2.2`. Take `⟨k₀, f₀, hk⟩` from `GlobalTheory.T.bijective_baseChange_descends_filteredColimit J F c hc j _ _ (prodMapOf (F.obj j) A q actA) (prodMapOf_finite _ _ q hq actA) hb`. Use `⟨k₀, f₀, fun k f => ?_⟩` and prove the remaining obligations. Use `letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra`. Conclude with `(bc_prodMapOf_bijective_iff (F.obj j) (F.obj k) A q hq actA).2 (hk k f)`.
-/
theorem eventually_prodMapOf_bijective : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A] (actA : Multiplicative (ZMod q) →* (A ≃ₐ[F.obj j] A)),
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      GlobalTheory.LocAcyc.IsZModTorsor c.pt (c.pt ⊗[F.obj j] A) q (GlobalTheory.TorsorColim.bcAct c.pt actA)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Function.Bijective (GlobalTheory.TorsorColim.prodMapOf (F.obj k) (F.obj k ⊗[F.obj j] A) q
        (GlobalTheory.TorsorColim.bcAct (F.obj k) actA)) := by
  intro J _ _ F c hc q hq j A _ _ _ actA hT
  haveI : NeZero q := ⟨hq.ne'⟩
  haveI : Algebra.FinitePresentation (F.obj j) (A ⊗[F.obj j] A) :=
    Algebra.FinitePresentation.trans (F.obj j) A (A ⊗[F.obj j] A)
  have hb : letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id c.pt c.pt) (prodMapOf (F.obj j) A q actA)) := by
    letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
    exact (bc_prodMapOf_bijective_iff (F.obj j) c.pt A q hq actA).1 hT.2.2.2
  obtain ⟨k₀, f₀, hk⟩ := GlobalTheory.T.bijective_baseChange_descends_filteredColimit J F c hc j _ _ (prodMapOf (F.obj j) A q actA)
    (prodMapOf_finite _ _ q hq actA) hb
  refine ⟨k₀, f₀, fun k f => ?_⟩
  letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra
  exact (bc_prodMapOf_bijective_iff (F.obj j) (F.obj k) A q hq actA).2 (hk k f)

end GlobalTheory.TorsorColim

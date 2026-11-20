import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.DerivSub
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeJacquetHolds
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZDerivJac

namespace GlobalTheory.RgGu.Nup2

/- English proof (translation)
Establish `hx : ∃ x : ∀ a, X a, φ (PiTensorProduct.tprod ℂ x) ≠ 0`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hne (PiTensorProduct.ext (MultilinearMap.ext fun x => by simpa using h x))`. Take `⟨x, hx⟩` from `hx`.

Set `ℓ : X i →ₗ[ℂ] D` to `φ ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap x i`. Establish `hℓ : ∀ w, ℓ w = φ (PiTensorProduct.tprod ℂ (Function.update x i w))` using `fun w => rfl`. Set `f : (ρ i).IntertwiningMap R` to `⟨ℓ, fun g => LinearMap.ext fun w => by show ℓ (ρ i g w) = R g (ℓ w)`. Rewrite using `[hℓ, hℓ, ← hφ, piTensor_tprod]`. Use `congr 2`.

Use function extensionality and compare the values at `a`. Distinguish the cases in `h : a = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.mulSingle_eq_of_ne h, Function.update_of_ne h]⟩`.

Use `⟨f, ?_⟩` and prove the remaining obligations. Use `haveI := hi`. Break down `Representation.IsIrreducible.injective_or_eq_zero f with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction.

Apply `hx` to reduce the goal to its premises. Establish `e` using `congrArg (fun F : (ρ i).IntertwiningMap R => F (x i)) h`. Establish `e2 : f (x i) = φ (PiTensorProduct.tprod ℂ x)` using `by show ℓ (x i) = _`. Rewrite using `[hℓ, Function.update_eq_self]`. Rewrite using `[← e2]`.

Conclude with `e`.
-/
theorem exists_injective_of_tensor {α : Type} [DecidableEq α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (i : α)
    (hi : (ρ i).IsIrreducible) {D : Type} [AddCommGroup D] [Module ℂ D] (R : Representation ℂ (Γ i) D)
    (φ : PiTensorProduct ℂ X →ₗ[ℂ] D) (hφ : ∀ g x, φ (piTensor ρ (Pi.mulSingle i g) x) = R g (φ x)) (hne : φ ≠ 0) :
    ∃ f : (ρ i).IntertwiningMap R, Function.Injective f := by
  have hx : ∃ x : ∀ a, X a, φ (PiTensorProduct.tprod ℂ x) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (PiTensorProduct.ext (MultilinearMap.ext fun x => by simpa using h x))
  obtain ⟨x, hx⟩ := hx
  let ℓ : X i →ₗ[ℂ] D := φ ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap x i
  have hℓ : ∀ w, ℓ w = φ (PiTensorProduct.tprod ℂ (Function.update x i w)) := fun w => rfl
  let f : (ρ i).IntertwiningMap R := ⟨ℓ, fun g => LinearMap.ext fun w => by
    show ℓ (ρ i g w) = R g (ℓ w)
    rw [hℓ, hℓ, ← hφ, piTensor_tprod]
    congr 2
    funext a
    by_cases h : a = i
    · subst h
      simp
    · simp [Pi.mulSingle_eq_of_ne h, Function.update_of_ne h]⟩
  refine ⟨f, ?_⟩
  haveI := hi
  rcases Representation.IsIrreducible.injective_or_eq_zero f with h | h
  · exact h
  · exfalso
    apply hx
    have e := congrArg (fun F : (ρ i).IntertwiningMap R => F (x i)) h
    have e2 : f (x i) = φ (PiTensorProduct.tprod ℂ x) := by
      show ℓ (x i) = _
      rw [hℓ, Function.update_eq_self]
    rw [← e2]
    exact e

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨hGT, hLT⟩` from `(hasFiniteLength_iff_wellFounded T).1 hT`. Set `P : Set (Subrepresentation T)` to `{B | ∃ x ∈ B, L x ≠ 0}`. Establish `hP : P.Nonempty`. Assume the negation of the conclusion as `h`. Apply `hne` to reduce the goal to its premises.

Use extensionality with `x`. Assume the negation of the conclusion as `hx`. Conclude with `h ⟨⊤, x, trivial, hx⟩`. Take `⟨B, ⟨x0, hx0B, hx0⟩, hBmin⟩` from `wellFounded_lt.has_min P hP`. Establish `hbot : ⊥ < B`.

Use `bot_lt_iff_ne_bot.2 fun h => ?_` and prove the remaining obligations. Substitute `h` using the available equality. Establish `: x0 = 0` using `(Submodule.mem_bot ℂ).1 hx0B`. Conclude with `hx0 (by rw [this, map_zero])`. Take `⟨C, hCB, hCmax⟩` from `wellFounded_gt.has_min {C : Subrepresentation T | C < B} ⟨⊥, hbot⟩`.

Establish `hcov : C ⋖ B` using `⟨hCB, fun E hCE hEB => hCmax E hEB hCE⟩`. Establish `hCker : ∀ x ∈ C, L x = 0`. Introduce `x hx`. Assume the negation of the conclusion as `h`. Conclude with `hBmin C ⟨x, hx, h⟩ hCB`.

Set `K` to `C.toSubmodule.comap B.toSubmodule.subtype`. Set `φ : (B.toSubmodule ⧸ K) →ₗ[ℂ] D` to `K.liftQ (L ∘ₗ B.toSubmodule.subtype) (fun y hy => hCker y.1 hy)`. Establish `hφ : ∀ y : B.toSubmodule, φ (Submodule.Quotient.mk y) = L y.1` using `fun y => rfl`. Establish `hZi : (subQuot B C).IsIrreducible` using `isIrreducible_subQuot hcov`. Establish `hZsq : IsSubquotient (subQuot B C) T` using `⟨B, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.mkQ_surjective _⟩`.

Establish `hZs : IsSmooth (subQuot B C)` using `hZsq.isSmooth hs`. Take `⟨σ, ⟨E⟩⟩` from `GlobalTheory.T.levi_irreducible_tensor_decomposition hA (dd n t) (⟨_, subQuot B C, hZs, hZi⟩ : IrrRep _)`. Set `φ'` to `φ ∘ₗ E.symm.toIntertwiningMap.toLinearMap`. Establish `hq : ∀ (g : GL (Fin (dd n t 0)) k) z, φ (subQuot B C (Pi.mulSingle 0 g) z) = R g (φ z)`. Introduce `g z`.

Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`. Conclude with `hL g y.1`. Establish `hφ'rel : ∀ (g : GL (Fin (dd n t 0)) k) x, φ' ((piTensor fun a => (σ a).rep.ρ) (Pi.mulSingle 0 g) x) = R g (φ' x)`. Introduce `g x`. Establish `hE` using `LinearMap.congr_fun (E.symm.toIntertwiningMap.isIntertwining' (Pi.mulSingle 0 g)) x`.

Conclude with `(congrArg φ hE).trans (hq g _)`. Establish `hφ'ne : φ' ≠ 0`. Introduce `h0`. Apply `hx0` to reduce the goal to its premises. Establish `e` using `LinearMap.congr_fun h0 (E.toIntertwiningMap (Submodule.Quotient.mk ⟨x0, hx0B⟩))`.

Establish `e2 : E.symm.toIntertwiningMap (E.toIntertwiningMap (Submodule.Quotient.mk ⟨x0, hx0B⟩)) = Submodule.Quotient.mk ⟨x0, hx0B⟩` using `E.toLinearEquiv.symm_apply_apply _`. Establish `e3 : φ' (E.toIntertwiningMap (Submodule.Quotient.mk ⟨x0, hx0B⟩)) = L x0` using `by show φ (E.symm.toIntertwiningMap _) = _`. Rewrite using `[e2]`. Both sides reduce to the same expression. Rewrite using `[← e3]`.

Conclude with `e`. Take `⟨f, hf⟩` from `exists_injective_of_tensor (fun a => (σ a).rep.ρ) (0 : Fin 2) (σ 0).rep.irr (R := R) φ' hφ'rel hφ'ne`. Use `⟨(σ 0).rep, f, hf⟩` and prove the remaining obligations.
-/
theorem exists_irr_sub_of_quot (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {n t : ℕ} {X D : Type} [AddCommGroup X]
    [Module ℂ X] [AddCommGroup D] [Module ℂ D] (T : Representation ℂ (Levi k fun a => Fin (dd n t a)) X)
    (hs : IsSmooth T) (hT : HasFiniteLength T) (R : Representation ℂ (GL (Fin n) k) D) (L : X →ₗ[ℂ] D)
    (hL : ∀ g x, L ((T.comp (iota n t) : Representation ℂ (GL (Fin n) k) X) g x) = R g (L x)) (hne : L ≠ 0) :
    ∃ (S : IrrRep (GL (Fin n) k)) (f : S.ρ.IntertwiningMap R), Function.Injective f := by
  obtain ⟨hGT, hLT⟩ := (hasFiniteLength_iff_wellFounded T).1 hT
  let P : Set (Subrepresentation T) := {B | ∃ x ∈ B, L x ≠ 0}
  have hP : P.Nonempty := by
    by_contra h
    apply hne
    ext x
    by_contra hx
    exact h ⟨⊤, x, trivial, hx⟩
  obtain ⟨B, ⟨x0, hx0B, hx0⟩, hBmin⟩ := wellFounded_lt.has_min P hP
  have hbot : ⊥ < B := by
    refine bot_lt_iff_ne_bot.2 fun h => ?_
    subst h
    have : x0 = 0 := (Submodule.mem_bot ℂ).1 hx0B
    exact hx0 (by rw [this, map_zero])
  obtain ⟨C, hCB, hCmax⟩ := wellFounded_gt.has_min {C : Subrepresentation T | C < B} ⟨⊥, hbot⟩
  have hcov : C ⋖ B := ⟨hCB, fun E hCE hEB => hCmax E hEB hCE⟩
  have hCker : ∀ x ∈ C, L x = 0 := by
    intro x hx
    by_contra h
    exact hBmin C ⟨x, hx, h⟩ hCB
  let K := C.toSubmodule.comap B.toSubmodule.subtype
  let φ : (B.toSubmodule ⧸ K) →ₗ[ℂ] D := K.liftQ (L ∘ₗ B.toSubmodule.subtype) (fun y hy => hCker y.1 hy)
  have hφ : ∀ y : B.toSubmodule, φ (Submodule.Quotient.mk y) = L y.1 := fun y => rfl
  have hZi : (subQuot B C).IsIrreducible := isIrreducible_subQuot hcov
  have hZsq : IsSubquotient (subQuot B C) T :=
    ⟨B, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.mkQ_surjective _⟩
  have hZs : IsSmooth (subQuot B C) := hZsq.isSmooth hs
  obtain ⟨σ, ⟨E⟩⟩ := GlobalTheory.T.levi_irreducible_tensor_decomposition hA (dd n t) (⟨_, subQuot B C, hZs, hZi⟩ : IrrRep _)
  let φ' := φ ∘ₗ E.symm.toIntertwiningMap.toLinearMap
  have hq : ∀ (g : GL (Fin (dd n t 0)) k) z, φ (subQuot B C (Pi.mulSingle 0 g) z) = R g (φ z) := by
    intro g z
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact hL g y.1
  have hφ'rel : ∀ (g : GL (Fin (dd n t 0)) k) x,
      φ' ((piTensor fun a => (σ a).rep.ρ) (Pi.mulSingle 0 g) x) = R g (φ' x) := by
    intro g x
    have hE := LinearMap.congr_fun (E.symm.toIntertwiningMap.isIntertwining' (Pi.mulSingle 0 g)) x
    exact (congrArg φ hE).trans (hq g _)
  have hφ'ne : φ' ≠ 0 := by
    intro h0
    apply hx0
    have e := LinearMap.congr_fun h0 (E.toIntertwiningMap (Submodule.Quotient.mk ⟨x0, hx0B⟩))
    have e2 : E.symm.toIntertwiningMap (E.toIntertwiningMap (Submodule.Quotient.mk ⟨x0, hx0B⟩)) =
        Submodule.Quotient.mk ⟨x0, hx0B⟩ := E.toLinearEquiv.symm_apply_apply _
    have e3 : φ' (E.toIntertwiningMap (Submodule.Quotient.mk ⟨x0, hx0B⟩)) = L x0 := by
      show φ (E.symm.toIntertwiningMap _) = _
      rw [e2]
      rfl
    rw [← e3]
    exact e
  obtain ⟨f, hf⟩ := exists_injective_of_tensor (fun a => (σ a).rep.ρ) (0 : Fin 2) (σ 0).rep.irr
    (R := R) φ' hφ'rel hφ'ne
  refine ⟨(σ 0).rep, f, hf⟩

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨L, hL, hLe⟩` from `exists_jac_deriv ψ n j π`. Use `⟨L, hL, fun g x => ?_⟩` and prove the remaining obligations. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite using `[twist_apply]`. Establish `h1` using `congrArg (fun c : ℂˣ => (c : ℂ) • GlobalTheory.BZMir.deriv k ψ j π g (L (Submodule.Quotient.mk v))) (delta_mulSingle n j g)`.

Use `Eq.trans ?_ h1` and prove the remaining obligations. Establish `h2` using `hLe g v`. Establish `h3 : (jac (stdBlocks (dd n (j + 1)) (dd_sum n j)) π).comp (iota n (j + 1)) g (Submodule.Quotient.mk v) = (((deltaHalf k (fun a => Fin (dd n (j + 1) a)) (Pi.mulSingle (M` using `fun a => GL (Fin (dd n (j + 1) a)) k) (0 : Fin 2) g))⁻¹ : ℂˣ) : ℂ) • Submodule.Quotient.mk (π (leviEmb k (stdBlocks (dd n (j + 1)) (dd_sum n j)) (Pi.mulSingle (M := fun a => GL (Fin (dd n (j + 1) a)) k) (0 : Fin 2) g)) v) := jac_mk _ π _ v`. Rewrite using `[h3, map_smul, h2]`.
-/
theorem jac_deriv_rel (ψ : AddChar k Circle) (n j : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V) :
    ∃ L : Jacquet π (unipRad k (stdBlocks (dd n (j + 1)) (dd_sum n j))) →ₗ[ℂ]
        TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k n) 1,
      Function.Surjective L ∧ ∀ g x,
        L (((jac (stdBlocks (dd n (j + 1)) (dd_sum n j)) π).comp (iota n (j + 1)) :
          Representation ℂ (GL (Fin n) k) _) g x) =
        twist (GlobalTheory.BZMir.deriv k ψ j π) (detChar (Fin n) (absPow k (-(((j : ℂ) + 1) / 2)))) g (L x) := by
  obtain ⟨L, hL, hLe⟩ := exists_jac_deriv ψ n j π
  refine ⟨L, hL, fun g x => ?_⟩
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [twist_apply]
  have h1 := congrArg (fun c : ℂˣ => (c : ℂ) • GlobalTheory.BZMir.deriv k ψ j π g (L (Submodule.Quotient.mk v)))
    (delta_mulSingle n j g)
  refine Eq.trans ?_ h1
  have h2 := hLe g v
  have h3 : (jac (stdBlocks (dd n (j + 1)) (dd_sum n j)) π).comp (iota n (j + 1)) g (Submodule.Quotient.mk v) =
      (((deltaHalf k (fun a => Fin (dd n (j + 1) a))
        (Pi.mulSingle (M := fun a => GL (Fin (dd n (j + 1) a)) k) (0 : Fin 2) g))⁻¹ : ℂˣ) : ℂ) •
      Submodule.Quotient.mk (π (leviEmb k (stdBlocks (dd n (j + 1)) (dd_sum n j))
        (Pi.mulSingle (M := fun a => GL (Fin (dd n (j + 1) a)) k) (0 : Fin 2) g)) v) :=
    jac_mk _ π _ v
  rw [h3, map_smul, h2]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `ψ n j V _ _ π hs hf hnt`. Establish `hχ : IsSmoothChar (detChar (Fin (n + 1)) (absPow k (-(((j : ℂ) + 1) / 2))))` using `(isSmoothChar_absPow _).detChar`. Establish `hχi : IsSmoothChar (detChar (Fin (n + 1)) (absPow k (-(((j : ℂ) + 1) / 2))))⁻¹`. Unfold `IsSmoothChar at hχ ⊢`. Use `hχ using 2` and compare the differences between its conclusion and the goal.

Use extensionality with `g`. Simplify using `[MonoidHom.mem_ker]`. Take `⟨L, hL, hLe⟩` from `jac_deriv_rel ψ (n + 1) j π`. Establish `hne : L ≠ 0`. Introduce `h0`.

Take `⟨y, hy⟩` from `exists_ne (0 : TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k (n + 1)) 1)`. Take `⟨x, rfl⟩` from `hL y`. Conclude with `hy (by rw [h0, LinearMap.zero_apply])`. Take `⟨S0, f, hf'⟩` from `exists_irr_sub_of_quot hA _ (isSmooth_jac _ hs) (GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k _ _ _ _ V π hs hf) _ L hLe hne`. Use `⟨⟨S0.V, twist S0.ρ (detChar (Fin (n + 1)) (absPow k (-(((j : ℂ) + 1) / 2))))⁻¹, isSmooth_twist S0.smooth hχi, isIrreducible_twist S0.irr _⟩, ⟨f.toLinearMap, fun g => ?_⟩, hf'⟩` and prove the remaining obligations.

Use extensionality with `w`. Establish `e` using `LinearMap.congr_fun (f.isIntertwining' g) w`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, twist_apply] at e ⊢`. Rewrite using `[map_smul, e, smul_smul]`. Simplify using the standard rewrite rules.
-/
theorem derivSub (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) : GlobalTheory.BZSeg.DerivSub k := by
  intro ψ n j V _ _ π hs hf hnt
  have hχ : IsSmoothChar (detChar (Fin (n + 1)) (absPow k (-(((j : ℂ) + 1) / 2)))) :=
    (isSmoothChar_absPow _).detChar
  have hχi : IsSmoothChar (detChar (Fin (n + 1)) (absPow k (-(((j : ℂ) + 1) / 2))))⁻¹ := by
    unfold IsSmoothChar at hχ ⊢
    convert hχ using 2
    ext g
    simp [MonoidHom.mem_ker]
  obtain ⟨L, hL, hLe⟩ := jac_deriv_rel ψ (n + 1) j π
  have hne : L ≠ 0 := by
    intro h0
    obtain ⟨y, hy⟩ := exists_ne (0 : TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k (n + 1)) 1)
    obtain ⟨x, rfl⟩ := hL y
    exact hy (by rw [h0, LinearMap.zero_apply])
  obtain ⟨S0, f, hf'⟩ := exists_irr_sub_of_quot hA _ (isSmooth_jac _ hs)
    (GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k _ _ _ _ V π hs hf) _ L hLe hne
  refine ⟨⟨S0.V, twist S0.ρ (detChar (Fin (n + 1)) (absPow k (-(((j : ℂ) + 1) / 2))))⁻¹,
    isSmooth_twist S0.smooth hχi, isIrreducible_twist S0.irr _⟩, ⟨f.toLinearMap, fun g => ?_⟩, hf'⟩
  ext w
  have e := LinearMap.congr_fun (f.isIntertwining' g) w
  simp only [LinearMap.coe_comp, Function.comp_apply, twist_apply] at e ⊢
  rw [map_smul, e, smul_smul]
  simp

/- English proof (translation)
Introduce `_ _ _ _ _ hA` and use `derivSub hA`.
-/
theorem derivSub_main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.DerivSub k :=
  fun _ _ _ _ _ hA => derivSub hA

end GlobalTheory.RgGu.Nup2

end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.HasSupportOfIsSubquotientProdIrr
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

noncomputable section

namespace Ysupp.UnramifiedTwistSupport

open GlobalTheory

open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LocGL
open scoped TensorProduct

variable {g : ℕ} [Fact g.Prime]

/- English proof (translation)
Introduce `x hx`. Establish `a1` using `GlobalTheory.SplitWeil.padic_valuation_lt_iff g (x : ℚ_[g]) 1`. Establish `a2` using `GlobalTheory.SplitWeil.padic_valuation_lt_iff g 1 (x : ℚ_[g])`. Rewrite `a1`, `a2` using `[hx, map_one]`. Establish `h1 : ‖(x : ℚ_[g])‖ = 1`.

Simplify using `only [lt_self_iff_false, norm_one, false_iff, not_lt] at a1 a2`. Conclude with `le_antisymm a2 a1`. Use `h (PadicInt.mkUnits h1)` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal. Conclude with `Units.ext rfl`.
-/
theorem isUnram_of_supp {ν : ℚ_[g]ˣ →* ℂˣ} (h : Supp.IsUnram ν) : GlobalTheory.SplitWeil.IsUnram ν := by
  intro x hx
  have a1 := GlobalTheory.SplitWeil.padic_valuation_lt_iff g (x : ℚ_[g]) 1
  have a2 := GlobalTheory.SplitWeil.padic_valuation_lt_iff g 1 (x : ℚ_[g])
  rw [hx, map_one] at a1 a2
  have h1 : ‖(x : ℚ_[g])‖ = 1 := by
    simp only [lt_self_iff_false, norm_one, false_iff, not_lt] at a1 a2
    exact le_antisymm a2 a1
  have := h (PadicInt.mkUnits h1)
  convert this using 2
  exact Units.ext rfl

/- English proof (translation)
Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add u v hu hv => rw [map_add, hu, hv, map_add, smul_add]`. Consider the case `tmul u v`. Rewrite using `[extTensor_tmul, TensorProduct.map_tmul, twist_apply, twist_apply, TensorProduct.smul_tmul_smul, Units.val_mul]`.
-/
theorem extTensor_twist_apply {a b : ℕ} {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W) (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W')
    (χ₁ : GL (Fin a) ℚ_[g] →* ℂˣ) (χ₂ : GL (Fin b) ℚ_[g] →* ℂˣ) (x : GL (Fin a) ℚ_[g]) (y : GL (Fin b) ℚ_[g])
    (w : W ⊗[ℂ] W') :
    extTensor (twist σ χ₁) (twist ρ χ₂) (x, y) w = ((χ₁ x * χ₂ y : ℂˣ) : ℂ) • TensorProduct.map (σ x) (ρ y) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [map_add, hu, hv, map_add, smul_add]
  | tmul u v =>
    rw [extTensor_tmul, TensorProduct.map_tmul, twist_apply, twist_apply, TensorProduct.smul_tmul_smul,
      Units.val_mul]

/- English proof (translation)
Simplify using `only [MonoidHom.mul_apply, MonoidHom.inv_apply]`. Simplify using `[mul_assoc, mul_comm, mul_left_comm]`.
-/
theorem scal_eq (ν₁ ν₂ A B : ℚ_[g]ˣ →* ℂˣ) (u v : ℚ_[g]ˣ) :
    (A u * B v) * ((ν₁ * A⁻¹) u * (ν₂ * B⁻¹) v) = ν₁ u * ν₂ v := by
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
  simp [mul_assoc, mul_comm, mul_left_comm]

/- English proof (translation)
Use `set X := ((leviTwo ℚ_[g] (Fin a) (Fin b)).symm (leviProj ℚ_[g] _ q)).1 with hX`. Use `set Y := ((leviTwo ℚ_[g] (Fin a) (Fin b)).symm (leviProj ℚ_[g] _ q)).2 with hY`. Establish `hL : leviProj ℚ_[g] _ q = leviTwo ℚ_[g] _ _ (X, Y)` using `(MulEquiv.apply_symm_apply _ _).symm`. Establish `hpar` using `(mem_parab_two ℚ_[g]).1 q.2`. Establish `h0 : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j = 0`.

Introduce `i j hj hi`. Establish `e1 : stdSum (rfl : a + b = a + b) (.inr ⟨i - a, by omega⟩) = i` using `Fin.ext (by rw [stdSum_inr]; simp; omega)`. Establish `e2 : stdSum (rfl : a + b = a + b) (.inl ⟨j, hj⟩) = j` using `Fin.ext (by rw [stdSum_inl])`. Use `hpar ⟨i - a, by omega⟩ ⟨j, hj⟩` as an intermediate fact. Rewrite `this` using `[e1, e2]`. Then use the resulting hypothesis.

Establish `hx : ∀ i j : Fin a, (X : Matrix (Fin a) (Fin a) ℚ_[g]) i j = Formalism.MainNotions.ArithmeticCylinders.entN ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j`. Introduce `i j`. Establish `hi` using `i.2`. Establish `hj` using `j.2`. Rewrite using `[Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos ⟨by omega, by omega⟩]`.

Use `show ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (stdSum (rfl : a + b = a + b) (.inl i)) (stdSum (rfl : a + b = a + b) (.inl j)) = _`. Apply the tactic sequence `congr 1 <;> exact Fin.ext (stdSum_inl _ _)`. Establish `hy : ∀ i j : Fin b, (Y : Matrix (Fin b) (Fin b) ℚ_[g]) i j = Formalism.MainNotions.ArithmeticCylinders.entN ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (a + i) (a + j)`. Introduce `i j`. Establish `hi` using `i.2`.

Establish `hj` using `j.2`. Rewrite using `[Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos ⟨by omega, by omega⟩]`. Use `show ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (stdSum (rfl : a + b = a + b) (.inr i)) (stdSum (rfl : a + b = a + b) (.inr j)) = _`. Apply the tactic sequence `congr 1 <;> exact Fin.ext (stdSum_inr _ _)`. Rewrite using `[hΛ q X Y h0 hx hy w, hL, MulEquiv.symm_apply_apply, deltaHalf_two, extTensor_twist_apply, smul_smul, ← Units.val_mul, detChar_apply, detChar_apply]`.

Simplify using `only [Fintype.card_fin]`. Rewrite using `[scal_eq]`.
-/
theorem law {a b : ℕ} {V W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (π : Representation ℂ (GL (Fin (a + b)) ℚ_[g]) V)
    (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W) (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W')
    (ν₁ ν₂ : ℚ_[g]ˣ →* ℂˣ) (Λ : V →ₗ[ℂ] W ⊗[ℂ] W')
    (hΛ : ∀ (p : GL (Fin (a + b)) ℚ_[g]) (x : GL (Fin a) ℚ_[g]) (y : GL (Fin b) ℚ_[g]),
      (∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j = 0) →
      (∀ i j : Fin a, (x : Matrix (Fin a) (Fin a) ℚ_[g]) i j =
        Formalism.MainNotions.ArithmeticCylinders.entN (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j) →
      (∀ i j : Fin b, (y : Matrix (Fin b) (Fin b) ℚ_[g]) i j =
        Formalism.MainNotions.ArithmeticCylinders.entN (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (a + i) (a + j)) →
      ∀ v, Λ (π p v) = ((ν₁ (Matrix.GeneralLinearGroup.det x) * ν₂ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) •
        TensorProduct.map (σ x) (ρ y) (Λ v))
    (q : parab ℚ_[g] (two (stdSum (rfl : a + b = a + b)))) (w : V) :
    Λ (π q w) = (deltaHalf ℚ_[g] (Two (Fin a) (Fin b)) (leviProj ℚ_[g] _ q) : ℂ) •
      extTensor (twist σ (detChar (Fin a) (ν₁ * (absPow ℚ_[g] ((b : ℂ) / 2))⁻¹)))
        (twist ρ (detChar (Fin b) (ν₂ * (absPow ℚ_[g] (-(a : ℂ) / 2))⁻¹)))
        ((leviTwo ℚ_[g] (Fin a) (Fin b)).symm (leviProj ℚ_[g] _ q)) (Λ w) := by
  set X := ((leviTwo ℚ_[g] (Fin a) (Fin b)).symm (leviProj ℚ_[g] _ q)).1 with hX
  set Y := ((leviTwo ℚ_[g] (Fin a) (Fin b)).symm (leviProj ℚ_[g] _ q)).2 with hY
  have hL : leviProj ℚ_[g] _ q = leviTwo ℚ_[g] _ _ (X, Y) := (MulEquiv.apply_symm_apply _ _).symm
  have hpar := (mem_parab_two ℚ_[g]).1 q.2
  have h0 : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) →
      ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j = 0 := by
    intro i j hj hi
    have e1 : stdSum (rfl : a + b = a + b) (.inr ⟨i - a, by omega⟩) = i := Fin.ext (by rw [stdSum_inr]; simp; omega)
    have e2 : stdSum (rfl : a + b = a + b) (.inl ⟨j, hj⟩) = j := Fin.ext (by rw [stdSum_inl])
    have := hpar ⟨i - a, by omega⟩ ⟨j, hj⟩
    rwa [e1, e2] at this
  have hx : ∀ i j : Fin a, (X : Matrix (Fin a) (Fin a) ℚ_[g]) i j =
      Formalism.MainNotions.ArithmeticCylinders.entN ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j := by
    intro i j
    have hi := i.2
    have hj := j.2
    rw [Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos ⟨by omega, by omega⟩]
    show ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (stdSum (rfl : a + b = a + b) (.inl i)) (stdSum (rfl : a + b = a + b) (.inl j)) = _
    congr 1 <;> exact Fin.ext (stdSum_inl _ _)
  have hy : ∀ i j : Fin b, (Y : Matrix (Fin b) (Fin b) ℚ_[g]) i j =
      Formalism.MainNotions.ArithmeticCylinders.entN ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (a + i) (a + j) := by
    intro i j
    have hi := i.2
    have hj := j.2
    rw [Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos ⟨by omega, by omega⟩]
    show ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (stdSum (rfl : a + b = a + b) (.inr i)) (stdSum (rfl : a + b = a + b) (.inr j)) = _
    congr 1 <;> exact Fin.ext (stdSum_inr _ _)
  rw [hΛ q X Y h0 hx hy w, hL, MulEquiv.symm_apply_apply, deltaHalf_two, extTensor_twist_apply, smul_smul,
    ← Units.val_mul, detChar_apply, detChar_apply]
  simp only [Fintype.card_fin]
  rw [scal_eq]

/- English proof (translation)
Introduce `hP g _ n a b V W W' _ _ _ _ _ _ π σ ρ hs hπ hM ys yr hys hyr`. Take `⟨hn, ν₁, ν₂, Λ, h₁, h₂, hΛ0, hΛ⟩` from `hM`. Substitute `hn` using the available equality. Establish `hμ₁ : GlobalTheory.SplitWeil.IsUnram (ν₁ * (absPow ℚ_[g] ((b : ℂ) / 2))⁻¹)` using `isUnram_mul (isUnram_of_supp h₁) (isUnram_inv (isUnram_absPow _ _))`. Establish `hμ₂ : GlobalTheory.SplitWeil.IsUnram (ν₂ * (absPow ℚ_[g] (-(a : ℂ) / 2))⁻¹)` using `isUnram_mul (isUnram_of_supp h₂) (isUnram_inv (isUnram_absPow _ _))`.

Use `⟨_, _, hμ₁, hμ₂, ?_⟩` and prove the remaining obligations. Set `T : π.IntertwiningMap (prod₂ (twist σ (detChar (Fin a) (ν₁ * (absPow ℚ_[g] ((b : ℂ) / 2))⁻¹))) (twist ρ (detChar (Fin b) (ν₂ * (absPow ℚ_[g] (-(a : ℂ) / 2))⁻¹))))` to `{ toFun := fun v => ⟨⟨fun x => Λ (π x v), fun q x => by show Λ (π (q * x) v) = _`. Rewrite using `[map_mul, Module.End.mul_apply]`. Conclude with `law π σ ρ ν₁ ν₂ Λ hΛ q (π x v)⟩,`. Use `mem_smoothPart_of_nhds (Filter.mem_of_superset ((hs v).mem_nhds (by simp)) fun h hh => by`.

Establish `hh' : π h v = v` using `hh`. Use `Subtype.ext (funext fun x => ?_)` and prove the remaining obligations. Use `show Λ (π (x * h) v) = Λ (π x v)`. Rewrite using `[map_mul, Module.End.mul_apply, hh'])⟩`. Use the proof step `map_add' := fun v w => Subtype.ext (Subtype.ext (funext fun x => by show Λ (π x (v + w)) = Λ (π x v) + Λ (π x w)`.

Rewrite using `[map_add, map_add]))`. Use the proof step `map_smul' := fun c v => Subtype.ext (Subtype.ext (funext fun x => by show Λ (π x (c • v)) = c • Λ (π x v)`. Rewrite using `[map_smul, map_smul]))`. Use the proof step `isIntertwining' := fun h => LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun x => by show Λ (π x (π h v)) = Λ (π (x * h) v)`. Rewrite using `[map_mul, Module.End.mul_apply])) }`.

Establish `hT : Function.Injective T` using `by haveI := hπ`. Use `(Representation.IsIrreducible.injective_or_eq_zero T).resolve_right fun h0 => hΛ0 (LinearMap.ext fun v => ?_)` and prove the remaining obligations. Establish `h1 : (T v).1.1 1 = 0` using `by rw [h0]; rfl`. Express the relevant statement in the definitionally equal form `Λ (π 1 v) = 0 at h1`. Simplify using `using h1`.

Establish `hσ'` using `hys.tw _ (isSmoothChar_of_isUnram hμ₁)`. Establish `hρ'` using `hyr.tw _ (isSmoothChar_of_isUnram hμ₂)`. Take `⟨φ⟩` from `nonempty_prod₂_equiv_prodIrr _ hσ'.isSmooth hσ'.isIrreducible _ hρ'.isSmooth hρ'.isIrreducible (Fin.sum_univ_two _)`. Establish `hsub` using `(IsSubquotient.of_injective T hT).trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)`. Establish `key` using `Ysupp.hasSupport_of_isSubquotient_prodIrr hP (t := ![_, _]) (Fin.forall_fin_two.2 ⟨hσ'.of_equiv (IrrGL.equivOf _ _ _), hρ'.of_equiv (IrrGL.equivOf _ _ _)⟩) hπ hsub`.

Rewrite `key` using `[Fin.sum_univ_two]`. Conclude with `key`.
-/
theorem supp_of_mapsToProd : Ysupp.ProdSupport → ∀ (g : ℕ) [Fact g.Prime] (n a b : ℕ) (V W W' : Type)
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W)
    (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W'),
    GlobalTheory.PRep.IsSmooth π → π.IsIrreducible → Supp.MapsToProd π σ ρ →
    ∀ (ys yr : Multiset (GlobalTheory.LocGL.IrrGL ℚ_[g])), GlobalTheory.LocGL.HasSupport σ ys → GlobalTheory.LocGL.HasSupport ρ yr →
    ∃ (μ₁ μ₂ : ℚ_[g]ˣ →* ℂˣ) (h₁ : GlobalTheory.SplitWeil.IsUnram μ₁) (h₂ : GlobalTheory.SplitWeil.IsUnram μ₂),
      GlobalTheory.LocGL.HasSupport π (ys.map (fun x => x.tw μ₁ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h₁)) +
        yr.map (fun x => x.tw μ₂ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h₂))) := by
  intro hP g _ n a b V W W' _ _ _ _ _ _ π σ ρ hs hπ hM ys yr hys hyr
  obtain ⟨hn, ν₁, ν₂, Λ, h₁, h₂, hΛ0, hΛ⟩ := hM
  subst hn
  have hμ₁ : GlobalTheory.SplitWeil.IsUnram (ν₁ * (absPow ℚ_[g] ((b : ℂ) / 2))⁻¹) :=
    isUnram_mul (isUnram_of_supp h₁) (isUnram_inv (isUnram_absPow _ _))
  have hμ₂ : GlobalTheory.SplitWeil.IsUnram (ν₂ * (absPow ℚ_[g] (-(a : ℂ) / 2))⁻¹) :=
    isUnram_mul (isUnram_of_supp h₂) (isUnram_inv (isUnram_absPow _ _))
  refine ⟨_, _, hμ₁, hμ₂, ?_⟩
  let T : π.IntertwiningMap (prod₂ (twist σ (detChar (Fin a) (ν₁ * (absPow ℚ_[g] ((b : ℂ) / 2))⁻¹)))
      (twist ρ (detChar (Fin b) (ν₂ * (absPow ℚ_[g] (-(a : ℂ) / 2))⁻¹)))) :=
    { toFun := fun v => ⟨⟨fun x => Λ (π x v), fun q x => by
          show Λ (π (q * x) v) = _
          rw [map_mul, Module.End.mul_apply]
          exact law π σ ρ ν₁ ν₂ Λ hΛ q (π x v)⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hs v).mem_nhds (by simp)) fun h hh => by
          have hh' : π h v = v := hh
          refine Subtype.ext (funext fun x => ?_)
          show Λ (π (x * h) v) = Λ (π x v)
          rw [map_mul, Module.End.mul_apply, hh'])⟩
      map_add' := fun v w => Subtype.ext (Subtype.ext (funext fun x => by
        show Λ (π x (v + w)) = Λ (π x v) + Λ (π x w)
        rw [map_add, map_add]))
      map_smul' := fun c v => Subtype.ext (Subtype.ext (funext fun x => by
        show Λ (π x (c • v)) = c • Λ (π x v)
        rw [map_smul, map_smul]))
      isIntertwining' := fun h => LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun x => by
        show Λ (π x (π h v)) = Λ (π (x * h) v)
        rw [map_mul, Module.End.mul_apply])) }
  have hT : Function.Injective T := by
    haveI := hπ
    refine (Representation.IsIrreducible.injective_or_eq_zero T).resolve_right fun h0 => hΛ0 (LinearMap.ext fun v => ?_)
    have h1 : (T v).1.1 1 = 0 := by rw [h0]; rfl
    change Λ (π 1 v) = 0 at h1
    simpa using h1
  have hσ' := hys.tw _ (isSmoothChar_of_isUnram hμ₁)
  have hρ' := hyr.tw _ (isSmoothChar_of_isUnram hμ₂)
  obtain ⟨φ⟩ := nonempty_prod₂_equiv_prodIrr _ hσ'.isSmooth hσ'.isIrreducible _ hρ'.isSmooth hρ'.isIrreducible
    (Fin.sum_univ_two _)
  have hsub := (IsSubquotient.of_injective T hT).trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have key := Ysupp.hasSupport_of_isSubquotient_prodIrr hP
    (t := ![_, _]) (Fin.forall_fin_two.2 ⟨hσ'.of_equiv (IrrGL.equivOf _ _ _), hρ'.of_equiv (IrrGL.equivOf _ _ _)⟩)
    hπ hsub
  rw [Fin.sum_univ_two] at key
  exact key

end Ysupp.UnramifiedTwistSupport

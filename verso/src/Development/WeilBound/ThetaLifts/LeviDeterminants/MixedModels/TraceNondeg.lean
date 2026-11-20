import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.PureSt

noncomputable section

namespace PositivityTheory.Mix

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open mixedEmbedding
open scoped Classical

namespace Inf

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def rho (F : Type) [Field F] [NumberField F] : AF F →+* mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

def li (a : mixedSpace F) : AF F := ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rho_li (a : mixedSpace F) : rho F (li a) = a := (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply a

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem li_add (a b : mixedSpace F) : li (a + b) = li a + li b := Prod.ext (map_add _ a b) (add_zero _).symm

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem li_mul (a b : mixedSpace F) : li (a * b) = li a * li b := Prod.ext (map_mul _ a b) (mul_zero _).symm

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem li_rho (z : AF F) : li (rho F z) = li 1 * z :=
  Prod.ext (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _).trans (by
    change z.1 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm 1 * z.1
    rw [map_one, one_mul])) (zero_mul _).symm

def pr (w : (κ → AF F) × (κ → AF F)) : (κ → mixedSpace F) × (κ → mixedSpace F) := (fun i => rho F (w.1 i), fun i => rho F (w.2 i))

def lf (y : (κ → mixedSpace F) × (κ → mixedSpace F)) : (κ → AF F) × (κ → AF F) := (fun i => li (y.1 i), fun i => li (y.2 i))

omit [Fintype κ] in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pr_lf (y : (κ → mixedSpace F) × (κ → mixedSpace F)) : pr (lf y) = y :=
  Prod.ext (funext fun _ => rho_li _) (funext fun _ => rho_li _)

omit [Fintype κ] in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pr_smul (c : AF F) (w : (κ → AF F) × (κ → AF F)) : pr (c • w) = rho F c • pr w :=
  Prod.ext (funext fun _ => map_mul _ _ _) (funext fun _ => map_mul _ _ _)

omit [Fintype κ] in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lf_pr (w : (κ → AF F) × (κ → AF F)) : lf (pr w) = li (1 : mixedSpace F) • w :=
  Prod.ext (funext fun _ => li_rho _) (funext fun _ => li_rho _)

def loc (T : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] ((κ → AF F) × (κ → AF F))) :
    ((κ → mixedSpace F) × (κ → mixedSpace F)) →ₗ[mixedSpace F] ((κ → mixedSpace F) × (κ → mixedSpace F)) where
  toFun y := pr (T (lf y))
  map_add' y z := by
    have e : lf (y + z) = lf y + lf z := Prod.ext (funext fun _ => li_add _ _) (funext fun _ => li_add _ _)
    rw [e, map_add]
    exact Prod.ext (funext fun _ => map_add _ _ _) (funext fun _ => map_add _ _ _)
  map_smul' c y := by
    have e : lf (c • y) = li c • lf y := Prod.ext (funext fun _ => li_mul _ _) (funext fun _ => li_mul _ _)
    rw [e, map_smul, pr_smul, rho_li]
    rfl

omit [Fintype κ] in
/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem loc_pr (T : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] ((κ → AF F) × (κ → AF F))) (w : (κ → AF F) × (κ → AF F)) :
    loc T (pr w) = pr (T w) := by
  change pr (T (lf (pr w))) = _
  rw [lf_pr, map_smul, pr_smul, rho_li, one_smul]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem pr_dot (x y : κ → AF F) : (fun i => rho F (x i)) ⬝ᵥ (fun i => rho F (y i)) = rho F (x ⬝ᵥ y) := by
  simp [dotProduct, map_sum]

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem trace_nondeg (a : mixedSpace F) (h : ∀ b, Algebra.trace ℝ (mixedSpace F) (a * b) = 0) : a = 0 := by
  let b : mixedSpace F := (fun w => (a.1 w)⁻¹, fun w => (a.2 w)⁻¹)
  have h1 : a * b * a = a := Prod.ext (funext fun w => mul_inv_mul_cancel (a.1 w)) (funext fun w => mul_inv_mul_cancel (a.2 w))
  have h2 : IsIdempotentElem (Algebra.lmul ℝ (mixedSpace F) (a * b)) := by
    unfold IsIdempotentElem
    rw [← map_mul, ← mul_assoc, h1]
  have h3 := (LinearMap.IsIdempotentElem.isProj_range _ h2).trace
  have h4 : LinearMap.trace ℝ _ (Algebra.lmul ℝ (mixedSpace F) (a * b)) = 0 := h b
  rw [h4] at h3
  have h5 : LinearMap.range (Algebra.lmul ℝ (mixedSpace F) (a * b)) = ⊥ :=
    Submodule.finrank_eq_zero.1 (by exact_mod_cast h3.symm)
  have h6 : a * b * a ∈ LinearMap.range (Algebra.lmul ℝ (mixedSpace F) (a * b)) := ⟨a, rfl⟩
  rwa [h5, h1, Submodule.mem_bot] at h6

def betaL (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] : (κ → mixedSpace F) →ₗ[ℝ] (κ → mixedSpace F) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (beta F κ) (fun x y z => by simp only [beta, add_dotProduct, map_add]) (fun c x y => by simp [beta, smul_dotProduct])
    (fun x y z => by simp only [beta, dotProduct_add, map_add]) fun c x y => by simp [beta, dotProduct_smul]

end Inf

open Inf

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem infSt_of (h : RealSt) : InfSt := by
  intro F _ _ κ _ S hS
  let S₀ : ((κ → mixedSpace F) × (κ → mixedSpace F)) ≃ₗ[mixedSpace F] ((κ → mixedSpace F) × (κ → mixedSpace F)) :=
    LinearEquiv.ofLinear (loc S.toLinearMap) (loc S.symm.toLinearMap)
      (LinearMap.ext fun y => by
        change loc S.toLinearMap (pr (S.symm (lf y))) = y
        rw [loc_pr]; simp [pr_lf])
      (LinearMap.ext fun y => by
        change loc S.symm.toLinearMap (pr (S (lf y))) = y
        rw [loc_pr]; simp [pr_lf])
  have hp : ∀ w, (S₀.restrictScalars ℝ) (pr w) = pr (S w) := fun w => loc_pr S.toLinearMap w
  obtain ⟨T, hT⟩ := h (κ → mixedSpace F) (betaL F κ) (fun x y => congrArg (Algebra.trace ℝ (mixedSpace F)) (dotProduct_comm x y))
    (fun x hx => funext fun i => trace_nondeg _ fun b => by
      have e : beta F κ x (Pi.single i b) = 0 := hx _
      rwa [beta, dotProduct_single] at e)
    (S₀.restrictScalars ℝ) fun y z => by
      rw [← pr_lf y, ← pr_lf z, hp, hp]
      change beta F κ _ _ - beta F κ _ _ = beta F κ _ _ - beta F κ _ _
      simp only [beta, pr, pr_dot, ← map_sub, hS]
  refine ⟨T, fun w f g hg x => ?_⟩
  have := hT (pr w) f g hg x
  rw [hp] at this
  exact this

end PositivityTheory.Mix

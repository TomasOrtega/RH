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
The claim follows from `(InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply a`.
-/
theorem rho_li (a : mixedSpace F) : rho F (li a) = a := (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply a

/- English proof (translation)
The claim follows from `Prod.ext (map_add _ a b) (add_zero _).symm`.
-/
theorem li_add (a b : mixedSpace F) : li (a + b) = li a + li b := Prod.ext (map_add _ a b) (add_zero _).symm

/- English proof (translation)
The claim follows from `Prod.ext (map_mul _ a b) (mul_zero _).symm`.
-/
theorem li_mul (a b : mixedSpace F) : li (a * b) = li a * li b := Prod.ext (map_mul _ a b) (mul_zero _).symm

/- English proof (translation)
The claim follows from `Prod.ext (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _).trans (by change z.1 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm 1 * z.1 rw [map_one, one_mul])) (zero_mul _).symm`.
-/
theorem li_rho (z : AF F) : li (rho F z) = li 1 * z :=
  Prod.ext (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _).trans (by
    change z.1 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm 1 * z.1
    rw [map_one, one_mul])) (zero_mul _).symm

def pr (w : (κ → AF F) × (κ → AF F)) : (κ → mixedSpace F) × (κ → mixedSpace F) := (fun i => rho F (w.1 i), fun i => rho F (w.2 i))

def lf (y : (κ → mixedSpace F) × (κ → mixedSpace F)) : (κ → AF F) × (κ → AF F) := (fun i => li (y.1 i), fun i => li (y.2 i))

omit [Fintype κ] in
/- English proof (translation)
The claim follows from `Prod.ext (funext fun _ => rho_li _) (funext fun _ => rho_li _)`.
-/
theorem pr_lf (y : (κ → mixedSpace F) × (κ → mixedSpace F)) : pr (lf y) = y :=
  Prod.ext (funext fun _ => rho_li _) (funext fun _ => rho_li _)

omit [Fintype κ] in
/- English proof (translation)
The claim follows from `Prod.ext (funext fun _ => map_mul _ _ _) (funext fun _ => map_mul _ _ _)`.
-/
theorem pr_smul (c : AF F) (w : (κ → AF F) × (κ → AF F)) : pr (c • w) = rho F c • pr w :=
  Prod.ext (funext fun _ => map_mul _ _ _) (funext fun _ => map_mul _ _ _)

omit [Fintype κ] in
/- English proof (translation)
The claim follows from `Prod.ext (funext fun _ => li_rho _) (funext fun _ => li_rho _)`.
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
Express the relevant statement in the definitionally equal form `pr (T (lf (pr w))) = _`. Rewrite using `[lf_pr, map_smul, pr_smul, rho_li, one_smul]`.
-/
theorem loc_pr (T : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] ((κ → AF F) × (κ → AF F))) (w : (κ → AF F) × (κ → AF F)) :
    loc T (pr w) = pr (T w) := by
  change pr (T (lf (pr w))) = _
  rw [lf_pr, map_smul, pr_smul, rho_li, one_smul]

/- English proof (translation)
Simplify using `[dotProduct, map_sum]`.
-/
theorem pr_dot (x y : κ → AF F) : (fun i => rho F (x i)) ⬝ᵥ (fun i => rho F (y i)) = rho F (x ⬝ᵥ y) := by
  simp [dotProduct, map_sum]

/- English proof (translation)
Set `b : mixedSpace F` to `(fun w => (a.1 w)⁻¹, fun w => (a.2 w)⁻¹)`. Establish `h1 : a * b * a = a` using `Prod.ext (funext fun w => mul_inv_mul_cancel (a.1 w)) (funext fun w => mul_inv_mul_cancel (a.2 w))`. Establish `h2 : IsIdempotentElem (Algebra.lmul ℝ (mixedSpace F) (a * b))`. Unfold `IsIdempotentElem`. Rewrite using `[← map_mul, ← mul_assoc, h1]`.

Establish `h3` using `(LinearMap.IsIdempotentElem.isProj_range _ h2).trace`. Establish `h4 : LinearMap.trace ℝ _ (Algebra.lmul ℝ (mixedSpace F) (a * b)) = 0` using `h b`. Rewrite `h3` using `[h4]`. Establish `h5 : LinearMap.range (Algebra.lmul ℝ (mixedSpace F) (a * b)) = ⊥` using `Submodule.finrank_eq_zero.1 (by exact_mod_cast h3.symm)`. Establish `h6 : a * b * a ∈ LinearMap.range (Algebra.lmul ℝ (mixedSpace F) (a * b))` using `⟨a, rfl⟩`.

Rewrite `h6` using `[h5, h1, Submodule.mem_bot]`. Then use the resulting hypothesis.
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
Introduce `F _ _ κ _ S hS`. Set `S₀ : ((κ → mixedSpace F) × (κ → mixedSpace F)) ≃ₗ[mixedSpace F] ((κ → mixedSpace F) × (κ → mixedSpace F))` to `LinearEquiv.ofLinear (loc S.toLinearMap) (loc S.symm.toLinearMap) (LinearMap.ext fun y => by`. Express the relevant statement in the definitionally equal form `loc S.toLinearMap (pr (S.symm (lf y))) = y`. Rewrite using `[loc_pr]`. Simplify using `[pr_lf])`.

Use the proof step `(LinearMap.ext fun y => by`. Express the relevant statement in the definitionally equal form `loc S.symm.toLinearMap (pr (S (lf y))) = y`. Rewrite using `[loc_pr]`. Simplify using `[pr_lf])`. Establish `hp : ∀ w, (S₀.restrictScalars ℝ) (pr w) = pr (S w)` using `fun w => loc_pr S.toLinearMap w`.

Take `⟨T, hT⟩` from `h (κ → mixedSpace F) (betaL F κ) (fun x y => congrArg (Algebra.trace ℝ (mixedSpace F)) (dotProduct_comm x y)) (fun x hx => funext fun i => trace_nondeg _ fun b => by`. Establish `e : beta F κ x (Pi.single i b) = 0` using `hx _`. Rewrite using `[beta, dotProduct_single] at e)` and apply the resulting hypothesis. Use the proof step `(S₀.restrictScalars ℝ) fun y z => by`. Rewrite using `[← pr_lf y, ← pr_lf z, hp, hp]`.

Express the relevant statement in the definitionally equal form `beta F κ _ _ - beta F κ _ _ = beta F κ _ _ - beta F κ _ _`. Simplify using `only [beta, pr, pr_dot, ← map_sub, hS]`. Use `⟨T, fun w f g hg x => ?_⟩` and prove the remaining obligations. Use `hT (pr w) f g hg x` as an intermediate fact. Rewrite `this` using `[hp]`.

Conclude with `this`.
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

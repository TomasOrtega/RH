import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmStar

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjMult

section Rep

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}

def realEquiv (c : H' ≃ₗᵢ⋆[ℂ] H) : H' ≃L[ℝ] H where
  toFun := c
  invFun := c.symm
  map_add' := map_add c
  map_smul' r x := by
    rw [← Complex.coe_smul, map_smulₛₗ]
    simp
  left_inv := c.symm_apply_apply
  right_inv := c.apply_symm_apply
  continuous_toFun := c.continuous
  continuous_invFun := c.symm.continuous

/- English proof (translation)
Use `List.prod_induction _ (fun a b => mul_mem_UH J) (one_mem_UH J) fun x hx => ?_` and prove the remaining obligations. Take `⟨i, rfl⟩` from `List.mem_ofFn.1 hx`. Conclude with `GlobalTheory.SmoothAutCheck.exp_mem_UH hJ (hX i) _`.
-/
theorem expProd_mem (hJ : IsUnit J.det) {k : ℕ} {Xs : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ i, (Xs i)ᴴ * J + J * Xs i = 0) (t : Fin k → ℝ) :
    (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod ∈ Formalism.QuantumDeterminants.UH J := by
  refine List.prod_induction _ (fun a b => mul_mem_UH J) (one_mem_UH J) fun x hx => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  exact GlobalTheory.SmoothAutCheck.exp_mem_UH hJ (hX i) _

/- English proof (translation)
Introduce `k Xs hX`. Use `(realEquiv c).contDiff.comp (hw k Xs hX)` as an intermediate fact. Use `this using 2 with t` and compare the differences between its conclusion and the goal. Conclude with `(hc _ (expProd_mem hJ hX t) w).symm`.
-/
theorem smoothVec_conj (hJ : IsUnit J.det) (c : H' ≃ₗᵢ⋆[ℂ] H)
    (hc : ∀ g ∈ Formalism.QuantumDeterminants.UH J, ∀ w, c (σ' g w) = σ g (c w)) {w : H'}
    (hw : SmoothVec {X | Xᴴ * J + J * X = 0} σ' w) : SmoothVec {X | Xᴴ * J + J * X = 0} σ (c w) := by
  intro k Xs hX
  have := (realEquiv c).contDiff.comp (hw k Xs hX)
  convert this using 2 with t
  exact (hc _ (expProd_mem hJ hX t) w).symm

/- English proof (translation)
Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span (smoothVec_conj hJ c hc hx)`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx => rw [map_smulₛₗ]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem span_conj (hJ : IsUnit J.det) (c : H' ≃ₗᵢ⋆[ℂ] H)
    (hc : ∀ g ∈ Formalism.QuantumDeterminants.UH J, ∀ w, c (σ' g w) = σ g (c w)) {w : H'}
    (hw : w ∈ Submodule.span ℂ {w | SmoothVec {X | Xᴴ * J + J * X = 0} σ' w}) :
    c w ∈ Submodule.span ℂ {w | SmoothVec {X | Xᴴ * J + J * X = 0} σ w} := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (smoothVec_conj hJ c hc hx)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Establish `e : (fun t : ℝ => σ (NormedSpace.exp (t • X)) (c w)) = realEquiv c ∘ fun t : ℝ => σ' (NormedSpace.exp (t • X)) w`. Use function extensionality and compare the values at `fun t => (hc _ (GlobalTheory.SmoothAutCheck.exp_mem_UH hJ hX t) w).symm`. Rewrite using `[dRep, e, deriv, ContinuousLinearEquiv.comp_fderiv]`. Both sides reduce to the same expression.
-/
theorem dRep_conj (hJ : IsUnit J.det) (c : H' ≃ₗᵢ⋆[ℂ] H)
    (hc : ∀ g ∈ Formalism.QuantumDeterminants.UH J, ∀ w, c (σ' g w) = σ g (c w)) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : Xᴴ * J + J * X = 0) (w : H') : dRep σ X (c w) = c (dRep σ' X w) := by
  have e : (fun t : ℝ => σ (NormedSpace.exp (t • X)) (c w)) =
      realEquiv c ∘ fun t : ℝ => σ' (NormedSpace.exp (t • X)) w :=
    funext fun t => (hc _ (GlobalTheory.SmoothAutCheck.exp_mem_UH hJ hX t) w).symm
  rw [dRep, e, deriv, ContinuousLinearEquiv.comp_fderiv]
  rfl

/- English proof (translation)
Take `⟨S, C, hS, hC⟩` from `h`. Use `⟨{ toFun := fun w => star (ℓ (c w)) map_add' := fun x y => by simp map_smul' := fun a x => by rw [map_smulₛₗ, map_smul]; simp }, ⟨S, C, hS, fun w hw => ?_⟩, fun _ => rfl⟩` and prove the remaining obligations. Establish `e : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, Xᴴ * J + J * X = 0) → l.foldr (dRep σ) (c w) = c (l.foldr (dRep σ') w)`. Introduce `l`. Proceed by induction on `l with`.

Consider the case `nil => intro _`. Both sides reduce to the same expression. Consider the case `cons X l ih`. Introduce `hl`. Rewrite using `[List.foldr_cons, ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY), dRep_conj hJ c hc (hl X List.mem_cons_self), List.foldr_cons]`.

Establish `h1` using `hC _ (smoothVec_conj hJ c hc hw)`. Establish `h2 : (S.map fun l => ‖l.foldr (dRep σ) (c w)‖) = S.map fun l => ‖l.foldr (dRep σ') w‖` using `List.map_congr_left fun l hl => by rw [e l (hS l hl), c.norm_map]`. Rewrite `h1` using `[h2]`. Conclude with `(norm_star _).trans_le h1`.
-/
theorem sobCont_conj (hJ : IsUnit J.det) (c : H' ≃ₗᵢ⋆[ℂ] H)
    (hc : ∀ g ∈ Formalism.QuantumDeterminants.UH J, ∀ w, c (σ' g w) = σ g (c w)) {ℓ : H →ₗ[ℂ] ℂ}
    (h : Sobolev₂ {X | Xᴴ * J + J * X = 0} σ ℓ) :
    ∃ ℓ' : H' →ₗ[ℂ] ℂ, Sobolev₂ {X | Xᴴ * J + J * X = 0} σ' ℓ' ∧ ∀ w, ℓ' w = star (ℓ (c w)) := by
  obtain ⟨S, C, hS, hC⟩ := h
  refine ⟨{ toFun := fun w => star (ℓ (c w))
            map_add' := fun x y => by simp
            map_smul' := fun a x => by rw [map_smulₛₗ, map_smul]; simp }, ⟨S, C, hS, fun w hw => ?_⟩, fun _ => rfl⟩
  have e : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, Xᴴ * J + J * X = 0) →
      l.foldr (dRep σ) (c w) = c (l.foldr (dRep σ') w) := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons X l ih =>
      intro hl
      rw [List.foldr_cons, ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY), dRep_conj hJ c hc (hl X List.mem_cons_self),
        List.foldr_cons]
  have h1 := hC _ (smoothVec_conj hJ c hc hw)
  have h2 : (S.map fun l => ‖l.foldr (dRep σ) (c w)‖) = S.map fun l => ‖l.foldr (dRep σ') w‖ :=
    List.map_congr_left fun l hl => by rw [e l (hS l hl), c.norm_map]
  rw [h2] at h1
  exact (norm_star _).trans_le h1

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons a l ih`. Rewrite using `[List.prod_cons, List.map_cons, List.prod_cons, mul_assoc, ih]`. Simplify using `only [mul_assoc]`.

Rewrite using `[Matrix.mul_nonsing_inv_cancel_left _ _ hg]`.
-/
theorem prod_conj {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g.det) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    l.prod * g = g * (l.map fun a => g⁻¹ * a * g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, mul_assoc, ih]
    simp only [mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hg]

/- English proof (translation)
Introduce `k Xs hX`. Establish `hu` using `isUnit_of_UH hJ hg`. Establish `hd` using `(Matrix.isUnit_iff_isUnit_det _).1 hu`. Establish `hi : (g⁻¹)ᴴ * J * g⁻¹ = J`. Establish `: (hu.unit⁻¹).1 ∈ Formalism.QuantumDeterminants.UH J` using `(UG J).inv_mem (x := hu.unit) hg`.

Rewrite `this` using `[Matrix.coe_units_inv]`. Then use the resulting hypothesis. Establish `hg' : gᴴ * J * g = J` using `hg`. Establish `hX' : ∀ i, (g⁻¹ * Xs i * g)ᴴ * J + J * (g⁻¹ * Xs i * g) = 0` using `fun i => by`. Establish `h1 : (g⁻¹)ᴴ * J = J * g` using `by conv_rhs => rw [← hi]`. Rewrite using `[Matrix.nonsing_inv_mul_cancel_right _ _ hd]`.

Establish `h2 : J * g⁻¹ = gᴴ * J` using `by conv_lhs => rw [← hg']`. Rewrite using `[Matrix.mul_nonsing_inv_cancel_right _ _ hd]`. Establish `h3 : (Xs i)ᴴ * J + J * Xs i = 0` using `hX i`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, mul_assoc]`.

Use `_ = gᴴ * ((Xs i)ᴴ * J + J * Xs i) * g := by rw [h1, h2]; simp only [mul_add, add_mul, mul_assoc]`. Use `_ = 0 := by rw [h3, mul_zero, zero_mul]`. Use `((σ g).restrictScalars ℝ).contDiff.comp (hw k _ hX')` as an intermediate fact. Use `this using 2 with t` and compare the differences between its conclusion and the goal. Express the relevant statement in the definitionally equal form `_ = σ g (σ _ w)`.

Rewrite using `[← hm _ (expProd_mem hJ hX t) _ hg, ← hm _ hg _ (expProd_mem hJ hX' t), prod_conj hd, List.map_ofFn]`. Use `congr 5`. Use function extensionality and compare the values at `i`. Rewrite using `[Function.comp_apply, ← Matrix.exp_conj' _ _ hu, mul_smul_comm, smul_mul_assoc]`.
-/
theorem smoothVec_act (hJ : IsUnit J.det)
    (hm : ∀ g ∈ Formalism.QuantumDeterminants.UH J, ∀ g' ∈ Formalism.QuantumDeterminants.UH J, ∀ w, σ (g * g') w = σ g (σ g' w))
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH J) {w : H}
    (hw : SmoothVec {X | Xᴴ * J + J * X = 0} σ w) : SmoothVec {X | Xᴴ * J + J * X = 0} σ (σ g w) := by
  intro k Xs hX
  have hu := isUnit_of_UH hJ hg
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have hi : (g⁻¹)ᴴ * J * g⁻¹ = J := by
    have : (hu.unit⁻¹).1 ∈ Formalism.QuantumDeterminants.UH J := (UG J).inv_mem (x := hu.unit) hg
    rwa [Matrix.coe_units_inv] at this
  have hg' : gᴴ * J * g = J := hg
  have hX' : ∀ i, (g⁻¹ * Xs i * g)ᴴ * J + J * (g⁻¹ * Xs i * g) = 0 := fun i => by
    have h1 : (g⁻¹)ᴴ * J = J * g := by
      conv_rhs => rw [← hi]
      rw [Matrix.nonsing_inv_mul_cancel_right _ _ hd]
    have h2 : J * g⁻¹ = gᴴ * J := by
      conv_lhs => rw [← hg']
      rw [Matrix.mul_nonsing_inv_cancel_right _ _ hd]
    have h3 : (Xs i)ᴴ * J + J * Xs i = 0 := hX i
    calc _ = gᴴ * (Xs i)ᴴ * ((g⁻¹)ᴴ * J) + J * g⁻¹ * Xs i * g := by
          simp only [Matrix.conjTranspose_mul, mul_assoc]
      _ = gᴴ * ((Xs i)ᴴ * J + J * Xs i) * g := by rw [h1, h2]; simp only [mul_add, add_mul, mul_assoc]
      _ = 0 := by rw [h3, mul_zero, zero_mul]
  have := ((σ g).restrictScalars ℝ).contDiff.comp (hw k _ hX')
  convert this using 2 with t
  change _ = σ g (σ _ w)
  rw [← hm _ (expProd_mem hJ hX t) _ hg, ← hm _ hg _ (expProd_mem hJ hX' t), prod_conj hd, List.map_ofFn]
  congr 5
  funext i
  rw [Function.comp_apply, ← Matrix.exp_conj' _ _ hu, mul_smul_comm, smul_mul_assoc]

end Rep

variable {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar}

/- English proof (translation)
Establish `h1 : M.σ τ 1 = 1` using `(M.ds τ).2.2.1.1.1`. Rewrite using `[DSModel.rep, mul_one, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)), h1]`. Both sides reduce to the same expression.
-/
theorem rep_one (M : DSModel V S) (τ : D.what₂.Tau) (w : M.H τ) : M.rep τ 1 w = w := by
  have h1 : M.σ τ 1 = 1 := (M.ds τ).2.2.1.1.1
  rw [DSModel.rep, mul_one, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)), h1]
  rfl

/- English proof (translation)
Establish `hd` using `(Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)`. Establish `key : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ UJset (M.ε τ)` using `fun g hg => by`. Establish `hg' : gᴴ * gramAt D V τ * g = gramAt D V τ` using `hg`. Rewrite `hg'` using `[← M.fr_gram τ]`. Express the relevant statement in the definitionally equal form `_ * _ * _ = _`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, mul_assoc]`. Use `_ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by`. Rewrite using `[hg']`. Simplify using `only [Matrix.conjTranspose_mul, mul_assoc]`.

Use `_ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp`. Introduce `g hg g' hg' w`. Establish `h` using `(M.ds τ).2.2.1.1.2 _ (key g hg) _ (key g' hg')`. Establish `e : M.fr τ * (g * g') * (M.fr τ)⁻¹ = (M.fr τ * g * (M.fr τ)⁻¹) * (M.fr τ * g' * (M.fr τ)⁻¹)`. Simplify using `only [mul_assoc]`.

Rewrite using `[Matrix.nonsing_inv_mul_cancel_left _ _ hd]`. Rewrite using `[DSModel.rep, e, h]`. Both sides reduce to the same expression.
-/
theorem rep_mul (M : DSModel V S) (τ : D.what₂.Tau) : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
    ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, M.rep τ (g * g') w = M.rep τ g (M.rep τ g' w) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have key : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ UJset (M.ε τ) := fun g hg => by
    have hg' : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
    rw [← M.fr_gram τ] at hg'
    change _ * _ * _ = _
    calc _ = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g) * (M.fr τ)⁻¹ := by
          simp only [Matrix.conjTranspose_mul, mul_assoc]
      _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
          rw [hg']; simp only [Matrix.conjTranspose_mul, mul_assoc]
      _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp
  intro g hg g' hg' w
  have h := (M.ds τ).2.2.1.1.2 _ (key g hg) _ (key g' hg')
  have e : M.fr τ * (g * g') * (M.fr τ)⁻¹ = (M.fr τ * g * (M.fr τ)⁻¹) * (M.fr τ * g' * (M.fr τ)⁻¹) := by
    simp only [mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  rw [DSModel.rep, e, h]
  rfl

/- English proof (translation)
Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Conclude with `Submodule.subset_span (smoothVec_act (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) (rep_mul M τ) hg hx)`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem rep_mem_sm (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {w : M.H τ} (hw : w ∈ M.sm τ) : M.rep τ g w ∈ M.sm τ := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    exact Submodule.subset_span (smoothVec_act (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) (rep_mul M τ) hg hx)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Establish `h1 : ∀ y ∈ realMon θ V, ∀ v, ∃ v', ∀ x, T v (x * y) = T v' x`. Introduce `y hy`. Proceed by induction on `hy using Submonoid.closure_induction with`. Consider the case `mem y hy`. Take `⟨τ, g, hg, rfl⟩` from `hy`.

Introduce `v`. Conclude with `⟨_, fun x => (congrFun (h.equiv τ g hg v ⟨_, rep_mem_sm M τ hg (v τ).2⟩ rfl) x).symm⟩`. Consider the case `one => exact fun v => ⟨v, fun x => by rw [mul_one]⟩`. Consider the case `mul a b _ _ ha hb`. Introduce `v`.

Take `⟨v₁, h₁⟩` from `hb v`. Take `⟨v₂, h₂⟩` from `ha v₁`. Conclude with `⟨v₂, fun x => by rw [← mul_assoc, h₁, h₂]⟩`. Introduce `y hy τ x`. Take `⟨u, hu⟩` from `h1 y hy v`.

Simplify using `only [hu]`. Use `⟨?_, fun g hg g' hg' => ?_⟩` and prove the remaining obligations. Use `congrFun (h.equiv τ 1 (one_mem_UH _) u (u τ) (rep_one M τ _).symm) x` as an intermediate fact. Rewrite `this` using `[Function.update_eq_self]`. Conclude with `this.symm`.

Establish `a1` using `congrFun (h.equiv τ g' hg' u ⟨_, rep_mem_sm M τ hg' (u τ).2⟩ rfl) (x * atTau θ V τ g)`. Establish `a2` using `congrFun (h.equiv τ (g * g') (mul_mem_UH _ hg hg') u ⟨_, rep_mem_sm M τ (mul_mem_UH _ hg hg') (u τ).2⟩ rfl) x`. Establish `a3` using `congrFun (h.equiv τ g hg (Function.update u τ ⟨_, rep_mem_sm M τ hg' (u τ).2⟩) ⟨_, rep_mem_sm M τ (mul_mem_UH _ hg hg') (u τ).2⟩ (by rw [Function.update_self]; exact rep_mul M τ g hg g' hg' _)) x`. Rewrite `a3` using `[Function.update_idem]`. Conclude with `a1.symm.trans (a3.symm.trans a2)`.
-/
theorem value_mem_homFun {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M}
    (h : IsMultMap θ M J χ T) (v : M.Vec) : T v ∈ homFun θ V := by
  classical
  have h1 : ∀ y ∈ realMon θ V, ∀ v, ∃ v', ∀ x, T v (x * y) = T v' x := by
    intro y hy
    induction hy using Submonoid.closure_induction with
    | mem y hy =>
      obtain ⟨τ, g, hg, rfl⟩ := hy
      intro v
      exact ⟨_, fun x => (congrFun (h.equiv τ g hg v ⟨_, rep_mem_sm M τ hg (v τ).2⟩ rfl) x).symm⟩
    | one => exact fun v => ⟨v, fun x => by rw [mul_one]⟩
    | mul a b _ _ ha hb =>
      intro v
      obtain ⟨v₁, h₁⟩ := hb v
      obtain ⟨v₂, h₂⟩ := ha v₁
      exact ⟨v₂, fun x => by rw [← mul_assoc, h₁, h₂]⟩
  intro y hy τ x
  obtain ⟨u, hu⟩ := h1 y hy v
  simp only [hu]
  refine ⟨?_, fun g hg g' hg' => ?_⟩
  · have := congrFun (h.equiv τ 1 (one_mem_UH _) u (u τ) (rep_one M τ _).symm) x
    rw [Function.update_eq_self] at this
    exact this.symm
  · have a1 := congrFun (h.equiv τ g' hg' u ⟨_, rep_mem_sm M τ hg' (u τ).2⟩ rfl) (x * atTau θ V τ g)
    have a2 := congrFun (h.equiv τ (g * g') (mul_mem_UH _ hg hg') u ⟨_, rep_mem_sm M τ (mul_mem_UH _ hg hg') (u τ).2⟩ rfl) x
    have a3 := congrFun (h.equiv τ g hg (Function.update u τ ⟨_, rep_mem_sm M τ hg' (u τ).2⟩)
      ⟨_, rep_mem_sm M τ (mul_mem_UH _ hg hg') (u τ).2⟩ (by rw [Function.update_self]; exact rep_mul M τ g hg g' hg' _)) x
    rw [Function.update_idem] at a3
    exact a1.symm.trans (a3.symm.trans a2)

/- English proof (translation)
Introduce `D V S S' θ M M' c hc`. Establish `hs : ∀ τ {w : M'.H τ}, w ∈ M'.sm τ → c τ w ∈ M.sm τ` using `fun τ _ hw => span_conj (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) (c τ) (hc τ) hw`. Use `⟨fun τ w => ⟨hs τ, fun hw => ?_⟩, fun J χ T hT => ?_⟩` and prove the remaining obligations. Use `span_conj (σ := M'.rep τ) (σ' := M.rep τ) (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) (c τ).symm (fun g hg w => (c τ).injective (by rw [hc τ g hg, (c τ).apply_symm_apply, (c τ).apply_symm_apply])) hw` as an intermediate fact. Rewrite `this` using `[(c τ).symm_apply_apply]`. Then use the resulting hypothesis.

Establish `h` using `(GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ T).1 hT`. Set `cs : ∀ τ, M'.sm τ → M.sm τ` to `fun τ w => ⟨c τ w, hs τ w.2⟩`. Set `cv : M'.Vec → M.Vec` to `fun v τ => cs τ (v τ)`. Establish `hup : ∀ [DecidableEq D.what₂.Tau] (v : M'.Vec) τ w, cv (Function.update v τ w) = Function.update (cv v) τ (cs τ w)` using `fun v τ w => funext fun ρ => Function.apply_update cs v τ w ρ`. Set `T' : MMap M'` to `{ toFun := fun v => star (T (cv v)) map_update_add' := fun v τ x y => by`.

Establish `: cs τ (x + y) = cs τ x + cs τ y` using `Subtype.ext (map_add (c τ) _ _)`. Rewrite using `[hup, hup, hup, this, T.map_update_add, star_add]`. Use the proof step `map_update_smul' := fun v τ a x => by`. Establish `: cs τ (a • x) = star a • cs τ x` using `Subtype.ext (map_smulₛₗ (c τ) _ _)`. Rewrite using `[hup, hup, this, T.map_update_smul, star_smul, star_star] }`.

Establish `hT' : ∀ v, T' v = star (T (cv v))` using `fun _ => rfl`. Use `⟨T', Submodule.subset_span ⟨fun v => isAutFunSm_star (h.aut _) (value_mem_homFun h _), fun v => ?_, fun v k hk g => ?_, fun τ g hg v w hw => ?_, fun τ v x => ?_⟩, fun v' v hv g => ?_⟩` and prove the remaining obligations. Introduce `r C hC μ 𝓕 hμ h𝓕 g`. Use `h.cusp (cv v) r C hC μ 𝓕 hμ h𝓕 g` as an intermediate fact. Express the relevant statement in the definitionally equal form `∫ n in 𝓕, starRingEnd ℂ (T (cv v) ((n : GA D V) * g)) ∂μ = 0`.

Rewrite using `[integral_conj, this, map_zero]`. Rewrite using `[hT', Pi.star_apply, Pi.star_apply, h.lev _ k hk, star_mul']`. Rewrite using `[hT', hT', hup, h.equiv τ g hg (cv v) (cs τ w) (by change c τ w = _; rw [hw, hc τ g hg])]`. Both sides reduce to the same expression. Take `⟨ℓ, h1, h2⟩` from `h.cont τ (cv v) x`.

Take `⟨ℓ', h3, h4⟩` from `sobCont_conj (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) (c τ) (hc τ) h1`. Use `⟨ℓ', h3, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[h4, hT', hup, Pi.star_apply, ← h2]`. Establish `: cv v' = v` using `funext fun τ => Subtype.ext (hv τ).symm`. Rewrite using `[hT', this, Pi.star_apply]`.
-/
theorem conj_mult : ∀ {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w)) → (∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) ∧ ∀ J χ, ∀ T ∈ Mult θ M J χ, ∃ T' ∈ Mult θ M' J (fun k => star (χ k)), ∀ (v' : M'.Vec) (v : M.Vec), (∀ τ, (v τ : M.H τ) = c τ (v' τ)) → ∀ g, T' v' g = star (T v g) := by
  intro D V S S' θ M M' c hc
  classical
  have hs : ∀ τ {w : M'.H τ}, w ∈ M'.sm τ → c τ w ∈ M.sm τ := fun τ _ hw =>
    span_conj (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) (c τ) (hc τ) hw
  refine ⟨fun τ w => ⟨hs τ, fun hw => ?_⟩, fun J χ T hT => ?_⟩
  · have := span_conj (σ := M'.rep τ) (σ' := M.rep τ) (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) (c τ).symm
      (fun g hg w => (c τ).injective (by rw [hc τ g hg, (c τ).apply_symm_apply, (c τ).apply_symm_apply])) hw
    rwa [(c τ).symm_apply_apply] at this
  have h := (GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ T).1 hT
  let cs : ∀ τ, M'.sm τ → M.sm τ := fun τ w => ⟨c τ w, hs τ w.2⟩
  let cv : M'.Vec → M.Vec := fun v τ => cs τ (v τ)
  have hup : ∀ [DecidableEq D.what₂.Tau] (v : M'.Vec) τ w, cv (Function.update v τ w) = Function.update (cv v) τ (cs τ w) :=
    fun v τ w => funext fun ρ => Function.apply_update cs v τ w ρ
  let T' : MMap M' :=
    { toFun := fun v => star (T (cv v))
      map_update_add' := fun v τ x y => by
        have : cs τ (x + y) = cs τ x + cs τ y := Subtype.ext (map_add (c τ) _ _)
        rw [hup, hup, hup, this, T.map_update_add, star_add]
      map_update_smul' := fun v τ a x => by
        have : cs τ (a • x) = star a • cs τ x := Subtype.ext (map_smulₛₗ (c τ) _ _)
        rw [hup, hup, this, T.map_update_smul, star_smul, star_star] }
  have hT' : ∀ v, T' v = star (T (cv v)) := fun _ => rfl
  refine ⟨T', Submodule.subset_span ⟨fun v => isAutFunSm_star (h.aut _) (value_mem_homFun h _), fun v => ?_,
    fun v k hk g => ?_, fun τ g hg v w hw => ?_, fun τ v x => ?_⟩, fun v' v hv g => ?_⟩
  · intro r C hC μ 𝓕 hμ h𝓕 g
    have := h.cusp (cv v) r C hC μ 𝓕 hμ h𝓕 g
    change ∫ n in 𝓕, starRingEnd ℂ (T (cv v) ((n : GA D V) * g)) ∂μ = 0
    rw [integral_conj, this, map_zero]
  · rw [hT', Pi.star_apply, Pi.star_apply, h.lev _ k hk, star_mul']
  · rw [hT', hT', hup, h.equiv τ g hg (cv v) (cs τ w) (by change c τ w = _; rw [hw, hc τ g hg])]
    rfl
  · obtain ⟨ℓ, h1, h2⟩ := h.cont τ (cv v) x
    obtain ⟨ℓ', h3, h4⟩ := sobCont_conj (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) (c τ) (hc τ) h1
    refine ⟨ℓ', h3, fun w => ?_⟩
    rw [h4, hT', hup, Pi.star_apply, ← h2]
  · have : cv v' = v := funext fun τ => Subtype.ext (hv τ).symm
    rw [hT', this, Pi.star_apply]

end GlobalTheory.ConjMult

end

import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.TA

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

/- English proof (translation)
Simplify using `[qdet, qminor, Tm, map_list_prod, List.map_ofFn, Function.comp_def, apply_ite φ]`.
-/
theorem qdet_map' {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {m : ℕ} (φ : A →ₐ[ℂ] B)
    (E : Fin m → Fin m → A) (u : ℂ) : φ (qdet E u) = qdet (fun a b => φ (E a b)) u := by
  simp [qdet, qminor, Tm, map_list_prod, List.map_ofFn, Function.comp_def, apply_ite φ]

/- English proof (translation)
Unfold `qdet qminor`. Use `Commute.sum_left _ _ _ fun σ _ => ?_` and prove the remaining obligations. Use `Commute.mul_left (Int.cast_commute _ _) (Commute.list_prod_left _ _ ?_)` and prove the remaining obligations. Introduce `x hx`. Take `⟨k, rfl⟩` from `List.mem_ofFn.mp hx`.

Unfold `Tm`. Use `Commute.add_left ?_ (h _ _)` and prove the remaining obligations. Use `split_ifs`. Conclude with `Algebra.commute_algebraMap_left _ _`. Conclude with `Commute.zero_left _`.
-/
theorem qdet_commute {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (u : ℂ) (Z : A)
    (h : ∀ a b, Commute (E a b) Z) : Commute (qdet E u) Z := by
  unfold qdet qminor
  refine Commute.sum_left _ _ _ fun σ _ => ?_
  refine Commute.mul_left (Int.cast_commute _ _) (Commute.list_prod_left _ _ ?_)
  intro x hx
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
  unfold Tm
  refine Commute.add_left ?_ (h _ _)
  split_ifs
  · exact Algebra.commute_algebraMap_left _ _
  · exact Commute.zero_left _

/- English proof (translation)
Introduce `a b c d`. Simplify using `only`. Rewrite using `[← map_mul, ← map_mul, ← map_sub, h a b c d]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem glRel_map {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {m : ℕ} (φ : A →ₐ[ℂ] B)
    (E : Fin m → Fin m → A) (h : GlRel E) : GlRel fun a b => φ (E a b) := by
  intro a b c d
  dsimp only
  rw [← map_mul, ← map_mul, ← map_sub, h a b c d]
  split_ifs <;> simp

/- English proof (translation)
Establish `hs : s ⊆ Subalgebra.centralizer ℂ {Z}` using `fun T hT => by`. Rewrite using `[SetLike.mem_coe, Subalgebra.mem_centralizer_iff]`. Introduce `g hg`. Rewrite `hg` using `[Set.mem_singleton_iff]`. Rewrite using `[hg]`.

Conclude with `(h T hT).symm.eq`. Establish `hX'` using `Algebra.adjoin_le hs hX`. Rewrite `hX'` using `[Subalgebra.mem_centralizer_iff]`. Conclude with `(hX' Z rfl).symm`.
-/
theorem comm_of_mem_adjoin {A : Type*} [Ring A] [Algebra ℂ A] {s : Set A} {X Z : A}
    (hX : X ∈ Algebra.adjoin ℂ s) (h : ∀ T ∈ s, Commute T Z) : Commute X Z := by
  have hs : s ⊆ Subalgebra.centralizer ℂ {Z} := fun T hT => by
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact (h T hT).symm.eq
  have hX' := Algebra.adjoin_le hs hX
  rw [Subalgebra.mem_centralizer_iff] at hX'
  exact (hX' Z rfl).symm

variable {P : Type} [Fintype P] [DecidableEq P]

omit [Fintype P] [DecidableEq P] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem liftA_apply (B : Module.End ℂ M) : liftA n M P B = lift B := rfl

omit [Fintype P] [DecidableEq P] in
/- English proof (translation)
Introduce `u`. Establish `e : (fun a b => (lift (F a b) : Module.End ℂ (TV n M P))) = fun a b => liftA n M P (F a b)`. Use function extensionality and compare the values at `a b`. Rewrite using `[liftA_apply]`. Rewrite using `[e, ← qdet_map', h u, AlgHom.commutes]`.
-/
theorem qdet_lift (F : Fin n → Fin n → Module.End ℂ M) (l : Fin n → ℂ) (h : HasChar F l) :
    HasChar (fun a b => (lift (F a b) : Module.End ℂ (TV n M P))) l := by
  intro u
  have e : (fun a b => (lift (F a b) : Module.End ℂ (TV n M P))) = fun a b => liftA n M P (F a b) := by
    funext a b
    rw [liftA_apply]
  rw [e, ← qdet_map', h u, AlgHom.commutes]

omit [Fintype P] in
/- English proof (translation)
Use function extensionality and compare the values at `a b`. Simplify using `[tE]`.
-/
theorem tE_empty (F : Fin n → Fin n → Module.End ℂ M) :
    (tE (∅ : Finset P) F : Fin n → Fin n → Module.End ℂ (TV n M P)) = fun a b => lift (F a b) := by
  funext a b
  simp [tE]

omit [Fintype P] in
/- English proof (translation)
Unfold `tE`. Use `Commute.add_left ?_ (Commute.sum_left _ _ _ fun p _ => ?_)` and prove the remaining obligations. Establish `hc` using `(h a b).map (liftA n M P)`. Simplify `hc` using `only [liftA_apply]`. Unfold `Commute SemiconjBy`.

Use `LinearMap.ext fun x => funext fun I => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, eAt, lift, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem tE_comm_lift (S : Finset P) (F : Fin n → Fin n → Module.End ℂ M) (B : Module.End ℂ M)
    (h : ∀ c d, Commute (F c d) B) (a b : Fin n) :
    Commute (tE S F a b : Module.End ℂ (TV n M P)) (lift B) := by
  unfold tE
  refine Commute.add_left ?_ (Commute.sum_left _ _ _ fun p _ => ?_)
  · have hc := (h a b).map (liftA n M P)
    simpa only [liftA_apply] using hc
  · unfold Commute SemiconjBy
    refine LinearMap.ext fun x => funext fun I => ?_
    simp only [Module.End.mul_apply, eAt, lift, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval]
    split_ifs <;> simp

/- English proof (translation)
Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Simplify using `[cA, alt, pm, lift, LinearMap.sum_apply, map_sum, map_zsmul]`.
-/
theorem cA_lift {C : Type} [DecidableEq C] (col : P → C) (b : P → Fin n) (B : Module.End ℂ M) :
    cA col b ∘ₗ lift B = B ∘ₗ (cA col b : TV n M P →ₗ[ℂ] M) := by
  refine LinearMap.ext fun x => ?_
  simp [cA, alt, pm, lift, LinearMap.sum_apply, map_sum, map_zsmul]

def cj {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W) :
    Module.End ℂ W →ₐ[ℂ] Module.End ℂ V where
  toFun X := e.symm.toLinearMap ∘ₗ X ∘ₗ e.toLinearMap
  map_one' := LinearMap.ext fun v => by simp
  map_mul' X Y := LinearMap.ext fun v => by simp
  map_zero' := LinearMap.ext fun v => by simp
  map_add' X Y := LinearMap.ext fun v => by simp
  commutes' r := LinearMap.ext fun v => by simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cj_apply {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    (X : Module.End ℂ W) (v : V) : cj e X v = e.symm (X (e v)) := rfl

end PositivityTheory.Rg.Cz.TA

end

import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace CurryingSwaps

variable {α : Type*} {m k : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `x`. Use `Fin.addCases (fun i' => ?_) (fun j' => ?_) x` and prove the remaining obligations. Distinguish the cases in `h : i' = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Function.update_of_ne (fun e => h (Fin.castAdd_injective _ _ e)), Fin.append_left, Fin.append_left, Function.update_of_ne h]`. Rewrite using `[Function.update_of_ne (fun e => by simp [Fin.ext_iff] at e; omega), Fin.append_right, Fin.append_right]`.
-/
theorem upd_castAdd (I : Fin m → α) (J : Fin k → α) (i : Fin m) (v : α) :
    Function.update (Fin.append I J) (Fin.castAdd k i) v = Fin.append (Function.update I i v) J := by
  funext x
  refine Fin.addCases (fun i' => ?_) (fun j' => ?_) x
  · by_cases h : i' = i
    · subst h; simp
    · rw [Function.update_of_ne (fun e => h (Fin.castAdd_injective _ _ e)), Fin.append_left, Fin.append_left,
        Function.update_of_ne h]
  · rw [Function.update_of_ne (fun e => by simp [Fin.ext_iff] at e; omega), Fin.append_right, Fin.append_right]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Use `Fin.addCases (fun i' => ?_) (fun j' => ?_) x` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (fun e => by simp [Fin.ext_iff] at e; omega), Fin.append_left, Fin.append_left]`. Distinguish the cases in `h : j' = j`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne (fun e => h (Fin.natAdd_injective _ _ e)), Fin.append_right, Fin.append_right, Function.update_of_ne h]`.
-/
theorem upd_natAdd (I : Fin m → α) (J : Fin k → α) (j : Fin k) (v : α) :
    Function.update (Fin.append I J) (Fin.natAdd m j) v = Fin.append I (Function.update J j v) := by
  funext x
  refine Fin.addCases (fun i' => ?_) (fun j' => ?_) x
  · rw [Function.update_of_ne (fun e => by simp [Fin.ext_iff] at e; omega), Fin.append_left, Fin.append_left]
  · by_cases h : j' = j
    · subst h; simp
    · rw [Function.update_of_ne (fun e => h (Fin.natAdd_injective _ _ e)), Fin.append_right, Fin.append_right,
        Function.update_of_ne h]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Use `Fin.addCases (fun a => ?_) (fun b => ?_) x` and prove the remaining obligations. Apply the tactic sequence `simp only [Function.comp_apply, Fin.append_left, Equiv.swap_apply_def, Fin.castAdd_inj] split_ifs <;> simp`. Establish `h1 : Fin.natAdd m b ≠ Fin.castAdd k i` using `fun e => by simp [Fin.ext_iff] at e; omega`. Establish `h2 : Fin.natAdd m b ≠ Fin.castAdd k i'` using `fun e => by simp [Fin.ext_iff] at e; omega`.

Simplify using `only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_right]`.
-/
theorem swap_castAdd (I : Fin m → α) (J : Fin k → α) (i i' : Fin m) :
    Fin.append I J ∘ Equiv.swap (Fin.castAdd k i) (Fin.castAdd k i') = Fin.append (I ∘ Equiv.swap i i') J := by
  funext x
  refine Fin.addCases (fun a => ?_) (fun b => ?_) x
  · simp only [Function.comp_apply, Fin.append_left, Equiv.swap_apply_def, Fin.castAdd_inj]
    split_ifs <;> simp
  · have h1 : Fin.natAdd m b ≠ Fin.castAdd k i := fun e => by simp [Fin.ext_iff] at e; omega
    have h2 : Fin.natAdd m b ≠ Fin.castAdd k i' := fun e => by simp [Fin.ext_iff] at e; omega
    simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_right]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Use `Fin.addCases (fun a => ?_) (fun b => ?_) x` and prove the remaining obligations. Establish `h1 : Fin.castAdd k a ≠ Fin.natAdd m j` using `fun e => by simp [Fin.ext_iff] at e; omega`. Establish `h2 : Fin.castAdd k a ≠ Fin.natAdd m j'` using `fun e => by simp [Fin.ext_iff] at e; omega`. Simplify using `only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_left]`.

Apply the tactic sequence `simp only [Function.comp_apply, Fin.append_right, Equiv.swap_apply_def, Fin.natAdd_inj] split_ifs <;> simp`.
-/
theorem swap_natAdd (I : Fin m → α) (J : Fin k → α) (j j' : Fin k) :
    Fin.append I J ∘ Equiv.swap (Fin.natAdd m j) (Fin.natAdd m j') = Fin.append I (J ∘ Equiv.swap j j') := by
  funext x
  refine Fin.addCases (fun a => ?_) (fun b => ?_) x
  · have h1 : Fin.castAdd k a ≠ Fin.natAdd m j := fun e => by simp [Fin.ext_iff] at e; omega
    have h2 : Fin.castAdd k a ≠ Fin.natAdd m j' := fun e => by simp [Fin.ext_iff] at e; omega
    simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_left]
  · simp only [Function.comp_apply, Fin.append_right, Equiv.swap_apply_def, Fin.natAdd_inj]
    split_ifs <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `x`. Use `Fin.addCases (fun a => ?_) (fun b => ?_) x` and prove the remaining obligations. Establish `h2 : Fin.castAdd k a ≠ Fin.natAdd m j` using `fun e => by simp [Fin.ext_iff] at e; omega`. Distinguish the cases in `h : a = i`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Establish `h1 : Fin.castAdd k a ≠ Fin.castAdd k i` using `fun e => h (Fin.castAdd_injective _ _ e)`. Simplify using `only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_left, Function.update_of_ne h]`. Establish `h1 : Fin.natAdd m b ≠ Fin.castAdd k i` using `fun e => by simp [Fin.ext_iff] at e; omega`. Distinguish the cases in `h : b = j`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Establish `h2 : Fin.natAdd m b ≠ Fin.natAdd m j` using `fun e => h (Fin.natAdd_injective _ _ e)`. Simplify using `only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_right, Function.update_of_ne h]`.
-/
theorem swap_mixed (I : Fin m → α) (J : Fin k → α) (i : Fin m) (j : Fin k) :
    Fin.append I J ∘ Equiv.swap (Fin.castAdd k i) (Fin.natAdd m j) =
      Fin.append (Function.update I i (J j)) (Function.update J j (I i)) := by
  funext x
  refine Fin.addCases (fun a => ?_) (fun b => ?_) x
  · have h2 : Fin.castAdd k a ≠ Fin.natAdd m j := fun e => by simp [Fin.ext_iff] at e; omega
    by_cases h : a = i
    · subst h; simp
    · have h1 : Fin.castAdd k a ≠ Fin.castAdd k i := fun e => h (Fin.castAdd_injective _ _ e)
      simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_left,
        Function.update_of_ne h]
  · have h1 : Fin.natAdd m b ≠ Fin.castAdd k i := fun e => by simp [Fin.ext_iff] at e; omega
    by_cases h : b = j
    · subst h; simp
    · have h2 : Fin.natAdd m b ≠ Fin.natAdd m j := fun e => h (Fin.natAdd_injective _ _ e)
      simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_right,
        Function.update_of_ne h]

/- English proof (translation)
Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem iteApp {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (p : Prop) [Decidable p]
    (g : V →ₗ[ℂ] W) (x : V) : (if p then g else 0) x = if p then g x else 0 := by
  split_ifs <;> rfl

end CurryingSwaps

open CurryingSwaps in
/- English proof (translation)
Introduce `n M _ _ E m k`. Use `⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `f g h`. Use function extensionality and compare the values at `K`. Use `congrFun (congrFun (congrArg (fun x => x) h) (fun j => K (Fin.natAdd m j))) (fun i => K (Fin.castAdd k i))` as an intermediate fact.

Simplify `this` using `only [curF_apply, Fin.append_castAdd_natAdd]`. Introduce `g`. Use `⟨fun K => g (fun j => K (Fin.natAdd m j)) (fun i => K (Fin.castAdd k i)), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `J I`. Simplify using `only [curF_apply, Fin.append_left, Fin.append_right]`.

Introduce `a b`. Use `LinearMap.ext fun f => funext fun J => funext fun I => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, curF_apply, tE_apply, Pi.add_apply, Finset.sum_apply, ite_apply, Pi.zero_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right, upd_castAdd, upd_natAdd, add_assoc]`. Introduce `i`. Use `LinearMap.ext fun f => funext fun J => funext fun I => ?_` and prove the remaining obligations.

Establish `hz : ∀ b : Fin k, ¬ (Fin.natAdd m b < Fin.castAdd k i)` using `fun b h => by`. Apply the tactic sequence `simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] at h <;> omega`. Establish `hc : ∀ x : Fin m, Fin.castAdd k x < Fin.castAdd k i ↔ x < i` using `fun x => by`. Apply the tactic sequence `simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] <;> omega`. Simplify using `only [xJ, LinearMap.comp_apply, LinearMap.add_apply, Pi.add_apply, Om_apply, LinearMap.sum_apply, Finset.sum_apply, pm_apply, iteApp, ite_apply, Pi.zero_apply, lift_apply, curF_apply, Fin.append_left, upd_castAdd, Finset.sum_filter, Fin.sum_univ_add, swap_castAdd, hz, hc, if_fals …`.

Introduce `j`. Use `LinearMap.ext fun f => funext fun J => funext fun I => ?_` and prove the remaining obligations. Establish `hz : ∀ x : Fin m, Fin.castAdd k x < Fin.natAdd m j` using `fun x => by`. Apply the tactic sequence `simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] <;> omega`. Establish `hc : ∀ b : Fin k, Fin.natAdd m b < Fin.natAdd m j ↔ b < j` using `fun b => by`.

Apply the tactic sequence `simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] <;> omega`. Simplify using `only [xJ, LinearMap.comp_apply, LinearMap.add_apply, Pi.add_apply, Om_apply, LinearMap.sum_apply, Finset.sum_apply, pm_apply, iteApp, ite_apply, Pi.zero_apply, curF_apply, tE_apply, Fin.append_right, upd_natAdd, upd_castAdd, Finset.sum_filter, Fin.sum_univ_add, swap_natAdd, swap_ …`. Rewrite using `[Finset.sum_comm (f := fun x p => if I p = x then f (Fin.append (Function.update I p (J j)) (Function.update J j x)) else 0)]`. Simplify using `only [Finset.sum_ite_eq, Finset.mem_univ, if_true, add_assoc]`. Introduce `B`.

Both sides reduce to the same expression. Introduce `i i'`. Use `LinearMap.ext fun f => funext fun J => funext fun I => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, curF_apply, pm_apply, lift_apply, swap_castAdd]`. Introduce `j j'`.

Use `LinearMap.ext fun f => funext fun J => funext fun I => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, curF_apply, pm_apply, swap_natAdd]`.
-/
theorem curry_holds : Curry := by
  intro n M _ _ E m k
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f g h
    funext K
    have := congrFun (congrFun (congrArg (fun x => x) h) (fun j => K (Fin.natAdd m j))) (fun i => K (Fin.castAdd k i))
    simpa only [curF_apply, Fin.append_castAdd_natAdd] using this
  · intro g
    refine ⟨fun K => g (fun j => K (Fin.natAdd m j)) (fun i => K (Fin.castAdd k i)), ?_⟩
    funext J I
    simp only [curF_apply, Fin.append_left, Fin.append_right]
  · intro a b
    refine LinearMap.ext fun f => funext fun J => funext fun I => ?_
    simp only [LinearMap.comp_apply, curF_apply, tE_apply, Pi.add_apply, Finset.sum_apply, ite_apply, Pi.zero_apply,
      Fin.sum_univ_add, Fin.append_left, Fin.append_right, upd_castAdd, upd_natAdd, add_assoc]
  · intro i
    refine LinearMap.ext fun f => funext fun J => funext fun I => ?_
    have hz : ∀ b : Fin k, ¬ (Fin.natAdd m b < Fin.castAdd k i) := fun b h => by
      simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] at h <;> omega
    have hc : ∀ x : Fin m, Fin.castAdd k x < Fin.castAdd k i ↔ x < i := fun x => by
      simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] <;> omega
    simp only [xJ, LinearMap.comp_apply, LinearMap.add_apply, Pi.add_apply, Om_apply, LinearMap.sum_apply,
      Finset.sum_apply, pm_apply, iteApp, ite_apply, Pi.zero_apply, lift_apply, curF_apply, Fin.append_left, upd_castAdd, Finset.sum_filter,
      Fin.sum_univ_add, swap_castAdd, hz, hc, if_false, Finset.sum_const_zero, add_zero]
  · intro j
    refine LinearMap.ext fun f => funext fun J => funext fun I => ?_
    have hz : ∀ x : Fin m, Fin.castAdd k x < Fin.natAdd m j := fun x => by
      simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] <;> omega
    have hc : ∀ b : Fin k, Fin.natAdd m b < Fin.natAdd m j ↔ b < j := fun b => by
      simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] <;> omega
    simp only [xJ, LinearMap.comp_apply, LinearMap.add_apply, Pi.add_apply, Om_apply, LinearMap.sum_apply,
      Finset.sum_apply, pm_apply, iteApp, ite_apply, Pi.zero_apply, curF_apply, tE_apply, Fin.append_right, upd_natAdd, upd_castAdd,
      Finset.sum_filter, Fin.sum_univ_add, swap_natAdd, swap_mixed, hz, hc, if_true, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun x p => if I p = x then
      f (Fin.append (Function.update I p (J j)) (Function.update J j x)) else 0)]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, add_assoc]
  · intro B
    rfl
  · intro i i'
    refine LinearMap.ext fun f => funext fun J => funext fun I => ?_
    simp only [LinearMap.comp_apply, curF_apply, pm_apply, lift_apply, swap_castAdd]
  · intro j j'
    refine LinearMap.ext fun f => funext fun J => funext fun I => ?_
    simp only [LinearMap.comp_apply, curF_apply, pm_apply, swap_natAdd]

end PositivityTheory.Rg.Cz

end

import GroundTheory.AutomorphicForms.StableConjCyclic

/- English proof (translation)
Use `haveI : Infinite E := Infinite.of_injective _ (Nat.cast_injective (R := E))`. Establish `hsep : (LinearMap.charpoly (Matrix.toLinAlgEquiv' γ : Module.End E (Fin n → E))).Separable`. Establish `: (Matrix.toLinAlgEquiv' γ : Module.End E (Fin n → E)) = Matrix.toLin' γ` using `rfl`. Rewrite using `[this, Matrix.charpoly_toLin']`. Conclude with `h`.

Establish `ha' : Commute γ a` using `ha.symm`. Establish `hb' : Commute γ b` using `hb.symm`. Establish `hc` using `GroundTheory.Automorphic.commute_of_commute_of_separable hsep (ha'.map (Matrix.toLinAlgEquiv' (R := E) (n := Fin n))) (hb'.map (Matrix.toLinAlgEquiv' (R := E) (n := Fin n)))`. Apply `(Matrix.toLinAlgEquiv' (R := E) (n := Fin n)).injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul]`.

Conclude with `hc`.
-/
private theorem UpperTheory.commute_of_commute_of_charpoly_separable {E : Type} [Field E] [CharZero E] {n : ℕ}
    (γ a b : Matrix (Fin n) (Fin n) E) (h : γ.charpoly.Separable)
    (ha : a * γ = γ * a) (hb : b * γ = γ * b) : a * b = b * a := by
  haveI : Infinite E := Infinite.of_injective _ (Nat.cast_injective (R := E))
  have hsep : (LinearMap.charpoly (Matrix.toLinAlgEquiv' γ : Module.End E (Fin n → E))).Separable := by
    have : (Matrix.toLinAlgEquiv' γ : Module.End E (Fin n → E)) = Matrix.toLin' γ := rfl
    rw [this, Matrix.charpoly_toLin']
    exact h
  have ha' : Commute γ a := ha.symm
  have hb' : Commute γ b := hb.symm
  have hc := GroundTheory.Automorphic.commute_of_commute_of_separable hsep
    (ha'.map (Matrix.toLinAlgEquiv' (R := E) (n := Fin n)))
    (hb'.map (Matrix.toLinAlgEquiv' (R := E) (n := Fin n)))
  apply (Matrix.toLinAlgEquiv' (R := E) (n := Fin n)).injective
  rw [map_mul, map_mul]
  exact hc

/- English proof (translation)
Introduce `W K _ _ n γ hγ a b ha hb`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j w`. Establish `key` using `UpperTheory.commute_of_commute_of_charpoly_separable ((Pi.evalRingHom K w).mapMatrix (γ : Matrix (Fin n) (Fin n) (∀ w, K w))) ((Pi.evalRingHom K w).mapMatrix (a : Matrix (Fin n) (Fin n) (∀ w, K w))) ((Pi.evalRingHom K w).mapMatrix (b : Matrix (Fin n) (Fin n) (∀ w, K w))) (by rw [ …`. Rewrite `key` using `[← map_mul, ← map_mul]`.

Conclude with `congrFun (congrFun key i) j`.
-/
theorem UpperTheory.generalLinearPi_centralizer_comm_of_charpoly_separable :
    ∀ (W : Type) (K : W → Type) [∀ w, Field (K w)] [∀ w, CharZero (K w)] (n : ℕ) (γ : GL (Fin n) (∀ w, K w)), (γ : Matrix (Fin n) (Fin n) (∀ w, K w)).charpoly.Separable → ∀ a b : GL (Fin n) (∀ w, K w), a * γ = γ * a → b * γ = γ * b → a * b = b * a := by
  intro W K _ _ n γ hγ a b ha hb
  apply Units.ext
  ext i j w
  have key := UpperTheory.commute_of_commute_of_charpoly_separable
    ((Pi.evalRingHom K w).mapMatrix (γ : Matrix (Fin n) (Fin n) (∀ w, K w)))
    ((Pi.evalRingHom K w).mapMatrix (a : Matrix (Fin n) (Fin n) (∀ w, K w)))
    ((Pi.evalRingHom K w).mapMatrix (b : Matrix (Fin n) (Fin n) (∀ w, K w)))
    (by rw [RingHom.mapMatrix_apply, Matrix.charpoly_map]; exact hγ.map)
    (by rw [← map_mul, ← map_mul, ← Units.val_mul, ha, Units.val_mul])
    (by rw [← map_mul, ← map_mul, ← Units.val_mul, hb, Units.val_mul])
  rw [← map_mul, ← map_mul] at key
  exact congrFun (congrFun key i) j

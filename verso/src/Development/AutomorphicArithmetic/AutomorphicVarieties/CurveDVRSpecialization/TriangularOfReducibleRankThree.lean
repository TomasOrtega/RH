import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ValuationRingClearLastRowEntry
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CanonEx

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

/- English proof (translation)
Establish `t10 : T 1 0 = 0` using `hT (by decide)`. Establish `t20 : T 2 0 = 0` using `hT (by decide)`. Establish `t21 : T 2 1 = 0` using `hT (by decide)`. Establish `e' : ∀ b a, T b 0 * m 0 a + T b 1 * m 1 a + T b 2 * m 2 a = m b a * d a` using `fun b a => by`. Use `congrFun (congrFun e b) a` as an intermediate fact.

Rewrite `this` using `[Matrix.mul_diagonal, Matrix.mul_apply, Fin.sum_univ_three]`. Then use the resulting hypothesis. Establish `h2 : ∀ a, a ≠ 2 → m 2 a = 0` using `fun a ha => by`. Use `e' 2 a` as an intermediate fact. Rewrite `this` using `[t20, t21]`. Use `(mul_eq_zero.1 (?_ : (T 2 2 - d a) * m 2 a = 0)).resolve_left (sub_ne_zero.2 (hd a 2 ha))` and prove the remaining obligations.

Take the linear combination `this`. Establish `h1 : m 1 0 = 0`. Use `e' 1 0` as an intermediate fact. Rewrite `this` using `[t10, h2 0 (by decide)]`. Use `(mul_eq_zero.1 (?_ : (T 1 1 - d 0) * m 1 0 = 0)).resolve_left (sub_ne_zero.2 (hd 0 1 (by decide)))` and prove the remaining obligations.

Take the linear combination `this`. Establish `h20` using `h2 0 (by decide)`. Establish `h21` using `h2 1 (by decide)`. Introduce `i j hij`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simpa`.
-/
private theorem go_up {K : Type} [Field K] (T m : Matrix (Fin 3) (Fin 3) K) (d : Fin 3 → K)
    (hT : T.BlockTriangular id) (hd : ∀ a b, a ≠ b → T b b ≠ d a) (e : T * m = m * Matrix.diagonal d) :
    m.BlockTriangular id := by
  have t10 : T 1 0 = 0 := hT (by decide)
  have t20 : T 2 0 = 0 := hT (by decide)
  have t21 : T 2 1 = 0 := hT (by decide)
  have e' : ∀ b a, T b 0 * m 0 a + T b 1 * m 1 a + T b 2 * m 2 a = m b a * d a := fun b a => by
    have := congrFun (congrFun e b) a
    rwa [Matrix.mul_diagonal, Matrix.mul_apply, Fin.sum_univ_three] at this
  have h2 : ∀ a, a ≠ 2 → m 2 a = 0 := fun a ha => by
    have := e' 2 a
    rw [t20, t21] at this
    refine (mul_eq_zero.1 (?_ : (T 2 2 - d a) * m 2 a = 0)).resolve_left (sub_ne_zero.2 (hd a 2 ha))
    linear_combination this
  have h1 : m 1 0 = 0 := by
    have := e' 1 0
    rw [t10, h2 0 (by decide)] at this
    refine (mul_eq_zero.1 (?_ : (T 1 1 - d 0) * m 1 0 = 0)).resolve_left (sub_ne_zero.2 (hd 0 1 (by decide)))
    linear_combination this
  have h20 := h2 0 (by decide)
  have h21 := h2 1 (by decide)
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simpa

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single a]`. Introduce `b _ hb`. Break down `lt_or_gt_of_ne hb with h | h` into its components or cases. Rewrite using `[hX h, zero_mul]`. Rewrite using `[hY h, mul_zero]`.

Simplify using the standard rewrite rules.
-/
private theorem go_diag {C : Type} [CommRing C] {X Y : Matrix (Fin 3) (Fin 3) C} (hX : X.BlockTriangular id)
    (hY : Y.BlockTriangular id) (a : Fin 3) : (X * Y) a a = X a a * Y a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h | h
    · rw [hX h, zero_mul]
    · rw [hY h, mul_zero]
  · simp

/- English proof (translation)
Establish `hi : (m⁻¹).val.BlockTriangular id`. Rewrite using `[Matrix.coe_units_inv]`. Use `haveI := m.invertible`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hm`. Use `⟨(hi.mul hY).mul hm, fun a => ?_⟩` and prove the remaining obligations.

Rewrite using `[go_diag (hi.mul hY) hm, go_diag hi hY, mul_right_comm, ← go_diag hi hm, Units.inv_mul, Matrix.one_apply_eq, one_mul]`.
-/
private theorem go_conj {K : Type} [Field K] (m : GL (Fin 3) K) (hm : m.val.BlockTriangular id)
    (Y : Matrix (Fin 3) (Fin 3) K) (hY : Y.BlockTriangular id) :
    ((m⁻¹).val * Y * m.val).BlockTriangular id ∧ ∀ a, ((m⁻¹).val * Y * m.val) a a = Y a a := by
  have hi : (m⁻¹).val.BlockTriangular id := by
    rw [Matrix.coe_units_inv]
    haveI := m.invertible
    exact Matrix.blockTriangular_inv_of_blockTriangular hm
  refine ⟨(hi.mul hY).mul hm, fun a => ?_⟩
  rw [go_diag (hi.mul hY) hm, go_diag hi hY, mul_right_comm, ← go_diag hi hm, Units.inv_mul, Matrix.one_apply_eq,
    one_mul]

/- English proof (translation)
Simplify using `[conjBy, GG.mat, hg]`.
-/
private theorem go_mat {D C : Type} [Group D] [CommRing C] (r : D →* GG 3 C) (h : GL (Fin 3) C) (g : D)
    (hg : (r g).right = 1) : (conjBy h⁻¹ r g).mat = (h⁻¹).val * (r g).mat * h.val := by
  simp [conjBy, GG.mat, hg]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem diagonal_character_rep_matrix {O D : Type} [CommRing O] [Group D] (η : D →* ℤˣ) (Ψ : D →* Oˣ) (g : D) :
    (r0 η Ψ g).mat = Matrix.diagonal fun a => UnitaryThreeInertia.psi Ψ a g := rfl

/- English proof (translation)
Establish `e0 : UnitaryThreeInertia.psi Ψ 0 x = Ψ x` using `by simp [UnitaryThreeInertia.psi, wt1]`. Establish `e1 : UnitaryThreeInertia.psi Ψ 1 x = 1` using `by simp [UnitaryThreeInertia.psi, wt1]`. Establish `e2 : UnitaryThreeInertia.psi Ψ 2 x = ((Ψ x)⁻¹ : Oˣ)` using `by simp [UnitaryThreeInertia.psi, wt1]`. Generalize the expression as in `Ψ x = t at *`. Establish `ht : (t : O) * (t⁻¹ : Oˣ) = 1` using `Units.mul_inv t`.

Establish `h01 : IsUnit (UnitaryThreeInertia.psi Ψ 0 x - UnitaryThreeInertia.psi Ψ 1 x)`. Rewrite using `[e0, e1]`. Conclude with `isUnit_of_mul_isUnit_left (y := (t : O) + 1) (by convert hu using 1; ring)`. Establish `h02 : IsUnit (UnitaryThreeInertia.psi Ψ 0 x - UnitaryThreeInertia.psi Ψ 2 x)`. Rewrite using `[e0, e2]`.

Conclude with `isUnit_of_mul_isUnit_left (y := (t : O)) (by convert hu using 1; linear_combination -ht)`. Establish `h12 : IsUnit (UnitaryThreeInertia.psi Ψ 1 x - UnitaryThreeInertia.psi Ψ 2 x)`. Rewrite using `[e1, e2]`. Conclude with `isUnit_of_mul_isUnit_left (y := (t : O) * (t + 1)) (by convert hu using 1; linear_combination (-(t : O) - 1) * ht)`. Establish `hs : ∀ {u v : O}, IsUnit (u - v) → IsUnit (v - u)` using `fun h => by rw [← neg_sub]; exact h.neg`.

Apply the tactic sequence `fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | assumption | exact hs (by assumption)`.
-/
private theorem go_unit {O D : Type} [CommRing O] [Group D] (Ψ : D →* Oˣ) (x : D)
    (hu : IsUnit ((Ψ x : O) ^ 2 - 1)) (a b : Fin 3) (hab : a ≠ b) : IsUnit (UnitaryThreeInertia.psi Ψ a x - UnitaryThreeInertia.psi Ψ b x) := by
  have e0 : UnitaryThreeInertia.psi Ψ 0 x = Ψ x := by simp [UnitaryThreeInertia.psi, wt1]
  have e1 : UnitaryThreeInertia.psi Ψ 1 x = 1 := by simp [UnitaryThreeInertia.psi, wt1]
  have e2 : UnitaryThreeInertia.psi Ψ 2 x = ((Ψ x)⁻¹ : Oˣ) := by simp [UnitaryThreeInertia.psi, wt1]
  generalize Ψ x = t at *
  have ht : (t : O) * (t⁻¹ : Oˣ) = 1 := Units.mul_inv t
  have h01 : IsUnit (UnitaryThreeInertia.psi Ψ 0 x - UnitaryThreeInertia.psi Ψ 1 x) := by
    rw [e0, e1]
    exact isUnit_of_mul_isUnit_left (y := (t : O) + 1) (by convert hu using 1; ring)
  have h02 : IsUnit (UnitaryThreeInertia.psi Ψ 0 x - UnitaryThreeInertia.psi Ψ 2 x) := by
    rw [e0, e2]
    exact isUnit_of_mul_isUnit_left (y := (t : O)) (by convert hu using 1; linear_combination -ht)
  have h12 : IsUnit (UnitaryThreeInertia.psi Ψ 1 x - UnitaryThreeInertia.psi Ψ 2 x) := by
    rw [e1, e2]
    exact isUnit_of_mul_isUnit_left (y := (t : O) * (t + 1))
      (by convert hu using 1; linear_combination (-(t : O) - 1) * ht)
  have hs : ∀ {u v : O}, IsUnit (u - v) → IsUnit (v - u) := fun h => by rw [← neg_sub]; exact h.neg
  fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | assumption | exact hs (by assumption)

/- English proof (translation)
Assume the negation of the conclusion as `hv`. Establish `h1 : v ∈ maximalIdeal A` using `hv`. Establish `h2 : u ∈ maximalIdeal A` using `by simpa using Ideal.sub_mem _ h1 h`. Conclude with `h2 hu`.
-/
private theorem go_uadd {A : Type} [CommRing A] [IsLocalRing A] {u v : A} (hu : IsUnit u) (h : v - u ∈ maximalIdeal A) :
    IsUnit v := by
  by_contra hv
  have h1 : v ∈ maximalIdeal A := hv
  have h2 : u ∈ maximalIdeal A := by simpa using Ideal.sub_mem _ h1 h
  exact h2 hu

/- English proof (translation)
Establish `hw : ∀ a b : Fin 3, wt a b < 0 ↔ b < a` using `by decide`. Establish `hd : ∀ a, (r x).mat a a - algebraMap O A (UnitaryThreeInertia.psi Ψ a x) ∈ maximalIdeal A` using `fun a => by`. Simplify `hr.red x a a` using `[diagonal_character_rep_matrix]`. Establish `ho : ∀ a b, a ≠ b → (r x).mat a b ∈ maximalIdeal A` using `fun a b hab => by`. Simplify `hr.red x a b` using `[diagonal_character_rep_matrix, hab]`.

Establish `hU` using `fun a b hab => (go_unit Ψ x hu a b hab).map (algebraMap O A)`. Take `⟨h, h1, h2, h3⟩` from `UnitaryThreeInertia.exists_canon (r x).mat (fun a b hab => go_uadd (hU a b hab) (by`. Use `Ideal.sub_mem _ (hd a) (hd b) using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_sub]`. Use the proof step `ring)) ho`.

Take `⟨d, hdd⟩ : ∃ d, Matrix.diagonal d = (h⁻¹).val * (r x).mat * h.val` from `⟨_, h3.diagonal_diag⟩`. Establish `hX : (r x).mat * h.val = h.val * Matrix.diagonal d`. Rewrite using `[hdd, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]`. Establish `hdm : ∀ a, d a - (r x).mat a a ∈ maximalIdeal A` using `fun a => by`. Establish `e` using `congrFun (congrFun hX a) a`.

Rewrite `e` using `[Matrix.mul_diagonal, h2, one_mul, Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ a), h2, mul_one]`. Rewrite using `[← e, add_sub_cancel_left]`. Conclude with `Ideal.sum_mem _ fun b hb => Ideal.mul_mem_right _ _ (ho a b (Finset.ne_of_mem_erase hb).symm)`. Set `h' : GL (Fin 3) K` to `Matrix.GeneralLinearGroup.map (j : A →+* K) h`. Establish `hm : ∀ g, η g = 1 → (push j r g).right = 1` using `fun g hg => (hr.mult g).trans hg`.

Establish `hT : ∀ g, η g = 1 → ((k⁻¹).val * (push j r g).mat * k.val).BlockTriangular id` using `fun g hg a b hab => by`. Rewrite using `[← go_mat _ _ _ (hm g hg)]`. Conclude with `hk.tri g hg a b ((hw a b).2 hab)`. Establish `hI : ∀ g ∈ I, η g = 1 → ∀ a, ((k⁻¹).val * (push j r g).mat * k.val) a a = algebraMap O K (UnitaryThreeInertia.psi Ψ a g)` using `fun g hg hg' a => by`. Rewrite using `[← go_mat _ _ _ (hm g hg')]`.

Conclude with `hk.ine g hg hg' a`. Establish `hup : (k⁻¹ * h').val.BlockTriangular id`. Use `go_up _ _ (fun a => j (d a)) (hT x hη) (fun a b hab => ?_) ?_` and prove the remaining obligations. Rewrite using `[hI x hx hη, ← j.commutes, ← sub_ne_zero, ← map_sub]`. Use `((go_uadd (hU b a hab.symm) ?_).map j).ne_zero` and prove the remaining obligations.

Use `(maximalIdeal A).neg_mem (Ideal.add_mem _ (hdm a) (hd a)) using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree. Establish `e` using `congrArg (fun M => M.map (j : A →+* K)) hX`. Simplify using `only [Matrix.map_mul, Matrix.diagonal_map (map_zero (j : A →+* K))] at e`.

Rewrite using `[Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc k.val, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc]`. Conclude with `congrArg _ e`. Establish `key : ∀ g, η g = 1 → ∀ a b, j ((conjBy h⁻¹ r g).mat a b) = (((k⁻¹ * h')⁻¹).val * ((k⁻¹).val * (push j r g).mat * k.val) * (k⁻¹ * h').val) a b` using `fun g hg a b => by`. Establish `e : ((k⁻¹ * h')⁻¹).val * ((k⁻¹).val * (push j r g).mat * k.val) * (k⁻¹ * h').val = (h'⁻¹).val * (push j r g).mat * h'.val`. Simplify using `only [_root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left]`.

Rewrite using `[e, go_mat _ _ _ ((hr.mult g).trans hg), ← map_inv]`. Use `show ((h⁻¹).val * (r g).mat * h.val).map (j : A →+* K) a b = _`. Rewrite using `[Matrix.map_mul, Matrix.map_mul]`. Both sides reduce to the same expression. Use `⟨h, h1, fun g hg a b hab => hj ?_, fun g hg hg' a => hj ?_⟩` and prove the remaining obligations.

Rewrite using `[key g hg, map_zero]`. Conclude with `(go_conj _ hup _ (hT g hg)).1 ((hw a b).1 hab)`. Rewrite using `[key g hg', (go_conj _ hup _ (hT g hg')).2, hI g hg hg', j.commutes]`.
-/
private theorem triangular_of_reducible_rank_three {O A K D : Type} [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [Algebra O A] [Field K] [Algebra O K] [Group D]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (r : D →* GG 3 A) (hr : UnitaryThreeInertia.Red η Ψ r) (j : A →ₐ[O] K)
    (hj : Function.Injective j) (x : D) (hx : x ∈ I) (hη : η x = 1) (hu : IsUnit ((Ψ x : O) ^ 2 - 1))
    (k : GL (Fin 3) K) (hk : UnitaryThreeInertia.TriIn η Ψ I (push j r) k) : UnitaryThreeInertia.CondT η Ψ I r := by
  have hw : ∀ a b : Fin 3, wt a b < 0 ↔ b < a := by decide
  have hd : ∀ a, (r x).mat a a - algebraMap O A (UnitaryThreeInertia.psi Ψ a x) ∈ maximalIdeal A := fun a => by
    simpa [diagonal_character_rep_matrix] using hr.red x a a
  have ho : ∀ a b, a ≠ b → (r x).mat a b ∈ maximalIdeal A := fun a b hab => by
    simpa [diagonal_character_rep_matrix, hab] using hr.red x a b
  have hU := fun a b hab => (go_unit Ψ x hu a b hab).map (algebraMap O A)
  obtain ⟨h, h1, h2, h3⟩ := UnitaryThreeInertia.exists_canon (r x).mat (fun a b hab => go_uadd (hU a b hab) (by
    convert Ideal.sub_mem _ (hd a) (hd b) using 1
    rw [map_sub]; ring)) ho
  obtain ⟨d, hdd⟩ : ∃ d, Matrix.diagonal d = (h⁻¹).val * (r x).mat * h.val := ⟨_, h3.diagonal_diag⟩
  have hX : (r x).mat * h.val = h.val * Matrix.diagonal d := by
    rw [hdd, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hdm : ∀ a, d a - (r x).mat a a ∈ maximalIdeal A := fun a => by
    have e := congrFun (congrFun hX a) a
    rw [Matrix.mul_diagonal, h2, one_mul, Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ a), h2,
      mul_one] at e
    rw [← e, add_sub_cancel_left]
    exact Ideal.sum_mem _ fun b hb => Ideal.mul_mem_right _ _ (ho a b (Finset.ne_of_mem_erase hb).symm)
  let h' : GL (Fin 3) K := Matrix.GeneralLinearGroup.map (j : A →+* K) h
  have hm : ∀ g, η g = 1 → (push j r g).right = 1 := fun g hg => (hr.mult g).trans hg
  have hT : ∀ g, η g = 1 → ((k⁻¹).val * (push j r g).mat * k.val).BlockTriangular id := fun g hg a b hab => by
    rw [← go_mat _ _ _ (hm g hg)]
    exact hk.tri g hg a b ((hw a b).2 hab)
  have hI : ∀ g ∈ I, η g = 1 → ∀ a, ((k⁻¹).val * (push j r g).mat * k.val) a a = algebraMap O K (UnitaryThreeInertia.psi Ψ a g) :=
    fun g hg hg' a => by
      rw [← go_mat _ _ _ (hm g hg')]
      exact hk.ine g hg hg' a
  have hup : (k⁻¹ * h').val.BlockTriangular id := by
    refine go_up _ _ (fun a => j (d a)) (hT x hη) (fun a b hab => ?_) ?_
    · rw [hI x hx hη, ← j.commutes, ← sub_ne_zero, ← map_sub]
      refine ((go_uadd (hU b a hab.symm) ?_).map j).ne_zero
      convert (maximalIdeal A).neg_mem (Ideal.add_mem _ (hdm a) (hd a)) using 1
      rw [map_sub]; ring
    · have e := congrArg (fun M => M.map (j : A →+* K)) hX
      simp only [Matrix.map_mul, Matrix.diagonal_map (map_zero (j : A →+* K))] at e
      rw [Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc k.val, Units.mul_inv, Matrix.one_mul,
        Matrix.mul_assoc]
      exact congrArg _ e
  have key : ∀ g, η g = 1 → ∀ a b, j ((conjBy h⁻¹ r g).mat a b) =
      (((k⁻¹ * h')⁻¹).val * ((k⁻¹).val * (push j r g).mat * k.val) * (k⁻¹ * h').val) a b := fun g hg a b => by
    have e : ((k⁻¹ * h')⁻¹).val * ((k⁻¹).val * (push j r g).mat * k.val) * (k⁻¹ * h').val =
        (h'⁻¹).val * (push j r g).mat * h'.val := by
      simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left]
    rw [e, go_mat _ _ _ ((hr.mult g).trans hg), ← map_inv]
    show ((h⁻¹).val * (r g).mat * h.val).map (j : A →+* K) a b = _
    rw [Matrix.map_mul, Matrix.map_mul]
    rfl
  refine ⟨h, h1, fun g hg a b hab => hj ?_, fun g hg hg' a => hj ?_⟩
  · rw [key g hg, map_zero]
    exact (go_conj _ hup _ (hT g hg)).1 ((hw a b).1 hab)
  · rw [key g hg', (go_conj _ hup _ (hT g hg')).2, hI g hg hg', j.commutes]

/- English proof (translation)
Substitute `hD hI` using the available equality. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, σ, rfl⟩ hg`. Conclude with `hk.tri σ hg`. Introduce and unpack `⟨s, hs⟩ ⟨σ, hσ, e⟩ hg`.

Take `rfl : ι σ = s` from `e`. Conclude with `hk.ine σ hσ hg`.
-/
private theorem go_tr {O A H G : Type} [CommRing O] [CommRing A] [Algebra O A] [Group H] [Group G]
    (η : G →* ℤˣ) (Ψ : G →* Oˣ) (r : G →* GG 3 A) (ι : H →* G) (J : Subgroup H) (Dc In : Subgroup G)
    (hD : ι.range = Dc) (hI : J.map ι = In) (k : GL (Fin 3) A)
    (hk : UnitaryThreeInertia.TriIn (η.comp ι) (Ψ.comp ι) J (r.comp ι) k) :
    UnitaryThreeInertia.TriIn (η.comp Dc.subtype) (Ψ.comp Dc.subtype) (In.subgroupOf Dc) (r.comp Dc.subtype) k := by
  subst hD hI
  constructor
  · rintro ⟨_, σ, rfl⟩ hg
    exact hk.tri σ hg
  · rintro ⟨s, hs⟩ ⟨σ, hσ, e⟩ hg
    obtain rfl : ι σ = s := e
    exact hk.ine σ hσ hg

/- English proof (translation)
Simplify using `only [GG.mat, unitaryThreeReflection_left, tor_val]`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Rewrite using `[Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]`. Conclude with `(congrArg Units.val (map_zpow (Units.map φ.toMonoidHom) (Ψ g) (wt1 a))).symm`.

Rewrite using `[Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h, map_zero]`.
-/
private theorem go_r0map {G A B : Type} [Group G] [CommRing A] [CommRing B] (φ : A →+* B) (η : G →* ℤˣ) (Ψ : G →* Aˣ)
    (g : G) (a b : Fin 3) :
    (r0 η ((Units.map φ.toMonoidHom).comp Ψ) g).mat a b = φ ((r0 η Ψ g).mat a b) := by
  simp only [GG.mat, unitaryThreeReflection_left, tor_val]
  by_cases h : a = b
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    exact (congrArg Units.val (map_zpow (Units.map φ.toMonoidHom) (Ψ g) (wt1 a))).symm
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h, map_zero]

/- English proof (translation)
Establish `hm : ∀ y ∈ maximalIdeal R, f y ∈ maximalIdeal A` using `fun y hy hu => hy (hf.map_nonunit y hu)`. Use `⟨⟨fun g => r.hasMult g, fun g a b => ?_⟩, fun n => ?_⟩` and prove the remaining obligations. Use `show f ((r.hom g).mat a b) - algebraMap O A ((r0 η Ψ g).mat a b) ∈ _`. Rewrite using `[← f.commutes, ← map_sub]`. Use `hm _ ((Alg.res_eq_zero_iff O R _).1 ?_)` and prove the remaining obligations.

Establish `h2 : Alg.res O R ((r.hom g).mat a b) = (rbar O η Ψ g).mat a b` using `congrArg (fun x : GG 3 (ResidueField O) => x.mat a b) (r.red g)`. Establish `h3 : (rbar O η Ψ g).mat a b = residue O ((r0 η Ψ g).mat a b)` using `go_r0map _ _ _ _ _ _`. Rewrite using `[map_sub, AlgHom.commutes, h2, h3]`. Conclude with `sub_self _`. Establish `hle : maximalIdeal R ^ n ≤ (maximalIdeal A ^ n).comap (f : R →+* A)` using `le_trans (Ideal.pow_right_mono (fun y hy => hm y hy) n) (Ideal.le_comap_pow _ n)`.

Use `(IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_` and prove the remaining obligations. Establish `h` using `fun p : Fin 3 × Fin 3 => ((r.cont p.1 p.2 n).comp (Ideal.quotientMap _ (f : R →+* A) hle)).eventually_eq g`. Use `filter_upwards [Filter.eventually_all.2 h] with g' hg'`. Conclude with `Matrix.ext fun a b => hg' (a, b)`.
-/
private theorem go_push {O R A Γ : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Alg.IsCO O R]
    [CommRing A] [IsLocalRing A] [Algebra O A] [Group Γ] [TopologicalSpace Γ] {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ}
    (r : GLift O η Ψ R) (f : R →ₐ[O] A) (hf : IsLocalHom f) :
    UnitaryThreeInertia.Red η Ψ (push f r.hom) ∧ UnitaryThreeInertia.AdicCont (maximalIdeal A) (push f r.hom) := by
  have hm : ∀ y ∈ maximalIdeal R, f y ∈ maximalIdeal A := fun y hy hu => hy (hf.map_nonunit y hu)
  refine ⟨⟨fun g => r.hasMult g, fun g a b => ?_⟩, fun n => ?_⟩
  · show f ((r.hom g).mat a b) - algebraMap O A ((r0 η Ψ g).mat a b) ∈ _
    rw [← f.commutes, ← map_sub]
    refine hm _ ((Alg.res_eq_zero_iff O R _).1 ?_)
    have h2 : Alg.res O R ((r.hom g).mat a b) = (rbar O η Ψ g).mat a b :=
      congrArg (fun x : GG 3 (ResidueField O) => x.mat a b) (r.red g)
    have h3 : (rbar O η Ψ g).mat a b = residue O ((r0 η Ψ g).mat a b) := go_r0map _ _ _ _ _ _
    rw [map_sub, AlgHom.commutes, h2, h3]
    exact sub_self _
  · have hle : maximalIdeal R ^ n ≤ (maximalIdeal A ^ n).comap (f : R →+* A) :=
      le_trans (Ideal.pow_right_mono (fun y hy => hm y hy) n) (Ideal.le_comap_pow _ n)
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
    have h := fun p : Fin 3 × Fin 3 =>
      ((r.cont p.1 p.2 n).comp (Ideal.quotientMap _ (f : R →+* A) hle)).eventually_eq g
    filter_upwards [Filter.eventually_all.2 h] with g' hg'
    exact Matrix.ext fun a b => hg' (a, b)

/- English proof (translation)
Introduce `hP Ω _ _ _ K _ _ _ l _ c N _ e ψ D g₁ _ U S B hB A _ _ _ _ _ f hf`. Establish `hid : S.r.map (AlgHom.id c.O S.R) = S.r` using `GLift.ext rfl`. Establish `h0` using `(S.rep S.R).1 (AlgHom.id c.O S.R)`. Rewrite `h0` using `[hid]`. Take `⟨hn, hk, φ, hφ, hI⟩` from `h0`.

Take `⟨hred, hcont⟩` from `go_push S.r f hf`. Take `⟨B₀, hl, hD, hIn, -, hB₀, -⟩` from `dat_loc D`. Take `rfl : B = B₀` from `ValuationSubring.ext _ _ fun x => (hB x).trans (hB₀ x).symm`. Use `⟨hred, hcont, ⟨?_, ?_, ?_⟩, fun B' hB' s hs hη hΨ => ?_, ?_⟩` and prove the remaining obligations. Use `show (S.r.hom D.cc).mat.map (f : S.R →+* A) = 1`.

Rewrite using `[hn.atc, Matrix.map_one _ (map_zero _) (map_one _)]`. Use `congrArg f hn.z12` as an intermediate fact. Rewrite `this` using `[map_zero, zmat, Matrix.sub_apply, map_sub]`. Conclude with `this`. Use `congrArg f hn.z21` as an intermediate fact.

Rewrite `this` using `[map_zero, zmat, Matrix.sub_apply, map_sub]`. Conclude with `this`. Use `show GG.map (f : S.R →+* A) (S.r.hom s) = 1`. Rewrite using `[hk s ⟨B', hB', hs, ?_⟩, map_one]`. Use `SemidirectProduct.ext ?_ hη` and prove the remaining obligations.

Use `show tor _ (Units.map _ (D.Ψ s)) = 1`. Rewrite using `[hΨ, map_one, map_one]`. Take `⟨hη, x, hx, hu⟩` from `(dat_facts D).2.2.2.2.2.2.2.2.2.2 B hl`. Set `j₀ : A →ₐ[c.O] FractionRing A` to `IsScalarTower.toAlgHom c.O A (FractionRing A)`. Establish `h1 : (U.r.map φ).hom = S.r.hom.comp D.ι` using `congrArg GLift.hom hφ`.

Take `⟨K', _, _, _, _, _, k, hk'⟩` from `@Loc.lemma2c hP l _ c.O _ _ c.dvr _ _ c.fin (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1 D.loc U (FractionRing A) _ _ ((push j₀ (push f S.r.hom)).comp D.ι) ⟨j₀.comp (f.comp φ), by`. Use `MonoidHom.ext fun g => ?_` and prove the remaining obligations. Use `show GG.map (j₀ : A →+* FractionRing A) (GG.map (f : S.R →+* A) ((U.r.map φ).hom g)) = _`. Rewrite using `[h1]`. Use the proof step `rfl, fun y hy => by`.

Establish `: φ y = 0` using `hI hy`. Use `show j₀ (f (φ y)) = 0`. Rewrite using `[this, map_zero, map_zero]⟩`. Set `j : A →ₐ[c.O] K'` to `(IsScalarTower.toAlgHom c.O (FractionRing A) K').comp j₀`. Establish `hj : Function.Injective j` using `(algebraMap (FractionRing A) K').injective.comp (IsFractionRing.injective A (FractionRing A))`.

Conclude with `triangular_of_reducible_rank_three _ _ _ _ ⟨fun g => hred.mult _, fun g => hred.red _⟩ j hj ⟨x, hx.1⟩ hx (hη hx) hu k (go_tr D.η D.Ψ (push j (push f S.r.hom)) D.ι (Loc.Iq l) _ _ hD hIn k hk')`.
-/
theorem UpperTheory.V.Pr.ordPt_of_gd :
    Loc.LocalPublishedTheorems → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) (g₁ : G ℚ Ω), D.Marked g₁ → ∀ (U : D.ULoc) (S : D.Ring U g₁),
    ∀ (B : ValuationSubring Ω), (∀ x, x ∈ B ↔ ‖D.j x‖ ≤ 1) → ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A] [Algebra c.O A] (f : S.R →ₐ[c.O] A), IsLocalHom f →
      OrdPt l D.η D.Ψ D.cc g₁ B (U3.push f S.r.hom) := by
  intro hP Ω _ _ _ K _ _ _ l _ c N _ e ψ D g₁ _ U S B hB A _ _ _ _ _ f hf
  have hid : S.r.map (AlgHom.id c.O S.R) = S.r := GLift.ext rfl
  have h0 := (S.rep S.R).1 (AlgHom.id c.O S.R)
  rw [hid] at h0
  obtain ⟨hn, hk, φ, hφ, hI⟩ := h0
  obtain ⟨hred, hcont⟩ := go_push S.r f hf
  obtain ⟨B₀, hl, hD, hIn, -, hB₀, -⟩ := dat_loc D
  obtain rfl : B = B₀ := ValuationSubring.ext _ _ fun x => (hB x).trans (hB₀ x).symm
  refine ⟨hred, hcont, ⟨?_, ?_, ?_⟩, fun B' hB' s hs hη hΨ => ?_, ?_⟩
  · show (S.r.hom D.cc).mat.map (f : S.R →+* A) = 1
    rw [hn.atc, Matrix.map_one _ (map_zero _) (map_one _)]
  · have := congrArg f hn.z12
    rw [map_zero, zmat, Matrix.sub_apply, map_sub] at this
    exact this
  · have := congrArg f hn.z21
    rw [map_zero, zmat, Matrix.sub_apply, map_sub] at this
    exact this
  · show GG.map (f : S.R →+* A) (S.r.hom s) = 1
    rw [hk s ⟨B', hB', hs, ?_⟩, map_one]
    refine SemidirectProduct.ext ?_ hη
    show tor _ (Units.map _ (D.Ψ s)) = 1
    rw [hΨ, map_one, map_one]
  · obtain ⟨hη, x, hx, hu⟩ := (dat_facts D).2.2.2.2.2.2.2.2.2.2 B hl
    let j₀ : A →ₐ[c.O] FractionRing A := IsScalarTower.toAlgHom c.O A (FractionRing A)
    have h1 : (U.r.map φ).hom = S.r.hom.comp D.ι := congrArg GLift.hom hφ
    obtain ⟨K', _, _, _, _, _, k, hk'⟩ := @Loc.lemma2c hP l _ c.O _ _ c.dvr _ _ c.fin
      (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1 D.loc U (FractionRing A) _ _
      ((push j₀ (push f S.r.hom)).comp D.ι) ⟨j₀.comp (f.comp φ), by
        refine MonoidHom.ext fun g => ?_
        show GG.map (j₀ : A →+* FractionRing A) (GG.map (f : S.R →+* A) ((U.r.map φ).hom g)) = _
        rw [h1]
        rfl, fun y hy => by
        have : φ y = 0 := hI hy
        show j₀ (f (φ y)) = 0
        rw [this, map_zero, map_zero]⟩
    let j : A →ₐ[c.O] K' := (IsScalarTower.toAlgHom c.O (FractionRing A) K').comp j₀
    have hj : Function.Injective j :=
      (algebraMap (FractionRing A) K').injective.comp (IsFractionRing.injective A (FractionRing A))
    exact triangular_of_reducible_rank_three _ _ _ _ ⟨fun g => hred.mult _, fun g => hred.red _⟩ j hj ⟨x, hx.1⟩ hx (hη hx) hu k
      (go_tr D.η D.Ψ (push j (push f S.r.hom)) D.ι (Loc.Iq l) _ _ hD hIn k hk')

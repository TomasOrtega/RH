import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section SlopeTestRemainingChoices

variable {O : Type} [CommRing O] [IsLocalRing O] {C : Type} [CommRing C] [Algebra O C]
  {K : Ideal C} (u : K →ₗ[O] ResidueField O)

/- English proof (translation)
Rewrite using `[evK_of_mem u hx, evK_of_mem u hy, evK_of_mem u (K.add_mem hx hy), ← map_add]`. Both sides reduce to the same expression.
-/
private theorem evk_add {x y : C} (hx : x ∈ K) (hy : y ∈ K) :
    evK K u (x + y) = evK K u x + evK K u y := by
  rw [evK_of_mem u hx, evK_of_mem u hy, evK_of_mem u (K.add_mem hx hy), ← map_add]
  rfl

/- English proof (translation)
Rewrite using `[evK_of_mem u hx, evK_of_mem u hy, evK_of_mem u (K.sub_mem hx hy), ← map_sub]`. Both sides reduce to the same expression.
-/
private theorem evk_sub {x y : C} (hx : x ∈ K) (hy : y ∈ K) :
    evK K u (x - y) = evK K u x - evK K u y := by
  rw [evK_of_mem u hx, evK_of_mem u hy, evK_of_mem u (K.sub_mem hx hy), ← map_sub]
  rfl

/- English proof (translation)
Rewrite using `[evK_of_mem u hx, evK_of_mem u (K.neg_mem hx), ← map_neg]`. Both sides reduce to the same expression.
-/
private theorem evk_neg {x : C} (hx : x ∈ K) : evK K u (-x) = - evK K u x := by
  rw [evK_of_mem u hx, evK_of_mem u (K.neg_mem hx), ← map_neg]
  rfl

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Rewrite using `[Finset.sum_empty, Finset.sum_empty, evK_of_mem u K.zero_mem]`. Conclude with `map_zero u`. Consider the case `insert a s ha ih`.

Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, evk_add u (hf a) (K.sum_mem fun i _ => hf i), ih]`.
-/
private theorem evk_sum {ι : Type} (s : Finset ι) (f : ι → C) (hf : ∀ i, f i ∈ K) :
    evK K u (∑ i ∈ s, f i) = ∑ i ∈ s, evK K u (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, evK_of_mem u K.zero_mem]
    exact map_zero u
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, evk_add u (hf a) (K.sum_mem fun i _ => hf i), ih]

/- English proof (translation)
Take `⟨b, hb⟩` from `IsCO.res_surj (O := O) a`. Establish `h0 : (a - algebraMap O C b) * x = 0`. Use `Ideal.mul_mem_mul hb hx` as an intermediate fact. Rewrite `this` using `[hK, Ideal.mem_bot]`. Then use the resulting hypothesis. Establish `h1 : res O C a = algebraMap O _ b`.

Use `(res_eq_zero_iff O C _).2 hb` as an intermediate fact. Rewrite `this` using `[map_sub, AlgHom.commutes, sub_eq_zero]`. Then use the resulting hypothesis. Rewrite using `[evK_of_mem u hx, evK_of_mem u (K.mul_mem_left a hx), h1, ← Algebra.smul_def, ← map_smul]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show a * x = b • x`. Rewrite using `[Algebra.smul_def, ← sub_eq_zero, ← sub_mul, h0]`.
-/
private theorem evk_mul [IsCO O C] (hK : maximalIdeal C * K = ⊥) (a : C) {x : C} (hx : x ∈ K) :
    evK K u (a * x) = res O C a * evK K u x := by
  obtain ⟨b, hb⟩ := IsCO.res_surj (O := O) a
  have h0 : (a - algebraMap O C b) * x = 0 := by
    have := Ideal.mul_mem_mul hb hx
    rwa [hK, Ideal.mem_bot] at this
  have h1 : res O C a = algebraMap O _ b := by
    have := (res_eq_zero_iff O C _).2 hb
    rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
  rw [evK_of_mem u hx, evK_of_mem u (K.mul_mem_left a hx), h1, ← Algebra.smul_def, ← map_smul]
  congr 1
  apply Subtype.ext
  show a * x = b • x
  rw [Algebra.smul_def, ← sub_eq_zero, ← sub_mul, h0]

variable {n : ℕ}

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Conclude with `K.sum_mem fun k _ => K.mul_mem_left _ (hZ k j)`.
-/
private theorem mem_left {Z : Matrix (Fin n) (Fin n) C} (hZ : ∀ i j, Z i j ∈ K)
    (A : Matrix (Fin n) (Fin n) C) (i j : Fin n) : (A * Z) i j ∈ K := by
  rw [Matrix.mul_apply]
  exact K.sum_mem fun k _ => K.mul_mem_left _ (hZ k j)

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Conclude with `K.sum_mem fun k _ => K.mul_mem_right _ (hZ i k)`.
-/
private theorem mem_right {Z : Matrix (Fin n) (Fin n) C} (hZ : ∀ i j, Z i j ∈ K)
    (A : Matrix (Fin n) (Fin n) C) (i j : Fin n) : (Z * A) i j ∈ K := by
  rw [Matrix.mul_apply]
  exact K.sum_mem fun k _ => K.mul_mem_right _ (hZ i k)

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, Matrix.mul_apply, Matrix.mul_apply, evk_sum u _ _ fun k => K.mul_mem_left _ (hZ k j)]`. Conclude with `Finset.sum_congr rfl fun k _ => evk_mul u hK _ (hZ k j)`.
-/
private theorem map_left [IsCO O C] (hK : maximalIdeal C * K = ⊥) {Z : Matrix (Fin n) (Fin n) C}
    (hZ : ∀ i j, Z i j ∈ K) (A : Matrix (Fin n) (Fin n) C) :
    (A * Z).map (evK K u) = A.map (res O C) * Z.map (evK K u) := by
  ext i j
  rw [Matrix.map_apply, Matrix.mul_apply, Matrix.mul_apply,
    evk_sum u _ _ fun k => K.mul_mem_left _ (hZ k j)]
  exact Finset.sum_congr rfl fun k _ => evk_mul u hK _ (hZ k j)

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, Matrix.mul_apply, Matrix.mul_apply, evk_sum u _ _ fun k => K.mul_mem_right _ (hZ i k)]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm, evk_mul u hK _ (hZ i k), mul_comm]`. Both sides reduce to the same expression.
-/
private theorem map_right [IsCO O C] (hK : maximalIdeal C * K = ⊥) {Z : Matrix (Fin n) (Fin n) C}
    (hZ : ∀ i j, Z i j ∈ K) (A : Matrix (Fin n) (Fin n) C) :
    (Z * A).map (evK K u) = Z.map (evK K u) * A.map (res O C) := by
  ext i j
  rw [Matrix.map_apply, Matrix.mul_apply, Matrix.mul_apply,
    evk_sum u _ _ fun k => K.mul_mem_right _ (hZ i k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, evk_mul u hK _ (hZ i k), mul_comm]
  rfl

/- English proof (translation)
The claim follows from `K.neg_mem (mem_right (mem_left (Z := Zᵀ) (fun i j => hZ j i) _) _ i j)`.
-/
private theorem mem_theta {Z : Matrix (Fin n) (Fin n) C} (hZ : ∀ i j, Z i j ∈ K) (i j : Fin n) :
    thetaLie Z i j ∈ K :=
  K.neg_mem (mem_right (mem_left (Z := Zᵀ) (fun i j => hZ j i) _) _ i j)

/- English proof (translation)
Establish `hT : ∀ i j, Zᵀ i j ∈ K` using `fun i j => hZ j i`. Establish `hJ : (Jmat C n).map (res O C) = Jmat (ResidueField O) n` using `Jmat_map (res O C : C →+* ResidueField O) n`. Establish `e : (Jmat C n * Zᵀ * Jmat C n).map (evK K u) = Jmat (ResidueField O) n * (Z.map (evK K u))ᵀ * Jmat (ResidueField O) n`. Rewrite using `[map_right u hK (mem_left hT _), map_left u hK hT, hJ]`. Both sides reduce to the same expression.

Unfold `thetaLie`. Rewrite using `[← e]`. Use extensionality with `i j`. Conclude with `evk_neg u (mem_right (mem_left hT _) _ i j)`.
-/
private theorem map_thetaLie [IsCO O C] (hK : maximalIdeal C * K = ⊥) {Z : Matrix (Fin n) (Fin n) C}
    (hZ : ∀ i j, Z i j ∈ K) : (thetaLie Z).map (evK K u) = thetaLie (Z.map (evK K u)) := by
  have hT : ∀ i j, Zᵀ i j ∈ K := fun i j => hZ j i
  have hJ : (Jmat C n).map (res O C) = Jmat (ResidueField O) n :=
    Jmat_map (res O C : C →+* ResidueField O) n
  have e : (Jmat C n * Zᵀ * Jmat C n).map (evK K u) =
      Jmat (ResidueField O) n * (Z.map (evK K u))ᵀ * Jmat (ResidueField O) n := by
    rw [map_right u hK (mem_left hT _), map_left u hK hT, hJ]
    rfl
  unfold thetaLie
  rw [← e]
  ext i j
  exact evk_neg u (mem_right (mem_left hT _) _ i j)

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `O _ _ C _ _ _ n K u hK hKm Z hZ`. Establish `hsq : ∀ Z' : Matrix (Fin n) (Fin n) C, (∀ i j, Z' i j ∈ K) → Z * Z' = 0` using `fun Z' hZ' => by`. Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations.

Use `Ideal.mul_mem_mul (hKm (hZ i k)) (hZ' k j)` as an intermediate fact. Rewrite `this` using `[hK, Ideal.mem_bot]`. Then use the resulting hypothesis. Use `⟨fun Z' hZ' => ⟨hsq Z' hZ', ?_, ?_⟩, fun A => ⟨fun i j => ⟨mem_left hZ A i j, mem_right hZ A i j⟩, map_left u hK hZ A, map_right u hK hZ A⟩, fun x => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Conclude with `evk_add u (hZ i j) (hZ' i j)`.

Use extensionality with `i j`. Conclude with `evk_sub u (hZ i j) (hZ' i j)`. Establish `hY : ∀ i j, (if x.right = 1 then Z else thetaLie Z) i j ∈ K` using `fun i j => by split_ifs`. Conclude with `hZ i j`. Conclude with `mem_theta hZ i j`.

Use `⟨mem_right (mem_left hY _) _, ?_, fun z hz => ?_⟩` and prove the remaining obligations. Establish `hY' : (if x.right = 1 then Z else thetaLie Z).map (evK K u) = if x.right = 1 then Z.map (evK K u) else thetaLie (Z.map (evK K u))` using `by split_ifs`. Both sides reduce to the same expression. Conclude with `map_thetaLie u hK hZ`. Unfold `GG.adFun`.

Rewrite using `[map_right u hK (mem_left hY _), map_left u hK hY, hY']`. Both sides reduce to the same expression. Establish `hinv : ((z⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) = 1 - Z`. Establish `: (z : Matrix (Fin n) (Fin n) C) * (1 - Z) = 1`. Rewrite using `[hz, add_mul, mul_sub, mul_sub, hsq Z hZ]`.

Simplify using the standard rewrite rules. Conclude with `Units.inv_eq_of_mul_eq_one_right this`. Establish `hl : (x * GG.ofGL z * x⁻¹).left = x.left * sgnAct n C x.right z * x.left⁻¹`. Rewrite using `[SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl, mul_one, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]`. Establish `hs : ((sgnAct n C x.right z : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) = 1 + (if x.right = 1 then Z else thetaLie Z)`.

Break down `Int.units_eq_one_or x.right with h | h` into its components or cases. Rewrite using `[h, sgnAct_one, if_pos rfl, hz]`. Rewrite using `[h, sgnAct_neg_one, if_neg (by decide), theta_val, hinv, thetaLie, Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Jmat_mul_Jmat, sub_eq_add_neg]`. Unfold `GG.adFun GG.mat`. Rewrite using `[hl, Units.val_mul, Units.val_mul, hs, mul_add, add_mul, mul_one, Units.mul_inv]`.
-/
theorem UpperTheory.V.Fr.pr_evk :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (n : ℕ) (K : Ideal C) (u : K →ₗ[O] ResidueField O), maximalIdeal C * K = ⊥ → K ≤ maximalIdeal C → ∀ Z : Matrix (Fin n) (Fin n) C, (∀ i j, Z i j ∈ K) → (∀ Z' : Matrix (Fin n) (Fin n) C, (∀ i j, Z' i j ∈ K) → Z * Z' = 0 ∧ (Z + Z').map (evK K u) = Z.map (evK K u) + Z'.map (evK K u) ∧ (Z - Z').map (evK K u) = Z.map (evK K u) - Z'.map (evK K u)) ∧ (∀ A : Matrix (Fin n) (Fin n) C, (∀ i j, (A * Z) i j ∈ K ∧ (Z * A) i j ∈ K) ∧ (A * Z).map (evK K u) = A.map (res O C) * Z.map (evK K u) ∧ (Z * A).map (evK K u) = Z.map (evK K u) * A.map (res O C)) ∧ ∀ x : GG n C, (∀ i j, x.adFun Z i j ∈ K) ∧ (x.adFun Z).map (evK K u) = (GG.map (res O C : C →+* ResidueField O) x).adFun (Z.map (evK K u)) ∧ ∀ z : GL (Fin n) C, (z : Matrix (Fin n) (Fin n) C) = 1 + Z → (x * GG.ofGL z * x⁻¹).mat = 1 + x.adFun Z := by
  intro O _ _ C _ _ _ n K u hK hKm Z hZ
  have hsq : ∀ Z' : Matrix (Fin n) (Fin n) C, (∀ i j, Z' i j ∈ K) → Z * Z' = 0 := fun Z' hZ' => by
    ext i j
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    have := Ideal.mul_mem_mul (hKm (hZ i k)) (hZ' k j)
    rwa [hK, Ideal.mem_bot] at this
  refine ⟨fun Z' hZ' => ⟨hsq Z' hZ', ?_, ?_⟩,
    fun A => ⟨fun i j => ⟨mem_left hZ A i j, mem_right hZ A i j⟩, map_left u hK hZ A, map_right u hK hZ A⟩,
    fun x => ?_⟩
  · ext i j
    exact evk_add u (hZ i j) (hZ' i j)
  · ext i j
    exact evk_sub u (hZ i j) (hZ' i j)
  have hY : ∀ i j, (if x.right = 1 then Z else thetaLie Z) i j ∈ K := fun i j => by
    split_ifs
    · exact hZ i j
    · exact mem_theta hZ i j
  refine ⟨mem_right (mem_left hY _) _, ?_, fun z hz => ?_⟩
  · have hY' : (if x.right = 1 then Z else thetaLie Z).map (evK K u) =
        if x.right = 1 then Z.map (evK K u) else thetaLie (Z.map (evK K u)) := by
      split_ifs
      · rfl
      · exact map_thetaLie u hK hZ
    unfold GG.adFun
    rw [map_right u hK (mem_left hY _), map_left u hK hY, hY']
    rfl
  · have hinv : ((z⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) = 1 - Z := by
      have : (z : Matrix (Fin n) (Fin n) C) * (1 - Z) = 1 := by
        rw [hz, add_mul, mul_sub, mul_sub, hsq Z hZ]
        simp
      exact Units.inv_eq_of_mul_eq_one_right this
    have hl : (x * GG.ofGL z * x⁻¹).left = x.left * sgnAct n C x.right z * x.left⁻¹ := by
      rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
        SemidirectProduct.inv_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl, mul_one,
        ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    have hs : ((sgnAct n C x.right z : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) =
        1 + (if x.right = 1 then Z else thetaLie Z) := by
      rcases Int.units_eq_one_or x.right with h | h
      · rw [h, sgnAct_one, if_pos rfl, hz]
      · rw [h, sgnAct_neg_one, if_neg (by decide), theta_val, hinv, thetaLie, Matrix.transpose_sub,
          Matrix.transpose_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Jmat_mul_Jmat,
          sub_eq_add_neg]
    unfold GG.adFun GG.mat
    rw [hl, Units.val_mul, Units.val_mul, hs, mul_add, add_mul, mul_one, Units.mul_inv]

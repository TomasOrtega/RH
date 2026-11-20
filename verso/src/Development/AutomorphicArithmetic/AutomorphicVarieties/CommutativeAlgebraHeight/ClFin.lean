import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `Submodule.smul_induction_on hx (fun a ha y _ i => ?_) (fun a b ha hb i => ?_)` and prove the remaining obligations. Conclude with `J.mul_mem_right _ ha`. Conclude with `J.add_mem (ha i) (hb i)`.

Introduce `hx`. Rewrite using `[pi_eq_sum_univ x]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top`.
-/
private theorem mem_smul_top_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha y _ i => ?_) (fun a b ha hb i => ?_)
    · exact J.mul_mem_right _ ha
    · exact J.add_mem (ha i) (hb i)
  · intro hx
    rw [pi_eq_sum_univ x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

/- English proof (translation)
Use `⟨fun f hf => ?_⟩` and prove the remaining obligations. Establish `key : ∀ i, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)]` using `fun i => IsPrecomplete.prec' (I := I) (fun n => f n i) fun {m n} hmn => by`. Establish `h` using `hf hmn`. Rewrite `h` using `[SModEq.sub_mem, mem_smul_top_pi]`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`.

Conclude with `h i`. Use `choose L hL using key`. Use `⟨L, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, mem_smul_top_pi]`. Introduce `i`.

Establish `h` using `hL i n`. Rewrite `h` using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`. Then use the resulting hypothesis.
-/
private theorem isPrecomplete_pi {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (r : ℕ) :
    IsPrecomplete I (Fin r → R) := by
  refine ⟨fun f hf => ?_⟩
  have key : ∀ i, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := fun i =>
    IsPrecomplete.prec' (I := I) (fun n => f n i) fun {m n} hmn => by
      have h := hf hmn
      rw [SModEq.sub_mem, mem_smul_top_pi] at h
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      exact h i
  choose L hL using key
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, mem_smul_top_pi]
  intro i
  have h := hL i n
  rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h

/- English proof (translation)
Take `⟨r, π, hπ⟩` from `Module.Finite.exists_fin' R M`. Use `haveI := isPrecomplete_pi I r`. Rewrite using `[← AdicCompletion.of_surjective_iff]`. Introduce `y`. Take `⟨z, rfl⟩` from `AdicCompletion.map_surjective I hπ y`.

Take `⟨w, rfl⟩` from `AdicCompletion.of_surjective I (Fin r → R) z`. Conclude with `⟨π w, (AdicCompletion.map_of I π w).symm⟩`.
-/
private theorem isPrecomplete_finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I M := by
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' R M
  haveI := isPrecomplete_pi I r
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨z, rfl⟩ := AdicCompletion.map_surjective I hπ y
  obtain ⟨w, rfl⟩ := AdicCompletion.of_surjective I (Fin r → R) z
  exact ⟨π w, (AdicCompletion.map_of I π w).symm⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun f hf => by simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢ obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun k => f ((e + 1) * k)) (fun {m n} hmn => by rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] have h := hf (Nat.mul_le_mul_left (e + 1) hmn) rw [pow_mul …`.
-/
private theorem prec_cofinal {R : Type*} [CommRing R] {I J : Ideal R} (hJI : J ≤ I) {e : ℕ}
    (he : I ^ e ≤ J) (hJ : IsPrecomplete J R) : IsPrecomplete I R := ⟨fun f hf => by
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun k => f ((e + 1) * k))
    (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have h := hf (Nat.mul_le_mul_left (e + 1) hmn)
      rw [pow_mul] at h
      exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right (Nat.le_succ e)).trans he) m h)
  refine ⟨L, fun n => ?_⟩
  have h1 := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 := hf (m := n) (n := (e + 1) * n) (Nat.le_mul_of_pos_left n (Nat.succ_pos e))
  simpa using (I ^ n).add_mem h2 (Ideal.pow_right_mono hJI n h1)⟩

/- English proof (translation)
Introduce `O _ R _ _ _ R' _ _ _ _ _ _ h`. Use `haveI := h.noeth`. Use `haveI := h.complete`. Use `haveI := h.isLocalHom`. Use `haveI := h.res_fin`.

Use `haveI hN : IsNoetherianRing R' := IsNoetherianRing.of_finite R R'`. Establish `hcomap : (maximalIdeal R').comap (algebraMap R R') = maximalIdeal R` using `eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal R'))`. Establish `hle : (maximalIdeal R).map (algebraMap R R') ≤ maximalIdeal R'` using `Ideal.map_le_iff_le_comap.2 hcomap.ge`. Establish `hrad : maximalIdeal R' ≤ ((maximalIdeal R).map (algebraMap R R')).radical`. Rewrite using `[Ideal.radical_eq_sInf]`.

Use `le_sInf fun P hP => ?_` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hP`. Establish `h3 : P.comap (algebraMap R R') = maximalIdeal R` using `((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ h2.ne_top) (Ideal.map_le_iff_le_comap.1 h1)).symm`. Establish `h4 : P.IsMaximal` using `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) P (h3 ▸ maximalIdeal.isMaximal R)`. Conclude with `(eq_maximalIdeal h4).ge`.

Take `⟨e, he⟩` from `Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)`. Establish `hP : IsPrecomplete (maximalIdeal R') R'` using `prec_cofinal hle he (IsPrecomplete.map_algebraMap_iff.2 (isPrecomplete_finite _))`. Use `haveI hloc : IsLocalHom (algebraMap R R') := ⟨fun a ha => by`. Assume the negation of the conclusion as `hn`. Establish `h1 : a ∈ maximalIdeal R` using `hn`.

Rewrite `h1` using `[← hcomap, Ideal.mem_comap]`. Conclude with `h1 ha⟩`. Use `haveI hT : IsScalarTower O (ResidueField R) (ResidueField R') := IsScalarTower.of_algebraMap_eq fun a => by`. Rewrite using `[IsScalarTower.algebraMap_apply O R (ResidueField R), ← IsScalarTower.algebraMap_apply R (ResidueField R) (ResidueField R'), IsScalarTower.algebraMap_apply O R' (ResidueField R'), IsScalarTower.algebraMap_apply R R' (ResidueField R'), IsScalarTower.algebraMap_apply O R R']`. Conclude with `{ noeth := hN complete := { toIsHausdorff := inferInstance, toIsPrecomplete := hP } isLocalHom := by`.

Rewrite using `[IsScalarTower.algebraMap_eq O R R']`. Use `infer_instance`. Use `res_fin := Module.Finite.trans (ResidueField R) (ResidueField R') }`.
-/
theorem UpperTheory.V.CA.cl_fin :
    ∀ (O : Type) [CommRing O] (R : Type) [CommRing R] [Algebra O R] [IsLocalRing R] (R' : Type) [CommRing R'] [Algebra O R'] [IsLocalRing R'] [Algebra R R'] [IsScalarTower O R R'] [Module.Finite R R'], IsCL O R → IsCL O R' := by
  intro O _ R _ _ _ R' _ _ _ _ _ _ h
  haveI := h.noeth
  haveI := h.complete
  haveI := h.isLocalHom
  haveI := h.res_fin
  haveI hN : IsNoetherianRing R' := IsNoetherianRing.of_finite R R'
  have hcomap : (maximalIdeal R').comap (algebraMap R R') = maximalIdeal R :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal R'))
  have hle : (maximalIdeal R).map (algebraMap R R') ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.2 hcomap.ge
  have hrad : maximalIdeal R' ≤ ((maximalIdeal R).map (algebraMap R R')).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP => ?_
    obtain ⟨h1, h2⟩ := hP
    have h3 : P.comap (algebraMap R R') = maximalIdeal R :=
      ((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ h2.ne_top)
        (Ideal.map_le_iff_le_comap.1 h1)).symm
    have h4 : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) P (h3 ▸ maximalIdeal.isMaximal R)
    exact (eq_maximalIdeal h4).ge
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  have hP : IsPrecomplete (maximalIdeal R') R' :=
    prec_cofinal hle he (IsPrecomplete.map_algebraMap_iff.2 (isPrecomplete_finite _))
  haveI hloc : IsLocalHom (algebraMap R R') := ⟨fun a ha => by
    by_contra hn
    have h1 : a ∈ maximalIdeal R := hn
    rw [← hcomap, Ideal.mem_comap] at h1
    exact h1 ha⟩
  haveI hT : IsScalarTower O (ResidueField R) (ResidueField R') :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply O R (ResidueField R),
        ← IsScalarTower.algebraMap_apply R (ResidueField R) (ResidueField R'),
        IsScalarTower.algebraMap_apply O R' (ResidueField R'),
        IsScalarTower.algebraMap_apply R R' (ResidueField R'),
        IsScalarTower.algebraMap_apply O R R']
  exact
    { noeth := hN
      complete := { toIsHausdorff := inferInstance, toIsPrecomplete := hP }
      isLocalHom := by
        rw [IsScalarTower.algebraMap_eq O R R']
        infer_instance
      res_fin := Module.Finite.trans (ResidueField R) (ResidueField R') }

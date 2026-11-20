import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.ResLeCont

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp

private def formJ (R : Type) [CommRing R] : M4 R := !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [formJ, adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four]`.
-/
private theorem formJ_adj {R : Type} [CommRing R] (X : M4 R) : formJ R * adj X = X.transpose * formJ R := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [formJ, adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [formJ, Matrix.mul_apply, Fin.sum_univ_four]`.
-/
private theorem formJ_sq (R : Type) [CommRing R] : formJ R * formJ R = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [formJ, Matrix.mul_apply, Fin.sum_univ_four]

private def formU (R : Type) [CommRing R] : GL (Fin 4) R :=
  ⟨formJ R, -formJ R, by rw [mul_neg, formJ_sq, neg_neg], by rw [neg_mul, formJ_sq, neg_neg]⟩

/- English proof (translation)
Establish `hX' : adj X * X = ν • 1` using `hX`. Rewrite using `[← formJ_adj, Matrix.mul_assoc, hX', Matrix.mul_smul, Matrix.mul_one]`.
-/
private theorem form_gsp {R : Type} [CommRing R] {ν : R} {X : M4 R} (hX : IsGSp ν X) :
    X.transpose * formJ R * X = ν • formJ R := by
  have hX' : adj X * X = ν • 1 := hX
  rw [← formJ_adj, Matrix.mul_assoc, hX', Matrix.mul_smul, Matrix.mul_one]

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D T c' h K n r hr`. Take `⟨j, hj⟩` from `K.s.hc`. Establish `hfixF : ∀ x : T.F, K.s.c (algebraMap T.F Ω x) = algebraMap T.F Ω x`. Introduce `x`. Apply `j.injective` to reduce the goal to its premises.

Rewrite using `[hj]`. Establish `hw` using `IsTotallyReal.isReal (InfinitePlace.mk (j.comp (algebraMap T.F Ω)))`. Rewrite `hw` using `[InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff]`. Establish `hx` using `RingHom.congr_fun hw x`. Simplify `hx` using `[ComplexEmbedding.conjugate_coe_eq]`.

Set `cF : G T.F Ω` to `AlgEquiv.ofRingEquiv (f := K.s.c.toRingEquiv) hfixF`. Establish `hCiC : r cF⁻¹ * r cF = 1` using `by rw [← map_mul, inv_mul_cancel, map_one]`. Establish `hCCi : r cF * r cF⁻¹ = 1` using `by rw [← map_mul, mul_inv_cancel, map_one]`. Set `U : GL (Fin 4) (PadicAlgCl l)` to `⟨r cF⁻¹, r cF, hCiC, hCCi⟩`. Use `⟨formU (PadicAlgCl l) * U, ?_⟩` and prove the remaining obligations.

Introduce `s s' hs`. Establish `hres : resLe T.F_le s' = cF * resLe T.F_le s * cF⁻¹`. Use extensionality with `x`. Establish `hx` using `DFunLike.congr_fun hs x`. Use `first`.

Consider the case `exact hx`. Consider the case `simpa [cF] using hx`. Establish `hconj` using `K.conj s s' hs`. Rewrite using `[K.rho_val, K.rho_val, hres, map_mul, map_mul]`. Establish `hA` using `form_gsp (hr (resLe T.F_le s))`.

Establish `hU : ((formU (PadicAlgCl l) * U : GL (Fin 4) (PadicAlgCl l)) : M4 (PadicAlgCl l)) = formJ (PadicAlgCl l) * r cF⁻¹` using `rfl`. Rewrite using `[hU]`. Establish `key : (r (resLe T.F_le s)).transpose * (formJ (PadicAlgCl l) * r cF⁻¹) * (r cF * r (resLe T.F_le s) * r cF⁻¹) = ((r (resLe T.F_le s)).transpose * formJ (PadicAlgCl l) * r (resLe T.F_le s)) * r cF⁻¹`. Combine the equalities or inequalities in the displayed calculation. Rewrite `key` using `[hA, Matrix.smul_mul]`.

Simplify using `only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]`. Rewrite using `[key, smul_smul]`. Use `congr 1`. Rewrite using `[K.twc_val, K.twc_val, ← map_mul, ← map_mul]`. Establish `hq : resQ T.F (resLe T.F_le s) = resQ T.L s` using `rfl`.

Rewrite using `[hq]`. Establish `hb : (↑(K.β s) : c'.O) * ↑(K.β s') = 1` using `by rw [← Units.val_mul, hconj.2.1, Units.val_one]`. Establish `e1 : (↑(K.κ s') * ↑(K.β s') ^ n : c'.O) * (↑(K.κ s) * ↑(K.β s) ^ n) * inc h ↑(D.th (resQ T.L s)) = ↑(K.κ s) * ↑(K.κ s') * inc h ↑(D.th (resQ T.L s))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e1]`.

Establish `e3` using `congrArg (algebraMap c'.O (PadicAlgCl l)) hconj.1`. Rewrite `e3` using `[map_mul, map_pow, map_one]`. Establish `hχ : algebraMap c'.O (PadicAlgCl l) ↑((chiO T.L Ω l c'.O) s) = (↑(cycBar T.L Ω l s) : PadicAlgCl l)` using `rfl`. Rewrite `e3` using `[hχ]`. Rewrite using `[eq_inv_of_mul_eq_one_left e3]`.

Establish `hz : (1 - ((4 : ℕ) : ℤ)) = -3` using `by norm_num`. Rewrite using `[hz]`. Use `first`. Consider the case `simp [zpow_neg, Units.val_zpow_eq_zpow_val]`. Consider the case `(rw [MonoidHom.zpow_apply]; simp [zpow_neg, Units.val_zpow_eq_zpow_val])`.

Consider the case `done`.
-/
theorem UpperTheory.V.Ws.Pt.ptPair :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (n : ℕ) (r : G T.F Ω →* M4 (PadicAlgCl l)), (∀ g, IsGSp (algebraMap c'.O (PadicAlgCl l) (inc h (D.th (resQ T.F g)))) (r g)) → ∃ P : GL (Fin 4) (PadicAlgCl l), Af.IsPairing K.s.c (K.rhoQ n r) (cycBar T.L Ω l ^ (1 - ((4 : ℕ) : ℤ))) P := by
  intro Ω _ _ _ l _ c D T c' h K n r hr
  obtain ⟨j, hj⟩ := K.s.hc
  have hfixF : ∀ x : T.F, K.s.c (algebraMap T.F Ω x) = algebraMap T.F Ω x := by
    intro x
    apply j.injective
    rw [hj]
    have hw := IsTotallyReal.isReal (InfinitePlace.mk (j.comp (algebraMap T.F Ω)))
    rw [InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff] at hw
    have hx := RingHom.congr_fun hw x
    simpa [ComplexEmbedding.conjugate_coe_eq] using hx
  let cF : G T.F Ω := AlgEquiv.ofRingEquiv (f := K.s.c.toRingEquiv) hfixF
  have hCiC : r cF⁻¹ * r cF = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hCCi : r cF * r cF⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  let U : GL (Fin 4) (PadicAlgCl l) := ⟨r cF⁻¹, r cF, hCiC, hCCi⟩
  refine ⟨formU (PadicAlgCl l) * U, ?_⟩
  intro s s' hs
  have hres : resLe T.F_le s' = cF * resLe T.F_le s * cF⁻¹ := by
    ext x
    have hx := DFunLike.congr_fun hs x
    first
      | exact hx
      | simpa [cF] using hx
  have hconj := K.conj s s' hs
  rw [K.rho_val, K.rho_val, hres, map_mul, map_mul]
  have hA := form_gsp (hr (resLe T.F_le s))
  have hU : ((formU (PadicAlgCl l) * U : GL (Fin 4) (PadicAlgCl l)) : M4 (PadicAlgCl l)) =
      formJ (PadicAlgCl l) * r cF⁻¹ := rfl
  rw [hU]
  have key : (r (resLe T.F_le s)).transpose * (formJ (PadicAlgCl l) * r cF⁻¹) *
      (r cF * r (resLe T.F_le s) * r cF⁻¹) =
      ((r (resLe T.F_le s)).transpose * formJ (PadicAlgCl l) * r (resLe T.F_le s)) * r cF⁻¹ := by
    calc _ = (r (resLe T.F_le s)).transpose * formJ (PadicAlgCl l) * (r cF⁻¹ * r cF) *
          r (resLe T.F_le s) * r cF⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hCiC, Matrix.mul_one]
  rw [hA, Matrix.smul_mul] at key
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [key, smul_smul]
  congr 1
  rw [K.twc_val, K.twc_val, ← map_mul, ← map_mul]
  have hq : resQ T.F (resLe T.F_le s) = resQ T.L s := rfl
  rw [hq]
  have hb : (↑(K.β s) : c'.O) * ↑(K.β s') = 1 := by rw [← Units.val_mul, hconj.2.1, Units.val_one]
  have e1 : (↑(K.κ s') * ↑(K.β s') ^ n : c'.O) * (↑(K.κ s) * ↑(K.β s) ^ n) * inc h ↑(D.th (resQ T.L s)) =
      ↑(K.κ s) * ↑(K.κ s') * inc h ↑(D.th (resQ T.L s)) := by
    calc _ = ↑(K.κ s) * ↑(K.κ s') * inc h ↑(D.th (resQ T.L s)) * (↑(K.β s) * ↑(K.β s')) ^ n := by ring
      _ = _ := by rw [hb, one_pow, mul_one]
  rw [e1]
  have e3 := congrArg (algebraMap c'.O (PadicAlgCl l)) hconj.1
  rw [map_mul, map_pow, map_one] at e3
  have hχ : algebraMap c'.O (PadicAlgCl l) ↑((chiO T.L Ω l c'.O) s) = (↑(cycBar T.L Ω l s) : PadicAlgCl l) := rfl
  rw [hχ] at e3
  rw [eq_inv_of_mul_eq_one_left e3]
  have hz : (1 - ((4 : ℕ) : ℤ)) = -3 := by norm_num
  rw [hz]
  first
    | simp [zpow_neg, Units.val_zpow_eq_zpow_val]
    | (rw [MonoidHom.zpow_apply]; simp [zpow_neg, Units.val_zpow_eq_zpow_val])
    | done

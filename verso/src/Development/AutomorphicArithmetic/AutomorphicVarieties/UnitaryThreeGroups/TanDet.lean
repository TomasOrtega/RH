import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Rigid0
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.nakayama
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

section Alg

variable {O R κ Γ : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing κ] [Algebra O κ] [Group Γ]

private def sndL (F : R →ₐ[O] DualNumber κ) : R →ₗ[O] κ :=
  ((TrivSqZeroExt.sndHom κ κ).restrictScalars O).comp F.toLinearMap

/- English proof (translation)
Use `show (F (x * y)).snd = (F x).fst * (F y).snd + (F y).fst * (F x).snd`. Rewrite using `[map_mul, DualNumber.snd_mul, mul_comm (F x).snd]`.
-/
private theorem sndL_mul (F : R →ₐ[O] DualNumber κ) (x y : R) :
    sndL F (x * y) = dualFst F x * sndL F y + dualFst F y * sndL F x := by
  show (F (x * y)).snd = (F x).fst * (F y).snd + (F y).fst * (F x).snd
  rw [map_mul, DualNumber.snd_mul, mul_comm (F x).snd]

/- English proof (translation)
Use `show (F 1).snd = 0`. Rewrite using `[map_one, TrivSqZeroExt.snd_one]`.
-/
private theorem sndL_one (F : R →ₐ[O] DualNumber κ) : sndL F 1 = 0 := by
  show (F 1).snd = 0
  rw [map_one, TrivSqZeroExt.snd_one]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum, sndL_mul, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`.
-/
private theorem map_sndL_mul {m : ℕ} (F : R →ₐ[O] DualNumber κ) (A B : Matrix (Fin m) (Fin m) R) :
    (A * B).map (sndL F) = A.map (sndL F) * B.map (dualFst F) + A.map (dualFst F) * B.map (sndL F) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum, sndL_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, Matrix.one_apply]`. Use `split_ifs`. Conclude with `sndL_one F`. Conclude with `map_zero _`.
-/
private theorem map_sndL_one {m : ℕ} (F : R →ₐ[O] DualNumber κ) :
    (1 : Matrix (Fin m) (Fin m) R).map (sndL F) = 0 := by
  ext i j
  rw [Matrix.map_apply, Matrix.one_apply]
  split_ifs
  · exact sndL_one F
  · exact map_zero _

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, Jmat]`. Use `split_ifs`. Conclude with `sndL_one F`. Conclude with `map_zero _`.
-/
private theorem map_sndL_J {m : ℕ} (F : R →ₐ[O] DualNumber κ) : (Jmat R m).map (sndL F) = 0 := by
  ext i j
  rw [Matrix.map_apply, Jmat]
  split_ifs
  · exact sndL_one F
  · exact map_zero _

private def lder {m : ℕ} (F : R →ₐ[O] DualNumber κ) (a : GL (Fin m) R) : Matrix (Fin m) (Fin m) κ :=
  (a : Matrix (Fin m) (Fin m) R).map (sndL F) * ((a⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R).map (dualFst F)

/- English proof (translation)
Rewrite using `[← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero f) (map_one f)]`.
-/
private theorem fst_mul_inv {m : ℕ} (f : R →ₐ[O] κ) (a : GL (Fin m) R) :
    (a : Matrix (Fin m) (Fin m) R).map f * ((a⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R).map f = 1 := by
  rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero f) (map_one f)]

/- English proof (translation)
Rewrite using `[← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero f) (map_one f)]`.
-/
private theorem fst_inv_mul {m : ℕ} (f : R →ₐ[O] κ) (a : GL (Fin m) R) :
    ((a⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R).map f * (a : Matrix (Fin m) (Fin m) R).map f = 1 := by
  rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero f) (map_one f)]

/- English proof (translation)
Simplify using `only [lder, _root_.mul_inv_rev, Units.val_mul, map_sndL_mul, Matrix.map_mul, Matrix.add_mul, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (b.val.map _) (b⁻¹.val.map _), fst_mul_inv, Matrix.one_mul]`.
-/
private theorem lder_mul {m : ℕ} (F : R →ₐ[O] DualNumber κ) (a b : GL (Fin m) R) :
    lder F (a * b) = lder F a + (a : Matrix (Fin m) (Fin m) R).map (dualFst F) * lder F b *
      ((a⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R).map (dualFst F) := by
  simp only [lder, _root_.mul_inv_rev, Units.val_mul, map_sndL_mul, Matrix.map_mul, Matrix.add_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (b.val.map _) (b⁻¹.val.map _), fst_mul_inv, Matrix.one_mul]

/- English proof (translation)
Establish `hJ : (Jmat R m).map (dualFst F) = Jmat κ m` using `Jmat_map (dualFst F : R →+* κ) m`. Establish `h1` using `map_sndL_mul F b.val b⁻¹.val`. Rewrite `h1` using `[Units.mul_inv, map_sndL_one]`. Establish `h2 : lder F b = -(b.val.map (dualFst F) * b⁻¹.val.map (sndL F))` using `eq_neg_of_add_eq_zero_left h1.symm`. Rewrite using `[thetaLie, h2, lder, theta_val, theta_inv_val]`.

Simplify using `only [map_sndL_mul, map_sndL_J, Matrix.map_mul, hJ, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.transpose_map, Matrix.transpose_neg, Matrix.transpose_mul, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (Jmat κ m) (Jmat κ m), Jmat_mul_Jmat, Matrix.one_mul]`.
-/
private theorem lder_theta {m : ℕ} (F : R →ₐ[O] DualNumber κ) (b : GL (Fin m) R) :
    lder F (theta b) = thetaLie (lder F b) := by
  have hJ : (Jmat R m).map (dualFst F) = Jmat κ m := Jmat_map (dualFst F : R →+* κ) m
  have h1 := map_sndL_mul F b.val b⁻¹.val
  rw [Units.mul_inv, map_sndL_one] at h1
  have h2 : lder F b = -(b.val.map (dualFst F) * b⁻¹.val.map (sndL F)) := eq_neg_of_add_eq_zero_left h1.symm
  rw [thetaLie, h2, lder, theta_val, theta_inv_val]
  simp only [map_sndL_mul, map_sndL_J, Matrix.map_mul, hJ, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.transpose_map, Matrix.transpose_neg, Matrix.transpose_mul, Matrix.mul_neg, Matrix.neg_mul, neg_neg,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Jmat κ m) (Jmat κ m), Jmat_mul_Jmat, Matrix.one_mul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem tanCoc_eq (F : R →ₐ[O] DualNumber κ) (r : Γ →* GG 3 R) (g : Γ) :
    tanCoc F r g = lder F (r g).left := rfl

/- English proof (translation)
Introduce `g h`. Establish `hne : ((-1 : ℤˣ) = 1) = False` using `by decide`. Establish `e : adRep (push (dualFst F) r) g (tanCoc F r h) = (r g).left.val.map (dualFst F) * (if (r g).right = 1 then tanCoc F r h else thetaLie (tanCoc F r h)) * ((r g).left⁻¹).val.map (dualFst F)` using `rfl`. Rewrite using `[e, tanCoc_eq, tanCoc_eq, tanCoc_eq, map_mul, SemidirectProduct.mul_left, lder_mul]`. Break down `Int.units_eq_one_or (r g).right with hs | hs` into its components or cases.

Rewrite using `[hs, sgnAct_one, if_pos rfl]`. Rewrite using `[hs, sgnAct_neg_one, lder_theta]`. Simplify using `only [hne, if_false]`.
-/
private theorem tan_isCoc (F : R →ₐ[O] DualNumber κ) (r : Γ →* GG 3 R) :
    IsCoc (push (dualFst F) r) (tanCoc F r) := by
  intro g h
  have hne : ((-1 : ℤˣ) = 1) = False := by decide
  have e : adRep (push (dualFst F) r) g (tanCoc F r h) =
      (r g).left.val.map (dualFst F) * (if (r g).right = 1 then tanCoc F r h else thetaLie (tanCoc F r h)) *
        ((r g).left⁻¹).val.map (dualFst F) := rfl
  rw [e, tanCoc_eq, tanCoc_eq, tanCoc_eq, map_mul, SemidirectProduct.mul_left, lder_mul]
  rcases Int.units_eq_one_or (r g).right with hs | hs
  · rw [hs, sgnAct_one, if_pos rfl]
  · rw [hs, sgnAct_neg_one, lder_theta]
    simp only [hne, if_false]

/- English proof (translation)
Use `show lder F (r g).left * (r g).left.val.map (dualFst F) = _`. Rewrite using `[lder, Matrix.mul_assoc, fst_inv_mul, Matrix.mul_one]`. Both sides reduce to the same expression.
-/
private theorem tan_mul (F : R →ₐ[O] DualNumber κ) (r : Γ →* GG 3 R) (g : Γ) :
    tanCoc F r g * (push (dualFst F) r g).mat = (r g).mat.map (sndL F) := by
  show lder F (r g).left * (r g).left.val.map (dualFst F) = _
  rw [lder, Matrix.mul_assoc, fst_inv_mul, Matrix.mul_one]
  rfl

/- English proof (translation)
Use `show (r g).mat.map (sndL F) * _ = _`. Rewrite using `[h, map_sndL_one, Matrix.zero_mul]`.
-/
private theorem tan_zero (F : R →ₐ[O] DualNumber κ) (r : Γ →* GG 3 R) (g : Γ) (h : (r g).mat = 1) :
    tanCoc F r g = 0 := by
  show (r g).mat.map (sndL F) * _ = _
  rw [h, map_sndL_one, Matrix.zero_mul]

/- English proof (translation)
Establish `hz : ∀ a b, zvar c g₁ (push (dualFst F) r) (tanCoc F r) a b = sndL F (zmat c g₁ r a b)` using `fun a b => by`. Rewrite using `[zvar, tan_mul, tan_mul, zmat]`. Simplify using `only [Matrix.sub_apply, Matrix.map_apply, map_sub]`. Conclude with `⟨tan_zero F r c h.atc, by rw [hz, h.z12, map_zero], by rw [hz, h.z21, map_zero]⟩`.
-/
private theorem tan_norm (F : R →ₐ[O] DualNumber κ) (r : Γ →* GG 3 R) (c g₁ : Γ) (h : Normalised c g₁ r) :
    NormCoc c g₁ (push (dualFst F) r) (tanCoc F r) := by
  have hz : ∀ a b, zvar c g₁ (push (dualFst F) r) (tanCoc F r) a b = sndL F (zmat c g₁ r a b) := fun a b => by
    rw [zvar, tan_mul, tan_mul, zmat]
    simp only [Matrix.sub_apply, Matrix.map_apply, map_sub]
  exact ⟨tan_zero F r c h.atc, by rw [hz, h.z12, map_zero], by rw [hz, h.z21, map_zero]⟩

end Alg

/- English proof (translation)
Use `show Module.Finite O (R ⧸ J)`. Establish `hH : IsHausdorff (maximalIdeal O) (R ⧸ J)`. Rewrite using `[← IsHausdorff.map_algebraMap_iff (S := R)]`. Conclude with `IsHausdorff.of_isLocalRing _ _ (map_maximalIdeal_lt_top (algebraMap O R)).ne`. Use `(UpperTheory.V.abelian₂.nakayama O (maximalIdeal O) (R ⧸ J)).2 ?_` and prove the remaining obligations.

Establish `h1 : Finite (R ⧸ maximalIdeal R)` using `Finite.of_surjective _ (resMap_bijective O R).2`. Establish `h2 : Finite (R ⧸ (maximalIdeal R ^ n).restrictScalars O)` using `Ideal.finite_quotient_pow (IsNoetherian.noetherian (maximalIdeal R)) n`. Set `φ : R →ₗ[O] (R ⧸ J) ⧸ maximalIdeal O • (⊤ : Submodule O (R ⧸ J))` to `(Submodule.mkQ _).comp (Ideal.Quotient.mkₐ O _).toLinearMap`. Establish `hφ : Function.Surjective φ` using `(Submodule.mkQ_surjective _).comp Ideal.Quotient.mk_surjective`. Establish `hk : (maximalIdeal R ^ n).restrictScalars O ≤ LinearMap.ker φ` using `fun y hy => by`.

Take `⟨u, hu, v, hv, rfl⟩` from `Submodule.mem_sup.1 (hn hy)`. Take `⟨w, rfl⟩` from `Ideal.mem_span_singleton'.1 hu`. Use `show Submodule.Quotient.mk (Ideal.Quotient.mk _ _) = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hv, add_zero]`. Establish `e : Ideal.Quotient.mk J (w * algebraMap O R a) = a • Ideal.Quotient.mk J w`.

Rewrite using `[Algebra.smul_def, map_mul, mul_comm]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `Submodule.smul_mem_smul ha Submodule.mem_top`. Use `Module.Finite.of_surjective (Submodule.liftQ _ φ hk) fun z => ?_` and prove the remaining obligations.

Take `⟨y, rfl⟩` from `hφ z`. Conclude with `⟨Submodule.Quotient.mk y, rfl⟩`.
-/
private theorem fin_gen {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] (J : Ideal R) (a : O) (ha : a ∈ maximalIdeal O)
    (n : ℕ) (hn : maximalIdeal R ^ n ≤ Ideal.span {algebraMap O R a} ⊔ J) :
    Module.Finite O (R ⧸ J.restrictScalars O) := by
  show Module.Finite O (R ⧸ J)
  have hH : IsHausdorff (maximalIdeal O) (R ⧸ J) := by
    rw [← IsHausdorff.map_algebraMap_iff (S := R)]
    exact IsHausdorff.of_isLocalRing _ _ (map_maximalIdeal_lt_top (algebraMap O R)).ne
  refine (UpperTheory.V.abelian₂.nakayama O (maximalIdeal O) (R ⧸ J)).2 ?_
  have h1 : Finite (R ⧸ maximalIdeal R) :=
    Finite.of_surjective _ (resMap_bijective O R).2
  have h2 : Finite (R ⧸ (maximalIdeal R ^ n).restrictScalars O) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian (maximalIdeal R)) n
  let φ : R →ₗ[O] (R ⧸ J) ⧸ maximalIdeal O • (⊤ : Submodule O (R ⧸ J)) :=
    (Submodule.mkQ _).comp (Ideal.Quotient.mkₐ O _).toLinearMap
  have hφ : Function.Surjective φ := (Submodule.mkQ_surjective _).comp Ideal.Quotient.mk_surjective
  have hk : (maximalIdeal R ^ n).restrictScalars O ≤ LinearMap.ker φ := fun y hy => by
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 (hn hy)
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hu
    show Submodule.Quotient.mk (Ideal.Quotient.mk _ _) = 0
    rw [Submodule.Quotient.mk_eq_zero, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hv, add_zero]
    have e : Ideal.Quotient.mk J (w * algebraMap O R a) = a • Ideal.Quotient.mk J w := by
      rw [Algebra.smul_def, map_mul, mul_comm]
      rfl
    rw [e]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  refine Module.Finite.of_surjective (Submodule.liftQ _ φ hk) fun z => ?_
  obtain ⟨y, rfl⟩ := hφ z
  exact ⟨Submodule.Quotient.mk y, rfl⟩

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ, pow_succ]`. Use `(Ideal.mul_mono_left ih).trans ?_` and prove the remaining obligations.

Rewrite using `[Ideal.sup_mul, Ideal.mul_sup]`. Conclude with `sup_le (sup_le le_sup_left (le_sup_of_le_right (Ideal.mul_le_inf.trans inf_le_right))) (le_sup_of_le_right (Ideal.mul_le_inf.trans inf_le_left))`.
-/
private theorem sup_pow_le {R : Type} [CommRing R] (I J : Ideal R) (k : ℕ) : (I ⊔ J) ^ k ≤ I ^ k ⊔ J := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    refine (Ideal.mul_mono_left ih).trans ?_
    rw [Ideal.sup_mul, Ideal.mul_sup]
    exact sup_le (sup_le le_sup_left (le_sup_of_le_right (Ideal.mul_le_inf.trans inf_le_right)))
      (le_sup_of_le_right (Ideal.mul_le_inf.trans inf_le_left))

section Fin

variable {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R]

/- English proof (translation)
Establish `hi : IsIntegral ℚ_[l] x` using `Algebra.IsIntegral.isIntegral x`. Establish `h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x)` using `rfl`. Rewrite using `[h0, spectralValue_le_one_iff (minpoly.monic hi)]`. Prove the components needed by the constructor for the conclusion. Introduce `h n`.

Rewrite using `[minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]`. Conclude with `PadicInt.norm_le_one _`. Introduce `h`. Establish `hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l])` using `(Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩`. Take `⟨q, hq, -, hqm⟩` from `Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)`.

Conclude with `⟨q, hqm, by rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩`.
-/
private theorem int_iff (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

/- English proof (translation)
The claim follows from `(int_iff _).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map c.O.val)`.
-/
private theorem normO_le (a : c.O) : ‖algebraMap c.O (PadicAlgCl l) a‖ ≤ 1 :=
  (int_iff _).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map c.O.val)

/- English proof (translation)
Rewrite using `[Algebra.smul_def, norm_mul]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (normO_le a)`.
-/
private theorem norm_smul_le' (a : c.O) (z : PadicAlgCl l) : ‖a • z‖ ≤ ‖z‖ := by
  rw [Algebra.smul_def, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (normO_le a)

/- English proof (translation)
Take `⟨a, ha⟩` from `IsCO.res_surj (O := c.O) x`. Establish `e : f x = f (x - algebraMap c.O R a) + algebraMap c.O _ a`. Rewrite using `[map_sub, AlgHom.commutes, sub_add_cancel]`. Rewrite using `[e]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf _ ha).le (normO_le a))`.
-/
private theorem pt_le {f : R →ₐ[c.O] PadicAlgCl l} (hf : IsLocPt f) (x : R) : ‖f x‖ ≤ 1 := by
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := c.O) x
  have e : f x = f (x - algebraMap c.O R a) + algebraMap c.O _ a := by
    rw [map_sub, AlgHom.commutes, sub_add_cancel]
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf _ ha).le (normO_le a))

/- English proof (translation)
Use `Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)` and prove the remaining obligations. Rewrite using `[Ideal.radical_eq_sInf]`. Use `le_sInf ?_` and prove the remaining obligations. Introduce and unpack `q ⟨hq, hp⟩`. Establish `hk : RingHom.ker f ≤ q` using `hp.le_of_pow_le (le_sup_right.trans hq)`.

Establish `hl : (l : R) ∈ q` using `hq (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))`. Establish `hint : Algebra.IsIntegral c.O (R ⧸ RingHom.ker f)` using `⟨fun x => by`. Rewrite using `[← isIntegral_algHom_iff (Ideal.kerLiftAlg f) (Ideal.kerLiftAlg_injective f)]`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Conclude with `((int_iff _).2 (pt_le hf y)).tower_top⟩`.

Establish `hint2 : Algebra.IsIntegral c.O (R ⧸ q)` using `Algebra.IsIntegral.of_surjective (Ideal.Quotient.factorₐ c.O hk) (Ideal.Quotient.factor_surjective hk)`. Establish `hne : (⊥ : Ideal (R ⧸ q)).comap (algebraMap c.O (R ⧸ q)) ≠ ⊥`. Introduce `h0`. Establish `h1 : (l : c.O) ∈ (⊥ : Ideal (R ⧸ q)).comap (algebraMap c.O (R ⧸ q))`. Rewrite using `[Ideal.mem_comap, map_natCast, Ideal.mem_bot, ← map_natCast (Ideal.Quotient.mk q), Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `hl`. Rewrite `h1` using `[h0, Ideal.mem_bot]`. Conclude with `(Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h1`. Establish `hm : ((⊥ : Ideal (R ⧸ q)).comap (algebraMap c.O (R ⧸ q))).IsMaximal` using `Ideal.IsPrime.isMaximal inferInstance hne`. Establish `hb : (⊥ : Ideal (R ⧸ q)).IsMaximal` using `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ hm`.

Establish `hq' : q.IsMaximal`. Use `Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective (K := ⊥)` as an intermediate fact. Rewrite `this` using `[← RingHom.ker_eq_comap_bot, Ideal.mk_ker]`. Then use the resulting hypothesis. Conclude with `(eq_maximalIdeal hq').ge`.
-/
private theorem pow_le {f : R →ₐ[c.O] PadicAlgCl l} (hf : IsLocPt f) :
    ∃ n : ℕ, maximalIdeal R ^ n ≤ Ideal.span {(l : R)} ⊔ RingHom.ker f ^ 2 := by
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)
  rw [Ideal.radical_eq_sInf]
  refine le_sInf ?_
  rintro q ⟨hq, hp⟩
  have hk : RingHom.ker f ≤ q := hp.le_of_pow_le (le_sup_right.trans hq)
  have hl : (l : R) ∈ q := hq (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  have hint : Algebra.IsIntegral c.O (R ⧸ RingHom.ker f) := ⟨fun x => by
    rw [← isIntegral_algHom_iff (Ideal.kerLiftAlg f) (Ideal.kerLiftAlg_injective f)]
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ((int_iff _).2 (pt_le hf y)).tower_top⟩
  have hint2 : Algebra.IsIntegral c.O (R ⧸ q) :=
    Algebra.IsIntegral.of_surjective (Ideal.Quotient.factorₐ c.O hk) (Ideal.Quotient.factor_surjective hk)
  have hne : (⊥ : Ideal (R ⧸ q)).comap (algebraMap c.O (R ⧸ q)) ≠ ⊥ := by
    intro h0
    have h1 : (l : c.O) ∈ (⊥ : Ideal (R ⧸ q)).comap (algebraMap c.O (R ⧸ q)) := by
      rw [Ideal.mem_comap, map_natCast, Ideal.mem_bot, ← map_natCast (Ideal.Quotient.mk q),
        Ideal.Quotient.eq_zero_iff_mem]
      exact hl
    rw [h0, Ideal.mem_bot] at h1
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h1
  have hm : ((⊥ : Ideal (R ⧸ q)).comap (algebraMap c.O (R ⧸ q))).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance hne
  have hb : (⊥ : Ideal (R ⧸ q)).IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ hm
  have hq' : q.IsMaximal := by
    have := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective (K := ⊥)
    rwa [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at this
  exact (eq_maximalIdeal hq').ge

/- English proof (translation)
Take `⟨hc, hfin, hlm, -⟩` from `UpperTheory.V.abelian₂.dvr_finite l c.O`. Take `⟨n, hn⟩` from `pow_le hf`. Conclude with `fin_gen _ (l : c.O) hlm n (by rwa [map_natCast])`.
-/
private theorem fin_quot {f : R →ₐ[c.O] PadicAlgCl l} (hf : IsLocPt f) :
    Module.Finite c.O (R ⧸ (RingHom.ker f ^ 2).restrictScalars c.O) := by
  obtain ⟨hc, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  obtain ⟨n, hn⟩ := pow_le hf
  exact fin_gen _ (l : c.O) hlm n (by rwa [map_natCast])

/- English proof (translation)
Establish `h1 : Module.Finite c.O (R ⧸ (RingHom.ker f ^ 2).restrictScalars c.O)` using `fin_quot hf`. Take `⟨s, hs⟩` from `h1.fg_top`. Set `D'` to `Submodule.liftQ ((RingHom.ker f ^ 2).restrictScalars c.O) D fun y hy => LinearMap.mem_ker.2 (hD y ((Submodule.restrictScalars_mem _ _ _).1 hy))`. Take `⟨z, -, hz⟩` from `(insert 0 s).exists_max_image (fun z => ‖D' z‖) (Finset.insert_nonempty _ _)`. Take `⟨y₀, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`.

Use `⟨y₀, fun y => ?_⟩` and prove the remaining obligations. Establish `key : ∀ w ∈ Submodule.span c.O (s : Set (R ⧸ (RingHom.ker f ^ 2).restrictScalars c.O)), ‖D' w‖ ≤ ‖D y₀‖`. Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact hz x (Finset.mem_insert_of_mem hx)`.

Consider the case `zero => rw [map_zero, norm_zero]`. Conclude with `norm_nonneg _`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)`.

Consider the case `smul a x _ hx`. Rewrite using `[map_smul]`. Conclude with `(norm_smul_le' a _).trans hx`. Conclude with `key (Submodule.Quotient.mk y) (hs ▸ Submodule.mem_top)`.
-/
private theorem exists_max {f : R →ₐ[c.O] PadicAlgCl l} (hf : IsLocPt f) (D : R →ₗ[c.O] PadicAlgCl l)
    (hD : ∀ y ∈ RingHom.ker f ^ 2, D y = 0) : ∃ y₀, ∀ y, ‖D y‖ ≤ ‖D y₀‖ := by
  have h1 : Module.Finite c.O (R ⧸ (RingHom.ker f ^ 2).restrictScalars c.O) := fin_quot hf
  obtain ⟨s, hs⟩ := h1.fg_top
  let D' := Submodule.liftQ ((RingHom.ker f ^ 2).restrictScalars c.O) D fun y hy =>
    LinearMap.mem_ker.2 (hD y ((Submodule.restrictScalars_mem _ _ _).1 hy))
  classical
  obtain ⟨z, -, hz⟩ := (insert 0 s).exists_max_image (fun z => ‖D' z‖) (Finset.insert_nonempty _ _)
  obtain ⟨y₀, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  refine ⟨y₀, fun y => ?_⟩
  have key : ∀ w ∈ Submodule.span c.O (s : Set (R ⧸ (RingHom.ker f ^ 2).restrictScalars c.O)), ‖D' w‖ ≤ ‖D y₀‖ := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx => exact hz x (Finset.mem_insert_of_mem hx)
    | zero => rw [map_zero, norm_zero]; exact norm_nonneg _
    | add x y _ _ hx hy =>
      rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
    | smul a x _ hx =>
      rw [map_smul]
      exact (norm_smul_le' a _).trans hx
  exact key (Submodule.Quotient.mk y) (hs ▸ Submodule.mem_top)

/- English proof (translation)
Take `⟨y₀, h₀⟩` from `exists_max hf D hD`. Take `⟨n, hn⟩` from `pow_le hf`. Establish `hl : ‖(l : PadicAlgCl l)‖ < 1`. Establish `: (l : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l])` using `by simp`. Rewrite using `[this, norm_algebraMap']`.

Conclude with `Padic.norm_p_lt_one`. Establish `hpos : 0 < ‖D y₀‖ + 1` using `by positivity`. Take `⟨k, hk⟩` from `exists_pow_lt_of_lt_one (div_pos hε hpos) hl`. Use `⟨n * k, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hle : maximalIdeal R ^ (n * k) ≤ Ideal.span {(l : R) ^ k} ⊔ RingHom.ker f ^ 2`.

Rewrite using `[pow_mul, ← Ideal.span_singleton_pow]`. Conclude with `(Ideal.pow_right_mono hn k).trans (sup_pow_le _ _ _)`. Take `⟨u, hu, v, hv, rfl⟩` from `Submodule.mem_sup.1 (hle hy)`. Take `⟨w, rfl⟩` from `Ideal.mem_span_singleton'.1 hu`. Establish `e : w * (l : R) ^ k = ((l : c.O) ^ k) • w`.

Rewrite using `[Algebra.smul_def, map_pow, map_natCast, mul_comm]`. Rewrite using `[map_add, hD v hv, add_zero, e, map_smul, Algebra.smul_def, map_pow, map_natCast, norm_mul, norm_pow]`. Rewrite `hk` using `[lt_div_iff₀ hpos]`. Conclude with `lt_of_le_of_lt (mul_le_mul_of_nonneg_left ((h₀ w).trans (by linarith)) (by positivity)) hk`.
-/
private theorem small {f : R →ₐ[c.O] PadicAlgCl l} (hf : IsLocPt f) (D : R →ₗ[c.O] PadicAlgCl l)
    (hD : ∀ y ∈ RingHom.ker f ^ 2, D y = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ y ∈ maximalIdeal R ^ N, ‖D y‖ < ε := by
  obtain ⟨y₀, h₀⟩ := exists_max hf D hD
  obtain ⟨n, hn⟩ := pow_le hf
  have hl : ‖(l : PadicAlgCl l)‖ < 1 := by
    have : (l : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  have hpos : 0 < ‖D y₀‖ + 1 := by positivity
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hpos) hl
  refine ⟨n * k, fun y hy => ?_⟩
  have hle : maximalIdeal R ^ (n * k) ≤ Ideal.span {(l : R) ^ k} ⊔ RingHom.ker f ^ 2 := by
    rw [pow_mul, ← Ideal.span_singleton_pow]
    exact (Ideal.pow_right_mono hn k).trans (sup_pow_le _ _ _)
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 (hle hy)
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  have e : w * (l : R) ^ k = ((l : c.O) ^ k) • w := by
    rw [Algebra.smul_def, map_pow, map_natCast, mul_comm]
  rw [map_add, hD v hv, add_zero, e, map_smul, Algebra.smul_def, map_pow, map_natCast, norm_mul, norm_pow]
  rw [lt_div_iff₀ hpos] at hk
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left ((h₀ w).trans (by linarith)) (by positivity)) hk

/- English proof (translation)
Rewrite using `[Metric.continuous_iff']`. Introduce `x ε hε`. Take `⟨N, hN⟩` from `small hf D hD ε hε`. Use `filter_upwards [(hu N).eventually_eq x] with y hy`. Rewrite using `[dist_eq_norm, ← map_sub]`.

Conclude with `hN _ (Ideal.Quotient.eq.1 hy)`.
-/
private theorem cont_of {X : Type} [TopologicalSpace X] {f : R →ₐ[c.O] PadicAlgCl l} (hf : IsLocPt f)
    (D : R →ₗ[c.O] PadicAlgCl l) (hD : ∀ y ∈ RingHom.ker f ^ 2, D y = 0) {u : X → R}
    (hu : AdicCont (maximalIdeal R) u) : Continuous fun x => D (u x) := by
  rw [Metric.continuous_iff']
  intro x ε hε
  obtain ⟨N, hN⟩ := small hf D hD ε hε
  filter_upwards [(hu N).eventually_eq x] with y hy
  rw [dist_eq_norm, ← map_sub]
  exact hN _ (Ideal.Quotient.eq.1 hy)

end Fin

/- English proof (translation)
Assume the negation of the conclusion as `hT`. Establish `hO : ∀ a : O, algebraMap O U.R a ∈ T` using `fun a => by`. Rewrite using `[Algebra.algebraMap_eq_smul_one]`. Conclude with `T.smul_mem a h1`. Establish `htor : Module.IsTorsionBySet O (U.R ⧸ T) (maximalIdeal O)`.

Introduce and unpack `z ⟨a, ha⟩`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective T z`. Take `⟨b, hb⟩` from `IsCO.res_surj (O := O) x`. Use `show Submodule.Quotient.mk (a • x) = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`.

Establish `e : a • x = algebraMap O U.R a * (x - algebraMap O U.R b) + algebraMap O U.R (a * b)`. Rewrite using `[Algebra.smul_def, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `T.add_mem (h2 _ (map_nonunit (algebraMap O U.R) a ha) _ hb) (hO _)`.

Use `letI : Module (ResidueField O) (U.R ⧸ T) := htor.module`. Use `haveI : IsScalarTower O (ResidueField O) (U.R ⧸ T) := htor.isScalarTower`. Choose the witnesses or unpack the hypotheses as in `⟨x₀, hx₀⟩ : ∃ x₀, x₀ ∉ T := by`. Assume the negation of the conclusion as `h`. Conclude with `hT (eq_top_iff.2 fun x _ => by_contra fun hx => h ⟨x, hx⟩)`.

Take `⟨φ, hφ⟩` from `Module.Projective.exists_dual_ne_zero (ResidueField O) (x := (Submodule.Quotient.mk x₀ : U.R ⧸ T)) (by rwa [Ne, Submodule.Quotient.mk_eq_zero])`. Set `δ : U.R →ₗ[O] ResidueField O` to `(φ.restrictScalars O).comp T.mkQ`. Establish `hδ : ∀ x ∈ T, δ x = 0` using `fun x hx => by show φ (Submodule.Quotient.mk x) = 0`. Rewrite using `[(Submodule.Quotient.mk_eq_zero T).2 hx, map_zero]`. Establish `hmul : ∀ x y, δ (x * y) = res O U.R x * δ y + δ x * res O U.R y` using `fun x y => by`.

Take `⟨a, ha⟩` from `IsCO.res_surj (O := O) x`. Take `⟨b, hb⟩` from `IsCO.res_surj (O := O) y`. Establish `ra` using `(res_eq_zero_iff O U.R _).2 ha`. Establish `rb` using `(res_eq_zero_iff O U.R _).2 hb`. Rewrite `ra`, `rb` using `[map_sub, AlgHom.commutes, sub_eq_zero]`.

Establish `e : x * y = (x - algebraMap O U.R a) * (y - algebraMap O U.R b) + a • y + b • x - algebraMap O U.R (a * b)`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, map_sub, map_add, map_add, hδ _ (h2 _ ha _ hb), hδ _ (hO _), map_smul, map_smul, ra, rb, Algebra.smul_def, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree.

Use `haveI := (co_res O).2`. Set `F₀ : U.R →ₐ[O] DualNumber (ResidueField O)` to `(TrivSqZeroExt.inlAlgHom O _ _).comp (res O U.R)`. Apply the tactic sequence `let F₁ : U.R →ₐ[O] DualNumber (ResidueField O) := { toFun := fun x => TrivSqZeroExt.inl (res O U.R x) + TrivSqZeroExt.inr (δ x) map_one' := by ext <;> simp [hδ 1 h1] map_mul' := fun x y => by ext <;> simp [hmul] map_zero' := by ext <;> simp map_add' := fun x y => by ext <;> simp …`. Rewrite using `[hδ _ (hO a), AlgHom.commutes, TrivSqZeroExt.inr_zero, add_zero]`. Use `rfl }`.

Establish `hr : U.r.map F₁ = U.r.map F₀`. Use `GLift.ext (MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl)` and prove the remaining obligations. Use `ext1 a b`. Use `show TrivSqZeroExt.inl (res O U.R ((U.r.hom g).mat a b)) + TrivSqZeroExt.inr (δ ((U.r.hom g).mat a b)) = TrivSqZeroExt.inl (res O U.R ((U.r.hom g).mat a b))`. Rewrite using `[hδ _ (he g a b), TrivSqZeroExt.inr_zero, add_zero]`.

Take `⟨hP, hu⟩` from `U.rep (DualNumber (ResidueField O))`. Establish `hF : F₁ = F₀` using `(hu _ (hP F₀)).unique hr rfl`. Establish `h3` using `congrArg (fun F : U.R →ₐ[O] DualNumber (ResidueField O) => (F x₀).snd) hF`. Establish `h4 : δ x₀ = 0` using `by simpa [F₁, F₀] using h3`. Conclude with `hφ h4`.
-/
private theorem span_top {O Γ : Type} [CommRing O] [IsLocalRing O] [Group Γ] [TopologicalSpace Γ] {η : Γ →* ℤˣ}
    {Ψ : Γ →* Oˣ} {P : GCond O η Ψ} (U : Univ P) (T : Submodule O U.R) (h1 : (1 : U.R) ∈ T)
    (h2 : ∀ x ∈ maximalIdeal U.R, ∀ y ∈ maximalIdeal U.R, x * y ∈ T)
    (he : ∀ g a b, (U.r.hom g).mat a b ∈ T) : T = ⊤ := by
  by_contra hT
  have hO : ∀ a : O, algebraMap O U.R a ∈ T := fun a => by
    rw [Algebra.algebraMap_eq_smul_one]; exact T.smul_mem a h1
  have htor : Module.IsTorsionBySet O (U.R ⧸ T) (maximalIdeal O) := by
    rintro z ⟨a, ha⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective T z
    obtain ⟨b, hb⟩ := IsCO.res_surj (O := O) x
    show Submodule.Quotient.mk (a • x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    have e : a • x = algebraMap O U.R a * (x - algebraMap O U.R b) + algebraMap O U.R (a * b) := by
      rw [Algebra.smul_def, map_mul]; ring
    rw [e]
    exact T.add_mem (h2 _ (map_nonunit (algebraMap O U.R) a ha) _ hb) (hO _)
  letI : Module (ResidueField O) (U.R ⧸ T) := htor.module
  haveI : IsScalarTower O (ResidueField O) (U.R ⧸ T) := htor.isScalarTower
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ ∉ T := by
    by_contra h
    exact hT (eq_top_iff.2 fun x _ => by_contra fun hx => h ⟨x, hx⟩)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero (ResidueField O)
    (x := (Submodule.Quotient.mk x₀ : U.R ⧸ T)) (by rwa [Ne, Submodule.Quotient.mk_eq_zero])
  let δ : U.R →ₗ[O] ResidueField O := (φ.restrictScalars O).comp T.mkQ
  have hδ : ∀ x ∈ T, δ x = 0 := fun x hx => by
    show φ (Submodule.Quotient.mk x) = 0
    rw [(Submodule.Quotient.mk_eq_zero T).2 hx, map_zero]
  have hmul : ∀ x y, δ (x * y) = res O U.R x * δ y + δ x * res O U.R y := fun x y => by
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
    obtain ⟨b, hb⟩ := IsCO.res_surj (O := O) y
    have ra := (res_eq_zero_iff O U.R _).2 ha
    have rb := (res_eq_zero_iff O U.R _).2 hb
    rw [map_sub, AlgHom.commutes, sub_eq_zero] at ra rb
    have e : x * y = (x - algebraMap O U.R a) * (y - algebraMap O U.R b) + a • y + b • x -
        algebraMap O U.R (a * b) := by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]; ring
    rw [e, map_sub, map_add, map_add, hδ _ (h2 _ ha _ hb), hδ _ (hO _), map_smul, map_smul, ra, rb,
      Algebra.smul_def, Algebra.smul_def]
    ring
  haveI := (co_res O).2
  let F₀ : U.R →ₐ[O] DualNumber (ResidueField O) := (TrivSqZeroExt.inlAlgHom O _ _).comp (res O U.R)
  let F₁ : U.R →ₐ[O] DualNumber (ResidueField O) :=
    { toFun := fun x => TrivSqZeroExt.inl (res O U.R x) + TrivSqZeroExt.inr (δ x)
      map_one' := by ext <;> simp [hδ 1 h1]
      map_mul' := fun x y => by ext <;> simp [hmul]
      map_zero' := by ext <;> simp
      map_add' := fun x y => by ext <;> simp
      commutes' := fun a => by
        rw [hδ _ (hO a), AlgHom.commutes, TrivSqZeroExt.inr_zero, add_zero]
        rfl }
  have hr : U.r.map F₁ = U.r.map F₀ := by
    refine GLift.ext (MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl)
    ext1 a b
    show TrivSqZeroExt.inl (res O U.R ((U.r.hom g).mat a b)) + TrivSqZeroExt.inr (δ ((U.r.hom g).mat a b)) =
      TrivSqZeroExt.inl (res O U.R ((U.r.hom g).mat a b))
    rw [hδ _ (he g a b), TrivSqZeroExt.inr_zero, add_zero]
  obtain ⟨hP, hu⟩ := U.rep (DualNumber (ResidueField O))
  have hF : F₁ = F₀ := (hu _ (hP F₀)).unique hr rfl
  have h3 := congrArg (fun F : U.R →ₐ[O] DualNumber (ResidueField O) => (F x₀).snd) hF
  have h4 : δ x₀ = 0 := by simpa [F₁, F₀] using h3
  exact hφ h4

section Main

variable {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R]

/- English proof (translation)
Introduce `y hy` and use `by rw [pow_two] at hy refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) (fun a b ha hb => ?_) · rw [hD, (RingHom.mem_ker).1 ha, (RingHom.mem_ker).1 hb, zero_mul, zero_mul, add_zero] · rw [map_add, ha, hb, add_zero]`.
-/
private theorem der_sq {f : R →ₐ[c.O] PadicAlgCl l} (D : R →ₗ[c.O] PadicAlgCl l)
    (hD : ∀ x y, D (x * y) = f x * D y + f y * D x) : ∀ y ∈ RingHom.ker f ^ 2, D y = 0 := fun y hy => by
  rw [pow_two] at hy
  refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · rw [hD, (RingHom.mem_ker).1 ha, (RingHom.mem_ker).1 hb, zero_mul, zero_mul, add_zero]
  · rw [map_add, ha, hb, add_zero]

/- English proof (translation)
Establish `h1 : Continuous fun g => (r g).mat.map (sndL F)` using `continuous_matrix fun a b => cont_of hf (sndL F) (der_sq _ (sndL_mul F)) (hr a b)`. Establish `h2 : Continuous fun g => (r g).mat.map (dualFst F)` using `continuous_matrix fun a b => cont_of hf (dualFst F).toLinearMap (fun y hy => (RingHom.mem_ker (f := dualFst F)).1 (Ideal.pow_le_self two_ne_zero hy)) (hr a b)`. Establish `hdet : ∀ g, ((r g).mat.map (dualFst F)).det ≠ 0` using `fun g => (Matrix.isUnit_det_of_right_inverse (fst_mul_inv (dualFst F) (r g).left)).ne_zero`. Establish `e : tanCoc F r = fun g => (r g).mat.map (sndL F) * ((((r g).mat.map (dualFst F)).det)⁻¹ • ((r g).mat.map (dualFst F)).adjugate)`. Use function extensionality and compare the values at `g`.

Rewrite using `[← Ring.inverse_eq_inv', ← Matrix.inv_def, Matrix.inv_eq_right_inv (A := (r g).mat.map (dualFst F)) (fst_mul_inv (dualFst F) (r g).left)]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `h1.matrix_mul ((h2.matrix_det.inv₀ hdet).smul h2.matrix_adjugate)`.
-/
private theorem tan_cont {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsCO c.O R] (r : Γ →* GG 3 R)
    (hr : ∀ a b, AdicCont (maximalIdeal R) fun g => (r g).mat a b) (F : R →ₐ[c.O] DualNumber (PadicAlgCl l))
    (hf : IsLocPt (dualFst F)) : Continuous (tanCoc F r) := by
  have h1 : Continuous fun g => (r g).mat.map (sndL F) :=
    continuous_matrix fun a b => cont_of hf (sndL F) (der_sq _ (sndL_mul F)) (hr a b)
  have h2 : Continuous fun g => (r g).mat.map (dualFst F) :=
    continuous_matrix fun a b => cont_of hf (dualFst F).toLinearMap
      (fun y hy => (RingHom.mem_ker (f := dualFst F)).1 (Ideal.pow_le_self two_ne_zero hy)) (hr a b)
  have hdet : ∀ g, ((r g).mat.map (dualFst F)).det ≠ 0 := fun g =>
    (Matrix.isUnit_det_of_right_inverse (fst_mul_inv (dualFst F) (r g).left)).ne_zero
  have e : tanCoc F r = fun g => (r g).mat.map (sndL F) *
      ((((r g).mat.map (dualFst F)).det)⁻¹ • ((r g).mat.map (dualFst F)).adjugate) := by
    funext g
    rw [← Ring.inverse_eq_inv', ← Matrix.inv_def,
      Matrix.inv_eq_right_inv (A := (r g).mat.map (dualFst F)) (fst_mul_inv (dualFst F) (r g).left)]
    rfl
  rw [e]
  exact h1.matrix_mul ((h2.matrix_det.inv₀ hdet).smul h2.matrix_adjugate)

/- English proof (translation)
Take `⟨y₀, h₀⟩` from `exists_max hf D (der_sq D hD)`. Assume the negation of the conclusion as `hy`. Establish `hpos : 0 < ‖D y₀‖` using `(norm_pos_iff.2 hy).trans_le (h₀ y)`. Set `T : Submodule c.O U.R` to `{ carrier := {x | ‖D x‖ < ‖D y₀‖} add_mem' := fun {a b} ha hb => by show ‖D (a + b)‖ < _`. Rewrite using `[map_add]`.

Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)`. Use the proof step `zero_mem' := by show ‖D 0‖ < _`. Rewrite using `[map_zero, norm_zero]` and apply the resulting hypothesis. Use the proof step `smul_mem' := fun a x hx => by show ‖D (a • x)‖ < _`. Rewrite using `[map_smul]`.

Conclude with `(norm_smul_le' a _).trans_lt hx }`. Establish `hlt : ∀ x ∈ maximalIdeal U.R, ∀ z, ‖f x * D z‖ < ‖D y₀‖` using `fun x hx z => by`. Rewrite using `[norm_mul]`. Conclude with `(mul_le_mul_of_nonneg_left (h₀ z) (norm_nonneg _)).trans_lt (mul_lt_of_lt_one_left hpos (hf x hx))`. Establish `hT : T = ⊤`.

Use `span_top U T ?_ (fun x hx z hz => ?_) (fun g a b => ?_)` and prove the remaining obligations. Use `show ‖D 1‖ < _`. Establish `h1` using `hD 1 1`. Rewrite `h1` using `[mul_one, map_one f, one_mul]`. Rewrite using `[left_eq_add.1 h1, norm_zero]` and apply the resulting hypothesis.

Use `show ‖D (x * z)‖ < _`. Rewrite using `[hD]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hlt x hx z) (hlt z hz x))`. Use `show ‖D _‖ < _`. Rewrite using `[he, norm_zero]` and apply the resulting hypothesis.

Establish `: y₀ ∈ T` using `hT ▸ Submodule.mem_top`. Conclude with `lt_irrefl _ (show ‖D y₀‖ < ‖D y₀‖ from this)`.
-/
private theorem der_zero {Γ : Type} [Group Γ] [TopologicalSpace Γ] {η : Γ →* ℤˣ} {Ψ : Γ →* (c.O)ˣ}
    {P : GCond c.O η Ψ} (U : Univ P) {f : U.R →ₐ[c.O] PadicAlgCl l} (hf : IsLocPt f)
    (D : U.R →ₗ[c.O] PadicAlgCl l) (hD : ∀ x y, D (x * y) = f x * D y + f y * D x)
    (he : ∀ g a b, D ((U.r.hom g).mat a b) = 0) (y : U.R) : D y = 0 := by
  obtain ⟨y₀, h₀⟩ := exists_max hf D (der_sq D hD)
  by_contra hy
  have hpos : 0 < ‖D y₀‖ := (norm_pos_iff.2 hy).trans_le (h₀ y)
  let T : Submodule c.O U.R :=
    { carrier := {x | ‖D x‖ < ‖D y₀‖}
      add_mem' := fun {a b} ha hb => by
        show ‖D (a + b)‖ < _
        rw [map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
      zero_mem' := by
        show ‖D 0‖ < _
        rwa [map_zero, norm_zero]
      smul_mem' := fun a x hx => by
        show ‖D (a • x)‖ < _
        rw [map_smul]
        exact (norm_smul_le' a _).trans_lt hx }
  have hlt : ∀ x ∈ maximalIdeal U.R, ∀ z, ‖f x * D z‖ < ‖D y₀‖ := fun x hx z => by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (h₀ z) (norm_nonneg _)).trans_lt (mul_lt_of_lt_one_left hpos (hf x hx))
  have hT : T = ⊤ := by
    refine span_top U T ?_ (fun x hx z hz => ?_) (fun g a b => ?_)
    · show ‖D 1‖ < _
      have h1 := hD 1 1
      rw [mul_one, map_one f, one_mul] at h1
      rwa [left_eq_add.1 h1, norm_zero]
    · show ‖D (x * z)‖ < _
      rw [hD]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hlt x hx z) (hlt z hz x))
    · show ‖D _‖ < _
      rwa [he, norm_zero]
  have : y₀ ∈ T := hT ▸ Submodule.mem_top
  exact lt_irrefl _ (show ‖D y₀‖ < ‖D y₀‖ from this)

end Main

/- English proof (translation)
Introduce `l _ c Γ H _ _ _ _ _ _ η Ψ N ι hι U I cc g₁ S _ _ _ F hf`. Establish `hS : NormCond cc g₁ (BoxCond N ι hι U I) S.R S.r` using `(S.rep S.R).1 (AlgHom.id _ _)`. Use `⟨tan_isCoc F _, tan_norm F _ _ _ hS.1, fun g hg => tan_zero F _ g ?_, tan_cont _ S.r.cont F hf, fun F' hF' a a' h y => ?_⟩` and prove the remaining obligations. Rewrite using `[hS.2.1 g hg]`. Both sides reduce to the same expression.

Use `der_zero S hf (a • sndL F + a' • sndL F') (fun x z => ?_) (fun g i j => ?_) y` and prove the remaining obligations. Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]`. Rewrite using `[sndL_mul F, sndL_mul F', hF']`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `congrArg (· * (push (dualFst F) S.r.hom g).mat) (congrFun h g)`.

Establish `h2` using `tan_mul F' S.r.hom g`. Rewrite `h2` using `[hF']`. Simplify using `only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, Matrix.add_mul, Matrix.smul_mul, Matrix.zero_mul] at h1`. Rewrite `h1` using `[tan_mul F, h2]`. Conclude with `congrFun (congrFun h1 i) j`.
-/
theorem UpperTheory.V.U3.tanCoc_determines :
    ∀ {l : ℕ} [Fact l.Prime] {c : Coef l} {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      {η : Γ →* ℤˣ} {Ψ : Γ →* (c.O)ˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
      {U : Univ (GCond.noCondition c.O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {cc g₁ : Γ} (S : SRing N hι U I cc g₁) (M : Model S (PadicAlgCl l)), l ≠ 2 → Marks η Ψ cc g₁ →
      ∀ F : S.R →ₐ[c.O] DualNumber (PadicAlgCl l), IsLocPt (dualFst F) →
        IsCoc (push (dualFst F) S.r.hom) (tanCoc F S.r.hom) ∧ NormCoc cc g₁ (push (dualFst F) S.r.hom) (tanCoc F S.r.hom) ∧
        (∀ g ∈ N, tanCoc F S.r.hom g = 0) ∧ Continuous (tanCoc F S.r.hom) ∧
        ∀ F' : S.R →ₐ[c.O] DualNumber (PadicAlgCl l), dualFst F' = dualFst F → ∀ a a' : PadicAlgCl l,
          a • tanCoc F S.r.hom + a' • tanCoc F' S.r.hom = 0 → ∀ y, a * (F y).snd + a' * (F' y).snd = 0 := by
  intro l _ c Γ H _ _ _ _ _ _ η Ψ N ι hι U I cc g₁ S _ _ _ F hf
  have hS : NormCond cc g₁ (BoxCond N ι hι U I) S.R S.r := (S.rep S.R).1 (AlgHom.id _ _)
  refine ⟨tan_isCoc F _, tan_norm F _ _ _ hS.1, fun g hg => tan_zero F _ g ?_, tan_cont _ S.r.cont F hf,
    fun F' hF' a a' h y => ?_⟩
  · rw [hS.2.1 g hg]
    rfl
  · refine der_zero S hf (a • sndL F + a' • sndL F') (fun x z => ?_) (fun g i j => ?_) y
    · simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [sndL_mul F, sndL_mul F', hF']
      ring
    · have h1 := congrArg (· * (push (dualFst F) S.r.hom g).mat) (congrFun h g)
      have h2 := tan_mul F' S.r.hom g
      rw [hF'] at h2
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, Matrix.add_mul, Matrix.smul_mul, Matrix.zero_mul] at h1
      rw [tan_mul F, h2] at h1
      exact congrFun (congrFun h1 i) j

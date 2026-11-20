import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExtReal
open UpperTheory.V.Af UpperTheory.V.Af.Gu
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.GalOfCusp

/- English proof (translation)
Unfold `infDiag`. Rewrite using `[MonoidHom.finsetProd_apply, Units.coe_prod]`. Set `ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L` to `MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)`. Express the relevant statement in the definitionally equal form `∏ w : InfinitePlace L, ι (Pi.mulSingle w (algebraMap L w.Completion k)) = ι (fun w => algebraMap L w.Completion k)`. Rewrite using `[← map_prod, Finset.univ_prod_mulSingle]`.
-/
private theorem eta_val (L : Type) [Field L] [NumberField L] (k : Lˣ) :
    ((infDiag k : Ideles L) : AdeleRing (𝓞 L) L) = (algebraMap L (InfiniteAdeleRing L) k, 1) := by
  classical
  unfold infDiag
  rw [MonoidHom.finsetProd_apply, Units.coe_prod]
  let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
    MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
  change ∏ w : InfinitePlace L, ι (Pi.mulSingle w (algebraMap L w.Completion k)) =
    ι (fun w => algebraMap L w.Completion k)
  rw [← map_prod, Finset.univ_prod_mulSingle]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap K L ((infDiag x : Ideles K) : AdeleRing (𝓞 K) K) = _`. Rewrite using `[eta_val, eta_val]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Establish `h` using `congrArg Prod.fst (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap K L (x : K))`.

Conclude with `h`. Conclude with `map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap K L)`.
-/
private theorem eta_map (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (x : Kˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap K L (infDiag x) = infDiag (Units.map (algebraMap K L).toMonoidHom x) := by
  apply Units.ext
  change GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap K L ((infDiag x : Ideles K) : AdeleRing (𝓞 K) K) = _
  rw [eta_val, eta_val]
  refine Prod.ext ?_ ?_
  · have h := congrArg Prod.fst (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap K L (x : K))
    exact h
  · exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap K L)

/- English proof (translation)
Establish `hv : v.IsReal` using `IsTotallyReal.isReal v`. Set `e` to `InfinitePlace.Completion.ringEquivRealOfIsReal hv`. Establish `he : e (algebraMap _ v.Completion (k : F)) = InfinitePlace.embedding_of_isReal hv k` using `InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hv ((WithAbs.equiv v.1).symm (k : F))`. Establish `hsq : ∀ x : (v.Completion)ˣ, 0 < e x → χ.locInf v x = 1` using `fun x hx => by`. Establish `h0 : e.symm (Real.sqrt (e x)) ≠ 0`.

Rewrite using `[map_ne_zero]`. Conclude with `(Real.sqrt_pos.2 hx).ne'`. Establish `e1 : x = Units.mk0 _ h0 ^ 2` using `Units.ext (e.injective (by`. Rewrite using `[Units.val_pow_eq_pow_val, map_pow, Units.val_mk0, e.apply_symm_apply, Real.sq_sqrt hx.le]))`. Rewrite using `[e1, map_pow]`.

Conclude with `h2 _`. Establish `h0 : InfinitePlace.embedding_of_isReal hv k ≠ 0` using `(map_ne_zero _).2 k.ne_zero`. Rewrite using `[← InfinitePlace.embedding_of_isReal_apply hv, Complex.norm_real, Real.norm_eq_abs]`. Break down `lt_or_gt_of_ne h0 with h | h` into its components or cases. Establish `e1 : atInf v k = -1 * -atInf v k` using `by simp`.

Rewrite using `[e1, map_mul, hs, hsq _ (by`. Rewrite using `[Units.val_neg, map_neg]`. Conclude with `neg_pos.2 (he ▸ h)), abs_of_neg h]`. Simplify using the standard rewrite rules. Rewrite using `[hsq _ (he ▸ h), abs_of_pos h]`.

Simplify using the standard rewrite rules.
-/
private theorem eta_loc {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (χ : HChar F) (h2 : ∀ x, χ.1 x ^ 2 = 1)
    (v : InfinitePlace F) (hs : χ.locInf v (-1) = -1) (k : Fˣ) :
    ((χ.locInf v (atInf v k) : ℂˣ) : ℂ) * ((‖v.embedding (k : F)‖ : ℝ) : ℂ) = v.embedding (k : F) := by
  have hv : v.IsReal := IsTotallyReal.isReal v
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hv
  have he : e (algebraMap _ v.Completion (k : F)) = InfinitePlace.embedding_of_isReal hv k :=
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hv ((WithAbs.equiv v.1).symm (k : F))
  have hsq : ∀ x : (v.Completion)ˣ, 0 < e x → χ.locInf v x = 1 := fun x hx => by
    have h0 : e.symm (Real.sqrt (e x)) ≠ 0 := by
      rw [map_ne_zero]
      exact (Real.sqrt_pos.2 hx).ne'
    have e1 : x = Units.mk0 _ h0 ^ 2 := Units.ext (e.injective (by
      rw [Units.val_pow_eq_pow_val, map_pow, Units.val_mk0, e.apply_symm_apply, Real.sq_sqrt hx.le]))
    rw [e1, map_pow]
    exact h2 _
  have h0 : InfinitePlace.embedding_of_isReal hv k ≠ 0 := (map_ne_zero _).2 k.ne_zero
  rw [← InfinitePlace.embedding_of_isReal_apply hv, Complex.norm_real, Real.norm_eq_abs]
  rcases lt_or_gt_of_ne h0 with h | h
  · have e1 : atInf v k = -1 * -atInf v k := by simp
    rw [e1, map_mul, hs, hsq _ (by
      rw [Units.val_neg, map_neg]
      exact neg_pos.2 (he ▸ h)), abs_of_neg h]
    simp
  · rw [hsq _ (he ▸ h), abs_of_pos h]
    simp

/- English proof (translation)
Establish `hb : Function.Bijective fun v : InfinitePlace F => v.embedding` using `⟨InfinitePlace.embedding_injective F, fun φ => ⟨InfinitePlace.mk φ, InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal φ)⟩⟩`. Establish `e1 : χ.inf k = ∏ v : InfinitePlace F, χ.locInf v (atInf v k)`. Unfold `HChar.inf HChar.locInf infDiag`. Rewrite using `[MonoidHom.comp_apply, MonoidHom.finsetProd_apply, map_prod]`. Both sides reduce to the same expression.

Rewrite using `[← hb.prod_comp fun φ => φ (k : F), e1, Units.coe_prod, norm_prod, Complex.ofReal_prod, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun v _ => eta_loc χ h2 v (hs v) k`.
-/
private theorem eta_inf {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (χ : HChar F) (h2 : ∀ x, χ.1 x ^ 2 = 1)
    (hs : ∀ v, χ.locInf v (-1) = -1) (k : Fˣ) :
    ((χ.inf k : ℂˣ) : ℂ) * ((‖∏ φ : F →+* ℂ, φ (k : F)‖ : ℝ) : ℂ) = ∏ φ : F →+* ℂ, φ (k : F) := by
  have hb : Function.Bijective fun v : InfinitePlace F => v.embedding :=
    ⟨InfinitePlace.embedding_injective F, fun φ =>
      ⟨InfinitePlace.mk φ, InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal φ)⟩⟩
  have e1 : χ.inf k = ∏ v : InfinitePlace F, χ.locInf v (atInf v k) := by
    unfold HChar.inf HChar.locInf infDiag
    rw [MonoidHom.comp_apply, MonoidHom.finsetProd_apply, map_prod]
    rfl
  rw [← hb.prod_comp fun φ => φ (k : F), e1, Units.coe_prod, norm_prod, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ => eta_loc χ h2 v (hs v) k

/- English proof (translation)
Establish `h` using `Algebra.norm_eq_prod_embeddings ℚ ℂ k`. Rewrite `h` using `[← Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => φ k) (fun σ : E →ₐ[ℚ] ℂ => σ k) (fun _ => rfl)]`. Rewrite using `[← h]`. Simplify using the standard rewrite rules.
-/
private theorem eta_norm (E : Type) [Field E] [NumberField E] (k : E) :
    ∏ φ : E →+* ℂ, φ k = ((Algebra.norm ℚ k : ℚ) : ℂ) := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ k
  rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => φ k)
    (fun σ : E →ₐ[ℚ] ℂ => σ k) (fun _ => rfl)] at h
  rw [← h]; simp

/- English proof (translation)
Establish `e1 : (GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2))).inf k = (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2)).inf (Units.map (algebraMap (maximalRealSubfield E) E).toMonoidHom k)` using `congrArg (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2)).1 (eta_map _ E k)`. Rewrite using `[e1, (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E _).2.2]`. Simplify using `only [← Complex.ofReal_cpow (norm_nonneg _)]`. Rewrite using `[← Complex.ofReal_prod, Real.finsetProd_rpow _ _ fun _ _ => norm_nonneg _, ← norm_prod, eta_norm, eta_norm]`. Establish `e2 : Algebra.norm ℚ ((Units.map (algebraMap (maximalRealSubfield E) E).toMonoidHom k : Eˣ) : E) = Algebra.norm ℚ (k : maximalRealSubfield E) ^ 2`.

Express the relevant statement in the definitionally equal form `Algebra.norm ℚ (algebraMap (maximalRealSubfield E) E k) = _`. Rewrite using `[← Algebra.norm_norm (S := maximalRealSubfield E), Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two, map_pow]`. Rewrite using `[e2, Rat.cast_pow, norm_pow, ← Complex.ofReal_zpow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_intCast]`. Use `congr 2`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem eta_abs (E : Type) [Field E] [NumberField E] [IsCMField E] (f : ℤ) (k : (maximalRealSubfield E)ˣ) :
    (((GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2))).inf k : ℂˣ) : ℂ) =
      ((‖∏ φ : maximalRealSubfield E →+* ℂ, φ (k : maximalRealSubfield E)‖ : ℝ) : ℂ) ^ f := by
  have e1 : (GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2))).inf k =
      (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2)).inf (Units.map (algebraMap (maximalRealSubfield E) E).toMonoidHom k) :=
    congrArg (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2)).1 (eta_map _ E k)
  rw [e1, (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E _).2.2]
  simp only [← Complex.ofReal_cpow (norm_nonneg _)]
  rw [← Complex.ofReal_prod, Real.finsetProd_rpow _ _ fun _ _ => norm_nonneg _, ← norm_prod, eta_norm, eta_norm]
  have e2 : Algebra.norm ℚ ((Units.map (algebraMap (maximalRealSubfield E) E).toMonoidHom k : Eˣ) : E) =
      Algebra.norm ℚ (k : maximalRealSubfield E) ^ 2 := by
    change Algebra.norm ℚ (algebraMap (maximalRealSubfield E) E k) = _
    rw [← Algebra.norm_norm (S := maximalRealSubfield E), Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two,
      map_pow]
  rw [e2, Rat.cast_pow, norm_pow, ← Complex.ofReal_zpow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
    ← Real.rpow_intCast]
  congr 2
  push_cast
  ring

/- English proof (translation)
Introduce `E _ _ _ f`. Establish `hq : ∀ x, (quadChar E).1 x ^ 2 = 1` using `fun x => by`. Express the relevant statement in the definitionally equal form `(Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E x)) ^ 2 = 1`. Rewrite using `[← map_pow, Int.units_sq, map_one]`. Take `⟨ξ, m, hm, hξ⟩` from `Cq.extReal E (GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2)) * quadChar E ^ f)⁻¹ (-f) fun k => by`.

Establish `e : (quadChar E ^ f).inf k = (quadChar E).inf k ^ f` using `rfl`. Rewrite using `[HChar.inf_inv, HChar.inf_mul, Units.val_inv_eq_inv_val, Units.val_mul, eta_abs, e, Units.val_zpow_eq_zpow_val, ← mul_zpow, mul_comm, eta_inf _ hq (quadChar_locInf E), Finset.prod_zpow, zpow_neg]`. Use `⟨ξ, m, hm, ?_⟩` and prove the remaining obligations. Establish `e : GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2) * ξ) = GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2)) * GlobalTheory.HeightCounting.Blocks.resReal ξ` using `rfl`. Rewrite using `[e, hξ, mul_inv, mul_inv_cancel_left, map_inv, map_zpow, compNorm_quadChar, one_zpow, inv_one]`.
-/
theorem UpperTheory.eta_condition :
    Eta := by
  intro E _ _ _ f
  have hq : ∀ x, (quadChar E).1 x ^ 2 = 1 := fun x => by
    change (Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E x)) ^ 2 = 1
    rw [← map_pow, Int.units_sq, map_one]
  obtain ⟨ξ, m, hm, hξ⟩ := Cq.extReal E
    (GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2)) * quadChar E ^ f)⁻¹ (-f) fun k => by
      have e : (quadChar E ^ f).inf k = (quadChar E).inf k ^ f := rfl
      rw [HChar.inf_inv, HChar.inf_mul, Units.val_inv_eq_inv_val, Units.val_mul, eta_abs, e, Units.val_zpow_eq_zpow_val,
        ← mul_zpow, mul_comm, eta_inf _ hq (quadChar_locInf E), Finset.prod_zpow, zpow_neg]
  refine ⟨ξ, m, hm, ?_⟩
  have e : GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2) * ξ) =
      GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2)) * GlobalTheory.HeightCounting.Blocks.resReal ξ := rfl
  rw [e, hξ, mul_inv, mul_inv_cancel_left, map_inv, map_zpow, compNorm_quadChar, one_zpow, inv_one]

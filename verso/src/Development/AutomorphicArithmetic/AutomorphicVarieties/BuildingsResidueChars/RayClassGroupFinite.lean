import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.PerDeriv
import GroundTheory.AutomorphicForms.ReductionDirichlet
import GroundTheory.AutomorphicForms.ReductionIdele
open UpperTheory.V.Sd.Eis
open NumberField IsDedekindDomain Topology Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V

/- English proof (translation)
Establish `h : ∀ x, TR.pInf F (TR.sInf F x) = x` using `fun x => (TR.infEq F).symm_apply_apply x`. Establish `h2 : ∀ x, TR.pInf F (sFin F x) = 0` using `fun x => map_zero (TR.infEq F).symm`. Establish `h3 : ∀ x, pFin F (TR.sInf F x) = 0` using `fun x => rfl`. Establish `h4 : ∀ x, pFin F (sFin F x) = x` using `fun x => rfl`. Use `Units.ext (TR.ad_ext ?_ ?_)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `TR.pInf F ((1 - TR.sInf F 1 + TR.sInf F (TR.pInf F x.val)) * (1 - sFin F 1 + sFin F (pFin F x.val))) = _`. Simplify using `[h, h2]`. Express the relevant statement in the definitionally equal form `pFin F ((1 - TR.sInf F 1 + TR.sInf F (TR.pInf F x.val)) * (1 - sFin F 1 + sFin F (pFin F x.val))) = _`. Simplify using `[h3, h4]`.
-/
private theorem idele_split (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (x : Ideles F) :
    TR.infId F (Units.map (TR.pInf F).toMonoidHom x) * finId F (Units.map (pFin F).toMonoidHom x) = x := by
  have h : ∀ x, TR.pInf F (TR.sInf F x) = x := fun x => (TR.infEq F).symm_apply_apply x
  have h2 : ∀ x, TR.pInf F (sFin F x) = 0 := fun x => map_zero (TR.infEq F).symm
  have h3 : ∀ x, pFin F (TR.sInf F x) = 0 := fun x => rfl
  have h4 : ∀ x, pFin F (sFin F x) = x := fun x => rfl
  refine Units.ext (TR.ad_ext ?_ ?_)
  · change TR.pInf F ((1 - TR.sInf F 1 + TR.sInf F (TR.pInf F x.val)) * (1 - sFin F 1 + sFin F (pFin F x.val))) = _
    simp [h, h2]
  · change pFin F ((1 - TR.sInf F 1 + TR.sInf F (TR.pInf F x.val)) * (1 - sFin F 1 + sFin F (pFin F x.val))) = _
    simp [h3, h4]

/- English proof (translation)
The claim follows from `(InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).continuous.comp ((continuous_apply v).comp continuous_fst)`.
-/
private theorem cont_pInf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) :
    Continuous fun x : Ad F => TR.pInf F x v :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).continuous.comp
    ((continuous_apply v).comp continuous_fst)

open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic.Reduction in
/- English proof (translation)
Introduce `F _ _ _ H hK hR hf`. Establish `hopen : IsOpen (H : Set (Ideles F))`. Apply `H.isOpen_of_mem_nhds (g := 1)` to reduce the goal to its premises. Establish `c1 : Continuous (Units.map (pFin F).toMonoidHom : Ideles F → (Af F)ˣ)` using `Continuous.units_map _ continuous_snd`. Establish `h1 : ∀ᶠ x : Ideles F in 𝓝 1, finId F (Units.map (pFin F).toMonoidHom x) ∈ H`.

Use `c1.continuousAt (x := 1)` as an intermediate fact. Rewrite `this` using `[ContinuousAt, map_one]`. Conclude with `this hf`. Establish `h2 : ∀ᶠ x : Ideles F in 𝓝 1, ∀ v, 0 < TR.pInf F x.val v`. Rewrite using `[Filter.eventually_all]`.

Introduce `v`. Establish `c : Continuous fun x : Ideles F => TR.pInf F x.val v` using `(cont_pInf F v).comp Units.continuous_val`. Use `c.continuousAt.eventually (lt_mem_nhds ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules. Use `filter_upwards [h1, h2] with x hx1 hx2`.

Rewrite using `[← idele_split F x]`. Conclude with `H.mul_mem (hR _ hx2) hx1`. Use `⟨hopen, ?_⟩` and prove the remaining obligations. Establish `hsq : ∀ (ρ : ℝ) (hρ : 0 < ρ), ((posIdele ρ hρ : IdeleGroup F) : Ideles F) ^ 2 ∈ H`. Introduce `ρ hρ`.

Use `set z : Ideles F := (posIdele ρ hρ : IdeleGroup F) with hz`. Establish `e : Units.map (pFin F).toMonoidHom z = 1`. Use `Units.ext ?_` and prove the remaining obligations. Use extensionality with `v`. Conclude with `congrArg _ (posIdele_finite ρ hρ v)`.

Establish `e2` using `idele_split F z`. Rewrite `e2` using `[e, map_one, mul_one]`. Rewrite using `[← e2, ← map_pow]`. Use `hR _ fun v => ?_` and prove the remaining obligations. Use `set y := Units.map (TR.pInf F).toMonoidHom z`.

Establish `hy : y.val v ≠ 0`. Use `congrFun y.mul_inv v` as an intermediate fact. Conclude with `left_ne_zero_of_mul_eq_one this`. Rewrite using `[Units.val_pow_eq_pow_val, Pi.pow_apply]`. Check the signs of the components of the expression.

Take `⟨S, hS, hSm⟩` from `exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := F) one_pos 1`. Establish `hcov : ∀ t : Ideles F, ∃ s ∈ S, s⁻¹ * t ∈ H`. Introduce `t`. Establish `hn : 2 * Module.finrank ℚ F ≠ 0` using `mul_ne_zero two_ne_zero Module.finrank_pos.ne'`. Establish `ht : 0 < (ideleModule F t : ℝ)` using `(ideleModule F t).2`.

Use `set ρ : ℝ := (ideleModule F t : ℝ) ^ (((2 * Module.finrank ℚ F : ℕ) : ℝ)⁻¹) with hρdef`. Establish `hρ : 0 < ρ` using `Real.rpow_pos_of_pos ht _`. Establish `hρn : ρ ^ (2 * Module.finrank ℚ F) = (ideleModule F t : ℝ)` using `Real.rpow_inv_natCast_pow ht.le hn`. Establish `hzH` using `hsq ρ hρ`. Establish `hzt : ideleModule F (posIdele ρ hρ ^ 2) = ideleModule F t`.

Use `Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[sq, map_mul, ← hρn, two_mul, pow_add, ← ideleModule_posIdele ρ hρ]`. Both sides reduce to the same expression. Generalize the expression as in `(posIdele ρ hρ : IdeleGroup F) ^ 2 = z at hzH hzt`. Establish `h1 : (ideleModule F (t * z⁻¹) : ℝ) = 1`.

Rewrite using `[map_mul, map_inv, hzt, mul_inv_cancel]`. Both sides reduce to the same expression. Take `⟨c, hcS⟩` from `hSm (t * z⁻¹) h1.ge h1.le`. Use `⟨_, hcS, ?_⟩` and prove the remaining obligations. Establish `e : (diagonal F c * (t * z⁻¹))⁻¹ * t = z * (diagonal F c)⁻¹`.

Rewrite using `[mul_inv, mul_inv, inv_inv, mul_assoc, mul_right_comm, inv_mul_cancel, one_mul, mul_comm]`. Rewrite using `[e]`. Conclude with `H.mul_mem hzH (H.inv_mem (hK c))`. Use `haveI : DiscreteTopology (Ideles F ⧸ H) := QuotientGroup.discreteTopology hopen`. Establish `hfin : ((QuotientGroup.mk : Ideles F → Ideles F ⧸ H) '' S).Finite` using `(hS.image QuotientGroup.continuous_mk).finite_of_discrete`.

Use `haveI : Finite (Ideles F ⧸ H) := by`. Use `Set.finite_univ_iff.1 (hfin.subset fun q _ => ?_)` and prove the remaining obligations. Take `⟨t, rfl⟩` from `QuotientGroup.mk_surjective q`. Take `⟨s, hs, hst⟩` from `hcov t`. Conclude with `⟨s, hs, QuotientGroup.eq.2 hst⟩`.

Conclude with `Subgroup.finiteIndex_of_finite_quotient`.
-/
theorem UpperTheory.ray_class_group_finite :
    UpperTheory.V.Sd.Eis.RayFin := by
  intro F _ _ _ H hK hR hf
  have hopen : IsOpen (H : Set (Ideles F)) := by
    apply H.isOpen_of_mem_nhds (g := 1)
    have c1 : Continuous (Units.map (pFin F).toMonoidHom : Ideles F → (Af F)ˣ) :=
      Continuous.units_map _ continuous_snd
    have h1 : ∀ᶠ x : Ideles F in 𝓝 1, finId F (Units.map (pFin F).toMonoidHom x) ∈ H := by
      have := c1.continuousAt (x := 1)
      rw [ContinuousAt, map_one] at this
      exact this hf
    have h2 : ∀ᶠ x : Ideles F in 𝓝 1, ∀ v, 0 < TR.pInf F x.val v := by
      rw [Filter.eventually_all]
      intro v
      have c : Continuous fun x : Ideles F => TR.pInf F x.val v := (cont_pInf F v).comp Units.continuous_val
      refine c.continuousAt.eventually (lt_mem_nhds ?_)
      simp
    filter_upwards [h1, h2] with x hx1 hx2
    rw [← idele_split F x]
    exact H.mul_mem (hR _ hx2) hx1
  refine ⟨hopen, ?_⟩
  have hsq : ∀ (ρ : ℝ) (hρ : 0 < ρ), ((posIdele ρ hρ : IdeleGroup F) : Ideles F) ^ 2 ∈ H := by
    intro ρ hρ
    set z : Ideles F := (posIdele ρ hρ : IdeleGroup F) with hz
    have e : Units.map (pFin F).toMonoidHom z = 1 := by
      refine Units.ext ?_
      ext v
      exact congrArg _ (posIdele_finite ρ hρ v)
    have e2 := idele_split F z
    rw [e, map_one, mul_one] at e2
    rw [← e2, ← map_pow]
    refine hR _ fun v => ?_
    set y := Units.map (TR.pInf F).toMonoidHom z
    have hy : y.val v ≠ 0 := by
      have := congrFun y.mul_inv v
      exact left_ne_zero_of_mul_eq_one this
    rw [Units.val_pow_eq_pow_val, Pi.pow_apply]
    positivity
  obtain ⟨S, hS, hSm⟩ := exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := F) one_pos 1
  have hcov : ∀ t : Ideles F, ∃ s ∈ S, s⁻¹ * t ∈ H := by
    intro t
    have hn : 2 * Module.finrank ℚ F ≠ 0 := mul_ne_zero two_ne_zero Module.finrank_pos.ne'
    have ht : 0 < (ideleModule F t : ℝ) := (ideleModule F t).2
    set ρ : ℝ := (ideleModule F t : ℝ) ^ (((2 * Module.finrank ℚ F : ℕ) : ℝ)⁻¹) with hρdef
    have hρ : 0 < ρ := Real.rpow_pos_of_pos ht _
    have hρn : ρ ^ (2 * Module.finrank ℚ F) = (ideleModule F t : ℝ) := Real.rpow_inv_natCast_pow ht.le hn
    have hzH := hsq ρ hρ
    have hzt : ideleModule F (posIdele ρ hρ ^ 2) = ideleModule F t := by
      refine Subtype.ext ?_
      rw [sq, map_mul, ← hρn, two_mul, pow_add, ← ideleModule_posIdele ρ hρ]
      rfl
    generalize (posIdele ρ hρ : IdeleGroup F) ^ 2 = z at hzH hzt
    have h1 : (ideleModule F (t * z⁻¹) : ℝ) = 1 := by
      rw [map_mul, map_inv, hzt, mul_inv_cancel]; rfl
    obtain ⟨c, hcS⟩ := hSm (t * z⁻¹) h1.ge h1.le
    refine ⟨_, hcS, ?_⟩
    have e : (diagonal F c * (t * z⁻¹))⁻¹ * t = z * (diagonal F c)⁻¹ := by
      rw [mul_inv, mul_inv, inv_inv, mul_assoc, mul_right_comm, inv_mul_cancel, one_mul, mul_comm]
    rw [e]
    exact H.mul_mem hzH (H.inv_mem (hK c))
  haveI : DiscreteTopology (Ideles F ⧸ H) := QuotientGroup.discreteTopology hopen
  have hfin : ((QuotientGroup.mk : Ideles F → Ideles F ⧸ H) '' S).Finite :=
    (hS.image QuotientGroup.continuous_mk).finite_of_discrete
  haveI : Finite (Ideles F ⧸ H) := by
    refine Set.finite_univ_iff.1 (hfin.subset fun q _ => ?_)
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨s, hs, hst⟩ := hcov t
    exact ⟨s, hs, QuotientGroup.eq.2 hst⟩
  exact Subgroup.finiteIndex_of_finite_quotient

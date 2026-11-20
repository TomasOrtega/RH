import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ConeCpt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullMatBd
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

/- English proof (translation)
Use `⟨∑ I : Fin q → Fin n, ∏ i, ‖LinearMap.toContinuousLinearMap (b.coord (I i))‖, by positivity, ?_⟩` and prove the remaining obligations. Introduce `F _ _ m δ hδ h v`. Establish `e : m v = ∑ I : Fin q → Fin n, (∏ i, b.repr (v i) (I i)) • m fun i => b (I i)`. Establish `e1 : v = fun i => ∑ j, b.repr (v i) j • b j` using `funext fun i => (b.sum_repr (v i)).symm`. Use `conv_lhs => rw [e1]`.

Rewrite using `[ContinuousAlternatingMap.map_sum]`. Conclude with `Finset.sum_congr rfl fun I _ => m.map_smul_univ _ _`. Rewrite using `[e, mul_assoc, Finset.sum_mul]`. Use `norm_sum_le_of_le _ fun I _ => ?_` and prove the remaining obligations. Rewrite using `[norm_smul, norm_prod, mul_comm δ, ← mul_assoc, ← Finset.prod_mul_distrib]`.

Use `mul_le_mul (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_) (h I) (norm_nonneg _) (by positivity)` and prove the remaining obligations. Conclude with `(LinearMap.toContinuousLinearMap (b.coord (I i))).le_opNorm (v i)`.
-/
private theorem basis_bd {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {n : ℕ}
    (b : Module.Basis (Fin n) ℝ V) (q : ℕ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
      (m : V [⋀^Fin q]→L[ℝ] F) (δ : ℝ), 0 ≤ δ → (∀ I : Fin q → Fin n, ‖m fun i => b (I i)‖ ≤ δ) →
      ∀ v, ‖m v‖ ≤ c * δ * ∏ i, ‖v i‖ := by
  refine ⟨∑ I : Fin q → Fin n, ∏ i, ‖LinearMap.toContinuousLinearMap (b.coord (I i))‖, by positivity, ?_⟩
  intro F _ _ m δ hδ h v
  have e : m v = ∑ I : Fin q → Fin n, (∏ i, b.repr (v i) (I i)) • m fun i => b (I i) := by
    have e1 : v = fun i => ∑ j, b.repr (v i) j • b j := funext fun i => (b.sum_repr (v i)).symm
    conv_lhs => rw [e1]
    rw [ContinuousAlternatingMap.map_sum]
    exact Finset.sum_congr rfl fun I _ => m.map_smul_univ _ _
  rw [e, mul_assoc, Finset.sum_mul]
  refine norm_sum_le_of_le _ fun I _ => ?_
  rw [norm_smul, norm_prod, mul_comm δ, ← mul_assoc, ← Finset.prod_mul_distrib]
  refine mul_le_mul (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_) (h I) (norm_nonneg _) (by positivity)
  exact (LinearMap.toContinuousLinearMap (b.coord (I i))).le_opNorm (v i)

/- English proof (translation)
Proceed by induction on `m using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero, map_zero]`. Both sides reduce to the same expression. Consider the case `tmul φ v => simp [mul_comm]`. Consider the case `add x y hx hy => simp only [map_add, Pi.add_apply, Submodule.coe_add, hx, hy]`.
-/
private theorem ev_cmp {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a d : ℕ}
    (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (g : GA E a) (j : Fin d) : ev m g j = (cmp j m).1 g := by
  induction m using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; rfl
  | tmul φ v => simp [mul_comm]
  | add x y hx hy => simp only [map_add, Pi.add_apply, Submodule.coe_add, hx, hy]

/- English proof (translation)
Establish `hs : Continuous (sInf E : Cinf E → Ad E)` using `(GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const`. Conclude with `Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))`.
-/
private theorem cont_inf (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) :
    Continuous (infGL E a) := by
  have hs : Continuous (sInf E : Cinf E → Ad E) := (GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

/- English proof (translation)
Introduce `E _ _ _ a ho U Ξ q ω w hw hl s K hK hKc`. Take `⟨x, rfl⟩` from `QuotientGroup.mk_surjective s`. Take `⟨C, hC, hCK⟩` from `coneCpt E a K hK hKc`. Establish `c1 : Continuous fun g : GL (Fin a) (Cinf E) => toL g.val` using `Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))`. Establish `c2 : Continuous fun g : GL (Fin a) (Cinf E) => toL (g⁻¹).val` using `Units.continuous_coe_inv (M := Matrix (Fin a) (Fin a) (Cinf E))`.

Take `⟨R1, hR1⟩` from `hC.exists_bound_of_continuousOn c1.continuousOn`. Take `⟨R2, hR2⟩` from `hC.exists_bound_of_continuousOn c2.continuousOn`. Take `⟨B, hB, hM⟩` from `matBd E a Ξ (max R1 R2)`. Set `b` to `Module.finBasis ℝ (HV E a)`. Take `⟨c, hc, hb⟩` from `basis_bd b q`.

Establish `hD : IsCompact ((fun g => infGL E a g * finGL E a x) '' C)` using `hC.image ((cont_inf E a).mul continuous_const)`. Rewrite using `[Metric.tendstoUniformlyOn_iff]`. Introduce `ε hε`. Establish `hA : 0 ≤ c * B * B ^ q` using `by positivity`. Take `⟨δ, hδ, hδε⟩` from `exists_pos_mul_lt hε (c * B * B ^ q)`.

Establish `hev : ∀ᶠ k in atTop, ∀ (I : Fin q → Fin (Module.finrank ℝ (HV E a))) (j : Fin Ξ.d), ∀ y ∈ (fun g => infGL E a g * finGL E a x) '' C, dist ((0 : Sm E a).1 y) ((cmp j (ω k fun i => hv.symm (b (I i)))).1 y) < δ` using `eventually_all.2 fun I => eventually_all.2 fun j => Metric.tendstoUniformlyOn_iff.1 (hl (fun i => hv.symm (b (I i))) j _ hD) δ hδ`. Use `filter_upwards [hev] with k hk p hp`. Take `⟨g, hg, rfl⟩` from `hCK p hp`. Take `⟨m1, -, m3⟩` from `hM g ((hR1 g hg).trans (le_max_left _ _)) ((hR2 g hg).trans (le_max_right _ _))`. Rewrite using `[Pi.zero_apply, dist_zero_left]`.

Use `lt_of_le_of_lt (ContinuousAlternatingMap.opNorm_le_bound _ (by positivity) fun v => ?_) hδε` and prove the remaining obligations. Establish `key` using `hb _ (((w k).1 x (sand g (hOne E a))).compContinuousLinearMap ((2 : ℝ) • sand g)) (B * δ) (by positivity) (fun I => ?_) fun i => (1 / 2 : ℝ) • sand g⁻¹ (v i)`. Establish `e : (((2 : ℝ) • sand g : HV E a →L[ℝ] HV E a) ∘ fun i => (1 / 2 : ℝ) • sand g⁻¹ (v i)) = v`. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp_apply, ContinuousLinearMap.smul_apply, map_smul, smul_smul]`.

Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]`. Evaluate the numerical expressions. Rewrite `key` using `[ContinuousAlternatingMap.compContinuousLinearMap_apply, e]`. Establish `hp : ∏ i, ‖(1 / 2 : ℝ) • sand g⁻¹ (v i)‖ ≤ B ^ q * ∏ i, ‖v i‖`. Establish `: B ^ q * ∏ i, ‖v i‖ = ∏ i, B * ‖v i‖`.

Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[this]`. Use `Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_smul]`. Establish `h3` using `m3 (v i)`.

Establish `h4` using `norm_nonneg (sand g⁻¹ (v i))`. Establish `h5 : ‖(1 / 2 : ℝ)‖ = 1 / 2` using `by norm_num`. Rewrite using `[h5]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.

Establish `hc` using `hw k g x fun i => hv.symm (b (I i))`. Simplify using `only [LinearEquiv.apply_symm_apply] at hc`. Rewrite using `[ContinuousAlternatingMap.compContinuousLinearMap_apply]`. Use `(congrArg norm hc).le.trans ((m1 _).trans (mul_le_mul_of_nonneg_left ?_ hB))` and prove the remaining obligations. Use `(pi_norm_le_iff_of_nonneg hδ.le).2 fun j => ?_` and prove the remaining obligations.

Use `hk I j _ ⟨g, hg, rfl⟩` as an intermediate fact. Rewrite using `[ev_cmp]`. Simplify using `using this.le`.
-/
theorem UpperTheory.V.Cj.H.corrLim :
    UpperTheory.V.Cj.H.CorrLim := by
  intro E _ _ _ a ho U Ξ q ω w hw hl s K hK hKc
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨C, hC, hCK⟩ := coneCpt E a K hK hKc
  have c1 : Continuous fun g : GL (Fin a) (Cinf E) => toL g.val :=
    Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))
  have c2 : Continuous fun g : GL (Fin a) (Cinf E) => toL (g⁻¹).val :=
    Units.continuous_coe_inv (M := Matrix (Fin a) (Fin a) (Cinf E))
  obtain ⟨R1, hR1⟩ := hC.exists_bound_of_continuousOn c1.continuousOn
  obtain ⟨R2, hR2⟩ := hC.exists_bound_of_continuousOn c2.continuousOn
  obtain ⟨B, hB, hM⟩ := matBd E a Ξ (max R1 R2)
  let b := Module.finBasis ℝ (HV E a)
  obtain ⟨c, hc, hb⟩ := basis_bd b q
  have hD : IsCompact ((fun g => infGL E a g * finGL E a x) '' C) :=
    hC.image ((cont_inf E a).mul continuous_const)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hA : 0 ≤ c * B * B ^ q := by positivity
  obtain ⟨δ, hδ, hδε⟩ := exists_pos_mul_lt hε (c * B * B ^ q)
  have hev : ∀ᶠ k in atTop, ∀ (I : Fin q → Fin (Module.finrank ℝ (HV E a))) (j : Fin Ξ.d),
      ∀ y ∈ (fun g => infGL E a g * finGL E a x) '' C,
        dist ((0 : Sm E a).1 y) ((cmp j (ω k fun i => hv.symm (b (I i)))).1 y) < δ :=
    eventually_all.2 fun I => eventually_all.2 fun j =>
      Metric.tendstoUniformlyOn_iff.1 (hl (fun i => hv.symm (b (I i))) j _ hD) δ hδ
  filter_upwards [hev] with k hk p hp
  obtain ⟨g, hg, rfl⟩ := hCK p hp
  obtain ⟨m1, -, m3⟩ := hM g ((hR1 g hg).trans (le_max_left _ _)) ((hR2 g hg).trans (le_max_right _ _))
  rw [Pi.zero_apply, dist_zero_left]
  refine lt_of_le_of_lt (ContinuousAlternatingMap.opNorm_le_bound _ (by positivity) fun v => ?_) hδε
  have key := hb _ (((w k).1 x (sand g (hOne E a))).compContinuousLinearMap ((2 : ℝ) • sand g)) (B * δ)
    (by positivity) (fun I => ?_) fun i => (1 / 2 : ℝ) • sand g⁻¹ (v i)
  · have e : (((2 : ℝ) • sand g : HV E a →L[ℝ] HV E a) ∘ fun i => (1 / 2 : ℝ) • sand g⁻¹ (v i)) = v := by
      funext i
      simp only [Function.comp_apply, ContinuousLinearMap.smul_apply, map_smul, smul_smul]
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      norm_num
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, e] at key
    have hp : ∏ i, ‖(1 / 2 : ℝ) • sand g⁻¹ (v i)‖ ≤ B ^ q * ∏ i, ‖v i‖ := by
      have : B ^ q * ∏ i, ‖v i‖ = ∏ i, B * ‖v i‖ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [this]
      refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
      rw [norm_smul]
      have h3 := m3 (v i)
      have h4 := norm_nonneg (sand g⁻¹ (v i))
      have h5 : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
      rw [h5]
      linarith
    calc _ ≤ _ := key
      _ ≤ c * (B * δ) * (B ^ q * ∏ i, ‖v i‖) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by ring
  · have hc := hw k g x fun i => hv.symm (b (I i))
    simp only [LinearEquiv.apply_symm_apply] at hc
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    refine (congrArg norm hc).le.trans ((m1 _).trans (mul_le_mul_of_nonneg_left ?_ hB))
    refine (pi_norm_le_iff_of_nonneg hδ.le).2 fun j => ?_
    have := hk I j _ ⟨g, hg, rfl⟩
    rw [ev_cmp]
    simpa using this.le

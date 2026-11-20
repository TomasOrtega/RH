import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.ThFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.FinMH

open Polynomial UpperTheory.V.Z.Sym.Wt

/- English proof (translation)
Use `haveI : FiniteDimensional ℂ (MH d n) := finMH K d n`. Set `W : Submodule ℂ (Module.Dual ℂ (MH d n))` to `{ carrier := {φ | Continuous fun t => φ (mRep d n (γ t) x)} add_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq, LinearMap.add_apply] at *`. Conclude with `ha.add hb`.

Use the proof step `zero_mem' := by`. Simplify using `only [Set.mem_setOf_eq, LinearMap.zero_apply]`. Conclude with `continuous_const`. Use the proof step `smul_mem' := by`. Introduce `c a ha`.

Simplify using `only [Set.mem_setOf_eq, LinearMap.smul_apply, smul_eq_mul] at *`. Conclude with `continuous_const.mul ha }`. Establish `hev : ∀ y : K × Fin d → ℂ, (MvPolynomial.aeval y : MvPolynomial (K × Fin d) ℂ →ₐ[ℂ] ℂ).toLinearMap.comp (MH d n).subtype ∈ W`. Introduce `y`. Establish `hc : Continuous fun t => MvPolynomial.eval y ((mRep d n (γ t) x : MH d n) : MvPolynomial (K × Fin d) ℂ)`.

Simplify using `only [eval_mRep]`. Use `(MvPolynomial.continuous_eval (x : MvPolynomial (K × Fin d) ℂ)).comp ?_` and prove the remaining obligations. Use `continuous_pi fun p => ?_` and prove the remaining obligations. Conclude with `continuous_finset_sum _ fun j _ => continuous_const.mul (hγ p.1 j p.2)`. Use `show Continuous fun t => (MvPolynomial.aeval y) ((mRep d n (γ t) x : MH d n) : MvPolynomial (K × Fin d) ℂ)`.

Use `hc using 2 with t` and compare the differences between its conclusion and the goal. Conclude with `DFunLike.congr_fun (MvPolynomial.coe_aeval_eq_eval y) _`. Establish `hb : W.dualCoannihilator = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `v hv`.

Rewrite `hv` using `[Submodule.mem_dualCoannihilator]`. Rewrite using `[Submodule.mem_bot]`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `y`.

Use `hv _ (hev y)` as an intermediate fact. Establish `e : (MvPolynomial.aeval y) (v : MvPolynomial (K × Fin d) ℂ) = MvPolynomial.eval y (v : MvPolynomial (K × Fin d) ℂ)` using `DFunLike.congr_fun (MvPolynomial.coe_aeval_eq_eval y) _`. Rewrite using `[Submodule.coe_zero, map_zero, ← e]`. Conclude with `this`. Establish `htop : W = ⊤`.

Rewrite using `[← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), hb, Submodule.dualAnnihilator_bot]`. Establish `hf : f ∈ W` using `htop ▸ Submodule.mem_top`. Conclude with `hf`.
-/
private theorem cont_m {K T : Type} [Fintype K] [TopologicalSpace T] {d : ℕ} (n : K → ℕ) (γ : T → K → GL (Fin d) ℂ)
    (hγ : ∀ k i j, Continuous fun t => (γ t k : Matrix (Fin d) (Fin d) ℂ) i j) (x : MH d n) (f : MH d n →ₗ[ℂ] ℂ) :
    Continuous fun t => f (mRep d n (γ t) x) := by
  haveI : FiniteDimensional ℂ (MH d n) := finMH K d n
  let W : Submodule ℂ (Module.Dual ℂ (MH d n)) :=
    { carrier := {φ | Continuous fun t => φ (mRep d n (γ t) x)}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, LinearMap.add_apply] at *
        exact ha.add hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq, LinearMap.zero_apply]
        exact continuous_const
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq, LinearMap.smul_apply, smul_eq_mul] at *
        exact continuous_const.mul ha }
  have hev : ∀ y : K × Fin d → ℂ,
      (MvPolynomial.aeval y : MvPolynomial (K × Fin d) ℂ →ₐ[ℂ] ℂ).toLinearMap.comp (MH d n).subtype ∈ W := by
    intro y
    have hc : Continuous fun t => MvPolynomial.eval y ((mRep d n (γ t) x : MH d n) : MvPolynomial (K × Fin d) ℂ) := by
      simp only [eval_mRep]
      refine (MvPolynomial.continuous_eval (x : MvPolynomial (K × Fin d) ℂ)).comp ?_
      refine continuous_pi fun p => ?_
      exact continuous_finset_sum _ fun j _ => continuous_const.mul (hγ p.1 j p.2)
    show Continuous fun t => (MvPolynomial.aeval y) ((mRep d n (γ t) x : MH d n) : MvPolynomial (K × Fin d) ℂ)
    convert hc using 2 with t
    exact DFunLike.congr_fun (MvPolynomial.coe_aeval_eq_eval y) _
  have hb : W.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv
    rw [Submodule.mem_bot]
    apply Subtype.ext
    apply MvPolynomial.funext
    intro y
    have := hv _ (hev y)
    have e : (MvPolynomial.aeval y) (v : MvPolynomial (K × Fin d) ℂ) = MvPolynomial.eval y (v : MvPolynomial (K × Fin d) ℂ) :=
      DFunLike.congr_fun (MvPolynomial.coe_aeval_eq_eval y) _
    rw [Submodule.coe_zero, map_zero, ← e]
    exact this
  have htop : W = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), hb, Submodule.dualAnnihilator_bot]
  have hf : f ∈ W := htop ▸ Submodule.mem_top
  exact hf

/- English proof (translation)
Introduce `I _`. Establish `entc : ∀ (d : ℕ) (k : I) (i j : Fin d), Continuous fun g : I → GL (Fin d) ℂ => ((g k : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) i j`. Introduce `d k i j`. Conclude with `((Units.continuous_val (M := Matrix (Fin d) (Fin d) ℂ)).comp (continuous_apply k)).matrix_elem i j`. Establish `entci : ∀ (d : ℕ) (k : I) (i j : Fin d), Continuous fun g : I → GL (Fin d) ℂ => (((g k)⁻¹ : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) i j`.

Introduce `d k i j`. Conclude with `((Units.continuous_coe_inv (M := Matrix (Fin d) (Fin d) ℂ)).comp (continuous_apply k)).matrix_elem i j`. Use `⟨fun j x f => ?_, fun n e x f => ?_⟩` and prove the remaining obligations. Establish `hsplit : (fun g => f (repG I j g x)) = fun g => ∑ S, f (Pi.single S (repG I j g x S))`. Use function extensionality and compare the values at `g`.

Rewrite using `[← map_sum, Finset.univ_sum_single]`. Rewrite using `[hsplit]`. Use `continuous_finset_sum _ fun S _ => ?_` and prove the remaining obligations. Establish `hent : ∀ (k : I × Bool) (i i' : Fin 3), Continuous fun g : I → GL (Fin 3) ℂ => ((dbl 3 g k : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) i i'`. Introduce `k i i'`.

Establish `hfun : (fun g : I → GL (Fin 3) ℂ => ((dbl 3 g k : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) i i') = fun g => if k.2 = true then (((g k.1)⁻¹ : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) i' i else ((g k.1 : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) i i'`. Use function extensionality and compare the values at `g`. Simplify using `only [dbl, MonoidHom.coe_mk, OneHom.coe_mk]`. Apply the tactic sequence `split_ifs <;> rfl`. Rewrite using `[hfun]`.

Distinguish the cases in `hk : k.2 = true`. Simplify using `only [hk, if_true]`. Conclude with `entci 3 k.1 i' i`. Simplify using `only [if_neg hk]`. Conclude with `entc 3 k.1 i i'`.

Conclude with `cont_m (fun k : I × Bool => dg j S k.1) (fun g : I → GL (Fin 3) ℂ => dbl 3 g) hent (x S) (f ∘ₗ LinearMap.single ℂ (fun S => ↥(Bi 3 (dg j S))) S)`. Establish `hdet : ∀ v : I, Continuous fun g : I → GL (Fin 2) ℂ => Matrix.GeneralLinearGroup.det (g v)`. Introduce `v`. Use `Units.continuous_iff.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Use `show Continuous fun g : I → GL (Fin 2) ℂ => ((Matrix.GeneralLinearGroup.det (g v) : ℂˣ) : ℂ)`.

Simplify using `only [Matrix.GeneralLinearGroup.val_det_apply]`. Conclude with `((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) ℂ)).comp (continuous_apply v)).matrix_det`. Establish `h : ∀ g : I → GL (Fin 2) ℂ, (((Matrix.GeneralLinearGroup.det (g v))⁻¹ : ℂˣ) : ℂ) = (((g v)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det`. Introduce `g`. Rewrite using `[← map_inv, Matrix.GeneralLinearGroup.val_det_apply]`.

Simplify using `only [h]`. Conclude with `((Units.continuous_coe_inv (M := Matrix (Fin 2) (Fin 2) ℂ)).comp (continuous_apply v)).matrix_det`. Establish `hd : Continuous fun g : I → GL (Fin 2) ℂ => detE 2 e g` using `by show Continuous fun g : I → GL (Fin 2) ℂ => ∏ v, Matrix.GeneralLinearGroup.det (g v) ^ e`. Conclude with `continuous_finset_prod _ fun v _ => (hdet v).zpow e`. Simplify using `only [repD_apply, LinearMap.smul_apply, map_smul, smul_eq_mul]`.

Conclude with `(Units.continuous_val.comp hd).mul (cont_m (fun _ : I => n) (fun g : I → GL (Fin 2) ℂ => g) (fun k i j => entc 2 k i j) x f)`.
-/
theorem UpperTheory.V.Z.Sym.Wt.contRep :
    UpperTheory.V.Z.Sym.Wt.ContRep := by
  intro I _
  classical
  have entc : ∀ (d : ℕ) (k : I) (i j : Fin d),
      Continuous fun g : I → GL (Fin d) ℂ => ((g k : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) i j := by
    intro d k i j
    exact ((Units.continuous_val (M := Matrix (Fin d) (Fin d) ℂ)).comp (continuous_apply k)).matrix_elem i j
  have entci : ∀ (d : ℕ) (k : I) (i j : Fin d),
      Continuous fun g : I → GL (Fin d) ℂ => (((g k)⁻¹ : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) i j := by
    intro d k i j
    exact ((Units.continuous_coe_inv (M := Matrix (Fin d) (Fin d) ℂ)).comp (continuous_apply k)).matrix_elem i j
  refine ⟨fun j x f => ?_, fun n e x f => ?_⟩
  · have hsplit : (fun g => f (repG I j g x)) = fun g => ∑ S, f (Pi.single S (repG I j g x S)) := by
      funext g
      rw [← map_sum, Finset.univ_sum_single]
    rw [hsplit]
    refine continuous_finset_sum _ fun S _ => ?_
    have hent : ∀ (k : I × Bool) (i i' : Fin 3),
        Continuous fun g : I → GL (Fin 3) ℂ => ((dbl 3 g k : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) i i' := by
      intro k i i'
      have hfun : (fun g : I → GL (Fin 3) ℂ => ((dbl 3 g k : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) i i') =
          fun g => if k.2 = true then (((g k.1)⁻¹ : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) i' i
            else ((g k.1 : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) i i' := by
        funext g
        simp only [dbl, MonoidHom.coe_mk, OneHom.coe_mk]
        split_ifs <;> rfl
      rw [hfun]
      by_cases hk : k.2 = true
      · simp only [hk, if_true]
        exact entci 3 k.1 i' i
      · simp only [if_neg hk]
        exact entc 3 k.1 i i'
    exact cont_m (fun k : I × Bool => dg j S k.1) (fun g : I → GL (Fin 3) ℂ => dbl 3 g) hent (x S)
      (f ∘ₗ LinearMap.single ℂ (fun S => ↥(Bi 3 (dg j S))) S)
  · have hdet : ∀ v : I, Continuous fun g : I → GL (Fin 2) ℂ => Matrix.GeneralLinearGroup.det (g v) := by
      intro v
      refine Units.continuous_iff.mpr ⟨?_, ?_⟩
      · show Continuous fun g : I → GL (Fin 2) ℂ => ((Matrix.GeneralLinearGroup.det (g v) : ℂˣ) : ℂ)
        simp only [Matrix.GeneralLinearGroup.val_det_apply]
        exact ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) ℂ)).comp (continuous_apply v)).matrix_det
      · have h : ∀ g : I → GL (Fin 2) ℂ,
            (((Matrix.GeneralLinearGroup.det (g v))⁻¹ : ℂˣ) : ℂ) = (((g v)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det := by
          intro g
          rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
        simp only [h]
        exact ((Units.continuous_coe_inv (M := Matrix (Fin 2) (Fin 2) ℂ)).comp (continuous_apply v)).matrix_det
    have hd : Continuous fun g : I → GL (Fin 2) ℂ => detE 2 e g := by
      show Continuous fun g : I → GL (Fin 2) ℂ => ∏ v, Matrix.GeneralLinearGroup.det (g v) ^ e
      exact continuous_finset_prod _ fun v _ => (hdet v).zpow e
    simp only [repD_apply, LinearMap.smul_apply, map_smul, smul_eq_mul]
    exact (Units.continuous_val.comp hd).mul
      (cont_m (fun _ : I => n) (fun g : I → GL (Fin 2) ℂ => g) (fun k i j => entc 2 k i j) x f)

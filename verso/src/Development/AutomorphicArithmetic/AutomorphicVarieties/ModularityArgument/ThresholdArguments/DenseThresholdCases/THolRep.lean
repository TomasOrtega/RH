import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocCompR
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatLoc

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Polynomial UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd Matrix
open GlobalTheory.CuspRep (SmIrr Af invT finId pFin locGL finGL GA chiDet)
section Proj
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ}
/- English proof (translation)
Introduce `o φ hφ` and use `by refine Submodule.mem_comap.1 ((iSup₂_le (a := Submodule.comap (TR.act o) _) fun π hπ x hx => ?_) hφ) exact Submodule.mem_iSup_of_mem π (Submodule.mem_iSup_of_mem hπ (π.stable o x hx))`.
-/
private theorem stable_iSup (S : Set (TR.CuspSub F a)) : TR.IsStable (⨆ π ∈ S, π.V) := fun o φ hφ => by
  refine Submodule.mem_comap.1 ((iSup₂_le (a := Submodule.comap (TR.act o) _) fun π hπ x hx => ?_) hφ)
  exact Submodule.mem_iSup_of_mem π (Submodule.mem_iSup_of_mem hπ (π.stable o x hx))
/- English proof (translation)
Take `⟨S, hS⟩` from `Submodule.mem_iSup_iff_exists_finset.1 h`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact absurd (by simpa using hS) h0`. Consider the case `insert π S hπ ih`. Rewrite `hS` using `[Finset.iSup_insert]`.

Establish `hs : TR.IsStable (⨆ π ∈ S, π.V)` using `stable_iSup (S : Set (TR.CuspSub F a))`. Break down `π.irred (π.V ⊓ ⨆ π ∈ S, π.V) inf_le_left (fun o x hx => ⟨π.stable o x hx.1, hs o x hx.2⟩) with e | e` into its components or cases. Take `⟨ψ, h1, ψ', h2, e2⟩` from `Submodule.mem_sup.1 hS`. Distinguish the cases in `h3 : ψ = 0`. Conclude with `ih (by rw [← e2, h3, zero_add]; exact h2)`.

Use `⟨π, ψ, h1, h3, fun z hz c hc => ?_⟩` and prove the remaining obligations. Rewrite `hc` using `[← e2, map_add, smul_add]`. Establish `h4 : z ψ - c • ψ ∈ π.V ⊓ ⨆ π ∈ S, π.V`. Use `⟨sub_mem (hz _ π.stable _ h1) (π.V.smul_mem c h1), ?_⟩` and prove the remaining obligations. Establish `: z ψ - c • ψ = c • ψ' - z ψ'` using `by linear_combination (norm := module) hc`.

Rewrite using `[this]`. Conclude with `sub_mem (Submodule.smul_mem _ c h2) (hz _ hs _ h2)`. Rewrite `h4` using `[e, Submodule.mem_bot]`. Conclude with `sub_eq_zero.1 h4`. Conclude with `ih ((sup_le (inf_eq_left.1 e) le_rfl) hS)`.
-/
private theorem proj {φ : TR.Sm F a} (h0 : φ ≠ 0) (h : φ ∈ ⨆ π : TR.CuspSub F a, π.V) :
    ∃ (π : TR.CuspSub F a) (ψ : TR.Sm F a), ψ ∈ π.V ∧ ψ ≠ 0 ∧ ∀ z : Module.End ℂ (TR.Sm F a),
      (∀ V, TR.IsStable V → ∀ x ∈ V, z x ∈ V) → ∀ c : ℂ, z φ = c • φ → z ψ = c • ψ := by
  classical
  obtain ⟨S, hS⟩ := Submodule.mem_iSup_iff_exists_finset.1 h
  induction S using Finset.induction_on with
  | empty => exact absurd (by simpa using hS) h0
  | insert π S hπ ih =>
    rw [Finset.iSup_insert] at hS
    have hs : TR.IsStable (⨆ π ∈ S, π.V) := stable_iSup (S : Set (TR.CuspSub F a))
    rcases π.irred (π.V ⊓ ⨆ π ∈ S, π.V) inf_le_left (fun o x hx => ⟨π.stable o x hx.1, hs o x hx.2⟩) with e | e
    · obtain ⟨ψ, h1, ψ', h2, e2⟩ := Submodule.mem_sup.1 hS
      by_cases h3 : ψ = 0
      · exact ih (by rw [← e2, h3, zero_add]; exact h2)
      refine ⟨π, ψ, h1, h3, fun z hz c hc => ?_⟩
      rw [← e2, map_add, smul_add] at hc
      have h4 : z ψ - c • ψ ∈ π.V ⊓ ⨆ π ∈ S, π.V := by
        refine ⟨sub_mem (hz _ π.stable _ h1) (π.V.smul_mem c h1), ?_⟩
        have : z ψ - c • ψ = c • ψ' - z ψ' := by linear_combination (norm := module) hc
        rw [this]
        exact sub_mem (Submodule.smul_mem _ c h2) (hz _ hs _ h2)
      rw [e, Submodule.mem_bot] at h4
      exact sub_eq_zero.1 h4
    · exact ih ((sup_le (inf_eq_left.1 e) le_rfl) hS)
/- English proof (translation)
Use `LinearMap.ext fun φ => Subtype.ext <| funext fun g => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `fderiv ℝ (TR.chart φ.1 (g * TR.infGL F a y)) (TR.oneL F a) (TR.toL X) = fderiv ℝ (TR.chart (fun x => φ.1 (x * TR.infGL F a y)) g) (TR.oneL F a) (TR.toL (y.val * X * (y⁻¹).val))`. Establish `hd : DifferentiableAt ℝ (TR.chart φ.1 g) (TR.toL y.val)` using `(TR.contDiffAt_chart φ.2 g (TR.val_mem_invSet y)).differentiableAt (by simp)`. Establish `e1 : TR.lmul (TR.toL y.val) (TR.oneL F a) = TR.toL y.val` using `mul_one y.val`. Establish `e2 : TR.rmul (TR.toL y.val) (TR.oneL F a) = TR.toL y.val` using `one_mul y.val`.

Rewrite using `[TR.chart_mul, TR.chart_rt_inf, fderiv_comp _ (by rw [e1]; exact hd) (TR.lmul (TR.toL y.val)).differentiableAt, fderiv_comp _ (by rw [e2]; exact hd) (TR.rmul (TR.toL y.val)).differentiableAt, e1, e2, ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]`. Conclude with `congrArg (fun Z => fderiv ℝ (TR.chart φ.1 g) (TR.toL y.val) (TR.toL Z)) (Units.inv_mul_cancel_right (y.val * X) y).symm`.
-/
private theorem rt_lie (y : GL (Fin a) (TR.Rinf F)) (X : Matrix (Fin a) (Fin a) (TR.Rinf F)) :
    TR.rt F a (TR.infGL F a y) * TR.lie F a (TR.toL X) =
      TR.lie F a (TR.toL (y.val * X * (y⁻¹).val)) * TR.rt F a (TR.infGL F a y) := by
  refine LinearMap.ext fun φ => Subtype.ext <| funext fun g => ?_
  change fderiv ℝ (TR.chart φ.1 (g * TR.infGL F a y)) (TR.oneL F a) (TR.toL X) =
    fderiv ℝ (TR.chart (fun x => φ.1 (x * TR.infGL F a y)) g) (TR.oneL F a) (TR.toL (y.val * X * (y⁻¹).val))
  have hd : DifferentiableAt ℝ (TR.chart φ.1 g) (TR.toL y.val) :=
    (TR.contDiffAt_chart φ.2 g (TR.val_mem_invSet y)).differentiableAt (by simp)
  have e1 : TR.lmul (TR.toL y.val) (TR.oneL F a) = TR.toL y.val := mul_one y.val
  have e2 : TR.rmul (TR.toL y.val) (TR.oneL F a) = TR.toL y.val := one_mul y.val
  rw [TR.chart_mul, TR.chart_rt_inf, fderiv_comp _ (by rw [e1]; exact hd) (TR.lmul (TR.toL y.val)).differentiableAt,
    fderiv_comp _ (by rw [e2]; exact hd) (TR.rmul (TR.toL y.val)).differentiableAt, e1, e2,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  exact congrArg (fun Z => fderiv ℝ (TR.chart φ.1 g) (TR.toL y.val) (TR.toL Z)) (Units.inv_mul_cancel_right (y.val * X) y).symm
open Classical in
/- English proof (translation)
Set `L : Matrix (Fin a) (Fin a) (TR.Rinf F) →ₗ[ℝ] Module.End ℂ (TR.Sm F a)` to `TR.lie F a`. Establish `e : X = ∑ v, ∑ i, ∑ j, X i j v • Matrix.single i j (Pi.single v 1 : TR.Rinf F)`. Use extensionality with `i j v`. Simplify using `[Matrix.sum_apply, Matrix.single_apply, ite_and, Pi.single_apply, ite_apply]`. Express the relevant statement in the definitionally equal form `L X = _`.

Use `conv_lhs => rw [e]`. Simplify using `only [map_sum, map_smul]`. Both sides reduce to the same expression.
-/
private theorem lie_eq_sum (X : Matrix (Fin a) (Fin a) (TR.Rinf F)) :
    TR.lie F a (TR.toL X) = ∑ v, ∑ i, ∑ j, ((X i j v : ℝ) : ℂ) • TR.Eop v i j := by
  let L : Matrix (Fin a) (Fin a) (TR.Rinf F) →ₗ[ℝ] Module.End ℂ (TR.Sm F a) := TR.lie F a
  have e : X = ∑ v, ∑ i, ∑ j, X i j v • Matrix.single i j (Pi.single v 1 : TR.Rinf F) := by
    ext i j v
    simp [Matrix.sum_apply, Matrix.single_apply, ite_and, Pi.single_apply, ite_apply]
  change L X = _
  conv_lhs => rw [e]
  simp only [map_sum, map_smul]
  rfl
/- English proof (translation)
Rewrite using `[TR.Eop, rt_lie, lie_eq_sum, Finset.sum_eq_single v]`. Simplify using `[Matrix.mul_apply, Matrix.single_apply, ite_and, ite_apply]`. Introduce `v' _ h`. Simplify using `[Matrix.mul_apply, Matrix.single_apply, ite_and, ite_apply, h]`. Simplify using the standard rewrite rules.
-/
private theorem rt_Eop (y : GL (Fin a) (TR.Rinf F)) (v : InfinitePlace F) (i j : Fin a) :
    TR.rt F a (TR.infGL F a y) * TR.Eop v i j =
      (∑ k, ∑ l, (((y.val k i v : ℝ) : ℂ) * (((y⁻¹).val j l v : ℝ) : ℂ)) • TR.Eop v k l) * TR.rt F a (TR.infGL F a y) := by
  classical
  rw [TR.Eop, rt_lie, lie_eq_sum, Finset.sum_eq_single v]
  · simp [Matrix.mul_apply, Matrix.single_apply, ite_and, ite_apply]
  · intro v' _ h
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, ite_apply, h]
  · simp
/- English proof (translation)
Consider the cases of `o with`. Consider the case `fin k => exact GlobalTheory.CapAdInv.qdet_semiconj _ _ _ (fun i j => (TR.lie_rt_fin _ k).symm) _`. Consider the case `cpt k => set y := Unitary.toUnits k`. Set `f : TR.Rinf F →+* ℂ` to `Complex.ofRealHom.comp (Pi.evalRingHom _ v)`. Establish `h` using `GlobalTheory.CapAdInv.qdet_semiconj _ _ _ (rt_Eop y v) (u + ((a : ℂ) - 1) / 2)`.

Establish `hQP : ((y⁻¹).val.map f) * (y.val.map f) = 1`. Rewrite using `[← Matrix.map_mul, Units.inv_mul]`. Simplify using the standard rewrite rules. Conclude with `h.trans (congrArg (· * _) (GlobalTheory.CapAdInv.qdet_ad _ (TR.glRel_Eop v) _ _ hQP (u + ((a : ℂ) - 1) / 2)))`. Consider the case `lie X`.

Establish `h : ∀ v' i j, Commute (TR.Eop (a` using `a) v' i j) (TR.cap v u) := fun v' i j => by`. Distinguish the cases in `e : v' = v`. Substitute `e` using the available equality. Conclude with `(TR.cap_comm _ _ _ _).symm`. Conclude with `GlobalTheory.CapAdInv.qdet_semiconj _ _ _ (fun k l => TR.Eop_comm e _ _ _ _) _`.

Express the relevant statement in the definitionally equal form `Commute (TR.lie F a (TR.toL (Matrix.of X))) _`. Rewrite using `[lie_eq_sum]`. Conclude with `Commute.sum_left _ _ _ fun v' _ => Commute.sum_left _ _ _ fun i _ => Commute.sum_left _ _ _ fun j _ => (h v' i j).smul_left _`.
-/
private theorem cap_act (v : InfinitePlace F) (u : ℂ) (o : TR.Op F a) : TR.act o * TR.cap v u = TR.cap v u * TR.act o := by
  cases o with
  | fin k => exact GlobalTheory.CapAdInv.qdet_semiconj _ _ _ (fun i j => (TR.lie_rt_fin _ k).symm) _
  | cpt k =>
    set y := Unitary.toUnits k
    let f : TR.Rinf F →+* ℂ := Complex.ofRealHom.comp (Pi.evalRingHom _ v)
    have h := GlobalTheory.CapAdInv.qdet_semiconj _ _ _ (rt_Eop y v) (u + ((a : ℂ) - 1) / 2)
    have hQP : ((y⁻¹).val.map f) * (y.val.map f) = 1 := by
      rw [← Matrix.map_mul, Units.inv_mul]; simp
    exact h.trans (congrArg (· * _) (GlobalTheory.CapAdInv.qdet_ad _ (TR.glRel_Eop v) _ _ hQP (u + ((a : ℂ) - 1) / 2)))
  | lie X =>
    have h : ∀ v' i j, Commute (TR.Eop (a := a) v' i j) (TR.cap v u) := fun v' i j => by
      by_cases e : v' = v
      · subst e; exact (TR.cap_comm _ _ _ _).symm
      · exact GlobalTheory.CapAdInv.qdet_semiconj _ _ _ (fun k l => TR.Eop_comm e _ _ _ _) _
    change Commute (TR.lie F a (TR.toL (Matrix.of X))) _
    rw [lie_eq_sum]
    exact Commute.sum_left _ _ _ fun v' _ => Commute.sum_left _ _ _ fun i _ => Commute.sum_left _ _ _ fun j _ =>
      (h v' i j).smul_left _
/- English proof (translation)
Break down `π.irred (π.V ⊓ Module.End.eigenspace (TR.cap v u) c) inf_le_left (fun o x hx => ⟨π.stable o x hx.1, by` into its components or cases. Use `Module.End.mem_eigenspace_iff.1 hx.2` as an intermediate fact. Use `Module.End.mem_eigenspace_iff.2 ?_` and prove the remaining obligations. Rewrite using `[← Module.End.mul_apply, ← cap_act, Module.End.mul_apply, this, map_smul]⟩) with e | e`. Conclude with `absurd (e.le ⟨h, Module.End.mem_eigenspace_iff.2 hc⟩) h0`.

Conclude with `fun x hx => Module.End.mem_eigenspace_iff.1 (e.ge hx).2`.
-/
private theorem cap_all (π : TR.CuspSub F a) {ψ : TR.Sm F a} (h : ψ ∈ π.V) (h0 : ψ ≠ 0) (v : InfinitePlace F) (u c : ℂ)
    (hc : TR.cap v u ψ = c • ψ) : ∀ x ∈ π.V, TR.cap v u x = c • x := by
  rcases π.irred (π.V ⊓ Module.End.eigenspace (TR.cap v u) c) inf_le_left (fun o x hx => ⟨π.stable o x hx.1, by
    have := Module.End.mem_eigenspace_iff.1 hx.2
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [← Module.End.mul_apply, ← cap_act, Module.End.mul_apply, this, map_smul]⟩) with e | e
  · exact absurd (e.le ⟨h, Module.End.mem_eigenspace_iff.2 hc⟩) h0
  · exact fun x hx => Module.End.mem_eigenspace_iff.1 (e.ge hx).2
/- English proof (translation)
Take `⟨⟨σ, hσ⟩, h2⟩` from `_root_.UpperTheory.V.Af.local_comp_real_of_printed_results P F a π w`. Establish `hi` using `h2 σ hσ`. Take `⟨h3, h4⟩` from `_root_.UpperTheory.V.Af.satake_local_of_printed_results P F a w σ`. Take `⟨x, hx0, hx⟩` from `h`. Take `⟨B, hB⟩` from `h3 (GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup (π.locRep w) σ.ρ σ.irred (fun f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.finPart (locGL F a w g) (f v)} => f.1) (fun f => f.2) (GlobalTheory.LFun.KGL w a : Set _) x hx0 hx (hi.2 ▸ Submodule.mem_top))`.

Conclude with `⟨B, (h4 _ _ hi B).2 hB⟩`.
-/
private theorem exists_sat (P : _root_.UpperTheory.V.Af.Hypotheses') (π : TR.CuspSub F a) (w : HeightOneSpectrum (𝓞 F))
    (h : HasFixed (π.locRep w) (GlobalTheory.LFun.KGL w a)) : ∃ B, π.HasSat w B := by
  obtain ⟨⟨σ, hσ⟩, h2⟩ := _root_.UpperTheory.V.Af.local_comp_real_of_printed_results P F a π w
  have hi := h2 σ hσ
  obtain ⟨h3, h4⟩ := _root_.UpperTheory.V.Af.satake_local_of_printed_results P F a w σ
  obtain ⟨x, hx0, hx⟩ := h
  obtain ⟨B, hB⟩ := h3 (GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup (π.locRep w) σ.ρ σ.irred
    (fun f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.finPart (locGL F a w g) (f v)} => f.1) (fun f => f.2)
    (GlobalTheory.LFun.KGL w a : Set _) x hx0 hx (hi.2 ▸ Submodule.mem_top))
  exact ⟨B, (h4 _ _ hi B).2 hB⟩
end Proj
section Loc
open GlobalTheory.LFun Formalism.UG
/- English proof (translation)
Establish `hfin : (MulAction.orbit K (a : G ⧸ K)).Finite` using `hf.subset fun c hc => by`. Rewrite using `[Set.mem_setOf_eq, h1 _ (by rwa [QuotientGroup.out_eq'])]; exact one_ne_zero`. Use `letI := hfin.fintype`. Rewrite using `[Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, ← finsum_eq_sum_of_fintype, finsum_set_coe_eq_finsum_mem (f := fun c : G ⧸ K => ρ c.out x), heckeVec]`. Use `finsum_congr fun c => ?_` and prove the remaining obligations.

Distinguish the cases in `hc : c ∈ MulAction.orbit K (a : G ⧸ K)`. Rewrite using `[h1 _ (by rwa [QuotientGroup.out_eq'])]; simp [hc]`. Rewrite using `[h2 _ (by rwa [QuotientGroup.out_eq'])]; simp [hc]`.
-/
private theorem hecke_eq_dc {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (a : G) (h : G → ℂ) (h1 : ∀ g : G, (g : G ⧸ K) ∈ MulAction.orbit K (a : G ⧸ K) → h g = 1)
    (h2 : ∀ g : G, (g : G ⧸ K) ∉ MulAction.orbit K (a : G ⧸ K) → h g = 0) (hf : {c : G ⧸ K | h c.out ≠ 0}.Finite) (x : V) :
    heckeVec ρ K h x = Hi.dc ρ K K a x := by
  classical
  have hfin : (MulAction.orbit K (a : G ⧸ K)).Finite := hf.subset fun c hc => by
    rw [Set.mem_setOf_eq, h1 _ (by rwa [QuotientGroup.out_eq'])]; exact one_ne_zero
  letI := hfin.fintype
  rw [Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, ← finsum_eq_sum_of_fintype,
    finsum_set_coe_eq_finsum_mem (f := fun c : G ⧸ K => ρ c.out x), heckeVec]
  refine finsum_congr fun c => ?_
  by_cases hc : c ∈ MulAction.orbit K (a : G ⧸ K)
  · rw [h1 _ (by rwa [QuotientGroup.out_eq'])]; simp [hc]
  · rw [h2 _ (by rwa [QuotientGroup.out_eq'])]; simp [hc]
variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
/- English proof (translation)
Use extensionality with `g`. Use `⟨fun ⟨k, _, e⟩ => ⟨k, e⟩, fun ⟨k, e⟩ => ⟨k, ?_, e⟩⟩` and prove the remaining obligations. Use `haveI : Subsingleton (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) := Ideal.Quotient.subsingleton_iff.2 (by simp)`. Conclude with `Subsingleton.elim _ _`.
-/
private theorem iwahori_level_zero_eq : K1 w 0 = KGL w 2 := by
  ext g
  refine ⟨fun ⟨k, _, e⟩ => ⟨k, e⟩, fun ⟨k, e⟩ => ⟨k, ?_, e⟩⟩
  haveI : Subsingleton (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) :=
    Ideal.Quotient.subsingleton_iff.2 (by simp)
  exact Subsingleton.elim _ _
/- English proof (translation)
Use `hecke_eq_dc ρ _ a _ (fun g hg => ?_) (fun g hg => ?_) (Formalism.UG.P.finite_support_cosets (Final.GLintComm F w 2) (Tj_mem_hecke (unif_spec w) j).2) x` and prove the remaining obligations. Take `⟨k, hk⟩` from `hg`. Establish `h : ((k : GL (Fin 2) (w.adicCompletion F)) * a)⁻¹ * g ∈ KGL w 2` using `QuotientGroup.eq.1 hk`. Rewrite using `[Tj, Set.indicator_of_mem, Pi.one_apply]`. Use `⟨k, k.2, _, h, ?_⟩` and prove the remaining obligations.

Rewrite using `[← ha, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel_left]`. Rewrite using `[Tj, Set.indicator_of_notMem]`. Introduce and unpack `⟨k, hk, k', hk', e⟩`. Use `hg ⟨⟨k, hk⟩, ?_⟩` and prove the remaining obligations. Rewrite `e` using `[← ha, ← Units.val_mul, ← Units.val_mul]`.

Rewrite using `[Units.ext e]`. Conclude with `(QuotientGroup.mk_mul_of_mem (k * a) hk').symm`.
-/
private theorem hecke_Tj {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V)
    (j : ℕ) (a : GL (Fin 2) (w.adicCompletion F)) (ha : a.val = diagJ 2 (atFin w (unif w) : w.adicCompletion F) j) (x : V) :
    heckeVec ρ (KGL w 2) (Tj ℂ 2 (Ov F w) (atFin w (unif w) : w.adicCompletion F) j) x = Hi.dc ρ (KGL w 2) (KGL w 2) a x := by
  refine hecke_eq_dc ρ _ a _ (fun g hg => ?_) (fun g hg => ?_)
    (Formalism.UG.P.finite_support_cosets (Final.GLintComm F w 2) (Tj_mem_hecke (unif_spec w) j).2) x
  · obtain ⟨k, hk⟩ := hg
    have h : ((k : GL (Fin 2) (w.adicCompletion F)) * a)⁻¹ * g ∈ KGL w 2 := QuotientGroup.eq.1 hk
    rw [Tj, Set.indicator_of_mem, Pi.one_apply]
    refine ⟨k, k.2, _, h, ?_⟩
    rw [← ha, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel_left]
  · rw [Tj, Set.indicator_of_notMem]
    rintro ⟨k, hk, k', hk', e⟩
    refine hg ⟨⟨k, hk⟩, ?_⟩
    rw [← ha, ← Units.val_mul, ← Units.val_mul] at e
    rw [Units.ext e]
    exact (QuotientGroup.mk_mul_of_mem (k * a) hk').symm
/- English proof (translation)
Take `⟨α, β, rfl⟩` from `Multiset.card_eq_two.1 h.2.2.1`. Use `⟨α, β, rfl, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [Uop, iwahori_level_zero_eq, ← hecke_Tj w ρ 1 _ (by ext i j; fin_cases i <;> fin_cases j <;> simp [aff, diagJ]), h.2.2.2 _ (unif_spec w) 1 (by norm_num)]`. Use `congr 1`. Rewrite using `[Complex.ofReal_cpow (by positivity)]`.

Establish `: qV F w = normV w` using `rfl`. Simplify using `[satEig, Multiset.esymm, Multiset.powersetCard_one, this]`. Evaluate the numerical expressions using `[add_comm]`. Establish `h2` using `h.2.2.2 _ (unif_spec w) 2 le_rfl set z := GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))`. Apply the tactic sequence `rw [hecke_Tj w ρ 2 z (by ext i j; fin_cases i <;> fin_cases j <;> simp [z, diagJ])] at h2`.

Establish `ho : ∀ q ∈ MulAction.orbit (KGL w 2) (z : _ ⧸ KGL w 2), q = z`. Introduce and unpack `_ ⟨k, rfl⟩`. Express the relevant statement in the definitionally equal form `(((k : GL (Fin 2) (w.adicCompletion F)) * z : GL (Fin 2) (w.adicCompletion F)) : _ ⧸ KGL w 2) = _`. Rewrite using `[← GlobalTheory.CuspRep.scalar_comm]`. Conclude with `QuotientGroup.mk_mul_of_mem _ k.2`.

Rewrite `h2` using `[(Hi.dcSum ℂ _ V ρ _ _ z ((Set.finite_singleton _).subset ho)).1 {z} (fun y hy => by rw [Finset.mem_singleton.1 hy]; exact MulAction.mem_orbit_self _) (fun q hq => ⟨z, ⟨Finset.mem_singleton_self _, (ho q hq).symm⟩, fun y hy => Finset.mem_singleton.1 hy.1⟩) x (GlobalTheory.LGrp.me …`. Rewrite using `[h2]`. Simplify using `[satEig, Multiset.esymm, Multiset.powersetCard_cons, Multiset.powersetCard_one]`.
-/
private theorem sat_two {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V}
    {x : V} {B : Multiset ℂˣ} (h : IsSatVecGL w ρ x B) : ∃ α β : ℂˣ, B = {α, β} ∧
      Uop w ρ 0 x = ((((normV w : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (α + β)) • x ∧
      ρ (GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) x = ((α * β : ℂˣ) : ℂ) • x := by
  obtain ⟨α, β, rfl⟩ := Multiset.card_eq_two.1 h.2.2.1
  refine ⟨α, β, rfl, ?_, ?_⟩
  · rw [Uop, iwahori_level_zero_eq, ← hecke_Tj w ρ 1 _ (by ext i j; fin_cases i <;> fin_cases j <;> simp [aff, diagJ]),
      h.2.2.2 _ (unif_spec w) 1 (by norm_num)]
    congr 1
    rw [Complex.ofReal_cpow (by positivity)]
    have : qV F w = normV w := rfl
    simp [satEig, Multiset.esymm, Multiset.powersetCard_one, this]
    norm_num [add_comm]
  · have h2 := h.2.2.2 _ (unif_spec w) 2 le_rfl
    set z := GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))
    rw [hecke_Tj w ρ 2 z (by ext i j; fin_cases i <;> fin_cases j <;> simp [z, diagJ])] at h2
    have ho : ∀ q ∈ MulAction.orbit (KGL w 2) (z : _ ⧸ KGL w 2), q = z := by
      rintro _ ⟨k, rfl⟩
      change (((k : GL (Fin 2) (w.adicCompletion F)) * z : GL (Fin 2) (w.adicCompletion F)) : _ ⧸ KGL w 2) = _
      rw [← GlobalTheory.CuspRep.scalar_comm]
      exact QuotientGroup.mk_mul_of_mem _ k.2
    rw [(Hi.dcSum ℂ _ V ρ _ _ z ((Set.finite_singleton _).subset ho)).1 {z}
      (fun y hy => by rw [Finset.mem_singleton.1 hy]; exact MulAction.mem_orbit_self _)
      (fun q hq => ⟨z, ⟨Finset.mem_singleton_self _, (ho q hq).symm⟩, fun y hy => Finset.mem_singleton.1 hy.1⟩) x
      (GlobalTheory.LGrp.mem_fixed.1 h.2.1), Finset.sum_singleton] at h2
    rw [h2]
    simp [satEig, Multiset.esymm, Multiset.powersetCard_cons, Multiset.powersetCard_one]
/- English proof (translation)
Use `haveI := Formalism.UG.P.glint_finite_residueField w`. Use `letI := Fintype.ofFinite (IsLocalRing.ResidueField (w.adicCompletionIntegers F))`. Use `choose s hs using (IsLocalRing.residue_surjective (R := w.adicCompletionIntegers F))`. Establish `hS : Set.BijOn (IsLocalRing.residue _) ((Finset.univ.image s : Finset _) : Set (w.adicCompletionIntegers F)) Set.univ`. Use `⟨fun _ _ => trivial, fun u hu u' hu' e => ?_, fun r _ => ⟨s r, by simp, hs r⟩⟩` and prove the remaining obligations.

Take `⟨r, -, rfl⟩` from `Finset.mem_image.1 hu`. Take `⟨r', -, rfl⟩` from `Finset.mem_image.1 hu'`. Rewrite `e` using `[hs, hs]`. Rewrite using `[e]`. Establish `hd : ∀ u, GeneralLinearGroup.det (aff (atFin w (unif w)) u) = atFin w (unif w)` using `fun u => Units.ext (by simp [aff, Matrix.det_fin_two])`.

Rewrite using `[(uopSum F w V ρ c x hx).2 _ hS, (uopSum F w W ρ' c _ hx').2 _ hS, map_add, map_sum, smul_add, Finset.smul_sum]`. Simplify using `only [hf, hd]`. Use `congr 1`. Use `split_ifs`. Rewrite using `[map_mul GeneralLinearGroup.det, map_inv, hd]`.

Use `congr 3`. Conclude with `Units.ext (by simp [sq])`. Simplify using the standard rewrite rules.
-/
private theorem uop_map {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V} {ρ' : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) W}
    (f : V →ₗ[ℂ] W) (χ : (w.adicCompletion F)ˣ →* ℂˣ)
    (hf : ∀ g x, ρ' g (f x) = ((χ (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • f (ρ g x)) (c : ℕ) (x : V)
    (hx : x ∈ Hi.fixd ρ (K1 w c)) (hx' : f x ∈ Hi.fixd ρ' (K1 w c)) :
    Uop w ρ' c (f x) = ((χ (atFin w (unif w)) : ℂˣ) : ℂ) • f (Uop w ρ c x) := by
  classical
  haveI := Formalism.UG.P.glint_finite_residueField w
  letI := Fintype.ofFinite (IsLocalRing.ResidueField (w.adicCompletionIntegers F))
  choose s hs using (IsLocalRing.residue_surjective (R := w.adicCompletionIntegers F))
  have hS : Set.BijOn (IsLocalRing.residue _) ((Finset.univ.image s : Finset _) : Set (w.adicCompletionIntegers F)) Set.univ := by
    refine ⟨fun _ _ => trivial, fun u hu u' hu' e => ?_, fun r _ => ⟨s r, by simp, hs r⟩⟩
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨r', -, rfl⟩ := Finset.mem_image.1 hu'
    rw [hs, hs] at e
    rw [e]
  have hd : ∀ u, GeneralLinearGroup.det (aff (atFin w (unif w)) u) = atFin w (unif w) := fun u =>
    Units.ext (by simp [aff, Matrix.det_fin_two])
  rw [(uopSum F w V ρ c x hx).2 _ hS, (uopSum F w W ρ' c _ hx').2 _ hS, map_add, map_sum, smul_add, Finset.smul_sum]
  simp only [hf, hd]
  congr 1
  split_ifs
  · rw [map_mul GeneralLinearGroup.det, map_inv, hd]
    congr 3
    exact Units.ext (by simp [sq])
  · simp
/- English proof (translation)
Establish `h` using `GlobalTheory.CuspRep.finId_det_locGL w (GeneralLinearGroup.scalar (Fin 1) x)`. Rewrite `h`, the goal using `[locGL, GlobalTheory.CuspRep.cornerGL_scalar]`. Rewrite using `[finGL, GlobalTheory.CuspRep.cornerGL_scalar]`. Use `congr 1`. Conclude with `(congrArg (finId F) (GlobalTheory.CuspRep.CG.det_oneByOne _)).symm.trans (h.trans (congrArg (localIdele F w) (GlobalTheory.CuspRep.CG.det_oneByOne _)))`.
-/
private theorem fin_scalar (x : (w.adicCompletion F)ˣ) :
    finGL F 2 (locGL F 2 w (GeneralLinearGroup.scalar (Fin 2) x)) = GeneralLinearGroup.scalar (Fin 2) (localIdele F w x) := by
  have h := GlobalTheory.CuspRep.finId_det_locGL w (GeneralLinearGroup.scalar (Fin 1) x)
  rw [locGL, GlobalTheory.CuspRep.cornerGL_scalar] at h ⊢
  rw [finGL, GlobalTheory.CuspRep.cornerGL_scalar]
  congr 1
  exact (congrArg (finId F) (GlobalTheory.CuspRep.CG.det_oneByOne _)).symm.trans
    (h.trans (congrArg (localIdele F w) (GlobalTheory.CuspRep.CG.det_oneByOne _)))
/- English proof (translation)
Take `⟨k, -, rfl⟩` from `hk`. Rewrite using `[IsUnitAt, GlobalTheory.CuspRep.det_map]`. Conclude with `HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 (Units.isUnit _)`.
-/
private theorem unit_det {c : ℕ} {k : GL (Fin 2) (w.adicCompletion F)} (hk : k ∈ K1 w c) :
    IsUnitAt w (GeneralLinearGroup.det k) := by
  obtain ⟨k, -, rfl⟩ := hk
  rw [IsUnitAt, GlobalTheory.CuspRep.det_map]
  exact HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 (Units.isUnit _)
end Loc
section Inf
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
open GlobalTheory.HeckeGal.Model GlobalTheory.Mem.Chr.CharModel
/- English proof (translation)
Use `TR.expo_eq_of_exp _ v s fun t => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Complex.exp (s * logNorm F (TR.infId F (TR.expU (Pi.single v t)))) = _`. Establish `h1 : finPart F (TR.infId F (TR.expU (Pi.single v t))) = 1` using `Units.ext (by`. Express the relevant statement in the definitionally equal form `(1 : Af F) - 0 + 0 = 1`. Use the proof step `simp)`.

Establish `h2 : ∀ u, ‖(infPart F (TR.infId F (TR.expU (Pi.single v t)))).val u‖ = Real.exp ((Pi.single v t : TR.Rinf F) u)` using `fun u => by`. Establish `e : (infPart F (TR.infId F (TR.expU (Pi.single v t)))).val = TR.infEq F (TR.expU (Pi.single v t)).val`. Express the relevant statement in the definitionally equal form `1 - TR.infEq F 1 + TR.infEq F _ = _`. Simplify using the standard rewrite rules. Rewrite using `[e]`.

Conclude with `(((InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal u)).symm.isometry.norm_map_of_map_zero (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal u)).symm)) _).trans (Real.norm_of_nonneg (Real.exp_pos _).le)`. Rewrite using `[logNorm, h1, logFin_one, logInf]`. Simplify using `[h2, Pi.single_apply, InfinitePlace.mult, IsTotallyReal.isReal]`.
-/
private theorem expo_abs (s : ℝ) (v : InfinitePlace F) : TR.expo (absPow F s) v = s := by
  classical
  refine TR.expo_eq_of_exp _ v s fun t => ?_
  change Complex.exp (s * logNorm F (TR.infId F (TR.expU (Pi.single v t)))) = _
  have h1 : finPart F (TR.infId F (TR.expU (Pi.single v t))) = 1 := Units.ext (by
    change (1 : Af F) - 0 + 0 = 1
    simp)
  have h2 : ∀ u, ‖(infPart F (TR.infId F (TR.expU (Pi.single v t)))).val u‖ = Real.exp ((Pi.single v t : TR.Rinf F) u) := fun u => by
    have e : (infPart F (TR.infId F (TR.expU (Pi.single v t)))).val = TR.infEq F (TR.expU (Pi.single v t)).val := by
      change 1 - TR.infEq F 1 + TR.infEq F _ = _
      simp
    rw [e]
    exact (((InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal u)).symm.isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal u)).symm)) _).trans
      (Real.norm_of_nonneg (Real.exp_pos _).le)
  rw [logNorm, h1, logFin_one, logInf]
  simp [h2, Pi.single_apply, InfinitePlace.mult, IsTotallyReal.isReal]
omit [IsTotallyReal F] in
/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Use `set x := ReciprocityTheory.Neutral.Bridge.HCFR.infIdele F v (-1)`. Establish `h0 : logNorm F 1 = 0` using `by have := logNorm_mul F 1 1; rw [mul_one] at this; linarith`. Establish `h` using `logNorm_mul F x x`. Rewrite `h` using `[← map_mul, neg_mul_neg, mul_one, map_one, h0]`.

Express the relevant statement in the definitionally equal form `Complex.exp (s * logNorm F x) = 1`. Rewrite using `[show logNorm F x = 0 by linarith]`. Simplify using the standard rewrite rules.
-/
private theorem sign_abs (s : ℝ) (v : InfinitePlace F) : (absPow F s).locInf v (-1) = 1 := by
  refine Units.ext ?_
  set x := ReciprocityTheory.Neutral.Bridge.HCFR.infIdele F v (-1)
  have h0 : logNorm F 1 = 0 := by have := logNorm_mul F 1 1; rw [mul_one] at this; linarith
  have h := logNorm_mul F x x
  rw [← map_mul, neg_mul_neg, mul_one, map_one, h0] at h
  change Complex.exp (s * logNorm F x) = 1
  rw [show logNorm F x = 0 by linarith]
  simp
end Inf
section Sign
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
private def rot (θ : TR.Rinf F) : GL (Fin 2) (TR.Rinf F) where
  val := !![fun v => Real.cos (θ v), fun v => Real.sin (θ v); fun v => -Real.sin (θ v), fun v => Real.cos (θ v)]
  inv := !![fun v => Real.cos (θ v), fun v => -Real.sin (θ v); fun v => Real.sin (θ v), fun v => Real.cos (θ v)]
  val_inv := by
    ext i j v
    have := Real.sin_sq_add_cos_sq (θ v)
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> linarith
  inv_val := by
    ext i j v
    have := Real.sin_sq_add_cos_sq (θ v)
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> linarith
omit [NumberField F] [IsTotallyReal F] in
/- English proof (translation)
Use extensionality with `i j v`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [rot, Matrix.mul_apply, Fin.sum_univ_succ, Real.cos_add, Real.sin_add] <;> ring`.
-/
private theorem rot_add (θ θ' : TR.Rinf F) : rot (θ + θ') = rot θ * rot θ' := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot, Matrix.mul_apply, Fin.sum_univ_succ, Real.cos_add, Real.sin_add] <;> ring
/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `h0 (Subtype.ext (funext h))`. Use `set e : TR.Rinf F := Pi.single v 1 with he`.

Establish `hr0 : rot ((0 : ℝ) • e) = 1`. Use extensionality with `i j u`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [rot]`. Establish `hd0 : ∀ g, HasDerivAt (fun t : ℝ => φ.1 (g * TR.infGL F 2 (rot (t • e)))) (Complex.I * k * φ.1 g) 0` using `fun g => by`. Establish `h1` using `TR.hasDerivAt_curve φ g (fun t : ℝ => rot (t • e)) (TR.toL (Matrix.single 0 1 e) - TR.toL (Matrix.single 1 0 e)) hr0 (by`.

Use `hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun u => ?_` and prove the remaining obligations. Establish `hc` using `((hasDerivAt_id (0 : ℝ)).mul_const (e u)).cos`. Establish `hs` using `((hasDerivAt_id (0 : ℝ)).mul_const (e u)).sin`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Simplify `hc` using `[rot]`.

Simplify `hs` using `[rot]`. Simplify `hs.fun_neg` using `[rot]`. Simplify `hc)` using `[rot]`. Rewrite `h1` using `[← TR.lie_apply, map_sub]`. Conclude with `h1.congr_deriv (congrArg (fun x : TR.Sm F 2 => x.1 g) (hφ.wt v))`.

Use `set f : ℝ → ℂ := fun t => φ.1 (g * TR.infGL F 2 (rot (t • e))) with hf`. Establish `hd : ∀ t, HasDerivAt f (Complex.I * k * f t) t` using `fun t => by`. Establish `h1` using `HasDerivAt.comp_sub_const t t ((sub_self t).symm ▸ hd0 (g * TR.infGL F 2 (rot (t • e))))`. Use `h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Simplify using `only [hf]`.

Rewrite using `[mul_assoc, ← map_mul, ← rot_add, ← add_smul, add_sub_cancel]`. Establish `hc : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f t * Complex.exp (-(Complex.I * k * t))) 0 t` using `fun t => by`. Establish `h1` using `(hd t).mul (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (Complex.I * k)).fun_neg.cexp)`. Conclude with `h1.congr_deriv (by simp; ring)`. Establish `h2` using `is_const_of_deriv_eq_zero (fun t => (hc t).differentiableAt) (fun t => (hc t).deriv) Real.pi 0`.

Establish `hu : (1 - 2 * e) * (1 - 2 * e) = 1`. Use function extensionality and compare the values at `w`. Distinguish the cases in `h : w = v`. Substitute `h` using the available equality. Simplify using `[he]`.

Evaluate the numerical expressions. Simplify using `[he, h]`. Set `u : (TR.Rinf F)ˣ` to `⟨1 - 2 * e, 1 - 2 * e, hu, hu⟩`. Establish `h3 : rot (Real.pi • e) = GeneralLinearGroup.scalar (Fin 2) u`. Use extensionality with `i j w`.

Distinguish the cases in `h : w = v`. Apply the tactic sequence `subst h fin_cases i <;> fin_cases j <;> simp [rot, u, he] <;> norm_num`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [rot, u, he, h]`. Establish `h4 : Units.map (GlobalTheory.CuspRep.corner (TR.sInf F)) u = ReciprocityTheory.Neutral.Bridge.HCFR.infIdele F v (-1)`. Use `Units.ext (Prod.ext (funext fun w => ?_) ?_)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(1 - TR.infEq F 1 + TR.infEq F (1 - 2 * e)) w = Pi.mulSingle (M := fun w : InfinitePlace F => w.Completion) v (-1) w`. Rewrite using `[map_one, sub_self, zero_add]`. Express the relevant statement in the definitionally equal form `(InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm ((1 - 2 * e) w) = _`. Distinguish the cases in `h : w = v`. Substitute `h` using the available equality.

Rewrite using `[show (1 - 2 * e) w = -1 by simp [he]; norm_num]`. Simplify using the standard rewrite rules. Simplify using `[he, h]`. Express the relevant statement in the definitionally equal form `(1 : Af F) - 0 + 0 = 1`. Simplify using the standard rewrite rules.

Simplify using `only [hf, hr0, h3, TR.infGL, map_one, mul_one] at h2`. Rewrite `h2` using `[GlobalTheory.CuspRep.cornerGL_scalar, h4, ← GlobalTheory.CuspRep.scalar_comm, hφ.cent]`. Rewrite `h2` using `[Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one, Complex.exp_neg, mul_right_comm, mul_eq_right₀ hg, mul_inv_eq_one₀ (Complex.exp_ne_zero _)]`. Conclude with `h2`.
-/
private theorem sign_hol {k c} {ω : HChar F} {φ : TR.Sm F 2} (hφ : IsHol k c ω φ) (h0 : φ ≠ 0) (v : InfinitePlace F) :
    ((ω.locInf v (-1) : ℂˣ) : ℂ) = Complex.exp (Complex.I * k * Real.pi) := by
  classical
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (Subtype.ext (funext h))
  set e : TR.Rinf F := Pi.single v 1 with he
  have hr0 : rot ((0 : ℝ) • e) = 1 := by
    ext i j u
    fin_cases i <;> fin_cases j <;> simp [rot]
  have hd0 : ∀ g, HasDerivAt (fun t : ℝ => φ.1 (g * TR.infGL F 2 (rot (t • e)))) (Complex.I * k * φ.1 g) 0 := fun g => by
    have h1 := TR.hasDerivAt_curve φ g (fun t : ℝ => rot (t • e))
      (TR.toL (Matrix.single 0 1 e) - TR.toL (Matrix.single 1 0 e)) hr0 (by
        refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun u => ?_
        have hc := ((hasDerivAt_id (0 : ℝ)).mul_const (e u)).cos
        have hs := ((hasDerivAt_id (0 : ℝ)).mul_const (e u)).sin
        fin_cases i <;> fin_cases j
        · simpa [rot] using hc
        · simpa [rot] using hs
        · simpa [rot] using hs.fun_neg
        · simpa [rot] using hc)
    rw [← TR.lie_apply, map_sub] at h1
    exact h1.congr_deriv (congrArg (fun x : TR.Sm F 2 => x.1 g) (hφ.wt v))
  set f : ℝ → ℂ := fun t => φ.1 (g * TR.infGL F 2 (rot (t • e))) with hf
  have hd : ∀ t, HasDerivAt f (Complex.I * k * f t) t := fun t => by
    have h1 := HasDerivAt.comp_sub_const t t ((sub_self t).symm ▸ hd0 (g * TR.infGL F 2 (rot (t • e))))
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [hf]
    rw [mul_assoc, ← map_mul, ← rot_add, ← add_smul, add_sub_cancel]
  have hc : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f t * Complex.exp (-(Complex.I * k * t))) 0 t := fun t => by
    have h1 := (hd t).mul (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (Complex.I * k)).fun_neg.cexp)
    exact h1.congr_deriv (by simp; ring)
  have h2 := is_const_of_deriv_eq_zero (fun t => (hc t).differentiableAt) (fun t => (hc t).deriv) Real.pi 0
  have hu : (1 - 2 * e) * (1 - 2 * e) = 1 := by
    funext w
    by_cases h : w = v
    · subst h; simp [he]; norm_num
    · simp [he, h]
  let u : (TR.Rinf F)ˣ := ⟨1 - 2 * e, 1 - 2 * e, hu, hu⟩
  have h3 : rot (Real.pi • e) = GeneralLinearGroup.scalar (Fin 2) u := by
    ext i j w
    by_cases h : w = v
    · subst h
      fin_cases i <;> fin_cases j <;> simp [rot, u, he] <;> norm_num
    · fin_cases i <;> fin_cases j <;> simp [rot, u, he, h]
  have h4 : Units.map (GlobalTheory.CuspRep.corner (TR.sInf F)) u = ReciprocityTheory.Neutral.Bridge.HCFR.infIdele F v (-1) := by
    refine Units.ext (Prod.ext (funext fun w => ?_) ?_)
    · change (1 - TR.infEq F 1 + TR.infEq F (1 - 2 * e)) w = Pi.mulSingle (M := fun w : InfinitePlace F => w.Completion) v (-1) w
      rw [map_one, sub_self, zero_add]
      change (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm ((1 - 2 * e) w) = _
      by_cases h : w = v
      · subst h
        rw [show (1 - 2 * e) w = -1 by simp [he]; norm_num]
        simp
      · simp [he, h]
    · change (1 : Af F) - 0 + 0 = 1
      simp
  simp only [hf, hr0, h3, TR.infGL, map_one, mul_one] at h2
  rw [GlobalTheory.CuspRep.cornerGL_scalar, h4, ← GlobalTheory.CuspRep.scalar_comm, hφ.cent] at h2
  rw [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one, Complex.exp_neg, mul_right_comm,
    mul_eq_right₀ hg, mul_inv_eq_one₀ (Complex.exp_ne_zero _)] at h2
  exact h2
end Sign
/- English proof (translation)
Introduce `P F _ _ _ k hk c ω hω φ lam hφ hcusp`. Take `⟨h1, hcap⟩` from `holCap F k c ω hω φ hφ.hol`. Take `⟨π₀, ψ, hψ, h0, hz⟩` from `proj hφ.ne (P.ssR F 2 φ hcusp ⟨0, by rw [h1, zero_smul]⟩)`. Use `set ν := GlobalTheory.HeckeGal.Model.absPow F (1 - (k : ℝ) / 2) with hν`. Take `⟨hν1, hν2, -⟩` from `GlobalTheory.HeckeGal.Model.absPow_isAbsPow F (1 - (k : ℝ) / 2)`.

Rewrite `hν1`, `hν2` using `[← hν]`. Establish `hq : ∀ w : Pl F, (0 : ℝ) < normV w` using `fun w => Nat.cast_pos.2 (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm w))`. Establish `hν3 : ∀ w, ((ν.val w : ℂˣ) : ℂ) = (((normV w : ℝ) ^ ((k : ℝ) / 2 - 1) : ℝ) : ℂ)` using `fun w => by`. Rewrite using `[hν2, Complex.ofReal_cpow (hq w).le, ← Complex.ofReal_neg, neg_sub]`. Both sides reduce to the same expression.

Use `set π := π₀.twist ν`. Use `set x₀ : π₀.V := ⟨ψ, hψ⟩`. Use `set T := π₀.toTwist ν`. Establish `hx0 : T x₀ ≠ 0` using `(map_ne_zero_iff _ T.injective).2 fun e => h0 (congrArg Subtype.val e)`. Establish `hact : ∀ w g y, π.locRep w g (T y) = ((ν.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • T (π₀.locRep w g y)` using `fun w g y => (TR.CuspSub.finPart_toTwist ν _ y).trans (by rw [TR.CuspSub.chiDet_locGL]; rfl)`.

Establish `hloc : ∀ w g (a : ℂ), locSm F w g φ = a • φ → π₀.locRep w g x₀ = a • x₀` using `fun w g a h => Subtype.ext (hz _ (fun V hV => hV (.fin (locGL F 2 w g))) a h)`. Establish `hfix₀ : ∀ w, x₀ ∈ Hi.fixd (π₀.locRep w) (K1 w (c w))` using `fun w u hu => (hloc w u 1 ((hφ.hol.level w u hu).trans (one_smul _ _).symm)).trans (one_smul _ _)`. Establish `hfix : ∀ w, T x₀ ∈ Hi.fixd (π.locRep w) (K1 w (c w))` using `fun w u hu => by`. Rewrite using `[hact, hν1 w _ (unit_det w hu), hfix₀ w u hu, Units.val_one, one_smul]`. Establish `hU : ∀ w, Uop w (π.locRep w) (c w) (T x₀) = lam w • T x₀` using `fun w => by`.

Establish `h2` using `hz (Sd.hk k w (c w)) (fun V hV y hy => V.smul_mem _ (finsum_induction (fun z : Module.End ℂ (TR.Sm F 2) => z y ∈ V) V.zero_mem (fun _ _ => V.add_mem) fun q => hV (.fin _) y hy)) _ (hφ.eig w)`. Establish `h3` using `uop_map w (ρ' := locSm F w) π₀.V.subtype 1 (fun g y => (one_smul _ _).symm) (c w) x₀ (hfix₀ w) fun u hu => congrArg Subtype.val (hfix₀ w u hu)`. Use `(uop_map w T.toLinearMap (ν.loc w) (hact w) (c w) x₀ (hfix₀ w) (hfix w)).trans ?_` and prove the remaining obligations. Rewrite using `[LinearEquiv.coe_coe, ← map_smul T, ← map_smul T]`. Use `congrArg T (Subtype.ext ?_)` and prove the remaining obligations.

Use `Eq.trans ?_ h2` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((ν.val w : ℂˣ) : ℂ) • π₀.V.subtype (Uop w (π₀.locRep w) (c w) x₀) = (((normV w : ℝ) ^ ((k : ℝ) / 2 - 1) : ℝ) : ℂ) • Uop w (locSm F w) (c w) (π₀.V.subtype x₀)`. Rewrite using `[h3, hν3]`. Conclude with `congrArg _ (one_smul _ _).symm`. Establish `hZ : ∀ w, π.locRep w (GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) (T x₀) = (((ω * ν * ν).val w : ℂˣ) : ℂ) • T x₀` using `fun w => by`.

Rewrite using `[hact, hloc w _ (ω.val w : ℂˣ) (Subtype.ext (funext fun g => by`. Express the relevant statement in the definitionally equal form `φ.1 (g * finGL F 2 (locGL F 2 w _)) = _`. Rewrite using `[fin_scalar, ← GlobalTheory.CuspRep.scalar_comm, hφ.hol.cent]`. Use the proof step `rfl)), map_smul, smul_smul,`. Use `show GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) = atFin w (unif w) * atFin w (unif w) from Units.ext (by simp [sq]), map_mul, mul_comm, ← Units.val_mul, ← mul_assoc]`.

Both sides reduce to the same expression. Establish `hsat : ∀ w, (∀ u ∈ GlobalTheory.LFun.KGL w 2, π.locRep w u (T x₀) = T x₀) → ∃ α β : ℂˣ, π.HasSat w {α, β} ∧ Uop w (π.locRep w) 0 (T x₀) = ((((normV w : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (α + β)) • T x₀ ∧ α * β = (ω * ν * ν).val w` using `fun w h => by`. Take `⟨B, hB⟩` from `exists_sat P.toClassicalTheorems π w ⟨_, hx0, h⟩`. Take `⟨α, β, rfl, h2, h3⟩` from `sat_two w (hB.2 _ (GlobalTheory.LGrp.mem_fixed.2 h) hx0)`. Conclude with `⟨α, β, hB, h2, Units.ext (smul_left_injective ℂ hx0 (h3.symm.trans (hZ w)))⟩`.

Establish `hinf : ∀ v, π.HasInfChar v (infOf ![0, 1 - (k : ℤ)])` using `fun v => by`. Establish `h2 : π₀.HasInfChar v {((k : ℂ) - 1) / 2, -(((k : ℂ) - 1) / 2)}` using `⟨rfl, fun u => cap_all π₀ hψ h0 v u _ (by`. Rewrite using `[hz _ (fun V hV => TR.Zalg_stable (fun X => hV (.lie X)) (Algebra.subset_adjoin ⟨v, u, rfl⟩)) _ (hcap v u)]`. Simplify using `[sub_eq_add_neg])⟩`. Use `h2.twist ν using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[hν, expo_abs]`. Simplify using `only [infOf, Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]`. Express the relevant statement in the definitionally equal form `_ ::ₘ ({_} : Multiset ℂ) = _`. Apply the tactic sequence `refine congrArg₂ _ ?_ (congrArg _ ?_) <;> simp <;> ring`. Use `⟨π, fun v => ⟨_, hinf v, ?_, fun z hz => ?_⟩, ⟨ω * ν * ν, fun v v' => ?_, ?_⟩, hinf, fun w => ⟨_, hx0, hfix w, hU w⟩, fun w hw => ?_⟩` and prove the remaining obligations.

Use `Multiset.Nodup.map (fun i j e => ?_) Finset.univ.nodup` and prove the remaining obligations. Establish `e' : ![0, 1 - (k : ℤ)] i = ![0, 1 - (k : ℤ)] j` using `by exact_mod_cast add_left_cancel e`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp at e' ⊢ <;> omega`. Take `⟨i, -, rfl⟩` from `Multiset.mem_map.1 hz`. Conclude with `⟨_, add_comm _ _⟩`.

Simplify using `only [HChar.locInf_mul, hν, sign_abs, mul_one]`. Conclude with `Units.ext ((sign_hol hφ.hol hφ.ne v).trans (sign_hol hφ.hol hφ.ne v').symm)`. Take `⟨B, hl, hr, hf, hc, hX⟩` from `P.gkR F 2 π`. Use `TR.CuspSub.isSelfDualBy_of_iso B hl hr hf hc hX (P.smoR F 2 one_le_two _ _ ?_)` and prove the remaining obligations. Use `filter_upwards [GlobalTheory.CuspRep.LocSph.eventually_mem ((π.isSmooth_finPart (T x₀)).mem_nhds (show π.finPart 1 (T x₀) = T x₀ by rw [map_one]; rfl)), Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified (ω * ν * ν))] with w hw hu`.

Take `⟨α, β, h2, -, h3⟩` from `hsat w (by rintro _ ⟨g, rfl⟩; exact hw g)`. Establish `e : (({α, β} : Multiset ℂˣ).map (·⁻¹)).map (· * (ω * ν * ν).val w) = {α, β}`. Rewrite using `[← h3, Multiset.pair_comm α β]`. Simplify using `only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, inv_mul_cancel_left]`. Rewrite using `[mul_comm α β, inv_mul_cancel_left]`.

Conclude with `Multiset.pair_comm α β`. Conclude with `⟨_, h2, e ▸ h2.dual.twist hu⟩`. Take `⟨α, β, h2, h3, h4⟩` from `hsat w (by have := hfix w; rwa [hw, iwahori_level_zero_eq] at this)`. Use `⟨_, h2, ?_⟩` and prove the remaining obligations. Establish `h5` using `hU w`.

Rewrite `h5` using `[hw]`. Establish `h6` using `smul_left_injective ℂ hx0 (h5.symm.trans h3)`. Establish `h7 : (α : ℂ) * β = (ω.val w : ℂˣ) * (ν.val w : ℂˣ) * (ν.val w : ℂˣ)` using `congrArg Units.val h4`. Use `set r : ℂ := (((normV w : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) with hr`. Establish `h8 : r * r * ((ν.val w : ℂˣ) * (ν.val w : ℂˣ)) = (normV w : ℂ) ^ (k - 1)`.

Rewrite using `[hν3, hr, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.rpow_add (hq w), ← Real.rpow_add (hq w), ← Real.rpow_add (hq w), show (1 / 2 + 1 / 2 + ((k : ℝ) / 2 - 1 + (k / 2 - 1))) = ((k - 1 : ℕ) : ℝ) by`. Rewrite using `[Nat.cast_sub (by omega)]; push_cast; ring, Real.rpow_natCast]`. Simplify using the standard rewrite rules. Establish `h9 : algSat 2 (normV w) {α, β} = {r * α, r * β}`. Simplify using `only [algSat, hr, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]`.

Evaluate the numerical expressions. Rewrite using `[h9, h6, ← h8, show (ω.val w : ℂˣ) * (r * r * (((ν.val w : ℂˣ) : ℂ) * (ν.val w : ℂˣ))) = r * α * (r * β) by`. Take the linear combination `(-(r * r)) * h7]`. Simplify using `only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, map_mul, map_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Sd.holRep_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Sd.HolRep := by
  intro P F _ _ _ k hk c ω hω φ lam hφ hcusp
  obtain ⟨h1, hcap⟩ := holCap F k c ω hω φ hφ.hol
  obtain ⟨π₀, ψ, hψ, h0, hz⟩ := proj hφ.ne (P.ssR F 2 φ hcusp ⟨0, by rw [h1, zero_smul]⟩)
  set ν := GlobalTheory.HeckeGal.Model.absPow F (1 - (k : ℝ) / 2) with hν
  obtain ⟨hν1, hν2, -⟩ := GlobalTheory.HeckeGal.Model.absPow_isAbsPow F (1 - (k : ℝ) / 2)
  rw [← hν] at hν1 hν2
  have hq : ∀ w : Pl F, (0 : ℝ) < normV w := fun w =>
    Nat.cast_pos.2 (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm w))
  have hν3 : ∀ w, ((ν.val w : ℂˣ) : ℂ) = (((normV w : ℝ) ^ ((k : ℝ) / 2 - 1) : ℝ) : ℂ) := fun w => by
    rw [hν2, Complex.ofReal_cpow (hq w).le, ← Complex.ofReal_neg, neg_sub]
    rfl
  set π := π₀.twist ν
  set x₀ : π₀.V := ⟨ψ, hψ⟩
  set T := π₀.toTwist ν
  have hx0 : T x₀ ≠ 0 := (map_ne_zero_iff _ T.injective).2 fun e => h0 (congrArg Subtype.val e)
  have hact : ∀ w g y, π.locRep w g (T y) = ((ν.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • T (π₀.locRep w g y) :=
    fun w g y => (TR.CuspSub.finPart_toTwist ν _ y).trans (by rw [TR.CuspSub.chiDet_locGL]; rfl)
  have hloc : ∀ w g (a : ℂ), locSm F w g φ = a • φ → π₀.locRep w g x₀ = a • x₀ := fun w g a h =>
    Subtype.ext (hz _ (fun V hV => hV (.fin (locGL F 2 w g))) a h)
  have hfix₀ : ∀ w, x₀ ∈ Hi.fixd (π₀.locRep w) (K1 w (c w)) := fun w u hu =>
    (hloc w u 1 ((hφ.hol.level w u hu).trans (one_smul _ _).symm)).trans (one_smul _ _)
  have hfix : ∀ w, T x₀ ∈ Hi.fixd (π.locRep w) (K1 w (c w)) := fun w u hu => by
    rw [hact, hν1 w _ (unit_det w hu), hfix₀ w u hu, Units.val_one, one_smul]
  have hU : ∀ w, Uop w (π.locRep w) (c w) (T x₀) = lam w • T x₀ := fun w => by
    have h2 := hz (Sd.hk k w (c w)) (fun V hV y hy => V.smul_mem _
      (finsum_induction (fun z : Module.End ℂ (TR.Sm F 2) => z y ∈ V) V.zero_mem (fun _ _ => V.add_mem)
        fun q => hV (.fin _) y hy)) _ (hφ.eig w)
    have h3 := uop_map w (ρ' := locSm F w) π₀.V.subtype 1 (fun g y => (one_smul _ _).symm) (c w) x₀ (hfix₀ w)
      fun u hu => congrArg Subtype.val (hfix₀ w u hu)
    refine (uop_map w T.toLinearMap (ν.loc w) (hact w) (c w) x₀ (hfix₀ w) (hfix w)).trans ?_
    rw [LinearEquiv.coe_coe, ← map_smul T, ← map_smul T]
    refine congrArg T (Subtype.ext ?_)
    refine Eq.trans ?_ h2
    change ((ν.val w : ℂˣ) : ℂ) • π₀.V.subtype (Uop w (π₀.locRep w) (c w) x₀) =
      (((normV w : ℝ) ^ ((k : ℝ) / 2 - 1) : ℝ) : ℂ) • Uop w (locSm F w) (c w) (π₀.V.subtype x₀)
    rw [h3, hν3]
    exact congrArg _ (one_smul _ _).symm
  have hZ : ∀ w, π.locRep w (GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) (T x₀) =
      (((ω * ν * ν).val w : ℂˣ) : ℂ) • T x₀ := fun w => by
    rw [hact, hloc w _ (ω.val w : ℂˣ) (Subtype.ext (funext fun g => by
      change φ.1 (g * finGL F 2 (locGL F 2 w _)) = _
      rw [fin_scalar, ← GlobalTheory.CuspRep.scalar_comm, hφ.hol.cent]
      rfl)), map_smul, smul_smul,
      show GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) =
        atFin w (unif w) * atFin w (unif w) from Units.ext (by simp [sq]), map_mul, mul_comm, ← Units.val_mul, ← mul_assoc]
    rfl
  have hsat : ∀ w, (∀ u ∈ GlobalTheory.LFun.KGL w 2, π.locRep w u (T x₀) = T x₀) → ∃ α β : ℂˣ, π.HasSat w {α, β} ∧
      Uop w (π.locRep w) 0 (T x₀) = ((((normV w : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (α + β)) • T x₀ ∧
      α * β = (ω * ν * ν).val w := fun w h => by
    obtain ⟨B, hB⟩ := exists_sat P.toClassicalTheorems π w ⟨_, hx0, h⟩
    obtain ⟨α, β, rfl, h2, h3⟩ := sat_two w (hB.2 _ (GlobalTheory.LGrp.mem_fixed.2 h) hx0)
    exact ⟨α, β, hB, h2, Units.ext (smul_left_injective ℂ hx0 (h3.symm.trans (hZ w)))⟩
  have hinf : ∀ v, π.HasInfChar v (infOf ![0, 1 - (k : ℤ)]) := fun v => by
    have h2 : π₀.HasInfChar v {((k : ℂ) - 1) / 2, -(((k : ℂ) - 1) / 2)} := ⟨rfl, fun u => cap_all π₀ hψ h0 v u _ (by
      rw [hz _ (fun V hV => TR.Zalg_stable (fun X => hV (.lie X)) (Algebra.subset_adjoin ⟨v, u, rfl⟩)) _ (hcap v u)]
      simp [sub_eq_add_neg])⟩
    convert h2.twist ν using 1
    rw [hν, expo_abs]
    simp only [infOf, Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton]
    change _ ::ₘ ({_} : Multiset ℂ) = _
    refine congrArg₂ _ ?_ (congrArg _ ?_) <;> simp <;> ring
  refine ⟨π, fun v => ⟨_, hinf v, ?_, fun z hz => ?_⟩, ⟨ω * ν * ν, fun v v' => ?_, ?_⟩, hinf,
    fun w => ⟨_, hx0, hfix w, hU w⟩, fun w hw => ?_⟩
  · refine Multiset.Nodup.map (fun i j e => ?_) Finset.univ.nodup
    have e' : ![0, 1 - (k : ℤ)] i = ![0, 1 - (k : ℤ)] j := by exact_mod_cast add_left_cancel e
    fin_cases i <;> fin_cases j <;> simp at e' ⊢ <;> omega
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
    exact ⟨_, add_comm _ _⟩
  · simp only [HChar.locInf_mul, hν, sign_abs, mul_one]
    exact Units.ext ((sign_hol hφ.hol hφ.ne v).trans (sign_hol hφ.hol hφ.ne v').symm)
  · obtain ⟨B, hl, hr, hf, hc, hX⟩ := P.gkR F 2 π
    refine TR.CuspSub.isSelfDualBy_of_iso B hl hr hf hc hX (P.smoR F 2 one_le_two _ _ ?_)
    filter_upwards [GlobalTheory.CuspRep.LocSph.eventually_mem ((π.isSmooth_finPart (T x₀)).mem_nhds
        (show π.finPart 1 (T x₀) = T x₀ by rw [map_one]; rfl)),
      Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified (ω * ν * ν))] with w hw hu
    obtain ⟨α, β, h2, -, h3⟩ := hsat w (by rintro _ ⟨g, rfl⟩; exact hw g)
    have e : (({α, β} : Multiset ℂˣ).map (·⁻¹)).map (· * (ω * ν * ν).val w) = {α, β} := by
      rw [← h3, Multiset.pair_comm α β]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, inv_mul_cancel_left]
      rw [mul_comm α β, inv_mul_cancel_left]
      exact Multiset.pair_comm α β
    exact ⟨_, h2, e ▸ h2.dual.twist hu⟩
  · obtain ⟨α, β, h2, h3, h4⟩ := hsat w (by have := hfix w; rwa [hw, iwahori_level_zero_eq] at this)
    refine ⟨_, h2, ?_⟩
    have h5 := hU w
    rw [hw] at h5
    have h6 := smul_left_injective ℂ hx0 (h5.symm.trans h3)
    have h7 : (α : ℂ) * β = (ω.val w : ℂˣ) * (ν.val w : ℂˣ) * (ν.val w : ℂˣ) := congrArg Units.val h4
    set r : ℂ := (((normV w : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) with hr
    have h8 : r * r * ((ν.val w : ℂˣ) * (ν.val w : ℂˣ)) = (normV w : ℂ) ^ (k - 1) := by
      rw [hν3, hr, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.rpow_add (hq w),
        ← Real.rpow_add (hq w), ← Real.rpow_add (hq w),
        show (1 / 2 + 1 / 2 + ((k : ℝ) / 2 - 1 + (k / 2 - 1))) = ((k - 1 : ℕ) : ℝ) by
          rw [Nat.cast_sub (by omega)]; push_cast; ring, Real.rpow_natCast]
      simp
    have h9 : algSat 2 (normV w) {α, β} = {r * α, r * β} := by
      simp only [algSat, hr, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
      norm_num
    rw [h9, h6, ← h8, show (ω.val w : ℂˣ) * (r * r * (((ν.val w : ℂˣ) : ℂ) * (ν.val w : ℂˣ))) = r * α * (r * β) by
      linear_combination (-(r * r)) * h7]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
      Multiset.prod_singleton, map_mul, map_add]
    ring
end
end

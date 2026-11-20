import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCO
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj.ProdOpen

open Filter Topology

variable {D : D7}

/- English proof (translation)
Establish `hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype` using `Matrix.map_injective Subtype.val_injective`. Use `⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩` and prove the remaining obligations. Simplify using `only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `g.mul_inv`. Simplify using `only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]`.

Conclude with `g.inv_mul`.
-/
theorem mem_GLint_of_entries {L : Type} [Field L] {n : ℕ} (O : Subring L) (g : GL (Fin n) L)
    (h1 : ∀ i j, g.1 i j ∈ O) (h2 : ∀ i j, g⁻¹.1 i j ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem inBasis_apply {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) (i j : Fin n') :
    (inBasis h β w x).1 i j = cpt w ((β⁻¹ * x * β).1 (finCongr h i) (finCongr h j)) := rfl

/- English proof (translation)
Take `⟨y, rfl⟩` from `hx`. Rewrite using `[GlobalTheory.SmGL.SphCompletion.KO_completion w n]`. Establish `hm : ∀ z : GL (Fin n) (Lev.EAf D), z ∈ ({Formalism.L2.DIV.intGL _ _ n y, (Formalism.L2.DIV.intGL _ _ n y)⁻¹} : Set _) → ∀ a b, cpt w (z.1 a b) ∈ Formalism.UG.Ov D.host.E w`. Introduce `z hz a b`. Use `(mem_OA_iff _).1 ?_ w` and prove the remaining obligations.

Break down `hz with rfl | rfl` into its components or cases. Conclude with `(y.1 a b).2`. Rewrite using `[← map_inv]`. Conclude with `((y⁻¹).1 a b).2`. Establish `e1 : β⁻¹ * Formalism.L2.DIV.frGL β y * β = Formalism.L2.DIV.intGL _ _ n y`.

Simplify using `only [Formalism.L2.DIV.frGL, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply]`. Use `group`. Establish `e2 : β⁻¹ * (Formalism.L2.DIV.frGL β y)⁻¹ * β = (Formalism.L2.DIV.intGL _ _ n y)⁻¹`. Rewrite using `[← e1]`. Use `group`.

Use `mem_GLint_of_entries _ _ (fun i j => ?_) (fun i j => ?_)` and prove the remaining obligations. Rewrite using `[inBasis_apply, e1]`. Conclude with `hm _ (Or.inl rfl) _ _`. Rewrite using `[← map_inv, inBasis_apply, e2]`. Conclude with `hm _ (Or.inr rfl) _ _`.
-/
theorem inBasis_mem_KO {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)) (hx : x ∈ St β) (w : Pl D.host.E) :
    inBasis rfl β w x ∈ KO (Kw w) (Fin n) := by
  obtain ⟨y, rfl⟩ := hx
  rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
  have hm : ∀ z : GL (Fin n) (Lev.EAf D), z ∈ ({Formalism.L2.DIV.intGL _ _ n y, (Formalism.L2.DIV.intGL _ _ n y)⁻¹} : Set _) →
      ∀ a b, cpt w (z.1 a b) ∈ Formalism.UG.Ov D.host.E w := by
    intro z hz a b
    refine (mem_OA_iff _).1 ?_ w
    rcases hz with rfl | rfl
    · exact (y.1 a b).2
    · rw [← map_inv]; exact ((y⁻¹).1 a b).2
  have e1 : β⁻¹ * Formalism.L2.DIV.frGL β y * β = Formalism.L2.DIV.intGL _ _ n y := by
    simp only [Formalism.L2.DIV.frGL, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply]
    group
  have e2 : β⁻¹ * (Formalism.L2.DIV.frGL β y)⁻¹ * β = (Formalism.L2.DIV.intGL _ _ n y)⁻¹ := by
    rw [← e1]; group
  refine mem_GLint_of_entries _ _ (fun i j => ?_) (fun i j => ?_)
  · rw [inBasis_apply, e1]; exact hm _ (Or.inl rfl) _ _
  · rw [← map_inv, inBasis_apply, e2]; exact hm _ (Or.inr rfl) _ _

/- English proof (translation)
Take `⟨π, hπ, -⟩` from `GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram`. Establish `hf : Continuous (finHom V)` using `(continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ`. Use `tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => Metric.tendsto_nhds.2 fun ε hε => ?_` and prove the remaining obligations. Take `⟨k, hk⟩` from `exists_pow_lt_of_lt_one hε (GlobalTheory.LocalData.norm_resChar_lt_one w)`. Establish `hN : Formalism.MainNotions.S.Loc.resChar w ^ k ≠ 0` using `pow_ne_zero _ (GlobalTheory.LocalData.resChar_prime w).ne_zero`.

Use `filter_upwards [eventually_cong_mat β hN hf (map_one _)] with κ ⟨z, hz, e⟩`. Express the relevant statement in the definitionally equal form `(β⁻¹ * Lev.finE V κ * β).1 - 1 = _ at e`. Establish `e2` using `congr_fun (congr_fun e (finCongr h i)) (finCongr h j)`. Rewrite `e2` using `[Matrix.sub_apply, Matrix.smul_apply, sub_eq_iff_eq_add]`. Establish `e3 : cpt w ((1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) (finCongr h i) (finCongr h j)) = (1 : Matrix (Fin n') (Fin n') (Kw w)) i j`.

Simplify using `only [Matrix.one_apply, (finCongr h).injective.eq_iff]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hz1 : ‖cpt w (z (finCongr h i) (finCongr h j))‖ ≤ 1` using `Valued.toNormedField.norm_le_one_iff.2 ((mem_OA_iff _).1 (hz _ _) w)`. Rewrite using `[dist_eq_norm, inBasis_apply, e2, map_add, e3, add_sub_cancel_right, map_nsmul, nsmul_eq_mul, norm_mul, Nat.cast_pow, norm_pow]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tendsto_inBasis_val (V : HSp D) {n' : ℕ} (h : n' = V.rank) (β : GL (Fin V.rank) (Lev.EAf D)) (w : Pl D.host.E) :
    Tendsto (fun κ : GA D V => ((inBasis h β w (Lev.finE V κ)).1 : Matrix (Fin n') (Fin n') (Kw w))) (𝓝 1) (𝓝 1) := by
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  have hf : Continuous (finHom V) := (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (GlobalTheory.LocalData.norm_resChar_lt_one w)
  have hN : Formalism.MainNotions.S.Loc.resChar w ^ k ≠ 0 := pow_ne_zero _ (GlobalTheory.LocalData.resChar_prime w).ne_zero
  filter_upwards [eventually_cong_mat β hN hf (map_one _)] with κ ⟨z, hz, e⟩
  change (β⁻¹ * Lev.finE V κ * β).1 - 1 = _ at e
  have e2 := congr_fun (congr_fun e (finCongr h i)) (finCongr h j)
  rw [Matrix.sub_apply, Matrix.smul_apply, sub_eq_iff_eq_add] at e2
  have e3 : cpt w ((1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) (finCongr h i) (finCongr h j)) =
      (1 : Matrix (Fin n') (Fin n') (Kw w)) i j := by
    simp only [Matrix.one_apply, (finCongr h).injective.eq_iff]
    split_ifs <;> simp
  have hz1 : ‖cpt w (z (finCongr h i) (finCongr h j))‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.2 ((mem_OA_iff _).1 (hz _ _) w)
  rw [dist_eq_norm, inBasis_apply, e2, map_add, e3, add_sub_cancel_right, map_nsmul, nsmul_eq_mul, norm_mul,
    Nat.cast_pow, norm_pow]
  calc ‖((Formalism.MainNotions.S.Loc.resChar w : ℕ) : Kw w)‖ ^ k * ‖cpt w (z (finCongr h i) (finCongr h j))‖
      ≤ ‖((Formalism.MainNotions.S.Loc.resChar w : ℕ) : Kw w)‖ ^ k * 1 := by gcongr
    _ < ε := by rwa [mul_one]

/- English proof (translation)
Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram` as an intermediate fact. Rewrite using `[Units.isInducing_embedProduct.tendsto_nhds_iff]`. Establish `hinv : Tendsto (fun κ : GA D V => κ⁻¹) (𝓝 1) (𝓝 1)`. Simplify using `using (continuous_inv.tendsto (1 : GA D V))`. Establish `h2 : Tendsto (fun κ : GA D V => ((inBasis h β w (Lev.finE V κ))⁻¹).1) (𝓝 1) (𝓝 1)`.

Use `(tendsto_inBasis_val V h β w).comp hinv` as an intermediate fact. Use `this.congr fun κ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, map_inv]`. Establish `h3` using `(tendsto_inBasis_val V h β w).prodMk_nhds (MulOpposite.continuous_op.tendsto _ |>.comp h2)`. Use `h3 using 2` and compare the differences between its conclusion and the goal.

Apply the tactic sequence `ext <;> simp [Units.embedProduct]`. Rewrite using `[map_one]`. Both sides reduce to the same expression.
-/
theorem tendsto_inBasis (V : HSp D) {n' : ℕ} (h : n' = V.rank) (β : GL (Fin V.rank) (Lev.EAf D)) (w : Pl D.host.E) :
    Tendsto (fun κ : GA D V => inBasis h β w (Lev.finE V κ)) (𝓝 1) (𝓝 1) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
  have hinv : Tendsto (fun κ : GA D V => κ⁻¹) (𝓝 1) (𝓝 1) := by
    simpa using (continuous_inv.tendsto (1 : GA D V))
  have h2 : Tendsto (fun κ : GA D V => ((inBasis h β w (Lev.finE V κ))⁻¹).1) (𝓝 1) (𝓝 1) := by
    have := (tendsto_inBasis_val V h β w).comp hinv
    refine this.congr fun κ => ?_
    simp only [Function.comp_apply, map_inv]
  have h3 := (tendsto_inBasis_val V h β w).prodMk_nhds (MulOpposite.continuous_op.tendsto _ |>.comp h2)
  convert h3 using 2
  · ext <;> simp [Units.embedProduct]
  · rw [map_one]; rfl

/- English proof (translation)
Introduce `D V β P n' h K hK`. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram` as an intermediate fact. Use `Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_` and prove the remaining obligations. Establish `hP : ∀ w : P, ∀ᶠ κ in 𝓝 (1 : GA D V), inBasis (h w) β w (Lev.finE V κ) ∈ K w` using `fun w => tendsto_inBasis V (h w) β w.1 ((hK w).mem_nhds (one_mem _))`. Use `filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β ∅, Filter.eventually_all.2 hP] with κ hh h3`.

Conclude with `Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 h3, Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun _ => inBasis_mem_KO β _ hh.2.1 w'⟩`.
-/
theorem isOpen_comap_prodLev : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E)) {n' : P → ℕ}
    (h : ∀ w, n' w = V.rank) (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))),
    (∀ w, IsOpen (K w : Set (GL (Fin (n' w)) (Kw w.1)))) →
      IsOpen (((prodLev β P h K).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
  intro D V β P n' h K hK
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have hP : ∀ w : P, ∀ᶠ κ in 𝓝 (1 : GA D V), inBasis (h w) β w (Lev.finE V κ) ∈ K w := fun w =>
    tendsto_inBasis V (h w) β w.1 ((hK w).mem_nhds (one_mem _))
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β ∅, Filter.eventually_all.2 hP] with κ hh h3
  exact Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 h3,
    Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun _ => inBasis_mem_KO β _ hh.2.1 w'⟩

end GlobalTheory.FunObj.ProdOpen

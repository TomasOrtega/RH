import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactor
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensOp
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.EigAdm
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped ComplexConjugate Classical

namespace UpperTheory.ConvolutionTheory.L1

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simp`. Consider the case `cons A L ih`. Establish `h1` using `ih fun B hB => h B (List.mem_cons_of_mem _ hB)`. Rewrite using `[List.prod_cons, ContinuousLinearMap.mul_apply, h1, map_smul, h A List.mem_cons_self, smul_smul, List.length_cons, pow_succ]`.
-/
private theorem list_prod_apply {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (L : List (H →L[ℂ] H)) (v : H) (c : ℂ)
    (h : ∀ A ∈ L, A v = c • v) : L.prod v = c ^ L.length • v := by
  induction L with
  | nil => simp
  | cons A L ih =>
    have h1 := ih fun B hB => h B (List.mem_cons_of_mem _ hB)
    rw [List.prod_cons, ContinuousLinearMap.mul_apply, h1, map_smul, h A List.mem_cons_self, smul_smul, List.length_cons,
      pow_succ]

section One
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

/- English proof (translation)
Simplify using `only [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.smul_apply, LinearMap.id_apply]`.
-/
private theorem mem_eigL' (w : Pl K) (J : Subgroup (Gw n w)) (χ : Gw n w → ℂ) (v : LL μ) :
    v ∈ eigL μ w J χ ↔ ∀ x ∈ J, rhoL μ w x v = χ x • v := by
  simp only [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.smul_apply,
    LinearMap.id_apply]

/- English proof (translation)
Simplify using `only [fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.id_apply, Subgroup.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, rhoL]`.
-/
private theorem mem_fixL' (w : Pl K) (J : Subgroup (Gw n w)) (v : LL μ) :
    v ∈ fixL μ w J ↔ ∀ x ∈ J, rhoL μ w x v = v := by
  simp only [fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.id_apply,
    Subgroup.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, rhoL]

/- English proof (translation)
Establish `h` using `(UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.2.1 w' hne g x`. Simplify using `only [rhoL, rhoF]`. Rewrite using `[← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, ← map_mul, ← map_mul, h]`.
-/
private theorem rhoL_comm {w w' : Pl K} (hne : w' ≠ w) (g : Gw n w) (x : Gw n w') (v : LL μ) :
    rhoL μ w' x (rhoL μ w g v) = rhoL μ w g (rhoL μ w' x v) := by
  have h := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.2.1 w' hne g x
  simp only [rhoL, rhoF]
  rw [← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, ← map_mul, ← map_mul, h]

/- English proof (translation)
The claim follows from `(MultiplicityOne.finProj_mul_archProj_comm h a).symm`.
-/
private theorem archP_finProj_comm (a : archGroup K n) (h : AdelicGLn.FiniteAdelicGL K n) :
    archP K n a * MultiplicityOne.finProj K n h = MultiplicityOne.finProj K n h * archP K n a :=
  (MultiplicityOne.finProj_mul_archProj_comm h a).symm

end One

section Grp
variable {G : Type} [Group G] [TopologicalSpace G]

/- English proof (translation)
Establish `h1` using `h.2.2 1 J.one_mem 1 J.one_mem`. Establish `h2 : χ 1 ≠ 0` using `fun h0 => by`. Use `h.2.1 1 J.one_mem` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`. Conclude with `zero_ne_one this`.

Rewrite `h1` using `[mul_one]`. Conclude with `mul_left_cancel₀ h2 (by rw [← h1, mul_one])`.
-/
private theorem chr_one {J : Subgroup G} {χ : G → ℂ} (h : IsChr J χ) : χ 1 = 1 := by
  have h1 := h.2.2 1 J.one_mem 1 J.one_mem
  have h2 : χ 1 ≠ 0 := fun h0 => by
    have := h.2.1 1 J.one_mem
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  rw [mul_one] at h1
  exact mul_left_cancel₀ h2 (by rw [← h1, mul_one])

private def kerS (J : Subgroup G) (χ : G → ℂ) (h : IsChr J χ) : Subgroup G where
  carrier := {x | x ∈ J ∧ χ x = 1}
  one_mem' := ⟨J.one_mem, chr_one h⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨J.mul_mem ha hb, by rw [h.2.2 a ha b hb, ha', hb', one_mul]⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨J.inv_mem ha, ?_⟩
    have h1 := h.2.2 a ha a⁻¹ (J.inv_mem ha)
    rwa [mul_inv_cancel, chr_one h, ha', one_mul, eq_comm] at h1

/- English proof (translation)
Establish `e : (kerS J χ h : Set G) = (J : Set G) ∩ χ ⁻¹' {1}` using `rfl`. Establish `ho : IsOpen (χ ⁻¹' {(1 : ℂ)})` using `h.1.isOpen_fiber 1`. Establish `hc : IsClosed (χ ⁻¹' {(1 : ℂ)})` using `isClosed_singleton.preimage h.1.continuous`. Rewrite using `[CO, e]`. Conclude with `⟨hJ.1.inter_right hc, hJ.2.inter ho⟩`.
-/
private theorem kerS_co {J : Subgroup G} {χ : G → ℂ} (hJ : CO J) (h : IsChr J χ) : CO (kerS J χ h) := by
  have e : (kerS J χ h : Set G) = (J : Set G) ∩ χ ⁻¹' {1} := rfl
  have ho : IsOpen (χ ⁻¹' {(1 : ℂ)}) := h.1.isOpen_fiber 1
  have hc : IsClosed (χ ⁻¹' {(1 : ℂ)}) := isClosed_singleton.preimage h.1.continuous
  rw [CO, e]
  exact ⟨hJ.1.inter_right hc, hJ.2.inter ho⟩

end Grp

section Two
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E ≃ₐ[F] E} {n m : ℕ} {q : Pl F} {w₀ : PlacesOver E q}
variable (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]

/- English proof (translation)
Use `ext1`. Conclude with `(Ideal.over_def u.1.asIdeal v.asIdeal).symm`.
-/
private theorem under_of_over {v : Pl F} (u : PlacesOver E v) : u.1.under (𝓞 F) = v := by
  ext1
  exact (Ideal.over_def u.1.asIdeal v.asIdeal).symm

/- English proof (translation)
Use `(Set.finite_range fun u : PlacesOver E v => u.1).subset fun w hw => ?_` and prove the remaining obligations. Substitute `hw` using the available equality. Conclude with `⟨⟨w, ⟨rfl⟩⟩, rfl⟩`.
-/
private theorem finite_over (v : Pl F) : {w : Pl E | w.under (𝓞 F) = v}.Finite := by
  refine (Set.finite_range fun u : PlacesOver E v => u.1).subset fun w hw => ?_
  subst hw
  exact ⟨⟨w, ⟨rfl⟩⟩, rfl⟩

/- English proof (translation)
Simplify using `only [Ty.Z, archEig, eigIn, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_top, true_and, Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe, and_assoc]`.
-/
private theorem mem_Z (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)) (O : Fin (m + 1) → LL μ →L[ℂ] LL μ) (y : ℝ) (v : LL μ) :
    v ∈ T.Z μ V O y ↔ v ∈ V ∧ (∀ i, O i v = (y : ℂ) • v) ∧ ∀ w ∉ T.marked, v ∈ eigL μ w (T.J w) (T.χ w) := by
  simp only [Ty.Z, archEig, eigIn, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_top, true_and,
    Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe, and_assoc]

/- English proof (translation)
Simplify using `only [Ty.Y, Ty.typed, archEig, eigIn, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_top, true_and, Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe, and_assoc]`.
-/
private theorem mem_Y (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)) (O : Fin (m + 1) → LL μ →L[ℂ] LL μ) (y : ℝ) (v : LL μ) :
    v ∈ T.Y μ V O y ↔ v ∈ V ∧ (∀ i, O i v = (y : ℂ) • v) ∧ ∀ w, v ∈ eigL μ w (T.J w) (T.χ w) := by
  simp only [Ty.Y, Ty.typed, archEig, eigIn, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_top, true_and,
    Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe, and_assoc]

/- English proof (translation)
Break down `hw with rfl | ⟨v, hv, rfl⟩` into its components or cases. Conclude with `T.triv q hq w₀`. Conclude with `T.triv v (Finset.mem_filter.1 hv).2 (T.mk' v)`.
-/
private theorem marked_chi (hq : GM.Split E q) (T : Ty σ n q w₀) {w : Pl E} (hw : w ∈ T.marked) : T.χ w = 1 := by
  rcases hw with rfl | ⟨v, hv, rfl⟩
  · exact T.triv q hq w₀
  · exact T.triv v (Finset.mem_filter.1 hv).2 (T.mk' v)

/- English proof (translation)
Break down `hw with rfl | ⟨v, hv, rfl⟩` into its components or cases. Rewrite using `[under_of_over]`. Conclude with `Finset.mem_insert_self _ _`. Rewrite using `[under_of_over]`. Conclude with `Finset.mem_insert_of_mem (Finset.mem_filter.1 hv).1`.
-/
private theorem marked_under (T : Ty σ n q w₀) {w : Pl E} (hw : w ∈ T.marked) : w.under (𝓞 F) ∈ insert q T.S := by
  rcases hw with rfl | ⟨v, hv, rfl⟩
  · rw [under_of_over]
    exact Finset.mem_insert_self _ _
  · rw [under_of_over]
    exact Finset.mem_insert_of_mem (Finset.mem_filter.1 hv).1

/- English proof (translation)
Establish `key : (rhoF μ h) ∘L OComponent μ s hs ν a = OComponent μ s hs ν a ∘L (rhoF μ h)`. Use `UnitaryRep.comp_integrated_of_mem_intertwiners _ _ ?_ _` and prove the remaining obligations. Introduce `x u`. Simplify using `only [UnitaryRep.compHom_apply, rhoF]`. Rewrite using `[← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, archP_finProj_comm]`.

Conclude with `(DFunLike.congr_fun key v).symm`.
-/
private theorem operatorAt_comm (s : archGroup F n →* archGroup E n) (hs : Continuous s) (ν : Measure (archGroup F n)) [ν.IsHaarMeasure]
    (a : TI F n) (h : AdelicGLn.FiniteAdelicGL E n) (v : LL μ) :
    OComponent μ s hs ν a (rhoF μ h v) = rhoF μ h (OComponent μ s hs ν a v) := by
  have key : (rhoF μ h) ∘L OComponent μ s hs ν a = OComponent μ s hs ν a ∘L (rhoF μ h) := by
    refine UnitaryRep.comp_integrated_of_mem_intertwiners _ _ ?_ _
    intro x u
    simp only [UnitaryRep.compHom_apply, rhoF]
    rw [← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, archP_finProj_comm]
  exact (DFunLike.congr_fun key v).symm

/- English proof (translation)
Establish `e : (T.Z μ V O y : Set (LL μ)) = (V : Set (LL μ)) ∩ ((⋂ i, {v | O i v = (y : ℂ) • v}) ∩ ⋂ w, ⋂ (_ : w ∉ T.marked), (eigL μ w (T.J w) (T.χ w) : Set (LL μ)))`. Use extensionality with `v`. Simplify using `only [SetLike.mem_coe, mem_Z, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]`. Rewrite using `[e]`. Use `hV.inter (IsClosed.inter (isClosed_iInter fun i => isClosed_eq (O i).continuous (continuous_const_smul _)) ?_)` and prove the remaining obligations.

Conclude with `isClosed_iInter fun w => isClosed_iInter fun _ => (UpperTheory.ConvolutionTheory.L1.eigBasic E n μ w (T.J w) (T.χ w) (T.co w) (T.chr w)).1`.
-/
private theorem Z_closed (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)) (hV : IsClosed (V : Set (LL μ)))
    (O : Fin (m + 1) → LL μ →L[ℂ] LL μ) (y : ℝ) : IsClosed (T.Z μ V O y : Set (LL μ)) := by
  have e : (T.Z μ V O y : Set (LL μ)) = (V : Set (LL μ)) ∩ ((⋂ i, {v | O i v = (y : ℂ) • v}) ∩
      ⋂ w, ⋂ (_ : w ∉ T.marked), (eigL μ w (T.J w) (T.χ w) : Set (LL μ))) := by
    ext v
    simp only [SetLike.mem_coe, mem_Z, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [e]
  refine hV.inter (IsClosed.inter (isClosed_iInter fun i => isClosed_eq (O i).continuous (continuous_const_smul _)) ?_)
  exact isClosed_iInter fun w => isClosed_iInter fun _ =>
    (UpperTheory.ConvolutionTheory.L1.eigBasic E n μ w (T.J w) (T.χ w) (T.co w) (T.chr w)).1

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `(mem_Z μ T V _ y v).1 hv`. Use `(mem_Z μ T V _ y _).2 ⟨hV.inv _ _ h1, fun i => ?_, fun w' hw' => ?_⟩` and prove the remaining obligations. Use `operatorAt_comm μ (s i) (hs i) νF a (AdelicGLn.localEmbedding w g) v` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Rewrite using `[h2 i, map_smul]`.

Both sides reduce to the same expression. Use `(mem_eigL' μ _ _ _ _).2 fun x hx => ?_` and prove the remaining obligations. Establish `hne : w' ≠ w` using `fun h => hw' (h ▸ hw)`. Rewrite using `[rhoL_comm μ hne, (mem_eigL' μ _ _ _ _).1 (h3 w' hw') x hx, map_smul]`.
-/
private theorem Z_stable (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)) (hV : IsSummand μ V)
    (s : Fin (m + 1) → archGroup F n →* archGroup E n) (hs : ∀ i, Continuous (s i)) (νF : Measure (archGroup F n)) [νF.IsHaarMeasure]
    (a : TI F n) (y : ℝ) (w : Pl E) (hw : w ∈ T.marked) (g : Gw n w) (v : LL μ)
    (hv : v ∈ T.Z μ V (fun i => OComponent μ (s i) (hs i) νF a) y) :
    rhoL μ w g v ∈ T.Z μ V (fun i => OComponent μ (s i) (hs i) νF a) y := by
  obtain ⟨h1, h2, h3⟩ := (mem_Z μ T V _ y v).1 hv
  refine (mem_Z μ T V _ y _).2 ⟨hV.inv _ _ h1, fun i => ?_, fun w' hw' => ?_⟩
  · have := operatorAt_comm μ (s i) (hs i) νF a (AdelicGLn.localEmbedding w g) v
    refine this.trans ?_
    rw [h2 i, map_smul]
    rfl
  · refine (mem_eigL' μ _ _ _ _).2 fun x hx => ?_
    have hne : w' ≠ w := fun h => hw' (h ▸ hw)
    rw [rhoL_comm μ hne, (mem_eigL' μ _ _ _ _).1 (h3 w' hw') x hx, map_smul]

/- English proof (translation)
Establish `hfix : ∀ w ∈ T.marked, eigL μ w (T.J w) (T.χ w) = fixL μ w (T.J w)` using `fun w hw => by`. Rewrite using `[marked_chi hq T hw]`. Conclude with `(UpperTheory.ConvolutionTheory.L1.eigBasic E n μ w (T.J w) 1 (T.co w) (marked_chi hq T hw ▸ T.chr w)).2.1`. Use extensionality with `v`. Simplify using `only [Submodule.mem_inf, Submodule.mem_iInf, mem_Y, mem_Z]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, h3⟩`. Conclude with `⟨⟨h1, h2, fun w _ => h3 w⟩, fun w hw => hfix w hw ▸ h3 w⟩`. Introduce and unpack `⟨⟨h1, h2, h3⟩, h4⟩`. Use `⟨h1, h2, fun w => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hw : w ∈ T.marked`. Conclude with `(hfix w hw).symm ▸ h4 w hw`. Conclude with `h3 w hw`.
-/
private theorem Y_eq (hq : GM.Split E q) (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)) (O : Fin (m + 1) → LL μ →L[ℂ] LL μ) (y : ℝ) :
    T.Y μ V O y = T.Z μ V O y ⊓ ⨅ w ∈ T.marked, fixL μ w (T.J w) := by
  have hfix : ∀ w ∈ T.marked, eigL μ w (T.J w) (T.χ w) = fixL μ w (T.J w) := fun w hw => by
    rw [marked_chi hq T hw]
    exact (UpperTheory.ConvolutionTheory.L1.eigBasic E n μ w (T.J w) 1 (T.co w) (marked_chi hq T hw ▸ T.chr w)).2.1
  ext v
  simp only [Submodule.mem_inf, Submodule.mem_iInf, mem_Y, mem_Z]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2, fun w _ => h3 w⟩, fun w hw => hfix w hw ▸ h3 w⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    refine ⟨h1, h2, fun w => ?_⟩
    by_cases hw : w ∈ T.marked
    · exact (hfix w hw).symm ▸ h4 w hw
    · exact h3 w hw

end Two

section Three
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E ≃ₐ[F] E} {n m : ℕ} {q : Pl F} {w₀ : PlacesOver E q}

/- English proof (translation)
Take `⟨-, -, -, -, -, -, hH, hβ⟩` from `UpperTheory.ConvolutionTheory.L1.archBasic F E σ m D n`. Use `haveI := hH νF`. Take `⟨β, hβ⟩` from `hβ fun _ => a`. Establish `hop : Oinf μ (Measure.map (glueA D n) (Measure.pi fun _ => νF)) β = (List.ofFn fun i => OComponent μ (s i) (hs i) νF a).prod` using `UpperTheory.ConvolutionTheory.L1.tensOp F E σ m D n (Measure.map (glueA D n) (Measure.pi fun _ => νF)) νF rfl s hs hposition (LL μ) _ (fun _ => a) β hβ`. Establish `hfin : {w : Pl E | w.under (𝓞 F) ∈ insert q T.S}.Finite`.

Establish `: {w : Pl E | w.under (𝓞 F) ∈ insert q T.S} = ⋃ v ∈ insert q T.S, {w : Pl E | w.under (𝓞 F) = v}`. Use extensionality with `w`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `(Finset.finite_toSet _).biUnion fun v _ => finite_over v`.

Use `set P : Finset (Pl E) := hfin.toFinset with hP`. Establish `hPm : ∀ w, w ∈ P ↔ w.under (𝓞 F) ∈ insert q T.S` using `fun w => by simp [hP]`. Set `U' : ∀ w : Pl E, Subgroup (Gw n w)` to `fun w => if w ∈ T.marked then U w else kerS (T.J w) (T.χ w) (T.chr w)`. Establish `hU' : ∀ w ∈ P, CO (U' w)` using `fun w _ => by`. Distinguish the cases in `hw : w ∈ T.marked`.

Simplify `hU w hw` using `only [U', if_pos hw]`. Simplify `kerS_co (T.co w) (T.chr w)` using `only [U', if_neg hw]`. Use `haveI := UpperTheory.ConvolutionTheory.C.eigAdm E n hn μ (Measure.map (glueA D n) (Measure.pi fun _ => νF)) β (y ^ (m + 1)) (pow_ne_zero _ hy.ne') P U' hU'`. Use `Submodule.finiteDimensional_of_le (fun v hv => ?_) (S₂ := eigIn (cuspidalL2 μ) (Oinf μ (Measure.map (glueA D n) (Measure.pi fun _ => νF)) β) (y ^ (m + 1)) ⊓ sphOff μ P ⊓ ⨅ w ∈ P, fixL μ w (U' w))` and prove the remaining obligations. Take `⟨hZ, hf⟩` from `Submodule.mem_inf.1 hv`.

Take `⟨h1, h2, h3⟩` from `(mem_Z μ T V _ y v).1 hZ`. Establish `hf' : ∀ w ∈ T.marked, v ∈ fixL μ w (U w)` using `fun w hw => by`. Simplify `(Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hf w) hw` using `only [Submodule.mem_iInf]`. Use `Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hV.le h1, ?_⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe, hop, list_prod_apply _ v (y : ℂ)]`.

Simplify using the standard rewrite rules. Introduce `A hA`. Take `⟨i, rfl⟩` from `List.mem_ofFn.1 hA`. Conclude with `h2 i`. Use `(Submodule.mem_iInf _).2 fun w => (Submodule.mem_iInf _).2 fun hw => ?_` and prove the remaining obligations.

Establish `hmk : w ∉ T.marked` using `fun h => hw ((hPm w).2 (marked_under T h))`. Establish `hu : w.under (𝓞 F) ∉ insert q T.S` using `fun h => hw ((hPm w).2 h)`. Take `⟨e1, e2⟩` from `T.off w (fun h => hu (Finset.mem_insert_of_mem h)) (fun h => hu (by rw [h]; exact Finset.mem_insert_self _ _))`. Use `(mem_fixL' μ _ _ _).2 fun x hx => ?_` and prove the remaining obligations. Rewrite using `[(mem_eigL' μ _ _ _ _).1 (h3 w hmk) x (e1 ▸ hx), e2]`.

Simplify using the standard rewrite rules. Use `(Submodule.mem_iInf _).2 fun w => (Submodule.mem_iInf _).2 fun _ => ?_` and prove the remaining obligations. Distinguish the cases in `hw : w ∈ T.marked`. Simplify `hf' w hw` using `only [U', if_pos hw]`. Simplify using `only [U', if_neg hw]`.

Use `(mem_fixL' μ _ _ _).2 fun x hx => ?_` and prove the remaining obligations. Rewrite using `[(mem_eigL' μ _ _ _ _).1 (h3 w hw) x hx.1, hx.2, one_smul]`.
-/
private theorem Z_fin (hn : 0 < n) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (D : InfD σ m)
    (s : Fin (m + 1) → archGroup F n →* archGroup E n) (hs : ∀ i, Continuous (s i)) (hposition : IsBlockElement D n s)
    (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (a : TI F n) (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)) (hV : IsSummand μ V)
    (y : ℝ) (hy : 0 < y) (U : ∀ w : Pl E, Subgroup (Gw n w)) (hU : ∀ w ∈ T.marked, CO (U w)) :
    FiniteDimensional ℂ ↥(T.Z μ V (fun i => OComponent μ (s i) (hs i) νF a) y ⊓ ⨅ w ∈ T.marked, fixL μ w (U w)) := by
  obtain ⟨-, -, -, -, -, -, hH, hβ⟩ := UpperTheory.ConvolutionTheory.L1.archBasic F E σ m D n
  haveI := hH νF
  obtain ⟨β, hβ⟩ := hβ fun _ => a
  have hop : Oinf μ (Measure.map (glueA D n) (Measure.pi fun _ => νF)) β =
      (List.ofFn fun i => OComponent μ (s i) (hs i) νF a).prod :=
    UpperTheory.ConvolutionTheory.L1.tensOp F E σ m D n (Measure.map (glueA D n) (Measure.pi fun _ => νF)) νF rfl s hs hposition (LL μ) _ (fun _ => a) β hβ
  have hfin : {w : Pl E | w.under (𝓞 F) ∈ insert q T.S}.Finite := by
    have : {w : Pl E | w.under (𝓞 F) ∈ insert q T.S} = ⋃ v ∈ insert q T.S, {w : Pl E | w.under (𝓞 F) = v} := by
      ext w
      simp
    rw [this]
    exact (Finset.finite_toSet _).biUnion fun v _ => finite_over v
  set P : Finset (Pl E) := hfin.toFinset with hP
  have hPm : ∀ w, w ∈ P ↔ w.under (𝓞 F) ∈ insert q T.S := fun w => by simp [hP]
  let U' : ∀ w : Pl E, Subgroup (Gw n w) := fun w =>
    if w ∈ T.marked then U w else kerS (T.J w) (T.χ w) (T.chr w)
  have hU' : ∀ w ∈ P, CO (U' w) := fun w _ => by
    by_cases hw : w ∈ T.marked
    · simpa only [U', if_pos hw] using hU w hw
    · simpa only [U', if_neg hw] using kerS_co (T.co w) (T.chr w)
  haveI := UpperTheory.ConvolutionTheory.C.eigAdm E n hn μ (Measure.map (glueA D n) (Measure.pi fun _ => νF)) β (y ^ (m + 1)) (pow_ne_zero _ hy.ne') P U' hU'
  refine Submodule.finiteDimensional_of_le (fun v hv => ?_)
    (S₂ := eigIn (cuspidalL2 μ) (Oinf μ (Measure.map (glueA D n) (Measure.pi fun _ => νF)) β) (y ^ (m + 1)) ⊓ sphOff μ P ⊓
      ⨅ w ∈ P, fixL μ w (U' w))
  obtain ⟨hZ, hf⟩ := Submodule.mem_inf.1 hv
  obtain ⟨h1, h2, h3⟩ := (mem_Z μ T V _ y v).1 hZ
  have hf' : ∀ w ∈ T.marked, v ∈ fixL μ w (U w) := fun w hw => by
    simpa only [Submodule.mem_iInf] using (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hf w) hw
  refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hV.le h1, ?_⟩, ?_⟩, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe, hop, list_prod_apply _ v (y : ℂ)]
    · simp
    · intro A hA
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hA
      exact h2 i
  · refine (Submodule.mem_iInf _).2 fun w => (Submodule.mem_iInf _).2 fun hw => ?_
    have hmk : w ∉ T.marked := fun h => hw ((hPm w).2 (marked_under T h))
    have hu : w.under (𝓞 F) ∉ insert q T.S := fun h => hw ((hPm w).2 h)
    obtain ⟨e1, e2⟩ := T.off w (fun h => hu (Finset.mem_insert_of_mem h)) (fun h => hu (by rw [h]; exact Finset.mem_insert_self _ _))
    refine (mem_fixL' μ _ _ _).2 fun x hx => ?_
    rw [(mem_eigL' μ _ _ _ _).1 (h3 w hmk) x (e1 ▸ hx), e2]
    simp
  · refine (Submodule.mem_iInf _).2 fun w => (Submodule.mem_iInf _).2 fun _ => ?_
    by_cases hw : w ∈ T.marked
    · simpa only [U', if_pos hw] using hf' w hw
    · simp only [U', if_neg hw]
      refine (mem_fixL' μ _ _ _).2 fun x hx => ?_
      rw [(mem_eigL' μ _ _ _ _).1 (h3 w hw) x hx.1, hx.2, one_smul]

end Three

end UpperTheory.ConvolutionTheory.L1

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ m n hn μ _ D s hs hposition νF _ a q w₀ hq T V hV y hy`. Conclude with `⟨UpperTheory.ConvolutionTheory.L1.Z_closed μ T V hV.closed _ y, fun w hw g v hv => UpperTheory.ConvolutionTheory.L1.Z_stable μ T V hV s hs νF a y w hw g v hv, fun U hU => UpperTheory.ConvolutionTheory.L1.Z_fin hn μ D s hs hposition νF a T V hV y hy U hU, UpperTheory.ConvolutionTh …`.
-/
theorem UpperTheory.ConvolutionTheory.L1.zBasic :
    UpperTheory.ConvolutionTheory.L1.ZBasic := by
  intro F E _ _ _ _ _ σ m n hn μ _ D s hs hposition νF _ a q w₀ hq T V hV y hy
  exact ⟨UpperTheory.ConvolutionTheory.L1.Z_closed μ T V hV.closed _ y, fun w hw g v hv => UpperTheory.ConvolutionTheory.L1.Z_stable μ T V hV s hs νF a y w hw g v hv,
    fun U hU => UpperTheory.ConvolutionTheory.L1.Z_fin hn μ D s hs hposition νF a T V hV y hy U hU, UpperTheory.ConvolutionTheory.L1.Y_eq μ hq T V _ y⟩

import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.L2DbarEstimates (V leviV)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.ChartGlue
open scoped ContDiff

namespace GlobalTheory.TrueGeo.OfLattice

section Rect

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {B : LB X} {α β : Type} [Fintype α] [Fintype β]

def combWeight (hB : B.IsLB) (s : α → B.Sec) {σ : k →+* ℂ} (A : Matrix α β ℂ)
    (h : Weight.NoCommonZero fun a => ∑ j, A j a • secVal p σ (s j)) : Weight p σ B :=
  Weight.fs hB _ (fun _ => Submodule.sum_mem _ fun _ _ => Submodule.smul_mem _ _ (secVal_mem _)) h

/- English proof (translation)
Simplify using `only [combWeight, Weight.fs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem combWeight_φ (hB : B.IsLB) (s : α → B.Sec) {σ : k →+* ℂ} (A : Matrix α β ℂ)
    (h : Weight.NoCommonZero fun a => ∑ j, A j a • secVal p σ (s j)) (i : B.ι) (y : CxPts p σ) :
    (combWeight hB s A h).φ i y = Real.log (∑ a, ‖∑ j, A j a * valR y.1 (B.U i) ((s j).f i)‖ ^ 2) := by
  simp only [combWeight, Weight.fs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

/- English proof (translation)
Introduce `i y hy` and use `by have hs : ContDiff ℝ ∞ fun v : α → ℂ => ∑ a, ‖∑ j, A j a * v j‖ ^ 2 := ContDiff.sum fun a _ => (ContDiff.sum fun j _ => contDiff_const.mul (contDiff_apply ℝ ℂ j)).norm_sq ℂ refine ⟨B.U i, α, inferInstance, fun j => (s j).f i, fun v => Real.log (∑ a, ‖∑ j, A j a * v j‖ ^ 2), {v …`.
-/
theorem isCInf_combWeight (hB : B.IsLB) (s : α → B.Sec) {σ : k →+* ℂ} (A : Matrix α β ℂ)
    (h : Weight.NoCommonZero fun a => ∑ j, A j a • secVal p σ (s j)) : (combWeight hB s A h).IsCInf := fun i y hy => by
  have hs : ContDiff ℝ ∞ fun v : α → ℂ => ∑ a, ‖∑ j, A j a * v j‖ ^ 2 :=
    ContDiff.sum fun a _ => (ContDiff.sum fun j _ =>
      contDiff_const.mul (contDiff_apply ℝ ℂ j)).norm_sq ℂ
  refine ⟨B.U i, α, inferInstance, fun j => (s j).f i,
    fun v => Real.log (∑ a, ‖∑ j, A j a * v j‖ ^ 2), {v | ∑ a, ‖∑ j, A j a * v j‖ ^ 2 ≠ 0}, hy,
    isOpen_ne_fun hs.continuous continuous_const, ?_, hs.contDiffOn.log fun _ h => h,
    .of_forall fun z => combWeight_φ hB s A h i z⟩
  have := (h.sum_pos hy).ne'
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  exact this

/- English proof (translation)
Introduce `i c y hy ξ` and use `by let G (a : β) (v : V D) : ℂ := ∑ j, A j a * ev p σ _ ((s j).f i) (c.e.symm v) have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i)) have hG (a) : ContDiffAt ℂ 2 (G a) (c.e y) := ContDiffAt.sum fun j _ => contDiffAt_const.mul (((ReciprocityTheory.L2DbarEstimates.c …`.
-/
theorem semiPosReg_combWeight (hB : B.IsLB) (s : α → B.Sec) {σ : k →+* ℂ} (A : Matrix α β ℂ)
    (h : Weight.NoCommonZero fun a => ∑ j, A j a • secVal p σ (s j)) (D : ℕ) :
    (combWeight hB s A h).SemiPosReg D := fun i c y hy ξ => by
  let G (a : β) (v : V D) : ℂ := ∑ j, A j a * ev p σ _ ((s j).f i) (c.e.symm v)
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i))
  have hG (a) : ContDiffAt ℂ 2 (G a) (c.e y) := ContDiffAt.sum fun j _ => contDiffAt_const.mul
    (((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ _ ho (c.holo _ ((s j).f i))).contDiffAt
      (ho.mem_nhds (mem_over c.e hy.1 hy.2))).of_le (by norm_cast))
  have e (v : V D) : ∑ a, Complex.normSq (G ((Fintype.equivFin β).symm a) v) = ∑ a, ‖G a v‖ ^ 2 :=
    (Equiv.sum_comp (Fintype.equivFin β).symm fun a => Complex.normSq (G a v)).trans
      (Finset.sum_congr rfl fun a _ => Complex.normSq_eq_norm_sq _)
  have h0 := h.sum_pos hy.2
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h0
  have := ReciprocityTheory.L2DbarEstimates.leviV_log_sum_nonneg
    (u := fun a v => Complex.normSq (G ((Fintype.equivFin β).symm a) v))
    (fun a => ReciprocityTheory.L2DbarEstimates.contDiffAt_normSq_comp (hG _))
    (fun a => ReciprocityTheory.L2DbarEstimates.logPshAt_normSq (hG _))
    (by rw [e]; simp only [G, c.e.left_inv hy.1]; exact h0) ξ
  simp only [e] at this
  simp only [combWeight_φ]
  exact this

variable [DecidableEq β]

/- English proof (translation)
Introduce `i y y' hy' hy` and use `by rw [combWeight_φ, combWeight_φ] congr 1 have hv (j : α) : valR y'.1 (B.U i) ((s j).f i) = starRingEnd ℂ (valR y.1 (B.U i) ((s j).f i)) := CxPts.ev_conj hy' hy _ have := sum_normSq_vecMul_unitary hU fun a => starRingEnd ℂ (∑ j, A j a * valR y.1 (B.U i) ((s j).f i)) simp only [R …`.
-/
theorem isConj_combWeight (hB : B.IsLB) (s : α → B.Sec) {σ σ' : k →+* ℂ} {A A' : Matrix α β ℂ}
    (h : Weight.NoCommonZero fun a => ∑ j, A j a • secVal p σ (s j))
    (h' : Weight.NoCommonZero fun a => ∑ j, A' j a • secVal p σ' (s j)) {U : Matrix β β ℂ}
    (hU : U ∈ Matrix.unitaryGroup β ℂ) (e : A' = A.map (starRingEnd ℂ) * U) :
    (combWeight hB s A h).IsConj (combWeight hB s A' h') := fun i y y' hy' hy => by
  rw [combWeight_φ, combWeight_φ]
  congr 1
  have hv (j : α) : valR y'.1 (B.U i) ((s j).f i) = starRingEnd ℂ (valR y.1 (B.U i) ((s j).f i)) :=
    CxPts.ev_conj hy' hy _
  have := sum_normSq_vecMul_unitary hU fun a =>
    starRingEnd ℂ (∑ j, A j a * valR y.1 (B.U i) ((s j).f i))
  simp only [RCLike.norm_conj] at this
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) this
  congr 2
  simp only [e, hv, Matrix.mul_apply, Matrix.map_apply, Matrix.vecMul, dotProduct, map_sum, map_mul,
    Finset.sum_mul]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

def combHerm (hB : B.IsLB) (s : α → B.Sec) (A : (k →+* ℂ) → Matrix α β ℂ)
    (h : ∀ σ, Weight.NoCommonZero fun a => ∑ j, A σ j a • secVal p σ (s j))
    (hc : ∀ σ, ∃ U ∈ Matrix.unitaryGroup β ℂ, A ((starRingEnd ℂ).comp σ) = (A σ).map (starRingEnd ℂ) * U) :
    HermLB p where
  B := B
  isLB := hB
  φ σ := combWeight hB s (A σ) (h σ)
  cInf σ := isCInf_combWeight hB s _ _
  conj σ σ' i y y' e hy := by
    obtain rfl := eq_conj_of_conj e
    obtain ⟨U, hU, e'⟩ := hc σ
    exact isConj_combWeight hB s (h σ) (h _) hU e' i y y' e hy

end Rect

/- English proof (translation)
Introduce `Z i _ _ κ _ _ _ hd`. Use `hX.finite` as an intermediate fact. Establish `: IsProper p` using `CommonModel.isProper_of_isProjOver hX.isProjOver`. Take `⟨H, hH⟩` from `exists_isAmpleLB_of_isProjOver hX.isProjOver`. Establish `hA` using `hH.pull_of_isClosedImmersion i`.

Establish `: IsFinite (spMap (Int.castRingHom k))`. Rewrite using `[spMap, IsFinite.SpecMap_iff]`. Conclude with `(RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance`. Establish `e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k)` using `specZIsTerminal.hom_ext _ _`. Establish `: IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ))` using `by rw [e]; infer_instance`.

Establish `: IsProper (strHom κ Z)` using `IsProper.of_comp _ (spMap (Int.castRingHom κ))`. Establish `h` using `(isNef_iff_isClosedImmersion.1 ((hL.pull i).isNef (k := κ) hA)).2 Z (𝟙 Z) inferInstance inferInstance hd (by rw [Category.id_comp]; infer_instance)`. Rewrite `h` using `[interNumOn_id]`. Use `h.trans_eq (congrArg _ (funext fun j => ?_))` and prove the remaining obligations. Use `fin_cases j`.

Both sides reduce to the same expression.
-/
theorem nefFib_of_isGenerated {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D)
    (L : HermLB p) (hL : IsGenerated L.B) : ArInt.NefFib L := by
  intro Z i _ _ κ _ _ _ hd
  have := hX.finite
  have : IsProper p := CommonModel.isProper_of_isProjOver hX.isProjOver
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hX.isProjOver
  have hA := hH.pull_of_isClosedImmersion i
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  have : IsProper (strHom κ Z) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  have h := (isNef_iff_isClosedImmersion.1 ((hL.pull i).isNef (k := κ) hA)).2 Z (𝟙 Z) inferInstance inferInstance hd
    (by rw [Category.id_comp]; infer_instance)
  rw [interNumOn_id] at h
  refine h.trans_eq (congrArg _ (funext fun j => ?_))
  fin_cases j
  rfl

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Establish `P` using `presents_toLB Δ`. Set `t : Fin (n + 1) → (Y.lb Δ).Sec` to `fun a => Var.sec (w a)`. Establish `hgen (a) (x : Y.X) : Δ.GeneratesAt x (w a : Y.Fn) ↔ x ∈ nonzeroLocus (t a)`. Rewrite using `[← P.generatesAt_rat_iff, Var.rat_sec]`. Establish `ht : ⨆ a, nonzeroLocus (t a) = ⊤` using `top_le_iff.1 fun x _ =>`.

Establish `⟨a, ha⟩` using `hw x`. Use the proof step `Opens.mem_iSup.2 ⟨a, (hgen a x).1 ha⟩`. Set `c` to `Y.str ≫ spMap (algebraMap (𝓞 F) F)`. Take `⟨X, π, j, hX, hπ, hfl, H, hg⟩` from `IntModel.exists_flat_model (O := 𝓞 F) Y.str Y.isProjOver (fun _ : Unit => PSpace (𝓞 F) n) (fun _ => PSpace.str (𝓞 F) n) (fun _ => ProjSpace.toProj c t ht) (fun _ => ⟨n, 𝟙 _, inferInstance, Category.id_comp _⟩) (fun _ => ProjSpace.toProj_str c t ht)`. Take `⟨g, hg₁, hg₂⟩` from `hg ()`.

Use `CommonModel.isProper_of_isProjOver hπ` as an intermediate fact. Establish `hZ : Flat (spMap (Int.castRingHom (𝓞 F)))`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`. Conclude with `(RingHom.flat_algebraMap_iff (R := ℤ) (S := 𝓞 F)).2 inferInstance`. Establish `har : IsArithVar π Y.dim` using `⟨inferInstance, inferInstance, hX, hπ, inferInstance, IntModel.topologicalKrullDim_eq_succ (RingOfIntegers.not_isField F) H Y.topologicalKrullDim_eq⟩`.

Set `B` to `(ProjSpace.O1 (𝓞 F) n).pull g`. Establish `hB : B.IsLB` using `LB.isLB_pull (ProjSpace.O1_isLB _ n) g`. Set `s : Fin (n + 1) → B.Sec` to `fun a => secPull (ProjSpace.coord (𝓞 F) n a) g`. Set `ix (i : (B.pull j).ι) : Fin (n + 1)` to `i PUnit.unit PUnit.unit`. Establish `hU (i : (B.pull j).ι) : (B.pull j).U i ≤ ProjSpace.toProj c t ht ⁻¹ᵁ ProjSpace.chart (𝓞 F) n (ix i)`.

Rewrite using `[← hg₁]`. Conclude with `fun x hx => (pull_U _ g _).le ((pull_U B j i).le hx)`. Establish `hU' (i : (B.pull j).ι) {x : Y.X} (hx : x ∈ (B.pull j).U i) : Δ.GeneratesAt x (w (ix i) : Y.Fn)` using `(hgen _ x).2 ((ProjSpace.toProj_preimage_chart c t ht _).le (hU i hx))`. Establish `hf (a) (i : (B.pull j).ι) : (secPull (s a) j).f i = ProjSpace.pullRatio (ProjSpace.toProj c t ht) _ (ix i) (hU i) a`. Establish `hU₀` using `hU i`.

Rewrite `hU₀` using `[← hg₁]`. Use `Eq.trans ?_ (ProjSpace.pullRatio_of_eq hg₁ hU₀ _)` and prove the remaining obligations. Conclude with `congrArg (fun ψ => ψ.hom (ProjSpace.ratio (𝓞 F) n (ix i) a)) (Scheme.Hom.appLE_comp_appLE j g _ _ _ (pull_U _ g (i PUnit.unit)).le (pull_U B j i).le)`. Set `r (i : (B.pull j).ι) : Y.Fnˣ` to `if h : (w (ix i) : Y.Fn) = 0 then 1 else (Units.mk0 _ h)⁻¹`. Establish `hr (i : (B.pull j).ι) {x : Y.X} (hx : x ∈ (B.pull j).U i) : (r i : Y.Fn) = (w (ix i) : Y.Fn)⁻¹`.

Simplify using `only [r, dif_neg (hU' i hx).ne_zero, Units.val_inv_eq_inv_val, Units.val_mk0]`. Establish `key (a) (i : (B.pull j).ι) (h : genericPoint Y.X ∈ (B.pull j).U i) : (w a : Y.Fn) * r i = fnOf _ h ((secPull (s a) j).f i)`. Take `⟨m, hm⟩` from `exists_chart P.isLB (genericPoint Y.X)`. Establish `e` using `congrArg (fnOf _ (memInf h hm)) (ProjSpace.sec_eq_pullRatio_toProj_mul c t ht (ix i) a m (W := (B.pull j).U i ⊓ (Y.lb Δ).U m) (inf_le_left.trans (hU i)) inf_le_right)`. Rewrite `e` using `[map_mul, fnOf_resG, fnOf_resG, ← P.rat_mul, ← P.rat_mul, Var.rat_sec, Var.rat_sec, ← ProjSpace.resG_pullRatio (hi := hU i) inf_le_left, fnOf_resG, ← mul_assoc]`.

Rewrite using `[hf, hr i h, mul_right_cancel₀ (Units.ne_zero _) e, mul_inv_cancel_right₀ (hU' i h).ne_zero]`. Use `⟨⟨X, π, har, j, H⟩, B, hB, s, r, ProjSpace.iSup_nonzeroLocus_secPull (ProjSpace.iSup_nonzeroLocus_coord _ n) g, ⟨LB.isLB_pull hB j, fun i i' h => ?_, fun i x hx => ?_⟩, key⟩` and prove the remaining obligations. Establish `e` using `congrArg (fnOf ((B.pull j).U i ⊓ (B.pull j).U i') h) (LB.sec_rel (secPull (s (ix i')) j) i i' inf_le_left inf_le_right le_rfl)`. Rewrite `e` using `[map_mul, fnOf_resG, fnOf_resG, fnOf_resG, ← key, ← key, mul_left_comm]`. Conclude with `mul_left_cancel₀ (hU' i' h.2).ne_zero e`.

Rewrite using `[CartierDiv.isEqn_iff_generatesAt_inv, hr i hx, inv_inv]`. Conclude with `hU' i hx`.
-/
theorem exists_model_sections (Y : Var F) (Δ : Y.Dv) {n : ℕ} (w : Fin (n + 1) → Y.H0 Δ)
    (hw : ∀ x, ∃ a, Δ.GeneratesAt x (w a : Y.Fn)) :
    ∃ (M : TrueGeo.Model Y) (B : LB M.X) (_ : B.IsLB) (s : Fin (n + 1) → B.Sec) (r : (B.pull M.j).ι → Y.Fnˣ),
      ⨆ a, nonzeroLocus (s a) = ⊤ ∧ Presents Δ (B.pull M.j) r ∧
      ∀ a i (h : genericPoint Y.X ∈ (B.pull M.j).U i),
        (w a : Y.Fn) * r i = fnOf _ h ((secPull (s a) M.j).f i) := by
  classical
  have P := presents_toLB Δ
  let t : Fin (n + 1) → (Y.lb Δ).Sec := fun a => Var.sec (w a)
  have hgen (a) (x : Y.X) : Δ.GeneratesAt x (w a : Y.Fn) ↔ x ∈ nonzeroLocus (t a) := by
    rw [← P.generatesAt_rat_iff, Var.rat_sec]
  have ht : ⨆ a, nonzeroLocus (t a) = ⊤ := top_le_iff.1 fun x _ =>
    have ⟨a, ha⟩ := hw x
    Opens.mem_iSup.2 ⟨a, (hgen a x).1 ha⟩
  let c := Y.str ≫ spMap (algebraMap (𝓞 F) F)
  obtain ⟨X, π, j, hX, hπ, hfl, H, hg⟩ := IntModel.exists_flat_model (O := 𝓞 F) Y.str Y.isProjOver
    (fun _ : Unit => PSpace (𝓞 F) n) (fun _ => PSpace.str (𝓞 F) n) (fun _ => ProjSpace.toProj c t ht)
    (fun _ => ⟨n, 𝟙 _, inferInstance, Category.id_comp _⟩) (fun _ => ProjSpace.toProj_str c t ht)
  obtain ⟨g, hg₁, hg₂⟩ := hg ()
  have := CommonModel.isProper_of_isProjOver hπ
  have hZ : Flat (spMap (Int.castRingHom (𝓞 F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (RingHom.flat_algebraMap_iff (R := ℤ) (S := 𝓞 F)).2 inferInstance
  have har : IsArithVar π Y.dim := ⟨inferInstance, inferInstance, hX, hπ, inferInstance,
    IntModel.topologicalKrullDim_eq_succ (RingOfIntegers.not_isField F) H Y.topologicalKrullDim_eq⟩
  let B := (ProjSpace.O1 (𝓞 F) n).pull g
  have hB : B.IsLB := LB.isLB_pull (ProjSpace.O1_isLB _ n) g
  let s : Fin (n + 1) → B.Sec := fun a => secPull (ProjSpace.coord (𝓞 F) n a) g
  let ix (i : (B.pull j).ι) : Fin (n + 1) := i PUnit.unit PUnit.unit
  have hU (i : (B.pull j).ι) : (B.pull j).U i ≤ ProjSpace.toProj c t ht ⁻¹ᵁ ProjSpace.chart (𝓞 F) n (ix i) := by
    rw [← hg₁]
    exact fun x hx => (pull_U _ g _).le ((pull_U B j i).le hx)
  have hU' (i : (B.pull j).ι) {x : Y.X} (hx : x ∈ (B.pull j).U i) : Δ.GeneratesAt x (w (ix i) : Y.Fn) :=
    (hgen _ x).2 ((ProjSpace.toProj_preimage_chart c t ht _).le (hU i hx))
  have hf (a) (i : (B.pull j).ι) : (secPull (s a) j).f i =
      ProjSpace.pullRatio (ProjSpace.toProj c t ht) _ (ix i) (hU i) a := by
    have hU₀ := hU i
    rw [← hg₁] at hU₀
    refine Eq.trans ?_ (ProjSpace.pullRatio_of_eq hg₁ hU₀ _)
    exact congrArg (fun ψ => ψ.hom (ProjSpace.ratio (𝓞 F) n (ix i) a))
      (Scheme.Hom.appLE_comp_appLE j g _ _ _ (pull_U _ g (i PUnit.unit)).le (pull_U B j i).le)
  let r (i : (B.pull j).ι) : Y.Fnˣ := if h : (w (ix i) : Y.Fn) = 0 then 1 else (Units.mk0 _ h)⁻¹
  have hr (i : (B.pull j).ι) {x : Y.X} (hx : x ∈ (B.pull j).U i) : (r i : Y.Fn) = (w (ix i) : Y.Fn)⁻¹ := by
    simp only [r, dif_neg (hU' i hx).ne_zero, Units.val_inv_eq_inv_val, Units.val_mk0]
  have key (a) (i : (B.pull j).ι) (h : genericPoint Y.X ∈ (B.pull j).U i) :
      (w a : Y.Fn) * r i = fnOf _ h ((secPull (s a) j).f i) := by
    obtain ⟨m, hm⟩ := exists_chart P.isLB (genericPoint Y.X)
    have e := congrArg (fnOf _ (memInf h hm)) (ProjSpace.sec_eq_pullRatio_toProj_mul c t ht (ix i) a m
      (W := (B.pull j).U i ⊓ (Y.lb Δ).U m) (inf_le_left.trans (hU i)) inf_le_right)
    rw [map_mul, fnOf_resG, fnOf_resG, ← P.rat_mul, ← P.rat_mul, Var.rat_sec, Var.rat_sec,
      ← ProjSpace.resG_pullRatio (hi := hU i) inf_le_left, fnOf_resG, ← mul_assoc] at e
    rw [hf, hr i h, mul_right_cancel₀ (Units.ne_zero _) e, mul_inv_cancel_right₀ (hU' i h).ne_zero]
  refine ⟨⟨X, π, har, j, H⟩, B, hB, s, r,
    ProjSpace.iSup_nonzeroLocus_secPull (ProjSpace.iSup_nonzeroLocus_coord _ n) g,
    ⟨LB.isLB_pull hB j, fun i i' h => ?_, fun i x hx => ?_⟩, key⟩
  · have e := congrArg (fnOf ((B.pull j).U i ⊓ (B.pull j).U i') h)
      (LB.sec_rel (secPull (s (ix i')) j) i i' inf_le_left inf_le_right le_rfl)
    rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, ← key, ← key, mul_left_comm] at e
    exact mul_left_cancel₀ (hU' i' h.2).ne_zero e
  · rw [CartierDiv.isEqn_iff_generatesAt_inv, hr i hx, inv_inv]
    exact hU' i hx

section Values

variable {K : Type} [Field K] {Y : Var F} (y : Sp K ⟶ Y.X) {τ : F →+* K}

omit [NumberField F] in

/- English proof (translation)
Take `⟨a, rfl⟩` from `hf`. Take `⟨b, rfl⟩` from `hg`. Rewrite using `[← map_add, SmallSec.valAt_algebraMap, SmallSec.valAt_algebraMap, SmallSec.valAt_algebraMap, map_add]`.
-/
theorem valAt_add {f g : Y.Fn} (hf : RegAt (below y) f) (hg : RegAt (below y) g) :
    valAt y (f + g) = valAt y f + valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_add, SmallSec.valAt_algebraMap, SmallSec.valAt_algebraMap, SmallSec.valAt_algebraMap, map_add]

omit [NumberField F] in

/- English proof (translation)
Use `(SmallSec.valAt_fnOf (y := y) (U := ⊤) trivial trivial (DVR.FlatBC.algX Y.str ⊤ a)).trans ?_` and prove the remaining obligations. Use `(Points.valR_appLE y Y.str (U := ⊤) (V := ⊤) le_top (Points.le_preimage_top y) _).trans ?_` and prove the remaining obligations. Rewrite using `[hy]`. Conclude with `Points.valR_specMap (CommRingCat.ofHom τ) a`.
-/
theorem valAt_const (hy : y ≫ Y.str = spMap τ) (a : F) : valAt y (algebraMap F Y.Fn a) = τ a := by
  refine (SmallSec.valAt_fnOf (y := y) (U := ⊤) trivial trivial (DVR.FlatBC.algX Y.str ⊤ a)).trans ?_
  refine (Points.valR_appLE y Y.str (U := ⊤) (V := ⊤) le_top (Points.le_preimage_top y) _).trans ?_
  rw [hy]
  exact Points.valR_specMap (CommRingCat.ofHom τ) a

omit [NumberField F] in

def evalSec (hy : y ≫ Y.str = spMap τ) {Δ : Y.Dv} {g : Y.Fnˣ} (hg : Δ.IsEqn (below y) g) {E : Type} [AddCommGroup E]
    [Module F E] (ι : E →ₗ[F] Y.Fn) (hι : ∀ x, ι x ∈ Y.H0 Δ) : E →ₛₗ[τ] K where
  toFun x := valAt y (ι x * g)
  map_add' x x' := by
    rw [map_add, add_mul]
    exact valAt_add y (hg.regularAt_iff.1 (Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 (hι x) _)) (hg.regularAt_iff.1 (Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 (hι x') _))
  map_smul' a x := by
    rw [map_smul, Algebra.smul_def, mul_assoc, SmallSec.valAt_mul (Y.regAt_algebraMap _ a)
      (hg.regularAt_iff.1 (Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 (hι x) _)), valAt_const y hy, smul_eq_mul]

/- English proof (translation)
The claim follows from `(SmallSec.valAt_fnOf hi _ _).trans (Points.valR_appLE y M.j (pull_U B M.j i).le ((Points.le_preimage_iff _ _).2 hi) _)`.
-/
theorem valAt_secPull (M : TrueGeo.Model Y) {B : LB M.X} (s : B.Sec) {i : (B.pull M.j).ι}
    (hi : below y ∈ (B.pull M.j).U i) :
    valAt y (fnOf _ (gen_mem hi) ((secPull s M.j).f i)) = valR (y ≫ M.j) (B.U (i PUnit.unit)) (s.f (i PUnit.unit)) :=
  (SmallSec.valAt_fnOf hi _ _).trans
    (Points.valR_appLE y M.j (pull_U B M.j i).le ((Points.le_preimage_iff _ _).2 hi) _)

end Values

/- English proof (translation)
The claim follows from `(RingHom.injective_iff_ker_eq_bot σ).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (by rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot] exact RingHom.injective_int _))`.
-/
theorem injective_emb (σ : 𝓞 F →+* ℂ) : Function.Injective σ :=
  (RingHom.injective_iff_ker_eq_bot σ).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (by
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _))

def extEmb (σ : 𝓞 F →+* ℂ) : F →+* ℂ := IsFractionRing.lift (injective_emb σ)

/- English proof (translation)
The claim follows from `RingHom.ext fun a => IsFractionRing.lift_algebraMap (K := F) (injective_emb σ) a`.
-/
theorem extEmb_comp (σ : 𝓞 F →+* ℂ) : (extEmb σ).comp (algebraMap (𝓞 F) F) = σ :=
  RingHom.ext fun a => IsFractionRing.lift_algebraMap (K := F) (injective_emb σ) a

/- English proof (translation)
The claim follows from `IsFractionRing.ringHom_ext (A := 𝓞 F) fun a => RingHom.congr_fun ((extEmb_comp σ).trans h.symm) a`.
-/
theorem extEmb_eq {σ : 𝓞 F →+* ℂ} {τ : F →+* ℂ} (h : τ.comp (algebraMap (𝓞 F) F) = σ) : extEmb σ = τ :=
  IsFractionRing.ringHom_ext (A := 𝓞 F) fun a => RingHom.congr_fun ((extEmb_comp σ).trans h.symm) a

variable [StarRing F]

/- English proof (translation)
Establish `e : InfinitePlace.mk ((starRingEnd ℂ).comp τ) = InfinitePlace.mk τ` using `InfinitePlace.mk_conjugate_eq τ`. Unfold `frameAt`. Rewrite using `[e]`. Distinguish the cases in `h₁ : (InfinitePlace.mk τ).embedding = τ`. Distinguish the cases in `h₂ : (InfinitePlace.mk τ).embedding = (starRingEnd ℂ).comp τ`.

Take `⟨U, hU, e'⟩` from `h _ (InfinitePlace.isReal_mk_iff.2 (show star τ = τ from h₂.symm.trans h₁))`. Use `⟨star U, Unitary.star_mem hU, ?_⟩` and prove the remaining obligations. Rewrite using `[if_pos h₁, if_pos h₂, e', Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff.1 hU, Matrix.mul_one]`. Conclude with `⟨1, one_mem _, by rw [if_pos h₁, if_neg h₂, Matrix.mul_one]⟩`. Establish `h₂ : (InfinitePlace.mk τ).embedding = (starRingEnd ℂ).comp τ` using `(InfinitePlace.embedding_mk_eq τ).resolve_left h₁`.

Use `⟨1, one_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[if_neg h₁, if_pos h₂, Matrix.mul_one]`. Use extensionality with `a b`. Simplify using the standard rewrite rules.
-/
theorem frameAt_conj (W : HLat F)
    (h : ∀ v : InfinitePlace F, v.IsReal → ∃ U ∈ Matrix.unitaryGroup W.ι ℂ, (W.X v).map (starRingEnd ℂ) = W.X v * U)
    (τ : F →+* ℂ) : ∃ U ∈ Matrix.unitaryGroup W.ι ℂ,
      frameAt W ((starRingEnd ℂ).comp τ) = (frameAt W τ).map (starRingEnd ℂ) * U := by
  have e : InfinitePlace.mk ((starRingEnd ℂ).comp τ) = InfinitePlace.mk τ := InfinitePlace.mk_conjugate_eq τ
  unfold frameAt
  rw [e]
  by_cases h₁ : (InfinitePlace.mk τ).embedding = τ
  · by_cases h₂ : (InfinitePlace.mk τ).embedding = (starRingEnd ℂ).comp τ
    · obtain ⟨U, hU, e'⟩ := h _ (InfinitePlace.isReal_mk_iff.2 (show star τ = τ from h₂.symm.trans h₁))
      refine ⟨star U, Unitary.star_mem hU, ?_⟩
      rw [if_pos h₁, if_pos h₂, e', Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff.1 hU, Matrix.mul_one]
    · exact ⟨1, one_mem _, by rw [if_pos h₁, if_neg h₂, Matrix.mul_one]⟩
  · have h₂ : (InfinitePlace.mk τ).embedding = (starRingEnd ℂ).comp τ :=
      (InfinitePlace.embedding_mk_eq τ).resolve_left h₁
    refine ⟨1, one_mem _, ?_⟩
    rw [if_neg h₁, if_pos h₂, Matrix.mul_one]
    ext a b
    simp

/- English proof (translation)
Unfold `frameAt`. Use `split_ifs`. Conclude with `(h.1 _).ne_zero`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `((h.1 _).map _).ne_zero`.
-/
theorem det_frameAt_ne_zero {W : HLat F} (h : W.Good) (τ : F →+* ℂ) : (frameAt W τ).det ≠ 0 := by
  unfold frameAt
  split_ifs
  · exact (h.1 _).ne_zero
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((h.1 _).map _).ne_zero

/- English proof (translation)
Use `by_contra! h0`. Establish `h1` using `Matrix.eq_zero_of_vecMul_eq_zero (det_frameAt_ne_zero h τ) (v := fun j => ℓ (W.b j)) (funext fun a => by simpa [Matrix.vecMul, dotProduct, mul_comm] using h0 a)`. Take `⟨x, hx⟩` from `hℓ`. Conclude with `hx (by rw [W.b.ext (f₁ := ℓ) (f₂ := 0) fun j => congrFun h1 j]; rfl)`.
-/
theorem exists_frame_ne_zero {W : HLat F} (h : W.Good) (τ : F →+* ℂ) (ℓ : W.V →ₛₗ[τ] ℂ) (hℓ : ∃ x, ℓ x ≠ 0) :
    ∃ a, ∑ j, frameAt W τ j a * ℓ (W.b j) ≠ 0 := by
  by_contra! h0
  have h1 := Matrix.eq_zero_of_vecMul_eq_zero (det_frameAt_ne_zero h τ) (v := fun j => ℓ (W.b j))
    (funext fun a => by simpa [Matrix.vecMul, dotProduct, mul_comm] using h0 a)
  obtain ⟨x, hx⟩ := hℓ
  exact hx (by rw [W.b.ext (f₁ := ℓ) (f₂ := 0) fun j => congrFun h1 j]; rfl)

omit [NumberField F] [StarRing F] in

/- English proof (translation)
Use `by_contra! h0`. Establish `key (z : E) : Δ.VanishesAt x (ι z)`. Proceed by induction on `(hv.ge (Submodule.mem_top : z ∈ ⊤)) using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨a, rfl⟩` from `hz`.

Conclude with `CartierDiv.vanishesAt_iff.2 ⟨CartierDiv.mem_sections.1 (h.mem _ ⟨_, rfl⟩) x, h0 a⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `Δ.vanishesAt_zero x`. Consider the case `add z z' _ _ hz hz' => rw [map_add]`. Conclude with `hz.add hz'`.

Consider the case `smul a z _ hz`. Take `⟨g, hg, hz⟩` from `hz`. Use `⟨g, hg, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, Algebra.smul_def, mul_assoc, mul_comm]`. Conclude with `hz.mul (Y.regAt_algebraMap x a)`.

Take `⟨_, ⟨z, rfl⟩, hz⟩` from `h.exists_generatesAt x`. Conclude with `(CartierDiv.vanishesAt_iff.1 (key z)).2 hz`.
-/
theorem exists_generatesAt {Y : Var F} {Δ : Y.Dv} {E α : Type} [AddCommGroup E] [Module F E] (ι : E →ₗ[F] Y.Fn)
    (h : Y.bpf Δ (Set.range ι)) (v : α → E) (hv : Submodule.span F (Set.range v) = ⊤) (x : Y.X) :
    ∃ a, Δ.GeneratesAt x (ι (v a)) := by
  by_contra! h0
  have key (z : E) : Δ.VanishesAt x (ι z) := by
    induction (hv.ge (Submodule.mem_top : z ∈ ⊤)) using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, rfl⟩ := hz
      exact CartierDiv.vanishesAt_iff.2 ⟨CartierDiv.mem_sections.1 (h.mem _ ⟨_, rfl⟩) x, h0 a⟩
    | zero => rw [map_zero]; exact Δ.vanishesAt_zero x
    | add z z' _ _ hz hz' => rw [map_add]; exact hz.add hz'
    | smul a z _ hz =>
      obtain ⟨g, hg, hz⟩ := hz
      refine ⟨g, hg, ?_⟩
      rw [map_smul, Algebra.smul_def, mul_assoc, mul_comm]
      exact hz.mul (Y.regAt_algebraMap x a)
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ := h.exists_generatesAt x
  exact (CartierDiv.vanishesAt_iff.1 (key z)).2 hz

omit [StarRing F] in

/- English proof (translation)
Establish `key (x : E) (hx : x ∈ L) : ℓ x ∈ e.O`. Rewrite `hx` using `[← hL]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem z hz => obtain ⟨a, rfl⟩ := hz`. Conclude with `h₁ a`.

Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add z z' _ _ hz hz' => rw [map_add]`. Conclude with `add_mem hz hz'`. Consider the case `smul a z _ hz`.

Rewrite using `[← algebraMap_smul F a z, map_smulₛₗ, smul_eq_mul]`. Use `mul_mem ((e.mem_O _).2 ?_) hz` and prove the remaining obligations. Rewrite using `[e.w_alg]`. Conclude with `IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_le_one (K := F) v (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) a`. Establish `hle (x : L) : e.w (ℓ x * t) ≤ e.w t`.

Rewrite using `[map_mul]`. Conclude with `mul_le_of_le_one_left (e.w.nonneg t) ((e.mem_O _).1 (key x x.2))`. Take `⟨a, ha⟩` from `h₂`. Use `le_antisymm (ciSup_le hle) ?_` and prove the remaining obligations. Use `le_of_eq_of_le ?_ (le_ciSup ⟨_, Set.forall_mem_range.2 hle⟩ (⟨u a, hL ▸ Submodule.subset_span ⟨a, rfl⟩⟩ : L))` and prove the remaining obligations.

Rewrite using `[map_mul, ha, one_mul]`.
-/
theorem iSup_lattice {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) {E α : Type} [AddCommGroup E] [Module F E]
    [Module (𝓞 F) E] [IsScalarTower (𝓞 F) F E] (ℓ : E →ₛₗ[algebraMap F (AlgebraicClosure F)] AlgebraicClosure F)
    (u : α → E) {L : Submodule (𝓞 F) E} (hL : Submodule.span (𝓞 F) (Set.range u) = L)
    (h₁ : ∀ a, ℓ (u a) ∈ e.O) (h₂ : ∃ a, e.w (ℓ (u a)) = 1) (t : AlgebraicClosure F) :
    ⨆ x : L, e.w (ℓ x * t) = e.w t := by
  have key (x : E) (hx : x ∈ L) : ℓ x ∈ e.O := by
    rw [← hL] at hx
    induction hx using Submodule.span_induction with
    | mem z hz => obtain ⟨a, rfl⟩ := hz; exact h₁ a
    | zero => rw [map_zero]; exact zero_mem _
    | add z z' _ _ hz hz' => rw [map_add]; exact add_mem hz hz'
    | smul a z _ hz =>
      rw [← algebraMap_smul F a z, map_smulₛₗ, smul_eq_mul]
      refine mul_mem ((e.mem_O _).2 ?_) hz
      rw [e.w_alg]
      exact IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_le_one (K := F) v
        (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) a
  have hle (x : L) : e.w (ℓ x * t) ≤ e.w t := by
    rw [map_mul]
    exact mul_le_of_le_one_left (e.w.nonneg t) ((e.mem_O _).1 (key x x.2))
  obtain ⟨a, ha⟩ := h₂
  refine le_antisymm (ciSup_le hle) ?_
  refine le_of_eq_of_le ?_ (le_ciSup ⟨_, Set.forall_mem_range.2 hle⟩
    (⟨u a, hL ▸ Submodule.subset_span ⟨a, rfl⟩⟩ : L))
  rw [map_mul, ha, one_mul]

omit [StarRing F] in

/- English proof (translation)
Establish `h₂` using `CartierDiv.isEqn_iff_generatesAt_inv.1 h₁`. Establish `h₃ : (1 • Δ).RegularAt (under y) (g : Y.Fn)⁻¹` using `by rw [one_nsmul]; exact h₂.regularAt`. Establish `h₄ : RegAt (under y) (f * (g : Y.Fn))` using `h₁.regularAt_iff.1 (by rwa [one_nsmul] at hf)`. Establish `h₅` using `C.pn_mul Y σ _ (C.mPow Y σ Δ 1 m) _ _ y h₄ h₃`. Establish `h₆` using `C.pn_mPow Y σ Δ 1 m _ y h₂`.

Rewrite `h₅` using `[mul_inv_cancel_right₀ g.ne_zero]`. Rewrite `h₆` using `[pow_one, pow_one]`. Rewrite using `[h₅, h₆]`.
-/
theorem pn_mPow_one (C : CxSt F) {Y : Var F} (σ : F →+* ℂ) {Δ : Y.Dv} (m : C.Met Y σ Δ) (y : Pts Y σ) {g : Y.Fnˣ}
    (h₁ : Δ.IsEqn (under y) g) {f : Y.Fn} (hf : (1 • Δ).RegularAt (under y) f) :
    C.pn Y σ _ (C.mPow Y σ Δ 1 m) (C.cx Y σ f) y =
      ‖ratVal (f * (g : Y.Fn)) y‖ ^ 2 * C.pn Y σ Δ m (C.cx Y σ (g : Y.Fn)⁻¹) y := by
  have h₂ := CartierDiv.isEqn_iff_generatesAt_inv.1 h₁
  have h₃ : (1 • Δ).RegularAt (under y) (g : Y.Fn)⁻¹ := by rw [one_nsmul]; exact h₂.regularAt
  have h₄ : RegAt (under y) (f * (g : Y.Fn)) := h₁.regularAt_iff.1 (by rwa [one_nsmul] at hf)
  have h₅ := C.pn_mul Y σ _ (C.mPow Y σ Δ 1 m) _ _ y h₄ h₃
  have h₆ := C.pn_mPow Y σ Δ 1 m _ y h₂
  rw [mul_inv_cancel_right₀ g.ne_zero] at h₅
  rw [pow_one, pow_one] at h₆
  rw [h₅, h₆]

/- English proof (translation)
Introduce `F _ _ _ C Y Δ W ι hW hreal hι hb`. Take `⟨n, u₀, hu₀⟩` from `Submodule.fg_iff_exists_fin_generating_family.1 hW.2.1`. Set `u : Fin (n + 1) → W.V` to `Fin.cons 0 u₀`. Establish `hu : Submodule.span (𝓞 F) (Set.range u) = W.L`. Rewrite using `[Fin.range_cons, Submodule.span_insert_zero, hu₀]`.

Establish `hu' : Submodule.span F (Set.range u) = ⊤`. Rewrite using `[← hW.2.2, ← hu, Submodule.span_span_of_tower]`. Establish `hgen` using `exists_generatesAt ι hb u hu'`. Use `choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun F).1 (hu'.ge (Submodule.mem_top : W.b j ∈ ⊤))`. Take `⟨M, B, hB, s, r, hs, hr, hv⟩` from `exists_model_sections Y Δ (fun a => ⟨ι (u a), hι _⟩) hgen`.

Establish `val {K : Type} [Field K] (y : Sp K ⟶ Y.X) {i : (B.pull M.j).ι} (hi : below y ∈ (B.pull M.j).U i) (a) : valAt y (ι (u a) * r i) = valR (y ≫ M.j) (B.U (i PUnit.unit)) ((s a).f (i PUnit.unit))` using `(congrArg _ (hv a i (gen_mem hi))).trans (valAt_secPull y M (s a) hi)`. Set `A (τ : F →+* ℂ) : Matrix (Fin (n + 1)) W.ι ℂ` to `Matrix.of (fun a j => τ (c j a)) * frameAt W τ`. Establish `comb (τ : F →+* ℂ) (y : Pts Y τ) {i : (B.pull M.j).ι} (hi : under y ∈ (B.pull M.j).U i) (b : W.ι) : ∑ a, A τ a b * valR (y.1 ≫ M.j) (B.U (i PUnit.unit)) ((s a).f (i PUnit.unit)) = ∑ j, frameAt W τ j b * evalSec y.1 y.2 (hr.isEqn i _ hi) ι hι (W.b j)`. Simplify using `only [A, Matrix.mul_apply, Matrix.of_apply, ← hc, map_sum, map_smulₛₗ, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, ← val y.1 hi]`. Conclude with `Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by`.

Rewrite using `[mul_comm (τ _), mul_assoc]`. Use the proof step `rfl)`. Establish `nz (τ : F →+* ℂ) (y : Pts Y τ) {i : (B.pull M.j).ι} (hi : under y ∈ (B.pull M.j).U i) : ∃ b, ∑ j, frameAt W τ j b * evalSec y.1 y.2 (hr.isEqn i _ hi) ι hι (W.b j) ≠ 0` using `exists_frame_ne_zero hW τ _ (have ⟨a, ha⟩ := hgen (under y) ⟨u a, SmallSec.valAt_ne_zero ((hr.isEqn i _ hi).generatesAt_iff.1 ha)⟩)`. Establish `hz (σ : 𝓞 F →+* ℂ) : Weight.NoCommonZero fun b => ∑ a, A (extEmb σ) a b • secVal M.p σ (s a)`. Introduce `i y' hy'`.

Establish `w : y'.1 ≫ M.p = spMap (extEmb σ) ≫ spMap (algebraMap (𝓞 F) F)`. Rewrite using `[y'.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, extEmb_comp]`. Set `y : Pts Y (extEmb σ)` to `⟨M.pb.lift y'.1 _ w, M.pb.lift_snd _ _ _⟩`. Establish `e : y.1 ≫ M.j = y'.1` using `M.pb.lift_fst _ _ _`. Establish `hi : under y ∈ (B.pull M.j).U fun _ => i` using `(pull_U B M.j _).ge (by`.

Express the relevant statement in the definitionally equal form `(y.1 ≫ M.j) _ ∈ B.U i`. Rewrite using `[e]`. Conclude with `mem_ptsIn.1 hy')`. Take `⟨b, hb⟩` from `nz _ y hi`. Rewrite `hb` using `[← comb _ y hi, e]`.

Use `⟨b, ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `hb`. Establish `hcj (σ : 𝓞 F →+* ℂ) : ∃ U ∈ Matrix.unitaryGroup W.ι ℂ, A (extEmb ((starRingEnd ℂ).comp σ)) = (A (extEmb σ)).map (starRingEnd ℂ) * U`. Take `⟨U, hU, e⟩` from `frameAt_conj W hreal (extEmb σ)`.

Use `⟨U, hU, ?_⟩` and prove the remaining obligations. Rewrite using `[extEmb_eq (τ := (starRingEnd ℂ).comp (extEmb σ)) (by rw [RingHom.comp_assoc, extEmb_comp])]`. Simplify using `only [A]`. Rewrite using `[e, Matrix.map_mul, Matrix.mul_assoc]`. Both sides reduce to the same expression.

Use `⟨M, combHerm hB s (fun σ => A (extEmb σ)) hz hcj, ⟨by simp, r, ?_, ?_, ?_⟩, nefFib_of_isGenerated M.ar _ (isGenerated_of_finite s hs), fun σ => semiPosReg_combWeight hB s _ (hz σ) _⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Presents (1 • Δ) _ _`. Rewrite using `[one_nsmul]` and apply the resulting hypothesis. Introduce `σ y y' i f hy hi hf`. Establish `h₁` using `hr.isEqn i _ hi`.

Establish `e₁ (j : W.ι) : ratVal (ι (W.b j) * (r i : Y.Fn)) y = evalSec y.1 y.2 h₁ ι hι (W.b j)` using `SmallSec.ratVal_eq_valAt y (h₁.regularAt_iff.1 (Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 (hι _) _))`. Establish `hpos : 0 < ∑ b, ‖∑ j, frameAt W σ j b * evalSec y.1 y.2 h₁ ι hι (W.b j)‖ ^ 2`. Take `⟨b, hb⟩` from `nz σ y hi`. Conclude with `Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨b, Finset.mem_univ b, by positivity⟩`. Establish `h₂` using `C.pn_fs Y σ Δ (fun j => ι (W.b j)) (frameAt W σ) (r i : Y.Fn)⁻¹ y (r i) h₁ (fun _ => hι _) (CartierDiv.isEqn_iff_generatesAt_inv.1 h₁).regularAt (by simp only [e₁]; exact hpos.ne')`.

Establish `h₃ : ratVal (1 : Y.Fn) y = 1`. Establish `e` using `ratVal_fnOf (y := y) CxPts.mem_ptsIn_top trivial 1`. Rewrite `e` using `[map_one, CxPts.ev_one CxPts.mem_ptsIn_top]`. Then use the resulting hypothesis. Simplify using `only [e₁, inv_mul_cancel₀ (r i).ne_zero, h₃, norm_one, one_pow] at h₂`. Establish `h₄` using `(combWeight_φ hB s _ (hz (σ.comp (algebraMap (𝓞 F) F))) (i PUnit.unit) y').trans (show _ = Real.log (∑ b, ‖∑ j, frameAt W σ j b * evalSec y.1 y.2 h₁ ι hι (W.b j)‖ ^ 2) by`.

Rewrite using `[hy, extEmb_eq (τ := σ) rfl]`. Simplify using `only [← comb σ y hi])`. Establish `h₅` using `pn_mPow_one C σ ((ofW C Y Δ W ι).m σ) y h₁ hf`. Express the relevant statement in the definitionally equal form `Real.exp (-(2 * (1 : ℕ) * (1 : ℕ) * 0)) * _ = _ * Real.exp (-(combWeight hB s _ (hz _)).φ _ _)`. Rewrite using `[h₄, mul_zero, neg_zero, Real.exp_zero, one_mul, Real.exp_neg, Real.exp_log hpos, ← one_div, ← h₂]`.

Conclude with `h₅`. Introduce `v e y yt i h hi`. Establish `hy : below y.1 ∈ (B.pull M.j).U i` using `OfModel.le_chart M B e y yt h hi trivial`. Establish `h₁` using `hr.isEqn i _ hy`. Establish `h₂ : Δ.IsEqn (below y.1) (eqn Δ (below y.1))` using `(Δ.exists_isEqn _).choose_spec`.

Establish `h₃` using `h₁.iff_unitAt.1 h₂`. Establish `e₁ (a) : evalSec y.1 y.2 h₁ ι hι (u a) = (valR yt (B.U (i PUnit.unit)) ((s a).f (i PUnit.unit)) : e.O)`. Use `(val y.1 hy a).trans ?_` and prove the remaining obligations. Rewrite using `[← h]`. Conclude with `Points.valR_spMap_comp e.O.subtype yt _ hi _`.

Establish `e₂ : ∃ a, e.w (evalSec y.1 y.2 h₁ ι hι (u a)) = 1`. Take `⟨a, ha⟩` from `Opens.mem_iSup.1 (hs.ge (Opens.mem_top (yt (IsLocalRing.closedPoint e.O))))`. Use `⟨a, (congrArg e.w (e₁ a)).trans (OfModel.w_unit e ?_)⟩` and prove the remaining obligations. Conclude with `(Points.le_preimage_basicOpen_iff yt hi _).1 ((Points.le_preimage_iff _ _).2 ((mem_nonzeroLocus_iff_basicOpen (s a) ((Points.le_preimage_iff _ _).1 hi)).1 ha))`. Establish `e₃` using `iSup_lattice e (evalSec y.1 y.2 h₁ ι hι) u hu (fun a => e₁ a ▸ Subtype.property _) e₂ (valAt y.1 ((eqn Δ (below y.1) : Y.Fn) / r i))`.

Establish `e₄ (x : W.V) : valAt y.1 (ι x * (eqn Δ (below y.1) : Y.Fn)) = evalSec y.1 y.2 h₁ ι hι x * valAt y.1 ((eqn Δ (below y.1) : Y.Fn) / r i)`. Rewrite using `[CartierDiv.mul_eqn_eq _ _ (r i)]`. Conclude with `SmallSec.valAt_mul (h₁.regularAt_iff.1 (Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 (hι _) _)) h₃.regAt`. Establish `e₅ : valAt y.1 (((eqn Δ (below y.1))⁻¹ ^ 1 * r i : Y.Fnˣ) : Y.Fn) = (valAt y.1 ((eqn Δ (below y.1) : Y.Fn) / r i))⁻¹`. Use `eq_inv_of_mul_eq_one_left ?_` and prove the remaining obligations.

Establish `e' : (((eqn Δ (below y.1))⁻¹ ^ 1 * r i : Y.Fnˣ) : Y.Fn) = ((eqn Δ (below y.1) : Y.Fn) / r i)⁻¹`. Rewrite using `[pow_one, Units.val_mul, Units.val_inv_eq_inv_val, inv_div, div_eq_inv_mul]`. Rewrite using `[e', ← SmallSec.valAt_mul h₃.inv.regAt h₃.regAt, inv_mul_cancel₀ h₃.ne_zero, ← map_one (algebraMap F Y.Fn), valAt_const y.1 y.2, map_one]`. Express the relevant statement in the definitionally equal form `((1 : ℕ) : ℝ) * -Real.log (⨆ x : W.L, e.w (valAt y.1 (ι x * (eqn Δ (below y.1) : Y.Fn)))) = Real.log (e.w (valAt y.1 (((eqn Δ (below y.1))⁻¹ ^ 1 * r i : Y.Fnˣ) : Y.Fn))) - (1 : ℕ) * (1 : ℕ) * 0`. Simplify using `only [e₄]`.

Rewrite using `[e₃, e₅, map_inv₀, Real.log_inv]`. Simplify using the standard rewrite rules.
-/
theorem exists_induced : ∀ (F : Type) [Field F] [NumberField F] [StarRing F] (C : CxSt F) (Y : Var F) (Δ : Y.Dv)
    (W : HLat F) (ι : W.V →ₗ[F] Y.Fn), W.Good →
    (∀ v : InfinitePlace F, v.IsReal → ∃ U ∈ Matrix.unitaryGroup W.ι ℂ, (W.X v).map (starRingEnd ℂ) = W.X v * U) →
    (∀ x, ι x ∈ Y.H0 Δ) → Y.bpf Δ (Set.range ι) →
    ∃ (M : TrueGeo.Model Y) (L : HermLB M.p), (ofW C Y Δ W ι).Induced M L 1 0 ∧ ArInt.NefFib L ∧ L.SemiPos Y.dim := by
  intro F _ _ _ C Y Δ W ι hW hreal hι hb
  obtain ⟨n, u₀, hu₀⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hW.2.1
  let u : Fin (n + 1) → W.V := Fin.cons 0 u₀
  have hu : Submodule.span (𝓞 F) (Set.range u) = W.L := by
    rw [Fin.range_cons, Submodule.span_insert_zero, hu₀]
  have hu' : Submodule.span F (Set.range u) = ⊤ := by
    rw [← hW.2.2, ← hu, Submodule.span_span_of_tower]
  have hgen := exists_generatesAt ι hb u hu'
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun F).1 (hu'.ge (Submodule.mem_top : W.b j ∈ ⊤))
  obtain ⟨M, B, hB, s, r, hs, hr, hv⟩ := exists_model_sections Y Δ (fun a => ⟨ι (u a), hι _⟩) hgen
  have val {K : Type} [Field K] (y : Sp K ⟶ Y.X) {i : (B.pull M.j).ι} (hi : below y ∈ (B.pull M.j).U i) (a) :
      valAt y (ι (u a) * r i) = valR (y ≫ M.j) (B.U (i PUnit.unit)) ((s a).f (i PUnit.unit)) :=
    (congrArg _ (hv a i (gen_mem hi))).trans (valAt_secPull y M (s a) hi)
  let A (τ : F →+* ℂ) : Matrix (Fin (n + 1)) W.ι ℂ := Matrix.of (fun a j => τ (c j a)) * frameAt W τ
  have comb (τ : F →+* ℂ) (y : Pts Y τ) {i : (B.pull M.j).ι} (hi : under y ∈ (B.pull M.j).U i) (b : W.ι) :
      ∑ a, A τ a b * valR (y.1 ≫ M.j) (B.U (i PUnit.unit)) ((s a).f (i PUnit.unit)) =
        ∑ j, frameAt W τ j b * evalSec y.1 y.2 (hr.isEqn i _ hi) ι hι (W.b j) := by
    simp only [A, Matrix.mul_apply, Matrix.of_apply, ← hc, map_sum, map_smulₛₗ, smul_eq_mul, Finset.sum_mul,
      Finset.mul_sum, ← val y.1 hi]
    exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
      rw [mul_comm (τ _), mul_assoc]; rfl)
  have nz (τ : F →+* ℂ) (y : Pts Y τ) {i : (B.pull M.j).ι} (hi : under y ∈ (B.pull M.j).U i) :
      ∃ b, ∑ j, frameAt W τ j b * evalSec y.1 y.2 (hr.isEqn i _ hi) ι hι (W.b j) ≠ 0 :=
    exists_frame_ne_zero hW τ _ (have ⟨a, ha⟩ := hgen (under y)
      ⟨u a, SmallSec.valAt_ne_zero ((hr.isEqn i _ hi).generatesAt_iff.1 ha)⟩)
  have hz (σ : 𝓞 F →+* ℂ) : Weight.NoCommonZero fun b => ∑ a, A (extEmb σ) a b • secVal M.p σ (s a) := by
    intro i y' hy'
    have w : y'.1 ≫ M.p = spMap (extEmb σ) ≫ spMap (algebraMap (𝓞 F) F) := by
      rw [y'.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, extEmb_comp]
    let y : Pts Y (extEmb σ) := ⟨M.pb.lift y'.1 _ w, M.pb.lift_snd _ _ _⟩
    have e : y.1 ≫ M.j = y'.1 := M.pb.lift_fst _ _ _
    have hi : under y ∈ (B.pull M.j).U fun _ => i := (pull_U B M.j _).ge (by
      change (y.1 ≫ M.j) _ ∈ B.U i
      rw [e]
      exact mem_ptsIn.1 hy')
    obtain ⟨b, hb⟩ := nz _ y hi
    rw [← comb _ y hi, e] at hb
    refine ⟨b, ?_⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact hb
  have hcj (σ : 𝓞 F →+* ℂ) : ∃ U ∈ Matrix.unitaryGroup W.ι ℂ,
      A (extEmb ((starRingEnd ℂ).comp σ)) = (A (extEmb σ)).map (starRingEnd ℂ) * U := by
    obtain ⟨U, hU, e⟩ := frameAt_conj W hreal (extEmb σ)
    refine ⟨U, hU, ?_⟩
    rw [extEmb_eq (τ := (starRingEnd ℂ).comp (extEmb σ)) (by rw [RingHom.comp_assoc, extEmb_comp])]
    simp only [A]
    rw [e, Matrix.map_mul, Matrix.mul_assoc]
    rfl
  refine ⟨M, combHerm hB s (fun σ => A (extEmb σ)) hz hcj, ⟨by simp, r, ?_, ?_, ?_⟩,
    nefFib_of_isGenerated M.ar _ (isGenerated_of_finite s hs), fun σ => semiPosReg_combWeight hB s _ (hz σ) _⟩
  · change Presents (1 • Δ) _ _
    rwa [one_nsmul]
  · intro σ y y' i f hy hi hf
    have h₁ := hr.isEqn i _ hi
    have e₁ (j : W.ι) : ratVal (ι (W.b j) * (r i : Y.Fn)) y = evalSec y.1 y.2 h₁ ι hι (W.b j) :=
      SmallSec.ratVal_eq_valAt y (h₁.regularAt_iff.1 (Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 (hι _) _))
    have hpos : 0 < ∑ b, ‖∑ j, frameAt W σ j b * evalSec y.1 y.2 h₁ ι hι (W.b j)‖ ^ 2 := by
      obtain ⟨b, hb⟩ := nz σ y hi
      exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨b, Finset.mem_univ b, by positivity⟩
    have h₂ := C.pn_fs Y σ Δ (fun j => ι (W.b j)) (frameAt W σ) (r i : Y.Fn)⁻¹ y (r i) h₁ (fun _ => hι _)
      (CartierDiv.isEqn_iff_generatesAt_inv.1 h₁).regularAt (by simp only [e₁]; exact hpos.ne')
    have h₃ : ratVal (1 : Y.Fn) y = 1 := by
      have e := ratVal_fnOf (y := y) CxPts.mem_ptsIn_top trivial 1
      rwa [map_one, CxPts.ev_one CxPts.mem_ptsIn_top] at e
    simp only [e₁, inv_mul_cancel₀ (r i).ne_zero, h₃, norm_one, one_pow] at h₂
    have h₄ := (combWeight_φ hB s _ (hz (σ.comp (algebraMap (𝓞 F) F))) (i PUnit.unit) y').trans
      (show _ = Real.log (∑ b, ‖∑ j, frameAt W σ j b * evalSec y.1 y.2 h₁ ι hι (W.b j)‖ ^ 2) by
        rw [hy, extEmb_eq (τ := σ) rfl]
        simp only [← comb σ y hi])
    have h₅ := pn_mPow_one C σ ((ofW C Y Δ W ι).m σ) y h₁ hf
    change Real.exp (-(2 * (1 : ℕ) * (1 : ℕ) * 0)) * _ = _ * Real.exp (-(combWeight hB s _ (hz _)).φ _ _)
    rw [h₄, mul_zero, neg_zero, Real.exp_zero, one_mul, Real.exp_neg, Real.exp_log hpos, ← one_div, ← h₂]
    exact h₅
  · intro v e y yt i h hi
    have hy : below y.1 ∈ (B.pull M.j).U i := OfModel.le_chart M B e y yt h hi trivial
    have h₁ := hr.isEqn i _ hy
    have h₂ : Δ.IsEqn (below y.1) (eqn Δ (below y.1)) := (Δ.exists_isEqn _).choose_spec
    have h₃ := h₁.iff_unitAt.1 h₂
    have e₁ (a) : evalSec y.1 y.2 h₁ ι hι (u a) = (valR yt (B.U (i PUnit.unit)) ((s a).f (i PUnit.unit)) : e.O) := by
      refine (val y.1 hy a).trans ?_
      rw [← h]
      exact Points.valR_spMap_comp e.O.subtype yt _ hi _
    have e₂ : ∃ a, e.w (evalSec y.1 y.2 h₁ ι hι (u a)) = 1 := by
      obtain ⟨a, ha⟩ := Opens.mem_iSup.1 (hs.ge (Opens.mem_top (yt (IsLocalRing.closedPoint e.O))))
      refine ⟨a, (congrArg e.w (e₁ a)).trans (OfModel.w_unit e ?_)⟩
      exact (Points.le_preimage_basicOpen_iff yt hi _).1 ((Points.le_preimage_iff _ _).2
        ((mem_nonzeroLocus_iff_basicOpen (s a) ((Points.le_preimage_iff _ _).1 hi)).1 ha))
    have e₃ := iSup_lattice e (evalSec y.1 y.2 h₁ ι hι) u hu (fun a => e₁ a ▸ Subtype.property _) e₂
      (valAt y.1 ((eqn Δ (below y.1) : Y.Fn) / r i))
    have e₄ (x : W.V) : valAt y.1 (ι x * (eqn Δ (below y.1) : Y.Fn)) =
        evalSec y.1 y.2 h₁ ι hι x * valAt y.1 ((eqn Δ (below y.1) : Y.Fn) / r i) := by
      rw [CartierDiv.mul_eqn_eq _ _ (r i)]
      exact SmallSec.valAt_mul (h₁.regularAt_iff.1 (Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 (hι _) _)) h₃.regAt
    have e₅ : valAt y.1 (((eqn Δ (below y.1))⁻¹ ^ 1 * r i : Y.Fnˣ) : Y.Fn) =
        (valAt y.1 ((eqn Δ (below y.1) : Y.Fn) / r i))⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      have e' : (((eqn Δ (below y.1))⁻¹ ^ 1 * r i : Y.Fnˣ) : Y.Fn) = ((eqn Δ (below y.1) : Y.Fn) / r i)⁻¹ := by
        rw [pow_one, Units.val_mul, Units.val_inv_eq_inv_val, inv_div, div_eq_inv_mul]
      rw [e', ← SmallSec.valAt_mul h₃.inv.regAt h₃.regAt, inv_mul_cancel₀ h₃.ne_zero, ← map_one (algebraMap F Y.Fn),
        valAt_const y.1 y.2, map_one]
    change ((1 : ℕ) : ℝ) * -Real.log (⨆ x : W.L, e.w (valAt y.1 (ι x * (eqn Δ (below y.1) : Y.Fn)))) =
      Real.log (e.w (valAt y.1 (((eqn Δ (below y.1))⁻¹ ^ 1 * r i : Y.Fnˣ) : Y.Fn))) - (1 : ℕ) * (1 : ℕ) * 0
    simp only [e₄]
    rw [e₃, e₅, map_inv₀, Real.log_inv]
    simp

end GlobalTheory.TrueGeo.OfLattice

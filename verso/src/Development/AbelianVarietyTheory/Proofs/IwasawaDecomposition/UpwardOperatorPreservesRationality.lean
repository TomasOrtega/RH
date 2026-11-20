import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Formalism.LocalRingCardinality.DataLatDefs
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IndexAtLevelIffOuterClausesAnd
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.LocalToGlobal.HermitianForms.FramesLemmas
import Formalism.LocalToGlobal.GlobalTheory.GL6.BwAValIntegralNonneg

noncomputable section

namespace GlobalTheory.LevelHecke

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix
open scoped TensorProduct Pointwise

section Span

variable {D : D7} {n : ℕ}

/- English proof (translation)
Proceed by induction on `hP using AddSubgroup.closure_induction with`. Consider the case `mem p hp`. Take `⟨r', f, hf, rfl⟩` from `hp`. Conclude with `AddSubgroup.subset_closure ⟨r * r', f, hf, by rw [smul_smul, map_mul]⟩`. Consider the case `zero => rw [smul_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [smul_neg]`. Conclude with `neg_mem hx`.
-/
theorem ratSpan_smul (lam : D.what₂.Tau → DomWeight n) (r : D.what₂.LL)
    {P : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ} (hP : P ∈ RatSpan D lam) :
    D.what₂.embLL r • P ∈ RatSpan D lam := by
  induction hP using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨r', f, hf, rfl⟩ := hp
    exact AddSubgroup.subset_closure ⟨r * r', f, hf, by rw [smul_smul, map_mul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

/- English proof (translation)
Rewrite using `[MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]`.
-/
theorem map_embLL_smul {σ : Type} (r : D.what₂.LL) (F : MvPolynomial σ D.what₂.LL) :
    MvPolynomial.map D.what₂.embLL (r • F) = D.what₂.embLL r • MvPolynomial.map D.what₂.embLL F := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]

/- English proof (translation)
Proceed by induction on `hP using AddSubgroup.closure_induction with`. Consider the case `mem p hp`. Take `⟨r, f, hf, rfl⟩` from `hp`. Use `⟨r • ∏ τ, Formalism.GradedWeylDivisibility.blockEmb D.what₂.LL τ (MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ)), Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun τ => ?_, rfl⟩), ?_⟩` and prove the remaining obligations. Conclude with `Formalism.GradedWeylDivisibility.weylLeDual _ n n le_rfl _ (Formalism.L2.Col.natW_anti (lam τ)) (Formalism.L2.Col.map_mem_weyl le_rfl _ _ (hf τ))`.

Rewrite using `[map_embLL_smul, Formalism.L2.Col.map_ten]`. Use `congr 2`. Use function extensionality and compare the values at `τ`. Rewrite using `[MvPolynomial.map_map]`. Use `congr 2`.

Conclude with `RingHom.ext_int _ _`. Consider the case `zero => exact ⟨0, zero_mem _, map_zero _⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨F, hF, rfl⟩` from `hx`. Take `⟨G, hG, rfl⟩` from `hy`.

Conclude with `⟨F + G, add_mem hF hG, map_add _ _ _⟩`. Consider the case `neg x _ hx`. Take `⟨F, hF, rfl⟩` from `hx`. Conclude with `⟨-F, neg_mem hF, map_neg _ _⟩`.
-/
theorem exists_of_mem_ratSpan (lam : D.what₂.Tau → DomWeight n)
    {P : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ} (hP : P ∈ RatSpan D lam) :
    ∃ F ∈ Formalism.L2.DIV.VV D.what₂.LL lam, MvPolynomial.map D.what₂.embLL F = P := by
  induction hP using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨r, f, hf, rfl⟩ := hp
    refine ⟨r • ∏ τ, Formalism.GradedWeylDivisibility.blockEmb D.what₂.LL τ (MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ)),
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun τ => ?_, rfl⟩), ?_⟩
    · exact Formalism.GradedWeylDivisibility.weylLeDual _ n n le_rfl _ (Formalism.L2.Col.natW_anti (lam τ)) (Formalism.L2.Col.map_mem_weyl le_rfl _ _ (hf τ))
    · rw [map_embLL_smul, Formalism.L2.Col.map_ten]
      congr 2
      funext τ
      rw [MvPolynomial.map_map]
      congr 2
      exact RingHom.ext_int _ _
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨F, hF, rfl⟩ := hx
    obtain ⟨G, hG, rfl⟩ := hy
    exact ⟨F + G, add_mem hF hG, map_add _ _ _⟩
  | neg x _ hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    exact ⟨-F, neg_mem hF, map_neg _ _⟩

/- English proof (translation)
Use `haveI : CharZero D.what₂.LL := D.what₂.embLL.charZero`. Set `S : D.what₂.Tau → Set (MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL)` to `fun τ => Set.range fun w : List (Fin n × Fin n × ℕ) => MvPolynomial.rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.applyWord D.what₂.LL w (Formalism.GradedWeylDivisibility.hw D.what₂.LL le_rfl (lam τ).natW))`. Establish `hle : Formalism.L2.DIV.VV D.what₂.LL lam ≤ Submodule.span D.what₂.LL (∏ τ, S τ)`. Unfold `Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨f, hf, rfl⟩`. Establish `h1 : ∀ τ, MvPolynomial.rename (Prod.mk τ) (f τ) ∈ Submodule.span D.what₂.LL (S τ)`. Introduce `τ`. Establish `hf' : f τ ∈ delSq D.what₂.LL n (lam τ)`. Rewrite using `[← Formalism.L2.Col.nablaSq_eq_delSq]`.

Conclude with `hf τ`. Establish `h` using `Submodule.mem_map_of_mem (f := (MvPolynomial.rename (R := D.what₂.LL) (Prod.mk τ : Fin n × Fin n → D.what₂.Tau × Fin n × Fin n)).toLinearMap) hf'`. Unfold `delSq Formalism.GradedWeylDivisibility.weyl at h`. Rewrite `h` using `[Submodule.map_span, ← Set.range_comp]`. Conclude with `h`.

Rewrite using `[← Submodule.prod_span]`. Conclude with `Formalism.L2.Col.prod_mem_prod_sub _ _ _ fun τ _ => h1 τ`. Establish `hF'` using `hle hF`. Use `clear hF`. Proceed by induction on `hF' using Submodule.span_induction with`.

Consider the case `mem x hx`. Rewrite `hx` using `[Set.mem_finsetProd]`. Take `⟨g, hg, rfl⟩` from `hx`. Establish `hg' : ∀ τ, ∃ w : List (Fin n × Fin n × ℕ), MvPolynomial.rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.applyWord D.what₂.LL w (Formalism.GradedWeylDivisibility.hw D.what₂.LL le_rfl (lam τ).natW)) = g τ` using `fun τ => hg (Finset.mem_univ τ)`. Use `choose w hw using hg'`.

Use `AddSubgroup.subset_closure ⟨1, fun τ => Formalism.GradedWeylDivisibility.applyWord ℤ (w τ) (Formalism.GradedWeylDivisibility.hw ℤ le_rfl (lam τ).natW), fun τ => Submodule.subset_span ⟨w τ, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_one, one_smul, map_prod, ten]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← hw τ, MvPolynomial.map_rename, ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map, ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]`. Consider the case `zero => rw [map_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [map_embLL_smul]`. Conclude with `ratSpan_smul lam c hx`.
-/
theorem map_mem_ratSpan (lam : D.what₂.Tau → DomWeight n)
    {F : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL} (hF : F ∈ Formalism.L2.DIV.VV D.what₂.LL lam) :
    MvPolynomial.map D.what₂.embLL F ∈ RatSpan D lam := by
  classical
  haveI : CharZero D.what₂.LL := D.what₂.embLL.charZero
  let S : D.what₂.Tau → Set (MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL) := fun τ =>
    Set.range fun w : List (Fin n × Fin n × ℕ) =>
      MvPolynomial.rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.applyWord D.what₂.LL w (Formalism.GradedWeylDivisibility.hw D.what₂.LL le_rfl (lam τ).natW))
  have hle : Formalism.L2.DIV.VV D.what₂.LL lam ≤ Submodule.span D.what₂.LL (∏ τ, S τ) := by
    unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have h1 : ∀ τ, MvPolynomial.rename (Prod.mk τ) (f τ) ∈ Submodule.span D.what₂.LL (S τ) := by
      intro τ
      have hf' : f τ ∈ delSq D.what₂.LL n (lam τ) := by
        rw [← Formalism.L2.Col.nablaSq_eq_delSq]; exact hf τ
      have h := Submodule.mem_map_of_mem (f := (MvPolynomial.rename (R := D.what₂.LL)
        (Prod.mk τ : Fin n × Fin n → D.what₂.Tau × Fin n × Fin n)).toLinearMap) hf'
      unfold delSq Formalism.GradedWeylDivisibility.weyl at h
      rw [Submodule.map_span, ← Set.range_comp] at h
      exact h
    rw [← Submodule.prod_span]
    exact Formalism.L2.Col.prod_mem_prod_sub _ _ _ fun τ _ => h1 τ
  have hF' := hle hF
  clear hF
  induction hF' using Submodule.span_induction with
  | mem x hx =>
    rw [Set.mem_finsetProd] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    have hg' : ∀ τ, ∃ w : List (Fin n × Fin n × ℕ),
        MvPolynomial.rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.applyWord D.what₂.LL w (Formalism.GradedWeylDivisibility.hw D.what₂.LL le_rfl (lam τ).natW)) = g τ :=
      fun τ => hg (Finset.mem_univ τ)
    choose w hw using hg'
    refine AddSubgroup.subset_closure ⟨1, fun τ => Formalism.GradedWeylDivisibility.applyWord ℤ (w τ) (Formalism.GradedWeylDivisibility.hw ℤ le_rfl (lam τ).natW),
      fun τ => Submodule.subset_span ⟨w τ, rfl⟩, ?_⟩
    rw [map_one, one_smul, map_prod, ten]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← hw τ, MvPolynomial.map_rename, ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map,
      ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_embLL_smul]; exact ratSpan_smul lam c hx

/- English proof (translation)
Take `⟨F, hF, rfl⟩` from `exists_of_mem_ratSpan lam hP`. Rewrite using `[← Formalism.L2.Col.map_blockAct]`. Apply `map_mem_ratSpan` to reduce the goal to its premises. Conclude with `(Formalism.GradedWeylDivisibility.blockActTensor D.what₂.LL D.what₂.LL D.what₂.Tau n n g).2 (fun τ => nablaSq D.what₂.LL n (lam τ)) (fun τ => nablaSq D.what₂.LL n (lam τ)) (fun τ f hf => Formalism.GradedWeylDivisibility.dualWeylRowStable D.what₂.LL n n _ _ f hf) F hF`.
-/
theorem ratSpan_blockAct (lam : D.what₂.Tau → DomWeight n) (g : D.what₂.Tau → Matrix (Fin n) (Fin n) D.what₂.LL)
    {P : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ} (hP : P ∈ RatSpan D lam) :
    Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => (g τ).map D.what₂.embLL) P ∈ RatSpan D lam := by
  obtain ⟨F, hF, rfl⟩ := exists_of_mem_ratSpan lam hP
  rw [← Formalism.L2.Col.map_blockAct]
  apply map_mem_ratSpan
  exact (Formalism.GradedWeylDivisibility.blockActTensor D.what₂.LL D.what₂.LL D.what₂.Tau n n g).2 (fun τ => nablaSq D.what₂.LL n (lam τ))
    (fun τ => nablaSq D.what₂.LL n (lam τ)) (fun τ f hf => Formalism.GradedWeylDivisibility.dualWeylRowStable D.what₂.LL n n _ _ f hf) F hF

/- English proof (translation)
Set `g : D.what₂.Tau → Matrix (Fin n) (Fin n) D.what₂.LL` to `fun τ => γ.map fun a => D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG) a)`. Establish `hg : atInf (embT D) γ = fun τ => (g τ).map D.what₂.embLL`. Use function extensionality and compare the values at `τ`. Use extensionality with `a b`. Conclude with `bwA_embT_eq D τ (γ a b)`.

Use `⟨D.what₂.embLL (∏ τ, (g τ).det ^ s τ) • Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => (g τ).map D.what₂.embLL) P, ratSpan_smul lam _ (ratSpan_blockAct lam g hP), ?_⟩` and prove the remaining obligations. Establish `h` using `Formalism.L2.Col.fnOf_mul G s (fun τ => (g τ).map D.what₂.embLL) 1 P`. Simplify using `only [Pi.one_apply, Matrix.mul_one] at h`. Rewrite using `[hg, h, map_prod]`. Simplify using `only [map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply]`.
-/
theorem exists_ratSpan_fnOf_atInf (lam : D.what₂.Tau → DomWeight n) (G : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ)
    (s : D.what₂.Tau → ℤ) (γ : Matrix (Fin n) (Fin n) D.host.E)
    {P : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ} (hP : P ∈ RatSpan D lam) :
    ∃ Q ∈ RatSpan D lam, fnOf G s (atInf (embT D) γ) P = fnOf G s 1 Q := by
  let g : D.what₂.Tau → Matrix (Fin n) (Fin n) D.what₂.LL := fun τ =>
    γ.map fun a => D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG) a)
  have hg : atInf (embT D) γ = fun τ => (g τ).map D.what₂.embLL := by
    funext τ
    ext a b
    exact bwA_embT_eq D τ (γ a b)
  refine ⟨D.what₂.embLL (∏ τ, (g τ).det ^ s τ) • Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => (g τ).map D.what₂.embLL) P,
    ratSpan_smul lam _ (ratSpan_blockAct lam g hP), ?_⟩
  have h := Formalism.L2.Col.fnOf_mul G s (fun τ => (g τ).map D.what₂.embLL) 1 P
  simp only [Pi.one_apply, Matrix.mul_one] at h
  rw [hg, h, map_prod]
  simp only [map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply]

end Span

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Rewrite using `[T.glev0.chi_eq κ]`. Use `prod_mem fun i _ => ?_` and prove the remaining obligations. Use `finprod_induction (fun z : ℂ => z ∈ D.what₂.embLL.fieldRange) (one_mem _) (fun _ _ hx hy => mul_mem hx hy) fun v => ?_` and prove the remaining obligations. Use `finprod_induction (fun z : ℂ => z ∈ D.what₂.embLL.fieldRange) (one_mem _) (fun _ _ hx hy => mul_mem hx hy) fun hv => ?_` and prove the remaining obligations. Use `inv_mem ?_` and prove the remaining obligations.

Unfold `lamJ`. Rewrite using `[Finset.range_zero, Finset.prod_empty, mul_one]`. Conclude with `h i v hv _`.
-/
theorem chi_mem_range {D : D7} {u : D.what₂.Word} (T : Forms0 D u)
    (h : ∀ i v h x, ∃ r : D.what₂.LL, D.what₂.embLL r = T.gl.psi0 i v h x) (κ : T.cls0.lev.U) :
    ((T.cls0.lev.chi κ : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
  rw [T.glev0.chi_eq κ]
  refine prod_mem fun i _ => ?_
  refine finprod_induction (fun z : ℂ => z ∈ D.what₂.embLL.fieldRange) (one_mem _) (fun _ _ hx hy => mul_mem hx hy) fun v => ?_
  refine finprod_induction (fun z : ℂ => z ∈ D.what₂.embLL.fieldRange) (one_mem _) (fun _ _ hx hy => mul_mem hx hy) fun hv => ?_
  refine inv_mem ?_
  unfold lamJ
  rw [Finset.range_zero, Finset.prod_empty, mul_one]
  exact h i v hv _

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `(T.val0.rat _).2 ⟨hFi, fun c => ?_⟩` and prove the remaining obligations. Establish `hx` using `((T.val0.rat _).1 ⟨x, rfl⟩).2`. Establish `key : ∀ w : (D.fm u).lv 0 v c, (D.fm u).fv 0 v c w = 1 → ∃ P ∈ RatSpan D ((D.fm u).lam 0), ∀ z, (D.fm u).upT 0 v c w ((D.fm u).emb 0 x ((D.fm u).up 0 v c w)) z = fnOf _ (shiftOf (lamT u 0)) 1 P (T.val0.eY z)`. Introduce `w hw`. Take `⟨z, rfl⟩` from `T.lv0.pr_surj v c w`.

Take `⟨γ, η, κ, -, -, -, -, -, hT⟩` from `T.up_natural_level_zero v c z hw`. Take `⟨P, hP, hPe⟩` from `hx ((D.fm u).up 0 v c (T.lv0.pr v c z))`. Take `⟨Q, hQ, hQe⟩` from `exists_ratSpan_fnOf_atInf ((D.fm u).lam 0) (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) (shiftOf (lamT u 0)) (γ.1⁻¹).1 hP`. Take `⟨r, hr⟩` from `chi_mem_range T h κ⁻¹`. Use `⟨D.what₂.embLL r • Q, ratSpan_smul _ r hQ, fun s => ?_⟩` and prove the remaining obligations.

Set `y' : Fr D 0 (Nat.zero_le _)` to `(T.val0.eY s).tr _ (isUnit_det_atInf (embT D) γ.1⁻¹)`. Establish `htr : IsTr (atInf (embT D) γ.1.1) (T.val0.eY (T.val0.eY.symm y')) (T.val0.eY s)`. Rewrite using `[Equiv.apply_symm_apply]`. Introduce `τ`. Use `show (T.val0.eY s).1 τ = atInf (embT D) γ.1.1 τ * (atInf (embT D) (γ.1⁻¹).1 τ * (T.val0.eY s).1 τ)`.

Rewrite using `[← Matrix.mul_assoc, atInf_mul_inv, Matrix.one_mul]`. Rewrite using `[hT _ s _ htr, hPe, Equiv.apply_symm_apply, Formalism.L2.Col.fnOf_tr (shiftOf (lamT u 0)) 1 (atInf (embT D) (γ.1⁻¹).1) P y' (T.val0.eY s) (fun τ => rfl), map_smul, Pi.smul_apply, smul_eq_mul, ← hQe, hr, map_inv]`. Simplify using `only [Pi.one_apply, Matrix.one_mul]`. Use `choose! P hP hPe using key`. Use `⟨∑ w ∈ Finset.univ.filter (fun w : (D.fm u).lv 0 v c => (D.fm u).fv 0 v c w = 1), P w, sum_mem fun w hw => hP w (Finset.mem_filter.1 hw).2, fun z => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sum, Finset.sum_apply]`. Simplify using `only [LT.Uop, LinearMap.pi_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.coe_coe]`. Use `Finset.sum_congr rfl fun w hw => hPe w (Finset.mem_filter.1 hw).2 z` and compare the differences between its conclusion and the goal.
-/
theorem uop_rat (D : D7) (u : D.what₂.Word) (T : Forms0 D u)
    (h : ∀ i v h x, ∃ r : D.what₂.LL, D.what₂.embLL r = T.gl.psi0 i v h x)
    (v : (D.mem u).A.vT) (x : ((D.fm u).lat 0).V)
    (hFi : LT.Uop D u 0 v ((D.fm u).emb 0 x) ∈ (D.fm u).Fi 0) :
    ∃ y, (D.fm u).emb 0 y = LT.Uop D u 0 v ((D.fm u).emb 0 x) := by
  classical
  refine (T.val0.rat _).2 ⟨hFi, fun c => ?_⟩
  have hx := ((T.val0.rat _).1 ⟨x, rfl⟩).2
  have key : ∀ w : (D.fm u).lv 0 v c, (D.fm u).fv 0 v c w = 1 → ∃ P ∈ RatSpan D ((D.fm u).lam 0), ∀ z,
      (D.fm u).upT 0 v c w ((D.fm u).emb 0 x ((D.fm u).up 0 v c w)) z =
        fnOf _ (shiftOf (lamT u 0)) 1 P (T.val0.eY z) := by
    intro w hw
    obtain ⟨z, rfl⟩ := T.lv0.pr_surj v c w
    obtain ⟨γ, η, κ, -, -, -, -, -, hT⟩ := T.up_natural_level_zero v c z hw
    obtain ⟨P, hP, hPe⟩ := hx ((D.fm u).up 0 v c (T.lv0.pr v c z))
    obtain ⟨Q, hQ, hQe⟩ := exists_ratSpan_fnOf_atInf ((D.fm u).lam 0)
      (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) (shiftOf (lamT u 0)) (γ.1⁻¹).1 hP
    obtain ⟨r, hr⟩ := chi_mem_range T h κ⁻¹
    refine ⟨D.what₂.embLL r • Q, ratSpan_smul _ r hQ, fun s => ?_⟩
    let y' : Fr D 0 (Nat.zero_le _) := (T.val0.eY s).tr _ (isUnit_det_atInf (embT D) γ.1⁻¹)
    have htr : IsTr (atInf (embT D) γ.1.1) (T.val0.eY (T.val0.eY.symm y')) (T.val0.eY s) := by
      rw [Equiv.apply_symm_apply]
      intro τ
      show (T.val0.eY s).1 τ = atInf (embT D) γ.1.1 τ * (atInf (embT D) (γ.1⁻¹).1 τ * (T.val0.eY s).1 τ)
      rw [← Matrix.mul_assoc, atInf_mul_inv, Matrix.one_mul]
    rw [hT _ s _ htr, hPe, Equiv.apply_symm_apply,
      Formalism.L2.Col.fnOf_tr (shiftOf (lamT u 0)) 1 (atInf (embT D) (γ.1⁻¹).1) P y' (T.val0.eY s) (fun τ => rfl),
      map_smul, Pi.smul_apply, smul_eq_mul, ← hQe, hr, map_inv]
    simp only [Pi.one_apply, Matrix.one_mul]
  choose! P hP hPe using key
  refine ⟨∑ w ∈ Finset.univ.filter (fun w : (D.fm u).lv 0 v c => (D.fm u).fv 0 v c w = 1), P w,
    sum_mem fun w hw => hP w (Finset.mem_filter.1 hw).2, fun z => ?_⟩
  rw [map_sum, Finset.sum_apply]
  simp only [LT.Uop, LinearMap.pi_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearEquiv.coe_coe]
  convert Finset.sum_congr rfl fun w hw => hPe w (Finset.mem_filter.1 hw).2 z

end GlobalTheory.LevelHecke

end

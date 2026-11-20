import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfCharInfCharOfCommute

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host
open GlobalTheory.CuspRep (Af GA finGL)

namespace UpperTheory.V.TR.Cen

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}

/- English proof (translation)
Set `S : Subalgebra ℂ (Module.End ℂ (Sm E a))` to `Subalgebra.centralizer ℂ {z}`. Establish `hS : ∀ x, x ∈ S ↔ Commute x z` using `fun x => by`. Simplify using `only [S, Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]`. Conclude with `⟨fun h => h.symm, fun h => h.symm⟩`. Establish `hE : ∀ i j, Eop τ i j ∈ S` using `fun i j => (hS _).2 (h i j)`.

Use `(hS _).1 ?_` and prove the remaining obligations. Use `S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)` and prove the remaining obligations. Take `⟨k, rfl⟩` from `List.mem_ofFn.1 hx`. Use `S.add_mem ?_ (hE _ _)` and prove the remaining obligations. Use `split_ifs`.

Conclude with `S.algebraMap_mem _`. Conclude with `S.zero_mem`.
-/
theorem commute_cap_of_commute_Eop (τ : InfinitePlace E) (u : ℂ) (z : Module.End ℂ (Sm E a))
    (h : ∀ i j, Commute (Eop τ i j) z) : Commute (cap τ u) z := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) := Subalgebra.centralizer ℂ {z}
  have hS : ∀ x, x ∈ S ↔ Commute x z := fun x => by
    simp only [S, Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hE : ∀ i j, Eop τ i j ∈ S := fun i j => (hS _).2 (h i j)
  refine (hS _).1 ?_
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hE _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

/- English proof (translation)
Distinguish the cases in `h : τ = τ'`. Substitute `h` using the available equality. Conclude with `cap_comm τ u i j`. Conclude with `commute_cap_of_commute_Eop τ u _ fun k l => Eop_comm h k l i j`.
-/
theorem commute_cap_Eop (τ τ' : InfinitePlace E) (u : ℂ) (i j : Fin a) : Commute (cap τ u) (Eop τ' i j) := by
  by_cases h : τ = τ'
  · subst h; exact cap_comm τ u i j
  · exact commute_cap_of_commute_Eop τ u _ fun k l => Eop_comm h k l i j

open Classical in

/- English proof (translation)
Establish `e : (Pi.single v t : Rinf E) = t • Pi.single v 1`. Rewrite using `[← Pi.single_smul, smul_eq_mul, mul_one]`. Rewrite using `[e, map_smul, Eop_eq]`. Both sides reduce to the same expression.
-/
theorem lieS_single (v : InfinitePlace E) (i j : Fin a) (t : ℝ) :
    lieS E a i j (Pi.single v t) = (t : ℂ) • Eop v i j := by
  have e : (Pi.single v t : Rinf E) = t • Pi.single v 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [e, map_smul, Eop_eq]
  rfl

/- English proof (translation)
Establish `hX : lie E a X = ∑ i, ∑ j, lieS E a i j (X i j)`. Simplify using `only [lieS_apply, ← map_sum]`. Conclude with `congrArg _ (Matrix.matrix_eq_sum_single (Matrix.of X))`. Rewrite using `[hX]`. Use `Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.univ_sum_single (X i j), map_sum]`. Use `Commute.sum_right _ _ _ fun w _ => ?_` and prove the remaining obligations. Rewrite using `[lieS_single]`. Conclude with `(commute_cap_Eop τ w u i j).smul_right _`.
-/
theorem commute_cap_lie (τ : InfinitePlace E) (u : ℂ) (X : Lie E a) : Commute (cap τ u) (lie E a X) := by
  classical
  have hX : lie E a X = ∑ i, ∑ j, lieS E a i j (X i j) := by
    simp only [lieS_apply, ← map_sum]
    exact congrArg _ (Matrix.matrix_eq_sum_single (Matrix.of X))
  rw [hX]
  refine Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => ?_
  rw [← Finset.univ_sum_single (X i j), map_sum]
  refine Commute.sum_right _ _ _ fun w _ => ?_
  rw [lieS_single]
  exact (commute_cap_Eop τ w u i j).smul_right _

/- English proof (translation)
The claim follows from `commute_cap_of_commute_Eop τ u _ fun _ _ => lie_rt_fin _ k`.
-/
theorem commute_cap_finRep (τ : InfinitePlace E) (u : ℂ) (k : GL (Fin a) (Af E)) : Commute (cap τ u) (finRep E a k) :=
  commute_cap_of_commute_Eop τ u _ fun _ _ => lie_rt_fin _ k

/- English proof (translation)
Use `LinearMap.ext fun φ => Subtype.ext <| funext fun g => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `fderiv ℝ (chart φ.1 (g * infGL E a y)) (oneL E a) (toL X) = fderiv ℝ (chart (fun x => φ.1 (x * infGL E a y)) g) (oneL E a) (toL (y.val * X * (y⁻¹).val))`. Establish `hd : DifferentiableAt ℝ (chart φ.1 g) (toL y.val)` using `(contDiffAt_chart φ.2 g (val_mem_invSet y)).differentiableAt (by simp)`. Establish `e1 : lmul (toL y.val) (oneL E a) = toL y.val` using `mul_one y.val`. Establish `e2 : rmul (toL y.val) (oneL E a) = toL y.val` using `one_mul y.val`.

Rewrite using `[chart_mul, chart_rt_inf, fderiv_comp _ (by rw [e1]; exact hd) (lmul (toL y.val)).differentiableAt, fderiv_comp _ (by rw [e2]; exact hd) (rmul (toL y.val)).differentiableAt, e1, e2, ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]`. Conclude with `congrArg (fun Z => fderiv ℝ (chart φ.1 g) (toL y.val) (toL Z)) (Units.inv_mul_cancel_right (y.val * X) y).symm`.
-/
theorem rt_lie (y : GL (Fin a) (Rinf E)) (X : Matrix (Fin a) (Fin a) (Rinf E)) :
    rt E a (infGL E a y) * lie E a (toL X) = lie E a (toL (y.val * X * (y⁻¹).val)) * rt E a (infGL E a y) := by
  refine LinearMap.ext fun φ => Subtype.ext <| funext fun g => ?_
  change fderiv ℝ (chart φ.1 (g * infGL E a y)) (oneL E a) (toL X) =
    fderiv ℝ (chart (fun x => φ.1 (x * infGL E a y)) g) (oneL E a) (toL (y.val * X * (y⁻¹).val))
  have hd : DifferentiableAt ℝ (chart φ.1 g) (toL y.val) :=
    (contDiffAt_chart φ.2 g (val_mem_invSet y)).differentiableAt (by simp)
  have e1 : lmul (toL y.val) (oneL E a) = toL y.val := mul_one y.val
  have e2 : rmul (toL y.val) (oneL E a) = toL y.val := one_mul y.val
  rw [chart_mul, chart_rt_inf, fderiv_comp _ (by rw [e1]; exact hd) (lmul (toL y.val)).differentiableAt,
    fderiv_comp _ (by rw [e2]; exact hd) (rmul (toL y.val)).differentiableAt, e1, e2,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  exact congrArg (fun Z => fderiv ℝ (chart φ.1 g) (toL y.val) (toL Z)) (Units.inv_mul_cancel_right (y.val * X) y).symm

/- English proof (translation)
Rewrite using `[Eop_eq, lieS_apply, rt_lie]`. Use `congr 1`. Establish `e : y.val * Matrix.single i j (Pi.single τ 1 : Rinf E) * (y⁻¹).val = ∑ k, ∑ l, Matrix.single k l (Pi.single τ (y.val k i τ * (y⁻¹).val j l τ) : Rinf E)`. Rewrite using `[Matrix.matrix_eq_sum_single (y.val * Matrix.single i j (Pi.single τ 1 : Rinf E) * (y⁻¹).val)]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Use `congr 1`. Establish `h1 : (y.val * Matrix.single i j (Pi.single τ 1 : Rinf E) * (y⁻¹).val) k l = y.val k i * (y⁻¹).val j l * Pi.single τ 1`. Simplify using `[Matrix.mul_apply, Matrix.single_apply, ite_and, mul_right_comm]`. Rewrite using `[h1]`. Use function extensionality and compare the values at `w`.

Distinguish the cases in `hw : w = τ`. Substitute `hw` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne hw]`. Rewrite using `[e]`.

Set `L : Matrix (Fin a) (Fin a) (Rinf E) →ₗ[ℝ] Module.End ℂ (Sm E a)` to `lie E a`. Establish `key : ∀ f : Fin a → Fin a → Matrix (Fin a) (Fin a) (Rinf E), L (∑ k, ∑ l, f k l) = ∑ k, ∑ l, L (f k l)` using `fun f => by simp only [map_sum]`. Use `(key _).trans (Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_)` and prove the remaining obligations. Rewrite using `[← Complex.ofReal_mul, ← lieS_single]`. Both sides reduce to the same expression.
-/
theorem rt_Eop (y : GL (Fin a) (Rinf E)) (τ : InfinitePlace E) (i j : Fin a) :
    rt E a (infGL E a y) * Eop τ i j =
      (∑ k, ∑ l, (((y.val k i τ : ℝ) : ℂ) * (((y⁻¹).val j l τ : ℝ) : ℂ)) • Eop τ k l) * rt E a (infGL E a y) := by
  classical
  rw [Eop_eq, lieS_apply, rt_lie]
  congr 1
  have e : y.val * Matrix.single i j (Pi.single τ 1 : Rinf E) * (y⁻¹).val =
      ∑ k, ∑ l, Matrix.single k l (Pi.single τ (y.val k i τ * (y⁻¹).val j l τ) : Rinf E) := by
    rw [Matrix.matrix_eq_sum_single (y.val * Matrix.single i j (Pi.single τ 1 : Rinf E) * (y⁻¹).val)]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    congr 1
    have h1 : (y.val * Matrix.single i j (Pi.single τ 1 : Rinf E) * (y⁻¹).val) k l =
        y.val k i * (y⁻¹).val j l * Pi.single τ 1 := by
      simp [Matrix.mul_apply, Matrix.single_apply, ite_and, mul_right_comm]
    rw [h1]
    funext w
    by_cases hw : w = τ
    · subst hw; simp
    · simp [Pi.single_eq_of_ne hw]
  rw [e]
  let L : Matrix (Fin a) (Fin a) (Rinf E) →ₗ[ℝ] Module.End ℂ (Sm E a) := lie E a
  have key : ∀ f : Fin a → Fin a → Matrix (Fin a) (Fin a) (Rinf E), L (∑ k, ∑ l, f k l) = ∑ k, ∑ l, L (f k l) :=
    fun f => by simp only [map_sum]
  refine (key _).trans (Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_)
  rw [← Complex.ofReal_mul, ← lieS_single]
  rfl

/- English proof (translation)
Establish `h` using `GlobalTheory.CapAdInv.qdet_semiconj _ _ _ (rt_Eop y τ) (u + ((a : ℂ) - 1) / 2)`. Set `c : Rinf E →+* ℂ` to `Complex.ofRealHom.comp (Pi.evalRingHom (fun _ => ℝ) τ)`. Establish `hQP : ((y⁻¹).val.map c) * (y.val.map c) = 1`. Rewrite using `[← Matrix.map_mul, Units.inv_mul]`. Simplify using the standard rewrite rules.

Establish `h2` using `GlobalTheory.CapAdInv.qdet_ad _ (glRel_Eop τ) _ _ hQP (u + ((a : ℂ) - 1) / 2)`. Conclude with `(h.trans (congrArg (· * rt E a (infGL E a y)) h2)).symm`.
-/
theorem commute_cap_rt_infGL (τ : InfinitePlace E) (u : ℂ) (y : GL (Fin a) (Rinf E)) :
    Commute (cap (a := a) τ u) (rt E a (infGL E a y)) := by
  have h := GlobalTheory.CapAdInv.qdet_semiconj _ _ _ (rt_Eop y τ) (u + ((a : ℂ) - 1) / 2)
  let c : Rinf E →+* ℂ := Complex.ofRealHom.comp (Pi.evalRingHom (fun _ => ℝ) τ)
  have hQP : ((y⁻¹).val.map c) * (y.val.map c) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul]; simp
  have h2 := GlobalTheory.CapAdInv.qdet_ad _ (glRel_Eop τ) _ _ hQP (u + ((a : ℂ) - 1) / 2)
  exact (h.trans (congrArg (· * rt E a (infGL E a y)) h2)).symm

/- English proof (translation)
Consider the cases of `o with`. Consider the case `fin k => exact commute_cap_finRep τ u k`. Consider the case `cpt k => exact commute_cap_rt_infGL τ u _`. Consider the case `lie X => exact commute_cap_lie τ u X`.
-/
theorem commute_cap_act (τ : InfinitePlace E) (u : ℂ) (o : Op E a) : Commute (cap (a := a) τ u) (act o) := by
  cases o with
  | fin k => exact commute_cap_finRep τ u k
  | cpt k => exact commute_cap_rt_infGL τ u _
  | lie X => exact commute_cap_lie τ u X

/- English proof (translation)
Proceed by induction on `hz using Algebra.adjoin_induction with`. Consider the case `mem x hx => obtain ⟨τ, u, rfl⟩ := hx`. Conclude with `commute_cap_act τ u o`. Consider the case `algebraMap r => exact Algebra.commutes r _`. Consider the case `add x y _ _ hx hy => exact hx.add_left hy`.

Consider the case `mul x y _ _ hx hy => exact hx.mul_left hy`.
-/
theorem commute_Zalg_act {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (o : Op E a) : Commute z (act o) := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨τ, u, rfl⟩ := hx; exact commute_cap_act τ u o
  | algebraMap r => exact Algebra.commutes r _
  | add x y _ _ hx hy => exact hx.add_left hy
  | mul x y _ _ hx hy => exact hx.mul_left hy

/- English proof (translation)
Establish `hc` using `commute_Zalg_act hz`. Take `⟨φ, hφ, h0⟩` from `(Submodule.ne_bot_iff _).1 π.ne_bot`. Use `set U := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hU`. Establish `hfin : FiniteDimensional ℂ U` using `(π.cusp φ hφ).1.zfin`. Establish `hle : U ≤ π.V` using `Submodule.span_le.2 (by`.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `Zalg_stable (fun X => π.stable (.lie X)) hy φ hφ)`. Establish `hst : ∀ x ∈ U, z x ∈ U` using `fun x hx => by`. Establish `: U ≤ U.comap z` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Conclude with `Submodule.subset_span ⟨z * y, mul_mem hz hy, rfl⟩)`. Conclude with `this hx`. Establish `hφU : φ ∈ U` using `Submodule.subset_span ⟨1, one_mem _, rfl⟩`. Establish `: Nontrivial U` using `⟨⟨φ, hφU⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩`. Take `⟨c, hc'⟩` from `Module.End.exists_eigenvalue (z.restrict hst)`.

Take `⟨v, hv⟩` from `hc'.exists_hasEigenvector`. Establish `hv1 : z v.1 = c • v.1` using `congrArg Subtype.val hv.apply_eq_smul`. Use `⟨c, fun ψ hψ => ?_⟩` and prove the remaining obligations. Break down `π.irred (π.V ⊓ z.eigenspace c) inf_le_left (fun o x hx => ⟨π.stable o x hx.1, by` into its components or cases. Establish `h1 : z x = c • x` using `Module.End.mem_eigenspace_iff.1 hx.2`.

Use `Module.End.mem_eigenspace_iff.2 ?_` and prove the remaining obligations. Rewrite using `[← map_smul, ← h1]`. Conclude with `LinearMap.congr_fun (hc o).eq x⟩) with h | h`. Establish `: v.1 ∈ π.V ⊓ z.eigenspace c` using `⟨hle v.2, Module.End.mem_eigenspace_iff.2 hv1⟩`. Rewrite `this` using `[h]`.

Conclude with `absurd (Subtype.ext ((Submodule.mem_bot ℂ).1 this)) hv.2`. Rewrite `hψ` using `[← h]`. Conclude with `Module.End.mem_eigenspace_iff.1 hψ.2`.
-/
theorem exists_scalar (π : CuspSub E a) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    ∃ c : ℂ, ∀ φ ∈ π.V, z φ = c • φ := by
  have hc := commute_Zalg_act hz
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  set U := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hU
  have hfin : FiniteDimensional ℂ U := (π.cusp φ hφ).1.zfin
  have hle : U ≤ π.V := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact Zalg_stable (fun X => π.stable (.lie X)) hy φ hφ)
  have hst : ∀ x ∈ U, z x ∈ U := fun x hx => by
    have : U ≤ U.comap z := Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.subset_span ⟨z * y, mul_mem hz hy, rfl⟩)
    exact this hx
  have hφU : φ ∈ U := Submodule.subset_span ⟨1, one_mem _, rfl⟩
  have : Nontrivial U := ⟨⟨φ, hφU⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue (z.restrict hst)
  obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
  have hv1 : z v.1 = c • v.1 := congrArg Subtype.val hv.apply_eq_smul
  refine ⟨c, fun ψ hψ => ?_⟩
  rcases π.irred (π.V ⊓ z.eigenspace c) inf_le_left (fun o x hx => ⟨π.stable o x hx.1, by
    have h1 : z x = c • x := Module.End.mem_eigenspace_iff.1 hx.2
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [← map_smul, ← h1]
    exact LinearMap.congr_fun (hc o).eq x⟩) with h | h
  · have : v.1 ∈ π.V ⊓ z.eigenspace c := ⟨hle v.2, Module.End.mem_eigenspace_iff.2 hv1⟩
    rw [h] at this
    exact absurd (Subtype.ext ((Submodule.mem_bot ℂ).1 this)) hv.2
  · rw [← h] at hψ
    exact Module.End.mem_eigenspace_iff.1 hψ.2

/- English proof (translation)
Establish `hc : ∀ v u, ∃ c : ℂ, ∀ φ ∈ π.V, cap v u φ = c • φ` using `fun v u => exists_scalar π (Algebra.subset_adjoin ⟨v, u, rfl⟩)`. Use `choose c hc using hc`. Conclude with `⟨c, hc⟩`.
-/
theorem exists_cap_scalar (π : CuspSub E a) : ∃ c : InfinitePlace E → ℂ → ℂ, ∀ v u, ∀ φ ∈ π.V, cap v u φ = c v u • φ := by
  have hc : ∀ v u, ∃ c : ℂ, ∀ φ ∈ π.V, cap v u φ = c • φ := fun v u =>
    exists_scalar π (Algebra.subset_adjoin ⟨v, u, rfl⟩)
  choose c hc using hc
  exact ⟨c, hc⟩

/- English proof (translation)
Take `⟨φ, hφ, h0⟩` from `(Submodule.ne_bot_iff _).1 π.ne_bot`. Take `⟨f, hf⟩` from `Module.Projective.exists_dual_eq_one ℂ h0`. Take `⟨m, hm, h⟩` from `GlobalTheory.CuspRep.exists_multiset_qdet (Eop (a := a) v) (((a : ℂ) - 1) / 2) φ f hf`. Use `⟨m, hm, fun u ψ hψ => ?_⟩` and prove the remaining obligations. Take `⟨c, h1⟩` from `exists_cap_scalar π`.

Establish `h2 : f (cap v u φ) = _` using `h u`. Rewrite `h2` using `[h1 v u φ hφ, map_smul, hf, smul_eq_mul, mul_one]`. Rewrite using `[h1 v u ψ hψ, h2]`.
-/
theorem exists_hasInfChar (π : CuspSub E a) (v : InfinitePlace E) : ∃ m, π.HasInfChar v m := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  obtain ⟨m, hm, h⟩ := GlobalTheory.CuspRep.exists_multiset_qdet (Eop (a := a) v) (((a : ℂ) - 1) / 2) φ f hf
  refine ⟨m, hm, fun u ψ hψ => ?_⟩
  obtain ⟨c, h1⟩ := exists_cap_scalar π
  have h2 : f (cap v u φ) = _ := h u
  rw [h1 v u φ hφ, map_smul, hf, smul_eq_mul, mul_one] at h2
  rw [h1 v u ψ hψ, h2]

/- English proof (translation)
Establish `e : (fun k : Kinf E a => (cptRep E a k φ).1 g) = fun k => chart φ.1 g (toL (Unitary.toUnits k : GL (Fin a) (Rinf E)).val)`. Use function extensionality and compare the values at `k`. Rewrite using `[chart_val]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Establish `h3 : Continuous fun k : Kinf E a => toL ((Unitary.toUnits k : GL (Fin a) (Rinf E)) : Matrix (Fin a) (Fin a) (Rinf E))` using `continuous_subtype_val`. Conclude with `(φ.2 g).continuousOn.comp_continuous h3 fun k => val_mem_invSet _`.
-/
theorem continuous_cptRep (φ : Sm E a) (g : GA E a) : Continuous fun k : Kinf E a => (cptRep E a k φ).1 g := by
  have e : (fun k : Kinf E a => (cptRep E a k φ).1 g) =
      fun k => chart φ.1 g (toL (Unitary.toUnits k : GL (Fin a) (Rinf E)).val) := by
    funext k
    rw [chart_val]
    rfl
  rw [e]
  have h3 : Continuous fun k : Kinf E a =>
      toL ((Unitary.toUnits k : GL (Fin a) (Rinf E)) : Matrix (Fin a) (Fin a) (Rinf E)) := continuous_subtype_val
  exact (φ.2 g).continuousOn.comp_continuous h3 fun k => val_mem_invSet _

end UpperTheory.V.TR.Cen

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.VolBr.RepDict

/- English proof (translation)
Take `⟨c₀, h₀⟩ : ∃ c, genericPoint X ∈ B.U c` from `Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top _))`. Use `⟨fun u => fnOf _ h₀ (u.f c₀) / ρ c₀, fun u c hc => ?_⟩` and prove the remaining obligations. Establish `e : fnOf _ hc (u.f c) = fnOf _ (memInf hc h₀) (B.g c c₀ : Γ(X, B.U c ⊓ B.U c₀)) * fnOf _ h₀ (u.f c₀)`. Rewrite using `[← fnOf_resG inf_le_left (memInf hc h₀), ← fnOf_resG inf_le_right (memInf hc h₀), ← map_mul]`. Conclude with `congrArg _ (u.compat c c₀)`.

Rewrite using `[e, hρ c c₀ (memInf hc h₀)]`. Use `(ρ c₀).ne_zero` as an intermediate fact. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_quot {X : Scheme.{0}} [IsIntegral X] {B : LB X} (hB : B.IsLB) {ρ : B.ι → X.functionFieldˣ}
    (hρ : IsRatSec B ρ) : ∃ e : B.Sec → X.functionField,
      ∀ u c (hc : genericPoint X ∈ B.U c), e u * (ρ c : X.functionField) = fnOf _ hc (u.f c) := by
  obtain ⟨c₀, h₀⟩ : ∃ c, genericPoint X ∈ B.U c := Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top _))
  refine ⟨fun u => fnOf _ h₀ (u.f c₀) / ρ c₀, fun u c hc => ?_⟩
  have e : fnOf _ hc (u.f c) = fnOf _ (memInf hc h₀) (B.g c c₀ : Γ(X, B.U c ⊓ B.U c₀)) * fnOf _ h₀ (u.f c₀) := by
    rw [← fnOf_resG inf_le_left (memInf hc h₀), ← fnOf_resG inf_le_right (memInf hc h₀), ← map_mul]
    exact congrArg _ (u.compat c c₀)
  rw [e, hρ c c₀ (memInf hc h₀)]
  have := (ρ c₀).ne_zero
  field_simp

/- English proof (translation)
Establish `h : ∀ c, ∃ a : Γ(X, B.U c), ∀ hc, fnOf _ hc a = f * ρ c` using `fun c => by`. Distinguish the cases in `hc : genericPoint X ∈ B.U c`. Take `⟨a, ha⟩` from `exists_fnOf_eq hc (hf c)`. Conclude with `⟨a, fun _ => ha⟩`. Conclude with `⟨0, fun h => (hc h).elim⟩`.

Use `choose a ha using h`. Use `⟨⟨a, fun i j => Cartier.fn_ext fun h => ?_⟩, ha⟩` and prove the remaining obligations. Rewrite using `[map_mul]`. Use `(fnOf_resG _ h _).trans (Eq.trans ?_ (congrArg (_ * ·) (fnOf_resG _ h _).symm))` and prove the remaining obligations. Rewrite using `[ha, ha, hρ i j h]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_sec {X : Scheme.{0}} [IsIntegral X] {B : LB X} {ρ : B.ι → X.functionFieldˣ}
    (hρ : IsRatSec B ρ) {f : X.functionField} (hf : ∀ c, ∀ x ∈ B.U c, RegAt x (f * ρ c)) :
    ∃ u : B.Sec, ∀ c (hc : genericPoint X ∈ B.U c), fnOf _ hc (u.f c) = f * ρ c := by
  have h : ∀ c, ∃ a : Γ(X, B.U c), ∀ hc, fnOf _ hc a = f * ρ c := fun c => by
    by_cases hc : genericPoint X ∈ B.U c
    · obtain ⟨a, ha⟩ := exists_fnOf_eq hc (hf c)
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => (hc h).elim⟩
  choose a ha using h
  refine ⟨⟨a, fun i j => Cartier.fn_ext fun h => ?_⟩, ha⟩
  rw [map_mul]
  refine (fnOf_resG _ h _).trans (Eq.trans ?_ (congrArg (_ * ·) (fnOf_resG _ h _).symm))
  rw [ha, ha, hρ i j h]
  ring

/- English proof (translation)
Introduce `k _ X _ p P a b M ⟨ρ, hρ, hu, hn⟩`. Take `⟨e, he⟩` from `exists_quot M.isLB hρ`. Establish `hcov {B : LB X} (hB : B.IsLB) (x : X) : ∃ c, x ∈ B.U c` using `Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top _))`. Establish `hl (f : X.functionField) c i j : P.loc a b f i j * ((ρ c : X.functionField) / P.loc a b 1 i j) = f * ρ c`. Use `(P.r i).ne_zero` as an intermediate fact.

Use `(P.r' j).ne_zero` as an intermediate fact. Simplify using `only [Pair.loc]`. Clear the denominators using the available nonvanishing facts. Establish `hl' (f : X.functionField) c i j : P.loc a b f i j = f * ρ c * ((ρ c : X.functionField) / P.loc a b 1 i j)⁻¹`. Use `(P.r i).ne_zero` as an intermediate fact.

Use `(P.r' j).ne_zero` as an intermediate fact. Use `(ρ c).ne_zero` as an intermediate fact. Simplify using `only [Pair.loc]`. Clear the denominators using the available nonvanishing facts. Establish `hmem u : e u ∈ P.H a b` using `fun x i j hi hj => by`.

Take `⟨c, hc⟩` from `hcov M.isLB x`. Rewrite using `[hl' _ c, he u c (gen_mem hc)]`. Conclude with `(regAt_fnOf hc _ _).mul (hu x c i j hc hi hj).inv.regAt`. Use `⟨e, fun u v huv => ?_, ?_, fun u σ y => ?_, fun u x i j hi hj => ?_⟩` and prove the remaining obligations. Use `ReciprocityTheory.ChartRestriction.G.DVR.SecOps.sec_ext fun c => Cartier.fn_ext fun hc => ?_` and prove the remaining obligations.

Rewrite using `[← he, ← he, huv]`. Use `Set.Subset.antisymm (Set.range_subset_iff.2 hmem) fun f hf => ?_` and prove the remaining obligations. Take `⟨u, hu'⟩` from `exists_sec hρ (f := f) fun c x hc => by`. Take `⟨i, hi⟩` from `hcov P.L.isLB x`. Take `⟨j, hj⟩` from `hcov P.A.isLB x`.

Rewrite using `[← hl f c i j]`. Conclude with `(hf x i j hi hj).mul (hu x c i j hc hi hj).regAt`. Take `⟨c, hc⟩` from `hcov M.isLB (genericPoint X)`. Conclude with `⟨u, mul_right_cancel₀ (ρ c).ne_zero ((he u c hc).trans (hu' c hc))⟩`. Establish `hi` using `mem_pick (P.L.φ σ).isLB y`.

Establish `hj` using `mem_pick (P.A.φ σ).isLB y`. Establish `hc` using `mem_pick (M.φ σ).isLB y`. Establish `hU` using `hu _ _ _ _ (mem_ptsIn.1 hc) (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)`. Establish `h1` using `hn σ y _ _ _ hc hi hj`. Establish `h2` using `ratVal_mul (y := y) (hmem u _ _ _ (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)) hU.regAt`.

Rewrite `h2` using `[hl, he u _ (gen_mem (mem_ptsIn.1 hc)), ratVal_fnOf hc]`. Establish `h3` using `norm_pos_iff.2 (ratVal_ne_zero hU)`. Rewrite using `[Pair.nu, Weight.nsq, secVal_apply, h2, ← h1, Real.exp_sub, Real.exp_log h3, norm_mul, Real.exp_neg]`. Establish `h4 : Real.exp ((M.φ σ).φ (pick (M.φ σ).isLB y) y) = Real.exp ((M.φ σ).φ (pick (M.φ σ).isLB y) y / 2) ^ 2`. Rewrite using `[← Real.exp_nat_mul]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h4]`. Clear the denominators using the available nonvanishing facts.

Take `⟨c, hc⟩` from `hcov M.isLB x`. Establish `hU` using `hu x c i j hc hi hj`. Rewrite using `[mem_nonzeroLocus_iff u c hc, ← unitAt_fnOf_iff hc (gen_mem hc), ← he]`. Conclude with `⟨fun h => hl' (e u) c i j ▸ h.mul hU.inv, fun h => hl (e u) c i j ▸ h.mul hU⟩`.
-/
theorem rep_dict : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (M : HermLB p), P.Rep a b M → ∃ e : M.B.Sec → X.functionField, Function.Injective e ∧ Set.range e = (P.H a b : Set X.functionField) ∧ (∀ u (σ : k →+* ℂ) (y : CxPts p σ), P.nu a b σ y (e u) ^ 2 = (M.φ σ).nsq (secVal p σ u) y) ∧ ∀ u (x : X) i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j → (x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u ↔ UnitAt x (P.loc a b (e u) i j)) := by
  intro k _ X _ p P a b M ⟨ρ, hρ, hu, hn⟩
  obtain ⟨e, he⟩ := exists_quot M.isLB hρ
  have hcov {B : LB X} (hB : B.IsLB) (x : X) : ∃ c, x ∈ B.U c :=
    Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top _))
  have hl (f : X.functionField) c i j :
      P.loc a b f i j * ((ρ c : X.functionField) / P.loc a b 1 i j) = f * ρ c := by
    have := (P.r i).ne_zero
    have := (P.r' j).ne_zero
    simp only [Pair.loc]
    field_simp
  have hl' (f : X.functionField) c i j :
      P.loc a b f i j = f * ρ c * ((ρ c : X.functionField) / P.loc a b 1 i j)⁻¹ := by
    have := (P.r i).ne_zero
    have := (P.r' j).ne_zero
    have := (ρ c).ne_zero
    simp only [Pair.loc]
    field_simp
  have hmem u : e u ∈ P.H a b := fun x i j hi hj => by
    obtain ⟨c, hc⟩ := hcov M.isLB x
    rw [hl' _ c, he u c (gen_mem hc)]
    exact (regAt_fnOf hc _ _).mul (hu x c i j hc hi hj).inv.regAt
  refine ⟨e, fun u v huv => ?_, ?_, fun u σ y => ?_, fun u x i j hi hj => ?_⟩
  · refine ReciprocityTheory.ChartRestriction.G.DVR.SecOps.sec_ext fun c => Cartier.fn_ext fun hc => ?_
    rw [← he, ← he, huv]
  · refine Set.Subset.antisymm (Set.range_subset_iff.2 hmem) fun f hf => ?_
    obtain ⟨u, hu'⟩ := exists_sec hρ (f := f) fun c x hc => by
      obtain ⟨i, hi⟩ := hcov P.L.isLB x
      obtain ⟨j, hj⟩ := hcov P.A.isLB x
      rw [← hl f c i j]
      exact (hf x i j hi hj).mul (hu x c i j hc hi hj).regAt
    obtain ⟨c, hc⟩ := hcov M.isLB (genericPoint X)
    exact ⟨u, mul_right_cancel₀ (ρ c).ne_zero ((he u c hc).trans (hu' c hc))⟩
  · have hi := mem_pick (P.L.φ σ).isLB y
    have hj := mem_pick (P.A.φ σ).isLB y
    have hc := mem_pick (M.φ σ).isLB y
    have hU := hu _ _ _ _ (mem_ptsIn.1 hc) (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
    have h1 := hn σ y _ _ _ hc hi hj
    have h2 := ratVal_mul (y := y) (hmem u _ _ _ (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)) hU.regAt
    rw [hl, he u _ (gen_mem (mem_ptsIn.1 hc)), ratVal_fnOf hc] at h2
    have h3 := norm_pos_iff.2 (ratVal_ne_zero hU)
    rw [Pair.nu, Weight.nsq, secVal_apply, h2, ← h1, Real.exp_sub, Real.exp_log h3, norm_mul, Real.exp_neg]
    have h4 : Real.exp ((M.φ σ).φ (pick (M.φ σ).isLB y) y) =
        Real.exp ((M.φ σ).φ (pick (M.φ σ).isLB y) y / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h4]
    field_simp
  · obtain ⟨c, hc⟩ := hcov M.isLB x
    have hU := hu x c i j hc hi hj
    rw [mem_nonzeroLocus_iff u c hc, ← unitAt_fnOf_iff hc (gen_mem hc), ← he]
    exact ⟨fun h => hl' (e u) c i j ▸ h.mul hU.inv, fun h => hl (e u) c i j ▸ h.mul hU⟩

end GlobalTheory.VolBr.RepDict

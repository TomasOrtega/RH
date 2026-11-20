import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrameEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

/- English proof (translation)
Establish `hpk : ((p : ℚ) ^ k) ≠ 0` using `pow_ne_zero _ (by exact_mod_cast hp)`. Use `set q : ℚ := ((p : ℚ) ^ k)⁻¹ with hq`. Set `f : V →ₗ[ℤ] V` to `(LinearMap.lsmul ℚ V q).toAddMonoidHom.toIntLinearMap`. Establish `hf : ∀ x, f x = q • x` using `fun x => rfl`. Use `set W : Submodule ℤ V := Submodule.span ℤ (f '' (s : Set V)) with hW`.

Establish `hWfg : W.FG` using `Submodule.fg_span ((s.finite_toSet).image f)`. Use `haveI : IsNoetherian ℤ W := isNoetherian_of_fg_of_noetherian W hWfg`. Establish `hNfg : (AddSubgroup.toIntSubmodule M ⊓ W).FG` using `Submodule.FG.of_le_of_isNoetherian inf_le_right`. Take `⟨t, ht⟩` from `hNfg`. Establish `hcl : ∀ y, y ∈ AddSubgroup.closure (t : Set V) ↔ y ∈ M ∧ y ∈ W`.

Introduce `y`. Rewrite using `[← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup, ht, Submodule.mem_inf]`. Both sides reduce to the same expression. Establish `hsW : ∀ y ∈ AddSubgroup.closure (s : Set V), q • y ∈ W`. Introduce `y hy`.

Rewrite `hy` using `[← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup]`. Establish `hy' : f y ∈ (Submodule.span ℤ (s : Set V)).map f` using `Submodule.mem_map_of_mem hy`. Rewrite `hy'` using `[Submodule.map_span]`. Rewrite using `[← hf]`. Conclude with `hy'`.

Use `⟨t, ?_, fun w => ⟨fun hw => ?_, fun ⟨m, hm, hmw⟩ => hsat m w hm ((hcl _).1 hmw).1⟩⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← hs, Submodule.span_le]`. Introduce `x hx`. Establish `hx1 : p ^ k • x ∈ M` using `h1 x hx`. Establish `e : p ^ k • x = q • ((p ^ k * p ^ k) • x)`.

Rewrite using `[← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]`. Use `congr 1`. Use `push_cast`. Rewrite using `[hq, ← _root_.mul_assoc, inv_mul_cancel₀ hpk, _root_.one_mul]`. Establish `hx2 : p ^ k • x ∈ W`.

Rewrite using `[e]`. Conclude with `hsW _ (AddSubgroup.nsmul_mem _ (AddSubgroup.subset_closure hx) _)`. Establish `hmem : p ^ k • x ∈ Submodule.span ℚ (t : Set V)` using `(AddSubgroup.closure_le (K := (Submodule.span ℚ (t : Set V)).toAddSubgroup)).2 Submodule.subset_span ((hcl _).2 ⟨hx1, hx2⟩)`. Establish `e2 : x = q • (p ^ k • x)`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℚ, smul_smul]`.

Use `push_cast`. Rewrite using `[hq, inv_mul_cancel₀ hpk, one_smul]`. Use `show x ∈ Submodule.span ℚ (t : Set V)`. Rewrite using `[e2]`. Conclude with `Submodule.smul_mem _ q hmem`.

Take `⟨m, hm, hmem⟩` from `h2 w hw`. Use `⟨m, hm, (hcl _).2 ⟨M.nsmul_mem hw m, ?_⟩⟩` and prove the remaining obligations. Establish `e : m • w = q • ((m * p ^ k) • w)`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]`. Use `congr 1`.

Use `push_cast`. Rewrite using `[hq, _root_.mul_comm (m : ℚ), ← _root_.mul_assoc, inv_mul_cancel₀ hpk, _root_.one_mul]`. Rewrite using `[e]`. Conclude with `hsW _ hmem`.
-/
private theorem plat_core {V : Type} [AddCommGroup V] [Module ℚ V] (p : ℕ) (hp : p ≠ 0) (M : AddSubgroup V)
    (s : Finset V) (k : ℕ) (hs : Submodule.span ℚ (s : Set V) = ⊤)
    (hsat : ∀ (m : ℕ) x, m.Coprime p → m • x ∈ M → x ∈ M)
    (h1 : ∀ x ∈ s, p ^ k • x ∈ M)
    (h2 : ∀ x ∈ M, ∃ m : ℕ, m.Coprime p ∧ (m * p ^ k) • x ∈ AddSubgroup.closure (s : Set V)) :
    ∃ t : Finset V, Submodule.span ℚ (t : Set V) = ⊤ ∧
      ∀ w, w ∈ M ↔ ∃ m : ℕ, m.Coprime p ∧ m • w ∈ AddSubgroup.closure (t : Set V) := by
  have hpk : ((p : ℚ) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp)
  set q : ℚ := ((p : ℚ) ^ k)⁻¹ with hq
  let f : V →ₗ[ℤ] V := (LinearMap.lsmul ℚ V q).toAddMonoidHom.toIntLinearMap
  have hf : ∀ x, f x = q • x := fun x => rfl
  set W : Submodule ℤ V := Submodule.span ℤ (f '' (s : Set V)) with hW
  have hWfg : W.FG := Submodule.fg_span ((s.finite_toSet).image f)
  haveI : IsNoetherian ℤ W := isNoetherian_of_fg_of_noetherian W hWfg
  have hNfg : (AddSubgroup.toIntSubmodule M ⊓ W).FG :=
    Submodule.FG.of_le_of_isNoetherian inf_le_right
  obtain ⟨t, ht⟩ := hNfg
  have hcl : ∀ y, y ∈ AddSubgroup.closure (t : Set V) ↔ y ∈ M ∧ y ∈ W := by
    intro y
    rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup, ht,
      Submodule.mem_inf]
    rfl
  have hsW : ∀ y ∈ AddSubgroup.closure (s : Set V), q • y ∈ W := by
    intro y hy
    rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup] at hy
    have hy' : f y ∈ (Submodule.span ℤ (s : Set V)).map f := Submodule.mem_map_of_mem hy
    rw [Submodule.map_span] at hy'
    rw [← hf]
    exact hy'
  refine ⟨t, ?_, fun w => ⟨fun hw => ?_, fun ⟨m, hm, hmw⟩ => hsat m w hm ((hcl _).1 hmw).1⟩⟩
  · rw [eq_top_iff, ← hs, Submodule.span_le]
    intro x hx
    have hx1 : p ^ k • x ∈ M := h1 x hx
    have e : p ^ k • x = q • ((p ^ k * p ^ k) • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
      congr 1
      push_cast
      rw [hq, ← _root_.mul_assoc, inv_mul_cancel₀ hpk, _root_.one_mul]
    have hx2 : p ^ k • x ∈ W := by
      rw [e]
      exact hsW _ (AddSubgroup.nsmul_mem _ (AddSubgroup.subset_closure hx) _)
    have hmem : p ^ k • x ∈ Submodule.span ℚ (t : Set V) :=
      (AddSubgroup.closure_le (K := (Submodule.span ℚ (t : Set V)).toAddSubgroup)).2
        Submodule.subset_span ((hcl _).2 ⟨hx1, hx2⟩)
    have e2 : x = q • (p ^ k • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
      push_cast
      rw [hq, inv_mul_cancel₀ hpk, one_smul]
    show x ∈ Submodule.span ℚ (t : Set V)
    rw [e2]
    exact Submodule.smul_mem _ q hmem
  · obtain ⟨m, hm, hmem⟩ := h2 w hw
    refine ⟨m, hm, (hcl _).2 ⟨M.nsmul_mem hw m, ?_⟩⟩
    have e : m • w = q • ((m * p ^ k) • w) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
      congr 1
      push_cast
      rw [hq, _root_.mul_comm (m : ℚ), ← _root_.mul_assoc, inv_mul_cancel₀ hpk, _root_.one_mul]
    rw [e]
    exact hsW _ hmem

/- English proof (translation)
Introduce `p _ D M s k hs hO hsat h1 h2`. Conclude with `⟨hO, plat_core p (Fact.out : p.Prime).ne_zero M s k hs hsat h1 h2⟩`.
-/
theorem UpperTheory.Gal.W2.pLatOf_of :
    UpperTheory.Gal.W2.PLatOf := by
  intro p _ D M s k hs hO hsat h1 h2
  exact ⟨hO, plat_core p (Fact.out : p.Prime).ne_zero M s k hs hsat h1 h2⟩

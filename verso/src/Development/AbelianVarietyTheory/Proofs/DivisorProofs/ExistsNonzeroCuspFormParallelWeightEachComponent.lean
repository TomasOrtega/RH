import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspOnRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroScalarWeightCuspFormComponentStatement
import Formalism.LocalToGlobal.ProjectiveLattices.CuspMulOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds

set_option autoImplicit false

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.FlatCore.NonzeroCusp

/- English proof (translation)
Use function extensionality and compare the values at `τ j`. Establish `e : (n + 2 * m) / 2 = n / 2 + m` using `by omega`. Simplify using `only [laU, Pi.zero_apply, e]`. Apply the tactic sequence `split_ifs <;> push_cast <;> ring`.
-/
theorem laU_const {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (V : Unf Xo c σ r) (m n : ℕ) (k : V.Comp) :
    laU V (fun _ => m) n k = laU V 0 (n + 2 * m) k := by
  funext τ j
  have e : (n + 2 * m) / 2 = n / 2 + m := by omega
  simp only [laU, Pi.zero_apply, e]
  split_ifs <;> push_cast <;> ring

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c r U x hL Z`. Establish `hσ : GoodEmb c c.F.val.toRingHom` using `rfl`. Take `⟨n₀, hn₀, hev, f₀, hf₀, ⟨k, y⟩, hz, hne⟩` from `GlobalTheory.T.exists_nonzero_scalarWeight_cuspForm_component E H Dw l Xo c r U x hL _ hσ Z`. Take `⟨hy, hlies⟩` from `hz`. Establish `hM : CuspMul Xo c U` using `cusp_mul_of_M5 siegelSpaceAlgebra_holds U`.

Establish `hD0 : ∀ m, Even m → Dom (0 : (E →+* ℂ) × ℕ → ℕ) m` using `fun m hm => ⟨fun _ => antitone_const, hm⟩`. Establish `hpow : ∀ j : ℕ, f₀ ^ (j + 1) ∈ cusp Xo c U 0 ((j + 1) * n₀)`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simpa using hf₀`.

Consider the case `succ j ih`. Establish `h` using `hM 0 0 ((j + 1) * n₀) n₀ (f₀ ^ (j + 1)) f₀ (hD0 _ (hev.mul_left _)) (hD0 _ hev) ih hf₀`. Establish `e1 : ((j + 1) * n₀ + n₀) = (j + 1 + 1) * n₀` using `by ring`. Rewrite `h` using `[add_zero, e1]`. Rewrite using `[pow_succ]`.

Conclude with `h`. Establish `hrd : ∀ j : ℕ, rdU (U c.F.val.toRingHom) (f₀ ^ (j + 1)) k y = (rdU (U c.F.val.toRingHom) f₀ k y) ^ (j + 1)`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp`.

Consider the case `succ j ih`. Rewrite using `[pow_succ, Formalism.L2.Pj.rdU_mul, Pi.mul_apply, Pi.mul_apply, ih]`. Expand and normalize the polynomial expressions, which then agree. Use `set M : ℕ := 4 * (finrank ℚ E * r) + 7 with hMdef`. Take `⟨t, ht⟩` from `hev`.

Establish `hMt : (M + 1) * n₀ = (M + 1) * t + (M + 1) * t` using `by rw [ht]; ring`. Establish `ht1 : 1 ≤ t` using `by omega`. Establish `hMt1 : M + 1 ≤ (M + 1) * t` using `Nat.le_mul_of_pos_right _ ht1`. Use `set n : ℕ := (M + 1) * n₀ - 4 with hndef`. Establish `hnev : Even n` using `⟨(M + 1) * t - 2, by omega⟩`.

Establish `hnb : 4 * (finrank ℚ E * r) + 4 ≤ n` using `by omega`. Establish `hn4 : n + 2 * 2 = (M + 1) * n₀` using `by omega`. Establish `hP : rdU (U c.F.val.toRingHom) (f₀ ^ (M + 1)) ∈ holSub0 (U c.F.val.toRingHom).X (laU (U c.F.val.toRingHom) (fun _ => 2) n)`. Establish `e : laU (U c.F.val.toRingHom) (fun _ => 2) n = laU (U c.F.val.toRingHom) 0 ((M + 1) * n₀)`. Use function extensionality and compare the values at `fun k' => by rw [laU_const, hn4]`.

Rewrite using `[e]`. Conclude with `⟨((mem_cusp Xo c U 0 _ _).1 (hpow M)).2 _ hσ, rdU_mem_offZero _ _⟩`. Establish `hspan` using `hL.onto _ hσ (fun _ => 2) n ⟨fun _ => antitone_const, hnev⟩ (fun _ _ _ => by norm_num) hnb hP`. Choose the witnesses or unpack the hypotheses as in `⟨f, hf, hfy⟩ : ∃ f ∈ cusp Xo c U (fun _ => 2) n, rdU (U c.F.val.toRingHom) f k y ≠ 0 := by`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Set `ev : FDSec (U c.F.val.toRingHom).X →ₗ[ℂ] ℂ` to `{ toFun := fun P => P k y, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Establish `hle : Submodule.span ℂ (rdU (U c.F.val.toRingHom) '' (cusp Xo c U (fun _ => 2) n : Set (Rul Xo c))) ≤ LinearMap.ker ev`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨f, hf, rfl⟩`.

Conclude with `hcon f hf`. Establish `h0 : ev (rdU (U c.F.val.toRingHom) (f₀ ^ (M + 1))) = 0` using `hle hspan`. Establish `h1 : ev (rdU (U c.F.val.toRingHom) (f₀ ^ (M + 1))) = (rdU (U c.F.val.toRingHom) f₀ k y) ^ (M + 1)` using `hrd M`. Conclude with `pow_ne_zero _ hne (h1.symm.trans h0)`. Take `⟨g, hg, -⟩` from `GlobalTheory.CompRestr.exists_cuspOn_restrict E H Dw l Xo c r U hL.unf Z (wtZ (fun _ => 2) n) ⟨f, by rw [cuspW_wtZ]; exact hf⟩`.

Use `⟨fun _ => 2, n, ⟨fun _ => antitone_const, hnev⟩, fun _ _ _ => le_rfl, hnb, g, g.2, ?_⟩` and prove the remaining obligations. Introduce `h0`. Establish `e : rdU (U c.F.val.toRingHom) (g : Rul Xo c) k y = rdU (U c.F.val.toRingHom) f k y`. Simplify using `only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hy]`. Rewrite using `[hg _ _ hlies]`.

Rewrite `e` using `[h0, map_zero]`. Conclude with `hfy e.symm`.
-/
theorem exists_cuspOn_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c), ∃ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n ∧ (∀ τ i, i < Dw.mult τ → 2 ≤ a (τ, i)) ∧ 4 * (finrank ℚ E * r) + 4 ≤ n ∧ ∃ f ∈ cuspOn U Z (wtZ a n), f ≠ 0 := by
  intro E _ _ _ H Dw l Xo c r U x hL Z
  have hσ : GoodEmb c c.F.val.toRingHom := rfl
  obtain ⟨n₀, hn₀, hev, f₀, hf₀, ⟨k, y⟩, hz, hne⟩ := GlobalTheory.T.exists_nonzero_scalarWeight_cuspForm_component E H Dw l Xo c r U x hL _ hσ Z
  obtain ⟨hy, hlies⟩ := hz
  have hM : CuspMul Xo c U := cusp_mul_of_M5 siegelSpaceAlgebra_holds U
  have hD0 : ∀ m, Even m → Dom (0 : (E →+* ℂ) × ℕ → ℕ) m := fun m hm => ⟨fun _ => antitone_const, hm⟩
  have hpow : ∀ j : ℕ, f₀ ^ (j + 1) ∈ cusp Xo c U 0 ((j + 1) * n₀) := by
    intro j
    induction j with
    | zero => simpa using hf₀
    | succ j ih =>
      have h := hM 0 0 ((j + 1) * n₀) n₀ (f₀ ^ (j + 1)) f₀ (hD0 _ (hev.mul_left _)) (hD0 _ hev) ih hf₀
      have e1 : ((j + 1) * n₀ + n₀) = (j + 1 + 1) * n₀ := by ring
      rw [add_zero, e1] at h
      rw [pow_succ]
      exact h
  have hrd : ∀ j : ℕ, rdU (U c.F.val.toRingHom) (f₀ ^ (j + 1)) k y = (rdU (U c.F.val.toRingHom) f₀ k y) ^ (j + 1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, Formalism.L2.Pj.rdU_mul, Pi.mul_apply, Pi.mul_apply, ih]
      ring
  set M : ℕ := 4 * (finrank ℚ E * r) + 7 with hMdef
  obtain ⟨t, ht⟩ := hev
  have hMt : (M + 1) * n₀ = (M + 1) * t + (M + 1) * t := by rw [ht]; ring
  have ht1 : 1 ≤ t := by omega
  have hMt1 : M + 1 ≤ (M + 1) * t := Nat.le_mul_of_pos_right _ ht1
  set n : ℕ := (M + 1) * n₀ - 4 with hndef
  have hnev : Even n := ⟨(M + 1) * t - 2, by omega⟩
  have hnb : 4 * (finrank ℚ E * r) + 4 ≤ n := by omega
  have hn4 : n + 2 * 2 = (M + 1) * n₀ := by omega
  have hP : rdU (U c.F.val.toRingHom) (f₀ ^ (M + 1)) ∈
      holSub0 (U c.F.val.toRingHom).X (laU (U c.F.val.toRingHom) (fun _ => 2) n) := by
    have e : laU (U c.F.val.toRingHom) (fun _ => 2) n = laU (U c.F.val.toRingHom) 0 ((M + 1) * n₀) :=
      funext fun k' => by rw [laU_const, hn4]
    rw [e]
    exact ⟨((mem_cusp Xo c U 0 _ _).1 (hpow M)).2 _ hσ, rdU_mem_offZero _ _⟩
  have hspan := hL.onto _ hσ (fun _ => 2) n ⟨fun _ => antitone_const, hnev⟩ (fun _ _ _ => by norm_num) hnb hP
  obtain ⟨f, hf, hfy⟩ : ∃ f ∈ cusp Xo c U (fun _ => 2) n, rdU (U c.F.val.toRingHom) f k y ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    let ev : FDSec (U c.F.val.toRingHom).X →ₗ[ℂ] ℂ :=
      { toFun := fun P => P k y, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hle : Submodule.span ℂ (rdU (U c.F.val.toRingHom) '' (cusp Xo c U (fun _ => 2) n : Set (Rul Xo c))) ≤
        LinearMap.ker ev := by
      rw [Submodule.span_le]
      rintro _ ⟨f, hf, rfl⟩
      exact hcon f hf
    have h0 : ev (rdU (U c.F.val.toRingHom) (f₀ ^ (M + 1))) = 0 := hle hspan
    have h1 : ev (rdU (U c.F.val.toRingHom) (f₀ ^ (M + 1))) = (rdU (U c.F.val.toRingHom) f₀ k y) ^ (M + 1) := hrd M
    exact pow_ne_zero _ hne (h1.symm.trans h0)
  obtain ⟨g, hg, -⟩ := GlobalTheory.CompRestr.exists_cuspOn_restrict E H Dw l Xo c r U hL.unf Z (wtZ (fun _ => 2) n)
    ⟨f, by rw [cuspW_wtZ]; exact hf⟩
  refine ⟨fun _ => 2, n, ⟨fun _ => antitone_const, hnev⟩, fun _ _ _ => le_rfl, hnb, g, g.2, ?_⟩
  intro h0
  have e : rdU (U c.F.val.toRingHom) (g : Rul Xo c) k y = rdU (U c.F.val.toRingHom) f k y := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hy]
    rw [hg _ _ hlies]
  rw [h0, map_zero] at e
  exact hfy e.symm

end GlobalTheory.FlatCore.NonzeroCusp

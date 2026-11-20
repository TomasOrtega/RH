import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section
namespace GlobalTheory.CompAtUniq

open Topology
open scoped WithZero

/- English proof (translation)
Rewrite using `[Valued.mem_nhds]`. Establish `h' : (Valued.v : Valuation K ℤᵐ⁰).restrict r ≠ 0` using `by simp [hr]`. Conclude with `⟨Units.mk0 _ h', fun y hy => (Valuation.restrict_lt_iff _).1 hy⟩`.
-/
theorem ball_mem_nhds' {K : Type} [Field K] [Valued K ℤᵐ⁰] (x r : K) (hr : r ≠ 0) :
    {y | Valued.v (y - x) < Valued.v r} ∈ 𝓝 x := by
  rw [Valued.mem_nhds]
  have h' : (Valued.v : Valuation K ℤᵐ⁰).restrict r ≠ 0 := by simp [hr]
  exact ⟨Units.mk0 _ h', fun y hy => (Valuation.restrict_lt_iff _).1 hy⟩

/- English proof (translation)
Establish `hvu : Valued.v u ≠ 0` using `by simpa using hu`. Establish `hlt : Valued.v (y - u) < Valued.v u` using `lt_of_lt_of_le h (mul_le_of_le_one_right' hc)`. Establish `hvy : Valued.v y = Valued.v u` using `Valuation.map_eq_of_sub_lt _ hlt`. Establish `hy : y ≠ 0`. Introduce `h0`.

Rewrite `hvy` using `[h0, map_zero]`. Conclude with `hvu hvy.symm`. Use `⟨hy, ?_⟩` and prove the remaining obligations. Establish `: u * y⁻¹ - 1 = -((y - u) * y⁻¹)` using `by field_simp; ring`. Rewrite using `[this, Valuation.map_neg, map_mul, map_inv₀, hvy]`.

Establish `hpos : (0 : ℤᵐ⁰) < Valued.v u` using `pos_iff_ne_zero.2 hvu`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem val_div_sub_one_lt {K : Type} [Field K] [Valued K ℤᵐ⁰] {u y : K} {c : ℤᵐ⁰} (hu : u ≠ 0)
    (hc : c ≤ 1) (h : Valued.v (y - u) < Valued.v u * c) : y ≠ 0 ∧ Valued.v (u * y⁻¹ - 1) < c := by
  have hvu : Valued.v u ≠ 0 := by simpa using hu
  have hlt : Valued.v (y - u) < Valued.v u := lt_of_lt_of_le h (mul_le_of_le_one_right' hc)
  have hvy : Valued.v y = Valued.v u := Valuation.map_eq_of_sub_lt _ hlt
  have hy : y ≠ 0 := by
    intro h0; rw [h0, map_zero] at hvy; exact hvu hvy.symm
  refine ⟨hy, ?_⟩
  have : u * y⁻¹ - 1 = -((y - u) * y⁻¹) := by field_simp; ring
  rw [this, Valuation.map_neg, map_mul, map_inv₀, hvy]
  have hpos : (0 : ℤᵐ⁰) < Valued.v u := pos_iff_ne_zero.2 hvu
  calc Valued.v (y - u) * (Valued.v u)⁻¹ < Valued.v u * c * (Valued.v u)⁻¹ :=
        mul_lt_mul_of_pos_right h (inv_pos.2 hpos)
    _ = c := by field_simp

/- English proof (translation)
Introduce `L _ _ _ χ s ξ ξ' hξ hξ'`. Take `⟨⟨N₁, hN₁⟩, hk⟩` from `hξ`. Take `⟨⟨N₂, hN₂⟩, hk'⟩` from `hξ'`. Use `ext1 u`. Take `⟨π, hπ⟩` from `s.v.valuation_exists_uniformizer (maximalRealSubfield L)`.

Establish `hπ' : Valued.v ((π : s.v.adicCompletion (maximalRealSubfield L))) = WithZero.exp (-1 : ℤ)`. Rewrite using `[HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]`. Use `set N := max N₁ N₂ with hN`. Establish `hN1 : N₁ ≤ N` using `le_max_left _ _`. Establish `hN2 : N₂ ≤ N` using `le_max_right _ _`.

Establish `hu0 : (u : s.v.adicCompletion (maximalRealSubfield L)) ≠ 0` using `u.ne_zero`. Establish `hπ0 : (π : s.v.adicCompletion (maximalRealSubfield L)) ≠ 0`. Introduce `h`. Rewrite `hπ'` using `[h, map_zero]`. Conclude with `(WithZero.exp_ne_zero) hπ'.symm`.

Establish `hvr : Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) * (π : s.v.adicCompletion (maximalRealSubfield L)) ^ N) = Valued.v (u : s.v.adicCompletion (maximalRealSubfield L)) * WithZero.exp (-(N : ℤ))`. Rewrite using `[map_mul, map_pow, hπ', ← WithZero.exp_nsmul]`. Use `congr 2`. Simplify using the standard rewrite rules. Establish `hnhds` using `ball_mem_nhds' (u : s.v.adicCompletion (maximalRealSubfield L)) _ (mul_ne_zero hu0 (pow_ne_zero N hπ0))`.

Take `⟨x, hx⟩` from `(HeightOneSpectrum.denseRange_algebraMap (K := maximalRealSubfield L) s.v).mem_nhds hnhds`. Rewrite `hx` using `[Set.mem_setOf_eq, hvr]`. Establish `hle : WithZero.exp (-(N : ℤ)) ≤ 1`. Rewrite using `[← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.

Take `⟨hy0, hw⟩` from `val_div_sub_one_lt hu0 hle hx`. Establish `hx0 : x ≠ 0` using `by rintro rfl; exact hy0 (map_zero _)`. Use `set k : Lˣ := Units.mk0 (algebraMap (maximalRealSubfield L) L x) ((map_ne_zero _).2 hx0) with hkdef`. Establish `hik : ((Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k : _) : s.v.adicCompletion (maximalRealSubfield L)) = algebraMap (maximalRealSubfield L) (s.v.adicCompletion (maximalRealSubfield L)) x`. Simplify using `[k]`.

Use `set w : (s.v.adicCompletion (maximalRealSubfield L))ˣ := u * (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k)⁻¹ with hwdef`. Establish `hu : u = Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k * w` using `by simp [w]`. Establish `hw' : Valued.v ((w : s.v.adicCompletion (maximalRealSubfield L)) - 1) < WithZero.exp (-(N : ℤ))`. Establish `: (w : s.v.adicCompletion (maximalRealSubfield L)) = (u : s.v.adicCompletion (maximalRealSubfield L)) * (algebraMap (maximalRealSubfield L) (s.v.adicCompletion (maximalRealSubfield L)) x)⁻¹`. Rewrite using `[hwdef, Units.val_mul, Units.val_inv_eq_inv_val, hik]`.

Rewrite using `[this]`. Conclude with `hw`. Establish `e1 : ξ w = 1` using `hN₁ w (hw'.le.trans (WithZero.exp_le_exp.2 (by omega)))`. Establish `e2 : ξ' w = 1` using `hN₂ w (hw'.le.trans (WithZero.exp_le_exp.2 (by omega)))`. Use `clear_value w`.

Rewrite using `[hu, map_mul, map_mul, e1, e2, hk, hk']`.
-/
theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (χ : HChar L) (s : SplitPlace L) (ξ ξ' : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.IsCompAt χ s ξ → NG.IsCompAt χ s ξ' → ξ = ξ' := by
  intro L _ _ _ χ s ξ ξ' hξ hξ'
  obtain ⟨⟨N₁, hN₁⟩, hk⟩ := hξ
  obtain ⟨⟨N₂, hN₂⟩, hk'⟩ := hξ'
  ext1 u
  obtain ⟨π, hπ⟩ := s.v.valuation_exists_uniformizer (maximalRealSubfield L)
  have hπ' : Valued.v ((π : s.v.adicCompletion (maximalRealSubfield L))) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  set N := max N₁ N₂ with hN
  have hN1 : N₁ ≤ N := le_max_left _ _
  have hN2 : N₂ ≤ N := le_max_right _ _
  have hu0 : (u : s.v.adicCompletion (maximalRealSubfield L)) ≠ 0 := u.ne_zero
  have hπ0 : (π : s.v.adicCompletion (maximalRealSubfield L)) ≠ 0 := by
    intro h; rw [h, map_zero] at hπ'; exact (WithZero.exp_ne_zero) hπ'.symm
  have hvr : Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) * (π : s.v.adicCompletion (maximalRealSubfield L)) ^ N)
      = Valued.v (u : s.v.adicCompletion (maximalRealSubfield L)) * WithZero.exp (-(N : ℤ)) := by
    rw [map_mul, map_pow, hπ', ← WithZero.exp_nsmul]; congr 2; simp
  have hnhds := ball_mem_nhds' (u : s.v.adicCompletion (maximalRealSubfield L)) _ (mul_ne_zero hu0 (pow_ne_zero N hπ0))
  obtain ⟨x, hx⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := maximalRealSubfield L) s.v).mem_nhds hnhds
  rw [Set.mem_setOf_eq, hvr] at hx
  have hle : WithZero.exp (-(N : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  obtain ⟨hy0, hw⟩ := val_div_sub_one_lt hu0 hle hx
  have hx0 : x ≠ 0 := by rintro rfl; exact hy0 (map_zero _)
  set k : Lˣ := Units.mk0 (algebraMap (maximalRealSubfield L) L x) ((map_ne_zero _).2 hx0) with hkdef
  have hik : ((Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k : _) : s.v.adicCompletion (maximalRealSubfield L))
      = algebraMap (maximalRealSubfield L) (s.v.adicCompletion (maximalRealSubfield L)) x := by
    simp [k]
  set w : (s.v.adicCompletion (maximalRealSubfield L))ˣ := u * (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k)⁻¹ with hwdef
  have hu : u = Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k * w := by simp [w]
  have hw' : Valued.v ((w : s.v.adicCompletion (maximalRealSubfield L)) - 1) < WithZero.exp (-(N : ℤ)) := by
    have : (w : s.v.adicCompletion (maximalRealSubfield L)) = (u : s.v.adicCompletion (maximalRealSubfield L)) *
        (algebraMap (maximalRealSubfield L) (s.v.adicCompletion (maximalRealSubfield L)) x)⁻¹ := by
      rw [hwdef, Units.val_mul, Units.val_inv_eq_inv_val, hik]
    rw [this]; exact hw
  have e1 : ξ w = 1 := hN₁ w (hw'.le.trans (WithZero.exp_le_exp.2 (by omega)))
  have e2 : ξ' w = 1 := hN₂ w (hw'.le.trans (WithZero.exp_le_exp.2 (by omega)))
  clear_value w
  rw [hu, map_mul, map_mul, e1, e2, hk, hk']

end GlobalTheory.CompAtUniq

end

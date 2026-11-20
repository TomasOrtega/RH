import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort

noncomputable section

namespace GlobalTheory.CoeffRingTest

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

section Ring

variable {O L : Type} [CommRing O] [Field L] (ι : O →+* L) (σ : L →+* ℂ)

def gen : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (Set.range (σ.comp ι))

def Full : Prop := Function.Injective ι ∧ ∀ z ∈ gen ι σ, IsIntegral ℤ z → z ∈ Set.range (σ.comp ι)

/- English proof (translation)
The claim follows from `Complex.isPrimitiveRoot_exp n hn`.
-/
theorem zeta_prim {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (zeta n) n := Complex.isPrimitiveRoot_exp n hn

end Ring

/- English proof (translation)
Take `⟨k, rfl⟩` from `hmn`. Establish `hm : m ≠ 0` using `left_ne_zero_of_mul hn`. Establish `hk : k ≠ 0` using `right_ne_zero_of_mul hn`. Establish `: zeta m = zeta (m * k) ^ k`. Rewrite using `[zeta, zeta, ← Complex.exp_nat_mul]`.

Use `congr 1`. Establish `: (k : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hk`. Establish `: (m : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hm`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this]`. Conclude with `pow_mem h k`.
-/
theorem zeta_mem_of_dvd {F : IntermediateField ℚ ℂ} {m n : ℕ} (hn : n ≠ 0) (hmn : m ∣ n) (h : zeta n ∈ F) :
    zeta m ∈ F := by
  obtain ⟨k, rfl⟩ := hmn
  have hm : m ≠ 0 := left_ne_zero_of_mul hn
  have hk : k ≠ 0 := right_ne_zero_of_mul hn
  have : zeta m = zeta (m * k) ^ k := by
    rw [zeta, zeta, ← Complex.exp_nat_mul]
    congr 1
    have : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk
    have : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm
    push_cast
    field_simp
  rw [this]
  exact pow_mem h k

/- English proof (translation)
Establish `hM : d.l₂.M' ≠ 0` using `Nat.lcm_ne_zero (by have := d.l₂.three_le; omega) d.l₂.A_pos.ne'`. Establish `hd : d.pd ∣ d.l₂.M'` using `(h.2.1 ▸ dvd_mul_left d.pd l.M).trans (Nat.dvd_lcm_left _ _)`. Conclude with `d.hF ▸ zeta_mem_of_dvd hM hd d.c₂.zeta_mem`.
-/
theorem zeta_pd_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) (h : d.IsLev) : zeta d.pd ∈ c.F := by
  have hM : d.l₂.M' ≠ 0 := Nat.lcm_ne_zero (by have := d.l₂.three_le; omega) d.l₂.A_pos.ne'
  have hd : d.pd ∣ d.l₂.M' := (h.2.1 ▸ dvd_mul_left d.pd l.M).trans (Nat.dvd_lcm_left _ _)
  exact d.hF ▸ zeta_mem_of_dvd hM hd d.c₂.zeta_mem

end GlobalTheory.CoeffRingTest

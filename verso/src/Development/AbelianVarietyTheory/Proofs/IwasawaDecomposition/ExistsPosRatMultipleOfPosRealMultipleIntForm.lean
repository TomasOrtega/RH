import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory

/- English proof (translation)
Establish `hpt : ∀ u v, (x u v : ℝ) = d * (y u v : ℝ)`. Introduce `u v`. Use `congrArg (fun f => f u v) h` as an intermediate fact. Simplify `this` using `[toReal]`. Choose the witnesses or unpack the hypotheses as in `⟨u, v, huv⟩ : ∃ u v, y u v ≠ 0 := by`.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hy (LinearMap.ext₂ hc)`. Use `set r : ℚ := (x u v : ℚ) / (y u v : ℚ) with hr_def`. Establish `hy' : (y u v : ℝ) ≠ 0` using `by exact_mod_cast huv`.

Establish `hdr : d = (r : ℝ)`. Rewrite using `[hr_def]`. Use `push_cast`. Rewrite using `[hpt u v]`. Clear the denominators using the available nonvanishing facts.

Establish `hr : 0 < r` using `by exact_mod_cast (hdr ▸ hd)`. Establish `hnum : 0 < r.num` using `Rat.num_pos.mpr hr`. Establish `hcast : ((r.num.toNat : ℕ) : ℤ) = r.num` using `Int.toNat_of_nonneg hnum.le`. Use `⟨r.den, r.num.toNat, r.den_pos, by omega, ?_⟩` and prove the remaining obligations. Apply `LinearMap.ext₂` to reduce the goal to its premises.

Introduce `p q`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul]`. Rewrite using `[hcast]`. Apply `Int.cast_injective (α := ℝ)` to reduce the goal to its premises. Use `push_cast`.

Rewrite using `[hpt p q, hdr]`. Establish `hrr : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ)`. Rewrite using `[← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]`. Establish `hden : (r.den : ℝ) ≠ 0` using `by exact_mod_cast r.den_ne_zero`. Rewrite using `[hrr]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem posReal_multiple_rat {X : Type} [AddCommGroup X] (x y : LinearMap.BilinForm ℤ X) (d : ℝ)
    (hd : 0 < d) (hy : y ≠ 0) (h : toReal x = d • toReal y) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ (a : ℤ) • x = (b : ℤ) • y := by
  have hpt : ∀ u v, (x u v : ℝ) = d * (y u v : ℝ) := by
    intro u v
    have := congrArg (fun f => f u v) h
    simpa [toReal] using this
  obtain ⟨u, v, huv⟩ : ∃ u v, y u v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hy (LinearMap.ext₂ hc)
  set r : ℚ := (x u v : ℚ) / (y u v : ℚ) with hr_def
  have hy' : (y u v : ℝ) ≠ 0 := by exact_mod_cast huv
  have hdr : d = (r : ℝ) := by
    rw [hr_def]; push_cast; rw [hpt u v]; field_simp
  have hr : 0 < r := by exact_mod_cast (hdr ▸ hd)
  have hnum : 0 < r.num := Rat.num_pos.mpr hr
  have hcast : ((r.num.toNat : ℕ) : ℤ) = r.num := Int.toNat_of_nonneg hnum.le
  refine ⟨r.den, r.num.toNat, r.den_pos, by omega, ?_⟩
  apply LinearMap.ext₂
  intro p q
  simp only [LinearMap.smul_apply, smul_eq_mul]
  rw [hcast]
  apply Int.cast_injective (α := ℝ)
  push_cast
  rw [hpt p q, hdr]
  have hrr : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  rw [hrr]; field_simp

end GlobalTheory

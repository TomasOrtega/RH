import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqZeroOfGe

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.SeriesFrobRoot

/- English proof (translation)
Establish `hp : p ≠ 0` using `(Fact.out : p.Prime).ne_zero`. Rewrite using `[← MvPowerSeries.map_frobenius_expand p hp]`. Use extensionality with `μ`. Rewrite using `[MvPowerSeries.coeff_map]`. Distinguish the cases in `h : ∀ i, p ∣ μ i`.

Take `⟨m, hm⟩ : ∃ m, p • m = μ` from `⟨μ.mapRange (fun a ↦ a / p) (by simp), by ext i; simp [(Nat.mul_div_cancel' (h i))]⟩`. Rewrite using `[← hm, MvPowerSeries.coeff_expand_smul, frobenius_def, hc]`. Use `push Not at h`. Take `⟨i, hi⟩` from `h`. Rewrite using `[MvPowerSeries.coeff_expand_of_not_dvd p hp _ hi, map_zero]`.

Establish `h0 : μ i ≠ 0` using `fun h => hi (h ▸ dvd_zero p)`. Establish `hle : Finsupp.single i 1 ≤ μ`. Rewrite using `[Finsupp.single_le_iff]`. Use linear arithmetic over natural numbers and integers. Establish `h1` using `congrArg (MvPowerSeries.coeff (μ - Finsupp.single i 1)) (hb i)`.

Rewrite `h1` using `[MvPowerSeries.coeff_pderiv, tsub_add_cancel_of_le hle, map_zero]`. Use `(mul_eq_zero.1 h1).resolve_right fun h2 => hi ?_` and prove the remaining obligations. Rewrite using `[← CharP.cast_eq_zero_iff k p]`. Establish `h3 : μ i = ((μ - Finsupp.single i 1 : σ →₀ ℕ) i) + 1`. Simplify using `only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[h3]`. Use `push_cast`. Conclude with `h2`.
-/
theorem eq_pow_of_pderiv {k σ : Type} [CommRing k] [IsDomain k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (b c : MvPowerSeries σ k) (hb : ∀ i, MvPowerSeries.pderiv k i b = 0)
    (hc : ∀ ν, MvPowerSeries.coeff ν c ^ p = MvPowerSeries.coeff (p • ν) b) : b = c ^ p := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [← MvPowerSeries.map_frobenius_expand p hp]
  ext μ
  rw [MvPowerSeries.coeff_map]
  by_cases h : ∀ i, p ∣ μ i
  · obtain ⟨m, hm⟩ : ∃ m, p • m = μ := ⟨μ.mapRange (fun a ↦ a / p) (by simp),
      by ext i; simp [(Nat.mul_div_cancel' (h i))]⟩
    rw [← hm, MvPowerSeries.coeff_expand_smul, frobenius_def, hc]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    rw [MvPowerSeries.coeff_expand_of_not_dvd p hp _ hi, map_zero]
    have h0 : μ i ≠ 0 := fun h => hi (h ▸ dvd_zero p)
    have hle : Finsupp.single i 1 ≤ μ := by
      rw [Finsupp.single_le_iff]; omega
    have h1 := congrArg (MvPowerSeries.coeff (μ - Finsupp.single i 1)) (hb i)
    rw [MvPowerSeries.coeff_pderiv, tsub_add_cancel_of_le hle, map_zero] at h1
    refine (mul_eq_zero.1 h1).resolve_right fun h2 => hi ?_
    rw [← CharP.cast_eq_zero_iff k p]
    have h3 : μ i = ((μ - Finsupp.single i 1 : σ →₀ ℕ) i) + 1 := by
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]; omega
    rw [h3]; push_cast; exact h2

variable {C : Type} [Field C] {V : VF C} {σ : Type}

open TeichPair

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun μ => ⟨MvPowerSeries.coeff μ f, hf μ⟩, by ext μ; rfl⟩`.
-/
theorem exists_lift {f : MvPowerSeries σ C} (hf : IntS V f) :
    ∃ F : MvPowerSeries σ (intRing V), MvPowerSeries.map (intRing V).subtype F = f :=
  ⟨fun μ => ⟨MvPowerSeries.coeff μ f, hf μ⟩, by ext μ; rfl⟩

/- English proof (translation)
Rewrite using `[MvPowerSeries.ext_iff]`. Use `forall_congr' fun μ => ?_` and prove the remaining obligations. Rewrite using `[MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem]`. Both sides reduce to the same expression.
-/
theorem mm_iff (F : MvPowerSeries σ (intRing V)) :
    (∀ μ, V.MM (MvPowerSeries.coeff μ (MvPowerSeries.map (intRing V).subtype F))) ↔
      MvPowerSeries.map (Ideal.Quotient.mk (maxId V)) F = 0 := by
  rw [MvPowerSeries.ext_iff]
  refine forall_congr' fun μ => ?_
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem]
  rfl

/- English proof (translation)
Use `(CharP.charP_iff_prime_eq_zero V.l_prime).2 ?_` and prove the remaining obligations. Rewrite using `[← map_natCast (Ideal.Quotient.mk (maxId V)), Ideal.Quotient.eq_zero_iff_mem]`. Use `show 0 < V.v (((V.l : ℕ) : intRing V) : C)`. Rewrite using `[show (((V.l : ℕ) : intRing V) : C) = (V.l : C) by simp, V.v_l]`. Conclude with `zero_lt_one`.
-/
theorem charP_res (V : VF C) : CharP (intRing V ⧸ maxId V) V.l := by
  refine (CharP.charP_iff_prime_eq_zero V.l_prime).2 ?_
  rw [← map_natCast (Ideal.Quotient.mk (maxId V)), Ideal.Quotient.eq_zero_iff_mem]
  show 0 < V.v (((V.l : ℕ) : intRing V) : C)
  rw [show (((V.l : ℕ) : intRing V) : C) = (V.l : C) by simp, V.v_l]
  exact zero_lt_one

/- English proof (translation)
Use extensionality with `μ`. Simplify using `[MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_map]`.
-/
theorem pderiv_map' {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (i : σ) (F : MvPowerSeries σ R) :
    MvPowerSeries.pderiv S i (MvPowerSeries.map φ F) = MvPowerSeries.map φ (MvPowerSeries.pderiv R i F) := by
  ext μ
  simp [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_map]

/- English proof (translation)
Unfold `VF.Ge at h ⊢`. Rewrite `h` using `[V.v.map_pow]`. Assume the negation of the conclusion as `hx`. Rewrite `hx` using `[not_le]`. Proceed by induction on `hv : V.v x using WithTop.recTopCoe with`.

Consider the case `top => rw [hv] at hx`. Conclude with `not_top_lt hx`. Consider the case `coe t`. Rewrite `hx`, `h` using `[hv]`. Rewrite `h` using `[← WithTop.coe_nsmul, WithTop.coe_le_coe, nsmul_eq_mul]`.

Rewrite `hx` using `[WithTop.coe_lt_coe]`. Establish `: (0 : ℝ) < n` using `by exact_mod_cast Nat.pos_of_ne_zero hn`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem ge_of_pow {x : C} {n : ℕ} (hn : n ≠ 0) (h : V.Ge 0 (x ^ n)) : V.Ge 0 x := by
  unfold VF.Ge at h ⊢
  rw [V.v.map_pow] at h
  by_contra hx
  rw [not_le] at hx
  induction hv : V.v x using WithTop.recTopCoe with
  | top => rw [hv] at hx; exact not_top_lt hx
  | coe t =>
    rw [hv] at hx h
    rw [← WithTop.coe_nsmul, WithTop.coe_le_coe, nsmul_eq_mul] at h
    rw [WithTop.coe_lt_coe] at hx
    have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    nlinarith

/- English proof (translation)
Introduce `C _ _ V σ _`. Establish `: Fact V.l.Prime` using `⟨V.l_prime⟩`. Use `charP_res V` as an intermediate fact. Establish `: CharP (MvPowerSeries σ (intRing V ⧸ maxId V)) V.l` using `charP_of_injective_ringHom (MvPowerSeries.C_injective (σ := σ)) V.l`. Establish `: IsDomain (MvPowerSeries σ (intRing V ⧸ maxId V))` using `NoZeroDivisors.to_isDomain _`.

Use `⟨fun b hb hd => ?_, fun f g hf hg h => ?_, fun f g hf hg => ?_⟩` and prove the remaining obligations. Use `choose r hr using fun ν : σ →₀ ℕ => IsAlgClosed.exists_pow_nat_eq (MvPowerSeries.coeff (V.l • ν) b) V.l_prime.pos`. Establish `hri : ∀ ν, V.Ge 0 (r ν)` using `fun ν => ge_of_pow V.l_prime.ne_zero (by rw [hr]; exact hb _)`. Take `⟨B, rfl⟩` from `exists_lift hb`. Set `B' : MvPowerSeries σ (intRing V)` to `fun ν => ⟨r ν, hri ν⟩`.

Use `⟨MvPowerSeries.map (intRing V).subtype B', hri, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow, ← map_sub, mm_iff, map_sub, map_pow, sub_eq_zero]`. Use `eq_pow_of_pderiv V.l _ _ (fun i => ?_) fun ν => ?_` and prove the remaining obligations. Rewrite using `[pderiv_map', ← mm_iff, ← pderiv_map']`. Conclude with `hd i`.

Rewrite using `[MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, ← map_pow]`. Use `congr 1`. Conclude with `Subtype.ext (hr ν)`. Take `⟨F, rfl⟩` from `exists_lift hf`. Take `⟨G, rfl⟩` from `exists_lift hg`.

Rewrite `h` using `[← map_pow, ← map_pow, ← map_sub, mm_iff, map_sub, map_pow, map_pow, ← sub_pow_char]`. Rewrite using `[← map_sub, mm_iff, map_sub]`. Conclude with `(pow_eq_zero_iff V.l_prime.ne_zero).1 h`. Take `⟨F, rfl⟩` from `exists_lift hf`. Take `⟨G, rfl⟩` from `exists_lift hg`.

Rewrite using `[forall_and]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← map_add, ← map_pow, ← map_pow, ← map_pow, ← map_sub, ← map_sub, mm_iff]`. Simplify using `only [map_sub, map_pow, map_add, add_pow_char]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← map_sub, ← map_pow, ← map_pow, ← map_pow, ← map_sub, ← map_sub, mm_iff]`. Simplify using `only [map_sub, map_pow, sub_pow_char]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem main : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (σ : Type) [Fintype σ], (∀ b : MvPowerSeries σ C, IntS V b → (∀ i μ, V.MM (MvPowerSeries.coeff μ (MvPowerSeries.pderiv C i b))) → ∃ b' : MvPowerSeries σ C, IntS V b' ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ (b - b' ^ V.l))) ∧ (∀ f g : MvPowerSeries σ C, IntS V f → IntS V g → (∀ μ, V.MM (MvPowerSeries.coeff μ (f ^ V.l - g ^ V.l))) → ∀ μ, V.MM (MvPowerSeries.coeff μ (f - g))) ∧ ∀ f g : MvPowerSeries σ C, IntS V f → IntS V g → ∀ μ, V.MM (MvPowerSeries.coeff μ ((f + g) ^ V.l - f ^ V.l - g ^ V.l)) ∧ V.MM (MvPowerSeries.coeff μ ((f - g) ^ V.l - (f ^ V.l - g ^ V.l))) := by
  intro C _ _ V σ _
  have : Fact V.l.Prime := ⟨V.l_prime⟩
  have := charP_res V
  have : CharP (MvPowerSeries σ (intRing V ⧸ maxId V)) V.l :=
    charP_of_injective_ringHom (MvPowerSeries.C_injective (σ := σ)) V.l
  have : IsDomain (MvPowerSeries σ (intRing V ⧸ maxId V)) := NoZeroDivisors.to_isDomain _
  refine ⟨fun b hb hd => ?_, fun f g hf hg h => ?_, fun f g hf hg => ?_⟩
  · choose r hr using fun ν : σ →₀ ℕ =>
      IsAlgClosed.exists_pow_nat_eq (MvPowerSeries.coeff (V.l • ν) b) V.l_prime.pos
    have hri : ∀ ν, V.Ge 0 (r ν) := fun ν => ge_of_pow V.l_prime.ne_zero (by rw [hr]; exact hb _)
    obtain ⟨B, rfl⟩ := exists_lift hb
    let B' : MvPowerSeries σ (intRing V) := fun ν => ⟨r ν, hri ν⟩
    refine ⟨MvPowerSeries.map (intRing V).subtype B', hri, ?_⟩
    rw [← map_pow, ← map_sub, mm_iff, map_sub, map_pow, sub_eq_zero]
    refine eq_pow_of_pderiv V.l _ _ (fun i => ?_) fun ν => ?_
    · rw [pderiv_map', ← mm_iff, ← pderiv_map']
      exact hd i
    · rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, ← map_pow]
      congr 1
      exact Subtype.ext (hr ν)
  · obtain ⟨F, rfl⟩ := exists_lift hf
    obtain ⟨G, rfl⟩ := exists_lift hg
    rw [← map_pow, ← map_pow, ← map_sub, mm_iff, map_sub, map_pow, map_pow, ← sub_pow_char] at h
    rw [← map_sub, mm_iff, map_sub]
    exact (pow_eq_zero_iff V.l_prime.ne_zero).1 h
  · obtain ⟨F, rfl⟩ := exists_lift hf
    obtain ⟨G, rfl⟩ := exists_lift hg
    rw [forall_and]
    constructor
    · rw [← map_add, ← map_pow, ← map_pow, ← map_pow, ← map_sub, ← map_sub, mm_iff]
      simp only [map_sub, map_pow, map_add, add_pow_char]
      ring
    · rw [← map_sub, ← map_pow, ← map_pow, ← map_pow, ← map_sub, ← map_sub, mm_iff]
      simp only [map_sub, map_pow, sub_pow_char]
      ring

end GlobalTheory.SeriesFrobRoot

import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

/- English proof (translation)
Proceed by induction on `k generalizing a with`. Consider the case `zero => simpa using hx`. Consider the case `succ k ih`. Apply `ih` to reduce the goal to its premises. Establish `h` using `(P.PD (botExt l)).Fil_anti (a + k)`.

Apply `h` to reduce the goal to its premises. Establish `: a + ((k + 1 : ℕ) : ℤ) = a + k + 1` using `by push_cast; ring`. Rewrite using `[← this]` and apply the resulting hypothesis.
-/
theorem fil_add_nat_le {l : ℕ} [Fact l.Prime] (P : LocPrime l) (a : ℤ) (k : ℕ) {x : P.R.BdR}
    (hx : x ∈ (P.PD (botExt l)).Fil (a + k)) : x ∈ (P.PD (botExt l)).Fil a := by
  induction k generalizing a with
  | zero => simpa using hx
  | succ k ih =>
    apply ih
    have h := (P.PD (botExt l)).Fil_anti (a + k)
    apply h
    have : a + ((k + 1 : ℕ) : ℤ) = a + k + 1 := by push_cast; ring
    rwa [← this]

/- English proof (translation)
Introduce `l _ P AI T h d hh hd c hc hfil`. Establish `hF : IsField P.R.BdR` using `GlobalTheory.RegularRing.isField_of_tied T`. Establish `hι : Function.Injective P.ιB` using `fun a b hab => (P.PD (botExt l)).ι_inj (by rw [P.PD_ι, P.PD_ι, hab])`. Use `set PD := P.PD (botExt l) with hPD`. Establish `hdom : ∀ a b : P.R.B, a * b = 0 → a = 0 ∨ b = 0`.

Introduce `a b hab`. Establish `h0 : P.ιB a * P.ιB b = 0` using `by rw [← map_mul, hab, map_zero]`. Distinguish the cases in `ha : P.ιB a = 0`. Conclude with `Or.inl (hι (by rw [ha, map_zero]))`. Use `right`.

Take `⟨y, hy⟩` from `hF.mul_inv_cancel ha`. Apply `hι` to reduce the goal to its premises. Rewrite using `[map_zero]`. Combine the equalities or inequalities in the displayed calculation. Use `haveI : NoZeroDivisors P.R.B := ⟨fun {a b} hab => hdom a b hab⟩`.

Use `haveI : Nontrivial P.R.B := nontrivial_B P`. Assume the negation of the conclusion as `hc0`. Use `set N : P.R.B := ∏ j ∈ Finset.range h, P.φB^[j] c with hN`. Establish `hφN : c * P.φB N = N * P.φB^[h] c`. Establish `e1 : P.φB N = ∏ j ∈ Finset.range h, P.φB^[j + 1] c`.

Rewrite using `[hN, map_prod]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Function.iterate_succ_apply']`. Rewrite using `[e1, hN]`. Establish `e2` using `Finset.prod_range_succ' (fun j => P.φB^[j] c) h`.

Establish `e3` using `Finset.prod_range_succ (fun j => P.φB^[j] c) h`. Simplify using `only [Function.iterate_zero, id] at e2`. Rewrite using `[mul_comm c, ← e2, e3]`. Establish `hlN : (l : P.R.B) ^ d * P.φB N = N`. Establish `: c * ((l : P.R.B) ^ d * P.φB N - N) = 0`.

Combine the equalities or inequalities in the displayed calculation. Break down `hdom _ _ this with h1 | h1` into its components or cases. Conclude with `absurd h1 hc0`. Conclude with `sub_eq_zero.mp h1`. Use `set x : P.R.B := N * P.tB ^ d with hx`.

Establish `hφx : PD.φ x = x`. Rewrite using `[P.PD_φ, hx, map_mul, map_pow, localPrime_frobenius_periodT, Algebra.smul_def, map_natCast, mul_pow]`. Take the linear combination `(P.tB ^ d) * hlN`. Establish `hmul : ∀ (a b : ℤ) (u v : P.R.BdR), u ∈ PD.Fil a → v ∈ PD.Fil b → u * v ∈ PD.Fil (a + b)` using `fun a b u v hu hv => PD.Fil_mul a b u v hu hv`. Establish `hιN : P.ιB N ∈ PD.Fil 0`.

Rewrite using `[hN, map_prod]`. Use `Finset.prod_induction _ (fun u => u ∈ PD.Fil 0) (fun u v hu hv => by simpa using hmul 0 0 u v hu hv) (by simpa using PD.one_mem) fun j hj => ?_` and prove the remaining obligations. Conclude with `hfil j (Finset.mem_range.mp hj)`. Establish `hιt : P.ιB P.tB ∈ PD.Fil 1`. Use `PD.mem_filtration_one` as an intermediate fact.

Rewrite `this` using `[P.PD_ι, P.period_datum_t_eq]`. Then use the resulting hypothesis. Establish `hιtd : ∀ k : ℕ, P.ιB (P.tB ^ k) ∈ PD.Fil k`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa using PD.one_mem`.

Consider the case `succ k ih`. Rewrite using `[pow_succ, map_mul]`. Use `hmul k 1 _ _ ih hιt` as an intermediate fact. Simplify using `using this`. Establish `hιx1 : P.ιB x ∈ PD.Fil 1`.

Establish `h1 : P.ιB x ∈ PD.Fil (0 + d)` using `by rw [hx, map_mul]; exact hmul 0 d _ _ hιN (hιtd d)`. Take `⟨k, hk⟩ : ∃ k : ℕ, d = k + 1` from `⟨d - 1, by omega⟩`. Apply `fil_add_nat_le P 1 k` to reduce the goal to its premises. Establish `: (1 : ℤ) + (k : ℤ) = 0 + (d : ℤ)` using `by rw [hk]; push_cast; ring`. Rewrite using `[this]` and apply the resulting hypothesis.

Establish `hιx0 : P.ιB x ∈ PD.Fil 0` using `fil_add_nat_le P 0 1 (by simpa using hιx1)`. Take `⟨q, hq⟩` from `PD.fund x hφx (by rw [P.PD_ι]; exact hιx0)`. Distinguish the cases in `hq0 : q = 0`. Establish `hx0 : x = 0` using `by rw [← hq, hq0, map_zero]`. Establish `hN0 : N = 0`.

Break down `hdom _ _ hx0 with h1 | h1` into its components or cases. Conclude with `h1`. Conclude with `absurd (pow_eq_zero_iff (by omega) |>.mp h1) (isUnit_tB P).ne_zero`. Rewrite `hN0` using `[hN, Finset.prod_eq_zero_iff]`. Take `⟨j, -, hj⟩` from `hN0`.

Apply `hc0` to reduce the goal to its premises. Apply `(phiB_injective P).iterate j` to reduce the goal to its premises. Rewrite using `[hj, iterate_map_zero]`. Establish `hqx : P.ιB x = algebraMap ℚ_[l] P.R.BdR q` using `by rw [← hq, AlgHom.commutes]`. Establish `hinv : algebraMap ℚ_[l] P.R.BdR q⁻¹ ∈ PD.Fil 0`.

Rewrite using `[Algebra.algebraMap_eq_smul_one]`. Conclude with `Submodule.smul_of_tower_mem _ _ PD.one_mem`. Establish `hone : algebraMap ℚ_[l] P.R.BdR q⁻¹ * P.ιB x = 1`. Rewrite using `[hqx, ← map_mul, inv_mul_cancel₀ hq0, map_one]`. Establish `h2 : P.ιB P.tB ∈ PD.Fil 2`.

Use `hmul 1 (0 + 1) _ _ hιt (hmul 0 1 _ _ hinv hιx1)` as an intermediate fact. Rewrite `this` using `[hone, mul_one]`. Simplify using `using this`. Use `PD.not_mem_filtration_two` as an intermediate fact. Rewrite `this` using `[P.PD_ι, P.period_datum_t_eq]`.

Conclude with `this h2`.
-/
theorem no_fil_zero_neg_slope : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (h d : ℕ), 0 < h → 0 < d → ∀ c : P.R.B, (l : P.R.B) ^ d * P.φB^[h] c = c →
    (∀ j < h, ev P j c ∈ Fil P 0) → c = 0 := by
  intro l _ P AI T h d hh hd c hc hfil
  have hF : IsField P.R.BdR := GlobalTheory.RegularRing.isField_of_tied T
  have hι : Function.Injective P.ιB := fun a b hab => (P.PD (botExt l)).ι_inj (by rw [P.PD_ι, P.PD_ι, hab])
  set PD := P.PD (botExt l) with hPD
  have hdom : ∀ a b : P.R.B, a * b = 0 → a = 0 ∨ b = 0 := by
    intro a b hab
    have h0 : P.ιB a * P.ιB b = 0 := by rw [← map_mul, hab, map_zero]
    by_cases ha : P.ιB a = 0
    · exact Or.inl (hι (by rw [ha, map_zero]))
    · right
      obtain ⟨y, hy⟩ := hF.mul_inv_cancel ha
      apply hι
      rw [map_zero]
      calc P.ιB b = (y * P.ιB a) * P.ιB b := by rw [mul_comm y, hy, one_mul]
        _ = 0 := by rw [mul_assoc, h0, mul_zero]
  haveI : NoZeroDivisors P.R.B := ⟨fun {a b} hab => hdom a b hab⟩
  haveI : Nontrivial P.R.B := nontrivial_B P
  by_contra hc0
  set N : P.R.B := ∏ j ∈ Finset.range h, P.φB^[j] c with hN
  have hφN : c * P.φB N = N * P.φB^[h] c := by
    have e1 : P.φB N = ∏ j ∈ Finset.range h, P.φB^[j + 1] c := by
      rw [hN, map_prod]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Function.iterate_succ_apply']
    rw [e1, hN]
    have e2 := Finset.prod_range_succ' (fun j => P.φB^[j] c) h
    have e3 := Finset.prod_range_succ (fun j => P.φB^[j] c) h
    simp only [Function.iterate_zero, id] at e2
    rw [mul_comm c, ← e2, e3]
  have hlN : (l : P.R.B) ^ d * P.φB N = N := by
    have : c * ((l : P.R.B) ^ d * P.φB N - N) = 0 := by
      calc c * ((l : P.R.B) ^ d * P.φB N - N) = (l : P.R.B) ^ d * (c * P.φB N) - N * c := by ring
        _ = N * ((l : P.R.B) ^ d * P.φB^[h] c) - N * c := by rw [hφN]; ring
        _ = 0 := by rw [hc, sub_self]
    rcases hdom _ _ this with h1 | h1
    · exact absurd h1 hc0
    · exact sub_eq_zero.mp h1
  set x : P.R.B := N * P.tB ^ d with hx
  have hφx : PD.φ x = x := by
    rw [P.PD_φ, hx, map_mul, map_pow, localPrime_frobenius_periodT, Algebra.smul_def, map_natCast, mul_pow]
    linear_combination (P.tB ^ d) * hlN
  have hmul : ∀ (a b : ℤ) (u v : P.R.BdR), u ∈ PD.Fil a → v ∈ PD.Fil b → u * v ∈ PD.Fil (a + b) :=
    fun a b u v hu hv => PD.Fil_mul a b u v hu hv
  have hιN : P.ιB N ∈ PD.Fil 0 := by
    rw [hN, map_prod]
    refine Finset.prod_induction _ (fun u => u ∈ PD.Fil 0) (fun u v hu hv => by simpa using hmul 0 0 u v hu hv)
      (by simpa using PD.one_mem) fun j hj => ?_
    exact hfil j (Finset.mem_range.mp hj)
  have hιt : P.ιB P.tB ∈ PD.Fil 1 := by
    have := PD.mem_filtration_one
    rwa [P.PD_ι, P.period_datum_t_eq] at this
  have hιtd : ∀ k : ℕ, P.ιB (P.tB ^ k) ∈ PD.Fil k := by
    intro k
    induction k with
    | zero => simpa using PD.one_mem
    | succ k ih =>
      rw [pow_succ, map_mul]
      have := hmul k 1 _ _ ih hιt
      simpa using this
  have hιx1 : P.ιB x ∈ PD.Fil 1 := by
    have h1 : P.ιB x ∈ PD.Fil (0 + d) := by rw [hx, map_mul]; exact hmul 0 d _ _ hιN (hιtd d)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, d = k + 1 := ⟨d - 1, by omega⟩
    apply fil_add_nat_le P 1 k
    have : (1 : ℤ) + (k : ℤ) = 0 + (d : ℤ) := by rw [hk]; push_cast; ring
    rwa [this]
  have hιx0 : P.ιB x ∈ PD.Fil 0 := fil_add_nat_le P 0 1 (by simpa using hιx1)
  obtain ⟨q, hq⟩ := PD.fund x hφx (by rw [P.PD_ι]; exact hιx0)
  by_cases hq0 : q = 0
  · have hx0 : x = 0 := by rw [← hq, hq0, map_zero]
    have hN0 : N = 0 := by
      rcases hdom _ _ hx0 with h1 | h1
      · exact h1
      · exact absurd (pow_eq_zero_iff (by omega) |>.mp h1) (isUnit_tB P).ne_zero
    rw [hN, Finset.prod_eq_zero_iff] at hN0
    obtain ⟨j, -, hj⟩ := hN0
    apply hc0
    apply (phiB_injective P).iterate j
    rw [hj, iterate_map_zero]
  · have hqx : P.ιB x = algebraMap ℚ_[l] P.R.BdR q := by rw [← hq, AlgHom.commutes]
    have hinv : algebraMap ℚ_[l] P.R.BdR q⁻¹ ∈ PD.Fil 0 := by
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_of_tower_mem _ _ PD.one_mem
    have hone : algebraMap ℚ_[l] P.R.BdR q⁻¹ * P.ιB x = 1 := by
      rw [hqx, ← map_mul, inv_mul_cancel₀ hq0, map_one]
    have h2 : P.ιB P.tB ∈ PD.Fil 2 := by
      have := hmul 1 (0 + 1) _ _ hιt (hmul 0 1 _ _ hinv hιx1)
      rw [hone, mul_one] at this
      simpa using this
    have := PD.not_mem_filtration_two
    rw [P.PD_ι, P.period_datum_t_eq] at this
    exact this h2

end GlobalTheory.PMon

end

import Mathlib

noncomputable section

open NumberField

namespace Formalism.L2.SG.NGCut.TorsionTotientBound

/- English proof (translation)
Proceed by induction on `n using Nat.recOnPosPrimePosCoprime with`. Consider the case `prime_pow p k hp hk`. Rewrite using `[Nat.totient_prime_pow hp hk]`. Take `⟨m, rfl⟩ : ∃ m, k = m + 1` from `⟨k - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel]`.

Break down `hp.eq_two_or_odd' with rfl | hodd` into its components or cases. Establish `he : Even (2 ^ (m + 1))` using `Nat.even_pow.mpr ⟨even_two, by omega⟩`. Rewrite using `[if_pos he]`. Establish `h1 : 2 ^ m ≤ 2 ^ m * 2 ^ m` using `Nat.le_mul_of_pos_right _ (by positivity)`. Rewrite using `[pow_succ]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hne : ¬ Even (p ^ (m + 1))`. Rewrite using `[Nat.not_even_iff_odd]`. Conclude with `hodd.pow`. Rewrite using `[if_neg hne, one_mul]`.

Establish `h3 : 3 ≤ p`. Use `hp.two_le` as an intermediate fact. Break down `hodd with ⟨j, hj⟩` into its components or cases. Use linear arithmetic over natural numbers and integers. Take `⟨q, rfl⟩ : ∃ q, p = q + 1` from `⟨p - 1, by omega⟩`.

Simplify using `only [Nat.add_sub_cancel]`. Establish `hP : 1 ≤ (q + 1) ^ m` using `Nat.one_le_pow _ _ (by omega)`. Establish `hq : q + 1 ≤ q ^ 2` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation. Consider the case `zero => simp`.

Consider the case `one => simp`. Consider the case `coprime a b ha hb hab iha ihb`. Rewrite using `[Nat.totient_mul hab, mul_pow]`. Establish `hce : (if Even (a * b) then 2 else 1) = (if Even a then 2 else 1) * (if Even b then 2 else 1)`. Apply the tactic sequence `by_cases ea : Even a <;> by_cases eb : Even b <;> simp [ea, eb, Nat.even_mul]`.

Establish `h2 : 2 ∣ Nat.gcd a b` using `Nat.dvd_gcd (even_iff_two_dvd.mp ea) (even_iff_two_dvd.mp eb)`. Rewrite `h2` using `[hab.gcd_eq_one]`. Evaluate the numerical expressions using `at h2`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem le_mul_totient_sq (n : ℕ) : n ≤ (if Even n then 2 else 1) * n.totient ^ 2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    rw [Nat.totient_prime_pow hp hk]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rcases hp.eq_two_or_odd' with rfl | hodd
    · have he : Even (2 ^ (m + 1)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
      rw [if_pos he]
      have h1 : 2 ^ m ≤ 2 ^ m * 2 ^ m := Nat.le_mul_of_pos_right _ (by positivity)
      rw [pow_succ]
      nlinarith
    · have hne : ¬ Even (p ^ (m + 1)) := by
        rw [Nat.not_even_iff_odd]
        exact hodd.pow
      rw [if_neg hne, one_mul]
      have h3 : 3 ≤ p := by
        have := hp.two_le
        rcases hodd with ⟨j, hj⟩
        omega
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have hP : 1 ≤ (q + 1) ^ m := Nat.one_le_pow _ _ (by omega)
      have hq : q + 1 ≤ q ^ 2 := by nlinarith
      calc (q + 1) ^ (m + 1) = (q + 1) ^ m * (q + 1) := pow_succ _ _
        _ ≤ (q + 1) ^ m * q ^ 2 := Nat.mul_le_mul_left _ hq
        _ ≤ ((q + 1) ^ m) ^ 2 * q ^ 2 := Nat.mul_le_mul_right _ (by nlinarith)
        _ = ((q + 1) ^ m * q) ^ 2 := by ring
  | zero => simp
  | one => simp
  | coprime a b ha hb hab iha ihb =>
    rw [Nat.totient_mul hab, mul_pow]
    have hce : (if Even (a * b) then 2 else 1) =
        (if Even a then 2 else 1) * (if Even b then 2 else 1) := by
      by_cases ea : Even a <;> by_cases eb : Even b <;> simp [ea, eb, Nat.even_mul]
      have h2 : 2 ∣ Nat.gcd a b := Nat.dvd_gcd (even_iff_two_dvd.mp ea) (even_iff_two_dvd.mp eb)
      rw [hab.gcd_eq_one] at h2
      norm_num at h2
    calc a * b ≤ ((if Even a then 2 else 1) * a.totient ^ 2) *
          ((if Even b then 2 else 1) * b.totient ^ 2) := Nat.mul_le_mul iha ihb
      _ = _ := by rw [hce]; ring

/- English proof (translation)
Use `le_mul_totient_sq n` as an intermediate fact. Apply the tactic sequence `split_ifs at this <;> nlinarith [Nat.zero_le (n.totient ^ 2)]`.
-/
theorem le_two_totient_sq (n : ℕ) : n ≤ 2 * n.totient ^ 2 := by
  have := le_mul_totient_sq n
  split_ifs at this <;> nlinarith [Nat.zero_le (n.totient ^ 2)]

/- English proof (translation)
Take `⟨g, hg⟩` from `IsCyclic.exists_generator (α := NumberField.Units.torsion E)`. Establish `hord : orderOf g = Units.torsionOrder E`. Rewrite using `[orderOf_eq_card_of_forall_mem_zpowers hg]`. Both sides reduce to the same expression. Establish `hpos : 0 < Units.torsionOrder E` using `hord ▸ orderOf_pos g`.

Set `f : NumberField.Units.torsion E →* E` to `((algebraMap (𝓞 E) E : 𝓞 E →+* E) : 𝓞 E →* E).comp ((Units.coeHom (𝓞 E)).comp (NumberField.Units.torsion E).subtype)`. Establish `hf : Function.Injective f`. Introduce `x y hxy`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Conclude with `(FaithfulSMul.algebraMap_injective (𝓞 E) E) hxy`. Establish `hζ : IsPrimitiveRoot (f g) (Units.torsionOrder E)` using `hord ▸ (IsPrimitiveRoot.orderOf g).map_of_injective hf`. Establish `hdeg : (Units.torsionOrder E).totient ≤ Module.finrank ℚ E`. Rewrite using `[← Polynomial.natDegree_cyclotomic (Units.torsionOrder E) ℚ, Polynomial.cyclotomic_eq_minpoly_rat hζ hpos]`. Conclude with `minpoly.natDegree_le _`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem torsionOrder_le (E : Type) [Field E] [NumberField E] :
    Units.torsionOrder E ≤ 2 * (Module.finrank ℚ E) ^ 2 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := NumberField.Units.torsion E)
  have hord : orderOf g = Units.torsionOrder E := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg]
    rfl
  have hpos : 0 < Units.torsionOrder E := hord ▸ orderOf_pos g
  let f : NumberField.Units.torsion E →* E :=
    ((algebraMap (𝓞 E) E : 𝓞 E →+* E) : 𝓞 E →* E).comp
      ((Units.coeHom (𝓞 E)).comp (NumberField.Units.torsion E).subtype)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Units.ext
    exact (FaithfulSMul.algebraMap_injective (𝓞 E) E) hxy
  have hζ : IsPrimitiveRoot (f g) (Units.torsionOrder E) :=
    hord ▸ (IsPrimitiveRoot.orderOf g).map_of_injective hf
  have hdeg : (Units.torsionOrder E).totient ≤ Module.finrank ℚ E := by
    rw [← Polynomial.natDegree_cyclotomic (Units.torsionOrder E) ℚ,
      Polynomial.cyclotomic_eq_minpoly_rat hζ hpos]
    exact minpoly.natDegree_le _
  calc Units.torsionOrder E ≤ 2 * (Units.torsionOrder E).totient ^ 2 := le_two_totient_sq _
    _ ≤ 2 * (Module.finrank ℚ E) ^ 2 := by gcongr

end Formalism.L2.SG.NGCut.TorsionTotientBound

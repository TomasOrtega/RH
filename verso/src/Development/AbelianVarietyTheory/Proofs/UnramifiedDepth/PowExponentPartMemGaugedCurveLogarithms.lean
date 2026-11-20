import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedFormalGroupCurveLogarithmsAddSubgroupRescaStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedCurveLogarithmsClosedUnderTadicLimits
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CurveLogarithmsInvNatCastSmulMemStatement

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

noncomputable section

namespace GlobalTheory.RowLaw.TypPart

variable {C : Type} [Field C]

/- English proof (translation)
Take `⟨n, rfl | rfl⟩` from `a.eq_nat_or_neg`. Simplify using `using VF.ge_natCast (V := V) n`. Simplify using `using (VF.ge_natCast (V := V) n).neg`.
-/
theorem ge_intCast (V : VF C) (a : ℤ) : V.Ge 0 (a : C) := by
  obtain ⟨n, rfl | rfl⟩ := a.eq_nat_or_neg
  · simpa using VF.ge_natCast (V := V) n
  · simpa using (VF.ge_natCast (V := V) n).neg

/- English proof (translation)
Establish `hc : IsCoprime (p : ℤ) (V.l : ℤ)` using `Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp V.l_prime).2 hpl)`. Take `⟨a, b, hab⟩` from `hc`. Establish `h1 : (a : C) * (p : C) + (b : C) * (V.l : C) = 1`. Use `congrArg (fun z : ℤ => (z : C)) hab` as an intermediate fact. Simplify using `using this`.

Establish `h0 : (0 : WithTop ℝ) ≤ V.v (p : C)` using `by simpa [VF.Ge] using VF.ge_natCast (V := V) p`. Establish `ha : (0 : WithTop ℝ) ≤ V.v (a : C)` using `by simpa [VF.Ge] using ge_intCast V a`. Establish `hb : (0 : WithTop ℝ) ≤ V.v (b : C)` using `by simpa [VF.Ge] using ge_intCast V b`. Assume the negation of the conclusion as `hne`. Establish `hpos : (0 : WithTop ℝ) < V.v (p : C)` using `lt_of_le_of_ne h0 (Ne.symm hne)`.

Establish `e1 : (0 : WithTop ℝ) < V.v ((a : C) * (p : C))`. Rewrite using `[V.v.map_mul]`. Conclude with `lt_of_lt_of_le hpos (le_add_of_nonneg_left ha)`. Establish `e2 : (0 : WithTop ℝ) < V.v ((b : C) * (V.l : C))`. Rewrite using `[V.v.map_mul, V.v_l]`.

Conclude with `lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left hb)`. Use `V.v.map_lt_add e1 e2` as an intermediate fact. Rewrite `this` using `[h1, V.v.map_one]`. Conclude with `lt_irrefl _ this`.
-/
theorem v_prime_eq_zero (V : VF C) {p : ℕ} (hp : p.Prime) (hpl : p ≠ V.l) : V.v (p : C) = 0 := by
  have hc : IsCoprime (p : ℤ) (V.l : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp V.l_prime).2 hpl)
  obtain ⟨a, b, hab⟩ := hc
  have h1 : (a : C) * (p : C) + (b : C) * (V.l : C) = 1 := by
    have := congrArg (fun z : ℤ => (z : C)) hab
    simpa using this
  have h0 : (0 : WithTop ℝ) ≤ V.v (p : C) := by simpa [VF.Ge] using VF.ge_natCast (V := V) p
  have ha : (0 : WithTop ℝ) ≤ V.v (a : C) := by simpa [VF.Ge] using ge_intCast V a
  have hb : (0 : WithTop ℝ) ≤ V.v (b : C) := by simpa [VF.Ge] using ge_intCast V b
  by_contra hne
  have hpos : (0 : WithTop ℝ) < V.v (p : C) := lt_of_le_of_ne h0 (Ne.symm hne)
  have e1 : (0 : WithTop ℝ) < V.v ((a : C) * (p : C)) := by
    rw [V.v.map_mul]; exact lt_of_lt_of_le hpos (le_add_of_nonneg_left ha)
  have e2 : (0 : WithTop ℝ) < V.v ((b : C) * (V.l : C)) := by
    rw [V.v.map_mul, V.v_l]; exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left hb)
  have := V.v.map_lt_add e1 e2
  rw [h1, V.v.map_one] at this
  exact lt_irrefl _ this

/- English proof (translation)
Establish `h1 : p • V.v ζ = 0` using `by rw [← V.v.map_pow, h, V.v.map_one]`. Unfold `VF.Ge`. Proceed by induction on `hv : V.v ζ using WithTop.recTopCoe with`. Consider the case `top => exact le_top`. Consider the case `coe t`.

Rewrite `h1` using `[hv, ← WithTop.coe_nsmul]`. Establish `h2 : p • t = 0` using `by exact_mod_cast h1`. Establish `h3 : t = 0`. Rewrite `h2` using `[nsmul_eq_mul]`. Break down `mul_eq_zero.1 h2 with h | h` into its components or cases.

Conclude with `absurd (by exact_mod_cast h) hp.ne'`. Conclude with `h`. Rewrite using `[h3]`.
-/
theorem ge_of_pow_eq_one (V : VF C) {ζ : C} {p : ℕ} (hp : 0 < p) (h : ζ ^ p = 1) : V.Ge 0 ζ := by
  have h1 : p • V.v ζ = 0 := by rw [← V.v.map_pow, h, V.v.map_one]
  unfold VF.Ge
  induction hv : V.v ζ using WithTop.recTopCoe with
  | top => exact le_top
  | coe t =>
    rw [hv, ← WithTop.coe_nsmul] at h1
    have h2 : p • t = 0 := by exact_mod_cast h1
    have h3 : t = 0 := by
      rw [nsmul_eq_mul] at h2
      rcases mul_eq_zero.1 h2 with h | h
      · exact absurd (by exact_mod_cast h) hp.ne'
      · exact h
    rw [h3]

/- English proof (translation)
Establish `e : ∀ j, (ζ ^ j) ^ m = (ζ ^ m) ^ j` using `fun j => by rw [← pow_mul, ← pow_mul, mul_comm]`. Repeatedly rewrite using `[e]`. Use `split_ifs with h`. Rewrite using `[(hζ.pow_eq_one_iff_dvd m).2 h]`. Simplify using the standard rewrite rules.

Establish `hne : ζ ^ m - 1 ≠ 0` using `fun h' => h ((hζ.pow_eq_one_iff_dvd m).1 (sub_eq_zero.1 h'))`. Use `geom_sum_mul (ζ ^ m) p` as an intermediate fact. Rewrite `this` using `[← pow_mul, mul_comm m p, pow_mul, hζ.pow_eq_one, one_pow, sub_self]`. Conclude with `(mul_eq_zero.1 this).resolve_right hne`.
-/
theorem sum_pow_root {ζ : C} {p : ℕ} (hζ : IsPrimitiveRoot ζ p) (m : ℕ) :
    ∑ j ∈ Finset.range p, (ζ ^ j) ^ m = if p ∣ m then (p : C) else 0 := by
  have e : ∀ j, (ζ ^ j) ^ m = (ζ ^ m) ^ j := fun j => by rw [← pow_mul, ← pow_mul, mul_comm]
  simp_rw [e]
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd m).2 h]; simp
  · have hne : ζ ^ m - 1 ≠ 0 := fun h' => h ((hζ.pow_eq_one_iff_dvd m).1 (sub_eq_zero.1 h'))
    have := geom_sum_mul (ζ ^ m) p
    rw [← pow_mul, mul_comm m p, pow_mul, hζ.pow_eq_one, one_pow, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right hne

open Classical in

def filt (P : ℕ → Prop) (f : PowerSeries C) : PowerSeries C :=
  PowerSeries.mk fun m => if P m then PowerSeries.coeff m f else 0

open Classical in
/- English proof (translation)
Simplify using `[filt]`.
-/
theorem coeff_filt (P : ℕ → Prop) (f : PowerSeries C) (m : ℕ) :
    PowerSeries.coeff m (filt P f) = if P m then PowerSeries.coeff m f else 0 := by
  simp [filt]

/- English proof (translation)
Use extensionality with `m`. Establish `hp' : (p : C) ≠ 0` using `by exact_mod_cast hp.ne'`. Rewrite using `[coeff_filt, map_add, map_neg, PowerSeries.coeff_smul, map_sum]`. Repeatedly rewrite using `[PowerSeries.coeff_rescale]`. Rewrite using `[← Finset.sum_mul, sum_pow_root hζ]`.

Distinguish the cases in `h : p ∣ m`. Simplify using `[h, hp']`. Simplify using `[h]`.
-/
theorem sub_avg [CharZero C] {ζ : C} {p : ℕ} (hp : 0 < p) (hζ : IsPrimitiveRoot ζ p) (f : PowerSeries C) :
    f + -((p : C)⁻¹ • ∑ j ∈ Finset.range p, PowerSeries.rescale (ζ ^ j) f) = filt (fun m => ¬ p ∣ m) f := by
  ext m
  have hp' : (p : C) ≠ 0 := by exact_mod_cast hp.ne'
  rw [coeff_filt, map_add, map_neg, PowerSeries.coeff_smul, map_sum]
  simp_rw [PowerSeries.coeff_rescale]
  rw [← Finset.sum_mul, sum_pow_root hζ]
  by_cases h : p ∣ m
  · simp [h, hp']
  · simp [h]

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[coeff_filt, coeff_filt, coeff_filt]`. Apply the tactic sequence `by_cases h : P m <;> by_cases h' : Q m <;> simp [h, h']`.
-/
theorem filt_filt (P Q : ℕ → Prop) (f : PowerSeries C) :
    filt P (filt Q f) = filt (fun m => P m ∧ Q m) f := by
  ext m
  rw [coeff_filt, coeff_filt, coeff_filt]
  by_cases h : P m <;> by_cases h' : Q m <;> simp [h, h']

/- English proof (translation)
Establish `: P = Q` using `funext fun m => propext (h m)`. Rewrite using `[this]`.
-/
theorem filt_congr {P Q : ℕ → Prop} (h : ∀ m, P m ↔ Q m) (f : PowerSeries C) : filt P f = filt Q f := by
  have : P = Q := funext fun m => propext (h m)
  rw [this]

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[coeff_filt, if_pos (h m)]`.
-/
theorem filt_true {P : ℕ → Prop} (h : ∀ m, P m) (f : PowerSeries C) : filt P f = f := by
  ext m
  rw [coeff_filt, if_pos (h m)]

def Good (l n m : ℕ) : Prop := ∀ p < n, p.Prime → p ≠ l → ¬ p ∣ m

/- English proof (translation)
Rewrite using `[coeff_filt]`. Unfold `typ`. Distinguish the cases in `hm : ∃ s, l ^ s = m`. Take `⟨s, rfl⟩` from `hm`. Rewrite using `[coeff_tyS_pow hl.two_le, if_pos]`.

Introduce `p _ hp hpl hd`. Conclude with `hpl ((Nat.prime_dvd_prime_iff_eq hp hl).1 (hp.dvd_of_dvd_pow hd))`. Rewrite using `[coeff_tyS_of_ne _ m (fun s hs => hm ⟨s, hs⟩), if_neg]`. Introduce `hg`. Break down `Nat.eq_zero_or_pos m with rfl | hpos` into its components or cases.

Conclude with `hg 2 (by omega) Nat.prime_two (Ne.symm hl2) (dvd_zero 2)`. Apply `hm` to reduce the goal to its premises. Use `⟨_, (Nat.eq_prime_pow_of_unique_prime_dvd hpos.ne' ?_).symm⟩` and prove the remaining obligations. Introduce `q hq hqm`. Assume the negation of the conclusion as `hne`.

Conclude with `hg q (by have := Nat.le_of_dvd hpos hqm; omega) hq hne hqm`.
-/
theorem coeff_filt_good {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (f : PowerSeries C) (m n : ℕ) (hn : m + 3 ≤ n) :
    PowerSeries.coeff m (filt (Good l n) f) = PowerSeries.coeff m (typ l f) := by
  rw [coeff_filt]
  unfold typ
  by_cases hm : ∃ s, l ^ s = m
  · obtain ⟨s, rfl⟩ := hm
    rw [coeff_tyS_pow hl.two_le, if_pos]
    intro p _ hp hpl hd
    exact hpl ((Nat.prime_dvd_prime_iff_eq hp hl).1 (hp.dvd_of_dvd_pow hd))
  · rw [coeff_tyS_of_ne _ m (fun s hs => hm ⟨s, hs⟩), if_neg]
    intro hg
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exact hg 2 (by omega) Nat.prime_two (Ne.symm hl2) (dvd_zero 2)
    · apply hm
      refine ⟨_, (Nat.eq_prime_pow_of_unique_prime_dvd hpos.ne' ?_).symm⟩
      intro q hq hqm
      by_contra hne
      exact hg q (by have := Nat.le_of_dvd hpos hqm; omega) hq hne hqm

variable {V : VF C} {d : ℕ} [NeZero d] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
  {X : RawChart C d I κ}

/- English proof (translation)
Use `hX.charZero` as an intermediate fact. Use `hX.closed` as an intermediate fact. Establish `: NeZero (p : C)` using `⟨by exact_mod_cast hp.ne_zero⟩`. Establish `: NeZero p` using `⟨hp.ne_zero⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot C p`.

Take `⟨h0, hadd, hneg, hres⟩` from `GlobalTheory.T.gaugedFormalGroupCurveLogarithms_addSubgroup_rescale C V d I κ X hX g`. Establish `hζ0 : V.Ge 0 ζ` using `ge_of_pow_eq_one V hp.pos hζ.pow_eq_one`. Establish `hs : ∀ n : ℕ, ((fun i => ∑ j ∈ Finset.range n, PowerSeries.rescale (ζ ^ j) (a.1 i), fun q => ∑ j ∈ Finset.range n, PowerSeries.rescale (ζ ^ j) (a.2 q)) : (κ → PowerSeries C) × (JJ I g → PowerSeries C)) ∈ Cv X V g`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero`. Simplify using `only [Finset.range_zero, Finset.sum_empty]`. Conclude with `h0`. Consider the case `succ n ih`. Use `hadd _ ih _ (hres (ζ ^ n) (hζ0.pow n) a ha)` as an intermediate fact.

Simplify using `only [Finset.sum_range_succ]`. Conclude with `this`. Establish `h2` using `hadd _ ha _ (hneg _ (GlobalTheory.T.curveLogarithms_inv_natCast_smul_mem C V d I κ X hX g p (v_prime_eq_zero V hp hpl) _ (hs p)))`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use `Prod.ext (funext fun i => ?_) (funext fun q => ?_)` and prove the remaining obligations.

Conclude with `(sub_avg hp.pos hζ (a.1 i)).symm`. Conclude with `(sub_avg hp.pos hζ (a.2 q)).symm`.
-/
theorem filt_not_dvd_mem (hX : RLaw X V) (g : Fin 2) {p : ℕ} (hp : p.Prime) (hpl : p ≠ V.l)
    (a : (κ → PowerSeries C) × (JJ I g → PowerSeries C)) (ha : a ∈ Cv X V g) :
    ((fun i => filt (fun m => ¬ p ∣ m) (a.1 i), fun q => filt (fun m => ¬ p ∣ m) (a.2 q)) :
      (κ → PowerSeries C) × (JJ I g → PowerSeries C)) ∈ Cv X V g := by
  have := hX.charZero
  have := hX.closed
  have : NeZero (p : C) := ⟨by exact_mod_cast hp.ne_zero⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C p
  obtain ⟨h0, hadd, hneg, hres⟩ := GlobalTheory.T.gaugedFormalGroupCurveLogarithms_addSubgroup_rescale C V d I κ X hX g
  have hζ0 : V.Ge 0 ζ := ge_of_pow_eq_one V hp.pos hζ.pow_eq_one
  have hs : ∀ n : ℕ, ((fun i => ∑ j ∈ Finset.range n, PowerSeries.rescale (ζ ^ j) (a.1 i),
      fun q => ∑ j ∈ Finset.range n, PowerSeries.rescale (ζ ^ j) (a.2 q)) :
      (κ → PowerSeries C) × (JJ I g → PowerSeries C)) ∈ Cv X V g := by
    intro n
    induction n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact h0
    | succ n ih =>
      have := hadd _ ih _ (hres (ζ ^ n) (hζ0.pow n) a ha)
      simp only [Finset.sum_range_succ]
      exact this
  have h2 := hadd _ ha _ (hneg _ (GlobalTheory.T.curveLogarithms_inv_natCast_smul_mem C V d I κ X hX g p (v_prime_eq_zero V hp hpl) _ (hs p)))
  convert h2 using 1
  refine Prod.ext (funext fun i => ?_) (funext fun q => ?_)
  · exact (sub_avg hp.pos hζ (a.1 i)).symm
  · exact (sub_avg hp.pos hζ (a.2 q)).symm

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `h : ∀ m, Good V.l 0 m` using `fun m p hp => absurd hp (Nat.not_lt_zero p)`. Simplify using `only [filt_true h]`. Conclude with `ha`.

Consider the case `succ n ih`. Distinguish the cases in `hn : n.Prime ∧ n ≠ V.l`. Establish `h : ∀ m, Good V.l (n + 1) m ↔ (¬ n ∣ m ∧ Good V.l n m)`. Introduce `m`. Prove the components needed by the constructor for the conclusion.

Introduce `hg`. Conclude with `⟨hg n (by omega) hn.1 hn.2, fun p hp => hg p (by omega)⟩`. Introduce and unpack `⟨h1, h2⟩ p hp hpp hpl`. Break down `Nat.lt_succ_iff_lt_or_eq.1 hp with h | rfl` into its components or cases. Conclude with `h2 p h hpp hpl`.

Conclude with `h1`. Use `filt_not_dvd_mem hX g hn.1 hn.2 _ ih` as an intermediate fact. Simplify using `only [filt_filt] at this`. Simplify using `only [filt_congr h]`. Conclude with `this`.

Establish `h : ∀ m, Good V.l (n + 1) m ↔ Good V.l n m`. Introduce `m`. Prove the components needed by the constructor for the conclusion. Introduce `hg p hp`. Conclude with `hg p (by omega)`.

Introduce `h2 p hp hpp hpl`. Break down `Nat.lt_succ_iff_lt_or_eq.1 hp with h | rfl` into its components or cases. Conclude with `h2 p h hpp hpl`. Conclude with `absurd ⟨hpp, hpl⟩ hn`. Simplify using `only [filt_congr h]`.

Conclude with `ih`.
-/
theorem filt_good_mem (hX : RLaw X V) (g : Fin 2)
    (a : (κ → PowerSeries C) × (JJ I g → PowerSeries C)) (ha : a ∈ Cv X V g) (n : ℕ) :
    ((fun i => filt (Good V.l n) (a.1 i), fun q => filt (Good V.l n) (a.2 q)) :
      (κ → PowerSeries C) × (JJ I g → PowerSeries C)) ∈ Cv X V g := by
  induction n with
  | zero =>
    have h : ∀ m, Good V.l 0 m := fun m p hp => absurd hp (Nat.not_lt_zero p)
    simp only [filt_true h]
    exact ha
  | succ n ih =>
    by_cases hn : n.Prime ∧ n ≠ V.l
    · have h : ∀ m, Good V.l (n + 1) m ↔ (¬ n ∣ m ∧ Good V.l n m) := by
        intro m
        constructor
        · intro hg
          exact ⟨hg n (by omega) hn.1 hn.2, fun p hp => hg p (by omega)⟩
        · rintro ⟨h1, h2⟩ p hp hpp hpl
          rcases Nat.lt_succ_iff_lt_or_eq.1 hp with h | rfl
          · exact h2 p h hpp hpl
          · exact h1
      have := filt_not_dvd_mem hX g hn.1 hn.2 _ ih
      simp only [filt_filt] at this
      simp only [filt_congr h]
      exact this
    · have h : ∀ m, Good V.l (n + 1) m ↔ Good V.l n m := by
        intro m
        constructor
        · intro hg p hp
          exact hg p (by omega)
        · intro h2 p hp hpp hpl
          rcases Nat.lt_succ_iff_lt_or_eq.1 hp with h | rfl
          · exact h2 p h hpp hpl
          · exact absurd ⟨hpp, hpl⟩ hn
      simp only [filt_congr h]
      exact ih

end GlobalTheory.RowLaw.TypPart

open GlobalTheory.RowLaw.TypPart in

/- English proof (translation)
Introduce `C _ V d _ I _ κ _ X hX g a ha`. Use `GlobalTheory.RowLaw.cv_closed_under_limits C V d I κ X hX g _ _ (filt_good_mem hX g a ha) fun m => ⟨m + 3, fun n hn => ⟨fun i => ?_, fun q => ?_⟩⟩` and prove the remaining obligations. Conclude with `coeff_filt_good V.l_prime hX.odd _ m n hn`. Conclude with `coeff_filt_good V.l_prime hX.odd _ m n hn`.
-/
theorem GlobalTheory.RowLaw.typ_mem_Cv : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g, ∀ a ∈ Cv X V g, ((fun i => typ V.l (a.1 i), fun q => typ V.l (a.2 q)) : ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) ∈ Cv X V g := by
  intro C _ V d _ I _ κ _ X hX g a ha
  refine GlobalTheory.RowLaw.cv_closed_under_limits C V d I κ X hX g _ _ (filt_good_mem hX g a ha) fun m => ⟨m + 3, fun n hn => ⟨fun i => ?_, fun q => ?_⟩⟩
  · exact coeff_filt_good V.l_prime hX.odd _ m n hn
  · exact coeff_filt_good V.l_prime hX.odd _ m n hn

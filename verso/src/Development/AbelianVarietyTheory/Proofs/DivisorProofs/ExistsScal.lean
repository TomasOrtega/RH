import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.RefSum.ScalApprox

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Establish `h0 : w.intValuation r ≠ 0` using `w.intValuation_ne_zero r hr`. Rewrite using `[← w.intValuation_le_pow_iff_mem, vAdd, HeightOneSpectrum.valuation_of_algebraMap]`. Use `conv_lhs => rw [← WithZero.exp_log h0]`. Rewrite using `[WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_pow_iff (w : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K} (hr : r ≠ 0) (n : ℕ) :
    r ∈ w.asIdeal ^ n ↔ (n : ℤ) ≤ vAdd w (r : K) := by
  have h0 : w.intValuation r ≠ 0 := w.intValuation_ne_zero r hr
  rw [← w.intValuation_le_pow_iff_mem, vAdd, HeightOneSpectrum.valuation_of_algebraMap]
  conv_lhs => rw [← WithZero.exp_log h0]
  rw [WithZero.exp_le_exp]
  omega

/- English proof (translation)
Establish `hx' : w.valuation K x ≠ 0` using `(Valuation.ne_zero_iff _).2 hx`. Establish `hy' : w.valuation K y ≠ 0` using `(Valuation.ne_zero_iff _).2 hy`. Rewrite using `[vAdd, vAdd, vAdd, map_div₀, WithZero.log_div hx' hy']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vAdd_div (w : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    vAdd w (x / y) = vAdd w x - vAdd w y := by
  have hx' : w.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : w.valuation K y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  rw [vAdd, vAdd, vAdd, map_div₀, WithZero.log_div hx' hy']
  ring

end GlobalTheory.RefSum.ScalApprox

namespace GlobalTheory.RefSum.ScalApprox

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Introduce `K _ _ ρ hρ w`. Use `set S : Finset (HeightOneSpectrum (𝓞 K)) := insert w hρ.toFinset with hS`. Establish `hne : ∀ v : HeightOneSpectrum (𝓞 K), ∃ e : 𝓞 K, e ∈ v.asIdeal ∧ e ≠ 0` using `fun v => Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot`. Use `choose e he he0 using hne`. Use `set N : ℕ := ∑ v ∈ S, (⌊ρ v⌋).toNat with hN`.

Use `set c : 𝓞 K := (∏ v ∈ S, e v) ^ N with hc`. Establish `hc0 : c ≠ 0` using `pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun v _ => he0 v)`. Establish `hcK : (c : K) ≠ 0` using `by exact_mod_cast hc0`. Establish `hcS : ∀ v ∈ S, -⌊ρ v⌋ + vAdd v (c : K) ≥ 0`. Introduce `v hv`.

Establish `h1 : ∏ u ∈ S, e u ∈ v.asIdeal`. Take `⟨t, ht⟩` from `Finset.dvd_prod_of_mem e hv`. Rewrite using `[ht]`. Conclude with `Ideal.mul_mem_right _ _ (he v)`. Establish `h2 : c ∈ v.asIdeal ^ N` using `Ideal.pow_mem_pow h1 N`.

Establish `h3` using `(mem_pow_iff v hc0 N).1 h2`. Establish `h4 : (⌊ρ v⌋).toNat ≤ N` using `Finset.single_le_sum (f := fun u => (⌊ρ u⌋).toNat) (fun _ _ => Nat.zero_le _) hv`. Establish `h5 : ⌊ρ v⌋ ≤ ((⌊ρ v⌋).toNat : ℤ)` using `Int.self_le_toNat _`. Use linear arithmetic over natural numbers and integers. Establish `hfc` using `GlobalTheory.FlatLine.finite_vAdd hcK`.

Use `set T : Finset (HeightOneSpectrum (𝓞 K)) := S ∪ hfc.toFinset with hT`. Use `set E : HeightOneSpectrum (𝓞 K) → ℕ := fun v => (-⌊ρ v⌋ + vAdd v (c : K)).toNat with hE`. Take `⟨π, hπ⟩` from `w.intValuation_exists_uniformizer`. Establish `hπpow : ∀ n : ℕ, w.intValuation (π ^ n) = WithZero.exp (-(n : ℤ))` using `fun n => by`. Rewrite using `[map_pow, hπ, ← WithZero.exp_nsmul]`.

Use `congr 1`. Simplify using the standard rewrite rules. Establish `hwT : w ∈ T` using `Finset.mem_union_left _ (Finset.mem_insert_self _ _)`. Take `⟨b, hb⟩` from `IsDedekindDomain.exists_forall_sub_mem_ideal (s := T) (fun v => v.asIdeal) (fun v => if v = w then E w + 1 else E v) (fun v _ => v.prime) (fun v _ u _ h h' => h (HeightOneSpectrum.ext h')) (fun v => if (v : HeightOneSpectrum (𝓞 K)) = w then π ^ E w else 0)`. Establish `hbw` using `hb w hwT`.

Simplify using `only [if_true] at hbw`. Establish `hπE : π ^ E w ∈ w.asIdeal ^ E w` using `(w.intValuation_le_pow_iff_mem _ _).1 (le_of_eq (hπpow _))`. Establish `hπE1 : π ^ E w ∉ w.asIdeal ^ (E w + 1)`. Rewrite using `[← w.intValuation_le_pow_iff_mem, hπpow, WithZero.exp_le_exp]`. Use `push_cast`.

Use linear arithmetic over natural numbers and integers. Establish `hbw1 : b ∈ w.asIdeal ^ E w`. Use `Ideal.pow_le_pow_right (I := w.asIdeal) (Nat.le_succ (E w)) hbw` as an intermediate fact. Simplify using `using add_mem this hπE`. Establish `hbw2 : b ∉ w.asIdeal ^ (E w + 1)` using `fun h => hπE1 (by simpa using sub_mem h hbw)`.

Establish `hb0 : b ≠ 0` using `by rintro rfl; exact hbw2 (Submodule.zero_mem _)`. Establish `hbK : (b : K) ≠ 0` using `by exact_mod_cast hb0`. Establish `hvw : vAdd w (b : K) = E w`. Establish `h1` using `(mem_pow_iff w hb0 _).1 hbw1`. Establish `h2` using `mt (mem_pow_iff w hb0 (E w + 1)).2 hbw2`.

Move the coercions through the operations in `at h2`. Use linear arithmetic over natural numbers and integers. Establish `hball : ∀ v, (E v : ℤ) ≤ vAdd v (b : K)`. Introduce `v`. Distinguish the cases in `hv : v ∈ T`.

Distinguish the cases in `hvw' : v = w`. Substitute `hvw'` using the available equality. Rewrite using `[hvw]`. Use `hb v hv` as an intermediate fact. Simplify using `only [hvw', if_false, sub_zero] at this`.

Conclude with `(mem_pow_iff v hb0 _).1 this`. Establish `hvS : v ∉ S` using `fun h => hv (Finset.mem_union_left _ h)`. Establish `hρv : ρ v = 0`. Assume the negation of the conclusion as `h`. Conclude with `hvS (Finset.mem_insert_of_mem (hρ.mem_toFinset.2 h))`.

Establish `hcv : vAdd v (c : K) = 0`. Assume the negation of the conclusion as `h`. Conclude with `hv (Finset.mem_union_right _ (hfc.mem_toFinset.2 (by simpa using h)))`. Establish `: E v = 0` using `by simp [hE, hρv, hcv]`. Rewrite using `[this]; exact (mem_pow_iff v hb0 0).1 (by simp)`.

Use `⟨(b : K) / c, div_ne_zero hbK hcK, ?_, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[vAdd_div w hbK hcK, hvw]`. Use `hcS w (Finset.mem_insert_self _ _)` as an intermediate fact. Establish `h6 : ((E w : ℕ) : ℤ) = -⌊ρ w⌋ + vAdd w (c : K)` using `Int.toNat_of_nonneg this`. Rewrite using `[h6]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[vAdd_div v hbK hcK]`. Establish `h1` using `hball v`. Establish `h2 : -⌊ρ v⌋ + vAdd v (c : K) ≤ ((E v : ℕ) : ℤ)` using `Int.self_le_toNat _`.

Establish `h3 : -⌊ρ v⌋ ≤ vAdd v (b : K) - vAdd v (c : K)` using `by omega`. Establish `h4 : (⌊ρ v⌋ : ℝ) ≤ ρ v` using `Int.floor_le _`. Establish `h5 : ((-⌊ρ v⌋ : ℤ) : ℝ) ≤ ((vAdd v (b : K) - vAdd v (c : K) : ℤ) : ℝ)` using `by exact_mod_cast h3`. Move the coercions through the operations in `at h5 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_scal : ∀ (K : Type) [Field K] [NumberField K] (ρ : HeightOneSpectrum (𝓞 K) → ℝ),
    (Function.support ρ).Finite → ∀ w : HeightOneSpectrum (𝓞 K), ∃ a : K, a ≠ 0 ∧
      (vAdd w a : ℝ) = -(⌊ρ w⌋ : ℝ) ∧ ∀ w', 0 ≤ (vAdd w' a : ℝ) + ρ w' := by
  intro K _ _ ρ hρ w
  classical
  set S : Finset (HeightOneSpectrum (𝓞 K)) := insert w hρ.toFinset with hS

  have hne : ∀ v : HeightOneSpectrum (𝓞 K), ∃ e : 𝓞 K, e ∈ v.asIdeal ∧ e ≠ 0 := fun v =>
    Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  choose e he he0 using hne
  set N : ℕ := ∑ v ∈ S, (⌊ρ v⌋).toNat with hN
  set c : 𝓞 K := (∏ v ∈ S, e v) ^ N with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun v _ => he0 v)
  have hcK : (c : K) ≠ 0 := by exact_mod_cast hc0
  have hcS : ∀ v ∈ S, -⌊ρ v⌋ + vAdd v (c : K) ≥ 0 := by
    intro v hv
    have h1 : ∏ u ∈ S, e u ∈ v.asIdeal := by
      obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem e hv
      rw [ht]; exact Ideal.mul_mem_right _ _ (he v)
    have h2 : c ∈ v.asIdeal ^ N := Ideal.pow_mem_pow h1 N
    have h3 := (mem_pow_iff v hc0 N).1 h2
    have h4 : (⌊ρ v⌋).toNat ≤ N := Finset.single_le_sum (f := fun u => (⌊ρ u⌋).toNat)
      (fun _ _ => Nat.zero_le _) hv
    have h5 : ⌊ρ v⌋ ≤ ((⌊ρ v⌋).toNat : ℤ) := Int.self_le_toNat _
    omega
  have hfc := GlobalTheory.FlatLine.finite_vAdd hcK
  set T : Finset (HeightOneSpectrum (𝓞 K)) := S ∪ hfc.toFinset with hT
  set E : HeightOneSpectrum (𝓞 K) → ℕ := fun v => (-⌊ρ v⌋ + vAdd v (c : K)).toNat with hE
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  have hπpow : ∀ n : ℕ, w.intValuation (π ^ n) = WithZero.exp (-(n : ℤ)) := fun n => by
    rw [map_pow, hπ, ← WithZero.exp_nsmul]; congr 1; simp
  have hwT : w ∈ T := Finset.mem_union_left _ (Finset.mem_insert_self _ _)
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun v => v.asIdeal) (fun v => if v = w then E w + 1 else E v)
    (fun v _ => v.prime) (fun v _ u _ h h' => h (HeightOneSpectrum.ext h'))
    (fun v => if (v : HeightOneSpectrum (𝓞 K)) = w then π ^ E w else 0)
  have hbw := hb w hwT
  simp only [if_true] at hbw
  have hπE : π ^ E w ∈ w.asIdeal ^ E w := (w.intValuation_le_pow_iff_mem _ _).1 (le_of_eq (hπpow _))
  have hπE1 : π ^ E w ∉ w.asIdeal ^ (E w + 1) := by
    rw [← w.intValuation_le_pow_iff_mem, hπpow, WithZero.exp_le_exp]
    push_cast; omega
  have hbw1 : b ∈ w.asIdeal ^ E w := by
    have := Ideal.pow_le_pow_right (I := w.asIdeal) (Nat.le_succ (E w)) hbw
    simpa using add_mem this hπE
  have hbw2 : b ∉ w.asIdeal ^ (E w + 1) := fun h => hπE1 (by simpa using sub_mem h hbw)
  have hb0 : b ≠ 0 := by rintro rfl; exact hbw2 (Submodule.zero_mem _)
  have hbK : (b : K) ≠ 0 := by exact_mod_cast hb0
  have hvw : vAdd w (b : K) = E w := by
    have h1 := (mem_pow_iff w hb0 _).1 hbw1
    have h2 := mt (mem_pow_iff w hb0 (E w + 1)).2 hbw2
    push_cast at h2; omega
  have hball : ∀ v, (E v : ℤ) ≤ vAdd v (b : K) := by
    intro v
    by_cases hv : v ∈ T
    · by_cases hvw' : v = w
      · subst hvw'; rw [hvw]
      · have := hb v hv
        simp only [hvw', if_false, sub_zero] at this
        exact (mem_pow_iff v hb0 _).1 this
    · have hvS : v ∉ S := fun h => hv (Finset.mem_union_left _ h)
      have hρv : ρ v = 0 := by
        by_contra h; exact hvS (Finset.mem_insert_of_mem (hρ.mem_toFinset.2 h))
      have hcv : vAdd v (c : K) = 0 := by
        by_contra h
        exact hv (Finset.mem_union_right _ (hfc.mem_toFinset.2 (by simpa using h)))
      have : E v = 0 := by simp [hE, hρv, hcv]
      rw [this]; exact (mem_pow_iff v hb0 0).1 (by simp)
  refine ⟨(b : K) / c, div_ne_zero hbK hcK, ?_, fun v => ?_⟩
  · rw [vAdd_div w hbK hcK, hvw]
    have := hcS w (Finset.mem_insert_self _ _)
    have h6 : ((E w : ℕ) : ℤ) = -⌊ρ w⌋ + vAdd w (c : K) := Int.toNat_of_nonneg this
    rw [h6]; push_cast; ring
  · rw [vAdd_div v hbK hcK]
    have h1 := hball v
    have h2 : -⌊ρ v⌋ + vAdd v (c : K) ≤ ((E v : ℕ) : ℤ) := Int.self_le_toNat _
    have h3 : -⌊ρ v⌋ ≤ vAdd v (b : K) - vAdd v (c : K) := by omega
    have h4 : (⌊ρ v⌋ : ℝ) ≤ ρ v := Int.floor_le _
    have h5 : ((-⌊ρ v⌋ : ℤ) : ℝ) ≤ ((vAdd v (b : K) - vAdd v (c : K) : ℤ) : ℝ) := by exact_mod_cast h3
    push_cast at h5 ⊢
    linarith

end GlobalTheory.RefSum.ScalApprox

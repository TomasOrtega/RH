import Formalism.GaussValuationBounds.Statement
import Formalism.WindowSums.PowerSeriesRelationList

noncomputable section

namespace Formalism.NOK

open Polynomial

/- English proof (translation)
Take `⟨u, hu⟩ : ∃ u : ℤ_[ℓ]ˣ, x = (u : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ x.valuation` from `⟨_, PadicInt.unitCoeff_spec hx⟩`. Use `⟨((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]), ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_comm (u : ℤ_[ℓ]), mul_assoc, Units.mul_inv, mul_one]`. Use `_ = x * ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) := by rw [← hu]`.
-/
theorem padicInt_dvd_pow_valuation (ℓ : ℕ) [Fact ℓ.Prime] {x : ℤ_[ℓ]} (hx : x ≠ 0) :
    x ∣ (ℓ : ℤ_[ℓ]) ^ x.valuation := by
  obtain ⟨u, hu⟩ : ∃ u : ℤ_[ℓ]ˣ, x = (u : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ x.valuation :=
    ⟨_, PadicInt.unitCoeff_spec hx⟩
  refine ⟨((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]), ?_⟩
  calc (ℓ : ℤ_[ℓ]) ^ x.valuation
      = ((u : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ x.valuation) * ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) := by
        rw [mul_comm (u : ℤ_[ℓ]), mul_assoc, Units.mul_inv, mul_one]
    _ = x * ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) := by rw [← hu]

/- English proof (translation)
Establish `h` using `PadicInt.valuation_mul (Units.ne_zero u) (Units.ne_zero u⁻¹)`. Rewrite `h` using `[Units.mul_inv, PadicInt.valuation_one]`. Use linear arithmetic over natural numbers and integers.
-/
theorem padicInt_valuation_unit (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) :
    (u : ℤ_[ℓ]).valuation = 0 := by
  have h := PadicInt.valuation_mul (Units.ne_zero u) (Units.ne_zero u⁻¹)
  rw [Units.mul_inv, PadicInt.valuation_one] at h
  omega

/- English proof (translation)
Introduce `ℓ _ hℓ χ hχ`. Establish `hZ` using `Formalism.WindowSums.arc_ZpowVal ℓ χ 1 le_rfl (fun h => absurd h hℓ) hχ`. Establish `hℓ0 : (ℓ : ℤ_[ℓ]) ≠ 0` using `by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero`. Establish `hdvd : ∀ j : ℤ, (ℓ : ℤ_[ℓ]) ∣ ((χ ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1`. Introduce `j`.

Distinguish the cases in `hj : j = 0`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Take `⟨hne, hv⟩` from `hZ (-j) (neg_ne_zero.2 hj)`. Rewrite using `[PadicInt.unitCoeff_spec hne]`.

Conclude with `Dvd.dvd.mul_left (dvd_pow_self _ (by rw [hv]; omega)) _`. Use `choose d hd using hdvd`. Establish `hc1 : ∀ j, -(ℓ : ℤ_[ℓ]) * (-d j) = ((χ ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1`. Introduce `j`. Rewrite using `[hd j]`.

Expand and normalize the polynomial expressions, which then agree. Establish `key : ∀ j j' : ℤ, j ≠ j' → -d j' - -d j ≠ 0 ∧ PadicInt.valuation (-d j' - -d j) = padicValInt ℓ (j' - j)`. Introduce `j j' hjj`. Establish `hid : χ ^ (-j) = χ ^ (-j') * χ ^ (j' - j)`. Rewrite using `[← zpow_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hkey : (ℓ : ℤ_[ℓ]) ^ 1 * (-d j' - -d j) = ((χ ^ (-j') : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * (((χ ^ (j' - j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1)`. Establish `e1` using `hd j`. Establish `e2` using `hd j'`.

Rewrite `e1` using `[hid, Units.val_mul]`. Take the linear combination `e2 - e1`. Take `⟨hne, hv⟩` from `hZ (j' - j) (sub_ne_zero.2 (Ne.symm hjj))`. Establish `hw : -d j' - -d j ≠ 0`. Introduce `h`.

Rewrite `hkey` using `[h, mul_zero]`. Conclude with `mul_ne_zero (Units.ne_zero _) hne hkey.symm`. Use `⟨hw, ?_⟩` and prove the remaining obligations. Establish `h1` using `PadicInt.valuation_p_pow_mul 1 (-d j' - -d j) hw`. Rewrite `h1` using `[hkey, PadicInt.valuation_mul (Units.ne_zero _) hne, padicInt_valuation_unit, hv]`.

Use linear arithmetic over natural numbers and integers. Use `⟨fun j => -d j, hc1, ?_, fun j j' h => key j' j (Ne.symm h)⟩` and prove the remaining obligations. Establish `h0 : (ℓ : ℤ_[ℓ]) * d 0 = 0`. Rewrite using `[← hd 0]`. Simplify using the standard rewrite rules.

Use `show -d 0 = 0`. Rewrite using `[neg_eq_zero]`. Conclude with `(mul_eq_zero.1 h0).resolve_left hℓ0`.
-/
theorem cjExist_proof : CjExist := by
  intro ℓ _ hℓ χ hχ
  have hZ := Formalism.WindowSums.arc_ZpowVal ℓ χ 1 le_rfl (fun h => absurd h hℓ) hχ
  have hℓ0 : (ℓ : ℤ_[ℓ]) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  have hdvd : ∀ j : ℤ, (ℓ : ℤ_[ℓ]) ∣ ((χ ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 := by
    intro j
    by_cases hj : j = 0
    · subst hj
      simp
    · obtain ⟨hne, hv⟩ := hZ (-j) (neg_ne_zero.2 hj)
      rw [PadicInt.unitCoeff_spec hne]
      exact Dvd.dvd.mul_left (dvd_pow_self _ (by rw [hv]; omega)) _
  choose d hd using hdvd
  have hc1 : ∀ j, -(ℓ : ℤ_[ℓ]) * (-d j) = ((χ ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 := by
    intro j
    rw [hd j]
    ring
  have key : ∀ j j' : ℤ, j ≠ j' → -d j' - -d j ≠ 0 ∧
      PadicInt.valuation (-d j' - -d j) = padicValInt ℓ (j' - j) := by
    intro j j' hjj
    have hid : χ ^ (-j) = χ ^ (-j') * χ ^ (j' - j) := by
      rw [← zpow_add]
      congr 1
      ring
    have hkey : (ℓ : ℤ_[ℓ]) ^ 1 * (-d j' - -d j) =
        ((χ ^ (-j') : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * (((χ ^ (j' - j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) := by
      have e1 := hd j
      have e2 := hd j'
      rw [hid, Units.val_mul] at e1
      linear_combination e2 - e1
    obtain ⟨hne, hv⟩ := hZ (j' - j) (sub_ne_zero.2 (Ne.symm hjj))
    have hw : -d j' - -d j ≠ 0 := by
      intro h
      rw [h, mul_zero] at hkey
      exact mul_ne_zero (Units.ne_zero _) hne hkey.symm
    refine ⟨hw, ?_⟩
    have h1 := PadicInt.valuation_p_pow_mul 1 (-d j' - -d j) hw
    rw [hkey, PadicInt.valuation_mul (Units.ne_zero _) hne, padicInt_valuation_unit, hv] at h1
    omega
  refine ⟨fun j => -d j, hc1, ?_, fun j j' h => key j' j (Ne.symm h)⟩
  have h0 : (ℓ : ℤ_[ℓ]) * d 0 = 0 := by
    rw [← hd 0]
    simp
  show -d 0 = 0
  rw [neg_eq_zero]
  exact (mul_eq_zero.1 h0).resolve_left hℓ0

/- English proof (translation)
Establish `hsub : R₁ ⊆ R₁ ∪ R₂` using `Finset.subset_union_left`. Establish `hinj : Set.InjOn c ((R₁ ∪ R₂ : Finset ℤ) : Set ℤ)`. Introduce `m _ m' _ h`. Assume the negation of the conclusion as `hne`. Conclude with `(hc m m' hne).1 (sub_eq_zero.2 h)`.

Use `Formalism.WindowSums.arc_Lagrange ℤ_[ℓ] V T (R₁ ∪ R₂) R₁ c ((ℓ : ℤ_[ℓ]) ^ E) x hsub hinj h1 ?_ ?_` and prove the remaining obligations. Rewrite using `[Finset.union_sdiff_cancel_left hdisj]`. Conclude with `h2`. Introduce `k hk`. Establish `hstep : (∏ m ∈ (R₁ ∪ R₂).erase k, (c k - c m)) ∣ (ℓ : ℤ_[ℓ]) ^ (∑ m ∈ (R₁ ∪ R₂).erase k, padicValInt ℓ (k - m))`.

Rewrite using `[← Finset.prod_pow_eq_pow_sum]`. Apply `Finset.prod_dvd_prod_of_dvd` to reduce the goal to its premises. Introduce `m hm`. Establish `hne : k ≠ m` using `(Finset.ne_of_mem_erase hm).symm`. Take `⟨h0, hv⟩` from `hc k m hne`.

Rewrite using `[← hv]`. Conclude with `padicInt_dvd_pow_valuation ℓ h0`. Use `hstep.trans (pow_dvd_pow _ ?_)` and prove the remaining obligations. Take `⟨j₀, -⟩` from `hwin k hk`. Set `g : ℤ → Fin J` to `fun m => if h : m ∈ R₁ ∪ R₂ then Classical.choose (hwin m h) else j₀`.

Establish `hg : ∀ m ∈ R₁ ∪ R₂, a (g m) ≤ m ∧ m < a (g m) + L (g m)`. Introduce `m hm`. Simplify using `only [g, dif_pos hm]`. Conclude with `Classical.choose_spec (hwin m hm)`. Rewrite using `[← Finset.sum_fiberwise ((R₁ ∪ R₂).erase k) g]`.

Establish `hj : ∀ j : Fin J, ((∑ m ∈ ((R₁ ∪ R₂).erase k).filter (fun m => g m = j), padicValInt ℓ (k - m) : ℕ) : ℝ) ≤ (L j : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D`. Introduce `j`. Establish `himg` using `Finset.sum_image (s := ((R₁ ∪ R₂).erase k).filter (fun m => g m = j)) (g := fun m : ℤ => k - m) (f := fun i => padicValInt ℓ i) (by intro x _ y _ h; simpa using h)`. Rewrite using `[← himg]`. Apply `Formalism.WindowSums.arc_WindowSum ℓ (k - a j - L j + 1) (L j) D` to reduce the goal to its premises.

Introduce `i hi`. Rewrite `hi` using `[Finset.mem_image]`. Take `⟨m, hm, rfl⟩` from `hi`. Rewrite `hm` using `[Finset.mem_filter]`. Take `⟨hm1, hm2⟩` from `hm`.

Establish `hw` using `hg m (Finset.mem_of_mem_erase hm1)`. Rewrite `hw` using `[hm2]`. Rewrite using `[Finset.mem_Ico]`. Use linear arithmetic over natural numbers and integers. Introduce `h0`.

Rewrite `h0` using `[Finset.mem_image]`. Take `⟨m, hm, hm0⟩` from `h0`. Use `Finset.ne_of_mem_erase (Finset.mem_filter.1 hm).1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce `i hi`.

Rewrite `hi` using `[Finset.mem_image]`. Take `⟨m, hm, rfl⟩` from `hi`. Conclude with `hD k hk m (Finset.mem_of_mem_erase (Finset.mem_filter.1 hm).1)`. Establish `hsum : ((∑ j, ∑ m ∈ ((R₁ ∪ R₂).erase k).filter (fun m => g m = j), padicValInt ℓ (k - m) : ℕ) : ℝ) ≤ E`. Rewrite using `[Nat.cast_sum]`.

Conclude with `(Finset.sum_le_sum fun j _ => hj j).trans hE`. Conclude with `hsum` after adjusting the coercions.
-/
theorem gapLagrange (ℓ : ℕ) [Fact ℓ.Prime] (V : Type) [AddCommGroup V] [Module ℤ_[ℓ] V]
    (T : Module.End ℤ_[ℓ] V) (c : ℤ → ℤ_[ℓ])
    (hc : ∀ j j', j ≠ j' → c j - c j' ≠ 0 ∧
      PadicInt.valuation (c j - c j') = padicValInt ℓ (j - j'))
    (R₁ R₂ : Finset ℤ) (x : V) (J : ℕ) (a : Fin J → ℤ) (L : Fin J → ℕ) (D E : ℕ)
    (hdisj : Disjoint R₁ R₂)
    (h1 : aeval T (∏ r ∈ R₁, (X - C (c r))) x = 0)
    (h2 : aeval T (∏ r ∈ R₂, (X - C (c r))) x = 0)
    (hwin : ∀ r ∈ R₁ ∪ R₂, ∃ j, a j ≤ r ∧ r < a j + L j)
    (hD : ∀ r ∈ R₁ ∪ R₂, ∀ r' ∈ R₁ ∪ R₂, |r - r'| ≤ D)
    (hE : (∑ j, ((L j : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D)) ≤ E) :
    ((ℓ : ℤ_[ℓ]) ^ E) • x = 0 := by
  have hsub : R₁ ⊆ R₁ ∪ R₂ := Finset.subset_union_left
  have hinj : Set.InjOn c ((R₁ ∪ R₂ : Finset ℤ) : Set ℤ) := by
    intro m _ m' _ h
    by_contra hne
    exact (hc m m' hne).1 (sub_eq_zero.2 h)
  refine Formalism.WindowSums.arc_Lagrange ℤ_[ℓ] V T (R₁ ∪ R₂) R₁ c ((ℓ : ℤ_[ℓ]) ^ E) x hsub hinj h1 ?_ ?_
  · rw [Finset.union_sdiff_cancel_left hdisj]
    exact h2
  · intro k hk
    have hstep : (∏ m ∈ (R₁ ∪ R₂).erase k, (c k - c m)) ∣
        (ℓ : ℤ_[ℓ]) ^ (∑ m ∈ (R₁ ∪ R₂).erase k, padicValInt ℓ (k - m)) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_dvd_prod_of_dvd
      intro m hm
      have hne : k ≠ m := (Finset.ne_of_mem_erase hm).symm
      obtain ⟨h0, hv⟩ := hc k m hne
      rw [← hv]
      exact padicInt_dvd_pow_valuation ℓ h0
    refine hstep.trans (pow_dvd_pow _ ?_)
    obtain ⟨j₀, -⟩ := hwin k hk
    let g : ℤ → Fin J := fun m =>
      if h : m ∈ R₁ ∪ R₂ then Classical.choose (hwin m h) else j₀
    have hg : ∀ m ∈ R₁ ∪ R₂, a (g m) ≤ m ∧ m < a (g m) + L (g m) := by
      intro m hm
      simp only [g, dif_pos hm]
      exact Classical.choose_spec (hwin m hm)
    rw [← Finset.sum_fiberwise ((R₁ ∪ R₂).erase k) g]
    have hj : ∀ j : Fin J,
        ((∑ m ∈ ((R₁ ∪ R₂).erase k).filter (fun m => g m = j), padicValInt ℓ (k - m) : ℕ) : ℝ)
          ≤ (L j : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D := by
      intro j
      have himg := Finset.sum_image (s := ((R₁ ∪ R₂).erase k).filter (fun m => g m = j))
        (g := fun m : ℤ => k - m) (f := fun i => padicValInt ℓ i)
        (by intro x _ y _ h; simpa using h)
      rw [← himg]
      apply Formalism.WindowSums.arc_WindowSum ℓ (k - a j - L j + 1) (L j) D
      · intro i hi
        rw [Finset.mem_image] at hi
        obtain ⟨m, hm, rfl⟩ := hi
        rw [Finset.mem_filter] at hm
        obtain ⟨hm1, hm2⟩ := hm
        have hw := hg m (Finset.mem_of_mem_erase hm1)
        rw [hm2] at hw
        rw [Finset.mem_Ico]
        omega
      · intro h0
        rw [Finset.mem_image] at h0
        obtain ⟨m, hm, hm0⟩ := h0
        have := Finset.ne_of_mem_erase (Finset.mem_filter.1 hm).1
        omega
      · intro i hi
        rw [Finset.mem_image] at hi
        obtain ⟨m, hm, rfl⟩ := hi
        exact hD k hk m (Finset.mem_of_mem_erase (Finset.mem_filter.1 hm).1)
    have hsum : ((∑ j, ∑ m ∈ ((R₁ ∪ R₂).erase k).filter (fun m => g m = j),
        padicValInt ℓ (k - m) : ℕ) : ℝ) ≤ E := by
      rw [Nat.cast_sum]
      exact (Finset.sum_le_sum fun j _ => hj j).trans hE
    exact_mod_cast hsum

/- English proof (translation)
Introduce `ℓ _ V _ _ T c hc a S η b E R₁ R₂ x hb hR₁ hR₂ h1 h2 hE`. Establish `m1 : ∀ r ∈ R₁, (b : ℤ) - S - a + 1 ≤ r ∧ r ≤ b` using `fun r hr => Finset.mem_Icc.1 (hR₁ hr)`. Establish `m2 : ∀ r ∈ R₂, ((b : ℤ) + 1 ≤ r ∧ r ≤ b + S + a) ∨ (1 - (η : ℤ) ≤ r ∧ r ≤ η + a)`. Introduce `r hr`. Simplify `hR₂ hr` using `only [Finset.mem_union, Finset.mem_Icc]`.

Establish `hall : ∀ r ∈ R₁ ∪ R₂, 1 - (η : ℤ) ≤ r ∧ r ≤ b + S + a`. Introduce `r hr`. Break down `Finset.mem_union.1 hr with hr | hr` into its components or cases. Use `m1 r hr` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `m2 r hr` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `gapLagrange ℓ V T c hc R₁ R₂ x 2 ![(b : ℤ) - S - a + 1, 1 - η] ![2 * S + 2 * a, 2 * η + a] (b + S + a + η) E ?_ h1 h2 ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[Finset.disjoint_left]`. Introduce `r hr1 hr2`.

Use `m1 r hr1` as an intermediate fact. Use `m2 r hr2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce `r hr`. Break down `Finset.mem_union.1 hr with hr | hr` into its components or cases.

Use `m1 r hr` as an intermediate fact. Use `⟨0, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.cons_val_zero]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers.

Break down `m2 r hr with h | h` into its components or cases. Use `⟨0, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.cons_val_zero]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers.

Use `⟨1, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.cons_val_one]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers. Introduce `r hr r' hr'`.

Use `hall r hr` as an intermediate fact. Use `hall r' hr'` as an intermediate fact. Rewrite using `[abs_le]`. Use `push_cast`. Apply the tactic sequence `constructor <;> omega`.

Simplify using `only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]`. Use `hE using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gaussValueContraction_proof_fact_bis : GapPure1 := by
  intro ℓ _ V _ _ T c hc a S η b E R₁ R₂ x hb hR₁ hR₂ h1 h2 hE
  have m1 : ∀ r ∈ R₁, (b : ℤ) - S - a + 1 ≤ r ∧ r ≤ b := fun r hr => Finset.mem_Icc.1 (hR₁ hr)
  have m2 : ∀ r ∈ R₂, ((b : ℤ) + 1 ≤ r ∧ r ≤ b + S + a) ∨ (1 - (η : ℤ) ≤ r ∧ r ≤ η + a) := by
    intro r hr
    simpa only [Finset.mem_union, Finset.mem_Icc] using hR₂ hr
  have hall : ∀ r ∈ R₁ ∪ R₂, 1 - (η : ℤ) ≤ r ∧ r ≤ b + S + a := by
    intro r hr
    rcases Finset.mem_union.1 hr with hr | hr
    · have := m1 r hr
      omega
    · have := m2 r hr
      omega
  refine gapLagrange ℓ V T c hc R₁ R₂ x 2 ![(b : ℤ) - S - a + 1, 1 - η] ![2 * S + 2 * a, 2 * η + a]
    (b + S + a + η) E ?_ h1 h2 ?_ ?_ ?_
  · rw [Finset.disjoint_left]
    intro r hr1 hr2
    have := m1 r hr1
    have := m2 r hr2
    omega
  · intro r hr
    rcases Finset.mem_union.1 hr with hr | hr
    · have := m1 r hr
      refine ⟨0, ?_⟩
      simp only [Matrix.cons_val_zero]
      push_cast
      omega
    · rcases m2 r hr with h | h
      · refine ⟨0, ?_⟩
        simp only [Matrix.cons_val_zero]
        push_cast
        omega
      · refine ⟨1, ?_⟩
        simp only [Matrix.cons_val_one]
        push_cast
        omega
  · intro r hr r' hr'
    have := hall r hr
    have := hall r' hr'
    rw [abs_le]
    push_cast
    constructor <;> omega
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    convert hE using 1
    push_cast
    ring

/- English proof (translation)
Introduce `ℓ _ V _ _ T c hc a S b E R₁ x hab hR₁ h1 h2 hE`. Establish `m1 : ∀ r ∈ R₁, (1 ≤ r ∧ r ≤ (a : ℤ)) ∨ (-(b : ℤ) - S + 1 ≤ r ∧ r ≤ -(b : ℤ) + a)`. Introduce `r hr`. Simplify `hR₁ hr` using `only [Finset.mem_union, Finset.mem_Icc]`. Establish `h1' : aeval T (∏ j ∈ ({0} : Finset ℤ), (X - C (c j))) x = 0`.

Rewrite using `[Finset.prod_singleton]`. Conclude with `h1`. Establish `hall : ∀ r ∈ ({0} : Finset ℤ) ∪ R₁, -(b : ℤ) - S + 1 ≤ r ∧ r ≤ a`. Introduce `r hr`. Break down `Finset.mem_union.1 hr with hr | hr` into its components or cases.

Rewrite `hr` using `[Finset.mem_singleton]`. Use linear arithmetic over natural numbers and integers. Use `m1 r hr` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `gapLagrange ℓ V T c hc {0} R₁ x 2 ![0, -(b : ℤ) - S + 1] ![a + 1, S + a] (b + S + a) E ?_ h1' h2 ?_ ?_ ?_` and prove the remaining obligations.

Rewrite using `[Finset.disjoint_singleton_left]`. Introduce `h0`. Use `m1 0 h0` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce `r hr`.

Break down `Finset.mem_union.1 hr with hr | hr` into its components or cases. Rewrite `hr` using `[Finset.mem_singleton]`. Use `⟨0, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.cons_val_zero]`. Use `push_cast`.

Use linear arithmetic over natural numbers and integers. Break down `m1 r hr with h | h` into its components or cases. Use `⟨0, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.cons_val_zero]`. Use `push_cast`.

Use linear arithmetic over natural numbers and integers. Use `⟨1, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.cons_val_one]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers.

Introduce `r hr r' hr'`. Use `hall r hr` as an intermediate fact. Use `hall r' hr'` as an intermediate fact. Rewrite using `[abs_le]`. Use `push_cast`.

Apply the tactic sequence `constructor <;> omega`. Simplify using `only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]`. Use `hE using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gaussValueContraction_proof_fact_alt : GapPure2 := by
  intro ℓ _ V _ _ T c hc a S b E R₁ x hab hR₁ h1 h2 hE
  have m1 : ∀ r ∈ R₁, (1 ≤ r ∧ r ≤ (a : ℤ)) ∨ (-(b : ℤ) - S + 1 ≤ r ∧ r ≤ -(b : ℤ) + a) := by
    intro r hr
    simpa only [Finset.mem_union, Finset.mem_Icc] using hR₁ hr
  have h1' : aeval T (∏ j ∈ ({0} : Finset ℤ), (X - C (c j))) x = 0 := by
    rw [Finset.prod_singleton]
    exact h1
  have hall : ∀ r ∈ ({0} : Finset ℤ) ∪ R₁, -(b : ℤ) - S + 1 ≤ r ∧ r ≤ a := by
    intro r hr
    rcases Finset.mem_union.1 hr with hr | hr
    · rw [Finset.mem_singleton] at hr
      omega
    · have := m1 r hr
      omega
  refine gapLagrange ℓ V T c hc {0} R₁ x 2 ![0, -(b : ℤ) - S + 1] ![a + 1, S + a]
    (b + S + a) E ?_ h1' h2 ?_ ?_ ?_
  · rw [Finset.disjoint_singleton_left]
    intro h0
    have := m1 0 h0
    omega
  · intro r hr
    rcases Finset.mem_union.1 hr with hr | hr
    · rw [Finset.mem_singleton] at hr
      refine ⟨0, ?_⟩
      simp only [Matrix.cons_val_zero]
      push_cast
      omega
    · rcases m1 r hr with h | h
      · refine ⟨0, ?_⟩
        simp only [Matrix.cons_val_zero]
        push_cast
        omega
      · refine ⟨1, ?_⟩
        simp only [Matrix.cons_val_one]
        push_cast
        omega
  · intro r hr r' hr'
    have := hall r hr
    have := hall r' hr'
    rw [abs_le]
    push_cast
    constructor <;> omega
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    convert hE using 1
    push_cast
    ring

end Formalism.NOK

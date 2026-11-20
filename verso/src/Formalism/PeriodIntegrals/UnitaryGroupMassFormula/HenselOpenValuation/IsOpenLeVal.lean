import Mathlib
import Formalism.PeriodIntegrals.Hensel

open ValuativeRel Polynomial Topology

namespace PI.HenselValuation

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
The claim follows from `(Valuation.mem_integer_iff _ _).mp x.2`.
-/
lemma val_le_one (x : 𝒪[F]) : valuation F (x : F) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).mp x.2

/- English proof (translation)
Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `x hx`. Establish `hx' : γ < valuation F x` using `hx`. Establish `hx0 : valuation F x ≠ 0` using `(lt_of_le_of_lt zero_le hx').ne'`. Rewrite using `[IsValuativeTopology.mem_nhds_iff']`.

Use `⟨Units.mk0 _ hx0, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hy' : valuation F (y - x) < valuation F x` using `by simpa using hy`. Use `show γ < valuation F y`. Rewrite using `[Valuation.map_eq_of_sub_lt _ hy']`. Conclude with `hx'`.
-/
lemma isOpen_lt_val (γ : ValueGroupWithZero F) : IsOpen {x : F | γ < valuation F x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hx' : γ < valuation F x := hx
  have hx0 : valuation F x ≠ 0 := (lt_of_le_of_lt zero_le hx').ne'
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 _ hx0, fun y hy => ?_⟩
  have hy' : valuation F (y - x) < valuation F x := by simpa using hy
  show γ < valuation F y
  rw [Valuation.map_eq_of_sub_lt _ hy']
  exact hx'

/- English proof (translation)
Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `x hx`. Establish `hx' : γ ≤ valuation F x` using `hx`. Establish `hx0 : valuation F x ≠ 0`. Introduce `h0`.

Rewrite `hx'` using `[h0]`. Conclude with `hγ (le_antisymm hx' zero_le)`. Rewrite using `[IsValuativeTopology.mem_nhds_iff']`. Use `⟨Units.mk0 _ hx0, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hy' : valuation F (y - x) < valuation F x` using `by simpa using hy`.

Use `show γ ≤ valuation F y`. Rewrite using `[Valuation.map_eq_of_sub_lt _ hy']`. Conclude with `hx'`.
-/
lemma isOpen_le_val {γ : ValueGroupWithZero F} (hγ : γ ≠ 0) :
    IsOpen {x : F | γ ≤ valuation F x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hx' : γ ≤ valuation F x := hx
  have hx0 : valuation F x ≠ 0 := by
    intro h0
    rw [h0] at hx'
    exact hγ (le_antisymm hx' zero_le)
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 _ hx0, fun y hy => ?_⟩
  have hy' : valuation F (y - x) < valuation F x := by simpa using hy
  show γ ≤ valuation F y
  rw [Valuation.map_eq_of_sub_lt _ hy']
  exact hx'

/- English proof (translation)
The claim follows from `continuous_subtype_val.comp f.continuous`.
-/
lemma continuous_eval (f : Polynomial 𝒪[F]) :
    Continuous fun y : 𝒪[F] => ((f.eval y : 𝒪[F]) : F) :=
  continuous_subtype_val.comp f.continuous

/- English proof (translation)
Establish `hc0 : valuation F ((f.derivative.eval a : 𝒪[F]) : F) ≠ 0` using `(lt_of_le_of_lt zero_le hba).ne'`. Take `⟨z, hz⟩` from `Polynomial.evalSubFactor f.derivative b a`. Establish `hdiff : ((f.derivative.eval b : 𝒪[F]) : F) - ((f.derivative.eval a : 𝒪[F]) : F) = (z : F) * ((b - a : 𝒪[F]) : F)`. Conclude with `congrArg Subtype.val hz` after adjusting the coercions. Establish `hdb : valuation F ((f.derivative.eval b : 𝒪[F]) : F) = valuation F ((f.derivative.eval a : 𝒪[F]) : F)`.

Apply `Valuation.map_eq_of_sub_lt` to reduce the goal to its premises. Rewrite using `[hdiff, Valuation.map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (val_le_one z)) hba`. Establish `hdb0 : ((f.derivative.eval b : 𝒪[F]) : F) ≠ 0`. Introduce `h0`.

Apply `hc0` to reduce the goal to its premises. Rewrite using `[← hdb, h0, Valuation.map_zero]`. Establish `hfb0 : ((f.eval b : 𝒪[F]) : F) ≠ 0`. Introduce `h0`. Conclude with `hne (by exact_mod_cast h0)`.

Take `⟨h, hh⟩ : ∃ h : F, h = -((f.eval b : 𝒪[F]) : F) / ((f.derivative.eval b : 𝒪[F]) : F)` from `⟨_, rfl⟩`. Establish `hhd : h * ((f.derivative.eval b : 𝒪[F]) : F) = -((f.eval b : 𝒪[F]) : F)`. Rewrite using `[hh, div_mul_cancel₀ _ hdb0]`. Establish `hvh : valuation F h * valuation F ((f.derivative.eval a : 𝒪[F]) : F) = valuation F ((f.eval b : 𝒪[F]) : F)`. Rewrite using `[← hdb, ← Valuation.map_mul, hhd, Valuation.map_neg]`.

Establish `hh0 : valuation F h ≠ 0`. Introduce `h0`. Rewrite `hvh` using `[h0, zero_mul]`. Conclude with `hfb0 ((Valuation.zero_iff _).mp hvh.symm)`. Establish `hhc : valuation F h < valuation F ((f.derivative.eval a : 𝒪[F]) : F)`.

Assume the negation of the conclusion as `hlt`. Establish `hle` using `not_lt.mp hlt`. Establish `hsq : valuation F ((f.derivative.eval a : 𝒪[F]) : F) ^ 2 ≤ valuation F ((f.eval b : 𝒪[F]) : F)`. Rewrite using `[pow_two, ← hvh]`. Conclude with `mul_le_mul' hle le_rfl`.

Conclude with `absurd hfb (not_lt.mpr hsq)`. Establish `hmem : h ∈ 𝒪[F]` using `(Valuation.mem_integer_iff _ _).mpr (hhc.le.trans (val_le_one _))`. Take `⟨hO, hcoe⟩ : ∃ hO : 𝒪[F], (hO : F) = h` from `⟨⟨h, hmem⟩, rfl⟩`. Take `⟨k, hk⟩` from `Polynomial.binomExpansion f b hO`. Establish `hk' : ((f.eval (b + hO) : 𝒪[F]) : F) = ((f.eval b : 𝒪[F]) : F) + ((f.derivative.eval b : 𝒪[F]) : F) * (hO : F) + (k : F) * (hO : F) ^ 2`.

Conclude with `congrArg Subtype.val hk` after adjusting the coercions. Rewrite `hk'` using `[hcoe]`. Use `⟨b + hO, ?_, ?_⟩` and prove the remaining obligations. Establish `hsum : ((b + hO - a : 𝒪[F]) : F) = ((b - a : 𝒪[F]) : F) + h`. Use `push_cast`.

Rewrite using `[hcoe]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsum]`. Conclude with `Valuation.map_add_lt _ hba hhc`. Establish `hval : ((f.eval (b + hO) : 𝒪[F]) : F) = (k : F) * h ^ 2`.

Rewrite using `[hk']`. Take the linear combination `hhd`. Rewrite using `[hval, Valuation.map_mul, Valuation.map_pow, ← hvh, pow_two]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem newton_step (f : Polynomial 𝒪[F]) (a b : 𝒪[F])
    (hba : valuation F ((b - a : 𝒪[F]) : F) < valuation F ((f.derivative.eval a : 𝒪[F]) : F))
    (hfb : valuation F ((f.eval b : 𝒪[F]) : F) <
      valuation F ((f.derivative.eval a : 𝒪[F]) : F) ^ 2)
    (hne : f.eval b ≠ 0) :
    ∃ b' : 𝒪[F], valuation F ((b' - a : 𝒪[F]) : F) <
        valuation F ((f.derivative.eval a : 𝒪[F]) : F) ∧
      valuation F ((f.eval b' : 𝒪[F]) : F) < valuation F ((f.eval b : 𝒪[F]) : F) := by
  have hc0 : valuation F ((f.derivative.eval a : 𝒪[F]) : F) ≠ 0 :=
    (lt_of_le_of_lt zero_le hba).ne'
  obtain ⟨z, hz⟩ := Polynomial.evalSubFactor f.derivative b a
  have hdiff : ((f.derivative.eval b : 𝒪[F]) : F) - ((f.derivative.eval a : 𝒪[F]) : F) =
      (z : F) * ((b - a : 𝒪[F]) : F) := by
    exact_mod_cast congrArg Subtype.val hz
  have hdb : valuation F ((f.derivative.eval b : 𝒪[F]) : F) =
      valuation F ((f.derivative.eval a : 𝒪[F]) : F) := by
    apply Valuation.map_eq_of_sub_lt
    rw [hdiff, Valuation.map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_le_one z)) hba
  have hdb0 : ((f.derivative.eval b : 𝒪[F]) : F) ≠ 0 := by
    intro h0
    apply hc0
    rw [← hdb, h0, Valuation.map_zero]
  have hfb0 : ((f.eval b : 𝒪[F]) : F) ≠ 0 := by
    intro h0
    exact hne (by exact_mod_cast h0)
  obtain ⟨h, hh⟩ : ∃ h : F, h = -((f.eval b : 𝒪[F]) : F) / ((f.derivative.eval b : 𝒪[F]) : F) :=
    ⟨_, rfl⟩
  have hhd : h * ((f.derivative.eval b : 𝒪[F]) : F) = -((f.eval b : 𝒪[F]) : F) := by
    rw [hh, div_mul_cancel₀ _ hdb0]
  have hvh : valuation F h * valuation F ((f.derivative.eval a : 𝒪[F]) : F) =
      valuation F ((f.eval b : 𝒪[F]) : F) := by
    rw [← hdb, ← Valuation.map_mul, hhd, Valuation.map_neg]
  have hh0 : valuation F h ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hvh
    exact hfb0 ((Valuation.zero_iff _).mp hvh.symm)
  have hhc : valuation F h < valuation F ((f.derivative.eval a : 𝒪[F]) : F) := by
    by_contra hlt
    have hle := not_lt.mp hlt
    have hsq : valuation F ((f.derivative.eval a : 𝒪[F]) : F) ^ 2 ≤
        valuation F ((f.eval b : 𝒪[F]) : F) := by
      rw [pow_two, ← hvh]
      exact mul_le_mul' hle le_rfl
    exact absurd hfb (not_lt.mpr hsq)
  have hmem : h ∈ 𝒪[F] := (Valuation.mem_integer_iff _ _).mpr
    (hhc.le.trans (val_le_one _))
  obtain ⟨hO, hcoe⟩ : ∃ hO : 𝒪[F], (hO : F) = h := ⟨⟨h, hmem⟩, rfl⟩
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion f b hO
  have hk' : ((f.eval (b + hO) : 𝒪[F]) : F) = ((f.eval b : 𝒪[F]) : F) +
      ((f.derivative.eval b : 𝒪[F]) : F) * (hO : F) + (k : F) * (hO : F) ^ 2 := by
    exact_mod_cast congrArg Subtype.val hk
  rw [hcoe] at hk'
  refine ⟨b + hO, ?_, ?_⟩
  · have hsum : ((b + hO - a : 𝒪[F]) : F) = ((b - a : 𝒪[F]) : F) + h := by
      push_cast
      rw [hcoe]
      ring
    rw [hsum]
    exact Valuation.map_add_lt _ hba hhc
  · have hval : ((f.eval (b + hO) : 𝒪[F]) : F) = (k : F) * h ^ 2 := by
      rw [hk']
      linear_combination hhd
    rw [hval, Valuation.map_mul, Valuation.map_pow, ← hvh, pow_two]
    calc valuation F (k : F) * (valuation F h * valuation F h)
        ≤ valuation F h * valuation F h :=
          mul_le_of_le_one_left' (val_le_one k)
      _ < valuation F h * valuation F ((f.derivative.eval a : 𝒪[F]) : F) :=
          mul_lt_mul_of_pos_left hhc (lt_of_le_of_ne zero_le (Ne.symm hh0))

/- English proof (translation)
Establish `hg : Continuous fun b : 𝒪[F] => ((b - a : 𝒪[F]) : F)` using `continuous_subtype_val.comp (continuous_id.sub continuous_const)`. Establish `h1 : IsClosed {b : 𝒪[F] | valuation F ((b - a : 𝒪[F]) : F) < valuation F ((f.derivative.eval a : 𝒪[F]) : F)}`. Establish `hc` using `((isOpen_le_val hc0).preimage hg).isClosed_compl`. Use `hc using 1` and compare the differences between its conclusion and the goal. Use extensionality with `b`.

Simplify using `only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_preimage, not_le]`. Establish `h2 : IsClosed {b : 𝒪[F] | valuation F ((f.eval b : 𝒪[F]) : F) ≤ valuation F ((f.eval a : 𝒪[F]) : F)}`. Establish `hc` using `((isOpen_lt_val (valuation F ((f.eval a : 𝒪[F]) : F))).preimage (continuous_eval f)).isClosed_compl`. Use `hc using 1` and compare the differences between its conclusion and the goal. Use extensionality with `b`.

Simplify using `only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_preimage, not_lt]`. Conclude with `h1.inter h2`.
-/
lemma isClosed_S (f : Polynomial 𝒪[F]) (a : 𝒪[F]) (hc0 : valuation F ((f.derivative.eval a : 𝒪[F]) : F) ≠ 0) :
    IsClosed {b : 𝒪[F] | valuation F ((b - a : 𝒪[F]) : F) <
        valuation F ((f.derivative.eval a : 𝒪[F]) : F) ∧
      valuation F ((f.eval b : 𝒪[F]) : F) ≤ valuation F ((f.eval a : 𝒪[F]) : F)} := by
  have hg : Continuous fun b : 𝒪[F] => ((b - a : 𝒪[F]) : F) :=
    continuous_subtype_val.comp (continuous_id.sub continuous_const)
  have h1 : IsClosed {b : 𝒪[F] | valuation F ((b - a : 𝒪[F]) : F) <
      valuation F ((f.derivative.eval a : 𝒪[F]) : F)} := by
    have hc := ((isOpen_le_val hc0).preimage hg).isClosed_compl
    convert hc using 1
    ext b
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_preimage, not_le]
  have h2 : IsClosed {b : 𝒪[F] | valuation F ((f.eval b : 𝒪[F]) : F) ≤
      valuation F ((f.eval a : 𝒪[F]) : F)} := by
    have hc := ((isOpen_lt_val (valuation F ((f.eval a : 𝒪[F]) : F))).preimage
      (continuous_eval f)).isClosed_compl
    convert hc using 1
    ext b
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_preimage, not_lt]
  exact h1.inter h2

/- English proof (translation)
Unfold `PI.HenselStrong`. Introduce `F _ _ _ _ f a hfa`. Establish `hc0 : valuation F ((f.derivative.eval a : 𝒪[F]) : F) ≠ 0`. Introduce `h0`. Rewrite `hfa` using `[h0, zero_pow two_ne_zero]`.

Conclude with `not_lt_zero hfa`. Assume the negation of the conclusion as `hno`. Establish `hS` using `(isClosed_S f a hc0).isCompact`. Establish `step : ∀ b ∈ {b : 𝒪[F] | valuation F ((b - a : 𝒪[F]) : F) < valuation F ((f.derivative.eval a : 𝒪[F]) : F) ∧ valuation F ((f.eval b : 𝒪[F]) : F) ≤ valuation F ((f.eval a : 𝒪[F]) : F)}, ∃ b' ∈ {b : 𝒪[F] | valuation F ((b - a : 𝒪[F]) : F) < valuation F ((f.derivative.eval a : 𝒪[F]) …`. Introduce `b hb`.

Establish `hne : f.eval b ≠ 0` using `fun h0 => hno ⟨b, h0, hb.1⟩`. Take `⟨b', h1, h2⟩` from `newton_step f a b hb.1 (lt_of_le_of_lt hb.2 hfa) hne`. Conclude with `⟨b', ⟨h1, h2.le.trans hb.2⟩, h2⟩`. Take `⟨t, htS, htfin, hcov⟩` from `hS.elim_finite_subcover_image (b := {b : 𝒪[F] | valuation F ((b - a : 𝒪[F]) : F) < valuation F ((f.derivative.eval a : 𝒪[F]) : F) ∧ valuation F ((f.eval b : 𝒪[F]) : F) ≤ valuation F ((f.eval a : 𝒪[F]) : F)}) (c := fun b => {x : 𝒪[F] | valuation F ((f.eval b : 𝒪[F]) : F) < valuati …`. Take `⟨x', hx', hlt⟩` from `step x hx`.

Conclude with `Set.mem_biUnion hx' hlt)`. Establish `haS : a ∈ {b : 𝒪[F] | valuation F ((b - a : 𝒪[F]) : F) < valuation F ((f.derivative.eval a : 𝒪[F]) : F) ∧ valuation F ((f.eval b : 𝒪[F]) : F) ≤ valuation F ((f.eval a : 𝒪[F]) : F)}`. Use `⟨?_, le_rfl⟩` and prove the remaining obligations. Establish `h00 : ((a - a : 𝒪[F]) : F) = 0` using `by simp`. Rewrite using `[h00, Valuation.map_zero]`.

Conclude with `lt_of_le_of_ne zero_le (Ne.symm hc0)`. Take `⟨i, hi, -⟩` from `Set.mem_iUnion₂.mp (hcov haS)`. Take `⟨m, hmt, hmin⟩` from `Set.exists_min_image t (fun b => valuation F ((f.eval b : 𝒪[F]) : F)) htfin ⟨i, hi⟩`. Take `⟨j, hjt, hj⟩` from `Set.mem_iUnion₂.mp (hcov (htS hmt))`. Conclude with `absurd (hmin j hjt) (not_le.mpr hj)`.
-/
theorem henselStrong : PI.HenselStrong := by
  unfold PI.HenselStrong
  intro F _ _ _ _ f a hfa
  have hc0 : valuation F ((f.derivative.eval a : 𝒪[F]) : F) ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hfa
    exact not_lt_zero hfa
  by_contra hno
  have hS := (isClosed_S f a hc0).isCompact
  have step : ∀ b ∈ {b : 𝒪[F] | valuation F ((b - a : 𝒪[F]) : F) <
        valuation F ((f.derivative.eval a : 𝒪[F]) : F) ∧
      valuation F ((f.eval b : 𝒪[F]) : F) ≤ valuation F ((f.eval a : 𝒪[F]) : F)},
      ∃ b' ∈ {b : 𝒪[F] | valuation F ((b - a : 𝒪[F]) : F) <
        valuation F ((f.derivative.eval a : 𝒪[F]) : F) ∧
      valuation F ((f.eval b : 𝒪[F]) : F) ≤ valuation F ((f.eval a : 𝒪[F]) : F)},
        valuation F ((f.eval b' : 𝒪[F]) : F) < valuation F ((f.eval b : 𝒪[F]) : F) := by
    intro b hb
    have hne : f.eval b ≠ 0 := fun h0 => hno ⟨b, h0, hb.1⟩
    obtain ⟨b', h1, h2⟩ := newton_step f a b hb.1 (lt_of_le_of_lt hb.2 hfa) hne
    exact ⟨b', ⟨h1, h2.le.trans hb.2⟩, h2⟩
  obtain ⟨t, htS, htfin, hcov⟩ := hS.elim_finite_subcover_image
    (b := {b : 𝒪[F] | valuation F ((b - a : 𝒪[F]) : F) <
        valuation F ((f.derivative.eval a : 𝒪[F]) : F) ∧
      valuation F ((f.eval b : 𝒪[F]) : F) ≤ valuation F ((f.eval a : 𝒪[F]) : F)})
    (c := fun b => {x : 𝒪[F] | valuation F ((f.eval b : 𝒪[F]) : F) <
      valuation F ((f.eval x : 𝒪[F]) : F)})
    (fun b _ => (isOpen_lt_val _).preimage (continuous_eval f))
    (fun x hx => by
      obtain ⟨x', hx', hlt⟩ := step x hx
      exact Set.mem_biUnion hx' hlt)
  have haS : a ∈ {b : 𝒪[F] | valuation F ((b - a : 𝒪[F]) : F) <
        valuation F ((f.derivative.eval a : 𝒪[F]) : F) ∧
      valuation F ((f.eval b : 𝒪[F]) : F) ≤ valuation F ((f.eval a : 𝒪[F]) : F)} := by
    refine ⟨?_, le_rfl⟩
    have h00 : ((a - a : 𝒪[F]) : F) = 0 := by simp
    rw [h00, Valuation.map_zero]
    exact lt_of_le_of_ne zero_le (Ne.symm hc0)
  obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.mp (hcov haS)
  obtain ⟨m, hmt, hmin⟩ := Set.exists_min_image t
    (fun b => valuation F ((f.eval b : 𝒪[F]) : F)) htfin ⟨i, hi⟩
  obtain ⟨j, hjt, hj⟩ := Set.mem_iUnion₂.mp (hcov (htS hmt))
  exact absurd (hmin j hjt) (not_le.mpr hj)

end PI.HenselValuation

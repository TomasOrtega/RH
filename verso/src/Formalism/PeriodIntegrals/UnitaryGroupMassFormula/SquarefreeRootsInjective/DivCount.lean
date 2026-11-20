import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootsInjective.ClaimOf

open Polynomial

noncomputable section

open Classical

namespace PI.SqfRootsInj.W

/- English proof (translation)
Use `set k := r - h.natDegree`. Set `φ : (ZMod g)[X] → (Fin k → ZMod g)` to `fun f i => (f /ₘ h).coeff i`. Establish `key : ∀ f ∈ T.filter (h ∣ ·), (f /ₘ h).Monic ∧ (f /ₘ h).natDegree = k ∧ h * (f /ₘ h) = f`. Introduce `f hf`. Rewrite `hf` using `[Finset.mem_filter]`.

Take `⟨hfT, hdv⟩` from `hf`. Take `⟨hm, hd⟩` from `hT f hfT`. Establish `e1 : h * (f /ₘ h) = f`. Use `modByMonic_add_div f h` as an intermediate fact. Rewrite `this` using `[(modByMonic_eq_zero_iff_dvd hh).2 hdv, zero_add]`.

Conclude with `this`. Use `⟨?_, ?_, e1⟩` and prove the remaining obligations. Establish `hm' : (h * (f /ₘ h)).Monic` using `by rw [e1]; exact hm`. Conclude with `hh.of_mul_monic_left hm'`. Rewrite using `[natDegree_divByMonic f hh, hd]`.

Establish `hinj : Set.InjOn φ (T.filter (h ∣ ·))`. Introduce `f hf f' hf' heq`. Take `⟨m1, d1, e1⟩` from `key f hf`. Take `⟨m2, d2, e2⟩` from `key f' hf'`. Establish `hq : f /ₘ h = f' /ₘ h`.

Use extensionality with `n`. Break down `lt_trichotomy n k with hn | hn | hn` into its components or cases. Conclude with `congrFun heq ⟨n, hn⟩`. Substitute `hn` using the available equality. Establish `a1` using `m1.coeff_natDegree`.

Establish `a2` using `m2.coeff_natDegree`. Rewrite `a1` using `[d1]`. Rewrite `a2` using `[d2]`. Rewrite using `[a1, a2]`. Rewrite using `[coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]`.

Rewrite using `[← e1, ← e2, hq]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem divCount {g : ℕ} [Fact g.Prime] (r : ℕ) (T : Finset (ZMod g)[X])
    (hT : ∀ f ∈ T, f.Monic ∧ f.natDegree = r) (h : (ZMod g)[X]) (hh : h.Monic) :
    (T.filter (h ∣ ·)).card ≤ g ^ (r - h.natDegree) := by
  classical
  set k := r - h.natDegree
  let φ : (ZMod g)[X] → (Fin k → ZMod g) := fun f i => (f /ₘ h).coeff i
  have key : ∀ f ∈ T.filter (h ∣ ·), (f /ₘ h).Monic ∧ (f /ₘ h).natDegree = k ∧
      h * (f /ₘ h) = f := by
    intro f hf
    rw [Finset.mem_filter] at hf
    obtain ⟨hfT, hdv⟩ := hf
    obtain ⟨hm, hd⟩ := hT f hfT
    have e1 : h * (f /ₘ h) = f := by
      have := modByMonic_add_div f h
      rw [(modByMonic_eq_zero_iff_dvd hh).2 hdv, zero_add] at this
      exact this
    refine ⟨?_, ?_, e1⟩
    · have hm' : (h * (f /ₘ h)).Monic := by rw [e1]; exact hm
      exact hh.of_mul_monic_left hm'
    · rw [natDegree_divByMonic f hh, hd]
  have hinj : Set.InjOn φ (T.filter (h ∣ ·)) := by
    intro f hf f' hf' heq
    obtain ⟨m1, d1, e1⟩ := key f hf
    obtain ⟨m2, d2, e2⟩ := key f' hf'
    have hq : f /ₘ h = f' /ₘ h := by
      ext n
      rcases lt_trichotomy n k with hn | hn | hn
      · exact congrFun heq ⟨n, hn⟩
      · subst hn
        have a1 := m1.coeff_natDegree
        have a2 := m2.coeff_natDegree
        rw [d1] at a1; rw [d2] at a2
        rw [a1, a2]
      · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]
    rw [← e1, ← e2, hq]
  calc (T.filter (h ∣ ·)).card ≤ (Finset.univ : Finset (Fin k → ZMod g)).card :=
        Finset.card_le_card_of_injOn φ (fun _ _ => Finset.mem_univ _) hinj
    _ = g ^ k := by simp [ZMod.card]

end PI.SqfRootsInj.W

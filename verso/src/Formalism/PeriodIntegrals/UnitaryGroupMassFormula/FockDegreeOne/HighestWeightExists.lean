import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.CoeffXMulPderivSelf

noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FockOneDegW.HwC

open Classical in

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `u _ hu0 hcard`. It suffices to derive a contradiction.

Apply `hu0` to reduce the goal to its premises. Establish `h0` using `Nat.le_zero.1 hcard`. Rewrite `h0` using `[Finset.card_eq_zero, Finset.image_eq_empty]`. Conclude with `MvPolynomial.support_eq_empty.1 h0`. Consider the case `succ n ih`.

Introduce `u hu hu0 hcard`. Distinguish the cases in `hall : ∀ β₁ ∈ u.support, ∀ β₂ ∈ u.support, wtv β₁ = wtv β₂`. Take `⟨β₀, hβ₀⟩` from `Finset.nonempty_iff_ne_empty.2 (fun h => hu0 (MvPolynomial.support_eq_empty.1 h))`. Conclude with `⟨wtv β₀, u, hu, hu0, fun β hβ c => by rw [hall β hβ β₀ hβ₀], subset_rfl⟩`. Use `push_neg at hall`.

Take `⟨β₁, h₁, β₂, h₂, hne⟩` from `hall`. Take `⟨c, hc⟩` from `Function.ne_iff.1 hne`. Establish `hcoeff : ∀ β, coeff β (fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u) = (((wtv β c : ℚ) : ℂ) - ((wtv β₁ c : ℚ) : ℂ)) * coeff β u`. Introduce `β`. Rewrite using `[coeff_sub, coeff_Ecc, coeff_smul, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsub : (fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u).support ⊆ u.support`. Introduce `β hβ`. Rewrite `hβ`, the goal using `[MvPolynomial.mem_support_iff]`. Introduce `h0`.

Apply `hβ` to reduce the goal to its premises. Rewrite using `[hcoeff, h0, mul_zero]`. Establish `hmem : fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u ∈ U` using `U.sub_mem (hU c u hu) (U.smul_mem _ hu)`. Establish `hβ₂ : β₂ ∈ (fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u).support`. Rewrite using `[MvPolynomial.mem_support_iff, hcoeff]`.

Use `mul_ne_zero ?_ (MvPolynomial.mem_support_iff.1 h₂)` and prove the remaining obligations. Rewrite using `[sub_ne_zero]`. Conclude with `(Ne.symm hc)` after adjusting the coercions. Establish `hne0 : fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u ≠ 0`. Introduce `h`.

Rewrite `hβ₂` using `[h, MvPolynomial.support_zero]`. Simplify using `at hβ₂`. Establish `himg : (fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u).support.image wtv ⊆ (u.support.image wtv).erase (wtv β₁)`. Introduce `w hw`. Take `⟨β, hβ, rfl⟩` from `Finset.mem_image.1 hw`.

Use `Finset.mem_erase.2 ⟨fun heq => ?_, Finset.mem_image_of_mem _ (hsub hβ)⟩` and prove the remaining obligations. Establish `h0 : coeff β (fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u) = 0`. Rewrite using `[hcoeff, heq, sub_self, zero_mul]`. Conclude with `(MvPolynomial.mem_support_iff.1 hβ) h0`. Establish `hcard' : ((fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u).support.image wtv).card ≤ n`.

Establish `h1` using `Finset.card_le_card himg`. Establish `h2` using `Finset.card_erase_of_mem (Finset.mem_image_of_mem wtv h₁)`. Use linear arithmetic over natural numbers and integers. Take `⟨ν, v, hv, hv0, hvw, hvs⟩` from `ih _ hmem hne0 hcard'`. Conclude with `⟨ν, v, hv, hv0, hvw, hvs.trans hsub⟩`.
-/
theorem exists_wtvec {p q r s : ℕ} (U : Submodule ℂ (Pol p q r s))
    (hU : ∀ c : Ix p q, ∀ u ∈ U, fockAct1 p q r s (Eab c c) u ∈ U) :
    ∀ (n : ℕ) (u : Pol p q r s), u ∈ U → u ≠ 0 → (u.support.image wtv).card ≤ n →
      ∃ (ν : Ix p q → ℚ) (v : Pol p q r s), v ∈ U ∧ v ≠ 0 ∧ IsWt ν v ∧ v.support ⊆ u.support := by
  intro n
  induction n with
  | zero =>
    intro u _ hu0 hcard
    exfalso
    apply hu0
    have h0 := Nat.le_zero.1 hcard
    rw [Finset.card_eq_zero, Finset.image_eq_empty] at h0
    exact MvPolynomial.support_eq_empty.1 h0
  | succ n ih =>
    intro u hu hu0 hcard
    by_cases hall : ∀ β₁ ∈ u.support, ∀ β₂ ∈ u.support, wtv β₁ = wtv β₂
    · obtain ⟨β₀, hβ₀⟩ := Finset.nonempty_iff_ne_empty.2 (fun h => hu0 (MvPolynomial.support_eq_empty.1 h))
      exact ⟨wtv β₀, u, hu, hu0, fun β hβ c => by rw [hall β hβ β₀ hβ₀], subset_rfl⟩
    · push_neg at hall
      obtain ⟨β₁, h₁, β₂, h₂, hne⟩ := hall
      obtain ⟨c, hc⟩ := Function.ne_iff.1 hne

      have hcoeff : ∀ β, coeff β (fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u) =
          (((wtv β c : ℚ) : ℂ) - ((wtv β₁ c : ℚ) : ℂ)) * coeff β u := by
        intro β
        rw [coeff_sub, coeff_Ecc, coeff_smul, smul_eq_mul]
        ring
      have hsub : (fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u).support ⊆ u.support := by
        intro β hβ
        rw [MvPolynomial.mem_support_iff] at hβ ⊢
        intro h0
        apply hβ
        rw [hcoeff, h0, mul_zero]
      have hmem : fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u ∈ U :=
        U.sub_mem (hU c u hu) (U.smul_mem _ hu)
      have hβ₂ : β₂ ∈ (fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u).support := by
        rw [MvPolynomial.mem_support_iff, hcoeff]
        refine mul_ne_zero ?_ (MvPolynomial.mem_support_iff.1 h₂)
        rw [sub_ne_zero]
        exact_mod_cast (Ne.symm hc)
      have hne0 : fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u ≠ 0 := by
        intro h
        rw [h, MvPolynomial.support_zero] at hβ₂
        simp at hβ₂
      have himg : (fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u).support.image wtv ⊆
          (u.support.image wtv).erase (wtv β₁) := by
        intro w hw
        obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hw
        refine Finset.mem_erase.2 ⟨fun heq => ?_, Finset.mem_image_of_mem _ (hsub hβ)⟩
        have h0 : coeff β (fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u) = 0 := by
          rw [hcoeff, heq, sub_self, zero_mul]
        exact (MvPolynomial.mem_support_iff.1 hβ) h0
      have hcard' : ((fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u).support.image wtv).card ≤ n := by
        have h1 := Finset.card_le_card himg
        have h2 := Finset.card_erase_of_mem (Finset.mem_image_of_mem wtv h₁)
        omega
      obtain ⟨ν, v, hv, hv0, hvw, hvs⟩ := ih _ hmem hne0 hcard'
      exact ⟨ν, v, hv, hv0, hvw, hvs.trans hsub⟩

/- English proof (translation)
Set `bs` to `Module.finBasis ℂ U`. Use `⟨Finset.univ.biUnion fun k => ((bs k : U) : Pol p q r s).support, fun u hu => ?_⟩` and prove the remaining obligations. Establish `e : (⟨u, hu⟩ : U) = ∑ k, (bs.repr ⟨u, hu⟩ k) • bs k` using `(bs.sum_repr _).symm`. Establish `e' : u = ∑ k, (bs.repr ⟨u, hu⟩ k) • ((bs k : U) : Pol p q r s)`. Establish `h` using `congrArg Subtype.val e`.

Rewrite `h` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul] at h`. Conclude with `h`. Rewrite using `[e']`. Conclude with `MvPolynomial.support_sum.trans (Finset.biUnion_mono fun k _ => MvPolynomial.support_smul)`.
-/
theorem exists_cover {p q r s : ℕ} (U : Submodule ℂ (Pol p q r s)) [FiniteDimensional ℂ U] :
    ∃ S : Finset (Ln p q r s →₀ ℕ), ∀ u ∈ U, u.support ⊆ S := by
  classical
  let bs := Module.finBasis ℂ U
  refine ⟨Finset.univ.biUnion fun k => ((bs k : U) : Pol p q r s).support, fun u hu => ?_⟩
  have e : (⟨u, hu⟩ : U) = ∑ k, (bs.repr ⟨u, hu⟩ k) • bs k := (bs.sum_repr _).symm
  have e' : u = ∑ k, (bs.repr ⟨u, hu⟩ k) • ((bs k : U) : Pol p q r s) := by
    have h := congrArg Subtype.val e
    rw [Submodule.coe_sum] at h
    simp only [Submodule.coe_smul] at h
    exact h
  rw [e']
  exact MvPolynomial.support_sum.trans (Finset.biUnion_mono fun k _ => MvPolynomial.support_smul)

def tw {p q : ℕ} : Ix p q → ℚ
  | .inl i => -((i : ℕ) : ℚ)
  | .inr j => -((j : ℕ) : ℚ)

def fw {p q : ℕ} (ν : Ix p q → ℚ) : ℚ := ∑ c, tw c * ν c

/- English proof (translation)
Unfold `fw`. Simplify using `only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
-/
theorem fw_shift {p q : ℕ} (ν : Ix p q → ℚ) (a b : Ix p q) :
    fw (fun c => ν c + (if a = c then 1 else 0) - (if b = c then 1 else 0)) =
      fw ν + tw a - tw b := by
  unfold fw
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/- English proof (translation)
Apply the tactic sequence `rcases a with i | i <;> rcases b with j | j <;> simp only [posC] at h`. Use `⟨trivial, fun e => (ne_of_lt h) (Sum.inl.inj e), ?_⟩` and prove the remaining obligations. Establish `h' : (i : ℕ) < j` using `h`. Use `show -((j : ℕ) : ℚ) < -((i : ℕ) : ℚ)`. Conclude with `neg_lt_neg (by exact_mod_cast h')`.

Use `⟨trivial, fun e => (ne_of_lt h) (Sum.inr.inj e), ?_⟩` and prove the remaining obligations. Establish `h' : (i : ℕ) < j` using `h`. Use `show -((j : ℕ) : ℚ) < -((i : ℕ) : ℚ)`. Conclude with `neg_lt_neg (by exact_mod_cast h')`.
-/
theorem posC_facts {p q : ℕ} {a b : Ix p q} (h : posC a b) :
    sameBlock a b ∧ a ≠ b ∧ tw b < tw a := by
  rcases a with i | i <;> rcases b with j | j <;> simp only [posC] at h
  · refine ⟨trivial, fun e => (ne_of_lt h) (Sum.inl.inj e), ?_⟩
    have h' : (i : ℕ) < j := h
    show -((j : ℕ) : ℚ) < -((i : ℕ) : ℚ)
    exact neg_lt_neg (by exact_mod_cast h')
  · refine ⟨trivial, fun e => (ne_of_lt h) (Sum.inr.inj e), ?_⟩
    have h' : (i : ℕ) < j := h
    show -((j : ℕ) : ℚ) < -((i : ℕ) : ℚ)
    exact neg_lt_neg (by exact_mod_cast h')

end PI.FockOneDegW.HwC

namespace PI.FockOneDegW

open HwC

open Classical in
/- English proof (translation)
Introduce `p q r s U hfd hU0 hstab`. Use `haveI := hfd`. Take `⟨S, hS⟩` from `exists_cover U`. Apply the tactic sequence `have hdiag : ∀ c : Ix p q, ∀ u ∈ U, fockAct1 p q r s (Eab c c) u ∈ U := fun c => hstab c c (by cases c <;> trivial)`. Establish `hwtS : ∀ (ν : Ix p q → ℚ) (v : Pol p q r s), v ∈ U → v ≠ 0 → IsWt ν v → ν ∈ S.image wtv`.

Introduce `ν v hv hv0 hw`. Take `⟨β, hβ⟩` from `Finset.nonempty_iff_ne_empty.2 (fun h => hv0 (MvPolynomial.support_eq_empty.1 h))`. Conclude with `Finset.mem_image.2 ⟨β, hS v hv hβ, funext fun c => hw β hβ c⟩`. Establish `hT : ((S.image wtv).filter (fun ν => ∃ v ∈ U, v ≠ 0 ∧ IsWt ν v)).Nonempty`. Take `⟨u, hu, hu0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hU0`.

Take `⟨ν, v, hv, hv0, hvw, -⟩` from `exists_wtvec U hdiag _ u hu hu0 le_rfl`. Conclude with `⟨ν, Finset.mem_filter.2 ⟨hwtS ν v hv hv0 hvw, v, hv, hv0, hvw⟩⟩`. Take `⟨ν₀, hν₀, hmax⟩` from `Finset.exists_max_image _ fw hT`. Take `⟨-, v, hv, hv0, hvw⟩` from `Finset.mem_filter.1 hν₀`. Use `⟨ν₀, v, hv, ?_⟩` and prove the remaining obligations.

Unfold `IsHW hwSub`. Use `⟨hv0, Submodule.mem_inf.2 ⟨?_, ?_⟩⟩` and prove the remaining obligations. Simplify using `only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]`. Introduce `a`. Rewrite using `[Ecc_of_wt hvw a, sub_self]`.

Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker]`. Introduce `a b hab`. Take `⟨hsame, hne, htw⟩` from `posC_facts hab`. Assume the negation of the conclusion as `hw0`. Establish `hwU` using `hstab a b hsame v hv`.

Establish `hw'` using `wt_Eab_of hvw a b hsame hne`. Establish `hmemT : (fun c => ν₀ c + (if a = c then 1 else 0) - (if b = c then 1 else 0)) ∈ (S.image wtv).filter (fun ν => ∃ v ∈ U, v ≠ 0 ∧ IsWt ν v)` using `Finset.mem_filter.2 ⟨hwtS _ _ hwU hw0 hw', _, hwU, hw0, hw'⟩`. Establish `h1` using `hmax _ hmemT`. Rewrite `h1` using `[fw_shift]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hwExist : HwExist := by
  intro p q r s U hfd hU0 hstab
  haveI := hfd
  obtain ⟨S, hS⟩ := exists_cover U
  have hdiag : ∀ c : Ix p q, ∀ u ∈ U, fockAct1 p q r s (Eab c c) u ∈ U :=
    fun c => hstab c c (by cases c <;> trivial)

  have hwtS : ∀ (ν : Ix p q → ℚ) (v : Pol p q r s), v ∈ U → v ≠ 0 → IsWt ν v → ν ∈ S.image wtv := by
    intro ν v hv hv0 hw
    obtain ⟨β, hβ⟩ := Finset.nonempty_iff_ne_empty.2 (fun h => hv0 (MvPolynomial.support_eq_empty.1 h))
    exact Finset.mem_image.2 ⟨β, hS v hv hβ, funext fun c => hw β hβ c⟩
  have hT : ((S.image wtv).filter (fun ν => ∃ v ∈ U, v ≠ 0 ∧ IsWt ν v)).Nonempty := by
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    obtain ⟨ν, v, hv, hv0, hvw, -⟩ := exists_wtvec U hdiag _ u hu hu0 le_rfl
    exact ⟨ν, Finset.mem_filter.2 ⟨hwtS ν v hv hv0 hvw, v, hv, hv0, hvw⟩⟩

  obtain ⟨ν₀, hν₀, hmax⟩ := Finset.exists_max_image _ fw hT
  obtain ⟨-, v, hv, hv0, hvw⟩ := Finset.mem_filter.1 hν₀
  refine ⟨ν₀, v, hv, ?_⟩
  unfold IsHW hwSub
  refine ⟨hv0, Submodule.mem_inf.2 ⟨?_, ?_⟩⟩
  · simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply]
    intro a
    rw [Ecc_of_wt hvw a, sub_self]
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro a b hab
    obtain ⟨hsame, hne, htw⟩ := posC_facts hab
    by_contra hw0
    have hwU := hstab a b hsame v hv
    have hw' := wt_Eab_of hvw a b hsame hne
    have hmemT : (fun c => ν₀ c + (if a = c then 1 else 0) - (if b = c then 1 else 0)) ∈
        (S.image wtv).filter (fun ν => ∃ v ∈ U, v ≠ 0 ∧ IsWt ν v) :=
      Finset.mem_filter.2 ⟨hwtS _ _ hwU hw0 hw', _, hwU, hw0, hw'⟩
    have h1 := hmax _ hmemT
    rw [fw_shift] at h1
    linarith

end PI.FockOneDegW

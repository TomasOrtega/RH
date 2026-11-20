import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsKfin
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsLowK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsAdm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SchurA

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Data

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

/- English proof (translation)
Establish `hE` using `hD.glRep`. Establish `hU` using `isInfUnitary_of_isDerivedOn hσ hD`. Take `⟨w, hwV, hw0, hw⟩` from `hV.2.2.2`. Establish `hwG : w ∈ genSub E V` using `rorth_le_genSub hwV`. Distinguish the cases in `hVN : ∃ x ∈ N ⊓ V, x ≠ 0`.

Take `⟨x, hx, hx0⟩` from `hVN`. Conclude with `Or.inr (le_antisymm hN (schA_genSub_le hV N hNE hx.2 hx.1 hx0))`. Use `push Not at hVN`. Establish `hNk : IsKStableSub ε E N` using `fun a b _ x hx => hNE a b x hx`. Establish `hfd : ∀ a, ∀ y ∈ N, (innerₛₗ ℂ w) (E a a y) = (lowK ε lam a : ℂ) * (innerₛₗ ℂ w) y`.

Introduce `a y _`. Establish `h1` using `hU a a w y`. Simplify using `only [hw.1 a, inner_smul_left, adjSign, if_true, one_mul, Complex.conj_ofReal] at h1`. Simplify using `only [innerₛₗ_apply_apply]`. Conclude with `h1.symm`.

Establish `hfl : ∀ a b, a < b → ε a = ε b → ∀ y ∈ N, (innerₛₗ ℂ w) (E b a y) = 0`. Introduce `a b hab h y _`. Establish `h1` using `hU a b w y`. Rewrite `h1` using `[hw.2 a b hab h, inner_zero_left, show adjSign ε a b = 1 by simp [adjSign, h], one_mul]`. Simplify using `only [innerₛₗ_apply_apply]`.

Conclude with `h1.symm`. Establish `horth : ∀ z ∈ N, inner ℂ z w = 0`. Introduce `z hz`. Rewrite using `[← inner_eq_zero_symm]`. Assume the negation of the conclusion as `hne`.

Take `⟨u, huN, hu, huz, -⟩` from `schA_riesz hE hU hV.1 hV.2.1 N hN hNk (innerₛₗ ℂ w) (lowK ε lam) hfd hfl hz`. Establish `huV : u ∈ V` using `khw_lowK_mem hE hU hV hc hgap (hN huN) hu`. Use `hVN u ⟨huN, huV⟩` as an intermediate fact. Rewrite `huz` using `[this, inner_zero_left, innerₛₗ_apply_apply]`. Conclude with `hne huz.symm`.

Establish `hY : ∀ a b, ∀ y ∈ genSub E V ⊓ Nᗮ, E a b y ∈ genSub E V ⊓ Nᗮ`. Introduce `a b y hy`. Use `⟨rorth_apply_mem_genSub a b hy.1, (Submodule.mem_orthogonal _ _).2 fun z hz => ?_⟩` and prove the remaining obligations. Establish `h1` using `hU b a z y`. Rewrite `h1` using `[(Submodule.mem_orthogonal _ _).1 hy.2 _ (hNE b a z hz)]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[schA_adjSign_sq, one_mul]`. Use `_ = adjSign ε b a * (adjSign ε b a * inner ℂ z (E a b y)) := by ring`. Use `_ = 0 := by rw [← h1, mul_zero]`. Establish `hle` using `schA_genSub_le hV _ hY hwV ⟨hwG, (Submodule.mem_orthogonal _ _).2 horth⟩ hw0`.

Use `Or.inl ((Submodule.eq_bot_iff _).2 fun z hz => ?_)` and prove the remaining obligations. Conclude with `inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 (hle (hN hz)).2 z hz)`.
-/
theorem data_genSub_irred (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (N : Submodule ℂ D) (hN : N ≤ genSub E V)
    (hNE : ∀ a b, ∀ x ∈ N, E a b x ∈ N) (hNK : ∀ k ∈ Kset ε, ∀ x ∈ N, ∃ y ∈ N, (y : H) = σ k x) :
    N = ⊥ ∨ N = genSub E V := by
  have hE := hD.glRep
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  obtain ⟨w, hwV, hw0, hw⟩ := hV.2.2.2
  have hwG : w ∈ genSub E V := rorth_le_genSub hwV
  by_cases hVN : ∃ x ∈ N ⊓ V, x ≠ 0
  · obtain ⟨x, hx, hx0⟩ := hVN
    exact Or.inr (le_antisymm hN (schA_genSub_le hV N hNE hx.2 hx.1 hx0))
  push Not at hVN
  have hNk : IsKStableSub ε E N := fun a b _ x hx => hNE a b x hx
  have hfd : ∀ a, ∀ y ∈ N, (innerₛₗ ℂ w) (E a a y) = (lowK ε lam a : ℂ) * (innerₛₗ ℂ w) y := by
    intro a y _
    have h1 := hU a a w y
    simp only [hw.1 a, inner_smul_left, adjSign, if_true, one_mul, Complex.conj_ofReal] at h1
    simp only [innerₛₗ_apply_apply]
    exact h1.symm
  have hfl : ∀ a b, a < b → ε a = ε b → ∀ y ∈ N, (innerₛₗ ℂ w) (E b a y) = 0 := by
    intro a b hab h y _
    have h1 := hU a b w y
    rw [hw.2 a b hab h, inner_zero_left, show adjSign ε a b = 1 by simp [adjSign, h], one_mul] at h1
    simp only [innerₛₗ_apply_apply]
    exact h1.symm
  have horth : ∀ z ∈ N, inner ℂ z w = 0 := by
    intro z hz
    rw [← inner_eq_zero_symm]
    by_contra hne
    obtain ⟨u, huN, hu, huz, -⟩ :=
      schA_riesz hE hU hV.1 hV.2.1 N hN hNk (innerₛₗ ℂ w) (lowK ε lam) hfd hfl hz
    have huV : u ∈ V := khw_lowK_mem hE hU hV hc hgap (hN huN) hu
    have := hVN u ⟨huN, huV⟩
    rw [this, inner_zero_left, innerₛₗ_apply_apply] at huz
    exact hne huz.symm
  have hY : ∀ a b, ∀ y ∈ genSub E V ⊓ Nᗮ, E a b y ∈ genSub E V ⊓ Nᗮ := by
    intro a b y hy
    refine ⟨rorth_apply_mem_genSub a b hy.1, (Submodule.mem_orthogonal _ _).2 fun z hz => ?_⟩
    have h1 := hU b a z y
    rw [(Submodule.mem_orthogonal _ _).1 hy.2 _ (hNE b a z hz)] at h1
    calc inner ℂ z (E a b y) = (adjSign ε b a * adjSign ε b a) * inner ℂ z (E a b y) := by
          rw [schA_adjSign_sq, one_mul]
      _ = adjSign ε b a * (adjSign ε b a * inner ℂ z (E a b y)) := by ring
      _ = 0 := by rw [← h1, mul_zero]
  have hle := schA_genSub_le hV _ hY hwV ⟨hwG, (Submodule.mem_orthogonal _ _).2 horth⟩ hw0
  refine Or.inl ((Submodule.eq_bot_iff _).2 fun z hz => ?_)
  exact inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 (hle (hN hz)).2 z hz)

/- English proof (translation)
Establish `hE` using `hD.glRep`. Establish `hU` using `isInfUnitary_of_isDerivedOn hσ hD`. Take `⟨w, hwV, hw0, hw⟩` from `hV.2.2.2`. Establish `hwG : w ∈ genSub E V` using `rorth_le_genSub hwV`. Establish `hAw : IsKHWVec ε E (lowK ε lam) (A w)`.

Use `⟨fun a => ?_, fun a b hab h => ?_⟩` and prove the remaining obligations. Rewrite using `[← hAE a a w hwG, hw.1 a, map_smul]`. Rewrite using `[← hAE a b w hwG, hw.2 a b hab h, map_zero]`. Establish `hAwV : A w ∈ V` using `khw_lowK_mem hE hU hV hc hgap (hA w hwG) hAw`. Take `⟨c, hc'⟩` from `khw_line_of_kIrrHW hE hU hV hAwV hwV hAw hw hw0`.

Establish `hk : ∀ x, x ∈ LinearMap.ker (A - c • (1 : Module.End ℂ D)) ↔ A x = c • x` using `fun x => by`. Simplify using `[sub_eq_zero]`. Establish `hX : ∀ a b, ∀ x ∈ genSub E V ⊓ LinearMap.ker (A - c • (1 : Module.End ℂ D)), E a b x ∈ genSub E V ⊓ LinearMap.ker (A - c • (1 : Module.End ℂ D))`. Introduce `a b x hx`. Use `⟨rorth_apply_mem_genSub a b hx.1, (hk _).2 ?_⟩` and prove the remaining obligations.

Rewrite using `[hAE a b x hx.1, (hk x).1 hx.2, map_smul]`. Establish `hle` using `schA_genSub_le hV _ hX hwV ⟨hwG, (hk w).2 hc'⟩ hw0`. Conclude with `⟨c, fun x hx => (hk x).1 (hle hx).2⟩`.
-/
theorem data_end_scalar (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (A : D →ₗ[ℂ] D) (hA : ∀ x ∈ genSub E V, A x ∈ genSub E V)
    (hAE : ∀ a b, ∀ x ∈ genSub E V, A (E a b x) = E a b (A x))
    (hAK : ∀ k ∈ Kset ε, ∀ x ∈ genSub E V, ∀ y ∈ genSub E V, (y : H) = σ k x → (A y : H) = σ k (A x)) :
    ∃ c : ℂ, ∀ x ∈ genSub E V, A x = c • x := by
  have hE := hD.glRep
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  obtain ⟨w, hwV, hw0, hw⟩ := hV.2.2.2
  have hwG : w ∈ genSub E V := rorth_le_genSub hwV
  have hAw : IsKHWVec ε E (lowK ε lam) (A w) := by
    refine ⟨fun a => ?_, fun a b hab h => ?_⟩
    · rw [← hAE a a w hwG, hw.1 a, map_smul]
    · rw [← hAE a b w hwG, hw.2 a b hab h, map_zero]
  have hAwV : A w ∈ V := khw_lowK_mem hE hU hV hc hgap (hA w hwG) hAw
  obtain ⟨c, hc'⟩ := khw_line_of_kIrrHW hE hU hV hAwV hwV hAw hw hw0
  have hk : ∀ x, x ∈ LinearMap.ker (A - c • (1 : Module.End ℂ D)) ↔ A x = c • x := fun x => by
    simp [sub_eq_zero]
  have hX : ∀ a b, ∀ x ∈ genSub E V ⊓ LinearMap.ker (A - c • (1 : Module.End ℂ D)),
      E a b x ∈ genSub E V ⊓ LinearMap.ker (A - c • (1 : Module.End ℂ D)) := by
    intro a b x hx
    refine ⟨rorth_apply_mem_genSub a b hx.1, (hk _).2 ?_⟩
    rw [hAE a b x hx.1, (hk x).1 hx.2, map_smul]
  have hle := schA_genSub_le hV _ hX hwV ⟨hwG, (hk w).2 hc'⟩ hw0
  exact ⟨c, fun x hx => (hk x).1 (hle hx).2⟩

/- English proof (translation)
Establish `hE` using `hD.glRep`. Establish `hU` using `isInfUnitary_of_isDerivedOn hσ hD`. Take `⟨w, hwV, hw0, hw⟩` from `hV.2.2.2`. Establish `hwG : w ∈ genSub E V` using `rorth_le_genSub hwV`. Establish `hww : inner ℂ w w ≠ 0` using `inner_self_ne_zero.2 hw0`.

Use `set cc : ℂ := b w w / inner ℂ w w with hcdef`. Use `set f : D →ₗ[ℂ] ℂ := b w - cc • innerₛₗ ℂ w with hf`. Establish `hfapp : ∀ y, f y = b w y - cc * inner ℂ w y` using `fun y => by simp [hf]`. Establish `hfw : f w = 0` using `by rw [hfapp, hcdef, div_mul_cancel₀ _ hww, sub_self]`. Establish `hfd : ∀ a, ∀ y ∈ genSub E V, f (E a a y) = (lowK ε lam a : ℂ) * f y`.

Introduce `a y hy`. Establish `h1` using `hbE a a w hwG y hy`. Establish `h2` using `hU a a w y`. Simplify using `only [hw.1 a, adjSign, if_true, one_mul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Complex.conj_ofReal, inner_smul_left] at h1 h2`. Rewrite using `[hfapp, hfapp, ← h1, ← h2]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hfl : ∀ a b', a < b' → ε a = ε b' → ∀ y ∈ genSub E V, f (E b' a y) = 0`. Introduce `a b' hab h y hy`. Establish `h1` using `hbE a b' w hwG y hy`. Establish `h2` using `hU a b' w y`.

Rewrite `h1` using `[hw.2 a b' hab h, map_zero, LinearMap.zero_apply, show adjSign ε a b' = 1 by simp [adjSign, h], one_mul]`. Rewrite `h2` using `[hw.2 a b' hab h, inner_zero_left, show adjSign ε a b' = 1 by simp [adjSign, h], one_mul]`. Rewrite using `[hfapp, ← h1, ← h2]`. Simplify using the standard rewrite rules. Establish `hfz : ∀ y ∈ genSub E V, f y = 0`.

Introduce `y hy`. Assume the negation of the conclusion as `hne`. Take `⟨u, huG, hu, huy, huV'⟩` from `schA_riesz hE hU hV.1 hV.2.1 (genSub E V) le_rfl (fun a b _ x hx => rorth_apply_mem_genSub a b hx) f (lowK ε lam) hfd hfl hy`. Establish `huV : u ∈ V` using `khw_lowK_mem hE hU hV hc hgap huG hu`. Take `⟨c', hc'⟩` from `khw_line_of_kIrrHW hE hU hV huV hwV hu hw hw0`.

Establish `h3` using `huV' w ⟨hwG, hwV⟩`. Rewrite `h3` using `[hfw, hc', inner_smul_left]`. Establish `hc0 : c' = 0`. Break down `mul_eq_zero.1 h3 with h | h` into its components or cases. Simplify using `using h`.

Conclude with `absurd h hww`. Rewrite `huy` using `[hc', hc0, zero_smul, inner_zero_left]`. Conclude with `hne huy.symm`. Set `X : Submodule ℂ D` to `{ carrier := {x | x ∈ genSub E V ∧ ∀ y ∈ genSub E V, b x y = cc * inner ℂ x y} add_mem' := fun {x x'} hx hx' => ⟨(genSub E V).add_mem hx.1 hx'.1, fun y hy => by`. Rewrite using `[map_add, LinearMap.add_apply, hx.2 y hy, hx'.2 y hy, inner_add_left, mul_add]⟩`.

Use the proof step `zero_mem' := ⟨(genSub E V).zero_mem, fun y _ => by simp⟩`. Use the proof step `smul_mem' := fun r x hx => ⟨(genSub E V).smul_mem r hx.1, fun y hy => by`. Rewrite using `[map_smulₛₗ, LinearMap.smul_apply, hx.2 y hy, inner_smul_left, smul_eq_mul]`. Use the proof step `ring⟩ }`. Establish `hX : ∀ a c, ∀ x ∈ X, E a c x ∈ X`.

Introduce `a c x hx`. Use `⟨rorth_apply_mem_genSub a c hx.1, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[hbE a c x hx.1 y hy, hx.2 _ (rorth_apply_mem_genSub c a hy), hU]`. Expand and normalize the polynomial expressions, which then agree. Establish `hwX : w ∈ X` using `⟨hwG, fun y hy => by`.

Use `hfz y hy` as an intermediate fact. Rewrite `this` using `[hfapp, sub_eq_zero]`. Conclude with `this⟩`. Establish `hle` using `schA_genSub_le hV X hX hwV hwX hw0`. Conclude with `⟨cc, fun x hx y hy => (hle hx).2 y hy⟩`.
-/
theorem data_form_scalar (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (b : D →ₗ⋆[ℂ] D →ₗ[ℂ] ℂ)
    (hbE : ∀ a c, ∀ x ∈ genSub E V, ∀ y ∈ genSub E V, b (E a c x) y = adjSign ε a c * b x (E c a y))
    (hbK : ∀ k ∈ Kset ε, ∀ x ∈ genSub E V, ∀ y ∈ genSub E V, ∀ x' ∈ genSub E V, ∀ y' ∈ genSub E V,
      (x' : H) = σ k x → (y' : H) = σ k y → b x' y' = b x y) :
    ∃ c : ℂ, ∀ x ∈ genSub E V, ∀ y ∈ genSub E V, b x y = c * inner ℂ (x : H) (y : H) := by
  have hE := hD.glRep
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  obtain ⟨w, hwV, hw0, hw⟩ := hV.2.2.2
  have hwG : w ∈ genSub E V := rorth_le_genSub hwV
  have hww : inner ℂ w w ≠ 0 := inner_self_ne_zero.2 hw0
  set cc : ℂ := b w w / inner ℂ w w with hcdef
  set f : D →ₗ[ℂ] ℂ := b w - cc • innerₛₗ ℂ w with hf
  have hfapp : ∀ y, f y = b w y - cc * inner ℂ w y := fun y => by simp [hf]
  have hfw : f w = 0 := by rw [hfapp, hcdef, div_mul_cancel₀ _ hww, sub_self]
  have hfd : ∀ a, ∀ y ∈ genSub E V, f (E a a y) = (lowK ε lam a : ℂ) * f y := by
    intro a y hy
    have h1 := hbE a a w hwG y hy
    have h2 := hU a a w y
    simp only [hw.1 a, adjSign, if_true, one_mul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      Complex.conj_ofReal, inner_smul_left] at h1 h2
    rw [hfapp, hfapp, ← h1, ← h2]
    ring
  have hfl : ∀ a b', a < b' → ε a = ε b' → ∀ y ∈ genSub E V, f (E b' a y) = 0 := by
    intro a b' hab h y hy
    have h1 := hbE a b' w hwG y hy
    have h2 := hU a b' w y
    rw [hw.2 a b' hab h, map_zero, LinearMap.zero_apply,
      show adjSign ε a b' = 1 by simp [adjSign, h], one_mul] at h1
    rw [hw.2 a b' hab h, inner_zero_left, show adjSign ε a b' = 1 by simp [adjSign, h], one_mul] at h2
    rw [hfapp, ← h1, ← h2]
    simp
  have hfz : ∀ y ∈ genSub E V, f y = 0 := by
    intro y hy
    by_contra hne
    obtain ⟨u, huG, hu, huy, huV'⟩ := schA_riesz hE hU hV.1 hV.2.1 (genSub E V) le_rfl
      (fun a b _ x hx => rorth_apply_mem_genSub a b hx) f (lowK ε lam) hfd hfl hy
    have huV : u ∈ V := khw_lowK_mem hE hU hV hc hgap huG hu
    obtain ⟨c', hc'⟩ := khw_line_of_kIrrHW hE hU hV huV hwV hu hw hw0
    have h3 := huV' w ⟨hwG, hwV⟩
    rw [hfw, hc', inner_smul_left] at h3
    have hc0 : c' = 0 := by
      rcases mul_eq_zero.1 h3 with h | h
      · simpa using h
      · exact absurd h hww
    rw [hc', hc0, zero_smul, inner_zero_left] at huy
    exact hne huy.symm
  let X : Submodule ℂ D :=
    { carrier := {x | x ∈ genSub E V ∧ ∀ y ∈ genSub E V, b x y = cc * inner ℂ x y}
      add_mem' := fun {x x'} hx hx' => ⟨(genSub E V).add_mem hx.1 hx'.1, fun y hy => by
        rw [map_add, LinearMap.add_apply, hx.2 y hy, hx'.2 y hy, inner_add_left, mul_add]⟩
      zero_mem' := ⟨(genSub E V).zero_mem, fun y _ => by simp⟩
      smul_mem' := fun r x hx => ⟨(genSub E V).smul_mem r hx.1, fun y hy => by
        rw [map_smulₛₗ, LinearMap.smul_apply, hx.2 y hy, inner_smul_left, smul_eq_mul]; ring⟩ }
  have hX : ∀ a c, ∀ x ∈ X, E a c x ∈ X := by
    intro a c x hx
    refine ⟨rorth_apply_mem_genSub a c hx.1, fun y hy => ?_⟩
    rw [hbE a c x hx.1 y hy, hx.2 _ (rorth_apply_mem_genSub c a hy), hU]
    ring
  have hwX : w ∈ X := ⟨hwG, fun y hy => by
    have := hfz y hy
    rw [hfapp, sub_eq_zero] at this
    exact this⟩
  have hle := schA_genSub_le hV X hX hwV hwX hw0
  exact ⟨cc, fun x hx y hy => (hle hx).2 y hy⟩

end Data

section Two

variable {ε : Fin n → Bool}
  {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] {lam₁ : Fin n → ℝ}
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {D₁ : Submodule ℂ H₁}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {V₁ : Submodule ℂ D₁}
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] {lam₂ : Fin n → ℝ}
  {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)} {D₂ : Submodule ℂ H₂}
  {E₂ : Fin n → Fin n → Module.End ℂ D₂} {V₂ : Submodule ℂ D₂}

/- English proof (translation)
Establish `hE₁` using `hD₁.glRep`. Establish `hU₁` using `isInfUnitary_of_isDerivedOn hσ₁ hD₁`. Establish `hE₂` using `hD₂.glRep`. Establish `hU₂` using `isInfUnitary_of_isDerivedOn hσ₂ hD₂`. Take `⟨w₁, hw₁V, hw₁0, hw₁⟩` from `hV₁.2.2.2`.

Take `⟨w₂, hw₂V, hw₂0, hw₂⟩` from `hV₂.2.2.2`. Establish `hw₁G : w₁ ∈ genSub E₁ V₁` using `rorth_le_genSub hw₁V`. Establish `hw₂G : w₂ ∈ genSub E₂ V₂` using `rorth_le_genSub hw₂V`. Establish `hsg : ∀ a b', ε a = ε b' → adjSign ε a b' = 1` using `fun a b' h => by simp [adjSign, h]`. Set `X₁ : Submodule ℂ D₁` to `{ carrier := {x | x ∈ genSub E₁ V₁ ∧ ∀ y ∈ genSub E₂ V₂, b x y = 0} add_mem' := fun {x x'} hx hx' => ⟨(genSub E₁ V₁).add_mem hx.1 hx'.1, fun y hy => by`.

Rewrite using `[map_add, LinearMap.add_apply, hx.2 y hy, hx'.2 y hy, add_zero]⟩`. Use the proof step `zero_mem' := ⟨(genSub E₁ V₁).zero_mem, fun y _ => by simp⟩`. Use the proof step `smul_mem' := fun r x hx => ⟨(genSub E₁ V₁).smul_mem r hx.1, fun y hy => by`. Rewrite using `[map_smulₛₗ, LinearMap.smul_apply, hx.2 y hy, smul_zero]⟩ }`. Set `X₂ : Submodule ℂ D₂` to `{ carrier := {y | y ∈ genSub E₂ V₂ ∧ ∀ x ∈ genSub E₁ V₁, b x y = 0} add_mem' := fun {y y'} hy hy' => ⟨(genSub E₂ V₂).add_mem hy.1 hy'.1, fun x hx => by`.

Rewrite using `[map_add, hy.2 x hx, hy'.2 x hx, add_zero]⟩`. Use the proof step `zero_mem' := ⟨(genSub E₂ V₂).zero_mem, fun x _ => by simp⟩`. Use the proof step `smul_mem' := fun r y hy => ⟨(genSub E₂ V₂).smul_mem r hy.1, fun x hx => by`. Rewrite using `[map_smul, hy.2 x hx, smul_zero]⟩ }`. Establish `hX₁ : ∀ a c, ∀ x ∈ X₁, E₁ a c x ∈ X₁` using `fun a c x hx => ⟨rorth_apply_mem_genSub a c hx.1, fun y hy => by`.

Rewrite using `[hbE a c x hx.1 y hy, hx.2 _ (rorth_apply_mem_genSub c a hy), mul_zero]⟩`. Establish `hX₂ : ∀ a c, ∀ y ∈ X₂, E₂ a c y ∈ X₂` using `fun a c y hy => ⟨rorth_apply_mem_genSub a c hy.1, fun x hx => by`. Establish `h` using `hbE c a x hx y hy.1`. Rewrite `h` using `[hy.2 _ (rorth_apply_mem_genSub c a hx)]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[schA_adjSign_sq, one_mul]`. Use `_ = adjSign ε c a * (adjSign ε c a * b x (E₂ a c y)) := by ring`. Use `_ = 0 := by rw [← h, mul_zero]⟩`. Distinguish the cases in `hL : ∀ y ∈ genSub E₂ V₂, b w₁ y = 0`. Establish `hle` using `schA_genSub_le hV₁ X₁ hX₁ hw₁V ⟨hw₁G, hL⟩ hw₁0`.

Conclude with `fun x hx y hy => (hle hx).2 y hy`. Distinguish the cases in `hR : ∀ x ∈ genSub E₁ V₁, b x w₂ = 0`. Establish `hle` using `schA_genSub_le hV₂ X₂ hX₂ hw₂V ⟨hw₂G, hR⟩ hw₂0`. Conclude with `fun x hx y hy => (hle hy).2 x hx`. It suffices to derive a contradiction.

Use `push Not at hL hR`. Take `⟨y₀, hy₀, hby⟩` from `hL`. Take `⟨x₀, hx₀, hbx⟩` from `hR`. Establish `hfd₂ : ∀ a, ∀ y ∈ genSub E₂ V₂, b w₁ (E₂ a a y) = (lowK ε lam₁ a : ℂ) * b w₁ y`. Introduce `a y hy`.

Establish `h1` using `hbE a a w₁ hw₁G y hy`. Simplify using `only [hw₁.1 a, adjSign, if_true, one_mul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Complex.conj_ofReal] at h1`. Conclude with `h1.symm`. Establish `hfl₂ : ∀ a b', a < b' → ε a = ε b' → ∀ y ∈ genSub E₂ V₂, b w₁ (E₂ b' a y) = 0`. Introduce `a b' hab h y hy`.

Establish `h1` using `hbE a b' w₁ hw₁G y hy`. Rewrite `h1` using `[hw₁.2 a b' hab h, map_zero, LinearMap.zero_apply, hsg a b' h, one_mul]`. Conclude with `h1.symm`. Take `⟨u₂, hu₂G, hu₂, hu₂y, -⟩` from `schA_riesz hE₂ hU₂ hV₂.1 hV₂.2.1 (genSub E₂ V₂) le_rfl (fun a b' _ x hx => rorth_apply_mem_genSub a b' hx) (b w₁) (lowK ε lam₁) hfd₂ hfl₂ hy₀`. Establish `hu₂0 : u₂ ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hu₂y` using `[inner_zero_left]`. Conclude with `hby hu₂y.symm`. Set `g : D₁ →ₗ[ℂ] ℂ` to `{ toFun := fun x => starRingEnd ℂ (b x w₂) map_add' := fun x x' => by simp map_smul' := fun r x => by simp }`. Establish `hgapp : ∀ x, g x = starRingEnd ℂ (b x w₂)` using `fun _ => rfl`.

Establish `hfd₁ : ∀ a, ∀ x ∈ genSub E₁ V₁, g (E₁ a a x) = (lowK ε lam₂ a : ℂ) * g x`. Introduce `a x hx`. Establish `h1` using `hbE a a x hx w₂ hw₂G`. Simplify using `only [hw₂.1 a, adjSign, if_true, one_mul, map_smul, smul_eq_mul] at h1`. Rewrite using `[hgapp, hgapp, h1, map_mul, Complex.conj_ofReal]`.

Establish `hfl₁ : ∀ a b', a < b' → ε a = ε b' → ∀ x ∈ genSub E₁ V₁, g (E₁ b' a x) = 0`. Introduce `a b' hab h x hx`. Establish `h1` using `hbE b' a x hx w₂ hw₂G`. Rewrite `h1` using `[hw₂.2 a b' hab h, map_zero, mul_zero]`. Rewrite using `[hgapp, h1, map_zero]`.

Take `⟨u₁, hu₁G, hu₁, hu₁x, -⟩` from `schA_riesz hE₁ hU₁ hV₁.1 hV₁.2.1 (genSub E₁ V₁) le_rfl (fun a b' _ x hx => rorth_apply_mem_genSub a b' hx) g (lowK ε lam₂) hfd₁ hfl₁ hx₀`. Establish `hu₁0 : u₁ ≠ 0`. Introduce and unpack `rfl`. Rewrite `hu₁x` using `[inner_zero_left, hgapp]`. Conclude with `hbx (by simpa using hu₁x.symm)`.

Establish `hΛ : lowK ε lam₁ ≠ lowK ε lam₂`. Introduce `h`. Apply `hne` to reduce the goal to its premises. Use function extensionality and compare the values at `a`. Use `congrFun h a` as an intermediate fact.

Simplify using `only [lowK, Pi.add_apply, Pi.sub_apply] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨hmono₁, h₁, hh₁, hbig₁⟩` from `hgap₁`. Take `⟨hmono₂, h₂, hh₂, hbig₂⟩` from `hgap₂`. Take `⟨j₂, -, hpos₂, hle₂⟩` from `casimir_gap_at_noncompact_weight hE₂ hU₂ hV₂ hc₂ hmono₂ hh₂ hbig₂ hu₂G hu₂0 hu₂ hΛ`.

Take `⟨j₁, -, hpos₁, hle₁⟩` from `casimir_gap_at_noncompact_weight hE₁ hU₁ hV₁ hc₁ hmono₁ hh₁ hbig₁ hu₁G hu₁0 hu₁ hΛ.symm`. Establish `p₁ : 0 < 2 * ((j₁ : ℝ) + 1) * (h₁ - n + 1)` using `mul_pos (by positivity) hpos₁`. Establish `p₂ : 0 < 2 * ((j₂ : ℝ) + 1) * (h₂ - n + 1)` using `mul_pos (by positivity) hpos₂`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem data_form_zero (hgap₁ : StdGap ε lam₁)
    (hσ₁ : IsURepOn (UJset ε) σ₁) (hD₁ : IsDerivedOn ε σ₁ D₁ E₁) (hV₁ : IsKIrrHW ε E₁ (lowK ε lam₁) V₁)
    (hc₁ : ∀ v ∈ V₁, casimir E₁ v = (casVal lam₁ : ℂ) • v)
    (hVK₁ : ∀ k ∈ Kset ε, ∀ v ∈ V₁, ∃ w ∈ V₁, (w : H₁) = σ₁ k v)
    (hgap₂ : StdGap ε lam₂)
    (hσ₂ : IsURepOn (UJset ε) σ₂) (hD₂ : IsDerivedOn ε σ₂ D₂ E₂) (hV₂ : IsKIrrHW ε E₂ (lowK ε lam₂) V₂)
    (hc₂ : ∀ v ∈ V₂, casimir E₂ v = (casVal lam₂ : ℂ) • v)
    (hVK₂ : ∀ k ∈ Kset ε, ∀ v ∈ V₂, ∃ w ∈ V₂, (w : H₂) = σ₂ k v)
    (hne : lam₁ ≠ lam₂) (b : D₁ →ₗ⋆[ℂ] D₂ →ₗ[ℂ] ℂ)
    (hbE : ∀ a c, ∀ x ∈ genSub E₁ V₁, ∀ y ∈ genSub E₂ V₂, b (E₁ a c x) y = adjSign ε a c * b x (E₂ c a y))
    (hbK : ∀ k ∈ Kset ε, ∀ x ∈ genSub E₁ V₁, ∀ y ∈ genSub E₂ V₂, ∀ x' ∈ genSub E₁ V₁, ∀ y' ∈ genSub E₂ V₂,
      (x' : H₁) = σ₁ k x → (y' : H₂) = σ₂ k y → b x' y' = b x y) :
    ∀ x ∈ genSub E₁ V₁, ∀ y ∈ genSub E₂ V₂, b x y = 0 := by
  have hE₁ := hD₁.glRep
  have hU₁ := isInfUnitary_of_isDerivedOn hσ₁ hD₁
  have hE₂ := hD₂.glRep
  have hU₂ := isInfUnitary_of_isDerivedOn hσ₂ hD₂
  obtain ⟨w₁, hw₁V, hw₁0, hw₁⟩ := hV₁.2.2.2
  obtain ⟨w₂, hw₂V, hw₂0, hw₂⟩ := hV₂.2.2.2
  have hw₁G : w₁ ∈ genSub E₁ V₁ := rorth_le_genSub hw₁V
  have hw₂G : w₂ ∈ genSub E₂ V₂ := rorth_le_genSub hw₂V
  have hsg : ∀ a b', ε a = ε b' → adjSign ε a b' = 1 := fun a b' h => by simp [adjSign, h]
  let X₁ : Submodule ℂ D₁ :=
    { carrier := {x | x ∈ genSub E₁ V₁ ∧ ∀ y ∈ genSub E₂ V₂, b x y = 0}
      add_mem' := fun {x x'} hx hx' => ⟨(genSub E₁ V₁).add_mem hx.1 hx'.1, fun y hy => by
        rw [map_add, LinearMap.add_apply, hx.2 y hy, hx'.2 y hy, add_zero]⟩
      zero_mem' := ⟨(genSub E₁ V₁).zero_mem, fun y _ => by simp⟩
      smul_mem' := fun r x hx => ⟨(genSub E₁ V₁).smul_mem r hx.1, fun y hy => by
        rw [map_smulₛₗ, LinearMap.smul_apply, hx.2 y hy, smul_zero]⟩ }
  let X₂ : Submodule ℂ D₂ :=
    { carrier := {y | y ∈ genSub E₂ V₂ ∧ ∀ x ∈ genSub E₁ V₁, b x y = 0}
      add_mem' := fun {y y'} hy hy' => ⟨(genSub E₂ V₂).add_mem hy.1 hy'.1, fun x hx => by
        rw [map_add, hy.2 x hx, hy'.2 x hx, add_zero]⟩
      zero_mem' := ⟨(genSub E₂ V₂).zero_mem, fun x _ => by simp⟩
      smul_mem' := fun r y hy => ⟨(genSub E₂ V₂).smul_mem r hy.1, fun x hx => by
        rw [map_smul, hy.2 x hx, smul_zero]⟩ }
  have hX₁ : ∀ a c, ∀ x ∈ X₁, E₁ a c x ∈ X₁ := fun a c x hx =>
    ⟨rorth_apply_mem_genSub a c hx.1, fun y hy => by
      rw [hbE a c x hx.1 y hy, hx.2 _ (rorth_apply_mem_genSub c a hy), mul_zero]⟩
  have hX₂ : ∀ a c, ∀ y ∈ X₂, E₂ a c y ∈ X₂ := fun a c y hy =>
    ⟨rorth_apply_mem_genSub a c hy.1, fun x hx => by
      have h := hbE c a x hx y hy.1
      rw [hy.2 _ (rorth_apply_mem_genSub c a hx)] at h
      calc b x (E₂ a c y) = (adjSign ε c a * adjSign ε c a) * b x (E₂ a c y) := by
            rw [schA_adjSign_sq, one_mul]
        _ = adjSign ε c a * (adjSign ε c a * b x (E₂ a c y)) := by ring
        _ = 0 := by rw [← h, mul_zero]⟩
  by_cases hL : ∀ y ∈ genSub E₂ V₂, b w₁ y = 0
  · have hle := schA_genSub_le hV₁ X₁ hX₁ hw₁V ⟨hw₁G, hL⟩ hw₁0
    exact fun x hx y hy => (hle hx).2 y hy
  by_cases hR : ∀ x ∈ genSub E₁ V₁, b x w₂ = 0
  · have hle := schA_genSub_le hV₂ X₂ hX₂ hw₂V ⟨hw₂G, hR⟩ hw₂0
    exact fun x hx y hy => (hle hy).2 x hx
  exfalso
  push Not at hL hR
  obtain ⟨y₀, hy₀, hby⟩ := hL
  obtain ⟨x₀, hx₀, hbx⟩ := hR
  have hfd₂ : ∀ a, ∀ y ∈ genSub E₂ V₂, b w₁ (E₂ a a y) = (lowK ε lam₁ a : ℂ) * b w₁ y := by
    intro a y hy
    have h1 := hbE a a w₁ hw₁G y hy
    simp only [hw₁.1 a, adjSign, if_true, one_mul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      Complex.conj_ofReal] at h1
    exact h1.symm
  have hfl₂ : ∀ a b', a < b' → ε a = ε b' → ∀ y ∈ genSub E₂ V₂, b w₁ (E₂ b' a y) = 0 := by
    intro a b' hab h y hy
    have h1 := hbE a b' w₁ hw₁G y hy
    rw [hw₁.2 a b' hab h, map_zero, LinearMap.zero_apply, hsg a b' h, one_mul] at h1
    exact h1.symm
  obtain ⟨u₂, hu₂G, hu₂, hu₂y, -⟩ := schA_riesz hE₂ hU₂ hV₂.1 hV₂.2.1 (genSub E₂ V₂) le_rfl
    (fun a b' _ x hx => rorth_apply_mem_genSub a b' hx) (b w₁) (lowK ε lam₁) hfd₂ hfl₂ hy₀
  have hu₂0 : u₂ ≠ 0 := by
    rintro rfl
    rw [inner_zero_left] at hu₂y
    exact hby hu₂y.symm
  let g : D₁ →ₗ[ℂ] ℂ :=
    { toFun := fun x => starRingEnd ℂ (b x w₂)
      map_add' := fun x x' => by simp
      map_smul' := fun r x => by simp }
  have hgapp : ∀ x, g x = starRingEnd ℂ (b x w₂) := fun _ => rfl
  have hfd₁ : ∀ a, ∀ x ∈ genSub E₁ V₁, g (E₁ a a x) = (lowK ε lam₂ a : ℂ) * g x := by
    intro a x hx
    have h1 := hbE a a x hx w₂ hw₂G
    simp only [hw₂.1 a, adjSign, if_true, one_mul, map_smul, smul_eq_mul] at h1
    rw [hgapp, hgapp, h1, map_mul, Complex.conj_ofReal]
  have hfl₁ : ∀ a b', a < b' → ε a = ε b' → ∀ x ∈ genSub E₁ V₁, g (E₁ b' a x) = 0 := by
    intro a b' hab h x hx
    have h1 := hbE b' a x hx w₂ hw₂G
    rw [hw₂.2 a b' hab h, map_zero, mul_zero] at h1
    rw [hgapp, h1, map_zero]
  obtain ⟨u₁, hu₁G, hu₁, hu₁x, -⟩ := schA_riesz hE₁ hU₁ hV₁.1 hV₁.2.1 (genSub E₁ V₁) le_rfl
    (fun a b' _ x hx => rorth_apply_mem_genSub a b' hx) g (lowK ε lam₂) hfd₁ hfl₁ hx₀
  have hu₁0 : u₁ ≠ 0 := by
    rintro rfl
    rw [inner_zero_left, hgapp] at hu₁x
    exact hbx (by simpa using hu₁x.symm)
  have hΛ : lowK ε lam₁ ≠ lowK ε lam₂ := by
    intro h
    apply hne
    funext a
    have := congrFun h a
    simp only [lowK, Pi.add_apply, Pi.sub_apply] at this
    linarith
  obtain ⟨hmono₁, h₁, hh₁, hbig₁⟩ := hgap₁
  obtain ⟨hmono₂, h₂, hh₂, hbig₂⟩ := hgap₂
  obtain ⟨j₂, -, hpos₂, hle₂⟩ := casimir_gap_at_noncompact_weight hE₂ hU₂ hV₂ hc₂ hmono₂ hh₂ hbig₂ hu₂G hu₂0 hu₂ hΛ
  obtain ⟨j₁, -, hpos₁, hle₁⟩ := casimir_gap_at_noncompact_weight hE₁ hU₁ hV₁ hc₁ hmono₁ hh₁ hbig₁ hu₁G hu₁0 hu₁ hΛ.symm
  have p₁ : 0 < 2 * ((j₁ : ℝ) + 1) * (h₁ - n + 1) := mul_pos (by positivity) hpos₁
  have p₂ : 0 < 2 * ((j₂ : ℝ) + 1) * (h₂ - n + 1) := mul_pos (by positivity) hpos₂
  linarith

end Two

end ReciprocityTheory.ChartRestriction.DS

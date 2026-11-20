import Formalism.SharpRestriction.GrowthBounds.RootWeights.CrCCommApply

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def cr_WS (E : GLOps n K V) (S : Set (Fin n → ℤ)) : Submodule K V := ⨆ ν ∈ S, weightSp E ν

/- English proof (translation)
Unfold `cr_WS`. Conclude with `biSup_mono fun i hi => h hi`.
-/
theorem cr_WS_mono (E : GLOps n K V) {S S' : Set (Fin n → ℤ)} (h : S ⊆ S') : cr_WS E S ≤ cr_WS E S' := by
  unfold cr_WS
  exact biSup_mono fun i hi => h hi

/- English proof (translation)
Unfold `cr_WS`. Conclude with `le_iSup₂ (f := fun ν (_ : ν ∈ S) => weightSp E ν) ν h`.
-/
theorem cr_WS_of_mem (E : GLOps n K V) {S : Set (Fin n → ℤ)} {ν : Fin n → ℤ} (h : ν ∈ S) :
    weightSp E ν ≤ cr_WS E S := by
  unfold cr_WS
  exact le_iSup₂ (f := fun ν (_ : ν ∈ S) => weightSp E ν) ν h

/- English proof (translation)
Take `⟨a, ha⟩` from `Function.ne_iff.1 hne`. Establish `e1` using `(v2rep_mem_weightSp E ν x).1 h1 a`. Establish `e2` using `(v2rep_mem_weightSp E ν' x).1 h2 a`. Establish `e3 : ((ν a : K) - (ν' a : K)) • x = 0` using `by rw [sub_smul, ← e1, ← e2, sub_self]`. Break down `smul_eq_zero.1 e3 with h | h` into its components or cases.

Conclude with `absurd (Int.cast_injective (sub_eq_zero.1 h)) ha`. Conclude with `h`.
-/
theorem cr_wt_disj [CharZero K] (E : GLOps n K V) {ν ν' : Fin n → ℤ} (hne : ν ≠ ν') {x : V}
    (h1 : x ∈ weightSp E ν) (h2 : x ∈ weightSp E ν') : x = 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hne
  have e1 := (v2rep_mem_weightSp E ν x).1 h1 a
  have e2 := (v2rep_mem_weightSp E ν' x).1 h2 a
  have e3 : ((ν a : K) - (ν' a : K)) • x = 0 := by rw [sub_smul, ← e1, ← e2, sub_self]
  rcases smul_eq_zero.1 e3 with h | h
  · exact absurd (Int.cast_injective (sub_eq_zero.1 h)) ha
  · exact h

/- English proof (translation)
Rewrite using `[(v2rep_mem_weightSp E ν x).1 hx a]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem cr_wt_diag_stable (E : GLOps n K V) (ν : Fin n → ℤ) (a : Fin n) (x : V) (hx : x ∈ weightSp E ν) :
    E a a x ∈ weightSp E ν := by
  rw [(v2rep_mem_weightSp E ν x).1 hx a]
  exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Take `⟨f, hf, rfl⟩` from `(Submodule.mem_iSup_iff_exists_finsupp _ _).1 hz`. Establish `hf' : ∀ ν, f ν ∈ weightSp E ν` using `fun ν => (iSup_le fun _ => le_rfl : (⨆ (_ : ν ∈ S), weightSp E ν) ≤ _) (hf ν)`. Establish `h` using `v2rep_comp_mem E (weightSp E ν0) (fun a x hx => cr_wt_diag_stable E ν0 a x hx) f.support (fun ν => f ν) (fun ν _ => hf' ν) hz0`. Establish `hsupp : ∀ ν ∈ f.support, ν = ν0`. Introduce `ν hν`.

Assume the negation of the conclusion as `hh`. Conclude with `(Finsupp.mem_support_iff.1 hν) (cr_wt_disj E hh (hf' ν) (h ν hν))`. Assume the negation of the conclusion as `hS`. Establish `h0 : f ν0 = 0`. Use `hf ν0` as an intermediate fact.

Simplify `this` using `[hS]`. Apply `hne` to reduce the goal to its premises. Use `Finset.sum_eq_zero fun ν hν => ?_` and prove the remaining obligations. Rewrite using `[hsupp ν hν]`. Conclude with `h0`.
-/
theorem cr_WS_mem [CharZero K] (E : GLOps n K V) {S : Set (Fin n → ℤ)} {ν0 : Fin n → ℤ} {z : V}
    (hz : z ∈ cr_WS E S) (hz0 : z ∈ weightSp E ν0) (hne : z ≠ 0) : ν0 ∈ S := by
  classical
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hz
  have hf' : ∀ ν, f ν ∈ weightSp E ν := fun ν => (iSup_le fun _ => le_rfl : (⨆ (_ : ν ∈ S), weightSp E ν) ≤ _) (hf ν)
  have h := v2rep_comp_mem E (weightSp E ν0) (fun a x hx => cr_wt_diag_stable E ν0 a x hx) f.support
    (fun ν => f ν) (fun ν _ => hf' ν) hz0
  have hsupp : ∀ ν ∈ f.support, ν = ν0 := by
    intro ν hν
    by_contra hh
    exact (Finsupp.mem_support_iff.1 hν) (cr_wt_disj E hh (hf' ν) (h ν hν))
  by_contra hS
  have h0 : f ν0 = 0 := by
    have := hf ν0
    simpa [hS] using this
  apply hne
  refine Finset.sum_eq_zero fun ν hν => ?_
  rw [hsupp ν hν]
  exact h0

def cr_Low (lam : Fin n → ℤ) : Set (Fin n → ℤ) := {ν | lam - ν ∈ cr_Pos n ∧ 0 < weightHeight' (lam - ν)}

def weightsBelow (lam : Fin n → ℤ) : Set (Fin n → ℤ) := {ν | lam - ν ∈ cr_Pos n}

/- English proof (translation)
Introduce `_ hν` and use `hν.1`.
-/
theorem cr_Low_sub (lam : Fin n → ℤ) : cr_Low lam ⊆ weightsBelow lam := fun _ hν => hν.1

/- English proof (translation)
Use `iSup₂_le fun ν hν x hx => ?_` and prove the remaining obligations. Use `show E a b x ∈ cr_WS E (cr_Low lam)`. Use `cr_WS_of_mem E ?_ (v2rep_shift E hR a b ν x hx)` and prove the remaining obligations. Establish `e : lam - (ν + rootW a b) = (lam - ν) + rootW b a`. Use extensionality with `c`.

Simplify using `only [rootW, Pi.sub_apply, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `add_mem hν (cr_root_mem b a h)`.

Rewrite using `[e, cr_ht_add]`. Establish `h1` using `cr_Pos_ht hν`. Establish `h2` using `cr_ht_root b a h`. Use linear arithmetic over natural numbers and integers.
-/
theorem cr_lower (E : GLOps n K V) (hR : SatisfiesGLRelations E) (lam : Fin n → ℤ) (a b : Fin n) (h : b < a) :
    cr_WS E (weightsBelow lam) ≤ (cr_WS E (cr_Low lam)).comap (E a b) := by
  refine iSup₂_le fun ν hν x hx => ?_
  show E a b x ∈ cr_WS E (cr_Low lam)
  refine cr_WS_of_mem E ?_ (v2rep_shift E hR a b ν x hx)
  have e : lam - (ν + rootW a b) = (lam - ν) + rootW b a := by
    ext c; simp only [rootW, Pi.sub_apply, Pi.add_apply]; ring
  refine ⟨?_, ?_⟩
  · rw [e]; exact add_mem hν (cr_root_mem b a h)
  · rw [e, cr_ht_add]
    have h1 := cr_Pos_ht hν
    have h2 := cr_ht_root b a h
    omega

/- English proof (translation)
Establish `hv0 : Submodule.span K {v} ⊔ cr_WS E (cr_Low lam) ≤ cr_WS E (weightsBelow lam)`. Use `sup_le ?_ (cr_WS_mono E (cr_Low_sub lam))` and prove the remaining obligations. Rewrite using `[Submodule.span_singleton_le_iff_mem]`. Use `cr_WS_of_mem E ?_ hv.2.1` and prove the remaining obligations. Use `show lam - lam ∈ cr_Pos n`.

Rewrite using `[sub_self]`. Conclude with `zero_mem _`. Proceed by induction on `k with`. Consider the case `zero => exact le_sup_left`. Consider the case `succ k ih`.

Use `sup_le ih ?_` and prove the remaining obligations. Use `iSup_le fun ab => iSup_le fun hab => ?_` and prove the remaining obligations. Rewrite using `[Submodule.map_le_iff_le_comap]`. Use `(ih.trans hv0).trans ((cr_lower E hR lam ab.1 ab.2 hab).trans ?_)` and prove the remaining obligations. Conclude with `Submodule.comap_mono le_sup_right`.
-/
theorem cr_Y_le (E : GLOps n K V) (hR : SatisfiesGLRelations E) (lam : Fin n → ℤ) (v : V) (hv : IsHWV E lam v) (k : ℕ) :
    cyclicLevelSubmodule E v k ≤ Submodule.span K {v} ⊔ cr_WS E (cr_Low lam) := by
  have hv0 : Submodule.span K {v} ⊔ cr_WS E (cr_Low lam) ≤ cr_WS E (weightsBelow lam) := by
    refine sup_le ?_ (cr_WS_mono E (cr_Low_sub lam))
    rw [Submodule.span_singleton_le_iff_mem]
    refine cr_WS_of_mem E ?_ hv.2.1
    show lam - lam ∈ cr_Pos n
    rw [sub_self]; exact zero_mem _
  induction k with
  | zero => exact le_sup_left
  | succ k ih =>
    refine sup_le ih ?_
    refine iSup_le fun ab => iSup_le fun hab => ?_
    rw [Submodule.map_le_iff_le_comap]
    refine (ih.trans hv0).trans ((cr_lower E hR lam ab.1 ab.2 hab).trans ?_)
    exact Submodule.comap_mono le_sup_right

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `x ⟨u, hu, v, hvW, hv, rfl⟩`. Take `⟨k, hk⟩` from `v2rep_Umon_Y E hR lam v hv u hu 0 v (Submodule.mem_span_singleton_self v)`. Establish `hle : Submodule.span K {v} ⊔ cr_WS E (cr_Low lam) ≤ (Wx ⊓ weightSp E lam) ⊔ cr_WS E (cr_Low lam)`. Use `sup_le_sup_right ?_ _` and prove the remaining obligations.

Rewrite using `[Submodule.span_singleton_le_iff_mem]`. Conclude with `⟨hvW, hv.2.1⟩`. Conclude with `hle (cr_Y_le E hR lam v hv k hk)`.
-/
theorem cr_isoIn_le (E : GLOps n K V) (hR : SatisfiesGLRelations E) (Wx : Submodule K V) (lam : Fin n → ℤ) :
    isotypicPartIn E Wx lam ≤ (Wx ⊓ weightSp E lam) ⊔ cr_WS E (cr_Low lam) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨u, hu, v, hvW, hv, rfl⟩
  obtain ⟨k, hk⟩ := v2rep_Umon_Y E hR lam v hv u hu 0 v (Submodule.mem_span_singleton_self v)
  have hle : Submodule.span K {v} ⊔ cr_WS E (cr_Low lam) ≤ (Wx ⊓ weightSp E lam) ⊔ cr_WS E (cr_Low lam) := by
    refine sup_le_sup_right ?_ _
    rw [Submodule.span_singleton_le_iff_mem]
    exact ⟨hvW, hv.2.1⟩
  exact hle (cr_Y_le E hR lam v hv k hk)

/- English proof (translation)
Use `(cr_isoIn_le E hR Wx lam).trans (sup_le ?_ (cr_WS_mono E (cr_Low_sub lam)))` and prove the remaining obligations. Use `inf_le_right.trans (cr_WS_of_mem E ?_)` and prove the remaining obligations. Use `show lam - lam ∈ cr_Pos n`. Rewrite using `[sub_self]`. Conclude with `zero_mem _`.
-/
theorem isotypic_component_le_lower_weights (E : GLOps n K V) (hR : SatisfiesGLRelations E) (Wx : Submodule K V) (lam : Fin n → ℤ) :
    isotypicPartIn E Wx lam ≤ cr_WS E (weightsBelow lam) := by
  refine (cr_isoIn_le E hR Wx lam).trans (sup_le ?_ (cr_WS_mono E (cr_Low_sub lam)))
  refine inf_le_right.trans (cr_WS_of_mem E ?_)
  show lam - lam ∈ cr_Pos n
  rw [sub_self]; exact zero_mem _

/- English proof (translation)
Establish `hba : b ≠ a` using `hab.symm`. Establish `hef : E a b * E b a - E b a * E a b = E a a - E b b`. Use `rel a b b a` as an intermediate fact. Simplify using `using this`. Establish `h1 : E a a * E a b - E a b * E a a = E a b`.

Use `rel a a a b` as an intermediate fact. Simplify `this` using `[hba]`. Establish `h2 : E b b * E a b - E a b * E b b = - E a b`. Use `rel b b a b` as an intermediate fact. Simplify `this` using `[hba]`.

Establish `h3 : E a a * E b a - E b a * E a a = - E b a`. Use `rel a a b a` as an intermediate fact. Simplify `this` using `[hab]`. Establish `h4 : E b b * E b a - E b a * E b b = E b a`. Use `rel b b b a` as an intermediate fact.

Simplify `this` using `[hab]`. Establish `hva : E a a v = (mu a : K) • v` using `(v2rep_mem_weightSp E mu v).1 hv a`. Establish `hvb : E b b v = (mu b : K) • v` using `(v2rep_mem_weightSp E mu v).1 hv b`. Establish `hhf : (E a a - E b b) * E b a - E b a * (E a a - E b b) = -(2 • E b a)`. Establish `: (E a a - E b b) * E b a - E b a * (E a a - E b b) = (E a a * E b a - E b a * E a a) - (E b b * E b a - E b a * E b b)` using `by noncomm_ring`.

Rewrite using `[this, h3, h4, two_smul]`. Normalize the expressions using the abelian group laws. Establish `hhe : (E a a - E b b) * E a b - E a b * (E a a - E b b) = 2 • E a b`. Establish `: (E a a - E b b) * E a b - E a b * (E a a - E b b) = (E a a * E a b - E a b * E a a) - (E b b * E a b - E a b * E b b)` using `by noncomm_ring`. Rewrite using `[this, h1, h2, two_smul]`.

Normalize the expressions using the abelian group laws. Establish `hhv : (E a a - E b b) v = ((mu a : K) - (mu b : K)) • v`. Rewrite using `[LinearMap.sub_apply, hva, hvb, sub_smul]`. Distinguish the cases in `hh0 : E a a - E b b = 0`. Rewrite `hhv` using `[hh0, LinearMap.zero_apply]`.

Break down `smul_eq_zero.1 hhv.symm with h | h` into its components or cases. Conclude with `(Int.cast_injective (sub_eq_zero.1 h)).ge`. Conclude with `absurd h hne`. Establish `t : IsSl2Triple (E a a - E b b) (E a b) (E b a)` using `{ h_ne_zero := hh0 lie_e_f := by rw [Ring.lie_def]; exact hef lie_h_e_nsmul := by rw [Ring.lie_def]; exact hhe lie_h_f_nsmul := by rw [Ring.lie_def]; exact hhf }`. Establish `P : t.HasPrimitiveVectorWith v ((mu a : K) - (mu b : K))` using `{ ne_zero := hne lie_h := by rw [Module.End.lie_apply]; exact hhv lie_e := by rw [Module.End.lie_apply]; exact he }`.

Take `⟨m, hm⟩` from `P.exists_nat`. Establish `: ((mu a - mu b : ℤ) : K) = ((m : ℤ) : K)` using `by push_cast; exact hm`. Use `Int.cast_injective this` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem cr_dom [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (rel : SatisfiesGLRelations E) {mu : Fin n → ℤ} {v : V}
    (hne : v ≠ 0) (hv : v ∈ weightSp E mu) (a b : Fin n) (hab : a ≠ b) (he : E a b v = 0) : mu b ≤ mu a := by
  have hba : b ≠ a := hab.symm
  have hef : E a b * E b a - E b a * E a b = E a a - E b b := by
    have := rel a b b a
    simpa using this
  have h1 : E a a * E a b - E a b * E a a = E a b := by
    have := rel a a a b
    simpa [hba] using this
  have h2 : E b b * E a b - E a b * E b b = - E a b := by
    have := rel b b a b
    simpa [hba] using this
  have h3 : E a a * E b a - E b a * E a a = - E b a := by
    have := rel a a b a
    simpa [hab] using this
  have h4 : E b b * E b a - E b a * E b b = E b a := by
    have := rel b b b a
    simpa [hab] using this
  have hva : E a a v = (mu a : K) • v := (v2rep_mem_weightSp E mu v).1 hv a
  have hvb : E b b v = (mu b : K) • v := (v2rep_mem_weightSp E mu v).1 hv b
  have hhf : (E a a - E b b) * E b a - E b a * (E a a - E b b) = -(2 • E b a) := by
    have : (E a a - E b b) * E b a - E b a * (E a a - E b b) =
        (E a a * E b a - E b a * E a a) - (E b b * E b a - E b a * E b b) := by noncomm_ring
    rw [this, h3, h4, two_smul]; abel
  have hhe : (E a a - E b b) * E a b - E a b * (E a a - E b b) = 2 • E a b := by
    have : (E a a - E b b) * E a b - E a b * (E a a - E b b) =
        (E a a * E a b - E a b * E a a) - (E b b * E a b - E a b * E b b) := by noncomm_ring
    rw [this, h1, h2, two_smul]; abel
  have hhv : (E a a - E b b) v = ((mu a : K) - (mu b : K)) • v := by
    rw [LinearMap.sub_apply, hva, hvb, sub_smul]
  by_cases hh0 : E a a - E b b = 0
  · rw [hh0, LinearMap.zero_apply] at hhv
    rcases smul_eq_zero.1 hhv.symm with h | h
    · exact (Int.cast_injective (sub_eq_zero.1 h)).ge
    · exact absurd h hne
  have t : IsSl2Triple (E a a - E b b) (E a b) (E b a) :=
    { h_ne_zero := hh0
      lie_e_f := by rw [Ring.lie_def]; exact hef
      lie_h_e_nsmul := by rw [Ring.lie_def]; exact hhe
      lie_h_f_nsmul := by rw [Ring.lie_def]; exact hhf }
  have P : t.HasPrimitiveVectorWith v ((mu a : K) - (mu b : K)) :=
    { ne_zero := hne
      lie_h := by rw [Module.End.lie_apply]; exact hhv
      lie_e := by rw [Module.End.lie_apply]; exact he }
  obtain ⟨m, hm⟩ := P.exists_nat
  have : ((mu a - mu b : ℤ) : K) = ((m : ℤ) : K) := by push_cast; exact hm
  have := Int.cast_injective this
  omega

/- English proof (translation)
Introduce `a b hab`. Break down `hab.lt_or_eq with h | h` into its components or cases. Conclude with `cr_dom E rel hv.1 hv.2.1 a b h.ne (hv.2.2 a b h)`. Rewrite using `[h]`.
-/
theorem cr_hwv_dom [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (rel : SatisfiesGLRelations E) {mu : Fin n → ℤ} {v : V}
    (hv : IsHWV E mu v) : Dominant mu := by
  intro a b hab
  rcases hab.lt_or_eq with h | h
  · exact cr_dom E rel hv.1 hv.2.1 a b h.ne (hv.2.2 a b h)
  · rw [h]

/- English proof (translation)
Assume the negation of the conclusion as `hd`. Apply `hne` to reduce the goal to its premises. Establish `: isotypicPartIn E Wx mu = ⊥`. Rewrite using `[isotypicPartIn, Submodule.span_eq_bot]`. Introduce and unpack `y ⟨u, _, v, _, hv, rfl⟩`.

Conclude with `absurd (cr_hwv_dom E rel hv) hd`. Rewrite `hx` using `[this]`. Conclude with `(Submodule.mem_bot K).1 hx`.
-/
theorem cr_isoIn_dom [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (rel : SatisfiesGLRelations E) (Wx : Submodule K V)
    {mu : Fin n → ℤ} {x : V} (hx : x ∈ isotypicPartIn E Wx mu) (hne : x ≠ 0) : Dominant mu := by
  by_contra hd
  apply hne
  have : isotypicPartIn E Wx mu = ⊥ := by
    rw [isotypicPartIn, Submodule.span_eq_bot]
    rintro y ⟨u, _, v, _, hv, rfl⟩
    exact absurd (cr_hwv_dom E rel hv) hd
  rw [this] at hx
  exact (Submodule.mem_bot K).1 hx

end Formalism.MainNotions.G.GLWeightTheory

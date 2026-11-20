import Formalism.SharpRestriction.GrowthBounds.RootWeights.RaiseLowerPowCommutatorOnWeight

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

inductive IsLoweringWord (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) : (Fin n → ℤ) → V → Prop
  | base : IsLoweringWord E lam v lam v
  | step (c d : Fin n) (h : d < c) (l : ℕ) (hl : 1 ≤ l) (nu : Fin n → ℤ) (x : V) :
      IsLoweringWord E lam v nu x → IsLoweringWord E lam v (nu + (l : ℤ) • rootW c d) (divPowE E c d l x)

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `zero => simp`. Consider the case `succ l ih`. Establish `e : nu + ((l + 1 : ℕ) : ℤ) • rootW a b = nu + (l : ℤ) • rootW a b + rootW a b` using `by push_cast; rw [add_smul, one_smul, add_assoc]`. Rewrite using `[e, weightHeightAscending_add_root, ih]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weight_height_add_root_smul (nu : Fin n → ℤ) (a b : Fin n) (l : ℕ) :
    weightHeightAscending (nu + (l : ℤ) • rootW a b) = weightHeightAscending nu + l * (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) := by
  induction l with
  | zero => simp
  | succ l ih =>
    have e : nu + ((l + 1 : ℕ) : ℤ) • rootW a b = nu + (l : ℤ) • rootW a b + rootW a b := by
      push_cast; rw [add_smul, one_smul, add_assoc]
    rw [e, weightHeightAscending_add_root, ih]; push_cast; ring

/- English proof (translation)
Rewrite using `[divPowE, LinearMap.smul_apply]`. Conclude with `Submodule.smul_mem _ _ (integral_operator_pow_shifts_weight hE hx a c j)`.
-/
theorem dividedPower_mem_shifted_weight {E : GLOps n (KK O) V} (hE : IsGLRep E) {nu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E nu)
    (a c : Fin n) (j : ℕ) : divPowE E a c j x ∈ weightSp E (nu + (j : ℤ) • rootW a c) := by
  rw [divPowE, LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (integral_operator_pow_shifts_weight hE hx a c j)

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `base => exact hv`. Consider the case `step c d _ l _ nu x _ ih => exact dividedPower_mem_shifted_weight hE ih c d l`.
-/
theorem loweringWord_mem_weightSpace {E : GLOps n (KK O) V} (hE : IsGLRep E) {lam : Fin n → ℤ} {v : V} (hv : v ∈ weightSp E lam)
    {nu : Fin n → ℤ} {x : V} (h : IsLoweringWord E lam v nu x) : x ∈ weightSp E nu := by
  induction h with
  | base => exact hv
  | step c d _ l _ nu x _ ih => exact dividedPower_mem_shifted_weight hE ih c d l

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `base => exact le_refl _`. Consider the case `step c d hdc l _ nu x _ ih`. Rewrite using `[weight_height_add_root_smul]`. Establish `h1 : ((d : ℕ) : ℤ) < ((c : ℕ) : ℤ)` using `by exact_mod_cast hdc`.

Establish `: (0 : ℤ) ≤ (l : ℤ) * (((c : ℕ) : ℤ) - ((d : ℕ) : ℤ))` using `mul_nonneg (by positivity) (by omega)`. Use linear arithmetic over natural numbers and integers.
-/
theorem loweringWord_height_ge_highest {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    {nu : Fin n → ℤ} {x : V} (h : IsLoweringWord E lam v nu x) : weightHeightAscending lam ≤ weightHeightAscending nu := by
  induction h with
  | base => exact le_refl _
  | step c d hdc l _ nu x _ ih =>
    rw [weight_height_add_root_smul]
    have h1 : ((d : ℕ) : ℤ) < ((c : ℕ) : ℤ) := by exact_mod_cast hdc
    have : (0 : ℤ) ≤ (l : ℤ) * (((c : ℕ) : ℤ) - ((d : ℕ) : ℤ)) := mul_nonneg (by positivity) (by omega)
    omega

def loweringSpanOfHeight (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) (N : ℤ) : Submodule O V :=
  Submodule.span O {x | ∃ nu, IsLoweringWord E lam v nu x ∧ weightHeightAscending nu ≤ weightHeightAscending lam + N}

/- English proof (translation)
Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `x ⟨nu, h1, h2⟩`. Conclude with `⟨nu, h1, by omega⟩`.
-/
theorem loweringSpan_height_monotone (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) {N N' : ℤ} (h : N ≤ N') :
    loweringSpanOfHeight (O := O) E lam v N ≤ loweringSpanOfHeight (O := O) E lam v N' := by
  refine Submodule.span_mono ?_
  rintro x ⟨nu, h1, h2⟩
  exact ⟨nu, h1, by omega⟩

/- English proof (translation)
Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => obtain ⟨nu, h1, h2⟩ := hy`. Conclude with `h nu y h1 h2`. Consider the case `zero => simp`.

Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `Submodule.add_mem _ hy hz`. Consider the case `smul r y _ hy`. Rewrite using `[← algebraMap_smul (KK O) r y, map_smul, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem loweringSpan_map_le_of_words {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} {N : ℤ} {L : Submodule O V}
    (T : Module.End (KK O) V)
    (h : ∀ nu x, IsLoweringWord E lam v nu x → weightHeightAscending nu ≤ weightHeightAscending lam + N → T x ∈ L) :
    ∀ y ∈ loweringSpanOfHeight (O := O) E lam v N, T y ∈ L := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨nu, h1, h2⟩ := hy; exact h nu y h1 h2
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy =>
    rw [← algebraMap_smul (KK O) r y, map_smul, algebraMap_smul]; exact Submodule.smul_mem _ _ hy

/- English proof (translation)
Use `loweringSpan_map_le_of_words _ fun nu x h1 h2 => ?_` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos i with rfl | hi` into its components or cases. Establish `: divPowE E c d 0 x = x` using `by simp [divPowE]`. Rewrite using `[this]`. Conclude with `Submodule.subset_span ⟨nu, h1, by simpa using h2⟩`.

Conclude with `Submodule.subset_span ⟨_, IsLoweringWord.step c d hdc i hi nu x h1, by rw [weight_height_add_root_smul]; omega⟩`.
-/
theorem loweringSpan_lower_dividedPower_mem (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) {c d : Fin n} (hdc : d < c) (i : ℕ) (M : ℤ) :
    ∀ y ∈ loweringSpanOfHeight (O := O) E lam v M,
      divPowE E c d i y ∈ loweringSpanOfHeight (O := O) E lam v (M + i * (((c : ℕ) : ℤ) - ((d : ℕ) : ℤ))) := by
  refine loweringSpan_map_le_of_words _ fun nu x h1 h2 => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have : divPowE E c d 0 x = x := by simp [divPowE]
    rw [this]
    exact Submodule.subset_span ⟨nu, h1, by simpa using h2⟩
  · exact Submodule.subset_span ⟨_, IsLoweringWord.step c d hdc i hi nu x h1, by rw [weight_height_add_root_smul]; omega⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dividedPower_eq_divPowE (E : GLOps n (KK O) V) (a b : Fin n) (k : ℕ) : dividedPower (KK O) (E a b) k = divPowE E a b k := rfl

/- English proof (translation)
Rewrite using `[dividedPower, dividedPower, neg_pow, smul_smul]`. Use `push_cast`. Rewrite using `[mul_comm, ← smul_smul]`. Use `congr 1`. Apply the tactic sequence `rcases Nat.even_or_odd j with h | h <;> simp [h.neg_one_pow]`.
-/
theorem dividedPower_neg_sign (X : Module.End (KK O) V) (j : ℕ) :
    dividedPower (KK O) (-X) j = (((-1 : ℤ) ^ j : ℤ) : KK O) • dividedPower (KK O) X j := by
  rw [dividedPower, dividedPower, neg_pow, smul_smul]
  push_cast
  rw [mul_comm, ← smul_smul]
  congr 1
  rcases Nat.even_or_odd j with h | h <;> simp [h.neg_one_pow]

/- English proof (translation)
Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ N IH`. Introduce `nu x hLW hht a b hab k`. Consider the cases of `hLW with`. Consider the case `base`.

Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases. Establish `: divPowE E a b 0 v = v` using `by simp [divPowE]`. Rewrite using `[this]`. Conclude with `Submodule.subset_span ⟨lam, IsLoweringWord.base, by omega⟩`. Take `⟨k', rfl⟩ : ∃ k', k = k' + 1` from `⟨k - 1, by omega⟩`.

Establish `: divPowE E a b (k' + 1) v = 0`. Rewrite using `[divPowE, LinearMap.smul_apply, pow_succ, Module.End.mul_apply, hv.2.2 a b hab, map_zero, smul_zero]`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`. Consider the case `step c d hdc l hl nu' x' hLW'`.

Establish `hgap : (1 : ℤ) ≤ ((c : ℕ) : ℤ) - ((d : ℕ) : ℤ)`. Establish `: ((d : ℕ) : ℤ) < ((c : ℕ) : ℤ)` using `by exact_mod_cast hdc`. Use linear arithmetic over natural numbers and integers. Establish `hab' : ((a : ℕ) : ℤ) < ((b : ℕ) : ℤ)` using `by exact_mod_cast hab`. Rewrite `hht` using `[weight_height_add_root_smul]`.

Establish `hlow` using `loweringWord_height_ge_highest hLW'`. Establish `hlg : (1 : ℤ) ≤ (l : ℤ) * (((c : ℕ) : ℤ) - ((d : ℕ) : ℤ))`. Establish `h1 : (1 : ℤ) ≤ (l : ℤ)` using `by exact_mod_cast hl`. Use the polynomial consequences of the given equalities and inequalities. Take `⟨M, hM⟩ : ∃ M : ℕ, (M : ℤ) = N - (l : ℤ) * (((c : ℕ) : ℤ) - ((d : ℕ) : ℤ))` from `⟨(N - (l : ℤ) * (((c : ℕ) : ℤ) - ((d : ℕ) : ℤ))).toNat, by omega⟩`.

Establish `hMN : M < N` using `by omega`. Establish `hx'M : weightHeightAscending nu' ≤ weightHeightAscending lam + M` using `by omega`. Establish `IHM` using `IH M hMN`. Establish `RL : ∀ a' b' : Fin n, a' < b' → ∀ k' : ℕ, ∀ y ∈ loweringSpanOfHeight (O` using `O) E lam v M, divPowE E a' b' k' y ∈ loweringSpanOfHeight (O := O) E lam v M := fun a' b' h' k' => loweringSpan_map_le_of_words _ fun nu2 x2 h1 h2 => IHM nu2 x2 h1 h2 a' b' h' k'`. Establish `hx'w` using `loweringWord_mem_weightSpace hE hv.2.1 hLW'`.

Distinguish the cases in `hcase : c = b ∧ d = a`. Take `⟨rfl, rfl⟩` from `hcase`. Rewrite using `[raise_lower_dividedPower_binomial hE (ne_of_lt hab) hx'w k l]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Use `split_ifs with hj`.

Use `intCast_smul_mem_submodule _ _ ?_` and prove the remaining obligations. Use `loweringSpan_height_monotone E lam v ?_ (loweringSpan_lower_dividedPower_mem E lam v hdc (l - j) M _ (IHM nu' x' hLW' hx'M d c hab (k - j)))` and prove the remaining obligations. Establish `: ((l - j : ℕ) : ℤ) ≤ (l : ℤ)` using `by exact_mod_cast Nat.sub_le l j`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `Submodule.zero_mem _`.

Establish `key : ∀ Z : Module.End (KK O) V, E a b * E c d = E c d * E a b + Z → Z * E c d = E c d * Z → E a b * Z = Z * E a b → (∀ j : ℕ, ∀ y ∈ loweringSpanOfHeight (O` using `O) E lam v M, dividedPower (KK O) Z j y ∈ loweringSpanOfHeight (O := O) E lam v (M + j * (((c : ℕ) : ℤ) - ((d : ℕ) : ℤ)))) → divPowE E a b k (divPowE E c d l x') ∈ loweringSpanOfHeight (O := O) E lam v N := by`. Introduce `Z h1 h2 h3 h4`. Establish `e` using `heisenberg_dividedPower_expansion (K := KK O) h1 h2 h3 k l`. Establish `e2 : divPowE E a b k (divPowE E c d l x') = (dividedPower (KK O) (E a b) k * dividedPower (KK O) (E c d) l) x'` using `rfl`. Rewrite using `[e2, e, LinearMap.sum_apply]`.

Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Use `split_ifs with hj`. Rewrite using `[Module.End.mul_apply, Module.End.mul_apply]`. Establish `s1` using `IHM nu' x' hLW' hx'M a b hab (k - j)`. Establish `s2` using `h4 j _ s1`.

Establish `s3` using `loweringSpan_lower_dividedPower_mem E lam v hdc (l - j) _ _ s2`. Use `loweringSpan_height_monotone E lam v ?_ s3` and prove the remaining obligations. Move the coercions through the operations in `[Nat.cast_sub hj]`. Rewrite using `[hM]`. Put the polynomial expressions in normal form.

Conclude with `le_refl _`. Simplify using the standard rewrite rules. Establish `hr` using `hE.1 a b c d`. Distinguish the cases in `hbc : b = c`. Establish `hda : d ≠ a` using `fun e => hcase ⟨hbc.symm, e⟩`.

Substitute `hbc` using the available equality. Use `key (E a d) ?_ ?_ ?_ ?_` and prove the remaining obligations. Rewrite `hr` using `[if_pos rfl, if_neg hda, sub_zero]`. Rewrite using `[← hr]`. Normalize the expressions using the abelian group laws.

Use `hE.1 a d b d` as an intermediate fact. Rewrite `this` using `[if_neg (ne_of_lt hdc), if_neg hda, sub_zero]`. Conclude with `sub_eq_zero.1 this`. Use `hE.1 a b a d` as an intermediate fact. Rewrite `this` using `[if_neg (ne_of_gt hab), if_neg hda, sub_zero]`.

Conclude with `sub_eq_zero.1 this`. Introduce `j y hy`. Rewrite using `[dividedPower_eq_divPowE]`. Break down `lt_or_gt_of_ne hda with h | h` into its components or cases. Establish `hh : ((d : ℕ) : ℤ) < ((a : ℕ) : ℤ)` using `by exact_mod_cast h`.

Use `loweringSpan_height_monotone E lam v ?_ (loweringSpan_lower_dividedPower_mem E lam v h j M y hy)` and prove the remaining obligations. Establish `: (0 : ℤ) ≤ (j : ℤ)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Use `loweringSpan_height_monotone E lam v ?_ (RL a d h j y hy)` and prove the remaining obligations. Establish `: (0 : ℤ) ≤ (j : ℤ)` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Distinguish the cases in `hda : d = a`. Substitute `hda` using the available equality. Use `key (-E c b) ?_ ?_ ?_ ?_` and prove the remaining obligations. Rewrite `hr` using `[if_neg hbc, if_pos rfl, zero_sub]`.

Rewrite using `[← hr]`. Normalize the expressions using the abelian group laws. Use `hE.1 c b c d` as an intermediate fact. Rewrite `this` using `[if_neg hbc, if_neg (ne_of_lt hdc), sub_zero]`. Rewrite using `[neg_mul, mul_neg, sub_eq_zero.1 this]`.

Use `hE.1 d b c b` as an intermediate fact. Rewrite `this` using `[if_neg hbc, if_neg (ne_of_gt hab), sub_zero]`. Rewrite using `[neg_mul, mul_neg, sub_eq_zero.1 this]`. Introduce `j y hy`. Rewrite using `[dividedPower_neg_sign, LinearMap.smul_apply, dividedPower_eq_divPowE]`.

Use `intCast_smul_mem_submodule _ _ ?_` and prove the remaining obligations. Break down `lt_or_gt_of_ne hbc with h | h` into its components or cases. Establish `hh : ((b : ℕ) : ℤ) < ((c : ℕ) : ℤ)` using `by exact_mod_cast h`. Use `loweringSpan_height_monotone E lam v ?_ (loweringSpan_lower_dividedPower_mem E lam v h j M y hy)` and prove the remaining obligations. Establish `: (0 : ℤ) ≤ (j : ℤ)` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Use `loweringSpan_height_monotone E lam v ?_ (RL c b h j y hy)` and prove the remaining obligations. Establish `: (0 : ℤ) ≤ (j : ℤ)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Use `key 0 ?_ (by simp) (by simp) ?_` and prove the remaining obligations.

Rewrite `hr` using `[if_neg hbc, if_neg hda, sub_zero]`. Rewrite using `[add_zero]`. Conclude with `sub_eq_zero.1 hr`. Introduce `j y hy`. Break down `Nat.eq_zero_or_pos j with rfl | hj` into its components or cases.

Simplify `hy` using `[dividedPower]`. Establish `: dividedPower (KK O) (0 : Module.End (KK O) V) j = 0`. Rewrite using `[dividedPower, zero_pow (by omega), smul_zero]`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`.
-/
theorem raising_dividedPower_loweringSpan [CharZero (KK O)] {E : GLOps n (KK O) V} (hE : IsGLRep E) {lam : Fin n → ℤ} {v : V}
    (hv : IsHWV E lam v) (N : ℕ) : ∀ nu x, IsLoweringWord E lam v nu x → weightHeightAscending nu ≤ weightHeightAscending lam + N →
      ∀ a b : Fin n, a < b → ∀ k : ℕ, divPowE E a b k x ∈ loweringSpanOfHeight (O := O) E lam v N := by
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro nu x hLW hht a b hab k
  cases hLW with
  | base =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : divPowE E a b 0 v = v := by simp [divPowE]
      rw [this]
      exact Submodule.subset_span ⟨lam, IsLoweringWord.base, by omega⟩
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have : divPowE E a b (k' + 1) v = 0 := by
        rw [divPowE, LinearMap.smul_apply, pow_succ, Module.End.mul_apply, hv.2.2 a b hab, map_zero, smul_zero]
      rw [this]; exact Submodule.zero_mem _
  | step c d hdc l hl nu' x' hLW' =>
    have hgap : (1 : ℤ) ≤ ((c : ℕ) : ℤ) - ((d : ℕ) : ℤ) := by
      have : ((d : ℕ) : ℤ) < ((c : ℕ) : ℤ) := by exact_mod_cast hdc
      omega
    have hab' : ((a : ℕ) : ℤ) < ((b : ℕ) : ℤ) := by exact_mod_cast hab
    rw [weight_height_add_root_smul] at hht
    have hlow := loweringWord_height_ge_highest hLW'
    have hlg : (1 : ℤ) ≤ (l : ℤ) * (((c : ℕ) : ℤ) - ((d : ℕ) : ℤ)) := by
      have h1 : (1 : ℤ) ≤ (l : ℤ) := by exact_mod_cast hl
      nlinarith
    obtain ⟨M, hM⟩ : ∃ M : ℕ, (M : ℤ) = N - (l : ℤ) * (((c : ℕ) : ℤ) - ((d : ℕ) : ℤ)) :=
      ⟨(N - (l : ℤ) * (((c : ℕ) : ℤ) - ((d : ℕ) : ℤ))).toNat, by omega⟩
    have hMN : M < N := by omega
    have hx'M : weightHeightAscending nu' ≤ weightHeightAscending lam + M := by omega
    have IHM := IH M hMN
    have RL : ∀ a' b' : Fin n, a' < b' → ∀ k' : ℕ, ∀ y ∈ loweringSpanOfHeight (O := O) E lam v M,
        divPowE E a' b' k' y ∈ loweringSpanOfHeight (O := O) E lam v M := fun a' b' h' k' =>
      loweringSpan_map_le_of_words _ fun nu2 x2 h1 h2 => IHM nu2 x2 h1 h2 a' b' h' k'
    have hx'w := loweringWord_mem_weightSpace hE hv.2.1 hLW'
    by_cases hcase : c = b ∧ d = a
    · obtain ⟨rfl, rfl⟩ := hcase
      rw [raise_lower_dividedPower_binomial hE (ne_of_lt hab) hx'w k l]
      refine Submodule.sum_mem _ fun j _ => ?_
      split_ifs with hj
      · refine intCast_smul_mem_submodule _ _ ?_
        refine loweringSpan_height_monotone E lam v ?_ (loweringSpan_lower_dividedPower_mem E lam v hdc (l - j) M _ (IHM nu' x' hLW' hx'M d c hab (k - j)))
        have : ((l - j : ℕ) : ℤ) ≤ (l : ℤ) := by exact_mod_cast Nat.sub_le l j
        nlinarith
      · exact Submodule.zero_mem _
    ·
      have key : ∀ Z : Module.End (KK O) V, E a b * E c d = E c d * E a b + Z → Z * E c d = E c d * Z →
          E a b * Z = Z * E a b →
          (∀ j : ℕ, ∀ y ∈ loweringSpanOfHeight (O := O) E lam v M,
            dividedPower (KK O) Z j y ∈ loweringSpanOfHeight (O := O) E lam v (M + j * (((c : ℕ) : ℤ) - ((d : ℕ) : ℤ)))) →
          divPowE E a b k (divPowE E c d l x') ∈ loweringSpanOfHeight (O := O) E lam v N := by
        intro Z h1 h2 h3 h4
        have e := heisenberg_dividedPower_expansion (K := KK O) h1 h2 h3 k l
        have e2 : divPowE E a b k (divPowE E c d l x') =
            (dividedPower (KK O) (E a b) k * dividedPower (KK O) (E c d) l) x' := rfl
        rw [e2, e, LinearMap.sum_apply]
        refine Submodule.sum_mem _ fun j _ => ?_
        split_ifs with hj
        · rw [Module.End.mul_apply, Module.End.mul_apply]
          have s1 := IHM nu' x' hLW' hx'M a b hab (k - j)
          have s2 := h4 j _ s1
          have s3 := loweringSpan_lower_dividedPower_mem E lam v hdc (l - j) _ _ s2
          refine loweringSpan_height_monotone E lam v ?_ s3
          push_cast [Nat.cast_sub hj]
          rw [hM]; ring_nf; exact le_refl _
        · simp
      have hr := hE.1 a b c d
      by_cases hbc : b = c
      · have hda : d ≠ a := fun e => hcase ⟨hbc.symm, e⟩
        subst hbc
        refine key (E a d) ?_ ?_ ?_ ?_
        · rw [if_pos rfl, if_neg hda, sub_zero] at hr
          rw [← hr]; abel
        · have := hE.1 a d b d
          rw [if_neg (ne_of_lt hdc), if_neg hda, sub_zero] at this
          exact sub_eq_zero.1 this
        · have := hE.1 a b a d
          rw [if_neg (ne_of_gt hab), if_neg hda, sub_zero] at this
          exact sub_eq_zero.1 this
        · intro j y hy
          rw [dividedPower_eq_divPowE]
          rcases lt_or_gt_of_ne hda with h | h
          · have hh : ((d : ℕ) : ℤ) < ((a : ℕ) : ℤ) := by exact_mod_cast h
            refine loweringSpan_height_monotone E lam v ?_ (loweringSpan_lower_dividedPower_mem E lam v h j M y hy)
            have : (0 : ℤ) ≤ (j : ℤ) := by positivity
            nlinarith
          · refine loweringSpan_height_monotone E lam v ?_ (RL a d h j y hy)
            have : (0 : ℤ) ≤ (j : ℤ) := by positivity
            nlinarith
      · by_cases hda : d = a
        · subst hda
          refine key (-E c b) ?_ ?_ ?_ ?_
          · rw [if_neg hbc, if_pos rfl, zero_sub] at hr
            rw [← hr]; abel
          · have := hE.1 c b c d
            rw [if_neg hbc, if_neg (ne_of_lt hdc), sub_zero] at this
            rw [neg_mul, mul_neg, sub_eq_zero.1 this]
          · have := hE.1 d b c b
            rw [if_neg hbc, if_neg (ne_of_gt hab), sub_zero] at this
            rw [neg_mul, mul_neg, sub_eq_zero.1 this]
          · intro j y hy
            rw [dividedPower_neg_sign, LinearMap.smul_apply, dividedPower_eq_divPowE]
            refine intCast_smul_mem_submodule _ _ ?_
            rcases lt_or_gt_of_ne hbc with h | h
            · have hh : ((b : ℕ) : ℤ) < ((c : ℕ) : ℤ) := by exact_mod_cast h
              refine loweringSpan_height_monotone E lam v ?_ (loweringSpan_lower_dividedPower_mem E lam v h j M y hy)
              have : (0 : ℤ) ≤ (j : ℤ) := by positivity
              nlinarith
            · refine loweringSpan_height_monotone E lam v ?_ (RL c b h j y hy)
              have : (0 : ℤ) ≤ (j : ℤ) := by positivity
              nlinarith
        · refine key 0 ?_ (by simp) (by simp) ?_
          · rw [if_neg hbc, if_neg hda, sub_zero] at hr
            rw [add_zero]; exact sub_eq_zero.1 hr
          · intro j y hy
            rcases Nat.eq_zero_or_pos j with rfl | hj
            · simpa [dividedPower] using hy
            · have : dividedPower (KK O) (0 : Module.End (KK O) V) j = 0 := by
                rw [dividedPower, zero_pow (by omega), smul_zero]
              rw [this]; exact Submodule.zero_mem _

end hw

end Formalism.MainNotions.G.GLWeightTheory

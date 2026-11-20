import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.EquivariantL2Space
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.OneParameterSubgroups.ExpChart

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base
open ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
open Matrix Formalism.QuantumDeterminants
open scoped Matrix.Norms.Operator

def levB (k r : ℕ) (a : Fin (2 * r + k + 1)) : ℕ :=
  if a.val < r then a.val else if a.val ≤ r + k then r else a.val - k

def flipB (k r : ℕ) (a : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if a.val < r ∨ r + k < a.val then ⟨2 * r + k - a.val, by omega⟩ else a

def sgnB (k r : ℕ) (a : Fin (2 * r + k + 1)) : ℂ := if a.val = r + k then -1 else 1

variable {k r : ℕ}

/- English proof (translation)
Establish `ha` using `a.isLt`. Unfold `levB`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem levB_le (a : Fin (2 * r + k + 1)) : levB k r a ≤ 2 * r := by
  have ha := a.isLt
  unfold levB
  split_ifs <;> omega

/- English proof (translation)
Unfold `flipB`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem flipB_val (a : Fin (2 * r + k + 1)) :
    (flipB k r a).val = if a.val < r ∨ r + k < a.val then 2 * r + k - a.val else a.val := by
  unfold flipB
  split_ifs <;> rfl

/- English proof (translation)
Establish `ha` using `a.isLt`. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[flipB_val, flipB_val]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem flipB_flipB (a : Fin (2 * r + k + 1)) : flipB k r (flipB k r a) = a := by
  have ha := a.isLt
  apply Fin.ext
  rw [flipB_val, flipB_val]
  split_ifs <;> omega

/- English proof (translation)
Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`. Simplify using `only [Hpk, sgnB, Fin.ext_iff, flipB_val]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega | norm_num`.
-/
theorem Hpk_apply (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = flipB k r i then sgnB k r i else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, sgnB, Fin.ext_iff, flipB_val]
  split_ifs <;> first | rfl | omega | norm_num

/- English proof (translation)
Establish `ha` using `a.isLt`. Simplify using `only [sgnB, flipB_val]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
theorem sgnB_flip (a : Fin (2 * r + k + 1)) : sgnB k r (flipB k r a) = sgnB k r a := by
  have ha := a.isLt
  simp only [sgnB, flipB_val]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Simplify using `[Matrix.mul_apply, Hpk_apply, ite_mul]`.
-/
theorem Hpk_mul_apply (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (Hpk k r * X) i j = sgnB k r i * X (flipB k r i) j := by
  simp [Matrix.mul_apply, Hpk_apply, ite_mul]

/- English proof (translation)
Establish `h : ∀ l, (j = flipB k r l) ↔ (l = flipB k r j)` using `fun l => ⟨fun h => by rw [h, flipB_flipB], fun h => by rw [h, flipB_flipB]⟩`. Simplify using `[Matrix.mul_apply, Hpk_apply, h, mul_ite, sgnB_flip]`.
-/
theorem mul_Hpk_apply (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (X * Hpk k r) i j = X i (flipB k r j) * sgnB k r j := by
  have h : ∀ l, (j = flipB k r l) ↔ (l = flipB k r j) := fun l =>
    ⟨fun h => by rw [h, flipB_flipB], fun h => by rw [h, flipB_flipB]⟩
  simp [Matrix.mul_apply, Hpk_apply, h, mul_ite, sgnB_flip]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Hpk_mul_apply, Hpk_apply, flipB_flipB, sgnB_flip, Matrix.one_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl]`.

Unfold `sgnB`. Apply the tactic sequence `split_ifs <;> norm_num`. Rewrite using `[if_neg (Ne.symm h), if_neg h, mul_zero]`.
-/
theorem Hpk_sq : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Hpk_mul_apply, Hpk_apply, flipB_flipB, sgnB_flip, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl]
    unfold sgnB
    split_ifs <;> norm_num
  · rw [if_neg (Ne.symm h), if_neg h, mul_zero]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[conjTranspose_apply, Hpk_apply, Hpk_apply]`. Distinguish the cases in `h : j = flipB k r i`. Establish `h' : i = flipB k r j` using `by rw [h, flipB_flipB]`. Rewrite using `[if_pos h, if_pos h', h, sgnB_flip]`.

Unfold `sgnB`. Apply the tactic sequence `split_ifs <;> simp`. Establish `h' : ¬ i = flipB k r j` using `fun h' => h (by rw [h', flipB_flipB])`. Rewrite using `[if_neg h, if_neg h', star_zero]`.
-/
theorem Hpk_herm : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [conjTranspose_apply, Hpk_apply, Hpk_apply]
  by_cases h : j = flipB k r i
  · have h' : i = flipB k r j := by rw [h, flipB_flipB]
    rw [if_pos h, if_pos h', h, sgnB_flip]
    unfold sgnB
    split_ifs <;> simp
  · have h' : ¬ i = flipB k r j := fun h' => h (by rw [h', flipB_flipB])
    rw [if_neg h, if_neg h', star_zero]

/- English proof (translation)
Establish `ha` using `a.isLt`. Simplify using `only [levB, flipB_val]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
private lemma levB_add_levB_flipB_eq_two_mul (a : Fin (2 * r + k + 1)) :
    levB k r a + levB k r (flipB k r a) = 2 * r := by
  have ha := a.isLt
  simp only [levB, flipB_val]
  split_ifs <;> omega

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij X hX a b hab`. Conclude with `hX a b (by omega)`. Introduce `i j x y hx hy a b hab`. Rewrite using `[Matrix.mul_apply]`.

Use `Finset.sum_eq_zero (fun c _ => ?_)` and prove the remaining obligations. Distinguish the cases in `h1 : levB k r c < levB k r a + i + 1`. Rewrite using `[hx a c h1, zero_mul]`. Rewrite using `[hy c b (by omega), mul_zero]`. Rewrite using `[eq_bot_iff]`.

Introduce `X hX`. Rewrite using `[Submodule.mem_bot]`. Use extensionality with `a b`. Use `levB_le (k := k) (r := r) b` as an intermediate fact. Conclude with `hX a b (by omega)`.
-/
theorem isFilB : IsFil (levF (levB k r)) (2 * r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij X hX a b hab
    exact hX a b (by omega)
  · intro i j x y hx hy a b hab
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun c _ => ?_)
    by_cases h1 : levB k r c < levB k r a + i + 1
    · rw [hx a c h1, zero_mul]
    · rw [hy c b (by omega), mul_zero]
  · rw [eq_bot_iff]
    intro X hX
    rw [Submodule.mem_bot]
    ext a b
    have := levB_le (k := k) (r := r) b
    exact hX a b (by omega)

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y show Hpk k r * (x * y)ᴴ * Hpk k r = Hpk k r * yᴴ * Hpk k r * (Hpk k r * xᴴ * Hpk k r)`. Rewrite using `[conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (Hpk k r) (Hpk k r), Hpk_sq, Matrix.one_mul]`.

Use `show Hpk k r * (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r = 1`. Rewrite using `[conjTranspose_one, Matrix.mul_one, Hpk_sq]`. Introduce `x hx`. Establish `hx' : ∀ a b, levB k r b < levB k r a + 0 + 1 → x a b = 0` using `hx`. Use `show ∀ a b, levB k r b < levB k r a + 0 + 1 → (Hpk k r * xᴴ * Hpk k r) a b = 0`.

Introduce `a b hab`. Establish `h1` using `levB_add_levB_flipB_eq_two_mul (k := k) (r := r) a`. Establish `h2` using `levB_add_levB_flipB_eq_two_mul (k := k) (r := r) b`. Establish `hz : x (flipB k r b) (flipB k r a) = 0` using `hx' _ _ (by omega)`. Rewrite using `[mul_Hpk_apply, Hpk_mul_apply, conjTranspose_apply, hz, star_zero, mul_zero, zero_mul]`.
-/
theorem isAdjB : IsAdj (levF (levB k r)) (adjH (Hpk k r)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    show Hpk k r * (x * y)ᴴ * Hpk k r = Hpk k r * yᴴ * Hpk k r * (Hpk k r * xᴴ * Hpk k r)
    rw [conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Hpk k r) (Hpk k r), Hpk_sq, Matrix.one_mul]
  · show Hpk k r * (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r = 1
    rw [conjTranspose_one, Matrix.mul_one, Hpk_sq]
  · intro x hx
    have hx' : ∀ a b, levB k r b < levB k r a + 0 + 1 → x a b = 0 := hx
    show ∀ a b, levB k r b < levB k r a + 0 + 1 → (Hpk k r * xᴴ * Hpk k r) a b = 0
    intro a b hab
    have h1 := levB_add_levB_flipB_eq_two_mul (k := k) (r := r) a
    have h2 := levB_add_levB_flipB_eq_two_mul (k := k) (r := r) b
    have hz : x (flipB k r b) (flipB k r a) = 0 := hx' _ _ (by omega)
    rw [mul_Hpk_apply, Hpk_mul_apply, conjTranspose_apply, hz, star_zero, mul_zero, zero_mul]

/- English proof (translation)
Use extensionality with `g`. Rewrite using `[mem_grpN_iff _ _ Hpk_sq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hU, he, hm⟩`. Use `⟨?_, hU⟩` and prove the remaining obligations.

Establish `hf : ∀ (j : Fin (2 * r + k + 1)) (a : ℕ) (ha : a < r), j.val + a ≤ 2 * r + k → g ⟨2 * r + k - a, by omega⟩ j = if (⟨2 * r + k - a, by omega⟩ : Fin (2 * r + k + 1)) = j then 1 else 0`. Introduce `j a`. Proceed by induction on `a using Nat.strong_induction_on with`. Consider the case `_ a ih`. Introduce `ha hja`.

Establish `h1` using `congrFun (congrFun hU (eI k r ⟨a, ha⟩)) j`. Rewrite `h1` using `[Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single (eI k r ⟨a, ha⟩)]`. Rewrite `h1` using `[conjTranspose_apply, he ⟨a, ha⟩ _ le_rfl, if_pos rfl, Hpk_mul_apply, Hpk_apply]`. Establish `e1 : flipB k r (eI k r ⟨a, ha⟩) = ⟨2 * r + k - a, by omega⟩` using `Fin.ext (by rw [flipB_val]; simp [eI, ha])`. Establish `e2 : sgnB k r (eI k r ⟨a, ha⟩) = 1`.

Unfold `sgnB`. Rewrite using `[if_neg]`. Simplify using `only [eI]`. Use linear arithmetic over natural numbers and integers. Rewrite `h1` using `[e1, e2]`.

Simplify `h1` using `[eq_comm]`. Introduce `c _ hc`. Rewrite using `[conjTranspose_apply]`. Distinguish the cases in `hca : c.val < a`. Establish `e1 : flipB k r c = ⟨2 * r + k - c.val, by omega⟩` using `Fin.ext (by rw [flipB_val, if_pos (Or.inl (by omega))])`.

Rewrite using `[Hpk_mul_apply, e1, ih c.val hca (by omega) (by omega), if_neg, mul_zero, mul_zero]`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `only at this`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[he ⟨a, ha⟩ c (by simp only; omega), if_neg hc, star_zero, zero_mul]`. Simplify using the standard rewrite rules. Introduce `a b h`. Establish `hal` using `a.isLt`. Establish `hbl` using `b.isLt`.

Establish `key : g a b = if a = b then 1 else 0`. Unfold `levB at h`. Distinguish the cases in `hb : b.val < r`. Apply the tactic sequence `have := he ⟨b.val, hb⟩ a (by simp only; split_ifs at h <;> omega)`. Conclude with `this`.

Distinguish the cases in `hb2 : b.val ≤ r + k`. Apply the tactic sequence `exact hm a b (by omega) hb2 (by split_ifs at h <;> omega)`. Apply the tactic sequence `have ha : r + k < a.val ∧ b.val ≤ a.val := by split_ifs at h <;> omega`. Use `hf b (2 * r + k - a.val) (by omega) (by omega)` as an intermediate fact. Establish `e : (⟨2 * r + k - (2 * r + k - a.val), by omega⟩ : Fin (2 * r + k + 1)) = a` using `Fin.ext (by simp only; omega)`.

Rewrite `this` using `[e]`. Then use the resulting hypothesis. Rewrite using `[Matrix.sub_apply, key, Matrix.one_apply, sub_self]`. Introduce and unpack `⟨hF, hU⟩`. Establish `key : ∀ a b, levB k r b ≤ levB k r a → g a b = if a = b then 1 else 0` using `fun a b h => by`. Use `hF a b (by omega)` as an intermediate fact.

Rewrite `this` using `[Matrix.sub_apply, sub_eq_zero, Matrix.one_apply]`. Then use the resulting hypothesis. Use `⟨hU, fun a i h => key _ _ ?_, fun i j h1 h2 h3 => key _ _ ?_⟩` and prove the remaining obligations. Use `a.isLt` as an intermediate fact. Apply the tactic sequence `unfold levB eI; simp only; split_ifs <;> omega`. Apply the tactic sequence `unfold levB; split_ifs <;> omega`.
-/
theorem Nset_eq : Nset k r = grpN (levF (levB k r)) (adjH (Hpk k r)) := by
  ext g
  rw [mem_grpN_iff _ _ Hpk_sq]
  constructor
  · rintro ⟨hU, he, hm⟩
    refine ⟨?_, hU⟩

    have hf : ∀ (j : Fin (2 * r + k + 1)) (a : ℕ) (ha : a < r), j.val + a ≤ 2 * r + k →
        g ⟨2 * r + k - a, by omega⟩ j = if (⟨2 * r + k - a, by omega⟩ : Fin (2 * r + k + 1)) = j
          then 1 else 0 := by
      intro j a
      induction a using Nat.strong_induction_on with
      | _ a ih =>
        intro ha hja
        have h1 := congrFun (congrFun hU (eI k r ⟨a, ha⟩)) j
        rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single (eI k r ⟨a, ha⟩)] at h1
        · rw [conjTranspose_apply, he ⟨a, ha⟩ _ le_rfl, if_pos rfl, Hpk_mul_apply, Hpk_apply] at h1
          have e1 : flipB k r (eI k r ⟨a, ha⟩) = ⟨2 * r + k - a, by omega⟩ :=
            Fin.ext (by rw [flipB_val]; simp [eI, ha])
          have e2 : sgnB k r (eI k r ⟨a, ha⟩) = 1 := by
            unfold sgnB; rw [if_neg]; simp only [eI]; omega
          rw [e1, e2] at h1
          simpa [eq_comm] using h1
        · intro c _ hc
          rw [conjTranspose_apply]
          by_cases hca : c.val < a
          · have e1 : flipB k r c = ⟨2 * r + k - c.val, by omega⟩ :=
              Fin.ext (by rw [flipB_val, if_pos (Or.inl (by omega))])
            rw [Hpk_mul_apply, e1, ih c.val hca (by omega) (by omega), if_neg, mul_zero, mul_zero]
            intro h; have := congrArg Fin.val h; simp only at this; omega
          · rw [he ⟨a, ha⟩ c (by simp only; omega), if_neg hc, star_zero, zero_mul]
        · simp
    intro a b h
    have hal := a.isLt
    have hbl := b.isLt
    have key : g a b = if a = b then 1 else 0 := by
      unfold levB at h
      by_cases hb : b.val < r
      · have := he ⟨b.val, hb⟩ a (by simp only; split_ifs at h <;> omega)
        exact this
      · by_cases hb2 : b.val ≤ r + k
        · exact hm a b (by omega) hb2 (by split_ifs at h <;> omega)
        · have ha : r + k < a.val ∧ b.val ≤ a.val := by split_ifs at h <;> omega
          have := hf b (2 * r + k - a.val) (by omega) (by omega)
          have e : (⟨2 * r + k - (2 * r + k - a.val), by omega⟩ : Fin (2 * r + k + 1)) = a :=
            Fin.ext (by simp only; omega)
          rwa [e] at this
    rw [Matrix.sub_apply, key, Matrix.one_apply, sub_self]
  · rintro ⟨hF, hU⟩
    have key : ∀ a b, levB k r b ≤ levB k r a → g a b = if a = b then 1 else 0 := fun a b h => by
      have := hF a b (by omega)
      rwa [Matrix.sub_apply, sub_eq_zero, Matrix.one_apply] at this
    refine ⟨hU, fun a i h => key _ _ ?_, fun i j h1 h2 h3 => key _ _ ?_⟩
    · have := a.isLt
      unfold levB eI; simp only; split_ifs <;> omega
    · unfold levB; split_ifs <;> omega

/- English proof (translation)
Use extensionality with `Y`. Rewrite using `[Nset_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hd` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0`.

Rewrite `hd` using `[zero_smul, NormedSpace.exp_zero, one_mul]`. Establish `h' : ∀ t : ℝ, NormedSpace.exp (t • Y) ∈ grpN (levF (levB k r)) (adjH (Hpk k r))` using `fun t => by have := h t; rw [Complex.coe_smul] at this; exact this`. Use `mem_lieN.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Establish `h2` using `hasDerivAt_iff_tendsto_slope_zero.mp hd`. Use `(levF (levB k r) 0).closed_of_finiteDimensional.mem_of_tendsto h2 (Filter.Eventually.of_forall fun t => (levF (levB k r) 0).smul_mem _ ?_)` and prove the remaining obligations.

Simplify using `only [zero_add, zero_smul, NormedSpace.exp_zero]`. Conclude with `(h' t).1`. Establish `h3` using `((LinearMap.toContinuousLinearMap (adjH (Hpk k r))).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd).mul hd`. Establish `h4 : HasDerivAt (fun _ : ℝ => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) 0 0` using `hasDerivAt_const _ _`. Establish `h5` using `h4.unique (h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ((h' t).2).symm))`.

Simplify using `only [Function.comp, zero_smul, NormedSpace.exp_zero, mul_one, LinearMap.coe_toContinuousLinearMap', isAdjB.one, one_mul] at h5`. Conclude with `eq_neg_of_add_eq_zero_left h5.symm`. Introduce `h t`. Use `exp_mem_grpN isFilB isAdjB ((lieN _ _).smul_mem t h)` as an intermediate fact. Rewrite using `[Complex.coe_smul]`.

Conclude with `this`.
-/
theorem lieOf_Nset_eq : Formalism.MainNotions.S.lieOf (Nset k r) =
    (lieN (levF (levB k r)) (adjH (Hpk k r)) : Set _) := by
  ext Y
  rw [Nset_eq]
  constructor
  · intro h
    have hd := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at hd
    have h' : ∀ t : ℝ, NormedSpace.exp (t • Y) ∈ grpN (levF (levB k r)) (adjH (Hpk k r)) :=
      fun t => by have := h t; rw [Complex.coe_smul] at this; exact this
    refine mem_lieN.mpr ⟨?_, ?_⟩
    · have h2 := hasDerivAt_iff_tendsto_slope_zero.mp hd
      refine (levF (levB k r) 0).closed_of_finiteDimensional.mem_of_tendsto h2
        (Filter.Eventually.of_forall fun t => (levF (levB k r) 0).smul_mem _ ?_)
      simp only [zero_add, zero_smul, NormedSpace.exp_zero]
      exact (h' t).1
    · have h3 := ((LinearMap.toContinuousLinearMap (adjH (Hpk k r))).hasFDerivAt.comp_hasDerivAt
        (0 : ℝ) hd).mul hd
      have h4 : HasDerivAt (fun _ : ℝ => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
          0 0 := hasDerivAt_const _ _
      have h5 := h4.unique (h3.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun t => ((h' t).2).symm))
      simp only [Function.comp, zero_smul, NormedSpace.exp_zero, mul_one,
        LinearMap.coe_toContinuousLinearMap', isAdjB.one, one_mul] at h5
      exact eq_neg_of_add_eq_zero_left h5.symm
  · intro h t
    have := exp_mem_grpN isFilB isAdjB ((lieN _ _).smul_mem t h)
    rw [Complex.coe_smul]; exact this

end ReciprocityTheory.ChartRestriction.DS.Lap.Base

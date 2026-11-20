import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensSAChar

noncomputable section

open NumberField Complex

namespace PI.VolStabS

namespace ChLiftW

/- English proof (translation)
Take `⟨n, hn⟩` from `hint p`. Establish `key : ∀ t : ℝ, t ∈ Set.uIcc (0 : ℝ) (n : ℝ) → ∃ m : ℤ, t = m`. Introduce `t ht`. Break down `le_total (0 : ℝ) n with h | h` into its components or cases. Rewrite `ht` using `[Set.uIcc_of_le h]`.

Take `⟨q, hq⟩` from `intermediate_value_univ a p hψ (by rw [ha, hn]; exact ht)`. Take `⟨m, hm⟩` from `hint q`. Conclude with `⟨m, by rw [← hq, hm]⟩`. Rewrite `ht` using `[Set.uIcc_of_ge h]`. Take `⟨q, hq⟩` from `intermediate_value_univ p a hψ (by rw [ha, hn]; exact ht)`.

Take `⟨m, hm⟩` from `hint q`. Conclude with `⟨m, by rw [← hq, hm]⟩`. Rewrite using `[hn]`. Assume the negation of the conclusion as `hne`. Establish `hn0 : n ≠ 0` using `fun h => hne (by simp [h])`.

Break down `lt_or_gt_of_ne hn0 with h | h` into its components or cases. Establish `hn1 : (n : ℝ) ≤ -1` using `by exact_mod_cast (show n ≤ -1 by omega)`. Take `⟨m, hm⟩` from `key (-1 / 2) (by`. Rewrite using `[Set.uIcc_of_ge (by linarith)]`. Apply the tactic sequence `constructor <;> linarith)`.

Establish `h2 : ((2 * m : ℤ) : ℝ) = -1` using `by push_cast; linarith`. Establish `h3 : 2 * m = -1` using `by exact_mod_cast h2`. Use linear arithmetic over natural numbers and integers. Establish `hn1 : (1 : ℝ) ≤ n` using `by exact_mod_cast (show 1 ≤ n by omega)`. Take `⟨m, hm⟩` from `key (1 / 2) (by`.

Rewrite using `[Set.uIcc_of_le (by linarith)]`. Apply the tactic sequence `constructor <;> linarith)`. Establish `h2 : ((2 * m : ℤ) : ℝ) = 1` using `by push_cast; linarith`. Establish `h3 : 2 * m = 1` using `by exact_mod_cast h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem int_valued_zero {Y : Type*} [TopologicalSpace Y] [PreconnectedSpace Y] (ψ : Y → ℝ)
    (hψ : Continuous ψ) (hint : ∀ p, ∃ n : ℤ, ψ p = n) (a : Y) (ha : ψ a = 0) (p : Y) :
    ψ p = 0 := by
  obtain ⟨n, hn⟩ := hint p
  have key : ∀ t : ℝ, t ∈ Set.uIcc (0 : ℝ) (n : ℝ) → ∃ m : ℤ, t = m := by
    intro t ht
    rcases le_total (0 : ℝ) n with h | h
    · rw [Set.uIcc_of_le h] at ht
      obtain ⟨q, hq⟩ := intermediate_value_univ a p hψ (by rw [ha, hn]; exact ht)
      obtain ⟨m, hm⟩ := hint q
      exact ⟨m, by rw [← hq, hm]⟩
    · rw [Set.uIcc_of_ge h] at ht
      obtain ⟨q, hq⟩ := intermediate_value_univ p a hψ (by rw [ha, hn]; exact ht)
      obtain ⟨m, hm⟩ := hint q
      exact ⟨m, by rw [← hq, hm]⟩
  rw [hn]
  by_contra hne
  have hn0 : n ≠ 0 := fun h => hne (by simp [h])
  rcases lt_or_gt_of_ne hn0 with h | h
  · have hn1 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    obtain ⟨m, hm⟩ := key (-1 / 2) (by
      rw [Set.uIcc_of_ge (by linarith)]
      constructor <;> linarith)
    have h2 : ((2 * m : ℤ) : ℝ) = -1 := by push_cast; linarith
    have h3 : 2 * m = -1 := by exact_mod_cast h2
    omega
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    obtain ⟨m, hm⟩ := key (1 / 2) (by
      rw [Set.uIcc_of_le (by linarith)]
      constructor <;> linarith)
    have h2 : ((2 * m : ℤ) : ℝ) = 1 := by push_cast; linarith
    have h3 : 2 * m = 1 := by exact_mod_cast h2
    omega

/- English proof (translation)
Establish `hne : ∀ x, χ x ≠ 0` using `fun x h => by`. Use `hadd x (-x)` as an intermediate fact. Rewrite `this` using `[add_neg_cancel, h0, h, zero_mul]`. Conclude with `one_ne_zero this`. Set `f : C(W, {z : ℂ // z ≠ 0})` to `⟨fun x => ⟨χ x, hne x⟩, hc.subtype_mk _⟩`.

Take `⟨g, ⟨hg0, hgl⟩, -⟩` from `Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0 (by ext; simp [f, h0])`. Establish `hge : ∀ x, exp (g x) = χ x` using `fun x => congrArg Subtype.val (congrFun hgl x)`. Establish `h2 : (2 * Real.pi * I : ℂ) ≠ 0` using `by simp [Real.pi_ne_zero, Complex.I_ne_zero]`. Set `D : W × W → ℂ` to `fun p => g (p.1 + p.2) - g p.1 - g p.2`. Establish `hDc : Continuous D`.

Use `g.continuous` as an intermediate fact. Use `fun_prop`. Establish `hDint : ∀ p, ∃ n : ℤ, D p = n * (2 * Real.pi * I)` using `fun p => by`. Rewrite using `[← Complex.exp_eq_one_iff]`. Simplify using `only [D, Complex.exp_sub, hge, hadd]`.

Clear denominators, using `[hne p.1, hne p.2]` for the nonvanishing conditions. Set `ψ : W × W → ℝ` to `fun p => (D p / (2 * Real.pi * I)).re`. Establish `hψint : ∀ p, ∃ n : ℤ, ψ p = n` using `fun p => by`. Take `⟨n, hn⟩` from `hDint p`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Simplify using `only [ψ, hn, mul_div_assoc, div_self h2, mul_one]`. Simplify using the standard rewrite rules. Establish `hψ : ∀ p, D p = ψ p * (2 * Real.pi * I)` using `fun p => by`. Take `⟨n, hn⟩` from `hDint p`. Establish `: ψ p = n` using `by simp only [ψ, hn, mul_div_assoc, div_self h2, mul_one]; simp`.

Rewrite using `[this, hn]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hψc : Continuous ψ`. Simplify using `only [ψ]`.

Use `fun_prop`. Establish `hψ0 : ψ (0, 0) = 0` using `by simp [ψ, D, hg0]`. Establish `hD0 : ∀ p, D p = 0` using `fun p => by`. Rewrite using `[hψ p, int_valued_zero ψ hψc hψint (0, 0) hψ0 p]`. Simplify using the standard rewrite rules.

Use `⟨{ toFun := g, map_zero' := hg0, map_add' := fun x y => ?_ }, g.continuous, fun x => (hge x).symm⟩` and prove the remaining obligations. Use `hD0 (x, y)` as an intermediate fact. Simplify using `only [D] at this`. Take the linear combination `this`.
-/
theorem lift_normed {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (χ : W → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : W →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  have hne : ∀ x, χ x ≠ 0 := fun x h => by
    have := hadd x (-x)
    rw [add_neg_cancel, h0, h, zero_mul] at this
    exact one_ne_zero this
  let f : C(W, {z : ℂ // z ≠ 0}) := ⟨fun x => ⟨χ x, hne x⟩, hc.subtype_mk _⟩
  obtain ⟨g, ⟨hg0, hgl⟩, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0
    (by ext; simp [f, h0])
  have hge : ∀ x, exp (g x) = χ x := fun x => congrArg Subtype.val (congrFun hgl x)
  have h2 : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  let D : W × W → ℂ := fun p => g (p.1 + p.2) - g p.1 - g p.2
  have hDc : Continuous D := by
    have := g.continuous
    fun_prop
  have hDint : ∀ p, ∃ n : ℤ, D p = n * (2 * Real.pi * I) := fun p => by
    rw [← Complex.exp_eq_one_iff]
    simp only [D, Complex.exp_sub, hge, hadd]
    field_simp [hne p.1, hne p.2]
  let ψ : W × W → ℝ := fun p => (D p / (2 * Real.pi * I)).re
  have hψint : ∀ p, ∃ n : ℤ, ψ p = n := fun p => by
    obtain ⟨n, hn⟩ := hDint p
    refine ⟨n, ?_⟩
    simp only [ψ, hn, mul_div_assoc, div_self h2, mul_one]
    simp
  have hψ : ∀ p, D p = ψ p * (2 * Real.pi * I) := fun p => by
    obtain ⟨n, hn⟩ := hDint p
    have : ψ p = n := by simp only [ψ, hn, mul_div_assoc, div_self h2, mul_one]; simp
    rw [this, hn]; push_cast; ring
  have hψc : Continuous ψ := by
    simp only [ψ]
    fun_prop
  have hψ0 : ψ (0, 0) = 0 := by simp [ψ, D, hg0]
  have hD0 : ∀ p, D p = 0 := fun p => by
    rw [hψ p, int_valued_zero ψ hψc hψint (0, 0) hψ0 p]; simp
  refine ⟨{ toFun := g, map_zero' := hg0, map_add' := fun x y => ?_ }, g.continuous,
    fun x => (hge x).symm⟩
  have := hD0 (x, y)
  simp only [D] at this
  linear_combination this

/- English proof (translation)
Establish `hes : ∀ a b, e.symm (a + b) = e.symm a + e.symm b` using `fun a b => by`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[he]`. Simplify using the standard rewrite rules. Establish `he0 : e.symm 0 = 0`.

Use `hes 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `left_eq_add.mp this`. Take `⟨ℓ', hℓc, hℓ⟩` from `lift_normed (χ ∘ e.symm) (hc.comp e.symm.continuous) (fun a b => by simp only [Function.comp, hes, hadd]) (by simp [he0, h0])`. Use `⟨ℓ'.comp (AddMonoidHom.mk' e he), hℓc.comp e.continuous, fun x => ?_⟩` and prove the remaining obligations.

Use `hℓ (e x)` as an intermediate fact. Simplify using `using this`.
-/
theorem lift_homeo {X W : Type*} [AddCommGroup X] [TopologicalSpace X] [NormedAddCommGroup W]
    [NormedSpace ℝ W] (e : X ≃ₜ W) (he : ∀ x y, e (x + y) = e x + e y) (χ : X → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : X →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  have hes : ∀ a b, e.symm (a + b) = e.symm a + e.symm b := fun a b => by
    apply e.injective
    rw [he]; simp
  have he0 : e.symm 0 = 0 := by
    have := hes 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  obtain ⟨ℓ', hℓc, hℓ⟩ := lift_normed (χ ∘ e.symm) (hc.comp e.symm.continuous)
    (fun a b => by simp only [Function.comp, hes, hadd]) (by simp [he0, h0])
  refine ⟨ℓ'.comp (AddMonoidHom.mk' e he), hℓc.comp e.continuous, fun x => ?_⟩
  have := hℓ (e x)
  simpa using this

/- English proof (translation)
Distinguish the cases in `hv : v.IsReal`. Conclude with `lift_homeo (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph (fun x y => (InfinitePlace.Completion.ringEquivRealOfIsReal hv).map_add x y) χ hc hadd h0`. Establish `hv' : v.IsComplex` using `InfinitePlace.not_isReal_iff_isComplex.1 hv`. Conclude with `lift_homeo (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').toHomeomorph (fun x y => (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv').map_add x y) χ hc hadd h0`.
-/
theorem lift_place {F : Type} [Field F] (v : InfinitePlace F) (χ : v.Completion → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : v.Completion →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  by_cases hv : v.IsReal
  · exact lift_homeo (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph
      (fun x y => (InfinitePlace.Completion.ringEquivRealOfIsReal hv).map_add x y) χ hc hadd h0
  · have hv' : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.1 hv
    exact lift_homeo (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').toHomeomorph
      (fun x y => (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv').map_add x y) χ hc hadd h0

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [AddChar.map_zero_eq_one]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]`.
-/
theorem addChar_sum {ι A : Type*} [AddCommMonoid A] (χ : AddChar A ℂ) (s : Finset ι) (f : ι → A) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

end ChLiftW

open Classical in

def sgl {F : Type} [Field F] (v : InfinitePlace F) (t : v.Completion) : InfiniteAdeleRing F :=
  Pi.single v t

open Classical in
/- English proof (translation)
The claim follows from `Pi.single_add v x y`.
-/
theorem sgl_add {F : Type} [Field F] (v : InfinitePlace F) (x y : v.Completion) :
    sgl v (x + y) = sgl v x + sgl v y :=
  Pi.single_add v x y

open Classical in
/- English proof (translation)
The claim follows from `Pi.single_zero v`.
-/
theorem sgl_zero {F : Type} [Field F] (v : InfinitePlace F) : sgl v (0 : v.Completion) = 0 :=
  Pi.single_zero v

open Classical in
/- English proof (translation)
The claim follows from `continuous_single (A := fun w : InfinitePlace F => w.Completion) v`.
-/
theorem continuous_sgl {F : Type} [Field F] (v : InfinitePlace F) : Continuous (sgl v) :=
  continuous_single (A := fun w : InfinitePlace F => w.Completion) v

open Classical in
/- English proof (translation)
The claim follows from `Finset.univ_sum_single (M := fun w : InfinitePlace F => w.Completion) x`.
-/
theorem sum_sgl {F : Type} [Field F] [NumberField F] (x : InfiniteAdeleRing F) :
    ∑ v, sgl v (x v) = x :=
  Finset.univ_sum_single (M := fun w : InfinitePlace F => w.Completion) x

open ChLiftW in
/- English proof (translation)
Introduce `F _ _ χ hχ`. Establish `hloc : ∀ v : InfinitePlace F, ∃ ℓ : v.Completion →+ ℂ, Continuous ℓ ∧ ∀ t, χ (sgl v t) = exp (ℓ t)` using `fun v => lift_place v (fun t => χ (sgl v t)) (hχ.comp (continuous_sgl v)) (fun x y => by simp only [sgl_add, AddChar.map_add_eq_mul]) (by simp only [sgl_zero, AddChar.map_zero_eq_one])`. Use `choose ℓv hℓc hℓ using hloc`. Set `ℓ : InfiniteAdeleRing F →+ ℂ` to `AddMonoidHom.mk' (fun x => ∑ v, ℓv v (x v)) (fun a b => by show ∑ v, ℓv v (a v + b v) = _`. Simplify using `[map_add, Finset.sum_add_distrib])`.

Use `⟨ℓ, ?_, fun x => ?_⟩` and prove the remaining obligations. Use `show Continuous (fun x : InfiniteAdeleRing F => ∑ v, ℓv v (x v))`. Conclude with `continuous_finsetSum _ fun v _ => (hℓc v).comp (continuous_apply v)`. Use `conv_lhs => rw [← sum_sgl x]`. Rewrite using `[addChar_sum]`.

Use `show _ = exp (∑ v, ℓv v (x v))`. Rewrite using `[Complex.exp_sum]`. Conclude with `Finset.prod_congr rfl fun v _ => hℓ v (x v)`.
-/
theorem chLift_holds : ChLift := by
  intro F _ _ χ hχ
  have hloc : ∀ v : InfinitePlace F, ∃ ℓ : v.Completion →+ ℂ, Continuous ℓ ∧
      ∀ t, χ (sgl v t) = exp (ℓ t) := fun v =>
    lift_place v (fun t => χ (sgl v t)) (hχ.comp (continuous_sgl v))
      (fun x y => by simp only [sgl_add, AddChar.map_add_eq_mul])
      (by simp only [sgl_zero, AddChar.map_zero_eq_one])
  choose ℓv hℓc hℓ using hloc
  let ℓ : InfiniteAdeleRing F →+ ℂ := AddMonoidHom.mk' (fun x => ∑ v, ℓv v (x v)) (fun a b => by
    show ∑ v, ℓv v (a v + b v) = _
    simp [map_add, Finset.sum_add_distrib])
  refine ⟨ℓ, ?_, fun x => ?_⟩
  · show Continuous (fun x : InfiniteAdeleRing F => ∑ v, ℓv v (x v))
    exact continuous_finsetSum _ fun v _ => (hℓc v).comp (continuous_apply v)
  · conv_lhs => rw [← sum_sgl x]
    rw [addChar_sum]
    show _ = exp (∑ v, ℓv v (x v))
    rw [Complex.exp_sum]
    exact Finset.prod_congr rfl fun v _ => hℓ v (x v)

end PI.VolStabS

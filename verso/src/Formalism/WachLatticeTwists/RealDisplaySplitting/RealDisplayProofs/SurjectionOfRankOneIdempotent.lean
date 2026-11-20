import Formalism.WachLatticeTwists.RealDisplaySplitting.SurjectionRankOneIdempotent
import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.Normal

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.SF

open Formalism.NG Formalism.RepresentationBoundsCohomology.ringDataObjects

section Inst
variable {R : Type} [Ring R] (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M]
  (n : Type) [Fintype n] [DecidableEq n] (ρ : R →+* Matrix n n O)

instance : SMulCommClass R O (LatM O M n ρ) :=
  ⟨fun a c m => LinearMap.map_smul (matEnd O M n (ρ a)) c m⟩

instance [IsDomain O] [IsDiscreteValuationRing O] :
    IsScalarTower O (FractionRing O) (LatM O (FractionRing O) n ρ) :=
  inferInstanceAs (IsScalarTower O (FractionRing O) (n → FractionRing O))

instance [IsDomain O] [IsDiscreteValuationRing O] :
    SMulCommClass R (FractionRing O) (LatM O (FractionRing O) n ρ) :=
  ⟨fun a x u => funext fun i => by
    show ∑ j, ρ a i j • (x * (u j : FractionRing O)) = x * ∑ j, ρ a i j • (u j : FractionRing O)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => (mul_smul_comm _ _ _).symm⟩

end Inst

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap O (FractionRing O))` using `IsFractionRing.injective O _`. Establish `he0 : e ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hrk`. Choose the witnesses or unpack the hypotheses as in `⟨i1, j1, h1⟩ : ∃ i j, e i j ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `he0 (Matrix.ext h)`. Take `⟨⟨i0, j0⟩, -, hp0⟩` from `Finset.exists_min_image (Finset.univ : Finset (n × n)) (fun p => IsDiscreteValuationRing.addVal O (e p.1 p.2)) ⟨(i1, j1), Finset.mem_univ _⟩`. Establish `hdiv : ∀ i j, e i0 j0 ∣ e i j` using `fun i j => (IsDiscreteValuationRing.addVal_le_iff_dvd).1 (hp0 (i, j) (Finset.mem_univ _))`.

Establish `hd0 : e i0 j0 ≠ 0`. Introduce `h`. Apply `h1` to reduce the goal to its premises. Use `hp0 (i1, j1) (Finset.mem_univ _)` as an intermediate fact. Simplify using `only [h, IsDiscreteValuationRing.addVal_zero, top_le_iff] at this`.

Conclude with `(IsDiscreteValuationRing.addVal_eq_top_iff).1 this`. Establish `hminor : ∀ i j, e i j * e i0 j0 = e i j0 * e i0 j`. Establish `hcol : ∀ j, (fun i => (e.map (algebraMap O (FractionRing O))) i j) ∈ LinearMap.range (e.map (algebraMap O (FractionRing O))).mulVecLin` using `fun j => ⟨Pi.single j 1, by`. Use extensionality with `i`. Simplify using `[Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]⟩`.

Establish `hnz : (⟨_, hcol j0⟩ : LinearMap.range (e.map (algebraMap O (FractionRing O))).mulVecLin) ≠ 0`. Introduce `h`. Use `congrFun (congrArg Subtype.val h) i0` as an intermediate fact. Simplify using `only [Matrix.map_apply, ZeroMemClass.coe_zero, Pi.zero_apply] at this`. Conclude with `hd0 ((map_eq_zero_iff _ hinj).1 this)`.

Establish `hrk' : Module.finrank (FractionRing O) (LinearMap.range (e.map (algebraMap O (FractionRing O))).mulVecLin) = 1` using `hrk`. Establish `hall` using `(finrank_eq_one_iff_of_nonzero' _ hnz).1 hrk'`. Introduce `i j`. Take `⟨t, ht⟩` from `hall ⟨_, hcol j⟩`. Establish `hti : ∀ i', t * algebraMap O (FractionRing O) (e i' j0) = algebraMap O (FractionRing O) (e i' j)` using `fun i' => by`.

Use `congrFun (congrArg Subtype.val ht) i'` as an intermediate fact. Simplify using `using this`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, ← hti i, ← hti i0]`. Expand and normalize the polynomial expressions, which then agree.

Use `choose v hv using fun i => hdiv i j0`. Use `⟨v, fun j => e i0 j, fun i j => ?_, ?_⟩` and prove the remaining obligations. Apply `mul_left_cancel₀ hd0` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Apply `mul_left_cancel₀ hd0` to reduce the goal to its premises.

Establish `hsq : ∑ j, e i0 j * e j j0 = e i0 j0`. Use `congrFun (congrFun he i0) j0` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Use `_ = ∑ j, e i0 j * e j j0 := by simp_rw [← hv]`. Use `_ = e i0 j0 * 1 := by rw [hsq, mul_one]`.
-/
theorem rank_one_factor (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : Type) [Fintype n]
    [DecidableEq n] (e : Matrix n n O) (he : e * e = e)
    (hrk : (e.map (algebraMap O (FractionRing O))).rank = 1) :
    ∃ v w : n → O, (∀ i j, e i j = v i * w j) ∧ ∑ j, w j * v j = 1 := by
  have hinj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O _
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at hrk
  obtain ⟨i1, j1, h1⟩ : ∃ i j, e i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact he0 (Matrix.ext h)
  obtain ⟨⟨i0, j0⟩, -, hp0⟩ := Finset.exists_min_image (Finset.univ : Finset (n × n))
    (fun p => IsDiscreteValuationRing.addVal O (e p.1 p.2)) ⟨(i1, j1), Finset.mem_univ _⟩
  have hdiv : ∀ i j, e i0 j0 ∣ e i j := fun i j =>
    (IsDiscreteValuationRing.addVal_le_iff_dvd).1 (hp0 (i, j) (Finset.mem_univ _))
  have hd0 : e i0 j0 ≠ 0 := by
    intro h
    apply h1
    have := hp0 (i1, j1) (Finset.mem_univ _)
    simp only [h, IsDiscreteValuationRing.addVal_zero, top_le_iff] at this
    exact (IsDiscreteValuationRing.addVal_eq_top_iff).1 this

  have hminor : ∀ i j, e i j * e i0 j0 = e i j0 * e i0 j := by
    have hcol : ∀ j, (fun i => (e.map (algebraMap O (FractionRing O))) i j) ∈
        LinearMap.range (e.map (algebraMap O (FractionRing O))).mulVecLin := fun j =>
      ⟨Pi.single j 1, by
        ext i
        simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]⟩
    have hnz : (⟨_, hcol j0⟩ : LinearMap.range (e.map (algebraMap O (FractionRing O))).mulVecLin) ≠ 0 := by
      intro h
      have := congrFun (congrArg Subtype.val h) i0
      simp only [Matrix.map_apply, ZeroMemClass.coe_zero, Pi.zero_apply] at this
      exact hd0 ((map_eq_zero_iff _ hinj).1 this)
    have hrk' : Module.finrank (FractionRing O)
        (LinearMap.range (e.map (algebraMap O (FractionRing O))).mulVecLin) = 1 := hrk
    have hall := (finrank_eq_one_iff_of_nonzero' _ hnz).1 hrk'
    intro i j
    obtain ⟨t, ht⟩ := hall ⟨_, hcol j⟩
    have hti : ∀ i', t * algebraMap O (FractionRing O) (e i' j0) = algebraMap O (FractionRing O) (e i' j) :=
      fun i' => by
        have := congrFun (congrArg Subtype.val ht) i'
        simpa using this
    apply hinj
    rw [map_mul, map_mul, ← hti i, ← hti i0]
    ring
  choose v hv using fun i => hdiv i j0
  refine ⟨v, fun j => e i0 j, fun i j => ?_, ?_⟩
  · apply mul_left_cancel₀ hd0
    calc e i0 j0 * e i j = e i j0 * e i0 j := by rw [mul_comm (e i0 j0), hminor]
      _ = e i0 j0 * (v i * e i0 j) := by rw [hv i]; ring
  · apply mul_left_cancel₀ hd0
    have hsq : ∑ j, e i0 j * e j j0 = e i0 j0 := by
      have := congrFun (congrFun he i0) j0
      simpa [Matrix.mul_apply] using this
    calc e i0 j0 * ∑ j, e i0 j * v j = ∑ j, e i0 j * (e i0 j0 * v j) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j, e i0 j * e j j0 := by simp_rw [← hv]
      _ = e i0 j0 * 1 := by rw [hsq, mul_one]

/- English proof (translation)
Establish `hE : ρ e₁ * ρ e₁ = ρ e₁` using `by rw [← map_mul, he]`. Take `⟨v, w, hvw, hwv⟩` from `rank_one_factor O n (ρ e₁) hE hrk`. Establish `hmap : ∀ i, ∑ j, ρ e₁ i j * v j = v i` using `fun i => by`. Simplify using `only [hvw]`. Rewrite using `[show ∑ j, v i * w j * v j = v i * ∑ j, w j * v j by`.

Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring, hwv, mul_one]`. Establish `hfix : e₁ • (show LatM O O n ρ from v) = (show LatM O O n ρ from v)`. Use function extensionality and compare the values at `i`. Use `show ∑ j, ρ e₁ i j • v j = v i`. Simplify `hmap i` using `only [smul_eq_mul]`.

Use `⟨v, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfix, ?_⟩` and prove the remaining obligations. Introduce `a u x`. Use function extensionality and compare the values at `i`. Use `show (∑ j, ρ a i j • u j) • x = ∑ j, ρ a i j • (u j • x)`. Rewrite using `[Finset.sum_smul]`.

Simplify using `only [smul_eq_mul, mul_smul]`. Introduce `m hm`. Use `⟨∑ j, w j • m j, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← hm]`. Use function extensionality and compare the values at `i`.

Use `show ∑ j, ρ e₁ i j • m j = v i • ∑ j, w j • m j`. Simplify using `only [hvw, mul_smul, Finset.smul_sum]`. Introduce `a u`. Use function extensionality and compare the values at `i`. Use `show algebraMap O (FractionRing O) (∑ j, ρ a i j • u j) = ∑ j, ρ a i j • algebraMap O (FractionRing O) (u j)`.

Rewrite using `[map_sum]`. Simplify using `[Algebra.smul_def]`. Introduce `a u`. Use function extensionality and compare the values at `i`. Use `show (1 : Submodule O (FractionRing O)).mkQ (∑ j, ρ a i j • u j) = ∑ j, ρ a i j • (1 : Submodule O (FractionRing O)).mkQ (u j)`.

Rewrite using `[map_sum]`. Simplify using `only [map_smul]`. Introduce `u x`. Use function extensionality and compare the values at `i`. Use `show u i • Submodule.Quotient.mk x = (1 : Submodule O (FractionRing O)).mkQ (x * algebraMap O (FractionRing O) (u i))`.

Rewrite using `[Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Algebra.smul_def, mul_comm]`. Introduce `u u' h`. Use function extensionality and compare the values at `i`. Conclude with `IsFractionRing.injective O (FractionRing O) (congrFun h i)`. Introduce `q choose y hy using fun i => Submodule.Quotient.mk_surjective _ (q i)`.

Conclude with `⟨y, funext hy⟩`. Use extensionality with `u`. Simplify using `only [LinearMap.mem_ker, LinearMap.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `hi : ∀ i, ∃ c : O, algebraMap O (FractionRing O) c = u i` using `fun i => by`. Establish `h' : (1 : Submodule O (FractionRing O)).mkQ (u i) = 0` using `congrFun h i`. Rewrite `h'` using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]`. Conclude with `h'`. Use `choose c hc using hi`.

Conclude with `⟨c, funext hc⟩`. Introduce and unpack `⟨c, rfl⟩`. Use function extensionality and compare the values at `i`. Use `show (1 : Submodule O (FractionRing O)).mkQ (algebraMap O (FractionRing O) (c i)) = 0`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]`.

Conclude with `⟨c i, rfl⟩`. Introduce `u`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors O) (Finset.univ : Finset n) (fun i => (u i : FractionRing O))`. Use `⟨b, nonZeroDivisors.coe_ne_zero b, ?_⟩` and prove the remaining obligations. Use `choose c hc using fun i => hb i (Finset.mem_univ i)`.

Conclude with `⟨c, funext fun i => (hc i).trans rfl⟩`. Introduce `u`. Take `⟨c, hc⟩` from `hsurj (Matrix.of fun i j => u i * w j)`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `hms : (c * e₁) • (show LatM O O n ρ from v) = c • e₁ • (show LatM O O n ρ from v)` using `mul_smul _ _ _`.

Use `hms.trans ?_` and prove the remaining obligations. Rewrite using `[hfix]`. Use function extensionality and compare the values at `i`. Use `show ∑ j, ρ c i j • v j = u i`. Simplify using `only [hc, Matrix.of_apply, smul_eq_mul]`.

Rewrite using `[show ∑ j, u i * w j * v j = u i * ∑ j, w j * v j by`. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring, hwv, mul_one]`.
-/
theorem surjection_of_rank_one_idempotent (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (A : Type) [Ring A]
    (n : Type) [Fintype n] [DecidableEq n] (ρ : A →+* Matrix n n O) (e₁ : A)
    (hsurj : Function.Surjective ρ) (he : e₁ * e₁ = e₁)
    (hrk : ((ρ e₁).map (algebraMap O (FractionRing O))).rank = 1) : SurjectionRankOneIdempotent O A n ρ e₁ := by
  have hE : ρ e₁ * ρ e₁ = ρ e₁ := by rw [← map_mul, he]
  obtain ⟨v, w, hvw, hwv⟩ := rank_one_factor O n (ρ e₁) hE hrk
  have hmap : ∀ i, ∑ j, ρ e₁ i j * v j = v i := fun i => by
    simp only [hvw]
    rw [show ∑ j, v i * w j * v j = v i * ∑ j, w j * v j by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring, hwv, mul_one]
  have hfix : e₁ • (show LatM O O n ρ from v) = (show LatM O O n ρ from v) := by
    funext i
    show ∑ j, ρ e₁ i j • v j = v i
    simpa only [smul_eq_mul] using hmap i
  refine ⟨v, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfix, ?_⟩
  · intro a u x
    funext i
    show (∑ j, ρ a i j • u j) • x = ∑ j, ρ a i j • (u j • x)
    rw [Finset.sum_smul]
    simp only [smul_eq_mul, mul_smul]
  · intro m hm
    refine ⟨∑ j, w j • m j, ?_⟩
    conv_lhs => rw [← hm]
    funext i
    show ∑ j, ρ e₁ i j • m j = v i • ∑ j, w j • m j
    simp only [hvw, mul_smul, Finset.smul_sum]
  · intro a u
    funext i
    show algebraMap O (FractionRing O) (∑ j, ρ a i j • u j) =
      ∑ j, ρ a i j • algebraMap O (FractionRing O) (u j)
    rw [map_sum]
    simp [Algebra.smul_def]
  · intro a u
    funext i
    show (1 : Submodule O (FractionRing O)).mkQ (∑ j, ρ a i j • u j) =
      ∑ j, ρ a i j • (1 : Submodule O (FractionRing O)).mkQ (u j)
    rw [map_sum]
    simp only [map_smul]
  · intro u x
    funext i
    show u i • Submodule.Quotient.mk x = (1 : Submodule O (FractionRing O)).mkQ (x * algebraMap O (FractionRing O) (u i))
    rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Algebra.smul_def, mul_comm]
  · intro u u' h
    funext i
    exact IsFractionRing.injective O (FractionRing O) (congrFun h i)
  · intro q
    choose y hy using fun i => Submodule.Quotient.mk_surjective _ (q i)
    exact ⟨y, funext hy⟩
  · ext u
    simp only [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro h
      have hi : ∀ i, ∃ c : O, algebraMap O (FractionRing O) c = u i := fun i => by
        have h' : (1 : Submodule O (FractionRing O)).mkQ (u i) = 0 := congrFun h i
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_one] at h'
        exact h'
      choose c hc using hi
      exact ⟨c, funext hc⟩
    · rintro ⟨c, rfl⟩
      funext i
      show (1 : Submodule O (FractionRing O)).mkQ (algebraMap O (FractionRing O) (c i)) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
      exact ⟨c i, rfl⟩
  · intro u
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
      (Finset.univ : Finset n) (fun i => (u i : FractionRing O))
    refine ⟨b, nonZeroDivisors.coe_ne_zero b, ?_⟩
    choose c hc using fun i => hb i (Finset.mem_univ i)
    exact ⟨c, funext fun i => (hc i).trans rfl⟩
  · intro u
    obtain ⟨c, hc⟩ := hsurj (Matrix.of fun i j => u i * w j)
    refine ⟨c, ?_⟩
    have hms : (c * e₁) • (show LatM O O n ρ from v) = c • e₁ • (show LatM O O n ρ from v) :=
      mul_smul _ _ _
    refine hms.trans ?_
    rw [hfix]
    funext i
    show ∑ j, ρ c i j • v j = u i
    simp only [hc, Matrix.of_apply, smul_eq_mul]
    rw [show ∑ j, u i * w j * v j = u i * ∑ j, w j * v j by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring, hwv, mul_one]

/- English proof (translation)
Use `⟨fun c => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `hsc c`. Use `⟨y * δO, Ideal.mul_mem_left _ y (Ideal.mem_span_singleton_self δO), fun m => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, hE, hy, mul_smul]`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.1 hx`.

Use `⟨algebraMap O A a, fun m => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, hE, algebraMap_smul, mul_smul]`.
-/
theorem scalar_action_on_block (O : Type) [CommRing O] (A : Type) [Ring A] [Algebra O A] (M : Type) [AddCommGroup M] [Module A M]
    [Module O M] [IsScalarTower O A M] (E : A) (δO : O) (hE : ∀ m : M, E • m = δO • m)
    (hsc : ∀ c : A, ∃ y : O, ∀ m : M, c • m = y • m) : ScalarActionOnBlock O A M E δO := by
  refine ⟨fun c => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy⟩ := hsc c
    refine ⟨y * δO, Ideal.mul_mem_left _ y (Ideal.mem_span_singleton_self δO), fun m => ?_⟩
    rw [mul_smul, hE, hy, mul_smul]
  · obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    refine ⟨algebraMap O A a, fun m => ?_⟩
    rw [mul_smul, hE, algebraMap_smul, mul_smul]

end Formalism.RepresentationBoundsCohomology.SF

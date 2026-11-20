import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

/- English proof (translation)
Take `⟨i, hi⟩` from `I.2.1`. Rewrite `ha` using `[twistMod_eq_span 0 I hi, zpow_zero, Submodule.mem_span_singleton]`. Take `⟨c, rfl⟩` from `ha`. Rewrite using `[chartRing_smul_def, mul_one]`. Conclude with `c.2`.
-/
theorem res_mem_chartRing_of_mem_twistMod_zero {I : Chart x} {a : Ω} (ha : a ∈ twistMod S x 0 I) :
    a ∈ chartRing S x I := by
  obtain ⟨i, hi⟩ := I.2.1
  rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.mem_span_singleton] at ha
  obtain ⟨c, rfl⟩ := ha
  rw [chartRing_smul_def, mul_one]; exact c.2

/- English proof (translation)
Use `(twistMod S x 0 I).smul_mem ⟨a, ha⟩ (one_mem_twistMod_zero I)` as an intermediate fact. Rewrite `this` using `[chartRing_smul_def, mul_one]`. Then use the resulting hypothesis.
-/
theorem res_mem_twistMod_zero_of_mem_chartRing {I : Chart x} {a : Ω} (ha : a ∈ chartRing S x I) :
    a ∈ twistMod S x 0 I := by
  have := (twistMod S x 0 I).smul_mem ⟨a, ha⟩ (one_mem_twistMod_zero I)
  rwa [chartRing_smul_def, mul_one] at this

/- English proof (translation)
Proceed by induction on `n generalizing b with`. Consider the case `zero`. Establish `hb' : b ∈ chartRing S x I` using `res_mem_chartRing_of_mem_twistMod_zero hb`. Use `((H.pow m).sub I).smul_mem ⟨b, hb'⟩ ha` as an intermediate fact. Rewrite `this` using `[chartRing_smul_def]`.

Rewrite using `[mul_comm]`. Conclude with `this`. Consider the case `succ n ih`. Express the relevant statement in the definitionally equal form `b ∈ ((H.pow n).twist H).sub I at hb`. Express the relevant statement in the definitionally equal form `a * b ∈ ((H.pow (m + n)).twist H).sub I`.

Use `Submodule.span_induction (p := fun z _ => a * z ∈ ((H.pow (m + n)).twist H).sub I) ?_ ?_ ?_ ?_ hb` and prove the remaining obligations. Introduce and unpack `_ ⟨q, hq, z, hz, rfl⟩`. Use `Submodule.subset_span ⟨q, hq, a * z, ih hz, ?_⟩` and prove the remaining obligations. Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[mul_zero]`. Conclude with `Submodule.zero_mem _`. Introduce `u v _ _ hu hv`. Rewrite using `[mul_add]`. Conclude with `Submodule.add_mem _ hu hv`.

Introduce `c u _ hu`. Rewrite using `[chartRing_smul_def, mul_left_comm, ← chartRing_smul_def]`. Conclude with `Submodule.smul_mem _ c hu`.
-/
theorem SubSystem.res_mul_mem_pow (H : SubSystem S x Ω) (I : Chart x) {m : ℕ} {a : Ω}
    (ha : a ∈ (H.pow m).sub I) (n : ℕ) {b : Ω} (hb : b ∈ (H.pow n).sub I) :
    a * b ∈ (H.pow (m + n)).sub I := by
  induction n generalizing b with
  | zero =>
    have hb' : b ∈ chartRing S x I := res_mem_chartRing_of_mem_twistMod_zero hb
    have := ((H.pow m).sub I).smul_mem ⟨b, hb'⟩ ha
    rw [chartRing_smul_def] at this
    rw [mul_comm]; exact this
  | succ n ih =>
    change b ∈ ((H.pow n).twist H).sub I at hb
    change a * b ∈ ((H.pow (m + n)).twist H).sub I
    refine Submodule.span_induction (p := fun z _ => a * z ∈ ((H.pow (m + n)).twist H).sub I)
      ?_ ?_ ?_ ?_ hb
    · rintro _ ⟨q, hq, z, hz, rfl⟩
      refine Submodule.subset_span ⟨q, hq, a * z, ih hz, ?_⟩
      simp only [smul_eq_mul]; ring
    · rw [mul_zero]; exact Submodule.zero_mem _
    · intro u v _ _ hu hv; rw [mul_add]; exact Submodule.add_mem _ hu hv
    · intro c u _ hu
      rw [chartRing_smul_def, mul_left_comm, ← chartRing_smul_def]
      exact Submodule.smul_mem _ c hu

/- English proof (translation)
Proceed by induction on `n generalizing z with`. Consider the case `zero`. Take `⟨a, ha, haz⟩` from `((twistBundle S x 0).mem_iff I J hIJ z).mp hz`. Conclude with `⟨a, ha, haz⟩`. Consider the case `succ n ih`.

Express the relevant statement in the definitionally equal form `z ∈ ((H.pow n).twist H.toSubSystem).sub J at hz`. Express the relevant statement in the definitionally equal form `∃ a : chartRing S x I, IsUnit (chartIncl hIJ a) ∧ (a : Ω) * z ∈ ((H.pow n).twist H.toSubSystem).sub I`. Use `Submodule.span_induction (p := fun z _ => ∃ a : chartRing S x I, IsUnit (chartIncl hIJ a) ∧ (a : Ω) * z ∈ ((H.pow n).twist H.toSubSystem).sub I) ?_ ?_ ?_ ?_ hz` and prove the remaining obligations. Introduce and unpack `_ ⟨q, hq, w, hw, rfl⟩`. Take `⟨a₁, ha₁, hq'⟩` from `(H.mem_iff I J hIJ q).mp hq`.

Take `⟨a₂, ha₂, hw'⟩` from `ih hw`. Use `⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, Submodule.subset_span ⟨_, hq', _, hw', ?_⟩⟩` and prove the remaining obligations. Simplify using `only [smul_eq_mul, Subalgebra.coe_mul]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨1, by rw [map_one]; exact isUnit_one, by rw [mul_zero]; exact Submodule.zero_mem _⟩`.

Introduce and unpack `u v _ _ ⟨a₁, ha₁, hu⟩ ⟨a₂, ha₂, hv⟩`. Use `⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩` and prove the remaining obligations. Establish `h1` using `Submodule.smul_mem _ a₂ hu`. Establish `h2` using `Submodule.smul_mem _ a₁ hv`. Rewrite `h1`, `h2` using `[chartRing_smul_def]`.

Use `Submodule.add_mem _ h1 h2 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Subalgebra.coe_mul]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `c u _ ⟨a, ha, hu⟩`. Take `⟨a', ha', hc⟩` from `exists_isUnit_mul_mem hIJ c`.

Use `⟨a' * a, by rw [map_mul]; exact ha'.mul ha, ?_⟩` and prove the remaining obligations. Use `Submodule.smul_mem _ (⟨_, hc⟩ : chartRing S x I) hu` as an intermediate fact. Rewrite `this` using `[chartRing_smul_def]`. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[chartRing_smul_def]`.

Simplify using `only [Subalgebra.coe_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem LineBundle.res_exists_mul_mem_pow (H : LineBundle S x) {I J : Chart x} (hIJ : I.1 ⊆ J.1)
    (n : ℕ) {z : Ω} (hz : z ∈ (H.pow n).sub J) :
    ∃ a : chartRing S x I, IsUnit (chartIncl hIJ a) ∧ (a : Ω) * z ∈ (H.pow n).sub I := by
  induction n generalizing z with
  | zero =>
    obtain ⟨a, ha, haz⟩ := ((twistBundle S x 0).mem_iff I J hIJ z).mp hz
    exact ⟨a, ha, haz⟩
  | succ n ih =>
    change z ∈ ((H.pow n).twist H.toSubSystem).sub J at hz
    change ∃ a : chartRing S x I, IsUnit (chartIncl hIJ a) ∧
      (a : Ω) * z ∈ ((H.pow n).twist H.toSubSystem).sub I
    refine Submodule.span_induction (p := fun z _ => ∃ a : chartRing S x I,
      IsUnit (chartIncl hIJ a) ∧ (a : Ω) * z ∈ ((H.pow n).twist H.toSubSystem).sub I) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, w, hw, rfl⟩
      obtain ⟨a₁, ha₁, hq'⟩ := (H.mem_iff I J hIJ q).mp hq
      obtain ⟨a₂, ha₂, hw'⟩ := ih hw
      refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂,
        Submodule.subset_span ⟨_, hq', _, hw', ?_⟩⟩
      simp only [smul_eq_mul, Subalgebra.coe_mul]; ring
    · exact ⟨1, by rw [map_one]; exact isUnit_one, by rw [mul_zero]; exact Submodule.zero_mem _⟩
    · rintro u v _ _ ⟨a₁, ha₁, hu⟩ ⟨a₂, ha₂, hv⟩
      refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
      have h1 := Submodule.smul_mem _ a₂ hu
      have h2 := Submodule.smul_mem _ a₁ hv
      rw [chartRing_smul_def] at h1 h2
      convert Submodule.add_mem _ h1 h2 using 1
      simp only [Subalgebra.coe_mul]; ring
    · rintro c u _ ⟨a, ha, hu⟩
      obtain ⟨a', ha', hc⟩ := exists_isUnit_mul_mem hIJ c
      refine ⟨a' * a, by rw [map_mul]; exact ha'.mul ha, ?_⟩
      have := Submodule.smul_mem _ (⟨_, hc⟩ : chartRing S x I) hu
      rw [chartRing_smul_def] at this
      convert this using 1
      rw [chartRing_smul_def]; simp only [Subalgebra.coe_mul]; ring

section AmpleChart

variable {H : SubSystem S x Ω} {σ : Ω} {I : Chart x}

/- English proof (translation)
Take `⟨n, hn⟩` from `ha`. Take `⟨m, hm⟩` from `hb`. Use `⟨n + m, ?_⟩` and prove the remaining obligations. Rewrite `hn`, `hm`, the goal using `[one_mul]`. Use `H.res_mul_mem_pow I hn m hm` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem res_ampleChart_mul {a b : Ω} (ha : a ∈ ampleChart H 1 σ I) (hb : b ∈ ampleChart H 1 σ I) :
    a * b ∈ ampleChart H 1 σ I := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨m, hm⟩ := hb
  refine ⟨n + m, ?_⟩
  rw [one_mul] at hn hm ⊢
  have := H.res_mul_mem_pow I hn m hm
  convert this using 1; ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, by rw [pow_zero, mul_one, mul_zero]; exact res_mem_twistMod_zero_of_mem_chartRing ha⟩`.
-/
theorem res_chartRing_sub_ampleChart {a : Ω} (ha : a ∈ chartRing S x I) : a ∈ ampleChart H 1 σ I :=
  ⟨0, by rw [pow_zero, mul_one, mul_zero]; exact res_mem_twistMod_zero_of_mem_chartRing ha⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero]`. Conclude with `res_chartRing_sub_ampleChart (one_mem _)`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `res_ampleChart_mul ih ha`.
-/
theorem res_ampleChart_pow {a : Ω} (ha : a ∈ ampleChart H 1 σ I) (n : ℕ) :
    a ^ n ∈ ampleChart H 1 σ I := by
  induction n with
  | zero => rw [pow_zero]; exact res_chartRing_sub_ampleChart (one_mem _)
  | succ n ih => rw [pow_succ]; exact res_ampleChart_mul ih ha

end AmpleChart

variable (x) in

def resUnionChart (I J : Chart x) : Chart x :=
  ⟨I.1 ∪ J.1, I.2.1.mono Finset.subset_union_left, Finset.union_subset I.2.2 J.2.2⟩

/- English proof (translation)
Use `IsHomogeneous.prod s (fun i => (X i : Poly S N)) (fun _ => 1) (fun i _ => isHomogeneous_X S i)` as an intermediate fact. Simplify using `using this`.
-/
theorem res_isHomogeneous_prod_X (s : Finset (Fin (N + 1))) :
    (∏ i ∈ s, (X i : Poly S N)).IsHomogeneous s.card := by
  have := IsHomogeneous.prod s (fun i => (X i : Poly S N)) (fun _ => 1)
    (fun i _ => isHomogeneous_X S i)
  simpa using this

/- English proof (translation)
Simplify using `[map_prod]`.
-/
theorem res_aeval_prod_X (s : Finset (Fin (N + 1))) :
    aeval x (∏ i ∈ s, (X i : Poly S N)) = ∏ i ∈ s, x i := by
  simp [map_prod]

/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.mpr fun _ hi => (mem_support x).mp (I.2.2 hi)`.
-/
theorem res_xProd_ne_zero (I : Chart x) : xProd I ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hi => (mem_support x).mp (I.2.2 hi)

/- English proof (translation)
Use `set t' := xProd J ^ I.1.card / xProd I ^ J.1.card with ht'`. Take `⟨i₀, hi₀⟩` from `I.2.1`. Establish `hx₀ : x i₀ ≠ 0` using `(mem_support x).mp (I.2.2 hi₀)`. Set `T : Ω → Prop` to `fun u => ∃ M : ℕ, t' ^ M * u ∈ chartRing S x I`. Establish `hTmem : ∀ {u}, u ∈ chartRing S x I → T u` using `fun hu => ⟨0, by rw [pow_zero, one_mul]; exact hu⟩`.

Establish `hTmul : ∀ {u v}, T u → T v → T (u * v)`. Introduce and unpack `u v ⟨M, hM⟩ ⟨M', hM'⟩`. Use `⟨M + M', ?_⟩` and prove the remaining obligations. Use `mul_mem hM hM'` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Establish `hgen : ∀ i ∈ I.1 ∪ J.1, T (x i₀ / x i)`. Introduce `i hi`. Break down `Finset.mem_union.mp hi with hiI | hiJ` into its components or cases. Conclude with `hTmem ⟨X i₀, X i, 1, X_mem_monos hiI, isHomogeneous_X S i₀, isHomogeneous_X S i, by simp⟩`.

Establish `hxi : x i ≠ 0` using `(mem_support x).mp (J.2.2 hiJ)`. Take `⟨a, ha⟩ : ∃ a, I.1.card = a + 1` from `⟨I.1.card - 1, (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr I.2.1)).symm⟩`. Take `⟨c, hc⟩ : ∃ c, (J.1.erase i).card = c` from `⟨_, rfl⟩`. Establish `hJc : J.1.card = c + 1` using `by rw [← hc, Finset.card_erase_add_one hiJ]`. Use `⟨1, X i₀ * (∏ l ∈ J.1.erase i, (X l : Poly S N)) * (∏ l ∈ J.1, (X l : Poly S N)) ^ a, (∏ l ∈ I.1, (X l : Poly S N)) ^ J.1.card, (a + 1) * (c + 1), pow_mem (prod_mem fun l hl => X_mem_monos hl) _, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `h1` using `((isHomogeneous_X S i₀).mul (res_isHomogeneous_prod_X (S := S) (J.1.erase i))).mul ((res_isHomogeneous_prod_X (S := S) J.1).pow a)`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hc, hJc]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `(res_isHomogeneous_prod_X (S := S) I.1).pow J.1.card`.

Use `h1 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[ha, hJc]`. Establish `hprod : ∏ l ∈ J.1, x l = x i * ∏ l ∈ J.1.erase i, x l` using `(Finset.mul_prod_erase _ _ hiJ).symm`. Establish `hxI` using `res_xProd_ne_zero I`. Simplify using `only [map_mul, map_pow, aeval_X, res_aeval_prod_X, ht', xProd]`.

Unfold `xProd at hxI`. Rewrite using `[ha, hprod]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hmono : ∀ s ∈ monos (S` using `S) (I.1 ∪ J.1), ∃ e : ℕ, s.IsHomogeneous e ∧ T (x i₀ ^ e / aeval x s) := by`.

Introduce `s hs`. Proceed by induction on `hs using Submonoid.closure_induction with`. Consider the case `mem s hs`. Take `⟨i, hi, rfl⟩` from `hs`. Conclude with `⟨1, isHomogeneous_X S i, by rw [pow_one, aeval_X]; exact hgen i (Finset.mem_coe.mp hi)⟩`.

Consider the case `one => exact ⟨0, isHomogeneous_one _ _, hTmem (by rw [pow_zero, map_one, div_one]; exact one_mem _)⟩`. Consider the case `mul s s' _ _ hs hs'`. Take `⟨e, he, hT⟩` from `hs`. Take `⟨e', he', hT'⟩` from `hs'`. Use `⟨e + e', he.mul he', ?_⟩` and prove the remaining obligations.

Use `hTmul hT hT'` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[pow_add, map_mul, div_mul_div_comm]`. Take `⟨f, s, e, hs, hf, hse, rfl⟩` from `hu`. Establish `hs0 : aeval x s ≠ 0` using `eval_ne_zero_of_mem_monos (resUnionChart x I J) hs`.

Take `⟨e', he', hT⟩` from `hmono s hs`. Establish `hee : e = e'` using `hse.inj_right he' (fun h => hs0 (by rw [h, map_zero]))`. Substitute `hee` using the available equality. Establish `h1 : aeval x f / x i₀ ^ e ∈ chartRing S x I` using `⟨f, X i₀ ^ e, e, pow_mem (X_mem_monos hi₀) e, hf, isHomogeneous_X_pow i₀ e, by`. Rewrite using `[map_pow, aeval_X]⟩`.

Take `⟨M, hM⟩` from `hTmul (hTmem h1) hT`. Use `⟨M, ?_⟩` and prove the remaining obligations. Use `hM using 2` and compare the differences between its conclusion and the goal. Clear the denominators using the available nonvanishing facts.
-/
theorem res_exists_pow_mul_mem_chartRing (I J : Chart x) {u : Ω}
    (hu : u ∈ chartRing S x (resUnionChart x I J)) :
    ∃ M : ℕ, (xProd J ^ I.1.card / xProd I ^ J.1.card) ^ M * u ∈ chartRing S x I := by
  set t' := xProd J ^ I.1.card / xProd I ^ J.1.card with ht'
  obtain ⟨i₀, hi₀⟩ := I.2.1
  have hx₀ : x i₀ ≠ 0 := (mem_support x).mp (I.2.2 hi₀)
  let T : Ω → Prop := fun u => ∃ M : ℕ, t' ^ M * u ∈ chartRing S x I
  have hTmem : ∀ {u}, u ∈ chartRing S x I → T u := fun hu => ⟨0, by rw [pow_zero, one_mul]; exact hu⟩
  have hTmul : ∀ {u v}, T u → T v → T (u * v) := by
    rintro u v ⟨M, hM⟩ ⟨M', hM'⟩
    refine ⟨M + M', ?_⟩
    have := mul_mem hM hM'
    convert this using 1; ring

  have hgen : ∀ i ∈ I.1 ∪ J.1, T (x i₀ / x i) := by
    intro i hi
    rcases Finset.mem_union.mp hi with hiI | hiJ
    · exact hTmem ⟨X i₀, X i, 1, X_mem_monos hiI, isHomogeneous_X S i₀, isHomogeneous_X S i,
        by simp⟩
    · have hxi : x i ≠ 0 := (mem_support x).mp (J.2.2 hiJ)
      obtain ⟨a, ha⟩ : ∃ a, I.1.card = a + 1 :=
        ⟨I.1.card - 1, (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr I.2.1)).symm⟩
      obtain ⟨c, hc⟩ : ∃ c, (J.1.erase i).card = c := ⟨_, rfl⟩
      have hJc : J.1.card = c + 1 := by rw [← hc, Finset.card_erase_add_one hiJ]
      refine ⟨1, X i₀ * (∏ l ∈ J.1.erase i, (X l : Poly S N)) * (∏ l ∈ J.1, (X l : Poly S N)) ^ a,
        (∏ l ∈ I.1, (X l : Poly S N)) ^ J.1.card, (a + 1) * (c + 1),
        pow_mem (prod_mem fun l hl => X_mem_monos hl) _, ?_, ?_, ?_⟩
      · have h1 := ((isHomogeneous_X S i₀).mul (res_isHomogeneous_prod_X (S := S) (J.1.erase i))).mul
          ((res_isHomogeneous_prod_X (S := S) J.1).pow a)
        convert h1 using 1
        rw [hc, hJc]; ring
      · have h1 := (res_isHomogeneous_prod_X (S := S) I.1).pow J.1.card
        convert h1 using 1
        rw [ha, hJc]
      · have hprod : ∏ l ∈ J.1, x l = x i * ∏ l ∈ J.1.erase i, x l := (Finset.mul_prod_erase _ _ hiJ).symm
        have hxI := res_xProd_ne_zero I
        simp only [map_mul, map_pow, aeval_X, res_aeval_prod_X, ht', xProd]
        unfold xProd at hxI
        rw [ha, hprod]
        field_simp
        ring

  have hmono : ∀ s ∈ monos (S := S) (I.1 ∪ J.1), ∃ e : ℕ, s.IsHomogeneous e ∧
      T (x i₀ ^ e / aeval x s) := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem s hs =>
      obtain ⟨i, hi, rfl⟩ := hs
      exact ⟨1, isHomogeneous_X S i, by rw [pow_one, aeval_X]; exact hgen i (Finset.mem_coe.mp hi)⟩
    | one => exact ⟨0, isHomogeneous_one _ _, hTmem (by rw [pow_zero, map_one, div_one]; exact one_mem _)⟩
    | mul s s' _ _ hs hs' =>
      obtain ⟨e, he, hT⟩ := hs
      obtain ⟨e', he', hT'⟩ := hs'
      refine ⟨e + e', he.mul he', ?_⟩
      have := hTmul hT hT'
      convert this using 1
      rw [pow_add, map_mul, div_mul_div_comm]
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := hu
  have hs0 : aeval x s ≠ 0 := eval_ne_zero_of_mem_monos (resUnionChart x I J) hs
  obtain ⟨e', he', hT⟩ := hmono s hs
  have hee : e = e' := hse.inj_right he' (fun h => hs0 (by rw [h, map_zero]))
  subst hee
  have h1 : aeval x f / x i₀ ^ e ∈ chartRing S x I :=
    ⟨f, X i₀ ^ e, e, pow_mem (X_mem_monos hi₀) e, hf, isHomogeneous_X_pow i₀ e, by
      rw [map_pow, aeval_X]⟩
  obtain ⟨M, hM⟩ := hTmul (hTmem h1) hT
  refine ⟨M, ?_⟩
  convert hM using 2
  field_simp

/- English proof (translation)
Establish `hloc : ∀ I : Chart x, ∃ E : ℕ, b ^ E * z ∈ ampleChart H.toSubSystem 1 σ I`. Introduce `I`. Establish `hIK : I.1 ⊆ (resUnionChart x I J).1` using `Finset.subset_union_left`. Establish `hJK : J.1 ⊆ (resUnionChart x I J).1` using `Finset.subset_union_right`. Take `⟨n, hn⟩` from `hz`.

Rewrite `hn` using `[one_mul]`. Establish `hnK` using `(H.pow n).mono J (resUnionChart x I J) hJK _ hn`. Take `⟨a, ha, haz⟩` from `H.res_exists_mul_mem_pow hIK n hnK`. Establish `haz' : (a : Ω) * z ∈ ampleChart H.toSubSystem 1 σ I` using `⟨n, by rw [one_mul, mul_assoc]; exact haz⟩`. Take `⟨v, hv⟩` from `ha.exists_right_inv`.

Establish `hav : (a : Ω) * (v : Ω) = 1` using `congrArg Subtype.val hv`. Take `⟨M, hM⟩` from `res_exists_pow_mul_mem_chartRing I J v.2`. Take `⟨e, he⟩` from `hbJ I`. Use `⟨e * M, ?_⟩` and prove the remaining obligations. Establish `hxI` using `res_xProd_ne_zero I`.

Establish `hxJ` using `res_xProd_ne_zero J`. Establish `htt : (xProd J ^ I.1.card / xProd I ^ J.1.card) * (xProd I ^ J.1.card / xProd J ^ I.1.card) = 1`. Clear the denominators using the available nonvanishing facts. Establish `key : b ^ (e * M) * z = ((xProd J ^ I.1.card / xProd I ^ J.1.card) ^ M * (v : Ω)) * (b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card)) ^ M * ((a : Ω) * z)`. Establish `: ((xProd J ^ I.1.card / xProd I ^ J.1.card) ^ M * (v : Ω)) * (b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card)) ^ M * ((a : Ω) * z) = ((xProd J ^ I.1.card / xProd I ^ J.1.card) * (xProd I ^ J.1.card / xProd J ^ I.1.card)) ^ M * b ^ (e * M) * ((a : Ω) * v) * z`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, htt, hav]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Conclude with `res_ampleChart_mul (res_ampleChart_mul (res_chartRing_sub_ampleChart hM) (res_ampleChart_pow he M)) haz'`.

Use `choose E hE using hloc`. Use `⟨Finset.univ.sup E, Set.mem_iInter.mpr fun I => ?_⟩` and prove the remaining obligations. Establish `hle : E I ≤ Finset.univ.sup E` using `Finset.le_sup (Finset.mem_univ I)`. Establish `hbI : b ∈ ampleChart H.toSubSystem 1 σ I` using `Set.mem_iInter.mp hb I`. Rewrite using `[← Nat.sub_add_cancel hle, pow_add, mul_assoc]`.

Conclude with `res_ampleChart_mul (res_ampleChart_pow hbI _) (hE I)`.
-/
theorem res_exists_pow_mul_mem_ampleRing (H : LineBundle S x) {σ b : Ω} {J : Chart x}
    (hb : b ∈ ampleRing H.toSubSystem 1 σ)
    (hbJ : ∀ I : Chart x, ∃ e : ℕ,
      b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card) ∈ ampleChart H.toSubSystem 1 σ I)
    {z : Ω} (hz : z ∈ ampleChart H.toSubSystem 1 σ J) :
    ∃ E : ℕ, b ^ E * z ∈ ampleRing H.toSubSystem 1 σ := by
  have hloc : ∀ I : Chart x, ∃ E : ℕ, b ^ E * z ∈ ampleChart H.toSubSystem 1 σ I := by
    intro I
    have hIK : I.1 ⊆ (resUnionChart x I J).1 := Finset.subset_union_left
    have hJK : J.1 ⊆ (resUnionChart x I J).1 := Finset.subset_union_right
    obtain ⟨n, hn⟩ := hz
    rw [one_mul] at hn
    have hnK := (H.pow n).mono J (resUnionChart x I J) hJK _ hn
    obtain ⟨a, ha, haz⟩ := H.res_exists_mul_mem_pow hIK n hnK
    have haz' : (a : Ω) * z ∈ ampleChart H.toSubSystem 1 σ I :=
      ⟨n, by rw [one_mul, mul_assoc]; exact haz⟩
    obtain ⟨v, hv⟩ := ha.exists_right_inv
    have hav : (a : Ω) * (v : Ω) = 1 := congrArg Subtype.val hv
    obtain ⟨M, hM⟩ := res_exists_pow_mul_mem_chartRing I J v.2
    obtain ⟨e, he⟩ := hbJ I
    refine ⟨e * M, ?_⟩
    have hxI := res_xProd_ne_zero I
    have hxJ := res_xProd_ne_zero J
    have htt : (xProd J ^ I.1.card / xProd I ^ J.1.card) *
        (xProd I ^ J.1.card / xProd J ^ I.1.card) = 1 := by
      field_simp
    have key : b ^ (e * M) * z = ((xProd J ^ I.1.card / xProd I ^ J.1.card) ^ M * (v : Ω)) *
        (b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card)) ^ M * ((a : Ω) * z) := by
      have : ((xProd J ^ I.1.card / xProd I ^ J.1.card) ^ M * (v : Ω)) *
          (b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card)) ^ M * ((a : Ω) * z) =
          ((xProd J ^ I.1.card / xProd I ^ J.1.card) *
            (xProd I ^ J.1.card / xProd J ^ I.1.card)) ^ M * b ^ (e * M) * ((a : Ω) * v) * z := by
        ring
      rw [this, htt, hav]; ring
    rw [key]
    exact res_ampleChart_mul (res_ampleChart_mul (res_chartRing_sub_ampleChart hM) (res_ampleChart_pow he M)) haz'
  choose E hE using hloc
  refine ⟨Finset.univ.sup E, Set.mem_iInter.mpr fun I => ?_⟩
  have hle : E I ≤ Finset.univ.sup E := Finset.le_sup (Finset.mem_univ I)
  have hbI : b ∈ ampleChart H.toSubSystem 1 σ I := Set.mem_iInter.mp hb I
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
  exact res_ampleChart_mul (res_ampleChart_pow hbI _) (hE I)

/- English proof (translation)
Use `Submodule.span_induction (p := fun z _ => z ∈ Submodule.span (chartRing S x J) R) (fun w hw => Submodule.subset_span hw) (Submodule.zero_mem _) (fun _ _ _ _ hu hv => Submodule.add_mem _ hu hv) ?_ hz` and prove the remaining obligations. Introduce `c u _ hu`. Use `Submodule.smul_mem _ (chartIncl hIJ c) hu` as an intermediate fact. Rewrite `this`, the goal using `[chartRing_smul_def]`. Conclude with `this`.
-/
theorem res_span_chart_le {R : Set Ω} {I J : Chart x} (hIJ : I.1 ⊆ J.1) {z : Ω}
    (hz : z ∈ Submodule.span (chartRing S x I) R) : z ∈ Submodule.span (chartRing S x J) R := by
  refine Submodule.span_induction (p := fun z _ => z ∈ Submodule.span (chartRing S x J) R)
    (fun w hw => Submodule.subset_span hw) (Submodule.zero_mem _)
    (fun _ _ _ _ hu hv => Submodule.add_mem _ hu hv) ?_ hz
  intro c u _ hu
  have := Submodule.smul_mem _ (chartIncl hIJ c) hu
  rw [chartRing_smul_def] at this ⊢
  exact this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hz`. Use `Submodule.span_induction (p := fun z _ => ∃ a : chartRing S x I, IsUnit (chartIncl hIJ a) ∧ (a : Ω) • z ∈ Submodule.span (chartRing S x I) R) ?_ ?_ ?_ ?_ hz` and prove the remaining obligations. Introduce `w hw`. Conclude with `⟨1, by rw [map_one]; exact isUnit_one, by rw [OneMemClass.coe_one, one_smul]; exact Submodule.subset_span hw⟩`.

Conclude with `⟨1, by rw [map_one]; exact isUnit_one, by rw [smul_zero]; exact Submodule.zero_mem _⟩`. Introduce and unpack `u v _ _ ⟨a₁, ha₁, hu⟩ ⟨a₂, ha₂, hv⟩`. Use `⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩` and prove the remaining obligations. Establish `h1` using `Submodule.smul_mem _ a₂ hu`. Establish `h2` using `Submodule.smul_mem _ a₁ hv`.

Rewrite `h1`, `h2` using `[chartRing_smul_def, smul_eq_mul]`. Use `Submodule.add_mem _ h1 h2 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [smul_eq_mul, Subalgebra.coe_mul]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `c u _ ⟨a, ha, hu⟩`.

Take `⟨a', ha', hc⟩` from `exists_isUnit_mul_mem hIJ c`. Use `⟨a' * a, by rw [map_mul]; exact ha'.mul ha, ?_⟩` and prove the remaining obligations. Use `Submodule.smul_mem _ (⟨_, hc⟩ : chartRing S x I) hu` as an intermediate fact. Rewrite `this` using `[chartRing_smul_def, smul_eq_mul]`. Use `this using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[chartRing_smul_def]`. Simplify using `only [smul_eq_mul, Subalgebra.coe_mul]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨a, ⟨u, hu⟩, haz⟩`. Establish `hJ` using `res_span_chart_le hIJ haz`.

Establish `hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1`. Use `congrArg Subtype.val (Units.inv_mul u)` as an intermediate fact. Rewrite `this` using `[hu]`. Conclude with `this`. Establish `hz : z = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • z)`.

Rewrite using `[chartRing_smul_def, smul_eq_mul, ← mul_assoc, hinv, one_mul]`. Rewrite using `[hz]`. Conclude with `Submodule.smul_mem _ _ hJ`.
-/
theorem res_mem_span_iff_exists_isUnit {R : Set Ω} {I J : Chart x} (hIJ : I.1 ⊆ J.1) (z : Ω) :
    z ∈ Submodule.span (chartRing S x J) R ↔ ∃ a : chartRing S x I, IsUnit (chartIncl hIJ a) ∧
      (a : Ω) • z ∈ Submodule.span (chartRing S x I) R := by
  constructor
  · intro hz
    refine Submodule.span_induction (p := fun z _ => ∃ a : chartRing S x I, IsUnit (chartIncl hIJ a) ∧
      (a : Ω) • z ∈ Submodule.span (chartRing S x I) R) ?_ ?_ ?_ ?_ hz
    · intro w hw
      exact ⟨1, by rw [map_one]; exact isUnit_one,
        by rw [OneMemClass.coe_one, one_smul]; exact Submodule.subset_span hw⟩
    · exact ⟨1, by rw [map_one]; exact isUnit_one, by rw [smul_zero]; exact Submodule.zero_mem _⟩
    · rintro u v _ _ ⟨a₁, ha₁, hu⟩ ⟨a₂, ha₂, hv⟩
      refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
      have h1 := Submodule.smul_mem _ a₂ hu
      have h2 := Submodule.smul_mem _ a₁ hv
      rw [chartRing_smul_def, smul_eq_mul] at h1 h2
      convert Submodule.add_mem _ h1 h2 using 1
      simp only [smul_eq_mul, Subalgebra.coe_mul]; ring
    · rintro c u _ ⟨a, ha, hu⟩
      obtain ⟨a', ha', hc⟩ := exists_isUnit_mul_mem hIJ c
      refine ⟨a' * a, by rw [map_mul]; exact ha'.mul ha, ?_⟩
      have := Submodule.smul_mem _ (⟨_, hc⟩ : chartRing S x I) hu
      rw [chartRing_smul_def, smul_eq_mul] at this
      convert this using 1
      rw [chartRing_smul_def]; simp only [smul_eq_mul, Subalgebra.coe_mul]; ring
  · rintro ⟨a, ⟨u, hu⟩, haz⟩
    have hJ := res_span_chart_le hIJ haz
    have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      rw [hu] at this
      exact this
    have hz : z = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • z) := by
      rw [chartRing_smul_def, smul_eq_mul, ← mul_assoc, hinv, one_mul]
    rw [hz]
    exact Submodule.smul_mem _ _ hJ

end

end GroundTheory.Heights₂.Heights.Kleiman

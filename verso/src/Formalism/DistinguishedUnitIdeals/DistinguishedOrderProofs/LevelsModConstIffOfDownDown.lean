import Mathlib
import Formalism.DistinguishedUnitIdeals.CoprimeProd
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.GroundTheory

noncomputable section

namespace Formalism.ExponentWindows

namespace TwoDown

open PowerSeries

section Coord

variable {O : Type} [CommRing O] {r : ℕ}

def coordA (b : Module.Basis (Fin r) O (Fin r → O)) (j : Fin r) (w : Fin r → PowerSeries O) :
    PowerSeries O :=
  ∑ i, C (b.repr (Pi.single i 1) j) * w i

/- English proof (translation)
Simplify using `[coordA, mul_add, Finset.sum_add_distrib]`.
-/
theorem coordA_add (b : Module.Basis (Fin r) O (Fin r → O)) (j : Fin r)
    (w w' : Fin r → PowerSeries O) : coordA b j (w + w') = coordA b j w + coordA b j w' := by
  simp [coordA, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[coordA, Finset.mul_sum, mul_left_comm]`.
-/
theorem coordA_smul (b : Module.Basis (Fin r) O (Fin r → O)) (j : Fin r) (g : PowerSeries O)
    (w : Fin r → PowerSeries O) : coordA b j (g • w) = g * coordA b j w := by
  simp [coordA, Finset.mul_sum, mul_left_comm]

/- English proof (translation)
Simplify using `[coordA]`.
-/
theorem coordA_zero (b : Module.Basis (Fin r) O (Fin r → O)) (j : Fin r) :
    coordA b j 0 = 0 := by
  simp [coordA]

/- English proof (translation)
Use extensionality with `k`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.
-/
theorem sum_single_smul (v : Fin r → O) : ∑ i, v i • (Pi.single i (1 : O) : Fin r → O) = v := by
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

/- English proof (translation)
Use `conv_rhs => rw [← sum_single_smul v]`. Simplify using `[coordA, cst, map_sum, mul_comm]`.
-/
theorem coordA_cst (b : Module.Basis (Fin r) O (Fin r → O)) (j : Fin r) (v : Fin r → O) :
    coordA b j (cst v) = C (b.repr v j) := by
  conv_rhs => rw [← sum_single_smul v]
  simp [coordA, cst, map_sum, mul_comm]

/- English proof (translation)
Use extensionality with `k`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coordA, cst, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Establish `hi : ∀ i, ∑ j, C (b.repr (Pi.single i 1) j) * w i * C (b j k) = w i * C ((Pi.single i (1 : O) : Fin r → O) k)`. Introduce `i`.

Establish `h` using `congrFun (b.sum_repr (Pi.single i 1)) k`. Rewrite using `[← h]`. Simplify using `[Finset.sum_apply, map_sum, Finset.mul_sum, mul_comm, mul_left_comm]`. Repeatedly rewrite using `[hi]`. Simplify using `[Pi.single_apply]`.
-/
theorem sum_coordA (b : Module.Basis (Fin r) O (Fin r → O)) (w : Fin r → PowerSeries O) :
    ∑ j, coordA b j w • cst (b j) = w := by
  ext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coordA, cst, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hi : ∀ i, ∑ j, C (b.repr (Pi.single i 1) j) * w i * C (b j k) =
      w i * C ((Pi.single i (1 : O) : Fin r → O) k) := by
    intro i
    have h := congrFun (b.sum_repr (Pi.single i 1)) k
    rw [← h]
    simp [Finset.sum_apply, map_sum, Finset.mul_sum, mul_comm, mul_left_comm]
  simp_rw [hi]
  simp [Pi.single_apply]

/- English proof (translation)
Proceed by induction on `hc using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨u, hu, rfl⟩` from `hx`. Rewrite using `[coordA_cst]`. Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.mp (hU u hu)`.

Rewrite using `[← ht, map_mul]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)`. Consider the case `zero => rw [coordA_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [coordA_add]`.

Conclude with `add_mem hx hy`. Consider the case `smul g x _ hx => rw [coordA_smul]`. Conclude with `Ideal.mul_mem_left _ _ hx`.
-/
theorem coordA_mem_of_ext (b : Module.Basis (Fin r) O (Fin r → O)) (j : Fin r)
    (U : Submodule O (Fin r → O)) (a : O) (hU : ∀ u ∈ U, b.repr u j ∈ Ideal.span {a})
    (c : Fin r → PowerSeries O) (hc : c ∈ ext U) : coordA b j c ∈ Ideal.span {C a} := by
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    rw [coordA_cst]
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (hU u hu)
    rw [← ht, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  | zero => rw [coordA_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [coordA_add]; exact add_mem hx hy
  | smul g x _ hx => rw [coordA_smul]; exact Ideal.mul_mem_left _ _ hx

/- English proof (translation)
The claim follows from `Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (hw i))`.
-/
theorem coordA_mem_ideal (b : Module.Basis (Fin r) O (Fin r → O)) (j : Fin r)
    (J : Ideal (PowerSeries O)) (w : Fin r → PowerSeries O) (hw : ∀ i, w i ∈ J) :
    coordA b j w ∈ J :=
  Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (hw i))

/- English proof (translation)
Use extensionality with `i`. Simplify using `[cst]`.
-/
theorem cst_sub (v v' : Fin r → O) : cst (v - v') = cst v - cst v' := by
  ext i; simp [cst]

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨v, hv, rfl⟩`.
-/
theorem cst_mem_ext (V : Submodule O (Fin r → O)) (v : Fin r → O) (hv : v ∈ V) :
    cst v ∈ ext V :=
  Submodule.subset_span ⟨v, hv, rfl⟩

end Coord

section PID

variable {O : Type} [CommRing O] [IsDomain O] {r : ℕ}

/- English proof (translation)
Take `⟨n, S⟩` from `U.smithNormalForm (Pi.basisFun O (Fin r))`. Use `⟨S.bM, fun j => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hj : j ∈ Set.range S.f`. Take `⟨i, rfl⟩` from `hj`. Use `⟨S.a i, fun u hu => ?_, ?_⟩` and prove the remaining obligations.

Establish `h : S.bM.repr u (S.f i) = S.bN.repr (S.a i • (⟨u, hu⟩ : U)) i` using `S.repr_apply_embedding_eq_repr_smul ⟨u, hu⟩`. Rewrite using `[h, map_smul, Finsupp.smul_apply, smul_eq_mul]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`. Rewrite using `[← S.snf i]`. Conclude with `(S.bN i).2`.

Use `⟨0, fun u hu => ?_, by simp⟩` and prove the remaining obligations. Establish `h : S.bM.repr u j = 0` using `S.repr_eq_zero_of_notMem_range ⟨u, hu⟩ hj`. Rewrite using `[h]`. Conclude with `zero_mem _`.
-/
theorem exists_adapted_basis [IsPrincipalIdealRing O] (U : Submodule O (Fin r → O)) :
    ∃ b : Module.Basis (Fin r) O (Fin r → O), ∀ j, ∃ a : O,
      (∀ u ∈ U, b.repr u j ∈ Ideal.span {a}) ∧ a • b j ∈ U := by
  obtain ⟨n, S⟩ := U.smithNormalForm (Pi.basisFun O (Fin r))
  refine ⟨S.bM, fun j => ?_⟩
  by_cases hj : j ∈ Set.range S.f
  · obtain ⟨i, rfl⟩ := hj
    refine ⟨S.a i, fun u hu => ?_, ?_⟩
    · have h : S.bM.repr u (S.f i) = S.bN.repr (S.a i • (⟨u, hu⟩ : U)) i :=
        S.repr_apply_embedding_eq_repr_smul ⟨u, hu⟩
      rw [h, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · rw [← S.snf i]; exact (S.bN i).2
  · refine ⟨0, fun u hu => ?_, by simp⟩
    have h : S.bM.repr u j = 0 := S.repr_eq_zero_of_notMem_range ⟨u, hu⟩ hj
    rw [h]; exact zero_mem _

/- English proof (translation)
Distinguish the cases in `a0 : a = 0`. Use `right`. Introduce `u hu`. Use `ha u hu` as an intermediate fact. Rewrite `this` using `[a0, Ideal.mem_span_singleton, zero_dvd_iff]`.

Conclude with `this`. Use `left`. Take `⟨n, w, hw⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible a0 hϖ`. Consider the cases of `n with`. Consider the case `zero`.

Establish `h` using `V.smul_mem (↑w⁻¹ : O) hab`. Rewrite `h` using `[hw, pow_zero, mul_one, smul_smul, Units.inv_mul, one_smul]`. Conclude with `h`. Consider the case `succ m`. It suffices to derive a contradiction.

Use `set a' : O := (w : O) * ϖ ^ m with ha'`. Establish `haa : a = ϖ * a'` using `by rw [hw, ha', pow_succ]; ring`. Establish `h1 : a' • b j ∈ V` using `hV _ (by rw [smul_smul, ← haa]; exact hab)`. Establish `h2` using `ha _ h1`. Rewrite `h2` using `[map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one, Ideal.mem_span_singleton, haa]`.

Take `⟨t, ht⟩` from `h2`. Establish `a'0 : a' ≠ 0`. Introduce `h0`. Apply `a0` to reduce the goal to its premises. Rewrite using `[haa, h0, mul_zero]`.

Establish `: a' * 1 = a' * (ϖ * t)` using `by rw [mul_one]; nth_rewrite 1 [ht]; ring`. Establish `h3` using `mul_left_cancel₀ a'0 this`. Conclude with `hϖ.not_isUnit (IsUnit.of_mul_eq_one t h3.symm)`.
-/
theorem adapted_of_saturated [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ)
    (V : Submodule O (Fin r → O)) (hV : Saturated ϖ V) (b : Module.Basis (Fin r) O (Fin r → O))
    (j : Fin r) (a : O) (ha : ∀ u ∈ V, b.repr u j ∈ Ideal.span {a}) (hab : a • b j ∈ V) :
    b j ∈ V ∨ ∀ u ∈ V, b.repr u j = 0 := by
  by_cases a0 : a = 0
  · right
    intro u hu
    have := ha u hu
    rw [a0, Ideal.mem_span_singleton, zero_dvd_iff] at this
    exact this
  left
  obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible a0 hϖ
  cases n with
  | zero =>
    have h := V.smul_mem (↑w⁻¹ : O) hab
    rw [hw, pow_zero, mul_one, smul_smul, Units.inv_mul, one_smul] at h
    exact h
  | succ m =>
    exfalso
    set a' : O := (w : O) * ϖ ^ m with ha'
    have haa : a = ϖ * a' := by rw [hw, ha', pow_succ]; ring
    have h1 : a' • b j ∈ V := hV _ (by rw [smul_smul, ← haa]; exact hab)
    have h2 := ha _ h1
    rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one, Ideal.mem_span_singleton, haa] at h2
    obtain ⟨t, ht⟩ := h2
    have a'0 : a' ≠ 0 := by
      intro h0; apply a0; rw [haa, h0, mul_zero]
    have : a' * 1 = a' * (ϖ * t) := by rw [mul_one]; nth_rewrite 1 [ht]; ring
    have h3 := mul_left_cancel₀ a'0 this
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one t h3.symm)

/- English proof (translation)
Take `⟨c, z, hc, hw⟩` from `h`. Take `⟨b, hb⟩` from `exists_adapted_basis V`. Establish `hj : ∀ j, ∃ c' t' : PowerSeries O, coordA b j w = c' + P * t' ∧ c' • cst (b j) ∈ ext V`. Introduce `j`. Take `⟨a, ha, hab⟩` from `hb j`.

Break down `adapted_of_saturated ϖ hϖ V hV b j a ha hab with hbj | h0` into its components or cases. Conclude with `⟨coordA b j w, 0, by simp, Submodule.smul_mem _ _ (cst_mem_ext V _ hbj)⟩`. Establish `hc0 : coordA b j c = 0`. Use `coordA_mem_of_ext b j V 0 (fun u hu => by rw [h0 u hu]; exact zero_mem _) c hc` as an intermediate fact. Rewrite `this` using `[map_zero, Ideal.mem_span_singleton, zero_dvd_iff]`.

Conclude with `this`. Establish `e1` using `congrArg (coordA b j) hw`. Rewrite `e1` using `[coordA_smul, coordA_add, coordA_smul, hc0, zero_add]`. Establish `: coordA b j w ∈ Ideal.span {P}` using `hP _ (by rw [e1]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))`. Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.mp this`.

Conclude with `⟨0, t, by rw [← ht]; ring, by rw [zero_smul]; exact zero_mem _⟩`. Use `choose c' t' hct hmem using hj`. Use `⟨∑ j, c' j • cst (b j), ∑ j, t' j • cst (b j), Submodule.sum_mem _ (fun j _ => hmem j), ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← sum_coordA b w]`. Repeatedly rewrite using `[hct, add_smul, Finset.sum_add_distrib, Finset.smul_sum, mul_smul]`.
-/
theorem ext_add_sat_step [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ)
    (V : Submodule O (Fin r → O)) (hV : Saturated ϖ V) (P : PowerSeries O)
    (hP : ∀ z, C ϖ * z ∈ Ideal.span {P} → z ∈ Ideal.span {P}) (w : Fin r → PowerSeries O)
    (h : ∃ c z, c ∈ ext V ∧ C ϖ • w = c + P • z) :
    ∃ c z, c ∈ ext V ∧ w = c + P • z := by
  obtain ⟨c, z, hc, hw⟩ := h
  obtain ⟨b, hb⟩ := exists_adapted_basis V
  have hj : ∀ j, ∃ c' t' : PowerSeries O, coordA b j w = c' + P * t' ∧
      c' • cst (b j) ∈ ext V := by
    intro j
    obtain ⟨a, ha, hab⟩ := hb j
    rcases adapted_of_saturated ϖ hϖ V hV b j a ha hab with hbj | h0
    · exact ⟨coordA b j w, 0, by simp, Submodule.smul_mem _ _ (cst_mem_ext V _ hbj)⟩
    · have hc0 : coordA b j c = 0 := by
        have := coordA_mem_of_ext b j V 0 (fun u hu => by rw [h0 u hu]; exact zero_mem _) c hc
        rw [map_zero, Ideal.mem_span_singleton, zero_dvd_iff] at this
        exact this
      have e1 := congrArg (coordA b j) hw
      rw [coordA_smul, coordA_add, coordA_smul, hc0, zero_add] at e1
      have : coordA b j w ∈ Ideal.span {P} :=
        hP _ (by rw [e1]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp this
      exact ⟨0, t, by rw [← ht]; ring, by rw [zero_smul]; exact zero_mem _⟩
  choose c' t' hct hmem using hj
  refine ⟨∑ j, c' j • cst (b j), ∑ j, t' j • cst (b j), Submodule.sum_mem _ (fun j _ => hmem j), ?_⟩
  conv_lhs => rw [← sum_coordA b w]
  simp_rw [hct, add_smul, Finset.sum_add_distrib, Finset.smul_sum, mul_smul]

/- English proof (translation)
Proceed by induction on `N generalizing w with`. Consider the case `zero => simpa using h`. Consider the case `succ N ih`. Apply `ih` to reduce the goal to its premises. Apply `ext_add_sat_step ϖ hϖ V hV P hP` to reduce the goal to its premises.

Take `⟨c, z, hc, hw⟩` from `h`. Use `⟨c, z, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[← hw, smul_smul, ← map_mul, ← pow_succ']`.
-/
theorem ext_add_sat [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ)
    (V : Submodule O (Fin r → O)) (hV : Saturated ϖ V) (P : PowerSeries O)
    (hP : ∀ z, C ϖ * z ∈ Ideal.span {P} → z ∈ Ideal.span {P}) (N : ℕ)
    (w : Fin r → PowerSeries O) (h : ∃ c z, c ∈ ext V ∧ C (ϖ ^ N) • w = c + P • z) :
    ∃ c z, c ∈ ext V ∧ w = c + P • z := by
  induction N generalizing w with
  | zero => simpa using h
  | succ N ih =>
    apply ih
    apply ext_add_sat_step ϖ hϖ V hV P hP
    obtain ⟨c, z, hc, hw⟩ := h
    refine ⟨c, z, hc, ?_⟩
    rw [← hw, smul_smul, ← map_mul, ← pow_succ']

/- English proof (translation)
Take `⟨b, hb⟩` from `exists_adapted_basis U`. Establish `hj : ∀ j, ∃ u₁ ∈ U, ∃ y : O, b.repr δ j • b j = u₁ + e • (y • b j)`. Introduce `j`. Take `⟨a, ha, hab⟩` from `hb j`. Establish `e1` using `congrArg (coordA b j) hδ`.

Rewrite `e1` using `[coordA_cst, coordA_add]`. Take `⟨g, hg⟩` from `Ideal.mem_span_singleton'.mp (coordA_mem_of_ext b j U a ha u hu)`. Take `⟨x, y, hxy⟩` from `hQ a (b.repr δ j) ⟨g, coordA b j jv, coordA_mem_ideal b j J jv hjv, by rw [e1, ← hg, mul_comm]⟩`. Use `⟨x • (a • b j), U.smul_mem x hab, y, ?_⟩` and prove the remaining obligations. Rewrite using `[hxy, add_smul, smul_smul, smul_smul, mul_comm e y]`.

Use `choose u₁ hu₁ y hy using hj`. Use `⟨∑ j, u₁ j, Submodule.sum_mem _ (fun j _ => hu₁ j), ∑ j, y j • b j, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← b.sum_repr δ]`. Repeatedly rewrite using `[hy, Finset.sum_add_distrib, Finset.smul_sum]`.
-/
theorem const_mem_of_ext_add_ideal [IsPrincipalIdealRing O] (U : Submodule O (Fin r → O))
    (J : Ideal (PowerSeries O)) (e : O)
    (hQ : ∀ a c : O, (∃ g h, h ∈ J ∧ C c = C a * g + h) → ∃ x y, c = x * a + y * e)
    (δ : Fin r → O) (u : Fin r → PowerSeries O) (hu : u ∈ ext U) (jv : Fin r → PowerSeries O)
    (hjv : ∀ i, jv i ∈ J) (hδ : cst δ = u + jv) :
    ∃ u' ∈ U, ∃ w : Fin r → O, δ = u' + e • w := by
  obtain ⟨b, hb⟩ := exists_adapted_basis U
  have hj : ∀ j, ∃ u₁ ∈ U, ∃ y : O, b.repr δ j • b j = u₁ + e • (y • b j) := by
    intro j
    obtain ⟨a, ha, hab⟩ := hb j
    have e1 := congrArg (coordA b j) hδ
    rw [coordA_cst, coordA_add] at e1
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp (coordA_mem_of_ext b j U a ha u hu)
    obtain ⟨x, y, hxy⟩ := hQ a (b.repr δ j)
      ⟨g, coordA b j jv, coordA_mem_ideal b j J jv hjv, by rw [e1, ← hg, mul_comm]⟩
    refine ⟨x • (a • b j), U.smul_mem x hab, y, ?_⟩
    rw [hxy, add_smul, smul_smul, smul_smul, mul_comm e y]
  choose u₁ hu₁ y hy using hj
  refine ⟨∑ j, u₁ j, Submodule.sum_mem _ (fun j _ => hu₁ j), ∑ j, y j • b j, ?_⟩
  conv_lhs => rw [← b.sum_repr δ]
  simp_rw [hy, Finset.sum_add_distrib, Finset.smul_sum]

/- English proof (translation)
Introduce `a c ⟨g, h, hh, hc⟩`. Distinguish the cases in `c0 : c = 0`. Conclude with `⟨0, 0, by simp [c0]⟩`. Take `⟨v, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible c0 hϖ`. It suffices to establish `hv : C (ϖ ^ v) ∈ J ∨ a ∣ (u : O) * ϖ ^ v by`.

Break down `hv with hv | ⟨t, ht⟩` into its components or cases. Take `⟨t, ht⟩` from `hJ v hv`. Conclude with `⟨0, u * t, by rw [ht]; ring⟩`. Conclude with `⟨t, 0, by rw [ht]; ring⟩`. Distinguish the cases in `a0 : a = 0`.

Use `left`. Rewrite `hc` using `[a0, map_zero, zero_mul, zero_add]`. Establish `: C (ϖ ^ v) = C (↑u⁻¹ : O) * C ((u : O) * ϖ ^ v)`. Rewrite using `[← map_mul, ← mul_assoc, Units.inv_mul, one_mul]`. Rewrite using `[this, hc]`.

Conclude with `Ideal.mul_mem_left _ _ hh`. Take `⟨t, u', rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible a0 hϖ`. Distinguish the cases in `htv : t ≤ v`. Use `right`. Use `⟨↑u'⁻¹ * u * ϖ ^ (v - t), ?_⟩` and prove the remaining obligations.

Establish `: (u' : O) * ϖ ^ t * (↑u'⁻¹ * u * ϖ ^ (v - t)) = ((u' : O) * ↑u'⁻¹) * u * (ϖ ^ t * ϖ ^ (v - t))` using `by ring`. Rewrite using `[this, Units.mul_inv, one_mul, ← pow_add, Nat.add_sub_cancel' htv]`. Use `left push Not at htv`. Establish `hpt : ϖ ^ t = ϖ ^ v * ϖ ^ (t - v)` using `by rw [← pow_add]; congr 1; omega`. Use `set F : PowerSeries O := C (u : O) - C ((u' : O) * ϖ ^ (t - v)) * g with hF`.

Establish `hFeq : C (ϖ ^ v) * F = h`. Rewrite using `[hF]`. Simplify using `only [map_mul] at hc ⊢`. Rewrite `hc` using `[hpt, map_mul]`. Take the linear combination `hc`.

Establish `hϖm : ϖ ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit`. Establish `hFu : IsUnit F`. Rewrite using `[PowerSeries.isUnit_iff_constantCoeff]`. Establish `hcF : constantCoeff F = (u : O) - (u' : O) * ϖ ^ (t - v) * constantCoeff g`. Rewrite using `[hF]`.

Simplify using the standard rewrite rules. Rewrite using `[hcF]`. Assume the negation of the conclusion as `hn`. Establish `hm : (u' : O) * ϖ ^ (t - v) * constantCoeff g ∈ IsLocalRing.maximalIdeal O` using `Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hϖm _ (by omega)))`. Establish `h1` using `add_mem ((IsLocalRing.mem_maximalIdeal _).mpr hn) hm`.

Rewrite `h1` using `[sub_add_cancel]`. Conclude with `((IsLocalRing.mem_maximalIdeal _).mp h1) u.isUnit`. Take `⟨Fu, hFu⟩` from `hFu`. Establish `: C (ϖ ^ v) = h * ↑Fu⁻¹`. Rewrite using `[← hFeq, ← hFu, mul_assoc, Units.mul_inv, mul_one]`.

Rewrite using `[this]`. Conclude with `Ideal.mul_mem_right _ _ hh`.
-/
theorem const_mem_of_span_add [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ)
    (J : Ideal (PowerSeries O)) (e : O) (hJ : ∀ v : ℕ, C (ϖ ^ v) ∈ J → e ∣ ϖ ^ v) :
    ∀ a c : O, (∃ g h, h ∈ J ∧ C c = C a * g + h) → ∃ x y, c = x * a + y * e := by
  intro a c ⟨g, h, hh, hc⟩
  by_cases c0 : c = 0
  · exact ⟨0, 0, by simp [c0]⟩
  obtain ⟨v, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible c0 hϖ
  suffices hv : C (ϖ ^ v) ∈ J ∨ a ∣ (u : O) * ϖ ^ v by
    rcases hv with hv | ⟨t, ht⟩
    · obtain ⟨t, ht⟩ := hJ v hv
      exact ⟨0, u * t, by rw [ht]; ring⟩
    · exact ⟨t, 0, by rw [ht]; ring⟩
  by_cases a0 : a = 0
  · left
    rw [a0, map_zero, zero_mul, zero_add] at hc
    have : C (ϖ ^ v) = C (↑u⁻¹ : O) * C ((u : O) * ϖ ^ v) := by
      rw [← map_mul, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this, hc]
    exact Ideal.mul_mem_left _ _ hh
  obtain ⟨t, u', rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible a0 hϖ
  by_cases htv : t ≤ v
  · right
    refine ⟨↑u'⁻¹ * u * ϖ ^ (v - t), ?_⟩
    have : (u' : O) * ϖ ^ t * (↑u'⁻¹ * u * ϖ ^ (v - t)) =
        ((u' : O) * ↑u'⁻¹) * u * (ϖ ^ t * ϖ ^ (v - t)) := by ring
    rw [this, Units.mul_inv, one_mul, ← pow_add, Nat.add_sub_cancel' htv]
  · left
    push Not at htv
    have hpt : ϖ ^ t = ϖ ^ v * ϖ ^ (t - v) := by rw [← pow_add]; congr 1; omega
    set F : PowerSeries O := C (u : O) - C ((u' : O) * ϖ ^ (t - v)) * g with hF
    have hFeq : C (ϖ ^ v) * F = h := by
      rw [hF]
      simp only [map_mul] at hc ⊢
      rw [hpt, map_mul] at hc
      linear_combination hc
    have hϖm : ϖ ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
    have hFu : IsUnit F := by
      rw [PowerSeries.isUnit_iff_constantCoeff]
      have hcF : constantCoeff F = (u : O) - (u' : O) * ϖ ^ (t - v) * constantCoeff g := by
        rw [hF]; simp
      rw [hcF]
      by_contra hn
      have hm : (u' : O) * ϖ ^ (t - v) * constantCoeff g ∈ IsLocalRing.maximalIdeal O :=
        Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _
          (Ideal.pow_mem_of_mem _ hϖm _ (by omega)))
      have h1 := add_mem ((IsLocalRing.mem_maximalIdeal _).mpr hn) hm
      rw [sub_add_cancel] at h1
      exact ((IsLocalRing.mem_maximalIdeal _).mp h1) u.isUnit
    obtain ⟨Fu, hFu⟩ := hFu
    have : C (ϖ ^ v) = h * ↑Fu⁻¹ := by
      rw [← hFeq, ← hFu, mul_assoc, Units.mul_inv, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ hh

end PID

section Ideals

variable {O : Type} [CommRing O] (ϖ : O)

/- English proof (translation)
Take `⟨N, a, a', e⟩` from `h`. Conclude with `⟨N, a', a, by rw [← e]; ring⟩`.
-/
theorem coprimeRat_symm {f g : PowerSeries O} (h : CoprimeRat ϖ f g) : CoprimeRat ϖ g f := by
  obtain ⟨N, a, a', e⟩ := h
  exact ⟨N, a', a, by rw [← e]; ring⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, 0, 1, by simp⟩`.
-/
theorem coprimeRat_one_right (f : PowerSeries O) : CoprimeRat ϖ f 1 :=
  ⟨0, 0, 1, by simp⟩

/- English proof (translation)
Take `⟨N, a, a', e1⟩` from `h1`. Take `⟨M, c, c', e2⟩` from `h2`. Conclude with `⟨N + M, a * (c * f + c' * h) + a' * g * c, a' * c', by`. Rewrite using `[pow_add, map_mul, ← e1, ← e2]`. Use the proof step `ring⟩`.
-/
theorem coprimeRat_mul_right {f g h : PowerSeries O} (h1 : CoprimeRat ϖ f g)
    (h2 : CoprimeRat ϖ f h) : CoprimeRat ϖ f (g * h) := by
  obtain ⟨N, a, a', e1⟩ := h1
  obtain ⟨M, c, c', e2⟩ := h2
  exact ⟨N + M, a * (c * f + c' * h) + a' * g * c, a' * c', by
    rw [pow_add, map_mul, ← e1, ← e2]; ring⟩

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero]`. Conclude with `coprimeRat_one_right ϖ f`. Consider the case `succ k ih => rw [pow_succ]`. Conclude with `coprimeRat_mul_right ϖ ih h`.
-/
theorem coprimeRat_pow_right {f g : PowerSeries O} (h : CoprimeRat ϖ f g) (k : ℕ) :
    CoprimeRat ϖ f (g ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact coprimeRat_one_right ϖ f
  | succ k ih => rw [pow_succ]; exact coprimeRat_mul_right ϖ ih h

/- English proof (translation)
The claim follows from `coprimeRat_symm ϖ (coprimeRat_pow_right ϖ (coprimeRat_symm ϖ (coprimeRat_pow_right ϖ h m)) k)`.
-/
theorem coprimeRat_pow_pow {f g : PowerSeries O} (h : CoprimeRat ϖ f g) (k m : ℕ) :
    CoprimeRat ϖ (f ^ k) (g ^ m) :=
  coprimeRat_symm ϖ (coprimeRat_pow_right ϖ (coprimeRat_symm ϖ (coprimeRat_pow_right ϖ h m)) k)

/- English proof (translation)
The claim follows from `Finset.prod_induction _ _ (fun _ _ h1 h2 => coprimeRat_mul_right ϖ h1 h2) (coprimeRat_one_right ϖ f) h`.
-/
theorem coprimeRat_prod_right {ι : Type} (f : PowerSeries O) (T : Finset ι)
    (g : ι → PowerSeries O) (h : ∀ t ∈ T, CoprimeRat ϖ f (g t)) :
    CoprimeRat ϖ f (∏ t ∈ T, g t) :=
  Finset.prod_induction _ _ (fun _ _ h1 h2 => coprimeRat_mul_right ϖ h1 h2)
    (coprimeRat_one_right ϖ f) h

def SatSpan (f : PowerSeries O) : Prop :=
  ∀ (N : ℕ) (z : PowerSeries O), C (ϖ ^ N) * z ∈ Ideal.span {f} → z ∈ Ideal.span {f}

/- English proof (translation)
Introduce `N z _`. Rewrite using `[Ideal.span_singleton_one]`. Conclude with `Submodule.mem_top`.
-/
theorem satSpan_one : SatSpan ϖ (1 : PowerSeries O) := by
  intro N z _; rw [Ideal.span_singleton_one]; exact Submodule.mem_top

variable [IsDomain O]

/- English proof (translation)
Distinguish the cases in `f0 : f = 0`. Rewrite using `[f0, zero_mul]`. Rewrite `hf` using `[f0]`. Conclude with `hf`. Introduce `N z hz`.

Establish `hzf : z ∈ Ideal.span {f}` using `hf N z (Ideal.mem_span_singleton.mpr (dvd_trans (dvd_mul_right f g) (Ideal.mem_span_singleton.mp hz)))`. Take `⟨z', rfl⟩` from `Ideal.mem_span_singleton'.mp hzf`. Take `⟨w, hw⟩` from `Ideal.mem_span_singleton'.mp hz`. Establish `h1 : C (ϖ ^ N) * z' = w * g`. Apply `mul_right_cancel₀ f0` to reduce the goal to its premises.

Take the linear combination `-hw`. Take `⟨t, rfl⟩` from `Ideal.mem_span_singleton'.mp (hg N z' (by`. Rewrite using `[h1]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))`. Conclude with `Ideal.mem_span_singleton'.mpr ⟨t, by ring⟩`.
-/
theorem satSpan_mul {f g : PowerSeries O} (hf : SatSpan ϖ f) (hg : SatSpan ϖ g) :
    SatSpan ϖ (f * g) := by
  by_cases f0 : f = 0
  · rw [f0, zero_mul]; rw [f0] at hf; exact hf
  intro N z hz
  have hzf : z ∈ Ideal.span {f} := hf N z (Ideal.mem_span_singleton.mpr
      (dvd_trans (dvd_mul_right f g) (Ideal.mem_span_singleton.mp hz)))
  obtain ⟨z', rfl⟩ := Ideal.mem_span_singleton'.mp hzf
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hz
  have h1 : C (ϖ ^ N) * z' = w * g := by
    apply mul_right_cancel₀ f0
    linear_combination -hw
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp (hg N z' (by
    rw [h1]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
  exact Ideal.mem_span_singleton'.mpr ⟨t, by ring⟩

/- English proof (translation)
The claim follows from `Finset.prod_induction _ _ (fun _ _ h1 h2 => satSpan_mul ϖ h1 h2) (satSpan_one ϖ) h`.
-/
theorem satSpan_prod {ι : Type} (T : Finset ι) (g : ι → PowerSeries O)
    (h : ∀ t ∈ T, SatSpan ϖ (g t)) : SatSpan ϖ (∏ t ∈ T, g t) :=
  Finset.prod_induction _ _ (fun _ _ h1 h2 => satSpan_mul ϖ h1 h2) (satSpan_one ϖ) h

/- English proof (translation)
Take `⟨N, a, a', e⟩` from `hc`. Take `⟨z₁, h1⟩` from `Ideal.mem_span_singleton'.mp hf`. Take `⟨z₂, h2⟩` from `Ideal.mem_span_singleton'.mp hg`. Apply `hs N` to reduce the goal to its premises. Rewrite using `[← e]`.

Use `Ideal.mem_span_singleton'.mpr ⟨a * z₂ + a' * z₁, ?_⟩` and prove the remaining obligations. Take the linear combination `(a * f) * h2 + (a' * g) * h1`.
-/
theorem mem_span_mul_of_coprime {f g z : PowerSeries O} (hc : CoprimeRat ϖ f g)
    (hs : SatSpan ϖ (f * g)) (hf : z ∈ Ideal.span {f}) (hg : z ∈ Ideal.span {g}) :
    z ∈ Ideal.span {f * g} := by
  obtain ⟨N, a, a', e⟩ := hc
  obtain ⟨z₁, h1⟩ := Ideal.mem_span_singleton'.mp hf
  obtain ⟨z₂, h2⟩ := Ideal.mem_span_singleton'.mp hg
  apply hs N
  rw [← e]
  refine Ideal.mem_span_singleton'.mpr ⟨a * z₂ + a' * z₁, ?_⟩
  linear_combination (a * f) * h2 + (a' * g) * h1

end Ideals

section Steps

variable {O : Type} [CommRing O] [IsDomain O] {r : ℕ}

def lamAway (p : ℕ → PowerSeries O) (H : ℕ → ℕ) (ell s : ℕ) : PowerSeries O :=
  ∏ t ∈ (Finset.range ell).erase s, p t ^ H t

/- English proof (translation)
The claim follows from `(Finset.mul_prod_erase _ _ (Finset.mem_range.mpr hs)).symm`.
-/
theorem lam_split (p : ℕ → PowerSeries O) (H : ℕ → ℕ) (ell s : ℕ) (hs : s < ell) :
    abelian₂ p H ell = p s ^ H s * lamAway p H ell s :=
  (Finset.mul_prod_erase _ _ (Finset.mem_range.mpr hs)).symm

/- English proof (translation)
Consider the cases of `k with`. Consider the case `thin`. Take `⟨N, z, hz⟩` from `h`. Use `⟨N, fun i => ?_⟩` and prove the remaining obligations. Use `congrFun hz i` as an intermediate fact.

Simplify using `only [Pi.smul_apply, smul_eq_mul] at this`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`. Consider the case `up => exact absurd rfl hk`. Consider the case `down`.

Take `⟨N, c, z, -, hz⟩` from `h`. Use `⟨N, fun i => ?_⟩` and prove the remaining obligations. Use `congrFun hz i` as an intermediate fact. Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.add_apply] at this`. Rewrite using `[this, Ideal.mem_span_singleton]`.

Conclude with `⟨c i + P ^ b * z i, by rw [pow_add]; ring⟩`.
-/
theorem mem_span_of_levelCond (ϖ : O) (P : PowerSeries O) (H b : ℕ) (k : Kind)
    (hk : k ≠ Kind.up) (V : Submodule O (Fin r → O)) (w : Fin r → PowerSeries O)
    (h : LevelCond ϖ P H b k V w) : ∃ N, ∀ i, C (ϖ ^ N) * w i ∈ Ideal.span {P ^ H} := by
  cases k with
  | thin =>
    obtain ⟨N, z, hz⟩ := h
    refine ⟨N, fun i => ?_⟩
    have := congrFun hz i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  | up => exact absurd rfl hk
  | down =>
    obtain ⟨N, c, z, -, hz⟩ := h
    refine ⟨N, fun i => ?_⟩
    have := congrFun hz i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply] at this
    rw [this, Ideal.mem_span_singleton]
    exact ⟨c i + P ^ b * z i, by rw [pow_add]; ring⟩

/- English proof (translation)
Take `⟨N, c, z, hc, hz⟩` from `h`. Establish `h2 : Λ' • (C (ϖ ^ N) • (C (ϖ ^ k) • x - cst d)) = c + P ^ b • z`. Use function extensionality and compare the values at `i`. Use `congrFun hz i` as an intermediate fact. Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply, cst] at this ⊢`.

Apply `mul_left_cancel₀ (pow_ne_zero H hP)` to reduce the goal to its premises. Rewrite `this` using `[pow_add]`. Take the linear combination `this`. Take `⟨M, a, a', hM⟩` from `hcop`. Use `⟨M + N, a • c, a • z + a' • (C (ϖ ^ N) • (C (ϖ ^ k) • x - cst d)), Submodule.smul_mem _ _ hc, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Use `congrFun h2 i` as an intermediate fact. Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply, cst] at this ⊢`. Rewrite using `[pow_add, map_mul (C : O →+* PowerSeries O)]`. Take the linear combination `a * this - (C (ϖ ^ N) * (C (ϖ ^ k) * x i - C (d i))) * hM`.
-/
theorem down_reduce (ϖ : O) (P Λ' : PowerSeries O) (H b : ℕ) (V : Submodule O (Fin r → O))
    (hP : P ≠ 0) (hcop : CoprimeRat ϖ Λ' (P ^ b)) (x : Fin r → PowerSeries O) (d : Fin r → O)
    (k : ℕ)
    (h : LevelCond ϖ P H b Kind.down V (C (ϖ ^ k) • ((P ^ H * Λ') • x) - (P ^ H * Λ') • cst d)) :
    ∃ N c z, c ∈ ext V ∧ C (ϖ ^ N) • (C (ϖ ^ k) • x - cst d) = c + P ^ b • z := by
  obtain ⟨N, c, z, hc, hz⟩ := h
  have h2 : Λ' • (C (ϖ ^ N) • (C (ϖ ^ k) • x - cst d)) = c + P ^ b • z := by
    funext i
    have := congrFun hz i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply, cst] at this ⊢
    apply mul_left_cancel₀ (pow_ne_zero H hP)
    rw [pow_add] at this
    linear_combination this
  obtain ⟨M, a, a', hM⟩ := hcop
  refine ⟨M + N, a • c, a • z + a' • (C (ϖ ^ N) • (C (ϖ ^ k) • x - cst d)),
    Submodule.smul_mem _ _ hc, ?_⟩
  funext i
  have := congrFun h2 i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply, cst] at this ⊢
  rw [pow_add, map_mul (C : O →+* PowerSeries O)]
  linear_combination a * this - (C (ϖ ^ N) * (C (ϖ ^ k) * x i - C (d i))) * hM

/- English proof (translation)
Break down `Nat.eq_zero_or_pos b with hb | hb` into its components or cases. Use `⟨0, 0, x, zero_mem _, ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Simplify using `[cst, hb]`. Take `⟨b', rfl⟩ : ∃ b', b = b' + 1` from `⟨b - 1, by omega⟩`.

Establish `hPs : ∀ z, C ϖ * z ∈ Ideal.span {P ^ (b' + 1)} → z ∈ Ideal.span {P ^ (b' + 1)}` using `fun z hz => mem_span_pow_of_uniformizer_mul O ϖ hϖ D P hP (b' + 1) 1 z (by rwa [pow_one])`. Take `⟨N, h⟩` from `h`. Take `⟨c, z, hc, hz⟩` from `ext_add_sat ϖ hϖ V hV (P ^ (b' + 1)) hPs N _ h`. Establish `hQ` using `const_mem_of_span_add ϖ hϖ (Ideal.span {C (ϖ ^ k), P ^ (b' + 1)}) (ϖ ^ k) (fun v hv => by`. Take `⟨g, w, hgw⟩` from `Ideal.mem_span_pair.mp hv`.

Use `pow_dvd_of_const_mem_span O ϖ hϖ D P hP hD (ϖ ^ v) k 0 g ?_` and prove the remaining obligations. Rewrite using `[pow_zero, map_one, one_mul, Ideal.mem_span_singleton]`. Conclude with `⟨w * P ^ b', by rw [← hgw, pow_succ]; ring⟩)`. Take `⟨u', hu', w', hδ⟩` from `const_mem_of_ext_add_ideal V _ (ϖ ^ k) hQ d (-c) (neg_mem hc) (C (ϖ ^ k) • x - P ^ (b' + 1) • z) (fun i => Ideal.mem_span_pair.mpr ⟨x i, -z i, by`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`.

Use the proof step `ring⟩)`. Use the proof step `(by`. Use function extensionality and compare the values at `i`. Use `congrFun hz i` as an intermediate fact. Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, cst] at this ⊢`.

Take the linear combination `(-1 : PowerSeries O) * this)`. Use `⟨w', ?_⟩` and prove the remaining obligations. Apply `ext_add_sat ϖ hϖ V hV (P ^ (b' + 1)) hPs k` to reduce the goal to its premises. Use `⟨c + cst u', z, add_mem hc (cst_mem_ext V u' hu'), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Establish `h1` using `congrFun hz i`. Establish `h2` using `congrArg C (congrFun hδ i)`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul] at h2`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply, cst] at h1 ⊢`. Rewrite `h1` using `[h2]`.

Take the linear combination `h1`.
-/
theorem const_reduce [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (D : ℕ)
    (P : PowerSeries O) (hP : UnitDist ϖ D P) (hD : 1 ≤ D) (b : ℕ)
    (V : Submodule O (Fin r → O)) (hV : Saturated ϖ V) (x : Fin r → PowerSeries O)
    (d : Fin r → O) (k : ℕ)
    (h : ∃ N c z, c ∈ ext V ∧ C (ϖ ^ N) • (C (ϖ ^ k) • x - cst d) = c + P ^ b • z) :
    ∃ lam c z, c ∈ ext V ∧ x - cst lam = c + P ^ b • z := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · refine ⟨0, 0, x, zero_mem _, ?_⟩
    ext i; simp [cst, hb]
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have hPs : ∀ z, C ϖ * z ∈ Ideal.span {P ^ (b' + 1)} → z ∈ Ideal.span {P ^ (b' + 1)} :=
    fun z hz => mem_span_pow_of_uniformizer_mul O ϖ hϖ D P hP (b' + 1) 1 z (by rwa [pow_one])
  obtain ⟨N, h⟩ := h
  obtain ⟨c, z, hc, hz⟩ := ext_add_sat ϖ hϖ V hV (P ^ (b' + 1)) hPs N _ h
  have hQ := const_mem_of_span_add ϖ hϖ (Ideal.span {C (ϖ ^ k), P ^ (b' + 1)}) (ϖ ^ k)
    (fun v hv => by
      obtain ⟨g, w, hgw⟩ := Ideal.mem_span_pair.mp hv
      refine pow_dvd_of_const_mem_span O ϖ hϖ D P hP hD (ϖ ^ v) k 0 g ?_
      rw [pow_zero, map_one, one_mul, Ideal.mem_span_singleton]
      exact ⟨w * P ^ b', by rw [← hgw, pow_succ]; ring⟩)
  obtain ⟨u', hu', w', hδ⟩ := const_mem_of_ext_add_ideal V _ (ϖ ^ k) hQ d (-c) (neg_mem hc)
    (C (ϖ ^ k) • x - P ^ (b' + 1) • z)
    (fun i => Ideal.mem_span_pair.mpr ⟨x i, -z i, by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring⟩)
    (by
      funext i
      have := congrFun hz i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, cst] at this ⊢
      linear_combination (-1 : PowerSeries O) * this)
  refine ⟨w', ?_⟩
  apply ext_add_sat ϖ hϖ V hV (P ^ (b' + 1)) hPs k
  refine ⟨c + cst u', z, add_mem hc (cst_mem_ext V u' hu'), ?_⟩
  funext i
  have h1 := congrFun hz i
  have h2 := congrArg C (congrFun hδ i)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul] at h2
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply, cst] at h1 ⊢
  rw [h2] at h1
  linear_combination h1

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono h)`.
-/
theorem ext_mono {V W : Submodule O (Fin r → O)} (h : V ≤ W) : ext V ≤ ext W :=
  Submodule.span_mono (Set.image_mono h)

/- English proof (translation)
Establish `hQ` using `const_mem_of_span_add ϖ hϖ (Ideal.span {P₁ ^ b₁, P₀ ^ b₀}) (ϖ ^ ρ) (fun v hv => pow_dvd_pow ϖ (hρmin v hv))`. Take `⟨u', hu', lam', hδ⟩` from `const_mem_of_ext_add_ideal (V₀ ⊔ V₁) _ (ϖ ^ ρ) hQ (l₀ - l₁) (c₁ - c₀) (sub_mem (ext_mono le_sup_right hc₁) (ext_mono le_sup_left hc₀)) (P₁ ^ b₁ • z₁ - P₀ ^ b₀ • z₀) (fun i => Ideal.mem_span_pair.mpr ⟨z₁ i, -z₀ i, by`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Use the proof step `ring⟩)`. Use the proof step `(by`.

Use function extensionality and compare the values at `i`. Establish `e0` using `congrFun h₀ i`. Establish `e1` using `congrFun h₁ i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply, cst, map_sub] at e0 e1 ⊢`. Take the linear combination `e1 - e0)`.

Take `⟨v₀, hv₀, v₁, hv₁, rfl⟩` from `Submodule.mem_sup.mp hu'`. Take `⟨g, hg⟩` from `Ideal.mem_span_singleton'.mp hf1`. Take `⟨h, hh⟩` from `Ideal.mem_span_singleton'.mp hf0`. Use `⟨l₁ + v₁, lam', x - cst (l₁ + v₁) - fρ • cst lam', by abel, ⟨c₀ + cst v₀, z₀ - h • cst lam', add_mem hc₀ (cst_mem_ext _ _ hv₀), ?_⟩, ⟨c₁ - cst v₁, z₁ - g • cst lam', sub_mem hc₁ (cst_mem_ext _ _ hv₁), ?_⟩⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Establish `e0` using `congrFun h₀ i`. Establish `hC` using `congrArg C (congrFun hδ i)`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add, map_sub, map_mul] at hC`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply, cst, map_add] at e0 ⊢`. Take the linear combination `e0 + hC + C (lam' i) * hh`.

Use function extensionality and compare the values at `i`. Establish `e1` using `congrFun h₁ i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply, cst, map_add] at e1 ⊢`. Take the linear combination `e1 + C (lam' i) * hg`.
-/
theorem two_const_reduce [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ)
    (P₀ P₁ : PowerSeries O) (b₀ b₁ : ℕ) (V₀ V₁ : Submodule O (Fin r → O)) (ρ : ℕ)
    (fρ : PowerSeries O)
    (hρmin : ∀ k : ℕ, C (ϖ ^ k) ∈ Ideal.span {P₁ ^ b₁, P₀ ^ b₀} → ρ ≤ k)
    (hf1 : fρ ∈ Ideal.span {P₁ ^ b₁}) (hf0 : fρ - C (ϖ ^ ρ) ∈ Ideal.span {P₀ ^ b₀})
    (x : Fin r → PowerSeries O) (l₀ l₁ : Fin r → O) (c₀ z₀ c₁ z₁ : Fin r → PowerSeries O)
    (hc₀ : c₀ ∈ ext V₀) (hc₁ : c₁ ∈ ext V₁) (h₀ : x - cst l₀ = c₀ + P₀ ^ b₀ • z₀)
    (h₁ : x - cst l₁ = c₁ + P₁ ^ b₁ • z₁) :
    ∃ (lam lam' : Fin r → O) (μ : Fin r → PowerSeries O), x = cst lam + fρ • cst lam' + μ ∧
      (∃ c z, c ∈ ext V₀ ∧ μ = c + P₀ ^ b₀ • z) ∧ (∃ c z, c ∈ ext V₁ ∧ μ = c + P₁ ^ b₁ • z) := by
  have hQ := const_mem_of_span_add ϖ hϖ (Ideal.span {P₁ ^ b₁, P₀ ^ b₀}) (ϖ ^ ρ)
    (fun v hv => pow_dvd_pow ϖ (hρmin v hv))
  obtain ⟨u', hu', lam', hδ⟩ := const_mem_of_ext_add_ideal (V₀ ⊔ V₁) _ (ϖ ^ ρ) hQ (l₀ - l₁)
    (c₁ - c₀) (sub_mem (ext_mono le_sup_right hc₁) (ext_mono le_sup_left hc₀))
    (P₁ ^ b₁ • z₁ - P₀ ^ b₀ • z₀)
    (fun i => Ideal.mem_span_pair.mpr ⟨z₁ i, -z₀ i, by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring⟩)
    (by
      funext i
      have e0 := congrFun h₀ i
      have e1 := congrFun h₁ i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply, cst, map_sub] at e0 e1 ⊢
      linear_combination e1 - e0)
  obtain ⟨v₀, hv₀, v₁, hv₁, rfl⟩ := Submodule.mem_sup.mp hu'
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp hf1
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.mp hf0
  refine ⟨l₁ + v₁, lam', x - cst (l₁ + v₁) - fρ • cst lam', by abel,
    ⟨c₀ + cst v₀, z₀ - h • cst lam', add_mem hc₀ (cst_mem_ext _ _ hv₀), ?_⟩,
    ⟨c₁ - cst v₁, z₁ - g • cst lam', sub_mem hc₁ (cst_mem_ext _ _ hv₁), ?_⟩⟩
  · funext i
    have e0 := congrFun h₀ i
    have hC := congrArg C (congrFun hδ i)
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add, map_sub,
      map_mul] at hC
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply, cst, map_add] at e0 ⊢
    linear_combination e0 + hC + C (lam' i) * hh
  · funext i
    have e1 := congrFun h₁ i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply, cst, map_add] at e1 ⊢
    linear_combination e1 + C (lam' i) * hg

end Steps

end TwoDown

open TwoDown PowerSeries

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ ℓ ell r p H b kind V hℓ hPS hsat _hub s₀ s₁ h01 h1 hk1 hk0 hthin ρ fρ _hρ hρmin hf1 hf0 y`. Establish `: (Ideal.span {ϖ}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible hϖ`. Establish `hs0 : s₀ < ell` using `by omega`. Establish `hUD : ∀ s < ell, UnitDist ϖ (ℓ ^ s) (p s)` using `hPS.1`. Establish `hp0 : ∀ s < ell, p s ≠ 0` using `fun s hs h0 => map_ne_zero_of_unitDist ϖ _ (p s) (hUD s hs) (by rw [h0, map_zero])`.

Establish `hdeg : ∀ s, 1 ≤ ℓ ^ s` using `fun s => Nat.one_le_pow _ _ (by omega)`. Establish `hcopΛ : ∀ s < ell, ∀ k, CoprimeRat ϖ (lamAway p H ell s) (p s ^ k)`. Introduce `s hs k`. Apply `coprimeRat_symm` to reduce the goal to its premises. Apply `coprimeRat_prod_right` to reduce the goal to its premises.

Introduce `t ht`. Take `⟨hts, htl⟩` from `Finset.mem_erase.mp ht`. Conclude with `coprimeRat_pow_pow ϖ (hPS.2 s hs t (Finset.mem_range.mp htl) (Ne.symm hts)) k (H t)`. Prove the components needed by the constructor for the conclusion. Introduce `hII`.

Establish `hstep1 : ∀ s < ell, ∀ i, y i ∈ Ideal.span {p s ^ H s}`. Introduce `s hs i`. Take `⟨d, k, hL⟩` from `hII s hs`. Establish `hk : kind s ≠ Kind.up`. Distinguish the cases in `e1 : s = s₁`.

Rewrite using `[e1, hk1]`. Evaluate the decidable proposition. Distinguish the cases in `e0 : s = s₀`. Rewrite using `[e0, hk0]`. Evaluate the decidable proposition.

Rewrite using `[hthin s hs e0 e1]`. Evaluate the decidable proposition. Take `⟨N, hN⟩` from `mem_span_of_levelCond ϖ (p s) (H s) (b s) (kind s) hk (V s) _ hL`. Establish `h2` using `hN i`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cst] at h2`.

Establish `hΛ : abelian₂ p H ell * C (d i) ∈ Ideal.span {p s ^ H s}`. Rewrite using `[lam_split p H ell s hs, mul_assoc]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`. Establish `h3` using `add_mem h2 (Ideal.mul_mem_left _ (C (ϖ ^ N)) hΛ)`. Establish `h4 : C (ϖ ^ (N + k)) * y i ∈ Ideal.span {p s ^ H s}`.

Rewrite using `[pow_add, map_mul (C : O →+* PowerSeries O)]`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Conclude with `mem_span_pow_of_uniformizer_mul O ϖ hϖ _ (p s) (hUD s hs) (H s) (N + k) (y i) h4`. Establish `hstep2 : ∀ i, y i ∈ Ideal.span {abelian₂ p H ell}`.

Introduce `i`. Establish `key : ∀ T ⊆ Finset.range ell, y i ∈ Ideal.span {∏ t ∈ T, p t ^ H t}`. Introduce `T`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => intro _`.

Simplify using the standard rewrite rules. Consider the case `@insert s T hsT ih`. Introduce `hT`. Rewrite using `[Finset.prod_insert hsT]`. Establish `hs : s < ell` using `Finset.mem_range.mp (hT (Finset.mem_insert_self _ _))`.

Establish `hT' : T ⊆ Finset.range ell` using `(Finset.subset_insert _ _).trans hT`. Apply `mem_span_mul_of_coprime ϖ` to reduce the goal to its premises. Apply `coprimeRat_prod_right` to reduce the goal to its premises. Introduce `t ht`. Establish `hst : s ≠ t` using `fun e => hsT (e ▸ ht)`.

Conclude with `coprimeRat_pow_pow ϖ (hPS.2 s hs t (Finset.mem_range.mp (hT' ht)) hst) _ _`. Apply `satSpan_mul ϖ` to reduce the goal to its premises. Conclude with `mem_span_pow_of_uniformizer_mul O ϖ hϖ _ (p s) (hUD s hs) (H s)`. Apply `satSpan_prod` to reduce the goal to its premises. Introduce `t ht`.

Conclude with `mem_span_pow_of_uniformizer_mul O ϖ hϖ _ (p t) (hUD t (Finset.mem_range.mp (hT' ht))) (H t)`. Conclude with `hstep1 s hs i`. Conclude with `ih hT'`. Conclude with `key _ subset_rfl`. Use `choose x hx using fun i => Ideal.mem_span_singleton'.mp (hstep2 i)`.

Establish `hy : y = abelian₂ p H ell • x`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← hx i, mul_comm]`. Establish `hdown : ∀ s, s < ell → kind s = Kind.down → ∃ lam c z, c ∈ ext (V s) ∧ x - cst lam = c + p s ^ b s • z`.

Introduce `s hs hks`. Take `⟨d, k, hL⟩` from `hII s hs`. Rewrite `hL` using `[hks, hy, lam_split p H ell s hs]`. Conclude with `const_reduce ϖ hϖ (ℓ ^ s) (p s) (hUD s hs) (hdeg s) (b s) (V s) (hsat s hs) x d k (down_reduce ϖ (p s) (lamAway p H ell s) (H s) (b s) (V s) (hp0 s hs) (hcopΛ s hs (b s)) x d k hL)`. Take `⟨l₁, c₁, z₁, hc₁, e₁⟩` from `hdown s₁ h1 hk1`.

Take `⟨l₀, c₀, z₀, hc₀, e₀⟩` from `hdown s₀ hs0 hk0`. Take `⟨lam, lam', μ, hxμ, ⟨c₀', z₀', hc₀', hμ₀⟩, ⟨c₁', z₁', hc₁', hμ₁⟩⟩` from `two_const_reduce ϖ hϖ (p s₀) (p s₁) (b s₀) (b s₁) (V s₀) (V s₁) ρ fρ hρmin hf1 hf0 x l₀ l₁ c₀ z₀ c₁ z₁ hc₀ hc₁ e₀ e₁`. Use `⟨lam, lam', abelian₂ p H ell • μ, ?_, ?_⟩` and prove the remaining obligations. Introduce `s hs`. Distinguish the cases in `es1 : s = s₁`.

Rewrite using `[es1, hk1]`. Use `⟨0, lamAway p H ell s₁ • c₁', lamAway p H ell s₁ • z₁', Submodule.smul_mem _ _ hc₁', ?_⟩` and prove the remaining obligations. Rewrite using `[hμ₁, lam_split p H ell s₁ h1]`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, pow_zero, map_one, one_mul]`.

Rewrite using `[pow_add]`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `es0 : s = s₀`. Rewrite using `[es0, hk0]`. Use `⟨0, lamAway p H ell s₀ • c₀', lamAway p H ell s₀ • z₀', Submodule.smul_mem _ _ hc₀', ?_⟩` and prove the remaining obligations.

Rewrite using `[hμ₀, lam_split p H ell s₀ hs0]`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, pow_zero, map_one, one_mul]`. Rewrite using `[pow_add]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hthin s hs es0 es1]`. Use `⟨0, lamAway p H ell s • μ, ?_⟩` and prove the remaining obligations. Rewrite using `[lam_split p H ell s hs]`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, pow_zero, map_one, one_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hy, hxμ]`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.

Introduce and unpack `⟨lam, lam', ν, hν, rfl⟩ s hs`. Distinguish the cases in `es1 : s = s₁`. Rewrite using `[es1]`. Use `⟨lam, 0, ?_⟩` and prove the remaining obligations. Establish `hc` using `hν s₁ h1`.

Rewrite `hc`, the goal using `[hk1]`. Take `⟨N, c, z, hc, hz⟩` from `hc`. Take `⟨g, hg⟩` from `Ideal.mem_span_singleton'.mp hf1`. Use `⟨N, c, z + C (ϖ ^ N) • ((lamAway p H ell s₁ * g) • cst lam'), hc, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Establish `e` using `congrFun hz i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply, cst, pow_zero, map_one, one_mul] at e ⊢`. Rewrite using `[lam_split p H ell s₁ h1, ← hg, pow_add]`. Rewrite `e` using `[pow_add]`. Take the linear combination `e`.

Distinguish the cases in `es0 : s = s₀`. Rewrite using `[es0]`. Use `⟨lam + ϖ ^ ρ • lam', 0, ?_⟩` and prove the remaining obligations. Establish `hc` using `hν s₀ hs0`. Rewrite `hc`, the goal using `[hk0]`.

Take `⟨N, c, z, hc, hz⟩` from `hc`. Take `⟨h, hh⟩` from `Ideal.mem_span_singleton'.mp hf0`. Use `⟨N, c, z + C (ϖ ^ N) • ((lamAway p H ell s₀ * h) • cst lam'), hc, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Establish `e` using `congrFun hz i`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply, cst, pow_zero, map_one, one_mul, map_add, map_mul] at e ⊢`. Rewrite using `[lam_split p H ell s₀ hs0, pow_add]`. Rewrite `e` using `[pow_add]`. Take the linear combination `e - (C (ϖ ^ N) * p s₀ ^ H s₀ * lamAway p H ell s₀ * C (lam' i)) * hh`. Rewrite using `[hthin s hs es0 es1]`.

Use `⟨lam, 0, ?_⟩` and prove the remaining obligations. Establish `hc` using `hν s hs`. Rewrite `hc` using `[hthin s hs es0 es1]`. Take `⟨N, z, hz⟩` from `hc`. Use `⟨N, z + C (ϖ ^ N) • ((lamAway p H ell s * fρ) • cst lam'), ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Establish `e` using `congrFun hz i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply, cst, pow_zero, map_one, one_mul] at e ⊢`. Rewrite using `[lam_split p H ell s hs]`. Take the linear combination `e`.
-/
theorem levels_mod_const_iff_of_down_down : MDD := by
  intro O _ _ _ ϖ hϖ ℓ ell r p H b kind V hℓ hPS hsat _hub s₀ s₁ h01 h1 hk1 hk0 hthin ρ fρ
    _hρ hρmin hf1 hf0 y
  have : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  have hs0 : s₀ < ell := by omega
  have hUD : ∀ s < ell, UnitDist ϖ (ℓ ^ s) (p s) := hPS.1
  have hp0 : ∀ s < ell, p s ≠ 0 := fun s hs h0 =>
    map_ne_zero_of_unitDist ϖ _ (p s) (hUD s hs) (by rw [h0, map_zero])
  have hdeg : ∀ s, 1 ≤ ℓ ^ s := fun s => Nat.one_le_pow _ _ (by omega)
  have hcopΛ : ∀ s < ell, ∀ k, CoprimeRat ϖ (lamAway p H ell s) (p s ^ k) := by
    intro s hs k
    apply coprimeRat_symm
    apply coprimeRat_prod_right
    intro t ht
    obtain ⟨hts, htl⟩ := Finset.mem_erase.mp ht
    exact coprimeRat_pow_pow ϖ (hPS.2 s hs t (Finset.mem_range.mp htl) (Ne.symm hts)) k (H t)
  constructor
  · intro hII

    have hstep1 : ∀ s < ell, ∀ i, y i ∈ Ideal.span {p s ^ H s} := by
      intro s hs i
      obtain ⟨d, k, hL⟩ := hII s hs
      have hk : kind s ≠ Kind.up := by
        by_cases e1 : s = s₁
        · rw [e1, hk1]; decide
        by_cases e0 : s = s₀
        · rw [e0, hk0]; decide
        rw [hthin s hs e0 e1]; decide
      obtain ⟨N, hN⟩ := mem_span_of_levelCond ϖ (p s) (H s) (b s) (kind s) hk (V s) _ hL
      have h2 := hN i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cst] at h2
      have hΛ : abelian₂ p H ell * C (d i) ∈ Ideal.span {p s ^ H s} := by
        rw [lam_split p H ell s hs, mul_assoc]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
      have h3 := add_mem h2 (Ideal.mul_mem_left _ (C (ϖ ^ N)) hΛ)
      have h4 : C (ϖ ^ (N + k)) * y i ∈ Ideal.span {p s ^ H s} := by
        rw [pow_add, map_mul (C : O →+* PowerSeries O)]
        convert h3 using 1
        ring
      exact mem_span_pow_of_uniformizer_mul O ϖ hϖ _ (p s) (hUD s hs) (H s) (N + k) (y i) h4

    have hstep2 : ∀ i, y i ∈ Ideal.span {abelian₂ p H ell} := by
      intro i
      have key : ∀ T ⊆ Finset.range ell, y i ∈ Ideal.span {∏ t ∈ T, p t ^ H t} := by
        intro T
        induction T using Finset.induction_on with
        | empty => intro _; simp
        | @insert s T hsT ih =>
          intro hT
          rw [Finset.prod_insert hsT]
          have hs : s < ell := Finset.mem_range.mp (hT (Finset.mem_insert_self _ _))
          have hT' : T ⊆ Finset.range ell := (Finset.subset_insert _ _).trans hT
          apply mem_span_mul_of_coprime ϖ
          · apply coprimeRat_prod_right
            intro t ht
            have hst : s ≠ t := fun e => hsT (e ▸ ht)
            exact coprimeRat_pow_pow ϖ (hPS.2 s hs t (Finset.mem_range.mp (hT' ht)) hst) _ _
          · apply satSpan_mul ϖ
            · exact mem_span_pow_of_uniformizer_mul O ϖ hϖ _ (p s) (hUD s hs) (H s)
            · apply satSpan_prod
              intro t ht
              exact mem_span_pow_of_uniformizer_mul O ϖ hϖ _ (p t) (hUD t (Finset.mem_range.mp (hT' ht))) (H t)
          · exact hstep1 s hs i
          · exact ih hT'
      exact key _ subset_rfl
    choose x hx using fun i => Ideal.mem_span_singleton'.mp (hstep2 i)
    have hy : y = abelian₂ p H ell • x := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← hx i, mul_comm]

    have hdown : ∀ s, s < ell → kind s = Kind.down →
        ∃ lam c z, c ∈ ext (V s) ∧ x - cst lam = c + p s ^ b s • z := by
      intro s hs hks
      obtain ⟨d, k, hL⟩ := hII s hs
      rw [hks, hy, lam_split p H ell s hs] at hL
      exact const_reduce ϖ hϖ (ℓ ^ s) (p s) (hUD s hs) (hdeg s) (b s) (V s) (hsat s hs) x d k
        (down_reduce ϖ (p s) (lamAway p H ell s) (H s) (b s) (V s) (hp0 s hs)
          (hcopΛ s hs (b s)) x d k hL)
    obtain ⟨l₁, c₁, z₁, hc₁, e₁⟩ := hdown s₁ h1 hk1
    obtain ⟨l₀, c₀, z₀, hc₀, e₀⟩ := hdown s₀ hs0 hk0
    obtain ⟨lam, lam', μ, hxμ, ⟨c₀', z₀', hc₀', hμ₀⟩, ⟨c₁', z₁', hc₁', hμ₁⟩⟩ :=
      two_const_reduce ϖ hϖ (p s₀) (p s₁) (b s₀) (b s₁) (V s₀) (V s₁) ρ fρ hρmin hf1 hf0 x
        l₀ l₁ c₀ z₀ c₁ z₁ hc₀ hc₁ e₀ e₁
    refine ⟨lam, lam', abelian₂ p H ell • μ, ?_, ?_⟩
    · intro s hs
      by_cases es1 : s = s₁
      · rw [es1, hk1]
        refine ⟨0, lamAway p H ell s₁ • c₁', lamAway p H ell s₁ • z₁',
          Submodule.smul_mem _ _ hc₁', ?_⟩
        rw [hμ₁, lam_split p H ell s₁ h1]
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, pow_zero, map_one, one_mul]
        rw [pow_add]
        ring
      by_cases es0 : s = s₀
      · rw [es0, hk0]
        refine ⟨0, lamAway p H ell s₀ • c₀', lamAway p H ell s₀ • z₀',
          Submodule.smul_mem _ _ hc₀', ?_⟩
        rw [hμ₀, lam_split p H ell s₀ hs0]
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, pow_zero, map_one, one_mul]
        rw [pow_add]
        ring
      rw [hthin s hs es0 es1]
      refine ⟨0, lamAway p H ell s • μ, ?_⟩
      rw [lam_split p H ell s hs]
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, pow_zero, map_one, one_mul]
      ring
    · rw [hy, hxμ]
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply]
      ring
  · rintro ⟨lam, lam', ν, hν, rfl⟩ s hs
    by_cases es1 : s = s₁
    · rw [es1]
      refine ⟨lam, 0, ?_⟩
      have hc := hν s₁ h1
      rw [hk1] at hc ⊢
      obtain ⟨N, c, z, hc, hz⟩ := hc
      obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp hf1
      refine ⟨N, c, z + C (ϖ ^ N) • ((lamAway p H ell s₁ * g) • cst lam'), hc, ?_⟩
      funext i
      have e := congrFun hz i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply, cst, pow_zero, map_one,
        one_mul] at e ⊢
      rw [lam_split p H ell s₁ h1, ← hg, pow_add]
      rw [pow_add] at e
      linear_combination e
    by_cases es0 : s = s₀
    · rw [es0]
      refine ⟨lam + ϖ ^ ρ • lam', 0, ?_⟩
      have hc := hν s₀ hs0
      rw [hk0] at hc ⊢
      obtain ⟨N, c, z, hc, hz⟩ := hc
      obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.mp hf0
      refine ⟨N, c, z + C (ϖ ^ N) • ((lamAway p H ell s₀ * h) • cst lam'), hc, ?_⟩
      funext i
      have e := congrFun hz i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply, cst, pow_zero, map_one,
        one_mul, map_add, map_mul] at e ⊢
      rw [lam_split p H ell s₀ hs0, pow_add]
      rw [pow_add] at e
      linear_combination e - (C (ϖ ^ N) * p s₀ ^ H s₀ * lamAway p H ell s₀ * C (lam' i)) * hh
    rw [hthin s hs es0 es1]
    refine ⟨lam, 0, ?_⟩
    have hc := hν s hs
    rw [hthin s hs es0 es1] at hc
    obtain ⟨N, z, hz⟩ := hc
    refine ⟨N, z + C (ϖ ^ N) • ((lamAway p H ell s * fρ) • cst lam'), ?_⟩
    funext i
    have e := congrFun hz i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply, cst, pow_zero, map_one,
      one_mul] at e ⊢
    rw [lam_split p H ell s hs]
    linear_combination e

end Formalism.ExponentWindows

import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Rewrite `hK` using `[Ne, Submodule.zero_eq_bot]`. Establish `hne : ({J : Ideal R | ∃ j : ℕ, A ^ j * J ≤ K}).Nonempty` using `⟨K, 0, by simp⟩`. Take `⟨J, ⟨j, hj⟩, hmax⟩` from `set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian R R) _ hne`. Use `⟨j, J, hj, ?_⟩` and prove the remaining obligations. Establish `hKJ : K ≤ J`.

Assume the negation of the conclusion as `h`. Use `hmax (J ⊔ K) ⟨j, ?_⟩ (lt_of_le_of_ne le_sup_left ?_)` and prove the remaining obligations. Rewrite using `[Ideal.mul_sup]`. Conclude with `sup_le hj (Ideal.mul_le_inf.trans inf_le_right)`. Introduce `e`.

Conclude with `h (le_sup_right.trans e.symm.le)`. Establish `hJ0 : J ≠ 0`. Rewrite using `[Ne, Submodule.zero_eq_bot]`. Introduce and unpack `rfl`. Conclude with `hK (le_bot_iff.mp hKJ)`.

Assume the negation of the conclusion as `hne'`. Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal _ hne'`. Establish `hJP : J ≤ P` using `le_trans le_sup_right hle`. Establish `hAP : A ≤ P` using `le_trans le_sup_left hle`. Take `⟨Q, hQ⟩` from `Ideal.dvd_iff_le.mpr hJP`.

Establish `hQmem : A ^ (j + 1) * Q ≤ K`. Combine the equalities or inequalities in the displayed calculation. Establish `hJQ : J ≤ Q`. Rewrite using `[hQ]`. Conclude with `(Ideal.mul_le_inf.trans inf_le_right)`.

Establish `hQJ : Q = J`. Assume the negation of the conclusion as `h`. Conclude with `hmax Q ⟨j + 1, hQmem⟩ (lt_of_le_of_ne hJQ (Ne.symm h))`. Rewrite `hQ` using `[hQJ]`. Conclude with `hP.ne_top (mul_right_cancel₀ hJ0 (hQ.symm.trans (Ideal.top_mul J).symm))`.
-/
theorem exists_pow_mul_coprime_le {R : Type} [CommRing R] [IsDedekindDomain R] (A K : Ideal R) (hK : K ≠ 0) :
    ∃ (j : ℕ) (J : Ideal R), A ^ j * J ≤ K ∧ A ⊔ J = ⊤ := by
  classical
  rw [Ne, Submodule.zero_eq_bot] at hK
  have hne : ({J : Ideal R | ∃ j : ℕ, A ^ j * J ≤ K}).Nonempty := ⟨K, 0, by simp⟩
  obtain ⟨J, ⟨j, hj⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian R R) _ hne
  refine ⟨j, J, hj, ?_⟩

  have hKJ : K ≤ J := by
    by_contra h
    refine hmax (J ⊔ K) ⟨j, ?_⟩ (lt_of_le_of_ne le_sup_left ?_)
    · rw [Ideal.mul_sup]
      exact sup_le hj (Ideal.mul_le_inf.trans inf_le_right)
    · intro e
      exact h (le_sup_right.trans e.symm.le)
  have hJ0 : J ≠ 0 := by
    rw [Ne, Submodule.zero_eq_bot]
    rintro rfl
    exact hK (le_bot_iff.mp hKJ)

  by_contra hne'
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne'
  have hJP : J ≤ P := le_trans le_sup_right hle
  have hAP : A ≤ P := le_trans le_sup_left hle
  obtain ⟨Q, hQ⟩ := Ideal.dvd_iff_le.mpr hJP
  have hQmem : A ^ (j + 1) * Q ≤ K :=
    calc A ^ (j + 1) * Q = A ^ j * (A * Q) := by rw [pow_succ, _root_.mul_assoc]
      _ ≤ A ^ j * (P * Q) := Ideal.mul_mono_right (Ideal.mul_mono_left hAP)
      _ = A ^ j * J := by rw [hQ]
      _ ≤ K := hj
  have hJQ : J ≤ Q := by
    rw [hQ]
    exact (Ideal.mul_le_inf.trans inf_le_right)
  have hQJ : Q = J := by
    by_contra h
    exact hmax Q ⟨j + 1, hQmem⟩ (lt_of_le_of_ne hJQ (Ne.symm h))
  rw [hQJ] at hQ

  exact hP.ne_top (mul_right_cancel₀ hJ0 (hQ.symm.trans (Ideal.top_mul J).symm))

/- English proof (translation)
Unfold `KilledBy at ht`. Establish `h0 : Xo.univ.t.act.act 0 = 1`. Establish `h` using `Xo.univ.t.act.add 0 0`. Rewrite `h` using `[add_zero]`. Establish `h'` using `congrArg (fun f => f * (Xo.univ.t.act.act 0)⁻¹) h`.

Simplify using `using h'.symm`. Establish `hnat : ∀ (n : ℕ) (y : 𝓞 E), Xo.univ.t.act.act ((n : 𝓞 E) * y) = Xo.univ.t.act.act y ^ n`. Introduce `n y`. Proceed by induction on `n with`. Consider the case `zero => simp [h0]`.

Consider the case `succ n ih => rw [Nat.cast_succ, add_mul, _root_.one_mul, Xo.univ.t.act.add, ih, pow_succ]`. Introduce `x hx`. Use `Submodule.mul_induction_on hx ?_ ?_` and prove the remaining obligations. Introduce `m hm b hb`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hm`.

Use `Xo.univ.t.act.hom b` as an intermediate fact. Use `Xo.univ.t.act.hom c` as an intermediate fact. Establish `e : c * (N : 𝓞 E) * b = (N : 𝓞 E) * b * c` using `by ring`. Rewrite using `[e, Xo.univ.t.act.mul, hnat, ← Category.assoc, MonObj.comp_pow, ← MonObj.pow_comp, hw, ht b hb, MonObj.one_comp]`. Introduce `y z hy hz`.

Rewrite using `[Xo.univ.t.act.add, MonObj.comp_mul, hy, hz, _root_.one_mul]`.
-/
private theorem comp_act_eq_one_of_pow_eq_killed {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) {T : Over Xo.X} (t w : T ⟶ Xo.univ.t.G) (N : ℕ)
    (ht : KilledBy Xo l.Mb t) (hw : w ^ N = t) :
    ∀ x ∈ Ideal.span {(N : 𝓞 E)} * l.Mb, w ≫ Xo.univ.t.act.act x = 1 := by
  unfold KilledBy at ht
  have h0 : Xo.univ.t.act.act 0 = 1 := by
    have h := Xo.univ.t.act.add 0 0
    rw [add_zero] at h
    have h' := congrArg (fun f => f * (Xo.univ.t.act.act 0)⁻¹) h
    simpa using h'.symm

  have hnat : ∀ (n : ℕ) (y : 𝓞 E), Xo.univ.t.act.act ((n : 𝓞 E) * y) = Xo.univ.t.act.act y ^ n := by
    intro n y
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [Nat.cast_succ, add_mul, _root_.one_mul, Xo.univ.t.act.add, ih, pow_succ]
  intro x hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro m hm b hb
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hm
    have := Xo.univ.t.act.hom b
    have := Xo.univ.t.act.hom c
    have e : c * (N : 𝓞 E) * b = (N : 𝓞 E) * b * c := by ring
    rw [e, Xo.univ.t.act.mul, hnat, ← Category.assoc, MonObj.comp_pow, ← MonObj.pow_comp, hw, ht b hb,
      MonObj.one_comp]
  · intro y z hy hz
    rw [Xo.univ.t.act.add, MonObj.comp_mul, hy, hz, _root_.one_mul]

/- English proof (translation)
Take `⟨i, hi, j, hj, hij⟩` from `Submodule.mem_sup.mp (hIJ ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ I ⊔ J)`. Establish `ht'` using `ht`. Unfold `KilledBy at ht'`. Use `⟨w ≫ Xo.univ.t.act.act j, ?_, ?_⟩` and prove the remaining obligations. Use `Xo.univ.t.act.hom j` as an intermediate fact.

Rewrite using `[← MonObj.pow_comp, hw]`. Establish `h1 : t ≫ Xo.univ.t.act.act i = 1` using `ht' i (hI hi)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1, _root_.one_mul]`. Use `_ = t ≫ Xo.univ.t.act.act (i + j) := by rw [Xo.univ.t.act.add, MonObj.comp_mul]`.

Use `_ = t := by rw [hij, Xo.univ.t.act.one, Category.comp_id]`. Unfold `KilledBy`. Introduce `a ha`. Rewrite using `[Category.assoc, ← Xo.univ.t.act.mul]`. Conclude with `comp_act_eq_one_of_pow_eq_killed Xo t w N ht hw _ (hle (_root_.mul_comm a j ▸ Ideal.mul_mem_mul ha hj))`.
-/
theorem exists_root_killedBy {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) {T : Over Xo.X} (t w : T ⟶ Xo.univ.t.G) (N : ℕ)
    (ht : KilledBy Xo l.Mb t) (hw : w ^ N = t) (I J : Ideal (𝓞 E)) (hI : I ≤ l.Mb) (hIJ : I ⊔ J = ⊤)
    (hle : I * J ≤ Ideal.span {(N : 𝓞 E)} * l.Mb) :
    ∃ t' : T ⟶ Xo.univ.t.G, t' ^ N = t ∧ KilledBy Xo I t' := by
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp (hIJ ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ I ⊔ J)
  have ht' := ht
  unfold KilledBy at ht'
  refine ⟨w ≫ Xo.univ.t.act.act j, ?_, ?_⟩
  · have := Xo.univ.t.act.hom j
    rw [← MonObj.pow_comp, hw]
    have h1 : t ≫ Xo.univ.t.act.act i = 1 := ht' i (hI hi)
    calc t ≫ Xo.univ.t.act.act j = (t ≫ Xo.univ.t.act.act i) * (t ≫ Xo.univ.t.act.act j) := by
          rw [h1, _root_.one_mul]
      _ = t ≫ Xo.univ.t.act.act (i + j) := by rw [Xo.univ.t.act.add, MonObj.comp_mul]
      _ = t := by rw [hij, Xo.univ.t.act.one, Category.comp_id]
  · unfold KilledBy
    intro a ha
    rw [Category.assoc, ← Xo.univ.t.act.mul]
    exact comp_act_eq_one_of_pow_eq_killed Xo t w N ht hw _ (hle (_root_.mul_comm a j ▸ Ideal.mul_mem_mul ha hj))

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo T t w N hN ht hw`. Establish `hMb0 : l.Mb ≠ 0`. Introduce `h`. Establish `hp` using `l.prod`. Rewrite `hp` using `[h, zero_mul, Submodule.zero_eq_bot, eq_comm, Ideal.span_singleton_eq_bot]`.

Establish `hM : l.M = 0` using `by exact_mod_cast hp`. Use `l.three_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hN0 : Ideal.span {(N : 𝓞 E)} ≠ 0`. Rewrite using `[Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]`.

Conclude with `hN.ne'` after adjusting the coercions. Take `⟨j, J, hj, hcop⟩` from `exists_pow_mul_coprime_le l.Mb _ (mul_ne_zero hN0 hMb0)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨t', ht'N, ht'⟩` from `exists_root_killedBy Xo t w N ht hw (l.Mb ^ (j + 1)) J (Ideal.pow_le_self (Nat.succ_ne_zero j)) (Ideal.pow_sup_eq_top hcop) (by rw [pow_succ', _root_.mul_assoc]; exact (Ideal.mul_le_inf.trans inf_le_right).trans hj)`. Conclude with `⟨t', ht'N, j + 1, ht'⟩`.

Introduce `hNM`. Use `exists_root_killedBy Xo t w N ht hw (l.Mb ^ 2) (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) (Ideal.pow_le_self two_ne_zero) (Ideal.pow_sup_eq_top l.coprime) (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[sq, _root_.mul_assoc, l.prod, _root_.mul_comm, hNM]`.
-/
theorem exists_root_killedBy_pow :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : Over Xo.X) (t w : T ⟶ Xo.univ.t.G) (N : ℕ), 0 < N → KilledBy Xo l.Mb t → w ^ N = t → (∃ t' : T ⟶ Xo.univ.t.G, t' ^ N = t ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) t') ∧ (N = l.M → ∃ t' : T ⟶ Xo.univ.t.G, t' ^ N = t ∧ KilledBy Xo (l.Mb ^ 2) t') := by
  intro E _ _ _ H Dw l Xo T t w N hN ht hw
  have hMb0 : l.Mb ≠ 0 := by
    intro h
    have hp := l.prod
    rw [h, zero_mul, Submodule.zero_eq_bot, eq_comm, Ideal.span_singleton_eq_bot] at hp
    have hM : l.M = 0 := by exact_mod_cast hp
    have := l.three_le
    omega
  have hN0 : Ideal.span {(N : 𝓞 E)} ≠ 0 := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  obtain ⟨j, J, hj, hcop⟩ := exists_pow_mul_coprime_le l.Mb _ (mul_ne_zero hN0 hMb0)
  refine ⟨?_, ?_⟩
  · obtain ⟨t', ht'N, ht'⟩ := exists_root_killedBy Xo t w N ht hw (l.Mb ^ (j + 1)) J
      (Ideal.pow_le_self (Nat.succ_ne_zero j)) (Ideal.pow_sup_eq_top hcop)
      (by rw [pow_succ', _root_.mul_assoc]; exact (Ideal.mul_le_inf.trans inf_le_right).trans hj)
    exact ⟨t', ht'N, j + 1, ht'⟩
  · intro hNM
    refine exists_root_killedBy Xo t w N ht hw (l.Mb ^ 2) (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
      (Ideal.pow_le_self two_ne_zero) (Ideal.pow_sup_eq_top l.coprime) (le_of_eq ?_)
    rw [sq, _root_.mul_assoc, l.prod, _root_.mul_comm, hNM]

end GlobalTheory

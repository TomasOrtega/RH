import Formalism.HermitianCurvature.StatementJ

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J

open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.Jx10

/- English proof (translation)
Unfold `Formalism.FourierDecayAlt.A5.IsPSD at h ⊢`. Introduce `a`. Use `show (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (η x) (η y)).im = 0 ∧ 0 ≤ (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (η x) (η y)).re`. Use `set b : X → ℂ := fun u => ∑ z ∈ F.filter (fun z => η z = u), a z with hb`. Establish `hmaps : ∀ x ∈ F, η x ∈ F.image η` using `fun x hx => Finset.mem_image_of_mem η hx`.

Establish `rhs : ∀ u v, b u * conj (b v) * k u v = ∑ x ∈ F.filter (fun z => η z = u), ∑ y ∈ F.filter (fun z => η z = v), a x * conj (a y) * k (η x) (η y)`. Introduce `u v`. Simplify using `only [hb]`. Rewrite using `[map_sum, Finset.sum_mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl (fun x hx => ?_)` and prove the remaining obligations.

Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl (fun y hy => ?_)` and prove the remaining obligations. Establish `h1` using `(Finset.mem_filter.mp hx).2`. Establish `h2` using `(Finset.mem_filter.mp hy).2`. Apply the tactic sequence `rw [h1, h2] <;> ring`.

Establish `key : (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (η x) (η y)) = ∑ u ∈ F.image η, ∑ v ∈ F.image η, b u * conj (b v) * k u v`. Repeatedly rewrite using `[rhs]`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to hmaps]`. Use `Finset.sum_congr rfl (fun u _ => ?_)` and prove the remaining obligations. Use `conv_rhs => rw [Finset.sum_comm]`.

Use `Finset.sum_congr rfl (fun x _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_fiberwise_of_maps_to hmaps]`. Rewrite using `[key]`. Conclude with `h b`.
-/
theorem pull {α X : Type} [DecidableEq X] (η : α → X) (F : Finset α) (k : X → X → ℂ)
    (h : A5.IsPSD (F.image η) k) : A5.IsPSD F (fun x y => k (η x) (η y)) := by
  unfold Formalism.FourierDecayAlt.A5.IsPSD at h ⊢
  intro a
  show (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (η x) (η y)).im = 0 ∧
    0 ≤ (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (η x) (η y)).re
  set b : X → ℂ := fun u => ∑ z ∈ F.filter (fun z => η z = u), a z with hb
  have hmaps : ∀ x ∈ F, η x ∈ F.image η := fun x hx => Finset.mem_image_of_mem η hx
  have rhs : ∀ u v, b u * conj (b v) * k u v =
      ∑ x ∈ F.filter (fun z => η z = u), ∑ y ∈ F.filter (fun z => η z = v),
        a x * conj (a y) * k (η x) (η y) := by
    intro u v
    simp only [hb]
    rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    have h1 := (Finset.mem_filter.mp hx).2
    have h2 := (Finset.mem_filter.mp hy).2
    rw [h1, h2] <;> ring
  have key : (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (η x) (η y)) =
      ∑ u ∈ F.image η, ∑ v ∈ F.image η, b u * conj (b v) * k u v := by
    simp_rw [rhs]
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_fiberwise_of_maps_to hmaps]
  rw [key]
  exact h b

/- English proof (translation)
Assume the negation of the conclusion as `ht`. Set `I : Ideal (𝓞 (maximalRealSubfield E))` to `{ carrier := {a | algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L} add_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq, map_add, add_mul] at ha hb ⊢`. Conclude with `L.add_mem ha hb`. Use the proof step `zero_mem' := by simp`.

Use the proof step `smul_mem' := fun c {a} ha => by`. Simplify using `only [Set.mem_setOf_eq, smul_eq_mul, map_mul, mul_assoc] at ha ⊢`. Conclude with `hL c _ ha }`. Establish `hI : I ≠ ⊤`. Introduce `hI`.

Apply `ht` to reduce the goal to its premises. Establish `h1 : (1 : 𝓞 (maximalRealSubfield E)) ∈ I`. Rewrite using `[hI]`. Conclude with `Submodule.mem_top`. Establish `h2 : algebraMap (𝓞 (maximalRealSubfield E)) E 1 * t ∈ L` using `h1`.

Simplify using `using h2`. Take `⟨P, hP, hIP⟩` from `Ideal.exists_le_maximal I hI`. Take `⟨a, haP, haL⟩` from `h P hP`. Conclude with `haP (hIP haL)`.
-/
theorem inter_of_module (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule ℤ E)
    (hL : ∀ (a : 𝓞 (maximalRealSubfield E)) (t : E), t ∈ L →
      algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L) (t : E)
    (h : ∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsMaximal → t ∈ S6.locAt E P L) : t ∈ L := by
  by_contra ht
  let I : Ideal (𝓞 (maximalRealSubfield E)) :=
    { carrier := {a | algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add, add_mul] at ha hb ⊢
        exact L.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun c {a} ha => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, mul_assoc] at ha ⊢
        exact hL c _ ha }
  have hI : I ≠ ⊤ := by
    intro hI
    apply ht
    have h1 : (1 : 𝓞 (maximalRealSubfield E)) ∈ I := by
      rw [hI]
      exact Submodule.mem_top
    have h2 : algebraMap (𝓞 (maximalRealSubfield E)) E 1 * t ∈ L := h1
    simpa using h2
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨a, haP, haL⟩ := h P hP
  exact haP (hIP haL)

end Formalism.FourierDecayAlt.P.Jx10

namespace Formalism.FourierDecayAlt.P

open Classical in

/- English proof (translation)
Introduce `hag hgram K _ _ _ R ψ hLD α η Y`. Rewrite using `[(hag α Y _).1, ← (hag α Y _).2]`. Conclude with `Jx10.pull η Y (A5.Kp R ψ) (hgram K R ψ hLD (Y.image η))`.
-/
theorem local_kernel_psd : Formalism.FourierDecayAlt.J.LocalKernelPSD := by
  intro hag hgram K _ _ _ R ψ hLD α η Y
  rw [(hag α Y _).1, ← (hag α Y _).2]
  exact Jx10.pull η Y (A5.Kp R ψ) (hgram K R ψ hLD (Y.image η))

/- English proof (translation)
Introduce `E _ _ _ L hL t`. Take `⟨hL1, -⟩` from `hL`. Prove the components needed by the constructor for the conclusion. Introduce `ht P hP`. Unfold `Formalism.FourierDecayAlt.S6.locAt`.

Rewrite using `[Set.mem_setOf_eq]`. Use `⟨1, fun h1 => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1), ?_⟩` and prove the remaining obligations. Rewrite using `[map_one, one_mul]`. Conclude with `ht`. Introduce `h`.

Conclude with `Jx10.inter_of_module E L hL1 t h`.
-/
theorem intersection_of_local : Formalism.FourierDecayAlt.J.IntersectionOfLocal := by
  intro E _ _ _ L hL t
  obtain ⟨hL1, -⟩ := hL
  constructor
  · intro ht P hP
    unfold Formalism.FourierDecayAlt.S6.locAt
    rw [Set.mem_setOf_eq]
    refine ⟨1, fun h1 => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1), ?_⟩
    rw [map_one, one_mul]
    exact ht
  · intro h
    exact Jx10.inter_of_module E L hL1 t h

/- English proof (translation)
Introduce `E _ _ _ L hL Q _ pl M hcov hM`. Establish `hint` using `intersection_of_local E L hL`. Use extensionality with `t`. Rewrite using `[AddSubgroup.mem_iInf, Submodule.mem_toAddSubgroup, hint]`. Prove the components needed by the constructor for the conclusion.

Introduce `h p`. Rewrite using `[hM]`. Introduce `P _ hP`. Conclude with `h P hP`. Introduce `h P hP`.

Take `⟨p, hp⟩` from `hcov P hP`. Conclude with `(hM p t).mp (h p) P hp hP`.
-/
theorem lattice_of_local : Formalism.FourierDecayAlt.J.LatticeOfLocal := by
  intro E _ _ _ L hL Q _ pl M hcov hM
  have hint := intersection_of_local E L hL
  ext t
  rw [AddSubgroup.mem_iInf, Submodule.mem_toAddSubgroup, hint]
  constructor
  · intro h p
    rw [hM]
    intro P _ hP
    exact h P hP
  · intro h P hP
    obtain ⟨p, hp⟩ := hcov P hP
    exact (hM p t).mp (h p) P hp hP

/- English proof (translation)
Introduce `hT E _ _ _ g ν s hg hpd P hP hgP K _ o σ hσ R u α ψ η Θ hR hu t`. Rewrite using `[hT E g ν s hg hpd P hP hgP K o σ hσ t]`. Use `show (u : K × K) * (σ.prod (σ.comp (IsCMField.complexConj E).toAlgHom.toRingHom)) t ∈ R ↔ _`. Rewrite using `[hR, hu]`. Establish `e : (((g : K)⁻¹, (-1) ^ s * (g : K)⁻¹) : K × K) * (σ.prod (σ.comp (IsCMField.complexConj E).toAlgHom.toRingHom)) t = (σ t / (g : K), (-1) ^ s * σ (IsCMField.complexConj E t) / (g : K))`.

Use `ext`. Simplify using `[div_eq_mul_inv, mul_comm]`. Simplify using `[div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.
-/
theorem pull_lattice_typed : Formalism.FourierDecayAlt.J.PullLatticeTyped := by
  intro hT E _ _ _ g ν s hg hpd P hP hgP K _ o σ hσ R u α ψ η Θ hR hu t
  rw [hT E g ν s hg hpd P hP hgP K o σ hσ t]
  show (u : K × K) * (σ.prod (σ.comp (IsCMField.complexConj E).toAlgHom.toRingHom)) t ∈ R ↔ _
  rw [hR, hu]
  have e : (((g : K)⁻¹, (-1) ^ s * (g : K)⁻¹) : K × K) *
      (σ.prod (σ.comp (IsCMField.complexConj E).toAlgHom.toRingHom)) t =
      (σ t / (g : K), (-1) ^ s * σ (IsCMField.complexConj E t) / (g : K)) := by
    ext
    · simp [div_eq_mul_inv, mul_comm]
    · simp [div_eq_mul_inv]; ring
  rw [e]

/- English proof (translation)
Introduce `f K l x X M hl hx h`. Establish `hprod : (∏ v, min 1 ((x v / l v) ^ K)) = ∏ v ∈ univ.filter (fun v => x v < l v), (x v / l v) ^ K`. Rewrite using `[Finset.prod_filter]`. Use `Finset.prod_congr rfl (fun v _ => ?_)` and prove the remaining obligations. Use `split_ifs with hv`.

Apply `min_eq_right` to reduce the goal to its premises. Conclude with `pow_le_one₀ (div_nonneg (hx v) (hl v).le) ((div_lt_one (hl v)).mpr hv).le`. Apply `min_eq_left` to reduce the goal to its premises. Apply `one_le_pow₀` to reduce the goal to its premises. Rewrite using `[one_le_div (hl v)]`.

Conclude with `not_lt.mp hv`. Establish `hPl : 0 < ∏ v ∈ univ.filter (fun v => x v < l v), l v ^ K` using `Finset.prod_pos (fun v _ => pow_pos (hl v) K)`. Rewrite using `[hprod]`. Simplify using `only [div_pow]`. Rewrite using `[Finset.prod_div_distrib, div_mul_eq_mul_div, le_div_iff₀ hPl, mul_comm X]`.

Conclude with `h _`.
-/
theorem minimum_shape : Formalism.FourierDecayAlt.J.MinShape := by
  intro f K l x X M hl hx h
  have hprod : (∏ v, min 1 ((x v / l v) ^ K)) =
      ∏ v ∈ univ.filter (fun v => x v < l v), (x v / l v) ^ K := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    split_ifs with hv
    · apply min_eq_right
      exact pow_le_one₀ (div_nonneg (hx v) (hl v).le) ((div_lt_one (hl v)).mpr hv).le
    · apply min_eq_left
      apply one_le_pow₀
      rw [one_le_div (hl v)]
      exact not_lt.mp hv
  have hPl : 0 < ∏ v ∈ univ.filter (fun v => x v < l v), l v ^ K :=
    Finset.prod_pos (fun v _ => pow_pos (hl v) K)
  rw [hprod]
  simp only [div_pow]
  rw [Finset.prod_div_distrib, div_mul_eq_mul_div, le_div_iff₀ hPl, mul_comm X]
  exact h _

/- English proof (translation)
Introduce `L f d pl sa al bt κ len lv be X B Mx hκ hlen hba hsa h1 h2`. Establish `hc : κ ^ (1 - (d : ℤ)) * κ ^ d = κ`. Rewrite using `[← zpow_natCast, ← zpow_add₀ hκ.ne']`. Simplify using the standard rewrite rules. Use `set c := κ ^ (1 - (d : ℤ)) with hcdef`.

Establish `hcpos : 0 < c` using `zpow_pos hκ _`. Establish `e1 : ∏ a, sa a = c ^ L * ∏ a, lv (pl a)`. Simplify using `only [hsa, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Establish `e2 : ∏ a, (1 / 2 : ℝ) * (4 / (bt a - al a)) ^ d = ∏ a : Fin L, (1 / 2 : ℝ) * (4 / len) ^ d`. Simplify using `only [hba]`.

Establish `e3 : ∏ a, κ * be (pl a) = c ^ L * (κ ^ d) ^ L * ∏ a, be (pl a)`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_pow, hc]`. Establish `e4 : ∏ a, (1 / 2 : ℝ) * be (pl a) * (4 * κ / len) ^ d = (∏ a : Fin L, (1 / 2 : ℝ) * (4 / len) ^ d) * (κ ^ d) ^ L * ∏ a, be (pl a)`. Establish `hterm : ∀ a : Fin L, (1 / 2 : ℝ) * be (pl a) * (4 * κ / len) ^ d = ((1 / 2 : ℝ) * (4 / len) ^ d) * κ ^ d * be (pl a)`. Introduce `a`.

Rewrite using `[show 4 * κ / len = (4 / len) * κ by ring, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.prod_congr rfl (fun a _ => hterm a), Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const (κ ^ d), Finset.card_univ, Fintype.card_fin]`. Rewrite `h1` using `[e2, e1]`. Rewrite `h2` using `[e3]`.

Rewrite using `[e4]`. Establish `hPh : 0 ≤ ∏ a : Fin L, (1 / 2 : ℝ) * (4 / len) ^ d` using `Finset.prod_nonneg (fun a _ => by positivity)`. Establish `hcL : 0 < c ^ L` using `pow_pos hcpos L`. Establish `key : c ^ L * ((∏ a, lv (pl a)) * X) ≤ c ^ L * ((∏ a : Fin L, (1 / 2 : ℝ) * (4 / len) ^ d) * (κ ^ d) ^ L * (∏ a, be (pl a)) * Mx)`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `le_of_mul_le_mul_left key hcL`.
-/
theorem chebyshev_to_threshold : Formalism.FourierDecayAlt.J.ChebToThreshold := by
  intro L f d pl sa al bt κ len lv be X B Mx hκ hlen hba hsa h1 h2
  have hc : κ ^ (1 - (d : ℤ)) * κ ^ d = κ := by
    rw [← zpow_natCast, ← zpow_add₀ hκ.ne']
    simp
  set c := κ ^ (1 - (d : ℤ)) with hcdef
  have hcpos : 0 < c := zpow_pos hκ _
  have e1 : ∏ a, sa a = c ^ L * ∏ a, lv (pl a) := by
    simp only [hsa, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have e2 : ∏ a, (1 / 2 : ℝ) * (4 / (bt a - al a)) ^ d = ∏ a : Fin L, (1 / 2 : ℝ) * (4 / len) ^ d := by
    simp only [hba]
  have e3 : ∏ a, κ * be (pl a) = c ^ L * (κ ^ d) ^ L * ∏ a, be (pl a) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_pow, hc]
  have e4 : ∏ a, (1 / 2 : ℝ) * be (pl a) * (4 * κ / len) ^ d =
      (∏ a : Fin L, (1 / 2 : ℝ) * (4 / len) ^ d) * (κ ^ d) ^ L * ∏ a, be (pl a) := by
    have hterm : ∀ a : Fin L, (1 / 2 : ℝ) * be (pl a) * (4 * κ / len) ^ d =
        ((1 / 2 : ℝ) * (4 / len) ^ d) * κ ^ d * be (pl a) := by
      intro a
      rw [show 4 * κ / len = (4 / len) * κ by ring, mul_pow]
      ring
    rw [Finset.prod_congr rfl (fun a _ => hterm a), Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_const (κ ^ d), Finset.card_univ, Fintype.card_fin]
  rw [e2, e1] at h1
  rw [e3] at h2
  rw [e4]
  have hPh : 0 ≤ ∏ a : Fin L, (1 / 2 : ℝ) * (4 / len) ^ d :=
    Finset.prod_nonneg (fun a _ => by positivity)
  have hcL : 0 < c ^ L := pow_pos hcpos L
  have key : c ^ L * ((∏ a, lv (pl a)) * X) ≤
      c ^ L * ((∏ a : Fin L, (1 / 2 : ℝ) * (4 / len) ^ d) * (κ ^ d) ^ L * (∏ a, be (pl a)) * Mx) := by
    calc c ^ L * ((∏ a, lv (pl a)) * X) = c ^ L * (∏ a, lv (pl a)) * X := by ring
      _ ≤ (∏ a : Fin L, (1 / 2 : ℝ) * (4 / len) ^ d) * B := h1
      _ ≤ (∏ a : Fin L, (1 / 2 : ℝ) * (4 / len) ^ d) *
            ((c ^ L * (κ ^ d) ^ L * ∏ a, be (pl a)) * Mx) := mul_le_mul_of_nonneg_left h2 hPh
      _ = _ := by ring
  exact le_of_mul_le_mul_left key hcL

/- English proof (translation)
Introduce `m i s C c c₂ κ N I A hκ hN hI hA hc hc₂ h4 h2`. Unfold `Formalism.FourierDecayAlt.Sz.lamThreshold`. Establish `hW : 0 ≤ (κ ^ (m - 1))⁻¹ * A` using `mul_nonneg (inv_nonneg.mpr (pow_nonneg hκ.le _)) hA`. Establish `hb : 4 * κ / (I / (c * N)) = 4 * c * (κ * N / I)`. Rewrite using `[div_div_eq_mul_div]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hb0 : 0 ≤ 4 * κ / (I / (c * N))` using `by positivity`. Establish `hbase : 4 * κ / (I / (c * N)) ≤ C * κ * N / I`. Rewrite using `[hb, show C * κ * N / I = C * (κ * N / I) by ring]`. Conclude with `mul_le_mul_of_nonneg_right h4 (by positivity)`.

Establish `hpow` using `pow_le_pow_left₀ hb0 hbase (2 * (i - 1) + s - 1)`. Establish `hfront : (1 / 2) * (c₂ * ((κ ^ (m - 1))⁻¹ * A)) ≤ C * ((κ ^ (m - 1))⁻¹ * A)`. Rewrite using `[← mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_right (by linarith) hW`. Conclude with `mul_le_mul hfront hpow (pow_nonneg hb0 _) (mul_nonneg (by linarith) hW)`.
-/
theorem threshold_below : Formalism.FourierDecayAlt.J.ThresholdBelow := by
  intro m i s C c c₂ κ N I A hκ hN hI hA hc hc₂ h4 h2
  unfold Formalism.FourierDecayAlt.Sz.lamThreshold
  have hW : 0 ≤ (κ ^ (m - 1))⁻¹ * A := mul_nonneg (inv_nonneg.mpr (pow_nonneg hκ.le _)) hA
  have hb : 4 * κ / (I / (c * N)) = 4 * c * (κ * N / I) := by
    rw [div_div_eq_mul_div]
    ring
  have hb0 : 0 ≤ 4 * κ / (I / (c * N)) := by positivity
  have hbase : 4 * κ / (I / (c * N)) ≤ C * κ * N / I := by
    rw [hb, show C * κ * N / I = C * (κ * N / I) by ring]
    exact mul_le_mul_of_nonneg_right h4 (by positivity)
  have hpow := pow_le_pow_left₀ hb0 hbase (2 * (i - 1) + s - 1)
  have hfront : (1 / 2) * (c₂ * ((κ ^ (m - 1))⁻¹ * A)) ≤ C * ((κ ^ (m - 1))⁻¹ * A) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) hW
  exact mul_le_mul hfront hpow (pow_nonneg hb0 _) (mul_nonneg (by linarith) hW)

end Formalism.FourierDecayAlt.P

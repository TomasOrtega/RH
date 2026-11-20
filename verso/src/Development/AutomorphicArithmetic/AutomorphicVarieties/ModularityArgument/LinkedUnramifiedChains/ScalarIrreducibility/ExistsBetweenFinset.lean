import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.NormLeOneOfInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IsInternalCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ArtinRees
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CoB

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

/- English proof (translation)
Use `letI dec : DirectSum.Decomposition gr := h1.chooseDecomposition`. Use `letI : GradedRing gr := { h2, dec with }`. Set `f : ∀ j, gr j →+ K` to `fun j => { toFun := fun a => u ^ j * ξ a.1 map_zero' := by simp map_add' := fun a b => by simp [mul_add] }`. Set `e : (DirectSum ℤ fun j => gr j) →+* K` to `DirectSum.toSemiring f (by show u ^ (0 : ℤ) * ξ 1 = 1; simp) (fun {i j} a b => by show u ^ (i + j) * ξ (a.1 * b.1) = (u ^ i * ξ a.1) * (u ^ j * ξ b.1)`. Rewrite using `[zpow_add₀ hu, map_mul]`.

Use the proof step `ring)`. Set `φ : A →+* K` to `e.comp (DirectSum.decomposeRingEquiv gr).toRingHom`. Establish `key : ∀ j, ∀ a ∈ gr j, φ a = u ^ j * ξ a` using `fun j a ha => by show e (DirectSum.decompose gr a) = _`. Establish `: DirectSum.decompose gr a = DirectSum.of (fun j => gr j) j ⟨a, ha⟩` using `DirectSum.decompose_of_mem gr ha`. Rewrite using `[this]`.

Conclude with `DirectSum.toSemiring_of _ _ _ _ _`. Use `⟨{ φ with commutes' := fun c => ?_ }, key⟩` and prove the remaining obligations. Use `show φ _ = _`. Rewrite using `[key 0 _ (h0 c), zpow_zero, one_mul, AlgHom.commutes]`.
-/
private theorem twist {O B A K : Type} [CommRing O] [CommRing B] [CommRing A] [Field K] [Algebra O A] [Algebra O K]
    [Algebra B A] (gr : ℤ → Submodule B A) (h1 : DirectSum.IsInternal gr) (h2 : SetLike.GradedMonoid gr)
    (h0 : ∀ c : O, algebraMap O A c ∈ gr 0) (ξ : A →ₐ[O] K) (u : K) (hu : u ≠ 0) :
    ∃ ξ' : A →ₐ[O] K, ∀ j, ∀ a ∈ gr j, ξ' a = u ^ j * ξ a := by
  classical
  letI dec : DirectSum.Decomposition gr := h1.chooseDecomposition
  letI : GradedRing gr := { h2, dec with }
  let f : ∀ j, gr j →+ K := fun j =>
    { toFun := fun a => u ^ j * ξ a.1
      map_zero' := by simp
      map_add' := fun a b => by simp [mul_add] }
  let e : (DirectSum ℤ fun j => gr j) →+* K := DirectSum.toSemiring f
    (by show u ^ (0 : ℤ) * ξ 1 = 1; simp)
    (fun {i j} a b => by
      show u ^ (i + j) * ξ (a.1 * b.1) = (u ^ i * ξ a.1) * (u ^ j * ξ b.1)
      rw [zpow_add₀ hu, map_mul]; ring)
  let φ : A →+* K := e.comp (DirectSum.decomposeRingEquiv gr).toRingHom
  have key : ∀ j, ∀ a ∈ gr j, φ a = u ^ j * ξ a := fun j a ha => by
    show e (DirectSum.decompose gr a) = _
    have : DirectSum.decompose gr a = DirectSum.of (fun j => gr j) j ⟨a, ha⟩ :=
      DirectSum.decompose_of_mem gr ha
    rw [this]
    exact DirectSum.toSemiring_of _ _ _ _ _
  refine ⟨{ φ with commutes' := fun c => ?_ }, key⟩
  show φ _ = _
  rw [key 0 _ (h0 c), zpow_zero, one_mul, AlgHom.commutes]

/- English proof (translation)
Establish `hx0 : x ≠ 0`. Introduce `h0`. Rewrite `hx` using `[h0, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc : 0 < Real.log ‖x‖` using `Real.log_pos hx`.

Take `⟨q, hq1, hq2⟩` from `exists_rat_btwn (div_lt_div_of_pos_right h hc)`. Take `⟨u, hu⟩` from `IsAlgClosed.exists_pow_nat_eq (x ^ q.num) q.den_pos`. Establish `hu0 : u ≠ 0`. Introduce and unpack `rfl`. Rewrite `hu` using `[zero_pow q.den_pos.ne']`.

Conclude with `zpow_ne_zero _ hx0 hu.symm`. Establish `hlog : Real.log ‖u‖ = (q : ℝ) * Real.log ‖x‖`. Establish `e` using `congrArg (fun z => Real.log ‖z‖) hu`. Simplify using `only [norm_pow, norm_zpow, Real.log_pow, Real.log_zpow] at e`. Establish `hd : (0 : ℝ) < q.den` using `by exact_mod_cast q.den_pos`.

Rewrite using `[Rat.cast_def]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `e`. Use `⟨u, hu0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hlog]`.

Rewrite `hq1` using `[div_lt_iff₀ hc]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hlog]`. Rewrite `hq2` using `[lt_div_iff₀ hc]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem exists_log_norm {K : Type} [NormedField K] [IsAlgClosed K] (x : K) (hx : 1 < ‖x‖) {α β : ℝ}
    (h : α < β) : ∃ u : K, u ≠ 0 ∧ α < Real.log ‖u‖ ∧ Real.log ‖u‖ < β := by
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hx
    linarith
  have hc : 0 < Real.log ‖x‖ := Real.log_pos hx
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (div_lt_div_of_pos_right h hc)
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (x ^ q.num) q.den_pos
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [zero_pow q.den_pos.ne'] at hu
    exact zpow_ne_zero _ hx0 hu.symm
  have hlog : Real.log ‖u‖ = (q : ℝ) * Real.log ‖x‖ := by
    have e := congrArg (fun z => Real.log ‖z‖) hu
    simp only [norm_pow, norm_zpow, Real.log_pow, Real.log_zpow] at e
    have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    rw [Rat.cast_def]
    field_simp
    linear_combination e
  refine ⟨u, hu0, ?_, ?_⟩
  · rw [hlog]
    rw [div_lt_iff₀ hc] at hq1
    linarith
  · rw [hlog]
    rw [lt_div_iff₀ hc] at hq2
    linarith

/- English proof (translation)
Break down `L.eq_empty_or_nonempty with rfl | hL` into its components or cases. Break down `U.eq_empty_or_nonempty with rfl | hU` into its components or cases. Conclude with `⟨0, 1, one_pos, by simp, by simp⟩`. Conclude with `⟨U.min' hU - 1, U.min' hU, by linarith, by simp, fun y hy => U.min'_le y hy⟩`. Break down `U.eq_empty_or_nonempty with rfl | hU` into its components or cases.

Conclude with `⟨L.max' hL, L.max' hL + 1, by linarith, fun x hx => L.le_max' x hx, by simp⟩`. Conclude with `⟨L.max' hL, U.min' hU, h _ (L.max'_mem hL) _ (U.min'_mem hU), fun x hx => L.le_max' x hx, fun y hy => U.min'_le y hy⟩`.
-/
private theorem exists_between_finset (L U : Finset ℝ) (h : ∀ x ∈ L, ∀ y ∈ U, x < y) :
    ∃ α β : ℝ, α < β ∧ (∀ x ∈ L, x ≤ α) ∧ ∀ y ∈ U, β ≤ y := by
  rcases L.eq_empty_or_nonempty with rfl | hL
  · rcases U.eq_empty_or_nonempty with rfl | hU
    · exact ⟨0, 1, one_pos, by simp, by simp⟩
    · exact ⟨U.min' hU - 1, U.min' hU, by linarith, by simp, fun y hy => U.min'_le y hy⟩
  · rcases U.eq_empty_or_nonempty with rfl | hU
    · exact ⟨L.max' hL, L.max' hL + 1, by linarith, fun x hx => L.le_max' x hx, by simp⟩
    · exact ⟨L.max' hL, U.min' hU, h _ (L.max'_mem hL) _ (U.min'_mem hU),
        fun x hx => L.le_max' x hx, fun y hy => U.min'_le y hy⟩

/- English proof (translation)
Use `haveI := Fintype.ofFinite P`. Set `L : Finset ℝ` to `(Finset.univ.filter (fun p => w p < 0 ∧ 0 < a p)).image (fun p => -Real.log (a p) / (w p : ℝ))`. Set `U : Finset ℝ` to `(Finset.univ.filter (fun p => 0 < w p ∧ 0 < a p)).image (fun p => -Real.log (a p) / (w p : ℝ))`. Establish `hLU : ∀ s ∈ L, ∀ t ∈ U, s < t`. Introduce `s hs t ht`.

Simplify using `only [L, U, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hs ht`. Take `⟨q, ⟨hq, haq⟩, rfl⟩` from `hs`. Take `⟨p, ⟨hp, hap⟩, rfl⟩` from `ht`. Establish `h1` using `hc p q hp hq`. Establish `hprod : 0 < a p ^ (-w q).toNat * a q ^ (w p).toNat` using `by positivity`.

Establish `hlog` using `Real.log_neg hprod h1`. Rewrite `hlog` using `[Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]`. Establish `e1 : (((-w q).toNat : ℕ) : ℝ) = -(w q : ℝ)`. Rewrite using `[← Int.cast_natCast, Int.toNat_of_nonneg (by omega), Int.cast_neg]`. Establish `e2 : (((w p).toNat : ℕ) : ℝ) = (w p : ℝ)`.

Rewrite using `[← Int.cast_natCast, Int.toNat_of_nonneg hp.le]`. Rewrite `hlog` using `[e1, e2]`. Establish `hwq : (w q : ℝ) < 0` using `by exact_mod_cast hq`. Establish `hwp : (0 : ℝ) < w p` using `by exact_mod_cast hp`. Establish `hq0 : (w q : ℝ) ≠ 0` using `hwq.ne`.

Establish `hp0 : (w p : ℝ) ≠ 0` using `hwp.ne'`. Establish `key : -Real.log (a p) / (w p : ℝ) - -Real.log (a q) / (w q : ℝ) = -((-(w q : ℝ)) * Real.log (a p) + (w p : ℝ) * Real.log (a q)) / ((w p : ℝ) * (-(w q : ℝ)))`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hpos : 0 < -Real.log (a p) / (w p : ℝ) - -Real.log (a q) / (w q : ℝ)`.

Rewrite using `[key]`. Apply `div_pos` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨α, β, hαβ, hαL, hβU⟩` from `exists_between_finset L U hLU`. Take `⟨u, hu0, h1, h2⟩` from `exists_log_norm x hx hαβ`. Use `⟨u, hu0, fun p => ?_⟩` and prove the remaining obligations. Break down `(ha p).eq_or_lt with hap | hap` into its components or cases. Rewrite using `[← hap, mul_zero]`.

Conclude with `one_pos`. Establish `hun : 0 < ‖u‖` using `norm_pos_iff.mpr hu0`. Establish `hpos : 0 < ‖u‖ ^ (w p) * a p` using `by positivity`. Rewrite using `[← Real.log_neg_iff hpos, Real.log_mul (by positivity) hap.ne', Real.log_zpow]`. Break down `lt_or_gt_of_ne (hw p) with hwn | hwp` into its components or cases.

Establish `hmem : -Real.log (a p) / (w p : ℝ) ∈ L`. Simplify using `only [L, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `⟨p, ⟨hwn, hap⟩, rfl⟩`. Establish `h3` using `lt_of_le_of_lt (hαL _ hmem) h1`. Establish `hwr : (w p : ℝ) < 0` using `by exact_mod_cast hwn`.

Rewrite `h3` using `[div_lt_iff_of_neg hwr]`. Combine the linear relations using `[mul_comm (Real.log ‖u‖) (w p : ℝ)]`. Establish `hmem : -Real.log (a p) / (w p : ℝ) ∈ U`. Simplify using `only [U, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `⟨p, ⟨hwp, hap⟩, rfl⟩`.

Establish `h4` using `lt_of_lt_of_le h2 (hβU _ hmem)`. Establish `hwr : (0 : ℝ) < w p` using `by exact_mod_cast hwp`. Rewrite `h4` using `[lt_div_iff₀ hwr]`. Combine the linear relations using `[mul_comm (Real.log ‖u‖) (w p : ℝ)]`.
-/
private theorem exists_scale {K P : Type} [NormedField K] [IsAlgClosed K] [Finite P] (x : K) (hx : 1 < ‖x‖)
    (w : P → ℤ) (a : P → ℝ) (ha : ∀ p, 0 ≤ a p) (hw : ∀ p, w p ≠ 0)
    (hc : ∀ p q, 0 < w p → w q < 0 → a p ^ (-w q).toNat * a q ^ (w p).toNat < 1) :
    ∃ u : K, u ≠ 0 ∧ ∀ p, ‖u‖ ^ (w p) * a p < 1 := by
  classical
  haveI := Fintype.ofFinite P
  let L : Finset ℝ := (Finset.univ.filter (fun p => w p < 0 ∧ 0 < a p)).image
    (fun p => -Real.log (a p) / (w p : ℝ))
  let U : Finset ℝ := (Finset.univ.filter (fun p => 0 < w p ∧ 0 < a p)).image
    (fun p => -Real.log (a p) / (w p : ℝ))
  have hLU : ∀ s ∈ L, ∀ t ∈ U, s < t := by
    intro s hs t ht
    simp only [L, U, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hs ht
    obtain ⟨q, ⟨hq, haq⟩, rfl⟩ := hs
    obtain ⟨p, ⟨hp, hap⟩, rfl⟩ := ht
    have h1 := hc p q hp hq
    have hprod : 0 < a p ^ (-w q).toNat * a q ^ (w p).toNat := by positivity
    have hlog := Real.log_neg hprod h1
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
    have e1 : (((-w q).toNat : ℕ) : ℝ) = -(w q : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega), Int.cast_neg]
    have e2 : (((w p).toNat : ℕ) : ℝ) = (w p : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hp.le]
    rw [e1, e2] at hlog
    have hwq : (w q : ℝ) < 0 := by exact_mod_cast hq
    have hwp : (0 : ℝ) < w p := by exact_mod_cast hp
    have hq0 : (w q : ℝ) ≠ 0 := hwq.ne
    have hp0 : (w p : ℝ) ≠ 0 := hwp.ne'
    have key : -Real.log (a p) / (w p : ℝ) - -Real.log (a q) / (w q : ℝ)
        = -((-(w q : ℝ)) * Real.log (a p) + (w p : ℝ) * Real.log (a q)) / ((w p : ℝ) * (-(w q : ℝ))) := by
      field_simp
      ring
    have hpos : 0 < -Real.log (a p) / (w p : ℝ) - -Real.log (a q) / (w q : ℝ) := by
      rw [key]
      apply div_pos
      · linarith
      · nlinarith
    linarith
  obtain ⟨α, β, hαβ, hαL, hβU⟩ := exists_between_finset L U hLU
  obtain ⟨u, hu0, h1, h2⟩ := exists_log_norm x hx hαβ
  refine ⟨u, hu0, fun p => ?_⟩
  rcases (ha p).eq_or_lt with hap | hap
  · rw [← hap, mul_zero]
    exact one_pos
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hpos : 0 < ‖u‖ ^ (w p) * a p := by positivity
  rw [← Real.log_neg_iff hpos, Real.log_mul (by positivity) hap.ne', Real.log_zpow]
  rcases lt_or_gt_of_ne (hw p) with hwn | hwp
  · have hmem : -Real.log (a p) / (w p : ℝ) ∈ L := by
      simp only [L, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨p, ⟨hwn, hap⟩, rfl⟩
    have h3 := lt_of_le_of_lt (hαL _ hmem) h1
    have hwr : (w p : ℝ) < 0 := by exact_mod_cast hwn
    rw [div_lt_iff_of_neg hwr] at h3
    linarith [mul_comm (Real.log ‖u‖) (w p : ℝ)]
  · have hmem : -Real.log (a p) / (w p : ℝ) ∈ U := by
      simp only [U, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨p, ⟨hwp, hap⟩, rfl⟩
    have h4 := lt_of_lt_of_le h2 (hβU _ hmem)
    have hwr : (0 : ℝ) < w p := by exact_mod_cast hwp
    rw [lt_div_iff₀ hwr] at h4
    linarith [mul_comm (Real.log ‖u‖) (w p : ℝ)]

/- English proof (translation)
Take `⟨U, hUs, hU⟩` from `(Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg`. Establish `bound : ∀ m : ℝ, 0 ≤ m → (∀ a ∈ U, ‖ξ a‖ ≤ m) → ∀ g, ‖ξ (s g)‖ ≤ m`. Introduce `m hm hUm`. Establish `key : ∀ x ∈ Submodule.span B (U : Set A), ‖ξ x‖ ≤ m`. Introduce `x hx`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact hUm x hx`. Consider the case `zero => simpa using hm`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add]`.

Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)`. Consider the case `smul b x _ hx`. Rewrite using `[Algebra.smul_def, map_mul, norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Introduce `g`.

Conclude with `key _ (hU ▸ Submodule.subset_span ⟨g, rfl⟩)`. Break down `U.eq_empty_or_nonempty with hE | hne` into its components or cases. Take `⟨g₀⟩` from `‹Nonempty G›`. Conclude with `⟨g₀, bound _ (norm_nonneg _) (by simp [hE])⟩`. Take `⟨a, ha, hmax⟩` from `U.exists_max_image (fun a => ‖ξ a‖) hne`.

Take `⟨g₀, rfl⟩` from `hUs ha`. Conclude with `⟨g₀, bound _ (norm_nonneg _) hmax⟩`.
-/
private theorem exists_max_entry {B A K G : Type} [CommRing B] [CommRing A] [Algebra B A] [NormedField K]
    [IsUltrametricDist K] [Nonempty G] (ξ : A →+* K) (hB : ∀ b, ‖ξ (algebraMap B A b)‖ ≤ 1) (s : G → A)
    (hfg : (Submodule.span B (Set.range s)).FG) : ∃ g₀, ∀ g, ‖ξ (s g)‖ ≤ ‖ξ (s g₀)‖ := by
  classical
  obtain ⟨U, hUs, hU⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  have bound : ∀ m : ℝ, 0 ≤ m → (∀ a ∈ U, ‖ξ a‖ ≤ m) → ∀ g, ‖ξ (s g)‖ ≤ m := by
    intro m hm hUm
    have key : ∀ x ∈ Submodule.span B (U : Set A), ‖ξ x‖ ≤ m := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact hUm x hx
      | zero => simpa using hm
      | add x y _ _ hx hy =>
        rw [map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
      | smul b x _ hx =>
        rw [Algebra.smul_def, map_mul, norm_mul]
        calc ‖ξ (algebraMap B A b)‖ * ‖ξ x‖ ≤ 1 * m :=
              mul_le_mul (hB b) hx (norm_nonneg _) zero_le_one
          _ = m := one_mul m
    intro g
    exact key _ (hU ▸ Submodule.subset_span ⟨g, rfl⟩)
  rcases U.eq_empty_or_nonempty with hE | hne
  · obtain ⟨g₀⟩ := ‹Nonempty G›
    exact ⟨g₀, bound _ (norm_nonneg _) (by simp [hE])⟩
  · obtain ⟨a, ha, hmax⟩ := U.exists_max_image (fun a => ‖ξ a‖) hne
    obtain ⟨g₀, rfl⟩ := hUs ha
    exact ⟨g₀, bound _ (norm_nonneg _) hmax⟩

/- English proof (translation)
Apply the tactic sequence `have hmax : ∀ p : {p : I × I // p.1 ≠ p.2}, ∃ g₀ : G, ∀ g, ‖ξ (r g p.1.1 p.1.2)‖ ≤ ‖ξ (r g₀ p.1.1 p.1.2)‖ := fun p => exists_max_entry (B := B) ξ.toRingHom hB (fun g => r g p.1.1 p.1.2) (hfg p.1.1 p.1.2)`. Use `choose g₀ hg₀ using hmax`. Establish `hc : ∀ p q : {p : I × I // p.1 ≠ p.2}, 0 < w p.1.1 - w p.1.2 → w q.1.1 - w q.1.2 < 0 → ‖ξ (r (g₀ p) p.1.1 p.1.2)‖ ^ (-(w q.1.1 - w q.1.2)).toNat * ‖ξ (r (g₀ q) q.1.1 q.1.2)‖ ^ (w p.1.1 - w p.1.2).toNat < 1`. Introduce `p q hp hq`. Establish `e1 : (((-(w q.1.1 - w q.1.2)).toNat : ℕ) : ℤ) = -(w q.1.1 - w q.1.2)` using `Int.toNat_of_nonneg (by omega)`.

Establish `e2 : (((w p.1.1 - w p.1.2).toNat : ℕ) : ℤ) = w p.1.1 - w p.1.2` using `Int.toNat_of_nonneg (by omega)`. Establish `hsum : ((List.replicate (-(w q.1.1 - w q.1.2)).toNat (g₀ p, p.1.1, p.1.2) ++ List.replicate (w p.1.1 - w p.1.2).toNat (g₀ q, q.1.1, q.1.2)).map fun s => w s.2.1 - w s.2.2).sum = 0`. Simplify using `only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate, nsmul_eq_mul]`. Rewrite using `[e1, e2]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hex : ∃ s ∈ List.replicate (-(w q.1.1 - w q.1.2)).toNat (g₀ p, p.1.1, p.1.2) ++ List.replicate (w p.1.1 - w p.1.2).toNat (g₀ q, q.1.1, q.1.2), s.2.1 ≠ s.2.2`. Use `⟨(g₀ p, p.1.1, p.1.2), ?_, p.2⟩` and prove the remaining obligations. Rewrite using `[List.mem_append, List.mem_replicate]`. Conclude with `Or.inl ⟨by omega, rfl⟩`. Establish `h` using `hcyc _ hsum hex`.

Simplify `h` using `only [List.map_append, List.map_replicate, List.prod_append, List.prod_replicate, map_mul, map_pow, norm_mul, norm_pow]`. Take `⟨u, hu, hu'⟩` from `exists_scale (P := {p : I × I // p.1 ≠ p.2}) x hx (fun p => w p.1.1 - w p.1.2) (fun p => ‖ξ (r (g₀ p) p.1.1 p.1.2)‖) (fun p => norm_nonneg _) (fun p => hw _ _ p.2) hc`. Take `⟨ξ', hξ'⟩` from `twist gr h1 h2 hO ξ u hu`. Use `⟨ξ', fun b => ?_, fun j c hc' => ?_, fun g i j hij => ?_⟩` and prove the remaining obligations. Rewrite using `[hξ' 0 _ (h0 b), zpow_zero, one_mul]`.

Rewrite using `[hξ' j c hc']`. Simplify using `[zpow_ne_zero _ hu]`. Rewrite using `[hξ' _ _ (hr g i j), norm_mul, norm_zpow]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem scale_core {O B A K G I : Type} [CommRing O] [CommRing B] [CommRing A] [NormedField K]
    [IsUltrametricDist K] [IsAlgClosed K] [Algebra O A] [Algebra O K] [Algebra B A] [Nonempty G] [Finite I]
    (x : K) (hx : 1 < ‖x‖) (gr : ℤ → Submodule B A) (h1 : DirectSum.IsInternal gr) (h2 : SetLike.GradedMonoid gr)
    (h0 : ∀ b : B, algebraMap B A b ∈ gr 0) (hO : ∀ c : O, algebraMap O A c ∈ gr 0)
    (w : I → ℤ) (hw : ∀ i j, i ≠ j → w i - w j ≠ 0) (r : G → I → I → A)
    (hr : ∀ g i j, r g i j ∈ gr (w i - w j))
    (hfg : ∀ i j, (Submodule.span B (Set.range fun g => r g i j)).FG) (ξ : A →ₐ[O] K)
    (hB : ∀ b, ‖ξ (algebraMap B A b)‖ ≤ 1)
    (hcyc : ∀ L : List (G × I × I), (L.map fun s => w s.2.1 - w s.2.2).sum = 0 → (∃ s ∈ L, s.2.1 ≠ s.2.2) →
      ‖ξ (L.map fun s => r s.1 s.2.1 s.2.2).prod‖ < 1) :
    ∃ ξ' : A →ₐ[O] K, (∀ b, ξ' (algebraMap B A b) = ξ (algebraMap B A b)) ∧
      (∀ j, ∀ a ∈ gr j, ξ' a = 0 ↔ ξ a = 0) ∧ ∀ g i j, i ≠ j → ‖ξ' (r g i j)‖ < 1 := by
  classical
  have hmax : ∀ p : {p : I × I // p.1 ≠ p.2}, ∃ g₀ : G,
      ∀ g, ‖ξ (r g p.1.1 p.1.2)‖ ≤ ‖ξ (r g₀ p.1.1 p.1.2)‖ := fun p =>
    exists_max_entry (B := B) ξ.toRingHom hB (fun g => r g p.1.1 p.1.2) (hfg p.1.1 p.1.2)
  choose g₀ hg₀ using hmax
  have hc : ∀ p q : {p : I × I // p.1 ≠ p.2}, 0 < w p.1.1 - w p.1.2 → w q.1.1 - w q.1.2 < 0 →
      ‖ξ (r (g₀ p) p.1.1 p.1.2)‖ ^ (-(w q.1.1 - w q.1.2)).toNat *
        ‖ξ (r (g₀ q) q.1.1 q.1.2)‖ ^ (w p.1.1 - w p.1.2).toNat < 1 := by
    intro p q hp hq
    have e1 : (((-(w q.1.1 - w q.1.2)).toNat : ℕ) : ℤ) = -(w q.1.1 - w q.1.2) := Int.toNat_of_nonneg (by omega)
    have e2 : (((w p.1.1 - w p.1.2).toNat : ℕ) : ℤ) = w p.1.1 - w p.1.2 := Int.toNat_of_nonneg (by omega)
    have hsum : ((List.replicate (-(w q.1.1 - w q.1.2)).toNat (g₀ p, p.1.1, p.1.2) ++
        List.replicate (w p.1.1 - w p.1.2).toNat (g₀ q, q.1.1, q.1.2)).map
          fun s => w s.2.1 - w s.2.2).sum = 0 := by
      simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate, nsmul_eq_mul]
      rw [e1, e2]
      ring
    have hex : ∃ s ∈ List.replicate (-(w q.1.1 - w q.1.2)).toNat (g₀ p, p.1.1, p.1.2) ++
        List.replicate (w p.1.1 - w p.1.2).toNat (g₀ q, q.1.1, q.1.2), s.2.1 ≠ s.2.2 := by
      refine ⟨(g₀ p, p.1.1, p.1.2), ?_, p.2⟩
      rw [List.mem_append, List.mem_replicate]
      exact Or.inl ⟨by omega, rfl⟩
    have h := hcyc _ hsum hex
    simpa only [List.map_append, List.map_replicate, List.prod_append, List.prod_replicate, map_mul, map_pow,
      norm_mul, norm_pow] using h
  obtain ⟨u, hu, hu'⟩ := exists_scale (P := {p : I × I // p.1 ≠ p.2}) x hx (fun p => w p.1.1 - w p.1.2)
    (fun p => ‖ξ (r (g₀ p) p.1.1 p.1.2)‖) (fun p => norm_nonneg _) (fun p => hw _ _ p.2) hc
  obtain ⟨ξ', hξ'⟩ := twist gr h1 h2 hO ξ u hu
  refine ⟨ξ', fun b => ?_, fun j c hc' => ?_, fun g i j hij => ?_⟩
  · rw [hξ' 0 _ (h0 b), zpow_zero, one_mul]
  · rw [hξ' j c hc']
    simp [zpow_ne_zero _ hu]
  · rw [hξ' _ _ (hr g i j), norm_mul, norm_zpow]
    calc ‖u‖ ^ (w i - w j) * ‖ξ (r g i j)‖
        ≤ ‖u‖ ^ (w i - w j) * ‖ξ (r (g₀ ⟨(i, j), hij⟩) i j)‖ :=
          mul_le_mul_of_nonneg_left (hg₀ ⟨(i, j), hij⟩ g) (zpow_nonneg (norm_nonneg _) _)
      _ < 1 := hu' ⟨(i, j), hij⟩

/- English proof (translation)
Apply the tactic sequence `rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp_all [Fr.w]`.
-/
private theorem w_sub_ne {n : ℕ} (hn : n = 2 ∨ n = 3) (i j : Fin n) (h : i ≠ j) : Fr.w n i - Fr.w n j ≠ 0 := by
  rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp_all [Fr.w]

/- English proof (translation)
Introduce `l _ c _ F C₀ n hF hn S ξ _`. Take `⟨hco, hmB⟩` from `Fr.co_B hF hn S`. Use `haveI := hco`. Take `⟨hcone, -⟩` from `Fr.cone_u hF hn S`. Take `⟨hint, hgm, hgr0, -, -, -, hrgr⟩` from `Fr.gr_A hF hn S`.

Take `⟨-, hy1, hy2⟩` from `coPt l c S.B (ξ.comp S.inc)`. Use `haveI : Nonempty F.G0 := ⟨F.g0⟩`. Establish `hx : 1 < ‖(((l : ℚ_[l])⁻¹ : ℚ_[l]) : Qbar l)‖`. Rewrite using `[PadicAlgCl.norm_extends, norm_inv, Padic.norm_p, inv_inv]`. Conclude with `(Fact.out : l.Prime).one_lt` after adjusting the coercions.

Establish `h0 : ∀ b : S.B, algebraMap S.B S.A b ∈ S.gr 0`. Introduce `b`. Rewrite using `[hgr0, Submodule.mem_one]`. Conclude with `⟨b, rfl⟩`. Establish `hO : ∀ o : c.O, algebraMap c.O S.A o ∈ S.gr 0` using `fun o => h0 (algebraMap c.O S.B o)`.

Establish `hB : ∀ b, ‖ξ (algebraMap S.B S.A b)‖ ≤ 1` using `fun b => hy1 b`. Establish `hcyc : ∀ L : List (F.G0 × Fin n × Fin n), (L.map fun s => Fr.w n s.2.1 - Fr.w n s.2.2).sum = 0 → (∃ s ∈ L, s.2.1 ≠ s.2.2) → ‖ξ (L.map fun s => S.u.r s.1 s.2.1 s.2.2).prod‖ < 1`. Introduce `L hs hne`. Take `⟨b, hb, hbe⟩` from `hcone.cyc L hs hne`. Rewrite using `[← hbe]`.

Conclude with `hy2 b hb`. Take `⟨ξ', hξB, hz, hoff⟩` from `scale_core _ hx S.gr hint hgm h0 hO (Fr.w n) (w_sub_ne hn) S.u.r hrgr hcone.fg ξ hB hcyc`. Establish `hξB' : ∀ b, ξ' (S.inc b) = ξ (S.inc b)` using `hξB`. Establish `hinc : ξ'.comp S.inc = ξ.comp S.inc` using `AlgHom.ext fun b => hξB' b`. Use `⟨ξ', ⟨⟨?_, ?_⟩, hoff⟩, hinc, hz⟩` and prove the remaining obligations.

Introduce and unpack `⟨a, ha⟩`. Establish `ha' : a ∈ Algebra.adjoin c.O ((S.B : Set S.R) ∪ {x | ∃ g i j, x = S.ρ.r g i j})` using `ha`. Use `Algebra.adjoin_induction (p := fun x hx => ‖ξ' ⟨x, hx⟩‖ ≤ 1) ?_ ?_ ?_ ?_ ha'` and prove the remaining obligations. Introduce `x hx`. Break down `hx with hxB | ⟨g, i, j, rfl⟩` into its components or cases.

Use `show ‖ξ' (S.inc ⟨x, hxB⟩)‖ ≤ 1`. Rewrite using `[hξB']`. Conclude with `hy1 _`. Distinguish the cases in `hij : i = j`. Substitute `hij show ‖ξ' (S.inc (S.aB g i))‖ ≤ 1` using the available equality.

Rewrite using `[hξB']`. Conclude with `hy1 _`. Conclude with `(hoff g i j hij).le`. Introduce `o show ‖ξ' (S.inc (algebraMap c.O S.B o))‖ ≤ 1`. Rewrite using `[hξB']`.

Conclude with `hy1 _`. Introduce `x y hx hy ihx ihy show ‖ξ' (⟨x, hx⟩ + ⟨y, hy⟩)‖ ≤ 1`. Rewrite using `[map_add]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ihx ihy)`. Introduce `x y hx hy ihx ihy show ‖ξ' (⟨x, hx⟩ * ⟨y, hy⟩)‖ ≤ 1`.

Rewrite using `[map_mul, norm_mul]`. Conclude with `mul_le_one₀ ihx (norm_nonneg _) ihy`. Introduce `b hb`. Rewrite using `[hξB']`. Conclude with `hy2 b (hmB ▸ hb)`.
-/
theorem UpperTheory.V.J.scale :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ ξ : S.A →ₐ[c.O] Qbar l, S.u.OffTri (RingHom.ker ξ) →
          ∃ ξ' : S.A →ₐ[c.O] Qbar l, VPt S ξ' ∧ ξ'.comp S.inc = ξ.comp S.inc ∧
            (∀ (j : ℤ), ∀ a ∈ S.gr j, ξ' a = 0 ↔ ξ a = 0) := by
  intro l _ c _ F C₀ n hF hn S ξ _
  obtain ⟨hco, hmB⟩ := Fr.co_B hF hn S
  haveI := hco
  obtain ⟨hcone, -⟩ := Fr.cone_u hF hn S
  obtain ⟨hint, hgm, hgr0, -, -, -, hrgr⟩ := Fr.gr_A hF hn S
  obtain ⟨-, hy1, hy2⟩ := coPt l c S.B (ξ.comp S.inc)
  haveI : Nonempty F.G0 := ⟨F.g0⟩
  have hx : 1 < ‖(((l : ℚ_[l])⁻¹ : ℚ_[l]) : Qbar l)‖ := by
    rw [PadicAlgCl.norm_extends, norm_inv, Padic.norm_p, inv_inv]
    exact_mod_cast (Fact.out : l.Prime).one_lt
  have h0 : ∀ b : S.B, algebraMap S.B S.A b ∈ S.gr 0 := by
    intro b
    rw [hgr0, Submodule.mem_one]
    exact ⟨b, rfl⟩
  have hO : ∀ o : c.O, algebraMap c.O S.A o ∈ S.gr 0 := fun o => h0 (algebraMap c.O S.B o)
  have hB : ∀ b, ‖ξ (algebraMap S.B S.A b)‖ ≤ 1 := fun b => hy1 b
  have hcyc : ∀ L : List (F.G0 × Fin n × Fin n), (L.map fun s => Fr.w n s.2.1 - Fr.w n s.2.2).sum = 0 →
      (∃ s ∈ L, s.2.1 ≠ s.2.2) → ‖ξ (L.map fun s => S.u.r s.1 s.2.1 s.2.2).prod‖ < 1 := by
    intro L hs hne
    obtain ⟨b, hb, hbe⟩ := hcone.cyc L hs hne
    rw [← hbe]
    exact hy2 b hb
  obtain ⟨ξ', hξB, hz, hoff⟩ := scale_core _ hx S.gr hint hgm h0 hO (Fr.w n) (w_sub_ne hn) S.u.r hrgr
    hcone.fg ξ hB hcyc
  have hξB' : ∀ b, ξ' (S.inc b) = ξ (S.inc b) := hξB
  have hinc : ξ'.comp S.inc = ξ.comp S.inc := AlgHom.ext fun b => hξB' b
  refine ⟨ξ', ⟨⟨?_, ?_⟩, hoff⟩, hinc, hz⟩
  · rintro ⟨a, ha⟩
    have ha' : a ∈ Algebra.adjoin c.O ((S.B : Set S.R) ∪ {x | ∃ g i j, x = S.ρ.r g i j}) := ha
    refine Algebra.adjoin_induction (p := fun x hx => ‖ξ' ⟨x, hx⟩‖ ≤ 1) ?_ ?_ ?_ ?_ ha'
    · intro x hx
      rcases hx with hxB | ⟨g, i, j, rfl⟩
      · show ‖ξ' (S.inc ⟨x, hxB⟩)‖ ≤ 1
        rw [hξB']
        exact hy1 _
      · by_cases hij : i = j
        · subst hij
          show ‖ξ' (S.inc (S.aB g i))‖ ≤ 1
          rw [hξB']
          exact hy1 _
        · exact (hoff g i j hij).le
    · intro o
      show ‖ξ' (S.inc (algebraMap c.O S.B o))‖ ≤ 1
      rw [hξB']
      exact hy1 _
    · intro x y hx hy ihx ihy
      show ‖ξ' (⟨x, hx⟩ + ⟨y, hy⟩)‖ ≤ 1
      rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ihx ihy)
    · intro x y hx hy ihx ihy
      show ‖ξ' (⟨x, hx⟩ * ⟨y, hy⟩)‖ ≤ 1
      rw [map_mul, norm_mul]
      exact mul_le_one₀ ihx (norm_nonneg _) ihy
  · intro b hb
    rw [hξB']
    exact hy2 b (hmB ▸ hb)

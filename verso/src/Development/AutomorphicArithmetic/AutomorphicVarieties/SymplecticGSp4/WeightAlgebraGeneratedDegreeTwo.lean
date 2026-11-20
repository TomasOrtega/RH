import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresGrZeroIsCOOfMemMaximalIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartSpan
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

/- English proof (translation)
Introduce `m`. Proceed by induction on `m using WellFoundedLT.induction with`. Consider the case `ind m ih`. Introduce `hm`. Establish `step : ∀ g : σ →₀ ℕ, g ≠ 0 → g ≤ m → Finsupp.weight lam g = 0 → P g → P m` using `fun g hg hle hw hP => by`.

Establish `e : m - g + g = m` using `tsub_add_cancel_of_le hle`. Establish `hlt : m - g < m` using `by conv_rhs => rw [← e]`. Conclude with `lt_add_of_pos_right _ (pos_iff_ne_zero.2 hg)`. Establish `hw' : Finsupp.weight lam (m - g) = 0`. Use `congrArg (Finsupp.weight lam) e` as an intermediate fact.

Rewrite `this` using `[map_add, hw, add_zero, hm]`. Then use the resulting hypothesis. Rewrite using `[← e]`. Conclude with `hadd _ _ (ih _ hlt hw') hP`. Distinguish the cases in `hz : ∃ s, m s ≠ 0 ∧ lam s = 0`. Take `⟨s, hs, hs0⟩` from `hz`.

Use `step (Finsupp.single s 1) (by simp) ?_ (by simp [Finsupp.weight_single, hs0]) (h1 s hs0)` and prove the remaining obligations. Rewrite using `[Finsupp.single_le_iff]`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hp : (∃ s, m s ≠ 0 ∧ lam s = 1) ∧ ∃ t, m t ≠ 0 ∧ lam t = -1`. Take `⟨⟨s, hs, hs1⟩, t, ht, ht1⟩` from `hp`.

Establish `hst : s ≠ t`. Introduce and unpack `rfl`. Use linear arithmetic over natural numbers and integers. Use `step _ (by simp) ?_ (by simp [Finsupp.weight_single, hs1, ht1]) (h2 s t hs1 ht1)` and prove the remaining obligations. Introduce `u`.

Simplify using `only [Finsupp.add_apply, Finsupp.single_apply]`. Use `split_ifs with a b b`. Conclude with `absurd (a.trans b.symm) hst`. Substitute `a` using the available equality. Use linear arithmetic over natural numbers and integers.

Substitute `b` using the available equality. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Establish `hsum : ∑ s, (m s : ℤ) * lam s = 0`. Rewrite using `[← hm, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]`.

Simplify using the standard rewrite rules. Establish `: m = 0`. Use extensionality with `u`. Use `push Not at hz`. Break down `not_and_or.1 hp with hp | hp` into its components or cases.

Use `push Not at hp`. Establish `hn : ∀ s ∈ Finset.univ, (m s : ℤ) * lam s ≤ 0` using `fun s _ => by`. Distinguish the cases in `h : m s = 0`. Simplify using `[h]`. Use `hl s` as an intermediate fact.

Use `hp s h` as an intermediate fact. Conclude with `mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)`. Establish `h3` using `(Finset.sum_eq_zero_iff_of_nonpos hn).1 hsum u (Finset.mem_univ _)`. Assume the negation of the conclusion as `h`. Break down `mul_eq_zero.1 h3 with h4 | h4` into its components or cases.

Conclude with `h (by exact_mod_cast h4)`. Conclude with `hz u h h4`. Use `push Not at hp`. Establish `hn : ∀ s ∈ Finset.univ, 0 ≤ (m s : ℤ) * lam s` using `fun s _ => by`. Distinguish the cases in `h : m s = 0`.

Simplify using `[h]`. Use `hl s` as an intermediate fact. Use `hp s h` as an intermediate fact. Conclude with `mul_nonneg (by positivity) (by omega)`. Establish `h3` using `(Finset.sum_eq_zero_iff_of_nonneg hn).1 hsum u (Finset.mem_univ _)`.

Assume the negation of the conclusion as `h`. Break down `mul_eq_zero.1 h3 with h4 | h4` into its components or cases. Conclude with `h (by exact_mod_cast h4)`. Conclude with `hz u h h4`. Rewrite using `[this]`.

Conclude with `h0`.
-/
private theorem aW_comb {σ : Type} [Fintype σ] (lam : σ → ℤ) (hl : ∀ s, lam s = -1 ∨ lam s = 0 ∨ lam s = 1)
    (P : (σ →₀ ℕ) → Prop) (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (h1 : ∀ s, lam s = 0 → P (Finsupp.single s 1))
    (h2 : ∀ s t, lam s = 1 → lam t = -1 → P (Finsupp.single s 1 + Finsupp.single t 1)) :
    ∀ m, Finsupp.weight lam m = 0 → P m := by
  classical
  intro m
  induction m using WellFoundedLT.induction with
  | ind m ih =>
  intro hm
  have step : ∀ g : σ →₀ ℕ, g ≠ 0 → g ≤ m → Finsupp.weight lam g = 0 → P g → P m := fun g hg hle hw hP => by
    have e : m - g + g = m := tsub_add_cancel_of_le hle
    have hlt : m - g < m := by
      conv_rhs => rw [← e]
      exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hg)
    have hw' : Finsupp.weight lam (m - g) = 0 := by
      have := congrArg (Finsupp.weight lam) e
      rwa [map_add, hw, add_zero, hm] at this
    rw [← e]
    exact hadd _ _ (ih _ hlt hw') hP
  by_cases hz : ∃ s, m s ≠ 0 ∧ lam s = 0
  · obtain ⟨s, hs, hs0⟩ := hz
    refine step (Finsupp.single s 1) (by simp) ?_ (by simp [Finsupp.weight_single, hs0]) (h1 s hs0)
    rw [Finsupp.single_le_iff]
    omega
  by_cases hp : (∃ s, m s ≠ 0 ∧ lam s = 1) ∧ ∃ t, m t ≠ 0 ∧ lam t = -1
  · obtain ⟨⟨s, hs, hs1⟩, t, ht, ht1⟩ := hp
    have hst : s ≠ t := by
      rintro rfl
      omega
    refine step _ (by simp) ?_ (by simp [Finsupp.weight_single, hs1, ht1]) (h2 s t hs1 ht1)
    intro u
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    split_ifs with a b b
    · exact absurd (a.trans b.symm) hst
    · subst a; omega
    · subst b; omega
    · omega
  have hsum : ∑ s, (m s : ℤ) * lam s = 0 := by
    rw [← hm, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  have : m = 0 := by
    ext u
    push Not at hz
    rcases not_and_or.1 hp with hp | hp
    · push Not at hp
      have hn : ∀ s ∈ Finset.univ, (m s : ℤ) * lam s ≤ 0 := fun s _ => by
        by_cases h : m s = 0
        · simp [h]
        · have := hl s; have := hp s h
          exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
      have h3 := (Finset.sum_eq_zero_iff_of_nonpos hn).1 hsum u (Finset.mem_univ _)
      by_contra h
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact h (by exact_mod_cast h4)
      · exact hz u h h4
    · push Not at hp
      have hn : ∀ s ∈ Finset.univ, 0 ≤ (m s : ℤ) * lam s := fun s _ => by
        by_cases h : m s = 0
        · simp [h]
        · have := hl s; have := hp s h
          exact mul_nonneg (by positivity) (by omega)
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg hn).1 hsum u (Finset.mem_univ _)
      by_contra h
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact h (by exact_mod_cast h4)
      · exact hz u h h4
  rw [this]
  exact h0

/- English proof (translation)
Evaluate the decidable proposition.
-/
private theorem aW_wts : ∀ w ∈ wts, (w.1 = -1 ∨ w.1 = 0 ∨ w.1 = 1) ∧ (-1 ≤ w.2 ∧ w.2 ≤ 1) := by decide

/- English proof (translation)
Establish `hmon : ∀ m, Finsupp.weight (fun s => (W.wt s).1) m = 0 → W.π (MvPowerSeries.monomial m 1) ∈ B`. Use `aW_comb _ (fun s => (aW_wts _ (hw s)).1) _ (by simp) (fun a b ha hb => ?_) h1 (fun s t hs ht => ?_)` and prove the remaining obligations. Use `mul_mem ha hb` as an intermediate fact. Rewrite `this` using `[← map_mul, MvPowerSeries.monomial_mul_monomial, one_mul]`. Then use the resulting hypothesis. Use `h2 s t hs ht` as an intermediate fact.

Rewrite `this` using `[WPres.z, WPres.z, ← map_mul, MvPowerSeries.X_def, MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial, one_mul]`. Then use the resulting hypothesis. Establish `hfst : ∀ m : W.σ →₀ ℕ, Finsupp.weight (fun s => (W.wt s).1) m = (Finsupp.weight W.wt m).1` using `fun m => by`. Proceed by induction on `m using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb, Prod.fst_add]`.

Consider the case `single s k => simp [Finsupp.weight_single]`. Take `⟨μ, hμ, hdec⟩` from `part_span O R (ℤ × ℤ) W {m | Finsupp.weight W.wt m = (0, n)} (0, n) (fun _ h => h)`. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Take `⟨b, hb, rfl⟩` from `hdec f hf`. Use `show W.π _ ∈ _`.

Rewrite using `[map_sum]`. Use `sum_mem fun m hm => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Use `mul_mem (h0 _ ⟨b m, hb m, rfl⟩) (hmon m ?_)` and prove the remaining obligations. Establish `: Finsupp.weight W.wt m = (0, n)` using `hμ hm`.

Rewrite using `[hfst, this]`.
-/
private theorem aW_gen {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (W : WPres O (ℤ × ℤ) R)
    (hw : ∀ s, W.wt s ∈ wts) (B : Subalgebra O R) (h0 : ∀ x ∈ W.part 0, x ∈ B)
    (h1 : ∀ s, (W.wt s).1 = 0 → W.z s ∈ B)
    (h2 : ∀ s t, (W.wt s).1 = 1 → (W.wt t).1 = -1 → W.z s * W.z t ∈ B) (n : ℤ) :
    ∀ x ∈ W.part (0, n), x ∈ B := by
  have hmon : ∀ m, Finsupp.weight (fun s => (W.wt s).1) m = 0 → W.π (MvPowerSeries.monomial m 1) ∈ B := by
    refine aW_comb _ (fun s => (aW_wts _ (hw s)).1) _ (by simp) (fun a b ha hb => ?_) h1 (fun s t hs ht => ?_)
    · have := mul_mem ha hb
      rwa [← map_mul, MvPowerSeries.monomial_mul_monomial, one_mul] at this
    · have := h2 s t hs ht
      rwa [WPres.z, WPres.z, ← map_mul, MvPowerSeries.X_def, MvPowerSeries.X_def,
        MvPowerSeries.monomial_mul_monomial, one_mul] at this
  have hfst : ∀ m : W.σ →₀ ℕ, Finsupp.weight (fun s => (W.wt s).1) m = (Finsupp.weight W.wt m).1 := fun m => by
    induction m using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb, Prod.fst_add]
    | single s k => simp [Finsupp.weight_single]
  obtain ⟨μ, hμ, hdec⟩ := part_span O R (ℤ × ℤ) W {m | Finsupp.weight W.wt m = (0, n)} (0, n) (fun _ h => h)
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨b, hb, rfl⟩ := hdec f hf
  show W.π _ ∈ _
  rw [map_sum]
  refine sum_mem fun m hm => ?_
  rw [map_mul]
  refine mul_mem (h0 _ ⟨b m, hb m, rfl⟩) (hmon m ?_)
  have : Finsupp.weight W.wt m = (0, n) := hμ hm
  rw [hfst, this]

/- English proof (translation)
Set `U : Set R` to `Set.range W.z ∪ Set.range fun p : W.σ × W.σ => W.z p.1 * W.z p.2`. Establish `hU : U.Finite` using `(Set.finite_range _).union (Set.finite_range _)`. Set `T : Set (gradedSub a)` to `{x | (x.1 ∈ a (-2) ∨ x.1 ∈ a (-1) ∨ x.1 ∈ a 1 ∨ x.1 ∈ a 2) ∧ x.1 ∈ U}`. Establish `hT : T.Finite` using `(hU.preimage Subtype.val_injective.injOn).subset fun x hx => hx.2`. Use `⟨hT.toFinset, fun x hx => (hT.mem_toFinset.1 hx).1, ?_⟩` and prove the remaining obligations.

Rewrite using `[hT.coe_toFinset]`. Use `set S := Algebra.adjoin O ({x : gradedSub a | x.1 ∈ a 0} ∪ T) with hS`. Establish `key : ∀ n : ℤ, -2 ≤ n → n ≤ 2 → ∀ y ∈ W.part (0, n), y ∈ U → y ∈ S.map (gradedSub a).val`. Introduce `n hn hn' y hy hyU`. Rewrite `hy` using `[← ha]`.

Use `⟨⟨y, le_iSup a n hy⟩, Algebra.subset_adjoin ?_, rfl⟩` and prove the remaining obligations. Establish `h4 : n = 0 ∨ n = -2 ∨ n = -1 ∨ n = 1 ∨ n = 2` using `by omega`. Break down `h4 with rfl | rfl | rfl | rfl | rfl` into its components or cases. Conclude with `Or.inl hy`. Conclude with `Or.inr ⟨Or.inl hy, hyU⟩`.

Conclude with `Or.inr ⟨Or.inr (Or.inl hy), hyU⟩`. Conclude with `Or.inr ⟨Or.inr (Or.inr (Or.inl hy)), hyU⟩`. Conclude with `Or.inr ⟨Or.inr (Or.inr (Or.inr hy)), hyU⟩`. Establish `main` using `aW_gen W hw (S.map (gradedSub a).val) (fun y hy => by`. Establish `hy' : y ∈ a 0` using `by rw [ha]; exact hy`.

Conclude with `⟨⟨y, le_iSup a 0 hy'⟩, Algebra.subset_adjoin (Or.inl hy'), rfl⟩)`. Use the proof step `(fun s hs => by`. Establish `hb` using `(aW_wts _ (hw s)).2`. Use `key (W.wt s).2 (by omega) (by omega) _ ?_ (Or.inl ⟨s, rfl⟩)` and prove the remaining obligations. Rewrite using `[← hs]`.

Conclude with `W.z_mem s)`. Use the proof step `(fun s t hs ht => by`. Establish `hb` using `(aW_wts _ (hw s)).2`. Establish `hb'` using `(aW_wts _ (hw t)).2`. Use `key ((W.wt s).2 + (W.wt t).2) (by omega) (by omega) _ ?_ (Or.inr ⟨(s, t), rfl⟩)` and prove the remaining obligations.

Establish `h5 : W.z s * W.z t ∈ W.part (W.wt s + W.wt t)` using `SetLike.GradedMul.mul_mem (W.z_mem s) (W.z_mem t)`. Establish `h6 : W.wt s + W.wt t = (0, (W.wt s).2 + (W.wt t).2)` using `Prod.ext (by rw [Prod.fst_add, hs, ht]; rfl) rfl`. Rewrite using `[h6] at h5)` and apply the resulting hypothesis. Rewrite using `[eq_top_iff]`. Introduce and unpack `⟨x, hx⟩ -`.

Establish `hxS : x ∈ S.map (gradedSub a).val` using `Submodule.iSup_induction a (motive := fun x => x ∈ S.map (gradedSub a).val) hx (fun n y hy => main n y (ha n ▸ hy)) (zero_mem _) (fun a b ha hb => add_mem ha hb)`. Take `⟨y, hy, hxy⟩` from `hxS`. Take `rfl : y = ⟨x, hx⟩` from `Subtype.ext hxy`. Conclude with `hy`.
-/
private theorem weight_algebra_generated_degree_two {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (W : WPres O (ℤ × ℤ) R)
    (hw : ∀ s, W.wt s ∈ wts) (a : ℤ → Submodule O R) [SetLike.GradedMonoid a] (ha : ∀ n, a n = W.part (0, n)) :
    ∃ s : Finset (gradedSub a), (∀ x ∈ s, x.1 ∈ a (-2) ∨ x.1 ∈ a (-1) ∨ x.1 ∈ a 1 ∨ x.1 ∈ a 2) ∧
      Algebra.adjoin O ({x : gradedSub a | x.1 ∈ a 0} ∪ s) = ⊤ := by
  classical
  let U : Set R := Set.range W.z ∪ Set.range fun p : W.σ × W.σ => W.z p.1 * W.z p.2
  have hU : U.Finite := (Set.finite_range _).union (Set.finite_range _)
  let T : Set (gradedSub a) := {x | (x.1 ∈ a (-2) ∨ x.1 ∈ a (-1) ∨ x.1 ∈ a 1 ∨ x.1 ∈ a 2) ∧ x.1 ∈ U}
  have hT : T.Finite := (hU.preimage Subtype.val_injective.injOn).subset fun x hx => hx.2
  refine ⟨hT.toFinset, fun x hx => (hT.mem_toFinset.1 hx).1, ?_⟩
  rw [hT.coe_toFinset]
  set S := Algebra.adjoin O ({x : gradedSub a | x.1 ∈ a 0} ∪ T) with hS
  have key : ∀ n : ℤ, -2 ≤ n → n ≤ 2 → ∀ y ∈ W.part (0, n), y ∈ U → y ∈ S.map (gradedSub a).val := by
    intro n hn hn' y hy hyU
    rw [← ha] at hy
    refine ⟨⟨y, le_iSup a n hy⟩, Algebra.subset_adjoin ?_, rfl⟩
    have h4 : n = 0 ∨ n = -2 ∨ n = -1 ∨ n = 1 ∨ n = 2 := by omega
    rcases h4 with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl hy
    · exact Or.inr ⟨Or.inl hy, hyU⟩
    · exact Or.inr ⟨Or.inr (Or.inl hy), hyU⟩
    · exact Or.inr ⟨Or.inr (Or.inr (Or.inl hy)), hyU⟩
    · exact Or.inr ⟨Or.inr (Or.inr (Or.inr hy)), hyU⟩
  have main := aW_gen W hw (S.map (gradedSub a).val)
    (fun y hy => by
      have hy' : y ∈ a 0 := by rw [ha]; exact hy
      exact ⟨⟨y, le_iSup a 0 hy'⟩, Algebra.subset_adjoin (Or.inl hy'), rfl⟩)
    (fun s hs => by
      have hb := (aW_wts _ (hw s)).2
      refine key (W.wt s).2 (by omega) (by omega) _ ?_ (Or.inl ⟨s, rfl⟩)
      rw [← hs]
      exact W.z_mem s)
    (fun s t hs ht => by
      have hb := (aW_wts _ (hw s)).2
      have hb' := (aW_wts _ (hw t)).2
      refine key ((W.wt s).2 + (W.wt t).2) (by omega) (by omega) _ ?_ (Or.inr ⟨(s, t), rfl⟩)
      have h5 : W.z s * W.z t ∈ W.part (W.wt s + W.wt t) :=
        SetLike.GradedMul.mul_mem (W.z_mem s) (W.z_mem t)
      have h6 : W.wt s + W.wt t = (0, (W.wt s).2 + (W.wt t).2) :=
        Prod.ext (by rw [Prod.fst_add, hs, ht]; rfl) rfl
      rwa [h6] at h5)
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  have hxS : x ∈ S.map (gradedSub a).val :=
    Submodule.iSup_induction a (motive := fun x => x ∈ S.map (gradedSub a).val) hx (fun n y hy => main n y (ha n ▸ hy))
      (zero_mem _) (fun a b ha hb => add_mem ha hb)
  obtain ⟨y, hy, hxy⟩ := hxS
  obtain rfl : y = ⟨x, hx⟩ := Subtype.ext hxy
  exact hy

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D _ M _`. Establish `hz : ∀ s, M.W.z s ∈ maximalIdeal M.R` using `fun s => by`. Rewrite using `[← res_eq_zero_iff c.O, ← res_map (M.W.origin M.org), WPres.z, M.W.origin_π, MvPowerSeries.constantCoeff_X, map_zero]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `haveI := wPres_gr_zero_isCO_of_mem_maximalIdeal c.O (ℤ × ℤ) M.R M.W hz`.

Set `p : M.W.gr 0 →ₐ[c.O] M.gr 0` to `{ toFun := fun F => ⟨⟨F.1.1, M.aPart_le (n := 0) F.2⟩, F.2⟩ map_one' := rfl map_mul' := fun F G => rfl map_zero' := rfl map_add' := fun F G => rfl commutes' := fun c => rfl }`. Use `haveI : Nontrivial (M.gr 0) := ⟨⟨0, 1, fun h => zero_ne_one (α := M.R) (congrArg (fun x : M.gr 0 => ((x : M.A) : M.R)) h)⟩⟩`. Use `co_quot c.O (M.W.gr 0) (M.gr 0) p ?_` and prove the remaining obligations. Introduce and unpack `⟨⟨x, hxA⟩, hx⟩`. Conclude with `⟨⟨⟨x, M.W.part_le_A (j := 0) hx⟩, hx⟩, rfl⟩`.

Conclude with `weight_algebra_generated_degree_two M.W M.wt_mem M.aPart (fun _ => rfl)`. Introduce and unpack `j hj f ⟨g, hg, hgf⟩`. Establish `hgf' : M.W.π g = (f : M.R)` using `hgf`. Use `show M.W.origin M.org (f : M.R) = 0`. Rewrite using `[← hgf', M.W.origin_π, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`.

Conclude with `hg 0 (by rw [map_zero]; exact fun h => hj (congrArg Prod.snd h).symm)`.
-/
theorem UpperTheory.V.GradeZeroInterpolatingElement.aW :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], IsWRing M.gr M.x0 := by
  intro Ω _ _ _ l _ c D _ M _
  classical
  have hz : ∀ s, M.W.z s ∈ maximalIdeal M.R := fun s => by
    rw [← res_eq_zero_iff c.O, ← res_map (M.W.origin M.org), WPres.z, M.W.origin_π, MvPowerSeries.constantCoeff_X,
      map_zero]
  refine ⟨?_, ?_, ?_⟩
  · haveI := wPres_gr_zero_isCO_of_mem_maximalIdeal c.O (ℤ × ℤ) M.R M.W hz
    let p : M.W.gr 0 →ₐ[c.O] M.gr 0 :=
      { toFun := fun F => ⟨⟨F.1.1, M.aPart_le (n := 0) F.2⟩, F.2⟩
        map_one' := rfl
        map_mul' := fun F G => rfl
        map_zero' := rfl
        map_add' := fun F G => rfl
        commutes' := fun c => rfl }
    haveI : Nontrivial (M.gr 0) := ⟨⟨0, 1, fun h =>
      zero_ne_one (α := M.R) (congrArg (fun x : M.gr 0 => ((x : M.A) : M.R)) h)⟩⟩
    refine co_quot c.O (M.W.gr 0) (M.gr 0) p ?_
    rintro ⟨⟨x, hxA⟩, hx⟩
    exact ⟨⟨⟨x, M.W.part_le_A (j := 0) hx⟩, hx⟩, rfl⟩
  · exact weight_algebra_generated_degree_two M.W M.wt_mem M.aPart (fun _ => rfl)
  · rintro j hj f ⟨g, hg, hgf⟩
    have hgf' : M.W.π g = (f : M.R) := hgf
    show M.W.origin M.org (f : M.R) = 0
    rw [← hgf', M.W.origin_π, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hg 0 (by rw [map_zero]; exact fun h => hj (congrArg Prod.snd h).symm)

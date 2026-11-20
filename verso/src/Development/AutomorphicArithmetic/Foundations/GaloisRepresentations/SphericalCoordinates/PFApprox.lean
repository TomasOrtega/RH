import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrameEx

namespace UpperTheory.Gal.W2.FA

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Take `⟨φ, hφ⟩` from `IntermediateField.exists_algHom_of_splits (F := ℚ_[p]) (E := PadicAlgCl p) (K := PadicAlgCl p) (fun t => ⟨Algebra.IsIntegral.isIntegral t, IsAlgClosed.splits _⟩) s`. Use `⟨AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ), fun y => ?_⟩` and prove the remaining obligations. Establish `hy` using `congrArg (fun f => f y) hφ`. Simplify using `using hy`.
-/
private theorem exists_ext (L : IntermediateField ℚ_[p] (PadicAlgCl p))
    (s : L →ₐ[ℚ_[p]] PadicAlgCl p) :
    ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ∀ y : L, σ y = s y := by
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits (F := ℚ_[p]) (E := PadicAlgCl p)
    (K := PadicAlgCl p) (fun t => ⟨Algebra.IsIntegral.isIntegral t, IsAlgClosed.splits _⟩) s
  refine ⟨AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ), fun y => ?_⟩
  have hy := congrArg (fun f => f y) hφ
  simpa using hy

variable {F : Type} [Field F] {J : Type} [Fintype J]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨φ, hφ0, hφ⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)`. Establish `hφf : ∀ x : F, φ (fun i => (⟨τ i x, hm i x⟩ : L i)) = 0` using `fun x => hφ (Submodule.subset_span ⟨x, rfl⟩)`. Set `ψ : ∀ i, L i →ₗ[ℚ_[p]] ℚ_[p]` to `fun i => φ ∘ₗ LinearMap.single ℚ_[p] (fun i => L i) i`. Establish `hsum : ∀ w : (∀ i, L i), φ w = ∑ i, ψ i (w i)`.

Introduce `w`. Use `conv_lhs => rw [← Finset.univ_sum_single w]`. Rewrite using `[map_sum]`. Both sides reduce to the same expression. Establish `hrep : ∀ i, ∃ a : L i, ∀ y, ψ i y = Algebra.trace ℚ_[p] (L i) (a * y)`.

Introduce `i`. Use `⟨((Algebra.traceForm ℚ_[p] (L i)).toDual (traceForm_nondegenerate ℚ_[p] (L i))).symm (ψ i), fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[← Algebra.traceForm_apply, ← LinearMap.BilinForm.toDual_def (traceForm_nondegenerate ℚ_[p] (L i)), LinearEquiv.apply_symm_apply]`. Use `choose a ha using hrep`. Set `χ : (Σ i, (L i →ₐ[ℚ_[p]] PadicAlgCl p)) → (F →* PadicAlgCl p)` to `fun t => { toFun := fun x => t.2 ⟨τ t.1 x, hm t.1 x⟩ map_one' := by`.

Rewrite using `[show (⟨τ t.1 1, hm t.1 1⟩ : L t.1) = 1 from Subtype.ext (map_one _)]`. Conclude with `map_one _`. Use the proof step `map_mul' := fun x y => by`. Rewrite using `[show (⟨τ t.1 (x * y), hm t.1 (x * y)⟩ : L t.1) = ⟨τ t.1 x, hm t.1 x⟩ * ⟨τ t.1 y, hm t.1 y⟩ from Subtype.ext (map_mul _ _ _)]`. Conclude with `map_mul _ _ _ }`.

Establish `hχ : ∀ t x, χ t x = t.2 ⟨τ t.1 x, hm t.1 x⟩` using `fun _ _ => rfl`. Establish `hχinj : Function.Injective χ`. Introduce and unpack `⟨i, s⟩ ⟨j, s'⟩ h`. Establish `hx : ∀ x, s ⟨τ i x, hm i x⟩ = s' ⟨τ j x, hm j x⟩` using `fun x => DFunLike.congr_fun h x`. Take `⟨σ, hσ⟩` from `exists_ext (L i) s`.

Take `⟨σ', hσ'⟩` from `exists_ext (L j) s'`. Establish `key : ∀ x, σ (τ i x) = σ' (τ j x)` using `fun x => by`. Establish `h1` using `hσ ⟨τ i x, hm i x⟩`. Establish `h2` using `hσ' ⟨τ j x, hm j x⟩`. Conclude with `h1.trans ((hx x).trans h2.symm)`.

Establish `hij : i = j`. Apply `hd i j (σ.trans σ'.symm)` to reduce the goal to its premises. Use extensionality with `x`. Use `show σ'.symm (σ (τ i x)) = τ j x`. Rewrite using `[key x]`.

Conclude with `σ'.symm_apply_apply _`. Substitute `hij` using the available equality. Establish `hfix : L i ≤ IntermediateField.fixedField (Subgroup.zpowers (σ.trans σ'.symm))`. Rewrite using `[hL i, IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨x, rfl⟩`.

Rewrite using `[SetLike.mem_coe, IntermediateField.mem_fixedField_iff]`. Introduce `f hf`. Take `⟨k, rfl⟩` from `Subgroup.mem_zpowers_iff.mp hf`. Establish `h0 : (σ.trans σ'.symm) (τ i x) = τ i x` using `by show σ'.symm (σ (τ i x)) = τ i x`. Rewrite using `[key x]`.

Conclude with `σ'.symm_apply_apply _`. Establish `hpow : ∀ n : ℕ, ((σ.trans σ'.symm) ^ n) (τ i x) = τ i x`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => rfl`.

Consider the case `succ n ih`. Rewrite using `[pow_succ, AlgEquiv.mul_apply, h0, ih]`. Break down `k with n | n` into its components or cases. Simplify using `using hpow n`. Rewrite using `[zpow_negSucc]`.

Use `hpow (n + 1)` as an intermediate fact. Rewrite using `[AlgEquiv.aut_inv]`. Use `conv_lhs => rw [← this]`. Conclude with `AlgEquiv.symm_apply_apply _ _`. Establish `hss : s = s'`.

Use extensionality with `y`. Establish `hy` using `(IntermediateField.mem_fixedField_iff _ _).mp (hfix y.2) (σ.trans σ'.symm) (Subgroup.mem_zpowers _)`. Establish `hy' : σ'.symm (σ y) = y` using `hy`. Establish `hy''` using `congrArg σ' hy'`. Rewrite `hy''` using `[AlgEquiv.apply_symm_apply]`.

Rewrite using `[← hσ y, ← hσ' y]`. Conclude with `hy''`. Substitute `hss` using the available equality. Both sides reduce to the same expression. Establish `hli : LinearIndependent (PadicAlgCl p) (fun t => (χ t : F → PadicAlgCl p))` using `(linearIndependent_monoidHom F (PadicAlgCl p)).comp χ hχinj`.

Establish `hzero` using `(Fintype.linearIndependent_iff.mp hli) (fun t => t.2 (a t.1)) (by`. Use function extensionality and compare the values at `x`. Rewrite using `[Finset.sum_apply, Pi.zero_apply]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, hχ]`. Rewrite using `[Fintype.sum_sigma]`.

Establish `hi : ∀ i, ∑ s : (L i →ₐ[ℚ_[p]] PadicAlgCl p), s (a i) * s ⟨τ i x, hm i x⟩ = algebraMap ℚ_[p] (PadicAlgCl p) (ψ i ⟨τ i x, hm i x⟩)`. Introduce `i`. Rewrite using `[ha i, trace_eq_sum_embeddings]`. Simplify using `only [map_mul]`. Rewrite using `[Finset.sum_congr rfl (fun i _ => hi i), ← map_sum]`.

Use `hsum (fun i => (⟨τ i x, hm i x⟩ : L i))` as an intermediate fact. Rewrite using `[← this, hφf x, map_zero])`. Establish `ha0 : ∀ i, a i = 0`. Introduce `i`. Set `s0 : L i →ₐ[ℚ_[p]] PadicAlgCl p` to `IsAlgClosed.lift`.

Apply `(s0 : L i →+* PadicAlgCl p).injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `hzero ⟨i, s0⟩`. Apply `hφ0` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `w`. Rewrite using `[hsum w, LinearMap.zero_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[ha i, ha0 i, zero_mul, map_zero]`.
-/
private theorem span_top (τ : J → F →+* PadicAlgCl p)
    (L : J → IntermediateField ℚ_[p] (PadicAlgCl p))
    [∀ i, FiniteDimensional ℚ_[p] (L i)]
    (hL : ∀ i, L i = IntermediateField.adjoin ℚ_[p] (Set.range (τ i)))
    (hm : ∀ i x, τ i x ∈ L i)
    (hd : ∀ i j (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
      ((σ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp (τ i) = τ j →
        i = j) :
    Submodule.span ℚ_[p]
      (Set.range (fun (x : F) (i : J) => (⟨τ i x, hm i x⟩ : L i))) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hφf : ∀ x : F, φ (fun i => (⟨τ i x, hm i x⟩ : L i)) = 0 := fun x =>
    hφ (Submodule.subset_span ⟨x, rfl⟩)
  let ψ : ∀ i, L i →ₗ[ℚ_[p]] ℚ_[p] := fun i => φ ∘ₗ LinearMap.single ℚ_[p] (fun i => L i) i
  have hsum : ∀ w : (∀ i, L i), φ w = ∑ i, ψ i (w i) := by
    intro w
    conv_lhs => rw [← Finset.univ_sum_single w]
    rw [map_sum]
    rfl
  have hrep : ∀ i, ∃ a : L i, ∀ y, ψ i y = Algebra.trace ℚ_[p] (L i) (a * y) := by
    intro i
    refine ⟨((Algebra.traceForm ℚ_[p] (L i)).toDual
      (traceForm_nondegenerate ℚ_[p] (L i))).symm (ψ i), fun y => ?_⟩
    rw [← Algebra.traceForm_apply, ← LinearMap.BilinForm.toDual_def
      (traceForm_nondegenerate ℚ_[p] (L i)), LinearEquiv.apply_symm_apply]
  choose a ha using hrep
  let χ : (Σ i, (L i →ₐ[ℚ_[p]] PadicAlgCl p)) → (F →* PadicAlgCl p) := fun t =>
    { toFun := fun x => t.2 ⟨τ t.1 x, hm t.1 x⟩
      map_one' := by
        rw [show (⟨τ t.1 1, hm t.1 1⟩ : L t.1) = 1 from Subtype.ext (map_one _)]
        exact map_one _
      map_mul' := fun x y => by
        rw [show (⟨τ t.1 (x * y), hm t.1 (x * y)⟩ : L t.1) =
          ⟨τ t.1 x, hm t.1 x⟩ * ⟨τ t.1 y, hm t.1 y⟩ from Subtype.ext (map_mul _ _ _)]
        exact map_mul _ _ _ }
  have hχ : ∀ t x, χ t x = t.2 ⟨τ t.1 x, hm t.1 x⟩ := fun _ _ => rfl
  have hχinj : Function.Injective χ := by
    rintro ⟨i, s⟩ ⟨j, s'⟩ h
    have hx : ∀ x, s ⟨τ i x, hm i x⟩ = s' ⟨τ j x, hm j x⟩ := fun x => DFunLike.congr_fun h x
    obtain ⟨σ, hσ⟩ := exists_ext (L i) s
    obtain ⟨σ', hσ'⟩ := exists_ext (L j) s'
    have key : ∀ x, σ (τ i x) = σ' (τ j x) := fun x => by
      have h1 := hσ ⟨τ i x, hm i x⟩
      have h2 := hσ' ⟨τ j x, hm j x⟩
      exact h1.trans ((hx x).trans h2.symm)
    have hij : i = j := by
      apply hd i j (σ.trans σ'.symm)
      ext x
      show σ'.symm (σ (τ i x)) = τ j x
      rw [key x]
      exact σ'.symm_apply_apply _
    subst hij
    have hfix : L i ≤ IntermediateField.fixedField (Subgroup.zpowers (σ.trans σ'.symm)) := by
      rw [hL i, IntermediateField.adjoin_le_iff]
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      intro f hf
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
      have h0 : (σ.trans σ'.symm) (τ i x) = τ i x := by
        show σ'.symm (σ (τ i x)) = τ i x
        rw [key x]
        exact σ'.symm_apply_apply _
      have hpow : ∀ n : ℕ, ((σ.trans σ'.symm) ^ n) (τ i x) = τ i x := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih =>
          rw [pow_succ, AlgEquiv.mul_apply, h0, ih]
      rcases k with n | n
      · simpa using hpow n
      · rw [zpow_negSucc]
        have := hpow (n + 1)
        rw [AlgEquiv.aut_inv]
        conv_lhs => rw [← this]
        exact AlgEquiv.symm_apply_apply _ _
    have hss : s = s' := by
      ext y
      have hy := (IntermediateField.mem_fixedField_iff _ _).mp (hfix y.2) (σ.trans σ'.symm)
        (Subgroup.mem_zpowers _)
      have hy' : σ'.symm (σ y) = y := hy
      have hy'' := congrArg σ' hy'
      rw [AlgEquiv.apply_symm_apply] at hy''
      rw [← hσ y, ← hσ' y]
      exact hy''
    subst hss
    rfl
  have hli : LinearIndependent (PadicAlgCl p) (fun t => (χ t : F → PadicAlgCl p)) :=
    (linearIndependent_monoidHom F (PadicAlgCl p)).comp χ hχinj
  have hzero := (Fintype.linearIndependent_iff.mp hli) (fun t => t.2 (a t.1)) (by
    funext x
    rw [Finset.sum_apply, Pi.zero_apply]
    simp only [Pi.smul_apply, smul_eq_mul, hχ]
    rw [Fintype.sum_sigma]
    have hi : ∀ i, ∑ s : (L i →ₐ[ℚ_[p]] PadicAlgCl p), s (a i) * s ⟨τ i x, hm i x⟩ =
        algebraMap ℚ_[p] (PadicAlgCl p) (ψ i ⟨τ i x, hm i x⟩) := by
      intro i
      rw [ha i, trace_eq_sum_embeddings]
      simp only [map_mul]
    rw [Finset.sum_congr rfl (fun i _ => hi i), ← map_sum]
    have := hsum (fun i => (⟨τ i x, hm i x⟩ : L i))
    rw [← this, hφf x, map_zero])
  have ha0 : ∀ i, a i = 0 := by
    intro i
    let s0 : L i →ₐ[ℚ_[p]] PadicAlgCl p := IsAlgClosed.lift
    apply (s0 : L i →+* PadicAlgCl p).injective
    rw [map_zero]
    exact hzero ⟨i, s0⟩
  apply hφ0
  apply LinearMap.ext
  intro w
  rw [hsum w, LinearMap.zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [ha i, ha0 i, zero_mul, map_zero]

/- English proof (translation)
Establish `hm : ∀ i x, τ i x ∈ L i` using `fun i x => by`. Rewrite using `[hL i]`. Conclude with `IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩`. Establish `hspan` using `span_top τ L hL hm hd`. Establish `hv` using `(Submodule.eq_top_iff'.mp hspan) v`.

Use `revert e`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨y, rfl⟩` from `hw`. Introduce `e he`.

Use `⟨y, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[sub_self, norm_zero]`. Conclude with `he`. Consider the case `zero`. Introduce `e he`.

Use `⟨0, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero]`. Use `show ‖(0 : PadicAlgCl p) - 0‖ < e`. Rewrite using `[sub_self, norm_zero]`. Conclude with `he`.

Consider the case `add w1 w2 _ _ h1 h2`. Introduce `e he`. Take `⟨x1, hx1⟩` from `h1 (e / 2) (by linarith)`. Take `⟨x2, hx2⟩` from `h2 (e / 2) (by linarith)`. Use `⟨x1 + x2, fun i => ?_⟩` and prove the remaining obligations.

Establish `hcalc : τ i (x1 + x2) - ((w1 + w2) i : PadicAlgCl p) = (τ i x1 - (w1 i : PadicAlgCl p)) + (τ i x2 - (w2 i : PadicAlgCl p))`. Rewrite using `[map_add]`. Use `show τ i x1 + τ i x2 - ((w1 i : PadicAlgCl p) + (w2 i : PadicAlgCl p)) = _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hcalc]`.

Combine the equalities or inequalities in the displayed calculation. Consider the case `smul c w _ h`. Introduce `e he`. Use `set B : ℝ := 1 + ∑ i, ‖(w i : PadicAlgCl p)‖ with hB`. Establish `hB1 : 1 ≤ B`.

Establish `: 0 ≤ ∑ i, ‖(w i : PadicAlgCl p)‖` using `Finset.sum_nonneg (fun i _ => norm_nonneg _)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hBpos : 0 < B` using `by linarith`. Establish `hwB : ∀ i, ‖(w i : PadicAlgCl p)‖ + 1 ≤ B`. Introduce `i`.

Establish `: ‖(w i : PadicAlgCl p)‖ ≤ ∑ j, ‖(w j : PadicAlgCl p)‖` using `Finset.single_le_sum (f := fun j => ‖(w j : PadicAlgCl p)‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcpos : 0 < ‖c‖ + 1` using `by positivity`. Establish `hδpos : 0 < min 1 (e / (2 * (‖c‖ + 1)))` using `lt_min one_pos (by positivity)`. Take `⟨x, hx⟩` from `h _ hδpos`.

Take `⟨q, hq⟩` from `Padic.rat_dense p c (show 0 < e / (2 * B) by positivity)`. Use `⟨(q : F) * x, fun i => ?_⟩` and prove the remaining obligations. Establish `hτx : ‖τ i x‖ ≤ B`. Establish `h1 : ‖τ i x‖ ≤ ‖τ i x - (w i : PadicAlgCl p)‖ + ‖(w i : PadicAlgCl p)‖`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[sub_add_cancel]`. Use `_ ≤ _ := norm_add_le _ _`. Establish `h2 : ‖τ i x - (w i : PadicAlgCl p)‖ < 1` using `lt_of_lt_of_le (hx i) (min_le_left _ _)`. Combine the linear relations using `[hwB i]`. Establish `hsm : ((c • w) i : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) c * (w i : PadicAlgCl p)` using `Algebra.smul_def c (w i : PadicAlgCl p)`.

Establish `hq' : τ i ((q : F) * x) = algebraMap ℚ_[p] (PadicAlgCl p) (q : ℚ_[p]) * τ i x`. Rewrite using `[map_mul, map_ratCast, map_ratCast]`. Establish `hcalc : τ i ((q : F) * x) - ((c • w) i : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) ((q : ℚ_[p]) - c) * τ i x + algebraMap ℚ_[p] (PadicAlgCl p) c * (τ i x - (w i : PadicAlgCl p))`. Rewrite using `[hsm, hq', map_sub]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hcalc]`. Establish `hc1 : ‖algebraMap ℚ_[p] (PadicAlgCl p) ((q : ℚ_[p]) - c)‖ ≤ e / (2 * B)`. Rewrite using `[norm_algebraMap', norm_sub_rev]`. Conclude with `hq.le`. Establish `hc2 : ‖τ i x - (w i : PadicAlgCl p)‖ ≤ e / (2 * (‖c‖ + 1))` using `(lt_of_lt_of_le (hx i) (min_le_right _ _)).le`.

Establish `hk : ‖c‖ * (e / (2 * (‖c‖ + 1))) < e / 2`. Rewrite using `[show ‖c‖ * (e / (2 * (‖c‖ + 1))) = (e / 2) * (‖c‖ / (‖c‖ + 1)) by field_simp]`. Establish `: ‖c‖ / (‖c‖ + 1) < 1` using `(div_lt_one hcpos).mpr (by linarith)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hb : e / (2 * B) * B = e / 2`.

Clear the denominators using the available nonvanishing facts. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul, norm_mul, norm_algebraMap' (PadicAlgCl p) c]`. Use `_ ≤ e / (2 * B) * B + ‖c‖ * (e / (2 * (‖c‖ + 1))) := by gcongr`. Use `_ < e := by linarith`.
-/
private theorem approx (τ : J → F →+* PadicAlgCl p)
    (L : J → IntermediateField ℚ_[p] (PadicAlgCl p))
    [∀ i, FiniteDimensional ℚ_[p] (L i)]
    (hL : ∀ i, L i = IntermediateField.adjoin ℚ_[p] (Set.range (τ i)))
    (hd : ∀ i j (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
      ((σ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp (τ i) = τ j →
        i = j)
    [CharZero F] (v : ∀ i, L i) (e : ℝ) (he : 0 < e) :
    ∃ x : F, ∀ i, ‖τ i x - (v i : PadicAlgCl p)‖ < e := by
  have hm : ∀ i x, τ i x ∈ L i := fun i x => by
    rw [hL i]
    exact IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
  have hspan := span_top τ L hL hm hd
  have hv := (Submodule.eq_top_iff'.mp hspan) v
  revert e
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨y, rfl⟩ := hw
    intro e he
    refine ⟨y, fun i => ?_⟩
    rw [sub_self, norm_zero]
    exact he
  | zero =>
    intro e he
    refine ⟨0, fun i => ?_⟩
    rw [map_zero]
    show ‖(0 : PadicAlgCl p) - 0‖ < e
    rw [sub_self, norm_zero]
    exact he
  | add w1 w2 _ _ h1 h2 =>
    intro e he
    obtain ⟨x1, hx1⟩ := h1 (e / 2) (by linarith)
    obtain ⟨x2, hx2⟩ := h2 (e / 2) (by linarith)
    refine ⟨x1 + x2, fun i => ?_⟩
    have hcalc : τ i (x1 + x2) - ((w1 + w2) i : PadicAlgCl p) =
        (τ i x1 - (w1 i : PadicAlgCl p)) + (τ i x2 - (w2 i : PadicAlgCl p)) := by
      rw [map_add]
      show τ i x1 + τ i x2 - ((w1 i : PadicAlgCl p) + (w2 i : PadicAlgCl p)) = _
      ring
    rw [hcalc]
    calc _ ≤ _ := norm_add_le _ _
      _ < e / 2 + e / 2 := add_lt_add (hx1 i) (hx2 i)
      _ = e := by ring
  | smul c w _ h =>
    intro e he
    set B : ℝ := 1 + ∑ i, ‖(w i : PadicAlgCl p)‖ with hB
    have hB1 : 1 ≤ B := by
      have : 0 ≤ ∑ i, ‖(w i : PadicAlgCl p)‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
      linarith
    have hBpos : 0 < B := by linarith
    have hwB : ∀ i, ‖(w i : PadicAlgCl p)‖ + 1 ≤ B := by
      intro i
      have : ‖(w i : PadicAlgCl p)‖ ≤ ∑ j, ‖(w j : PadicAlgCl p)‖ :=
        Finset.single_le_sum (f := fun j => ‖(w j : PadicAlgCl p)‖)
          (fun j _ => norm_nonneg _) (Finset.mem_univ i)
      linarith
    have hcpos : 0 < ‖c‖ + 1 := by positivity
    have hδpos : 0 < min 1 (e / (2 * (‖c‖ + 1))) := lt_min one_pos (by positivity)
    obtain ⟨x, hx⟩ := h _ hδpos
    obtain ⟨q, hq⟩ := Padic.rat_dense p c (show 0 < e / (2 * B) by positivity)
    refine ⟨(q : F) * x, fun i => ?_⟩
    have hτx : ‖τ i x‖ ≤ B := by
      have h1 : ‖τ i x‖ ≤ ‖τ i x - (w i : PadicAlgCl p)‖ + ‖(w i : PadicAlgCl p)‖ := by
        calc ‖τ i x‖ = ‖(τ i x - (w i : PadicAlgCl p)) + (w i : PadicAlgCl p)‖ := by
              rw [sub_add_cancel]
          _ ≤ _ := norm_add_le _ _
      have h2 : ‖τ i x - (w i : PadicAlgCl p)‖ < 1 := lt_of_lt_of_le (hx i) (min_le_left _ _)
      linarith [hwB i]
    have hsm : ((c • w) i : PadicAlgCl p) =
        algebraMap ℚ_[p] (PadicAlgCl p) c * (w i : PadicAlgCl p) :=
      Algebra.smul_def c (w i : PadicAlgCl p)
    have hq' : τ i ((q : F) * x) = algebraMap ℚ_[p] (PadicAlgCl p) (q : ℚ_[p]) * τ i x := by
      rw [map_mul, map_ratCast, map_ratCast]
    have hcalc : τ i ((q : F) * x) - ((c • w) i : PadicAlgCl p) =
        algebraMap ℚ_[p] (PadicAlgCl p) ((q : ℚ_[p]) - c) * τ i x +
          algebraMap ℚ_[p] (PadicAlgCl p) c * (τ i x - (w i : PadicAlgCl p)) := by
      rw [hsm, hq', map_sub]
      ring
    rw [hcalc]
    have hc1 : ‖algebraMap ℚ_[p] (PadicAlgCl p) ((q : ℚ_[p]) - c)‖ ≤ e / (2 * B) := by
      rw [norm_algebraMap', norm_sub_rev]
      exact hq.le
    have hc2 : ‖τ i x - (w i : PadicAlgCl p)‖ ≤ e / (2 * (‖c‖ + 1)) :=
      (lt_of_lt_of_le (hx i) (min_le_right _ _)).le
    have hk : ‖c‖ * (e / (2 * (‖c‖ + 1))) < e / 2 := by
      rw [show ‖c‖ * (e / (2 * (‖c‖ + 1))) = (e / 2) * (‖c‖ / (‖c‖ + 1)) by
        field_simp]
      have : ‖c‖ / (‖c‖ + 1) < 1 := (div_lt_one hcpos).mpr (by linarith)
      nlinarith
    have hb : e / (2 * B) * B = e / 2 := by
      field_simp
    calc _ ≤ ‖algebraMap ℚ_[p] (PadicAlgCl p) ((q : ℚ_[p]) - c) * τ i x‖ +
          ‖algebraMap ℚ_[p] (PadicAlgCl p) c * (τ i x - (w i : PadicAlgCl p))‖ := norm_add_le _ _
      _ = ‖algebraMap ℚ_[p] (PadicAlgCl p) ((q : ℚ_[p]) - c)‖ * ‖τ i x‖ +
          ‖c‖ * ‖τ i x - (w i : PadicAlgCl p)‖ := by
        rw [norm_mul, norm_mul, norm_algebraMap' (PadicAlgCl p) c]
      _ ≤ e / (2 * B) * B + ‖c‖ * (e / (2 * (‖c‖ + 1))) := by
        gcongr
      _ < e := by linarith

end UpperTheory.Gal.W2.FA

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

/- English proof (translation)
Set `φ : G.F →+* ℂ` to `Classical.choice (inferInstance : Nonempty (G.F →+* ℂ))`. Take `⟨x, hx, him⟩` from `G.hKq.2 φ`. Use `⟨⟨x, hx⟩, fun h => him ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg φ h`. Rewrite `h2` using `[IsCMField.complexEmbedding_complexConj]`.

Conclude with `Complex.conj_eq_iff_im.mp h2`.
-/
private theorem conj_ne {p : ℕ} [Fact p.Prime] (G : HTGroup p) :
    ∃ x : G.Kq, IsCMField.complexConj G.F (x : G.F) ≠ x := by
  let φ : G.F →+* ℂ := Classical.choice (inferInstance : Nonempty (G.F →+* ℂ))
  obtain ⟨x, hx, him⟩ := G.hKq.2 φ
  refine ⟨⟨x, hx⟩, fun h => him ?_⟩
  have h2 := congrArg φ h
  rw [IsCMField.complexEmbedding_complexConj] at h2
  exact Complex.conj_eq_iff_im.mp h2

/- English proof (translation)
Take `⟨x, hx⟩` from `conj_ne G`. Apply `hx` to reduce the goal to its premises. Apply `(G.emb w').injective` to reduce the goal to its premises. Rewrite using `[← h, G.emb_over w x, G.emb_over w' x]`. Conclude with `σ.commutes _`.
-/
private theorem no_cross {p : ℕ} [Fact p.Prime] (G : HTGroup p) (w w' : Fin G.m)
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (h : ∀ x, σ (G.emb w x) = G.emb w' (IsCMField.complexConj G.F x)) : False := by
  obtain ⟨x, hx⟩ := conj_ne G
  apply hx
  apply (G.emb w').injective
  rw [← h, G.emb_over w x, G.emb_over w' x]
  exact σ.commutes _

/- English proof (translation)
Introduce `_ p _ G a b e he`. Set `c : G.F →+* G.F` to `(IsCMField.complexConj G.F).toRingEquiv.toRingHom`. Establish `hcc : ∀ x, c (c x) = x` using `fun x => IsCMField.complexConj_apply_apply G.F x`. Set `τ : Fin G.m ⊕ Fin G.m → G.F →+* PadicAlgCl p` to `fun j => Sum.elim (fun w => G.emb w) (fun w => (G.emb w).comp c) j`. Set `L : Fin G.m ⊕ Fin G.m → IntermediateField ℚ_[p] (PadicAlgCl p)` to `fun j => G.Fw (Sum.elim id id j)`.

Use `haveI : ∀ j, FiniteDimensional ℚ_[p] (L j) := fun j => G.finiteDimensional_Fw _`. Establish `hL : ∀ j, L j = IntermediateField.adjoin ℚ_[p] (Set.range (τ j))`. Introduce `j`. Break down `j with w | w` into its components or cases. Both sides reduce to the same expression.

Use `show IntermediateField.adjoin ℚ_[p] (Set.range (G.emb w)) = _`. Use `congr 1`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`.

Conclude with `⟨c x, by simp only [τ, Sum.elim_inr, RingHom.comp_apply, hcc]⟩`. Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨c x, rfl⟩`. Establish `hd : ∀ i j (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), ((σ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp (τ i) = τ j → i = j`. Introduce `i j σ h`.

Establish `hx : ∀ x, σ (τ i x) = τ j x` using `fun x => congrArg (fun f => f x) h`. Apply the tactic sequence `rcases i with u | u <;> rcases j with v | v`. Establish `h' : (↑σ.toRingEquiv : PadicAlgCl p →+* PadicAlgCl p).comp (G.emb u) = G.emb v`. Use extensionality with `x`. Conclude with `hx x`.

Conclude with `congrArg _ (G.emb_inj u v σ h')`. Conclude with `(no_cross G u v σ fun x => hx x).elim`. Use `(no_cross G v u σ.symm fun x => ?_).elim` and prove the remaining obligations. Use `hx x` as an intermediate fact. Simplify using `only [τ, Sum.elim_inl, Sum.elim_inr, RingHom.comp_apply] at this`.

Rewrite using `[← this]`. Simplify using `[c]`. Establish `h' : (↑σ.toRingEquiv : PadicAlgCl p →+* PadicAlgCl p).comp (G.emb u) = G.emb v`. Use extensionality with `x`. Use `hx (c x)` as an intermediate fact.

Simplify using `only [τ, Sum.elim_inr, RingHom.comp_apply, hcc] at this`. Conclude with `this`. Conclude with `congrArg _ (G.emb_inj u v σ h')`. Set `v : ∀ j, L j` to `fun j => match j with`. Consider the case `Sum.inl w => a w`.

Consider the case `Sum.inr w => b w`. Take `⟨x, hx⟩` from `UpperTheory.Gal.W2.FA.approx τ L hL hd v e he`. Conclude with `⟨x, fun w => ⟨hx (Sum.inl w), hx (Sum.inr w)⟩⟩`.
-/
theorem UpperTheory.Gal.W2.fApprox_of :
    UpperTheory.Gal.W2.EmbAll → UpperTheory.Gal.W2.FApprox := by
  intro _ p _ G a b e he
  let c : G.F →+* G.F := (IsCMField.complexConj G.F).toRingEquiv.toRingHom
  have hcc : ∀ x, c (c x) = x := fun x => IsCMField.complexConj_apply_apply G.F x
  let τ : Fin G.m ⊕ Fin G.m → G.F →+* PadicAlgCl p :=
    fun j => Sum.elim (fun w => G.emb w) (fun w => (G.emb w).comp c) j
  let L : Fin G.m ⊕ Fin G.m → IntermediateField ℚ_[p] (PadicAlgCl p) :=
    fun j => G.Fw (Sum.elim id id j)
  haveI : ∀ j, FiniteDimensional ℚ_[p] (L j) := fun j => G.finiteDimensional_Fw _
  have hL : ∀ j, L j = IntermediateField.adjoin ℚ_[p] (Set.range (τ j)) := by
    intro j
    rcases j with w | w
    · rfl
    · show IntermediateField.adjoin ℚ_[p] (Set.range (G.emb w)) = _
      congr 1
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨c x, by simp only [τ, Sum.elim_inr, RingHom.comp_apply, hcc]⟩
      · rintro ⟨x, rfl⟩
        exact ⟨c x, rfl⟩
  have hd : ∀ i j (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
      ((σ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp (τ i) = τ j →
        i = j := by
    intro i j σ h
    have hx : ∀ x, σ (τ i x) = τ j x := fun x => congrArg (fun f => f x) h
    rcases i with u | u <;> rcases j with v | v
    · have h' : (↑σ.toRingEquiv : PadicAlgCl p →+* PadicAlgCl p).comp (G.emb u) = G.emb v := by
        ext x
        exact hx x
      exact congrArg _ (G.emb_inj u v σ h')
    · exact (no_cross G u v σ fun x => hx x).elim
    · refine (no_cross G v u σ.symm fun x => ?_).elim
      have := hx x
      simp only [τ, Sum.elim_inl, Sum.elim_inr, RingHom.comp_apply] at this
      rw [← this]
      simp [c]
    · have h' : (↑σ.toRingEquiv : PadicAlgCl p →+* PadicAlgCl p).comp (G.emb u) = G.emb v := by
        ext x
        have := hx (c x)
        simp only [τ, Sum.elim_inr, RingHom.comp_apply, hcc] at this
        exact this
      exact congrArg _ (G.emb_inj u v σ h')
  let v : ∀ j, L j := fun j => match j with
    | Sum.inl w => a w
    | Sum.inr w => b w
  obtain ⟨x, hx⟩ := UpperTheory.Gal.W2.FA.approx τ L hL hd v e he
  exact ⟨x, fun w => ⟨hx (Sum.inl w), hx (Sum.inr w)⟩⟩

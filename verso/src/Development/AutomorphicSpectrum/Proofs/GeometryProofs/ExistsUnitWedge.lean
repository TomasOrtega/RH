import Mathlib

namespace GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame

/- English proof (translation)
Establish `hA : (exteriorPower.ιMulti K n).compLinearMap (Fintype.linearCombination K z) = (Matrix.detRowAlternating : (Fin n → K) [⋀^Fin n]→ₗ[K] K).smulRight (exteriorPower.ιMulti K n z)`. Use `(Pi.basisFun K (Fin n)).ext_alternating fun u hu => ?_` and prove the remaining obligations. Set `s : Equiv.Perm (Fin n)` to `Equiv.ofBijective u (Finite.injective_iff_bijective.1 hu)`. Establish `e : (fun i => Pi.basisFun K (Fin n) (u i)) = (fun i => Pi.basisFun K (Fin n) i) ∘ s` using `rfl`. Rewrite using `[e, AlternatingMap.map_perm, AlternatingMap.map_perm]`.

Use `congr 1`. Establish `e1 : (Matrix.detRowAlternating : (Fin n → K) [⋀^Fin n]→ₗ[K] K) (fun i => Pi.basisFun K (Fin n) i) = 1`. Express the relevant statement in the definitionally equal form `Matrix.det (Matrix.of fun i => Pi.basisFun K (Fin n) i) = 1`. Rewrite using `[show (Matrix.of fun i => Pi.basisFun K (Fin n) i) = 1 from by`. Use extensionality with `i j`.

Simplify using `[Matrix.one_apply, Pi.single_apply, eq_comm], Matrix.det_one]`. Rewrite using `[AlternatingMap.smulRight_apply, e1, one_smul, AlternatingMap.compLinearMap_apply]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Conclude with `AlternatingMap.congr_fun hA M`.
-/
theorem wedge_rows {K V : Type} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (z : Fin n → V) :
    exteriorPower.ιMulti K n (fun i => ∑ j, M i j • z j) = M.det • exteriorPower.ιMulti K n z := by
  have hA : (exteriorPower.ιMulti K n).compLinearMap (Fintype.linearCombination K z) =
      (Matrix.detRowAlternating : (Fin n → K) [⋀^Fin n]→ₗ[K] K).smulRight
        (exteriorPower.ιMulti K n z) := by
    refine (Pi.basisFun K (Fin n)).ext_alternating fun u hu => ?_
    let s : Equiv.Perm (Fin n) := Equiv.ofBijective u (Finite.injective_iff_bijective.1 hu)
    have e : (fun i => Pi.basisFun K (Fin n) (u i)) = (fun i => Pi.basisFun K (Fin n) i) ∘ s := rfl
    rw [e, AlternatingMap.map_perm, AlternatingMap.map_perm]
    congr 1
    have e1 : (Matrix.detRowAlternating : (Fin n → K) [⋀^Fin n]→ₗ[K] K)
        (fun i => Pi.basisFun K (Fin n) i) = 1 := by
      change Matrix.det (Matrix.of fun i => Pi.basisFun K (Fin n) i) = 1
      rw [show (Matrix.of fun i => Pi.basisFun K (Fin n) i) = 1 from by
        ext i j; simp [Matrix.one_apply, Pi.single_apply, eq_comm], Matrix.det_one]
    rw [AlternatingMap.smulRight_apply, e1, one_smul, AlternatingMap.compLinearMap_apply]
    congr 1
    funext i
    simp
  exact AlternatingMap.congr_fun hA M

/- English proof (translation)
Establish `hfam` using `exteriorPower.ιMulti_family_linearIndependent_field (n := n) hv`. Set `s` to `Set.powersetCard.ofFinEmbEquiv (OrderIso.refl (Fin n)).toOrderEmbedding`. Establish `hs : exteriorPower.ιMulti_family Ω n v s = exteriorPower.ιMulti Ω n v`. Simplify using `only [exteriorPower.ιMulti_family, s, Equiv.symm_apply_apply]`. Both sides reduce to the same expression.

Conclude with `hs ▸ hfam.ne_zero s`.
-/
theorem wedge_ne_zero {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V]
    {n : ℕ} (v : Fin n → V) (hv : LinearIndependent Ω v) : exteriorPower.ιMulti Ω n v ≠ 0 := by
  have hfam := exteriorPower.ιMulti_family_linearIndependent_field (n := n) hv
  let s := Set.powersetCard.ofFinEmbEquiv (OrderIso.refl (Fin n)).toOrderEmbedding
  have hs : exteriorPower.ιMulti_family Ω n v s = exteriorPower.ιMulti Ω n v := by
    simp only [exteriorPower.ιMulti_family, s, Equiv.symm_apply_apply]
    rfl
  exact hs ▸ hfam.ne_zero s

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Set `N : Submodule R (⋀[Ω]^p E)` to `Submodule.map (LinearMap.toSpanSingleton R (⋀[Ω]^p E) ω) (IsLocalRing.maximalIdeal R)`. Establish `hle : Submodule.span R {w : ⋀[Ω]^p E | ∃ b : Fin p → E, (∀ i, b i ∈ A) ∧ w = exteriorPower.ιMulti Ω p b} ≤ N`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `w ⟨b, hb, rfl⟩`. Establish `hmem : exteriorPower.ιMulti Ω p b ∈ Submodule.span R {ω}` using `H ▸ Submodule.subset_span ⟨b, hb, rfl⟩`. Take `⟨r, hr⟩` from `Submodule.mem_span_singleton.1 hmem`. Establish `hnu : ¬ IsUnit r` using `fun hu => hcon b r hb hu hr.symm`. Conclude with `⟨r, (IsLocalRing.mem_maximalIdeal r).2 hnu, by simpa using hr⟩`.

Establish `hωN : ω ∈ N` using `hle (H ▸ Submodule.mem_span_singleton_self ω)`. Take `⟨r, hr, hrω⟩` from `hωN`. Establish `hrω' : (r : Ω) • ω = ω` using `hrω`. Establish `h1 : (r : Ω) = 1`. Establish `h0 : ((r : Ω) - 1) • ω = 0` using `by rw [sub_smul, one_smul, hrω', sub_self]`.

Break down `smul_eq_zero.1 h0 with h | h` into its components or cases. Conclude with `sub_eq_zero.1 h`. Conclude with `absurd h hω`. Establish `hr1 : r = 1` using `Subtype.ext h1`. Rewrite `hr` using `[hr1]`.

Conclude with `((IsLocalRing.mem_maximalIdeal (1 : R)).1 hr) isUnit_one`.
-/
theorem exists_unit_wedge {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] (R : Subring Ω)
    [IsLocalRing R] (A : Submodule R E) (p : ℕ) (ω : ⋀[Ω]^p E) (hω : ω ≠ 0)
    (H : Submodule.span R {w : ⋀[Ω]^p E | ∃ b : Fin p → E, (∀ i, b i ∈ A) ∧
      w = exteriorPower.ιMulti Ω p b} = Submodule.span R {ω}) :
    ∃ (b : Fin p → E) (r : R), (∀ i, b i ∈ A) ∧ IsUnit r ∧
      exteriorPower.ιMulti Ω p b = (r : Ω) • ω := by
  by_contra hcon
  push_neg at hcon
  let N : Submodule R (⋀[Ω]^p E) :=
    Submodule.map (LinearMap.toSpanSingleton R (⋀[Ω]^p E) ω) (IsLocalRing.maximalIdeal R)
  have hle : Submodule.span R {w : ⋀[Ω]^p E | ∃ b : Fin p → E, (∀ i, b i ∈ A) ∧
      w = exteriorPower.ιMulti Ω p b} ≤ N := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨b, hb, rfl⟩
    have hmem : exteriorPower.ιMulti Ω p b ∈ Submodule.span R {ω} :=
      H ▸ Submodule.subset_span ⟨b, hb, rfl⟩
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hmem
    have hnu : ¬ IsUnit r := fun hu => hcon b r hb hu hr.symm
    exact ⟨r, (IsLocalRing.mem_maximalIdeal r).2 hnu, by simpa using hr⟩
  have hωN : ω ∈ N := hle (H ▸ Submodule.mem_span_singleton_self ω)
  obtain ⟨r, hr, hrω⟩ := hωN
  have hrω' : (r : Ω) • ω = ω := hrω
  have h1 : (r : Ω) = 1 := by
    have h0 : ((r : Ω) - 1) • ω = 0 := by rw [sub_smul, one_smul, hrω', sub_self]
    rcases smul_eq_zero.1 h0 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hω
  have hr1 : r = 1 := Subtype.ext h1
  rw [hr1] at hr
  exact ((IsLocalRing.mem_maximalIdeal (1 : R)).1 hr) isUnit_one

/- English proof (translation)
Rewrite using `[AlternatingMap.map_update_sum, Finset.sum_eq_single j]`. Rewrite using `[AlternatingMap.map_update_smul, Function.update_eq_self]`. Introduce `k _ hk`. Rewrite using `[AlternatingMap.map_update_smul, AlternatingMap.map_update_self _ _ hk.symm, smul_zero]`. Simplify using the standard rewrite rules.
-/
theorem wedge_update_sum {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {p : ℕ}
    (b : Fin p → E) (c : Fin p → Ω) (j : Fin p) :
    exteriorPower.ιMulti Ω p (Function.update b j (∑ k, c k • b k)) =
      c j • exteriorPower.ιMulti Ω p b := by
  rw [AlternatingMap.map_update_sum, Finset.sum_eq_single j]
  · rw [AlternatingMap.map_update_smul, Function.update_eq_self]
  · intro k _ hk
    rw [AlternatingMap.map_update_smul, AlternatingMap.map_update_self _ _ hk.symm, smul_zero]
  · simp

/- English proof (translation)
Introduce `Ω E _ _ _ R _ A p v α hv hA hα H`. Establish `hιv` using `wedge_ne_zero v hv`. Establish `hω : α • exteriorPower.ιMulti Ω p v ≠ 0` using `smul_ne_zero hα hιv`. Take `⟨b, r, hb, hu, hιb⟩` from `exists_unit_wedge R A p _ hω H`. Take `⟨u, rfl⟩` from `hu`.

Establish `hc0 : ((u : R) : Ω) ≠ 0`. Introduce `h0`. Conclude with `u.ne_zero (Subtype.ext h0)`. Establish `hcinv : ((u : R) : Ω)⁻¹ = (((u⁻¹ : Rˣ) : R) : Ω)`. Establish `h : ((u : R) : Ω) * (((u⁻¹ : Rˣ) : R) : Ω) = 1`.

Rewrite using `[← Subring.coe_mul, Units.mul_inv]`. Both sides reduce to the same expression. Conclude with `(eq_inv_of_mul_eq_one_right h).symm`. Establish `hιb0 : exteriorPower.ιMulti Ω p b ≠ 0`. Rewrite using `[hιb]`.

Conclude with `smul_ne_zero hc0 hω`. Establish `hbli : LinearIndependent Ω b`. Assume the negation of the conclusion as `hnot`. Conclude with `hιb0 (AlternatingMap.map_linearDependent _ _ hnot)`. Establish `hex : ∀ i, ∃ c : Fin p → Ω, ∑ j, c j • v j = b i` using `fun i => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hA _ (hb i))`.

Take `⟨P, hP⟩ : ∃ P : Matrix (Fin p) (Fin p) Ω, ∀ i, ∑ j, P i j • v j = b i` from `⟨Matrix.of fun i => (hex i).choose, fun i => (hex i).choose_spec⟩`. Establish `hPb : (fun i => ∑ j, P i j • v j) = b` using `funext hP`. Establish `hdet : P.det = ((u : R) : Ω) * α`. Establish `h1` using `wedge_rows P v`. Rewrite `h1` using `[hPb, hιb, smul_smul]`.

Conclude with `(smul_left_injective Ω hιv h1).symm`. Use `⟨P, ?_, ?_, (u : R), (u : R).2, hcinv ▸ ((u⁻¹ : Rˣ) : R).2, hc0, hdet⟩` and prove the remaining obligations. Rewrite using `[hPb]`. Conclude with `hbli`. Rewrite using `[hPb]`.

Use `le_antisymm ?_ (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce `y hy`. Establish `hspan : Submodule.span Ω (Set.range b) = Submodule.span Ω (Set.range v)` using `by haveI : FiniteDimensional Ω (Submodule.span Ω (Set.range v)) := FiniteDimensional.span_of_finite Ω (Set.finite_range v)`. Use `Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `hA _ (hb i)`. Rewrite using `[finrank_span_eq_card hbli, finrank_span_eq_card hv]`. Establish `hy' : y ∈ Submodule.span Ω (Set.range b)` using `hspan ▸ hA y hy`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun Ω).1 hy'`. Establish `hcR : ∀ j, c j ∈ R`.

Introduce `j`. Establish `hmem : exteriorPower.ιMulti Ω p (Function.update b j y) ∈ Submodule.span R {α • exteriorPower.ιMulti Ω p v}`. Rewrite using `[← H]`. Use `Submodule.subset_span ⟨_, fun i => ?_, rfl⟩` and prove the remaining obligations. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using `using hy`. Simplify `hb i` using `[Function.update_of_ne hij]`. Take `⟨s, hs⟩` from `Submodule.mem_span_singleton.1 hmem`. Rewrite `hs` using `[← hc, wedge_update_sum, hιb]`.

Establish `hs' : (s : Ω) • (α • exteriorPower.ιMulti Ω p v) = (c j * ((u : R) : Ω)) • (α • exteriorPower.ιMulti Ω p v)`. Rewrite using `[mul_smul]`. Conclude with `hs`. Establish `hsc : (s : Ω) = c j * ((u : R) : Ω)` using `smul_left_injective Ω hω hs'`. Establish `hcj : c j = (s : Ω) * (((u⁻¹ : Rˣ) : R) : Ω)`.

Rewrite using `[← hcinv, hsc, mul_assoc, mul_inv_cancel₀ hc0, mul_one]`. Rewrite using `[hcj]`. Conclude with `R.mul_mem s.2 ((u⁻¹ : Rˣ) : R).2`. Rewrite using `[← hc]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations.

Establish `: c j • b j = (⟨c j, hcR j⟩ : R) • b j` using `rfl`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hb i`.
-/
theorem wedge_frame : ∀ (Ω E : Type) [Field Ω] [AddCommGroup E] [Module Ω E] (R : Subring Ω)
    [IsLocalRing R] (A : Submodule R E) (p : ℕ) (v : Fin p → E) (α : Ω),
    LinearIndependent Ω v → (∀ y ∈ A, y ∈ Submodule.span Ω (Set.range v)) → α ≠ 0 →
    Submodule.span R {w : ⋀[Ω]^p E | ∃ b : Fin p → E, (∀ i, b i ∈ A) ∧
      w = exteriorPower.ιMulti Ω p b} = Submodule.span R {α • exteriorPower.ιMulti Ω p v} →
    ∃ P : Matrix (Fin p) (Fin p) Ω, LinearIndependent Ω (fun i => ∑ j, P i j • v j) ∧
      A = Submodule.span R (Set.range fun i => ∑ j, P i j • v j) ∧
      ∃ c : Ω, c ∈ R ∧ c⁻¹ ∈ R ∧ c ≠ 0 ∧ P.det = c * α := by
  intro Ω E _ _ _ R _ A p v α hv hA hα H
  have hιv := wedge_ne_zero v hv
  have hω : α • exteriorPower.ιMulti Ω p v ≠ 0 := smul_ne_zero hα hιv
  obtain ⟨b, r, hb, hu, hιb⟩ := exists_unit_wedge R A p _ hω H
  obtain ⟨u, rfl⟩ := hu
  have hc0 : ((u : R) : Ω) ≠ 0 := by
    intro h0
    exact u.ne_zero (Subtype.ext h0)
  have hcinv : ((u : R) : Ω)⁻¹ = (((u⁻¹ : Rˣ) : R) : Ω) := by
    have h : ((u : R) : Ω) * (((u⁻¹ : Rˣ) : R) : Ω) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]; rfl
    exact (eq_inv_of_mul_eq_one_right h).symm
  have hιb0 : exteriorPower.ιMulti Ω p b ≠ 0 := by
    rw [hιb]; exact smul_ne_zero hc0 hω
  have hbli : LinearIndependent Ω b := by
    by_contra hnot
    exact hιb0 (AlternatingMap.map_linearDependent _ _ hnot)
  have hex : ∀ i, ∃ c : Fin p → Ω, ∑ j, c j • v j = b i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (hA _ (hb i))
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin p) (Fin p) Ω, ∀ i, ∑ j, P i j • v j = b i :=
    ⟨Matrix.of fun i => (hex i).choose, fun i => (hex i).choose_spec⟩
  have hPb : (fun i => ∑ j, P i j • v j) = b := funext hP
  have hdet : P.det = ((u : R) : Ω) * α := by
    have h1 := wedge_rows P v
    rw [hPb, hιb, smul_smul] at h1
    exact (smul_left_injective Ω hιv h1).symm
  refine ⟨P, ?_, ?_, (u : R), (u : R).2, hcinv ▸ ((u⁻¹ : Rˣ) : R).2, hc0, hdet⟩
  · rw [hPb]; exact hbli
  · rw [hPb]
    refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · intro y hy
      have hspan : Submodule.span Ω (Set.range b) = Submodule.span Ω (Set.range v) := by
        haveI : FiniteDimensional Ω (Submodule.span Ω (Set.range v)) :=
          FiniteDimensional.span_of_finite Ω (Set.finite_range v)
        refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
        · rintro _ ⟨i, rfl⟩
          exact hA _ (hb i)
        · rw [finrank_span_eq_card hbli, finrank_span_eq_card hv]
      have hy' : y ∈ Submodule.span Ω (Set.range b) := hspan ▸ hA y hy
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 hy'
      have hcR : ∀ j, c j ∈ R := by
        intro j
        have hmem : exteriorPower.ιMulti Ω p (Function.update b j y) ∈
            Submodule.span R {α • exteriorPower.ιMulti Ω p v} := by
          rw [← H]
          refine Submodule.subset_span ⟨_, fun i => ?_, rfl⟩
          by_cases hij : i = j
          · subst hij; simpa using hy
          · simpa [Function.update_of_ne hij] using hb i
        obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 hmem
        rw [← hc, wedge_update_sum, hιb] at hs
        have hs' : (s : Ω) • (α • exteriorPower.ιMulti Ω p v) =
            (c j * ((u : R) : Ω)) • (α • exteriorPower.ιMulti Ω p v) := by
          rw [mul_smul]; exact hs
        have hsc : (s : Ω) = c j * ((u : R) : Ω) := smul_left_injective Ω hω hs'
        have hcj : c j = (s : Ω) * (((u⁻¹ : Rˣ) : R) : Ω) := by
          rw [← hcinv, hsc, mul_assoc, mul_inv_cancel₀ hc0, mul_one]
        rw [hcj]
        exact R.mul_mem s.2 ((u⁻¹ : Rˣ) : R).2
      rw [← hc]
      refine Submodule.sum_mem _ fun j _ => ?_
      have : c j • b j = (⟨c j, hcR j⟩ : R) • b j := rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · rintro _ ⟨i, rfl⟩
      exact hb i

end GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame

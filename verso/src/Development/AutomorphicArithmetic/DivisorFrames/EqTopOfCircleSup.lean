import Mathlib
open Filter Topology

/- English proof (translation)
Introduce `G _ _ _ M hM hμ c hc hsup`. Set `S : AddSubgroup ℝ` to `{ carrier := {t | c (Circle.exp t) ∈ M} zero_mem' := by simp add_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq, Circle.exp_add, map_mul] at *`. Conclude with `M.mul_mem ha hb`.

Use the proof step `neg_mem' := by`. Introduce `a ha`. Simplify using `only [Set.mem_setOf_eq, Circle.exp_neg, map_inv] at *`. Conclude with `M.inv_mem ha }`. Establish `hSmem : ∀ t, t ∈ S ↔ c (Circle.exp t) ∈ M` using `fun t => Iff.rfl`.

Establish `hScl : IsClosed (S : Set ℝ)` using `hM.preimage (hc.comp Circle.exp.continuous)`. Break down `S.dense_or_cyclic with hd | ⟨a, ha⟩` into its components or cases. Establish `hall : (S : Set ℝ) = Set.univ` using `by rw [← hScl.closure_eq, hd.closure_eq]`. Rewrite using `[← hsup]`. Use `(sup_eq_left.2 ?_).symm` and prove the remaining obligations.

Introduce and unpack `_ ⟨z, rfl⟩`. Take `⟨t, rfl⟩` from `Circle.exp_surjective z`. Establish `: t ∈ (S : Set ℝ)` using `by rw [hall]; trivial`. Conclude with `this`. It suffices to derive a contradiction.

Establish `h2 : (2 * Real.pi) ∈ S` using `by rw [hSmem]; simp`. Rewrite `h2` using `[ha, AddSubgroup.mem_closure_singleton]`. Take `⟨n, hn⟩` from `h2`. Establish `hn0 : n ≠ 0`. Introduce and unpack `rfl`.

Simplify using `only [zero_smul] at hn`. Use `Real.pi_pos` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `haveI : IsClosed (M : Set G) := hM`. Set `f : Circle →* G ⧸ M` to `(QuotientGroup.mk' M).comp c`.

Establish `hfc : Continuous f` using `QuotientGroup.continuous_mk.comp hc`. Establish `hfs : Function.Surjective f`. Introduce `q`. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective q`. Establish `hg : g ∈ M ⊔ c.range` using `by rw [hsup]; trivial`.

Take `⟨m, hm, _, ⟨z, rfl⟩, rfl⟩` from `Subgroup.mem_sup.1 hg`. Use `⟨z, ?_⟩` and prove the remaining obligations. Simplify using `[f, (QuotientGroup.eq_one_iff m).2 hm]`. Establish `hq : IsQuotientMap f` using `hfc.isClosedMap.isQuotientMap hfc hfs`. Establish `hker : f.ker ≤ (zpowGroupHom n : Circle →* Circle).ker`.

Introduce `z hz`. Take `⟨t, rfl⟩` from `Circle.exp_surjective z`. Establish `ht : t ∈ S`. Rewrite using `[hSmem]`. Conclude with `(QuotientGroup.eq_one_iff _).1 hz`.

Rewrite `ht` using `[ha, AddSubgroup.mem_closure_singleton]`. Take `⟨k, rfl⟩` from `ht`. Rewrite using `[MonoidHom.mem_ker, zpowGroupHom_apply, ← Circle.exp_intCast_mul, Circle.exp_eq_one]`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[← hn]`.

Simplify using `only [zsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Set `φ : G ⧸ M →* Circle` to `f.liftOfSurjective hfs ⟨zpowGroupHom n, hker⟩`. Establish `hφ : ∀ z, φ (f z) = z ^ n` using `fun z => f.liftOfRightInverse_comp_apply _ _ _ z`. Establish `hφc : Continuous φ`.

Rewrite using `[hq.continuous_iff]`. Establish `: (φ ∘ f) = fun z => z ^ n` using `funext hφ`. Rewrite using `[this]`. Conclude with `continuous_zpow n`. Establish `h1` using `hμ (φ.comp (QuotientGroup.mk' M)) (hφc.comp QuotientGroup.continuous_mk) (by`.

Introduce `m hm`. Simplify using `[(QuotientGroup.eq_one_iff m).2 hm])`. Establish `h3 : (Circle.exp (Real.pi / n)) ^ n = 1`. Rewrite using `[← hφ]`. Conclude with `DFunLike.congr_fun h1 (c (Circle.exp (Real.pi / n)))`.

Establish `hn' : (n : ℝ) ≠ 0` using `by exact_mod_cast hn0`. Rewrite `h3` using `[← Circle.exp_intCast_mul, mul_div_cancel₀ _ hn']`. Conclude with `Circle.exp_pi_ne_one h3`.
-/
theorem UpperTheory.eq_top_of_circle_sup :
    ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] (M : Subgroup G), IsClosed (M : Set G) →
        (∀ μ : G →* Circle, Continuous μ → (∀ m ∈ M, μ m = 1) → μ = 1) →
        ∀ c : Circle →* G, Continuous c → M ⊔ c.range = ⊤ → M = ⊤ := by
  intro G _ _ _ M hM hμ c hc hsup
  let S : AddSubgroup ℝ :=
    { carrier := {t | c (Circle.exp t) ∈ M}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, Circle.exp_add, map_mul] at *
        exact M.mul_mem ha hb
      neg_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq, Circle.exp_neg, map_inv] at *
        exact M.inv_mem ha }
  have hSmem : ∀ t, t ∈ S ↔ c (Circle.exp t) ∈ M := fun t => Iff.rfl
  have hScl : IsClosed (S : Set ℝ) := hM.preimage (hc.comp Circle.exp.continuous)
  rcases S.dense_or_cyclic with hd | ⟨a, ha⟩
  · have hall : (S : Set ℝ) = Set.univ := by rw [← hScl.closure_eq, hd.closure_eq]
    rw [← hsup]
    refine (sup_eq_left.2 ?_).symm
    rintro _ ⟨z, rfl⟩
    obtain ⟨t, rfl⟩ := Circle.exp_surjective z
    have : t ∈ (S : Set ℝ) := by rw [hall]; trivial
    exact this
  · exfalso
    have h2 : (2 * Real.pi) ∈ S := by rw [hSmem]; simp
    rw [ha, AddSubgroup.mem_closure_singleton] at h2
    obtain ⟨n, hn⟩ := h2
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp only [zero_smul] at hn
      have := Real.pi_pos
      linarith
    haveI : IsClosed (M : Set G) := hM
    let f : Circle →* G ⧸ M := (QuotientGroup.mk' M).comp c
    have hfc : Continuous f := QuotientGroup.continuous_mk.comp hc
    have hfs : Function.Surjective f := by
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      have hg : g ∈ M ⊔ c.range := by rw [hsup]; trivial
      obtain ⟨m, hm, _, ⟨z, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hg
      refine ⟨z, ?_⟩
      simp [f, (QuotientGroup.eq_one_iff m).2 hm]
    have hq : IsQuotientMap f := hfc.isClosedMap.isQuotientMap hfc hfs
    have hker : f.ker ≤ (zpowGroupHom n : Circle →* Circle).ker := by
      intro z hz
      obtain ⟨t, rfl⟩ := Circle.exp_surjective z
      have ht : t ∈ S := by
        rw [hSmem]
        exact (QuotientGroup.eq_one_iff _).1 hz
      rw [ha, AddSubgroup.mem_closure_singleton] at ht
      obtain ⟨k, rfl⟩ := ht
      rw [MonoidHom.mem_ker, zpowGroupHom_apply, ← Circle.exp_intCast_mul, Circle.exp_eq_one]
      refine ⟨k, ?_⟩
      rw [← hn]
      simp only [zsmul_eq_mul]
      ring
    let φ : G ⧸ M →* Circle := f.liftOfSurjective hfs ⟨zpowGroupHom n, hker⟩
    have hφ : ∀ z, φ (f z) = z ^ n := fun z =>
      f.liftOfRightInverse_comp_apply _ _ _ z
    have hφc : Continuous φ := by
      rw [hq.continuous_iff]
      have : (φ ∘ f) = fun z => z ^ n := funext hφ
      rw [this]
      exact continuous_zpow n
    have h1 := hμ (φ.comp (QuotientGroup.mk' M)) (hφc.comp QuotientGroup.continuous_mk) (by
      intro m hm
      simp [(QuotientGroup.eq_one_iff m).2 hm])
    have h3 : (Circle.exp (Real.pi / n)) ^ n = 1 := by
      rw [← hφ]
      exact DFunLike.congr_fun h1 (c (Circle.exp (Real.pi / n)))
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
    rw [← Circle.exp_intCast_mul, mul_div_cancel₀ _ hn'] at h3
    exact Circle.exp_pi_ne_one h3

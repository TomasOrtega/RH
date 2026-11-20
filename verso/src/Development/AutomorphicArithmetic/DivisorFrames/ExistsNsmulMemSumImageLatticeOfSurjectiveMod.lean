import Mathlib

open NumberField

/- English proof (translation)
Introduce `gA gB p ΛA ΛB J hA hB hJ hsurj l hl`. Use `set Φ : (Fin p → (Fin gA → ℂ)) →ₗ[ℝ] (Fin gB → ℂ) := ∑ a, ((J a).restrictScalars ℝ).comp (LinearMap.proj a) with hΦ`. Establish `hΦapp : ∀ x, Φ x = ∑ a, J a (x a)`. Introduce `x`. Simplify using `[hΦ]`.

Set `Sz : Submodule ℤ (Fin gB → ℂ)` to `Submodule.map (Φ.restrictScalars ℤ) (Submodule.pi Set.univ (fun _ => ΛA))`. Establish `hSzB : Sz ≤ ΛB`. Introduce and unpack `y ⟨x, hx, rfl⟩`. Use `show Φ x ∈ ΛB`. Rewrite using `[hΦapp]`.

Conclude with `Submodule.sum_mem _ (fun a _ => hJ a (x a) (Submodule.mem_pi.mp hx a (Set.mem_univ a)))`. Use `haveI : Countable ΛB := TopologicalSpace.separableSpace_iff_countable.mp inferInstance`. Establish `hΦs : ∀ u, ∃ v, Φ v = u`. Introduce `u`. Assume the negation of the conclusion as `hu`.

Use `push_neg at hu`. Use `choose v hv using fun t : ℝ => hsurj (t • u)`. Set `f : ℝ → ΛB` to `fun t => ⟨t • u - Φ (v t), by rw [hΦapp]; exact hv t⟩`. Establish `hf : Function.Injective f`. Introduce `t t' htt`.

Establish `h1 : t • u - Φ (v t) = t' • u - Φ (v t')` using `congrArg Subtype.val htt`. Assume the negation of the conclusion as `hne`. Apply `hu ((t - t')⁻¹ • (v t - v t'))` to reduce the goal to its premises. Rewrite using `[map_smul, map_sub]`. Establish `h2 : (t - t') • u = Φ (v t) - Φ (v t')`.

Rewrite using `[sub_smul, sub_eq_sub_iff_sub_eq_sub]`. Conclude with `h1`. Rewrite using `[← h2, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul]`. Conclude with `Cardinal.not_countable_real (Set.countable_univ_iff.mpr hf.countable)`. Establish `hspan : Submodule.span ℝ (Sz : Set (Fin gB → ℂ)) = ⊤`.

Rewrite using `[eq_top_iff]`. Introduce and unpack `u -`. Take `⟨v, rfl⟩` from `hΦs u`. Rewrite using `[hΦapp]`. Use `Submodule.sum_mem _ (fun a _ => ?_)` and prove the remaining obligations.

Establish `hva : v a ∈ Submodule.span ℝ (ΛA : Set (Fin gA → ℂ))`. Rewrite using `[hA]`. Discharge the goal by the elementary cases of `trivial`. Establish `hsub : ((J a).restrictScalars ℝ) '' (ΛA : Set (Fin gA → ℂ)) ⊆ (Sz : Set (Fin gB → ℂ))`. Introduce and unpack `_ ⟨z, hz, rfl⟩`.

Use `⟨Pi.single a z, Submodule.mem_pi.mpr (fun b _ => ?_), ?_⟩` and prove the remaining obligations. Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality. Simplify using `using hz`. Simplify using `[Pi.single_eq_of_ne hb]`.

Use `show Φ (Pi.single a z) = J a z`. Rewrite using `[hΦapp, Finset.sum_eq_single a]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne hb]`.

Simplify using the standard rewrite rules. Conclude with `Submodule.span_mono hsub ((Submodule.span_image _).ge (Submodule.mem_map_of_mem hva))`. Take `⟨t, htS, htspan, hti⟩` from `exists_linearIndependent ℝ (Sz : Set (Fin gB → ℂ))`. Set `b : Module.Basis t ℝ (Fin gB → ℂ)` to `Module.Basis.mk hti (by simp only [Subtype.range_coe, htspan, hspan, le_refl])`. Use `haveI : Finite t := Module.Finite.finite_basis b`.

Use `haveI : Fintype t := Fintype.ofFinite t`. Establish `hbS : ∀ i, b i ∈ Sz` using `fun i => by`. Rewrite using `[Module.Basis.mk_apply]`. Conclude with `htS i.2`. Establish `hzS : Submodule.span ℤ (Set.range b) ≤ Sz` using `Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbS i)`.

Use `haveI : DiscreteTopology ΛB.toAddSubgroup := ‹DiscreteTopology ΛB›`. Use `haveI : DiscreteTopology (ΛB : Set (Fin gB → ℂ)) := ‹DiscreteTopology ΛB›`. Establish `hcl : IsClosed (ΛB : Set (Fin gB → ℂ))` using `AddSubgroup.isClosed_of_discrete (H := ΛB.toAddSubgroup)`. Establish `hfin : ((ZSpan.fundamentalDomain b) ∩ (ΛB : Set (Fin gB → ℂ))).Finite` using `Metric.finite_isBounded_inter_isClosed (isDiscrete_iff_discreteTopology.mpr ‹_›) (ZSpan.fundamentalDomain_isBounded b) hcl`. Establish `hmem : ∀ n : ℕ, ZSpan.fract b (n • l) ∈ (ZSpan.fundamentalDomain b) ∩ (ΛB : Set (Fin gB → ℂ))`.

Introduce `n`. Use `⟨ZSpan.fract_mem_fundamentalDomain b _, ?_⟩` and prove the remaining obligations. Rewrite using `[ZSpan.fract_apply]`. Conclude with `ΛB.sub_mem (ΛB.nsmul_mem hl n) (hSzB (hzS (ZSpan.floor b (n • l)).2))`. Take `⟨m, n, hmn, heq⟩` from `hfin.exists_lt_map_eq_of_forall_mem hmem`.

Establish `hdiff : (n - m) • l ∈ Sz`. Establish `h1 : (n - m) • l = n • l - m • l`. Rewrite using `[eq_sub_iff_add_eq, ← add_nsmul, Nat.sub_add_cancel hmn.le]`. Rewrite `heq` using `[ZSpan.fract_apply, ZSpan.fract_apply]`. Establish `h2 : n • l - m • l = (ZSpan.floor b (n • l) : Fin gB → ℂ) - ZSpan.floor b (m • l)`.

Rewrite using `[sub_eq_sub_iff_sub_eq_sub]`. Conclude with `heq.symm`. Rewrite using `[h1, h2]`. Conclude with `Sz.sub_mem (hzS (ZSpan.floor b _).2) (hzS (ZSpan.floor b _).2)`. Take `⟨x, hx, hxe⟩` from `hdiff`.

Use `⟨n - m, x, Nat.sub_pos_of_lt hmn, fun a => Submodule.mem_pi.mp hx a (Set.mem_univ a), ?_⟩` and prove the remaining obligations. Rewrite using `[← hxe]`. Conclude with `hΦapp x`.
-/
theorem UpperTheory.exists_nsmul_mem_sum_image_lattice_of_surjective_mod :
    ∀ (gA gB p : ℕ) (ΛA : Submodule ℤ (Fin gA → ℂ)) (ΛB : Submodule ℤ (Fin gB → ℂ))
        (J : Fin p → (Fin gA → ℂ) →ₗ[ℂ] (Fin gB → ℂ)),
        Submodule.span ℝ (ΛA : Set (Fin gA → ℂ)) = ⊤ → DiscreteTopology ΛB →
        (∀ a, ∀ z ∈ ΛA, J a z ∈ ΛB) → (∀ w, ∃ v : Fin p → (Fin gA → ℂ), w - ∑ a, J a (v a) ∈ ΛB) →
        ∀ l ∈ ΛB, ∃ (N : ℕ) (x : Fin p → (Fin gA → ℂ)), 0 < N ∧ (∀ a, x a ∈ ΛA) ∧ N • l = ∑ a, J a (x a) := by
  intro gA gB p ΛA ΛB J hA hB hJ hsurj l hl
  classical
  set Φ : (Fin p → (Fin gA → ℂ)) →ₗ[ℝ] (Fin gB → ℂ) :=
    ∑ a, ((J a).restrictScalars ℝ).comp (LinearMap.proj a) with hΦ
  have hΦapp : ∀ x, Φ x = ∑ a, J a (x a) := by
    intro x
    simp [hΦ]
  let Sz : Submodule ℤ (Fin gB → ℂ) :=
    Submodule.map (Φ.restrictScalars ℤ) (Submodule.pi Set.univ (fun _ => ΛA))
  have hSzB : Sz ≤ ΛB := by
    rintro y ⟨x, hx, rfl⟩
    show Φ x ∈ ΛB
    rw [hΦapp]
    exact Submodule.sum_mem _ (fun a _ => hJ a (x a) (Submodule.mem_pi.mp hx a (Set.mem_univ a)))
  haveI : Countable ΛB := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have hΦs : ∀ u, ∃ v, Φ v = u := by
    intro u
    by_contra hu
    push_neg at hu
    choose v hv using fun t : ℝ => hsurj (t • u)
    let f : ℝ → ΛB := fun t => ⟨t • u - Φ (v t), by rw [hΦapp]; exact hv t⟩
    have hf : Function.Injective f := by
      intro t t' htt
      have h1 : t • u - Φ (v t) = t' • u - Φ (v t') := congrArg Subtype.val htt
      by_contra hne
      apply hu ((t - t')⁻¹ • (v t - v t'))
      rw [map_smul, map_sub]
      have h2 : (t - t') • u = Φ (v t) - Φ (v t') := by
        rw [sub_smul, sub_eq_sub_iff_sub_eq_sub]
        exact h1
      rw [← h2, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul]
    exact Cardinal.not_countable_real (Set.countable_univ_iff.mpr hf.countable)
  have hspan : Submodule.span ℝ (Sz : Set (Fin gB → ℂ)) = ⊤ := by
    rw [eq_top_iff]
    rintro u -
    obtain ⟨v, rfl⟩ := hΦs u
    rw [hΦapp]
    refine Submodule.sum_mem _ (fun a _ => ?_)
    have hva : v a ∈ Submodule.span ℝ (ΛA : Set (Fin gA → ℂ)) := by
      rw [hA]
      trivial
    have hsub : ((J a).restrictScalars ℝ) '' (ΛA : Set (Fin gA → ℂ)) ⊆ (Sz : Set (Fin gB → ℂ)) := by
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨Pi.single a z, Submodule.mem_pi.mpr (fun b _ => ?_), ?_⟩
      · by_cases hb : b = a
        · subst hb
          simpa using hz
        · simp [Pi.single_eq_of_ne hb]
      · show Φ (Pi.single a z) = J a z
        rw [hΦapp, Finset.sum_eq_single a]
        · simp
        · intro b _ hb
          simp [Pi.single_eq_of_ne hb]
        · simp
    exact Submodule.span_mono hsub ((Submodule.span_image _).ge (Submodule.mem_map_of_mem hva))
  obtain ⟨t, htS, htspan, hti⟩ := exists_linearIndependent ℝ (Sz : Set (Fin gB → ℂ))
  let b : Module.Basis t ℝ (Fin gB → ℂ) :=
    Module.Basis.mk hti (by simp only [Subtype.range_coe, htspan, hspan, le_refl])
  haveI : Finite t := Module.Finite.finite_basis b
  haveI : Fintype t := Fintype.ofFinite t
  have hbS : ∀ i, b i ∈ Sz := fun i => by
    rw [Module.Basis.mk_apply]
    exact htS i.2
  have hzS : Submodule.span ℤ (Set.range b) ≤ Sz :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbS i)
  haveI : DiscreteTopology ΛB.toAddSubgroup := ‹DiscreteTopology ΛB›
  haveI : DiscreteTopology (ΛB : Set (Fin gB → ℂ)) := ‹DiscreteTopology ΛB›
  have hcl : IsClosed (ΛB : Set (Fin gB → ℂ)) := AddSubgroup.isClosed_of_discrete (H := ΛB.toAddSubgroup)
  have hfin : ((ZSpan.fundamentalDomain b) ∩ (ΛB : Set (Fin gB → ℂ))).Finite :=
    Metric.finite_isBounded_inter_isClosed (isDiscrete_iff_discreteTopology.mpr ‹_›)
      (ZSpan.fundamentalDomain_isBounded b) hcl
  have hmem : ∀ n : ℕ, ZSpan.fract b (n • l) ∈ (ZSpan.fundamentalDomain b) ∩ (ΛB : Set (Fin gB → ℂ)) := by
    intro n
    refine ⟨ZSpan.fract_mem_fundamentalDomain b _, ?_⟩
    rw [ZSpan.fract_apply]
    exact ΛB.sub_mem (ΛB.nsmul_mem hl n) (hSzB (hzS (ZSpan.floor b (n • l)).2))
  obtain ⟨m, n, hmn, heq⟩ := hfin.exists_lt_map_eq_of_forall_mem hmem
  have hdiff : (n - m) • l ∈ Sz := by
    have h1 : (n - m) • l = n • l - m • l := by
      rw [eq_sub_iff_add_eq, ← add_nsmul, Nat.sub_add_cancel hmn.le]
    rw [ZSpan.fract_apply, ZSpan.fract_apply] at heq
    have h2 : n • l - m • l = (ZSpan.floor b (n • l) : Fin gB → ℂ) - ZSpan.floor b (m • l) := by
      rw [sub_eq_sub_iff_sub_eq_sub]
      exact heq.symm
    rw [h1, h2]
    exact Sz.sub_mem (hzS (ZSpan.floor b _).2) (hzS (ZSpan.floor b _).2)
  obtain ⟨x, hx, hxe⟩ := hdiff
  refine ⟨n - m, x, Nat.sub_pos_of_lt hmn, fun a => Submodule.mem_pi.mp hx a (Set.mem_univ a), ?_⟩
  rw [← hxe]
  exact hΦapp x

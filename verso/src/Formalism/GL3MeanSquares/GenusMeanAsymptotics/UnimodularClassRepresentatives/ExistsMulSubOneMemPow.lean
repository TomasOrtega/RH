import Mathlib

open Module

set_option linter.deprecated false

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.MeanA

/- English proof (translation)
Take `⟨y, i, hi, hyi⟩` from `h𝔭.exists_inv ht`. Use `⟨(∑ j ∈ Finset.range k, i ^ j) * y, ?_⟩` and prove the remaining obligations. Establish `h1 : (∑ j ∈ Finset.range k, i ^ j) * (i - 1) = i ^ k - 1` using `geom_sum_mul i k`. Establish `h2 : (∑ j ∈ Finset.range k, i ^ j) * y * t - 1 = -(i ^ k)`. Take the linear combination `(∑ j ∈ Finset.range k, i ^ j) * hyi - h1`.

Rewrite using `[h2]`. Conclude with `(𝔭 ^ k).neg_mem (Ideal.pow_mem_pow hi k)`.
-/
theorem exists_mul_sub_one_mem_pow {R : Type*} [CommRing R] {𝔭 : Ideal R} (h𝔭 : 𝔭.IsMaximal) {t : R}
    (ht : t ∉ 𝔭) (k : ℕ) : ∃ u : R, u * t - 1 ∈ 𝔭 ^ k := by
  obtain ⟨y, i, hi, hyi⟩ := h𝔭.exists_inv ht
  refine ⟨(∑ j ∈ Finset.range k, i ^ j) * y, ?_⟩
  have h1 : (∑ j ∈ Finset.range k, i ^ j) * (i - 1) = i ^ k - 1 := geom_sum_mul i k
  have h2 : (∑ j ∈ Finset.range k, i ^ j) * y * t - 1 = -(i ^ k) := by
    linear_combination (∑ j ∈ Finset.range k, i ^ j) * hyi - h1
  rw [h2]
  exact (𝔭 ^ k).neg_mem (Ideal.pow_mem_pow hi k)

/- English proof (translation)
Take `⟨u, hu⟩` from `exists_mul_sub_one_mem_pow h𝔭 ht k`. Establish `e : c = u * (t * c) - (u * t - 1) * c` using `by ring`. Rewrite using `[e]`. Conclude with `Ideal.sub_mem _ (Ideal.mul_mem_left _ u h) (Ideal.mul_mem_right c _ hu)`.
-/
theorem mem_pow_of_mul_mem {R : Type*} [CommRing R] {𝔭 : Ideal R} (h𝔭 : 𝔭.IsMaximal) {t c : R}
    (ht : t ∉ 𝔭) {k : ℕ} (h : t * c ∈ 𝔭 ^ k) : c ∈ 𝔭 ^ k := by
  obtain ⟨u, hu⟩ := exists_mul_sub_one_mem_pow h𝔭 ht k
  have e : c = u * (t * c) - (u * t - 1) * c := by ring
  rw [e]
  exact Ideal.sub_mem _ (Ideal.mul_mem_left _ u h) (Ideal.mul_mem_right c _ hu)

variable {R F V : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F]
  [IsFractionRing R F] [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
  [FiniteDimensional F V]

/- English proof (translation)
Use `h𝔭` as an intermediate fact. Set `: Field (R ⧸ 𝔭)` to `Ideal.Quotient.field 𝔭`. Establish `: Module.Finite R M` using `Module.Finite.iff_fg.2 hfg`. Set `Q` to `M ⧸ (𝔭 • ⊤ : Submodule R M)`. Establish `: Module.Finite (R ⧸ 𝔭) Q` using `Module.Finite.of_restrictScalars_finite R _ _`.

Set `b` to `Module.finBasis (R ⧸ 𝔭) Q`. Use `choose x hx using fun i => Submodule.Quotient.mk_surjective _ (b i)`. Establish `hli : LinearIndependent F (M.subtype ∘ x)`. Use `Ideal.FinrankQuotientMap.linearIndependent_of_nontrivial (S := R ⧸ 𝔭) F ?_ M.subtype M.injective_subtype (Submodule.mkQ (𝔭 • ⊤ : Submodule R M)) ?_` and prove the remaining obligations. Rewrite using `[Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]`.

Conclude with `h𝔭.ne_top`. Establish `: (Submodule.mkQ (𝔭 • ⊤ : Submodule R M)) ∘ x = b`. Use function extensionality and compare the values at `i`. Conclude with `hx i`. Rewrite using `[this]`.

Conclude with `b.linearIndependent`. Establish `hsup : (⊤ : Submodule R M) ≤ Submodule.span R (Set.range x) ⊔ 𝔭 • ⊤`. Introduce `v _`. Establish `hv : (Submodule.Quotient.mk v : Q) ∈ Submodule.span (R ⧸ 𝔭) (Set.range b)` using `b.mem_span _`. Rewrite `hv` using `[← @Submodule.restrictScalars_mem R, Submodule.restrictScalars_span R (R ⧸ 𝔭) Ideal.Quotient.mk_surjective]`.

Establish `hb : Set.range b = (Submodule.mkQ (𝔭 • ⊤ : Submodule R M)) '' Set.range x`. Rewrite using `[← Set.range_comp]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `(hx i).symm`.

Rewrite `hv` using `[hb, ← Submodule.map_span]`. Take `⟨y, hy, e⟩` from `Submodule.mem_map.1 hv`. Rewrite `e` using `[Submodule.mkQ_apply, Submodule.Quotient.eq]`. Establish `: v = y - (y - v)` using `by abel`. Rewrite using `[this]`.

Conclude with `sub_mem (Submodule.mem_sup_left hy) (Submodule.mem_sup_right e)`. Take `⟨s, hs1, hs⟩` from `Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup (Module.Finite.fg_top (R := R) (M := M)) le_rfl hsup`. Establish `hs𝔭 : s ∉ 𝔭` using `fun h => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 (by`. Use `sub_mem h hs1` as an intermediate fact. Simplify using `using this))`.

Establish `hsv : ∀ v : M, s • v ∈ Submodule.span R (Set.range x)` using `fun v => hs (Submodule.smul_mem_pointwise_smul v s ⊤ trivial)`. Establish `hs0 : algebraMap R F s ≠ 0`. Introduce `h0`. Establish `: s = 0` using `(IsFractionRing.injective R F) (by rw [h0, map_zero])`. Conclude with `hs𝔭 (this ▸ 𝔭.zero_mem)`.

Establish `hsp : ⊤ ≤ Submodule.span F (Set.range (M.subtype ∘ x))`. Rewrite using `[← hspan, Submodule.span_le]`. Introduce `v hv`. Establish `h1` using `hsv ⟨v, hv⟩`. Establish `h2 : (s • v : V) ∈ Submodule.span F (Set.range (M.subtype ∘ x))`.

Establish `h3 : M.subtype (s • ⟨v, hv⟩) ∈ (Submodule.span R (Set.range x)).map M.subtype` using `Submodule.mem_map_of_mem h1`. Rewrite `h3` using `[Submodule.map_span, ← Set.range_comp]`. Conclude with `Submodule.span_le_restrictScalars R F _ h3`. Establish `h4 : v = (algebraMap R F s)⁻¹ • (s • v)`. Rewrite using `[← algebraMap_smul F s v, smul_smul, inv_mul_cancel₀ hs0, one_smul]`.

Rewrite using `[h4]`. Conclude with `Submodule.smul_mem _ _ h2`. Establish `hcard : finrank (R ⧸ 𝔭) Q = finrank F V`. Use `finrank_eq_card_basis (Basis.mk hli hsp)` as an intermediate fact. Simplify using `using this.symm`.

Establish `hliR : LinearIndependent R x`. Use `hli.restrict_scalars (R := R) (by` as an intermediate fact. Introduce `a b hab`. Simplify `hab |> fun h => (IsFractionRing.injective R F) (by simpa [Algebra.smul_def] using h))` using `[Algebra.smul_def]`. Conclude with `LinearIndependent.of_comp M.subtype this`.

Use `⟨x ∘ Fin.cast hcard.symm, s, hs𝔭, hliR.comp _ (Fin.cast_injective _), fun v => ?_⟩` and prove the remaining obligations. Establish `: Set.range (x ∘ Fin.cast hcard.symm) = Set.range x` using `(Fin.castOrderIso hcard.symm).surjective.range_comp x`. Rewrite using `[this]`. Conclude with `hsv v`.
-/
theorem exists_local_basis (M : Submodule R V) (hfg : M.FG)
    (hspan : Submodule.span F (M : Set V) = ⊤) {𝔭 : Ideal R} (h𝔭 : 𝔭.IsMaximal) :
    ∃ (x : Fin (finrank F V) → M) (s : R), s ∉ 𝔭 ∧ LinearIndependent R x ∧
      ∀ v : M, s • v ∈ Submodule.span R (Set.range x) := by
  have := h𝔭
  let : Field (R ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  have : Module.Finite R M := Module.Finite.iff_fg.2 hfg
  let Q := M ⧸ (𝔭 • ⊤ : Submodule R M)
  have : Module.Finite (R ⧸ 𝔭) Q := Module.Finite.of_restrictScalars_finite R _ _
  let b := Module.finBasis (R ⧸ 𝔭) Q
  choose x hx using fun i => Submodule.Quotient.mk_surjective _ (b i)
  have hli : LinearIndependent F (M.subtype ∘ x) := by
    refine Ideal.FinrankQuotientMap.linearIndependent_of_nontrivial (S := R ⧸ 𝔭) F ?_ M.subtype
      M.injective_subtype (Submodule.mkQ (𝔭 • ⊤ : Submodule R M)) ?_
    · rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]; exact h𝔭.ne_top
    · have : (Submodule.mkQ (𝔭 • ⊤ : Submodule R M)) ∘ x = b := by
        funext i; exact hx i
      rw [this]; exact b.linearIndependent
  have hsup : (⊤ : Submodule R M) ≤ Submodule.span R (Set.range x) ⊔ 𝔭 • ⊤ := by
    intro v _
    have hv : (Submodule.Quotient.mk v : Q) ∈ Submodule.span (R ⧸ 𝔭) (Set.range b) := b.mem_span _
    rw [← @Submodule.restrictScalars_mem R,
      Submodule.restrictScalars_span R (R ⧸ 𝔭) Ideal.Quotient.mk_surjective] at hv
    have hb : Set.range b = (Submodule.mkQ (𝔭 • ⊤ : Submodule R M)) '' Set.range x := by
      rw [← Set.range_comp]; congr 1; funext i; exact (hx i).symm
    rw [hb, ← Submodule.map_span] at hv
    obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 hv
    rw [Submodule.mkQ_apply, Submodule.Quotient.eq] at e
    have : v = y - (y - v) := by abel
    rw [this]
    exact sub_mem (Submodule.mem_sup_left hy) (Submodule.mem_sup_right e)
  obtain ⟨s, hs1, hs⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (Module.Finite.fg_top (R := R) (M := M)) le_rfl hsup
  have hs𝔭 : s ∉ 𝔭 := fun h => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 (by
    have := sub_mem h hs1; simpa using this))
  have hsv : ∀ v : M, s • v ∈ Submodule.span R (Set.range x) := fun v =>
    hs (Submodule.smul_mem_pointwise_smul v s ⊤ trivial)
  have hs0 : algebraMap R F s ≠ 0 := by
    intro h0
    have : s = 0 := (IsFractionRing.injective R F) (by rw [h0, map_zero])
    exact hs𝔭 (this ▸ 𝔭.zero_mem)
  have hsp : ⊤ ≤ Submodule.span F (Set.range (M.subtype ∘ x)) := by
    rw [← hspan, Submodule.span_le]
    intro v hv
    have h1 := hsv ⟨v, hv⟩
    have h2 : (s • v : V) ∈ Submodule.span F (Set.range (M.subtype ∘ x)) := by
      have h3 : M.subtype (s • ⟨v, hv⟩) ∈ (Submodule.span R (Set.range x)).map M.subtype :=
        Submodule.mem_map_of_mem h1
      rw [Submodule.map_span, ← Set.range_comp] at h3
      exact Submodule.span_le_restrictScalars R F _ h3
    have h4 : v = (algebraMap R F s)⁻¹ • (s • v) := by
      rw [← algebraMap_smul F s v, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [h4]
    exact Submodule.smul_mem _ _ h2
  have hcard : finrank (R ⧸ 𝔭) Q = finrank F V := by
    have := finrank_eq_card_basis (Basis.mk hli hsp)
    simpa using this.symm
  have hliR : LinearIndependent R x := by
    have := hli.restrict_scalars (R := R) (by
      intro a b hab
      simpa [Algebra.smul_def] using hab |> fun h => (IsFractionRing.injective R F) (by simpa [Algebra.smul_def] using h))
    exact LinearIndependent.of_comp M.subtype this
  refine ⟨x ∘ Fin.cast hcard.symm, s, hs𝔭, hliR.comp _ (Fin.cast_injective _), fun v => ?_⟩
  have : Set.range (x ∘ Fin.cast hcard.symm) = Set.range x :=
    (Fin.castOrderIso hcard.symm).surjective.range_comp x
  rw [this]; exact hsv v

/- English proof (translation)
Take `⟨x, s, hs, hli, hsx⟩` from `exists_local_basis M hfg hspan h𝔭`. Set `φ : (Fin (finrank F V) → R) →ₗ[R] M` to `{ toFun := fun c => ∑ i, c i • x i map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib] map_smul' := fun a c => by simp [Finset.smul_sum, smul_smul] }`. Establish `hφ : ∀ c, φ c = ∑ i, c i • x i` using `fun c => rfl`. Set `ψ` to `(𝔭 ^ k • ⊤ : Submodule R M).mkQ ∘ₗ φ`. Establish `hP : ∀ v ∈ (𝔭 ^ k • ⊤ : Submodule R M), ∃ d : Fin (finrank F V) → R, (∀ i, d i ∈ 𝔭 ^ k) ∧ s • v = ∑ i, d i • x i`.

Introduce `v hv`. Use `Submodule.smul_induction_on hv ?_ ?_` and prove the remaining obligations. Introduce `a ha m _`. Take `⟨r, hr⟩` from `(Submodule.mem_span_range_iff_exists_fun R).mp (hsx m)`. Use `⟨fun i => a * r i, fun i => Ideal.mul_mem_right _ _ ha, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_comm s a m, ← hr, Finset.smul_sum]`. Simplify using `only [smul_smul]`. Introduce `v w hv hw`. Take `⟨d, hd, hd'⟩` from `hv`. Take `⟨d', hd2, hd2'⟩` from `hw`.

Use `⟨d + d', fun i => Ideal.add_mem _ (hd i) (hd2 i), ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, hd', hd2']`. Simplify using `only [Pi.add_apply, add_smul, Finset.sum_add_distrib]`. Establish `hsurj : Function.Surjective ψ`. Introduce `y`.

Take `⟨m, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Take `⟨u, hu⟩` from `exists_mul_sub_one_mem_pow h𝔭 hs k`. Take `⟨r, hr⟩` from `(Submodule.mem_span_range_iff_exists_fun R).mp (hsx m)`. Use `⟨fun i => u * r i, ?_⟩` and prove the remaining obligations. Use `show Submodule.Quotient.mk (φ (fun i => u * r i)) = Submodule.Quotient.mk m`.

Rewrite using `[hφ, Submodule.Quotient.eq]`. Establish `e : ∑ i, (u * r i) • x i - m = (u * s - 1) • m`. Simplify using `only [mul_smul, ← Finset.smul_sum, hr, sub_smul, one_smul]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem_smul hu Submodule.mem_top`.

Establish `hker : LinearMap.ker ψ = Submodule.pi Set.univ (fun _ => 𝔭 ^ k)`. Use extensionality with `c`. Rewrite using `[LinearMap.mem_ker, Submodule.mem_pi]`. Use `show Submodule.Quotient.mk (φ c) = 0 ↔ _`. Rewrite using `[Submodule.Quotient.mk_eq_zero, hφ]`.

Prove the components needed by the constructor for the conclusion. Introduce `hc i _`. Take `⟨d, hd, hsd⟩` from `hP _ hc`. Establish `h0 : ∑ i, (s * c i - d i) • x i = 0`. Simplify using `only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, ← hsd, sub_self]`.

Establish `h1` using `Fintype.linearIndependent_iff.mp hli _ h0 i`. Conclude with `mem_pow_of_mul_mem h𝔭 hs (by rw [sub_eq_zero.mp h1]; exact hd i)`. Introduce `hc`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hc i (Set.mem_univ i)) Submodule.mem_top`. Establish `e` using `((LinearMap.quotKerEquivOfSurjective ψ hsurj).symm.trans ((Submodule.quotEquivOfEq _ _ hker).trans (Submodule.quotientPi (fun _ => 𝔭 ^ k))))`.

Rewrite using `[Nat.card_congr e.toEquiv, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.
-/
theorem card_quot_pow_smul_top (M : Submodule R V) (hfg : M.FG)
    (hspan : Submodule.span F (M : Set V) = ⊤) {𝔭 : Ideal R} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    Nat.card (M ⧸ (𝔭 ^ k • ⊤ : Submodule R M)) = Nat.card (R ⧸ 𝔭 ^ k) ^ finrank F V := by
  obtain ⟨x, s, hs, hli, hsx⟩ := exists_local_basis M hfg hspan h𝔭
  let φ : (Fin (finrank F V) → R) →ₗ[R] M :=
    { toFun := fun c => ∑ i, c i • x i
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by simp [Finset.smul_sum, smul_smul] }
  have hφ : ∀ c, φ c = ∑ i, c i • x i := fun c => rfl
  let ψ := (𝔭 ^ k • ⊤ : Submodule R M).mkQ ∘ₗ φ
  have hP : ∀ v ∈ (𝔭 ^ k • ⊤ : Submodule R M), ∃ d : Fin (finrank F V) → R,
      (∀ i, d i ∈ 𝔭 ^ k) ∧ s • v = ∑ i, d i • x i := by
    intro v hv
    refine Submodule.smul_induction_on hv ?_ ?_
    · intro a ha m _
      obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp (hsx m)
      refine ⟨fun i => a * r i, fun i => Ideal.mul_mem_right _ _ ha, ?_⟩
      rw [smul_comm s a m, ← hr, Finset.smul_sum]
      simp only [smul_smul]
    · intro v w hv hw
      obtain ⟨d, hd, hd'⟩ := hv
      obtain ⟨d', hd2, hd2'⟩ := hw
      refine ⟨d + d', fun i => Ideal.add_mem _ (hd i) (hd2 i), ?_⟩
      rw [smul_add, hd', hd2']
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨u, hu⟩ := exists_mul_sub_one_mem_pow h𝔭 hs k
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp (hsx m)
    refine ⟨fun i => u * r i, ?_⟩
    show Submodule.Quotient.mk (φ (fun i => u * r i)) = Submodule.Quotient.mk m
    rw [hφ, Submodule.Quotient.eq]
    have e : ∑ i, (u * r i) • x i - m = (u * s - 1) • m := by
      simp only [mul_smul, ← Finset.smul_sum, hr, sub_smul, one_smul]
    rw [e]
    exact Submodule.smul_mem_smul hu Submodule.mem_top
  have hker : LinearMap.ker ψ = Submodule.pi Set.univ (fun _ => 𝔭 ^ k) := by
    ext c
    rw [LinearMap.mem_ker, Submodule.mem_pi]
    show Submodule.Quotient.mk (φ c) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, hφ]
    constructor
    · intro hc i _
      obtain ⟨d, hd, hsd⟩ := hP _ hc
      have h0 : ∑ i, (s * c i - d i) • x i = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, ← hsd, sub_self]
      have h1 := Fintype.linearIndependent_iff.mp hli _ h0 i
      exact mem_pow_of_mul_mem h𝔭 hs (by rw [sub_eq_zero.mp h1]; exact hd i)
    · intro hc
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem_smul (hc i (Set.mem_univ i)) Submodule.mem_top
  have e := ((LinearMap.quotKerEquivOfSurjective ψ hsurj).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans (Submodule.quotientPi (fun _ => 𝔭 ^ k))))
  rw [Nat.card_congr e.toEquiv, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Formalism.HermitianLattices.Ext.L3.MeanA

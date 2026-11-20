import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

/- English proof (translation)
Introduce `L _ G _ _ U _ S hS y₀ hy₀`. Use `set V : Subgroup G := fixingSubgroup G (S : Set L) with hV`. Establish `hUV : U ≤ V`. Introduce `u hu`. Rewrite using `[hV, mem_fixingSubgroup_iff]`.

Introduce `s hs`. Conclude with `hS s hs ⟨u, hu⟩`. Establish `hy0 : ∀ a b : G, (a : G ⧸ U) = b → a • y₀ = b • y₀`. Introduce `a b hab`. Rewrite `hab` using `[QuotientGroup.eq]`.

Establish `h1 : (a⁻¹ * b) • y₀ = y₀` using `hy₀ ⟨_, hab⟩`. Combine the equalities or inequalities in the displayed calculation. Use `set f : G ⧸ U → L := fun q => q.out • y₀ with hf`. Establish `hfmk : ∀ g : G, f (g : G ⧸ U) = g • y₀` using `fun g => hy0 _ _ (QuotientGroup.out_eq' _)`. Establish `hfeq : ∀ (g : G) (q : G ⧸ U), f (g • q) = g • f q`.

Introduce `g q`. Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H a => show f ((g * a : G) : G ⧸ U) = g • f (a : G ⧸ U)`. Rewrite using `[hfmk, hfmk, mul_smul]`. Set `π : G ⧸ U → G ⧸ V` to `Subgroup.quotientMapOfLE hUV`.

Establish `hπmk : ∀ g : G, π (g : G ⧸ U) = (g : G ⧸ V)` using `fun g => rfl`. Establish `hπeq : ∀ (g : G) (q : G ⧸ U), π (g • q) = g • π q`. Introduce `g q`. Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H a => rw [MulAction.Quotient.smul_mk, hπmk, hπmk, MulAction.Quotient.smul_mk]`.

Establish `hV1 : ∀ g : G, (g : G ⧸ V) = ((1 : G) : G ⧸ V) ↔ g ∈ V`. Introduce `g`. Rewrite using `[QuotientGroup.eq, mul_one, inv_mem_iff]`. Use `haveI : Finite (G ⧸ V) := Finite.of_surjective π (by`. Introduce `c`.

Proceed by induction on `c using QuotientGroup.induction_on with`. Consider the case `H a => exact ⟨(a : G ⧸ U), rfl⟩)`. Use `letI : Fintype (G ⧸ V) := Fintype.ofFinite _`. Use `set F : Finset (G ⧸ U) := Finset.univ.filter (fun q => π q = ((1 : G) : G ⧸ V)) with hF`. Establish `hout : ∀ {H : Subgroup G} (a b : G ⧸ H), a.out = b.out → a = b`.

Introduce `H a b hab`. Rewrite using `[← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b, hab]`. Establish `hyV : ∀ v ∈ V, v • (∑ q ∈ F, f q) = ∑ q ∈ F, f q`. Introduce `v hv`. Rewrite using `[Finset.smul_sum]`.

Use `symm`. Use `Finset.sum_nbij' (fun q => v⁻¹ • q) (fun q => v • q) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `q hq`. Simplify using `only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢`. Rewrite using `[hπeq, hq, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, hV1]`.

Conclude with `V.inv_mem hv`. Introduce `q hq`. Simplify using `only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢`. Rewrite using `[hπeq, hq, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, hV1]`. Conclude with `hv`.

Introduce `q _`. Simplify using `only [smul_inv_smul]`. Introduce `q _`. Simplify using `only [inv_smul_smul]`. Introduce `q _`.

Rewrite using `[hfeq, smul_inv_smul]`. Use `⟨∑ q ∈ F, f q, F.image Quotient.out, (Finset.univ : Finset (G ⧸ V)).image Quotient.out, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_image (fun a _ b _ hab => hout a b hab)]`. Introduce `h`. Establish `hgh : (h : G ⧸ V).out⁻¹ * h ∈ V` using `QuotientGroup.eq.1 (QuotientGroup.out_eq' _)`.

Use `⟨(h : G ⧸ V).out, ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← mul_inv_cancel_left (h : G ⧸ V).out h]`. Rewrite using `[← smul_smul, hyV _ hgh]`. Introduce `s hs`. Establish `h2 : ((h : G ⧸ V).out⁻¹ * h) • s = s` using `(mem_fixingSubgroup_iff G).1 hgh s hs`.

Use `conv_lhs => rw [← mul_inv_cancel_left (h : G ⧸ V).out h]`. Rewrite using `[← smul_smul, h2]`. Introduce and unpack `g' ⟨hg'E, _, hg'S⟩`. Take `⟨c, _, rfl⟩` from `Finset.mem_image.1 hg'E`. Establish `h3 : c.out⁻¹ * h ∈ V` using `(mem_fixingSubgroup_iff G).2 (fun s hs => by`.

Rewrite using `[← smul_smul, hg'S s hs, inv_smul_smul])`. Establish `h4 : (c.out : G ⧸ V) = (h : G ⧸ V)` using `QuotientGroup.eq.2 h3`. Rewrite `h4` using `[QuotientGroup.out_eq']`. Rewrite using `[h4]`. Rewrite using `[Finset.sum_image (fun a _ b _ hab => hout a b hab)]`.

Unfold `cosetTrace`. Express the relevant statement in the definitionally equal form `_ = ∑ q : G ⧸ U, f q`. Rewrite using `[← Finset.sum_fiberwise Finset.univ π f]`. Use `Finset.sum_congr rfl (fun c _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.smul_sum]`.

Establish `key : ∀ g : G, g⁻¹ • (g : G ⧸ V) = ((1 : G) : G ⧸ V)` using `fun g => by`. Rewrite using `[MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel]`. Use `Finset.sum_nbij' (fun q => c.out • q) (fun q => c.out⁻¹ • q) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `q hq`. Simplify using `only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢`.

Rewrite using `[hπeq, hq, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.out_eq']`. Introduce `q hq`. Simplify using `only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢`. Rewrite using `[hπeq, hq]`. Establish `h5` using `key c.out`.

Rewrite `h5` using `[QuotientGroup.out_eq']`. Then use the resulting hypothesis. Introduce `q _`. Simplify using `only [inv_smul_smul]`. Introduce `q _`. Simplify using `only [smul_inv_smul]`.

Introduce `q _`. Rewrite using `[hfeq]`.
-/
theorem exists_reps_of_cosetTrace : ∀ (L : Type) [Field L] (G : Type) [Group G] [MulSemiringAction G L]
    (U : Subgroup G) [Fintype (G ⧸ U)] (S : Finset L), (∀ s ∈ S, s ∈ Fix L U) → ∀ y₀ ∈ Fix L U,
    ∃ (y : L) (D E : Finset G), y = ∑ d ∈ D, d • y₀ ∧
      (∀ h : G, ∃! g, g ∈ E ∧ h • y = g • y ∧ ∀ s ∈ S, h • s = g • s) ∧
      ∑ g ∈ E, g • y = cosetTrace U y₀ := by
  intro L _ G _ _ U _ S hS y₀ hy₀
  classical
  set V : Subgroup G := fixingSubgroup G (S : Set L) with hV
  have hUV : U ≤ V := by
    intro u hu
    rw [hV, mem_fixingSubgroup_iff]
    intro s hs
    exact hS s hs ⟨u, hu⟩
  have hy0 : ∀ a b : G, (a : G ⧸ U) = b → a • y₀ = b • y₀ := by
    intro a b hab
    rw [QuotientGroup.eq] at hab
    have h1 : (a⁻¹ * b) • y₀ = y₀ := hy₀ ⟨_, hab⟩
    calc a • y₀ = a • ((a⁻¹ * b) • y₀) := by rw [h1]
      _ = b • y₀ := by rw [smul_smul, mul_inv_cancel_left]
  set f : G ⧸ U → L := fun q => q.out • y₀ with hf
  have hfmk : ∀ g : G, f (g : G ⧸ U) = g • y₀ := fun g => hy0 _ _ (QuotientGroup.out_eq' _)
  have hfeq : ∀ (g : G) (q : G ⧸ U), f (g • q) = g • f q := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H a =>
      show f ((g * a : G) : G ⧸ U) = g • f (a : G ⧸ U)
      rw [hfmk, hfmk, mul_smul]
  let π : G ⧸ U → G ⧸ V := Subgroup.quotientMapOfLE hUV
  have hπmk : ∀ g : G, π (g : G ⧸ U) = (g : G ⧸ V) := fun g => rfl
  have hπeq : ∀ (g : G) (q : G ⧸ U), π (g • q) = g • π q := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H a => rw [MulAction.Quotient.smul_mk, hπmk, hπmk, MulAction.Quotient.smul_mk]
  have hV1 : ∀ g : G, (g : G ⧸ V) = ((1 : G) : G ⧸ V) ↔ g ∈ V := by
    intro g
    rw [QuotientGroup.eq, mul_one, inv_mem_iff]
  haveI : Finite (G ⧸ V) := Finite.of_surjective π (by
    intro c
    induction c using QuotientGroup.induction_on with
    | H a => exact ⟨(a : G ⧸ U), rfl⟩)
  letI : Fintype (G ⧸ V) := Fintype.ofFinite _
  set F : Finset (G ⧸ U) := Finset.univ.filter (fun q => π q = ((1 : G) : G ⧸ V)) with hF
  have hout : ∀ {H : Subgroup G} (a b : G ⧸ H), a.out = b.out → a = b := by
    intro H a b hab
    rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b, hab]

  have hyV : ∀ v ∈ V, v • (∑ q ∈ F, f q) = ∑ q ∈ F, f q := by
    intro v hv
    rw [Finset.smul_sum]
    symm
    refine Finset.sum_nbij' (fun q => v⁻¹ • q) (fun q => v • q) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rw [hπeq, hq, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, hV1]
      exact V.inv_mem hv
    · intro q hq
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rw [hπeq, hq, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, hV1]
      exact hv
    · intro q _
      simp only [smul_inv_smul]
    · intro q _
      simp only [inv_smul_smul]
    · intro q _
      rw [hfeq, smul_inv_smul]
  refine ⟨∑ q ∈ F, f q, F.image Quotient.out, (Finset.univ : Finset (G ⧸ V)).image Quotient.out, ?_, ?_, ?_⟩
  · rw [Finset.sum_image (fun a _ b _ hab => hout a b hab)]
  · intro h
    have hgh : (h : G ⧸ V).out⁻¹ * h ∈ V := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    refine ⟨(h : G ⧸ V).out, ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_, ?_⟩, ?_⟩
    · conv_lhs => rw [← mul_inv_cancel_left (h : G ⧸ V).out h]
      rw [← smul_smul, hyV _ hgh]
    · intro s hs
      have h2 : ((h : G ⧸ V).out⁻¹ * h) • s = s := (mem_fixingSubgroup_iff G).1 hgh s hs
      conv_lhs => rw [← mul_inv_cancel_left (h : G ⧸ V).out h]
      rw [← smul_smul, h2]
    · rintro g' ⟨hg'E, _, hg'S⟩
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hg'E
      have h3 : c.out⁻¹ * h ∈ V := (mem_fixingSubgroup_iff G).2 (fun s hs => by
        rw [← smul_smul, hg'S s hs, inv_smul_smul])
      have h4 : (c.out : G ⧸ V) = (h : G ⧸ V) := QuotientGroup.eq.2 h3
      rw [QuotientGroup.out_eq'] at h4
      rw [h4]
  · rw [Finset.sum_image (fun a _ b _ hab => hout a b hab)]
    unfold cosetTrace
    change _ = ∑ q : G ⧸ U, f q
    rw [← Finset.sum_fiberwise Finset.univ π f]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.smul_sum]
    have key : ∀ g : G, g⁻¹ • (g : G ⧸ V) = ((1 : G) : G ⧸ V) := fun g => by
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel]
    refine Finset.sum_nbij' (fun q => c.out • q) (fun q => c.out⁻¹ • q) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rw [hπeq, hq, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.out_eq']
    · intro q hq
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rw [hπeq, hq]
      have h5 := key c.out
      rwa [QuotientGroup.out_eq'] at h5
    · intro q _
      simp only [inv_smul_smul]
    · intro q _
      simp only [smul_inv_smul]
    · intro q _
      rw [hfeq]

end GlobalTheory.AlmostEt

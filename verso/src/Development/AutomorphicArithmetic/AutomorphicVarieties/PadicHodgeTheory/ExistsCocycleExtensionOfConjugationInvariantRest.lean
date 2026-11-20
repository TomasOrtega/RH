import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

/- English proof (translation)
Rewrite using `[← QuotientGroup.eq, QuotientGroup.out_eq']`. Use `conv_lhs => rw [← QuotientGroup.out_eq' q]`. Both sides reduce to the same expression.
-/
private theorem zm_mem {G : Type} [Group G] (H : Subgroup G) (g : G) (q : G ⧸ H) :
    (g • q).out⁻¹ * (g * q.out) ∈ H := by
  rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  rfl

private noncomputable def zm_h {G : Type} [Group G] (H : Subgroup G) (g : G) (q : G ⧸ H) : H :=
  ⟨(g • q).out⁻¹ * (g * q.out), zm_mem H g q⟩

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [zm_h, Subgroup.coe_mul, mul_smul]`. Use `group`.
-/
private theorem zm_h_mul {G : Type} [Group G] (H : Subgroup G) (g g' : G) (q : G ⧸ H) :
    zm_h H (g * g') q = zm_h H g (g' • q) * zm_h H g' q := by
  apply Subtype.ext
  simp only [zm_h, Subgroup.coe_mul, mul_smul]
  group

/- English proof (translation)
Simplify using `only [zm_h]`. Use `group`.
-/
private theorem zm_out {G : Type} [Group G] (H : Subgroup G) (g : G) (q : G ⧸ H) :
    (g • q).out * (zm_h H g q : G) = g * q.out := by
  simp only [zm_h]
  group

/- English proof (translation)
Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H x`. Rewrite using `[MulAction.Quotient.smul_mk, smul_eq_mul, eq_comm, QuotientGroup.eq]`. Use `hN.conj_mem _ h.2 x⁻¹` as an intermediate fact. Simplify `this` using `[mul_assoc]`.
-/
private theorem zm_fix {G : Type} [Group G] (H : Subgroup G) [hN : H.Normal] (h : H) (q : G ⧸ H) :
    (h : G) • q = q := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, eq_comm, QuotientGroup.eq]
    have := hN.conj_mem _ h.2 x⁻¹
    simpa [mul_assoc] using this

/- English proof (translation)
The claim follows from `Equiv.sum_comp (MulAction.toPerm g) f`.
-/
private theorem zm_sum {G : Type} [Group G] (H : Subgroup G) [Fintype (G ⧸ H)] {V : Type} [AddCommGroup V]
    (g : G) (f : G ⧸ H → V) : ∑ q, f (g • q) = ∑ q, f q :=
  Equiv.sum_comp (MulAction.toPerm g) f

/- English proof (translation)
Use `haveI : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH`. Establish `h1 : Continuous fun g : G => g • q` using `by fun_prop`. Conclude with `(continuous_of_discreteTopology (f := fun x : G ⧸ H => x.out)).comp h1`.
-/
private theorem zm_cont {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G)
    (hH : IsOpen (H : Set G)) (q : G ⧸ H) : Continuous fun g : G => (g • q).out := by
  haveI : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  have h1 : Continuous fun g : G => g • q := by fun_prop
  exact (continuous_of_discreteTopology (f := fun x : G ⧸ H => x.out)).comp h1

/- English proof (translation)
Introduce `l _ G _ _ _ A _ _ V _ _ _ _ _ _ _ _ _ ρ hρ H hHN _ hH N c hc hs`. Use `haveI : Fintype (G ⧸ H) := Fintype.ofFinite _`. Use `set n : ℕ := Fintype.card (G ⧸ H) with hn`. Establish `hn0 : (n : ℚ_[l]) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Take `⟨a, ha⟩ : ∃ a : A, ∀ x : V, a • (n • x) = x` from `⟨algebraMap ℚ_[l] A (n : ℚ_[l])⁻¹, fun x => by`.

Rewrite using `[algebraMap_smul, ← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, inv_mul_cancel₀ hn0, one_smul]⟩`. Establish `hmul : ∀ g g' x, ρ g (ρ g' x) = ρ (g * g') x` using `fun g g' x => by`. Rewrite using `[map_mul, Module.End.mul_apply]`. Rewrite `hc` using `[mem_Z1_iff_cocycle]`. Establish `hc2 : ∀ h h' : H, c (h * h') = c h + ρ h (c h')` using `hc.2`.

Set `cor : G → V` to `fun g => ∑ q : G ⧸ H, ρ (g • q).out (c (zm_h H g q))`. Establish `hcor : cor ∈ Z1 ρ`. Use `⟨continuous_finset_sum _ fun q _ => ?_, fun g g' => ?_⟩` and prove the remaining obligations. Establish `h1` using `zm_cont H hH q`. Establish `h2 : Continuous fun g : G => zm_h H g q` using `Continuous.subtype_mk (h1.inv.mul (continuous_id.mul continuous_const)) _`.

Conclude with `hρ.comp (h1.prodMk (hc.1.comp h2))`. Simplify using `only [cor]`. Rewrite using `[← zm_sum H g' (fun q => ρ (g • q).out (c (zm_h H g q))), map_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[zm_h_mul, hc2, map_add, hmul, hmul, mul_smul, zm_out]`.

Set `c' : G ⧸ H → H → V` to `fun q h => ρ q.out (c (zm_h H h q))`. Establish `hc' : ∀ q, c' q - c ∈ N` using `fun q => hs q.out (c' q) fun g g' hg => by`. Establish `: zm_h H g q = g'`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [zm_h, zm_fix, hg, mul_assoc]`.

Simplify using `only [c', this]`. Use `⟨a • cor, (Z1 ρ).smul_mem a hcor, ?_⟩` and prove the remaining obligations. Establish `e : (fun g : H => (a • cor) g) - c = a • ∑ q : G ⧸ H, (c' q - c)`. Use function extensionality and compare the values at `h`. Establish `e1 : cor h = ∑ q : G ⧸ H, c' q h`.

Simplify using `only [cor, c', zm_fix]`. Simplify using `only [Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, e1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← hn, smul_sub, ha]`. Rewrite using `[e]`. Conclude with `N.smul_mem a (N.sum_mem fun q _ => hc' q)`.
-/
theorem UpperTheory.exists_cocycle_extension_of_conjugation_invariant_restriction :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A G V), ContAction ρ → ∀ (H : Subgroup G) [H.Normal] [H.FiniteIndex], IsOpen (H : Set G) → ∀ (N : Submodule A (H → V)), ∀ c ∈ Z1 (ρ.comp H.subtype : Representation A H V), (∀ (s : G) (c' : H → V), (∀ g g' : H, (g' : G) = s⁻¹ * g * s → c' g = ρ s (c g')) → c' - c ∈ N) → ∃ b ∈ Z1 ρ, (fun g : H => b g) - c ∈ N := by
  intro l _ G _ _ _ A _ _ V _ _ _ _ _ _ _ _ _ ρ hρ H hHN _ hH N c hc hs
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  set n : ℕ := Fintype.card (G ⧸ H) with hn
  have hn0 : (n : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  obtain ⟨a, ha⟩ : ∃ a : A, ∀ x : V, a • (n • x) = x :=
    ⟨algebraMap ℚ_[l] A (n : ℚ_[l])⁻¹, fun x => by
      rw [algebraMap_smul, ← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, inv_mul_cancel₀ hn0, one_smul]⟩
  have hmul : ∀ g g' x, ρ g (ρ g' x) = ρ (g * g') x := fun g g' x => by
    rw [map_mul, Module.End.mul_apply]
  rw [mem_Z1_iff_cocycle] at hc
  have hc2 : ∀ h h' : H, c (h * h') = c h + ρ h (c h') := hc.2
  let cor : G → V := fun g => ∑ q : G ⧸ H, ρ (g • q).out (c (zm_h H g q))
  have hcor : cor ∈ Z1 ρ := by
    refine ⟨continuous_finset_sum _ fun q _ => ?_, fun g g' => ?_⟩
    · have h1 := zm_cont H hH q
      have h2 : Continuous fun g : G => zm_h H g q :=
        Continuous.subtype_mk (h1.inv.mul (continuous_id.mul continuous_const)) _
      exact hρ.comp (h1.prodMk (hc.1.comp h2))
    · simp only [cor]
      rw [← zm_sum H g' (fun q => ρ (g • q).out (c (zm_h H g q))), map_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [zm_h_mul, hc2, map_add, hmul, hmul, mul_smul, zm_out]
  let c' : G ⧸ H → H → V := fun q h => ρ q.out (c (zm_h H h q))
  have hc' : ∀ q, c' q - c ∈ N := fun q => hs q.out (c' q) fun g g' hg => by
    have : zm_h H g q = g' := by
      apply Subtype.ext
      simp only [zm_h, zm_fix, hg, mul_assoc]
    simp only [c', this]
  refine ⟨a • cor, (Z1 ρ).smul_mem a hcor, ?_⟩
  have e : (fun g : H => (a • cor) g) - c = a • ∑ q : G ⧸ H, (c' q - c) := by
    funext h
    have e1 : cor h = ∑ q : G ⧸ H, c' q h := by
      simp only [cor, c', zm_fix]
    simp only [Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, e1, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, ← hn, smul_sub, ha]
  rw [e]
  exact N.smul_mem a (N.sum_mem fun q _ => hc' q)

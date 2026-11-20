import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1

noncomputable section

open ReciprocityTheory.Gal

namespace UpperTheory.V.Base

/- English proof (translation)
Establish `h1 : Module.length R A ≤ Module.length R (P ⧸ LinearMap.ker g)`. Use `Module.length_le_of_surjective ((LinearMap.ker g).liftQ f hk) ?_` and prove the remaining obligations. Introduce `a`. Take `⟨p, rfl⟩` from `hf a`. Conclude with `⟨Submodule.Quotient.mk p, rfl⟩`.

Establish `h2 : Module.length R (P ⧸ LinearMap.ker g) = Module.length R (LinearMap.range g)` using `(LinearMap.quotKerEquivRange g).length_eq`. Establish `h3 : Module.length R (LinearMap.range g) ≤ Module.length R B` using `Module.length_le_of_injective (LinearMap.range g).subtype Subtype.val_injective`. Conclude with `h1.trans (h2.le.trans h3)`.
-/
private theorem len_le_of_ker_le {R P A B : Type} [CommRing R] [AddCommGroup P] [Module R P] [AddCommGroup A]
    [Module R A] [AddCommGroup B] [Module R B] (f : P →ₗ[R] A) (g : P →ₗ[R] B) (hf : Function.Surjective f)
    (hk : LinearMap.ker g ≤ LinearMap.ker f) : Module.length R A ≤ Module.length R B := by
  have h1 : Module.length R A ≤ Module.length R (P ⧸ LinearMap.ker g) := by
    refine Module.length_le_of_surjective ((LinearMap.ker g).liftQ f hk) ?_
    intro a
    obtain ⟨p, rfl⟩ := hf a
    exact ⟨Submodule.Quotient.mk p, rfl⟩
  have h2 : Module.length R (P ⧸ LinearMap.ker g) = Module.length R (LinearMap.range g) :=
    (LinearMap.quotKerEquivRange g).length_eq
  have h3 : Module.length R (LinearMap.range g) ≤ Module.length R B :=
    Module.length_le_of_injective (LinearMap.range g).subtype Subtype.val_injective
  exact h1.trans (h2.le.trans h3)

variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M]

omit [IsTopologicalAddGroup M] [DiscreteTopology M] in

instance continuousConstSMul_sub (N : Submodule R M) : ContinuousConstSMul R N :=
  ⟨fun c => (continuous_subtype_val.const_smul c).subtype_mk _⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/- English proof (translation)
Establish `hm` using `QuotientGroup.eq.mp e`. Use `⟨⟨((a⁻¹ * b : U) : G), Subgroup.mem_subgroupOf.mp hm⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[Subgroup.coe_inclusion]`.
-/
private theorem exists_mul_of_mk_eq {U' U : Subgroup G} (h : U' ≤ U) {a b : U}
    (e : (QuotientGroup.mk a : U ⧸ U'.subgroupOf U) = QuotientGroup.mk b) :
    ∃ u : U', b = a * Subgroup.inclusion h u := by
  have hm := QuotientGroup.eq.mp e
  refine ⟨⟨((a⁻¹ * b : U) : G), Subgroup.mem_subgroupOf.mp hm⟩, ?_⟩
  apply Subtype.ext
  simp [Subgroup.coe_inclusion]

/- English proof (translation)
Use `⟨⟨(g : K)⁻¹ * u * g, Subgroup.Normal.conj_mem' ‹_› _ u.2 _⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[mul_assoc]`.
-/
private theorem exists_inclusion_mul_eq_mul_inclusion_of_normal {K : Type} [Group K] {U' U : Subgroup K} [U'.Normal] (h : U' ≤ U) (u : U')
    (g : U) : ∃ v : U', Subgroup.inclusion h u * g = g * Subgroup.inclusion h v := by
  refine ⟨⟨(g : K)⁻¹ * u * g, Subgroup.Normal.conj_mem' ‹_› _ u.2 _⟩, ?_⟩
  apply Subtype.ext
  simp [mul_assoc]

/- English proof (translation)
Establish `hm : ∀ s : U, ∃ m : M, ∀ u : U', ρ s (z.1 (conjHom U' (s : G) u)) - z.1 u = ρ u m - m`. Introduce `s`. Take `⟨z', hz'e, hz'⟩` from `conjU_mk ρ U' (s : G) z`. Establish `hinv : conjU ρ U' (s : G) (Submodule.Quotient.mk z) = Submodule.Quotient.mk z` using `hz s`. Rewrite `hinv` using `[hz'e]`.

Take `⟨m, hm⟩` from `(mk_eq_mk ρ U' z' z).mp hinv`. Conclude with `⟨m, fun u => by rw [← hz' u]; exact hm u⟩`. Use `choose mS hmS using hm`. Establish `hcz : ∀ a b : U', z.1 (a * b) = z.1 a + ρ a (z.1 b)` using `fun a b => z.2.2 a b`. Establish `hsp : ∀ g : U, ∃ t : U', g = (QuotientGroup.mk g : U ⧸ U'.subgroupOf U).out * Subgroup.inclusion h t` using `fun g => exists_mul_of_mk_eq h (QuotientGroup.out_eq' (QuotientGroup.mk g : U ⧸ U'.subgroupOf U))`.

Use `choose v hv using hsp`. Set `y0 : U → M` to `fun g => mS (QuotientGroup.mk g : U ⧸ U'.subgroupOf U).out + ρ (QuotientGroup.mk g : U ⧸ U'.subgroupOf U).out (z.1 (v g))`. Establish `hR0 : ∀ (u : U') (g : U), y0 (g * Subgroup.inclusion h u) = y0 g + ρ g (z.1 u)`. Introduce `u g`. Establish `hmk : (QuotientGroup.mk (g * Subgroup.inclusion h u) : U ⧸ U'.subgroupOf U) = QuotientGroup.mk g`.

Rewrite using `[QuotientGroup.eq]`. Simplify using `[Subgroup.mem_subgroupOf, mul_assoc]`. Establish `e1` using `hv (g * Subgroup.inclusion h u)`. Establish `e0` using `hv g`. Simplify using `only [y0]`.

Generalize the expression as in `v (g * Subgroup.inclusion h u) = t at e1 ⊢`. Rewrite `e1`, the goal using `[hmk]`. Generalize the expression as in `(QuotientGroup.mk g : U ⧸ U'.subgroupOf U).out = s at e0 e1 ⊢`. Establish `eg : (g : G) = s * (v g)` using `congrArg Subtype.val e0`. Establish `ht : t = v g * u`.

Apply `Subgroup.inclusion_injective h` to reduce the goal to its premises. Rewrite using `[map_mul]`. Apply `mul_left_cancel (a := s)` to reduce the goal to its premises. Rewrite using `[← e1, ← mul_assoc, ← e0]`. Rewrite using `[ht, hcz, map_add, eg, map_mul, Module.End.mul_apply, add_assoc]`.

Establish `hL0 : ∀ (u : U') (g : U), y0 (Subgroup.inclusion h u * g) = z.1 u + ρ u (y0 g)`. Introduce `u g`. Take `⟨u', hu'⟩` from `exists_inclusion_mul_eq_mul_inclusion_of_normal h u g`. Establish `hmk : (QuotientGroup.mk (Subgroup.inclusion h u * g) : U ⧸ U'.subgroupOf U) = QuotientGroup.mk g`. Rewrite using `[hu', QuotientGroup.eq]`.

Simplify using `[Subgroup.mem_subgroupOf, mul_assoc]`. Establish `e1` using `hv (Subgroup.inclusion h u * g)`. Establish `e0` using `hv g`. Simplify using `only [y0]`. Generalize the expression as in `v (Subgroup.inclusion h u * g) = t at e1 ⊢`.

Rewrite `e1`, the goal using `[hmk]`. Generalize the expression as in `(QuotientGroup.mk g : U ⧸ U'.subgroupOf U).out = s at e0 e1 ⊢`. Establish `eg : (g : G) = s * (v g)` using `congrArg Subtype.val e0`. Establish `hsc : (s : G) * (conjHom U' (s : G) u : G) = u * s`. Simplify using `[conjHom, mul_assoc]`.

Establish `ht : t = conjHom U' (s : G) u * v g`. Apply `Subgroup.inclusion_injective h` to reduce the goal to its premises. Apply `mul_left_cancel (a := s)` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Establish `e1' : (u : G) * g = s * t` using `congrArg Subtype.val e1`.

Use `show (s : G) * t = s * ((conjHom U' (s : G) u : G) * v g)`. Rewrite using `[← e1', ← mul_assoc, hsc, eg, mul_assoc]`. Establish `hc : ρ s (z.1 (conjHom U' (s : G) u)) = z.1 u + (ρ u (mS s) - mS s)`. Rewrite using `[← hmS s u]`. Normalize the expressions using the abelian group laws.

Establish `hcomm : ∀ x : M, ρ s (ρ (conjHom U' (s : G) u : G) x) = ρ u (ρ s x)`. Introduce `x`. Rewrite using `[← Module.End.mul_apply, ← map_mul, hsc, map_mul, Module.End.mul_apply]`. Rewrite using `[ht, hcz, map_add, hc, hcomm, map_add]`. Normalize the expressions using the abelian group laws.

Establish `hc1 : ∀ u : U', ρ u (y0 1) = y0 1`. Introduce `u`. Establish `a1` using `hL0 u 1`. Establish `a2` using `hR0 u 1`. Rewrite `a1` using `[mul_one]`.

Rewrite `a2` using `[one_mul]`. Simplify using `only [OneMemClass.coe_one, map_one, Module.End.one_apply] at a2`. Establish `a3` using `a1.symm.trans a2`. Rewrite `a3` using `[add_comm]`. Conclude with `add_right_cancel a3`.

Establish `hR1 : ∀ (u : U') (g : U), y0 (g * Subgroup.inclusion h u) - y0 1 = (y0 g - y0 1) + ρ g (z.1 u)`. Introduce `u g`. Rewrite using `[hR0]`. Normalize the expressions using the abelian group laws. Use `⟨fun g => y0 g - y0 1, ?_, by simp, fun u g => ?_, hR1⟩` and prove the remaining obligations.

Rewrite using `[continuous_iff_continuousAt]`. Introduce `g`. Establish `hι : Topology.IsOpenEmbedding (Subgroup.inclusion h)` using `Topology.IsOpenEmbedding.inclusion (s := (U' : Set G)) (t := (U : Set G)) h ho`. Establish `hψ : Topology.IsOpenEmbedding (fun u : U' => g * Subgroup.inclusion h u)` using `(Homeomorph.mulLeft g).isOpenEmbedding.comp hι`. Establish `key : ContinuousAt (fun x => y0 x - y0 1) (g * Subgroup.inclusion h 1)`.

Rewrite using `[← hψ.continuousAt_iff]`. Establish `hfun : ((fun x => y0 x - y0 1) ∘ fun u : U' => g * Subgroup.inclusion h u) = fun u => (y0 g - y0 1) + ρ g (z.1 u)`. Use function extensionality and compare the values at `u`. Conclude with `hR1 u g`. Rewrite using `[hfun]`.

Conclude with `(continuous_const.add (continuous_of_discreteTopology.comp z.2.1)).continuousAt`. Simplify using `only [map_one, mul_one] at key`. Conclude with `key`. Use `show y0 (Subgroup.inclusion h u * g) - y0 1 = z.1 u + ρ u (y0 g - y0 1)`. Rewrite using `[hL0, map_sub, hc1]`.

Normalize the expressions using the abelian group laws.
-/
private theorem exists_ext (ρ : Representation R G M) (hρ : ContAction ρ) {U' U : Subgroup G} [U'.Normal] (h : U' ≤ U)
    (ho : IsOpen (U'.subgroupOf U : Set U)) (z : Z1U ρ U') (hz : Submodule.Quotient.mk z ∈ invariantsUnderSubgroupH1 ρ U U') :
    ∃ y : U → M, Continuous y ∧ y 1 = 0 ∧
      (∀ (u : U') (g : U), y (Subgroup.inclusion h u * g) = z.1 u + ρ u (y g)) ∧
      ∀ (u : U') (g : U), y (g * Subgroup.inclusion h u) = y g + ρ g (z.1 u) := by
  have hm : ∀ s : U, ∃ m : M, ∀ u : U', ρ s (z.1 (conjHom U' (s : G) u)) - z.1 u = ρ u m - m := by
    intro s
    obtain ⟨z', hz'e, hz'⟩ := conjU_mk ρ U' (s : G) z
    have hinv : conjU ρ U' (s : G) (Submodule.Quotient.mk z) = Submodule.Quotient.mk z := hz s
    rw [hz'e] at hinv
    obtain ⟨m, hm⟩ := (mk_eq_mk ρ U' z' z).mp hinv
    exact ⟨m, fun u => by rw [← hz' u]; exact hm u⟩
  choose mS hmS using hm
  have hcz : ∀ a b : U', z.1 (a * b) = z.1 a + ρ a (z.1 b) := fun a b => z.2.2 a b
  have hsp : ∀ g : U, ∃ t : U',
      g = (QuotientGroup.mk g : U ⧸ U'.subgroupOf U).out * Subgroup.inclusion h t :=
    fun g => exists_mul_of_mk_eq h (QuotientGroup.out_eq' (QuotientGroup.mk g : U ⧸ U'.subgroupOf U))
  choose v hv using hsp
  let y0 : U → M := fun g => mS (QuotientGroup.mk g : U ⧸ U'.subgroupOf U).out +
    ρ (QuotientGroup.mk g : U ⧸ U'.subgroupOf U).out (z.1 (v g))
  have hR0 : ∀ (u : U') (g : U), y0 (g * Subgroup.inclusion h u) = y0 g + ρ g (z.1 u) := by
    intro u g
    have hmk : (QuotientGroup.mk (g * Subgroup.inclusion h u) : U ⧸ U'.subgroupOf U) = QuotientGroup.mk g := by
      rw [QuotientGroup.eq]
      simp [Subgroup.mem_subgroupOf, mul_assoc]
    have e1 := hv (g * Subgroup.inclusion h u)
    have e0 := hv g
    simp only [y0]
    generalize v (g * Subgroup.inclusion h u) = t at e1 ⊢
    rw [hmk] at e1 ⊢
    generalize (QuotientGroup.mk g : U ⧸ U'.subgroupOf U).out = s at e0 e1 ⊢
    have eg : (g : G) = s * (v g) := congrArg Subtype.val e0
    have ht : t = v g * u := by
      apply Subgroup.inclusion_injective h
      rw [map_mul]
      apply mul_left_cancel (a := s)
      rw [← e1, ← mul_assoc, ← e0]
    rw [ht, hcz, map_add, eg, map_mul, Module.End.mul_apply, add_assoc]
  have hL0 : ∀ (u : U') (g : U), y0 (Subgroup.inclusion h u * g) = z.1 u + ρ u (y0 g) := by
    intro u g
    obtain ⟨u', hu'⟩ := exists_inclusion_mul_eq_mul_inclusion_of_normal h u g
    have hmk : (QuotientGroup.mk (Subgroup.inclusion h u * g) : U ⧸ U'.subgroupOf U) = QuotientGroup.mk g := by
      rw [hu', QuotientGroup.eq]
      simp [Subgroup.mem_subgroupOf, mul_assoc]
    have e1 := hv (Subgroup.inclusion h u * g)
    have e0 := hv g
    simp only [y0]
    generalize v (Subgroup.inclusion h u * g) = t at e1 ⊢
    rw [hmk] at e1 ⊢
    generalize (QuotientGroup.mk g : U ⧸ U'.subgroupOf U).out = s at e0 e1 ⊢
    have eg : (g : G) = s * (v g) := congrArg Subtype.val e0
    have hsc : (s : G) * (conjHom U' (s : G) u : G) = u * s := by
      simp [conjHom, mul_assoc]
    have ht : t = conjHom U' (s : G) u * v g := by
      apply Subgroup.inclusion_injective h
      apply mul_left_cancel (a := s)
      apply Subtype.ext
      have e1' : (u : G) * g = s * t := congrArg Subtype.val e1
      show (s : G) * t = s * ((conjHom U' (s : G) u : G) * v g)
      rw [← e1', ← mul_assoc, hsc, eg, mul_assoc]
    have hc : ρ s (z.1 (conjHom U' (s : G) u)) = z.1 u + (ρ u (mS s) - mS s) := by
      rw [← hmS s u]
      abel
    have hcomm : ∀ x : M, ρ s (ρ (conjHom U' (s : G) u : G) x) = ρ u (ρ s x) := by
      intro x
      rw [← Module.End.mul_apply, ← map_mul, hsc, map_mul, Module.End.mul_apply]
    rw [ht, hcz, map_add, hc, hcomm, map_add]
    abel
  have hc1 : ∀ u : U', ρ u (y0 1) = y0 1 := by
    intro u
    have a1 := hL0 u 1
    have a2 := hR0 u 1
    rw [mul_one] at a1
    rw [one_mul] at a2
    simp only [OneMemClass.coe_one, map_one, Module.End.one_apply] at a2
    have a3 := a1.symm.trans a2
    rw [add_comm] at a3
    exact add_right_cancel a3
  have hR1 : ∀ (u : U') (g : U), y0 (g * Subgroup.inclusion h u) - y0 1 = (y0 g - y0 1) + ρ g (z.1 u) := by
    intro u g
    rw [hR0]
    abel
  refine ⟨fun g => y0 g - y0 1, ?_, by simp, fun u g => ?_, hR1⟩
  · rw [continuous_iff_continuousAt]
    intro g
    have hι : Topology.IsOpenEmbedding (Subgroup.inclusion h) :=
      Topology.IsOpenEmbedding.inclusion (s := (U' : Set G)) (t := (U : Set G)) h ho
    have hψ : Topology.IsOpenEmbedding (fun u : U' => g * Subgroup.inclusion h u) :=
      (Homeomorph.mulLeft g).isOpenEmbedding.comp hι
    have key : ContinuousAt (fun x => y0 x - y0 1) (g * Subgroup.inclusion h 1) := by
      rw [← hψ.continuousAt_iff]
      have hfun : ((fun x => y0 x - y0 1) ∘ fun u : U' => g * Subgroup.inclusion h u) =
          fun u => (y0 g - y0 1) + ρ g (z.1 u) := by
        funext u
        exact hR1 u g
      rw [hfun]
      exact (continuous_const.add (continuous_of_discreteTopology.comp z.2.1)).continuousAt
    simp only [map_one, mul_one] at key
    exact key
  · show y0 (Subgroup.inclusion h u * g) - y0 1 = z.1 u + ρ u (y0 g - y0 1)
    rw [hL0, map_sub, hc1]
    abel

/- English proof (translation)
Use `⟨⟨(g : K)⁻¹ * u * g, Subgroup.Normal.conj_mem' ‹_› _ u.2 _⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[mul_assoc]`.
-/
private theorem exists_normal_conj_inclusion {K : Type} [Group K] {U' U : Subgroup K} [U'.Normal] (h : U' ≤ U) (u : U')
    (g : U) : ∃ v : U', Subgroup.inclusion h u * g = g * Subgroup.inclusion h v := by
  refine ⟨⟨(g : K)⁻¹ * u * g, Subgroup.Normal.conj_mem' ‹_› _ u.2 _⟩, ?_⟩
  apply Subtype.ext
  simp [mul_assoc]

omit [IsTopologicalGroup G] [DiscreteTopology M] in

/- English proof (translation)
Use `set F : U → U → M := fun a b => ρ a (y b) - y (a * b) + y a with hF`. Establish `hFr : ∀ (a b : U) (u : U'), F a (b * Subgroup.inclusion h u) = F a b`. Introduce `a b u`. Simplify using `only [hF]`. Rewrite using `[← mul_assoc, hR, hR]`.

Simplify using `only [map_add, Subgroup.coe_mul, map_mul, Module.End.mul_apply]`. Normalize the expressions using the abelian group laws. Establish `hFl : ∀ (a b : U) (u : U'), F (a * Subgroup.inclusion h u) b = F a b`. Introduce `a b u`. Take `⟨v, hv⟩` from `exists_normal_conj_inclusion h u b`.

Establish `key : ρ u (y b) = y b + ρ b (z v) - z u`. Establish `e1` using `hL u b`. Rewrite `e1` using `[hv, hR]`. Rewrite using `[e1]`. Normalize the expressions using the abelian group laws.

Simplify using `only [hF]`. Rewrite using `[mul_assoc a, hv, ← mul_assoc, hR, hR]`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inclusion, map_mul, Module.End.mul_apply, key, map_add, map_sub]`. Normalize the expressions using the abelian group laws. Establish `hinv : ∀ (a b : U) (u : U'), ρ u (F a b) = F a b`.

Introduce `a b u`. Take `⟨v, hv⟩` from `exists_normal_conj_inclusion h u a`. Establish `e1 : ∀ g : U, ρ u (y g) = y (Subgroup.inclusion h u * g) - z u`. Introduce `g`. Rewrite using `[hL]`.

Normalize the expressions using the abelian group laws. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hF, map_add, map_sub, e1, mul_assoc]`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inclusion, map_mul, Module.End.mul_apply]`. Normalize the expressions using the abelian group laws.

Use `_ = F (a * Subgroup.inclusion h v) b := by rw [hv]`. Use `_ = F a b := hFl a b v`. Establish `hN : ∀ a b : U, F a b ∈ Representation.invariants ((ρ.comp U.subtype).comp (U'.subgroupOf U).subtype)`. Introduce `a b v`. Conclude with `hinv a b ⟨(v : U), Subgroup.mem_subgroupOf.mp v.2⟩`.

Establish `hWF : ∀ a b : U, F (QuotientGroup.mk a : U ⧸ U'.subgroupOf U).out (QuotientGroup.mk b : U ⧸ U'.subgroupOf U).out = F a b`. Introduce `a b`. Take `⟨u, hu⟩` from `exists_mul_of_mk_eq h (QuotientGroup.out_eq' (QuotientGroup.mk a : U ⧸ U'.subgroupOf U)).symm`. Take `⟨v, hv⟩` from `exists_mul_of_mk_eq h (QuotientGroup.out_eq' (QuotientGroup.mk b : U ⧸ U'.subgroupOf U)).symm`. Rewrite using `[hu, hv, hFl, hFr]`.

Set `W : (U ⧸ U'.subgroupOf U) × (U ⧸ U'.subgroupOf U) → Representation.invariants ((ρ.comp U.subtype).comp (U'.subgroupOf U).subtype)` to `fun p => ⟨F p.1.out p.2.out, hN _ _⟩`. Establish `hW : ∀ a b : U, (W (QuotientGroup.mk a, QuotientGroup.mk b) : M) = F a b` using `hWF`. Use `⟨⟨W, continuous_of_discreteTopology, ?_⟩, fun a b => hW a b⟩` and prove the remaining obligations. Introduce `p q r`. Take `⟨a, rfl⟩` from `QuotientGroup.mk_surjective p`.

Take `⟨b, rfl⟩` from `QuotientGroup.mk_surjective q`. Take `⟨c, rfl⟩` from `QuotientGroup.mk_surjective r`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]`. Use `show ρ a (W (QuotientGroup.mk b, QuotientGroup.mk c) : M) - (W (QuotientGroup.mk (a * b), QuotientGroup.mk c) : M) + (W (QuotientGroup.mk a, QuotientGroup.mk (b * c)) : M) - (W (QuotientGroup.mk a, QuotientGroup.mk b) : M) = 0`.

Rewrite using `[hW, hW, hW, hW]`. Simplify using `only [hF, map_add, map_sub, Subgroup.coe_mul, map_mul, Module.End.mul_apply, mul_assoc]`. Normalize the expressions using the abelian group laws.
-/
private theorem exists_infl (ρ : Representation R G M) {U' U : Subgroup G} [U'.Normal] (h : U' ≤ U)
    [DiscreteTopology (U ⧸ U'.subgroupOf U)] (z : U' → M) (y : U → M)
    (hL : ∀ (u : U') (g : U), y (Subgroup.inclusion h u * g) = z u + ρ u (y g))
    (hR : ∀ (u : U') (g : U), y (g * Subgroup.inclusion h u) = y g + ρ g (z u)) :
    ∃ w : Z2 (quotRep ρ U U'), ∀ a b : U,
      (w.1 (QuotientGroup.mk a, QuotientGroup.mk b) : M) = ρ a (y b) - y (a * b) + y a := by
  set F : U → U → M := fun a b => ρ a (y b) - y (a * b) + y a with hF
  have hFr : ∀ (a b : U) (u : U'), F a (b * Subgroup.inclusion h u) = F a b := by
    intro a b u
    simp only [hF]
    rw [← mul_assoc, hR, hR]
    simp only [map_add, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
    abel
  have hFl : ∀ (a b : U) (u : U'), F (a * Subgroup.inclusion h u) b = F a b := by
    intro a b u
    obtain ⟨v, hv⟩ := exists_normal_conj_inclusion h u b
    have key : ρ u (y b) = y b + ρ b (z v) - z u := by
      have e1 := hL u b
      rw [hv, hR] at e1
      rw [e1]
      abel
    simp only [hF]
    rw [mul_assoc a, hv, ← mul_assoc, hR, hR]
    simp only [Subgroup.coe_mul, Subgroup.coe_inclusion, map_mul, Module.End.mul_apply, key,
      map_add, map_sub]
    abel
  have hinv : ∀ (a b : U) (u : U'), ρ u (F a b) = F a b := by
    intro a b u
    obtain ⟨v, hv⟩ := exists_normal_conj_inclusion h u a
    have e1 : ∀ g : U, ρ u (y g) = y (Subgroup.inclusion h u * g) - z u := by
      intro g
      rw [hL]
      abel
    calc ρ u (F a b) = F (Subgroup.inclusion h u * a) b := by
          simp only [hF, map_add, map_sub, e1, mul_assoc]
          simp only [Subgroup.coe_mul, Subgroup.coe_inclusion, map_mul, Module.End.mul_apply]
          abel
      _ = F (a * Subgroup.inclusion h v) b := by rw [hv]
      _ = F a b := hFl a b v
  have hN : ∀ a b : U,
      F a b ∈ Representation.invariants ((ρ.comp U.subtype).comp (U'.subgroupOf U).subtype) := by
    intro a b v
    exact hinv a b ⟨(v : U), Subgroup.mem_subgroupOf.mp v.2⟩
  have hWF : ∀ a b : U,
      F (QuotientGroup.mk a : U ⧸ U'.subgroupOf U).out (QuotientGroup.mk b : U ⧸ U'.subgroupOf U).out
        = F a b := by
    intro a b
    obtain ⟨u, hu⟩ := exists_mul_of_mk_eq h (QuotientGroup.out_eq' (QuotientGroup.mk a : U ⧸ U'.subgroupOf U)).symm
    obtain ⟨v, hv⟩ := exists_mul_of_mk_eq h (QuotientGroup.out_eq' (QuotientGroup.mk b : U ⧸ U'.subgroupOf U)).symm
    rw [hu, hv, hFl, hFr]
  let W : (U ⧸ U'.subgroupOf U) × (U ⧸ U'.subgroupOf U) →
      Representation.invariants ((ρ.comp U.subtype).comp (U'.subgroupOf U).subtype) :=
    fun p => ⟨F p.1.out p.2.out, hN _ _⟩
  have hW : ∀ a b : U, (W (QuotientGroup.mk a, QuotientGroup.mk b) : M) = F a b := hWF
  refine ⟨⟨W, continuous_of_discreteTopology, ?_⟩, fun a b => hW a b⟩
  intro p q r
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective p
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective r
  apply Subtype.ext
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  show ρ a (W (QuotientGroup.mk b, QuotientGroup.mk c) : M) - (W (QuotientGroup.mk (a * b), QuotientGroup.mk c) : M)
    + (W (QuotientGroup.mk a, QuotientGroup.mk (b * c)) : M) - (W (QuotientGroup.mk a, QuotientGroup.mk b) : M) = 0
  rw [hW, hW, hW, hW]
  simp only [hF, map_add, map_sub, Subgroup.coe_mul, map_mul, Module.End.mul_apply, mul_assoc]
  abel

omit [IsTopologicalGroup G] [DiscreteTopology M] in
/- English proof (translation)
Establish `hw0 : w ∈ Submodule.comap (Z2 (quotRep ρ U U')).subtype (B2 (quotRep ρ U U'))` using `(Submodule.Quotient.mk_eq_zero _).mp hw`. Establish `hw' : (w : _ → _) ∈ B2 (quotRep ρ U U')` using `hw0`. Take `⟨cb, hcb, hd⟩` from `(separated_dvr_second_cohomology_mem _ _).mp hw'`. Use `⟨fun a => (cb (QuotientGroup.mk a) : M), ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `continuous_subtype_val.comp (hcb.comp continuous_coinduced_rng)`.

Introduce `u`. Establish `h1 : (QuotientGroup.mk (Subgroup.inclusion h u) : U ⧸ U'.subgroupOf U) = QuotientGroup.mk 1`. Rewrite using `[QuotientGroup.mk_one, QuotientGroup.eq_one_iff]`. Conclude with `Subgroup.mem_subgroupOf.mpr u.2`. Use `show ((cb _ : _) : M) = cb _`.

Rewrite using `[h1]`. Introduce `a b`. Rewrite using `[← hd]`. Both sides reduce to the same expression.
-/
private theorem exists_of_mk_eq_zero (ρ : Representation R G M) {U' U : Subgroup G} [U'.Normal] (h : U' ≤ U)
    (w : Z2 (quotRep ρ U U')) (hw : (Submodule.Quotient.mk w : H2 (quotRep ρ U U')) = 0) :
    ∃ c : U → M, Continuous c ∧ (∀ u : U', c (Subgroup.inclusion h u) = c 1) ∧ ∀ a b : U,
      (w.1 (QuotientGroup.mk a, QuotientGroup.mk b) : M) = ρ a (c b) - c (a * b) + c a := by
  have hw0 : w ∈ Submodule.comap (Z2 (quotRep ρ U U')).subtype (B2 (quotRep ρ U U')) :=
    (Submodule.Quotient.mk_eq_zero _).mp hw
  have hw' : (w : _ → _) ∈ B2 (quotRep ρ U U') := hw0
  obtain ⟨cb, hcb, hd⟩ := (separated_dvr_second_cohomology_mem _ _).mp hw'
  refine ⟨fun a => (cb (QuotientGroup.mk a) : M), ?_, ?_, ?_⟩
  · exact continuous_subtype_val.comp (hcb.comp continuous_coinduced_rng)
  · intro u
    have h1 : (QuotientGroup.mk (Subgroup.inclusion h u) : U ⧸ U'.subgroupOf U) = QuotientGroup.mk 1 := by
      rw [QuotientGroup.mk_one, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr u.2
    show ((cb _ : _) : M) = cb _
    rw [h1]
  · intro a b
    rw [← hd]
    rfl

omit [IsTopologicalGroup G] [DiscreteTopology M] in
/- English proof (translation)
Establish `hz1 : (z : U' → M) 1 = 0`. Establish `h0` using `z.2.2 1 1`. Simplify using `using h0`. Establish `hy1 : y 1 = 0`. Establish `h0` using `hz 1`.

Rewrite `h0` using `[map_one]`. Rewrite using `[h0, hz1]`. Establish `hc0 : c 1 = 0`. Establish `h0` using `e 1 1`. Simplify using `at h0`.

Rewrite using `[h0, hy1]`. Establish `hx : (fun g => y g - c g) ∈ Z1U ρ U`. Use `⟨hy.sub hc, fun a b => ?_⟩` and prove the remaining obligations. Use `show y (a * b) - c (a * b) = (y a - c a) + ρ a (y b - c b)`. Rewrite using `[map_sub]`.

Establish `h0` using `e a b`. Rewrite `h0`, the goal using `[← sub_eq_zero]`. Rewrite using `[← h0]`. Normalize the expressions using the abelian group laws. Take `⟨x', hx'e, hx'⟩` from `resU_mk ρ h ⟨_, hx⟩`.

Use `⟨Submodule.Quotient.mk ⟨_, hx⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hx'e]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `u`.

Rewrite using `[hx' u]`. Use `show y (Subgroup.inclusion h u) - c (Subgroup.inclusion h u) = z.1 u`. Rewrite using `[hz u, hc1 u, hc0, sub_zero]`.
-/
private theorem mem_range_resU (ρ : Representation R G M) {U' U : Subgroup G} (h : U' ≤ U) (z : Z1U ρ U')
    (y c : U → M) (hy : Continuous y) (hc : Continuous c) (hz : ∀ u : U', y (Subgroup.inclusion h u) = z.1 u)
    (hc1 : ∀ u : U', c (Subgroup.inclusion h u) = c 1)
    (e : ∀ a b : U, ρ a (c b) - c (a * b) + c a = ρ a (y b) - y (a * b) + y a) :
    Submodule.Quotient.mk z ∈ LinearMap.range (resU ρ h) := by
  have hz1 : (z : U' → M) 1 = 0 := by
    have h0 := z.2.2 1 1
    simpa using h0
  have hy1 : y 1 = 0 := by
    have h0 := hz 1
    rw [map_one] at h0
    rw [h0, hz1]
  have hc0 : c 1 = 0 := by
    have h0 := e 1 1
    simp at h0
    rw [h0, hy1]
  have hx : (fun g => y g - c g) ∈ Z1U ρ U := by
    refine ⟨hy.sub hc, fun a b => ?_⟩
    show y (a * b) - c (a * b) = (y a - c a) + ρ a (y b - c b)
    rw [map_sub]
    have h0 := e a b
    rw [← sub_eq_zero] at h0 ⊢
    rw [← h0]
    abel
  obtain ⟨x', hx'e, hx'⟩ := resU_mk ρ h ⟨_, hx⟩
  refine ⟨Submodule.Quotient.mk ⟨_, hx⟩, ?_⟩
  rw [hx'e]
  congr 1
  apply Subtype.ext
  funext u
  rw [hx' u]
  show y (Subgroup.inclusion h u) - c (Subgroup.inclusion h u) = z.1 u
  rw [hz u, hc1 u, hc0, sub_zero]

set_option maxHeartbeats 800000 in

/- English proof (translation)
Use `haveI : DiscreteTopology (U ⧸ U'.subgroupOf U) := QuotientGroup.discreteTopology ho`. Set `P : Submodule R (↥(Z1U ρ U') × ((U → M) × ↥(Z2 (quotRep ρ U U'))))` to `{ carrier := {x | (Submodule.Quotient.mk x.1 : H1U ρ U') ∈ invariantsUnderSubgroupH1 ρ U U' ∧ Continuous x.2.1 ∧ (∀ u : U', x.2.1 (Subgroup.inclusion h u) = x.1.1 u) ∧ ∀ a b : U, (x.2.2.1 (QuotientGroup.mk a, QuotientGroup.mk b) : M) = ρ a (x.2.1 b) - x.2.1 (a * b) + x.2.1 a} add …`. Introduce and unpack `x x' ⟨h1, h2, h3, h4⟩ ⟨h1', h2', h3', h4'⟩`. Use `⟨?_, h2.add h2', fun u => ?_, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[Prod.fst_add, Submodule.Quotient.mk_add]`.

Conclude with `add_mem h1 h1'`. Simplify using `[h3 u, h3' u]`. Simplify using `[h4 a b, h4' a b]`. Normalize the expressions using the abelian group laws. Use the proof step `zero_mem' := by`.

Use `⟨?_, continuous_const, fun u => ?_, fun a b => ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Use the proof step `smul_mem' := by`.

Introduce and unpack `r x ⟨h1, h2, h3, h4⟩`. Use `⟨?_, h2.const_smul r, fun u => ?_, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[Prod.smul_fst, Submodule.Quotient.mk_smul]`. Conclude with `Submodule.smul_mem _ r h1`. Simplify using `[h3 u]`.

Simplify using `[h4 a b, smul_sub, smul_add] }`. Set `q1 : ↥(Z1U ρ U') →ₗ[R] H1U ρ U'` to `Submodule.mkQ _`. Set `q2 : ↥(invariantsUnderSubgroupH1 ρ U U') →ₗ[R] resCoker ρ h` to `Submodule.mkQ _`. Set `q3 : ↥(Z2 (quotRep ρ U U')) →ₗ[R] H2 (quotRep ρ U U')` to `Submodule.mkQ _`. Establish `hq1 : Function.Surjective q1` using `Submodule.mkQ_surjective _`.

Establish `hq2 : Function.Surjective q2` using `Submodule.mkQ_surjective _`. Set `f : P →ₗ[R] resCoker ρ h` to `q2 ∘ₗ LinearMap.codRestrict (invariantsUnderSubgroupH1 ρ U U') (q1 ∘ₗ LinearMap.fst R _ _ ∘ₗ P.subtype) (fun x => x.2.1)`. Set `g : P →ₗ[R] H2 (quotRep ρ U U')` to `q3 ∘ₗ (LinearMap.snd R _ _ ∘ₗ LinearMap.snd R _ _) ∘ₗ P.subtype`. Establish `hfs : Function.Surjective f`. Introduce `r`.

Take `⟨x, rfl⟩` from `hq2 r`. Take `⟨z, hz⟩` from `hq1 (x : H1U ρ U')`. Establish `hz' : (Submodule.Quotient.mk z : H1U ρ U') ∈ invariantsUnderSubgroupH1 ρ U U'`. Establish `hz3 : (Submodule.Quotient.mk z : H1U ρ U') = x` using `hz`. Rewrite using `[hz3]`.

Conclude with `x.2`. Establish `hex` using `exists_ext ρ hρ h ho z hz'`. Take `⟨y, hy, hy1, hL, hR⟩` from `hex`. Take `⟨w, hw⟩` from `exists_infl ρ h z.1 y hL hR`. Use `⟨⟨(z, y, w), hz', hy, fun u => ?_, hw⟩, ?_⟩` and prove the remaining obligations.

Establish `e` using `hR u 1`. Simplify `e` using `[hy1]`. Conclude with `congrArg q2 (Subtype.ext hz)`. Establish `hker : LinearMap.ker g ≤ LinearMap.ker f`. Introduce `x hx`.

Rewrite `hx`, the goal using `[LinearMap.mem_ker]`. Take `⟨⟨z, y, w⟩, h1, h2, h3, h4⟩` from `x`. Establish `hw0 : (Submodule.Quotient.mk w : H2 (quotRep ρ U U')) = 0` using `hx`. Take `⟨c, hc, hc1, hcw⟩` from `exists_of_mk_eq_zero ρ h w hw0`. Establish `hm` using `mem_range_resU ρ h z y c h2 hc h3 hc1 (fun a b => (hcw a b).symm.trans (h4 a b))`.

Conclude with `(Submodule.Quotient.mk_eq_zero _ (x := (⟨_, h1⟩ : invariantsUnderSubgroupH1 ρ U U'))).mpr hm`. Conclude with `len_le_of_ker_le f g hfs hker`.
-/
theorem length_restriction_coker_le_H2 (ρ : Representation R G M) (hρ : ContAction ρ) {U' U : Subgroup G} [U'.Normal]
    (h : U' ≤ U) (ho : IsOpen (U'.subgroupOf U : Set U)) :
    Module.length R (resCoker ρ h) ≤ Module.length R (H2 (quotRep ρ U U')) := by
  haveI : DiscreteTopology (U ⧸ U'.subgroupOf U) := QuotientGroup.discreteTopology ho
  let P : Submodule R (↥(Z1U ρ U') × ((U → M) × ↥(Z2 (quotRep ρ U U')))) :=
    { carrier := {x | (Submodule.Quotient.mk x.1 : H1U ρ U') ∈ invariantsUnderSubgroupH1 ρ U U' ∧ Continuous x.2.1 ∧
        (∀ u : U', x.2.1 (Subgroup.inclusion h u) = x.1.1 u) ∧
        ∀ a b : U, (x.2.2.1 (QuotientGroup.mk a, QuotientGroup.mk b) : M) =
          ρ a (x.2.1 b) - x.2.1 (a * b) + x.2.1 a}
      add_mem' := by
        rintro x x' ⟨h1, h2, h3, h4⟩ ⟨h1', h2', h3', h4'⟩
        refine ⟨?_, h2.add h2', fun u => ?_, fun a b => ?_⟩
        · rw [Prod.fst_add, Submodule.Quotient.mk_add]
          exact add_mem h1 h1'
        · simp [h3 u, h3' u]
        · simp [h4 a b, h4' a b]
          abel
      zero_mem' := by
        refine ⟨?_, continuous_const, fun u => ?_, fun a b => ?_⟩
        · simp
        · simp
        · simp
      smul_mem' := by
        rintro r x ⟨h1, h2, h3, h4⟩
        refine ⟨?_, h2.const_smul r, fun u => ?_, fun a b => ?_⟩
        · rw [Prod.smul_fst, Submodule.Quotient.mk_smul]
          exact Submodule.smul_mem _ r h1
        · simp [h3 u]
        · simp [h4 a b, smul_sub, smul_add] }
  let q1 : ↥(Z1U ρ U') →ₗ[R] H1U ρ U' := Submodule.mkQ _
  let q2 : ↥(invariantsUnderSubgroupH1 ρ U U') →ₗ[R] resCoker ρ h := Submodule.mkQ _
  let q3 : ↥(Z2 (quotRep ρ U U')) →ₗ[R] H2 (quotRep ρ U U') := Submodule.mkQ _
  have hq1 : Function.Surjective q1 := Submodule.mkQ_surjective _
  have hq2 : Function.Surjective q2 := Submodule.mkQ_surjective _
  let f : P →ₗ[R] resCoker ρ h :=
    q2 ∘ₗ LinearMap.codRestrict (invariantsUnderSubgroupH1 ρ U U') (q1 ∘ₗ LinearMap.fst R _ _ ∘ₗ P.subtype) (fun x => x.2.1)
  let g : P →ₗ[R] H2 (quotRep ρ U U') :=
    q3 ∘ₗ (LinearMap.snd R _ _ ∘ₗ LinearMap.snd R _ _) ∘ₗ P.subtype
  have hfs : Function.Surjective f := by
    intro r
    obtain ⟨x, rfl⟩ := hq2 r
    obtain ⟨z, hz⟩ := hq1 (x : H1U ρ U')
    have hz' : (Submodule.Quotient.mk z : H1U ρ U') ∈ invariantsUnderSubgroupH1 ρ U U' := by
      have hz3 : (Submodule.Quotient.mk z : H1U ρ U') = x := hz
      rw [hz3]
      exact x.2
    have hex := exists_ext ρ hρ h ho z hz'
    obtain ⟨y, hy, hy1, hL, hR⟩ := hex
    obtain ⟨w, hw⟩ := exists_infl ρ h z.1 y hL hR
    refine ⟨⟨(z, y, w), hz', hy, fun u => ?_, hw⟩, ?_⟩
    · have e := hR u 1
      simpa [hy1] using e
    · exact congrArg q2 (Subtype.ext hz)
  have hker : LinearMap.ker g ≤ LinearMap.ker f := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    obtain ⟨⟨z, y, w⟩, h1, h2, h3, h4⟩ := x
    have hw0 : (Submodule.Quotient.mk w : H2 (quotRep ρ U U')) = 0 := hx
    obtain ⟨c, hc, hc1, hcw⟩ := exists_of_mk_eq_zero ρ h w hw0
    have hm := mem_range_resU ρ h z y c h2 hc h3 hc1 (fun a b => (hcw a b).symm.trans (h4 a b))
    exact (Submodule.Quotient.mk_eq_zero _ (x := (⟨_, h1⟩ : invariantsUnderSubgroupH1 ρ U U'))).mpr hm
  exact len_le_of_ker_le f g hfs hker

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M] [DiscreteTopology M] in

/- English proof (translation)
Use `Module.length_le_of_injective (LinearMap.codRestrict (H0U ρ U) ((Representation.invariants ((ρ.comp U.subtype).comp (U'.subgroupOf U).subtype)).subtype ∘ₗ (H0 (quotRep ρ U U')).subtype) ?_) ?_` and prove the remaining obligations. Introduce `x g`. Conclude with `congrArg Subtype.val (x.2 (QuotientGroup.mk g))`. Introduce `x x' hxx`. Establish `hv` using `congrArg Subtype.val hxx`.

Conclude with `Subtype.ext (Subtype.ext hv)`.
-/
theorem length_H0_quotient_rep_le (ρ : Representation R G M) (U' U : Subgroup G) [(U'.subgroupOf U).Normal] :
    Module.length R (H0 (quotRep ρ U U')) ≤ Module.length R (H0U ρ U) := by
  refine Module.length_le_of_injective
    (LinearMap.codRestrict (H0U ρ U)
      ((Representation.invariants ((ρ.comp U.subtype).comp (U'.subgroupOf U).subtype)).subtype ∘ₗ
        (H0 (quotRep ρ U U')).subtype) ?_) ?_
  · intro x g
    exact congrArg Subtype.val (x.2 (QuotientGroup.mk g))
  · intro x x' hxx
    have hv := congrArg Subtype.val hxx
    exact Subtype.ext (Subtype.ext hv)

end UpperTheory.V.Base

end

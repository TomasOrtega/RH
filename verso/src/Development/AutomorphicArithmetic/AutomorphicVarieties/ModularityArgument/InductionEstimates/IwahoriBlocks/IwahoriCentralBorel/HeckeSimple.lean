import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

/- English proof (translation)
Establish `key : ∃ N : Subgroup Γ, N.FiniteIndex ∧ ∀ (N' : Subgroup Γ) [Fintype (Γ ⧸ N')], N' ≤ N → N'.Normal → ∑ c : Γ ⧸ N', σ c.out w = 0` using `by clear hfix`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨u, z, hz, rfl⟩` from `hx`. Take `⟨N, hN, hNz⟩` from `hZ z hz`.

Use `⟨N, hN, fun N' _ hle hn => ?_⟩` and prove the remaining obligations. Simplify using `only [map_sub, Finset.sum_sub_distrib]`. Rewrite using `[sub_eq_zero]`. Use `Fintype.sum_equiv (Equiv.mulRight (QuotientGroup.mk u : Γ ⧸ N')) _ _ fun c => ?_` and prove the remaining obligations. Take `⟨n, hn'⟩` from `QuotientGroup.mk_out_eq_mul N' (c.out * u)`.

Establish `h1 : (Equiv.mulRight (QuotientGroup.mk u : Γ ⧸ N')) c = QuotientGroup.mk (c.out * u)`. Simplify using the standard rewrite rules. Rewrite using `[h1, hn', map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hNz n (hle n.2)]`. Consider the case `zero => exact ⟨⊤, inferInstance, fun N' _ _ _ => by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨N₁, h₁, k₁⟩` from `hx`. Take `⟨N₂, h₂, k₂⟩` from `hy`. Use `⟨N₁ ⊓ N₂, inferInstance, fun N' _ hle hn => ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, Finset.sum_add_distrib]`. Rewrite using `[k₁ N' (hle.trans inf_le_left) hn, k₂ N' (hle.trans inf_le_right) hn, add_zero]`.

Consider the case `smul a x _ hx`. Take `⟨N₁, h₁, k₁⟩` from `hx`. Use `⟨N₁, h₁, fun N' _ hle hn => ?_⟩` and prove the remaining obligations. Simplify using `only [map_smul]`. Rewrite using `[← Finset.smul_sum, k₁ N' hle hn, smul_zero]`.

Take `⟨N, hN, k⟩` from `key`. Use `letI : Fintype (Γ ⧸ N.normalCore) := Fintype.ofFinite _`. Establish `h` using `k N.normalCore N.normalCore_le inferInstance`. Simplify using `only [hfix, Finset.sum_const, Finset.card_univ] at h`. Rewrite `h` using `[← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero]`.

Conclude with `h.resolve_left (by exact_mod_cast Fintype.card_ne_zero)`.
-/
private lemma map_zero_eq_one_of_additive_to_group {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ Γ V)
    (Z : Submodule ℂ V) (hZ : ∀ z ∈ Z, ∃ N : Subgroup Γ, N.FiniteIndex ∧ ∀ n ∈ N, σ n z = z) (w : V)
    (hw : w ∈ Submodule.span ℂ {x | ∃ u : Γ, ∃ z ∈ Z, x = σ u z - z}) (hfix : ∀ u, σ u w = w) : w = 0 := by
  have key : ∃ N : Subgroup Γ, N.FiniteIndex ∧ ∀ (N' : Subgroup Γ) [Fintype (Γ ⧸ N')], N' ≤ N → N'.Normal →
      ∑ c : Γ ⧸ N', σ c.out w = 0 := by
    clear hfix
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, z, hz, rfl⟩ := hx
      obtain ⟨N, hN, hNz⟩ := hZ z hz
      refine ⟨N, hN, fun N' _ hle hn => ?_⟩
      simp only [map_sub, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      refine Fintype.sum_equiv (Equiv.mulRight (QuotientGroup.mk u : Γ ⧸ N')) _ _ fun c => ?_
      obtain ⟨n, hn'⟩ := QuotientGroup.mk_out_eq_mul N' (c.out * u)
      have h1 : (Equiv.mulRight (QuotientGroup.mk u : Γ ⧸ N')) c = QuotientGroup.mk (c.out * u) := by
        simp
      rw [h1, hn', map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hNz n (hle n.2)]
    | zero => exact ⟨⊤, inferInstance, fun N' _ _ _ => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨N₁, h₁, k₁⟩ := hx
      obtain ⟨N₂, h₂, k₂⟩ := hy
      refine ⟨N₁ ⊓ N₂, inferInstance, fun N' _ hle hn => ?_⟩
      simp only [map_add, Finset.sum_add_distrib]
      rw [k₁ N' (hle.trans inf_le_left) hn, k₂ N' (hle.trans inf_le_right) hn, add_zero]
    | smul a x _ hx =>
      obtain ⟨N₁, h₁, k₁⟩ := hx
      refine ⟨N₁, h₁, fun N' _ hle hn => ?_⟩
      simp only [map_smul]
      rw [← Finset.smul_sum, k₁ N' hle hn, smul_zero]
  obtain ⟨N, hN, k⟩ := key
  letI : Fintype (Γ ⧸ N.normalCore) := Fintype.ofFinite _
  have h := k N.normalCore N.normalCore_le inferInstance
  simp only [hfix, Finset.sum_const, Finset.card_univ] at h
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h
  exact h.resolve_left (by exact_mod_cast Fintype.card_ne_zero)

/- English proof (translation)
Use `haveI : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU.2`. Establish `hc : Continuous fun u : G => (QuotientGroup.mk (u * g) : G ⧸ U)` using `QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)`. Use `(hU.1.image hc).finite_of_discrete` as an intermediate fact. Use `this.subset ?_` and prove the remaining obligations. Introduce and unpack `c ⟨u, hu, rfl⟩`.

Conclude with `⟨u, hu, rfl⟩`.
-/
private lemma finite_translates_double_coset {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G) (hU : CO U) (g : G) :
    {c : G ⧸ U | ∃ u ∈ U, c = QuotientGroup.mk (u * g)}.Finite := by
  haveI : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU.2
  have hc : Continuous fun u : G => (QuotientGroup.mk (u * g) : G ⧸ U) :=
    QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)
  have := (hU.1.image hc).finite_of_discrete
  refine this.subset ?_
  rintro c ⟨u, hu, rfl⟩
  exact ⟨u, hu, rfl⟩

/- English proof (translation)
Introduce `G _ _ _ V _ _ ρ Z U hU hS hsm Q hQZ hQfix hQhop`. Distinguish the cases in `hQ : Q = ⊥`. Conclude with `Or.inl hQ`. Use `right`. Set `σ : Representation ℂ U V` to `ρ.comp U.subtype`.

Establish `hσ : ∀ (u : U) (x : V), σ u x = ρ u x` using `fun _ _ => rfl`. Use `set W : Submodule ℂ V := Submodule.span ℂ {x | ∃ u : U, ∃ z ∈ Z, x = σ u z - z} with hW`. Establish `hZN : ∀ z ∈ Z, ∃ N : Subgroup U, N.FiniteIndex ∧ ∀ n ∈ N, σ n z = z`. Introduce `z hz`. Set `N : Subgroup U` to `{ carrier := {n | σ n z = z} one_mem' := by simp mul_mem' := fun {a b} ha hb => by`.

Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Rewrite using `[map_mul, Module.End.mul_apply, hb, ha]`. Use the proof step `inv_mem' := fun {a} ha => by`. Simplify using `only [Set.mem_setOf_eq] at ha ⊢`. Use `conv_lhs => rw [← ha]`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }`. Use `haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU.1`. Establish `ho : IsOpen (N : Set U)` using `(hsm z hz).preimage continuous_subtype_val`. Use `haveI := N.quotient_finite_of_isOpen ho`. Conclude with `⟨N, Subgroup.finiteIndex_of_finite_quotient, fun n hn => hn⟩`.

Establish `htr : ∀ g, ∀ q ∈ Q, ρ g q ∈ Q ⊔ W`. Introduce `g q hq`. Establish `hfin` using `finite_translates_double_coset U hU g`. Establish `h1` using `hQhop g q hq`. Unfold `hopR at h1`.

Rewrite `h1` using `[finsum_mem_eq_finite_toFinset_sum _ hfin]`. Establish `h2 : ∑ c ∈ hfin.toFinset, (ρ c.out q - ρ g q) ∈ W`. Use `W.sum_mem fun c hc => ?_` and prove the remaining obligations. Take `⟨u, hu, rfl⟩` from `hfin.mem_toFinset.mp hc`. Take `⟨n, hn⟩` from `QuotientGroup.mk_out_eq_mul U (u * g)`.

Use `Submodule.subset_span ⟨⟨u, hu⟩, ρ g q, hS.1 g q (hQZ hq), ?_⟩` and prove the remaining obligations. Rewrite using `[hn, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hQfix q hq n n.2, hσ]`. Rewrite `h2` using `[Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]`. Establish `h3` using `(Q ⊔ W).sub_mem (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)`. Rewrite `h3` using `[sub_sub_cancel]`.

Establish `hne : ((hfin.toFinset.card : ℕ) : ℂ) ≠ 0`. Establish `: hfin.toFinset.Nonempty` using `⟨QuotientGroup.mk (1 * g), hfin.mem_toFinset.mpr ⟨1, U.one_mem, rfl⟩⟩`. Conclude with `this.card_ne_zero` after adjusting the coercions. Conclude with `((Q ⊔ W).smul_mem_iff hne).mp h3`. Use `set T : Submodule ℂ V := Submodule.span ℂ {x | ∃ g : G, ∃ q ∈ Q, x = ρ g q} with hT`.

Establish `hTZ : T ≤ Z`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `x ⟨g, q, hq, rfl⟩`. Conclude with `hS.1 g q (hQZ hq)`. Establish `hTst : ∀ g, ∀ v ∈ T, ρ g v ∈ T`.

Introduce `g v hv`. Establish `: T.map (ρ g) ≤ T`. Rewrite using `[hT, Submodule.map_span_le]`. Introduce and unpack `x ⟨g', q, hq, rfl⟩`. Conclude with `Submodule.subset_span ⟨g * g', q, hq, by rw [map_mul, Module.End.mul_apply]⟩`.

Conclude with `this ⟨v, hv, rfl⟩`. Establish `hQT : Q ≤ T` using `fun q hq => Submodule.subset_span ⟨1, q, hq, by simp⟩`. Establish `hTeq : T = Z` using `(hS.2 T hTZ hTst).resolve_left fun h => hQ (le_bot_iff.mp (h ▸ hQT))`. Establish `hTle : T ≤ Q ⊔ W`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations.

Introduce and unpack `x ⟨g, q, hq, rfl⟩`. Conclude with `htr g q hq`. Introduce `v hv hvfix`. Take `⟨q, hq, w, hw, rfl⟩` from `Submodule.mem_sup.mp (hTle (hTeq ▸ hv))`. Establish `hw0 : w = 0`.

Use `map_zero_eq_one_of_additive_to_group σ Z hZN w hw fun u => ?_` and prove the remaining obligations. Use `hvfix u u.2` as an intermediate fact. Rewrite `this` using `[map_add, hQfix q hq u u.2]`. Conclude with `add_left_cancel this`. Simplify `hq` using `[hw0]`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.heckeSimple :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (Z : Submodule ℂ V) (U : Subgroup G), CO U → SimpleIn ρ Z → (∀ v ∈ Z, IsOpen {g | ρ g v = v}) →
      ∀ Q ≤ Z, (∀ v ∈ Q, ∀ u ∈ U, ρ u v = v) → (∀ g, ∀ v ∈ Q, hopR ρ U g v ∈ Q) → Q = ⊥ ∨ ∀ v ∈ Z, (∀ u ∈ U, ρ u v = v) → v ∈ Q := by
  intro G _ _ _ V _ _ ρ Z U hU hS hsm Q hQZ hQfix hQhop
  by_cases hQ : Q = ⊥
  · exact Or.inl hQ
  right
  let σ : Representation ℂ U V := ρ.comp U.subtype
  have hσ : ∀ (u : U) (x : V), σ u x = ρ u x := fun _ _ => rfl
  set W : Submodule ℂ V := Submodule.span ℂ {x | ∃ u : U, ∃ z ∈ Z, x = σ u z - z} with hW
  have hZN : ∀ z ∈ Z, ∃ N : Subgroup U, N.FiniteIndex ∧ ∀ n ∈ N, σ n z = z := by
    intro z hz
    let N : Subgroup U :=
      { carrier := {n | σ n z = z}
        one_mem' := by simp
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, Module.End.mul_apply, hb, ha]
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq] at ha ⊢
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU.1
    have ho : IsOpen (N : Set U) := (hsm z hz).preimage continuous_subtype_val
    haveI := N.quotient_finite_of_isOpen ho
    exact ⟨N, Subgroup.finiteIndex_of_finite_quotient, fun n hn => hn⟩
  have htr : ∀ g, ∀ q ∈ Q, ρ g q ∈ Q ⊔ W := by
    intro g q hq
    have hfin := finite_translates_double_coset U hU g
    have h1 := hQhop g q hq
    unfold hopR at h1
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at h1
    have h2 : ∑ c ∈ hfin.toFinset, (ρ c.out q - ρ g q) ∈ W := by
      refine W.sum_mem fun c hc => ?_
      obtain ⟨u, hu, rfl⟩ := hfin.mem_toFinset.mp hc
      obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul U (u * g)
      refine Submodule.subset_span ⟨⟨u, hu⟩, ρ g q, hS.1 g q (hQZ hq), ?_⟩
      rw [hn, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hQfix q hq n n.2, hσ]
    rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ] at h2
    have h3 := (Q ⊔ W).sub_mem (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)
    rw [sub_sub_cancel] at h3
    have hne : ((hfin.toFinset.card : ℕ) : ℂ) ≠ 0 := by
      have : hfin.toFinset.Nonempty := ⟨QuotientGroup.mk (1 * g), hfin.mem_toFinset.mpr ⟨1, U.one_mem, rfl⟩⟩
      exact_mod_cast this.card_ne_zero
    exact ((Q ⊔ W).smul_mem_iff hne).mp h3
  set T : Submodule ℂ V := Submodule.span ℂ {x | ∃ g : G, ∃ q ∈ Q, x = ρ g q} with hT
  have hTZ : T ≤ Z := by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨g, q, hq, rfl⟩
    exact hS.1 g q (hQZ hq)
  have hTst : ∀ g, ∀ v ∈ T, ρ g v ∈ T := by
    intro g v hv
    have : T.map (ρ g) ≤ T := by
      rw [hT, Submodule.map_span_le]
      rintro x ⟨g', q, hq, rfl⟩
      exact Submodule.subset_span ⟨g * g', q, hq, by rw [map_mul, Module.End.mul_apply]⟩
    exact this ⟨v, hv, rfl⟩
  have hQT : Q ≤ T := fun q hq => Submodule.subset_span ⟨1, q, hq, by simp⟩
  have hTeq : T = Z := (hS.2 T hTZ hTst).resolve_left fun h => hQ (le_bot_iff.mp (h ▸ hQT))
  have hTle : T ≤ Q ⊔ W := by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨g, q, hq, rfl⟩
    exact htr g q hq
  intro v hv hvfix
  obtain ⟨q, hq, w, hw, rfl⟩ := Submodule.mem_sup.mp (hTle (hTeq ▸ hv))
  have hw0 : w = 0 := by
    refine map_zero_eq_one_of_additive_to_group σ Z hZN w hw fun u => ?_
    have := hvfix u u.2
    rw [map_add, hQfix q hq u u.2] at this
    exact add_left_cancel this
  simpa [hw0] using hq

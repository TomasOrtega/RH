import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueAdmissibleLocalComponentDefiniteUnit

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

section Generic

variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Establish `hs : (Function.support fun q : G ⧸ K => f q.out • (ρ q.out ∘ₗ (LinearMap.id : V →ₗ[ℂ] V))).Finite` using `hfs.subset fun q hq h0 => hq (by simp [h0])`. Establish `h` using `(LinearMap.applyₗ (R := ℂ) (M := V) (M₂ := V) x).toAddMonoidHom.map_finsum hs`. Simplify using `only [levOp, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul]`. Conclude with `h`.
-/
private theorem levOp_self (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ)
    (hfs : (Function.support fun q : G ⧸ K => f q.out).Finite) (x : V) :
    levOp ρ K K f LinearMap.id x = ∑ᶠ q : G ⧸ K, f q.out • ρ q.out x := by
  have hs : (Function.support fun q : G ⧸ K => f q.out • (ρ q.out ∘ₗ (LinearMap.id : V →ₗ[ℂ] V))).Finite :=
    hfs.subset fun q hq h0 => hq (by simp [h0])
  have h := (LinearMap.applyₗ (R := ℂ) (M := V) (M₂ := V) x).toAddMonoidHom.map_finsum hs
  simp only [levOp, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul]
  exact h

/- English proof (translation)
Set `q₁ : G ⧸ K` to `QuotientGroup.mk 1`. Establish `hz : ∀ q : G ⧸ K, q ≠ q₁ → ((K : Set G).indicator 1 q.out : ℂ) = 0` using `fun q hq => by`. Use `Set.indicator_of_notMem (fun hm => hq ?_) _` and prove the remaining obligations. Rewrite using `[← QuotientGroup.out_eq' q]`. Conclude with `QuotientGroup.eq.2 (by simpa using K.inv_mem hm)`.

Establish `h1 : Quotient.out q₁ ∈ K`. Use `QuotientGroup.eq.1 (QuotientGroup.out_eq' q₁).symm` as an intermediate fact. Simplify `this` using `[q₁]`. Rewrite using `[levOp_self ρ K _ ((Set.finite_singleton q₁).subset fun q hq => by`. Assume the negation of the conclusion as `hne`.

Conclude with `hq (hz q hne)), finsum_eq_single _ q₁ fun q hq => by rw [hz q hq, zero_smul]]`. Rewrite using `[Set.indicator_of_mem h1]`. Simplify using `using GlobalTheory.LGrp.mem_fixed.1 hx _ h1`.
-/
private theorem levOp_ind (ρ : Representation ℂ G V) (K : Subgroup G) {x : V} (hx : x ∈ fixed ρ K) :
    levOp ρ K K ((K : Set G).indicator 1) LinearMap.id x = x := by
  let q₁ : G ⧸ K := QuotientGroup.mk 1
  have hz : ∀ q : G ⧸ K, q ≠ q₁ → ((K : Set G).indicator 1 q.out : ℂ) = 0 := fun q hq => by
    refine Set.indicator_of_notMem (fun hm => hq ?_) _
    rw [← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.2 (by simpa using K.inv_mem hm)
  have h1 : Quotient.out q₁ ∈ K := by
    have := QuotientGroup.eq.1 (QuotientGroup.out_eq' q₁).symm
    simpa [q₁] using this
  rw [levOp_self ρ K _ ((Set.finite_singleton q₁).subset fun q hq => by
    by_contra hne
    exact hq (hz q hne)), finsum_eq_single _ q₁ fun q hq => by rw [hz q hq, zero_smul]]
  rw [Set.indicator_of_mem h1]
  simpa using GlobalTheory.LGrp.mem_fixed.1 hx _ h1

/- English proof (translation)
Establish `hx0 : (⟨x, hx⟩ : fixed ρ K) ≠ 0` using `fun h => h0 (congrArg Subtype.val h)`. Establish `hall : ∀ y ∈ fixed ρ K, levOp ρ K K f LinearMap.id y = c • y` using `fun y hy => by`. Take `⟨a, ha⟩` from `(finrank_eq_one_iff_of_nonzero' _ hx0).1 h1 ⟨y, hy⟩`. Establish `hy' : y = a • x` using `(congrArg Subtype.val ha).symm`. Rewrite using `[hy', map_smul, hop, smul_comm]`.

Establish `hmem : ∀ v ∈ fixed ρ K, levOp ρ K K f LinearMap.id v ∈ fixed ρ K` using `fun v hv => by`. Rewrite using `[hall v hv]`. Conclude with `Submodule.smul_mem _ _ hv`. Establish `hr : (levOp ρ K K f LinearMap.id).restrict hmem = c • LinearMap.id`. Use extensionality with `y`.

Simplify using `[LinearMap.restrict_apply, hall y.1 y.2]`. Use `haveI : Module.Finite ℂ (fixed ρ K) := Module.finite_of_finrank_pos (by omega)`. Rewrite using `[twTr, dif_pos hmem, hr, map_smul, LinearMap.trace_id, h1]`. Simplify using the standard rewrite rules.
-/
private theorem twTr_line (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ) (c : ℂ)
    (h1 : Module.finrank ℂ (fixed ρ K) = 1) {x : V} (hx : x ∈ fixed ρ K) (h0 : x ≠ 0)
    (hop : levOp ρ K K f LinearMap.id x = c • x) : twTr ρ K K f LinearMap.id = c := by
  have hx0 : (⟨x, hx⟩ : fixed ρ K) ≠ 0 := fun h => h0 (congrArg Subtype.val h)
  have hall : ∀ y ∈ fixed ρ K, levOp ρ K K f LinearMap.id y = c • y := fun y hy => by
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hx0).1 h1 ⟨y, hy⟩
    have hy' : y = a • x := (congrArg Subtype.val ha).symm
    rw [hy', map_smul, hop, smul_comm]
  have hmem : ∀ v ∈ fixed ρ K, levOp ρ K K f LinearMap.id v ∈ fixed ρ K := fun v hv => by
    rw [hall v hv]
    exact Submodule.smul_mem _ _ hv
  have hr : (levOp ρ K K f LinearMap.id).restrict hmem = c • LinearMap.id := by
    ext y
    simp [LinearMap.restrict_apply, hall y.1 y.2]
  haveI : Module.Finite ℂ (fixed ρ K) := Module.finite_of_finrank_pos (by omega)
  rw [twTr, dif_pos hmem, hr, map_smul, LinearMap.trace_id, h1]
  simp

/- English proof (translation)
Take `⟨x, hx, h0⟩` from `(Submodule.ne_bot_iff _).1 hne`. Conclude with `twTr_line ρ K _ 1 h1 hx h0 (by rw [levOp_ind ρ K hx, one_smul])`.
-/
private theorem twTr_ind (ρ : Representation ℂ G V) (K : Subgroup G) (h1 : Module.finrank ℂ (fixed ρ K) = 1)
    (hne : fixed ρ K ≠ ⊥) : twTr ρ K K ((K : Set G).indicator 1) LinearMap.id = 1 := by
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 hne
  exact twTr_line ρ K _ 1 h1 hx h0 (by rw [levOp_ind ρ K hx, one_smul])

/- English proof (translation)
Use `haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK`. Establish `himg : IsCompact ((QuotientGroup.mk : G → G ⧸ K) '' tsupport f)` using `IsCompact.image hc continuous_quot_mk`. Use `himg.finite_of_discrete.subset fun q hq => ?_` and prove the remaining obligations. Conclude with `⟨q.out, subset_tsupport _ hq, QuotientGroup.out_eq' q⟩`.
-/
private theorem finite_supp [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G)
    (hK : IsOpen (K : Set G)) (f : G → ℂ) (hc : HasCompactSupport f) :
    (Function.support fun q : G ⧸ K => f q.out).Finite := by
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK
  have himg : IsCompact ((QuotientGroup.mk : G → G ⧸ K) '' tsupport f) :=
    IsCompact.image hc continuous_quot_mk
  refine himg.finite_of_discrete.subset fun q hq => ?_
  exact ⟨q.out, subset_tsupport _ hq, QuotientGroup.out_eq' q⟩

/- English proof (translation)
Set `φ : G ⧸ K₁ → H ⧸ K` to `fun q => QuotientGroup.mk (e q.out)`. Establish `hφ : Function.Bijective φ`. Prove the components needed by the constructor for the conclusion. Introduce `a b hab`. Rewrite using `[← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]`.

Use `QuotientGroup.eq.2 ((hK _).2 ?_)` and prove the remaining obligations. Use `QuotientGroup.eq.1 hab` as an intermediate fact. Simplify using `using this`. Introduce `q`. Use `⟨QuotientGroup.mk (e.symm q.out), ?_⟩` and prove the remaining obligations.

Rewrite using `[← QuotientGroup.out_eq' q]`. Use `QuotientGroup.eq.2 ?_` and prove the remaining obligations. Establish `h1 : (e.symm q.out)⁻¹ * (Quotient.out (QuotientGroup.mk (e.symm q.out) : G ⧸ K₁)) ∈ K₁` using `QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm`. Establish `h2` using `(hK _).1 (K₁.inv_mem h1)`. Simplify `h2` using `[φ]`.

Establish `hrep : ∀ q : G ⧸ K₁, ∃ k ∈ K, (φ q).out = e q.out * k` using `fun q => by`. Use `⟨(e q.out)⁻¹ * (φ q).out, QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm, by group⟩` and prove the remaining obligations. Establish `hval : ∀ q : G ⧸ K₁, F q.out = f (φ q).out` using `fun q => by`. Take `⟨k, hk, h⟩` from `hrep q`. Rewrite using `[h, hf _ k hk, hFf]`.

Establish `hfin' : (Function.support fun q : G ⧸ K₁ => F q.out).Finite`. Use `(hfin.preimage hφ.1.injOn).subset fun q hq => ?_` and prove the remaining obligations. Simplify `hq` using `[hval q]`. Rewrite using `[levOp_self _ K₁ F hfin', levOp_self ρ K f hfin, ← finsum_comp_equiv (Equiv.ofBijective φ hφ)]`. Use `finsum_congr fun q => ?_` and prove the remaining obligations.

Take `⟨k, hk, h⟩` from `hrep q`. Simplify using `only [Equiv.ofBijective_apply]`. Rewrite using `[hval q, h]`. Use `congr 1`. Establish `hk'` using `GlobalTheory.LGrp.mem_fixed.1 hx k hk`.

Rewrite using `[map_mul, Module.End.mul_apply, hk']`. Both sides reduce to the same expression.
-/
private theorem levOp_comp (e : G ≃* H) (ρ : Representation ℂ H V) (K : Subgroup H) (K₁ : Subgroup G)
    (hK : ∀ g, g ∈ K₁ ↔ e g ∈ K) (F : G → ℂ) (f : H → ℂ) (hFf : ∀ g, F g = f (e g))
    (hf : ∀ x, ∀ k ∈ K, f (x * k) = f x) (hfin : (Function.support fun q : H ⧸ K => f q.out).Finite)
    {x : V} (hx : x ∈ fixed ρ K) :
    levOp (ρ.comp e.toMonoidHom) K₁ K₁ F LinearMap.id x = levOp ρ K K f LinearMap.id x := by
  let φ : G ⧸ K₁ → H ⧸ K := fun q => QuotientGroup.mk (e q.out)
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b hab
      rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]
      refine QuotientGroup.eq.2 ((hK _).2 ?_)
      have := QuotientGroup.eq.1 hab
      simpa using this
    · intro q
      refine ⟨QuotientGroup.mk (e.symm q.out), ?_⟩
      rw [← QuotientGroup.out_eq' q]
      refine QuotientGroup.eq.2 ?_
      have h1 : (e.symm q.out)⁻¹ * (Quotient.out (QuotientGroup.mk (e.symm q.out) : G ⧸ K₁)) ∈ K₁ :=
        QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm
      have h2 := (hK _).1 (K₁.inv_mem h1)
      simpa [φ] using h2
  have hrep : ∀ q : G ⧸ K₁, ∃ k ∈ K, (φ q).out = e q.out * k := fun q => by
    refine ⟨(e q.out)⁻¹ * (φ q).out, QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm, by group⟩
  have hval : ∀ q : G ⧸ K₁, F q.out = f (φ q).out := fun q => by
    obtain ⟨k, hk, h⟩ := hrep q
    rw [h, hf _ k hk, hFf]
  have hfin' : (Function.support fun q : G ⧸ K₁ => F q.out).Finite := by
    refine (hfin.preimage hφ.1.injOn).subset fun q hq => ?_
    simpa [hval q] using hq
  rw [levOp_self _ K₁ F hfin', levOp_self ρ K f hfin, ← finsum_comp_equiv (Equiv.ofBijective φ hφ)]
  refine finsum_congr fun q => ?_
  obtain ⟨k, hk, h⟩ := hrep q
  simp only [Equiv.ofBijective_apply]
  rw [hval q, h]
  congr 1
  have hk' := GlobalTheory.LGrp.mem_fixed.1 hx k hk
  rw [map_mul, Module.End.mul_apply, hk']
  rfl

/- English proof (translation)
Use `Submodule.ext fun x => ⟨fun h => GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, fun h => GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_⟩` and prove the remaining obligations. Establish `h1` using `GlobalTheory.LGrp.mem_fixed.1 h (e.symm k) ((hK _).2 (by simpa using hk))`. Simplify using `using h1`. Conclude with `GlobalTheory.LGrp.mem_fixed.1 h (e k) ((hK k).1 hk)`.
-/
private theorem fixed_comp (e : G ≃* H) (ρ : Representation ℂ H V) (K : Subgroup H) (K₁ : Subgroup G)
    (hK : ∀ g, g ∈ K₁ ↔ e g ∈ K) : fixed (ρ.comp e.toMonoidHom) K₁ = fixed ρ K := by
  refine Submodule.ext fun x => ⟨fun h => GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, fun h => GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_⟩
  · have h1 := GlobalTheory.LGrp.mem_fixed.1 h (e.symm k) ((hK _).2 (by simpa using hk))
    simpa using h1
  · exact GlobalTheory.LGrp.mem_fixed.1 h (e k) ((hK k).1 hk)

end Generic

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E}

/- English proof (translation)
Rewrite using `[UL, if_pos hs]`. Conclude with `Subgroup.mem_top _`.
-/
private theorem mem_UL (hs : IsSplitAt w) (g : GLw n w) : g ∈ UL n w := by
  rw [UL, if_pos hs]
  exact Subgroup.mem_top _

private def eSp (hs : IsSplitAt w) : GLw n w ≃* UL n w where
  toFun g := ⟨g, mem_UL hs g⟩
  invFun x := x.1
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private def toGL (hs : IsSplitAt w) (σ : SmIrr (UL n w)) : SmIrr (GLw n w) :=
  { V := σ.V
    ρ := σ.ρ.comp (eSp hs).toMonoidHom
    smooth := fun v => (σ.smooth v).preimage (Continuous.subtype_mk continuous_id _)
    irred := GlobalTheory.BCT.LocCompU.isIrreducible_comp_of_surjective σ.ρ _ (eSp hs).surjective σ.irred }

/- English proof (translation)
The claim follows from `fixed_comp (eSp hs) σ.ρ (KL n w) (KGL w n) fun _ => Iff.rfl`.
-/
private theorem fixed_toGL (hs : IsSplitAt w) (σ : SmIrr (UL n w)) :
    fixed (toGL hs σ).ρ (KGL w n) = fixed σ.ρ (KL n w) :=
  fixed_comp (eSp hs) σ.ρ (KL n w) (KGL w n) fun _ => Iff.rfl

/- English proof (translation)
Take `⟨p, hp, -, f, hf0, hfm, hf⟩` from `h`. Use `⟨(toGL hs σ).irred, f, hf0, hfm, fun x v => ?_⟩` and prove the remaining obligations. Establish `he : eSp hs (((cLoc w).comp (locU n w).subtype) x) = p x` using `Subtype.ext (hp x).symm`. Conclude with `(congrArg (fun g => f (σ.ρ g v)) he).trans (hf x v)`.
-/
private theorem comp_toGL (hs : IsSplitAt w) {π : Submodule ℂ (UA E n → ℂ)} {σ : SmIrr (UL n w)}
    (h : IsCompU π w σ) :
    IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (toGL hs σ).ρ := by
  obtain ⟨p, hp, -, f, hf0, hfm, hf⟩ := h
  refine ⟨(toGL hs σ).irred, f, hf0, hfm, fun x v => ?_⟩
  have he : eSp hs (((cLoc w).comp (locU n w).subtype) x) = p x := Subtype.ext (hp x).symm
  exact (congrArg (fun g => f (σ.ρ g v)) he).trans (hf x v)

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1.comp_isClosedEmbedding (GlobalTheory.BCT.LocCompU.isClosed_UL hU n w).isClosedEmbedding_subtypeVal, fun k hk x => ⟨(h.2 k.1 (hK k hk) x.1).1, (h.2 k.1 (hK k hk) x.1).2⟩⟩`.
-/
private theorem isHecke_val (hU : GlobalTheory.BCT.Unr E) (K₀ : Subgroup (GLw n w)) (f : GLw n w → ℂ)
    (h : IsHecke K₀ f) (K₁ : Subgroup (UL n w)) (hK : ∀ k ∈ K₁, k.1 ∈ K₀) :
    IsHecke K₁ fun y : UL n w => f y.1 :=
  ⟨h.1.comp_isClosedEmbedding (GlobalTheory.BCT.LocCompU.isClosed_UL hU n w).isClosedEmbedding_subtypeVal,
    fun k hk x => ⟨(h.2 k.1 (hK k hk) x.1).1, (h.2 k.1 (hK k hk) x.1).2⟩⟩

/- English proof (translation)
Use `⟨HasCompactSupport.intro (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).2 fun x hx => Set.indicator_of_notMem hx _, fun k hk x => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ KL n w`. Rewrite using `[Set.indicator_of_mem (show x ∈ (KL n w : Set (UL n w)) from hx), Set.indicator_of_mem (show k * x ∈ (KL n w : Set (UL n w)) from (KL n w).mul_mem hk hx)]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem (show x ∉ (KL n w : Set (UL n w)) from hx), Set.indicator_of_notMem (show k * x ∉ (KL n w : Set (UL n w)) from fun h => hx (((KL n w).mul_mem_cancel_left hk).1 h))]`.

Distinguish the cases in `hx : x ∈ KL n w`. Rewrite using `[Set.indicator_of_mem (show x ∈ (KL n w : Set (UL n w)) from hx), Set.indicator_of_mem (show x * k ∈ (KL n w : Set (UL n w)) from (KL n w).mul_mem hx hk)]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem (show x ∉ (KL n w : Set (UL n w)) from hx), Set.indicator_of_notMem (show x * k ∉ (KL n w : Set (UL n w)) from fun h => hx (((KL n w).mul_mem_cancel_right hk).1 h))]`.
-/
private theorem isHecke_ind (hU : GlobalTheory.BCT.Unr E) : IsHecke (KL n w) ((KL n w : Set (UL n w)).indicator 1) := by
  refine ⟨HasCompactSupport.intro (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).2 fun x hx =>
    Set.indicator_of_notMem hx _, fun k hk x => ⟨?_, ?_⟩⟩
  · by_cases hx : x ∈ KL n w
    · rw [Set.indicator_of_mem (show x ∈ (KL n w : Set (UL n w)) from hx),
        Set.indicator_of_mem (show k * x ∈ (KL n w : Set (UL n w)) from (KL n w).mul_mem hk hx)]
      rfl
    · rw [Set.indicator_of_notMem (show x ∉ (KL n w : Set (UL n w)) from hx),
        Set.indicator_of_notMem (show k * x ∉ (KL n w : Set (UL n w)) from
          fun h => hx (((KL n w).mul_mem_cancel_left hk).1 h))]
  · by_cases hx : x ∈ KL n w
    · rw [Set.indicator_of_mem (show x ∈ (KL n w : Set (UL n w)) from hx),
        Set.indicator_of_mem (show x * k ∈ (KL n w : Set (UL n w)) from (KL n w).mul_mem hx hk)]
      rfl
    · rw [Set.indicator_of_notMem (show x ∉ (KL n w : Set (UL n w)) from hx),
        Set.indicator_of_notMem (show x * k ∉ (KL n w : Set (UL n w)) from
          fun h => hx (((KL n w).mul_mem_cancel_right hk).1 h))]

/- English proof (translation)
Take `⟨x, hx⟩` from `hB.exists_vec`. Take `⟨hH, hA⟩` from `hE E n w e`. Establish `hfix : x ∈ fixed σ.ρ (KL n w)` using `(fixed_toGL hs σ) ▸ hx.2.1`. Establish `hHU` using `isHecke_val hU _ _ hH (KL n w) fun k hk => hk`. Establish `hop` using `hA _ (toGL hs σ).ρ x B hx`.

Use `twTr_line σ.ρ (KL n w) _ _ h1 hfix hx.1 ?_` and prove the remaining obligations. Rewrite using `[← levOp_comp (eSp hs) σ.ρ (KL n w) (KGL w n) (fun g => Iff.rfl) (fn1 n w e) (fun y : UL n w => fn1 n w e y.1) (fun _ => rfl) (fun y k hk => (hHU.2 k hk y).2) (finite_supp _ (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).1 _ hHU.1) hfix]`. Conclude with `hop`.
-/
private theorem trace_test_function_eq (hE : ExAct) (hU : GlobalTheory.BCT.Unr E) (hs : IsSplitAt w) (σ : SmIrr (UL n w))
    (h1 : Module.finrank ℂ (fixed σ.ρ (KL n w)) = 1) {B : Multiset ℂˣ} (hB : HasSatGL w (toGL hs σ).ρ B)
    (e : Ex (Fin (n + 1))) :
    twTr σ.ρ (KL n w) (KL n w) (fun y : UL n w => fn1 n w e y.1) LinearMap.id = ev1 n w e B := by
  obtain ⟨x, hx⟩ := hB.exists_vec
  obtain ⟨hH, hA⟩ := hE E n w e
  have hfix : x ∈ fixed σ.ρ (KL n w) := (fixed_toGL hs σ) ▸ hx.2.1
  have hHU := isHecke_val hU _ _ hH (KL n w) fun k hk => hk
  have hop := hA _ (toGL hs σ).ρ x B hx
  refine twTr_line σ.ρ (KL n w) _ _ h1 hfix hx.1 ?_
  rw [← levOp_comp (eSp hs) σ.ρ (KL n w) (KGL w n) (fun g => Iff.rfl) (fn1 n w e)
    (fun y : UL n w => fn1 n w e y.1) (fun _ => rfl) (fun y k hk => (hHU.2 k hk y).2)
    (finite_supp _ (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).1 _ hHU.1) hfix]
  exact hop

end Local

/- English proof (translation)
Introduce `hUS hPl hEx hSL hIL hUC E _ _ _ hU n hn S hS lam Z hZ f hf hreg`. Take `⟨-, hcc, -, hsec⟩` from `hPl E`. Establish `hsplit' : ∀ w : Pl E, IsSplitAt w → IsSplitAt (cPl w)` using `fun w h => (hcc (cPl w)).2.2 (by rw [(hcc w).1]; exact ((hcc w).2.1 h).symm)`. Establish `hnot : ∀ w ∈ S, IsSplitAt w → cPl w ∉ S` using `fun w hw h hc => (hcc w).2.1 h ((hsec S hS w).2 hw hc)`. Choose the witnesses or unpack the hypotheses as in `⟨Kz, hKo, hKle, hKf, hKn⟩ : ∃ Kz : ∀ w : Pl E, Subgroup (GLw n w), (∀ w, IsOpen (Kz w : Set (GLw n w))) ∧ (∀ w, Kz w ≤ KGL w n) ∧ (∀ w ∈ Z, IsHecke (Kz w) (f w)) ∧ ∀ w, w ∉ Z → Kz w = KGL w n := by`.

Use `⟨fun w => if h : w ∈ Z then (hf w h).choose else KGL w n, fun w => ?_, fun w => ?_, fun w h => ?_, fun w h => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : w ∈ Z`. Simplify `(hf w h).choose_spec.1` using `[h]`. Simplify `(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1` using `[h]`. Distinguish the cases in `h : w ∈ Z`.

Simplify `(hf w h).choose_spec.2.1` using `[h]`. Simplify using `[h]`. Simplify `(hf w h).choose_spec.2.2` using `[h]`. Simplify using `[h]`. Set `K' : ∀ w : Pl E, Subgroup (UL n w)` to `fun w => (Kz w).subgroupOf (UL n w)`.

Establish `hKL : ∀ w, w ∉ Z → K' w = KL n w` using `fun w h => by`. Simplify using `only [K', hKn w h, KL]`. Establish `hLev : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K'`. Use `⟨fun w => ⟨?_, fun k hk => hKle w hk, fun k hk => hk⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [K', Subgroup.coe_subgroupOf]`.

Conclude with `(hKo w).preimage continuous_subtype_val`. Use `Filter.eventually_cofinite.2 (Z.finite_toSet.subset fun w hw => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hw (hKL w h)`. Take `⟨ι, hι, π, σ, hσ, -, hTr⟩` from `hUS E hU n hn S hS lam K' hLev`.

Establish `hline : ∀ i, ∀ w ∈ S, w ∉ Z → fixed (σ i w).ρ (KL n w) ≠ ⊥ ∧ Module.finrank ℂ (fixed (σ i w).ρ (KL n w)) = 1 ∧ ∃ B, ∀ hs : IsSplitAt w, HasSatGL w (toGL hs (σ i w)).ρ B` using `fun i w hw hz => by`. Take `⟨hc, hne, hfd⟩` from `(hσ i).2.2.2 w hw`. Rewrite `hne` using `[hKL w hz]`. Distinguish the cases in `hs : IsSplitAt w`. Take `⟨h1, B, hB⟩` from `hSL E n w (toGL hs (σ i w)) (by rw [fixed_toGL]; exact hne)`.

Use `⟨hne, ?_, B, fun _ => hB⟩` and prove the remaining obligations. Rewrite `h1` using `[fixed_toGL]`. Conclude with `h1`. Conclude with `⟨hne, hIL E hU n w hs (σ i w) hne (hfd _ (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).1), 0, fun h => absurd h hs⟩`. Set `B₀ : ι → Pl E → Multiset ℂˣ` to `fun i w => Classical.epsilon fun B => ∀ hs : IsSplitAt w, HasSatGL w (toGL hs (σ i w)).ρ B`.

Establish `hB₀ : ∀ i, ∀ w ∈ S, w ∉ Z → ∀ hs : IsSplitAt w, HasSatGL w (toGL hs (σ i w)).ρ (B₀ i w)` using `fun i w hw hz => Classical.epsilon_spec (p := fun B => ∀ hs : IsSplitAt w, HasSatGL w (toGL hs (σ i w)).ρ B) (hline i w hw hz).2.2`. Set `B : ι → Pl E → Multiset ℂˣ` to `fun i w => if w ∈ S then B₀ i w else inv (B₀ i (cPl w))`. Establish `hBS : ∀ i, ∀ w ∈ S, B i w = B₀ i w` using `fun i w hw => if_pos hw`. Establish `hBN : ∀ i w, w ∉ S → B i w = inv (B₀ i (cPl w))` using `fun i w hw => if_neg hw`. Set `A : ι → ℂ` to `fun i => ∏ w ∈ Z, twTr (σ i w).ρ (KL n w) (K' w) (fun x => f w x.1) LinearMap.id`.

Use `⟨K', ι, hι, π, A, B, hLev, fun i => ⟨(hσ i).1, fun w hns => ?_, fun w hoff hs => ?_⟩, fun T hT hd e₁ e₂ k => ?_⟩` and prove the remaining obligations. Establish `hw : w ∈ S`. Establish `hcw : cPl w = w`. Assume the negation of the conclusion as `h`. Conclude with `hns ((hcc w).2.2 h)`.

Break down `(hsec S hS w).1 with h | h` into its components or cases. Conclude with `h`. Rewrite `h` using `[hcw]`. Then use the resulting hypothesis. Establish `hz : w ∉ Z` using `fun h => hns (hZ w h).2`. Take `⟨φ, hφ, h0, hfix⟩` from `(hσ i).2.2.1`.

Take `⟨p, hp, -⟩` from `((hσ i).2.2.2 w hw).1`. Use `⟨φ, hφ, h0, fun x hx hk => hfix w hw x hx ⟨p ⟨x, hx⟩, ?_, hp ⟨x, hx⟩⟩⟩` and prove the remaining obligations. Rewrite using `[hKL w hz]`. Express the relevant statement in the definitionally equal form `(p ⟨x, hx⟩).1 ∈ KGL w n`. Rewrite using `[hp ⟨x, hx⟩]`.

Conclude with `hk`. Distinguish the cases in `hw : w ∈ S`. Rewrite using `[hBS i w hw]`. Conclude with `⟨toGL hs (σ i w), comp_toGL hs ((hσ i).2.2.2 w hw).1, hB₀ i w hw hoff.1 hs⟩`. Establish `hcw : cPl w ∈ S` using `((hsec S hS w).1).resolve_left hw`.

Establish `hsc` using `hsplit' w hs`. Establish `hu` using `hUC E n (π i) (cPl w) hsc (toGL hsc (σ i (cPl w))) (B₀ i (cPl w)) (comp_toGL hsc ((hσ i).2.2.2 _ hcw).1) (hB₀ i _ hcw hoff.2 hsc)`. Rewrite `hu` using `[(hcc w).1]`. Rewrite using `[hBN i w hw]`. Conclude with `hu`.

Establish `hTs : ∀ w ∈ T, w ∈ S ∧ IsSplitAt w ∧ w ∉ Z` using `fun w hw => ⟨(hT w hw).1, (hT w hw).2, Finset.disjoint_left.1 hd hw⟩`. Establish `hfZ : ∀ w ∈ Z, famU Z T f e₁ e₂ k w = fun x => f w x.1` using `fun w hw => by`. Simplify using `[famU, hw]`. Establish `hfT : ∀ w ∈ T, famU Z T f e₁ e₂ k w = fun x => fn1 n w (((e₁ w).pow k).mul ((e₂ w).pow k)) x.1` using `fun w hw => by`. Simplify using `[famU, hw, (hTs w hw).2.2]`.

Establish `hfO : ∀ w, w ∉ Z → w ∉ T → famU Z T f e₁ e₂ k w = (KL n w : Set _).indicator 1` using `fun w h1 h2 => by`. Simplify using `[famU, h1, h2]`. Establish `htest : GlobalTheory.BCT.IsTest (KL n) K' (famU Z T f e₁ e₂ k)`. Use `⟨fun w => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h1 : w ∈ Z`.

Rewrite using `[hfZ w h1]`. Conclude with `isHecke_val hU _ _ (hKf w h1) (K' w) fun k hk => hk`. Distinguish the cases in `h2 : w ∈ T`. Rewrite using `[hfT w h2]`. Conclude with `isHecke_val hU _ _ (hEx E n w _).1 (K' w) fun k hk => hKle w hk`.

Rewrite using `[hfO w h1 h2, hKL w h1]`. Conclude with `isHecke_ind hU`. Use `Filter.eventually_cofinite.2 ((Z ∪ T).finite_toSet.subset fun w hw => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Establish `h' : w ∉ Z ∧ w ∉ T` using `by simpa using h`.

Conclude with `hw (hfO w h'.1 h'.2)`. Use `⟨htest, ?_⟩` and prove the remaining obligations. Establish `hr : ∃ w ∈ S, ∀ y, famU Z T f e₁ e₂ k w y ≠ 0 → y.1.val.charpoly.Separable`. Take `⟨w, hw, hy⟩` from `hreg`. Use `⟨w, (hZ w hw).1, fun y h => hy y.1 ?_⟩` and prove the remaining obligations.

Rewrite `h` using `[hfZ w hw]`. Then use the resulting hypothesis. Rewrite using `[← hTr _ htest hr]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `set g : Pl E → ℂ := fun w => twTr (σ i w).ρ (KL n w) (K' w) (famU Z T f e₁ e₂ k w) LinearMap.id with hg`. Establish `hone : ∀ w ∈ S, w ∉ Z → w ∉ T → g w = 1` using `fun w hw h1 h2 => by`.

Take `⟨hne, hfr, -⟩` from `hline i w hw h1`. Simplify using `only [hg]`. Rewrite using `[hfO w h1 h2, hKL w h1]`. Conclude with `twTr_ind _ _ hfr hne`. Establish `hUS' : ∀ w ∈ Z ∪ T, w ∈ S` using `fun w hw => by`.

Break down `Finset.mem_union.1 hw with h | h` into its components or cases. Conclude with `(hZ w h).1`. Conclude with `(hTs w h).1`. Establish `hsupp : ∏ᶠ w ∈ S, g w = ∏ w ∈ Z ∪ T, g w`. Rewrite using `[← finprod_mem_coe_finset]`.

Use `finprod_mem_inter_mulSupport_eq' _ _ _ fun w hw => ⟨fun h => ?_, fun h => hUS' w h⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Establish `h' : w ∉ Z ∧ w ∉ T` using `by simpa using hn`. Conclude with `hw (hone w h h'.1 h'.2)`. Rewrite using `[hsupp, Finset.prod_union hd.symm]`.

Use `congrArg₂ (· * ·) (Finset.prod_congr rfl fun w hw => ?_) ?_` and prove the remaining obligations. Simplify using `only [hg]`. Rewrite using `[hfZ w hw]`. Rewrite using `[val1, ← Finset.prod_pow]`. Use `Finset.prod_congr rfl fun w hw => ?_` and prove the remaining obligations.

Take `⟨hwS, hs, hz⟩` from `hTs w hw`. Establish `hinv : inv (inv (B₀ i w)) = B₀ i w` using `by simp [inv, Multiset.map_map]`. Simplify using `only [hg]`. Rewrite using `[hfT w hw, hKL w hz, trace_test_function_eq hEx hU hs (σ i w) (hline i w hwS hz).2.1 (hB₀ i w hwS hz hs), hBS i w hwS, hBN i _ (hnot w hwS hs), (hcc w).1, hinv]`. Simplify using `only [ev1, Ex.ev, Ex.ev_pow, mul_pow]`.
-/
theorem rUEval : RUEval := by
  intro hUS hPl hEx hSL hIL hUC E _ _ _ hU n hn S hS lam Z hZ f hf hreg
  obtain ⟨-, hcc, -, hsec⟩ := hPl E
  have hsplit' : ∀ w : Pl E, IsSplitAt w → IsSplitAt (cPl w) := fun w h =>
    (hcc (cPl w)).2.2 (by rw [(hcc w).1]; exact ((hcc w).2.1 h).symm)
  have hnot : ∀ w ∈ S, IsSplitAt w → cPl w ∉ S := fun w hw h hc =>
    (hcc w).2.1 h ((hsec S hS w).2 hw hc)

  obtain ⟨Kz, hKo, hKle, hKf, hKn⟩ : ∃ Kz : ∀ w : Pl E, Subgroup (GLw n w), (∀ w, IsOpen (Kz w : Set (GLw n w))) ∧
      (∀ w, Kz w ≤ KGL w n) ∧ (∀ w ∈ Z, IsHecke (Kz w) (f w)) ∧ ∀ w, w ∉ Z → Kz w = KGL w n := by
    refine ⟨fun w => if h : w ∈ Z then (hf w h).choose else KGL w n, fun w => ?_, fun w => ?_, fun w h => ?_, fun w h => ?_⟩
    · by_cases h : w ∈ Z
      · simpa [h] using (hf w h).choose_spec.1
      · simpa [h] using (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1
    · by_cases h : w ∈ Z
      · simpa [h] using (hf w h).choose_spec.2.1
      · simp [h]
    · simpa [h] using (hf w h).choose_spec.2.2
    · simp [h]
  let K' : ∀ w : Pl E, Subgroup (UL n w) := fun w => (Kz w).subgroupOf (UL n w)
  have hKL : ∀ w, w ∉ Z → K' w = KL n w := fun w h => by
    simp only [K', hKn w h, KL]
  have hLev : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' := by
    refine ⟨fun w => ⟨?_, fun k hk => hKle w hk, fun k hk => hk⟩, ?_⟩
    · simp only [K', Subgroup.coe_subgroupOf]
      exact (hKo w).preimage continuous_subtype_val
    · refine Filter.eventually_cofinite.2 (Z.finite_toSet.subset fun w hw => ?_)
      by_contra h
      exact hw (hKL w h)
  obtain ⟨ι, hι, π, σ, hσ, -, hTr⟩ := hUS E hU n hn S hS lam K' hLev

  have hline : ∀ i, ∀ w ∈ S, w ∉ Z → fixed (σ i w).ρ (KL n w) ≠ ⊥ ∧ Module.finrank ℂ (fixed (σ i w).ρ (KL n w)) = 1 ∧
      ∃ B, ∀ hs : IsSplitAt w, HasSatGL w (toGL hs (σ i w)).ρ B := fun i w hw hz => by
    obtain ⟨hc, hne, hfd⟩ := (hσ i).2.2.2 w hw
    rw [hKL w hz] at hne
    by_cases hs : IsSplitAt w
    · obtain ⟨h1, B, hB⟩ := hSL E n w (toGL hs (σ i w)) (by rw [fixed_toGL]; exact hne)
      refine ⟨hne, ?_, B, fun _ => hB⟩
      rw [fixed_toGL] at h1
      exact h1
    · exact ⟨hne, hIL E hU n w hs (σ i w) hne (hfd _ (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).1),
        0, fun h => absurd h hs⟩
  let B₀ : ι → Pl E → Multiset ℂˣ := fun i w => Classical.epsilon fun B => ∀ hs : IsSplitAt w, HasSatGL w (toGL hs (σ i w)).ρ B
  have hB₀ : ∀ i, ∀ w ∈ S, w ∉ Z → ∀ hs : IsSplitAt w, HasSatGL w (toGL hs (σ i w)).ρ (B₀ i w) := fun i w hw hz =>
    Classical.epsilon_spec (p := fun B => ∀ hs : IsSplitAt w, HasSatGL w (toGL hs (σ i w)).ρ B) (hline i w hw hz).2.2
  let B : ι → Pl E → Multiset ℂˣ := fun i w => if w ∈ S then B₀ i w else inv (B₀ i (cPl w))
  have hBS : ∀ i, ∀ w ∈ S, B i w = B₀ i w := fun i w hw => if_pos hw
  have hBN : ∀ i w, w ∉ S → B i w = inv (B₀ i (cPl w)) := fun i w hw => if_neg hw
  let A : ι → ℂ := fun i => ∏ w ∈ Z, twTr (σ i w).ρ (KL n w) (K' w) (fun x => f w x.1) LinearMap.id
  refine ⟨K', ι, hι, π, A, B, hLev, fun i => ⟨(hσ i).1, fun w hns => ?_, fun w hoff hs => ?_⟩, fun T hT hd e₁ e₂ k => ?_⟩
  ·
    have hw : w ∈ S := by
      have hcw : cPl w = w := by
        by_contra h
        exact hns ((hcc w).2.2 h)
      rcases (hsec S hS w).1 with h | h
      · exact h
      · rwa [hcw] at h
    have hz : w ∉ Z := fun h => hns (hZ w h).2
    obtain ⟨φ, hφ, h0, hfix⟩ := (hσ i).2.2.1
    obtain ⟨p, hp, -⟩ := ((hσ i).2.2.2 w hw).1
    refine ⟨φ, hφ, h0, fun x hx hk => hfix w hw x hx ⟨p ⟨x, hx⟩, ?_, hp ⟨x, hx⟩⟩⟩
    rw [hKL w hz]
    change (p ⟨x, hx⟩).1 ∈ KGL w n
    rw [hp ⟨x, hx⟩]
    exact hk
  ·
    by_cases hw : w ∈ S
    · rw [hBS i w hw]
      exact ⟨toGL hs (σ i w), comp_toGL hs ((hσ i).2.2.2 w hw).1, hB₀ i w hw hoff.1 hs⟩
    · have hcw : cPl w ∈ S := ((hsec S hS w).1).resolve_left hw
      have hsc := hsplit' w hs
      have hu := hUC E n (π i) (cPl w) hsc (toGL hsc (σ i (cPl w))) (B₀ i (cPl w))
        (comp_toGL hsc ((hσ i).2.2.2 _ hcw).1) (hB₀ i _ hcw hoff.2 hsc)
      rw [(hcc w).1] at hu
      rw [hBN i w hw]
      exact hu
  ·
    have hTs : ∀ w ∈ T, w ∈ S ∧ IsSplitAt w ∧ w ∉ Z := fun w hw =>
      ⟨(hT w hw).1, (hT w hw).2, Finset.disjoint_left.1 hd hw⟩
    have hfZ : ∀ w ∈ Z, famU Z T f e₁ e₂ k w = fun x => f w x.1 := fun w hw => by
      simp [famU, hw]
    have hfT : ∀ w ∈ T, famU Z T f e₁ e₂ k w = fun x => fn1 n w (((e₁ w).pow k).mul ((e₂ w).pow k)) x.1 := fun w hw => by
      simp [famU, hw, (hTs w hw).2.2]
    have hfO : ∀ w, w ∉ Z → w ∉ T → famU Z T f e₁ e₂ k w = (KL n w : Set _).indicator 1 := fun w h1 h2 => by
      simp [famU, h1, h2]
    have htest : GlobalTheory.BCT.IsTest (KL n) K' (famU Z T f e₁ e₂ k) := by
      refine ⟨fun w => ?_, ?_⟩
      · by_cases h1 : w ∈ Z
        · rw [hfZ w h1]
          exact isHecke_val hU _ _ (hKf w h1) (K' w) fun k hk => hk
        · by_cases h2 : w ∈ T
          · rw [hfT w h2]
            exact isHecke_val hU _ _ (hEx E n w _).1 (K' w) fun k hk => hKle w hk
          · rw [hfO w h1 h2, hKL w h1]
            exact isHecke_ind hU
      · refine Filter.eventually_cofinite.2 ((Z ∪ T).finite_toSet.subset fun w hw => ?_)
        by_contra h
        have h' : w ∉ Z ∧ w ∉ T := by simpa using h
        exact hw (hfO w h'.1 h'.2)
    refine ⟨htest, ?_⟩
    have hr : ∃ w ∈ S, ∀ y, famU Z T f e₁ e₂ k w y ≠ 0 → y.1.val.charpoly.Separable := by
      obtain ⟨w, hw, hy⟩ := hreg
      refine ⟨w, (hZ w hw).1, fun y h => hy y.1 ?_⟩
      rwa [hfZ w hw] at h
    rw [← hTr _ htest hr]
    refine Finset.sum_congr rfl fun i _ => ?_
    set g : Pl E → ℂ := fun w => twTr (σ i w).ρ (KL n w) (K' w) (famU Z T f e₁ e₂ k w) LinearMap.id with hg
    have hone : ∀ w ∈ S, w ∉ Z → w ∉ T → g w = 1 := fun w hw h1 h2 => by
      obtain ⟨hne, hfr, -⟩ := hline i w hw h1
      simp only [hg]
      rw [hfO w h1 h2, hKL w h1]
      exact twTr_ind _ _ hfr hne
    have hUS' : ∀ w ∈ Z ∪ T, w ∈ S := fun w hw => by
      rcases Finset.mem_union.1 hw with h | h
      · exact (hZ w h).1
      · exact (hTs w h).1
    have hsupp : ∏ᶠ w ∈ S, g w = ∏ w ∈ Z ∪ T, g w := by
      rw [← finprod_mem_coe_finset]
      refine finprod_mem_inter_mulSupport_eq' _ _ _ fun w hw => ⟨fun h => ?_, fun h => hUS' w h⟩
      by_contra hn
      have h' : w ∉ Z ∧ w ∉ T := by simpa using hn
      exact hw (hone w h h'.1 h'.2)
    rw [hsupp, Finset.prod_union hd.symm]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun w hw => ?_) ?_
    · simp only [hg]
      rw [hfZ w hw]
    · rw [val1, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun w hw => ?_
      obtain ⟨hwS, hs, hz⟩ := hTs w hw
      have hinv : inv (inv (B₀ i w)) = B₀ i w := by simp [inv, Multiset.map_map]
      simp only [hg]
      rw [hfT w hw, hKL w hz, trace_test_function_eq hEx hU hs (σ i w) (hline i w hwS hz).2.1 (hB₀ i w hwS hz hs), hBS i w hwS,
        hBN i _ (hnot w hwS hs), (hcc w).1, hinv]
      simp only [ev1, Ex.ev, Ex.ev_pow, mul_pow]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

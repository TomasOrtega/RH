import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixedOpenSubgroupGLw

noncomputable section

open GlobalTheory.BCT GlobalTheory.PRep Matrix
open UpperTheory.V.Z.Tf.GlobalTraceComparison

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

section Generic

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Use extensionality with `k`. Prove the components needed by the constructor for the conclusion. Introduce `hk`. Establish `h` using `hk 1`. Simplify using `only [one_mul] at h`.

Assume the negation of the conclusion as `hn`. Rewrite `h` using `[Set.indicator_of_notMem (by simpa using hn), Set.indicator_of_mem (by simp [K'.one_mem])]`. Simplify using `at h`. Introduce `hk x`. Distinguish the cases in `hx : x ∈ K'`.

Rewrite using `[Set.indicator_of_mem (show x * k ∈ (K' : Set G) from K'.mul_mem hx hk), Set.indicator_of_mem (show x ∈ (K' : Set G) from hx)]`. Both sides reduce to the same expression. Establish `hxk : x * k ∉ K'` using `fun h => hx (by simpa using K'.mul_mem h (K'.inv_mem hk))`. Rewrite using `[Set.indicator_of_notMem (show x * k ∉ (K' : Set G) from hxk), Set.indicator_of_notMem (show x ∉ (K' : Set G) from hx)]`.
-/
private theorem rStab_ind (K' : Subgroup G) :
    rStab ((K' : Set G).indicator (1 : G → ℂ)) = K' := by
  classical
  ext k
  constructor
  · intro hk
    have h := hk 1
    simp only [one_mul] at h
    by_contra hn
    rw [Set.indicator_of_notMem (by simpa using hn), Set.indicator_of_mem (by simp [K'.one_mem])] at h
    simp at h
  · intro hk x
    by_cases hx : x ∈ K'
    · rw [Set.indicator_of_mem (show x * k ∈ (K' : Set G) from K'.mul_mem hx hk),
        Set.indicator_of_mem (show x ∈ (K' : Set G) from hx)]
      rfl
    · have hxk : x * k ∉ K' := fun h => hx (by simpa using K'.mul_mem h (K'.inv_mem hk))
      rw [Set.indicator_of_notMem (show x * k ∉ (K' : Set G) from hxk),
        Set.indicator_of_notMem (show x ∉ (K' : Set G) from hx)]

/- English proof (translation)
Use function extensionality and compare the values at `y`. Distinguish the cases in `hy : y ∈ K'`. Rewrite using `[Set.indicator_of_mem (show y⁻¹ ∈ (K' : Set G) from K'.inv_mem hy), Set.indicator_of_mem (show y ∈ (K' : Set G) from hy)]`. Both sides reduce to the same expression. Establish `: y⁻¹ ∉ K'` using `fun h => hy (by simpa using K'.inv_mem h)`.

Rewrite using `[Set.indicator_of_notMem (show y⁻¹ ∉ (K' : Set G) from this), Set.indicator_of_notMem (show y ∉ (K' : Set G) from hy)]`.
-/
private theorem ind_inv (K' : Subgroup G) :
    (fun y : G => (K' : Set G).indicator (1 : G → ℂ) y⁻¹) = (K' : Set G).indicator (1 : G → ℂ) := by
  classical
  funext y
  by_cases hy : y ∈ K'
  · rw [Set.indicator_of_mem (show y⁻¹ ∈ (K' : Set G) from K'.inv_mem hy),
      Set.indicator_of_mem (show y ∈ (K' : Set G) from hy)]
    rfl
  · have : y⁻¹ ∉ K' := fun h => hy (by simpa using K'.inv_mem h)
    rw [Set.indicator_of_notMem (show y⁻¹ ∉ (K' : Set G) from this),
      Set.indicator_of_notMem (show y ∉ (K' : Set G) from hy)]

/- English proof (translation)
Establish `hfx : ∀ h ∈ K', ρ h x = x` using `fun h hh => by simpa using hx ⟨h, hh⟩`. Establish `hout : ∀ q : G ⧸ K', q.out ∈ K' ↔ q = (QuotientGroup.mk 1 : G ⧸ K')`. Introduce `q`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `h2 : ((q.out : G) : G ⧸ K') = QuotientGroup.mk 1` using `QuotientGroup.eq.2 (by simpa using K'.inv_mem h)`. Rewrite `h2` using `[QuotientGroup.out_eq']`. Then use the resulting hypothesis. Introduce and unpack `rfl`. Use `QuotientGroup.mk_out_eq_mul K' (1 : G)` as an intermediate fact. Take `⟨h, hh⟩` from `this`.

Rewrite using `[hh]`. Simplify using `using h.2`. Unfold `levOp`. Rewrite using `[finsum_eq_single _ (QuotientGroup.mk 1 : G ⧸ K')]`. Rewrite using `[Set.indicator_of_mem (show (QuotientGroup.mk 1 : G ⧸ K').out ∈ (K' : Set G) from (hout _).2 rfl)]`.

Simplify using `[hfx _ ((hout _).2 rfl)]`. Introduce `q hq`. Rewrite using `[Set.indicator_of_notMem (show q.out ∉ (K' : Set G) from fun h => hq ((hout q).1 h))]`. Simplify using the standard rewrite rules.
-/
private theorem levOp_ind (ρ : Representation ℂ G V) (K K' : Subgroup G) (x : V) (hx : x ∈ fixed ρ K') :
    levOp ρ K K' ((K' : Set G).indicator (1 : G → ℂ)) LinearMap.id x = ((K'.relIndex K : ℕ) : ℂ)⁻¹ • x := by
  classical
  have hfx : ∀ h ∈ K', ρ h x = x := fun h hh => by simpa using hx ⟨h, hh⟩
  have hout : ∀ q : G ⧸ K', q.out ∈ K' ↔ q = (QuotientGroup.mk 1 : G ⧸ K') := by
    intro q
    constructor
    · intro h
      have h2 : ((q.out : G) : G ⧸ K') = QuotientGroup.mk 1 :=
        QuotientGroup.eq.2 (by simpa using K'.inv_mem h)
      rwa [QuotientGroup.out_eq'] at h2
    · rintro rfl
      have := QuotientGroup.mk_out_eq_mul K' (1 : G)
      obtain ⟨h, hh⟩ := this
      rw [hh]
      simpa using h.2
  unfold levOp
  rw [finsum_eq_single _ (QuotientGroup.mk 1 : G ⧸ K')]
  · rw [Set.indicator_of_mem (show (QuotientGroup.mk 1 : G ⧸ K').out ∈ (K' : Set G) from (hout _).2 rfl)]
    simp [hfx _ ((hout _).2 rfl)]
  · intro q hq
    rw [Set.indicator_of_notMem (show q.out ∉ (K' : Set G) from fun h => hq ((hout q).1 h))]
    simp

/- English proof (translation)
Establish `hlev : K ⊓ rStab ((K' : Set G).indicator (1 : G → ℂ)) ⊓ rStab (fun y : G => (K' : Set G).indicator (1 : G → ℂ) y⁻¹) = K'`. Rewrite using `[ind_inv, rStab_ind, inf_assoc, inf_idem]`. Conclude with `inf_eq_right.2 hle`. Unfold `trc`. Rewrite using `[hlev]`.

Establish `hc : ∀ v ∈ fixed ρ K', levOp ρ K K' ((K' : Set G).indicator (1 : G → ℂ)) LinearMap.id v ∈ fixed ρ K'`. Introduce `v hv`. Rewrite using `[levOp_ind ρ K K' v hv]`. Conclude with `Submodule.smul_mem _ _ hv`. Establish `hr : (levOp ρ K K' ((K' : Set G).indicator (1 : G → ℂ)) LinearMap.id).restrict hc = ((K'.relIndex K : ℕ) : ℂ)⁻¹ • LinearMap.id`.

Use extensionality with `v`. Simplify using `[LinearMap.restrict_apply, levOp_ind ρ K K' v v.2]`. Unfold `twTr`. Rewrite using `[dif_pos hc, hr, map_smul, LinearMap.trace_id, smul_eq_mul]`. Establish `hpos : Module.finrank ℂ (fixed ρ K') ≠ 0`.

Introduce `h0`. Conclude with `hne (Submodule.finrank_eq_zero.1 h0)`. Conclude with `mul_ne_zero (inv_ne_zero (by exact_mod_cast hi)) (by exact_mod_cast hpos)`.
-/
private theorem trc_ind_ne (ρ : Representation ℂ G V) (K K' : Subgroup G) (hle : K' ≤ K) (hi : K'.relIndex K ≠ 0)
    (hfd : FiniteDimensional ℂ (fixed ρ K')) (hne : fixed ρ K' ≠ ⊥) :
    trc ρ K ((K' : Set G).indicator (1 : G → ℂ)) ≠ 0 := by
  have hlev : K ⊓ rStab ((K' : Set G).indicator (1 : G → ℂ)) ⊓
      rStab (fun y : G => (K' : Set G).indicator (1 : G → ℂ) y⁻¹) = K' := by
    rw [ind_inv, rStab_ind, inf_assoc, inf_idem]
    exact inf_eq_right.2 hle
  unfold trc
  rw [hlev]
  have hc : ∀ v ∈ fixed ρ K', levOp ρ K K' ((K' : Set G).indicator (1 : G → ℂ)) LinearMap.id v ∈ fixed ρ K' := by
    intro v hv
    rw [levOp_ind ρ K K' v hv]
    exact Submodule.smul_mem _ _ hv
  have hr : (levOp ρ K K' ((K' : Set G).indicator (1 : G → ℂ)) LinearMap.id).restrict hc =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ • LinearMap.id := by
    ext v
    simp [LinearMap.restrict_apply, levOp_ind ρ K K' v v.2]
  unfold twTr
  rw [dif_pos hc, hr, map_smul, LinearMap.trace_id, smul_eq_mul]
  have hpos : Module.finrank ℂ (fixed ρ K') ≠ 0 := by
    intro h0
    exact hne (Submodule.finrank_eq_zero.1 h0)
  exact mul_ne_zero (inv_ne_zero (by exact_mod_cast hi)) (by exact_mod_cast hpos)

end Generic

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

/- English proof (translation)
Introduce `E _ _ _ n w τ`. Take `⟨ho, hc⟩` from `GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n`. Establish `hnt : Nontrivial τ.V`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nontrivial_iff_subsingleton]`.

Establish `hs : Subsingleton (Subrepresentation τ.ρ)` using `⟨fun a b => by`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Conclude with `Subsingleton.elim _ _⟩`. Use `haveI := τ.irred`. Conclude with `not_subsingleton (Subrepresentation τ.ρ) hs`.

Take `⟨v, hv⟩` from `exists_ne (0 : τ.V)`. Set `U : Subgroup (GLw n w)` to `{ carrier := {g | τ.ρ g v = v} one_mem' := by simp mul_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *`. Rewrite using `[hb, ha]`.

Use the proof step `inv_mem' := by`. Introduce `a ha`. Simplify using `only [Set.mem_setOf_eq] at *`. Use `conv_lhs => rw [← ha]`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`.

Simplify using `}`. Establish `hU : IsOpen (U : Set (GLw n w))` using `τ.smooth v`. Set `K' : Subgroup (GLw n w)` to `U ⊓ GlobalTheory.LFun.KGL w n`. Establish `hKo : IsOpen (K' : Set (GLw n w))` using `hU.inter ho`. Establish `hKc : IsCompact (K' : Set (GLw n w))` using `hc.inter_left (U.isClosed_of_isOpen hU)`.

Establish `hle : K' ≤ GlobalTheory.LFun.KGL w n` using `inf_le_right`. Establish `hfd : FiniteDimensional ℂ (fixed τ.ρ K')` using `finiteDimensional_fixed_openSubgroup_GLw E n w τ K' hKo`. Establish `hne : fixed τ.ρ K' ≠ ⊥`. Introduce `hb`. Establish `hm : v ∈ fixed τ.ρ K'` using `fun h => by`.

Establish `h1 : τ.ρ h v = v` using `h.2.1`. Simplify using `using h1`. Rewrite `hm` using `[hb]`. Conclude with `hv ((Submodule.mem_bot ℂ).1 hm)`. Establish `hi : K'.relIndex (GlobalTheory.LFun.KGL w n) ≠ 0` using `by haveI : CompactSpace (GlobalTheory.LFun.KGL w n) := isCompact_iff_compactSpace.1 hc haveI : Finite ((GlobalTheory.LFun.KGL w n) ⧸ K'.subgroupOf (GlobalTheory.LFun.KGL w n)) := Subgroup.quotient_finite_of_isOpen _ (hKo.preimage continuous_subtype_val)`.

Conclude with `(Subgroup.finiteIndex_of_finite_quotient (H := K'.subgroupOf (GlobalTheory.LFun.KGL w n))).index_ne_zero`. Use `⟨(K' : Set (GLw n w)).indicator 1, ⟨K', hKo, hle, ?_, ?_⟩, UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.trc_ind_ne τ.ρ _ K' hle hi hfd hne⟩` and prove the remaining obligations. Conclude with `HasCompactSupport.intro' hKc (K'.isClosed_of_isOpen hKo) fun x hx => Set.indicator_of_notMem hx _`. Introduce `k hk x`. Establish `h1 : (k * x ∈ (K' : Set (GLw n w))) ↔ x ∈ (K' : Set (GLw n w))` using `K'.mul_mem_cancel_left hk`.

Establish `h2 : (x * k ∈ (K' : Set (GLw n w))) ↔ x ∈ (K' : Set (GLw n w))` using `K'.mul_mem_cancel_right hk`. Use `show (K' : Set (GLw n w)).indicator 1 (k * x) = _ ∧ (K' : Set (GLw n w)).indicator 1 (x * k) = _`. Rewrite using `[Set.indicator_apply, Set.indicator_apply, Set.indicator_apply]`. Simplify using `only [h1, h2, Pi.one_apply, and_self]`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.levelFn :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.LevelFn := by
  intro E _ _ _ n w τ
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hnt : Nontrivial τ.V := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have hs : Subsingleton (Subrepresentation τ.ρ) :=
      ⟨fun a b => by
        apply Subrepresentation.toSubmodule_injective
        exact Subsingleton.elim _ _⟩
    haveI := τ.irred
    exact not_subsingleton (Subrepresentation τ.ρ) hs
  obtain ⟨v, hv⟩ := exists_ne (0 : τ.V)
  let U : Subgroup (GLw n w) :=
    { carrier := {g | τ.ρ g v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hb, ha]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  have hU : IsOpen (U : Set (GLw n w)) := τ.smooth v
  let K' : Subgroup (GLw n w) := U ⊓ GlobalTheory.LFun.KGL w n
  have hKo : IsOpen (K' : Set (GLw n w)) := hU.inter ho
  have hKc : IsCompact (K' : Set (GLw n w)) := hc.inter_left (U.isClosed_of_isOpen hU)
  have hle : K' ≤ GlobalTheory.LFun.KGL w n := inf_le_right
  have hfd : FiniteDimensional ℂ (fixed τ.ρ K') := finiteDimensional_fixed_openSubgroup_GLw E n w τ K' hKo
  have hne : fixed τ.ρ K' ≠ ⊥ := by
    intro hb
    have hm : v ∈ fixed τ.ρ K' := fun h => by
      have h1 : τ.ρ h v = v := h.2.1
      simpa using h1
    rw [hb] at hm
    exact hv ((Submodule.mem_bot ℂ).1 hm)
  have hi : K'.relIndex (GlobalTheory.LFun.KGL w n) ≠ 0 := by
    haveI : CompactSpace (GlobalTheory.LFun.KGL w n) := isCompact_iff_compactSpace.1 hc
    haveI : Finite ((GlobalTheory.LFun.KGL w n) ⧸ K'.subgroupOf (GlobalTheory.LFun.KGL w n)) :=
      Subgroup.quotient_finite_of_isOpen _ (hKo.preimage continuous_subtype_val)
    exact (Subgroup.finiteIndex_of_finite_quotient (H := K'.subgroupOf (GlobalTheory.LFun.KGL w n))).index_ne_zero
  refine ⟨(K' : Set (GLw n w)).indicator 1, ⟨K', hKo, hle, ?_, ?_⟩, UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.trc_ind_ne τ.ρ _ K' hle hi hfd hne⟩
  · exact HasCompactSupport.intro' hKc (K'.isClosed_of_isOpen hKo) fun x hx => Set.indicator_of_notMem hx _
  · classical
    intro k hk x
    have h1 : (k * x ∈ (K' : Set (GLw n w))) ↔ x ∈ (K' : Set (GLw n w)) := K'.mul_mem_cancel_left hk
    have h2 : (x * k ∈ (K' : Set (GLw n w))) ↔ x ∈ (K' : Set (GLw n w)) := K'.mul_mem_cancel_right hk
    show (K' : Set (GLw n w)).indicator 1 (k * x) = _ ∧ (K' : Set (GLw n w)).indicator 1 (x * k) = _
    rw [Set.indicator_apply, Set.indicator_apply, Set.indicator_apply]
    simp only [h1, h2, Pi.one_apply, and_self]

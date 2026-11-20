import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceIndicatorLevelLocalUnitary

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SplitPlace

section Generic

variable {G : Type} [Group G]

def toFull (H : Subgroup G) (hH : ∀ g, g ∈ H) : G →* H where
  toFun g := ⟨g, hH g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def quotEquiv (H : Subgroup G) (hH : ∀ g, g ∈ H) (K : Subgroup H) : H ⧸ K ≃ G ⧸ K.map H.subtype :=
  Quotient.congr (Equiv.ofBijective H.subtype ⟨Subtype.val_injective, fun g => ⟨⟨g, hH g⟩, rfl⟩⟩) fun a b => by
    change QuotientGroup.leftRel K a b ↔ QuotientGroup.leftRel (K.map H.subtype) a.1 b.1
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨x, hx, hxe⟩
      have : x = a⁻¹ * b := Subtype.ext hxe
      exact this ▸ hx

/- English proof (translation)
Use `haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK`. Establish `h1 : IsCompact ((QuotientGroup.mk : G → G ⧸ K) '' tsupport f)` using `hc.image continuous_quotient_mk'`. Use `h1.finite_of_discrete.subset fun q hq => ?_` and prove the remaining obligations. Conclude with `⟨q.out, subset_tsupport _ hq, QuotientGroup.out_eq' q⟩`.
-/
theorem finite_cosets [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G) (hK : IsOpen (K : Set G)) (f : G → ℂ)
    (hc : HasCompactSupport f) : {q : G ⧸ K | f q.out ≠ 0}.Finite := by
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK
  have h1 : IsCompact ((QuotientGroup.mk : G → G ⧸ K) '' tsupport f) := hc.image continuous_quotient_mk'
  refine h1.finite_of_discrete.subset fun q hq => ?_
  exact ⟨q.out, subset_tsupport _ hq, QuotientGroup.out_eq' q⟩

/- English proof (translation)
Establish `hcl : IsClosed {a : G | a ∈ H}`. Establish `: {a : G | a ∈ H} = Set.univ` using `Set.eq_univ_of_forall hH`. Rewrite using `[this]`. Conclude with `isClosed_univ`. Conclude with `hc.comp_isClosedEmbedding (Topology.IsClosedEmbedding.subtypeVal hcl)`.
-/
theorem hasCompactSupport_val [TopologicalSpace G] (H : Subgroup G) (hH : ∀ g, g ∈ H) (e : G → ℂ)
    (hc : HasCompactSupport e) : HasCompactSupport fun x : H => e x.1 := by
  have hcl : IsClosed {a : G | a ∈ H} := by
    have : {a : G | a ∈ H} = Set.univ := Set.eq_univ_of_forall hH
    rw [this]
    exact isClosed_univ
  exact hc.comp_isClosedEmbedding (Topology.IsClosedEmbedding.subtypeVal hcl)

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Establish `hr' : ((K'.relIndex K : ℕ) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hr`. Establish `hfin` using `finite_cosets K' hK' _ (hasCompactSupport_val H hH e hc)`. Establish `hs : (Function.support fun q : H ⧸ K' => ((fun x : H => ((K'.relIndex K : ℕ) : ℂ) * e x.1) q.out • (ρ q.out ∘ₗ LinearMap.id) : V →ₗ[ℂ] V)).Finite`. Use `hfin.subset fun q hq h0 => hq ?_` and prove the remaining obligations. Establish `h0' : e q.out.1 = 0` using `h0`.

Simplify using `[h0']`. Establish `h1 : levOp ρ K K' (fun x => ((K'.relIndex K : ℕ) : ℂ) * e x.1) LinearMap.id y = ((K'.relIndex K : ℕ) : ℂ)⁻¹ • (LinearMap.applyₗ y : (V →ₗ[ℂ] V) →ₗ[ℂ] V).toAddMonoidHom (∑ᶠ q : H ⧸ K', (fun x : H => ((K'.relIndex K : ℕ) : ℂ) * e x.1) q.out • (ρ q.out ∘ₗ LinearMap.id))` using `rfl`. Rewrite using `[h1, AddMonoidHom.map_finsum _ hs, smul_finsum, ← finsum_comp_equiv (quotEquiv H hH K')]`. Use `finsum_congr fun q => ?_` and prove the remaining obligations. Establish `hq : quotEquiv H hH K' q = ((q.out.1 : G) : G ⧸ K'.map H.subtype)` using `by conv_lhs => rw [← QuotientGroup.out_eq' q]`.

Both sides reduce to the same expression. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul (K'.map H.subtype) q.out.1`. Rewrite using `[hq, hk, hinv k.1 k.2]`. Establish `hk' : (toFull H hH k.1) ∈ K'`. Take `⟨x, hx, hxe⟩` from `k.2`.

Establish `: toFull H hH k.1 = x` using `Subtype.ext hxe.symm`. Conclude with `this ▸ hx`. Establish `hfix` using `(GlobalTheory.TwTrLin.mem_fixed_iff ρ K' y).1 hy _ hk'`. Establish `h2 : (ρ.comp (toFull H hH)) (q.out.1 * k.1) y = ρ q.out y`. Establish `: toFull H hH (q.out.1 * k.1) = q.out * toFull H hH k.1` using `Subtype.ext rfl`.

Rewrite using `[MonoidHom.comp_apply, this, map_mul, Module.End.mul_apply, hfix]`. Rewrite using `[h2]`. Simplify using `[smul_smul, hr']`.
-/
theorem levOp_full [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G) (hH : ∀ g, g ∈ H)
    (ρ : Representation ℂ H V) (K K' : Subgroup H) (hK' : IsOpen (K' : Set H)) (hr : K'.relIndex K ≠ 0) (e : G → ℂ)
    (hc : HasCompactSupport e) (hinv : ∀ k ∈ K'.map H.subtype, ∀ g, e (g * k) = e g) (y : V) (hy : y ∈ fixed ρ K') :
    levOp ρ K K' (fun x => ((K'.relIndex K : ℕ) : ℂ) * e x.1) LinearMap.id y =
      ∑ᶠ q : G ⧸ K'.map H.subtype, e q.out • (ρ.comp (toFull H hH)) q.out y := by
  have hr' : ((K'.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr
  have hfin := finite_cosets K' hK' _ (hasCompactSupport_val H hH e hc)
  have hs : (Function.support fun q : H ⧸ K' =>
      ((fun x : H => ((K'.relIndex K : ℕ) : ℂ) * e x.1) q.out • (ρ q.out ∘ₗ LinearMap.id) : V →ₗ[ℂ] V)).Finite := by
    refine hfin.subset fun q hq h0 => hq ?_
    have h0' : e q.out.1 = 0 := h0
    simp [h0']
  have h1 : levOp ρ K K' (fun x => ((K'.relIndex K : ℕ) : ℂ) * e x.1) LinearMap.id y =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ • (LinearMap.applyₗ y : (V →ₗ[ℂ] V) →ₗ[ℂ] V).toAddMonoidHom
        (∑ᶠ q : H ⧸ K', (fun x : H => ((K'.relIndex K : ℕ) : ℂ) * e x.1) q.out • (ρ q.out ∘ₗ LinearMap.id)) := rfl
  rw [h1, AddMonoidHom.map_finsum _ hs, smul_finsum, ← finsum_comp_equiv (quotEquiv H hH K')]
  refine finsum_congr fun q => ?_
  have hq : quotEquiv H hH K' q = ((q.out.1 : G) : G ⧸ K'.map H.subtype) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (K'.map H.subtype) q.out.1
  rw [hq, hk, hinv k.1 k.2]
  have hk' : (toFull H hH k.1) ∈ K' := by
    obtain ⟨x, hx, hxe⟩ := k.2
    have : toFull H hH k.1 = x := Subtype.ext hxe.symm
    exact this ▸ hx
  have hfix := (GlobalTheory.TwTrLin.mem_fixed_iff ρ K' y).1 hy _ hk'
  have h2 : (ρ.comp (toFull H hH)) (q.out.1 * k.1) y = ρ q.out y := by
    have : toFull H hH (q.out.1 * k.1) = q.out * toFull H hH k.1 := Subtype.ext rfl
    rw [MonoidHom.comp_apply, this, map_mul, Module.End.mul_apply, hfix]
  rw [h2]
  simp [smul_smul, hr']

def fullIrr [TopologicalSpace G] (H : Subgroup G) (hH : ∀ g, g ∈ H) (σ : SmIrr H) : SmIrr G where
  V := σ.V
  ρ := σ.ρ.comp (toFull H hH)
  smooth v := (σ.smooth v).preimage (Continuous.subtype_mk continuous_id hH)
  irred := by
    obtain ⟨h0, h⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 σ.irred
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g v hv => ?_⟩
    exact hW g.1 v hv

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Unfold `UL`. Rewrite using `[if_pos hw]`. Conclude with `Subgroup.mem_top g`.
-/
theorem mem_UL {w : Pl E} (hw : IsSplitAt w) (g : GLw n w) : g ∈ UL n w := by
  unfold UL
  rw [if_pos hw]
  exact Subgroup.mem_top g

/- English proof (translation)
Introduce `E _ _ _ n w hw σ`. Establish `hH` using `mem_UL (n := n) hw`. Use `⟨fullIrr (UL n w) hH σ, LinearEquiv.refl ℂ σ.V, fun _ _ => rfl, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `π ⟨p, hp, -, f, hf0, hfm, hfe⟩`. Use `⟨(fullIrr (UL n w) hH σ).irred, f, hf0, hfm, fun x v => ?_⟩` and prove the remaining obligations.

Establish `hpx : toFull (UL n w) hH (((cLoc w).comp (locU n w).subtype) x) = p x` using `Subtype.ext (hp x).symm`. Express the relevant statement in the definitionally equal form `f (σ.ρ (toFull (UL n w) hH (((cLoc w).comp (locU n w).subtype) x)) v) = _`. Rewrite using `[hpx]`. Conclude with `hfe x v`. Introduce `K' hlev e hk`.

Take `⟨-, -, hcs, hinv⟩` from `hk`. Establish `hKK : ∀ k ∈ K', ∀ x : UL n w, (k.1 * x.1 * 1 : GLw n w) = (k * x).1` using `fun k _ x => by simp`. Use `⟨⟨hasCompactSupport_val _ hH e hcs, fun k hk x => ⟨?_, ?_⟩⟩, fun y hy => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Use `hinv k.1 ⟨k, hk, rfl⟩ 1 (by simp) x.1` as an intermediate fact. Simplify using `using this`.

Use `hinv 1 (by simp) k.1 ⟨k, hk, rfl⟩ x.1` as an intermediate fact. Simplify using `using this`. Use `(GlobalTheory.TwTrLin.mem_fixed_iff _ _ _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, hk, rfl⟩`. Conclude with `(GlobalTheory.TwTrLin.mem_fixed_iff σ.ρ K' y).1 hy k hk`.

Establish `hr` using `(GlobalTheory.TwTrUnit.twTr_unit E n w K' hlev σ).2.1`. Conclude with `levOp_full (UL n w) hH σ.ρ (KL n w) K' hlev.1 hr e hcs (fun k hk g => by simpa using hinv 1 (by simp) k hk g) y hy`.
-/
theorem splitDict : PositivityTheory.Rg.BcB.F.Eig.SplitDict := by
  intro E _ _ _ n w hw σ
  have hH := mem_UL (n := n) hw
  refine ⟨fullIrr (UL n w) hH σ, LinearEquiv.refl ℂ σ.V, fun _ _ => rfl, ?_, ?_⟩
  · rintro π ⟨p, hp, -, f, hf0, hfm, hfe⟩
    refine ⟨(fullIrr (UL n w) hH σ).irred, f, hf0, hfm, fun x v => ?_⟩
    have hpx : toFull (UL n w) hH (((cLoc w).comp (locU n w).subtype) x) = p x := Subtype.ext (hp x).symm
    change f (σ.ρ (toFull (UL n w) hH (((cLoc w).comp (locU n w).subtype) x)) v) = _
    rw [hpx]
    exact hfe x v
  · intro K' hlev e hk
    obtain ⟨-, -, hcs, hinv⟩ := hk
    have hKK : ∀ k ∈ K', ∀ x : UL n w, (k.1 * x.1 * 1 : GLw n w) = (k * x).1 := fun k _ x => by simp
    refine ⟨⟨hasCompactSupport_val _ hH e hcs, fun k hk x => ⟨?_, ?_⟩⟩, fun y hy => ⟨?_, ?_⟩⟩
    · have := hinv k.1 ⟨k, hk, rfl⟩ 1 (by simp) x.1
      simpa using this
    · have := hinv 1 (by simp) k.1 ⟨k, hk, rfl⟩ x.1
      simpa using this
    · refine (GlobalTheory.TwTrLin.mem_fixed_iff _ _ _).2 ?_
      rintro _ ⟨k, hk, rfl⟩
      exact (GlobalTheory.TwTrLin.mem_fixed_iff σ.ρ K' y).1 hy k hk
    · have hr := (GlobalTheory.TwTrUnit.twTr_unit E n w K' hlev σ).2.1
      exact levOp_full (UL n w) hH σ.ρ (KL n w) K' hlev.1 hr e hcs
        (fun k hk g => by simpa using hinv 1 (by simp) k hk g) y hy

end GlobalTheory.CompanionTheory.SplitPlace

end

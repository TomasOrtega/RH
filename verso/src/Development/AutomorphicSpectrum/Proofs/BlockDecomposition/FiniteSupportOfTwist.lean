import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralOfTwistConjugatePlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SuppFinTw

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

open scoped Pointwise

/- English proof (translation)
Use `(hF.image (DoubleCoset.mk H K)).subset ?_` and prove the remaining obligations. Introduce and unpack `q ⟨k, hk, hq⟩`. Take `⟨h, hh, f, hf, k', hk', e⟩` from `hA _ hq`. Use `⟨f, hf, ?_⟩` and prove the remaining obligations. Rewrite using `[← DoubleCoset.out_eq' H K q]`.

Use `(DoubleCoset.eq H K _ _).2 ⟨h, hh, k' * k⁻¹, mul_mem hk' (inv_mem hk), ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← e, mul_inv_cancel_right]`.
-/
theorem cover_quot {G : Type} [Group G] (H K : Subgroup G) (A F : Set G) (hF : F.Finite)
    (hA : ∀ x ∈ A, ∃ h ∈ H, ∃ f ∈ F, ∃ k ∈ K, x = h * f * k) :
    {q : DoubleCoset.Quotient (H : Set G) (K : Set G) | ∃ k ∈ K, Quotient.out q * k ∈ A}.Finite := by
  refine (hF.image (DoubleCoset.mk H K)).subset ?_
  rintro q ⟨k, hk, hq⟩
  obtain ⟨h, hh, f, hf, k', hk', e⟩ := hA _ hq
  refine ⟨f, hf, ?_⟩
  rw [← DoubleCoset.out_eq' H K q]
  refine (DoubleCoset.eq H K _ _).2 ⟨h, hh, k' * k⁻¹, mul_mem hk' (inv_mem hk), ?_⟩
  rw [← mul_assoc, ← e, mul_inv_cancel_right]

/- English proof (translation)
Use `set T := twCent θ δ with hT`. Use `set Tc := cptPart T with hTc`. Set `L : G → Subgroup G` to `fun f => T ⊓ K.map (MulAut.conj f).toMonoidHom`. Establish `hL : ∀ f, Finite (Tc ⧸ (L f).subgroupOf Tc)` using `fun f => by`. Establish `h : ((L f).subgroupOf Tc).index ≠ 0` using `(hG.2 f).2`.

Use `haveI : ((L f).subgroupOf Tc).FiniteIndex := ⟨h⟩`. Conclude with `Subgroup.finite_quotient_of_finiteIndex`. Set `Rr : Set G` to `Set.range fun q : DoubleCoset.Quotient ((Γ.subgroupOf T : Subgroup T) : Set T) ((Tc.subgroupOf T : Subgroup T) : Set T) => ((Quotient.out q : T) : G)`. Set `P : G → Set G` to `fun f => Set.range fun q : Tc ⧸ (L f).subgroupOf Tc => ((q.out : Tc) : G)`. Establish `hRr : Rr.Finite` using `Set.finite_range _`.

Establish `hP : ∀ f, (P f).Finite` using `fun f => by haveI := hL f`. Conclude with `Set.finite_range _`. Use `⟨⋃ f ∈ F, (fun p : G × G => p.1 * p.2 * f) '' (Rr ×ˢ P f), hF.biUnion fun f _ => (hRr.prod (hP f)).image _, fun t ht f hf => ?_⟩` and prove the remaining obligations. Take `⟨h, c, hh, hc, e⟩` from `DoubleCoset.mk_out_eq_mul (Γ.subgroupOf T) (Tc.subgroupOf T) (⟨t, ht⟩ : T)`. Use `set r : T := Quotient.out (DoubleCoset.mk (Γ.subgroupOf T) (Tc.subgroupOf T) (⟨t, ht⟩ : T)) with hr`.

Establish `hhΓ : (h : G) ∈ Γ` using `Subgroup.mem_subgroupOf.1 hh`. Establish `hcT : (c : G) ∈ Tc` using `Subgroup.mem_subgroupOf.1 hc`. Establish `e' : (r : G) = h * t * c` using `by rw [e]; rfl`. Take `⟨l, hl⟩` from `QuotientGroup.mk_out_eq_mul ((L f).subgroupOf Tc) (⟨(c : G)⁻¹, inv_mem hcT⟩ : Tc)`. Use `set σ : Tc := (QuotientGroup.mk (⟨(c : G)⁻¹, inv_mem hcT⟩ : Tc) : Tc ⧸ (L f).subgroupOf Tc).out with hσ`.

Establish `hlL : ((l : Tc) : G) ∈ L f` using `Subgroup.mem_subgroupOf.1 l.2`. Establish `e2 : (σ : G) = (c : G)⁻¹ * ((l : Tc) : G)` using `by rw [hl]; rfl`. Take `⟨k, hk, ek⟩` from `Subgroup.mem_map.1 hlL.2`. Establish `ek' : f * k * f⁻¹ = ((l : Tc) : G)` using `ek`. Use `⟨(h : G)⁻¹, inv_mem hhΓ, r * σ * f, Set.mem_biUnion hf ⟨((r : G), (σ : G)), ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩, rfl⟩, k⁻¹, inv_mem hk, ?_⟩` and prove the remaining obligations.

Rewrite using `[e', e2, ← ek']`. Use `group`.
-/
theorem cover_gam {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K Γ : Subgroup G) (δ : G)
    (hG : Good θ K δ)
    (hfin : Finite (DoubleCoset.Quotient ((Γ.subgroupOf (twCent θ δ) : Subgroup (twCent θ δ)) : Set (twCent θ δ))
      ((cptPart (twCent θ δ)).subgroupOf (twCent θ δ) : Set (twCent θ δ))))
    (F : Set G) (hF : F.Finite) :
    ∃ F' : Set G, F'.Finite ∧ ∀ t ∈ twCent θ δ, ∀ f ∈ F, ∃ γ ∈ Γ, ∃ f' ∈ F', ∃ k ∈ K, t * f = γ * f' * k := by
  set T := twCent θ δ with hT
  set Tc := cptPart T with hTc
  let L : G → Subgroup G := fun f => T ⊓ K.map (MulAut.conj f).toMonoidHom
  have hL : ∀ f, Finite (Tc ⧸ (L f).subgroupOf Tc) := fun f => by
    have h : ((L f).subgroupOf Tc).index ≠ 0 := (hG.2 f).2
    haveI : ((L f).subgroupOf Tc).FiniteIndex := ⟨h⟩
    exact Subgroup.finite_quotient_of_finiteIndex
  let Rr : Set G := Set.range fun q : DoubleCoset.Quotient ((Γ.subgroupOf T : Subgroup T) : Set T)
    ((Tc.subgroupOf T : Subgroup T) : Set T) => ((Quotient.out q : T) : G)
  let P : G → Set G := fun f => Set.range fun q : Tc ⧸ (L f).subgroupOf Tc => ((q.out : Tc) : G)
  have hRr : Rr.Finite := Set.finite_range _
  have hP : ∀ f, (P f).Finite := fun f => by
    haveI := hL f
    exact Set.finite_range _
  refine ⟨⋃ f ∈ F, (fun p : G × G => p.1 * p.2 * f) '' (Rr ×ˢ P f),
    hF.biUnion fun f _ => (hRr.prod (hP f)).image _, fun t ht f hf => ?_⟩
  obtain ⟨h, c, hh, hc, e⟩ := DoubleCoset.mk_out_eq_mul (Γ.subgroupOf T) (Tc.subgroupOf T) (⟨t, ht⟩ : T)
  set r : T := Quotient.out (DoubleCoset.mk (Γ.subgroupOf T) (Tc.subgroupOf T) (⟨t, ht⟩ : T)) with hr
  have hhΓ : (h : G) ∈ Γ := Subgroup.mem_subgroupOf.1 hh
  have hcT : (c : G) ∈ Tc := Subgroup.mem_subgroupOf.1 hc
  have e' : (r : G) = h * t * c := by rw [e]; rfl
  obtain ⟨l, hl⟩ := QuotientGroup.mk_out_eq_mul ((L f).subgroupOf Tc) (⟨(c : G)⁻¹, inv_mem hcT⟩ : Tc)
  set σ : Tc := (QuotientGroup.mk (⟨(c : G)⁻¹, inv_mem hcT⟩ : Tc) : Tc ⧸ (L f).subgroupOf Tc).out with hσ
  have hlL : ((l : Tc) : G) ∈ L f := Subgroup.mem_subgroupOf.1 l.2
  have e2 : (σ : G) = (c : G)⁻¹ * ((l : Tc) : G) := by rw [hl]; rfl
  obtain ⟨k, hk, ek⟩ := Subgroup.mem_map.1 hlL.2
  have ek' : f * k * f⁻¹ = ((l : Tc) : G) := ek
  refine ⟨(h : G)⁻¹, inv_mem hhΓ, r * σ * f, Set.mem_biUnion hf ⟨((r : G), (σ : G)), ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩, rfl⟩, k⁻¹, inv_mem hk, ?_⟩
  rw [e', e2, ← ek']
  group

/- English proof (translation)
Use `⟨⋃ q ∈ {q : DoubleCoset.Quotient (twCent θ d : Set H) (K : Set H) | ∃ k ∈ K, (Quotient.out q * k)⁻¹ * d * θ (Quotient.out q * k) ∈ C}, (fun k => Quotient.out q * k) '' (K : Set H), hf.isCompact_biUnion fun q _ => hK.image (continuous_const.mul continuous_id), fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨h, k, hh, hk, e⟩` from `DoubleCoset.mk_out_eq_mul (twCent θ d) K z`. Establish `hh' : h * d = d * θ h` using `hh`. Establish `ez : Quotient.out (DoubleCoset.mk (twCent θ d) K z) * k⁻¹ = h * z` using `by rw [e, mul_inv_cancel_right]`. Use `⟨h⁻¹, inv_mem hh, ?_⟩` and prove the remaining obligations.

Rewrite using `[inv_inv]`. Use `Set.mem_biUnion (x := DoubleCoset.mk (twCent θ d) K z) ⟨k⁻¹, inv_mem hk, ?_⟩ ⟨k⁻¹, inv_mem hk, ez⟩` and prove the remaining obligations. Rewrite using `[ez, map_mul]`. Establish `e3 : (h * z)⁻¹ * d * (θ h * θ z) = z⁻¹ * (h⁻¹ * (d * θ h)) * θ z` using `by group`. Rewrite using `[e3, ← hh', inv_mul_cancel_left]`.

Conclude with `hz`.
-/
theorem cover_of_fin {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (θ : H →* H) (K : Subgroup H)
    (hK : IsCompact (K : Set H)) (d : H) (C : Set H)
    (hf : {q : DoubleCoset.Quotient (twCent θ d : Set H) (K : Set H) | ∃ k ∈ K,
      (Quotient.out q * k)⁻¹ * d * θ (Quotient.out q * k) ∈ C}.Finite) :
    ∃ B : Set H, IsCompact B ∧ ∀ z, z⁻¹ * d * θ z ∈ C → ∃ t ∈ twCent θ d, t⁻¹ * z ∈ B := by
  refine ⟨⋃ q ∈ {q : DoubleCoset.Quotient (twCent θ d : Set H) (K : Set H) | ∃ k ∈ K,
      (Quotient.out q * k)⁻¹ * d * θ (Quotient.out q * k) ∈ C}, (fun k => Quotient.out q * k) '' (K : Set H),
    hf.isCompact_biUnion fun q _ => hK.image (continuous_const.mul continuous_id), fun z hz => ?_⟩
  obtain ⟨h, k, hh, hk, e⟩ := DoubleCoset.mk_out_eq_mul (twCent θ d) K z
  have hh' : h * d = d * θ h := hh
  have ez : Quotient.out (DoubleCoset.mk (twCent θ d) K z) * k⁻¹ = h * z := by rw [e, mul_inv_cancel_right]
  refine ⟨h⁻¹, inv_mem hh, ?_⟩
  rw [inv_inv]
  refine Set.mem_biUnion (x := DoubleCoset.mk (twCent θ d) K z) ⟨k⁻¹, inv_mem hk, ?_⟩ ⟨k⁻¹, inv_mem hk, ez⟩
  rw [ez, map_mul]
  have e3 : (h * z)⁻¹ * d * (θ h * θ z) = z⁻¹ * (h⁻¹ * (d * θ h)) * θ z := by group
  rw [e3, ← hh', inv_mul_cancel_left]
  exact hz

/- English proof (translation)
Use `set δ := dG δ₁ δ₂ with hδ`. Use `set g := thP E a b (δ⁻¹ * t₀ * δ) with hg`. Apply the tactic sequence `obtain ⟨t, hz⟩ := exists_of_family (fun u => if u ∈ S then atH a b u t₀ else atH a b u g) (by filter_upwards [ae_mem t₀, ae_mem g] with u h1 h2 split_ifs <;> assumption)`. Establish `hin : ∀ u ∈ S, atH a b u t = atH a b u t₀` using `fun u hu => by rw [hz, if_pos hu]`. Establish `hout : ∀ u, u ∉ S → atH a b u t = atH a b u g` using `fun u hu => by rw [hz, if_neg hu]`.

Use `⟨t, ?_, hin⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `t * δ = δ * thP E a b t`. Use `ext_atH fun u => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul]`. Distinguish the cases in `huS : u ∈ S`.

Distinguish the cases in `hsp : IsSplitAt u`. Establish `hc` using `conj_not_mem hS huS hsp`. Establish `e1 : atH a b u (thP E a b t) = atH a b u (thP E a b g)` using `atH_thP_congr rfl (hout _ hc)`. Rewrite using `[e1, hg, thP_thP, map_mul, map_mul, map_inv, hin u huS]`. Use `group`.

Establish `hm : atH a b u t₀ * dW u δ₁ δ₂ = dW u δ₁ δ₂ * thW a b u (atH a b u t₀)` using `ht u huS`. Rewrite using `[usage₇ hsp, hδ, atH_dG_of_not_split hsp, hin u huS]`. Conclude with `hm`. Take `⟨v, hv, rfl⟩` from `(mem_or_conj hS u).resolve_left huS`. Establish `hne : GlobalTheory.EulerTw.cPl E v ≠ v` using `fun e => huS (by rw [e]; exact hv)`.

Establish `hsp` using `split_of_conj_ne hne`. Establish `e1 : atH a b (GlobalTheory.EulerTw.cPl E v) (thP E a b t) = atH a b (GlobalTheory.EulerTw.cPl E v) (thP E a b t₀)` using `atH_thP_congr (cPl_cPl v) (hin v hv)`. Rewrite using `[e1, hout _ huS, hg]`. Establish `hc : atH a b v (t₀ * (δ * thP E a b δ)) = atH a b v ((δ * thP E a b δ) * t₀)`. Establish `hm : atH a b v t₀ * dW v δ₁ δ₂ = dW v δ₁ δ₂ * thW a b v (atH a b v t₀)` using `ht v hv`.

Rewrite `hm` using `[thW_of_split hsp]`. Rewrite using `[map_mul (atH a b v) t₀, map_mul (atH a b v) (δ * _) t₀, hδ, atH_norm_of_split hsp]`. Conclude with `hm`. Establish `hc'` using `atH_thP_congr (cPl_cPl v) hc`. Simplify using `only [map_mul, map_inv, thP_thP] at hc' ⊢`.

Establish `h3` using `congrArg (fun z => (atH a b (GlobalTheory.EulerTw.cPl E v) (thP E a b δ))⁻¹ * z) hc'`. Simplify `h3` using `[mul_assoc]`.
-/
theorem glue {S : Set (Pl E)} (hS : IsSection S) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) (t₀ : Gf E a b)
    (ht : ∀ w ∈ S, atH a b w t₀ ∈ twCent (thW a b w) (dW w δ₁ δ₂)) :
    ∃ t ∈ twCent (thP E a b) (dG δ₁ δ₂), ∀ w ∈ S, atH a b w t = atH a b w t₀ := by
  set δ := dG δ₁ δ₂ with hδ
  set g := thP E a b (δ⁻¹ * t₀ * δ) with hg
  obtain ⟨t, hz⟩ := exists_of_family (fun u => if u ∈ S then atH a b u t₀ else atH a b u g) (by
    filter_upwards [ae_mem t₀, ae_mem g] with u h1 h2
    split_ifs <;> assumption)
  have hin : ∀ u ∈ S, atH a b u t = atH a b u t₀ := fun u hu => by rw [hz, if_pos hu]
  have hout : ∀ u, u ∉ S → atH a b u t = atH a b u g := fun u hu => by rw [hz, if_neg hu]
  refine ⟨t, ?_, hin⟩
  change t * δ = δ * thP E a b t
  refine ext_atH fun u => ?_
  rw [map_mul, map_mul]
  by_cases huS : u ∈ S
  · by_cases hsp : IsSplitAt u
    · have hc := conj_not_mem hS huS hsp
      have e1 : atH a b u (thP E a b t) = atH a b u (thP E a b g) := atH_thP_congr rfl (hout _ hc)
      rw [e1, hg, thP_thP, map_mul, map_mul, map_inv, hin u huS]
      group
    · have hm : atH a b u t₀ * dW u δ₁ δ₂ = dW u δ₁ δ₂ * thW a b u (atH a b u t₀) := ht u huS
      rw [usage₇ hsp, hδ, atH_dG_of_not_split hsp, hin u huS]
      exact hm
  · obtain ⟨v, hv, rfl⟩ := (mem_or_conj hS u).resolve_left huS
    have hne : GlobalTheory.EulerTw.cPl E v ≠ v := fun e => huS (by rw [e]; exact hv)
    have hsp := split_of_conj_ne hne
    have e1 : atH a b (GlobalTheory.EulerTw.cPl E v) (thP E a b t) = atH a b (GlobalTheory.EulerTw.cPl E v) (thP E a b t₀) :=
      atH_thP_congr (cPl_cPl v) (hin v hv)
    rw [e1, hout _ huS, hg]
    have hc : atH a b v (t₀ * (δ * thP E a b δ)) = atH a b v ((δ * thP E a b δ) * t₀) := by
      have hm : atH a b v t₀ * dW v δ₁ δ₂ = dW v δ₁ δ₂ * thW a b v (atH a b v t₀) := ht v hv
      rw [thW_of_split hsp] at hm
      rw [map_mul (atH a b v) t₀, map_mul (atH a b v) (δ * _) t₀, hδ, atH_norm_of_split hsp]
      exact hm
    have hc' := atH_thP_congr (cPl_cPl v) hc
    simp only [map_mul, map_inv, thP_thP] at hc' ⊢
    have h3 := congrArg (fun z => (atH a b (GlobalTheory.EulerTw.cPl E v) (thP E a b δ))⁻¹ * z) hc'
    simpa [mul_assoc] using h3

/- English proof (translation)
Set `P : Set (Gf E a b)` to `{x | ∀ w ∈ S, atH a b w x ∈ B w ∧ atH a b w (thP E a b x) ∈ B' w}`. Set `Φ : Gf E a b → ∀ w : R, ((GLw a w.1 × GLw b w.1) ⧸ K2 (E` to `E) a b w.1) × ((GLw a w.1 × GLw b w.1) ⧸ K2 (E := E) a b w.1) := fun x w => (QuotientGroup.mk (atH a b w.1 x), QuotientGroup.mk (atH a b w.1 (thP E a b x)))`. Establish `hopen : ∀ w : Pl E, IsOpen (K2 (E` using `E) a b w : Set (GLw a w × GLw b w)) := fun w => by`. Rewrite using `[Subgroup.coe_prod]`. Conclude with `(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1`.

Establish `hq : ∀ (w : Pl E) (C : Set (GLw a w × GLw b w)), IsCompact C → (QuotientGroup.mk '' C : Set ((GLw a w × GLw b w) ⧸ K2 (E` using `E) a b w)).Finite := fun w C hC => by haveI := QuotientGroup.discreteTopology (hopen w)`. Conclude with `(hC.image continuous_quotient_mk').finite_of_discrete`. Establish `hfin : (Φ '' P).Finite`. Use `(Set.Finite.pi (t := fun w : R => (QuotientGroup.mk '' B w.1) ×ˢ (QuotientGroup.mk '' B' w.1)) fun w => (hq _ _ (hB _ (hR _ w.2))).prod (hq _ _ (hB' _ (hR _ w.2)))).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩ w -`.

Conclude with `⟨⟨_, (hx _ (hR _ w.2)).1, rfl⟩, ⟨_, (hx _ (hR _ w.2)).2, rfl⟩⟩`. Use `⟨Function.invFunOn Φ P '' (Φ '' P), hfin.image _, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hex : ∃ y ∈ P, Φ y = Φ x` using `⟨x, hx, rfl⟩`. Use `set f := Function.invFunOn Φ P (Φ x) with hf`. Establish `hfP : f ∈ P` using `Function.invFunOn_mem hex`.

Establish `hΦ : Φ f = Φ x` using `Function.invFunOn_eq hex`. Use `⟨f, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, f⁻¹ * x, ?_, by group⟩` and prove the remaining obligations. Establish `key : ∀ v ∈ S, atH a b v (f⁻¹ * x) ∈ K2 a b v ∧ atH a b v (thP E a b (f⁻¹ * x)) ∈ K2 a b v`. Introduce `v hv`. Rewrite using `[map_mul, map_mul, map_inv, map_inv, map_mul, map_inv]`.

Distinguish the cases in `hvR : v ∈ R`. Establish `h` using `congrFun hΦ ⟨v, hvR⟩`. Conclude with `⟨QuotientGroup.eq.1 (congrArg Prod.fst h), QuotientGroup.eq.1 (congrArg Prod.snd h)⟩`. Conclude with `⟨mul_mem (inv_mem (hK v hv hvR (hfP v hv).1)) (hK v hv hvR (hx v hv).1), mul_mem (inv_mem (hK' v hv hvR (hfP v hv).2)) (hK' v hv hvR (hx v hv).2)⟩`. Rewrite using `[mem_KK_iff]`.

Introduce `u`. Break down `mem_or_conj hS u with hu | ⟨v, hv, rfl⟩` into its components or cases. Conclude with `(key u hu).1`. Conclude with `integral_of_twist_conjugate_place v (key v hv).2`.
-/
theorem finite_cover {S : Set (Pl E)} (hS : IsSection S) (R : Finset (Pl E)) (hR : ∀ w ∈ R, w ∈ S)
    (B B' : ∀ w : Pl E, Set (GLw a w × GLw b w)) (hB : ∀ w ∈ S, IsCompact (B w)) (hB' : ∀ w ∈ S, IsCompact (B' w))
    (hK : ∀ w ∈ S, w ∉ R → B w ⊆ K2 a b w) (hK' : ∀ w ∈ S, w ∉ R → B' w ⊆ K2 a b w) :
    ∃ F : Set (Gf E a b), F.Finite ∧ ∀ x, (∀ w ∈ S, atH a b w x ∈ B w ∧ atH a b w (thP E a b x) ∈ B' w) →
      ∃ f ∈ F, ∃ k ∈ KK E a b, x = f * k := by
  let P : Set (Gf E a b) := {x | ∀ w ∈ S, atH a b w x ∈ B w ∧ atH a b w (thP E a b x) ∈ B' w}
  let Φ : Gf E a b → ∀ w : R, ((GLw a w.1 × GLw b w.1) ⧸ K2 (E := E) a b w.1) × ((GLw a w.1 × GLw b w.1) ⧸ K2 (E := E) a b w.1) :=
    fun x w => (QuotientGroup.mk (atH a b w.1 x), QuotientGroup.mk (atH a b w.1 (thP E a b x)))
  have hopen : ∀ w : Pl E, IsOpen (K2 (E := E) a b w : Set (GLw a w × GLw b w)) := fun w => by
    rw [Subgroup.coe_prod]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1
  have hq : ∀ (w : Pl E) (C : Set (GLw a w × GLw b w)), IsCompact C →
      (QuotientGroup.mk '' C : Set ((GLw a w × GLw b w) ⧸ K2 (E := E) a b w)).Finite := fun w C hC => by
    haveI := QuotientGroup.discreteTopology (hopen w)
    exact (hC.image continuous_quotient_mk').finite_of_discrete
  have hfin : (Φ '' P).Finite := by
    refine (Set.Finite.pi (t := fun w : R => (QuotientGroup.mk '' B w.1) ×ˢ (QuotientGroup.mk '' B' w.1))
      fun w => (hq _ _ (hB _ (hR _ w.2))).prod (hq _ _ (hB' _ (hR _ w.2)))).subset ?_
    rintro _ ⟨x, hx, rfl⟩ w -
    exact ⟨⟨_, (hx _ (hR _ w.2)).1, rfl⟩, ⟨_, (hx _ (hR _ w.2)).2, rfl⟩⟩
  refine ⟨Function.invFunOn Φ P '' (Φ '' P), hfin.image _, fun x hx => ?_⟩
  have hex : ∃ y ∈ P, Φ y = Φ x := ⟨x, hx, rfl⟩
  set f := Function.invFunOn Φ P (Φ x) with hf
  have hfP : f ∈ P := Function.invFunOn_mem hex
  have hΦ : Φ f = Φ x := Function.invFunOn_eq hex
  refine ⟨f, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, f⁻¹ * x, ?_, by group⟩
  have key : ∀ v ∈ S, atH a b v (f⁻¹ * x) ∈ K2 a b v ∧ atH a b v (thP E a b (f⁻¹ * x)) ∈ K2 a b v := by
    intro v hv
    rw [map_mul, map_mul, map_inv, map_inv, map_mul, map_inv]
    by_cases hvR : v ∈ R
    · have h := congrFun hΦ ⟨v, hvR⟩
      exact ⟨QuotientGroup.eq.1 (congrArg Prod.fst h), QuotientGroup.eq.1 (congrArg Prod.snd h)⟩
    · exact ⟨mul_mem (inv_mem (hK v hv hvR (hfP v hv).1)) (hK v hv hvR (hx v hv).1),
        mul_mem (inv_mem (hK' v hv hvR (hfP v hv).2)) (hK' v hv hvR (hx v hv).2)⟩
  rw [mem_KK_iff]
  intro u
  rcases mem_or_conj hS u with hu | ⟨v, hv, rfl⟩
  · exact (key u hu).1
  · exact integral_of_twist_conjugate_place v (key v hv).2

/- English proof (translation)
Take `⟨K₁, K₂, -, -, h₃⟩` from `h`. Conclude with `⟨fun w => (h₃.1 w).1, h₃.2⟩`.
-/
theorem test_parts {φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ} (h : IsTestP φ) :
    (∀ w, HasCompactSupport (φ w)) ∧ ∀ᶠ w in cofinite, φ w = (K2 (E := E) a b w : Set (GLw a w × GLw b w)).indicator 1 := by
  obtain ⟨K₁, K₂, -, -, h₃⟩ := h
  exact ⟨fun w => (h₃.1 w).1, h₃.2⟩

/- English proof (translation)
Use `set f : Pl E → ℂ := fun w => φ₁ w (atW w y) * if IsSplitAt w then φ₂ w (atW w (thP E a b y)) else 1 with hf`. Establish `hfin : (S ∩ Function.mulSupport f).Finite`. Establish `hae : ∀ᶠ u in cofinite, f u = 1` using `by filter_upwards [(test_parts h₁).2, (test_parts h₂).2, ae_mem y, ae_mem (thP E a b y)] with u a₁ a₂ a₃ a₄`. Establish `b₃ : atW u y ∈ (K2 (E` using `E) a b u : Set (GLw a u × GLw b u)) := a₃`. Establish `b₄ : atW u (thP E a b y) ∈ (K2 (E` using `E) a b u : Set (GLw a u × GLw b u)) := a₄`.

Simplify using `only [hf, a₁, a₂, Set.indicator_of_mem b₃, Set.indicator_of_mem b₄]`. Apply the tactic sequence `split_ifs <;> simp`. Conclude with `(Filter.eventually_cofinite.1 hae).subset fun u hu => hu.2`. Establish `hne : f w ≠ 0`. Introduce `h0`.

Apply `h` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `∏ᶠ w ∈ S, f w = 0`. Rewrite using `[← finprod_mem_inter_mulSupport f S, finprod_mem_eq_finite_toFinset_prod f hfin]`. Use `Finset.prod_eq_zero (i := w) ?_ h0` and prove the remaining obligations. Rewrite using `[Set.Finite.mem_toFinset]`.

Conclude with `⟨hw, by rw [Function.mem_mulSupport, h0]; exact zero_ne_one⟩`. Use `⟨left_ne_zero_of_mul hne, fun hs => ?_⟩` and prove the remaining obligations. Use `right_ne_zero_of_mul hne` as an intermediate fact. Rewrite `this` using `[if_pos hs]`. Then use the resulting hypothesis.
-/
theorem factors_ne {S : Set (Pl E)} {φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂)
    (y : Gf E a b) (h : finFn S φ₁ φ₂ y ≠ 0) (w : Pl E) (hw : w ∈ S) :
    φ₁ w (atH a b w y) ≠ 0 ∧ (IsSplitAt w → φ₂ w (atH a b w (thP E a b y)) ≠ 0) := by
  set f : Pl E → ℂ := fun w => φ₁ w (atW w y) * if IsSplitAt w then φ₂ w (atW w (thP E a b y)) else 1 with hf
  have hfin : (S ∩ Function.mulSupport f).Finite := by
    have hae : ∀ᶠ u in cofinite, f u = 1 := by
      filter_upwards [(test_parts h₁).2, (test_parts h₂).2, ae_mem y, ae_mem (thP E a b y)] with u a₁ a₂ a₃ a₄
      have b₃ : atW u y ∈ (K2 (E := E) a b u : Set (GLw a u × GLw b u)) := a₃
      have b₄ : atW u (thP E a b y) ∈ (K2 (E := E) a b u : Set (GLw a u × GLw b u)) := a₄
      simp only [hf, a₁, a₂, Set.indicator_of_mem b₃, Set.indicator_of_mem b₄]
      split_ifs <;> simp
    exact (Filter.eventually_cofinite.1 hae).subset fun u hu => hu.2
  have hne : f w ≠ 0 := by
    intro h0
    apply h
    change ∏ᶠ w ∈ S, f w = 0
    rw [← finprod_mem_inter_mulSupport f S, finprod_mem_eq_finite_toFinset_prod f hfin]
    refine Finset.prod_eq_zero (i := w) ?_ h0
    rw [Set.Finite.mem_toFinset]
    exact ⟨hw, by rw [Function.mem_mulSupport, h0]; exact zero_ne_one⟩
  refine ⟨left_ne_zero_of_mul hne, fun hs => ?_⟩
  have := right_ne_zero_of_mul hne
  rwa [if_pos hs] at this

/- English proof (translation)
Establish `sep₁ : ∀ w : Pl E, (nrmL a w (locEl a w δ₁)).val.charpoly.Separable` using `fun w => by`. Rewrite using `[(GlobalTheory.BCT.ThBasic.twist_basic E hU a w).2.2.2.2.2.2.2.2.1 δ₁]`. Conclude with `e₁.2.2.1.map`. Establish `sep₂ : ∀ w : Pl E, (nrmL b w (locEl b w δ₂)).val.charpoly.Separable` using `fun w => by`. Rewrite using `[(GlobalTheory.BCT.ThBasic.twist_basic E hU b w).2.2.2.2.2.2.2.2.1 δ₂]`.

Conclude with `e₂.2.2.1.map`. Establish `hKc : ∀ w : Pl E, IsCompact (K2 (E` using `E) a b w : Set (GLw a w × GLw b w)) := fun w => by`. Rewrite using `[Subgroup.coe_prod]`. Conclude with `(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2`. Set `C' : ∀ w : Pl E, Set (GLw a w × GLw b w)` to `fun w => if IsSplitAt w then tsupport (φ₁ w) * tsupport (φ₂ w) else tsupport (φ₁ w)`.

Establish `hC' : ∀ w, IsCompact (C' w)` using `fun w => by`. Distinguish the cases in `h : IsSplitAt w`. Simplify using `only [C', if_pos h]`. Conclude with `((test_parts h₁).1 w).isCompact.mul ((test_parts h₂).1 w).isCompact`. Simplify using `only [C', if_neg h]`.

Conclude with `((test_parts h₁).1 w).isCompact`. Use `choose B₀ hB₀c hB₀ using fun w : Pl E => cover_of_fin (thW a b w) (K2 a b w) (hKc w) (dW w δ₁ δ₂) (C' w) ((LS E hU a b w (dW w δ₁ δ₂) (sep₁ w) (sep₂ w)).1 (C' w) (hC' w))`. Establish `hUA` using `UA E hU a b S hS δ₁ δ₂ e₁ e₂`. Set `Gd : Pl E → Prop` to `fun w => φ₁ w = (K2 (E := E) a b w : Set (GLw a w × GLw b w)).indicator 1 ∧ φ₂ w = (K2 (E := E) a b w : Set (GLw a w × GLw b w)).indicator 1 ∧ atH a b w (dG δ₁ δ₂) ∈ K2 a b w`. Establish `hbad1 : {w | ¬ Gd w}.Finite`.

Use `Filter.eventually_cofinite.1 ?_` and prove the remaining obligations. Use `filter_upwards [(test_parts h₁).2, (test_parts h₂).2, ae_mem (dG δ₁ δ₂)] with u a₁ a₂ a₃`. Conclude with `⟨a₁, a₂, a₃⟩`. Establish `hbad2` using `(Filter.eventually_cofinite.1 hUA).image Subtype.val`. Establish `hRs` using `(hbad1.union hbad2).inter_of_right S`.

Set `R : Finset (Pl E)` to `hRs.toFinset`. Establish `hRS : ∀ w ∈ R, w ∈ S` using `fun w hw => ((Set.Finite.mem_toFinset _).1 hw).1`. Establish `hG1 : ∀ w ∈ S, w ∉ R → Gd w` using `fun w hw hR => by`. Assume the negation of the conclusion as `hn`. Conclude with `hR ((Set.Finite.mem_toFinset _).2 ⟨hw, Or.inl hn⟩)`.

Establish `hG2 : ∀ w ∈ S, w ∉ R → ∀ g : GLw a w × GLw b w, g⁻¹ * dW w δ₁ δ₂ * thW a b w g ∈ K2 (E` using `E) a b w → ∃ t ∈ twCent (thW a b w) (dW w δ₁ δ₂), t⁻¹ * g ∈ K2 (E := E) a b w := fun w hw hR => by`. Assume the negation of the conclusion as `hn`. Use `hR ((Set.Finite.mem_toFinset _).2 ⟨hw, Or.inr ⟨⟨w, hw⟩, fun hc => hn ?_, rfl⟩⟩)` and prove the remaining obligations. Conclude with `(hc _ rfl).2.1`. Set `B : ∀ w : Pl E, Set (GLw a w × GLw b w)` to `fun w => if w ∈ R then B₀ w else K2 (E := E) a b w`.

Set `Cc : ∀ w : Pl E, Set (GLw a w × GLw b w)` to `fun w => if w ∈ R then tsupport (φ₁ w) else K2 (E := E) a b w`. Set `B' : ∀ w : Pl E, Set (GLw a w × GLw b w)` to `fun w => ({(atH a b w (dG δ₁ δ₂))⁻¹} * B w) * Cc w`. Establish `hBc : ∀ w, IsCompact (B w)` using `fun w => by`. Distinguish the cases in `h : w ∈ R`. Simplify using `only [B, if_pos h]`.

Conclude with `hB₀c w`. Simplify using `only [B, if_neg h]`. Conclude with `hKc w`. Establish `hCc : ∀ w, IsCompact (Cc w)` using `fun w => by`. Distinguish the cases in `h : w ∈ R`.

Simplify using `only [Cc, if_pos h]`. Conclude with `((test_parts h₁).1 w).isCompact`. Simplify using `only [Cc, if_neg h]`. Conclude with `hKc w`. Establish `hB'c : ∀ w, IsCompact (B' w)` using `fun w => (isCompact_singleton.mul (hBc w)).mul (hCc w)`.

Establish `hK : ∀ w ∈ S, w ∉ R → B w ⊆ K2 (E` using `E) a b w := fun w _ h => by simp only [B, if_neg h]; exact subset_rfl`. Establish `hK' : ∀ w ∈ S, w ∉ R → B' w ⊆ K2 (E` using `E) a b w := by`. Introduce and unpack `w hw hR _ ⟨_, ⟨_, rfl, p, hp, rfl⟩, c, hc, rfl⟩`. Establish `hc' : c ∈ K2 (E` using `E) a b w := by`. Establish `h : c ∈ Cc w` using `hc`.

Simplify using `only [Cc, if_neg hR] at h`. Conclude with `h`. Conclude with `mul_mem (mul_mem (inv_mem (hG1 w hw hR).2.2) (hK w hw hR hp)) hc'`. Take `⟨F, hF, hcov⟩` from `finite_cover hS R hRS B B' (fun w _ => hBc w) (fun w _ => hB'c w) hK hK'`. Use `⟨F, hF, fun x hx => ?_⟩` and prove the remaining obligations.

Use `set δ := dG δ₁ δ₂ with hδ`. Use `set y := x⁻¹ * δ * thP E a b x with hy`. Establish `hy0 : finFn S φ₁ φ₂ y ≠ 0` using `hx`. Establish `fac` using `factors_ne h₁ h₂ y hy0`. Establish `hyK : ∀ w ∈ S, w ∉ R → atH a b w y ∈ K2 (E` using `E) a b w := fun w hw hR => by`.

Assume the negation of the conclusion as `hn`. Apply `(fac w hw).1` to reduce the goal to its premises. Rewrite using `[(hG1 w hw hR).1]`. Conclude with `Set.indicator_of_notMem hn _`. Establish `hyK2 : ∀ w ∈ S, w ∉ R → IsSplitAt w → atH a b w (thP E a b y) ∈ K2 (E` using `E) a b w := fun w hw hR hs => by`.

Assume the negation of the conclusion as `hn`. Apply `(fac w hw).2 hs` to reduce the goal to its premises. Rewrite using `[(hG1 w hw hR).2.1]`. Conclude with `Set.indicator_of_notMem hn _`. Establish `hyC : ∀ w ∈ S, atH a b w y ∈ Cc w` using `fun w hw => by`.

Distinguish the cases in `hR : w ∈ R`. Simplify using `only [Cc, if_pos hR]`. Conclude with `subset_tsupport _ (fac w hw).1`. Simplify using `only [Cc, if_neg hR]`. Conclude with `hyK w hw hR`.

Establish `hsplit : ∀ w, IsSplitAt w → (atH a b w x)⁻¹ * dW w δ₁ δ₂ * thW a b w (atH a b w x) = atH a b w y * atH a b w (thP E a b y)` using `fun w hs => by`. Establish `e : y * thP E a b y = x⁻¹ * (δ * thP E a b δ) * x`. Simplify using `only [hy, map_mul, map_inv, thP_thP]`. Use `group`. Rewrite using `[thW_of_split hs, ← atH_norm_of_split hs, ← hδ, ← map_mul, e]`.

Simplify using `only [map_mul, map_inv]`. Establish `hinert : ∀ w, ¬ IsSplitAt w → (atH a b w x)⁻¹ * dW w δ₁ δ₂ * thW a b w (atH a b w x) = atH a b w y` using `fun w hs => by`. Rewrite using `[hy, map_mul, map_mul, map_inv, usage₇ hs, hδ, atH_dG_of_not_split hs]`. Establish `hloc : ∀ w ∈ S, ∃ t ∈ twCent (thW a b w) (dW w δ₁ δ₂), t⁻¹ * atH a b w x ∈ B w`. Introduce `w hw`.

Distinguish the cases in `hR : w ∈ R`. Simplify using `only [B, if_pos hR]`. Use `hB₀ w _ ?_` and prove the remaining obligations. Distinguish the cases in `hs : IsSplitAt w`. Simplify using `only [C', if_pos hs]`.

Rewrite using `[hsplit w hs]`. Conclude with `Set.mul_mem_mul (subset_tsupport _ (fac w hw).1) (subset_tsupport _ ((fac w hw).2 hs))`. Simplify using `only [C', if_neg hs]`. Rewrite using `[hinert w hs]`. Conclude with `subset_tsupport _ (fac w hw).1`.

Simplify using `only [B, if_neg hR]`. Use `hG2 w hw hR _ ?_` and prove the remaining obligations. Distinguish the cases in `hs : IsSplitAt w`. Rewrite using `[hsplit w hs]`. Conclude with `mul_mem (hyK w hw hR) (hyK2 w hw hR hs)`.

Rewrite using `[hinert w hs]`. Conclude with `hyK w hw hR`. Use `choose! tw htw htwB using hloc`. Take `⟨t₀, ht₀⟩` from `exists_of_family (fun u => if u ∈ S then tw u else 1) (by filter_upwards [ae_mem x, R.finite_toSet.compl_mem_cofinite] with u hxu huR`. Establish `huR' : u ∉ R` using `by simpa using huR`.

Distinguish the cases in `hu : u ∈ S`. Rewrite using `[if_pos hu]`. Establish `hb : (tw u)⁻¹ * atH a b u x ∈ K2 (E` using `E) a b u := by`. Establish `h` using `htwB u hu`. Simplify using `only [B, if_neg huR'] at h`.

Conclude with `h`. Establish `e : tw u = atH a b u x * ((tw u)⁻¹ * atH a b u x)⁻¹` using `by group`. Rewrite using `[e]`. Conclude with `mul_mem hxu (inv_mem hb)`. Rewrite using `[if_neg hu]`.

Conclude with `one_mem _)`. Establish `ht₀S : ∀ w ∈ S, atH a b w t₀ = tw w` using `fun w hw => by rw [ht₀, if_pos hw]`. Take `⟨t, htT, htS⟩` from `glue hS δ₁ δ₂ t₀ (fun w hw => by rw [ht₀S w hw]; exact htw w hw)`. Establish `ht' : t * δ = δ * thP E a b t` using `htT`. Establish `hth : thP E a b (t⁻¹ * x) = δ⁻¹ * (t⁻¹ * x) * y`.

Establish `e : δ⁻¹ * t⁻¹ = (thP E a b t)⁻¹ * δ⁻¹`. Rewrite using `[← _root_.mul_inv_rev, ← _root_.mul_inv_rev, ht']`. Rewrite using `[hy, map_mul, map_inv, ← mul_assoc δ⁻¹, e]`. Use `group`. Take `⟨f, hf, k, hk, e⟩` from `hcov (t⁻¹ * x) (fun w hw => by`.

Establish `hfirst : atH a b w (t⁻¹ * x) ∈ B w`. Rewrite using `[map_mul, map_inv, htS w hw, ht₀S w hw]`. Conclude with `htwB w hw`. Use `⟨hfirst, ?_⟩` and prove the remaining obligations. Rewrite using `[hth, map_mul, map_mul, map_inv]`.

Conclude with `Set.mul_mem_mul (Set.mul_mem_mul rfl hfirst) (hyC w hw))`. Use `⟨t, htT, f, hf, k, hk, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc, ← e, mul_inv_cancel_left]`.
-/
theorem exists_cover (hU : GlobalTheory.BCT.Unr E) (LS : LocSupp) (UA : UnitAE) {S : Set (Pl E)} (hS : IsSection S)
    {φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂)
    (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) (e₁ : polE δ₁ ∈ Ell E a) (e₂ : polE δ₂ ∈ Ell E b) :
    ∃ F : Set (Gf E a b), F.Finite ∧ ∀ x, orbFn S φ₁ φ₂ δ₁ δ₂ x ≠ 0 →
      ∃ t ∈ twCent (thP E a b) (dG δ₁ δ₂), ∃ f ∈ F, ∃ k ∈ KK E a b, x = t * f * k := by
  have sep₁ : ∀ w : Pl E, (nrmL a w (locEl a w δ₁)).val.charpoly.Separable := fun w => by
    rw [(GlobalTheory.BCT.ThBasic.twist_basic E hU a w).2.2.2.2.2.2.2.2.1 δ₁]
    exact e₁.2.2.1.map
  have sep₂ : ∀ w : Pl E, (nrmL b w (locEl b w δ₂)).val.charpoly.Separable := fun w => by
    rw [(GlobalTheory.BCT.ThBasic.twist_basic E hU b w).2.2.2.2.2.2.2.2.1 δ₂]
    exact e₂.2.2.1.map
  have hKc : ∀ w : Pl E, IsCompact (K2 (E := E) a b w : Set (GLw a w × GLw b w)) := fun w => by
    rw [Subgroup.coe_prod]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2
  let C' : ∀ w : Pl E, Set (GLw a w × GLw b w) := fun w =>
    if IsSplitAt w then tsupport (φ₁ w) * tsupport (φ₂ w) else tsupport (φ₁ w)
  have hC' : ∀ w, IsCompact (C' w) := fun w => by
    by_cases h : IsSplitAt w
    · simp only [C', if_pos h]
      exact ((test_parts h₁).1 w).isCompact.mul ((test_parts h₂).1 w).isCompact
    · simp only [C', if_neg h]
      exact ((test_parts h₁).1 w).isCompact
  choose B₀ hB₀c hB₀ using fun w : Pl E => cover_of_fin (thW a b w) (K2 a b w) (hKc w) (dW w δ₁ δ₂) (C' w)
    ((LS E hU a b w (dW w δ₁ δ₂) (sep₁ w) (sep₂ w)).1 (C' w) (hC' w))
  have hUA := UA E hU a b S hS δ₁ δ₂ e₁ e₂
  let Gd : Pl E → Prop := fun w => φ₁ w = (K2 (E := E) a b w : Set (GLw a w × GLw b w)).indicator 1 ∧
    φ₂ w = (K2 (E := E) a b w : Set (GLw a w × GLw b w)).indicator 1 ∧ atH a b w (dG δ₁ δ₂) ∈ K2 a b w
  have hbad1 : {w | ¬ Gd w}.Finite := by
    refine Filter.eventually_cofinite.1 ?_
    filter_upwards [(test_parts h₁).2, (test_parts h₂).2, ae_mem (dG δ₁ δ₂)] with u a₁ a₂ a₃
    exact ⟨a₁, a₂, a₃⟩
  have hbad2 := (Filter.eventually_cofinite.1 hUA).image Subtype.val
  have hRs := (hbad1.union hbad2).inter_of_right S
  let R : Finset (Pl E) := hRs.toFinset
  have hRS : ∀ w ∈ R, w ∈ S := fun w hw => ((Set.Finite.mem_toFinset _).1 hw).1
  have hG1 : ∀ w ∈ S, w ∉ R → Gd w := fun w hw hR => by
    by_contra hn
    exact hR ((Set.Finite.mem_toFinset _).2 ⟨hw, Or.inl hn⟩)
  have hG2 : ∀ w ∈ S, w ∉ R → ∀ g : GLw a w × GLw b w, g⁻¹ * dW w δ₁ δ₂ * thW a b w g ∈ K2 (E := E) a b w →
      ∃ t ∈ twCent (thW a b w) (dW w δ₁ δ₂), t⁻¹ * g ∈ K2 (E := E) a b w := fun w hw hR => by
    by_contra hn
    refine hR ((Set.Finite.mem_toFinset _).2 ⟨hw, Or.inr ⟨⟨w, hw⟩, fun hc => hn ?_, rfl⟩⟩)
    exact (hc _ rfl).2.1
  let B : ∀ w : Pl E, Set (GLw a w × GLw b w) := fun w => if w ∈ R then B₀ w else K2 (E := E) a b w
  let Cc : ∀ w : Pl E, Set (GLw a w × GLw b w) := fun w => if w ∈ R then tsupport (φ₁ w) else K2 (E := E) a b w
  let B' : ∀ w : Pl E, Set (GLw a w × GLw b w) := fun w => ({(atH a b w (dG δ₁ δ₂))⁻¹} * B w) * Cc w
  have hBc : ∀ w, IsCompact (B w) := fun w => by
    by_cases h : w ∈ R
    · simp only [B, if_pos h]; exact hB₀c w
    · simp only [B, if_neg h]; exact hKc w
  have hCc : ∀ w, IsCompact (Cc w) := fun w => by
    by_cases h : w ∈ R
    · simp only [Cc, if_pos h]; exact ((test_parts h₁).1 w).isCompact
    · simp only [Cc, if_neg h]; exact hKc w
  have hB'c : ∀ w, IsCompact (B' w) := fun w => (isCompact_singleton.mul (hBc w)).mul (hCc w)
  have hK : ∀ w ∈ S, w ∉ R → B w ⊆ K2 (E := E) a b w := fun w _ h => by simp only [B, if_neg h]; exact subset_rfl
  have hK' : ∀ w ∈ S, w ∉ R → B' w ⊆ K2 (E := E) a b w := by
    rintro w hw hR _ ⟨_, ⟨_, rfl, p, hp, rfl⟩, c, hc, rfl⟩
    have hc' : c ∈ K2 (E := E) a b w := by
      have h : c ∈ Cc w := hc
      simp only [Cc, if_neg hR] at h
      exact h
    exact mul_mem (mul_mem (inv_mem (hG1 w hw hR).2.2) (hK w hw hR hp)) hc'
  obtain ⟨F, hF, hcov⟩ := finite_cover hS R hRS B B' (fun w _ => hBc w) (fun w _ => hB'c w) hK hK'
  refine ⟨F, hF, fun x hx => ?_⟩
  set δ := dG δ₁ δ₂ with hδ
  set y := x⁻¹ * δ * thP E a b x with hy
  have hy0 : finFn S φ₁ φ₂ y ≠ 0 := hx
  have fac := factors_ne h₁ h₂ y hy0
  have hyK : ∀ w ∈ S, w ∉ R → atH a b w y ∈ K2 (E := E) a b w := fun w hw hR => by
    by_contra hn
    apply (fac w hw).1
    rw [(hG1 w hw hR).1]
    exact Set.indicator_of_notMem hn _
  have hyK2 : ∀ w ∈ S, w ∉ R → IsSplitAt w → atH a b w (thP E a b y) ∈ K2 (E := E) a b w := fun w hw hR hs => by
    by_contra hn
    apply (fac w hw).2 hs
    rw [(hG1 w hw hR).2.1]
    exact Set.indicator_of_notMem hn _
  have hyC : ∀ w ∈ S, atH a b w y ∈ Cc w := fun w hw => by
    by_cases hR : w ∈ R
    · simp only [Cc, if_pos hR]; exact subset_tsupport _ (fac w hw).1
    · simp only [Cc, if_neg hR]; exact hyK w hw hR
  have hsplit : ∀ w, IsSplitAt w → (atH a b w x)⁻¹ * dW w δ₁ δ₂ * thW a b w (atH a b w x) =
      atH a b w y * atH a b w (thP E a b y) := fun w hs => by
    have e : y * thP E a b y = x⁻¹ * (δ * thP E a b δ) * x := by
      simp only [hy, map_mul, map_inv, thP_thP]
      group
    rw [thW_of_split hs, ← atH_norm_of_split hs, ← hδ, ← map_mul, e]
    simp only [map_mul, map_inv]
  have hinert : ∀ w, ¬ IsSplitAt w → (atH a b w x)⁻¹ * dW w δ₁ δ₂ * thW a b w (atH a b w x) = atH a b w y := fun w hs => by
    rw [hy, map_mul, map_mul, map_inv, usage₇ hs, hδ, atH_dG_of_not_split hs]
  have hloc : ∀ w ∈ S, ∃ t ∈ twCent (thW a b w) (dW w δ₁ δ₂), t⁻¹ * atH a b w x ∈ B w := by
    intro w hw
    by_cases hR : w ∈ R
    · simp only [B, if_pos hR]
      refine hB₀ w _ ?_
      by_cases hs : IsSplitAt w
      · simp only [C', if_pos hs]
        rw [hsplit w hs]
        exact Set.mul_mem_mul (subset_tsupport _ (fac w hw).1) (subset_tsupport _ ((fac w hw).2 hs))
      · simp only [C', if_neg hs]
        rw [hinert w hs]
        exact subset_tsupport _ (fac w hw).1
    · simp only [B, if_neg hR]
      refine hG2 w hw hR _ ?_
      by_cases hs : IsSplitAt w
      · rw [hsplit w hs]
        exact mul_mem (hyK w hw hR) (hyK2 w hw hR hs)
      · rw [hinert w hs]
        exact hyK w hw hR
  choose! tw htw htwB using hloc
  obtain ⟨t₀, ht₀⟩ := exists_of_family (fun u => if u ∈ S then tw u else 1) (by
    filter_upwards [ae_mem x, R.finite_toSet.compl_mem_cofinite] with u hxu huR
    have huR' : u ∉ R := by simpa using huR
    by_cases hu : u ∈ S
    · rw [if_pos hu]
      have hb : (tw u)⁻¹ * atH a b u x ∈ K2 (E := E) a b u := by
        have h := htwB u hu
        simp only [B, if_neg huR'] at h
        exact h
      have e : tw u = atH a b u x * ((tw u)⁻¹ * atH a b u x)⁻¹ := by group
      rw [e]
      exact mul_mem hxu (inv_mem hb)
    · rw [if_neg hu]
      exact one_mem _)
  have ht₀S : ∀ w ∈ S, atH a b w t₀ = tw w := fun w hw => by rw [ht₀, if_pos hw]
  obtain ⟨t, htT, htS⟩ := glue hS δ₁ δ₂ t₀ (fun w hw => by rw [ht₀S w hw]; exact htw w hw)
  have ht' : t * δ = δ * thP E a b t := htT
  have hth : thP E a b (t⁻¹ * x) = δ⁻¹ * (t⁻¹ * x) * y := by
    have e : δ⁻¹ * t⁻¹ = (thP E a b t)⁻¹ * δ⁻¹ := by
      rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, ht']
    rw [hy, map_mul, map_inv, ← mul_assoc δ⁻¹, e]
    group
  obtain ⟨f, hf, k, hk, e⟩ := hcov (t⁻¹ * x) (fun w hw => by
    have hfirst : atH a b w (t⁻¹ * x) ∈ B w := by
      rw [map_mul, map_inv, htS w hw, ht₀S w hw]
      exact htwB w hw
    refine ⟨hfirst, ?_⟩
    rw [hth, map_mul, map_mul, map_inv]
    exact Set.mul_mem_mul (Set.mul_mem_mul rfl hfirst) (hyC w hw))
  refine ⟨t, htT, f, hf, k, hk, ?_⟩
  rw [mul_assoc, ← e, mul_inv_cancel_left]

/- English proof (translation)
Introduce `LS UA RF _ E _ _ _ hU a b S hS φ₁ φ₂ h₁ h₂ δ₁ δ₂ e₁ e₂`. Take `⟨F, hF, hcov⟩` from `exists_cover hU LS UA hS h₁ h₂ δ₁ δ₂ e₁ e₂`. Take `⟨hG, -, -, hfin⟩` from `RF E hU a b δ₁ δ₂ e₁ e₂`. Take `⟨F', hF', hc'⟩` from `cover_gam (thP E a b) (KK E a b) (gam δ₁ δ₂) (dG δ₁ δ₂) hG hfin F hF`. Use `⟨cover_quot _ _ {x | orbFn S φ₁ φ₂ δ₁ δ₂ x ≠ 0} F hF hcov, cover_quot _ _ {x | orbFn S φ₁ φ₂ δ₁ δ₂ x ≠ 0} F' hF' fun x hx => ?_⟩` and prove the remaining obligations.

Take `⟨t, ht, f, hf, k, hk, e⟩` from `hcov x hx`. Take `⟨γ, hγ, f', hf', k', hk', e'⟩` from `hc' t ht f hf`. Conclude with `⟨γ, hγ, f', hf', k' * k, mul_mem hk' hk, by rw [e, e', mul_assoc _ k' k]⟩`.
-/
theorem suppFinOf : SuppFinOf := by
  intro LS UA RF _ E _ _ _ hU a b S hS φ₁ φ₂ h₁ h₂ δ₁ δ₂ e₁ e₂
  obtain ⟨F, hF, hcov⟩ := exists_cover hU LS UA hS h₁ h₂ δ₁ δ₂ e₁ e₂
  obtain ⟨hG, -, -, hfin⟩ := RF E hU a b δ₁ δ₂ e₁ e₂
  obtain ⟨F', hF', hc'⟩ := cover_gam (thP E a b) (KK E a b) (gam δ₁ δ₂) (dG δ₁ δ₂) hG hfin F hF
  refine ⟨cover_quot _ _ {x | orbFn S φ₁ φ₂ δ₁ δ₂ x ≠ 0} F hF hcov,
    cover_quot _ _ {x | orbFn S φ₁ φ₂ δ₁ δ₂ x ≠ 0} F' hF' fun x hx => ?_⟩
  obtain ⟨t, ht, f, hf, k, hk, e⟩ := hcov x hx
  obtain ⟨γ, hγ, f', hf', k', hk', e'⟩ := hc' t ht f hf
  exact ⟨γ, hγ, f', hf', k' * k, mul_mem hk' hk, by rw [e, e', mul_assoc _ k' k]⟩

end GlobalTheory.CompanionTheory.SuppFinTw

end

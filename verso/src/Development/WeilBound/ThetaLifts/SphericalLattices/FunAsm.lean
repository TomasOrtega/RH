import Development.WeilBound.ThetaLifts.SphericalLattices.FunDefs
import Development.WeilBound.CoreStatements.LocalThetaKernels.EvlMain
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Inertof
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Kcompact

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

/- English proof (translation)
Establish `: CompactSpace K` using `isCompact_iff_compactSpace.1 hK`. Establish `ho : IsOpen ((H.subgroupOf K : Subgroup K) : Set K)` using `(H.subgroupOf K).isOpen_of_mem_nhds (Filter.mem_of_superset (continuous_subtype_val.continuousAt (x := (1 : K)) hU) fun k hk => Subgroup.mem_subgroupOf.2 (hH k.1 k.2 hk))`. Establish `: Finite (K ⧸ H.subgroupOf K)` using `Subgroup.quotient_finite_of_isOpen _ ho`. Conclude with `Subgroup.index_ne_zero_of_finite`.
-/
theorem relIndex_ne_zero_of_nhds {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K H : Subgroup G}
    (hK : IsCompact (K : Set G)) {U : Set G} (hU : U ∈ 𝓝 (1 : G)) (hH : ∀ k ∈ K, k ∈ U → k ∈ H) : H.relIndex K ≠ 0 := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen ((H.subgroupOf K : Subgroup K) : Set K) :=
    (H.subgroupOf K).isOpen_of_mem_nhds (Filter.mem_of_superset (continuous_subtype_val.continuousAt (x := (1 : K)) hU)
      fun k hk => Subgroup.mem_subgroupOf.2 (hH k.1 k.2 hk))
  have : Finite (K ⧸ H.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.index_ne_zero_of_finite

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

section Form

variable {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl F}
  {ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (Fn F n d v)}

def stabK (L : IsLocRep M ψ om v ω ρ) (φ : Fn F n d v) (hφ : φ ∈ SB _) : Subgroup (UA σ W.J) where
  carrier := {k | k ∈ KAt σ W v ∧ ω (1, k) φ = φ}
  one_mem' := ⟨(KSub σ W v).one_mem, L.one φ hφ⟩
  mul_mem' := fun {a b} ha hb => ⟨(KSub σ W v).mul_mem ha.1 hb.1, by rw [L.mulW ha.1.1 hb.1.1 hφ, hb.2, ha.2]⟩
  inv_mem' := fun {a} ha => ⟨(KSub σ W v).inv_mem ha.1, by
    have e := L.mulW (inv_mem_UAt ha.1.1) ha.1.1 hφ
    rw [inv_mul_cancel, ha.2] at e
    rw [← e]
    exact L.one φ hφ⟩

/- English proof (translation)
Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)`. Use `haveI : IsTopologicalGroup (UA σ W.J) := inferInstance`. Establish `o1` using `one_mem_UAt (σ := σ) X v`. Establish `oW` using `one_mem_UAt (σ := σ) W v`. Establish `stabFin : ∀ φ (hφ : φ ∈ SB _), (stabK L φ hφ).relIndex (KSub σ W v) ≠ 0` using `fun φ hφ => by`.

Take `⟨U, hU, hU'⟩` from `L.smooth φ hφ`. Conclude with `relIndex_ne_zero_of_nhds hKc hU fun k hk hkU => ⟨hk, hU' k hkU hk.1⟩`. Take `⟨lam, hinv, hfor⟩` from `hAvg (UA σ W.J) (Fn F n d v) (KSub σ W v) (SB _) (fun g => ω (1, g)) l₀ (fun k hk φ hφ => L.pres 1 o1 k hk.1 φ hφ) (fun φ hφ => L.one φ hφ) (fun k hk k' hk' φ hφ => L.mulW hk.1 hk'.1 hφ) (fun φ hφ => ⟨stabK L φ hφ, fun k hk => hk.1, stabFin φ hφ, fun k hk => hk.2⟩)`. Establish `haug : ∀ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB _, lam (ω (g, 1) φ) = lam φ` using `fun g hg φ hφ => by`. Establish `hφ'` using `L.pres g hg 1 oW φ hφ`.

Establish `hHK : stabK L φ hφ ⊓ stabK L _ hφ' ≤ KSub σ W v` using `fun k hk => hk.1.1`. Establish `hHf` using `Subgroup.relIndex_inf_ne_zero (stabFin φ hφ) (stabFin _ hφ')`. Rewrite using `[hfor _ hφ' _ hHK hHf (fun k hk => hk.2.2), hfor _ hφ _ hHK hHf (fun k hk => hk.1.2)]`. Use `congr 1`. Use `finsum_congr fun q => ?_` and prove the remaining obligations.

Establish `hk : ((Quotient.out q : KSub σ W v) : UA σ W.J) ∈ UAt σ W (evFin F v)` using `(Quotient.out q).2.1`. Establish `e : ω (1, ((Quotient.out q : KSub σ W v) : UA σ W.J)) (ω (g, 1) φ) = ω (g, 1) (ω (1, ((Quotient.out q : KSub σ W v) : UA σ W.J)) φ)`. Rewrite using `[← L.mul 1 o1 _ hk g hg 1 oW φ hφ, ← L.mul g hg 1 oW 1 o1 _ hk φ hφ, one_mul, mul_one, mul_one, one_mul]`. Express the relevant statement in the definitionally equal form `l₀ (ω (1, _) (ω (g, 1) φ)) = l₀ (ω (1, _) φ)`. Rewrite using `[e, hX g hg _ (L.pres 1 o1 _ hk φ hφ)]`.

Establish `hsub : Subsingleton (KSub σ W v ⧸ (KSub σ W v).subgroupOf (KSub σ W v))` using `⟨fun x y => Quotient.inductionOn₂' x y fun a b => QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 (a⁻¹ * b).2)⟩`. Establish `hvac : lam (M.vac v) = l₀ (M.vac v)`. Set `q₀ : KSub σ W v ⧸ (KSub σ W v).subgroupOf (KSub σ W v)` to `QuotientGroup.mk 1`. Rewrite using `[hfor _ hs (KSub σ W v) le_rfl (by rw [Subgroup.relIndex_self]; exact one_ne_zero) hfix, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_mul, finsum_eq_single _ q₀ fun x hx => absurd (Subsingleton.elim x q₀) hx]`. Conclude with `congrArg l₀ (hfix _ (Quotient.out q₀).2)`.

Use `⟨(l₀ (M.vac v))⁻¹ • lam, ⟨Submodule.span_le.2 ?_, fun k hk φ hφ => ?_, ?_⟩, fun h hh => ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨g, hg, φ, hφ, φ₁, -, ha, rfl⟩`. Rewrite using `[(L.acts g hg 1 oW φ hφ φ₁).1 ha]`. Express the relevant statement in the definitionally equal form `(l₀ (M.vac v))⁻¹ • lam (ω (g, 1) φ - φ) = 0`. Rewrite using `[map_sub, haug g hg φ hφ, sub_self, smul_zero]`.

Express the relevant statement in the definitionally equal form `(l₀ (M.vac v))⁻¹ • lam (ω (1, k) φ) = (l₀ (M.vac v))⁻¹ • lam φ`. Rewrite using `[hinv k hk φ hφ]`. Express the relevant statement in the definitionally equal form `(l₀ (M.vac v))⁻¹ • lam (M.vac v) = 1`. Rewrite using `[hvac, smul_eq_mul, inv_mul_cancel₀ h0]`. Establish `hfixh : ∀ k ∈ conjInf (KSub σ W v) h, ω (1, k) (ω (1, h) (M.vac v)) = ω (1, h) (M.vac v)` using `fun k hk => by`.

Take `⟨k₁, hk₁, e⟩` from `Subgroup.mem_map.1 hk.2`. Establish `e' : k = h * k₁ * h⁻¹` using `by rw [← e]; rfl`. Rewrite using `[← L.mulW hk.1.1 hh hs, e', show h * k₁ * h⁻¹ * h = h * k₁ by group, L.mulW hh hk₁.1 hs, hfix k₁ hk₁]`. Express the relevant statement in the definitionally equal form `(l₀ (M.vac v))⁻¹ • lam (ω (1, h) (M.vac v)) = _`. Rewrite using `[hfor _ (L.pres 1 o1 h hh _ hs) _ inf_le_left (hfin h hh) hfixh, avgK, smul_eq_mul, mul_left_comm, mul_finsum]`.

Use `congr 1`. Use `finsum_congr fun q => ?_` and prove the remaining obligations. Establish `hk : ((Quotient.out q : KSub σ W v) : UA σ W.J) ∈ UAt σ W (evFin F v)` using `(Quotient.out q).2.1`. Express the relevant statement in the definitionally equal form `(l₀ (M.vac v))⁻¹ * l₀ (ω (1, _) (ω (1, h) (M.vac v))) = _`. Rewrite using `[← L.mulW hk hh hs, div_eq_inv_mul]`.

Both sides reduce to the same expression.
-/
theorem exists_form (hAvg : AvgSt) (L : IsLocRep M ψ om v ω ρ) (hKc : IsCompact (KAt σ W v))
    (hfix : ∀ k ∈ KAt σ W v, ω (1, k) (M.vac v) = M.vac v) (hs : M.vac v ∈ SB _)
    (l₀ : Fn F n d v →ₗ[ℂ] ℂ) (h0 : l₀ (M.vac v) ≠ 0)
    (hX : ∀ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB _, l₀ (ω (g, 1) φ) = l₀ φ)
    (hfin : ∀ h ∈ UAt σ W (evFin F v), (conjInf (KSub σ W v) h).relIndex (KSub σ W v) ≠ 0) :
    ∃ l, IsSphForm M om v ω l ∧ ∀ h ∈ UAt σ W (evFin F v),
      l (ω (1, h) (M.vac v)) = avgK (KSub σ W v) (fun g => l₀ (ω (1, g) (M.vac v)) / l₀ (M.vac v)) h := by
  classical
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  haveI : IsTopologicalGroup (UA σ W.J) := inferInstance
  have o1 := one_mem_UAt (σ := σ) X v
  have oW := one_mem_UAt (σ := σ) W v
  have stabFin : ∀ φ (hφ : φ ∈ SB _), (stabK L φ hφ).relIndex (KSub σ W v) ≠ 0 := fun φ hφ => by
    obtain ⟨U, hU, hU'⟩ := L.smooth φ hφ
    exact relIndex_ne_zero_of_nhds hKc hU fun k hk hkU => ⟨hk, hU' k hkU hk.1⟩
  obtain ⟨lam, hinv, hfor⟩ := hAvg (UA σ W.J) (Fn F n d v) (KSub σ W v) (SB _) (fun g => ω (1, g)) l₀
    (fun k hk φ hφ => L.pres 1 o1 k hk.1 φ hφ) (fun φ hφ => L.one φ hφ) (fun k hk k' hk' φ hφ => L.mulW hk.1 hk'.1 hφ)
    (fun φ hφ => ⟨stabK L φ hφ, fun k hk => hk.1, stabFin φ hφ, fun k hk => hk.2⟩)
  have haug : ∀ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB _, lam (ω (g, 1) φ) = lam φ := fun g hg φ hφ => by
    have hφ' := L.pres g hg 1 oW φ hφ
    have hHK : stabK L φ hφ ⊓ stabK L _ hφ' ≤ KSub σ W v := fun k hk => hk.1.1
    have hHf := Subgroup.relIndex_inf_ne_zero (stabFin φ hφ) (stabFin _ hφ')
    rw [hfor _ hφ' _ hHK hHf (fun k hk => hk.2.2), hfor _ hφ _ hHK hHf (fun k hk => hk.1.2)]
    congr 1
    refine finsum_congr fun q => ?_
    have hk : ((Quotient.out q : KSub σ W v) : UA σ W.J) ∈ UAt σ W (evFin F v) := (Quotient.out q).2.1
    have e : ω (1, ((Quotient.out q : KSub σ W v) : UA σ W.J)) (ω (g, 1) φ) =
        ω (g, 1) (ω (1, ((Quotient.out q : KSub σ W v) : UA σ W.J)) φ) := by
      rw [← L.mul 1 o1 _ hk g hg 1 oW φ hφ, ← L.mul g hg 1 oW 1 o1 _ hk φ hφ, one_mul, mul_one, mul_one, one_mul]
    change l₀ (ω (1, _) (ω (g, 1) φ)) = l₀ (ω (1, _) φ)
    rw [e, hX g hg _ (L.pres 1 o1 _ hk φ hφ)]
  have hsub : Subsingleton (KSub σ W v ⧸ (KSub σ W v).subgroupOf (KSub σ W v)) :=
    ⟨fun x y => Quotient.inductionOn₂' x y fun a b => QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 (a⁻¹ * b).2)⟩
  have hvac : lam (M.vac v) = l₀ (M.vac v) := by
    let q₀ : KSub σ W v ⧸ (KSub σ W v).subgroupOf (KSub σ W v) := QuotientGroup.mk 1
    rw [hfor _ hs (KSub σ W v) le_rfl (by rw [Subgroup.relIndex_self]; exact one_ne_zero) hfix, Subgroup.relIndex_self,
      Nat.cast_one, inv_one, one_mul, finsum_eq_single _ q₀ fun x hx => absurd (Subsingleton.elim x q₀) hx]
    exact congrArg l₀ (hfix _ (Quotient.out q₀).2)
  refine ⟨(l₀ (M.vac v))⁻¹ • lam, ⟨Submodule.span_le.2 ?_, fun k hk φ hφ => ?_, ?_⟩, fun h hh => ?_⟩
  · rintro _ ⟨g, hg, φ, hφ, φ₁, -, ha, rfl⟩
    rw [(L.acts g hg 1 oW φ hφ φ₁).1 ha]
    change (l₀ (M.vac v))⁻¹ • lam (ω (g, 1) φ - φ) = 0
    rw [map_sub, haug g hg φ hφ, sub_self, smul_zero]
  · change (l₀ (M.vac v))⁻¹ • lam (ω (1, k) φ) = (l₀ (M.vac v))⁻¹ • lam φ
    rw [hinv k hk φ hφ]
  · change (l₀ (M.vac v))⁻¹ • lam (M.vac v) = 1
    rw [hvac, smul_eq_mul, inv_mul_cancel₀ h0]
  · have hfixh : ∀ k ∈ conjInf (KSub σ W v) h, ω (1, k) (ω (1, h) (M.vac v)) = ω (1, h) (M.vac v) := fun k hk => by
      obtain ⟨k₁, hk₁, e⟩ := Subgroup.mem_map.1 hk.2
      have e' : k = h * k₁ * h⁻¹ := by rw [← e]; rfl
      rw [← L.mulW hk.1.1 hh hs, e', show h * k₁ * h⁻¹ * h = h * k₁ by group, L.mulW hh hk₁.1 hs, hfix k₁ hk₁]
    change (l₀ (M.vac v))⁻¹ • lam (ω (1, h) (M.vac v)) = _
    rw [hfor _ (L.pres 1 o1 h hh _ hs) _ inf_le_left (hfin h hh) hfixh, avgK, smul_eq_mul, mul_left_comm, mul_finsum]
    congr 1
    refine finsum_congr fun q => ?_
    have hk : ((Quotient.out q : KSub σ W v) : UA σ W.J) ∈ UAt σ W (evFin F v) := (Quotient.out q).2.1
    change (l₀ (M.vac v))⁻¹ * l₀ (ω (1, _) (ω (1, h) (M.vac v))) = _
    rw [← L.mulW hk hh hs, div_eq_inv_mul]
    rfl

/- English proof (translation)
Rewrite using `[L.mulW (mul_mem_UAt hp hg) hk.1 hs, hfix k hk, L.mulW hp hg hs, hc _ (L.pres 1 (one_mem_UAt X v) g hg _ hs), mul_div_assoc]`.
-/
theorem fn_mul (L : IsLocRep M ψ om v ω ρ) (hfix : ∀ k ∈ KAt σ W v, ω (1, k) (M.vac v) = M.vac v) (hs : M.vac v ∈ SB _)
    {l₀ : Fn F n d v →ₗ[ℂ] ℂ} {p : UA σ W.J} (hp : p ∈ UAt σ W (evFin F v)) {c : ℂ}
    (hc : ∀ φ ∈ SB _, l₀ (ω (1, p) φ) = c * l₀ φ) {g k : UA σ W.J} (hg : g ∈ UAt σ W (evFin F v)) (hk : k ∈ KAt σ W v) :
    l₀ (ω (1, p * g * k) (M.vac v)) / l₀ (M.vac v) = c * (l₀ (ω (1, g) (M.vac v)) / l₀ (M.vac v)) := by
  rw [L.mulW (mul_mem_UAt hp hg) hk.1 hs, hfix k hk, L.mulW hp hg hs, hc _ (L.pres 1 (one_mem_UAt X v) g hg _ hs),
    mul_div_assoc]

omit [NumberField E] in
/- English proof (translation)
Rewrite using `[hc _ hs, mul_div_assoc, div_self h0, mul_one]`.
-/
theorem fn_val {l₀ : Fn F n d v →ₗ[ℂ] ℂ} (hs : M.vac v ∈ SB _) (h0 : l₀ (M.vac v) ≠ 0) {p : UA σ W.J} {c : ℂ}
    (hc : ∀ φ ∈ SB _, l₀ (ω (1, p) φ) = c * l₀ φ) : l₀ (ω (1, p) (M.vac v)) / l₀ (M.vac v) = c := by
  rw [hc _ hs, mul_div_assoc, div_self h0, mul_one]

end Form

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' hT v he ω ρ ω' ρ' L L' hK hK'`. Use `haveI : LocallyCompactSpace (Fv F v) := (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).locallyCompactSpace_of_mem_nhds_of_addGroup ((Valued.isOpen_valuationSubring _).mem_nhds (zero_mem (v.adicCompletionIntegers F)))`. Take `⟨w, hw⟩` from `inert_of_local F E σ B hT.base v he`. Establish `hv : v ∉ X.T` using `fun h => he.false (B.τ ⟨v, hT.chars.sub h⟩)`. Establish `P : PairOK B G.V G.W G.M om` using `⟨hT.base, ⟨_, _, hT.geo.hV⟩, ⟨_, _, hT.geo.hW⟩, hT.geo.hM, _, _, hT.weil⟩`.

Establish `P' : PairOK B G.V' G.W G.M' om'` using `⟨hT.base, ⟨_, _, hT.geo.hV'⟩, ⟨_, _, hT.geo.hW⟩, hT.geo.hM', _, _, hT.weil'⟩`. Take `⟨m, Cy, hL, hAd, hIw, -⟩` from `PositivityTheory.ThKH.Iwas.iwasawa F E σ _ _ B _ _ _ _ P v hT.geo.even ⟨w, hw⟩`. Take `⟨l₀, hl, hl0⟩` from `PositivityTheory.ThKH.Evl.evVac F E σ _ _ B _ _ _ _ P v ⟨w, hw⟩ m Cy hL hAd`. Take `⟨l₀', hl', hl0'⟩` from `PositivityTheory.ThKH.Evl.evVac F E σ _ _ B _ _ _ _ P' v ⟨w, hw⟩ m Cy hL hAd`. Take `⟨hs, -, -⟩` from `hT.geo.hM.vac v`.

Take `⟨hs', -, -⟩` from `hT.geo.hM'.vac v`. Establish `hKc : IsCompact (KAt σ G.W v)` using `stabiliser_compact F E σ _ _ B _ _ _ _ P v`. Establish `hch` using `hChar F E σ B a a' G X om om' hT v w hw hv`. Establish `hfin` using `hFin F E σ _ B G.W _ _ hT.base hT.geo.hW v w hw`. Establish `hX` using `hEv F E σ _ _ B _ _ _ _ _ _ P hT.weil v w hw (fun z hz => by rw [MonoidHom.div_apply, (hch z hz).2, div_self']) ω ρ L m Cy hL hAd l₀ hl ⟨_, hs, hl0⟩`.

Establish `hX'` using `hEv F E σ _ _ B _ _ _ _ _ _ P' hT.weil' v w hw (fun z hz => by rw [MonoidHom.div_apply, (hch z hz).2, div_self']) ω' ρ' L' m Cy hL hAd l₀' hl' ⟨_, hs', hl0'⟩`. Take `⟨l, hlS, hlf⟩` from `exists_form hAvg L hKc hK hs l₀ hl0 hX hfin`. Take `⟨l', hlS', hlf'⟩` from `exists_form hAvg L' hKc hK' hs' l₀' hl0' hX' hfin`. Use `⟨l, l', hlS, hlS', fun h hh => ?_⟩` and prove the remaining obligations. Rewrite using `[hlf h hh, hlf' h hh]`.

Establish `o1` using `one_mem_UAt (σ := σ) G.V v`. Establish `o1'` using `one_mem_UAt (σ := σ) G.V' v`. Establish `hval : ∀ p ∈ PSub σ G.W v Cy, ∃ (z : (AE F E)ˣ) (u : (Fv F v)ˣ), (∀ φ ∈ SB _, l₀ (ω (1, p) φ) = (X.β z : ℂ) * ((((sbClass (Fv F v)).modu u : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ) * l₀ φ) ∧ (∀ φ ∈ SB _, l₀' (ω' (1, p) φ) = (X.α z : ℂ) * ((((sbClass (Fv F v)).modu u : ℝ) ^ ((a' : ℝ) / 2) : …` using `fun p hp => by`. Establish `hp0` using `hp`. Take `⟨⟨hpU, t, ht⟩, -⟩` from `hp0`.

Take `⟨-, hu⟩` from `hPInv F E σ _ G.W v w hw m Cy hL p hp.1`. Take `⟨z, hz, hzc⟩` from `hLift F E v (hu t ht).unit`. Use `⟨z, Units.map (Algebra.norm (Fv F v) : Ev E v →* Fv F v) (hu t ht).unit, hSieg F E σ _ _ B G.V G.W G.M om _ _ P hT.weil v w hw ω ρ L m Cy hL hAd l₀ hl p hpU t ht z hz hzc _ ?_, hSieg F E σ _ _ B G.V' G.W G.M' om' _ _ P' hT.weil' v w hw ω' ρ' L' m Cy hL hAd l₀' hl' p hpU t ht z hz …` and prove the remaining obligations. Apply the tactic sequence `all_goals simp [hzc]`. Use `hCount (UA σ G.W.J) (PositivityTheory.ThKH.Iwas.USub σ G.W v) (KSub σ G.W v) (PSub σ G.W v Cy) _ _ (fun k hk => hk.1) (fun p hp => hp.1.1) (fun g hg => ?_) (fun g hg => hCart F E σ _ B G.W _ _ hT.base hT.geo.hW hT.geo.even v w hw g hg) (fun g hg => hfin g hg) ?_ ?_ (fun p hp g hg …` and prove the remaining obligations.

Take `⟨p, hp, k, hk, e⟩` from `hIw g hg`. Conclude with `⟨p, ⟨hp, (hPInv F E σ _ G.W v w hw m Cy hL p hp).1⟩, k, hk, e⟩`. Use `show l₀ (ω 1 (G.M.vac v)) / _ = 1`. Rewrite using `[L.one _ hs, div_self hl0]`. Use `show l₀' (ω' 1 (G.M'.vac v)) / _ = 1`.

Rewrite using `[L'.one _ hs', div_self hl0']`. Take `⟨z, u, h1, -, -, -⟩` from `hval p hp`. Rewrite using `[fn_mul L hK hs hp.1.1 h1 hg hk, fn_val hs hl0 h1]`. Take `⟨z, u, -, h2, -, -⟩` from `hval p hp`. Rewrite using `[fn_mul L' hK' hs' hp.1.1 h2 hg hk, fn_val hs' hl0' h2]`.

Take `⟨z, u, h1, h2, h3, h4⟩` from `hval p hp`. Rewrite using `[fn_val hs hl0 h1, fn_val hs' hl0' h2]`. Establish `h3' : (X.α z : ℂ) * (X.β z : ℂ) = 1` using `by rw [← Circle.coe_mul, h3, Circle.coe_one]`. Establish `hR0 : 0 ≤ ((sbClass (Fv F v)).modu u : ℝ)` using `NNReal.coe_nonneg _`. Establish `hm : (a : ℝ) / 2 + (a' : ℝ) / 2 = (m : ℝ)`.

Establish `: ((a : ℝ) + a') = 2 * m` using `by exact_mod_cast hL.rank`. Combine the linear equalities and inequalities to obtain the conclusion. Generalize the expression as in `((sbClass (Fv F v)).modu u : ℝ) = R at hR0 h4 ⊢`. Generalize the expression as in `(((PSub σ G.W v Cy ⊓ KSub σ G.W v).map (MulAut.conj p).toMonoidHom).relIndex (PSub σ G.W v Cy ⊓ KSub σ G.W v)) = n₁ at h4 ⊢`. Generalize the expression as in `(((PSub σ G.W v Cy ⊓ KSub σ G.W v).map (MulAut.conj p⁻¹).toMonoidHom).relIndex (PSub σ G.W v Cy ⊓ KSub σ G.W v)) = n₂ at h4 ⊢`.

Establish `e : R ^ ((a : ℝ) / 2) * R ^ ((a' : ℝ) / 2) = R ^ m`. Rewrite using `[← Real.rpow_add_of_nonneg hR0 (by positivity) (by positivity), hm, Real.rpow_natCast]`. Establish `h4' : ((n₂ : ℕ) : ℂ) = ((R ^ ((a : ℝ) / 2) : ℝ) : ℂ) * ((R ^ ((a' : ℝ) / 2) : ℝ) : ℂ) * ((n₁ : ℕ) : ℂ)`. Rewrite using `[← Complex.ofReal_mul, e]`. Conclude with `h4` after adjusting the coercions.

Rewrite using `[h4']`. Take the linear combination `(((R ^ ((a : ℝ) / 2) : ℝ) : ℂ) * ((R ^ ((a' : ℝ) / 2) : ℝ) : ℂ) * ((n₁ : ℕ) : ℂ)) * h3'`.
-/
theorem sphFun_of (hCount : CountSt) (hAvg : AvgSt) (hPInv : PInvSt) (hLift : UnitLiftSt) (hChar : CharSt) (hEv : EvInvSt)
    (hSieg : SiegSt) (hMod : ModSt) (hCart : CartanSt) (hFin : FinSt) : SphFun := by
  classical
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v he ω ρ ω' ρ' L L' hK hK'
  haveI : LocallyCompactSpace (Fv F v) :=
    (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).locallyCompactSpace_of_mem_nhds_of_addGroup
      ((Valued.isOpen_valuationSubring _).mem_nhds (zero_mem (v.adicCompletionIntegers F)))
  obtain ⟨w, hw⟩ := inert_of_local F E σ B hT.base v he
  have hv : v ∉ X.T := fun h => he.false (B.τ ⟨v, hT.chars.sub h⟩)
  have P : PairOK B G.V G.W G.M om := ⟨hT.base, ⟨_, _, hT.geo.hV⟩, ⟨_, _, hT.geo.hW⟩, hT.geo.hM, _, _, hT.weil⟩
  have P' : PairOK B G.V' G.W G.M' om' := ⟨hT.base, ⟨_, _, hT.geo.hV'⟩, ⟨_, _, hT.geo.hW⟩, hT.geo.hM', _, _, hT.weil'⟩
  obtain ⟨m, Cy, hL, hAd, hIw, -⟩ := PositivityTheory.ThKH.Iwas.iwasawa F E σ _ _ B _ _ _ _ P v hT.geo.even ⟨w, hw⟩
  obtain ⟨l₀, hl, hl0⟩ := PositivityTheory.ThKH.Evl.evVac F E σ _ _ B _ _ _ _ P v ⟨w, hw⟩ m Cy hL hAd
  obtain ⟨l₀', hl', hl0'⟩ := PositivityTheory.ThKH.Evl.evVac F E σ _ _ B _ _ _ _ P' v ⟨w, hw⟩ m Cy hL hAd
  obtain ⟨hs, -, -⟩ := hT.geo.hM.vac v
  obtain ⟨hs', -, -⟩ := hT.geo.hM'.vac v
  have hKc : IsCompact (KAt σ G.W v) := stabiliser_compact F E σ _ _ B _ _ _ _ P v
  have hch := hChar F E σ B a a' G X om om' hT v w hw hv
  have hfin := hFin F E σ _ B G.W _ _ hT.base hT.geo.hW v w hw
  have hX := hEv F E σ _ _ B _ _ _ _ _ _ P hT.weil v w hw (fun z hz => by rw [MonoidHom.div_apply, (hch z hz).2, div_self'])
    ω ρ L m Cy hL hAd l₀ hl ⟨_, hs, hl0⟩
  have hX' := hEv F E σ _ _ B _ _ _ _ _ _ P' hT.weil' v w hw (fun z hz => by rw [MonoidHom.div_apply, (hch z hz).2, div_self'])
    ω' ρ' L' m Cy hL hAd l₀' hl' ⟨_, hs', hl0'⟩
  obtain ⟨l, hlS, hlf⟩ := exists_form hAvg L hKc hK hs l₀ hl0 hX hfin
  obtain ⟨l', hlS', hlf'⟩ := exists_form hAvg L' hKc hK' hs' l₀' hl0' hX' hfin
  refine ⟨l, l', hlS, hlS', fun h hh => ?_⟩
  rw [hlf h hh, hlf' h hh]
  have o1 := one_mem_UAt (σ := σ) G.V v
  have o1' := one_mem_UAt (σ := σ) G.V' v

  have hval : ∀ p ∈ PSub σ G.W v Cy, ∃ (z : (AE F E)ˣ) (u : (Fv F v)ˣ),
      (∀ φ ∈ SB _, l₀ (ω (1, p) φ) = (X.β z : ℂ) * ((((sbClass (Fv F v)).modu u : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ) * l₀ φ) ∧
      (∀ φ ∈ SB _, l₀' (ω' (1, p) φ) = (X.α z : ℂ) * ((((sbClass (Fv F v)).modu u : ℝ) ^ ((a' : ℝ) / 2) : ℝ) : ℂ) * l₀' φ) ∧
      X.α z * X.β z = 1 ∧
      ((((PSub σ G.W v Cy ⊓ KSub σ G.W v).map (MulAut.conj p⁻¹).toMonoidHom).relIndex (PSub σ G.W v Cy ⊓ KSub σ G.W v) : ℕ) : ℝ) =
        ((sbClass (Fv F v)).modu u : ℝ) ^ m *
          ((((PSub σ G.W v Cy ⊓ KSub σ G.W v).map (MulAut.conj p).toMonoidHom).relIndex (PSub σ G.W v Cy ⊓ KSub σ G.W v) : ℕ) : ℝ) :=
    fun p hp => by
      have hp0 := hp
      obtain ⟨⟨hpU, t, ht⟩, -⟩ := hp0
      obtain ⟨-, hu⟩ := hPInv F E σ _ G.W v w hw m Cy hL p hp.1
      obtain ⟨z, hz, hzc⟩ := hLift F E v (hu t ht).unit
      refine ⟨z, Units.map (Algebra.norm (Fv F v) : Ev E v →* Fv F v) (hu t ht).unit,
        hSieg F E σ _ _ B G.V G.W G.M om _ _ P hT.weil v w hw ω ρ L m Cy hL hAd l₀ hl p hpU t ht z hz hzc _ ?_,
        hSieg F E σ _ _ B G.V' G.W G.M' om' _ _ P' hT.weil' v w hw ω' ρ' L' m Cy hL hAd l₀' hl' p hpU t ht z hz hzc _ ?_,
        (hch z hz).1, hMod F E σ _ B G.W _ _ hT.base hT.geo.hW v w hw m Cy hL hAd p hp t ht _ ?_⟩
      all_goals simp [hzc]
  refine hCount (UA σ G.W.J) (PositivityTheory.ThKH.Iwas.USub σ G.W v) (KSub σ G.W v) (PSub σ G.W v Cy) _ _ (fun k hk => hk.1)
    (fun p hp => hp.1.1) (fun g hg => ?_) (fun g hg => hCart F E σ _ B G.W _ _ hT.base hT.geo.hW hT.geo.even v w hw g hg)
    (fun g hg => hfin g hg) ?_ ?_ (fun p hp g hg k hk => ?_) (fun p hp g hg k hk => ?_) (fun p hp => ?_) h hh
  · obtain ⟨p, hp, k, hk, e⟩ := hIw g hg
    exact ⟨p, ⟨hp, (hPInv F E σ _ G.W v w hw m Cy hL p hp).1⟩, k, hk, e⟩
  · show l₀ (ω 1 (G.M.vac v)) / _ = 1
    rw [L.one _ hs, div_self hl0]
  · show l₀' (ω' 1 (G.M'.vac v)) / _ = 1
    rw [L'.one _ hs', div_self hl0']
  · obtain ⟨z, u, h1, -, -, -⟩ := hval p hp
    rw [fn_mul L hK hs hp.1.1 h1 hg hk, fn_val hs hl0 h1]
  · obtain ⟨z, u, -, h2, -, -⟩ := hval p hp
    rw [fn_mul L' hK' hs' hp.1.1 h2 hg hk, fn_val hs' hl0' h2]
  · obtain ⟨z, u, h1, h2, h3, h4⟩ := hval p hp
    rw [fn_val hs hl0 h1, fn_val hs' hl0' h2]
    have h3' : (X.α z : ℂ) * (X.β z : ℂ) = 1 := by rw [← Circle.coe_mul, h3, Circle.coe_one]
    have hR0 : 0 ≤ ((sbClass (Fv F v)).modu u : ℝ) := NNReal.coe_nonneg _
    have hm : (a : ℝ) / 2 + (a' : ℝ) / 2 = (m : ℝ) := by
      have : ((a : ℝ) + a') = 2 * m := by exact_mod_cast hL.rank
      linarith
    generalize ((sbClass (Fv F v)).modu u : ℝ) = R at hR0 h4 ⊢
    generalize (((PSub σ G.W v Cy ⊓ KSub σ G.W v).map (MulAut.conj p).toMonoidHom).relIndex
      (PSub σ G.W v Cy ⊓ KSub σ G.W v)) = n₁ at h4 ⊢
    generalize (((PSub σ G.W v Cy ⊓ KSub σ G.W v).map (MulAut.conj p⁻¹).toMonoidHom).relIndex
      (PSub σ G.W v Cy ⊓ KSub σ G.W v)) = n₂ at h4 ⊢
    have e : R ^ ((a : ℝ) / 2) * R ^ ((a' : ℝ) / 2) = R ^ m := by
      rw [← Real.rpow_add_of_nonneg hR0 (by positivity) (by positivity), hm, Real.rpow_natCast]
    have h4' : ((n₂ : ℕ) : ℂ) = ((R ^ ((a : ℝ) / 2) : ℝ) : ℂ) * ((R ^ ((a' : ℝ) / 2) : ℝ) : ℂ) * ((n₁ : ℕ) : ℂ) := by
      rw [← Complex.ofReal_mul, e]
      exact_mod_cast h4
    rw [h4']
    linear_combination (((R ^ ((a : ℝ) / 2) : ℝ) : ℂ) * ((R ^ ((a' : ℝ) / 2) : ℝ) : ℂ) * ((n₁ : ℕ) : ℂ)) * h3'

end PositivityTheory.Sph

end

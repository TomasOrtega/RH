import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.OrthZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TwtrContOfMem

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB
open GlobalTheory.CuspRep.LocEx GlobalTheory.Published
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH borelG borelF borelA

section SlopeTestRemainingChoices

private def rtRep {X Γ : Type} [Group X] [Group Γ] (τ : Γ →* X) (F : Submodule ℂ (X → ℂ))
    (h : ∀ γ, ∀ a ∈ F, (fun x => a (x * τ γ)) ∈ F) : Representation ℂ Γ F where
  toFun γ :=
    { toFun := fun a => ⟨fun x => a.1 (x * τ γ), h γ a.1 a.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext a x
    simp
  map_mul' γ δ := by
    ext a x
    simp [mul_assoc]

/- English proof (translation)
The claim follows from `FiniteDimensional.of_injective ((F.subtype.comp S.subtype).codRestrict U fun x => h _ x.2) fun x y e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))`.
-/
private lemma fd_sub {M : Type} [AddCommGroup M] [Module ℂ M] (F : Submodule ℂ M) (S : Submodule ℂ F)
    (U : Submodule ℂ M) [FiniteDimensional ℂ U] (h : ∀ x ∈ S, x.1 ∈ U) : FiniteDimensional ℂ S :=
  FiniteDimensional.of_injective ((F.subtype.comp S.subtype).codRestrict U fun x => h _ x.2)
    fun x y e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))

/- English proof (translation)
Establish `hle : Submodule.span ℂ (Set.range g) ≤ U.comap F.subtype` using `Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact h i)`. Conclude with `fd_sub F _ U fun x hx => hle hx`.
-/
private lemma fd_span {M ι : Type} [AddCommGroup M] [Module ℂ M] (F : Submodule ℂ M) (g : ι → F)
    (U : Submodule ℂ M) [FiniteDimensional ℂ U] (h : ∀ i, (g i).1 ∈ U) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range g)) := by
  have hle : Submodule.span ℂ (Set.range g) ≤ U.comap F.subtype :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact h i)
  exact fd_sub F _ U fun x hx => hle hx

/- English proof (translation)
Take `⟨s, -, hs⟩` from `hK.elim_nhds_subcover (fun k => {g | k⁻¹ * g ∈ L}) fun k _ => by`. Use `(hL.preimage (continuous_const.mul continuous_id)).mem_nhds ?_` and prove the remaining obligations. Simplify using `[L.one_mem]`. Use `⟨s, fun k hk => ?_⟩` and prove the remaining obligations. Take `⟨t, ht, h⟩` from `Set.mem_iUnion₂.1 (hs hk)`.

Conclude with `⟨t, ht, h⟩`.
-/
private lemma fin_cosets {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] (K L : Subgroup G)
    (hK : IsCompact (K : Set G)) (hL : IsOpen (L : Set G)) :
    ∃ s : Finset G, ∀ k ∈ K, ∃ t ∈ s, t⁻¹ * k ∈ L := by
  obtain ⟨s, -, hs⟩ := hK.elim_nhds_subcover (fun k => {g | k⁻¹ * g ∈ L}) fun k _ => by
    refine (hL.preimage (continuous_const.mul continuous_id)).mem_nhds ?_
    simp [L.one_mem]
  refine ⟨s, fun k hk => ?_⟩
  obtain ⟨t, ht, h⟩ := Set.mem_iUnion₂.1 (hs hk)
  exact ⟨t, ht, h⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
The claim follows from `(infGL_comm _ k).symm`.
-/
private lemma fin_kI_comm (k : GL (Fin n) (Af E)) (κ : Kinf E n) :
    finGL E n k * kI E n κ = kI E n κ * finGL E n k :=
  (infGL_comm _ k).symm

private def tau (K : Subgroup (GL (Fin n) (Af E))) : (K × Kinf E n) →* GA E n :=
  MonoidHom.noncommCoprod ((finGL E n).comp K.subtype) (kI E n) fun k κ => fin_kI_comm k.1 κ

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma tau_apply (K : Subgroup (GL (Fin n) (Af E))) (γ : K × Kinf E n) :
    tau K γ = finGL E n γ.1.1 * kI E n γ.2 := rfl

/- English proof (translation)
Use `⟨cptRep E n κ (π.finPart k ⟨ψ, hψ⟩).1, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `π.stable (Op.cpt κ) _ (π.finPart k ⟨ψ, hψ⟩).2`. Rewrite `h` using `[GlobalTheory.CuspRep.act]`. Then use the resulting hypothesis. Use function extensionality and compare the values at `x`. Express the relevant statement in the definitionally equal form `ψ.1 (x * kI E n κ * finGL E n k) = _`.

Rewrite using `[mul_assoc, fin_kI_comm]`.
-/
private lemma trans_mem (π : CuspSub E n) (ψ : Sm E n) (hψ : ψ ∈ π.V) (k : GL (Fin n) (Af E)) (κ : Kinf E n) :
    ∃ ψ' ∈ π.V, ψ'.1 = fun x => ψ.1 (x * (finGL E n k * kI E n κ)) := by
  refine ⟨cptRep E n κ (π.finPart k ⟨ψ, hψ⟩).1, ?_, ?_⟩
  · have h := π.stable (Op.cpt κ) _ (π.finPart k ⟨ψ, hψ⟩).2
    rwa [GlobalTheory.CuspRep.act] at h
  · funext x
    change ψ.1 (x * kI E n κ * finGL E n k) = _
    rw [mul_assoc, fin_kI_comm]

/- English proof (translation)
Take `⟨s, hs⟩` from `fin_cosets K (stab π.finPart ⟨ψ, hψ⟩) hK (π.isSmooth_finPart _)`. Set `S : GL (Fin n) (Af E) → Submodule ℂ (Sm E n)` to `fun t => orbSpan (π.finPart t ⟨ψ, hψ⟩).1`. Use `haveI : ∀ t, FiniteDimensional ℂ (S t) := fun t => (π.cusp _ (π.finPart t ⟨ψ, hψ⟩).2).1.kfin`. Use `haveI : FiniteDimensional ℂ ↥(s.sup S : Submodule ℂ (Sm E n)) := Submodule.finiteDimensional_finset_sup s S`. Use `⟨(s.sup S).map (Sm E n).subtype, Module.Finite.map _ _, fun k hk κ => ?_⟩` and prove the remaining obligations.

Take `⟨t, ht, hl⟩` from `hs k hk`. Establish `e : π.finPart k ⟨ψ, hψ⟩ = π.finPart t ⟨ψ, hψ⟩`. Establish `h1 : π.finPart (t⁻¹ * k) ⟨ψ, hψ⟩ = ⟨ψ, hψ⟩` using `hl`. Establish `h2 : k = t * (t⁻¹ * k)` using `by group`. Rewrite using `[h2, map_mul, Module.End.mul_apply, h1]`.

Use `⟨cptRep E n κ (π.finPart t ⟨ψ, hψ⟩).1, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Finset.le_sup (f := S) ht) (Submodule.subset_span ⟨κ, rfl⟩)`. Rewrite using `[← e]`. Use function extensionality and compare the values at `x`. Express the relevant statement in the definitionally equal form `ψ.1 (x * kI E n κ * finGL E n k) = _`.

Rewrite using `[mul_assoc, fin_kI_comm]`.
-/
private lemma orbit_fin (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E)))
    (hK : IsCompact (K : Set (GL (Fin n) (Af E)))) (ψ : Sm E n) (hψ : ψ ∈ π.V) :
    ∃ U : Submodule ℂ (GA E n → ℂ), FiniteDimensional ℂ U ∧ ∀ k ∈ K, ∀ κ : Kinf E n,
      (fun x => ψ.1 (x * (finGL E n k * kI E n κ))) ∈ U := by
  obtain ⟨s, hs⟩ := fin_cosets K (stab π.finPart ⟨ψ, hψ⟩) hK (π.isSmooth_finPart _)
  let S : GL (Fin n) (Af E) → Submodule ℂ (Sm E n) := fun t => orbSpan (π.finPart t ⟨ψ, hψ⟩).1
  haveI : ∀ t, FiniteDimensional ℂ (S t) := fun t => (π.cusp _ (π.finPart t ⟨ψ, hψ⟩).2).1.kfin
  haveI : FiniteDimensional ℂ ↥(s.sup S : Submodule ℂ (Sm E n)) := Submodule.finiteDimensional_finset_sup s S
  refine ⟨(s.sup S).map (Sm E n).subtype, Module.Finite.map _ _, fun k hk κ => ?_⟩
  obtain ⟨t, ht, hl⟩ := hs k hk
  have e : π.finPart k ⟨ψ, hψ⟩ = π.finPart t ⟨ψ, hψ⟩ := by
    have h1 : π.finPart (t⁻¹ * k) ⟨ψ, hψ⟩ = ⟨ψ, hψ⟩ := hl
    have h2 : k = t * (t⁻¹ * k) := by group
    rw [h2, map_mul, Module.End.mul_apply, h1]
  refine ⟨cptRep E n κ (π.finPart t ⟨ψ, hψ⟩).1, ?_, ?_⟩
  · exact (Finset.le_sup (f := S) ht) (Submodule.subset_span ⟨κ, rfl⟩)
  · rw [← e]
    funext x
    change ψ.1 (x * kI E n κ * finGL E n k) = _
    rw [mul_assoc, fin_kI_comm]

/- English proof (translation)
Introduce `u hu hc`. Take `⟨v, hv, ev⟩` from `ha u hu hc`. Take `⟨w, hw, ew⟩` from `hb u hu hc`. Use `⟨v - w, Submodule.sub_mem _ hv hw, ?_⟩` and prove the remaining obligations. Establish `e : (v - w) () = v () - w ()` using `rfl`.

Rewrite using `[e]`. Use `filter_upwards [Lp.coeFn_sub (v ()) (w ()), ev, ew] with x h1 h2 h3`. Simplify using `only [h1, Pi.sub_apply, h2, h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma inS_sub (D : Dom E n 0) (π : CuspSub E n) {a b : GA E n → ℂ} (ha : InS D π a) (hb : InS D π b) :
    InS D π (a - b) := by
  intro u hu hc
  obtain ⟨v, hv, ev⟩ := ha u hu hc
  obtain ⟨w, hw, ew⟩ := hb u hu hc
  refine ⟨v - w, Submodule.sub_mem _ hv hw, ?_⟩
  have e : (v - w) () = v () - w () := rfl
  rw [e]
  filter_upwards [Lp.coeFn_sub (v ()) (w ()), ev, ew] with x h1 h2 h3
  simp only [h1, Pi.sub_apply, h2, h3]
  ring

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `hAdm hDet hEv hCv hForm hOrth hAbs E _ _ _ n hn D π hfix K W hKo hKc hW hWR f hS hI hT`. Take `⟨Fm, B, hF, hBs, hBp, hBw, hBi⟩` from `hForm E n hn D`. Take `⟨Y0, -, hYfd, hY⟩` from `hAdm E n hn π hfix K W hKo hW`. Use `haveI := hYfd`. Use `haveI := hW`.

Establish `hdet : ∀ γ, logAbs (tau K γ).val.det = 0` using `fun γ => by`. Rewrite using `[tau_apply, DiscreteGroups.T1.G.Dcy.logAbs_det_mul', (hDet E n).2 K hKc _ γ.1.2, (hDet E n).1 γ.2, add_zero]`. Establish `hst : ∀ γ, ∀ a ∈ Fm, (fun x => a (x * tau K γ)) ∈ Fm` using `fun γ a ha => (hBi _ (hdet γ) ⟨a, ha⟩).1`. Set `R` to `rtRep (tau K) Fm hst`. Establish `hR : ∀ γ (a : Fm) x, (R γ a).1 x = a.1 (x * tau K γ)` using `fun _ _ _ => rfl`.

Set `W' : Submodule ℂ ((K × Kinf E n) → ℂ)` to `W.map (LinearMap.funLeft ℂ ℂ Prod.snd)`. Set `V : Submodule ℂ Fm` to `(π.V.map (Sm E n).subtype).comap Fm.subtype`. Set `Y : Submodule ℂ Fm` to `(Y0.map (Sm E n).subtype).comap Fm.subtype`. Establish `hSl : ∀ ψ ∈ π.V, Slab D ψ.1` using `fun ψ h => (hCv E n hn D π hfix ψ h).1`. Establish `hVm : ∀ ψ ∈ π.V, ∀ a : Fm, ψ.1 = a.1 → a ∈ V` using `fun ψ h a e => ⟨ψ, h, e⟩`.

Take `⟨d, p, w, hw, hs⟩` from `hEv (Kinf E n) (Kinf E n → ℂ) (fun x => LinearMap.proj x) (fun v hv => funext hv) W hW`. Set `z : Fm` to `⟨f, (hF f).2 hS⟩`. Set `zb : Fin d → Fm` to `fun b => R (1, p b) z`. Establish `hexp : ∀ γ, R γ z = ∑ b, w b γ.2 • zb b`. Introduce `γ`.

Use `Subtype.ext (funext fun x => ?_)` and prove the remaining obligations. Establish `e1 : f (x * tau K γ) = f (x * kI E n γ.2)`. Rewrite using `[tau_apply, fin_kI_comm, ← mul_assoc]`. Conclude with `hT.1 _ γ.1.2 _`. Establish `e2` using `congrFun (hs _ (hT.2 x)) γ.2`.

Simplify using `only [LinearMap.proj_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at e2`. Express the relevant statement in the definitionally equal form `f (x * tau K γ) = _`. Rewrite using `[e1, e2]`. Simplify using `only [AddSubmonoidClass.coe_finset_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Establish `e3 : (zb b).1 x = f (x * kI E n (p b))`. Express the relevant statement in the definitionally equal form `f (x * tau K (1, p b)) = _`. Simplify using `[tau_apply]`. Rewrite using `[e3, mul_comm]`. Take `⟨y, hyV, hyY, horth⟩` from `hAbs (K × Kinf E n) Fm R B W' V Y z hBs hBp (fun γ a b => (hBi _ (hdet γ) a).2 _ b _ (fun _ => rfl) fun _ => rfl) (by`.

Introduce and unpack `h ⟨v, hv, rfl⟩ γ`. Use `⟨_, hWR v hv γ.2, funext fun x => ?_⟩` and prove the remaining obligations. Simplify using `[LinearMap.funLeft_apply])`. Use the proof step `(by`. Introduce and unpack `γ v ⟨ψ, hψ, e⟩`.

Take `⟨ψ', h', e'⟩` from `trans_mem π ψ hψ γ.1.1 γ.2`. Use `hVm ψ' h' _ (e'.trans (funext fun x => ?_))` and prove the remaining obligations. Establish `e2 : ψ.1 = v.1` using `e`. Rewrite using `[hR, ← tau_apply, e2])`. Use the proof step `(by`.

Introduce and unpack `v ⟨ψ, hψ, e⟩`. Take `⟨U, hU, hUm⟩` from `orbit_fin π K hKc ψ hψ`. Use `haveI := hU`. Use `fd_span Fm _ U fun γ => ?_` and prove the remaining obligations. Use `hUm γ.1.1 γ.1.2 γ.2` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Establish `e2 : ψ.1 = v.1` using `e`. Rewrite using `[hR, tau_apply, e2])`. Use the proof step `(by haveI : FiniteDimensional ℂ (Y0.map (Sm E n).subtype) := Module.Finite.map _ _`.

Conclude with `fd_sub Fm Y (Y0.map (Sm E n).subtype) fun x hx => hx)`. Use the proof step `(by`. Introduce and unpack `v ⟨ψ, hψ, e⟩ hl`. Establish `key : ∀ g, ∃ h ∈ W, ∀ γ, h γ.2 = ψ.1 (g * tau K γ)`. Introduce `g`.

Take `⟨h, hh, e'⟩` from `hl ((LinearMap.proj g).comp Fm.subtype)`. Use `⟨h, hh, fun γ => ?_⟩` and prove the remaining obligations. Use `congrFun e' γ` as an intermediate fact. Simplify using `only [LinearMap.funLeft_apply] at this`. Rewrite using `[this]`.

Express the relevant statement in the definitionally equal form `v.1 (g * tau K γ) = _`. Establish `e2 : ψ.1 = v.1` using `e`. Rewrite using `[e2]`. Establish `hTy : TypeB K W ψ`. Use `⟨fun u hu g => ?_, fun g => ?_⟩` and prove the remaining obligations.

Take `⟨h, -, hh⟩` from `key g`. Establish `a1` using `hh (⟨u, hu⟩, 1)`. Establish `a2` using `hh 1`. Simplify using `only [tau_apply, map_one, mul_one] at a1 a2`. Conclude with `a1.symm.trans a2`.

Take `⟨h, hm, hh⟩` from `key g`. Use `hm using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `κ`. Establish `a1` using `hh (1, κ)`. Simplify using `only [tau_apply] at a1`.

Establish `a2 : ψ.1 (g * kI E n κ) = h κ` using `by simpa using a1.symm`. Conclude with `a2`. Conclude with `⟨ψ, hY ψ hψ hTy, e⟩)`. Use the proof step `(by`. Establish `hle : Submodule.span ℂ (Set.range fun γ => R γ z) ≤ Submodule.span ℂ (Set.range zb)` using `Submodule.span_le.2 (by`.

Introduce and unpack `_ ⟨γ, rfl⟩`. Simplify using `only [hexp γ]`. Conclude with `Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))`. Use `haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range zb)) := FiniteDimensional.span_of_finite ℂ (Set.finite_range zb)`. Conclude with `Submodule.finiteDimensional_of_le hle)`.

Use the proof step `(by`. Introduce `l`. Establish `e : (fun γ => l (R γ z)) = ∑ b, l (zb b) • LinearMap.funLeft ℂ ℂ Prod.snd (w b)`. Use function extensionality and compare the values at `γ`. Simplify using `only [hexp γ, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, LinearMap.funLeft_apply]`.

Conclude with `Finset.sum_congr rfl fun b _ => mul_comm _ _`. Rewrite using `[e]`. Conclude with `Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ ⟨w b, hw b, rfl⟩)`. Take `⟨ψ₀, hψ₀, e₀⟩` from `hyV`. Use `⟨ψ₀, hψ₀, ?_⟩` and prove the remaining obligations.

Establish `e₀' : ψ₀.1 = y.1` using `e₀`. Establish `hz : f - y.1 = 0`. Use `hOrth E n hn D π hfix _ ((hF _).1 (z - y).2) (inS_sub D π hI ?_) fun ψ hψ u hu hc => ?_` and prove the remaining obligations. Rewrite using `[← e₀']`. Conclude with `((hCv E n hn D π hfix ψ₀ hψ₀).2 0 0 ⟨continuous_const, HasCompactSupport.zero⟩ continuous_const).2.2`.

Establish `h1` using `hBw ⟨ψ.1, (hF _).2 (hSl ψ hψ)⟩ (z - y) u hu hc`. Establish `h2` using `horth ⟨ψ.1, (hF _).2 (hSl ψ hψ)⟩ (hVm ψ hψ _ rfl)`. Rewrite `h1` using `[h2, mul_zero]`. Conclude with `h1`. Rewrite using `[e₀']`.

Conclude with `(sub_eq_zero.1 hz).symm`.
-/
theorem typeIn_pf : PiAdm → DetZero → EvalBasis → CvIn → FormEx → OrthZero → AbsType → TypeIn := by
  intro hAdm hDet hEv hCv hForm hOrth hAbs E _ _ _ n hn D π hfix K W hKo hKc hW hWR f hS hI hT
  obtain ⟨Fm, B, hF, hBs, hBp, hBw, hBi⟩ := hForm E n hn D
  obtain ⟨Y0, -, hYfd, hY⟩ := hAdm E n hn π hfix K W hKo hW
  haveI := hYfd
  haveI := hW
  have hdet : ∀ γ, logAbs (tau K γ).val.det = 0 := fun γ => by
    rw [tau_apply, DiscreteGroups.T1.G.Dcy.logAbs_det_mul', (hDet E n).2 K hKc _ γ.1.2, (hDet E n).1 γ.2, add_zero]
  have hst : ∀ γ, ∀ a ∈ Fm, (fun x => a (x * tau K γ)) ∈ Fm := fun γ a ha => (hBi _ (hdet γ) ⟨a, ha⟩).1
  let R := rtRep (tau K) Fm hst
  have hR : ∀ γ (a : Fm) x, (R γ a).1 x = a.1 (x * tau K γ) := fun _ _ _ => rfl
  let W' : Submodule ℂ ((K × Kinf E n) → ℂ) := W.map (LinearMap.funLeft ℂ ℂ Prod.snd)
  let V : Submodule ℂ Fm := (π.V.map (Sm E n).subtype).comap Fm.subtype
  let Y : Submodule ℂ Fm := (Y0.map (Sm E n).subtype).comap Fm.subtype
  have hSl : ∀ ψ ∈ π.V, Slab D ψ.1 := fun ψ h => (hCv E n hn D π hfix ψ h).1
  have hVm : ∀ ψ ∈ π.V, ∀ a : Fm, ψ.1 = a.1 → a ∈ V := fun ψ h a e => ⟨ψ, h, e⟩

  obtain ⟨d, p, w, hw, hs⟩ := hEv (Kinf E n) (Kinf E n → ℂ) (fun x => LinearMap.proj x)
    (fun v hv => funext hv) W hW
  let z : Fm := ⟨f, (hF f).2 hS⟩
  let zb : Fin d → Fm := fun b => R (1, p b) z
  have hexp : ∀ γ, R γ z = ∑ b, w b γ.2 • zb b := by
    intro γ
    refine Subtype.ext (funext fun x => ?_)
    have e1 : f (x * tau K γ) = f (x * kI E n γ.2) := by
      rw [tau_apply, fin_kI_comm, ← mul_assoc]
      exact hT.1 _ γ.1.2 _
    have e2 := congrFun (hs _ (hT.2 x)) γ.2
    simp only [LinearMap.proj_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at e2
    change f (x * tau K γ) = _
    rw [e1, e2]
    simp only [AddSubmonoidClass.coe_finset_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    have e3 : (zb b).1 x = f (x * kI E n (p b)) := by
      change f (x * tau K (1, p b)) = _
      simp [tau_apply]
    rw [e3, mul_comm]
  obtain ⟨y, hyV, hyY, horth⟩ := hAbs (K × Kinf E n) Fm R B W' V Y z hBs hBp
    (fun γ a b => (hBi _ (hdet γ) a).2 _ b _ (fun _ => rfl) fun _ => rfl)
    (by
      rintro h ⟨v, hv, rfl⟩ γ
      refine ⟨_, hWR v hv γ.2, funext fun x => ?_⟩
      simp [LinearMap.funLeft_apply])
    (by
      rintro γ v ⟨ψ, hψ, e⟩
      obtain ⟨ψ', h', e'⟩ := trans_mem π ψ hψ γ.1.1 γ.2
      refine hVm ψ' h' _ (e'.trans (funext fun x => ?_))
      have e2 : ψ.1 = v.1 := e
      rw [hR, ← tau_apply, e2])
    (by
      rintro v ⟨ψ, hψ, e⟩
      obtain ⟨U, hU, hUm⟩ := orbit_fin π K hKc ψ hψ
      haveI := hU
      refine fd_span Fm _ U fun γ => ?_
      have := hUm γ.1.1 γ.1.2 γ.2
      convert this using 1
      funext x
      have e2 : ψ.1 = v.1 := e
      rw [hR, tau_apply, e2])
    (by
      haveI : FiniteDimensional ℂ (Y0.map (Sm E n).subtype) := Module.Finite.map _ _
      exact fd_sub Fm Y (Y0.map (Sm E n).subtype) fun x hx => hx)
    (by
      rintro v ⟨ψ, hψ, e⟩ hl
      have key : ∀ g, ∃ h ∈ W, ∀ γ, h γ.2 = ψ.1 (g * tau K γ) := by
        intro g
        obtain ⟨h, hh, e'⟩ := hl ((LinearMap.proj g).comp Fm.subtype)
        refine ⟨h, hh, fun γ => ?_⟩
        have := congrFun e' γ
        simp only [LinearMap.funLeft_apply] at this
        rw [this]
        change v.1 (g * tau K γ) = _
        have e2 : ψ.1 = v.1 := e
        rw [e2]
      have hTy : TypeB K W ψ := by
        refine ⟨fun u hu g => ?_, fun g => ?_⟩
        · obtain ⟨h, -, hh⟩ := key g
          have a1 := hh (⟨u, hu⟩, 1)
          have a2 := hh 1
          simp only [tau_apply, map_one, mul_one] at a1 a2
          exact a1.symm.trans a2
        · obtain ⟨h, hm, hh⟩ := key g
          convert hm using 1
          funext κ
          have a1 := hh (1, κ)
          simp only [tau_apply] at a1
          have a2 : ψ.1 (g * kI E n κ) = h κ := by simpa using a1.symm
          exact a2
      exact ⟨ψ, hY ψ hψ hTy, e⟩)
    (by
      have hle : Submodule.span ℂ (Set.range fun γ => R γ z) ≤ Submodule.span ℂ (Set.range zb) :=
        Submodule.span_le.2 (by
          rintro _ ⟨γ, rfl⟩
          simp only [hexp γ]
          exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))
      haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range zb)) :=
        FiniteDimensional.span_of_finite ℂ (Set.finite_range zb)
      exact Submodule.finiteDimensional_of_le hle)
    (by
      intro l
      have e : (fun γ => l (R γ z)) = ∑ b, l (zb b) • LinearMap.funLeft ℂ ℂ Prod.snd (w b) := by
        funext γ
        simp only [hexp γ, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          LinearMap.funLeft_apply]
        exact Finset.sum_congr rfl fun b _ => mul_comm _ _
      rw [e]
      exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ ⟨w b, hw b, rfl⟩)
  obtain ⟨ψ₀, hψ₀, e₀⟩ := hyV
  refine ⟨ψ₀, hψ₀, ?_⟩
  have e₀' : ψ₀.1 = y.1 := e₀
  have hz : f - y.1 = 0 := by
    refine hOrth E n hn D π hfix _ ((hF _).1 (z - y).2) (inS_sub D π hI ?_) fun ψ hψ u hu hc => ?_
    · rw [← e₀']
      exact ((hCv E n hn D π hfix ψ₀ hψ₀).2 0 0 ⟨continuous_const, HasCompactSupport.zero⟩ continuous_const).2.2
    · have h1 := hBw ⟨ψ.1, (hF _).2 (hSl ψ hψ)⟩ (z - y) u hu hc
      have h2 := horth ⟨ψ.1, (hF _).2 (hSl ψ hψ)⟩ (hVm ψ hψ _ rfl)
      rw [h2, mul_zero] at h1
      exact h1
  rw [e₀']
  exact (sub_eq_zero.1 hz).symm

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end

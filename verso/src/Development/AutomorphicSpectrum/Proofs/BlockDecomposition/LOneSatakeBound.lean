import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.SatakeSocle.SocleOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalSegmentRepLengthOneUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportOfPrincipalSeriesSubquotientStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Outright
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.OneSat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `hϖ` using `Zls.irreducible_unif (k := k)`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `le_uniformizer_iff.2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hϖ.not_isUnit)`. Take `⟨y, hy⟩` from `valuation_surjective (uniformizer k)`. Establish `hlt : valuation k y < 1` using `hy ▸ uniformizer_lt_one`.

Rewrite using `[← hy]`. Conclude with `(mem_cball_uniformiser hϖ (x := Zls.unifU k) rfl ⟨y, hlt.le⟩).2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 hlt)`.
-/
theorem valuation_unifU : valuation k ((Zls.unifU k : kˣ) : k) = uniformizer k := by
  have hϖ := Zls.irreducible_unif (k := k)
  apply le_antisymm
  · exact le_uniformizer_iff.2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hϖ.not_isUnit)
  · obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k)
    have hlt : valuation k y < 1 := hy ▸ uniformizer_lt_one
    rw [← hy]
    exact (mem_cball_uniformiser hϖ (x := Zls.unifU k) rfl ⟨y, hlt.le⟩).2
      (Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 hlt)

/- English proof (translation)
Use `⟨GlobalTheory.Parabolic.isIrreducible_of_equiv φ h.1, ?_, ?_⟩` and prove the remaining obligations. Take `⟨v, hv, h0⟩` from `(Submodule.ne_bot_iff _).1 h.2.1`. Use `(Submodule.ne_bot_iff _).2 ⟨φ v, fun g => ?_, fun e => h0 (φ.toLinearEquiv.injective ?_)⟩` and prove the remaining obligations. Establish `h1` using `hv g`. Establish `e : φ (π g v) = σ g (φ v)` using `φ.toIntertwiningMap.isIntertwining _ _ g v`.

Rewrite using `[← e, h1, map_smul]`. Simplify using `using e`. Conclude with `(IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans h.2.2`.
-/
theorem hasSatake_of_equiv {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin n) k) V} {σ : Representation ℂ (GL (Fin n) k) W} {α : Fin n → ℂˣ}
    (φ : π.Equiv σ) (h : HasSatake π α) : HasSatake σ α := by
  refine ⟨GlobalTheory.Parabolic.isIrreducible_of_equiv φ h.1, ?_, ?_⟩
  · obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 h.2.1
    refine (Submodule.ne_bot_iff _).2 ⟨φ v, fun g => ?_, fun e => h0 (φ.toLinearEquiv.injective ?_)⟩
    · have h1 := hv g
      have e : φ (π g v) = σ g (φ v) := φ.toIntertwiningMap.isIntertwining _ _ g v
      rw [← e, h1, map_smul]
    · simpa using e
  · exact (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans h.2.2

/- English proof (translation)
Establish `hBZ` using `GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness`. Establish `hadm : IsAdmissible x.rep` using `(hBZ k).1 (Fin x.1) x.2.rep.V x.rep x.2.rep.smooth x.2.rep.irr`. Establish `hI : fixed x.rep (iwahori k (Fin x.1)) ≠ ⊥`. Take `⟨v, hv, hv0⟩` from `(Submodule.ne_bot_iff _).1 hs`. Use `(Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩` and prove the remaining obligations.

Conclude with `hv ⟨h.1, iwahori_le_KO k _ h.2⟩`. Take `⟨α, hα⟩` from `GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries hadm x.2.rep.irr hI`. Establish `hχ : ∀ i, IsSmoothChar (unrChar k (α i))` using `fun i => isSmoothChar_of_isUnram (isUnram_unrChar k (α i))`. Establish `h1` using `GlobalTheory.T.supercuspidalSupport_of_principalSeries_subquotient k x.1 (fun i => unrChar k (α i)) hχ x.2.rep hα`. Establish `h2 : HasSupport x.rep {x}` using `hasSupport_self hx`.

Establish `he` using `GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique GlobalTheory.CompanionTheory.GeoLink.geometricLemma hBZ h1 h2`. Establish `hmem : x ∈ (Finset.univ.val.map fun i => IrrGL.ofChar (unrChar k (α i)) (hχ i))`. Rewrite using `[he]`. Conclude with `Multiset.mem_singleton_self x`. Take `⟨i, -, hi⟩` from `Multiset.mem_map.1 hmem`.

Conclude with `⟨unrChar k (α i), isUnram_unrChar k (α i), hi.symm⟩`.
-/
theorem isUnramChar_of_isCusp_of_isSpherical [CharZero k] (x : IrrGL k) (hx : x.IsCusp) (hs : IsSpherical x.rep) :
    x.IsUnramChar := by
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hadm : IsAdmissible x.rep := (hBZ k).1 (Fin x.1) x.2.rep.V x.rep x.2.rep.smooth x.2.rep.irr
  have hI : fixed x.rep (iwahori k (Fin x.1)) ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩
    exact hv ⟨h.1, iwahori_le_KO k _ h.2⟩
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries hadm x.2.rep.irr hI
  have hχ : ∀ i, IsSmoothChar (unrChar k (α i)) := fun i => isSmoothChar_of_isUnram (isUnram_unrChar k (α i))
  have h1 := GlobalTheory.T.supercuspidalSupport_of_principalSeries_subquotient k x.1 (fun i => unrChar k (α i)) hχ x.2.rep hα
  have h2 : HasSupport x.rep {x} := hasSupport_self hx
  have he := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique GlobalTheory.CompanionTheory.GeoLink.geometricLemma hBZ h1 h2
  have hmem : x ∈ (Finset.univ.val.map fun i => IrrGL.ofChar (unrChar k (α i)) (hχ i)) := by
    rw [he]; exact Multiset.mem_singleton_self x
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hmem
  exact ⟨unrChar k (α i), isUnram_unrChar k (α i), hi.symm⟩

/- English proof (translation)
Establish `hLM` using `PositivityTheory.Exh.langlandsMultisegments_holds`. Establish `hSC` using `PositivityTheory.Exh.standardCosocleGL_holds`. Establish `hBZ` using `GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness`. Take `⟨N, c⟩` from `y`. Take `⟨hd, hc⟩` from `id hL`.

Establish `hsub : IsSubquotient c.rep.ρ (prodIrr Δ.term hd)` using `hc.isSubquotient`. Establish `hsph` using `GlobalTheory.T.isSpherical_factor_of_spherical_subquotient k Δ.len N Δ.term hd _ c.rep.ρ hsub hS`. Establish `h0 : Δ.term ⟨0, Δ.len_pos⟩ = Δ.first` using `by simp [Segment.term]`. Establish `key : ∀ x z : IrrGL k, x = z → IsSpherical x.rep → IsSpherical z.rep`. Introduce and unpack `_ _ rfl h`.

Conclude with `h`. Establish `hU : Δ.first.IsUnramChar` using `isUnramChar_of_isCusp_of_isSpherical Δ.first Δ.isCusp_first (key _ _ h0 (hsph _))`. Take `⟨μ, hμ, hfirst⟩` from `hU`. Establish `hμs` using `isSmoothChar_of_isUnram hμ`. Establish `hterm : ∀ a, Δ.term a = IrrGL.ofChar (μ * absPow k ((a : ℕ) : ℂ)) (hμs.mul (isSmoothChar_absPow _))` using `fun a => by simp only [Segment.term, IrrGL.nu, hfirst, IrrGL.tw_ofChar]`.

Establish `hd1 : Δ.d = 1` using `congrArg Sigma.fst hfirst`. Establish `hN : N = Δ.len`. Establish `h2 : ∑ a, (Δ.term a).1 = N` using `hd`. Rewrite `h2` using `[Segment.sum_term_fst, Segment.deg, hd1, mul_one]`. Conclude with `h2.symm`.

Substitute `hN` using the available equality. Set `Γ` to `Segment.ofChar μ hμs Δ.len Δ.len_pos`. Establish `hterm' : ∀ a, Γ.term a = IrrGL.ofChar (μ * absPow k ((a : ℕ) : ℂ)) (hμs.mul (isSmoothChar_absPow _))` using `fun a => by show (IrrGL.ofChar μ hμs).nu _ = _`. Simplify using `only [IrrGL.nu, IrrGL.tw_ofChar]`. Establish `hd' : ∑ a, (Γ.term a).1 = Δ.len` using `(Segment.sum_term_fst _).trans (mul_one _)`.

Establish `hP` using `GlobalTheory.SphSeg.isSubquotient_prodIrr_prinSeries Δ.term hd _ _ hterm`. Establish `hP'` using `GlobalTheory.SphSeg.isSubquotient_prodIrr_prinSeries Γ.term hd' _ _ hterm'`. Set `χ'` to `μ * absPow k (((Δ.len : ℂ) - 1) / 2)`. Establish `hu' : IsUnram χ'` using `fun x hx => by`. Rewrite using `[MonoidHom.mul_apply, hμ x hx, isUnram_absPow k _ x hx, one_mul]`.

Establish `hχs : IsSmoothChar χ'` using `isSmoothChar_of_isUnram hu'`. Take `⟨f, hf⟩` from `embeds_detRep_segment hμs Δ.len_pos hd'`. Establish `hϖ` using `valuation_unifU (k := k)`. Establish `hu : ∀ i : Fin Δ.len, IsUnram (μ * absPow k ((i : ℕ) : ℂ))` using `fun i x hx => by`. Rewrite using `[MonoidHom.mul_apply, hμ x hx, isUnram_absPow k _ x hx, one_mul]`.

Set `α : Fin Δ.len → ℂˣ` to `fun i => (μ * absPow k ((i : ℕ) : ℂ)) (Zls.unifU k)`. Establish `heq : (fun i => unrChar k (α i)) = fun i : Fin Δ.len => μ * absPow k ((i : ℕ) : ℂ)`. Use function extensionality and compare the values at `fun i => (eq_unrChar (hu i) hϖ).symm`. Establish `hA : HasSatake c.rep.ρ α` using `⟨c.rep.irr, hS, by rw [heq]; exact hsub.trans hP⟩`. Establish `hB : HasSatake (IrrRep.det (Fin Δ.len) χ' hχs).ρ α` using `⟨(IrrRep.det (Fin Δ.len) χ' hχs).irr, isSpherical_detRep hu', by rw [heq]; exact (IsSubquotient.of_injective f hf).trans hP'⟩`.

Take `⟨E⟩` from `GlobalTheory.T.nonempty_equiv_of_same_satakeParameters hBZ k Δ.len α c.rep (IrrRep.det (Fin Δ.len) χ' hχs) hA hB`. Establish `hL2` using `(GlobalTheory.T.isLanglandsClassification_detCharacter hSC k Δ.len χ' hχs).of_equiv E.symm`. Establish `hL1` using `hL.isL`. Establish `hm` using `(hLM k).1 _ _ ⟨Δ.len, c⟩ hL1 hL2`. Use `congrArg Multiset.card hm` as an intermediate fact.

Simplify using `using this.symm`.
-/
theorem len_eq_one [CharZero k] (Δ : Segment k) (y : IrrGL k) (hL : IsLSeg Δ y.rep) (hS : IsSpherical y.rep) :
    Δ.len = 1 := by
  have hLM := PositivityTheory.Exh.langlandsMultisegments_holds
  have hSC := PositivityTheory.Exh.standardCosocleGL_holds
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  obtain ⟨N, c⟩ := y
  obtain ⟨hd, hc⟩ := id hL
  have hsub : IsSubquotient c.rep.ρ (prodIrr Δ.term hd) := hc.isSubquotient
  have hsph := GlobalTheory.T.isSpherical_factor_of_spherical_subquotient k Δ.len N Δ.term hd _ c.rep.ρ hsub hS
  have h0 : Δ.term ⟨0, Δ.len_pos⟩ = Δ.first := by simp [Segment.term]
  have key : ∀ x z : IrrGL k, x = z → IsSpherical x.rep → IsSpherical z.rep := by
    rintro _ _ rfl h; exact h
  have hU : Δ.first.IsUnramChar :=
    isUnramChar_of_isCusp_of_isSpherical Δ.first Δ.isCusp_first (key _ _ h0 (hsph _))
  obtain ⟨μ, hμ, hfirst⟩ := hU
  have hμs := isSmoothChar_of_isUnram hμ
  have hterm : ∀ a, Δ.term a = IrrGL.ofChar (μ * absPow k ((a : ℕ) : ℂ)) (hμs.mul (isSmoothChar_absPow _)) :=
    fun a => by simp only [Segment.term, IrrGL.nu, hfirst, IrrGL.tw_ofChar]
  have hd1 : Δ.d = 1 := congrArg Sigma.fst hfirst
  have hN : N = Δ.len := by
    have h2 : ∑ a, (Δ.term a).1 = N := hd
    rw [Segment.sum_term_fst, Segment.deg, hd1, mul_one] at h2
    exact h2.symm
  subst hN
  let Γ := Segment.ofChar μ hμs Δ.len Δ.len_pos
  have hterm' : ∀ a, Γ.term a = IrrGL.ofChar (μ * absPow k ((a : ℕ) : ℂ)) (hμs.mul (isSmoothChar_absPow _)) :=
    fun a => by
      show (IrrGL.ofChar μ hμs).nu _ = _
      simp only [IrrGL.nu, IrrGL.tw_ofChar]
  have hd' : ∑ a, (Γ.term a).1 = Δ.len := (Segment.sum_term_fst _).trans (mul_one _)
  have hP := GlobalTheory.SphSeg.isSubquotient_prodIrr_prinSeries Δ.term hd _ _ hterm
  have hP' := GlobalTheory.SphSeg.isSubquotient_prodIrr_prinSeries Γ.term hd' _ _ hterm'
  let χ' := μ * absPow k (((Δ.len : ℂ) - 1) / 2)
  have hu' : IsUnram χ' := fun x hx => by
    rw [MonoidHom.mul_apply, hμ x hx, isUnram_absPow k _ x hx, one_mul]
  have hχs : IsSmoothChar χ' := isSmoothChar_of_isUnram hu'
  obtain ⟨f, hf⟩ := embeds_detRep_segment hμs Δ.len_pos hd'
  have hϖ := valuation_unifU (k := k)
  have hu : ∀ i : Fin Δ.len, IsUnram (μ * absPow k ((i : ℕ) : ℂ)) := fun i x hx => by
    rw [MonoidHom.mul_apply, hμ x hx, isUnram_absPow k _ x hx, one_mul]
  let α : Fin Δ.len → ℂˣ := fun i => (μ * absPow k ((i : ℕ) : ℂ)) (Zls.unifU k)
  have heq : (fun i => unrChar k (α i)) = fun i : Fin Δ.len => μ * absPow k ((i : ℕ) : ℂ) :=
    funext fun i => (eq_unrChar (hu i) hϖ).symm
  have hA : HasSatake c.rep.ρ α := ⟨c.rep.irr, hS, by rw [heq]; exact hsub.trans hP⟩
  have hB : HasSatake (IrrRep.det (Fin Δ.len) χ' hχs).ρ α :=
    ⟨(IrrRep.det (Fin Δ.len) χ' hχs).irr, isSpherical_detRep hu',
      by rw [heq]; exact (IsSubquotient.of_injective f hf).trans hP'⟩
  obtain ⟨E⟩ := GlobalTheory.T.nonempty_equiv_of_same_satakeParameters hBZ k Δ.len α c.rep (IrrRep.det (Fin Δ.len) χ' hχs) hA hB
  have hL2 := (GlobalTheory.T.isLanglandsClassification_detCharacter hSC k Δ.len χ' hχs).of_equiv E.symm
  have hL1 := hL.isL
  have hm := (hLM k).1 _ _ ⟨Δ.len, c⟩ hL1 hL2
  have := congrArg Multiset.card hm
  simpa using this.symm

/- English proof (translation)
Take `⟨𝔪, hL⟩` from `PositivityTheory.Exh.langlandsExhaustionGL_holds k x`. Take `⟨h, y, hd, ⟨Δ, hord, hseg⟩, hcos⟩` from `id hL`. Establish `hsphy : ∀ a, IsSpherical (y a).rep` using `GlobalTheory.T.isSpherical_factor_of_spherical_subquotient k h x.1 y hd x.2.rep.V x.rep hcos.isSubquotient hsat.2.1`. Establish `hlen : ∀ i, (Δ i).len = 1` using `fun i => len_eq_one (Δ i) (y i) (hseg i) (hsphy i)`. Establish `hsingle : ∀ i, Δ i = Segment.single (Δ i).first (Δ i).isCusp_first` using `fun i => Segment.ext_first rfl (by rw [hlen i]; rfl)`.

Establish `hms : ∀ i, (Δ i).ms = {(Δ i).first}` using `fun i => (congrArg Segment.ms (hsingle i)).trans (Segment.ms_single _ _)`. Establish `h1 : HasSupport x.rep (∑ a, (Δ a).ms)` using `GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (fun a => (hseg a).hasSupport) x.2.rep.irr hcos.isSubquotient`. Establish `h2` using `GlobalTheory.T.supercuspidalSupport_of_principalSeries_subquotient k x.1 (fun i => unrChar k (α i)) (fun i => isSmoothChar_of_isUnram (isUnram_unrChar k (α i))) x.2.rep hsat.2.2`. Establish `heq` using `GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique GlobalTheory.CompanionTheory.GeoLink.geometricLemma GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness h1 h2`. Establish `hsupp : (∑ a, (Δ a).ms) = Finset.univ.val.map fun i => (Δ i).first`.

Simplify using `only [hms]`. Rewrite using `[Finset.sum_eq_multiset_sum]`. Conclude with `Multiset.bind_singleton Finset.univ.val fun i => (Δ i).first`. Rewrite `heq` using `[hsupp]`. Establish `hinj : Function.Injective fun D : Segment k => (D.first, D.len)` using `fun a b e => Segment.ext_first (congrArg Prod.fst e) (congrArg Prod.snd e)`.

Establish `hm : 𝔪 = Finset.univ.val.map fun i => Segment.single (IrrGL.ofChar (unrChar k (α i)) (isSmoothChar_of_isUnram (isUnram_unrChar k (α i)))) (IrrGL.isCusp_ofChar _ _)`. Apply `Multiset.map_injective hinj` to reduce the goal to its premises. Establish `e1` using `congrArg (Multiset.map fun ρ : IrrGL k => (ρ, 1)) heq`. Simplify using `only [Multiset.map_map, Function.comp_def] at e1`. Rewrite using `[← hord.1, Multiset.map_map, Multiset.map_map]`.

Simplify using `only [Function.comp_def, hlen]`. Conclude with `e1`. Rewrite using `[← hm]`. Conclude with `hL`.
-/
theorem isL_single_unrChar [CharZero k] (x : IrrGL k) (α : Fin x.1 → ℂˣ) (hsat : HasSatake x.rep α) :
    IsL (Finset.univ.val.map fun i => Segment.single (IrrGL.ofChar (unrChar k (α i))
      (isSmoothChar_of_isUnram (isUnram_unrChar k (α i)))) (IrrGL.isCusp_ofChar _ _)) x.rep := by
  obtain ⟨𝔪, hL⟩ := PositivityTheory.Exh.langlandsExhaustionGL_holds k x
  obtain ⟨h, y, hd, ⟨Δ, hord, hseg⟩, hcos⟩ := id hL
  have hsphy : ∀ a, IsSpherical (y a).rep :=
    GlobalTheory.T.isSpherical_factor_of_spherical_subquotient k h x.1 y hd x.2.rep.V x.rep hcos.isSubquotient hsat.2.1
  have hlen : ∀ i, (Δ i).len = 1 := fun i => len_eq_one (Δ i) (y i) (hseg i) (hsphy i)
  have hsingle : ∀ i, Δ i = Segment.single (Δ i).first (Δ i).isCusp_first := fun i =>
    Segment.ext_first rfl (by rw [hlen i]; rfl)
  have hms : ∀ i, (Δ i).ms = {(Δ i).first} := fun i =>
    (congrArg Segment.ms (hsingle i)).trans (Segment.ms_single _ _)
  have h1 : HasSupport x.rep (∑ a, (Δ a).ms) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (fun a => (hseg a).hasSupport) x.2.rep.irr
      hcos.isSubquotient
  have h2 := GlobalTheory.T.supercuspidalSupport_of_principalSeries_subquotient k x.1 (fun i => unrChar k (α i))
    (fun i => isSmoothChar_of_isUnram (isUnram_unrChar k (α i))) x.2.rep hsat.2.2
  have heq := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique GlobalTheory.CompanionTheory.GeoLink.geometricLemma
    GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness h1 h2
  have hsupp : (∑ a, (Δ a).ms) = Finset.univ.val.map fun i => (Δ i).first := by
    simp only [hms]
    rw [Finset.sum_eq_multiset_sum]
    exact Multiset.bind_singleton Finset.univ.val fun i => (Δ i).first
  rw [hsupp] at heq
  have hinj : Function.Injective fun D : Segment k => (D.first, D.len) := fun a b e =>
    Segment.ext_first (congrArg Prod.fst e) (congrArg Prod.snd e)
  have hm : 𝔪 = Finset.univ.val.map fun i => Segment.single (IrrGL.ofChar (unrChar k (α i))
      (isSmoothChar_of_isUnram (isUnram_unrChar k (α i)))) (IrrGL.isCusp_ofChar _ _) := by
    apply Multiset.map_injective hinj
    have e1 := congrArg (Multiset.map fun ρ : IrrGL k => (ρ, 1)) heq
    simp only [Multiset.map_map, Function.comp_def] at e1
    rw [← hord.1, Multiset.map_map, Multiset.map_map]
    simp only [Function.comp_def, hlen]
    exact e1
  rw [← hm]
  exact hL

end GlobalTheory.CompanionTheory.OneSat

open GlobalTheory.CompanionTheory.OneSat in

/- English proof (translation)
Introduce `k _ _ _ _ _ n ξ hξ V _ _ π hs`. Establish `hϖ` using `valuation_unifU (k := k)`. Establish `hms : ∀ (χ χ' : kˣ →* ℂˣ) (h : IsSmoothChar χ) (h' : IsSmoothChar χ') (c) (c'), χ = χ' → Segment.single (IrrGL.ofChar χ h) c = Segment.single (IrrGL.ofChar χ' h') c'`. Introduce and unpack `χ _ h h' c c' rfl`. Both sides reduce to the same expression.

Establish `key : ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL (Fin n) k) W), IsSmooth τ → HasSatake τ (PositivityTheory.SphericalProduct.atUnif k ξ) → IsL (PositivityTheory.SphericalProduct.msOne ξ hξ) τ`. Introduce `W _ _ τ hτ hsat`. Establish `φ` using `IrrGL.equivOf τ hτ hsat.1`. Establish `h1` using `isL_single_unrChar (IrrGL.of τ hτ hsat.1) (PositivityTheory.SphericalProduct.atUnif k ξ) (hasSatake_of_equiv φ hsat)`. Establish `h2 : PositivityTheory.SphericalProduct.msOne ξ hξ = Finset.univ.val.map fun i : Fin n => Segment.single (IrrGL.ofChar (unrChar k (PositivityTheory.SphericalProduct.atUnif k ξ i)) (isSmoothChar_of_isUnram (isUnram_unrChar k _))) (IrrGL.isCusp_ofChar _ _)` using `Multiset.map_congr rfl fun i _ => hms _ _ _ _ _ _ (eq_unrChar (hξ i) hϖ)`.

Rewrite using `[h2]`. Conclude with `h1.of_equiv φ.symm`. Use `⟨fun hL => ?_, key π hs⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `GlobalTheory.CuspRep.ParLaws.exists_hasSatake (k := k) (PositivityTheory.SphericalProduct.atUnif k ξ)`. Establish `hLy` using `key y.ρ y.smooth hy`.

Take `⟨h, x, hd, hx, hc⟩` from `hL`. Establish `hc'` using `PositivityTheory.Exh.lOrderFree_of GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k _ h n x hd hx y.ρ hLy`. Take `⟨e⟩` from `hc.unique hc'`. Conclude with `hasSatake_of_equiv e hy`.
-/
theorem GlobalTheory.CompanionTheory.OneSat.lOneSat : PositivityTheory.SphericalProduct.LOneSat := by
  intro k _ _ _ _ _ n ξ hξ V _ _ π hs
  have hϖ := valuation_unifU (k := k)
  have hms : ∀ (χ χ' : kˣ →* ℂˣ) (h : IsSmoothChar χ) (h' : IsSmoothChar χ') (c) (c'), χ = χ' →
      Segment.single (IrrGL.ofChar χ h) c = Segment.single (IrrGL.ofChar χ' h') c' := by
    rintro χ _ h h' c c' rfl; rfl
  have key : ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL (Fin n) k) W), IsSmooth τ →
      HasSatake τ (PositivityTheory.SphericalProduct.atUnif k ξ) → IsL (PositivityTheory.SphericalProduct.msOne ξ hξ) τ := by
    intro W _ _ τ hτ hsat
    have φ := IrrGL.equivOf τ hτ hsat.1
    have h1 := isL_single_unrChar (IrrGL.of τ hτ hsat.1) (PositivityTheory.SphericalProduct.atUnif k ξ) (hasSatake_of_equiv φ hsat)
    have h2 : PositivityTheory.SphericalProduct.msOne ξ hξ = Finset.univ.val.map fun i : Fin n =>
        Segment.single (IrrGL.ofChar (unrChar k (PositivityTheory.SphericalProduct.atUnif k ξ i))
          (isSmoothChar_of_isUnram (isUnram_unrChar k _))) (IrrGL.isCusp_ofChar _ _) :=
      Multiset.map_congr rfl fun i _ => hms _ _ _ _ _ _ (eq_unrChar (hξ i) hϖ)
    rw [h2]
    exact h1.of_equiv φ.symm
  refine ⟨fun hL => ?_, key π hs⟩
  obtain ⟨y, hy⟩ := GlobalTheory.CuspRep.ParLaws.exists_hasSatake (k := k) (PositivityTheory.SphericalProduct.atUnif k ξ)
  have hLy := key y.ρ y.smooth hy
  obtain ⟨h, x, hd, hx, hc⟩ := hL
  have hc' := PositivityTheory.Exh.lOrderFree_of GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k _ h n x hd hx y.ρ hLy
  obtain ⟨e⟩ := hc.unique hc'
  exact hasSatake_of_equiv e hy

end

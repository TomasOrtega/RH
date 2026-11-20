import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PartsGiveDimension
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisLocalWeights
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisLocalWeightsDeRham
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.GoodRCongr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.SplitBCOfGalIso
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.DistinctAbsIrredConstituents
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TraceOfCharpoly
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace UpperTheory.GalS.Parts

open UpperTheory.GalS GlobalTheory.NRows GlobalTheory.AbsIrrConstituents Pointwise

/- English proof (translation)
Establish `hne : Ideal.span {((D.nd.l i : ℕ) : 𝓞 D.host.E)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `(Fact.out : (D.nd.l i).Prime).ne_zero` after adjusting the coercions. Use `(Ideal.finite_factors hne).subset fun v hv => ?_` and prove the remaining obligations. Conclude with `Ideal.dvd_span_singleton.mpr hv`.
-/
theorem placesOver_finite (D : D7) (i : D.nd.Loc) : (placesOver D.host.E (D.nd.l i)).Finite := by
  have hne : Ideal.span {((D.nd.l i : ℕ) : 𝓞 D.host.E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : (D.nd.l i).Prime).ne_zero
  refine (Ideal.finite_factors hne).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.mpr hv

/- English proof (translation)
Unfold `isoLoc`. Proceed by induction on `h with`. Consider the case `nil => rfl`. Consider the case `cons x _ ih => simp only [List.foldr_cons, List.map_cons] at ih ⊢`. Rewrite using `[ih]`.

Consider the case `swap x y l`. Simplify using `only [List.foldr_cons, List.map_cons]`. Rewrite using `[← D.naut.lpSum_assoc, ← D.naut.lpSum_assoc, D.naut.lpSum_comm (spehLoc _ _ y w)]`. Consider the case `trans _ _ a b => exact a.trans b`.
-/
theorem isoLoc_perm (D : D7) {Pa Pa' : List (Part D.naut.CG)} (h : Pa.Perm Pa') (w : PlE D.host) :
    isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pa' w := by
  unfold isoLoc
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [List.foldr_cons, List.map_cons] at ih ⊢; rw [ih]
  | swap x y l =>
    simp only [List.foldr_cons, List.map_cons]
    rw [← D.naut.lpSum_assoc, ← D.naut.lpSum_assoc, D.naut.lpSum_comm (spehLoc _ _ y w)]
  | trans _ _ a b => exact a.trans b

def large₂ (D : D7) : Prop := ∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → RelW D.nd D.naut (D.naut.wdOf i ρ w) (D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2))) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), Nc D.nd D.naut (isoLoc D.nd D.naut Pa w) → D.naut.IsdRW i ρ w ∧ UpperTheory.GalN.RelA D.nd D.naut (D.naut.wdOf i ρ w) (D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.locAutHodgeTateWeightsLevelZero i τ

/- English proof (translation)
Distinguish the cases in `hs : IsSplitPl D.host w`. Rewrite using `[hB.2.2.2.1 w hs]`. Conclude with `D.naut.locV_unr i P w hs hQ hg hp`. Conclude with `(hB.2.2.2.2.1 w hs).1`.
-/
theorem iso_unr (D : D7) (i : D.nd.Loc) (P : D.naut.AV i) (Pa) (w) (hB : IsBCV D.nd D.naut i P Pa) (hQ : w ∉ D.nd.Q i)
    (hg : ∀ k, w ∉ placesOver D.host.E (D.host.g k))
    (hp : w ∉ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde)) :
    D.naut.unr (isoLoc D.nd D.naut Pa w) := by
  by_cases hs : IsSplitPl D.host w
  · rw [hB.2.2.2.1 w hs]
    exact D.naut.locV_unr i P w hs hQ hg hp
  · exact (hB.2.2.2.2.1 w hs).1

/- English proof (translation)
Establish `hl : (D.nd.l i).Prime` using `Fact.out`. Use `iso_unr D i P Pa w hB (fun hq => D.nd.SQ_l i w (Or.inr hq) hw) (fun k => ?_) ?_` and prove the remaining obligations. Establish `hk : D.nd.l i ≠ D.host.g k` using `by fin_cases k`. Conclude with `hl0`. Conclude with `hl1`.

Conclude with `SumRepresentations.not_over_of_ne hl (D.host.g_prime k) hk hw`. Use `split_ifs with hpd`. Conclude with `SumRepresentations.not_over_of_ne hl D.host.pde'_prime (hpd ▸ D.host.pde_ne) hw`. Conclude with `SumRepresentations.not_over_of_ne hl D.host.pde_prime hpd hw`.
-/
theorem iso_unr_l (D : D7) (i : D.nd.Loc) (P : D.naut.AV i) (Pa) (w) (hB : IsBCV D.nd D.naut i P Pa)
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (hl0 : D.nd.l i ≠ D.host.g 0) (hl1 : D.nd.l i ≠ D.host.g 1) :
    D.naut.unr (isoLoc D.nd D.naut Pa w) := by
  have hl : (D.nd.l i).Prime := Fact.out
  refine iso_unr D i P Pa w hB (fun hq => D.nd.SQ_l i w (Or.inr hq) hw) (fun k => ?_) ?_
  · have hk : D.nd.l i ≠ D.host.g k := by
      fin_cases k
      · exact hl0
      · exact hl1
    exact SumRepresentations.not_over_of_ne hl (D.host.g_prime k) hk hw
  · split_ifs with hpd
    · exact SumRepresentations.not_over_of_ne hl D.host.pde'_prime (hpd ▸ D.host.pde_ne) hw
    · exact SumRepresentations.not_over_of_ne hl D.host.pde_prime hpd hw

/- English proof (translation)
Introduce `D h1 h5 hex hcomp i P P' hP hPP'`. Take `⟨x, hx⟩` from `Option.ne_none_iff_exists'.mp hP`. Take `⟨ρ, hρ⟩` from `hex i x`. Establish `hx' : D.naut.ptV i P' = some x` using `hPP' ▸ hx`. Establish `perm : ∀ Pa Pa', IsBCV D.nd D.naut i P Pa → IsBCV D.nd D.naut i P' Pa' → Pa.Perm Pa'`.

Introduce `Pa Pa' hB hB'`. Use `h5.2.1 Pa Pa' hB.1 hB'.1 ?_` and prove the remaining obligations. Use `filter_upwards [(placesOver_finite D i).compl_mem_cofinite, GlobalTheory.SplitDetermines.isoLoc_unr_ae D.nd D.naut Pa, GlobalTheory.SplitDetermines.isoLoc_unr_ae D.nd D.naut Pa'] with w hw u u'`. Use `show isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pa' w`. Establish `e` using `(((hcomp i x P Pa hx hB ρ hρ).1 w hw).eq_of_unr ((D.naut.unr_tw _ _).2 u)).symm.trans (((hcomp i x P' Pa' hx' hB' ρ hρ).1 w hw).eq_of_unr ((D.naut.unr_tw _ _).2 u'))`.

Establish `e2` using `congrArg (fun a => D.naut.lpTw a (-((1 - (D.R.nV : ℝ)) / 2))) e`. Simplify `e2` using `only [D.naut.lpTw_add, add_neg_cancel, D.naut.lpTw_zero]`. Establish `key : ∀ Pa Pa', IsBCV D.nd D.naut i P Pa → IsBCV D.nd D.naut i P' Pa' → ∀ w, isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pa' w` using `fun Pa Pa' hB hB' w => isoLoc_perm D (perm Pa Pa' hB hB') w`. Use `⟨perm, fun w _ _ => ?_⟩` and prove the remaining obligations. Take `⟨Pa, hB⟩` from `h1 i P`.

Take `⟨Pa', hB'⟩` from `h1 i P'`. Use `⟨fun hs => ?_, fun hs => ?_⟩` and prove the remaining obligations. Rewrite using `[← hB.2.2.2.1 w hs, ← hB'.2.2.2.1 w hs, key Pa Pa' hB hB' w]`. Rewrite using `[← (hB.2.2.2.2.1 w hs).2, ← (hB'.2.2.2.2.1 w hs).2, key Pa Pa' hB hB' w]`.
-/
theorem point_determines : ∀ D : D7, SumRepresentations.adm1 D → SumRepresentations.adm5 D → (∀ (i : D.nd.Loc) (x : D.nd.X i), ∃ ρ, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ) → (∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → RelW D.nd D.naut (D.naut.wdOf i ρ w) (D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2))) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), Nc D.nd D.naut (isoLoc D.nd D.naut Pa w) → D.naut.IsdRW i ρ w ∧ UpperTheory.GalN.RelA D.nd D.naut (D.naut.wdOf i ρ w) (D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.locAutHodgeTateWeightsLevelZero i τ) → ∀ (i : D.nd.Loc) (P P' : D.naut.AV i), D.naut.ptV i P ≠ none → D.naut.ptV i P = D.naut.ptV i P' → (∀ Pa Pa', IsBCV D.nd D.naut i P Pa → IsBCV D.nd D.naut i P' Pa' → Pa.Perm Pa') ∧ ∀ w, w ∉ D.nd.S i → w ∉ D.nd.Q i → (IsSplitPl D.host w → D.naut.locV i P w = D.naut.locV i P' w) ∧ (¬ IsSplitPl D.host w → ubc D.R.nV (D.naut.satV i P w) = ubc D.R.nV (D.naut.satV i P' w)) := by
  intro D h1 h5 hex hcomp i P P' hP hPP'
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hP
  obtain ⟨ρ, hρ⟩ := hex i x
  have hx' : D.naut.ptV i P' = some x := hPP' ▸ hx
  have perm : ∀ Pa Pa', IsBCV D.nd D.naut i P Pa → IsBCV D.nd D.naut i P' Pa' → Pa.Perm Pa' := by
    intro Pa Pa' hB hB'
    refine h5.2.1 Pa Pa' hB.1 hB'.1 ?_
    filter_upwards [(placesOver_finite D i).compl_mem_cofinite, GlobalTheory.SplitDetermines.isoLoc_unr_ae D.nd D.naut Pa,
      GlobalTheory.SplitDetermines.isoLoc_unr_ae D.nd D.naut Pa'] with w hw u u'
    show isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pa' w
    have e := (((hcomp i x P Pa hx hB ρ hρ).1 w hw).eq_of_unr ((D.naut.unr_tw _ _).2 u)).symm.trans
      (((hcomp i x P' Pa' hx' hB' ρ hρ).1 w hw).eq_of_unr ((D.naut.unr_tw _ _).2 u'))
    have e2 := congrArg (fun a => D.naut.lpTw a (-((1 - (D.R.nV : ℝ)) / 2))) e
    simpa only [D.naut.lpTw_add, add_neg_cancel, D.naut.lpTw_zero] using e2
  have key : ∀ Pa Pa', IsBCV D.nd D.naut i P Pa → IsBCV D.nd D.naut i P' Pa' →
      ∀ w, isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pa' w :=
    fun Pa Pa' hB hB' w => isoLoc_perm D (perm Pa Pa' hB hB') w
  refine ⟨perm, fun w _ _ => ?_⟩
  · obtain ⟨Pa, hB⟩ := h1 i P
    obtain ⟨Pa', hB'⟩ := h1 i P'
    refine ⟨fun hs => ?_, fun hs => ?_⟩
    · rw [← hB.2.2.2.1 w hs, ← hB'.2.2.2.1 w hs, key Pa Pa' hB hB' w]
    · rw [← (hB.2.2.2.2.1 w hs).2, ← (hB'.2.2.2.2.1 w hs).2, key Pa Pa' hB hB' w]

/- English proof (translation)
Take `⟨-, -, hGal⟩` from `htie`. Establish `key : ∀ x, ∃ P Pa, D.naut.ptV i P = some x ∧ IsBCV D.nd D.naut i P Pa` using `fun x => by`. Take `⟨P, hP⟩` from `D.naut.pt_surj i x`. Take `⟨Pa, hPa⟩` from `hadm i P`. Conclude with `⟨P, Pa, hP, hPa⟩`.

Establish `hunr` using `iso_unr D i`. Use `⟨fun w hw hl0 hl1 x => ?_, fun x w hwl hwS hwQ => ?_⟩` and prove the remaining obligations. Take `⟨P, Pa, hP, hB⟩` from `key x`. Establish `hu` using `iso_unr_l D i P Pa w hB hw hl0 hl1`. Establish `h` using `(hLGC i x P Pa hP hB _ (hr x)).2 w hw (Nc.of_unr hu)`.

Conclude with `⟨(hGal.1 i _ _ w hw (hr x).1).2 ⟨h.1, h.2.1.unr ((D.naut.unr_tw _ _).2 hu)⟩, fun τ hτ => h.2.2 τ hτ⟩`. Take `⟨P, Pa, hP, hB⟩` from `key x`. Establish `h` using `(hLGC i x P Pa hP hB _ (hr x)).1 w hwl`. Establish `hS : ¬ ((w ∈ placesOver D.host.E (D.host.g 0) ∨ w ∈ placesOver D.host.E (D.host.g 1) ∨ w ∈ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde)) ∧ w ∉ placesOver D.host.E (D.nd.l i))` using `fun hh => hwS ((D.nd.S_def i w).2 hh)`. Establish `hu : D.naut.unr (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w)`.

Use `h.unr ?_` and prove the remaining obligations. Rewrite using `[D.naut.unr_tw]`. Use `hunr P Pa w hB hwQ (fun k hk => hS ⟨?_, hwl⟩) (fun hk => hS ⟨Or.inr (Or.inr hk), hwl⟩)` and prove the remaining obligations. Use `fin_cases k`. Conclude with `Or.inl hk`.

Conclude with `Or.inr (Or.inl hk)`. Establish `h1` using `(D.naut.wdOf_unr i _ w hwl (hr x).1).1 hu`. Introduce `A hA σ hσ`. Take `⟨g, hg⟩` from `exists_smul_eq_of_isPlaceOver (D.nd.plOm.2 w) hA`. Establish `hσ' : σ ∈ Ine (F` using `D.host.E) (g • D.nd.plOm.1 w) := by rw [hg]; exact hσ`.

Establish `h2` using `h1 _ (ine_conj_of_smul hσ')`. Establish `h3 : mapRep (iotaOQ D.nd D.naut i) (r x) σ = 1`. Establish `e : σ = g * (g⁻¹ * σ * g) * g⁻¹` using `by group`. Rewrite using `[e, map_mul, map_mul, h2, mul_one, ← map_mul, mul_inv_cancel, map_one]`. Apply `Units.ext` to reduce the goal to its premises.

Establish `h4` using `congrArg (fun u : GL (Fin D.R.nV) (Qbar (D.nd.l i)) => u.val) h3`. Simplify using `only [mapRep, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_one] at h4`. Use `Matrix.map_injective (SumRepresentations.iotaOQ_injective D.nd D.naut i) ?_` and prove the remaining obligations. Use `show (r x σ).val.map (iotaOQ D.nd D.naut i) = (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map (iotaOQ D.nd D.naut i)`. Rewrite using `[Matrix.map_one _ (map_zero _) (map_one _)]`.

Conclude with `h4`.
-/
theorem crys_unram_of_lgc (D : D7) (htie : SumRepresentations.tie0 D) (hadm : SumRepresentations.adm1 D) (hLGC : large₂ D) (i : D.nd.Loc)
    (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : ∀ x, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (mapRep (iotaOQ D.nd D.naut i) (r x))) :
    G2a D.nd D.naut i r ∧
    ∀ x w, w ∉ placesOver D.host.E (D.nd.l i) → w ∉ D.nd.S i → w ∉ D.nd.Q i → UnramAt (F := D.host.E) (r x) w := by
  obtain ⟨-, -, hGal⟩ := htie
  have key : ∀ x, ∃ P Pa, D.naut.ptV i P = some x ∧ IsBCV D.nd D.naut i P Pa := fun x => by
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hPa⟩ := hadm i P
    exact ⟨P, Pa, hP, hPa⟩
  have hunr := iso_unr D i
  refine ⟨fun w hw hl0 hl1 x => ?_, fun x w hwl hwS hwQ => ?_⟩
  · obtain ⟨P, Pa, hP, hB⟩ := key x
    have hu := iso_unr_l D i P Pa w hB hw hl0 hl1
    have h := (hLGC i x P Pa hP hB _ (hr x)).2 w hw (Nc.of_unr hu)
    exact ⟨(hGal.1 i _ _ w hw (hr x).1).2 ⟨h.1, h.2.1.unr ((D.naut.unr_tw _ _).2 hu)⟩, fun τ hτ => h.2.2 τ hτ⟩
  · obtain ⟨P, Pa, hP, hB⟩ := key x
    have h := (hLGC i x P Pa hP hB _ (hr x)).1 w hwl
    have hS : ¬ ((w ∈ placesOver D.host.E (D.host.g 0) ∨ w ∈ placesOver D.host.E (D.host.g 1) ∨
        w ∈ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde)) ∧
        w ∉ placesOver D.host.E (D.nd.l i)) := fun hh => hwS ((D.nd.S_def i w).2 hh)
    have hu : D.naut.unr (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) := by
      refine h.unr ?_
      rw [D.naut.unr_tw]
      refine hunr P Pa w hB hwQ (fun k hk => hS ⟨?_, hwl⟩) (fun hk => hS ⟨Or.inr (Or.inr hk), hwl⟩)
      fin_cases k
      · exact Or.inl hk
      · exact Or.inr (Or.inl hk)
    have h1 := (D.naut.wdOf_unr i _ w hwl (hr x).1).1 hu
    intro A hA σ hσ
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (D.nd.plOm.2 w) hA
    have hσ' : σ ∈ Ine (F := D.host.E) (g • D.nd.plOm.1 w) := by rw [hg]; exact hσ
    have h2 := h1 _ (ine_conj_of_smul hσ')
    have h3 : mapRep (iotaOQ D.nd D.naut i) (r x) σ = 1 := by
      have e : σ = g * (g⁻¹ * σ * g) * g⁻¹ := by group
      rw [e, map_mul, map_mul, h2, mul_one, ← map_mul, mul_inv_cancel, map_one]
    apply Units.ext
    have h4 := congrArg (fun u : GL (Fin D.R.nV) (Qbar (D.nd.l i)) => u.val) h3
    simp only [mapRep, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_one] at h4
    refine Matrix.map_injective (SumRepresentations.iotaOQ_injective D.nd D.naut i) ?_
    show (r x σ).val.map (iotaOQ D.nd D.naut i) = (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map (iotaOQ D.nd D.naut i)
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact h4

/- English proof (translation)
Use `letI alg : Algebra (Kf D.nd i) (Qbar (D.nd.l i)) := (D.naut.iotaQ i).toAlgebra`. Establish `hss : ∀ x, IsSSRep (mapRep (algebraMap (Kf D.nd i) (AlgebraicClosure (Kf D.nd i))) (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r x)))`. Introduce `x`. Set `f : AlgebraicClosure (Kf D.nd i) →ₐ[Kf D.nd i] Qbar (D.nd.l i)` to `IsAlgClosed.lift`. Use `letI : Algebra (AlgebraicClosure (Kf D.nd i)) (Qbar (D.nd.l i)) := f.toRingHom.toAlgebra`.

Apply `SumRepresentations.isSSRep_descent (L := Qbar (D.nd.l i))` to reduce the goal to its premises. Establish `e : ((algebraMap (AlgebraicClosure (Kf D.nd i)) (Qbar (D.nd.l i))).comp (algebraMap (Kf D.nd i) (AlgebraicClosure (Kf D.nd i)))).comp (algebraMap (D.nd.O i) (Kf D.nd i)) = iotaOQ D.nd D.naut i`. Use extensionality with `z`. Use `show f (algebraMap (Kf D.nd i) _ (algebraMap _ (Kf D.nd i) z)) = D.naut.iotaQ i (algebraMap _ _ z)`. Rewrite using `[f.commutes]`.

Both sides reduce to the same expression. Rewrite using `[← mapRep_comp, ← mapRep_comp, e]`. Conclude with `(hr x).2.1`. Take `⟨K', hF, hA, hFD, hsplit⟩` from `GlobalTheory.T.exists_finiteDimensional_ext_irrSub_absIrr (fun x => mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r x)) hss`. Use `⟨K', hF, hA, hFD, fun x => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[mapRep_comp]`. Conclude with `hsplit x`. Introduce `W₁ W₂ h1 h2 hdis hiso`. Set `f' : K' →ₐ[Kf D.nd i] Qbar (D.nd.l i)` to `IsAlgClosed.lift`. Establish `e' : (f'.toRingHom).comp ((algebraMap (Kf D.nd i) K').comp (algebraMap (D.nd.O i) (Kf D.nd i))) = iotaOQ D.nd D.naut i`.

Use extensionality with `z`. Use `show f' (algebraMap (Kf D.nd i) K' (algebraMap _ (Kf D.nd i) z)) = D.naut.iotaQ i (algebraMap _ _ z)`. Rewrite using `[f'.commutes]`. Both sides reduce to the same expression. Establish `hQ : mapRep f'.toRingHom (mapRep ((algebraMap (Kf D.nd i) K').comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) = mapRep (iotaOQ D.nd D.naut i) (r x)`.

Rewrite using `[← mapRep_comp, e']`. Establish `hssK : IsSSRep (mapRep ((algebraMap (Kf D.nd i) K').comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x))`. Use `letI : Algebra K' (Qbar (D.nd.l i)) := f'.toRingHom.toAlgebra`. Apply `SumRepresentations.isSSRep_descent (L := Qbar (D.nd.l i))` to reduce the goal to its premises. Use `show IsSSRep (mapRep f'.toRingHom _)`.

Rewrite using `[hQ]`. Conclude with `(hr x).2.1`. Take `⟨d, u, σ, υ, h, Pm, hd, hrel⟩` from `GlobalTheory.T.exists_conj_double_block_of_iso_subspaces _ W₁ W₂ hssK h1.2.1 h2.2.1 h1.1 hdis hiso`. Conclude with `hN x K' _ f'.toRingHom e' d u σ υ h Pm hd hrel`.
-/
theorem constituentCondition_of_noRepeatedFactor (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : ∀ x, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (mapRep (iotaOQ D.nd D.naut i) (r x)))
    (hN : ∀ x (K' : Type) [Field K'] (f : D.nd.O i →+* K') (f' : K' →+* Qbar (D.nd.l i)), f'.comp f = iotaOQ D.nd D.naut i →
      ∀ (d u : ℕ) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin d) K') (υ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin u) K')
        (h : d + d + u = D.R.nV) (Pm : GL (Fin D.R.nV) K'), 0 < d →
        (∀ g, ((Pm⁻¹ * mapRep f (r x) g * Pm : GL (Fin D.R.nV) K') : Matrix (Fin D.R.nV) (Fin D.R.nV) K') =
          Matrix.reindex (finCongr h) (finCongr h) ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) K') :
            Matrix (Fin (d + d + u)) (Fin (d + d + u)) K')) → False) : DistinctAbsIrredConstituents D.nd i r := by
  classical
  letI alg : Algebra (Kf D.nd i) (Qbar (D.nd.l i)) := (D.naut.iotaQ i).toAlgebra
  have hss : ∀ x, IsSSRep (mapRep (algebraMap (Kf D.nd i) (AlgebraicClosure (Kf D.nd i)))
      (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r x))) := by
    intro x
    let f : AlgebraicClosure (Kf D.nd i) →ₐ[Kf D.nd i] Qbar (D.nd.l i) := IsAlgClosed.lift
    letI : Algebra (AlgebraicClosure (Kf D.nd i)) (Qbar (D.nd.l i)) := f.toRingHom.toAlgebra
    apply SumRepresentations.isSSRep_descent (L := Qbar (D.nd.l i))
    have e : ((algebraMap (AlgebraicClosure (Kf D.nd i)) (Qbar (D.nd.l i))).comp
        (algebraMap (Kf D.nd i) (AlgebraicClosure (Kf D.nd i)))).comp (algebraMap (D.nd.O i) (Kf D.nd i)) =
        iotaOQ D.nd D.naut i := by
      ext z
      show f (algebraMap (Kf D.nd i) _ (algebraMap _ (Kf D.nd i) z)) = D.naut.iotaQ i (algebraMap _ _ z)
      rw [f.commutes]; rfl
    rw [← mapRep_comp, ← mapRep_comp, e]
    exact (hr x).2.1
  obtain ⟨K', hF, hA, hFD, hsplit⟩ :=
    GlobalTheory.T.exists_finiteDimensional_ext_irrSub_absIrr (fun x => mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r x)) hss
  refine ⟨K', hF, hA, hFD, fun x => ⟨?_, ?_⟩⟩
  · rw [mapRep_comp]; exact hsplit x
  · intro W₁ W₂ h1 h2 hdis hiso
    let f' : K' →ₐ[Kf D.nd i] Qbar (D.nd.l i) := IsAlgClosed.lift
    have e' : (f'.toRingHom).comp ((algebraMap (Kf D.nd i) K').comp (algebraMap (D.nd.O i) (Kf D.nd i))) =
        iotaOQ D.nd D.naut i := by
      ext z
      show f' (algebraMap (Kf D.nd i) K' (algebraMap _ (Kf D.nd i) z)) = D.naut.iotaQ i (algebraMap _ _ z)
      rw [f'.commutes]; rfl
    have hQ : mapRep f'.toRingHom (mapRep ((algebraMap (Kf D.nd i) K').comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) =
        mapRep (iotaOQ D.nd D.naut i) (r x) := by
      rw [← mapRep_comp, e']
    have hssK : IsSSRep (mapRep ((algebraMap (Kf D.nd i) K').comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) := by
      letI : Algebra K' (Qbar (D.nd.l i)) := f'.toRingHom.toAlgebra
      apply SumRepresentations.isSSRep_descent (L := Qbar (D.nd.l i))
      show IsSSRep (mapRep f'.toRingHom _)
      rw [hQ]; exact (hr x).2.1
    obtain ⟨d, u, σ, υ, h, Pm, hd, hrel⟩ := GlobalTheory.T.exists_conj_double_block_of_iso_subspaces _ W₁ W₂ hssK h1.2.1 h2.2.1 h1.1 hdis hiso
    exact hN x K' _ f'.toRingHom e' d u σ υ h Pm hd hrel

/- English proof (translation)
Establish `hr` using `fun x => GlobalTheory.T.isHeckeGaloisQ_of_isHeckeGalois' D i x (r x) (hg x)`. Use `constituentCondition_of_noRepeatedFactor D i r hr fun x K' _ f f' e' d u σ υ h Pm hd hrel => ?_` and prove the remaining obligations. Establish `hQ : mapRep f' (mapRep f (r x)) = mapRep (iotaOQ D.nd D.naut i) (r x)` using `by rw [← mapRep_comp, e']`. Establish `hrelQ` using `rel_map' f' h _ σ υ Pm hrel`. Rewrite `hrelQ` using `[hQ]`.

Establish `hcQ : SumRepresentations.At.ContQ D.nd i (mapRep (iotaOQ D.nd D.naut i) (r x))` using `(hr x).1`. Take `⟨hcA, hcυ⟩` from `continuous_blocks' _ _ _ h _ hrelQ hcQ`. Establish `hcσ : SumRepresentations.At.ContQ D.nd i (mapRep f' σ)` using `(continuous_blocks' (SumRepresentations.At.sumRep (mapRep f' σ) (mapRep f' σ)) (mapRep f' σ) (mapRep f' σ) rfl 1 (fun g => by simp) hcA).1`. Take `⟨P, hP⟩` from `D.naut.pt_surj i x`. Take `⟨τ, w, hτw⟩` from `GlobalTheory.T.exists_padicAlgCl_embedding_and_place_norm_lt_one D.host.E (D.nd.l i)`.

Establish `hpl : ∀ w', InducesW D.nd i τ w' → w' ∈ placesOver D.host.E (D.nd.l i)` using `fun w' hw' => mem_of_induces' D.host.E (D.nd.l i) τ w' hw'`. Establish `hτ : InducesW D.nd i τ w` using `hτw`. Establish `hJ` using `(hon x w (hpl w hτ)).2 τ hτ`. Use `jumps_not_nodup' D ht i τ w (hpl w hτ) hτ hpl h _ _ _ _ hd hcQ hcσ hcυ hrelQ (fun w' hw' => (hon x w' (hpl w' hw')).1) ?_` and prove the remaining obligations. Rewrite using `[hJ]`.

Conclude with `fixedJumps_nodup D i P τ`.
-/
theorem constituentCondition_of_hodgeJumps (D : D7) (ht : SumRepresentations.tie0 D) (i : D.nd.Loc)
    (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i))) (hg : GoodR D.nd i r)
    (hon : ∀ x, ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w ∧
      ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (r x)) τ = D.naut.locAutHodgeTateWeightsLevelZero i τ) :
    DistinctAbsIrredConstituents D.nd i r := by
  have hr := fun x => GlobalTheory.T.isHeckeGaloisQ_of_isHeckeGalois' D i x (r x) (hg x)
  refine constituentCondition_of_noRepeatedFactor D i r hr fun x K' _ f f' e' d u σ υ h Pm hd hrel => ?_
  have hQ : mapRep f' (mapRep f (r x)) = mapRep (iotaOQ D.nd D.naut i) (r x) := by rw [← mapRep_comp, e']
  have hrelQ := rel_map' f' h _ σ υ Pm hrel
  rw [hQ] at hrelQ
  have hcQ : SumRepresentations.At.ContQ D.nd i (mapRep (iotaOQ D.nd D.naut i) (r x)) := (hr x).1
  obtain ⟨hcA, hcυ⟩ := continuous_blocks' _ _ _ h _ hrelQ hcQ
  have hcσ : SumRepresentations.At.ContQ D.nd i (mapRep f' σ) :=
    (continuous_blocks' (SumRepresentations.At.sumRep (mapRep f' σ) (mapRep f' σ)) (mapRep f' σ) (mapRep f' σ) rfl 1 (fun g => by simp) hcA).1
  obtain ⟨P, hP⟩ := D.naut.pt_surj i x
  obtain ⟨τ, w, hτw⟩ := GlobalTheory.T.exists_padicAlgCl_embedding_and_place_norm_lt_one D.host.E (D.nd.l i)
  have hpl : ∀ w', InducesW D.nd i τ w' → w' ∈ placesOver D.host.E (D.nd.l i) :=
    fun w' hw' => mem_of_induces' D.host.E (D.nd.l i) τ w' hw'
  have hτ : InducesW D.nd i τ w := hτw
  have hJ := (hon x w (hpl w hτ)).2 τ hτ
  refine jumps_not_nodup' D ht i τ w (hpl w hτ) hτ hpl h _ _ _ _ hd hcQ hcσ hcυ hrelQ
    (fun w' hw' => (hon x w' (hpl w' hw')).1) ?_
  rw [hJ]; exact fixedJumps_nodup D i P τ

/- English proof (translation)
The claim follows from `constituentCondition_of_noRepeatedFactor D i r (fun x => GlobalTheory.T.isHeckeGaloisQ_of_isHeckeGalois' D i x (r x) (hg x)) fun x _ _ f f' e' _ _ σ υ h Pm hd hrel => noDouble_of_live D h5 i k hl hL r hg hb x f (by have := SumRepresentations.iotaOQ_injective D.nd D.naut i rw [← e …`.
-/
theorem constituentCondition_at_distinguishedPrime (D : D7) (h5 : SumRepresentations.adm5 D) (i : D.nd.Loc) (k : Fin 2) (hl : D.nd.l i = D.host.g k)
    (hL : GlobalTheory.CoefDuty.Live D.nd i) (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)))
    (hg : GoodR D.nd i r) (hb : ResidualCharpolyIndependent D.nd i r) : DistinctAbsIrredConstituents D.nd i r :=
  constituentCondition_of_noRepeatedFactor D i r (fun x => GlobalTheory.T.isHeckeGaloisQ_of_isHeckeGalois' D i x (r x) (hg x)) fun x _ _ f f' e' _ _ σ υ h Pm hd hrel =>
    noDouble_of_live D h5 i k hl hL r hg hb x f (by
      have := SumRepresentations.iotaOQ_injective D.nd D.naut i
      rw [← e'] at this
      exact Function.Injective.of_comp (f := f') this) σ υ h Pm hd hrel

/- English proof (translation)
Introduce `i x P Pa hP hPa ρ hρ`. Take `⟨ρ0, hc, hs, hw, hl⟩` from `isoRep D t0 a2 i P Pa hPa`. Take `⟨Pm, hPm⟩` from `GlobalTheory.T.heckeGaloisRepQbar_conjugate_unique D a5 i x ρ0 ρ (heckeQ D i x P Pa hP hPa ρ0 hc hs hw) hρ`. Take `⟨c1, c2, c3⟩` from `(t0.2.2.2.2.2 i).2.1 _ ρ0 ρ hc Pm hPm`. Use `⟨fun w h => by rw [c2 w (Or.inl h)]; exact hw w h, fun w h hn => ⟨(c1 w h).2 (hl w h hn).1, by rw [c2 w (Or.inr (hl w h hn).1)]; exact (hl w h hn).2.1, fun τ hτ => ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[c3 τ, (hl w h hn).2.2 τ hτ]`. Introduce `w' hw'`. Rewrite using `[ind_unique hτ hw']`. Conclude with `(hl _ h hn).1`.
-/
theorem lgc (D : D7) (t0 : SumRepresentations.tie0 D) (a2 : AutomorphicGaloisAdmissible D.nd D.naut) (a5 : SumRepresentations.adm5 D) : large₂ D := by
  intro i x P Pa hP hPa ρ hρ
  obtain ⟨ρ0, hc, hs, hw, hl⟩ := isoRep D t0 a2 i P Pa hPa
  obtain ⟨Pm, hPm⟩ := GlobalTheory.T.heckeGaloisRepQbar_conjugate_unique D a5 i x ρ0 ρ (heckeQ D i x P Pa hP hPa ρ0 hc hs hw) hρ
  obtain ⟨c1, c2, c3⟩ := (t0.2.2.2.2.2 i).2.1 _ ρ0 ρ hc Pm hPm
  refine ⟨fun w h => by rw [c2 w (Or.inl h)]; exact hw w h, fun w h hn => ⟨(c1 w h).2 (hl w h hn).1,
    by rw [c2 w (Or.inr (hl w h hn).1)]; exact (hl w h hn).2.1, fun τ hτ => ?_⟩⟩
  rw [c3 τ, (hl w h hn).2.2 τ hτ]
  intro w' hw'
  rw [ind_unique hτ hw']
  exact (hl _ h hn).1

def HeckeGaloisFamilyProperties (D : D7) : Prop := ∀ i : D.nd.Loc,
  ((∃ rq : D.nd.X i → (G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i))), ∀ x, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (rq x)) ∧
    ∃ r, GoodR D.nd i r) ∧
  (∀ P P' : D.naut.AV i, D.naut.ptV i P ≠ none → D.naut.ptV i P = D.naut.ptV i P' →
    (∀ Pa Pa', IsBCV D.nd D.naut i P Pa → IsBCV D.nd D.naut i P' Pa' → Pa.Perm Pa') ∧
    ∀ w, w ∉ D.nd.S i → w ∉ D.nd.Q i →
      (IsSplitPl D.host w → D.naut.locV i P w = D.naut.locV i P' w) ∧
      (¬ IsSplitPl D.host w → ubc D.R.nV (D.naut.satV i P w) = ubc D.R.nV (D.naut.satV i P' w))) ∧
  ∀ r, GoodR D.nd i r → SumRepresentations.At.G1 D.nd i r ∧ G2a D.nd D.naut i r ∧ G3 D.nd i r ∧ SumRepresentations.At.G4 D.nd i r

/- English proof (translation)
Establish `ex : ∀ (i : D.nd.Loc) (x : D.nd.X i), ∃ ρ, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ` using `fun i x => by`. Take `⟨P, hP⟩` from `D.naut.pt_surj i x`. Take `⟨Pa, hPa⟩` from `a1 i P`. Take `⟨ρ, hc, hs, hw, -⟩` from `isoRep D t0 a2 i P Pa hPa`. Conclude with `⟨ρ, heckeQ D i x P Pa hP hPa ρ hc hs hw⟩`.

Establish `lg` using `lgc D t0 a2 a5`. Introduce `i`. Establish `exq : ∃ rq : D.nd.X i → (G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i))), ∀ x, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (rq x)` using `⟨fun x => (ex i x).choose, fun x => (ex i x).choose_spec⟩`. Use `⟨⟨exq, SumRepresentations.exists_GoodR D.nd D.naut hO i exq⟩, point_determines D a1 a5 ex lg i, fun r hr => ?_⟩` and prove the remaining obligations. Establish `he` using `fun x => GlobalTheory.T.isHeckeGaloisQ_of_isHeckeGalois' D i x (r x) (hr x)`.

Establish `g1 : SumRepresentations.At.G1 D.nd i r` using `SumRepresentations.charpoly_clause_of_chebotarev D.nd a5.2.2.1 i r hr`. Establish `gb : ResidualCharpolyIndependent D.nd i r` using `SumRepresentations.residual_charpoly_of_chebotarev_clause D.nd i r g1`. Establish `cu` using `crys_unram_of_lgc D t0 a1 lg i r he`. Use `⟨g1, cu.1, ⟨fun hg => ?_, gb⟩, cu.2⟩` and prove the remaining obligations. Distinguish the cases in `hl : D.nd.l i ≠ D.host.g 0 ∧ D.nd.l i ≠ D.host.g 1`.

Use `constituentCondition_of_hodgeJumps D t0 i r hr fun x w hw => ?_` and prove the remaining obligations. Take `⟨P, hP⟩` from `D.naut.pt_surj i x`. Take `⟨Pa, hPa⟩` from `a1 i P`. Establish `h` using `(lg i x P Pa hP hPa _ (he x)).2 w hw (Nc.of_unr (iso_unr_l D i P Pa w hPa hw hl.1 hl.2))`. Conclude with `⟨h.1, h.2.2⟩`.

Establish `hL` using `hg.resolve_left hl`. Distinguish the cases in `h0 : D.nd.l i = D.host.g 0`. Conclude with `constituentCondition_at_distinguishedPrime D a5 i 0 h0 hL r hr gb`. Conclude with `constituentCondition_at_distinguishedPrime D a5 i 1 (by by_contra h1; exact hl ⟨h0, h1⟩) hL r hr gb`.
-/
theorem heckeGaloisFamilyProperties_of_admissible (D : D7) (t0 : SumRepresentations.tie0 D) (hO : SumRepresentations.hypO D) (a1 : SumRepresentations.adm1 D) (a2 : AutomorphicGaloisAdmissible D.nd D.naut) (a5 : SumRepresentations.adm5 D) :
    HeckeGaloisFamilyProperties D := by
  have ex : ∀ (i : D.nd.Loc) (x : D.nd.X i), ∃ ρ, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ := fun i x => by
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hPa⟩ := a1 i P
    obtain ⟨ρ, hc, hs, hw, -⟩ := isoRep D t0 a2 i P Pa hPa
    exact ⟨ρ, heckeQ D i x P Pa hP hPa ρ hc hs hw⟩
  have lg := lgc D t0 a2 a5
  intro i
  have exq : ∃ rq : D.nd.X i → (G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i))),
      ∀ x, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (rq x) := ⟨fun x => (ex i x).choose, fun x => (ex i x).choose_spec⟩
  refine ⟨⟨exq, SumRepresentations.exists_GoodR D.nd D.naut hO i exq⟩, point_determines D a1 a5 ex lg i, fun r hr => ?_⟩
  have he := fun x => GlobalTheory.T.isHeckeGaloisQ_of_isHeckeGalois' D i x (r x) (hr x)
  have g1 : SumRepresentations.At.G1 D.nd i r := SumRepresentations.charpoly_clause_of_chebotarev D.nd a5.2.2.1 i r hr
  have gb : ResidualCharpolyIndependent D.nd i r := SumRepresentations.residual_charpoly_of_chebotarev_clause D.nd i r g1
  have cu := crys_unram_of_lgc D t0 a1 lg i r he
  refine ⟨g1, cu.1, ⟨fun hg => ?_, gb⟩, cu.2⟩
  by_cases hl : D.nd.l i ≠ D.host.g 0 ∧ D.nd.l i ≠ D.host.g 1
  · refine constituentCondition_of_hodgeJumps D t0 i r hr fun x w hw => ?_
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hPa⟩ := a1 i P
    have h := (lg i x P Pa hP hPa _ (he x)).2 w hw (Nc.of_unr (iso_unr_l D i P Pa w hPa hw hl.1 hl.2))
    exact ⟨h.1, h.2.2⟩
  · have hL := hg.resolve_left hl
    by_cases h0 : D.nd.l i = D.host.g 0
    · exact constituentCondition_at_distinguishedPrime D a5 i 0 h0 hL r hr gb
    · exact constituentCondition_at_distinguishedPrime D a5 i 1 (by by_contra h1; exact hl ⟨h0, h1⟩) hL r hr gb

/- English proof (translation)
The claim follows from `(fun _ _ _ => (SumRepresentations.proposition_families_iff D a5 hO).2 (GlobalTheory.NRows.Parts.h41 D a)) t0 a1 a2`.
-/
theorem p41 (D : D7) (t0 : SumRepresentations.tie0 D) (hO : SumRepresentations.hypO D) (a1 : SumRepresentations.adm1 D) (a2 : SumRepresentations.adm2 D) (a5 : SumRepresentations.adm5 D)
    (a : SumRepresentations.AdmAt D) : SumRepresentations.Conclusion41 D := (fun _ _ _ => (SumRepresentations.proposition_families_iff D a5 hO).2 (GlobalTheory.NRows.Parts.h41 D a)) t0 a1 a2

/- English proof (translation)
Introduce `D a t s hk l th g` and use `⟨p41 D a.1.1 a.1.2.1 a.1.2.2.1 a.1.2.2.2.1 a.1.2.2.2.2.2.2 a, g, (SumRepresentations.proposition_parameters_iff_reduced D t).2 (GlobalTheory.NRows.Parts.h42 D a s hk l th)⟩`.
-/
theorem main : ∀ D : D7, GlobalTheory.NRows.PartsGive D := fun D a t s hk l th g =>
  ⟨p41 D a.1.1 a.1.2.1 a.1.2.2.1 a.1.2.2.2.1 a.1.2.2.2.2.2.2 a, g, (SumRepresentations.proposition_parameters_iff_reduced D t).2 (GlobalTheory.NRows.Parts.h42 D a s hk l th)⟩

end UpperTheory.GalS.Parts

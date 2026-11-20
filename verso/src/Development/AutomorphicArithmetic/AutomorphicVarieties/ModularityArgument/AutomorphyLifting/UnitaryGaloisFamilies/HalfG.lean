import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.IrrCaseT
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HalfOfCompatiblePolarization

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `hTw hC E Ω _ _ _ _ _ _ l _ ι a ha P hP ρ hρ m hm e he`. Use `set s : ℝ := ((e + a - 1 : ℤ) : ℝ) / 2 with hs`. Establish `hsC : (s : ℂ) = (e : ℂ) / 2 + ((a : ℂ) - 1) / 2`. Rewrite using `[hs]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hν` using `GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s`. Establish `hinf : ∀ τ, (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).infChar τ = (m τ).map (· + (s : ℂ))` using `fun τ => by`. Establish `h1` using `(hm τ).twist (GlobalTheory.HeckeGal.Model.absPow E s)`. Rewrite `h1` using `[(InfType.expo_of_infType E _).2.1 s hν τ]`.

Conclude with `CG.HasInfChar.infChar_eq (π := CG.mk _) h1`. Establish `hreg : (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).IsRegAlg` using `(GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by`. Rewrite using `[hinf]`. Use `⟨(he τ).1.map (add_left_injective _), fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, rfl⟩` from `Multiset.mem_map.1 hz`.

Take `⟨j, hj⟩` from `(he τ).2 y hy`. Conclude with `⟨j, by rw [hsC, ← hj]; ring⟩`. Use `choose σ hσ hcl using fun w => hTw E a P s w (ρ w) (hρ w)`. Take `⟨r, HT, hr, hHT⟩` from `hC E Ω l ι a ha _ _ hreg (GlobalTheory.HeightCounting.Blocks.isPolarized_twist_absPow hP s) σ hσ`. Establish `key : ∀ w (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRecT h rc → rc (algNorm (σ w)) = (rc (cl (ρ w))).lpTw ((e : ℝ) / 2)`.

Introduce `w A h rc hrc`. Take `⟨_, _, L⟩` from `hrc`. Rewrite using `[← L.nu]`. Use `congrArg rc ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(cl (σ w)).nu _ = _`.

Rewrite using `[hcl, IrrGL.nu_nu]`. Use `congr 1`. Rewrite using `[hsC]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨r, HT, ⟨hr.cont, hr.ss, fun w hg => hr.ht w fun A h rc hrc => ?_, fun w A h rc hrc => key w A h rc hrc ▸ hr.par w A h rc hrc⟩, fun τ => ?_⟩` and prove the remaining obligations. Use `hg A h rc hrc` as an intermediate fact. Simplify using `only [key w A h rc hrc]`. Conclude with `this`. Rewrite using `[hHT, hinf, Multiset.map_map]`.

Use `Multiset.map_congr rfl fun z _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, hsC]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Z.Win.Gu.halfG :
    TwistLoc → PolG → HalfG := by
  intro hTw hC E Ω _ _ _ _ _ _ l _ ι a ha P hP ρ hρ m hm e he
  set s : ℝ := ((e + a - 1 : ℤ) : ℝ) / 2 with hs
  have hsC : (s : ℂ) = (e : ℂ) / 2 + ((a : ℂ) - 1) / 2 := by
    rw [hs]; push_cast; ring
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s
  have hinf : ∀ τ, (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).infChar τ = (m τ).map (· + (s : ℂ)) := fun τ => by
    have h1 := (hm τ).twist (GlobalTheory.HeckeGal.Model.absPow E s)
    rw [(InfType.expo_of_infType E _).2.1 s hν τ] at h1
    exact CG.HasInfChar.infChar_eq (π := CG.mk _) h1
  have hreg : (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    rw [hinf]
    refine ⟨(he τ).1.map (add_left_injective _), fun z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    obtain ⟨j, hj⟩ := (he τ).2 y hy
    exact ⟨j, by rw [hsC, ← hj]; ring⟩
  choose σ hσ hcl using fun w => hTw E a P s w (ρ w) (hρ w)
  obtain ⟨r, HT, hr, hHT⟩ := hC E Ω l ι a ha _ _ hreg (GlobalTheory.HeightCounting.Blocks.isPolarized_twist_absPow hP s) σ hσ
  have key : ∀ w (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRecT h rc →
      rc (algNorm (σ w)) = (rc (cl (ρ w))).lpTw ((e : ℝ) / 2) := by
    intro w A h rc hrc
    obtain ⟨_, _, L⟩ := hrc
    rw [← L.nu]
    refine congrArg rc ?_
    change (cl (σ w)).nu _ = _
    rw [hcl, IrrGL.nu_nu]
    congr 1
    rw [hsC]; push_cast; ring
  refine ⟨r, HT, ⟨hr.cont, hr.ss, fun w hg => hr.ht w fun A h rc hrc => ?_,
    fun w A h rc hrc => key w A h rc hrc ▸ hr.par w A h rc hrc⟩, fun τ => ?_⟩
  · have := hg A h rc hrc
    simp only [key w A h rc hrc]
    exact this
  · rw [hHT, hinf, Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply, hsC]; ring

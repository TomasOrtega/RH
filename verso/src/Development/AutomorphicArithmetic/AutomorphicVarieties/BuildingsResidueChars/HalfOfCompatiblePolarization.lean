import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.CsdTwist
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DualIsConjOfIsCsd
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open UpperTheory.V.Af UpperTheory.V.Af.Gu

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `H hEta hTw hC E Ω _ _ _ _ _ _ l _ ι a ha P hP ρ hρ m hm e he`. Take `⟨ξ, mξ, hξ, hN⟩` from `hEta E (e + a - 1)`. Use `set s : ℝ := ((e + a - 1 : ℤ) : ℝ) / 2 with hs`. Establish `hsC : (s : ℂ) = (e : ℂ) / 2 + ((a : ℂ) - 1) / 2`. Rewrite using `[hs]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hν` using `GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s`. Establish `hinf : ∀ τ, (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).infChar τ = (m τ).map (· + (s : ℂ))` using `fun τ => by`. Establish `h1` using `(hm τ).twist (GlobalTheory.HeckeGal.Model.absPow E s)`.

Rewrite `h1` using `[(InfType.expo_of_infType E _).2.1 s hν τ]`. Conclude with `CG.HasInfChar.infChar_eq (π := CG.mk _) h1`. Establish `hreg : (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).IsRegAlg` using `(GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by`. Rewrite using `[hinf]`. Use `⟨(he τ).1.map (add_left_injective _), fun z hz => ?_⟩` and prove the remaining obligations.

Take `⟨y, hy, rfl⟩` from `Multiset.mem_map.1 hz`. Take `⟨j, hj⟩` from `(he τ).2 y hy`. Conclude with `⟨j, by rw [hsC, ← hj]; ring⟩`. Establish `hd : GlobalTheory.ContraPair.DualIsConj ((P.twist (GlobalTheory.HeckeGal.Model.absPow E s)).twist ξ)`. Rewrite using `[← CuspSub.twist_mul]`.

Conclude with `Cq.csdTwist E a P 1 _ ((GlobalTheory.ContraPair.dualIsConjBy_one P).2 (GlobalTheory.LocGlobDual.Model.dualIsConj_of_isCsd (H.litN.aut.gk E a P) hP)) (by rw [hN, inv_one])`. Use `choose σ hσ hcl using fun w => hTw E a P s w (ρ w) (hρ w)`. Take `⟨r, HT, hr, hHT⟩` from `hC E Ω l ι a ha _ _ ξ mξ hreg (GlobalTheory.HeightCounting.Blocks.isPolarized_twist_absPow hP s) hξ hd σ hσ`. Use `⟨r, HT, ⟨hr.cont, hr.ss, hr.ht, fun w => (hr.par w).congr fun A h rc hrc => ?_⟩, fun τ => ?_⟩` and prove the remaining obligations. Take `⟨_, _, _, -, L⟩` from `hrc`.

Rewrite using `[← L.nu_eq]`. Use `congrArg rc ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(cl (σ w)).nu _ = _`. Rewrite using `[hcl, IrrGL.nu_nu]`. Use `congr 1`.

Rewrite using `[hsC]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hHT, hinf, Multiset.map_map]`. Use `Multiset.map_congr rfl fun z _ => ?_` and prove the remaining obligations.

Simplify using `only [Function.comp_apply, hsC]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.half_of_compatible_polarization :
    HypothesesH → Eta → TwistLoc → CompatPol → Half := by
  intro H hEta hTw hC E Ω _ _ _ _ _ _ l _ ι a ha P hP ρ hρ m hm e he
  obtain ⟨ξ, mξ, hξ, hN⟩ := hEta E (e + a - 1)
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
  have hd : GlobalTheory.ContraPair.DualIsConj ((P.twist (GlobalTheory.HeckeGal.Model.absPow E s)).twist ξ) := by
    rw [← CuspSub.twist_mul]
    exact Cq.csdTwist E a P 1 _ ((GlobalTheory.ContraPair.dualIsConjBy_one P).2
      (GlobalTheory.LocGlobDual.Model.dualIsConj_of_isCsd (H.litN.aut.gk E a P) hP)) (by rw [hN, inv_one])
  choose σ hσ hcl using fun w => hTw E a P s w (ρ w) (hρ w)
  obtain ⟨r, HT, hr, hHT⟩ := hC E Ω l ι a ha _ _ ξ mξ hreg (GlobalTheory.HeightCounting.Blocks.isPolarized_twist_absPow hP s) hξ hd σ hσ
  refine ⟨r, HT, ⟨hr.cont, hr.ss, hr.ht, fun w => (hr.par w).congr fun A h rc hrc => ?_⟩, fun τ => ?_⟩
  · obtain ⟨_, _, _, -, L⟩ := hrc
    rw [← L.nu_eq]
    refine congrArg rc ?_
    change (cl (σ w)).nu _ = _
    rw [hcl, IrrGL.nu_nu]
    congr 1
    rw [hsC]; push_cast; ring
  · rw [hHT, hinf, Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply, hsC]; ring

import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIntTwoCocycleEqPowSmulOfReductionCoboundary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicCoboundaryOfDivisible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousTwoCocycleMultipleOfFundamental
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalTwoCocycleOfLocalTateDualityStatement

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

noncomputable section

namespace GlobalTheory.IntTateTop

open GlobalTheory.TateTop GlobalTheory.PadicH2Separated

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Establish `hG` using `fun r => GlobalTheory.GenSpan.gen_zmod (hgen r)`. Establish `hcc : Continuous c` using `continuous_of_reductions c fun s => (hG (s + 1)).1.1.continuous`. Establish `hcoc : ∀ g h k, (χ g : ℤ_[l]) * c (h, k) - c (g * h, k) + c (g, h * k) - c (g, h) = 0`. Introduce `g h k`.

Rewrite using `[← PadicInt.ext_of_toZModPow]`. Introduce `n`. Simplify `(hG n).1.2 g h k` using `only [map_sub, map_add, map_mul, map_zero]`. Establish `hlev : ∀ r, ∃ (x : ZMod (l ^ r)) (b : G → ZMod (l ^ r)), IsLocallyConstant b ∧ ∀ p, PadicInt.toZModPow r (w p) = PadicInt.toZModPow r (c p) * x + (PadicInt.toZModPow r (χ p.1 : ℤ_[l]) * b p.2 - b (p.1 * p.2) + b p.1)` using `fun r => (hG r).2.1 _ ((IsLocallyConstant.iff_continuous _).2 ((continuous_reduction r).comp hwc)) fun g k m => by`. Simplify `congrArg (PadicInt.toZModPow r) (hwcoc g k m)` using `only [map_sub, map_add, map_mul, map_zero]`.

Use `choose X B hB hXB using hlev`. Establish `hred : ∀ r, PadicInt.toZModPow r (((X r).val : ℕ) : ℤ_[l]) = X r` using `fun r => by`. Establish `: NeZero (l ^ r)` using `⟨pow_ne_zero _ hl.ne_zero⟩`. Rewrite using `[map_natCast, ZMod.natCast_zmod_val]`. Establish `hcomp : ∀ r, ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) (X (r + 1)) = X r`.

Introduce `r`. Use `set ψ := ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))`. Establish `hψ : ∀ a : ℤ_[l], ψ (PadicInt.toZModPow (r + 1) a) = PadicInt.toZModPow r a` using `fun a => by`. Rewrite using `[ZMod.castHom_apply]`. Conclude with `PadicInt.cast_toZModPow r (r + 1) (Nat.le_succ r) a`.

Rewrite using `[← sub_eq_zero]`. Use `(hG r).2.2 _ (fun g => B r g - ψ (B (r + 1) g)) ((hB r).sub ((hB (r + 1)).comp ψ)) fun p => ?_` and prove the remaining obligations. Establish `e1 : PadicInt.toZModPow r (w p) = PadicInt.toZModPow r (c p) * ψ (X (r + 1)) + (PadicInt.toZModPow r (χ p.1 : ℤ_[l]) * ψ (B (r + 1) p.2) - ψ (B (r + 1) (p.1 * p.2)) + ψ (B (r + 1) p.1))`. Use `congrArg ψ (hXB (r + 1) p)` as an intermediate fact. Simplify `this` using `only [map_add, map_sub, map_mul, hψ]`.

Establish `e2` using `hXB r p`. Use `show PadicInt.toZModPow r (c p) * (ψ (X (r + 1)) - X r) = PadicInt.toZModPow r (χ p.1 : ℤ_[l]) * (B r p.2 - ψ (B (r + 1) p.2)) - (B r (p.1 * p.2) - ψ (B (r + 1) (p.1 * p.2))) + (B r p.1 - ψ (B (r + 1) p.1))`. Take the linear combination `e2 - e1`. Take `⟨x, hx⟩` from `exists_lim (fun r => (((X r).val : ℕ) : ℤ_[l])) fun r => by`. Rewrite using `[dvd_iff_toZModPow, map_sub, hred, ← PadicInt.cast_toZModPow r (r + 1) (Nat.le_succ r), hred]`.

Conclude with `sub_eq_zero.2 (hcomp r)`. Establish `hxr : ∀ r, PadicInt.toZModPow r x = X r` using `fun r => by`. Use `(dvd_iff_toZModPow _).1 (hx r)` as an intermediate fact. Rewrite `this` using `[map_sub, hred, sub_eq_zero]`. Then use the resulting hypothesis. Establish `hcont : ContAction (charRep χ)` using `by show Continuous fun p : G × ℤ_[l] => charRep χ p.1 p.2`.

Simplify using `only [charRep_apply]`. Conclude with `(hχ.comp continuous_fst).mul continuous_snd`. Establish `hcompat : ∀ (r : ℕ) (g : G) (a : ℤ_[l]), PadicInt.toZModPow r (charRep χ g a) = charRep ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ) g (PadicInt.toZModPow r a)` using `fun r g a => by`. Simplify using `[charRep_apply]`. Establish `hyZ : (fun p => w p - x * c p) ∈ Z2 (charRep χ)`.

Use `(mem_cocycles2 _ _).2 ⟨hwc.sub (continuous_const.mul hcc), fun g h k => ?_⟩` and prove the remaining obligations. Simplify using `only [charRep_apply]`. Take the linear combination `hwcoc g h k - x * hcoc g h k`. Establish `hyB : ∀ r, (fun p => PadicInt.toZModPow r (w p - x * c p)) ∈ B2 (charRep ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ))`. Introduce `r`.

Use `(separated_dvr_second_cohomology_mem _ _).2 ⟨B r, (hB r).continuous, funext fun p => ?_⟩` and prove the remaining obligations. Take `⟨g, h⟩` from `p`. Simplify using `only [d1_apply, charRep_apply, MonoidHom.comp_apply, Units.coe_map, map_sub, map_mul, hxr]`. Establish `e` using `hXB r (g, h)`. Simplify using `only at e`.

Simplify using `only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]`. Take the linear combination `-e`. Establish `hker : ∀ r : ℕ, ∃ w' ∈ Z2 (charRep χ), (fun p => w p - x * c p) - (l : ℤ_[l]) ^ r • w' ∈ B2 (charRep χ)` using `fun r => GlobalTheory.padicInt_two_cocycle_eq_pow_smul_of_reduction_coboundary l G (charRep χ) hcont r _ (hcompat r) _ hyZ (hyB r)`. Take `⟨f, hf, hfd⟩` from `(separated_dvr_second_cohomology_mem _ _).1 (mem_coboundaries_of_forall_pow l G (charRep χ) _ hcompat hfin _ hyZ hker)`. Use `⟨x, f, hf, fun g h => ?_⟩` and prove the remaining obligations.

Establish `e` using `congrFun hfd (g, h)`. Simplify using `only [d1_apply, charRep_apply] at e`. Take the linear combination `e`.
-/
theorem int_span [IsTopologicalGroup G] [CompactSpace G] (χ : G →* ℤ_[l]ˣ) (c : G × G → ℤ_[l])
    (hχ : Continuous (fun g => (χ g : ℤ_[l]))) (hgen : ∀ r, Gen χ r c)
    (hfin : ∀ r : ℕ, 0 < r → Finite (ReciprocityTheory.Gal.H1 (ReciprocityTheory.Gal.charRep
      ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ))))
    (w : G × G → ℤ_[l]) (hwc : Continuous w)
    (hwcoc : ∀ g h k, (χ g : ℤ_[l]) * w (h, k) - w (g * h, k) + w (g, h * k) - w (g, h) = 0) :
    ∃ (x : ℤ_[l]) (f : G → ℤ_[l]), Continuous f ∧
      ∀ g h, (χ g : ℤ_[l]) * f h - f (g * h) + f g = w (g, h) - x * c (g, h) := by
  have hl : l.Prime := Fact.out
  have hG := fun r => GlobalTheory.GenSpan.gen_zmod (hgen r)
  have hcc : Continuous c := continuous_of_reductions c fun s => (hG (s + 1)).1.1.continuous
  have hcoc : ∀ g h k, (χ g : ℤ_[l]) * c (h, k) - c (g * h, k) + c (g, h * k) - c (g, h) = 0 := by
    intro g h k
    rw [← PadicInt.ext_of_toZModPow]
    intro n
    simpa only [map_sub, map_add, map_mul, map_zero] using (hG n).1.2 g h k
  have hlev : ∀ r, ∃ (x : ZMod (l ^ r)) (b : G → ZMod (l ^ r)), IsLocallyConstant b ∧ ∀ p,
      PadicInt.toZModPow r (w p) = PadicInt.toZModPow r (c p) * x +
        (PadicInt.toZModPow r (χ p.1 : ℤ_[l]) * b p.2 - b (p.1 * p.2) + b p.1) := fun r =>
    (hG r).2.1 _ ((IsLocallyConstant.iff_continuous _).2 ((continuous_reduction r).comp hwc))
      fun g k m => by
        simpa only [map_sub, map_add, map_mul, map_zero] using
          congrArg (PadicInt.toZModPow r) (hwcoc g k m)
  choose X B hB hXB using hlev
  have hred : ∀ r, PadicInt.toZModPow r (((X r).val : ℕ) : ℤ_[l]) = X r := fun r => by
    have : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.ne_zero⟩
    rw [map_natCast, ZMod.natCast_zmod_val]
  have hcomp : ∀ r, ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) (X (r + 1)) = X r := by
    intro r
    set ψ := ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))
    have hψ : ∀ a : ℤ_[l], ψ (PadicInt.toZModPow (r + 1) a) = PadicInt.toZModPow r a := fun a => by
      rw [ZMod.castHom_apply]
      exact PadicInt.cast_toZModPow r (r + 1) (Nat.le_succ r) a
    rw [← sub_eq_zero]
    refine (hG r).2.2 _ (fun g => B r g - ψ (B (r + 1) g)) ((hB r).sub ((hB (r + 1)).comp ψ))
      fun p => ?_
    have e1 : PadicInt.toZModPow r (w p) = PadicInt.toZModPow r (c p) * ψ (X (r + 1)) +
        (PadicInt.toZModPow r (χ p.1 : ℤ_[l]) * ψ (B (r + 1) p.2) - ψ (B (r + 1) (p.1 * p.2)) +
          ψ (B (r + 1) p.1)) := by
      have := congrArg ψ (hXB (r + 1) p)
      simpa only [map_add, map_sub, map_mul, hψ] using this
    have e2 := hXB r p
    show PadicInt.toZModPow r (c p) * (ψ (X (r + 1)) - X r) =
      PadicInt.toZModPow r (χ p.1 : ℤ_[l]) * (B r p.2 - ψ (B (r + 1) p.2)) -
        (B r (p.1 * p.2) - ψ (B (r + 1) (p.1 * p.2))) + (B r p.1 - ψ (B (r + 1) p.1))
    linear_combination e2 - e1
  obtain ⟨x, hx⟩ := exists_lim (fun r => (((X r).val : ℕ) : ℤ_[l])) fun r => by
    rw [dvd_iff_toZModPow, map_sub, hred, ← PadicInt.cast_toZModPow r (r + 1) (Nat.le_succ r),
      hred]
    exact sub_eq_zero.2 (hcomp r)
  have hxr : ∀ r, PadicInt.toZModPow r x = X r := fun r => by
    have := (dvd_iff_toZModPow _).1 (hx r)
    rwa [map_sub, hred, sub_eq_zero] at this
  have hcont : ContAction (charRep χ) := by
    show Continuous fun p : G × ℤ_[l] => charRep χ p.1 p.2
    simp only [charRep_apply]
    exact (hχ.comp continuous_fst).mul continuous_snd
  have hcompat : ∀ (r : ℕ) (g : G) (a : ℤ_[l]), PadicInt.toZModPow r (charRep χ g a) =
      charRep ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ) g
        (PadicInt.toZModPow r a) := fun r g a => by
    simp [charRep_apply]
  have hyZ : (fun p => w p - x * c p) ∈ Z2 (charRep χ) := by
    refine (mem_cocycles2 _ _).2 ⟨hwc.sub (continuous_const.mul hcc), fun g h k => ?_⟩
    simp only [charRep_apply]
    linear_combination hwcoc g h k - x * hcoc g h k
  have hyB : ∀ r, (fun p => PadicInt.toZModPow r (w p - x * c p)) ∈
      B2 (charRep ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ)) := by
    intro r
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨B r, (hB r).continuous, funext fun p => ?_⟩
    obtain ⟨g, h⟩ := p
    simp only [d1_apply, charRep_apply, MonoidHom.comp_apply, Units.coe_map, map_sub, map_mul, hxr]
    have e := hXB r (g, h)
    simp only at e
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    linear_combination -e
  have hker : ∀ r : ℕ, ∃ w' ∈ Z2 (charRep χ), (fun p => w p - x * c p) - (l : ℤ_[l]) ^ r • w' ∈
      B2 (charRep χ) := fun r =>
    GlobalTheory.padicInt_two_cocycle_eq_pow_smul_of_reduction_coboundary l G (charRep χ) hcont r _
      (hcompat r) _ hyZ (hyB r)
  obtain ⟨f, hf, hfd⟩ := (separated_dvr_second_cohomology_mem _ _).1
    (mem_coboundaries_of_forall_pow l G (charRep χ) _ hcompat hfin _ hyZ hker)
  refine ⟨x, f, hf, fun g h => ?_⟩
  have e := congrFun hfd (g, h)
  simp only [d1_apply, charRep_apply] at e
  linear_combination e

/- English proof (translation)
Rewrite using `[← PadicInt.ext_of_toZModPow]`. Introduce `n`. Rewrite using `[map_zero]`. Use `(GlobalTheory.GenSpan.gen_zmod (hgen n)).2.2 (PadicInt.toZModPow n x) (fun g => PadicInt.toZModPow n (f g)) ((IsLocallyConstant.iff_continuous _).2 ((continuous_reduction n).comp hf)) fun p => ?_` and prove the remaining obligations. Establish `e` using `congrArg (PadicInt.toZModPow (p := l) n) (h p.1 p.2)`.

Simplify using `only [map_sub, map_add, map_mul] at e`. Take the linear combination `-e`.
-/
theorem int_inj (χ : G →* ℤ_[l]ˣ) (c : G × G → ℤ_[l]) (hgen : ∀ r, Gen χ r c) (x : ℤ_[l])
    (f : G → ℤ_[l]) (hf : Continuous f)
    (h : ∀ g k, (χ g : ℤ_[l]) * f k - f (g * k) + f g = x * c (g, k)) : x = 0 := by
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  rw [map_zero]
  refine (GlobalTheory.GenSpan.gen_zmod (hgen n)).2.2 (PadicInt.toZModPow n x)
    (fun g => PadicInt.toZModPow n (f g))
    ((IsLocallyConstant.iff_continuous _).2 ((continuous_reduction n).comp hf)) fun p => ?_
  have e := congrArg (PadicInt.toZModPow (p := l) n) (h p.1 p.2)
  simp only [map_sub, map_add, map_mul] at e
  linear_combination -e

end GlobalTheory.IntTateTop

namespace GlobalTheory.IntTateTop

open GlobalTheory.TateTop Formalism.BasicNotions.Loc GlobalTheory.PadicH2Separated

/- English proof (translation)
Set `Φ : R →ₗ[R] M ⧸ N` to `N.mkQ.comp (LinearMap.toSpanSingleton R M z0)`. Establish `h1 : Function.Injective Φ` using `(injective_iff_map_eq_zero Φ).2 fun a ha => hinj a ((Submodule.Quotient.mk_eq_zero N).1 ha)`. Establish `h2 : Function.Surjective Φ`. Introduce `q`. Proceed by induction on `q using Submodule.Quotient.induction_on with`.

Consider the case `H z`. Take `⟨a, ha⟩` from `hsurj z`. Conclude with `⟨a, ((Submodule.Quotient.eq N).2 ha).symm⟩`. Conclude with `⟨(LinearEquiv.ofBijective Φ ⟨h1, h2⟩).symm⟩`.
-/
theorem nonempty_quot_equiv {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (N : Submodule R M)
    (z0 : M) (hinj : ∀ a : R, a • z0 ∈ N → a = 0) (hsurj : ∀ z : M, ∃ a : R, z - a • z0 ∈ N) :
    Nonempty ((M ⧸ N) ≃ₗ[R] R) := by
  let Φ : R →ₗ[R] M ⧸ N := N.mkQ.comp (LinearMap.toSpanSingleton R M z0)
  have h1 : Function.Injective Φ := (injective_iff_map_eq_zero Φ).2 fun a ha =>
    hinj a ((Submodule.Quotient.mk_eq_zero N).1 ha)
  have h2 : Function.Surjective Φ := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H z =>
      obtain ⟨a, ha⟩ := hsurj z
      exact ⟨a, ((Submodule.Quotient.eq N).2 ha).symm⟩
  exact ⟨(LinearEquiv.ofBijective Φ ⟨h1, h2⟩).symm⟩

variable {l : ℕ} [Fact l.Prime]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Use `haveI : FiniteDimensional ℚ_[l] ↥Lf.1 := Lf.2`. Use `haveI : IsIntegralClosure ↥(OL Lf) ℤ_[l] ↥Lf.1 := integralClosure.isIntegralClosure _ _`. Use `haveI : FaithfulSMul ℤ_[l] ↥Lf.1 := by`. Rewrite using `[faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥Lf.1]`. Conclude with `(algebraMap ℚ_[l] ↥Lf.1).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])`.

Use `haveI : Module.Finite ℤ_[l] ↥(OL Lf) := IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥Lf.1 _`. Use `haveI : Module.Free ℤ_[l] ↥(OL Lf) := IsIntegralClosure.module_free ℤ_[l] ℚ_[l] ↥Lf.1 _`. Use `haveI := IsIntegralClosure.isLocalization ℤ_[l] ℚ_[l] ↥Lf.1 ↥(OL Lf)`. Set `b` to `Module.finBasis ℤ_[l] ↥(OL Lf)`. Set `bL` to `b.localizationLocalization ℚ_[l] (nonZeroDivisors ℤ_[l]) ↥Lf.1`.

Set `ι : ↥(OL Lf) →+* ↥Lf.1` to `algebraMap _ _`. Establish `hι : Function.Injective ι` using `Subtype.val_injective`. Establish `hrepr : ∀ (o : ↥(OL Lf)) j, bL.repr (ι o) j = ((b.repr o j : ℤ_[l]) : ℚ_[l])` using `fun o j => Module.Basis.localizationLocalization_repr_algebraMap _ _ _ _ o j`. Establish `hsm : ∀ (x : ℤ_[l]) (o : ↥(OL Lf)), ι (x • o) = algebraMap ℚ_[l] ↥Lf.1 (x : ℚ_[l]) * ι o`. Introduce `x o`.

Rewrite using `[Algebra.smul_def, map_mul]`. Use `congr 1`. Apply the tactic sequence `try rw [← IsScalarTower.algebraMap_apply ℤ_[l] ↥(OL Lf) ↥Lf.1]`. Apply the tactic sequence `try rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥Lf.1]`. Apply the tactic sequence `try rfl`.

Establish `hcyc : ∀ g (o : ↥(OL Lf)), ((cycLL (P.PD K) ↥Lf.1 g : (↥Lf.1)ˣ) : ↥Lf.1) * ι o = ι ((χ g : ℤ_[l]) • o)`. Introduce `g o`. Rewrite using `[hsm, hχ]`. Both sides reduce to the same expression. Establish `hAlg : Continuous (algebraMap ℚ_[l] ↥Lf.1)` using `LinearMap.continuous_of_finiteDimensional (Algebra.linearMap ℚ_[l] ↥Lf.1)`.

Establish `hcZ : Continuous (fun x : ℤ_[l] => (x : ℚ_[l]))` using `(PadicInt.isOpenEmbedding_coe (p := l)).continuous`. Establish `hcoord : ∀ {X : Type} [TopologicalSpace X] (f : X → ↥Lf.1) (fO : X → ↥(OL Lf)), Continuous f → (∀ x, ι (fO x) = f x) → ∀ j, Continuous fun x => b.equivFun (fO x) j`. Introduce `X _ f fO hf hfO j`. Apply `(PadicInt.isOpenEmbedding_coe (p := l)).isEmbedding.continuous_iff.2` to reduce the goal to its premises. Establish `e : (fun x => ((b.equivFun (fO x) j : ℤ_[l]) : ℚ_[l])) = fun x => bL.coord j (f x)`.

Use function extensionality and compare the values at `x`. Rewrite using `[Module.Basis.coord_apply, ← hfO x, hrepr, Module.Basis.equivFun_apply]`. Use `show Continuous (fun x => ((b.equivFun (fO x) j : ℤ_[l]) : ℚ_[l]))`. Rewrite using `[e]`. Conclude with `(LinearMap.continuous_of_finiteDimensional (bL.coord j)).comp hf`.

Establish `hrec : ∀ {X : Type} [TopologicalSpace X] (F : Fin (Module.finrank ℤ_[l] ↥(OL Lf)) → X → ℤ_[l]), (∀ j, Continuous (F j)) → Continuous fun x => ι (b.equivFun.symm (fun j => F j x))`. Introduce `X _ F hF`. Simplify using `only [Module.Basis.equivFun_symm_apply, map_sum, hsm]`. Conclude with `continuous_finset_sum _ fun j _ => ((hAlg.comp (hcZ.comp (hF j))).mul continuous_const)`. Establish `hd1 : ∀ (f : ↥(GK K) → ↥Lf.1) g h, ReciprocityTheory.Def.d1 (Formalism.WeaklyAdmissibleFiltrations.charRep (cycLL (P.PD K) ↥Lf.1)) f (g, h) = ((cycLL (P.PD K) ↥Lf.1 g : (↥Lf.1)ˣ) : ↥Lf.1) * f h - f (g * h) + f g`.

Introduce `f g h`. Simplify using `[ReciprocityTheory.Def.d1, Formalism.WeaklyAdmissibleFiltrations.charRep]`. Establish `hd2 : ∀ (z : ↥(GK K) × ↥(GK K) → ↥Lf.1) g h k, ReciprocityTheory.Def.d2 (Formalism.WeaklyAdmissibleFiltrations.charRep (cycLL (P.PD K) ↥Lf.1)) z (g, h, k) = ((cycLL (P.PD K) ↥Lf.1 g : (↥Lf.1)ˣ) : ↥Lf.1) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h)`. Introduce `z g h k`. Simplify using `[ReciprocityTheory.Def.d2, Formalism.WeaklyAdmissibleFiltrations.charRep]`.

Set `cO : ↥(GK K) × ↥(GK K) → ↥(OL Lf)` to `fun p => (c p : ℤ_[l]) • (1 : ↥(OL Lf))`. Establish `hG` using `fun r => GlobalTheory.GenSpan.gen_zmod (hgen r)`. Establish `hcc : Continuous c` using `continuous_of_reductions c fun s => (hG (s + 1)).1.1.continuous`. Establish `hcoc : ∀ g h k, (χ g : ℤ_[l]) * c (h, k) - c (g * h, k) + c (g, h * k) - c (g, h) = 0`. Introduce `g h k`.

Rewrite using `[← PadicInt.ext_of_toZModPow]`. Introduce `n`. Simplify `(hG n).1.2 g h k` using `only [map_sub, map_add, map_mul, map_zero]`. Establish `hcOc : Continuous fun p => ι (cO p)`. Simplify using `only [cO, hsm, map_one, mul_one]`.

Conclude with `hAlg.comp (hcZ.comp hcc)`. Establish `hz0 : (fun p => ι (cO p)) ∈ Formalism.MainNotions.TruncatedSeriesCountingIdentities.twoCocyclesTwist (P.PD K) ↥Lf.1 ↥(OL Lf)`. Use `⟨⟨hcOc, fun p => ⟨cO p, rfl⟩⟩, ?_⟩` and prove the remaining obligations. Use `show ReciprocityTheory.Def.d2 _ _ = 0`. Use function extensionality and compare the values at `⟨g, h, k⟩`.

Rewrite using `[hd2]`. Simplify using `only [hcyc, ← map_sub, ← map_add, Pi.zero_apply, cO, smul_smul, ← sub_smul, ← add_smul]`. Rewrite using `[hcoc, zero_smul, map_zero]`. Set `z0 : ↥(Formalism.MainNotions.TruncatedSeriesCountingIdentities.twoCocyclesTwist (P.PD K) ↥Lf.1 ↥(OL Lf))` to `⟨_, hz0⟩`. Establish `haz0 : ∀ (a : ↥(OL Lf)) p, (a • z0 : ↥(Formalism.MainNotions.TruncatedSeriesCountingIdentities.twoCocyclesTwist (P.PD K) ↥Lf.1 ↥(OL Lf))).1 p = ι ((c p : ℤ_[l]) • a)`.

Introduce `a p`. Use `show a • ι (cO p) = _`. Rewrite using `[Algebra.smul_def, ← map_mul]`. Simplify using `only [cO, mul_smul_comm, mul_one]`. Both sides reduce to the same expression.

Unfold `Formalism.MainNotions.TruncatedSeriesCountingIdentities.TateDualityH2Integral`. Use `nonempty_quot_equiv _ z0 (fun a ha => ?_) (fun z => ?_)` and prove the remaining obligations. Take `⟨f, ⟨hfc, hfO⟩, hfd⟩` from `ha`. Use `choose fO hfO' using hfO`. Establish `e : ∀ g h, (χ g : ℤ_[l]) • fO h - fO (g * h) + fO g = (c (g, h) : ℤ_[l]) • a`.

Introduce `g h`. Apply `hι` to reduce the goal to its premises. Establish `e1` using `congrFun hfd (g, h)`. Simplify using `only [LinearMap.restrictScalars_apply, Submodule.subtype_apply] at e1`. Rewrite `e1` using `[hd1, haz0]`.

Rewrite using `[map_add, map_sub, ← hcyc, hfO', hfO', hfO', ← e1]`. Establish `hx : ∀ j, b.equivFun a j = 0`. Introduce `j`. Use `int_inj χ c hgen (b.equivFun a j) (fun g => b.equivFun (fO g) j) (hcoord f fO hfc hfO' j) fun g h => ?_` and prove the remaining obligations. Establish `e2` using `congrArg (fun o => b.equivFun o j) (e g h)`.

Simplify using `only [map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e2`. Rewrite using `[e2, mul_comm]`. Conclude with `b.equivFun.injective (by funext j; rw [hx j, map_zero]; rfl)`. Take `⟨⟨hzc, hzO⟩, hzd⟩` from `z.2`. Use `choose zO hzO' using hzO`.

Establish `hzd' : ∀ g h k, (χ g : ℤ_[l]) • zO (h, k) - zO (g * h, k) + zO (g, h * k) - zO (g, h) = 0`. Introduce `g h k`. Apply `hι` to reduce the goal to its premises. Establish `e1` using `congrFun (LinearMap.mem_ker.1 hzd) (g, h, k)`. Rewrite `e1` using `[hd2]`.

Rewrite using `[map_sub, map_add, map_sub, ← hcyc, hzO', hzO', hzO', hzO', map_zero]`. Conclude with `e1`. Establish `hspan` using `fun j => int_span χ c hχc hgen hfin (fun p => b.equivFun (zO p) j) (hcoord _ zO hzc hzO' j) fun g h k => by`. Establish `e2` using `congrArg (fun o => b.equivFun o j) (hzd' g h k)`. Simplify `e2` using `only [map_add, map_sub, map_smul, map_zero, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]`.

Use `choose X F hF hXF using hspan`. Set `a : ↥(OL Lf)` to `b.equivFun.symm X`. Set `FO : ↥(GK K) → ↥(OL Lf)` to `fun g => b.equivFun.symm (fun j => F j g)`. Use `⟨a, fun g => ι (FO g), ⟨hrec F hF, fun g => ⟨FO g, rfl⟩⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `⟨g, h⟩`.

Establish `hcalc : (χ g : ℤ_[l]) • FO h - FO (g * h) + FO g = zO (g, h) - (c (g, h) : ℤ_[l]) • a`. Apply `b.equivFun.injective` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Simplify using `only [map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, FO, a, LinearEquiv.apply_symm_apply]`. Rewrite using `[hXF j g h, mul_comm]`.

Establish `hcalc'` using `congrArg ι hcalc`. Rewrite `hcalc'` using `[map_add, map_sub, map_sub, ← hcyc, hzO' (g, h), ← haz0 a (g, h)]`. Use `(hd1 _ g h).trans (hcalc'.trans ?_)` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem tateH2OAt_of_fund (P : LocPrime l) (K Lf : FinExt l) [CompactSpace ↥(GK K)]
    (χ : ↥(GK K) →* ℤ_[l]ˣ) (c : ↥(GK K) × ↥(GK K) → ℤ_[l])
    (hχc : Continuous (fun g => (χ g : ℤ_[l])))
    (hχ : ∀ g, ((χ g : ℤ_[l]) : ℚ_[l]) = (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]))
    (hgen : ∀ r, Gen χ r c)
    (hfin : ∀ r : ℕ, 0 < r → Finite (ReciprocityTheory.Gal.H1 (ReciprocityTheory.Gal.charRep
      ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ)))) :
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.TateDualityH2Integral (P.PD K) ↥Lf.1 ↥(OL Lf) := by
  classical
  haveI : FiniteDimensional ℚ_[l] ↥Lf.1 := Lf.2
  haveI : IsIntegralClosure ↥(OL Lf) ℤ_[l] ↥Lf.1 := integralClosure.isIntegralClosure _ _
  haveI : FaithfulSMul ℤ_[l] ↥Lf.1 := by
    rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥Lf.1]
    exact (algebraMap ℚ_[l] ↥Lf.1).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  haveI : Module.Finite ℤ_[l] ↥(OL Lf) := IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥Lf.1 _
  haveI : Module.Free ℤ_[l] ↥(OL Lf) := IsIntegralClosure.module_free ℤ_[l] ℚ_[l] ↥Lf.1 _
  haveI := IsIntegralClosure.isLocalization ℤ_[l] ℚ_[l] ↥Lf.1 ↥(OL Lf)
  let b := Module.finBasis ℤ_[l] ↥(OL Lf)
  let bL := b.localizationLocalization ℚ_[l] (nonZeroDivisors ℤ_[l]) ↥Lf.1
  let ι : ↥(OL Lf) →+* ↥Lf.1 := algebraMap _ _
  have hι : Function.Injective ι := Subtype.val_injective
  have hrepr : ∀ (o : ↥(OL Lf)) j, bL.repr (ι o) j = ((b.repr o j : ℤ_[l]) : ℚ_[l]) := fun o j =>
    Module.Basis.localizationLocalization_repr_algebraMap _ _ _ _ o j
  have hsm : ∀ (x : ℤ_[l]) (o : ↥(OL Lf)), ι (x • o) = algebraMap ℚ_[l] ↥Lf.1 (x : ℚ_[l]) * ι o := by
    intro x o
    rw [Algebra.smul_def, map_mul]
    congr 1
    try rw [← IsScalarTower.algebraMap_apply ℤ_[l] ↥(OL Lf) ↥Lf.1]
    try rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥Lf.1]
    try rfl
  have hcyc : ∀ g (o : ↥(OL Lf)), ((cycLL (P.PD K) ↥Lf.1 g : (↥Lf.1)ˣ) : ↥Lf.1) * ι o =
      ι ((χ g : ℤ_[l]) • o) := by
    intro g o
    rw [hsm, hχ]
    rfl
  have hAlg : Continuous (algebraMap ℚ_[l] ↥Lf.1) :=
    LinearMap.continuous_of_finiteDimensional (Algebra.linearMap ℚ_[l] ↥Lf.1)
  have hcZ : Continuous (fun x : ℤ_[l] => (x : ℚ_[l])) := (PadicInt.isOpenEmbedding_coe (p := l)).continuous
  have hcoord : ∀ {X : Type} [TopologicalSpace X] (f : X → ↥Lf.1) (fO : X → ↥(OL Lf)),
      Continuous f → (∀ x, ι (fO x) = f x) → ∀ j, Continuous fun x => b.equivFun (fO x) j := by
    intro X _ f fO hf hfO j
    apply (PadicInt.isOpenEmbedding_coe (p := l)).isEmbedding.continuous_iff.2
    have e : (fun x => ((b.equivFun (fO x) j : ℤ_[l]) : ℚ_[l])) = fun x => bL.coord j (f x) := by
      funext x
      rw [Module.Basis.coord_apply, ← hfO x, hrepr, Module.Basis.equivFun_apply]
    show Continuous (fun x => ((b.equivFun (fO x) j : ℤ_[l]) : ℚ_[l]))
    rw [e]
    exact (LinearMap.continuous_of_finiteDimensional (bL.coord j)).comp hf
  have hrec : ∀ {X : Type} [TopologicalSpace X] (F : Fin (Module.finrank ℤ_[l] ↥(OL Lf)) → X → ℤ_[l]),
      (∀ j, Continuous (F j)) → Continuous fun x => ι (b.equivFun.symm (fun j => F j x)) := by
    intro X _ F hF
    simp only [Module.Basis.equivFun_symm_apply, map_sum, hsm]
    exact continuous_finset_sum _ fun j _ => ((hAlg.comp (hcZ.comp (hF j))).mul continuous_const)
  have hd1 : ∀ (f : ↥(GK K) → ↥Lf.1) g h, ReciprocityTheory.Def.d1 (Formalism.WeaklyAdmissibleFiltrations.charRep (cycLL (P.PD K) ↥Lf.1)) f (g, h) =
      ((cycLL (P.PD K) ↥Lf.1 g : (↥Lf.1)ˣ) : ↥Lf.1) * f h - f (g * h) + f g := by
    intro f g h
    simp [ReciprocityTheory.Def.d1, Formalism.WeaklyAdmissibleFiltrations.charRep]
  have hd2 : ∀ (z : ↥(GK K) × ↥(GK K) → ↥Lf.1) g h k,
      ReciprocityTheory.Def.d2 (Formalism.WeaklyAdmissibleFiltrations.charRep (cycLL (P.PD K) ↥Lf.1)) z (g, h, k) =
      ((cycLL (P.PD K) ↥Lf.1 g : (↥Lf.1)ˣ) : ↥Lf.1) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) := by
    intro z g h k
    simp [ReciprocityTheory.Def.d2, Formalism.WeaklyAdmissibleFiltrations.charRep]

  let cO : ↥(GK K) × ↥(GK K) → ↥(OL Lf) := fun p => (c p : ℤ_[l]) • (1 : ↥(OL Lf))
  have hG := fun r => GlobalTheory.GenSpan.gen_zmod (hgen r)
  have hcc : Continuous c := continuous_of_reductions c fun s => (hG (s + 1)).1.1.continuous
  have hcoc : ∀ g h k, (χ g : ℤ_[l]) * c (h, k) - c (g * h, k) + c (g, h * k) - c (g, h) = 0 := by
    intro g h k
    rw [← PadicInt.ext_of_toZModPow]
    intro n
    simpa only [map_sub, map_add, map_mul, map_zero] using (hG n).1.2 g h k
  have hcOc : Continuous fun p => ι (cO p) := by
    simp only [cO, hsm, map_one, mul_one]
    exact hAlg.comp (hcZ.comp hcc)
  have hz0 : (fun p => ι (cO p)) ∈ Formalism.MainNotions.TruncatedSeriesCountingIdentities.twoCocyclesTwist (P.PD K) ↥Lf.1 ↥(OL Lf) := by
    refine ⟨⟨hcOc, fun p => ⟨cO p, rfl⟩⟩, ?_⟩
    show ReciprocityTheory.Def.d2 _ _ = 0
    funext ⟨g, h, k⟩
    rw [hd2]
    simp only [hcyc, ← map_sub, ← map_add, Pi.zero_apply, cO, smul_smul, ← sub_smul, ← add_smul]
    rw [hcoc, zero_smul, map_zero]
  let z0 : ↥(Formalism.MainNotions.TruncatedSeriesCountingIdentities.twoCocyclesTwist (P.PD K) ↥Lf.1 ↥(OL Lf)) := ⟨_, hz0⟩
  have haz0 : ∀ (a : ↥(OL Lf)) p, (a • z0 : ↥(Formalism.MainNotions.TruncatedSeriesCountingIdentities.twoCocyclesTwist (P.PD K) ↥Lf.1 ↥(OL Lf))).1 p =
      ι ((c p : ℤ_[l]) • a) := by
    intro a p
    show a • ι (cO p) = _
    rw [Algebra.smul_def, ← map_mul]
    simp only [cO, mul_smul_comm, mul_one]
    rfl
  unfold Formalism.MainNotions.TruncatedSeriesCountingIdentities.TateDualityH2Integral
  refine nonempty_quot_equiv _ z0 (fun a ha => ?_) (fun z => ?_)
  ·
    obtain ⟨f, ⟨hfc, hfO⟩, hfd⟩ := ha
    choose fO hfO' using hfO
    have e : ∀ g h, (χ g : ℤ_[l]) • fO h - fO (g * h) + fO g = (c (g, h) : ℤ_[l]) • a := by
      intro g h
      apply hι
      have e1 := congrFun hfd (g, h)
      simp only [LinearMap.restrictScalars_apply, Submodule.subtype_apply] at e1
      rw [hd1, haz0] at e1
      rw [map_add, map_sub, ← hcyc, hfO', hfO', hfO', ← e1]
    have hx : ∀ j, b.equivFun a j = 0 := by
      intro j
      refine int_inj χ c hgen (b.equivFun a j) (fun g => b.equivFun (fO g) j)
        (hcoord f fO hfc hfO' j) fun g h => ?_
      have e2 := congrArg (fun o => b.equivFun o j) (e g h)
      simp only [map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul] at e2
      rw [e2, mul_comm]
    exact b.equivFun.injective (by funext j; rw [hx j, map_zero]; rfl)
  ·
    obtain ⟨⟨hzc, hzO⟩, hzd⟩ := z.2
    choose zO hzO' using hzO
    have hzd' : ∀ g h k, (χ g : ℤ_[l]) • zO (h, k) - zO (g * h, k) + zO (g, h * k) - zO (g, h) = 0 := by
      intro g h k
      apply hι
      have e1 := congrFun (LinearMap.mem_ker.1 hzd) (g, h, k)
      rw [hd2] at e1
      rw [map_sub, map_add, map_sub, ← hcyc, hzO', hzO', hzO', hzO', map_zero]
      exact e1
    have hspan := fun j => int_span χ c hχc hgen hfin (fun p => b.equivFun (zO p) j)
      (hcoord _ zO hzc hzO' j) fun g h k => by
        have e2 := congrArg (fun o => b.equivFun o j) (hzd' g h k)
        simpa only [map_add, map_sub, map_smul, map_zero, Pi.add_apply, Pi.sub_apply,
          Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using e2
    choose X F hF hXF using hspan
    let a : ↥(OL Lf) := b.equivFun.symm X
    let FO : ↥(GK K) → ↥(OL Lf) := fun g => b.equivFun.symm (fun j => F j g)
    refine ⟨a, fun g => ι (FO g), ⟨hrec F hF, fun g => ⟨FO g, rfl⟩⟩, ?_⟩
    funext ⟨g, h⟩
    have hcalc : (χ g : ℤ_[l]) • FO h - FO (g * h) + FO g = zO (g, h) - (c (g, h) : ℤ_[l]) • a := by
      apply b.equivFun.injective
      funext j
      simp only [map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        FO, a, LinearEquiv.apply_symm_apply]
      rw [hXF j g h, mul_comm]
    have hcalc' := congrArg ι hcalc
    rw [map_add, map_sub, map_sub, ← hcyc, hzO' (g, h), ← haz0 a (g, h)] at hcalc'
    refine (hd1 _ g h).trans (hcalc'.trans ?_)
    rfl

end GlobalTheory.IntTateTop

namespace GlobalTheory.IntTateTop

/- English proof (translation)
Introduce `hT D i w hw C`. Take `⟨hcpt, χ, c, hχc, hχ, hgen, hfin⟩` from `GlobalTheory.T.exists_fundamentalTwoCocycle_of_localTateDuality hT (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw`. Conclude with `tateH2OAt_of_fund (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL χ c hχc hχ hgen hfin`.
-/
theorem admH2_of_duality : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.admH2 i := by
  intro hT D i w hw C
  obtain ⟨hcpt, χ, c, hχc, hχ, hgen, hfin⟩ :=
    GlobalTheory.T.exists_fundamentalTwoCocycle_of_localTateDuality hT (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw
  exact tateH2OAt_of_fund (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL χ c hχc hχ hgen hfin

end GlobalTheory.IntTateTop

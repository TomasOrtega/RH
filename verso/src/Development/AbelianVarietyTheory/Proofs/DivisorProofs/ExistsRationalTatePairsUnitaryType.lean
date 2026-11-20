import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedLevelPointsOfLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PelOKOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatiblePrimitiveRootsThroughStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcLiftExtensionLargerClosedField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InjectiveOfIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TraitTate

open GlobalTheory.TorusExt GlobalTheory.ArcExt

/- English proof (translation)
Introduce `E _ _ _ H Dm l c O _ β hβ T b hb D _ o hP hrat`. Use `letI := H.starRing`. Use `haveI : CharZero (FractionRing T.V) := charZero_of_injective_algebraMap (IsFractionRing.injective T.V (FractionRing T.V))`. Use `haveI : CharZero (AlgebraicClosure (FractionRing T.V)) := charZero_of_injective_algebraMap (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))).injective`. Establish `hB : D.toPre.TauBimult` using `D.tau_bimult`.

Use `set g : O →+* AlgebraicClosure (FractionRing T.V) := (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))).comp ((algebraMap T.V _).comp b) with hg`. Establish `hginj : Function.Injective g` using `(algebraMap (FractionRing T.V) _).injective.comp ((IsFractionRing.injective T.V (FractionRing T.V)).comp hb)`. Choose the witnesses or unpack the hypotheses as in `⟨ζ₀, hζp, hζc, hζA⟩ : ∃ ζ₀ : ℕ → (AlgebraicClosure (FractionRing T.V))ˣ, (∀ n, 0 < n → IsPrimitiveRoot (ζ₀ n) n) ∧ (∀ n m, 0 < n → 0 < m → ζ₀ (n * m) ^ m = ζ₀ n) ∧ ∀ z : O, ((β z : c.F) : ℂ) = zeta l.A → (ζ₀ l.A : AlgebraicClosure (FractionRing T.V)) = g z := by`. Distinguish the cases in `hz : ∃ z : O, ((β z : c.F) : ℂ) = zeta l.A`. Take `⟨z, hz⟩` from `hz`.

Establish `h₀ : IsPrimitiveRoot (((β z : c.F) : ℂ)) l.A`. Rewrite using `[hz]`. Conclude with `Complex.isPrimitiveRoot_exp l.A l.A_pos.ne'`. Establish `h₁ : IsPrimitiveRoot (β z) l.A` using `IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom) h₀ Subtype.val_injective`. Establish `h₂ : IsPrimitiveRoot z l.A` using `IsPrimitiveRoot.of_map_of_injective (f := β) h₁ hβ`.

Establish `h₃ : IsPrimitiveRoot (g z) l.A` using `h₂.map_of_injective hginj`. Take `⟨ζ, e₁, e₂, e₃⟩` from `GlobalTheory.T.exists_compatible_primitiveRoots_through (AlgebraicClosure (FractionRing T.V)) l.A (g z) l.A_pos h₃`. Use `⟨ζ, e₁, e₂, fun z' hz' => ?_⟩` and prove the remaining obligations. Establish `: z' = z` using `hβ (Subtype.val_injective (hz'.trans hz.symm))`. Rewrite using `[this]`.

Conclude with `e₃`. Take `⟨ζ, e₁, e₂, -⟩` from `GlobalTheory.T.exists_compatible_primitiveRoots_through (AlgebraicClosure (FractionRing T.V)) 1 1 one_pos IsPrimitiveRoot.one`. Conclude with `⟨ζ, e₁, e₂, fun z hz' => (hz ⟨z, hz'⟩).elim⟩`. Take `⟨-, -, -, hF⟩` from `hP`. Take `⟨-, hT⟩` from `hF (AlgebraicClosure (FractionRing T.V))`.

Take `⟨I₀, hI₀⟩` from `hT ζ₀ hζp hζc`. Establish `hA : l.A ∣ l.M'` using `Nat.dvd_lcm_right l.M l.A`. Establish `hM : l.M ∣ l.M'` using `Nat.dvd_lcm_left l.M l.A`. Use `choose pA hpA using fun a => hrat l.A hA (I₀.ev l.A a)`. Use `choose pM hpM using fun a => hrat l.M hM (I₀.ev l.M a)`.

Use `⟨pA, pM, fun F _ _ _ z hz => ?_⟩` and prove the remaining obligations. Set `e : AlgebraicClosure (FractionRing T.V) →ₐ[FractionRing T.V] F` to `IsAlgClosed.lift (M := F) (R := FractionRing T.V) (S := AlgebraicClosure (FractionRing T.V))`. Establish `he : (e : AlgebraicClosure (FractionRing T.V) →+* F).comp (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) = algebraMap (FractionRing T.V) F` using `RingHom.ext fun x => e.commutes x`. Establish `hK : (algebraMap (AlgebraicClosure (FractionRing T.V)) (AlgebraicClosure (FractionRing T.V))).comp (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) = algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))` using `RingHom.ext fun _ => rfl`. Establish `base : ∀ {k : ℕ} (p₀ : QkPt D.toPre (FractionRing T.V) k) (r : QkPt D.toPre (AlgebraicClosure (FractionRing T.V)) k), QkExt (algebraMap _ (AlgebraicClosure (FractionRing T.V))) p₀ r → ∀ p, QkExt (algebraMap _ (AlgebraicClosure (FractionRing T.V))) p₀ p → QkPt.Equiv D.toPre (Algeb …`.

Introduce `k p₀ r hr p hp`. Establish `u` using `(existsUnique_qkExt hB (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) hK p₀).unique hp hr`. Rewrite using `[u]`. Conclude with `qk_equiv_refl hB r`. Use `⟨tateExt (e : AlgebraicClosure (FractionRing T.V) →+* F) he hB abelianSchemeLaws_all.1 I₀ (ArcInputCompare.weil_ext hB (e : AlgebraicClosure (FractionRing T.V) →+* F) he), ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `show ((Units.map (e : AlgebraicClosure (FractionRing T.V) →+* F).toMonoidHom (I₀.ζ l.A) : Fˣ) : F) = _`. Rewrite using `[hI₀, Units.coe_map, hζA z hz, hg]`. Conclude with `e.commutes _`. Introduce `a q hq`. Conclude with `GlobalTheory.LiftExt.equiv_of_base hB _ he (base (pA a) _ (hpA a)) q hq`.

Introduce `a q hq`. Conclude with `GlobalTheory.LiftExt.equiv_of_base hB _ he (base (pM a) _ (hpM a)) q hq`.
-/
theorem exists_tate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F), Function.Injective β → ∀ (T : Formalism.L2.Pj.CDVR) (b : O →+* T.V), Function.Injective b → ∀ (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), PelOK Dm D.toPre o → (∀ k : ℕ, k ∣ l.M' → ∀ q : QkPt D.toPre (AlgebraicClosure (FractionRing T.V)) k, ∃ p : QkPt D.toPre (FractionRing T.V) k, QkExt (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) p q) → ∃ (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A) (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M), ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F] (z : O), ((β z : c.F) : ℂ) = zeta l.A → ∃ I : (letI := H.starRing; TateIsoQ Dm D.toPre o F), (I.ζ l.A : F) = algebraMap (FractionRing T.V) F (algebraMap T.V _ (b z)) ∧ (∀ a q, QkExt (algebraMap _ F) (pA a) q → QkPt.Equiv D.toPre F q (I.ev l.A a)) ∧ ∀ a q, QkExt (algebraMap _ F) (pM a) q → QkPt.Equiv D.toPre F q (I.ev l.M a) := by
  intro E _ _ _ H Dm l c O _ β hβ T b hb D _ o hP hrat
  letI := H.starRing
  haveI : CharZero (FractionRing T.V) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective T.V (FractionRing T.V))
  haveI : CharZero (AlgebraicClosure (FractionRing T.V)) :=
    charZero_of_injective_algebraMap (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))).injective
  have hB : D.toPre.TauBimult := D.tau_bimult

  set g : O →+* AlgebraicClosure (FractionRing T.V) :=
    (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))).comp ((algebraMap T.V _).comp b) with hg
  have hginj : Function.Injective g :=
    (algebraMap (FractionRing T.V) _).injective.comp ((IsFractionRing.injective T.V (FractionRing T.V)).comp hb)

  obtain ⟨ζ₀, hζp, hζc, hζA⟩ : ∃ ζ₀ : ℕ → (AlgebraicClosure (FractionRing T.V))ˣ,
      (∀ n, 0 < n → IsPrimitiveRoot (ζ₀ n) n) ∧ (∀ n m, 0 < n → 0 < m → ζ₀ (n * m) ^ m = ζ₀ n) ∧
      ∀ z : O, ((β z : c.F) : ℂ) = zeta l.A → (ζ₀ l.A : AlgebraicClosure (FractionRing T.V)) = g z := by
    by_cases hz : ∃ z : O, ((β z : c.F) : ℂ) = zeta l.A
    · obtain ⟨z, hz⟩ := hz
      have h₀ : IsPrimitiveRoot (((β z : c.F) : ℂ)) l.A := by
        rw [hz]; exact Complex.isPrimitiveRoot_exp l.A l.A_pos.ne'
      have h₁ : IsPrimitiveRoot (β z) l.A :=
        IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom) h₀ Subtype.val_injective
      have h₂ : IsPrimitiveRoot z l.A := IsPrimitiveRoot.of_map_of_injective (f := β) h₁ hβ
      have h₃ : IsPrimitiveRoot (g z) l.A := h₂.map_of_injective hginj
      obtain ⟨ζ, e₁, e₂, e₃⟩ := GlobalTheory.T.exists_compatible_primitiveRoots_through (AlgebraicClosure (FractionRing T.V)) l.A (g z) l.A_pos h₃
      refine ⟨ζ, e₁, e₂, fun z' hz' => ?_⟩
      have : z' = z := hβ (Subtype.val_injective (hz'.trans hz.symm))
      rw [this]; exact e₃
    · obtain ⟨ζ, e₁, e₂, -⟩ := GlobalTheory.T.exists_compatible_primitiveRoots_through (AlgebraicClosure (FractionRing T.V)) 1 1 one_pos IsPrimitiveRoot.one
      exact ⟨ζ, e₁, e₂, fun z hz' => (hz ⟨z, hz'⟩).elim⟩

  obtain ⟨-, -, -, hF⟩ := hP
  obtain ⟨-, hT⟩ := hF (AlgebraicClosure (FractionRing T.V))
  obtain ⟨I₀, hI₀⟩ := hT ζ₀ hζp hζc

  have hA : l.A ∣ l.M' := Nat.dvd_lcm_right l.M l.A
  have hM : l.M ∣ l.M' := Nat.dvd_lcm_left l.M l.A
  choose pA hpA using fun a => hrat l.A hA (I₀.ev l.A a)
  choose pM hpM using fun a => hrat l.M hM (I₀.ev l.M a)
  refine ⟨pA, pM, fun F _ _ _ z hz => ?_⟩

  let e : AlgebraicClosure (FractionRing T.V) →ₐ[FractionRing T.V] F :=
    IsAlgClosed.lift (M := F) (R := FractionRing T.V) (S := AlgebraicClosure (FractionRing T.V))
  have he : (e : AlgebraicClosure (FractionRing T.V) →+* F).comp
      (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) = algebraMap (FractionRing T.V) F :=
    RingHom.ext fun x => e.commutes x
  have hK : (algebraMap (AlgebraicClosure (FractionRing T.V)) (AlgebraicClosure (FractionRing T.V))).comp
      (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) =
      algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V)) := RingHom.ext fun _ => rfl

  have base : ∀ {k : ℕ} (p₀ : QkPt D.toPre (FractionRing T.V) k) (r : QkPt D.toPre (AlgebraicClosure (FractionRing T.V)) k),
      QkExt (algebraMap _ (AlgebraicClosure (FractionRing T.V))) p₀ r →
      ∀ p, QkExt (algebraMap _ (AlgebraicClosure (FractionRing T.V))) p₀ p →
        QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing T.V)) p r := by
    intro k p₀ r hr p hp
    have u := (existsUnique_qkExt hB (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) hK p₀).unique hp hr
    rw [u]; exact qk_equiv_refl hB r
  refine ⟨tateExt (e : AlgebraicClosure (FractionRing T.V) →+* F) he hB abelianSchemeLaws_all.1 I₀
    (ArcInputCompare.weil_ext hB (e : AlgebraicClosure (FractionRing T.V) →+* F) he), ?_, ?_, ?_⟩
  ·
    show ((Units.map (e : AlgebraicClosure (FractionRing T.V) →+* F).toMonoidHom (I₀.ζ l.A) : Fˣ) : F) = _
    rw [hI₀, Units.coe_map, hζA z hz, hg]
    exact e.commutes _
  · intro a q hq
    exact GlobalTheory.LiftExt.equiv_of_base hB _ he (base (pA a) _ (hpA a)) q hq
  · intro a q hq
    exact GlobalTheory.LiftExt.equiv_of_base hB _ he (base (pM a) _ (hpM a)) q hq

end GlobalTheory.TraitTate

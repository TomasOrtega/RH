import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitLatticesIsoFormsProportionalRamificationStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelSmoothOfRelativeDimensionCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTamePolyhedralFan

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc.TraitRam

variable {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ}

/- English proof (translation)
Set `K` to `AlgebraicClosure (FractionRing T.V)`. Set `k : Sp K ⟶ Sp (FractionRing T.V)` to `spMap (algebraMap (FractionRing T.V) K)`. Establish `hK : (n : K) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Establish `hp` using `(IsPullback.of_hasPullback T.A.A.hom k).paste_horiz T.cart.1`. Establish `h1 : SmoothOfRelativeDimension T.A.g (pullback.snd T.A.A.hom k)` using `(smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback T.A.A.hom k) T.A.smoothDim`.

Use `GlobalTheory.SiegDim.dim_geometric_fibre F.univ hn hζ hK (k ≫ T.y) ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `SmoothOfRelativeDimension T.A.g (pullback.snd F.univ.A.hom (k ≫ T.y))`. Rewrite using `[← hp.isoPullback_inv_snd]`. Conclude with `(smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_horiz_isIso (fst := hp.isoPullback.inv) (g := 𝟙 _) ⟨by simp⟩) h1`.
-/
theorem dim_eq (hn : 2 ≤ n) (hζ : IsUnit ζ) (T : Trait F) : T.A.g = g := by
  let K := AlgebraicClosure (FractionRing T.V)
  let k : Sp K ⟶ Sp (FractionRing T.V) := spMap (algebraMap (FractionRing T.V) K)
  have hK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hp := (IsPullback.of_hasPullback T.A.A.hom k).paste_horiz T.cart.1
  have h1 : SmoothOfRelativeDimension T.A.g (pullback.snd T.A.A.hom k) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback T.A.A.hom k) T.A.smoothDim
  refine GlobalTheory.SiegDim.dim_geometric_fibre F.univ hn hζ hK (k ≫ T.y) ?_
  change SmoothOfRelativeDimension T.A.g (pullback.snd F.univ.A.hom (k ≫ T.y))
  rw [← hp.isoPullback_inv_snd]
  exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
    (IsPullback.of_horiz_isIso (fst := hp.isoPullback.inv) (g := 𝟙 _) ⟨by simp⟩) h1

/- English proof (translation)
Establish `hR : AdmBase T.V (maximalIdeal T.V)` using `⟨inferInstance, inferInstance, inferInstance, T.complete⟩`. Establish `h` using `GlobalTheory.TateUnif.rank_add_dim hR T.semi T.U`. Establish `e` using `dim_eq hn hζ T`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_le (hn : 2 ≤ n) (hζ : IsUnit ζ) (T : Trait F) : Module.finrank ℤ T.D.toPre.X ≤ g := by
  have hR : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, T.complete⟩
  have h := GlobalTheory.TateUnif.rank_add_dim hR T.semi T.U
  have e := dim_eq hn hζ T
  omega

/- English proof (translation)
Introduce `g n o _ ζ hn hζ F T T' f fK hf hl hK hy m hm φ hφ`. Establish `hB : GlobalTheory.Mum.Base T'.V` using `⟨⟨inferInstance, inferInstance, inferInstance, T'.complete⟩, inferInstance⟩`. Establish `hid : spMap (RingHom.id (FractionRing T'.V)) = 𝟙 _` using `Spec.map_id _`. Take `⟨e, he⟩` from `GlobalTheory.T.trait_lattices_iso_forms_proportional_ramification g n o ζ F T T' T'.V f (RingHom.id _) fK (RingHom.id _) hB inferInstance hf Function.injective_id hl inferInstance hK (fun _ => rfl) (by rw [hid, Category.id_comp, hy]) T'.ϖ m 1 T'.irr hm (by rw [pow_one]; rfl)`. Establish `hon` using `hφ T.D.toPre.X (finrank_le hn hζ T)`.

Establish `hc : toReal T.β ∈ psdCone (id : ℤ → ℤ) T.D.toPre.X` using `GlobalTheory.PolFan.TameZ.toReal_mem_psdCone_int (mem_balForms_int.2 T.symm) fun x => by simpa using T.mono.nonneg 0 x`. Rewrite using `[← evalR_toReal φ T.β, ← hon.homog _ hc m m.cast_nonneg, ← evalZ_pull φ (r := e.toIntLinearEquiv.toLinearMap) e.surjective, ← evalR_toReal]`. Use `congr 1`. Use `LinearMap.ext₂ fun a b => ?_` and prove the remaining obligations. Establish `h` using `he a b`.

Rewrite `h` using `[Nat.cast_one, one_mul]`. Simplify using `only [toReal_apply, pull_apply, LinearMap.smul_apply, smul_eq_mul]`. Conclude with `h.symm` after adjusting the coercions.
-/
theorem evalZ_eq_mul : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o), 2 ≤ n → IsUnit ζ → ∀ (F : SFam g n ζ) (T T' : Trait F) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V), Function.Injective f → IsLocalHom f → (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) → T'.y = spMap fK ≫ T.y → ∀ m : ℕ, Associated (f T.ϖ) (T'.ϖ ^ m) → ∀ φ : InvFun ℤ, IsPolFan id g φ → φ.evalZ T'.β = m * φ.evalZ T.β := by
  intro g n o _ ζ hn hζ F T T' f fK hf hl hK hy m hm φ hφ
  have hB : GlobalTheory.Mum.Base T'.V := ⟨⟨inferInstance, inferInstance, inferInstance, T'.complete⟩, inferInstance⟩
  have hid : spMap (RingHom.id (FractionRing T'.V)) = 𝟙 _ := Spec.map_id _
  obtain ⟨e, he⟩ := GlobalTheory.T.trait_lattices_iso_forms_proportional_ramification g n o ζ F T T' T'.V f (RingHom.id _) fK (RingHom.id _) hB inferInstance hf
    Function.injective_id hl inferInstance hK (fun _ => rfl) (by rw [hid, Category.id_comp, hy]) T'.ϖ m 1 T'.irr hm
    (by rw [pow_one]; rfl)
  have hon := hφ T.D.toPre.X (finrank_le hn hζ T)
  have hc : toReal T.β ∈ psdCone (id : ℤ → ℤ) T.D.toPre.X :=
    GlobalTheory.PolFan.TameZ.toReal_mem_psdCone_int (mem_balForms_int.2 T.symm) fun x => by simpa using T.mono.nonneg 0 x
  rw [← evalR_toReal φ T.β, ← hon.homog _ hc m m.cast_nonneg,
    ← evalZ_pull φ (r := e.toIntLinearEquiv.toLinearMap) e.surjective, ← evalR_toReal]
  congr 1
  refine LinearMap.ext₂ fun a b => ?_
  have h := he a b
  rw [Nat.cast_one, one_mul] at h
  simp only [toReal_apply, pull_apply, LinearMap.smul_apply, smul_eq_mul]
  exact_mod_cast h.symm

end GlobalTheory.Poinc.TraitRam

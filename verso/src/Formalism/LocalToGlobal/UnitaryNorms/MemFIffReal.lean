import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.DataNChoice
import Formalism.LocalToGlobal.UnitaryNorms.AdjoinCycZeta

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits

structure Frame {R : Ranks} (H : Formalism.BasicNotions.Host R) where

  j : H.E →ₐ[ℚ] Qb

  ι : Qb →+* ℂ

  phi0 : ∀ x : H.E, ι (j x) = H.φ₀ x

namespace Frame

variable {R : Ranks} {H : Formalism.BasicNotions.Host R} (T : Frame H)

/- English proof (translation)
The claim follows from `H.range_eq T.j`.
-/
theorem range : T.j.fieldRange = H.EQ := H.range_eq T.j

def iso : H.E ≃ₐ[ℚ] H.EQ := H.jOf T.j

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem iso_coe (x : H.E) : ((T.iso x : H.EQ) : Qb) = T.j x := rfl

/- English proof (translation)
Rewrite using `[T.range]`.
-/
theorem galOf : T.j.fieldRange.fixingSubgroup = GalOf (H.EQ) := by
  rw [T.range]

/- English proof (translation)
The claim follows from `H.mem_F_iff T.j x`.
-/
theorem mem_F (x : H.E) : x ∈ H.F ↔ T.j x ∈ H.FQ := H.mem_F_iff T.j x

/- English proof (translation)
The claim follows from `H.mem_K_iff T.j x`.
-/
theorem mem_K (x : H.E) : x ∈ H.K ↔ T.j x ∈ KQ H.d := H.mem_K_iff T.j x

/- English proof (translation)
The claim follows from `H.conjE_apply (T.ι.comp T.j.toRingHom) x`.
-/
theorem conj (x : H.E) : T.ι (T.j (H.conj x)) = starRingEnd ℂ (T.ι (T.j x)) :=
  H.conjE_apply (T.ι.comp T.j.toRingHom) x

/- English proof (translation)
Rewrite using `[← T.conj, H.conjE_mem_hostF_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `congrArg (fun y => T.ι (T.j y)) h`. Introduce `h`.

Conclude with `T.j.toRingHom.injective (T.ι.injective h)`.
-/
theorem mem_F_iff_real (x : H.E) : x ∈ H.F ↔ starRingEnd ℂ (T.ι (T.j x)) = T.ι (T.j x) := by
  rw [← T.conj, H.conjE_mem_hostF_iff]
  constructor
  · intro h; exact congrArg (fun y => T.ι (T.j y)) h
  · intro h; exact T.j.toRingHom.injective (T.ι.injective h)

/- English proof (translation)
Rewrite using `[T.phi0]`. Conclude with `H.φ₀_mem`.
-/
theorem sqrtMinusD : T.ι (T.j H.sqrtMinusD) = Complex.I * (Real.sqrt H.d : ℂ) := by
  rw [T.phi0]; exact H.φ₀_mem

def carry (σ : H.E ≃ₐ[ℚ] H.E) : H.EQ →ₐ[ℚ] Qb :=
  (T.j.comp (σ : H.E →ₐ[ℚ] H.E)).comp (T.iso.symm : H.EQ →ₐ[ℚ] H.E)

/- English proof (translation)
Simplify using `[carry]`.
-/
theorem carry_iso (σ : H.E ≃ₐ[ℚ] H.E) (x : H.E) : T.carry σ (T.iso x) = T.j (σ x) := by
  simp [carry]

/- English proof (translation)
The claim follows from `H.actsAs_gal T.j σ`.
-/
theorem galE_acts (σ : H.E ≃ₐ[ℚ] H.E) :
    H.ActsAs (T.carry σ) (H.galE σ) :=
  H.actsAs_gal T.j σ

def sQ (g : R.GG) : H.EQ →ₐ[ℚ] Qb := T.carry (H.sigmaOf g)

/- English proof (translation)
Establish `h` using `T.galE_acts (H.sigmaOf g)`. Establish `hg : H.galE (H.sigmaOf g) = g` using `(H.gal).apply_symm_apply g`. Rewrite `h` using `[hg]`. Then use the resulting hypothesis.
-/
theorem sQ_acts (g : R.GG) : H.ActsAs (T.sQ g) g := by
  have h := T.galE_acts (H.sigmaOf g)
  have hg : H.galE (H.sigmaOf g) = g := (H.gal).apply_symm_apply g
  rwa [hg] at h

/- English proof (translation)
Introduce `g g' h`. Establish `h1` using `T.sQ_acts g`. Establish `h2` using `T.sQ_acts g'`. Rewrite `h1` using `[h]`. Establish `e : H.gal.symm g = H.gal.symm g'` using `AlgEquiv.ext fun x => T.j.toRingHom.injective ((h1 T.j x).symm.trans (h2 T.j x))`.

Conclude with `H.gal.symm.injective e`.
-/
theorem sQ_injective : Function.Injective T.sQ := by
  intro g g' h
  have h1 := T.sQ_acts g
  have h2 := T.sQ_acts g'
  rw [h] at h1
  have e : H.gal.symm g = H.gal.symm g' :=
    AlgEquiv.ext fun x => T.j.toRingHom.injective ((h1 T.j x).symm.trans (h2 T.j x))
  exact H.gal.symm.injective e

include T in

/- English proof (translation)
Set `f' : H.E →ₐ[ℚ] Qb` to `s.comp (T.iso : H.E →ₐ[ℚ] H.EQ)`. Set `σ : H.E ≃ₐ[ℚ] H.E` to `(H.jOf f').trans T.iso.symm`. Establish `hσ : T.carry σ = s`. Use extensionality with `y`. Use `show T.j (T.iso.symm (H.jOf f' (T.iso.symm y))) = s y`.

Rewrite using `[← T.iso_coe, AlgEquiv.apply_symm_apply, H.jOf_coe]`. Use `show s (T.iso (T.iso.symm y)) = s y`. Rewrite using `[AlgEquiv.apply_symm_apply]`. Use `⟨H.galE σ, hσ ▸ T.galE_acts σ, fun g hg => ?_⟩` and prove the remaining obligations. Conclude with `hg.label_unique (hσ ▸ T.galE_acts σ)`.
-/
theorem label (s : H.EQ →ₐ[ℚ] Qb) : ∃! g : R.GG, H.ActsAs s g := by
  let f' : H.E →ₐ[ℚ] Qb := s.comp (T.iso : H.E →ₐ[ℚ] H.EQ)
  let σ : H.E ≃ₐ[ℚ] H.E := (H.jOf f').trans T.iso.symm
  have hσ : T.carry σ = s := by
    ext y
    show T.j (T.iso.symm (H.jOf f' (T.iso.symm y))) = s y
    rw [← T.iso_coe, AlgEquiv.apply_symm_apply, H.jOf_coe]
    show s (T.iso (T.iso.symm y)) = s y
    rw [AlgEquiv.apply_symm_apply]
  refine ⟨H.galE σ, hσ ▸ T.galE_acts σ, fun g hg => ?_⟩
  exact hg.label_unique (hσ ▸ T.galE_acts σ)

/- English proof (translation)
Rewrite using `[Frame.sQ, carry_iso, T.phi0]`. Both sides reduce to the same expression.
-/
theorem emb_eq (g : R.GG) (x : H.E) : H.emb g x = T.ι (T.sQ g (T.iso x)) := by
  rw [Frame.sQ, carry_iso, T.phi0]
  rfl

/- English proof (translation)
Establish `h1 : s (T.iso x) = T.j (H.gal.symm g x)` using `hs T.j x`. Rewrite using `[h1, T.phi0]`. Both sides reduce to the same expression.
-/
theorem emb_eq_of_acts {g : R.GG} {s : H.EQ →ₐ[ℚ] Qb} (hs : H.ActsAs s g) (x : H.E) :
    H.emb g x = T.ι (s (T.iso x)) := by
  have h1 : s (T.iso x) = T.j (H.gal.symm g x) := hs T.j x
  rw [h1, T.phi0]
  rfl

/- English proof (translation)
The claim follows from `(T.sQ_acts g).sqrt_d x hx`.
-/
theorem sQ_sqrt_d (g : R.GG) (x : H.EQ) (hx : (x : Qb) ∈ sqrts (-(H.d : ℤ))) :
    T.sQ g x = (((g.1.2 : ℤˣ) : ℤ) : Qb) * x := (T.sQ_acts g).sqrt_d x hx

/- English proof (translation)
Set `j : H.E →ₐ[ℚ] Qb` to `IsAlgClosed.lift`. Set `_ : Algebra H.E Qb` to `j.toRingHom.toAlgebra`. Set `_ : Algebra H.E ℂ` to `H.φ₀.toAlgebra`. Establish `: Algebra.IsAlgebraic H.E Qb`. Establish `: IsScalarTower ℚ H.E Qb` using `IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm`.

Establish `: Algebra.IsAlgebraic ℚ Qb` using `AlgebraicClosure.isAlgebraic ℚ`. Conclude with `Algebra.IsAlgebraic.tower_top (K := ℚ) H.E`. Set `ι : Qb →ₐ[H.E] ℂ` to `IsAlgClosed.lift`. Conclude with `⟨⟨j, ι.toRingHom, fun x => ι.commutes x⟩⟩`.
-/
theorem «exists» (H : Formalism.BasicNotions.Host R) : Nonempty (Frame H) := by
  let j : H.E →ₐ[ℚ] Qb := IsAlgClosed.lift
  let _ : Algebra H.E Qb := j.toRingHom.toAlgebra
  let _ : Algebra H.E ℂ := H.φ₀.toAlgebra
  have : Algebra.IsAlgebraic H.E Qb := by
    have : IsScalarTower ℚ H.E Qb := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
    have : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
    exact Algebra.IsAlgebraic.tower_top (K := ℚ) H.E
  let ι : Qb →ₐ[H.E] ℂ := IsAlgClosed.lift
  exact ⟨⟨j, ι.toRingHom, fun x => ι.commutes x⟩⟩

end Frame

def realPl {R : Ranks} (H : Formalism.BasicNotions.Host R) (g : R.Psi) : InfinitePlace H.F :=
  InfinitePlace.mk ((H.emb g).comp H.F.subtype)

def RealPlBij {R : Ranks} (H : Formalism.BasicNotions.Host R) : Prop := Function.Bijective (realPl H)

structure HostTied (D : D7) where

  fr : Frame D.host

  jLL : D.what₂.LL →+* Qb

  embLL : ∀ y : D.what₂.LL, fr.ι (jLL y) = D.what₂.embLL y

namespace HostTied

variable {D : D7} (T : HostTied D)

/- English proof (translation)
Apply `T.fr.ι.injective` to reduce the goal to its premises. Rewrite using `[T.embLL, T.fr.phi0, ← D.embE_φ₀]`. Both sides reduce to the same expression.
-/
theorem embE (x : D.host.E) : T.jLL (D.embE x) = T.fr.j x := by
  apply T.fr.ι.injective
  rw [T.embLL, T.fr.phi0, ← D.embE_φ₀]; rfl

def LLQ : Fld := T.jLL.toRatAlgHom.fieldRange

/- English proof (translation)
Introduce `y hy`. Establish `hy' : y ∈ T.fr.j.fieldRange` using `by rw [T.fr.range]; exact hy`. Take `⟨x, rfl⟩` from `hy'`. Conclude with `⟨D.embE x, T.embE x⟩`.
-/
theorem EQ_le_LLQ : D.host.EQ ≤ T.LLQ := by
  intro y hy
  have hy' : y ∈ T.fr.j.fieldRange := by rw [T.fr.range]; exact hy
  obtain ⟨x, rfl⟩ := hy'
  exact ⟨D.embE x, T.embE x⟩

/- English proof (translation)
Set `jLL : D.what₂.LL →ₐ[ℚ] Qb` to `IsAlgClosed.lift`. Set `_ : Algebra D.what₂.LL Qb` to `jLL.toRingHom.toAlgebra`. Set `_ : Algebra D.what₂.LL ℂ` to `D.what₂.embLL.toAlgebra`. Establish `: Algebra.IsAlgebraic D.what₂.LL Qb`. Establish `: IsScalarTower ℚ D.what₂.LL Qb` using `IsScalarTower.of_algebraMap_eq fun x => (jLL.commutes x).symm`.

Establish `: Algebra.IsAlgebraic ℚ Qb` using `AlgebraicClosure.isAlgebraic ℚ`. Conclude with `Algebra.IsAlgebraic.tower_top (K := ℚ) D.what₂.LL`. Set `ι : Qb →ₐ[D.what₂.LL] ℂ` to `IsAlgClosed.lift`. Set `j : D.host.E →ₐ[ℚ] Qb` to `(jLL.toRingHom.comp D.embE).toRatAlgHom`. Use `⟨⟨⟨j, ι.toRingHom, fun x => ?_⟩, jLL.toRingHom, fun y => ι.commutes y⟩⟩` and prove the remaining obligations.

Use `show ι (jLL (D.embE x)) = _`. Rewrite using `[← D.embE_φ₀]`. Conclude with `ι.commutes (D.embE x)`.
-/
theorem «exists» (D : D7) : Nonempty (HostTied D) := by
  let jLL : D.what₂.LL →ₐ[ℚ] Qb := IsAlgClosed.lift
  let _ : Algebra D.what₂.LL Qb := jLL.toRingHom.toAlgebra
  let _ : Algebra D.what₂.LL ℂ := D.what₂.embLL.toAlgebra
  have : Algebra.IsAlgebraic D.what₂.LL Qb := by
    have : IsScalarTower ℚ D.what₂.LL Qb := IsScalarTower.of_algebraMap_eq fun x => (jLL.commutes x).symm
    have : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
    exact Algebra.IsAlgebraic.tower_top (K := ℚ) D.what₂.LL
  let ι : Qb →ₐ[D.what₂.LL] ℂ := IsAlgClosed.lift
  let j : D.host.E →ₐ[ℚ] Qb := (jLL.toRingHom.comp D.embE).toRatAlgHom
  refine ⟨⟨⟨j, ι.toRingHom, fun x => ?_⟩, jLL.toRingHom, fun y => ι.commutes y⟩⟩
  show ι (jLL (D.embE x)) = _
  rw [← D.embE_φ₀]
  exact ι.commutes (D.embE x)

end HostTied

end Formalism.L2.Host

import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LamXEquivariant
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsScale

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PointLattice

section General

open Formalism.UG Formalism.UG.P IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

/- English proof (translation)
Take `⟨d, hd, hda⟩` from `levelaf_denom (E := E) a`. Take `⟨b, t, ht, hbt⟩` from `csGlob_approx csGlob_intAdApprox (d * c) (mul_ne_zero hd hc) _ hda`. Use `⟨(algebraMap (𝓞 F) E d)⁻¹ * algebraMap (𝓞 E) E b, t, ht, ?_⟩` and prove the remaining obligations. Establish `he : algebraMap (𝓞 F) E d ≠ 0` using `adelstab_algebraMap_ne_zero d hd`. Establish `hinv : ι ((algebraMap (𝓞 F) E d)⁻¹) * levelafC E d = 1`.

Rewrite using `[← adelstab_incl_C, ← map_mul, inv_mul_cancel₀ he, map_one]`. Establish `h2 : a = ι ((algebraMap (𝓞 F) E d)⁻¹) * (levelafC E d * a)`. Rewrite using `[← mul_assoc, hinv, one_mul]`. Rewrite using `[h2, hbt, levelafC_mul, map_mul]`. Take the linear combination `(levelafC E c * t) * hinv`.
-/
theorem exists_approx (c : 𝓞 F) (hc : c ≠ 0) (a : 𝒜) :
    ∃ x : E, ∃ w ∈ 𝒮, a = ι x + levelafC E c * w := by
  obtain ⟨d, hd, hda⟩ := levelaf_denom (E := E) a
  obtain ⟨b, t, ht, hbt⟩ := csGlob_approx csGlob_intAdApprox (d * c) (mul_ne_zero hd hc) _ hda
  refine ⟨(algebraMap (𝓞 F) E d)⁻¹ * algebraMap (𝓞 E) E b, t, ht, ?_⟩
  have he : algebraMap (𝓞 F) E d ≠ 0 := adelstab_algebraMap_ne_zero d hd
  have hinv : ι ((algebraMap (𝓞 F) E d)⁻¹) * levelafC E d = 1 := by
    rw [← adelstab_incl_C, ← map_mul, inv_mul_cancel₀ he, map_one]
  have h2 : a = ι ((algebraMap (𝓞 F) E d)⁻¹) * (levelafC E d * a) := by
    rw [← mul_assoc, hinv, one_mul]
  rw [h2, hbt, levelafC_mul, map_mul]
  linear_combination (levelafC E c * t) * hinv

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨e, csGlob_int (F := F) e he⟩, rfl⟩`.
-/
theorem mem_range_of_incl {e : E} (he : ι e ∈ 𝒮) : e ∈ (algebraMap (𝓞 E) E).range :=
  ⟨⟨e, csGlob_int (F := F) e he⟩, rfl⟩

variable (σ : E →ₐ[F] E) (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E))
  (hdual : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, hform (σ : E →+* E) J y x ∈ (algebraMap (𝓞 E) E).range)

include hdual

omit [NumberField F] [DecidableEq n] in
/- English proof (translation)
Introduce `x hx y hy`. Take `⟨b, hb⟩` from `(hdual y).1 hy x hx`. Rewrite using `[Int.cast_one, one_mul, ← hb]`. Conclude with `NumberField.RingOfIntegers.isIntegral_coe b`.
-/
theorem integral_of_selfDual :
    ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (((1 : ℤ) : E) * hform (σ : E →+* E) J x y) := by
  intro x hx y hy
  obtain ⟨b, hb⟩ := (hdual y).1 hy x hx
  rw [Int.cast_one, one_mul, ← hb]
  exact NumberField.RingOfIntegers.isIntegral_coe b

/- English proof (translation)
Take `⟨m, hm0, hm⟩` from `csGlob_single Λ hspan`. Establish `hc : ((m : 𝓞 F)) ≠ 0` using `Int.cast_ne_zero.mpr hm0`. Establish `hC : ∀ v : n → 𝒜, (∀ i, v i ∈ 𝒮) → (fun i => levelafC E (m : 𝓞 F) * v i) ∈ latS (F` using `F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ := by`. Introduce `v hv`. Establish `hk : ∀ k, (fun i => ι ((Pi.single k (m : E) : n → E) i)) ∈ latS (F` using `F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ := fun k => Submodule.subset_span ⟨_, hm k, rfl⟩`.

Establish `heq : (fun i => levelafC E (m : 𝓞 F) * v i) = ∑ k, (⟨v k, hv k⟩ : 𝒮) • (fun i => ι ((Pi.single k (m : E) : n → E) i))`. Use function extensionality and compare the values at `i`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single i]`. Simplify using `[Pi.single_apply, Subring.smul_def, ← adelstab_incl_C, mul_comm]`. Introduce `k _ hki`.

Simplify using `[Pi.single_apply, Ne.symm hki]`. Introduce `hi`. Conclude with `absurd (Finset.mem_univ i) hi`. Rewrite using `[heq]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hk k)`.

Use `choose x w hw hxw using fun i => exists_approx (E := E) (m : 𝓞 F) hc (z i)`. Establish `hint` using `integral_of_selfDual σ J Λ hdual`. Establish `hzc` using `hC w hw`. Establish `hz' : z = (fun i => ι (x i)) + (fun i => levelafC E (m : 𝓞 F) * w i)` using `funext hxw`. Establish `hx : x ∈ Λ`.

Use `(hdual x).2 fun y hy => ?_` and prove the remaining obligations. Establish `hyS : (fun i => ι (y i)) ∈ latS (F` using `F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ := Submodule.subset_span ⟨y, hy, rfl⟩`. Establish `h1` using `hz _ hyS`. Establish `h2` using `csScale_latS σ J Λ 1 hint hyS hzc`. Rewrite `h2` using `[Int.cast_one, map_one, one_mul]`.

Rewrite `h1` using `[hz', csScale_hform_add_right, csScale_hform_incl]`. Use `mem_range_of_incl (F := F) ?_` and prove the remaining obligations. Establish `h3` using `sub_mem h1 h2`. Rewrite `h3` using `[add_sub_cancel_right]`. Then use the resulting hypothesis. Rewrite using `[hz']`.

Conclude with `add_mem (Submodule.subset_span ⟨x, hx, rfl⟩) hzc`.
-/
theorem mem_latS_of_integral (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) (z : n → 𝒜)
    (hz : ∀ w ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ,
      hform (sigR σ (FiniteAdeleRing (𝓞 F) F)) (J.map ι) w z ∈ 𝒮) :
    z ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ := by
  obtain ⟨m, hm0, hm⟩ := csGlob_single Λ hspan
  have hc : ((m : 𝓞 F)) ≠ 0 := Int.cast_ne_zero.mpr hm0
  have hC : ∀ v : n → 𝒜, (∀ i, v i ∈ 𝒮) →
      (fun i => levelafC E (m : 𝓞 F) * v i) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ := by
    intro v hv
    have hk : ∀ k, (fun i => ι ((Pi.single k (m : E) : n → E) i)) ∈
        latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ :=
      fun k => Submodule.subset_span ⟨_, hm k, rfl⟩
    have heq : (fun i => levelafC E (m : 𝓞 F) * v i) =
        ∑ k, (⟨v k, hv k⟩ : 𝒮) • (fun i => ι ((Pi.single k (m : E) : n → E) i)) := by
      funext i
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · simp [Pi.single_apply, Subring.smul_def, ← adelstab_incl_C, mul_comm]
      · intro k _ hki
        simp [Pi.single_apply, Ne.symm hki]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rw [heq]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hk k)
  choose x w hw hxw using fun i => exists_approx (E := E) (m : 𝓞 F) hc (z i)
  have hint := integral_of_selfDual σ J Λ hdual
  have hzc := hC w hw
  have hz' : z = (fun i => ι (x i)) + (fun i => levelafC E (m : 𝓞 F) * w i) := funext hxw
  have hx : x ∈ Λ := by
    refine (hdual x).2 fun y hy => ?_
    have hyS : (fun i => ι (y i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ :=
      Submodule.subset_span ⟨y, hy, rfl⟩
    have h1 := hz _ hyS
    have h2 := csScale_latS σ J Λ 1 hint hyS hzc
    rw [Int.cast_one, map_one, one_mul] at h2
    rw [hz', csScale_hform_add_right, csScale_hform_incl] at h1
    refine mem_range_of_incl (F := F) ?_
    have h3 := sub_mem h1 h2
    rwa [add_sub_cancel_right] at h3
  rw [hz']
  exact add_mem (Submodule.subset_span ⟨x, hx, rfl⟩) hzc

/- English proof (translation)
Establish `hint` using `integral_of_selfDual σ J Λ hdual`. Prove the components needed by the constructor for the conclusion. Introduce `hx y hy`. Establish `h` using `csScale_glob σ J Λ 1 hint g hg hy hx`. Rewrite `h` using `[Int.cast_one, one_mul]`.

Conclude with `mem_range_of_incl (F := F) h`. Introduce `H`. Rewrite using `[csGlob_eq, adelstab_mem_iff]`. Use `mem_latS_of_integral σ J Λ hdual hspan _ fun w hw => ?_` and prove the remaining obligations. Take `⟨u, hu⟩ : ∃ u : n → 𝒜, u = ((g : GL n 𝒜) : Matrix n n 𝒜) *ᵥ w` from `⟨_, rfl⟩`.

Establish `hw' : w = ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u`. Rewrite using `[hu, mulVec_mulVec, Units.inv_mul, one_mulVec]`. Establish `huS` using `csSpan_back csGlob_intAdApprox Λ hfin hspan g u (by rw [← hw']; exact hw)`. Establish `h` using `csDual_span σ J (CS.globLat g Λ) x H u huS`. Establish `hU : Formalism.UG.cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) * J.map ι * ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) = J.map ι` using `inv_mem hg`.

Rewrite using `[hw', hform_mulVec, hU]`. Conclude with `h`.
-/
theorem globLat_selfDual (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) (g : GL n 𝒜)
    (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) (x : n → E) :
    x ∈ CS.globLat g Λ ↔
      ∀ y ∈ CS.globLat g Λ, hform (σ : E →+* E) J y x ∈ (algebraMap (𝓞 E) E).range := by
  have hint := integral_of_selfDual σ J Λ hdual
  constructor
  · intro hx y hy
    have h := csScale_glob σ J Λ 1 hint g hg hy hx
    rw [Int.cast_one, one_mul] at h
    exact mem_range_of_incl (F := F) h
  · intro H
    rw [csGlob_eq, adelstab_mem_iff]
    refine mem_latS_of_integral σ J Λ hdual hspan _ fun w hw => ?_
    obtain ⟨u, hu⟩ : ∃ u : n → 𝒜, u = ((g : GL n 𝒜) : Matrix n n 𝒜) *ᵥ w := ⟨_, rfl⟩
    have hw' : w = ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u := by
      rw [hu, mulVec_mulVec, Units.inv_mul, one_mulVec]
    have huS := csSpan_back csGlob_intAdApprox Λ hfin hspan g u (by rw [← hw']; exact hw)
    have h := csDual_span σ J (CS.globLat g Λ) x H u huS
    have hU : Formalism.UG.cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *
        J.map ι * ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) = J.map ι := inv_mem hg
    rw [hw', hform_mulVec, hU]
    exact h

end General

/- English proof (translation)
Establish `hmem : ∀ (x : I.GA) (y : Fin I.n → I.E), y ∈ Formalism.UG.CS.globLat (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) I.L ↔ I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F` using `I.F) (Af I.F) (y i)) ∈ I.Lf := by`. Establish `hL : I.Lf = Formalism.UG.latS (F` using `I.F) (Af I.F) (IntAf I.F I.E) I.L := by show Submodule.span _ _ = Submodule.span _ _`. Rewrite using `[Set.image_eq_range]`. Both sides reduce to the same expression. Introduce `x y`.

Rewrite using `[Formalism.UG.P.csGlob_eq, Formalism.UG.P.adelstab_mem_iff, hL]`. Both sides reduce to the same expression. Establish `hset : {y : Fin I.n → I.E | I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F` using `I.F) (Af I.F) (y i)) ∈ I.Lf} = (Formalism.UG.CS.globLat (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) I.L : Set (Fin I.n → I.E)) := by`. Use extensionality with `y`. Conclude with `(hmem x y).symm`.

Unfold `lamX`. Rewrite using `[hset, Submodule.span_eq]`.
-/
theorem lamX_eq_globLat (I : AutInst) (x : I.GA) :
    lamX I x = Formalism.UG.CS.globLat (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) I.L := by
  have hmem : ∀ (x : I.GA) (y : Fin I.n → I.E),
      y ∈ Formalism.UG.CS.globLat (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) I.L ↔
        I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ∈ I.Lf := by
    have hL : I.Lf = Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L := by
      show Submodule.span _ _ = Submodule.span _ _
      rw [Set.image_eq_range]
      rfl
    intro x y
    rw [Formalism.UG.P.csGlob_eq, Formalism.UG.P.adelstab_mem_iff, hL]
    rfl
  have hset : {y : Fin I.n → I.E |
      I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ∈ I.Lf} =
      (Formalism.UG.CS.globLat (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) I.L : Set (Fin I.n → I.E)) := by
    ext y
    exact (hmem x y).symm
  unfold lamX
  rw [hset, Submodule.span_eq]

/- English proof (translation)
Introduce `I x`. Establish `hmem : ∀ (x' : I.GA) (y : Fin I.n → I.E), y ∈ Formalism.UG.CS.globLat (x'.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) I.L ↔ I.fmat x'.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F` using `I.F) (Af I.F) (y i)) ∈ I.Lf := by`. Establish `hL : I.Lf = Formalism.UG.latS (F` using `I.F) (Af I.F) (IntAf I.F I.E) I.L := by show Submodule.span _ _ = Submodule.span _ _`. Rewrite using `[Set.image_eq_range]`. Both sides reduce to the same expression.

Introduce `x' y`. Rewrite using `[Formalism.UG.P.csGlob_eq, Formalism.UG.P.adelstab_mem_iff, hL]`. Both sides reduce to the same expression. Establish `hfin : Module.Finite (𝓞 I.E) I.L` using `Module.Finite.iff_fg.mpr I.L_fg`. Establish `hlat` using `Formalism.UG.P.csGlob_lattice (F := I.F) I.L hfin I.L_span (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))`.

Establish `hσ : ((I.cm.sig : I.E →ₐ[I.F] I.E) : I.E →+* I.E) = starRingEnd I.E` using `rfl`. Establish `hdual' : ∀ y, y ∈ I.L ↔ ∀ z ∈ I.L, Formalism.UG.hform ((I.cm.sig : I.E →ₐ[I.F] I.E) : I.E →+* I.E) I.J z y ∈ (algebraMap (𝓞 I.E) I.E).range`. Rewrite using `[hσ]`. Conclude with `I.L_dual`. Use `⟨fun y => ?_, ?_, ?_, fun y => ?_, fun k hk => ?_⟩` and prove the remaining obligations.

Rewrite using `[lamX_eq_globLat]`. Conclude with `hmem x y`. Rewrite using `[lamX_eq_globLat]`. Conclude with `hlat.fg`. Rewrite using `[lamX_eq_globLat]`.

Conclude with `hlat.span_eq_top`. Rewrite using `[lamX_eq_globLat, ← hσ]`. Conclude with `globLat_selfDual I.cm.sig I.J I.L hdual' hfin I.L_span _ x.2.2 y`. Rewrite using `[lamX_eq_globLat, lamX_eq_globLat]`. Use extensionality with `y`.

Rewrite using `[hmem, hmem]`. Establish `hk2 : ((k.2⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf` using `inv_mem (show ((k.2 : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf from hk)`. Establish `e1 : I.fmat (x * k).2⁻¹ = I.fmat k.2⁻¹ * I.fmat x.2⁻¹`. Rewrite using `[Prod.snd_mul, _root_.mul_inv_rev]`. Both sides reduce to the same expression.

Rewrite using `[e1, ← mulVec_mulVec]`. Conclude with `(hk2 _).symm`.
-/
theorem lamX_selfDual : ∀ (I : AutInst) (x : I.GA), (∀ y, y ∈ lamX I x ↔ I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ∈ I.Lf) ∧ (lamX I x).FG ∧ Submodule.span I.E (lamX I x : Set (Fin I.n → I.E)) = ⊤ ∧ (∀ y, y ∈ lamX I x ↔ ∀ z ∈ lamX I x, Formalism.UG.hform (starRingEnd I.E) I.J z y ∈ (algebraMap (𝓞 I.E) I.E).range) ∧ ∀ k : I.GA, k.2 ∈ I.Kset → lamX I (x * k) = lamX I x := by
  intro I x
  have hmem : ∀ (x' : I.GA) (y : Fin I.n → I.E),
      y ∈ Formalism.UG.CS.globLat (x'.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) I.L ↔
        I.fmat x'.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ∈ I.Lf := by
    have hL : I.Lf = Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L := by
      show Submodule.span _ _ = Submodule.span _ _
      rw [Set.image_eq_range]
      rfl
    intro x' y
    rw [Formalism.UG.P.csGlob_eq, Formalism.UG.P.adelstab_mem_iff, hL]
    rfl
  have hfin : Module.Finite (𝓞 I.E) I.L := Module.Finite.iff_fg.mpr I.L_fg
  have hlat := Formalism.UG.P.csGlob_lattice (F := I.F) I.L hfin I.L_span
    (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))
  have hσ : ((I.cm.sig : I.E →ₐ[I.F] I.E) : I.E →+* I.E) = starRingEnd I.E := rfl
  have hdual' : ∀ y, y ∈ I.L ↔ ∀ z ∈ I.L, Formalism.UG.hform ((I.cm.sig : I.E →ₐ[I.F] I.E) : I.E →+* I.E)
      I.J z y ∈ (algebraMap (𝓞 I.E) I.E).range := by
    rw [hσ]
    exact I.L_dual
  refine ⟨fun y => ?_, ?_, ?_, fun y => ?_, fun k hk => ?_⟩
  · rw [lamX_eq_globLat]
    exact hmem x y
  · rw [lamX_eq_globLat]
    exact hlat.fg
  · rw [lamX_eq_globLat]
    exact hlat.span_eq_top
  · rw [lamX_eq_globLat, ← hσ]
    exact globLat_selfDual I.cm.sig I.J I.L hdual' hfin I.L_span _ x.2.2 y
  · rw [lamX_eq_globLat, lamX_eq_globLat]
    ext y
    rw [hmem, hmem]
    have hk2 : ((k.2⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf :=
      inv_mem (show ((k.2 : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf from hk)
    have e1 : I.fmat (x * k).2⁻¹ = I.fmat k.2⁻¹ * I.fmat x.2⁻¹ := by
      rw [Prod.snd_mul, _root_.mul_inv_rev]
      rfl
    rw [e1, ← mulVec_mulVec]
    exact (hk2 _).symm

end GlobalTheory.PointLattice

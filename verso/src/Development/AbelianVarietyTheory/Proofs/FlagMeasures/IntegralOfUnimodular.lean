import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceOneIntegerConjDiffPrimeTo

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

namespace GlobalTheory.EichlerUnip

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

noncomputable def eich (σ w : S.V) (t : E) : S.V →ₗ[E] S.V :=
  LinearMap.id - (S.hT σ).smulRight w + (S.hT w).smulRight σ - t • (S.hT w).smulRight w

/- English proof (translation)
Simplify using `only [eich, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, mul_smul]`.
-/
theorem eich_apply (σ w : S.V) (t : E) (x : S.V) :
    eich S σ w t x = x - S.hT σ x • w + S.hT w x • σ - (t * S.hT w x) • w := by
  simp only [eich, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, mul_smul]

/- English proof (translation)
Rewrite using `[← LinearMap.isSymm_def.mp S.herm x y, starRingEnd_apply]`.
-/
theorem herm (x y : S.V) : S.hT y x = star (S.hT x y) := by
  rw [← LinearMap.isSymm_def.mp S.herm x y, starRingEnd_apply]

/- English proof (translation)
Establish `hσw : S.hT σ w = 0` using `by rw [herm, hwσ, star_zero]`. Rewrite using `[eich_apply, eich_apply]`. Simplify using `only [map_sub, map_add, map_neg, map_smul, LinearMap.neg_apply, smul_eq_mul, hw, hwσ, hσw, mul_zero, sub_zero, add_zero]`. Rewrite using `[← ht]`. Use `module`.
-/
theorem eich_inv (σ w : S.V) (t : E) (hw : S.hT w w = 0) (hwσ : S.hT w σ = 0)
    (ht : t + star t = S.hT σ σ) (x : S.V) : eich S (-σ) w (star t) (eich S σ w t x) = x := by
  have hσw : S.hT σ w = 0 := by rw [herm, hwσ, star_zero]
  rw [eich_apply, eich_apply]
  simp only [map_sub, map_add, map_neg, map_smul,
    LinearMap.neg_apply, smul_eq_mul, hw, hwσ, hσw, mul_zero, sub_zero, add_zero]
  rw [← ht]
  module

/- English proof (translation)
Establish `hσw : S.hT σ w = 0` using `by rw [herm, hwσ, star_zero]`. Rewrite using `[eich_apply, eich_apply]`. Simplify using `only [map_sub, map_add, map_smul, LinearMap.map_smulₛₗ₂, LinearMap.sub_apply, LinearMap.add_apply, smul_eq_mul, hw, hwσ, hσw, mul_zero, sub_zero, add_zero, starRingEnd_apply, star_mul']`. Rewrite using `[herm S w x, herm S σ x, ← ht]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eich_isom (σ w : S.V) (t : E) (hw : S.hT w w = 0) (hwσ : S.hT w σ = 0)
    (ht : t + star t = S.hT σ σ) (x y : S.V) :
    S.hT (eich S σ w t x) (eich S σ w t y) = S.hT x y := by
  have hσw : S.hT σ w = 0 := by rw [herm, hwσ, star_zero]
  rw [eich_apply, eich_apply]
  simp only [map_sub, map_add, map_smul, LinearMap.map_smulₛₗ₂, LinearMap.sub_apply,
    LinearMap.add_apply, smul_eq_mul, hw, hwσ, hσw, mul_zero, sub_zero, add_zero, starRingEnd_apply,
    star_mul']
  rw [herm S w x, herm S σ x, ← ht]
  ring

noncomputable def eichE (σ w : S.V) (t : E) (hw : S.hT w w = 0) (hwσ : S.hT w σ = 0)
    (ht : t + star t = S.hT σ σ) : S.V ≃ₗ[E] S.V :=
  LinearEquiv.ofLinear (eich S σ w t) (eich S (-σ) w (star t))
    (LinearMap.ext fun x => by
      have := eich_inv S (-σ) w (star t) hw (by simp [hwσ]) (by simp [← ht, add_comm]) x
      simpa using this)
    (LinearMap.ext fun x => eich_inv S σ w t hw hwσ ht x)

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.IsUnimodular at hΛ`. Establish `h1 : y ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ` using `by rw [hΛ]; exact hy`. Simplify using `only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one] at h1`. Take `⟨o, ho⟩` from `h1 x hx`. Conclude with `⟨o, ho⟩`.
-/
theorem integral_of_unimodular {Λ : Submodule (𝓞 E) S.V} (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ)
    {x y : S.V} (hx : x ∈ Λ) (hy : y ∈ Λ) : ∃ o : 𝓞 E, (o : E) = S.hT x y := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodular at hΛ
  have h1 : y ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by rw [hΛ]; exact hy
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one] at h1
  obtain ⟨o, ho⟩ := h1 x hx
  exact ⟨o, ho⟩

/- English proof (translation)
Take `⟨o, rfl⟩` from `hc`. Establish `h` using `Λ.smul_mem o hx`. Rewrite `h` using `[← algebraMap_smul E o x]`. Conclude with `h`.
-/
theorem smul_mem_of {Λ : Submodule (𝓞 E) S.V} {c : E} (hc : ∃ o : 𝓞 E, (o : E) = c) {x : S.V}
    (hx : x ∈ Λ) : c • x ∈ Λ := by
  obtain ⟨o, rfl⟩ := hc
  have h := Λ.smul_mem o hx
  rw [← algebraMap_smul E o x] at h
  exact h

/- English proof (translation)
Rewrite using `[eich_apply]`. Take `⟨a, ha⟩` from `integral_of_unimodular S hΛ hσ hx`. Take `⟨b, hb⟩` from `integral_of_unimodular S hΛ hw hx`. Take `⟨o, ho⟩` from `ht`. Establish `hob : ∃ c : 𝓞 E, (c : E) = t * S.hT w x` using `⟨o * b, by rw [← ho, ← hb]; rfl⟩`.

Conclude with `Λ.sub_mem (Λ.add_mem (Λ.sub_mem hx (smul_mem_of S ⟨a, ha⟩ hw)) (smul_mem_of S ⟨b, hb⟩ hσ)) (smul_mem_of S hob hw)`.
-/
theorem eich_mem {Λ : Submodule (𝓞 E) S.V} (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {σ w : S.V} {t : E}
    (hσ : σ ∈ Λ) (hw : w ∈ Λ) (ht : ∃ o : 𝓞 E, (o : E) = t) {x : S.V} (hx : x ∈ Λ) :
    eich S σ w t x ∈ Λ := by
  rw [eich_apply]
  obtain ⟨a, ha⟩ := integral_of_unimodular S hΛ hσ hx
  obtain ⟨b, hb⟩ := integral_of_unimodular S hΛ hw hx
  obtain ⟨o, ho⟩ := ht
  have hob : ∃ c : 𝓞 E, (c : E) = t * S.hT w x := ⟨o * b, by rw [← ho, ← hb]; rfl⟩
  exact Λ.sub_mem (Λ.add_mem (Λ.sub_mem hx (smul_mem_of S ⟨a, ha⟩ hw)) (smul_mem_of S ⟨b, hb⟩ hσ))
    (smul_mem_of S hob hw)

/- English proof (translation)
Take `⟨o, rfl⟩` from `ht`. Conclude with `⟨⟨star (o : E), (RingOfIntegers.isIntegral_coe o).map (starRingEnd E).toIntAlgHom⟩, rfl⟩`.
-/
theorem star_int {t : E} (ht : ∃ o : 𝓞 E, (o : E) = t) : ∃ o : 𝓞 E, (o : E) = star t := by
  obtain ⟨o, rfl⟩ := ht
  exact ⟨⟨star (o : E), (RingOfIntegers.isIntegral_coe o).map (starRingEnd E).toIntAlgHom⟩, rfl⟩

/- English proof (translation)
Establish `key : ∀ a, ∀ v ∈ Submodule.span E (Set.range F.fl.e), S.hT (F.fl.e a) v = 0`. Introduce `a v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem u hu => obtain ⟨b, rfl⟩ := hu`. Conclude with `F.fl.e_iso a b`.

Consider the case `zero => simp`. Consider the case `add u v _ _ hu hv => simp [hu, hv]`. Consider the case `smul c u _ hu => simp [hu]`. Establish `key2 : ∀ u ∈ Submodule.span E (Set.range F.fl.e), S.hT u y = 0`. Introduce `u hu`.

Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem u hu => obtain ⟨a, rfl⟩ := hu`. Conclude with `key a y hy`. Consider the case `zero => simp`. Consider the case `add u v _ _ hu hv => simp [hu, hv]`.

Consider the case `smul c u _ hu => simp [hu]`. Conclude with `key2 x hx`.
-/
theorem iso_X {r : ℕ} {T : E} (F : LFlag S r T) {x y : S.V} (hx : x ∈ Xsp F) (hy : y ∈ Xsp F) :
    S.hT x y = 0 := by
  have key : ∀ a, ∀ v ∈ Submodule.span E (Set.range F.fl.e), S.hT (F.fl.e a) v = 0 := by
    intro a v hv
    induction hv using Submodule.span_induction with
    | mem u hu => obtain ⟨b, rfl⟩ := hu; exact F.fl.e_iso a b
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul c u _ hu => simp [hu]
  have key2 : ∀ u ∈ Submodule.span E (Set.range F.fl.e), S.hT u y = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu => obtain ⟨a, rfl⟩ := hu; exact key a y hy
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul c u _ hu => simp [hu]
  exact key2 x hx

/- English proof (translation)
Simplify using `[orth, Submodule.mem_iInf, LinearMap.mem_ker]`.
-/
theorem mem_orth {U : Submodule E S.V} {y : S.V} : y ∈ orth S U ↔ ∀ x ∈ U, S.hT x y = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

/- English proof (translation)
Take `⟨hσΛ, hσX⟩` from `Submodule.mem_inf.mp hσ`. Take `⟨hwΛ, hwX⟩` from `Submodule.mem_inf.mp hw`. Establish `hσX' : σ ∈ orth S (Xsp F)` using `hσX`. Establish `hwX' : w ∈ Xsp F` using `hwX`. Establish `hww : S.hT w w = 0` using `iso_X S F hwX' hwX'`.

Establish `hwσ : S.hT w σ = 0` using `(mem_orth S).mp hσX' w hwX'`. Establish `hσσ : star (S.hT σ σ) = S.hT σ σ` using `(herm S σ σ).symm`. Take `⟨oσ, hoσ⟩` from `integral_of_unimodular S hΛ hσΛ hσΛ`. Establish `ht : (θ : E) * S.hT σ σ + star ((θ : E) * S.hT σ σ) = S.hT σ σ`. Rewrite using `[star_mul', hσσ]`.

Take the linear combination `(S.hT σ σ) * hθ`. Establish `htI : ∃ o : 𝓞 E, (o : E) = (θ : E) * S.hT σ σ` using `⟨θ * oσ, by rw [← hoσ]; rfl⟩`. Establish `hfix : ∀ x ∈ Xsp F, eich S σ w ((θ : E) * S.hT σ σ) x = x`. Introduce `x hx`. Establish `h1 : S.hT σ x = 0` using `by rw [herm, (mem_orth S).mp hσX' x hx, star_zero]`.

Establish `h2 : S.hT w x = 0` using `iso_X S F hwX' hx`. Rewrite using `[eich_apply, h1, h2]`. Simplify using the standard rewrite rules. Use `⟨eichE S σ w _ hww hwσ ht, ?_, _, hfix, fun x => eich_apply S σ w _ x⟩` and prove the remaining obligations. Simplify using `only [NLam, Set.mem_setOf_eq, IsAutLam]`.

Use `⟨⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `∀ x y, S.hT (eich S σ w _ x) (eich S σ w _ y) = S.hT x y`. Conclude with `fun x y => eich_isom S σ w _ hww hwσ ht x y`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Conclude with `eich_mem S hΛ hσΛ hwΛ htI hy`. Introduce `y hy`. Use `⟨(eichE S σ w _ hww hwσ ht).symm y, ?_, by simp⟩` and prove the remaining obligations. Conclude with `eich_mem S hΛ (Λ.neg_mem hσΛ) hwΛ (star_int htI) hy`. Introduce `j x hx`.

Establish `hxX : x ∈ Xsp F` using `Submodule.span_mono (Set.image_subset_range _ _) hx`. Express the relevant statement in the definitionally equal form `eich S σ w _ x - x ∈ _`. Rewrite using `[hfix x hxX, sub_self]`. Conclude with `Submodule.zero_mem _`. Introduce `x hx`.

Establish `h2 : S.hT w x = 0` using `(mem_orth S).mp hx w hwX'`. Establish `: eich S σ w ((θ : E) * S.hT σ σ) x - x = -(S.hT σ x • w)`. Rewrite using `[eich_apply, h2]`. Use `module`. Express the relevant statement in the definitionally equal form `eich S σ w _ x - x ∈ _`.

Rewrite using `[this]`. Conclude with `(Xsp F).neg_mem ((Xsp F).smul_mem _ hwX')`.
-/
theorem exists_eichler (θ : 𝓞 E) (hθ : (θ : E) + star (θ : E) = 1) {r : ℕ} {T : E} (F : LFlag S r T)
    (Λ : Submodule (𝓞 E) S.V) (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (σ : S.V) (hσ : σ ∈ Lrep Λ F)
    (w : S.V) (hw : w ∈ XLam Λ F) :
    ∃ n ∈ NLam Λ F, ∃ t : E, (∀ x ∈ Xsp F, n x = x) ∧
      ∀ x, n x = x - S.hT σ x • w + S.hT w x • σ - (t * S.hT w x) • w := by
  obtain ⟨hσΛ, hσX⟩ := Submodule.mem_inf.mp hσ
  obtain ⟨hwΛ, hwX⟩ := Submodule.mem_inf.mp hw
  have hσX' : σ ∈ orth S (Xsp F) := hσX
  have hwX' : w ∈ Xsp F := hwX
  have hww : S.hT w w = 0 := iso_X S F hwX' hwX'
  have hwσ : S.hT w σ = 0 := (mem_orth S).mp hσX' w hwX'
  have hσσ : star (S.hT σ σ) = S.hT σ σ := (herm S σ σ).symm
  obtain ⟨oσ, hoσ⟩ := integral_of_unimodular S hΛ hσΛ hσΛ
  have ht : (θ : E) * S.hT σ σ + star ((θ : E) * S.hT σ σ) = S.hT σ σ := by
    rw [star_mul', hσσ]
    linear_combination (S.hT σ σ) * hθ
  have htI : ∃ o : 𝓞 E, (o : E) = (θ : E) * S.hT σ σ := ⟨θ * oσ, by rw [← hoσ]; rfl⟩
  have hfix : ∀ x ∈ Xsp F, eich S σ w ((θ : E) * S.hT σ σ) x = x := by
    intro x hx
    have h1 : S.hT σ x = 0 := by rw [herm, (mem_orth S).mp hσX' x hx, star_zero]
    have h2 : S.hT w x = 0 := iso_X S F hwX' hx
    rw [eich_apply, h1, h2]
    simp
  refine ⟨eichE S σ w _ hww hwσ ht, ?_, _, hfix, fun x => eich_apply S σ w _ x⟩
  simp only [NLam, Set.mem_setOf_eq, IsAutLam]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · change ∀ x y, S.hT (eich S σ w _ x) (eich S σ w _ y) = S.hT x y
    exact fun x y => eich_isom S σ w _ hww hwσ ht x y
  · apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact eich_mem S hΛ hσΛ hwΛ htI hy
    · intro y hy
      refine ⟨(eichE S σ w _ hww hwσ ht).symm y, ?_, by simp⟩
      exact eich_mem S hΛ (Λ.neg_mem hσΛ) hwΛ (star_int htI) hy
  · intro j x hx
    have hxX : x ∈ Xsp F := Submodule.span_mono (Set.image_subset_range _ _) hx
    change eich S σ w _ x - x ∈ _
    rw [hfix x hxX, sub_self]
    exact Submodule.zero_mem _
  · intro x hx
    have h2 : S.hT w x = 0 := (mem_orth S).mp hx w hwX'
    have : eich S σ w ((θ : E) * S.hT σ σ) x - x = -(S.hT σ x • w) := by
      rw [eich_apply, h2]
      module
    change eich S σ w _ x - x ∈ _
    rw [this]
    exact (Xsp F).neg_mem ((Xsp F).smul_mem _ hwX')

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D T F Λ hΛ σ hσ w hw`. Take `⟨θ, hθ, -⟩` from `GlobalTheory.TraceOne.exists_trace_one D 2 Nat.prime_two`. Use `exists_eichler (hS D) θ ?_ F Λ hΛ σ hσ w hw` and prove the remaining obligations. Establish `h` using `congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) hθ`. Simplify using `only [map_add, map_one, GlobalTheory.InertSign.sgO_coe] at h`.

Rewrite using `[GlobalTheory.NormSum.AdLattice.star_eq_conj D]`. Conclude with `h`.
-/
theorem eichler_mem_unipotent : ∀ (D : D7) (T : D.host.E) (F : Fg D T) (Λ : LatV D), Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ → ∀ σ ∈ Lrep Λ F, ∀ w ∈ XLam Λ F, ∃ n ∈ NLam Λ F, ∃ t : D.host.E, (∀ x ∈ Xsp F, n x = x) ∧ ∀ x, n x = x - (hS D).hT σ x • w + (hS D).hT w x • σ - (t * (hS D).hT w x) • w := by
  intro D T F Λ hΛ σ hσ w hw
  obtain ⟨θ, hθ, -⟩ := GlobalTheory.TraceOne.exists_trace_one D 2 Nat.prime_two
  refine exists_eichler (hS D) θ ?_ F Λ hΛ σ hσ w hw
  have h := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) hθ
  simp only [map_add, map_one, GlobalTheory.InertSign.sgO_coe] at h
  rw [GlobalTheory.NormSum.AdLattice.star_eq_conj D]
  exact h

end GlobalTheory.EichlerUnip

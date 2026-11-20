import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.NTheta IsDedekindDomain NumberField GlobalTheory.SplitHecke
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicU.SplitFrame

variable {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul a x => rfl`.
-/
theorem map_map_sndA {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (u : HeightOneSpectrum (𝓞 F))
    (z : AF F ⊗[F] E) :
    Algebra.TensorProduct.map (evalV F u) (AlgHom.id F E) (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) =
      compFin F E u z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

/- English proof (translation)
The claim follows from `funext fun i => (map_map_sndA u (e * y i)).trans ((compFin D.host.F D.host.E u).map_mul e (y i))`.
-/
theorem vecLoc_finPart {n : ℕ} (u : HeightOneSpectrum (𝓞 D.host.F)) (e : AE D) (y : Fin n → AE D) :
    vecLoc u (fun i => finPart D (e * y i)) =
      compFin D.host.F D.host.E u e • fun i => compFin D.host.F D.host.E u (y i) :=
  funext fun i => (map_map_sndA u (e * y i)).trans ((compFin D.host.F D.host.E u).map_mul e (y i))

/- English proof (translation)
Take `⟨h1, h2, v', ε, ⟨α, rfl, -, ha⟩, hε⟩` from `he`. Establish `p1 : π e = 1`. Use `(hπ.2.1 (1 - e)).2 (by rw [mul_sub, mul_one, h1, sub_self])` as an intermediate fact. Rewrite `this` using `[map_sub, map_one, sub_eq_zero]`. Conclude with `this.symm`.

Establish `p2 : π (cA D e) = 0` using `(hπ.2.1 _).2 h2`. Establish `p3 : evalV D.host.F v α = 1`. Use `hπ.2.2.1 (pairA D.host.F 0 α)` as an intermediate fact. Rewrite `this` using `[← hε, map_add, p1, p2, add_zero]`. Conclude with `this.symm`.

Establish `hv : v = v'`. Assume the negation of the conclusion as `hne`. Rewrite `p3` using `[ha v hne]`. Conclude with `zero_ne_one p3`. Substitute `hv` using the available equality.

Establish `p4 : compFin D.host.F D.host.E u (e + cA D e) = 0`. Rewrite using `[hε]`. Express the relevant statement in the definitionally equal form `(evalV D.host.F u α) ⊗ₜ[D.host.F] (1 : D.host.E) = 0`. Rewrite using `[ha u hu, TensorProduct.zero_tmul]`. Establish `p5 : e = e * (e + cA D e)` using `by rw [mul_add, h1, h2, add_zero]`.

Rewrite using `[p5, map_mul, p4, mul_zero]`.
-/
theorem compFin_eq_zero (he : IsSplitIdem D e) (hπ : Chart e v π) {u : HeightOneSpectrum (𝓞 D.host.F)}
    (hu : u ≠ v) : compFin D.host.F D.host.E u e = 0 := by
  obtain ⟨h1, h2, v', ε, ⟨α, rfl, -, ha⟩, hε⟩ := he
  have p1 : π e = 1 := by
    have := (hπ.2.1 (1 - e)).2 (by rw [mul_sub, mul_one, h1, sub_self])
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this.symm
  have p2 : π (cA D e) = 0 := (hπ.2.1 _).2 h2
  have p3 : evalV D.host.F v α = 1 := by
    have := hπ.2.2.1 (pairA D.host.F 0 α)
    rw [← hε, map_add, p1, p2, add_zero] at this
    exact this.symm
  have hv : v = v' := by
    by_contra hne
    rw [ha v hne] at p3
    exact zero_ne_one p3
  subst hv
  have p4 : compFin D.host.F D.host.E u (e + cA D e) = 0 := by
    rw [hε]
    change (evalV D.host.F u α) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    rw [ha u hu, TensorProduct.zero_tmul]
  have p5 : e = e * (e + cA D e) := by rw [mul_add, h1, h2, add_zero]
  rw [p5, map_mul, p4, mul_zero]

/- English proof (translation)
Rewrite using `[mem_latHat_iff hL, ← splitIncl_mem_latLoc_iff h, ← hv]`. Use `⟨fun h => h v, fun h u => ?_⟩` and prove the remaining obligations. Distinguish the cases in `huv : u = v`. Substitute `huv` using the available equality. Conclude with `h`.

Rewrite using `[hu u huv]`. Conclude with `zero_mem _`.
-/
theorem mem_latHat_iff_of_support {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {n : ℕ} {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v)
    {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG) {y : Fin n → Af F ⊗[F] E} {z : Fin n → Fv F v}
    (hv : vecLoc v y = splitIncl h τ z) (hu : ∀ u, u ≠ v → vecLoc u y = 0) :
    y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) ↔ z ∈ splitLat τ L := by
  rw [mem_latHat_iff hL, ← splitIncl_mem_latLoc_iff h, ← hv]
  refine ⟨fun h => h v, fun h u => ?_⟩
  by_cases huv : u = v
  · subst huv; exact h
  · rw [hu u huv]; exact zero_mem _

/- English proof (translation)
Establish `: (fun k => π (y k)) = splitVec (chartEmb hπ) (fun k => compFin D.host.F D.host.E v (y k))`. Use function extensionality and compare the values at `fun k => chart_eq_splitProj hπ _`. Rewrite using `[this, splitIncl_splitVec, vecLoc_finPart, compFin_eq_splitIdem he hπ]`.
-/
theorem vecLoc_self (he : IsSplitIdem D e) (hπ : Chart e v π) {n : ℕ} (y : Fin n → AE D) :
    vecLoc v (fun i => finPart D (e * y i)) = splitIncl (isCMExt_host D) (chartEmb hπ) (fun k => π (y k)) := by
  have : (fun k => π (y k)) = splitVec (chartEmb hπ) (fun k => compFin D.host.F D.host.E v (y k)) :=
    funext fun k => chart_eq_splitProj hπ _
  rw [this, splitIncl_splitVec, vecLoc_finPart, compFin_eq_splitIdem he hπ]

/- English proof (translation)
Rewrite using `[vecLoc_finPart, compFin_eq_zero he hπ hu]`. Conclude with `funext fun i => zero_mul _`.
-/
theorem vecLoc_ne (he : IsSplitIdem D e) (hπ : Chart e v π) {n : ℕ} (y : Fin n → AE D)
    (u : HeightOneSpectrum (𝓞 D.host.F)) (hu : u ≠ v) : vecLoc u (fun i => finPart D (e * y i)) = 0 := by
  rw [vecLoc_finPart, compFin_eq_zero he hπ hu]
  exact funext fun i => zero_mul _

/- English proof (translation)
The claim follows from `congrArg (Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E) (hermitianSpaceBaseLattice_eq_frameLattice V)`.
-/
theorem lamHat_eq (V : HSp D) :
    LamHat V = Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (frameLat V : Set (Fin V.rank → D.host.E)) :=
  congrArg (Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E) (hermitianSpaceBaseLattice_eq_frameLattice V)

/- English proof (translation)
Rewrite using `[lamHat_eq]`. Conclude with `mem_latHat_iff_of_support (isCMExt_host D) _ (frameLat_fg V) (vecLoc_self he hπ y) (vecLoc_ne he hπ y)`.
-/
theorem mem_lamHat_iff (he : IsSplitIdem D e) (hπ : Chart e v π) (V : HSp D) (y : Fin V.rank → AE D) :
    (fun i => finPart D (e * y i)) ∈ LamHat V ↔ (fun k => π (y k)) ∈ splitLat (chartEmb hπ) (frameLat V) := by
  rw [lamHat_eq]
  exact mem_latHat_iff_of_support (isCMExt_host D) _ (frameLat_fg V) (vecLoc_self he hπ y) (vecLoc_ne he hπ y)

/- English proof (translation)
Introduce `D e v π he hπ V β`. Use `⟨fun h u => ?_, fun h y => ?_⟩` and prove the remaining obligations. Use `choose y hy using fun k => hπ.1 ((β.1 *ᵥ u) k)`. Establish `h1` using `h y`. Rewrite `h1` using `[mem_lamHat_iff he hπ, show (fun k => π (y k)) = β.1 *ᵥ u from funext hy, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`.

Simplify `h1.symm` using `only [isInt_Ov]`. Rewrite using `[mem_lamHat_iff he hπ, h.mem_iff]`. Simplify using `only [isInt_Ov]`.
-/
theorem frame_iff_isSplitBasis : ∀ {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)}
    {π : AE D →+* Fv D.host.F v}, IsSplitIdem D e → ∀ (hπ : Chart e v π) (V : HSp D)
    (β : GL (Fin V.rank) (Fv D.host.F v)),
    Frame V e π β ↔ GlobalTheory.AdelicU.IsSplitBasis (GlobalTheory.AdelicU.chartEmb hπ) (GlobalTheory.AdelicU.frameLat V) β := by
  intro D e v π he hπ V β
  refine ⟨fun h u => ?_, fun h y => ?_⟩
  · choose y hy using fun k => hπ.1 ((β.1 *ᵥ u) k)
    have h1 := h y
    rw [mem_lamHat_iff he hπ, show (fun k => π (y k)) = β.1 *ᵥ u from funext hy, Matrix.mulVec_mulVec,
      Units.inv_mul, Matrix.one_mulVec] at h1
    simpa only [isInt_Ov] using h1.symm
  · rw [mem_lamHat_iff he hπ, h.mem_iff]
    simp only [isInt_Ov]

end GlobalTheory.AdelicU.SplitFrame

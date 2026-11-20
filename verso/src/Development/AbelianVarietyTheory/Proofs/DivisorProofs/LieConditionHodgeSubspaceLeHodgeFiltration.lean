import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoords
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionModHodgeFiltration
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HTCount

/- English proof (translation)
Use `haveI := o₀.act.hom x`. Conclude with `push_mem_Fil (o₀.act.act x) hh`.
-/
theorem crysAct_mem_Fil {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R]
    {b : GlobalTheory.UPel.HT.Base D R} {N : ℕ} {k : Type} [Field k] {t : Sp k ⟶ Sp R} (o₀ : GlobalTheory.UPel.HT.Obj b N t)
    (x : D.O) {h : HdR o₀.A} (hh : h ∈ Fil o₀.A) : crysAct o₀ x h ∈ Fil o₀.A := by
  haveI := o₀.act.hom x
  exact push_mem_Fil (o₀.act.act x) hh

/- English proof (translation)
Rewrite using `[map_intCast, map_intCast, Int.cast_smul_eq_zsmul]`. Both sides reduce to the same expression.
-/
theorem crysAct_intCast {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R]
    {b : GlobalTheory.UPel.HT.Base D R} {N : ℕ} {k : Type} [Field k] {t : Sp k ⟶ Sp R} (o₀ : GlobalTheory.UPel.HT.Obj b N t)
    (n : ℤ) (h : HdR o₀.A) : crysAct o₀ (algebraMap (𝓞 D.F) D.O (n : 𝓞 D.F)) h = (n : k) • h := by
  rw [map_intCast, map_intCast, Int.cast_smul_eq_zsmul]
  rfl

/- English proof (translation)
Introduce `p _ D R _ b N k _ β s hs o₀`. Rewrite using `[lieZ, Submodule.span_le]`. Introduce and unpack `z ⟨r, lam, c, y, ⟨x, rfl⟩, hlam, rfl⟩`. Use `set T := crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) with hT`. Establish `hω : D.ω * D.ω = (D.tr : 𝓞 D.F) * D.ω - (D.nm : 𝓞 D.F)`.

Rewrite using `[← D.nm_eq, ← D.tr_eq]`. Expand and normalize the polynomial expressions, which then agree. Establish `hT2 : T (T x) = (D.tr : k) • T x - (D.nm : k) • x`. Use `congrArg (fun u => crysAct o₀ (algebraMap (𝓞 D.F) D.O u) x) hω` as an intermediate fact. Simplify using `only [map_mul, map_sub, Module.End.mul_apply, LinearMap.sub_apply] at this`.

Rewrite `this` using `[crysAct_intCast, crysAct_intCast]`. Conclude with `this`. Establish `hρ : β b.ρ * ((D.tr : k) - β b.ρ) = (D.nm : k)`. Use `congrArg β b.ρ_root` as an intermediate fact. Simplify using `only [map_add, map_sub, map_mul, map_pow, map_intCast, map_zero] at this`.

Take the linear combination `-this`. Establish `hy0 : T ((T - ((D.tr : k) - β b.ρ) • 1) x) - β b.ρ • (T - ((D.tr : k) - β b.ρ) • 1) x = 0`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hT2]`. Rewrite using `[← hρ]`. Use `module`.

Take `⟨w, hw, hyw⟩` from `GlobalTheory.HTSummand.lie_mod_fil p D R b N k β s hs o₀ _ (hy0 ▸ zero_mem _)`. Use `set y := (T - ((D.tr : k) - β b.ρ) • 1) x`. Use `set q := (Fil o₀.A).mkQ`. Establish `key : ∀ c' : 𝓞 D.F, q (crysAct o₀ (algebraMap (𝓞 D.F) D.O c') y) = ∑ i, β (b.t i c') • q (w i)`. Introduce `c'`.

Establish `h1 : crysAct o₀ (algebraMap (𝓞 D.F) D.O c') y - ∑ i, crysAct o₀ (algebraMap (𝓞 D.F) D.O c') (w i) ∈ Fil o₀.A`. Use `crysAct_mem_Fil o₀ (algebraMap (𝓞 D.F) D.O c') hyw` as an intermediate fact. Rewrite `this` using `[map_sub, map_sum]`. Then use the resulting hypothesis. Establish `e1 : q (crysAct o₀ (algebraMap (𝓞 D.F) D.O c') y) = q (∑ i, crysAct o₀ (algebraMap (𝓞 D.F) D.O c') (w i))` using `(Submodule.Quotient.eq _).2 h1`. Rewrite using `[e1, map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← map_smul]`. Conclude with `(Submodule.Quotient.eq _).2 (hw i c')`. Rewrite using `[SetLike.mem_coe, ← Submodule.Quotient.mk_eq_zero]`. Express the relevant statement in the definitionally equal form `q _ = 0`.

Simplify using `only [map_sum, map_smul, key, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_smul, hlam, zero_smul, Finset.sum_const_zero]`.
-/
theorem lieZ_le_Fil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (β : R →+* k) (s : Sp k ⟶ Sp R), s = spMap β →
    ∀ o₀ : GlobalTheory.UPel.HT.Obj b N s, GlobalTheory.HTCount.lieZ o₀ β ≤ Fil o₀.A := by
  intro p _ D R _ b N k _ β s hs o₀
  rw [lieZ, Submodule.span_le]
  rintro z ⟨r, lam, c, y, ⟨x, rfl⟩, hlam, rfl⟩
  set T := crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) with hT

  have hω : D.ω * D.ω = (D.tr : 𝓞 D.F) * D.ω - (D.nm : 𝓞 D.F) := by
    rw [← D.nm_eq, ← D.tr_eq]; ring
  have hT2 : T (T x) = (D.tr : k) • T x - (D.nm : k) • x := by
    have := congrArg (fun u => crysAct o₀ (algebraMap (𝓞 D.F) D.O u) x) hω
    simp only [map_mul, map_sub, Module.End.mul_apply, LinearMap.sub_apply] at this
    rw [crysAct_intCast, crysAct_intCast] at this
    exact this

  have hρ : β b.ρ * ((D.tr : k) - β b.ρ) = (D.nm : k) := by
    have := congrArg β b.ρ_root
    simp only [map_add, map_sub, map_mul, map_pow, map_intCast, map_zero] at this
    linear_combination -this

  have hy0 : T ((T - ((D.tr : k) - β b.ρ) • 1) x) - β b.ρ • (T - ((D.tr : k) - β b.ρ) • 1) x = 0 := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hT2]
    rw [← hρ]
    module
  obtain ⟨w, hw, hyw⟩ := GlobalTheory.HTSummand.lie_mod_fil p D R b N k β s hs o₀ _ (hy0 ▸ zero_mem _)
  set y := (T - ((D.tr : k) - β b.ρ) • 1) x
  set q := (Fil o₀.A).mkQ
  have key : ∀ c' : 𝓞 D.F, q (crysAct o₀ (algebraMap (𝓞 D.F) D.O c') y) = ∑ i, β (b.t i c') • q (w i) := by
    intro c'
    have h1 : crysAct o₀ (algebraMap (𝓞 D.F) D.O c') y - ∑ i, crysAct o₀ (algebraMap (𝓞 D.F) D.O c') (w i) ∈ Fil o₀.A := by
      have := crysAct_mem_Fil o₀ (algebraMap (𝓞 D.F) D.O c') hyw
      rwa [map_sub, map_sum] at this
    have e1 : q (crysAct o₀ (algebraMap (𝓞 D.F) D.O c') y) = q (∑ i, crysAct o₀ (algebraMap (𝓞 D.F) D.O c') (w i)) :=
      (Submodule.Quotient.eq _).2 h1
    rw [e1, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_smul]
    exact (Submodule.Quotient.eq _).2 (hw i c')
  rw [SetLike.mem_coe, ← Submodule.Quotient.mk_eq_zero]
  change q _ = 0
  simp only [map_sum, map_smul, key, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hlam, zero_smul, Finset.sum_const_zero]

end GlobalTheory.HTCount

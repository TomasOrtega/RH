import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.LangStep
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.UmgOps
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.HkApply
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.KilledOps
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.ResTyp
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.SliceUmg

noncomputable section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.V.Cm

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

omit [IsTotallyComplex E] in
/- English proof (translation)
Use `haveI : IsEmpty (AutomorphicForm.UPos n n) := ⟨fun p => by have := p.2.2; have := p.1.2.2; omega⟩`. Establish `h1 : AutomorphicForm.unipFundamentalDomain E n n = Set.univ`. Use extensionality with `X`. Simplify using `[AutomorphicForm.unipFundamentalDomain]`. Unfold `AutomorphicForm.constantTerm`.

Rewrite using `[h1, Measure.restrict_univ]`. Establish `h2 : ∀ X : AutomorphicForm.UPos n n → AdeleRing (𝓞 E) E, AutomorphicForm.unipGL X = 1` using `fun X => by`. Rewrite using `[Subsingleton.elim X 0, AutomorphicForm.unipGL_zero]`. Simplify using `only [h2, one_mul]`. Rewrite using `[AutomorphicForm.unipMeasure, Measure.pi_of_empty]`.

Simplify using the standard rewrite rules.
-/
private theorem ct_top {n : ℕ} (φ : GA E n → ℂ) (g : GA E n) : AutomorphicForm.constantTerm n φ g = φ g := by
  haveI : IsEmpty (AutomorphicForm.UPos n n) := ⟨fun p => by have := p.2.2; have := p.1.2.2; omega⟩
  have h1 : AutomorphicForm.unipFundamentalDomain E n n = Set.univ := by
    ext X
    simp [AutomorphicForm.unipFundamentalDomain]
  unfold AutomorphicForm.constantTerm
  rw [h1, Measure.restrict_univ]
  have h2 : ∀ X : AutomorphicForm.UPos n n → AdeleRing (𝓞 E) E, AutomorphicForm.unipGL X = 1 := fun X => by
    rw [Subsingleton.elim X 0, AutomorphicForm.unipGL_zero]
  simp only [h2, one_mul]
  rw [AutomorphicForm.unipMeasure, Measure.pi_of_empty]
  simp

/- English proof (translation)
Introduce `w hw` and use `((((hkOps E n w 0).2.2.2 S φ hw h).2.2.1 k).1) w hw`.
-/
private theorem sph_rt {S : Set (Pl E)} {n : ℕ} {φ : Sm E n} (h : Sph S φ) (k : KA E n) : Sph S (rt E n k φ) :=
  fun w hw => ((((hkOps E n w 0).2.2.2 S φ hw h).2.2.1 k).1) w hw

/- English proof (translation)
The claim follows from `(d.idx ⟨0, h⟩).pos`.
-/
private theorem len_pos {S : Set (Pl E)} {n : ℕ} (d : Dat S n) (h : 0 < n) : 0 < d.len :=
  (d.idx ⟨0, h⟩).pos

/- English proof (translation)
Introduce `r`. Proceed by induction on `r using Nat.strong_induction_on with`. Consider the case `_ r ihr`. Introduce `hr hrR`. Take `⟨s, rfl⟩` from `Nat.exists_eq_add_of_le (hrR.trans hR)`.

Use `langStep E S r s ρ φ hr hU hK hS (fun r' h0 h1 => ihr r' h1 h0 (h1.le.trans hrR)) ?_` and prove the remaining obligations. Introduce `k b hb t`. Establish `hU' : Umg (rt E (r + s) k φ)` using `((umgOps E (r + s)).2 φ hU).2.2.2.2.1 _`. Take `⟨ψ, hψ, hψU, -, hrt, hψS, hψK⟩` from `sliceUmg E S r s b t _ hU'`. Take `⟨-, ⟨ρ', hc, hρ'⟩, hlev⟩` from `resTyp E r s ρ`.

Establish `h0 : ψ = 0`. Use `ih s (by omega) ⟨ρ.d, ρ', hc⟩ ψ hψU ?_ (hψS (sph_rt hS k)) ?_` and prove the remaining obligations. Use `show Killed (⇑ρ') ψ.1`. Rewrite using `[hρ']`. Conclude with `hψK _ _ ((killedOps E _ ρ φ hK).1 k)`.

Introduce `k' d' hd'`. Establish `hd'' : d'.HasTyp (resR ρ.ρ)`. Rewrite using `[← hρ']`. Conclude with `hd'`. Establish `key` using `H (⟨_, hlev 1 k'⟩ * k) (Dat.cons b d') ⟨hb, hd''⟩ (fun h => by`.

Use `len_pos d' (by omega)` as an intermediate fact. Use `show 2 ≤ d'.len + 1`. Use the proof step `omega)`. Use function extensionality and compare the values at `t'`. Use `congrFun key (Fin.cons t t' : Fin (d'.len + 1) → ℝ)` as an intermediate fact.

Rewrite using `[hrt]`. Simplify using `only [Dat.comp, Fin.cons_zero, Fin.cons_succ, Subgroup.coe_mul, map_mul, Module.End.mul_apply] at this`. Conclude with `this`. Rewrite using `[← hψ, h0]`. Both sides reduce to the same expression.
-/
private theorem step {S : Set (Pl E)} {n : ℕ}
    (ih : ∀ m < n, ∀ (ρ : Typ E m) (φ : Sm E m), Umg φ → Killed ρ.ρ φ.1 → Sph S φ →
      (∀ (k : KA E m) (d : Dat S m), d.HasTyp ρ.ρ → d.comp (rt E m k φ).1 = 0) → φ = 0)
    (ρ : Typ E n) (φ : Sm E n) (hU : Umg φ) (hK : Killed ρ.ρ φ.1) (hS : Sph S φ) (R : ℕ) (hR : R ≤ n)
    (H : ∀ (k : KA E n) (d : Dat S n), d.HasTyp ρ.ρ → (R < n → 2 ≤ d.len) → d.comp (rt E n k φ).1 = 0) :
    ∀ r, 0 < r → r ≤ R → ∀ g, AutomorphicForm.constantTerm r φ.1 g = 0 := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ihr =>
  intro hr hrR
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le (hrR.trans hR)
  refine langStep E S r s ρ φ hr hU hK hS (fun r' h0 h1 => ihr r' h1 h0 (h1.le.trans hrR)) ?_
  intro k b hb t
  have hU' : Umg (rt E (r + s) k φ) := ((umgOps E (r + s)).2 φ hU).2.2.2.2.1 _
  obtain ⟨ψ, hψ, hψU, -, hrt, hψS, hψK⟩ := sliceUmg E S r s b t _ hU'
  obtain ⟨-, ⟨ρ', hc, hρ'⟩, hlev⟩ := resTyp E r s ρ
  have h0 : ψ = 0 := by
    refine ih s (by omega) ⟨ρ.d, ρ', hc⟩ ψ hψU ?_ (hψS (sph_rt hS k)) ?_
    · show Killed (⇑ρ') ψ.1
      rw [hρ']
      exact hψK _ _ ((killedOps E _ ρ φ hK).1 k)
    · intro k' d' hd'
      have hd'' : d'.HasTyp (resR ρ.ρ) := by
        rw [← hρ']; exact hd'
      have key := H (⟨_, hlev 1 k'⟩ * k) (Dat.cons b d') ⟨hb, hd''⟩ (fun h => by
        have := len_pos d' (by omega)
        show 2 ≤ d'.len + 1
        omega)
      funext t'
      have := congrFun key (Fin.cons t t' : Fin (d'.len + 1) → ℝ)
      rw [hrt]
      simp only [Dat.comp, Fin.cons_zero, Fin.cons_succ, Subgroup.coe_mul, map_mul, Module.End.mul_apply] at this
      exact this
  rw [← hψ, h0]
  rfl

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `ρ φ hU hK hS H`. Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases.

Use `congrFun (H 1 Dat.nil trivial) (fun _ => 0)` as an intermediate fact. Rewrite using `[Subsingleton.elim g 1]`. Simplify using `only [Dat.comp, Subgroup.coe_one, map_one] at this`. Conclude with `this`. Use `step ih ρ φ hU hK hS n le_rfl (fun k d hd _ => H k d hd) n hn le_rfl g` as an intermediate fact.

Rewrite `this` using `[ct_top]`. Conclude with `this`.
-/
private theorem part1 (S : Set (Pl E)) (n : ℕ) : ∀ (ρ : Typ E n) (φ : Sm E n), Umg φ → Killed ρ.ρ φ.1 → Sph S φ →
      (∀ (k : KA E n) (d : Dat S n), d.HasTyp ρ.ρ → d.comp (rt E n k φ).1 = 0) → φ = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ρ φ hU hK hS H
  refine Subtype.ext (funext fun g => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := congrFun (H 1 Dat.nil trivial) (fun _ => 0)
    rw [Subsingleton.elim g 1]
    simp only [Dat.comp, Subgroup.coe_one, map_one] at this
    exact this
  · have := step ih ρ φ hU hK hS n le_rfl (fun k d hd _ => H k d hd) n hn le_rfl g
    rw [ct_top] at this
    exact this

end UpperTheory.ConvolutionTheory.BW

/- English proof (translation)
Introduce `E _ _ _ S n ρ φ hU hK hS`. Use `⟨part1 S n ρ φ hU hK hS, fun H r hr hrn => ?_⟩` and prove the remaining obligations. Conclude with `step (fun m _ => part1 S m) ρ φ hU hK hS r hrn.le (fun k d hd h => H k d hd (h hrn)) r hr le_rfl`.
-/
theorem UpperTheory.ConvolutionTheory.BW.langlands :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.Langlands E := by
  intro E _ _ _ S n ρ φ hU hK hS
  refine ⟨part1 S n ρ φ hU hK hS, fun H r hr hrn => ?_⟩
  exact step (fun m _ => part1 S m) ρ φ hU hK hS r hrn.le (fun k d hd h => H k d hd (h hrn)) r hr le_rfl

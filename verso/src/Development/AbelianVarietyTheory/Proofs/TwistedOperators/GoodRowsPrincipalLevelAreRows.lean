import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasColOfChoice

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepRows.Good

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Introduce `x hx`. Take `⟨y, rfl, hy⟩` from `GlobalTheory.Grid.mem_princGL.1 (GlobalTheory.Grid.princGL_mono β h hx)`. Use `mem_princAt.2 ⟨⟨y, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[redFn_frGL]`. Apply `Units.ext` to reduce the goal to its premises.

Use extensionality with `i j`. Establish `h0 : resS F PP ((y.1 - 1) i j) = 0`. Unfold `resS`. Rewrite using `[RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 (hy i j), map_zero]`. Rewrite `h0` using `[Matrix.sub_apply, map_sub, sub_eq_zero]`.

Use `h0.trans ?_` and prove the remaining obligations. Simplify using `only [Units.val_one, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem princGL_le_princAt (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) {I : Ideal (𝓞 E)} {PP : Pl E} (h : I ≤ PP.asIdeal) :
    GlobalTheory.Grid.princGL β I ≤ princAt β PP := by
  intro x hx
  obtain ⟨y, rfl, hy⟩ := GlobalTheory.Grid.mem_princGL.1 (GlobalTheory.Grid.princGL_mono β h hx)
  refine mem_princAt.2 ⟨⟨y, rfl⟩, ?_⟩
  rw [redFn_frGL]
  apply Units.ext
  ext i j
  have h0 : resS F PP ((y.1 - 1) i j) = 0 := by
    unfold resS
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 (hy i j), map_zero]
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h0
  refine h0.trans ?_
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[← GlobalTheory.ColMeas.princ_eq_congLev hc J hfr I]`. Introduce and unpack `x ⟨h1, h2⟩`. Use `⟨⟨h1, ?_⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => princGL_le_princAt β (h PP hP) h2⟩` and prove the remaining obligations. Take `⟨y, e, -⟩` from `GlobalTheory.Grid.mem_princGL.1 h2`. Conclude with `⟨y, e⟩`.
-/
theorem congLev_le_Kg [StarRing E] (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    {Λ : Submodule (𝓞 E) (Fin n → E)} (hfr : IsFrame β Λ) {I : Ideal (𝓞 E)} {T : Finset (Pl E)}
    (h : ∀ PP ∈ T, I ≤ PP.asIdeal) : congLev hc J Λ I ≤ Kg hc J β T := by
  rw [← GlobalTheory.ColMeas.princ_eq_congLev hc J hfr I]
  rintro x ⟨h1, h2⟩
  refine ⟨⟨h1, ?_⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => princGL_le_princAt β (h PP hP) h2⟩
  obtain ⟨y, e, -⟩ := GlobalTheory.Grid.mem_princGL.1 h2
  exact ⟨y, e⟩

end General

variable {D : D7} {T : Type}

/- English proof (translation)
Establish `h1` using `P.pb_over k`. Establish `h2 : PP.under (𝓞 D.host.K) = P.pb k` using `h`. Rewrite `h1` using `[← h2]`. Establish `h3 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal` using `h1`. Rewrite `h3` using `[map_natCast]`. Then use the resulting hypothesis.
-/
theorem g_mem {P : Formalism.L2.Host.PiBar D.host} {k : Fin 2} {PP : Pl D.host.E} (h : P.Div k PP) :
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  have h1 := P.pb_over k
  have h2 : PP.under (𝓞 D.host.K) = P.pb k := h
  rw [← h2] at h1
  have h3 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := h1
  rwa [map_natCast] at h3

/- English proof (translation)
Introduce and unpack `k ⟨hk1, hk2⟩`. Take `⟨c, hfr, -⟩` from `hL.βY 0 (by have := D.R.two_le_m; omega)`. Use `⟨hk1, Kg_le_lev (T := L.Pg) (D := L.dat0 L.triv) subset_rfl (Finset.empty_subset _) (congLev_le_Kg _ _ hfr (fun PP hP => ?_) hk2)⟩` and prove the remaining obligations. Take `⟨l, hl⟩` from `(hL.Pg PP).1 hP`. Establish `hg` using `g_mem hl`.

Rewrite using `[Ideal.span_singleton_le_iff_mem, Nat.cast_mul]`. Use `fin_cases l`. Conclude with `Ideal.mul_mem_right _ _ hg`. Conclude with `Ideal.mul_mem_left _ _ hg`.
-/
theorem levRow_sub {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) :
    (levRow L : Set (GA D (Yc D 0))) ⊆ levS _ (L.βY 0) (L.dat0 L.triv) := by
  rintro k ⟨hk1, hk2⟩
  obtain ⟨c, hfr, -⟩ := hL.βY 0 (by have := D.R.two_le_m; omega)
  refine ⟨hk1, Kg_le_lev (T := L.Pg) (D := L.dat0 L.triv) subset_rfl (Finset.empty_subset _)
    (congLev_le_Kg _ _ hfr (fun PP hP => ?_) hk2)⟩
  obtain ⟨l, hl⟩ := (hL.Pg PP).1 hP
  have hg := g_mem hl
  rw [Ideal.span_singleton_le_iff_mem, Nat.cast_mul]
  fin_cases l
  · exact Ideal.mul_mem_right _ _ hg
  · exact Ideal.mul_mem_left _ _ hg

/- English proof (translation)
Establish `h : levFn (L.βY 0) (L.dat0 L.triv) (Lev.finE (Yc D 0) k) = 1`. Establish `h1 : ext1 (L.dat0 L.triv).P.H (L.dat0 L.triv).P.chi (rTup (L.βY 0) (L.dat0 L.triv) (Lev.finE (Yc D 0) k)) = 1` using `Lev.subgroupCharExtension_one_apply _ _`. Unfold `levFn`. Rewrite using `[h1]`. Simplify using `[LevCh.dat0, Lev.datY]`.

Unfold `Lev.levChi`. Rewrite using `[h, Units.val_one]`.
-/
theorem principalRowLevelCharacter_trivial (L : LevCh D T) (k : GA D (Yc D 0)) : Lev.levChi _ (L.βY 0) (L.dat0 L.triv) k = 1 := by
  have h : levFn (L.βY 0) (L.dat0 L.triv) (Lev.finE (Yc D 0) k) = 1 := by
    have h1 : ext1 (L.dat0 L.triv).P.H (L.dat0 L.triv).P.chi (rTup (L.βY 0) (L.dat0 L.triv) (Lev.finE (Yc D 0) k)) = 1 :=
      Lev.subgroupCharExtension_one_apply _ _
    unfold levFn
    rw [h1]
    simp [LevCh.dat0, Lev.datY]
  unfold Lev.levChi
  rw [h, Units.val_one]

end GlobalTheory.SepRows.Good

/- English proof (translation)
Introduce `D Γ _ _ Pl0 T A Ks _ _ _ R hL t ht`. Rewrite using `[mem_multT, LinearEquiv.symm_apply_apply]`. Use `Submodule.span_mono (fun U hU => ?_) (goodPart_le _ _ _ _ _ ht)` and prove the remaining obligations. Conclude with `⟨hU.aut, hU.cusp, fun v k hk g => by`. Rewrite using `[hU.lev v k (Good.levRow_sub hL hk) g, Good.principalRowLevelCharacter_trivial]`.

Use the proof step `rfl, hU.equiv, hU.cont⟩`.
-/
theorem GlobalTheory.SepRows.goodRows : GoodRows := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R hL t ht
  rw [mem_multT, LinearEquiv.symm_apply_apply]
  refine Submodule.span_mono (fun U hU => ?_) (goodPart_le _ _ _ _ _ ht)
  exact ⟨hU.aut, hU.cusp, fun v k hk g => by
    rw [hU.lev v k (Good.levRow_sub hL hk) g, Good.principalRowLevelCharacter_trivial]; rfl, hU.equiv, hU.cont⟩

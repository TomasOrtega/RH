import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceEqConjugatePlaceAndEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSetAutWdTieLabConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationPowSubPowLt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.CompRamified

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

/- English proof (translation)
Break down `eq_or_ne x 0 with rfl | hx0` into its components or cases. Conclude with `zero_le'`. Rewrite `h`, the goal using `[← WithZero.exp_log hx0]`. Rewrite `h` using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Rewrite using `[WithZero.exp_le_exp]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem le_exp_neg_one_of_lt_one' {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact zero_le'
  · rw [← WithZero.exp_log hx0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]; omega

/- English proof (translation)
Simplify using `only [HChar.UnrAt, not_forall] at hr`. Take `⟨x, hx, hne⟩` from `hr`. Establish `hx' : Valued.v (x : t.w.adicCompletion L) = 1` using `hx`. Take `⟨a, ha⟩` from `adic_exists_approx t.w (x : t.w.adicCompletion L) (le_of_eq hx')`. Take `⟨b, hb⟩` from `adic_exists_approx t.v (t.i (a : L)) (t.split_le_one a)`.

Use `set c : 𝓞 L := algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) b with hcdef`. Establish `hac : a - c ∈ t.w.asIdeal` using `by show a - c ∈ t.ideal`. Rewrite using `[t.split_mem_ideal]`. Establish `e : t.i ((c : 𝓞 L) : L) = algebraMap (𝓞 (maximalRealSubfield L)) (t.v.adicCompletion (maximalRealSubfield L)) b`. Rewrite using `[hcdef, split_coe_algebraMap, AlgHom.commutes]`.

Both sides reduce to the same expression. Establish `e2 : ((a - c : 𝓞 L) : L) = (a : L) - (c : L)` using `by push_cast; rfl`. Rewrite using `[e2, map_sub, e]`. Conclude with `hb`. Establish `hval : ∀ z : 𝓞 L, Valued.v (algebraMap (𝓞 L) (t.w.adicCompletion L) z) = t.w.valuation L (z : L)` using `fun z => by`.

Conclude with `adic_valued_algebraMap (R := 𝓞 L) (K := L) t.w (z : L)`. Establish `hxc : Valued.v ((x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ c) < 1`. Establish `e : (x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ c = ((x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ a) + algebraMap (𝓞 L) _ (a - c)`. Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Use `lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha ?_)` and prove the remaining obligations. Rewrite using `[hval]`. Conclude with `(t.w.valuation_lt_one_iff_mem (a - c)).2 hac`. Establish `hc1 : Valued.v (algebraMap (𝓞 L) (t.w.adicCompletion L) c) = 1`.

Establish `e : algebraMap (𝓞 L) (t.w.adicCompletion L) c = (x : t.w.adicCompletion L) - ((x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ c)` using `by ring`. Rewrite using `[e, Valuation.map_sub_eq_of_lt_left _ (by rw [hx']; exact hxc)]`. Conclude with `hx'`. Establish `hbv : b ∉ t.v.asIdeal`. Introduce `hm`.

Establish `h1` using `(t.split_alg_mem b).2 hm`. Establish `h2 : Valued.v (algebraMap (𝓞 L) (t.w.adicCompletion L) c) < 1`. Rewrite using `[hval]`. Conclude with `(t.w.valuation_lt_one_iff_mem c).2 h1`. Rewrite `h2` using `[hc1]`.

Conclude with `lt_irrefl _ h2`. Establish `hc0 : (c : L) ≠ 0`. Introduce `h0`. Establish `: algebraMap (𝓞 L) (t.w.adicCompletion L) c = 0` using `by show algebraMap L (t.w.adicCompletion L) (c : L) = 0`. Rewrite using `[h0, map_zero]`.

Rewrite `hc1` using `[this, map_zero]`. Conclude with `zero_ne_one hc1`. Use `⟨b, hbv, Units.mk0 (c : L) hc0, rfl, ?_⟩` and prove the remaining obligations. Introduce `h1`. Apply `hne` to reduce the goal to its premises.

Use `set y : (t.w.adicCompletion L)ˣ := atFin t.w (Units.mk0 (c : L) hc0) with hydef`. Establish `hy : (y : t.w.adicCompletion L) = algebraMap (𝓞 L) (t.w.adicCompletion L) c` using `rfl`. Establish `hu : IsUnitAt t.w (y * x⁻¹)` using `by show Valued.v (((y * x⁻¹ : (t.w.adicCompletion L)ˣ)) : t.w.adicCompletion L) = 1`. Rewrite using `[Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hy, hc1, hx', inv_one, mul_one]`. Establish `hsub : Valued.v (((y * x⁻¹ : (t.w.adicCompletion L)ˣ) : t.w.adicCompletion L) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ))`.

Establish `e : ((y * x⁻¹ : (t.w.adicCompletion L)ˣ) : t.w.adicCompletion L) - 1 = -((x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ c) * (x : t.w.adicCompletion L)⁻¹`. Rewrite using `[Units.val_mul, Units.val_inv_eq_inv_val, hy]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, map_mul, Valuation.map_neg, map_inv₀, hx', inv_one, mul_one]`.

Conclude with `le_exp_neg_one_of_lt_one' hxc`. Establish `h2` using `ht (y * x⁻¹) hu hsub`. Rewrite `h2` using `[map_mul, map_inv, mul_inv_eq_one]`. Rewrite using `[← h2]`. Conclude with `h1`.
-/
theorem exists_int_locK_ne (χ : HChar L) (t : SplitPlace L) (ht : χ.TameAt t.w) (hr : ¬ χ.UnrAt t.w) :
    ∃ b : 𝓞 (maximalRealSubfield L), b ∉ t.v.asIdeal ∧ ∃ k : Lˣ,
      (k : L) = ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) b : 𝓞 L) : L) ∧ χ.locK t.w k ≠ 1 := by
  classical
  simp only [HChar.UnrAt, not_forall] at hr
  obtain ⟨x, hx, hne⟩ := hr
  have hx' : Valued.v (x : t.w.adicCompletion L) = 1 := hx
  obtain ⟨a, ha⟩ := adic_exists_approx t.w (x : t.w.adicCompletion L) (le_of_eq hx')
  obtain ⟨b, hb⟩ := adic_exists_approx t.v (t.i (a : L)) (t.split_le_one a)
  set c : 𝓞 L := algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) b with hcdef
  have hac : a - c ∈ t.w.asIdeal := by
    show a - c ∈ t.ideal
    rw [t.split_mem_ideal]
    have e : t.i ((c : 𝓞 L) : L) =
        algebraMap (𝓞 (maximalRealSubfield L)) (t.v.adicCompletion (maximalRealSubfield L)) b := by
      rw [hcdef, split_coe_algebraMap, AlgHom.commutes]; rfl
    have e2 : ((a - c : 𝓞 L) : L) = (a : L) - (c : L) := by push_cast; rfl
    rw [e2, map_sub, e]
    exact hb
  have hval : ∀ z : 𝓞 L, Valued.v (algebraMap (𝓞 L) (t.w.adicCompletion L) z) = t.w.valuation L (z : L) := fun z => by
    exact adic_valued_algebraMap (R := 𝓞 L) (K := L) t.w (z : L)
  have hxc : Valued.v ((x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ c) < 1 := by
    have e : (x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ c =
        ((x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ a) + algebraMap (𝓞 L) _ (a - c) := by
      rw [map_sub]; ring
    rw [e]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha ?_)
    rw [hval]
    exact (t.w.valuation_lt_one_iff_mem (a - c)).2 hac
  have hc1 : Valued.v (algebraMap (𝓞 L) (t.w.adicCompletion L) c) = 1 := by
    have e : algebraMap (𝓞 L) (t.w.adicCompletion L) c =
        (x : t.w.adicCompletion L) - ((x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ c) := by ring
    rw [e, Valuation.map_sub_eq_of_lt_left _ (by rw [hx']; exact hxc)]
    exact hx'
  have hbv : b ∉ t.v.asIdeal := by
    intro hm
    have h1 := (t.split_alg_mem b).2 hm
    have h2 : Valued.v (algebraMap (𝓞 L) (t.w.adicCompletion L) c) < 1 := by
      rw [hval]; exact (t.w.valuation_lt_one_iff_mem c).2 h1
    rw [hc1] at h2
    exact lt_irrefl _ h2
  have hc0 : (c : L) ≠ 0 := by
    intro h0
    have : algebraMap (𝓞 L) (t.w.adicCompletion L) c = 0 := by
      show algebraMap L (t.w.adicCompletion L) (c : L) = 0
      rw [h0, map_zero]
    rw [this, map_zero] at hc1
    exact zero_ne_one hc1
  refine ⟨b, hbv, Units.mk0 (c : L) hc0, rfl, ?_⟩
  intro h1
  apply hne
  set y : (t.w.adicCompletion L)ˣ := atFin t.w (Units.mk0 (c : L) hc0) with hydef
  have hy : (y : t.w.adicCompletion L) = algebraMap (𝓞 L) (t.w.adicCompletion L) c := rfl
  have hu : IsUnitAt t.w (y * x⁻¹) := by
    show Valued.v (((y * x⁻¹ : (t.w.adicCompletion L)ˣ)) : t.w.adicCompletion L) = 1
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hy, hc1, hx', inv_one, mul_one]
  have hsub : Valued.v (((y * x⁻¹ : (t.w.adicCompletion L)ˣ) : t.w.adicCompletion L) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    have e : ((y * x⁻¹ : (t.w.adicCompletion L)ˣ) : t.w.adicCompletion L) - 1 =
        -((x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ c) * (x : t.w.adicCompletion L)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, hy]
      field_simp
      ring
    rw [e, map_mul, Valuation.map_neg, map_inv₀, hx', inv_one, mul_one]
    exact le_exp_neg_one_of_lt_one' hxc
  have h2 := ht (y * x⁻¹) hu hsub
  rw [map_mul, map_inv, mul_inv_eq_one] at h2
  rw [← h2]
  exact h1

end Gen

end GlobalTheory.CompRamified

open GlobalTheory.CompRamified in

/- English proof (translation)
Introduce `D cf j ξH s ξ htr hta hq hc`. Use `set η := cf.mu0 j * ξH with hη`. Establish `htame : ∀ u, η.TameAt u` using `fun u x hx h1 => by`. Rewrite using `[hη, HChar.loc_mul, (cf.isMu0 j).tame u x hx h1, hta u x hx h1, one_mul]`. Establish `htriv : ∀ k : (D.host.F)ˣ, ∏ P ∈ aboveF (L` using `D.host.E) D.host.F s.v, η.locK P (upF D.host.F k) = 1 := fun k => by`.

Establish `h1` using `(cf.isMu0 j).triv.1 s.v k`. Establish `h2` using `htr.1 s.v k`. Rewrite `h1`, `h2` using `[GlobalTheory.GalToHecke.resFin_eq]`. Rewrite using `[hη]`. Use `show ∏ P ∈ aboveF (L := D.host.E) D.host.F s.v, ((cf.mu0 j).locK P (upF D.host.F k) * ξH.locK P (upF D.host.F k)) = 1`.

Rewrite using `[Finset.prod_mul_distrib, h1, h2, one_mul]`. Take `⟨-, w, hw, hram⟩` from `hq`. Establish `key : ∃ b : 𝓞 (maximalRealSubfield D.host.E), b ∉ s.v.asIdeal ∧ ∃ k : (D.host.E)ˣ, (k : D.host.E) = ((algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) b : 𝓞 D.host.E) : D.host.E) ∧ η.locK w k ≠ 1`. Break down `GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s w hw with e | e` into its components or cases. Substitute `e` using the available equality.

Conclude with `exists_int_locK_ne η s (htame _) hram`. Establish `e2` using `(GlobalTheory.TypeTame.conjSP_w_of_isConjPl D s w e).1`. Establish `h` using `exists_int_locK_ne η (GlobalTheory.TypeTame.conjSP s) (e2 ▸ htame _) (e2 ▸ hram)`. Rewrite `h` using `[e2]`. Conclude with `h`.

Take `⟨b, hbv, k, hk, hne⟩` from `key`. Establish `hb0 : ((b : maximalRealSubfield D.host.E) : D.host.E) ≠ 0`. Introduce `h0`. Apply `hbv` to reduce the goal to its premises. Establish `: (b : maximalRealSubfield D.host.E) = 0` using `by exact_mod_cast h0`.

Establish `: b = 0` using `RingOfIntegers.coe_eq_zero_iff.mp this`. Rewrite using `[this]`. Conclude with `s.v.asIdeal.zero_mem`. Establish `hF0 : (b : maximalRealSubfield D.host.E) ≠ 0` using `fun h => hb0 (by rw [h]; rfl)`. Use `set f : (D.host.F)ˣ := Units.mk0 (b : maximalRealSubfield D.host.E) hF0 with hfdef`.

Establish `hfk : upF D.host.F f = k`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hk]`. Both sides reduce to the same expression. Establish `hsw : η.locK s.w k ≠ 1`.

Distinguish the cases in `e : s.w = w`. Rewrite using `[e]` and apply the resulting hypothesis. Establish `hc' : IsConjPl D.host w s.w` using `(GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s w hw).resolve_left e`. Establish `hab : aboveF (L` using `D.host.E) D.host.F s.v = {s.w, w} := by`. Use extensionality with `P`.

Rewrite using `[GlobalTheory.GalToHecke.mem_aboveF, Finset.mem_insert, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce `hP`. Establish `hov : NG.OverPl P s.v` using `by rw [← hP]; rfl`. Break down `GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s P hov with e' | e'` into its components or cases.

Conclude with `Or.inl e'.symm`. Conclude with `Or.inr (GlobalTheory.HeightCounting.TrueConjLabels.eq_of_isConjPl e' hc')`. Introduce and unpack `(rfl | rfl)`. Conclude with `HeightOneSpectrum.ext s.w_under`. Conclude with `HeightOneSpectrum.ext hw`.

Establish `h` using `htriv f`. Rewrite `h` using `[hab, Finset.prod_pair e, hfk]`. Introduce `h1`. Rewrite `h` using `[h1, one_mul]`. Conclude with `hne h`.

Use `⟨Units.map (s.i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E)) k, ?_, ?_⟩` and prove the remaining obligations. Use `show Valued.v (s.i (k : D.host.E)) = 1`. Rewrite using `[hk, s.split_val_alg]`. Use `le_antisymm (s.v.valuation_le_one b) (not_lt.1 fun h => hbv ((s.v.valuation_lt_one_iff_mem b).1 h))` and prove the remaining obligations. Rewrite using `[hc.2 k]`.

Conclude with `hsw`.
-/
theorem GlobalTheory.CompRamified.exists_unit_ne_one : ∀ (D : D7) (cf : CharFrame D) (j : Fin D.R.m) (ξH : HChar D.host.E) (s : SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), ξH.TrivOn D.host.F → (∀ u, ξH.TameAt u) → s.v ∈ qPl D (cf.mu0 j * ξH) → NG.IsCompAt (cf.mu0 j * ξH) s ξ → ∃ a : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ, Valued.v (a : s.v.adicCompletion (maximalRealSubfield D.host.E)) = 1 ∧ ξ a ≠ 1 := by
  classical
  intro D cf j ξH s ξ htr hta hq hc
  set η := cf.mu0 j * ξH with hη
  have htame : ∀ u, η.TameAt u := fun u x hx h1 => by
    rw [hη, HChar.loc_mul, (cf.isMu0 j).tame u x hx h1, hta u x hx h1, one_mul]
  have htriv : ∀ k : (D.host.F)ˣ, ∏ P ∈ aboveF (L := D.host.E) D.host.F s.v, η.locK P (upF D.host.F k) = 1 := fun k => by
    have h1 := (cf.isMu0 j).triv.1 s.v k
    have h2 := htr.1 s.v k
    rw [GlobalTheory.GalToHecke.resFin_eq] at h1 h2
    rw [hη]
    show ∏ P ∈ aboveF (L := D.host.E) D.host.F s.v, ((cf.mu0 j).locK P (upF D.host.F k) * ξH.locK P (upF D.host.F k)) = 1
    rw [Finset.prod_mul_distrib, h1, h2, one_mul]
  obtain ⟨-, w, hw, hram⟩ := hq
  have key : ∃ b : 𝓞 (maximalRealSubfield D.host.E), b ∉ s.v.asIdeal ∧ ∃ k : (D.host.E)ˣ,
      (k : D.host.E) = ((algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) b : 𝓞 D.host.E) : D.host.E) ∧
        η.locK w k ≠ 1 := by
    rcases GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s w hw with e | e
    · subst e
      exact exists_int_locK_ne η s (htame _) hram
    · have e2 := (GlobalTheory.TypeTame.conjSP_w_of_isConjPl D s w e).1
      have h := exists_int_locK_ne η (GlobalTheory.TypeTame.conjSP s) (e2 ▸ htame _) (e2 ▸ hram)
      rw [e2] at h
      exact h
  obtain ⟨b, hbv, k, hk, hne⟩ := key
  have hb0 : ((b : maximalRealSubfield D.host.E) : D.host.E) ≠ 0 := by
    intro h0
    apply hbv
    have : (b : maximalRealSubfield D.host.E) = 0 := by exact_mod_cast h0
    have : b = 0 := RingOfIntegers.coe_eq_zero_iff.mp this
    rw [this]; exact s.v.asIdeal.zero_mem
  have hF0 : (b : maximalRealSubfield D.host.E) ≠ 0 := fun h => hb0 (by rw [h]; rfl)
  set f : (D.host.F)ˣ := Units.mk0 (b : maximalRealSubfield D.host.E) hF0 with hfdef
  have hfk : upF D.host.F f = k := by
    apply Units.ext
    rw [hk]
    rfl
  have hsw : η.locK s.w k ≠ 1 := by
    by_cases e : s.w = w
    · rwa [e]
    have hc' : IsConjPl D.host w s.w := (GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s w hw).resolve_left e
    have hab : aboveF (L := D.host.E) D.host.F s.v = {s.w, w} := by
      ext P
      rw [GlobalTheory.GalToHecke.mem_aboveF, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hP
        have hov : NG.OverPl P s.v := by rw [← hP]; rfl
        rcases GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s P hov with e' | e'
        · exact Or.inl e'.symm
        · exact Or.inr (GlobalTheory.HeightCounting.TrueConjLabels.eq_of_isConjPl e' hc')
      · rintro (rfl | rfl)
        · exact HeightOneSpectrum.ext s.w_under
        · exact HeightOneSpectrum.ext hw
    have h := htriv f
    rw [hab, Finset.prod_pair e, hfk] at h
    intro h1
    rw [h1, one_mul] at h
    exact hne h
  refine ⟨Units.map (s.i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E)) k, ?_, ?_⟩
  · show Valued.v (s.i (k : D.host.E)) = 1
    rw [hk, s.split_val_alg]
    refine le_antisymm (s.v.valuation_le_one b) (not_lt.1 fun h => hbv ((s.v.valuation_lt_one_iff_mem b).1 h))
  · rw [hc.2 k]
    exact hsw

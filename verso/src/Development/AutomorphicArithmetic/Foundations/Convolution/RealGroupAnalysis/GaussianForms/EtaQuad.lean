import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import GroundTheory.GlobalFields.SemilocalAlgebras.Finite
import GroundTheory.GlobalFields.TateThesis.ChebotarevAbelian

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

namespace UpperTheory.ConvolutionTheory.R2.C.QuadraticHeckeCharacter

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Rewrite using `[normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]`.
-/
private theorem normV_abs {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    normV w = Ideal.absNorm w.asIdeal := by
  rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

/- English proof (translation)
Establish `: w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal` using `⟨rfl⟩`. Use `w.isMaximal` as an intermediate fact. Use `(w.under (𝓞 F)).isMaximal` as an intermediate fact. Rewrite using `[normV_abs, normV_abs, ← Ideal.absNorm_relNorm (𝓞 F) (𝓞 E) w.asIdeal, Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 F)).asIdeal, map_pow]`.
-/
private theorem normV_eq_pow (w : HeightOneSpectrum (𝓞 E)) :
    normV w = normV (w.under (𝓞 F)) ^ w.asIdeal.inertiaDeg (𝓞 F) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 F)).isMaximal
  rw [normV_abs, normV_abs, ← Ideal.absNorm_relNorm (𝓞 F) (𝓞 E) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 F)).asIdeal, map_pow]

/- English proof (translation)
Rewrite using `[normV_abs]`. Establish `h0 : Ideal.absNorm v.asIdeal ≠ 0` using `fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)`. Establish `h1 : Ideal.absNorm v.asIdeal ≠ 1` using `fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)`. Use linear arithmetic over natural numbers and integers.
-/
private theorem one_lt_normV {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    1 < normV v := by
  rw [normV_abs]
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

/- English proof (translation)
The claim follows from `HeightOneSpectrum.ext u.2.over.symm`.
-/
private theorem under_of_mem {v : HeightOneSpectrum (𝓞 F)} (u : SemiLocal.PlacesOver E v) : u.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext u.2.over.symm

/- English proof (translation)
Establish `: w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal` using `⟨rfl⟩`. Use `w.isMaximal` as an intermediate fact. Use `(w.under (𝓞 F)).isMaximal` as an intermediate fact. Rewrite using `[← Ideal.inertiaDeg'_eq_inertiaDeg (w.under (𝓞 F)).asIdeal w.asIdeal]`. Conclude with `Ideal.inertiaDeg'_pos _ _`.
-/
private theorem inertiaDeg_pos (w : HeightOneSpectrum (𝓞 E)) : 0 < w.asIdeal.inertiaDeg (𝓞 F) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 F)).isMaximal
  rw [← Ideal.inertiaDeg'_eq_inertiaDeg (w.under (𝓞 F)).asIdeal w.asIdeal]
  exact Ideal.inertiaDeg'_pos _ _

/- English proof (translation)
Use `(Set.Finite.preimage' (f := fun w : HeightOneSpectrum (𝓞 E) => w.under (𝓞 F)) (finite_setOf_exists_ramificationIdx_ne_one F E) fun v _ => ?_).subset fun w hw => ?_` and prove the remaining obligations. Conclude with `(Set.finite_range fun u : SemiLocal.PlacesOver E v => u.1).subset fun w hw => ⟨⟨w, ⟨by rw [← (Set.mem_singleton_iff.1 hw)]; rfl⟩⟩, rfl⟩`. Choose the witnesses or unpack the hypotheses as in `⟨u, hu, he⟩ : ∃ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = w.under (𝓞 F) ∧ u.asIdeal.ramificationIdx (𝓞 F) ≠ 1 := by`. Establish `hw' : ¬ Formalism.MainNotions.SchurIrreducible.IsUnram (E` using `E) (w.under (𝓞 F)) := hw`. Simplify `hw'` using `only [GlobalTheory.LFun.isUnram_iff, not_forall, exists_prop, ne_eq]`.

Conclude with `⟨u, ⟨by change (w.under (𝓞 F)).asIdeal = _; rw [← hu]; rfl⟩, he⟩`.
-/
private theorem finite_bad :
    {w : HeightOneSpectrum (𝓞 E) | ¬ Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (w.under (𝓞 F))}.Finite := by
  refine (Set.Finite.preimage' (f := fun w : HeightOneSpectrum (𝓞 E) => w.under (𝓞 F))
    (finite_setOf_exists_ramificationIdx_ne_one F E) fun v _ => ?_).subset fun w hw => ?_
  · exact (Set.finite_range fun u : SemiLocal.PlacesOver E v => u.1).subset fun w hw =>
      ⟨⟨w, ⟨by rw [← (Set.mem_singleton_iff.1 hw)]; rfl⟩⟩, rfl⟩
  · obtain ⟨u, hu, he⟩ : ∃ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = w.under (𝓞 F) ∧
        u.asIdeal.ramificationIdx (𝓞 F) ≠ 1 := by
      have hw' : ¬ Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (w.under (𝓞 F)) := hw
      simpa only [GlobalTheory.LFun.isUnram_iff, not_forall, exists_prop, ne_eq] using hw'
    exact ⟨u, ⟨by change (w.under (𝓞 F)).asIdeal = _; rw [← hu]; rfl⟩, he⟩

/- English proof (translation)
Establish `hsum` using `SemiLocal.sum_ramificationIdx_mul_inertiaDeg E (w.under (𝓞 F))`. Rewrite `hsum` using `[h2]`. Establish `hterm : ∀ u : SemiLocal.PlacesOver E (w.under (𝓞 F)), u.1.asIdeal.ramificationIdx (𝓞 F) * u.1.asIdeal.inertiaDeg (𝓞 F) = u.1.asIdeal.inertiaDeg (𝓞 F)` using `fun u => by rw [GlobalTheory.LFun.isUnram_iff.1 hu u.1 (under_of_mem u), one_mul]`. Simplify using `only [hterm] at hsum`. Set `w₀ : SemiLocal.PlacesOver E (w.under (𝓞 F))` to `⟨w, ⟨rfl⟩⟩`.

Establish `h1 : 1 < normV (w.under (𝓞 F))` using `one_lt_normV _`. Prove the components needed by the constructor for the conclusion. Introduce `hs`. Take `⟨P, Q, hPQ, hP, hQ⟩` from `GlobalTheory.LFun.isSplit_iff.1 hs`. Choose the witnesses or unpack the hypotheses as in `⟨u, hu', hne⟩ : ∃ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = w.under (𝓞 F) ∧ u ≠ w := by`.

Distinguish the cases in `h : P = w`. Conclude with `⟨Q, hQ, fun e => hPQ (h.trans e.symm)⟩`. Conclude with `⟨P, hP, h⟩`. Set `u₀ : SemiLocal.PlacesOver E (w.under (𝓞 F))` to `⟨u, ⟨by rw [← hu']; rfl⟩⟩`. Establish `hne' : w₀ ≠ u₀` using `fun e => hne (congrArg Subtype.val e).symm`.

Establish `hle` using `Finset.add_le_sum (f := fun u : SemiLocal.PlacesOver E (w.under (𝓞 F)) => u.1.asIdeal.inertiaDeg (𝓞 F)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ w₀) (Finset.mem_univ u₀) hne'`. Rewrite `hle` using `[hsum]`. Establish `p1 : 0 < w.asIdeal.inertiaDeg (𝓞 F)` using `inertiaDeg_pos w`. Establish `p2 : 0 < u.asIdeal.inertiaDeg (𝓞 F)` using `inertiaDeg_pos u`. Establish `hf : w.asIdeal.inertiaDeg (𝓞 F) = 1`.

Express the relevant statement in the definitionally equal form `w.asIdeal.inertiaDeg (𝓞 F) + u.asIdeal.inertiaDeg (𝓞 F) ≤ 2 at hle`. Use linear arithmetic over natural numbers and integers. Rewrite using `[normV_eq_pow (F := F) w, hf, pow_one]`. Introduce `hn`. Assume the negation of the conclusion as `hs`.

Establish `hall : ∀ u : SemiLocal.PlacesOver E (w.under (𝓞 F)), u = w₀` using `fun u => Subtype.ext (GlobalTheory.LFun.eq_of_not_isSplit hs (under_of_mem u) rfl)`. Rewrite `hsum` using `[Finset.sum_eq_single w₀ (fun b _ hb => absurd (hall b) hb) (by simp)]`. Express the relevant statement in the definitionally equal form `w.asIdeal.inertiaDeg (𝓞 F) = 2 at hsum`. Rewrite `hn` using `[normV_eq_pow (F := F) w, hsum]`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem isSplit_iff_normV (h2 : Module.finrank F E = 2) (w : HeightOneSpectrum (𝓞 E))
    (hu : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (w.under (𝓞 F))) :
    Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 F)) ↔ normV w = normV (w.under (𝓞 F)) := by
  have hsum := SemiLocal.sum_ramificationIdx_mul_inertiaDeg E (w.under (𝓞 F))
  rw [h2] at hsum
  have hterm : ∀ u : SemiLocal.PlacesOver E (w.under (𝓞 F)),
      u.1.asIdeal.ramificationIdx (𝓞 F) * u.1.asIdeal.inertiaDeg (𝓞 F) = u.1.asIdeal.inertiaDeg (𝓞 F) :=
    fun u => by rw [GlobalTheory.LFun.isUnram_iff.1 hu u.1 (under_of_mem u), one_mul]
  simp only [hterm] at hsum
  let w₀ : SemiLocal.PlacesOver E (w.under (𝓞 F)) := ⟨w, ⟨rfl⟩⟩
  have h1 : 1 < normV (w.under (𝓞 F)) := one_lt_normV _
  constructor
  · intro hs
    obtain ⟨P, Q, hPQ, hP, hQ⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
    obtain ⟨u, hu', hne⟩ : ∃ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = w.under (𝓞 F) ∧ u ≠ w := by
      by_cases h : P = w
      · exact ⟨Q, hQ, fun e => hPQ (h.trans e.symm)⟩
      · exact ⟨P, hP, h⟩
    let u₀ : SemiLocal.PlacesOver E (w.under (𝓞 F)) := ⟨u, ⟨by rw [← hu']; rfl⟩⟩
    have hne' : w₀ ≠ u₀ := fun e => hne (congrArg Subtype.val e).symm
    have hle := Finset.add_le_sum (f := fun u : SemiLocal.PlacesOver E (w.under (𝓞 F)) => u.1.asIdeal.inertiaDeg (𝓞 F))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ w₀) (Finset.mem_univ u₀) hne'
    rw [hsum] at hle
    have p1 : 0 < w.asIdeal.inertiaDeg (𝓞 F) := inertiaDeg_pos w
    have p2 : 0 < u.asIdeal.inertiaDeg (𝓞 F) := inertiaDeg_pos u
    have hf : w.asIdeal.inertiaDeg (𝓞 F) = 1 := by
      change w.asIdeal.inertiaDeg (𝓞 F) + u.asIdeal.inertiaDeg (𝓞 F) ≤ 2 at hle
      omega
    rw [normV_eq_pow (F := F) w, hf, pow_one]
  · intro hn
    by_contra hs
    have hall : ∀ u : SemiLocal.PlacesOver E (w.under (𝓞 F)), u = w₀ := fun u =>
      Subtype.ext (GlobalTheory.LFun.eq_of_not_isSplit hs (under_of_mem u) rfl)
    rw [Finset.sum_eq_single w₀ (fun b _ hb => absurd (hall b) hb) (by simp)] at hsum
    change w.asIdeal.inertiaDeg (𝓞 F) = 2 at hsum
    rw [normV_eq_pow (F := F) w, hsum] at hn
    nlinarith

end UpperTheory.ConvolutionTheory.R2.C.QuadraticHeckeCharacter

/- English proof (translation)
Introduce `F E _ _ _ _ _ _`. Establish `h2 : Module.finrank F E = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two F E`. Take `⟨η, hη, -⟩` from `GlobalTheory.IdeleNormChar.globalNormIndexTwo F E h2`. Establish `hη' : GlobalTheory.LFun.IsEta F E η` using `hη`. Establish `he` using `hη'.eq_normSign`.

Use `⟨GlobalTheory.LFun.toHChar η hη'.isHeckeF, ?_, fun a => ?_⟩` and prove the remaining obligations. Establish `hfin` using `QuadraticHeckeCharacter.finite_bad (F := F) (E := E) filter_upwards [hfin.compl_mem_cofinite] with w hw v hv`. Establish `hw' : Formalism.MainNotions.SchurIrreducible.IsUnram (E` using `E) (w.under (𝓞 F)) := by simpa using hw`. Take `rfl : w.under (𝓞 F) = v` from `GlobalTheory.LFun.comap_eq_iff.1 hv.symm`. Use `⟨(hη'.unrAt_iff h2).2 hw', ?_⟩` and prove the remaining obligations.

Rewrite using `[hη'.val_eq h2 hw']`. Unfold `GlobalTheory.LFun.etaU`. Establish `hi` using `QuadraticHeckeCharacter.isSplit_iff_normV h2 w hw'`. Distinguish the cases in `hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 F))`. Rewrite using `[if_pos hs, if_pos (hi.1 hs)]`.

Rewrite using `[if_neg hs, if_neg (mt hi.2 hs)]`. Establish `h3 : ((GlobalTheory.LFun.toHChar η hη'.isHeckeF).1 a : ℂ) = ((η a : Circle) : ℂ)` using `rfl`. Rewrite using `[h3, he, MonoidHom.comp_apply]`. Apply the tactic sequence `rcases Int.units_eq_one_or (GlobalTheory.IdeleNormChar.normSign E a) with e | e <;>`. Simplify using `[e, GlobalTheory.IdeleNormChar.signToCircle]`.
-/
theorem UpperTheory.ConvolutionTheory.R2.C.etaQuad :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E], ∃ η : HChar F, IsQuadCharOf E η ∧
    ∀ a, ((η.1 a : ℂˣ) : ℂ) = (((GlobalTheory.IdeleNormChar.normSign E a : ℤˣ) : ℤ) : ℂ) := by
  intro F E _ _ _ _ _ _
  have h2 : Module.finrank F E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F E
  obtain ⟨η, hη, -⟩ := GlobalTheory.IdeleNormChar.globalNormIndexTwo F E h2
  have hη' : GlobalTheory.LFun.IsEta F E η := hη
  have he := hη'.eq_normSign
  refine ⟨GlobalTheory.LFun.toHChar η hη'.isHeckeF, ?_, fun a => ?_⟩
  · have hfin := QuadraticHeckeCharacter.finite_bad (F := F) (E := E)
    filter_upwards [hfin.compl_mem_cofinite] with w hw v hv
    have hw' : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (w.under (𝓞 F)) := by simpa using hw
    obtain rfl : w.under (𝓞 F) = v := GlobalTheory.LFun.comap_eq_iff.1 hv.symm
    refine ⟨(hη'.unrAt_iff h2).2 hw', ?_⟩
    rw [hη'.val_eq h2 hw']
    unfold GlobalTheory.LFun.etaU
    have hi := QuadraticHeckeCharacter.isSplit_iff_normV h2 w hw'
    by_cases hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 F))
    · rw [if_pos hs, if_pos (hi.1 hs)]
    · rw [if_neg hs, if_neg (mt hi.2 hs)]
  · have h3 : ((GlobalTheory.LFun.toHChar η hη'.isHeckeF).1 a : ℂ) = ((η a : Circle) : ℂ) := rfl
    rw [h3, he, MonoidHom.comp_apply]
    rcases Int.units_eq_one_or (GlobalTheory.IdeleNormChar.normSign E a) with e | e <;>
      simp [e, GlobalTheory.IdeleNormChar.signToCircle]

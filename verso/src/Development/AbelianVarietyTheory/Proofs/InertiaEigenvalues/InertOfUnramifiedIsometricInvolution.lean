import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedNonsplitExistsConjInvolutionUniformise

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.InertOfUnramInv

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

/- English proof (translation)
Establish `hval : ∀ k : L, Valued.v (algebraMap L (w.adicCompletion L) k) = w.valuation L k` using `fun k => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) k`. Establish `hU : IsOpen {z : w.adicCompletion L | Valued.v (z - x) < 1}`. Establish `h` using `(Valued.isOpen_ball (w.adicCompletion L) 1).preimage (continuous_sub_right x)`. Simplify `h` using `[Valuation.restrict_lt_one_iff]`. Take `⟨y, hy⟩` from `(HeightOneSpectrum.denseRange_algebraMap (K := L) (v := w)).exists_mem_open hU ⟨x, by simp⟩`.

Establish `hy' : Valued.v (algebraMap L (w.adicCompletion L) y - x) < 1` using `hy`. Establish `hyv : w.valuation L y ≤ 1`. Rewrite using `[← hval]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨a, ha⟩` from `HeightOneSpectrum.exists_valuation_sub_lt_of_integer (K := L) (v := w) hyv 1`.

Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `e : x - algebraMap L (w.adicCompletion L) (a : L) = -(algebraMap L (w.adicCompletion L) y - x) + -(algebraMap L (w.adicCompletion L) (a : L) - algebraMap L (w.adicCompletion L) y)` using `by ring`. Rewrite using `[e]`. Use `Valuation.map_add_lt _ (by rw [Valuation.map_neg]; exact hy') ?_` and prove the remaining obligations. Rewrite using `[Valuation.map_neg, ← map_sub, hval]`.

Simplify using `using ha`.
-/
theorem exists_int_approx (w : HeightOneSpectrum (𝓞 L)) (x : w.adicCompletion L) (hx : Valued.v x ≤ 1) :
    ∃ a : 𝓞 L, Valued.v (x - algebraMap L (w.adicCompletion L) (a : L)) < 1 := by
  have hval : ∀ k : L, Valued.v (algebraMap L (w.adicCompletion L) k) = w.valuation L k :=
    fun k => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) k
  have hU : IsOpen {z : w.adicCompletion L | Valued.v (z - x) < 1} := by
    have h := (Valued.isOpen_ball (w.adicCompletion L) 1).preimage (continuous_sub_right x)
    simpa [Valuation.restrict_lt_one_iff] using h
  obtain ⟨y, hy⟩ :=
    (HeightOneSpectrum.denseRange_algebraMap (K := L) (v := w)).exists_mem_open hU ⟨x, by simp⟩
  have hy' : Valued.v (algebraMap L (w.adicCompletion L) y - x) < 1 := hy
  have hyv : w.valuation L y ≤ 1 := by
    rw [← hval]
    calc Valued.v (algebraMap L (w.adicCompletion L) y)
        = Valued.v ((algebraMap L (w.adicCompletion L) y - x) + x) := by rw [sub_add_cancel]
      _ ≤ max (Valued.v (algebraMap L (w.adicCompletion L) y - x)) (Valued.v x) := Valuation.map_add _ _ _
      _ ≤ 1 := max_le hy'.le hx
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer (K := L) (v := w) hyv 1
  refine ⟨a, ?_⟩
  have e : x - algebraMap L (w.adicCompletion L) (a : L) =
      -(algebraMap L (w.adicCompletion L) y - x) + -(algebraMap L (w.adicCompletion L) (a : L) -
        algebraMap L (w.adicCompletion L) y) := by ring
  rw [e]
  refine Valuation.map_add_lt _ (by rw [Valuation.map_neg]; exact hy') ?_
  rw [Valuation.map_neg, ← map_sub, hval]
  simpa using ha

/- English proof (translation)
Introduce `L _ _ _ v w hvw s ϖ q hsc hU`. Unfold `Formalism.UG.IsUnramInv at hU`. Take `⟨-, hsv, -, -, ⟨x, hxO, hx1⟩, -, hcard⟩` from `hU`. Establish `hvw' : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L)) = v.asIdeal` using `hvw`. Establish `hlo : w.asIdeal.LiesOver v.asIdeal` using `⟨hvw'.symm⟩`.

Set `φ : 𝓞 L →+* w.adicCompletion L` to `(algebraMap L (w.adicCompletion L)).comp (algebraMap (𝓞 L) L)`. Establish `hφ : ∀ b : 𝓞 L, Valued.v (φ b) = w.valuation L (algebraMap (𝓞 L) L b)` using `fun b => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) (algebraMap (𝓞 L) L b)`. Establish `hval : ∀ b : 𝓞 L, Valued.v (φ b) < 1 ↔ b ∈ w.asIdeal`. Introduce `b`. Rewrite using `[hφ]`.

Conclude with `HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) w b`. Establish `hfix : ∀ a : 𝓞 (maximalRealSubfield L), s (φ (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a)) = φ (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a)`. Introduce `a`. Use `show s (algebraMap L _ _) = algebraMap L _ _`. Rewrite using `[hsc]`.

Use `congr 1`. Conclude with `(IsCMField.complexConj L).commutes (a : maximalRealSubfield L)`. Establish `hxv : Valued.v x ≤ 1` using `hxO`. Establish `hf1 : w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) ≠ 1`. Introduce `hf`.

Establish `hn` using `Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal`. Rewrite `hn` using `[hf, pow_one, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]`. Establish `hle : v.asIdeal ≤ w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L))` using `hvw'.ge`. Establish `hinj : Function.Injective (Ideal.quotientMap w.asIdeal _ hle)` using `Ideal.quotientMap_injective' hvw'.le`. Establish `hbij` using `(Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, hn⟩`.

Take `⟨b, hb⟩` from `exists_int_approx w x hxv`. Take `⟨a, ha⟩` from `hbij.2 (Ideal.Quotient.mk w.asIdeal b)`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Rewrite `ha` using `[Ideal.quotientMap_mk, Ideal.Quotient.eq]`. Establish `hsz` using `hfix a`.

Use `set z := φ (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a) with hz`. Establish `h1 : Valued.v (x - z) < 1`. Establish `e : x - z = (x - φ b) + -(φ (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a - b))`. Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Use `Valuation.map_add_lt _ hb ?_` and prove the remaining obligations. Rewrite using `[Valuation.map_neg, hval]`. Conclude with `ha`. Establish `h2 : s x - x = s (x - z) + -(x - z)`.

Rewrite using `[map_sub, hsz]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : Valued.v (s x - x) < 1`. Rewrite using `[h2]`. Use `Valuation.map_add_lt _ ?_ ?_` and prove the remaining obligations.

Rewrite using `[hsv]`. Conclude with `h1`. Rewrite using `[Valuation.map_neg]`. Conclude with `h1`. Conclude with `absurd hx1 (ne_of_lt h3)`.

Establish `hfpos` using `Ideal.inertiaDeg_pos w.asIdeal (𝓞 (maximalRealSubfield L))`. Establish `hepos` using `Ideal.ramificationIdx_pos w.asIdeal (𝓞 (maximalRealSubfield L))`. Establish `hG2 : Nat.card (L ≃ₐ[maximalRealSubfield L] L) = 2`. Rewrite using `[IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]`. Establish `hsum` using `Ideal.sum_ramification_inertia_eq_card v.asIdeal (𝓞 L) (G := L ≃ₐ[maximalRealSubfield L] L)`.

Set `F : v.asIdeal.primesOver (𝓞 L) → ℕ` to `fun P => P.1.ramificationIdx (𝓞 (maximalRealSubfield L)) * P.1.inertiaDeg (𝓞 (maximalRealSubfield L))`. Establish `hsum' : ∑ P, F P = 2`. Rewrite using `[← hG2, ← hsum]`. Set `W : v.asIdeal.primesOver (𝓞 L)` to `⟨w.asIdeal, w.isPrime, hlo⟩`. Establish `hW : F W ≤ 2`.

Rewrite using `[← hsum']`. Conclude with `Finset.single_le_sum (f := F) (fun _ _ => Nat.zero_le _) (Finset.mem_univ W)`. Establish `hW' : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield L)) * w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) ≤ 2` using `hW`. Establish `hf2 : w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) = 2`. Establish `: 2 ≤ w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L))` using `by omega`.

Use the polynomial consequences of the given equalities and inequalities. Establish `he1 : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield L)) = 1`. Rewrite `hW'` using `[hf2]`. Use linear arithmetic over natural numbers and integers. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `: (w.asIdeal.under (𝓞 (maximalRealSubfield L))).IsMaximal`. Rewrite using `[← hlo.over]`. Conclude with `v.isMaximal`. Conclude with `Ideal.ramificationIdx_eq_one_iff.mp he1`. Introduce and unpack `⟨u, hne, hu⟩`.

Establish `hlu : u.asIdeal.LiesOver v.asIdeal` using `⟨by`. Rewrite using `[hlo.over]`. Conclude with `(congrArg HeightOneSpectrum.asIdeal hu).symm⟩`. Set `U : v.asIdeal.primesOver (𝓞 L)` to `⟨u.asIdeal, u.isPrime, hlu⟩`. Establish `hWU : W ≠ U` using `fun h => hne (HeightOneSpectrum.ext (congrArg Subtype.val h).symm)`.

Establish `h2 : F W + F U ≤ 2`. Rewrite using `[← hsum', ← Finset.sum_pair hWU]`. Conclude with `Finset.sum_le_sum_of_subset (Finset.subset_univ _)`. Establish `hu1` using `Ideal.inertiaDeg_pos u.asIdeal (𝓞 (maximalRealSubfield L))`. Establish `hu2` using `Ideal.ramificationIdx_pos u.asIdeal (𝓞 (maximalRealSubfield L))`.

Establish `hFU : 1 ≤ F U` using `Nat.mul_pos hu2 hu1`. Establish `hFW : F W = 2` using `by show w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield L)) * w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) = 2`. Rewrite using `[he1, hf2]`. Use linear arithmetic over natural numbers and integers. Set `O` to `(Valued.v : Valuation (w.adicCompletion L) (WithZero (Multiplicative ℤ))).valuationSubring`.

Establish `hmemO : ∀ b : 𝓞 L, φ b ∈ O`. Introduce `b`. Use `show Valued.v (φ b) ≤ 1`. Rewrite using `[hφ]`. Conclude with `HeightOneSpectrum.valuation_le_one (K := L) w b`.

Set `g : 𝓞 L →+* O` to `φ.codRestrict O hmemO`. Establish `hmax : ∀ y : O, y ∈ IsLocalRing.maximalIdeal O ↔ Valued.v (y : w.adicCompletion L) < 1`. Introduce `y`. Establish `hle : Valued.v (y : w.adicCompletion L) ≤ 1` using `y.2`. Establish `hu : IsUnit y ↔ Valued.v (y : w.adicCompletion L) = 1` using `HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one (K := L) (v := w) (a := y)`.

Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hu]`. Conclude with `⟨fun h => lt_of_le_of_ne hle h, fun h => ne_of_lt h⟩`. Set `G` to `(Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)).comp g`. Establish `hGs : Function.Surjective G`. Introduce `Y`.

Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective Y`. Take `⟨b, hb⟩` from `exists_int_approx w (y : w.adicCompletion L) y.2`. Use `⟨b, ?_⟩` and prove the remaining obligations. Use `show Ideal.Quotient.mk _ (g b) = Ideal.Quotient.mk _ y`. Rewrite using `[Ideal.Quotient.eq, hmax]`.

Use `show Valued.v (φ b - (y : w.adicCompletion L)) < 1`. Rewrite using `[← Valuation.map_neg, neg_sub]`. Conclude with `hb`. Establish `hker : RingHom.ker G = w.asIdeal`. Use extensionality with `b`.

Rewrite using `[RingHom.mem_ker]`. Use `show Ideal.Quotient.mk _ (g b) = 0 ↔ _`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, hmax]`. Conclude with `hval b`. Establish `hc` using `Nat.card_congr (RingHom.quotientKerEquivOfSurjective hGs).toEquiv`.

Rewrite `hc` using `[hker]`. Establish `hcard' : Nat.card (O ⧸ IsLocalRing.maximalIdeal O) = q ^ 2` using `hcard`. Establish `hn` using `Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal`. Rewrite `hn` using `[hf2, Ideal.absNorm_apply w.asIdeal, Submodule.cardQuot_apply, hc, hcard']`. Use `show q = Ideal.absNorm v.asIdeal`.

Conclude with `Nat.pow_left_injective (n := 2) (by norm_num) hn.symm`.
-/
theorem inert_of_isUnramInv : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s q → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal ∧ ¬ IsSplitAt w ∧ q = Formalism.UG.qV (maximalRealSubfield L) v := by
  intro L _ _ _ v w hvw s ϖ q hsc hU
  unfold Formalism.UG.IsUnramInv at hU
  obtain ⟨-, hsv, -, -, ⟨x, hxO, hx1⟩, -, hcard⟩ := hU
  have hvw' : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L)) = v.asIdeal := hvw
  have hlo : w.asIdeal.LiesOver v.asIdeal := ⟨hvw'.symm⟩
  let φ : 𝓞 L →+* w.adicCompletion L := (algebraMap L (w.adicCompletion L)).comp (algebraMap (𝓞 L) L)
  have hφ : ∀ b : 𝓞 L, Valued.v (φ b) = w.valuation L (algebraMap (𝓞 L) L b) :=
    fun b => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) (algebraMap (𝓞 L) L b)
  have hval : ∀ b : 𝓞 L, Valued.v (φ b) < 1 ↔ b ∈ w.asIdeal := by
    intro b
    rw [hφ]
    exact HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) w b
  have hfix : ∀ a : 𝓞 (maximalRealSubfield L),
      s (φ (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a)) = φ (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a) := by
    intro a
    show s (algebraMap L _ _) = algebraMap L _ _
    rw [hsc]
    congr 1
    exact (IsCMField.complexConj L).commutes (a : maximalRealSubfield L)
  have hxv : Valued.v x ≤ 1 := hxO

  have hf1 : w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) ≠ 1 := by
    intro hf
    have hn := Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal
    rw [hf, pow_one, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Submodule.cardQuot_apply] at hn
    have hle : v.asIdeal ≤ w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L)) := hvw'.ge
    have hinj : Function.Injective (Ideal.quotientMap w.asIdeal _ hle) :=
      Ideal.quotientMap_injective' hvw'.le
    have hbij := (Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, hn⟩
    obtain ⟨b, hb⟩ := exists_int_approx w x hxv
    obtain ⟨a, ha⟩ := hbij.2 (Ideal.Quotient.mk w.asIdeal b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at ha
    have hsz := hfix a
    set z := φ (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a) with hz
    have h1 : Valued.v (x - z) < 1 := by
      have e : x - z = (x - φ b) + -(φ (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a - b)) := by
        rw [map_sub]; ring
      rw [e]
      refine Valuation.map_add_lt _ hb ?_
      rw [Valuation.map_neg, hval]
      exact ha
    have h2 : s x - x = s (x - z) + -(x - z) := by
      rw [map_sub, hsz]; ring
    have h3 : Valued.v (s x - x) < 1 := by
      rw [h2]
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [hsv]; exact h1
      · rw [Valuation.map_neg]; exact h1
    exact absurd hx1 (ne_of_lt h3)
  have hfpos := Ideal.inertiaDeg_pos w.asIdeal (𝓞 (maximalRealSubfield L))
  have hepos := Ideal.ramificationIdx_pos w.asIdeal (𝓞 (maximalRealSubfield L))

  have hG2 : Nat.card (L ≃ₐ[maximalRealSubfield L] L) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  have hsum := Ideal.sum_ramification_inertia_eq_card v.asIdeal (𝓞 L)
    (G := L ≃ₐ[maximalRealSubfield L] L)
  let F : v.asIdeal.primesOver (𝓞 L) → ℕ := fun P =>
    P.1.ramificationIdx (𝓞 (maximalRealSubfield L)) * P.1.inertiaDeg (𝓞 (maximalRealSubfield L))
  have hsum' : ∑ P, F P = 2 := by
    rw [← hG2, ← hsum]
  let W : v.asIdeal.primesOver (𝓞 L) := ⟨w.asIdeal, w.isPrime, hlo⟩
  have hW : F W ≤ 2 := by
    rw [← hsum']
    exact Finset.single_le_sum (f := F) (fun _ _ => Nat.zero_le _) (Finset.mem_univ W)
  have hW' : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield L)) *
      w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) ≤ 2 := hW
  have hf2 : w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) = 2 := by
    have : 2 ≤ w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) := by omega
    nlinarith
  have he1 : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield L)) = 1 := by
    rw [hf2] at hW'
    omega
  refine ⟨?_, ?_, ?_⟩
  · have : (w.asIdeal.under (𝓞 (maximalRealSubfield L))).IsMaximal := by
      rw [← hlo.over]
      exact v.isMaximal
    exact Ideal.ramificationIdx_eq_one_iff.mp he1
  · rintro ⟨u, hne, hu⟩
    have hlu : u.asIdeal.LiesOver v.asIdeal := ⟨by
      rw [hlo.over]
      exact (congrArg HeightOneSpectrum.asIdeal hu).symm⟩
    let U : v.asIdeal.primesOver (𝓞 L) := ⟨u.asIdeal, u.isPrime, hlu⟩
    have hWU : W ≠ U := fun h => hne (HeightOneSpectrum.ext (congrArg Subtype.val h).symm)
    have h2 : F W + F U ≤ 2 := by
      rw [← hsum', ← Finset.sum_pair hWU]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have hu1 := Ideal.inertiaDeg_pos u.asIdeal (𝓞 (maximalRealSubfield L))
    have hu2 := Ideal.ramificationIdx_pos u.asIdeal (𝓞 (maximalRealSubfield L))
    have hFU : 1 ≤ F U := Nat.mul_pos hu2 hu1
    have hFW : F W = 2 := by
      show w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield L)) *
        w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) = 2
      rw [he1, hf2]
    omega
  ·
    let O := (Valued.v : Valuation (w.adicCompletion L) (WithZero (Multiplicative ℤ))).valuationSubring
    have hmemO : ∀ b : 𝓞 L, φ b ∈ O := by
      intro b
      show Valued.v (φ b) ≤ 1
      rw [hφ]
      exact HeightOneSpectrum.valuation_le_one (K := L) w b
    let g : 𝓞 L →+* O := φ.codRestrict O hmemO
    have hmax : ∀ y : O, y ∈ IsLocalRing.maximalIdeal O ↔ Valued.v (y : w.adicCompletion L) < 1 := by
      intro y
      have hle : Valued.v (y : w.adicCompletion L) ≤ 1 := y.2
      have hu : IsUnit y ↔ Valued.v (y : w.adicCompletion L) = 1 :=
        HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one (K := L) (v := w) (a := y)
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hu]
      exact ⟨fun h => lt_of_le_of_ne hle h, fun h => ne_of_lt h⟩
    let G := (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)).comp g
    have hGs : Function.Surjective G := by
      intro Y
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective Y
      obtain ⟨b, hb⟩ := exists_int_approx w (y : w.adicCompletion L) y.2
      refine ⟨b, ?_⟩
      show Ideal.Quotient.mk _ (g b) = Ideal.Quotient.mk _ y
      rw [Ideal.Quotient.eq, hmax]
      show Valued.v (φ b - (y : w.adicCompletion L)) < 1
      rw [← Valuation.map_neg, neg_sub]
      exact hb
    have hker : RingHom.ker G = w.asIdeal := by
      ext b
      rw [RingHom.mem_ker]
      show Ideal.Quotient.mk _ (g b) = 0 ↔ _
      rw [Ideal.Quotient.eq_zero_iff_mem, hmax]
      exact hval b
    have hc := Nat.card_congr (RingHom.quotientKerEquivOfSurjective hGs).toEquiv
    rw [hker] at hc
    have hcard' : Nat.card (O ⧸ IsLocalRing.maximalIdeal O) = q ^ 2 := hcard
    have hn := Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal
    rw [hf2, Ideal.absNorm_apply w.asIdeal, Submodule.cardQuot_apply, hc, hcard'] at hn
    show q = Ideal.absNorm v.asIdeal
    exact Nat.pow_left_injective (n := 2) (by norm_num) hn.symm

end GlobalTheory.InertOfUnramInv

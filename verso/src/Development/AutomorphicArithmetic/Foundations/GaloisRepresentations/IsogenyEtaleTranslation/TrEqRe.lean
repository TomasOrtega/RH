import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.EtCancel

open NumberField Polynomial GlobalTheory.UPel.HT GlobalTheory.LKGeo GlobalTheory.LKTrip

namespace UpperTheory.Gal.FixZ

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Introduce `h`. Establish `him : D.ρc.im = 0` using `Complex.conj_eq_iff_im.mp h`. Establish `hre : D.ρc = (D.ρc.re : ℂ)`. Apply the tactic sequence `apply Complex.ext <;> simp [him]`. Establish `hroot` using `D.ρc_root`.

Rewrite `hroot` using `[hre]`. Establish `hr : D.ρc.re ^ 2 - (D.tr : ℝ) * D.ρc.re + (D.nm : ℝ) = 0`. Conclude with `hroot` after adjusting the coercions. Establish `hd : ((D.tr : ℝ)) ^ 2 - 4 * (D.nm : ℝ) < 0` using `by exact_mod_cast D.disc_neg`. Use polynomial arithmetic with `[sq_nonneg (2 * D.ρc.re - (D.tr : ℝ))]`.
-/
private lemma conj_ne (D : Datum p) : (starRingEnd ℂ) D.ρc ≠ D.ρc := by
  intro h
  have him : D.ρc.im = 0 := Complex.conj_eq_iff_im.mp h
  have hre : D.ρc = (D.ρc.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hroot := D.ρc_root
  rw [hre] at hroot
  have hr : D.ρc.re ^ 2 - (D.tr : ℝ) * D.ρc.re + (D.nm : ℝ) = 0 := by
    exact_mod_cast hroot
  have hd : ((D.tr : ℝ)) ^ 2 - 4 * (D.nm : ℝ) < 0 := by exact_mod_cast D.disc_neg
  nlinarith [sq_nonneg (2 * D.ρc.re - (D.tr : ℝ))]

/- English proof (translation)
Establish `hne : D.ρc - (starRingEnd ℂ) D.ρc ≠ 0` using `sub_ne_zero.mpr (Ne.symm (conj_ne D))`. Establish `h1` using `D.ρc_root`. Establish `h2 : ((starRingEnd ℂ) D.ρc) ^ 2 - (D.tr : ℂ) * (starRingEnd ℂ) D.ρc + (D.nm : ℂ) = 0`. Use `congrArg (starRingEnd ℂ) h1` as an intermediate fact. Simplify using `using this`.

Apply `mul_left_cancel₀ hne` to reduce the goal to its premises. Take the linear combination `h2 - h1`.
-/
private lemma tr_eq_re (D : Datum p) : (D.tr : ℂ) = D.ρc + (starRingEnd ℂ) D.ρc := by
  have hne : D.ρc - (starRingEnd ℂ) D.ρc ≠ 0 := sub_ne_zero.mpr (Ne.symm (conj_ne D))
  have h1 := D.ρc_root
  have h2 : ((starRingEnd ℂ) D.ρc) ^ 2 - (D.tr : ℂ) * (starRingEnd ℂ) D.ρc + (D.nm : ℂ) = 0 := by
    have := congrArg (starRingEnd ℂ) h1
    simpa using this
  apply mul_left_cancel₀ hne
  linear_combination h2 - h1

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Establish `hω : ((D.ω : D.F)) ^ 2 - (D.tr : D.F) * (D.ω : D.F) + (D.nm : D.F) = 0`. Establish `h1 : (D.ω : 𝓞 D.F) ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0`. Rewrite using `[← D.tr_eq, ← D.nm_eq]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2` using `congrArg (algebraMap (𝓞 D.F) D.F) h1`. Simplify `h2` using `only [map_sub, map_add, map_mul, map_pow, map_intCast, map_zero]`. Establish `hτ : (τ (D.ω : D.F)) ^ 2 - (D.tr : ℂ) * τ (D.ω : D.F) + (D.nm : ℂ) = 0`. Use `congrArg τ hω` as an intermediate fact. Simplify using `using this`.

Establish `hfac : (τ (D.ω : D.F) - D.ρc) * (τ (D.ω : D.F) - (starRingEnd ℂ) D.ρc) = 0`. Establish `h1` using `D.ρc_root`. Establish `h2` using `tr_eq_re D`. Rewrite `h1`, `hτ` using `[h2]`. Take the linear combination `hτ - h1`.

Unfold `W2.epsD LocalSmoothExtension.epsOf`. Distinguish the cases in `h : τ (D.ω : D.F) = D.ρc`. Establish `: τ (D.ω : D.F) ≠ (starRingEnd ℂ) D.ρc`. Rewrite using `[h]`. Conclude with `Ne.symm (conj_ne D)`.

Simplify using `[h, Ne.symm (conj_ne D)]`. Establish `h' : τ (D.ω : D.F) = (starRingEnd ℂ) D.ρc`. Break down `mul_eq_zero.mp hfac with h0 | h0` into its components or cases. Conclude with `absurd (sub_eq_zero.mp h0) h`. Conclude with `sub_eq_zero.mp h0`.

Rewrite using `[if_neg h, if_pos h']`.
-/
private lemma eps_eq (D : Datum p) : W2.epsD D = LocalSmoothExtension.epsOf D := by
  funext τ
  have hω : ((D.ω : D.F)) ^ 2 - (D.tr : D.F) * (D.ω : D.F) + (D.nm : D.F) = 0 := by
    have h1 : (D.ω : 𝓞 D.F) ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
      rw [← D.tr_eq, ← D.nm_eq]; ring
    have h2 := congrArg (algebraMap (𝓞 D.F) D.F) h1
    simpa only [map_sub, map_add, map_mul, map_pow, map_intCast, map_zero] using h2
  have hτ : (τ (D.ω : D.F)) ^ 2 - (D.tr : ℂ) * τ (D.ω : D.F) + (D.nm : ℂ) = 0 := by
    have := congrArg τ hω
    simpa using this
  have hfac : (τ (D.ω : D.F) - D.ρc) * (τ (D.ω : D.F) - (starRingEnd ℂ) D.ρc) = 0 := by
    have h1 := D.ρc_root
    have h2 := tr_eq_re D
    rw [h2] at h1 hτ
    linear_combination hτ - h1
  unfold W2.epsD LocalSmoothExtension.epsOf
  by_cases h : τ (D.ω : D.F) = D.ρc
  · have : τ (D.ω : D.F) ≠ (starRingEnd ℂ) D.ρc := by
      rw [h]; exact Ne.symm (conj_ne D)
    simp [h, Ne.symm (conj_ne D)]
  · have h' : τ (D.ω : D.F) = (starRingEnd ℂ) D.ρc := by
      rcases mul_eq_zero.mp hfac with h0 | h0
      · exact absurd (sub_eq_zero.mp h0) h
      · exact sub_eq_zero.mp h0
    rw [if_neg h, if_pos h']

/- English proof (translation)
Unfold `W2.invPoly LocalSmoothExtension.invPol`. Rewrite using `[Polynomial.map_mul, Polynomial.map_C, map_inv₀, Polynomial.coeff_map]`. Use `congr 1`. Simplify using `only [Polynomial.reverse, Polynomial.natDegree_map, Polynomial.reflect_map]`.
-/
private lemma map_inv {K K' : Type} [Field K] [Field K'] (f : K →+* K') (P : K[X]) :
    (W2.invPoly P).map f = LocalSmoothExtension.invPol (P.map f) := by
  unfold W2.invPoly LocalSmoothExtension.invPol
  rw [Polynomial.map_mul, Polynomial.map_C, map_inv₀, Polynomial.coeff_map]
  congr 1
  simp only [Polynomial.reverse, Polynomial.natDegree_map, Polynomial.reflect_map]

/- English proof (translation)
Use `⟨fun h => (h _).trans (D.tau_ω i₀), fun h => ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `(L.sig v).mp hv`. Establish `hii : i = i₀` using `by haveI : Subsingleton (Fin D.a) := by rw [ha]; infer_instance`. Conclude with `Subsingleton.elim _ _`. Substitute `hii` using the available equality.

Establish `hs : ∀ x, (G.iotaC.comp (L.s i)) (L.e x) = D.tau i x` using `fun x => L.s_C i x`. Break down `InfinitePlace.embedding_mk_eq (G.iotaC.comp (L.s i)) with e | e` into its components or cases. Introduce `x`. Rewrite using `[hi, e]`. Conclude with `hs x`.

It suffices to derive a contradiction. Rewrite `h` using `[hi, e, ComplexEmbedding.conjugate_coe_eq, hs, D.tau_ω]`. Conclude with `conj_ne D h`.
-/
private lemma kap_iff {D : Datum p} {G : HTGroup p} (L : Link D G) (ha : D.a = 1) (i₀ : Fin D.a)
    (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1) :
    (∀ x, v.embedding (L.e x) = D.tau i₀ x) ↔ v.embedding (L.e (D.ω : D.F)) = D.ρc := by
  refine ⟨fun h => (h _).trans (D.tau_ω i₀), fun h => ?_⟩
  obtain ⟨i, hi⟩ := (L.sig v).mp hv
  have hii : i = i₀ := by
    haveI : Subsingleton (Fin D.a) := by rw [ha]; infer_instance
    exact Subsingleton.elim _ _
  subst hii
  have hs : ∀ x, (G.iotaC.comp (L.s i)) (L.e x) = D.tau i x := fun x => L.s_C i x
  rcases InfinitePlace.embedding_mk_eq (G.iotaC.comp (L.s i)) with e | e
  · intro x
    rw [hi, e]
    exact hs x
  · exfalso
    rw [hi, e, ComplexEmbedding.conjugate_coe_eq, hs, D.tau_ω] at h
    exact conj_ne D h

/- English proof (translation)
Unfold `W2.kap LocalSmoothExtension.markOf`. Distinguish the cases in `h : v.embedding (L.e (D.ω : D.F)) = D.ρc`. Rewrite using `[if_pos ((kap_iff L ha i₀ v hv).mpr h), if_pos h]`. Rewrite using `[if_neg (fun h' => h ((kap_iff L ha i₀ v hv).mp h')), if_neg h]`.
-/
private lemma kap_eq {D : Datum p} {G : HTGroup p} (L : Link D G) (ha : D.a = 1) (i₀ : Fin D.a)
    (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1) (μ : ℂ) :
    (W2.kap L v (D.tau i₀) μ)⁻¹ = LocalSmoothExtension.markOf L v μ := by
  unfold W2.kap LocalSmoothExtension.markOf
  by_cases h : v.embedding (L.e (D.ω : D.F)) = D.ρc
  · rw [if_pos ((kap_iff L ha i₀ v hv).mpr h), if_pos h]
  · rw [if_neg (fun h' => h ((kap_iff L ha i₀ v hv).mp h')), if_neg h]

end UpperTheory.Gal.FixZ

/- English proof (translation)
Introduce `p _ D G L ha i₀ v hv k α y`. Use function extensionality and compare the values at `P μ`. Unfold `UpperTheory.Gal.W2.wtFix UpperTheory.Gal.LocalSmoothExtension.cW UpperTheory.Gal.LocalSmoothExtension.endPol`. Rewrite using `[UpperTheory.Gal.FixZ.eps_eq, UpperTheory.Gal.FixZ.map_inv, UpperTheory.Gal.FixZ.kap_eq L ha i₀ v hv μ]`.
-/
theorem UpperTheory.Gal.FixZ.wtEq_of :
    UpperTheory.Gal.FixZ.WtEq := by
  intro p _ D G L ha i₀ v hv k α y
  funext P μ
  unfold UpperTheory.Gal.W2.wtFix UpperTheory.Gal.LocalSmoothExtension.cW UpperTheory.Gal.LocalSmoothExtension.endPol
  rw [UpperTheory.Gal.FixZ.eps_eq, UpperTheory.Gal.FixZ.map_inv, UpperTheory.Gal.FixZ.kap_eq L ha i₀ v hv μ]

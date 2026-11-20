import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreSemilocalCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyDimensionInequality
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

/- English proof (translation)
Set `_ : Algebra R R'` to `ψ.toRingHom.toAlgebra`. Set `e : (R ⧸ Ideal.span {r}) ≃ₐ[R] R' ⧸ Ideal.span {ψ r}` to `Ideal.quotientEquivAlg _ _ (AlgEquiv.ofRingEquiv (f := ψ) fun _ => rfl) (by rw [Ideal.map_span, Set.image_singleton]; rfl)`. Rewrite using `[e.toLinearEquiv.length_eq, Module.length_eq_of_surjective ψ.surjective]`.
-/
theorem length_quot_span_ringEquiv {R R' : Type*} [CommRing R] [CommRing R'] (ψ : R ≃+* R') (r : R) :
    Module.length R (R ⧸ Ideal.span {r}) = Module.length R' (R' ⧸ Ideal.span {ψ r}) := by
  let _ : Algebra R R' := ψ.toRingHom.toAlgebra
  let e : (R ⧸ Ideal.span {r}) ≃ₐ[R] R' ⧸ Ideal.span {ψ r} :=
    Ideal.quotientEquivAlg _ _ (AlgEquiv.ofRingEquiv (f := ψ) fun _ => rfl)
      (by rw [Ideal.map_span, Set.image_singleton]; rfl)
  rw [e.toLinearEquiv.length_eq, Module.length_eq_of_surjective ψ.surjective]

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel g hg hgW hz`. Use `hP.multiProj.isPrime` as an intermediate fact. Take `⟨hfinite, hrank⟩` from `hfin O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel`. Take `⟨e, he⟩` from `hmax O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel`. Establish `hbl : IsModelOver (blowUpOf P u) n` using `BlowUpModel.full O K ι J P n hP N u hu hu'`.

Use `⟨blowUpOverLoc P W u, inferInstance, inferInstance, inferInstance, hfinite, Subring.inclusion_injective _, hrank, e, fun 𝔫 => ⟨?_, (he 𝔫).2⟩⟩` and prove the remaining obligations. Take `⟨h, hloc⟩` from `(he 𝔫).1`. Generalize the expression as in `e 𝔫 = Q at h hloc ⊢`. Take `⟨Q, hQmin, hQrel, hQW⟩` from `Q`. Simplify using `only at h hloc ⊢`.

Establish `hblQ : blowUpOf P u ≤ Q` using `le_trans le_sup_left hQmin.1.2`. Establish `hxl : IsMultiHomog (liftForm (J` using `J) x) (liftMDeg c) := isMultiHomog_liftForm hx`. Establish `hgl : IsMultiHomog (liftForm (J` using `J) g) (liftMDeg c) := isMultiHomog_liftForm hg`. Establish `hgQ : liftForm (J` using `J) g ∉ Q := fun hm => hgW (by rw [← hQW]; exact hm)`. Establish `hxbl : liftForm (J` using `J) x ∉ blowUpOf P u := liftForm_not_mem_blowUpOf hxP`.

Establish `: (blowUpOf P u).IsPrime` using `RingHom.ker_isPrime _`. Establish `hz' : algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u) (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm x)) / algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u) (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm g) …` using `Subring.subset_closure ⟨liftMDeg c, _, _, hxl, hgl, hgQ, rfl⟩`. Take `⟨φ, hφ⟩` from `hiso O K ι J P u Q hblQ`. Establish `hlen : Module.length (homLocRing (blowUpOf P u) Q) (homLocRing (blowUpOf P u) Q ⧸ Ideal.span {(⟨_, hz'⟩ : homLocRing (blowUpOf P u) Q)}) = ((divCycle (blowUpOf P u) (liftForm x) Q).toNat : ℕ∞)`. Establish `hinj` using `IsFractionRing.injective (MRing (extIdx ι J) O ⧸ blowUpOf P u) (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u))`.

Establish `hne : ∀ y : MRing (extIdx ι J) O, y ∉ blowUpOf P u → algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u) (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ y) ≠ 0`. Introduce `y hy`. Rewrite using `[Ne, map_eq_zero_iff _ hinj, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hy`. Establish `hz0 : (⟨_, hz'⟩ : homLocRing (blowUpOf P u) Q) ≠ 0` using `fun h0 => div_ne_zero (hne _ hxbl) (hne _ fun hm => hgQ (hblQ hm)) (congrArg Subtype.val h0)`.

Establish `hQp : Q.IsPrime` using `hQmin.1.1`. Establish `hmult` using `hb O (Option K) (extIdx ι J) (blowUpOf P u) hbl.multiProj (liftMDeg c) (liftForm x) hxl hxbl Q hQmin hQrel (liftForm g) hgl hgQ hz'`. Establish `hloc'` using `ha O (Option K) (extIdx ι J) (blowUpOf P u) hbl.multiProj (liftMDeg c) (liftForm x) hxl hxbl Q hQmin hQrel`. Establish `hn : IsNoetherianRing (homLocRing (blowUpOf P u) Q)` using `hloc'.2.1`. Establish `hd : ringKrullDim (homLocRing (blowUpOf P u) Q) = 1` using `hloc'.2.2`.

Establish `hdivQ : divCycle (blowUpOf P u) (liftForm x) Q = ((multAt (blowUpOf P u ⊔ Ideal.span {liftForm x}) Q).toNat : ℤ)`. Unfold `divCycle`. Rewrite using `[dif_pos ⟨hQmin, hQrel⟩]`. Establish `: Ring.KrullDimLE 1 (homLocRing (blowUpOf P u) Q)`. Rewrite using `[Ring.krullDimLE_iff, hd]`.

Both sides reduce to the same expression. Establish `hfinl : Module.length (homLocRing (blowUpOf P u) Q) (homLocRing (blowUpOf P u) Q ⧸ Ideal.span {(⟨_, hz'⟩ : homLocRing (blowUpOf P u) Q)}) ≠ ⊤` using `Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_of_ne_zero hz0))`. Rewrite using `[hdivQ, Int.toNat_natCast, hmult, ENat.natCast_toNat hfinl]`. Set `_` to `(Subring.inclusion h).toAlgebra`. Use `𝔫.2.isPrime` as an intermediate fact.

Use `hloc` as an intermediate fact. Set `ψ₁ : Localization.AtPrime 𝔫.1 ≃ₐ[blowUpOverLoc P W u] blowUpLocRing P u Q` to `IsLocalization.algEquiv 𝔫.1.primeCompl _ _`. Set `ψ : Localization.AtPrime 𝔫.1 ≃+* homLocRing (blowUpOf P u) Q` to `ψ₁.toRingEquiv.trans φ.symm`. Establish `hψ : ψ (algebraMap (blowUpOverLoc P W u) (Localization.AtPrime 𝔫.1) (algebraMap (homLocRing P W) (blowUpOverLoc P W u) ⟨_, hz⟩)) = ⟨_, hz'⟩`. Apply `φ.injective` to reduce the goal to its premises.

Simplify using `only [ψ, RingEquiv.trans_apply, RingEquiv.apply_symm_apply, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hφ (liftMDeg c) _ _ hxl hgl hgQ, blowUpEval_liftForm, blowUpEval_liftForm]`. Both sides reduce to the same expression. Rewrite using `[length_quot_span_ringEquiv ψ, hψ]`.

Conclude with `hlen`.
-/
theorem BlowUpFibreSemilocal.proof (ha : HomLocRingLocal.Statement.{u})
    (hb : DivCycleHomLoc.Statement.{u}) (hiso : BlowUpLocRingIso.Statement.{u})
    (hfin : BlowUpOverLocFinite.Statement.{u}) (hmax : BlowUpOverLocMax.Statement.{u}) :
    BlowUpFibreSemilocal.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel g hg hgW hz
  have := hP.multiProj.isPrime
  obtain ⟨hfinite, hrank⟩ := hfin O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel
  obtain ⟨e, he⟩ := hmax O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have hbl : IsModelOver (blowUpOf P u) n := BlowUpModel.full O K ι J P n hP N u hu hu'
  refine ⟨blowUpOverLoc P W u, inferInstance, inferInstance, inferInstance, hfinite,
    Subring.inclusion_injective _, hrank, e, fun 𝔫 => ⟨?_, (he 𝔫).2⟩⟩
  obtain ⟨h, hloc⟩ := (he 𝔫).1
  generalize e 𝔫 = Q at h hloc ⊢
  obtain ⟨Q, hQmin, hQrel, hQW⟩ := Q
  dsimp only at h hloc ⊢
  have hblQ : blowUpOf P u ≤ Q := le_trans le_sup_left hQmin.1.2
  have hxl : IsMultiHomog (liftForm (J := J) x) (liftMDeg c) := isMultiHomog_liftForm hx
  have hgl : IsMultiHomog (liftForm (J := J) g) (liftMDeg c) := isMultiHomog_liftForm hg
  have hgQ : liftForm (J := J) g ∉ Q := fun hm => hgW (by rw [← hQW]; exact hm)
  have hxbl : liftForm (J := J) x ∉ blowUpOf P u := liftForm_not_mem_blowUpOf hxP
  have : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  have hz' : algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
        (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm x)) /
      algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
        (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm g)) ∈
      homLocRing (blowUpOf P u) Q :=
    Subring.subset_closure ⟨liftMDeg c, _, _, hxl, hgl, hgQ, rfl⟩
  obtain ⟨φ, hφ⟩ := hiso O K ι J P u Q hblQ

  have hlen : Module.length (homLocRing (blowUpOf P u) Q)
      (homLocRing (blowUpOf P u) Q ⧸ Ideal.span {(⟨_, hz'⟩ : homLocRing (blowUpOf P u) Q)}) =
        ((divCycle (blowUpOf P u) (liftForm x) Q).toNat : ℕ∞) := by
    have hinj := IsFractionRing.injective (MRing (extIdx ι J) O ⧸ blowUpOf P u)
      (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u))
    have hne : ∀ y : MRing (extIdx ι J) O, y ∉ blowUpOf P u →
        algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
          (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ y) ≠ 0 := by
      intro y hy
      rw [Ne, map_eq_zero_iff _ hinj, Ideal.Quotient.eq_zero_iff_mem]
      exact hy
    have hz0 : (⟨_, hz'⟩ : homLocRing (blowUpOf P u) Q) ≠ 0 := fun h0 =>
      div_ne_zero (hne _ hxbl) (hne _ fun hm => hgQ (hblQ hm)) (congrArg Subtype.val h0)
    have hQp : Q.IsPrime := hQmin.1.1
    have hmult := hb O (Option K) (extIdx ι J) (blowUpOf P u) hbl.multiProj (liftMDeg c) (liftForm x) hxl
      hxbl Q hQmin hQrel (liftForm g) hgl hgQ hz'
    have hloc' := ha O (Option K) (extIdx ι J) (blowUpOf P u) hbl.multiProj (liftMDeg c)
      (liftForm x) hxl hxbl Q hQmin hQrel
    have hn : IsNoetherianRing (homLocRing (blowUpOf P u) Q) := hloc'.2.1
    have hd : ringKrullDim (homLocRing (blowUpOf P u) Q) = 1 := hloc'.2.2
    have hdivQ : divCycle (blowUpOf P u) (liftForm x) Q =
        ((multAt (blowUpOf P u ⊔ Ideal.span {liftForm x}) Q).toNat : ℤ) := by
      unfold divCycle
      rw [dif_pos ⟨hQmin, hQrel⟩]
    have : Ring.KrullDimLE 1 (homLocRing (blowUpOf P u) Q) := by
      rw [Ring.krullDimLE_iff, hd]
      rfl
    have hfinl : Module.length (homLocRing (blowUpOf P u) Q)
        (homLocRing (blowUpOf P u) Q ⧸ Ideal.span {(⟨_, hz'⟩ : homLocRing (blowUpOf P u) Q)}) ≠ ⊤ :=
      Module.length_ne_top_iff.mpr
        (isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_of_ne_zero hz0))
    rw [hdivQ, Int.toNat_natCast, hmult, ENat.natCast_toNat hfinl]

  let _ := (Subring.inclusion h).toAlgebra
  have := 𝔫.2.isPrime
  have := hloc
  let ψ₁ : Localization.AtPrime 𝔫.1 ≃ₐ[blowUpOverLoc P W u] blowUpLocRing P u Q :=
    IsLocalization.algEquiv 𝔫.1.primeCompl _ _
  let ψ : Localization.AtPrime 𝔫.1 ≃+* homLocRing (blowUpOf P u) Q := ψ₁.toRingEquiv.trans φ.symm
  have hψ : ψ (algebraMap (blowUpOverLoc P W u) (Localization.AtPrime 𝔫.1)
      (algebraMap (homLocRing P W) (blowUpOverLoc P W u) ⟨_, hz⟩)) = ⟨_, hz'⟩ := by
    apply φ.injective
    simp only [ψ, RingEquiv.trans_apply, RingEquiv.apply_symm_apply, AlgEquiv.coe_ringEquiv,
      AlgEquiv.commutes]
    apply Subtype.ext
    rw [hφ (liftMDeg c) _ _ hxl hgl hgQ, blowUpEval_liftForm, blowUpEval_liftForm]
    rfl
  rw [length_quot_span_ringEquiv ψ, hψ]
  exact hlen

end

end GroundTheory.Heights₂.Heights.NumbersDVR

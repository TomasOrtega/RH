import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocPointLoc
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpLocRingIso
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingIsLocal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingMem
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

/- English proof (translation)
Rewrite using `[Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]`. Introduce `h`. Apply `hFb` to reduce the goal to its premises. Use `show F ∈ RingHom.ker (aeval (blowUpSubst P u))`. Rewrite using `[RingHom.mem_ker]`.

Use `show aeval (blowUpSubst P u) F = 0`. Rewrite using `[aeval_blowUpSubst_of_isMultiHomog P u hF, h, map_zero, zero_mul]`.
-/
theorem blowUpEval_ne_zero_of_not_mem {K : Type} [DecidableEq K] {ι : K → Type} {J : Type} {O : Type u}
    [CommRing O] {P : Ideal (MRing ι O)} [P.IsPrime] {u : J → MRing ι O} {F : MRing (extIdx ι J) O}
    {b : Option K → ℕ} (hF : IsMultiHomog F b) (hFb : F ∉ blowUpOf P u) :
    algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  intro h
  apply hFb
  show F ∈ RingHom.ker (aeval (blowUpSubst P u))
  rw [RingHom.mem_ker]
  show aeval (blowUpSubst P u) F = 0
  rw [aeval_blowUpSubst_of_isMultiHomog P u hF, h, map_zero, zero_mul]

/- English proof (translation)
Rewrite using `[← mul_assoc, div_mul_div_comm, mul_comm a b, mul_div_mul_left _ _ hb]`.
-/
theorem div_mul_div_mul_cancel_of_ne_zero {F : Type*} [Field F] (a b c w : F) (hb : b ≠ 0) :
    a / b * (b / c * w) = a / c * w := by
  rw [← mul_assoc, div_mul_div_comm, mul_comm a b, mul_div_mul_left _ _ hb]

/- English proof (translation)
Introduce `O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel`. Use `hP.multiProj.isPrime` as an intermediate fact. Introduce `W' hW'p hmh hW'rel hbl hW'W`. Establish `hBR : blowUpOverLoc P W u ≤ blowUpLocRing P u W'` using `iInf₂_le W' ⟨hW'p, hmh, hW'rel, hbl, hW'W.le⟩`. Establish `: (blowUpOf P u).IsPrime` using `RingHom.ker_isPrime _`.

Take `⟨φ, hφ⟩` from `BlowUpLocRingIso.proof O K ι J P u W' hbl`. Take `⟨hlocT, hunitT⟩` from `HomLocRingIsLocal.proof HomLocRingMem.proof O (Option K) (extIdx ι J) (blowUpOf P u) W' hW'p hbl`. Establish `: IsLocalRing (blowUpLocRing P u W')` using `φ.isLocalRing`. Establish `hPW : P ≤ W` using `le_sup_left.trans hWmin.1.2`. Establish `hWp : W.IsPrime` using `hWmin.1.1`.

Take `⟨hlocA, hunitA⟩` from `HomLocRingIsLocal.proof HomLocRingMem.proof O K ι P W hWp hPW`. Set `𝔫 : Ideal (blowUpOverLoc P W u)` to `(IsLocalRing.maximalIdeal (blowUpLocRing P u W')).comap (Subring.inclusion hBR)`. Establish `hcomapA : (𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u))).IsMaximal`. Establish `hle : IsLocalRing.maximalIdeal (homLocRing P W) ≤ 𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u))`. Introduce and unpack `⟨z, hz⟩ ha`.

Rewrite `ha` using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Take `⟨b, f, g, hf, hg, hgW, rfl⟩` from `(HomLocRingMem.proof O K ι P W hWp hPW z).mp hz`. Establish `hfW : f ∈ W`. Assume the negation of the conclusion as `hfW`. Conclude with `ha ((hunitA b f g hf hg hgW hz).mpr hfW)`.

Establish `hgW' : liftForm (J` using `J) g ∉ W' := fun h => hgW (by rw [← hW'W]; exact h)`. Establish `hfW' : liftForm (J` using `J) f ∈ W' := by rw [← hW'W] at hfW; exact hfW`. Establish `hlf` using `isMultiHomog_liftForm (J := J) hf`. Establish `hlg` using `isMultiHomog_liftForm (J := J) hg`. Establish `hz' : algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u) (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm f)) / algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u) (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm g) …` using `Subring.subset_closure ⟨liftMDeg b, _, _, hlf, hlg, hgW', rfl⟩`.

Establish `hnu : ¬ IsUnit (⟨_, hz'⟩ : homLocRing (blowUpOf P u) W')` using `fun h => (hunitT _ _ _ hlf hlg hgW' hz').mp h hfW'`. Establish `hφz : Subring.inclusion hBR (algebraMap (homLocRing P W) (blowUpOverLoc P W u) ⟨_, hz⟩) = φ ⟨_, hz'⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hφ _ _ _ hlf hlg hgW', blowUpEval_liftForm, blowUpEval_liftForm]`. Both sides reduce to the same expression.

Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, hφz, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]`. Conclude with `hnu`. Establish `hne : 𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u)) ≠ ⊤` using `Ideal.comap_ne_top _ (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top)`. Rewrite using `[le_antisymm (IsLocalRing.le_maximalIdeal hne) hle]`. Use `infer_instance`.

Take `⟨hfinite, -⟩` from `hfin O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel`. Establish `h𝔫 : 𝔫.IsMaximal` using `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap 𝔫 hcomapA`. Use `⟨hBR, 𝔫, h𝔫, ?_⟩` and prove the remaining obligations. Take `⟨W₁, hW₁p, hW₁h, hW₁r, hW₁b, -, h₁, hl₁⟩` from `hcen O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel 𝔫 h𝔫`. Set `_` to `(Subring.inclusion h₁).toAlgebra`.

Use `h𝔫.isPrime` as an intermediate fact. Establish `hl : IsLocalization.AtPrime (blowUpLocRing P u W₁) 𝔫` using `hl₁`. Establish `hunitB : ∀ s : blowUpOverLoc P W u, s ∉ 𝔫 → IsUnit (Subring.inclusion hBR s)`. Introduce `s hs`. Assume the negation of the conclusion as `h`.

Conclude with `hs ((IsLocalRing.mem_maximalIdeal _).mpr h)`. Establish `h3 : blowUpLocRing P u W₁ ≤ blowUpLocRing P u W'`. Introduce `z hz`. Take `⟨⟨b, s⟩, hbs⟩` from `IsLocalization.surj 𝔫.primeCompl (⟨z, hz⟩ : blowUpLocRing P u W₁)`. Take `⟨t, ht⟩` from `(hunitB s s.2).exists_right_inv`.

Establish `e₁ : z * ((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) = ((b : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P))` using `congrArg Subtype.val hbs`. Establish `e₂ : ((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) * (t : FractionRing (MRing ι O ⧸ P)) = 1` using `congrArg Subtype.val ht`. Establish `hzt : z = ((b : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) * t`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hzt]`.

Conclude with `(blowUpLocRing P u W').mul_mem (hBR b.2) t.2`. Establish `hdom : ∀ (y : FractionRing (MRing ι O ⧸ P)) (hy₁ : y ∈ blowUpLocRing P u W₁) (hy' : y ∈ blowUpLocRing P u W'), IsUnit (⟨y, hy'⟩ : blowUpLocRing P u W') → IsUnit (⟨y, hy₁⟩ : blowUpLocRing P u W₁)`. Introduce `y hy₁ hy' hyu`. Take `⟨⟨b, s⟩, hbs⟩` from `IsLocalization.surj 𝔫.primeCompl (⟨y, hy₁⟩ : blowUpLocRing P u W₁)`. Establish `e₁ : y * ((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) = ((b : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P))` using `congrArg Subtype.val hbs`.

Establish `hb : b ∉ 𝔫`. Introduce `hb`. Establish `hb' : Subring.inclusion hBR b ∈ IsLocalRing.maximalIdeal (blowUpLocRing P u W')` using `hb`. Apply `(IsLocalRing.mem_maximalIdeal _).mp hb'` to reduce the goal to its premises. Establish `hprod : Subring.inclusion hBR b = (⟨y, hy'⟩ : blowUpLocRing P u W') * Subring.inclusion hBR s` using `Subtype.ext e₁.symm`.

Rewrite using `[hprod]`. Conclude with `hyu.mul (hunitB s s.2)`. Establish `hbu : IsUnit (algebraMap (blowUpOverLoc P W u) (blowUpLocRing P u W₁) b)` using `IsLocalization.map_units (M := 𝔫.primeCompl) _ (⟨b, hb⟩ : 𝔫.primeCompl)`. Rewrite `hbu` using `[← hbs]`. Conclude with `isUnit_of_mul_isUnit_left hbu`.

Establish `h5 : blowUpLocRing P u W' ≤ blowUpLocRing P u W₁`. Use `Subring.closure_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `z ⟨d, F, G, hF, hG, hGW', rfl⟩`. Take `⟨i, hi⟩` from `powMonomial_not_mem hW₁p hW₁r d`. Establish `hH` using `isMultiHomog_powMonomial (R := O) d i`.

Establish `hσH : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) ≠ 0` using `blowUpEval_ne_zero_of_not_mem hH (fun h => hi (hW₁b h))`. Establish `hσG : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) ≠ 0` using `blowUpEval_ne_zero_of_not_mem hG (fun h => hGW' (hbl h))`. Establish `hy₁ : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) ∈ blowUpLocRing P u W₁` using `Subring.subset_closure ⟨d, G, _, hG, hH, hi, rfl⟩`. Establish `hFH : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) ∈ blowUpLocRing P u W₁` using `Subring.subset_closure ⟨d, F, _, hF, hH, hi, rfl⟩`. Establish `hinv : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) ∈ blowUpLocRing P u W'` using `Subring.subset_closure ⟨d, _, G, hH, hG, hGW', rfl⟩`.

Establish `hyu : IsUnit (⟨_, h3 hy₁⟩ : blowUpLocRing P u W')`. Use `IsUnit.of_mul_eq_one (⟨_, hinv⟩ : blowUpLocRing P u W') (Subtype.ext ?_)` and prove the remaining obligations. Use `show algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) * (algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) / algeb …`. Clear the denominators using the available nonvanishing facts. Take `⟨v, hv⟩` from `hdom _ hy₁ (h3 hy₁) hyu`.

Establish `e : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) * (((v⁻¹ : (blowUpLocRing P u W₁)ˣ) : blowUpLocRing P u W₁) : FractionRing (MRing ι O ⧸ P)) = 1`. Use `congrArg Subtype.val v.mul_inv` as an intermediate fact. Rewrite `this` using `[hv]`. Conclude with `this`. Establish `hz : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) = algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRi …`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hz]`. Conclude with `(blowUpLocRing P u W₁).mul_mem hFH (Subtype.property _)`. Establish `heq : W₁ = W'` using `hinj O K ι J P u W₁ W' hW₁p hW₁h hW₁r hW₁b hW'p hmh hW'rel hbl (le_antisymm h3 h5)`. Substitute `heq` using the available equality.

Conclude with `hl`.
-/
theorem BlowUpOverLocPointLoc.proof (hfin : BlowUpOverLocFinite.Statement.{u})
    (hcen : BlowUpOverLocMaxCentre.Statement.{u}) (hinj : BlowUpLocRingInj.Statement.{u}) :
    BlowUpOverLocPointLoc.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have := hP.multiProj.isPrime
  intro W' hW'p hmh hW'rel hbl hW'W
  have hBR : blowUpOverLoc P W u ≤ blowUpLocRing P u W' :=
    iInf₂_le W' ⟨hW'p, hmh, hW'rel, hbl, hW'W.le⟩
  have : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  obtain ⟨φ, hφ⟩ := BlowUpLocRingIso.proof O K ι J P u W' hbl
  obtain ⟨hlocT, hunitT⟩ :=
    HomLocRingIsLocal.proof HomLocRingMem.proof O (Option K) (extIdx ι J) (blowUpOf P u) W' hW'p hbl
  have : IsLocalRing (blowUpLocRing P u W') := φ.isLocalRing
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  have hWp : W.IsPrime := hWmin.1.1
  obtain ⟨hlocA, hunitA⟩ := HomLocRingIsLocal.proof HomLocRingMem.proof O K ι P W hWp hPW
  let 𝔫 : Ideal (blowUpOverLoc P W u) :=
    (IsLocalRing.maximalIdeal (blowUpLocRing P u W')).comap (Subring.inclusion hBR)

  have hcomapA : (𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u))).IsMaximal := by
    have hle : IsLocalRing.maximalIdeal (homLocRing P W) ≤
        𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u)) := by
      rintro ⟨z, hz⟩ ha
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha
      obtain ⟨b, f, g, hf, hg, hgW, rfl⟩ := (HomLocRingMem.proof O K ι P W hWp hPW z).mp hz
      have hfW : f ∈ W := by
        by_contra hfW
        exact ha ((hunitA b f g hf hg hgW hz).mpr hfW)
      have hgW' : liftForm (J := J) g ∉ W' := fun h => hgW (by rw [← hW'W]; exact h)
      have hfW' : liftForm (J := J) f ∈ W' := by rw [← hW'W] at hfW; exact hfW
      have hlf := isMultiHomog_liftForm (J := J) hf
      have hlg := isMultiHomog_liftForm (J := J) hg
      have hz' : algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
            (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm f)) /
          algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
            (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm g)) ∈
          homLocRing (blowUpOf P u) W' :=
        Subring.subset_closure ⟨liftMDeg b, _, _, hlf, hlg, hgW', rfl⟩
      have hnu : ¬ IsUnit (⟨_, hz'⟩ : homLocRing (blowUpOf P u) W') :=
        fun h => (hunitT _ _ _ hlf hlg hgW' hz').mp h hfW'
      have hφz : Subring.inclusion hBR (algebraMap (homLocRing P W) (blowUpOverLoc P W u) ⟨_, hz⟩) =
          φ ⟨_, hz'⟩ := by
        apply Subtype.ext
        rw [hφ _ _ _ hlf hlg hgW', blowUpEval_liftForm, blowUpEval_liftForm]
        rfl
      rw [Ideal.mem_comap, Ideal.mem_comap, hφz, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        isUnit_map_iff]
      exact hnu
    have hne : 𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u)) ≠ ⊤ :=
      Ideal.comap_ne_top _ (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top)
    rw [le_antisymm (IsLocalRing.le_maximalIdeal hne) hle]
    infer_instance
  obtain ⟨hfinite, -⟩ := hfin O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have h𝔫 : 𝔫.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap 𝔫 hcomapA
  refine ⟨hBR, 𝔫, h𝔫, ?_⟩

  obtain ⟨W₁, hW₁p, hW₁h, hW₁r, hW₁b, -, h₁, hl₁⟩ :=
    hcen O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel 𝔫 h𝔫
  let _ := (Subring.inclusion h₁).toAlgebra
  have := h𝔫.isPrime
  have hl : IsLocalization.AtPrime (blowUpLocRing P u W₁) 𝔫 := hl₁

  have hunitB : ∀ s : blowUpOverLoc P W u, s ∉ 𝔫 → IsUnit (Subring.inclusion hBR s) := by
    intro s hs
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).mpr h)

  have h3 : blowUpLocRing P u W₁ ≤ blowUpLocRing P u W' := by
    intro z hz
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj 𝔫.primeCompl (⟨z, hz⟩ : blowUpLocRing P u W₁)
    obtain ⟨t, ht⟩ := (hunitB s s.2).exists_right_inv
    have e₁ : z * ((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) = ((b : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) :=
      congrArg Subtype.val hbs
    have e₂ : ((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) * (t : FractionRing (MRing ι O ⧸ P)) = 1 := congrArg Subtype.val ht
    have hzt : z = ((b : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) * t := by
      calc z = z * (((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) * t) := by rw [e₂, mul_one]
        _ = (z * ((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P))) * t := by ring
        _ = ((b : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) * t := by rw [e₁]
    rw [hzt]
    exact (blowUpLocRing P u W').mul_mem (hBR b.2) t.2

  have hdom : ∀ (y : FractionRing (MRing ι O ⧸ P)) (hy₁ : y ∈ blowUpLocRing P u W₁) (hy' : y ∈ blowUpLocRing P u W'),
      IsUnit (⟨y, hy'⟩ : blowUpLocRing P u W') → IsUnit (⟨y, hy₁⟩ : blowUpLocRing P u W₁) := by
    intro y hy₁ hy' hyu
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj 𝔫.primeCompl (⟨y, hy₁⟩ : blowUpLocRing P u W₁)
    have e₁ : y * ((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) = ((b : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) :=
      congrArg Subtype.val hbs
    have hb : b ∉ 𝔫 := by
      intro hb
      have hb' : Subring.inclusion hBR b ∈ IsLocalRing.maximalIdeal (blowUpLocRing P u W') := hb
      apply (IsLocalRing.mem_maximalIdeal _).mp hb'
      have hprod : Subring.inclusion hBR b = (⟨y, hy'⟩ : blowUpLocRing P u W') * Subring.inclusion hBR s :=
        Subtype.ext e₁.symm
      rw [hprod]
      exact hyu.mul (hunitB s s.2)
    have hbu : IsUnit (algebraMap (blowUpOverLoc P W u) (blowUpLocRing P u W₁) b) :=
      IsLocalization.map_units (M := 𝔫.primeCompl) _ (⟨b, hb⟩ : 𝔫.primeCompl)
    rw [← hbs] at hbu
    exact isUnit_of_mul_isUnit_left hbu

  have h5 : blowUpLocRing P u W' ≤ blowUpLocRing P u W₁ := by
    refine Subring.closure_le.mpr ?_
    rintro z ⟨d, F, G, hF, hG, hGW', rfl⟩
    obtain ⟨i, hi⟩ := powMonomial_not_mem hW₁p hW₁r d
    have hH := isMultiHomog_powMonomial (R := O) d i
    have hσH : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) ≠ 0 :=
      blowUpEval_ne_zero_of_not_mem hH (fun h => hi (hW₁b h))
    have hσG : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) ≠ 0 := blowUpEval_ne_zero_of_not_mem hG (fun h => hGW' (hbl h))
    have hy₁ : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) ∈ blowUpLocRing P u W₁ :=
      Subring.subset_closure ⟨d, G, _, hG, hH, hi, rfl⟩
    have hFH : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) ∈ blowUpLocRing P u W₁ :=
      Subring.subset_closure ⟨d, F, _, hF, hH, hi, rfl⟩
    have hinv : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) ∈ blowUpLocRing P u W' :=
      Subring.subset_closure ⟨d, _, G, hH, hG, hGW', rfl⟩
    have hyu : IsUnit (⟨_, h3 hy₁⟩ : blowUpLocRing P u W') := by
      refine IsUnit.of_mul_eq_one (⟨_, hinv⟩ : blowUpLocRing P u W') (Subtype.ext ?_)
      show algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) * (algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G)) = 1
      field_simp
    obtain ⟨v, hv⟩ := hdom _ hy₁ (h3 hy₁) hyu
    have e : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) *
        (((v⁻¹ : (blowUpLocRing P u W₁)ˣ) : blowUpLocRing P u W₁) : FractionRing (MRing ι O ⧸ P)) = 1 := by
      have := congrArg Subtype.val v.mul_inv
      rw [hv] at this
      exact this
    have hz : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) = algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) *
        (((v⁻¹ : (blowUpLocRing P u W₁)ˣ) : blowUpLocRing P u W₁) : FractionRing (MRing ι O ⧸ P)) := by
      calc algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G)
          = algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) * (algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) *
            (((v⁻¹ : (blowUpLocRing P u W₁)ˣ) : blowUpLocRing P u W₁) : FractionRing (MRing ι O ⧸ P))) := by rw [e, mul_one]
        _ = algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) *
            (((v⁻¹ : (blowUpLocRing P u W₁)ˣ) : blowUpLocRing P u W₁) : FractionRing (MRing ι O ⧸ P)) :=
          div_mul_div_mul_cancel_of_ne_zero _ _ _ _ hσG
    rw [hz]
    exact (blowUpLocRing P u W₁).mul_mem hFH (Subtype.property _)
  have heq : W₁ = W' :=
    hinj O K ι J P u W₁ W' hW₁p hW₁h hW₁r hW₁b hW'p hmh hW'rel hbl (le_antisymm h3 h5)
  subst heq
  exact hl

end

end GroundTheory.Heights₂.Heights.NumbersDVR

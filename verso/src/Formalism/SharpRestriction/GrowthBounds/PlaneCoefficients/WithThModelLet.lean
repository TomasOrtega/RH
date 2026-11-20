import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.WordLossNonneg

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

def withTh {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} (Dt : SignedChainData p O r J)
    (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ) (h : ∀ j (m : Fin r), m.val + 2 ≤ r → 0 < thL j m) :
    SignedChainData p O r J :=
  SignedChainData.mk Dt.nL Dt.sgn Dt.d Dt.gP Dt.nch Dt.chain Dt.chain_mono Dt.chain_w th Dt.sl thL h Dt.ga Dt.ga_unit Dt.ga_dig
    Dt.c Dt.one_le_c

section With

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} (Dt : SignedChainData p O r J)
    (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ) (h : ∀ j (m : Fin r), m.val + 2 ≤ r → 0 < thL j m)

/- English proof (translation)
Unfold `SignedChainData.modelLet withTh`. Use `congr 1`. Use function extensionality and compare the values at `x`. Apply the tactic sequence `cases x <;> rfl`.
-/
theorem withTh_modelLet : (withTh Dt th thL h).modelLet = Dt.modelLet := by
  unfold SignedChainData.modelLet withTh
  congr 1
  funext x
  cases x <;> rfl

/- English proof (translation)
Unfold `SignedChainData.trueLet withTh`. Use `congr 1`. Use function extensionality and compare the values at `x`. Apply the tactic sequence `obtain ⟨j, l | m⟩ := x <;> rfl`.
-/
theorem withTh_trueLet : (withTh Dt th thL h).trueLet = Dt.trueLet := by
  unfold SignedChainData.trueLet withTh
  congr 1
  funext x
  obtain ⟨j, l | m⟩ := x <;> rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Apply the tactic sequence `cases x <;> rfl`.
-/
theorem withTh_levToML (j) : (withTh Dt th thL h).levToML j = Dt.levToML j := by
  funext x
  cases x <;> rfl

/- English proof (translation)
Unfold `SignedChainData.chainML`. Rewrite using `[withTh_levToML]`. Both sides reduce to the same expression.
-/
theorem withTh_chainML (j i) : (withTh Dt th thL h).chainML j i = Dt.chainML j i := by
  unfold SignedChainData.chainML
  rw [withTh_levToML]
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem withTh_TSet (j i) : (withTh Dt th thL h).TSet j i = Dt.TSet j i := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem withTh_digOK (rho) : (withTh Dt th thL h).digOK rho = Dt.digOK rho := rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Apply the tactic sequence `obtain ⟨⟨j, l | m⟩, a⟩ := x <;> rfl`.
-/
theorem withTh_liftVar : (withTh Dt th thL h).liftVar = Dt.liftVar := by
  funext x
  obtain ⟨⟨j, l | m⟩, a⟩ := x <;> rfl

/- English proof (translation)
Use function extensionality and compare the values at `mo x`. Apply the tactic sequence `obtain ⟨⟨j, l | m⟩, a⟩ := x <;> rfl`.
-/
theorem withTh_liftExp : (withTh Dt th thL h).liftExp = Dt.liftExp := by
  funext mo x
  obtain ⟨⟨j, l | m⟩, a⟩ := x <;> rfl

/- English proof (translation)
Simplify using `only [SignedChainData.Fdig, withTh_digOK, withTh_liftVar, withTh_liftExp]`. Both sides reduce to the same expression.
-/
theorem withTh_Fdig (rho F) : (withTh Dt th thL h).Fdig rho F = Dt.Fdig rho F := by
  simp only [SignedChainData.Fdig, withTh_digOK, withTh_liftVar, withTh_liftExp]
  rfl

/- English proof (translation)
Unfold `normE`. Rewrite using `[withTh_trueLet]`. Both sides reduce to the same expression.
-/
theorem withTh_normE (K : ℕ) [NeZero K] [NeZero J] : normE p K (withTh Dt th thL h) = normE p K Dt := by
  unfold normE
  rw [withTh_trueLet]
  rfl

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hF`. Use `⟨h1, fun rho j i => ?_, fun j m hm => ?_⟩` and prove the remaining obligations. Establish `hx` using `h2 rho j i erw [withTh_modelLet, withTh_chainML, withTh_Fdig] at hx`. Conclude with `geZ_anti (hth j i) hx`. Establish `hx` using `h3 j m hm erw [withTh_trueLet, withTh_TSet] at hx`.

Conclude with `geZ_anti (hthL j m hm) hx`.
-/
theorem XX_withTh [NeZero J] [NeZero r] (hth : ∀ j i, Dt.th j i ≤ th j i)
    (hthL : ∀ j (m : Fin r), m.val + 2 ≤ r → Dt.thL j m ≤ thL j m)
    (F : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) (hF : (withTh Dt th thL h).XX F) : Dt.XX F := by
  obtain ⟨h1, h2, h3⟩ := hF
  refine ⟨h1, fun rho j i => ?_, fun j m hm => ?_⟩
  · have hx := h2 rho j i
    erw [withTh_modelLet, withTh_chainML, withTh_Fdig] at hx
    exact geZ_anti (hth j i) hx
  · have hx := h3 j m hm
    erw [withTh_trueLet, withTh_TSet] at hx
    exact geZ_anti (hthL j m hm) hx

end With

/- English proof (translation)
Introduce `sc sL p n' r K m _ _ _ O _ _ _ hk Fr deg Y N₁ G' cP F hG J _ Dt dPl dNo ka hT rho e he nu`. Take `⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩` from `hT`. Set `th : ∀ j, Fin (Dt.nch j) → ℝ` to `fun j i => thStar Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) Dt.nL K ka j (i : ℕ) - sc * slU Fr p deg Y (r + K) Dt.nL j (i : ℕ)`. Set `thL : ZMod J → Fin r → ℝ` to `fun j mm => thStar Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) Dt.nL K ka j (Dt.nL j + (r - 1 - (mm : ℕ))) - sL * slU Fr p deg Y (r + K) Dt.nL j (Dt.nL j + (r - 1 - (mm : ℕ)))`. Establish `hpos : ∀ j (mm : Fin r), mm.val + 2 ≤ r → 0 < thL j mm`.

Introduce `j mm hmm`. Establish `a` using `Dt.thL_pos j mm hmm`. Establish `b` using `t9 j mm hmm`. Simplify using `only [sub_zero] at b`. Conclude with `lt_of_lt_of_le a b`.

Establish `hT' : TwistedSubstitutionGrowthBound Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) K sc sL (withTh Dt th thL hpos) dPl ka` using `⟨t1, t2, t3, t4, t5, t6, t7, fun j i => rfl, fun j mm _ => rfl⟩`. Establish `hX` using `hG J (withTh Dt th thL hpos) dPl dNo ka hT' rho e (by rw [withTh_normE]; exact he) nu`. Use `XX_withTh Dt th thL hpos (fun j i => ?_) (fun j mm hmm => ?_) _ hX` and prove the remaining obligations. Establish `b` using `t8 j i`. Simplify using `only [sub_zero] at b`.

Conclude with `b`. Establish `b` using `t9 j mm hmm`. Simplify using `only [sub_zero] at b`. Conclude with `b`.
-/
theorem restLeOfG : RestLeOfG := by
  intro sc sL p n' r K m _ _ _ O _ _ _ hk Fr deg Y N₁ G' cP F hG J _ Dt dPl dNo ka hT rho e he nu
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := hT
  let th : ∀ j, Fin (Dt.nch j) → ℝ := fun j i =>
    thStar Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) Dt.nL K ka j (i : ℕ) -
      sc * slU Fr p deg Y (r + K) Dt.nL j (i : ℕ)
  let thL : ZMod J → Fin r → ℝ := fun j mm =>
    thStar Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) Dt.nL K ka j (Dt.nL j + (r - 1 - (mm : ℕ))) -
      sL * slU Fr p deg Y (r + K) Dt.nL j (Dt.nL j + (r - 1 - (mm : ℕ)))
  have hpos : ∀ j (mm : Fin r), mm.val + 2 ≤ r → 0 < thL j mm := by
    intro j mm hmm
    have a := Dt.thL_pos j mm hmm
    have b := t9 j mm hmm
    simp only [sub_zero] at b
    exact lt_of_lt_of_le a b
  have hT' : TwistedSubstitutionGrowthBound Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) K sc sL
      (withTh Dt th thL hpos) dPl ka :=
    ⟨t1, t2, t3, t4, t5, t6, t7, fun j i => rfl, fun j mm _ => rfl⟩
  have hX := hG J (withTh Dt th thL hpos) dPl dNo ka hT' rho e (by rw [withTh_normE]; exact he) nu
  refine XX_withTh Dt th thL hpos (fun j i => ?_) (fun j mm hmm => ?_) _ hX
  · have b := t8 j i
    simp only [sub_zero] at b
    exact b
  · have b := t9 j mm hmm
    simp only [sub_zero] at b
    exact b

end Formalism.MainNotions.PairMembershipBlocks

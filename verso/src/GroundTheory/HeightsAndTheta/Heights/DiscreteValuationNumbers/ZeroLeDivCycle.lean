import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LocalizedQuotientIsSimpleModuleOfMul
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleFiniteSupport
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

/- English proof (translation)
Unfold `divCycle`. Apply the tactic sequence `split_ifs <;> positivity`.
-/
theorem zero_le_divCycle {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R] (P : Ideal (MRing ι R))
    (f : MRing ι R) (W : Ideal (MRing ι R)) : 0 ≤ divCycle P f W := by
  unfold divCycle
  split_ifs <;> positivity

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH hcommon`. Use `set N := commonExcess ϖ P f g s with hN`. Establish `hε : 0 < N` using `hpos O ϖ hϖ K ι P d hP b f g hD s hsP hcommon`. Establish `hbdd : BddAbove (Set.range fun G : {G : Ideal (MRing ι O) // (C ϖ : MRing ι O) ∈ G} => (divCycle P s G.1 * ratDiv P f g G.1).toNat)`. Use `(((DivCycleFiniteSupport.proof O K ι P s).image fun G => (divCycle P s G * ratDiv P f g G).toNat).insert 0).bddAbove.mono ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨G, rfl⟩`. Distinguish the cases in `h : divCycle P s G.1 = 0`. Use `left`. Simplify using `[h]`. Use `right`.

Conclude with `⟨G.1, h, rfl⟩`. Establish `hle : ∀ G, (C ϖ : MRing ι O) ∈ G → ∀ x y : ℤ, 0 ≤ x → 0 ≤ y → x ≤ divCycle P s G → y ≤ ratDiv P f g G → x * y ≤ N`. Introduce `G hG x y hx hy hxG hyG`. Establish `h1 : (divCycle P s G * ratDiv P f g G).toNat ≤ N` using `le_ciSup hbdd ⟨G, hG⟩`. Establish `h2 : x * y ≤ divCycle P s G * ratDiv P f g G` using `mul_le_mul hxG hyG hy (hx.trans hxG)`.

Conclude with `h2.trans ((Int.self_le_toNat _).trans (by exact_mod_cast h1))`. Establish `hterm : ∀ x y : ℤ, 0 ≤ x → (0 < x → 0 < y → x * y < N) → (x * y).toNat ≤ N - 1`. Introduce `x y hx h`. Break down `lt_or_ge 0 x with hx' | hx'` into its components or cases. Break down `lt_or_ge 0 y with hy | hy` into its components or cases.

Establish `h1` using `h hx' hy`. Generalize the expression as in `x * y = p at h1 ⊢`. Use linear arithmetic over natural numbers and integers. Establish `h1 : x * y ≤ 0` using `mul_nonpos_of_nonneg_of_nonpos hx hy`. Generalize the expression as in `x * y = p at h1 ⊢`.

Use linear arithmetic over natural numbers and integers. Take `rfl : x = 0` from `le_antisymm hx' hx`. Simplify using the standard rewrite rules. Establish `hne : Nonempty {G' : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O) // (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G'}` using `⟨⟨⊤, Submodule.mem_top⟩⟩`. Prove the components needed by the constructor for the conclusion.

Establish `h : commonExcess ϖ (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m) (liftForm s) ≤ N - 1`. Use `ciSup_le fun G' => hterm _ _ (zero_le_divCycle _ _ _) fun hx hy => ?_` and prove the remaining obligations. Take `⟨G, hG, h1, h2⟩` from `hres O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G'.1 G'.2 hx hy`. Establish `h3` using `hle G hG _ _ hx.le (by linarith) h1 h2`. Use the polynomial consequences of the given equalities and inequalities.

Use linear arithmetic over natural numbers and integers. Establish `h : commonExcess ϖ (blowUpOf P (blowUpGens s g f m e)) (liftForm (f * m)) (liftForm g * newVar (some none)) (newVar none) ≤ N - 1`. Use `ciSup_le fun G' => hterm _ _ (zero_le_divCycle _ _ _) fun hx hy => ?_` and prove the remaining obligations. Take `⟨G, hG, h1, h2⟩` from `hexc O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G'.1 G'.2 hx hy`. Establish `h3` using `hle G hG _ _ (by linarith) hy.le h1 h2`.

Use the polynomial consequences of the given equalities and inequalities. Use linear arithmetic over natural numbers and integers.
-/
theorem BlowUpExcessDecreases.proof (hpos : ExcessPositive.Statement.{u})
    (hres : ResidualComparison.Statement.{u}) (hexc : ExceptionalComparison.Statement.{u}) :
    BlowUpExcessDecreases.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH hcommon
  set N := commonExcess ϖ P f g s with hN
  have hε : 0 < N := hpos O ϖ hϖ K ι P d hP b f g hD s hsP hcommon

  have hbdd : BddAbove (Set.range fun G : {G : Ideal (MRing ι O) // (C ϖ : MRing ι O) ∈ G} =>
      (divCycle P s G.1 * ratDiv P f g G.1).toNat) := by
    refine (((DivCycleFiniteSupport.proof O K ι P s).image
      fun G => (divCycle P s G * ratDiv P f g G).toNat).insert 0).bddAbove.mono ?_
    rintro _ ⟨G, rfl⟩
    by_cases h : divCycle P s G.1 = 0
    · left; simp [h]
    · right; exact ⟨G.1, h, rfl⟩
  have hle : ∀ G, (C ϖ : MRing ι O) ∈ G → ∀ x y : ℤ, 0 ≤ x → 0 ≤ y → x ≤ divCycle P s G →
      y ≤ ratDiv P f g G → x * y ≤ N := by
    intro G hG x y hx hy hxG hyG
    have h1 : (divCycle P s G * ratDiv P f g G).toNat ≤ N := le_ciSup hbdd ⟨G, hG⟩
    have h2 : x * y ≤ divCycle P s G * ratDiv P f g G := mul_le_mul hxG hyG hy (hx.trans hxG)
    exact h2.trans ((Int.self_le_toNat _).trans (by exact_mod_cast h1))

  have hterm : ∀ x y : ℤ, 0 ≤ x → (0 < x → 0 < y → x * y < N) → (x * y).toNat ≤ N - 1 := by
    intro x y hx h
    rcases lt_or_ge 0 x with hx' | hx'
    · rcases lt_or_ge 0 y with hy | hy
      · have h1 := h hx' hy
        generalize x * y = p at h1 ⊢
        omega
      · have h1 : x * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx hy
        generalize x * y = p at h1 ⊢
        omega
    · obtain rfl : x = 0 := le_antisymm hx' hx
      simp
  have hne : Nonempty {G' : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O) //
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G'} := ⟨⟨⊤, Submodule.mem_top⟩⟩
  constructor
  ·
    have h : commonExcess ϖ (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m)
        (liftForm s) ≤ N - 1 := by
      refine ciSup_le fun G' => hterm _ _ (zero_le_divCycle _ _ _) fun hx hy => ?_
      obtain ⟨G, hG, h1, h2⟩ :=
        hres O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G'.1 G'.2 hx hy
      have h3 := hle G hG _ _ hx.le (by linarith) h1 h2
      nlinarith
    omega
  ·
    have h : commonExcess ϖ (blowUpOf P (blowUpGens s g f m e)) (liftForm (f * m))
        (liftForm g * newVar (some none)) (newVar none) ≤ N - 1 := by
      refine ciSup_le fun G' => hterm _ _ (zero_le_divCycle _ _ _) fun hx hy => ?_
      obtain ⟨G, hG, h1, h2⟩ :=
        hexc O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G'.1 G'.2 hx hy
      have h3 := hle G hG _ _ (by linarith) hy.le h1 h2
      nlinarith
    omega

end GroundTheory.Heights₂.Heights.NumbersDVR

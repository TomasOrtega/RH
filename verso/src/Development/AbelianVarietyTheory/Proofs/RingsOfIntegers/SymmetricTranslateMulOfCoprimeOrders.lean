import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueSymmetricTranslateOddLevel
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EqOfSqEqOfOdd
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalWeilPairingPullbackExistsUnique
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

/- English proof (translation)
Establish `h₁ : e ^ m = 1`. Take `⟨hex, hmul, -, -⟩` from `hW S P k T`. Take `⟨c₁, hc₁, hu⟩` from `hex 1 b (one_pow k) hb`. Establish `h₂` using `hmul 1 1 b c₁ c₁ hc₁ hc₁`. Rewrite `h₂` using `[_root_.mul_one]`.

Take `rfl : c₁ = 1` from `mul_eq_left.1 (hu _ h₂)`. Establish `hpow : ∀ j : ℕ, WeilIs P.A P.L k (a ^ j) b (e ^ j)` using `fun j => by`. Proceed by induction on `j with`. Consider the case `zero => rw [pow_zero, pow_zero]`. Conclude with `hc₁`.

Consider the case `succ j ih => rw [pow_succ, pow_succ]`. Conclude with `hmul _ _ _ _ _ ih he`. Establish `h` using `hpow m`. Rewrite `h` using `[ham]`. Conclude with `hu _ h`.

Establish `h₂ : e ^ m' = 1`. Establish `hbg : b ^ Nat.gcd k m' = 1` using `pow_gcd_eq_one.2 ⟨hb, hbm⟩`. Take `⟨n, hn⟩` from `Nat.gcd_dvd_left k m'`. Take `⟨n', hn'⟩` from `Nat.gcd_dvd_right k m'`. Generalize the expression as in `Nat.gcd k m' = g at hbg hn hn'`.

Substitute `hn` using the available equality. Establish `h` using `((hW S P g T).2.2.2 n a b e hk ha hbg).1 (by exact_mod_cast he)`. Establish `hg` using `GlobalTheory.UnivPairing.weilIs_pow_eq_one hW P g (a ^ n) b (by rw [← pow_mul, mul_comm]; exact ha) hbg e h`. Rewrite using `[hn', pow_mul, hg, one_pow]`. Establish `h` using `pow_gcd_eq_one.2 ⟨h₁, h₂⟩`.

Rewrite `h` using `[hc.gcd_eq_one, pow_one]`. Then use the resulting hypothesis.
-/
theorem weilIs_eq_one_of_coprime (hW : WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ)
    {T : Over S} (hk : IsUnit (k : Γ(T.left, ⊤))) (a b : T ⟶ P.A) (m m' : ℕ) (ha : a ^ k = 1) (hb : b ^ k = 1)
    (hc : Nat.Coprime m m') (ham : a ^ m = 1) (hbm : b ^ m' = 1) (e : Γ(T.left, ⊤)ˣ)
    (he : WeilIs P.A P.L k a b e) : e = 1 := by
  have h₁ : e ^ m = 1 := by
    obtain ⟨hex, hmul, -, -⟩ := hW S P k T
    obtain ⟨c₁, hc₁, hu⟩ := hex 1 b (one_pow k) hb
    have h₂ := hmul 1 1 b c₁ c₁ hc₁ hc₁
    rw [_root_.mul_one] at h₂
    obtain rfl : c₁ = 1 := mul_eq_left.1 (hu _ h₂)
    have hpow : ∀ j : ℕ, WeilIs P.A P.L k (a ^ j) b (e ^ j) := fun j => by
      induction j with
      | zero => rw [pow_zero, pow_zero]; exact hc₁
      | succ j ih => rw [pow_succ, pow_succ]; exact hmul _ _ _ _ _ ih he
    have h := hpow m
    rw [ham] at h
    exact hu _ h
  have h₂ : e ^ m' = 1 := by
    have hbg : b ^ Nat.gcd k m' = 1 := pow_gcd_eq_one.2 ⟨hb, hbm⟩
    obtain ⟨n, hn⟩ := Nat.gcd_dvd_left k m'
    obtain ⟨n', hn'⟩ := Nat.gcd_dvd_right k m'
    generalize Nat.gcd k m' = g at hbg hn hn'
    subst hn
    have h := ((hW S P g T).2.2.2 n a b e hk ha hbg).1 (by exact_mod_cast he)
    have hg := GlobalTheory.UnivPairing.weilIs_pow_eq_one hW P g (a ^ n) b (by rw [← pow_mul, mul_comm]; exact ha) hbg e h
    rw [hn', pow_mul, hg, one_pow]
  have h := pow_gcd_eq_one.2 ⟨h₁, h₂⟩
  rwa [hc.gcd_eq_one, pow_one] at h

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo S _ x k hk a b m m' ha hb hc ham hbm F F₁ F₂ h₁`. Establish `hW : WeilSt` using `GlobalTheory.firstFiveLaws.1.weil`. Use `UnivPol.isLocallyNoetherian Xo` as an intermediate fact. Establish `hu : IsUnit (k : Γ((ptO Xo x).left, ⊤))`. Establish `h` using `(UnivPol.isUnit_natCast Xo k hk.pos).map (ptO Xo x).hom.appTop.hom`.

Rewrite `h` using `[map_natCast]`. Then use the resulting hypothesis. Take `⟨e, he, -⟩` from `(hW Xo.X (UnivPol.pol Xo) k (ptO Xo x)).1 a b ha hb`. Establish `he1 : e = 1` using `weilIs_eq_one_of_coprime hW (UnivPol.pol Xo) k hu a b m m' ha hb hc ham hbm e he`. Take `⟨r, hr2, hrk, hr⟩` from `GlobalTheory.PlaceInt.moves_mul E H Dw l Xo S x k hk a b e ha hb he`. Establish `hr1 : toΓ S r = 1`.

Rewrite `hr2` using `[he1, Units.val_one]`. Establish `h3 : toΓ S r ^ k = 1` using `by rw [← map_pow, hrk, map_one]`. Take `⟨n, rfl⟩` from `hk`. Rewrite `h3` using `[pow_succ, pow_mul, hr2, one_pow, _root_.one_mul]`. Then use the resulting hypothesis. Establish `key : ∀ G G' : SecN Xo x k, Moves Xo a F₁ G → Moves Xo (a * b) F G' → G = G'`.

Introduce `G G' hG hG'`. Establish `h` using `hr F F₁ G G' h₁ hG hG'`. Establish `h' : G.f = G'.f` using `funext fun j => by`. Rewrite using `[h j, hr1]`. Unfold `liftFun`.

Rewrite using `[map_one, map_one, _root_.one_mul]`. Consider the cases of `G`. Consider the cases of `G'`. Consider the cases of `h'`. Both sides reduce to the same expression.

Establish `hab : (a * b) ^ k = 1` using `by rw [mul_pow, ha, hb, _root_.mul_one]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨G, hG, -⟩` from `(GlobalTheory.existsUnique_moves E H Dw l Xo S x k hk (a * b) hab F).1`. Rewrite using `[key F₂ G h hG]`.

Conclude with `hG`. Introduce `h`. Take `⟨G, hG, -⟩` from `(GlobalTheory.existsUnique_moves E H Dw l Xo S x k hk a ha F₁).1`. Rewrite using `[← key G F₂ hG h]`. Conclude with `hG`.
-/
theorem moves_mul_of_coprime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (k : ℕ), Odd k → ∀ (a b : (ptO Xo x ⟶ Xo.univ.t.G)) (m m' : ℕ), a ^ k = 1 → b ^ k = 1 → Nat.Coprime m m' → a ^ m = 1 → b ^ m' = 1 → ∀ F F₁ F₂ : SecN Xo x k, Moves Xo b F F₁ → (Moves Xo a F₁ F₂ ↔ Moves Xo (a * b) F F₂) := by
  intro E _ _ _ H Dw l Xo S _ x k hk a b m m' ha hb hc ham hbm F F₁ F₂ h₁
  have hW : WeilSt := GlobalTheory.firstFiveLaws.1.weil
  have := UnivPol.isLocallyNoetherian Xo
  have hu : IsUnit (k : Γ((ptO Xo x).left, ⊤)) := by
    have h := (UnivPol.isUnit_natCast Xo k hk.pos).map (ptO Xo x).hom.appTop.hom
    rwa [map_natCast] at h
  obtain ⟨e, he, -⟩ := (hW Xo.X (UnivPol.pol Xo) k (ptO Xo x)).1 a b ha hb
  have he1 : e = 1 := weilIs_eq_one_of_coprime hW (UnivPol.pol Xo) k hu a b m m' ha hb hc ham hbm e he
  obtain ⟨r, hr2, hrk, hr⟩ := GlobalTheory.PlaceInt.moves_mul E H Dw l Xo S x k hk a b e ha hb he
  have hr1 : toΓ S r = 1 := by
    rw [he1, Units.val_one] at hr2
    have h3 : toΓ S r ^ k = 1 := by rw [← map_pow, hrk, map_one]
    obtain ⟨n, rfl⟩ := hk
    rwa [pow_succ, pow_mul, hr2, one_pow, _root_.one_mul] at h3
  have key : ∀ G G' : SecN Xo x k, Moves Xo a F₁ G → Moves Xo (a * b) F G' → G = G' := by
    intro G G' hG hG'
    have h := hr F F₁ G G' h₁ hG hG'
    have h' : G.f = G'.f := funext fun j => by
      rw [h j, hr1]
      unfold liftFun
      rw [map_one, map_one, _root_.one_mul]
    cases G
    cases G'
    cases h'
    rfl
  have hab : (a * b) ^ k = 1 := by rw [mul_pow, ha, hb, _root_.mul_one]
  constructor
  · intro h
    obtain ⟨G, hG, -⟩ := (GlobalTheory.existsUnique_moves E H Dw l Xo S x k hk (a * b) hab F).1
    rw [key F₂ G h hG]
    exact hG
  · intro h
    obtain ⟨G, hG, -⟩ := (GlobalTheory.existsUnique_moves E H Dw l Xo S x k hk a ha F₁).1
    rw [← key G F₂ hG h]
    exact hG

end GlobalTheory.PlaceInt

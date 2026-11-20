import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPairingValuesOfFamiliesValues
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.MBLow

/- English proof (translation)
Introduce `V _ _ _ _ hV D A G _ _ hG U C _ _ _ _ _ _ hC N ν hI`. Introduce `g k hk ζ pt hζ hadd hinj hsurj hw`. Take `⟨f, hf1, hf2, hf3, hf4, hf5⟩` from `GlobalTheory.ZH.uTors_closed V hV A G D U C k hk`. Take `⟨-, -, hAdd, -, hQ⟩` from `GlobalTheory.Ex.GtValues.points_correspond V D.toPre D.psi_even D.tau_bimult C N ν`. Establish `hWp` using `GlobalTheory.WeilValues.weil_eq_values GlobalTheory.Ex.GtValues.points_correspond (GlobalTheory.Ex.brFam GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2) V D.toPre D.psi_even D.tau_bimult C N ν k hk`.

Take `⟨hQ1, hQ2, hQ3⟩` from `hQ k`. Establish `hmul : ∀ (p₁ p₂ p₃ : QkPt D.toPre C k) (q₁ q₂ : N.QT k), ν.QPt p₁ q₁ → ν.QPt p₂ q₂ → ν.QPt p₃ (q₁ * q₂) → f p₃ = f p₁ * f p₂`. Introduce `p₁ p₂ p₃ q₁ q₂ h₁ h₂ h₃`. Apply `hf4` to reduce the goal to its premises. Use `⟨p₃, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← h₃.1, ← h₁.1, ← h₂.1]`. Conclude with `map_add ν.eX _ _`. Conclude with `(hAdd _ _ _ _ _ _ h₁.2 h₂.2 h₃.2).2 rfl`. Conclude with `(hQ3 p₃ p₃ _ _ h₃ h₃).2 ((N.qEq_equivalence k).refl _)`. Establish `hpt0 : pt 0 = 1`.

Establish `h` using `hadd 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `(mul_eq_left.1 h.symm)`. Establish `hptn : ∀ (n : ℕ) a, pt (n • a) = pt a ^ n`. Introduce `n a`.

Proceed by induction on `n with`. Consider the case `zero => simpa using hpt0`. Consider the case `succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]`. Establish `hkt : ∀ a, pt a ^ k = 1`. Introduce `a`.

Establish `: k • a = 0`. Use function extensionality and compare the values at `i`. Simplify using `[nsmul_eq_mul, ZMod.natCast_self]`. Rewrite using `[← hptn, this, hpt0]`. Establish `hex : ∀ a, ∃ p, f p = pt a` using `fun a => hf2 (pt a) (hkt a)`.

Use `choose p hp using hex`. Establish `hexq : ∀ a, ∃ q, ν.QPt (p a) q` using `fun a => (hQ1 (p a)).exists`. Use `choose q hq using hexq`. Establish `hpow : ∀ (q' : N.QT k) (p' : QkPt D.toPre C k), ν.QPt p' q' → ∀ (n : ℕ) (pn : QkPt D.toPre C k), ν.QPt pn (q' ^ n) → f pn = f p' ^ n`. Introduce `q' p' hp' n`.

Proceed by induction on `n with`. Consider the case `zero`. Introduce `pn hpn`. Rewrite `hpn`, the goal using `[pow_zero]`. Establish `h` using `hmul pn pn pn 1 1 hpn hpn (by rw [_root_.mul_one]; exact hpn)`.

Conclude with `(mul_eq_left.1 h.symm)`. Consider the case `succ n ih`. Introduce `pn hpn`. Take `⟨pm, hpm⟩` from `hQ2 (q' ^ n)`. Rewrite `hpn` using `[pow_succ]`.

Rewrite using `[hmul pm p' pn _ _ hpm hp' hpn, ih pm hpm, pow_succ]`. Establish `hqk : ∀ q' : N.QT k, q' ^ k = N.qTriv k (Multiplicative.toAdd q'.1.1)`. Introduce `q'`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Prod.ext` to reduce the goal to its premises.

Use `show q'.1.1 ^ k = Multiplicative.ofAdd (k • Multiplicative.toAdd q'.1.1)`. Rewrite using `[ofAdd_nsmul, ofAdd_toAdd]`. Use `show q'.1.2 ^ k = N.io (Multiplicative.toAdd q'.1.1)`. Conclude with `(N.mem_QT).1 q'.2`. Use `⟨p, q, ⟨hζ, ?_, ?_, ?_, ?_⟩, fun a => ⟨hq a, (hf1 _ _).2 (hp a).symm⟩⟩` and prove the remaining obligations.

Introduce `a b`. Take `⟨p'', hp''⟩` from `hQ2 (q a * q b)`. Establish `h : f p'' = f (p (a + b))` using `by rw [hmul _ _ _ _ _ (hq a) (hq b) hp'', hp, hp, hp, hadd]`. Conclude with `(hQ3 _ _ _ _ hp'' (hq (a + b))).1 ((hf3 _ _).1 h)`. Introduce `a b h`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[← hp, ← hp]`. Conclude with `(hf3 _ _).2 ((hQ3 _ _ _ _ (hq a) (hq b)).2 h)`. Introduce `q'`. Take `⟨p', hp'⟩` from `hQ2 q'`.

Take `⟨p₀, hp₀⟩` from `hQ2 1`. Take `⟨pk, hpk⟩` from `hQ2 (q' ^ k)`. Establish `h0` using `hpow q' p' hp' 0 p₀ (by rw [pow_zero]; exact hp₀)`. Establish `hk'` using `hpow q' p' hp' k pk hpk`. Establish `heq : N.QEq 1 (q' ^ k)` using `(N.qEq_iff _ _).2 ⟨_, by rw [_root_.one_mul]; exact hqk q'⟩`.

Establish `h1 : f p₀ = f pk` using `(hf3 _ _).2 ((hQ3 _ _ _ _ hp₀ hpk).2 heq)`. Establish `htor : f p' ^ k = 1` using `by rw [← hk', ← h1, h0, pow_zero]`. Take `⟨a, ha⟩` from `hsurj (f p') htor`. Use `⟨a, (hQ3 _ _ _ _ (hq a) hp').1 ((hf3 _ _).1 ?_)⟩` and prove the remaining obligations. Rewrite using `[hp, ha]`.

Introduce `i j`. Establish `h` using `hw i j`. Rewrite `h` using `[← hp, ← hp]`. Establish `h'` using `(hf5 _ _ (ζ ^ stdSymp g i j)).2 h`. Conclude with `Units.ext ((hWp _ _ _ _ _ (hq _) (hq _)).1 h').symm`.
-/
theorem qLevel_of_torsion_labels : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∀ (g k : ℕ), 1 ≤ k → ∀ (ζ : Cˣ) (pt : (Fin (2 * g) → ZMod k) → (TFK (R := V) C ⟶ A.A)), IsPrimitiveRoot ζ k → (∀ a b, pt (a + b) = pt a * pt b) → Function.Injective pt → (∀ z : TFK (R := V) C ⟶ A.A, z ^ k = 1 → ∃ a, pt a = z) → (∀ i j, WeilIs A.A A.L k (pt (Pi.single i 1)) (pt (Pi.single j 1)) (unitOn (ζ ^ stdSymp g i j))) → ∃ (p : (Fin (2 * g) → ZMod k) → QkPt D.toPre C k) (q : (Fin (2 * g) → ZMod k) → N.QT k), QLevel N g k ζ q ∧ ∀ a, ν.QPt (p a) (q a) ∧ QkToAkU U.toUnifPre C k (p a) (pt a) := by
  intro V _ _ _ _ hV D A G _ _ hG U C _ _ _ _ _ _ hC N ν hI
  intro g k hk ζ pt hζ hadd hinj hsurj hw
  obtain ⟨f, hf1, hf2, hf3, hf4, hf5⟩ := GlobalTheory.ZH.uTors_closed V hV A G D U C k hk
  obtain ⟨-, -, hAdd, -, hQ⟩ := GlobalTheory.Ex.GtValues.points_correspond V D.toPre D.psi_even D.tau_bimult C N ν
  have hWp := GlobalTheory.WeilValues.weil_eq_values GlobalTheory.Ex.GtValues.points_correspond
    (GlobalTheory.Ex.brFam GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2) V D.toPre D.psi_even D.tau_bimult C N ν k hk
  obtain ⟨hQ1, hQ2, hQ3⟩ := hQ k

  have hmul : ∀ (p₁ p₂ p₃ : QkPt D.toPre C k) (q₁ q₂ : N.QT k), ν.QPt p₁ q₁ → ν.QPt p₂ q₂ → ν.QPt p₃ (q₁ * q₂) →
      f p₃ = f p₁ * f p₂ := by
    intro p₁ p₂ p₃ q₁ q₂ h₁ h₂ h₃
    apply hf4
    refine ⟨p₃, ?_, ?_, ?_⟩
    · rw [← h₃.1, ← h₁.1, ← h₂.1]
      exact map_add ν.eX _ _
    · exact (hAdd _ _ _ _ _ _ h₁.2 h₂.2 h₃.2).2 rfl
    · exact (hQ3 p₃ p₃ _ _ h₃ h₃).2 ((N.qEq_equivalence k).refl _)

  have hpt0 : pt 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have hptn : ∀ (n : ℕ) a, pt (n • a) = pt a ^ n := by
    intro n a
    induction n with
    | zero => simpa using hpt0
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hkt : ∀ a, pt a ^ k = 1 := by
    intro a
    have : k • a = 0 := by
      funext i
      simp [nsmul_eq_mul, ZMod.natCast_self]
    rw [← hptn, this, hpt0]
  have hex : ∀ a, ∃ p, f p = pt a := fun a => hf2 (pt a) (hkt a)
  choose p hp using hex
  have hexq : ∀ a, ∃ q, ν.QPt (p a) q := fun a => (hQ1 (p a)).exists
  choose q hq using hexq

  have hpow : ∀ (q' : N.QT k) (p' : QkPt D.toPre C k), ν.QPt p' q' → ∀ (n : ℕ) (pn : QkPt D.toPre C k),
      ν.QPt pn (q' ^ n) → f pn = f p' ^ n := by
    intro q' p' hp' n
    induction n with
    | zero =>
      intro pn hpn
      rw [pow_zero] at hpn ⊢
      have h := hmul pn pn pn 1 1 hpn hpn (by rw [_root_.mul_one]; exact hpn)
      exact (mul_eq_left.1 h.symm)
    | succ n ih =>
      intro pn hpn
      obtain ⟨pm, hpm⟩ := hQ2 (q' ^ n)
      rw [pow_succ] at hpn
      rw [hmul pm p' pn _ _ hpm hp' hpn, ih pm hpm, pow_succ]
  have hqk : ∀ q' : N.QT k, q' ^ k = N.qTriv k (Multiplicative.toAdd q'.1.1) := by
    intro q'
    apply Subtype.ext
    apply Prod.ext
    · show q'.1.1 ^ k = Multiplicative.ofAdd (k • Multiplicative.toAdd q'.1.1)
      rw [ofAdd_nsmul, ofAdd_toAdd]
    · show q'.1.2 ^ k = N.io (Multiplicative.toAdd q'.1.1)
      exact (N.mem_QT).1 q'.2
  refine ⟨p, q, ⟨hζ, ?_, ?_, ?_, ?_⟩, fun a => ⟨hq a, (hf1 _ _).2 (hp a).symm⟩⟩
  · intro a b
    obtain ⟨p'', hp''⟩ := hQ2 (q a * q b)
    have h : f p'' = f (p (a + b)) := by rw [hmul _ _ _ _ _ (hq a) (hq b) hp'', hp, hp, hp, hadd]
    exact (hQ3 _ _ _ _ hp'' (hq (a + b))).1 ((hf3 _ _).1 h)
  · intro a b h
    apply hinj
    rw [← hp, ← hp]
    exact (hf3 _ _).2 ((hQ3 _ _ _ _ (hq a) (hq b)).2 h)
  · intro q'
    obtain ⟨p', hp'⟩ := hQ2 q'
    obtain ⟨p₀, hp₀⟩ := hQ2 1
    obtain ⟨pk, hpk⟩ := hQ2 (q' ^ k)
    have h0 := hpow q' p' hp' 0 p₀ (by rw [pow_zero]; exact hp₀)
    have hk' := hpow q' p' hp' k pk hpk
    have heq : N.QEq 1 (q' ^ k) := (N.qEq_iff _ _).2 ⟨_, by rw [_root_.one_mul]; exact hqk q'⟩
    have h1 : f p₀ = f pk := (hf3 _ _).2 ((hQ3 _ _ _ _ hp₀ hpk).2 heq)
    have htor : f p' ^ k = 1 := by rw [← hk', ← h1, h0, pow_zero]
    obtain ⟨a, ha⟩ := hsurj (f p') htor
    refine ⟨a, (hQ3 _ _ _ _ (hq a) hp').1 ((hf3 _ _).1 ?_)⟩
    rw [hp, ha]
  · intro i j
    have h := hw i j
    rw [← hp, ← hp] at h
    have h' := (hf5 _ _ (ζ ^ stdSymp g i j)).2 h
    exact Units.ext ((hWp _ _ _ _ _ (hq _) (hq _)).1 h').symm

end GlobalTheory.MBLow
end

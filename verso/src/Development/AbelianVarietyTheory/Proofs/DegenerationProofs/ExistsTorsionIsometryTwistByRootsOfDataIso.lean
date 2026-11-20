import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistIsoTorsionRepresentativeMulEquivStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

namespace GlobalTheory.Relabel

/- English proof (translation)
Introduce `hGt hWp`. Unfold `BrGtSt AllN at hGt`. Unfold `BrWpSt AllN at hWp`. Unfold `AllD`. Introduce `E _ _ _ H D R R' _ _ _ _ F _ _ _ _ A D' _ oa' hE' hB' N' ν' k β u r J hr hact`.

Unfold `ActCompat at hact`. Establish `hG` using `hGt R A.D₀ A.even A.bimult F A.N A.ν`. Establish `hG'` using `hGt R' D' hE' hB' F N' ν'`. Establish `hW` using `hWp R A.D₀ A.even A.bimult F A.N A.ν`. Establish `hW'` using `hWp R' D' hE' hB' F N' ν'`.

Establish `hI` using `GlobalTheory.T.twist_iso_torsionRepresentative_mulEquiv F A.N N' k β u J`. Use `choose τ hτ using fun n (hn : 0 < n) => hI.1 (r n) n (hr.pow hn)`. Establish `hex : ∀ n (a : D.La), ∃ p : QkPt D' F n, ∀ hn : 0 < n, ν'.QPt p (τ n hn (A.q n a))`. Introduce `n a`. Distinguish the cases in `hn : 0 < n`.

Take `⟨p, hp⟩` from `(hG'.2.2.2.2 n).2.1 (τ n hn (A.q n a))`. Conclude with `⟨p, fun _ => hp⟩`. Take `⟨p, -⟩` from `(hG'.2.2.2.2 n).2.1 1`. Conclude with `⟨p, fun h => absurd h hn⟩`. Use `choose ev hev using hex`.

Set `I' : TateIsoQ D D' oa' F` to `{ ζ := A.I.ζ ζ_prim := A.I.ζ_prim ζ_pow := A.I.ζ_pow ev := ev add := by`. Introduce `n hn a b`. Take `⟨q₀, hy, hadd, heq⟩` from `A.I.add n hn a b`. Take `⟨w₀, hw₀, -⟩` from `(hG.2.2.2.2 n).1 q₀`. Establish `hw : w₀ = A.q n a * A.q n b`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Prod.ext` to reduce the goal to its premises. Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Apply `A.ν.eX.injective` to reduce the goal to its premises. Rewrite using `[hw₀.1, hy, ← (A.hq n a).1, ← (A.hq n b).1, ← map_add]`.

Both sides reduce to the same expression. Conclude with `(hG.2.2.1 _ _ _ _ _ _ (A.hq n a).2 (A.hq n b).2 hw₀.2).mp hadd`. Establish `hqe` using `((hG.2.2.2.2 n).2.2 _ _ _ _ hw₀ (A.hq n (a + b))).mp heq`. Rewrite `hqe` using `[hw]`. Establish `hqe'` using `((hτ n hn).2.1 _ _).mp hqe`.

Rewrite `hqe'` using `[map_mul]`. Take `⟨p, hp⟩` from `(hG'.2.2.2.2 n).2.1 (τ n hn (A.q n a) * τ n hn (A.q n b))`. Use `⟨p, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hp.1, ← (hev n a hn).1, ← (hev n b hn).1, ← map_add]`. Both sides reduce to the same expression.

Conclude with `(hG'.2.2.1 _ _ _ _ _ _ (hev n a hn).2 (hev n b hn).2 hp.2).mpr rfl`. Conclude with `((hG'.2.2.2.2 n).2.2 _ _ _ _ hp (hev n (a + b) hn)).mpr hqe'`. Use `lin := by`. Introduce `n hn x a`. Conclude with `hact n hn x _ _ _ _ _ _ _ _ (A.I.lin n hn x a) (A.hq n a) (A.hq n (x • a)) (((hτ n hn).1 _ _).mp rfl) (((hτ n hn).1 _ _).mp rfl) (hev n a hn) (hev n (x • a) hn)`.

Use `ker := by`. Introduce `n hn a b`. Rewrite using `[(hG'.2.2.2.2 n).2.2 _ _ _ _ (hev n a hn) (hev n b hn), ← (hτ n hn).2.1, ← (hG.2.2.2.2 n).2.2 _ _ _ _ (A.hq n a) (A.hq n b)]`. Conclude with `A.I.ker n hn a b`. Use `onto := by`.

Introduce `n hn p`. Take `⟨v, hv, -⟩` from `(hG'.2.2.2.2 n).1 p`. Take `⟨p₀, hp₀⟩` from `(hG.2.2.2.2 n).2.1 ((τ n hn).symm v)`. Take `⟨a, ha⟩` from `A.I.onto n hn p₀`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Rewrite using `[(hG'.2.2.2.2 n).2.2 _ _ _ _ (hev n a hn) hv]`. Establish `h` using `((hτ n hn).2.1 _ _).mp (((hG.2.2.2.2 n).2.2 _ _ _ _ (A.hq n a) hp₀).mp ha)`. Rewrite `h` using `[MulEquiv.apply_symm_apply]`. Then use the resulting hypothesis. Use `tower := by`. Introduce `n m hn hm a`.

Establish `hnm : 0 < n * m` using `Nat.mul_pos hn hm`. Take `⟨q₀, hy, hns, heq⟩` from `A.I.tower n m hn hm a`. Take `⟨w₀, hw₀, -⟩` from `(hG.2.2.2.2 n).1 q₀`. Establish `h1 : w₀.1.1 = (A.q (n * m) a).1.1`. Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises.

Apply `A.ν.eX.injective` to reduce the goal to its premises. Rewrite using `[hw₀.1, hy, (A.hq (n * m) a).1]`. Establish `h2 : w₀.1.2 = (A.q (n * m) a).1.2 ^ m` using `(GtValues.isNsmul_val A.ν m (A.hq (n * m) a).2 hw₀.2).mp hns`. Take `⟨e1, e2⟩` from `hI.2 (r n) (r (n * m)) n (n * m) m w₀ (A.q (n * m) a) (τ n hn w₀) (τ (n * m) hnm (A.q (n * m) a)) (hr.2 n m hn hm) h1 h2 (((hτ n hn).1 _ _).mp rfl) (((hτ (n * m) hnm).1 _ _).mp rfl)`. Take `⟨p, hp⟩` from `(hG'.2.2.2.2 n).2.1 (τ n hn w₀)`.

Use `⟨p, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hp.1, ← (hev (n * m) a hnm).1, e1]`. Conclude with `(GtValues.isNsmul_val ν' m (hev (n * m) a hnm).2 hp.2).mpr e2`. Rewrite using `[(hG'.2.2.2.2 n).2.2 _ _ _ _ hp (hev n a hn), ← (hτ n hn).2.1, ← (hG.2.2.2.2 n).2.2 _ _ _ _ hw₀ (A.hq n a)]`. Conclude with `heq`.

Use `isom := by`. Introduce `n hn a b`. Establish `h1 : 1 ≤ n` using `hn`. Rewrite using `[hW' n h1 _ _ _ _ _ (hev n a hn) (hev n b hn), (hτ n hn).2.2]`. Conclude with `(hW n h1 _ _ _ _ _ (A.hq n a) (A.hq n b)).mp (A.I.isom n hn a b) }`.

Conclude with `⟨I', rfl, fun j hj x => ⟨τ j hj (A.q j x), ((hτ j hj).1 _ _).mp rfl, hev j x hj⟩⟩`.
-/
theorem exists_tateIsoQ_twJ : BrGtSt → BrWpSt → AllD fun {E} _ _ _ {H} D => letI := H.starRing; ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (A : ArcF D R F) (D' : DegPre R') [Module (𝓞 E) D'.X] (oa' : D'.OAct (𝓞 E)), D'.PsiEven → D'.TauBimult → ∀ (N' : NumD F) (ν' : NumOf D' F N') (k : ℕ) (β : A.N.Form k) (u : Fˣ) (r : ℕ → Fˣ) (J : NumD.Iso (A.N.twist β u) N'), Roots u r → ActCompat A.ν A.oa ν' oa' β u r J → ∃ I' : TateIsoQ D D' oa' F, I'.ζ = A.I.ζ ∧ ∀ j, 0 < j → ∀ x, ∃ q', TwJ β u (r j) J (A.q j x) q' ∧ ν'.QPt (I'.ev j x) q' := by
  intro hGt hWp
  unfold BrGtSt AllN at hGt
  unfold BrWpSt AllN at hWp
  unfold AllD
  intro E _ _ _ H D R R' _ _ _ _ F _ _ _ _ A D' _ oa' hE' hB' N' ν' k β u r J hr hact
  unfold ActCompat at hact
  have hG := hGt R A.D₀ A.even A.bimult F A.N A.ν
  have hG' := hGt R' D' hE' hB' F N' ν'
  have hW := hWp R A.D₀ A.even A.bimult F A.N A.ν
  have hW' := hWp R' D' hE' hB' F N' ν'
  have hI := GlobalTheory.T.twist_iso_torsionRepresentative_mulEquiv F A.N N' k β u J
  choose τ hτ using fun n (hn : 0 < n) => hI.1 (r n) n (hr.pow hn)
  have hex : ∀ n (a : D.La), ∃ p : QkPt D' F n, ∀ hn : 0 < n, ν'.QPt p (τ n hn (A.q n a)) := by
    intro n a
    by_cases hn : 0 < n
    · obtain ⟨p, hp⟩ := (hG'.2.2.2.2 n).2.1 (τ n hn (A.q n a))
      exact ⟨p, fun _ => hp⟩
    · obtain ⟨p, -⟩ := (hG'.2.2.2.2 n).2.1 1
      exact ⟨p, fun h => absurd h hn⟩
  choose ev hev using hex
  let I' : TateIsoQ D D' oa' F :=
    { ζ := A.I.ζ
      ζ_prim := A.I.ζ_prim
      ζ_pow := A.I.ζ_pow
      ev := ev
      add := by
        intro n hn a b
        obtain ⟨q₀, hy, hadd, heq⟩ := A.I.add n hn a b
        obtain ⟨w₀, hw₀, -⟩ := (hG.2.2.2.2 n).1 q₀
        have hw : w₀ = A.q n a * A.q n b := by
          apply Subtype.ext
          apply Prod.ext
          · apply Multiplicative.toAdd.injective
            apply A.ν.eX.injective
            rw [hw₀.1, hy, ← (A.hq n a).1, ← (A.hq n b).1, ← map_add]
            rfl
          · exact (hG.2.2.1 _ _ _ _ _ _ (A.hq n a).2 (A.hq n b).2 hw₀.2).mp hadd
        have hqe := ((hG.2.2.2.2 n).2.2 _ _ _ _ hw₀ (A.hq n (a + b))).mp heq
        rw [hw] at hqe
        have hqe' := ((hτ n hn).2.1 _ _).mp hqe
        rw [map_mul] at hqe'
        obtain ⟨p, hp⟩ := (hG'.2.2.2.2 n).2.1 (τ n hn (A.q n a) * τ n hn (A.q n b))
        refine ⟨p, ?_, ?_, ?_⟩
        · rw [← hp.1, ← (hev n a hn).1, ← (hev n b hn).1, ← map_add]
          rfl
        · exact (hG'.2.2.1 _ _ _ _ _ _ (hev n a hn).2 (hev n b hn).2 hp.2).mpr rfl
        · exact ((hG'.2.2.2.2 n).2.2 _ _ _ _ hp (hev n (a + b) hn)).mpr hqe'
      lin := by
        intro n hn x a
        exact hact n hn x _ _ _ _ _ _ _ _ (A.I.lin n hn x a) (A.hq n a) (A.hq n (x • a))
          (((hτ n hn).1 _ _).mp rfl) (((hτ n hn).1 _ _).mp rfl) (hev n a hn) (hev n (x • a) hn)
      ker := by
        intro n hn a b
        rw [(hG'.2.2.2.2 n).2.2 _ _ _ _ (hev n a hn) (hev n b hn), ← (hτ n hn).2.1,
          ← (hG.2.2.2.2 n).2.2 _ _ _ _ (A.hq n a) (A.hq n b)]
        exact A.I.ker n hn a b
      onto := by
        intro n hn p
        obtain ⟨v, hv, -⟩ := (hG'.2.2.2.2 n).1 p
        obtain ⟨p₀, hp₀⟩ := (hG.2.2.2.2 n).2.1 ((τ n hn).symm v)
        obtain ⟨a, ha⟩ := A.I.onto n hn p₀
        refine ⟨a, ?_⟩
        rw [(hG'.2.2.2.2 n).2.2 _ _ _ _ (hev n a hn) hv]
        have h := ((hτ n hn).2.1 _ _).mp (((hG.2.2.2.2 n).2.2 _ _ _ _ (A.hq n a) hp₀).mp ha)
        rwa [MulEquiv.apply_symm_apply] at h
      tower := by
        intro n m hn hm a
        have hnm : 0 < n * m := Nat.mul_pos hn hm
        obtain ⟨q₀, hy, hns, heq⟩ := A.I.tower n m hn hm a
        obtain ⟨w₀, hw₀, -⟩ := (hG.2.2.2.2 n).1 q₀
        have h1 : w₀.1.1 = (A.q (n * m) a).1.1 := by
          apply Multiplicative.toAdd.injective
          apply A.ν.eX.injective
          rw [hw₀.1, hy, (A.hq (n * m) a).1]
        have h2 : w₀.1.2 = (A.q (n * m) a).1.2 ^ m :=
          (GtValues.isNsmul_val A.ν m (A.hq (n * m) a).2 hw₀.2).mp hns
        obtain ⟨e1, e2⟩ := hI.2 (r n) (r (n * m)) n (n * m) m w₀ (A.q (n * m) a) (τ n hn w₀)
          (τ (n * m) hnm (A.q (n * m) a)) (hr.2 n m hn hm) h1 h2 (((hτ n hn).1 _ _).mp rfl)
          (((hτ (n * m) hnm).1 _ _).mp rfl)
        obtain ⟨p, hp⟩ := (hG'.2.2.2.2 n).2.1 (τ n hn w₀)
        refine ⟨p, ?_, ?_, ?_⟩
        · rw [← hp.1, ← (hev (n * m) a hnm).1, e1]
        · exact (GtValues.isNsmul_val ν' m (hev (n * m) a hnm).2 hp.2).mpr e2
        · rw [(hG'.2.2.2.2 n).2.2 _ _ _ _ hp (hev n a hn), ← (hτ n hn).2.1,
            ← (hG.2.2.2.2 n).2.2 _ _ _ _ hw₀ (A.hq n a)]
          exact heq
      isom := by
        intro n hn a b
        have h1 : 1 ≤ n := hn
        rw [hW' n h1 _ _ _ _ _ (hev n a hn) (hev n b hn), (hτ n hn).2.2]
        exact (hW n h1 _ _ _ _ _ (A.hq n a) (A.hq n b)).mp (A.I.isom n hn a b) }
  exact ⟨I', rfl, fun j hj x => ⟨τ j hj (A.q j x), ((hτ j hj).1 _ _).mp rfl, hev j x hj⟩⟩

end GlobalTheory.Relabel

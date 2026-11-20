import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.QvalAddTower

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

namespace GlobalTheory.Ex.Arch

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in

/- English proof (translation)
Introduce `hGt hWp hPt hQk hWA`. Unfold `_root_.GlobalTheory.Ex.BrGtSt _root_.GlobalTheory.Ex.AllN at hGt`. Unfold `_root_.GlobalTheory.Ex.BrWpSt _root_.GlobalTheory.Ex.AllN at hWp`. Unfold `_root_.GlobalTheory.Ex.Arch.PtSt _root_.GlobalTheory.Ex.Arch.AllDict at hPt`. Unfold `_root_.GlobalTheory.Ex.Arch.QkSt _root_.GlobalTheory.Ex.Arch.AllDict at hQk`.

Unfold `_root_.GlobalTheory.Ex.Arch.WpSt _root_.GlobalTheory.Ex.Arch.AllDict at hWA`. Use `beta_reduce at hGt hWp hPt hQk hWA`. Unfold `_root_.GlobalTheory.Ex.Arch.TowerSt _root_.GlobalTheory.Ex.AllD`. Introduce `E _ _ _ H D R _ _ _ A B dd hl`. Use `letI := H.starRing`.

Establish `hG` using `hGt R A.D₀ A.even A.bimult ℂ A.N A.ν`. Establish `hW` using `hWp R A.D₀ A.even A.bimult ℂ A.N A.ν`. Establish `hV` using `hPt (𝓞 E) A.N _ dd`. Establish `hL` using `hQk (𝓞 E) A.N _ dd`. Establish `hE` using `hWA (𝓞 E) A.N _ dd`.

Establish `hq` using `A.hq`. Establish `hT` using `_root_.GlobalTheory.NestQVal.qval_add_tower E H D R A.D₀ A.oa A.even A.bimult ℂ A.I A.N A.ν A.q hG.1 hG.2.2.1 (fun k => ⟨(hG.2.2.2.2 k).1, (hG.2.2.2.2 k).2.2⟩) hq`. Use `choose! f hf using fun n (hn : 0 < n) (a : D.La) => (hL n hn).1 (A.q n a)`. Establish `hpow : ∀ (m : ℕ) v g, dd.IsPt v g → dd.IsPt (m • v) (g ^ m)`. Take `⟨g₀, hg₀, hu⟩` from `hV.1 0`.

Establish `h00` using `hV.2.2.1 0 0 g₀ g₀ hg₀ hg₀`. Rewrite `h00` using `[add_zero]`. Establish `hg₁ : g₀ = 1` using `mul_eq_left.1 (hu _ h00)`. Introduce `m v g hg`. Proceed by induction on `m with`.

Consider the case `zero => simpa [hg₁] using hg₀`. Consider the case `succ k ih => simpa [succ_nsmul, pow_succ] using hV.2.2.1 _ _ _ _ ih hg`. Use `⟨f, ?_, hf⟩` and prove the remaining obligations. Unfold `_root_.GlobalTheory.Ex.Arch.IsTower`. Introduce `n hn`.

Take `⟨-, hRep, hmul, hmod⟩` from `hL n hn`. Establish `hQn` using `(hG.2.2.2.2 n).2.2`. Establish `hadd : ∀ a b, ∃ e, f n (a + b) = f n a + f n b + n • e` using `fun a b => (hmod _ _ _ _ (hmul _ _ _ _ (hf n hn a) (hf n hn b)) (hf n hn (a + b))).1 (hT.1 n hn a b)`. Use `⟨hadd, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `c a`.

Take `⟨Q, hQy, hQg, hQe⟩` from `A.I.lin n hn c a`. Take `⟨p', hp', -⟩` from `hRep (c • f n a)`. Take `⟨hya, hga⟩` from `hq n a`. Take `⟨c'', hc'', -⟩` from `hG.1 Q.g`. Establish `hRa` using `hf n hn a`.

Establish `hv` using `hl.2 c _ _ _ _ _ hga hc'' hQg hRa.2`. Rewrite `hv` using `[map_smul, ← _root_.GlobalTheory.AnArc.degeneratingTori_basePeriodMap_smul]`. Establish `hc : c'' = (p' : Multiplicative A.N.X × A.N.Gt).2` using `(hV.1 _).unique hv hp'.2`. Establish `hQp : A.ν.QPt Q p'`. Use `⟨?_, hc ▸ hc''⟩` and prove the remaining obligations.

Rewrite using `[hp'.1, _root_.GlobalTheory.AnArc.La.smul_y, hl.1, hQy, ← hya, hRa.1]`. Unfold `_root_.GlobalTheory.Ex.ArcF.act`. Simplify using the standard rewrite rules. Conclude with `(hmod _ _ _ _ hp' (hf n hn (c • a))).1 ((hQn _ _ _ _ hQp (hq n (c • a))).1 hQe)`. Introduce `a`.

Choose the witnesses or unpack the hypotheses as in `⟨e₀, he₀⟩ : ∃ e, f n 0 = n • e := by`. Take `⟨e, he⟩` from `hadd 0 0`. Rewrite `he` using `[add_zero]`. Use `⟨-e, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_neg, eq_neg_iff_add_eq_zero]`.

Combine the equalities or inequalities in the displayed calculation. Establish `key : (∃ e, f n 0 = f n a + n • e) ↔ ∃ b, a = n • b`. Rewrite using `[← hmod _ _ _ _ (hf n hn a) (hf n hn 0), ← hQn _ _ _ _ (hq n a) (hq n 0), A.I.ker n hn a 0]`. Simplify using the standard rewrite rules. Rewrite using `[← key]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨e, he⟩`. Conclude with `⟨e₀ - e, by rw [he₀, he, smul_sub]; abel⟩`. Introduce and unpack `⟨e, he⟩`. Conclude with `⟨e₀ - e, by rw [smul_sub, ← he₀, he]; abel⟩`.

Introduce `x`. Take `⟨p, hp, -⟩` from `hRep x`. Take `⟨P, hP⟩` from `(hG.2.2.2.2 n).2.1 p`. Take `⟨a, ha⟩` from `A.I.onto n hn P`. Take `⟨e, he⟩` from `(hmod _ _ _ _ (hf n hn a) hp).1 ((hQn _ _ _ _ (hq n a) hP).1 ha)`.

Conclude with `⟨a, e, he⟩`. Introduce `m hm a`. Establish `hnm : 0 < n * m` using `Nat.mul_pos hn hm`. Take `⟨p, hp, -⟩` from `hRep (f (n * m) a)`. Establish `hR` using `hf (n * m) hnm a`.

Establish `h1 : (p : Multiplicative A.N.X × A.N.Gt).1 = (A.q (n * m) a : Multiplicative A.N.X × A.N.Gt).1`. Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Rewrite using `[hp.1, hR.1]`. Establish `h2 : (p : Multiplicative A.N.X × A.N.Gt).2 = (A.q (n * m) a : Multiplicative A.N.X × A.N.Gt).2 ^ m`. Apply `(hV.1 _).unique hp.2` to reduce the goal to its premises.

Use `hpow m _ _ hR.2 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, smul_smul]`. Use `congr 1`. Establish `: (n : ℂ) ≠ 0` using `by exact_mod_cast hn.ne'`. Establish `: (m : ℂ) ≠ 0` using `by exact_mod_cast hm.ne'`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Take `⟨e, he⟩` from `(hmod _ _ _ _ hp (hf n hn a)).1 (hT.2 n m hn hm a p h1 h2)`. Conclude with `⟨-e, by rw [he, smul_neg]; abel⟩`. Introduce `a b`.

Rewrite using `[(hW n hn _ _ _ _ _ (hq n a) (hq n b)).1 (A.I.isom n hn a b)]`. Conclude with `hE n hn _ _ _ _ (hf n hn a) (hf n hn b)`.
-/
theorem _root_.GlobalTheory.Ex.Arch.towerSt_of : _root_.GlobalTheory.Ex.BrGtSt → _root_.GlobalTheory.Ex.BrWpSt → _root_.GlobalTheory.Ex.Arch.PtSt → _root_.GlobalTheory.Ex.Arch.QkSt → _root_.GlobalTheory.Ex.Arch.WpSt → _root_.GlobalTheory.Ex.Arch.TowerSt := by
  intro hGt hWp hPt hQk hWA
  unfold _root_.GlobalTheory.Ex.BrGtSt _root_.GlobalTheory.Ex.AllN at hGt
  unfold _root_.GlobalTheory.Ex.BrWpSt _root_.GlobalTheory.Ex.AllN at hWp
  unfold _root_.GlobalTheory.Ex.Arch.PtSt _root_.GlobalTheory.Ex.Arch.AllDict at hPt
  unfold _root_.GlobalTheory.Ex.Arch.QkSt _root_.GlobalTheory.Ex.Arch.AllDict at hQk
  unfold _root_.GlobalTheory.Ex.Arch.WpSt _root_.GlobalTheory.Ex.Arch.AllDict at hWA
  beta_reduce at hGt hWp hPt hQk hWA
  unfold _root_.GlobalTheory.Ex.Arch.TowerSt _root_.GlobalTheory.Ex.AllD
  intro E _ _ _ H D R _ _ _ A B dd hl
  letI := H.starRing
  have hG := hGt R A.D₀ A.even A.bimult ℂ A.N A.ν
  have hW := hWp R A.D₀ A.even A.bimult ℂ A.N A.ν
  have hV := hPt (𝓞 E) A.N _ dd
  have hL := hQk (𝓞 E) A.N _ dd
  have hE := hWA (𝓞 E) A.N _ dd
  have hq := A.hq
  have hT := _root_.GlobalTheory.NestQVal.qval_add_tower E H D R A.D₀ A.oa A.even A.bimult ℂ A.I A.N A.ν A.q
    hG.1 hG.2.2.1 (fun k => ⟨(hG.2.2.2.2 k).1, (hG.2.2.2.2 k).2.2⟩) hq
  choose! f hf using fun n (hn : 0 < n) (a : D.La) => (hL n hn).1 (A.q n a)
  have hpow : ∀ (m : ℕ) v g, dd.IsPt v g → dd.IsPt (m • v) (g ^ m) := by
    obtain ⟨g₀, hg₀, hu⟩ := hV.1 0
    have h00 := hV.2.2.1 0 0 g₀ g₀ hg₀ hg₀
    rw [add_zero] at h00
    have hg₁ : g₀ = 1 := mul_eq_left.1 (hu _ h00)
    intro m v g hg
    induction m with
    | zero => simpa [hg₁] using hg₀
    | succ k ih => simpa [succ_nsmul, pow_succ] using hV.2.2.1 _ _ _ _ ih hg
  refine ⟨f, ?_, hf⟩
  unfold _root_.GlobalTheory.Ex.Arch.IsTower
  intro n hn
  obtain ⟨-, hRep, hmul, hmod⟩ := hL n hn
  have hQn := (hG.2.2.2.2 n).2.2
  have hadd : ∀ a b, ∃ e, f n (a + b) = f n a + f n b + n • e := fun a b =>
    (hmod _ _ _ _ (hmul _ _ _ _ (hf n hn a) (hf n hn b)) (hf n hn (a + b))).1 (hT.1 n hn a b)
  refine ⟨hadd, ?_, ?_, ?_, ?_, ?_⟩
  · intro c a
    obtain ⟨Q, hQy, hQg, hQe⟩ := A.I.lin n hn c a
    obtain ⟨p', hp', -⟩ := hRep (c • f n a)
    obtain ⟨hya, hga⟩ := hq n a
    obtain ⟨c'', hc'', -⟩ := hG.1 Q.g
    have hRa := hf n hn a
    have hv := hl.2 c _ _ _ _ _ hga hc'' hQg hRa.2
    rw [map_smul, ← _root_.GlobalTheory.AnArc.degeneratingTori_basePeriodMap_smul] at hv
    have hc : c'' = (p' : Multiplicative A.N.X × A.N.Gt).2 := (hV.1 _).unique hv hp'.2
    have hQp : A.ν.QPt Q p' := by
      refine ⟨?_, hc ▸ hc''⟩
      rw [hp'.1, _root_.GlobalTheory.AnArc.La.smul_y, hl.1, hQy, ← hya, hRa.1]
      unfold _root_.GlobalTheory.Ex.ArcF.act
      simp
    exact (hmod _ _ _ _ hp' (hf n hn (c • a))).1 ((hQn _ _ _ _ hQp (hq n (c • a))).1 hQe)
  · intro a
    obtain ⟨e₀, he₀⟩ : ∃ e, f n 0 = n • e := by
      obtain ⟨e, he⟩ := hadd 0 0
      rw [add_zero] at he
      refine ⟨-e, ?_⟩
      rw [smul_neg, eq_neg_iff_add_eq_zero]
      calc f n 0 + n • e = (f n 0 + f n 0 + n • e) - f n 0 := by abel
        _ = 0 := by rw [← he, sub_self]
    have key : (∃ e, f n 0 = f n a + n • e) ↔ ∃ b, a = n • b := by
      rw [← hmod _ _ _ _ (hf n hn a) (hf n hn 0), ← hQn _ _ _ _ (hq n a) (hq n 0), A.I.ker n hn a 0]
      simp
    rw [← key]
    constructor
    · rintro ⟨e, he⟩
      exact ⟨e₀ - e, by rw [he₀, he, smul_sub]; abel⟩
    · rintro ⟨e, he⟩
      exact ⟨e₀ - e, by rw [smul_sub, ← he₀, he]; abel⟩
  · intro x
    obtain ⟨p, hp, -⟩ := hRep x
    obtain ⟨P, hP⟩ := (hG.2.2.2.2 n).2.1 p
    obtain ⟨a, ha⟩ := A.I.onto n hn P
    obtain ⟨e, he⟩ := (hmod _ _ _ _ (hf n hn a) hp).1 ((hQn _ _ _ _ (hq n a) hP).1 ha)
    exact ⟨a, e, he⟩
  · intro m hm a
    have hnm : 0 < n * m := Nat.mul_pos hn hm
    obtain ⟨p, hp, -⟩ := hRep (f (n * m) a)
    have hR := hf (n * m) hnm a
    have h1 : (p : Multiplicative A.N.X × A.N.Gt).1 = (A.q (n * m) a : Multiplicative A.N.X × A.N.Gt).1 := by
      apply Multiplicative.toAdd.injective
      rw [hp.1, hR.1]
    have h2 : (p : Multiplicative A.N.X × A.N.Gt).2 = (A.q (n * m) a : Multiplicative A.N.X × A.N.Gt).2 ^ m := by
      apply (hV.1 _).unique hp.2
      convert hpow m _ _ hR.2 using 1
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      congr 1
      have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      push_cast
      field_simp
    obtain ⟨e, he⟩ := (hmod _ _ _ _ hp (hf n hn a)).1 (hT.2 n m hn hm a p h1 h2)
    exact ⟨-e, by rw [he, smul_neg]; abel⟩
  · intro a b
    rw [(hW n hn _ _ _ _ _ (hq n a) (hq n b)).1 (A.I.isom n hn a b)]
    exact hE n hn _ _ _ _ (hf n hn a) (hf n hn b)

end GlobalTheory.Ex.Arch

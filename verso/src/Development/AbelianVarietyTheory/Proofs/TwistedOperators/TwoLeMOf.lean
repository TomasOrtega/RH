import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyVertices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFirstColumnSpaceRankSignatureSelfDual
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.RowEx.CarryGrid

open scoped nonZeroDivisors

variable {D : D7} {T : Type}

/- English proof (translation)
Consider the cases of `i with`. Consider the case `zero => omega`. Consider the case `succ i => rfl`.
-/
theorem vtxOf_pos (L : LevCh D T) (Vs : ℕ → ℕ → LSp D) (i j : ℕ) (h : 1 ≤ i) : vtxOf L Vs i j = Vs i j := by
  cases i with
  | zero => omega
  | succ i => rfl

/- English proof (translation)
Consider the cases of `j with`. Consider the case `zero => omega`. Consider the case `succ j => rfl`.
-/
theorem xOf_pos (X₀ : LSp D) (Xs : ℕ → LSp D) (j : ℕ) (h : 1 ≤ j) : xOf X₀ Xs j = Xs j := by
  cases j with
  | zero => omega
  | succ j => rfl

def castDec {A A' B B' : HSp D} {c : ℕ} {ε : D.host.E} (ea : A = A') (eb : B = B') (d : HermitianOrthogonalExtensionData A B c ε) :
    HermitianOrthogonalExtensionData A' B' c ε := by
  subst ea eb; exact d

/- English proof (translation)
Substitute `ea eb` using the available equality. Both sides reduce to the same expression.
-/
theorem castDec_ι {A A' B B' : HSp D} {c : ℕ} {ε : D.host.E} (ea : A = A') (eb : B = B') (d : HermitianOrthogonalExtensionData A B c ε) :
    HEq (castDec ea eb d).ι d.ι := by
  subst ea eb; rfl

/- English proof (translation)
Substitute `ea eb` using the available equality. Both sides reduce to the same expression.
-/
theorem castDec_a {A A' B B' : HSp D} {c : ℕ} {ε : D.host.E} (ea : A = A') (eb : B = B') (d : HermitianOrthogonalExtensionData A B c ε) :
    HEq (castDec ea eb d).a d.a := by
  subst ea eb; rfl

/- English proof (translation)
Substitute `ey ez` using the available equality. Conclude with `h`.
-/
theorem castDec_lat {Y Y' Z Z' : LSp D} {c : ℕ} {ε : D.host.E} (ey : Y = Y') (ez : Z = Z') (d : HermitianOrthogonalExtensionData Y.sp Z.sp c ε)
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (h : Z.lat = d.lat Y.lat 𝔟) :
    Z'.lat = (castDec (congrArg LSp.sp ey) (congrArg LSp.sp ez) d).lat Y'.lat 𝔟 := by
  subst ey ez; exact h

/- English proof (translation)
The claim follows from `D.R.two_le_m`.
-/
theorem two_le_m_of (L : LevCh D T) : 2 ≤ D.R.m := D.R.two_le_m

/- English proof (translation)
Establish `hY` using `colY_isV D T L μ0 h 0 (Nat.zero_le _)`. Take `⟨μ, hμ⟩` from `D.R.m_even`. Establish `hk` using `D.R.m_add_three_le_k`. Establish `hr : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Take `⟨Z, hZ, d, hd⟩` from `GlobalTheory.GridSpaces.exists_line _ hY (by unfold rankV; omega)`.

Use `⟨Z, ?_, d, hd⟩` and prove the remaining obligations. Establish `e1 : rankP D 0 = rankV D 0 0 + 1` using `by simp [rankP, nRk, rankV]`. Establish `e2 : (D.R.m - 0 + 1) / 2 = (D.R.m - 0) / 2` using `by omega`. Rewrite using `[e1, e2]`. Conclude with `hZ`.
-/
theorem firstCore (L : LevCh D T) (μ0 : T) (h : L.Is μ0) : ∃ Z : LSp D, Z.IsV (rankP D 0) ((D.R.m - 0 + 1) / 2) ∧
    ∃ d : HermitianOrthogonalExtensionData (Yc D 0) Z.sp 1 1, Z.lat = d.lat (L.ΛY 0) fun _ => 1 := by
  have hY := colY_isV D T L μ0 h 0 (Nat.zero_le _)
  obtain ⟨μ, hμ⟩ := D.R.m_even
  have hk := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  obtain ⟨Z, hZ, d, hd⟩ := GlobalTheory.GridSpaces.exists_line _ hY (by unfold rankV; omega)
  refine ⟨Z, ?_, d, hd⟩
  have e1 : rankP D 0 = rankV D 0 0 + 1 := by simp [rankP, nRk, rankV]
  have e2 : (D.R.m - 0 + 1) / 2 = (D.R.m - 0) / 2 := by omega
  rw [e1, e2]; exact hZ

abbrev recOf (_L : LevCh D T) : D7 := D

local macro:max "kd% " e:term:max : term => `((by kexactB $e))

local macro "copyDec% " d:term:max : term =>
  `({ ι := ($d).ι, isom := (by kexactB ($d).isom), a := ($d).a, gram := (by kexactB ($d).gram),
      perp := (by kexactB ($d).perp), rank := (by kexactB ($d).rank) })

local macro "copyIsV% " h:term:max : term =>
  `(⟨(by kexactB ($h).rank), (by kexactB ($h).sigOK), (by kexactB ($h).sig), (by kexactB ($h).sd)⟩)

/- English proof (translation)
Introduce `X X' T T' L L' μ₀ μ₀' ι hA sc G`. Take `⟨B, Cc, Wr, Vd, Ss, Nn, Gj⟩` from `X`. Take `⟨B', Cc', Wr', Vd', Ss', Nn', Gj'⟩` from `X'`. Consider the cases of `B`. Consider the cases of `B'`.

Establish `hpre` using `hA.pre`. Simplify using `only at hpre`. Substitute `hpre` using the available equality. Take `⟨f, f', hf, hC, hC'⟩` from `hA.C`. Establish `hf2` using `eq_of_heq hf`.

Substitute `hf2` using the available equality. Establish `hPg : ∀ PP, PP ∈ L'.Pg ↔ PP ∈ L.Pg`. Introduce `PP`. Establish `h2 : PP ∈ L.Pg ↔ ∃ k, L.C.P.Div k PP` using `hA.is.Pg PP`. Rewrite using `[hA.is'.Pg, h2, hC, hC']`.

Conclude with `Iff.rfl`. Establish `hQ : ∀ t, L'.Q t = L.Q (ι t)` using `fun t => eq_of_heq (hA.Q t)`. Set `pl' : Places L'` to `{ v0 := (by with_unfolding_all exact (G.pl.v0 :)) basePlace_over_qZero := (by with_unfolding_all exact (G.pl.basePlace_over_qZero :)) w := (by with_unfolding_all exact (G.pl.w :)) w_over := (by with_unfolding_all exact (G.pl.w_over :)) w_split := (by with_unfolding_all exact (G.p …`. Set `ch' : Chars pl' sc.cGap` to `{ chiH := (by with_unfolding_all exact (G.ch.chiH :)) chi := (by with_unfolding_all exact (G.ch.chi :)) chi_eq := (by with_unfolding_all exact (G.ch.chi_eq :)) triv := (by with_unfolding_all exact (G.ch.triv :)) inf := (by with_unfolding_all exact (G.ch.inf :)) unr := (by with_un …`. Establish `hmX` using `two_le_m_of L`.

Establish `hmX'` using `two_le_m_of L'`. Establish `h1X` using `Nat.le_of_succ_le hmX`. Establish `h1X'` using `Nat.le_of_succ_le hmX'`. Take `⟨P₀, hP₀, d₀, hd₀⟩` from `firstCore L' μ₀' hA.is'`. Set `Vs' : ℕ → ℕ → type_of% P₀` to `fun i j => ⟨(by with_unfolding_all exact ((G.sp.Vs i j).sp :)), (by with_unfolding_all exact ((G.sp.Vs i j).lat :))⟩`.

Set `Xs' : ℕ → type_of% P₀` to `fun j => ⟨(by with_unfolding_all exact ((G.sp.Xs j).sp :)), (by with_unfolding_all exact ((G.sp.Xs j).lat :))⟩`. Set `P' : ℕ → type_of% P₀` to `fun i => match i with`. Consider the case `0 => P₀`. Consider the case `k + 1 => ⟨(by with_unfolding_all exact ((G.sp.P (k + 1)).sp :)), (by with_unfolding_all exact ((G.sp.P (k + 1)).lat :))⟩`. Set `sp' : Vertices L' (pl'.stA sc) (pl'.stAbar sc)` to `{ Vs := Vs' P := P' Xs := Xs' V_is := fun i j h1 h2 h3 => copyIsV% (G.sp.V_is i j h1 h2 h3) P_is := fun i hi => match i, hi with`.

Consider the case `0, _ => hP₀`. Consider the case `k + 1, hi => copyIsV% (G.sp.P_is (k + 1) hi)`. Use `X_is := fun j h1 h2 => copyIsV% (G.sp.X_is j h1 h2)`. Use `dec0 := d₀`. Use `lat0 := hd₀`.

Use `colDec := fun i h h' => match i, h, h' with`. Consider the case `0, h, _ => absurd h (by omega)`. Consider the case `k + 1, h, h' => copyDec% (G.sp.colDec (k + 1) h h')`. Use `colLat := fun i h h' => match i, h, h' with`. Consider the case `0, h, _ => absurd h (by omega)`.

Consider the case `k + 1, h, h' => (by with_unfolding_all exact ((G.sp.colLat (k + 1) h h') :))`. Use `rowDecS := fun j h => castDec rfl (congrArg LSp.sp (vtxOf_pos L' Vs' _ (j + 1) h1X').symm) (copyDec% (castDec rfl (congrArg LSp.sp (vtxOf_pos L G.sp.Vs _ (j + 1) h1X)) (G.sp.rowDecS j h)))`. Use `rowLat := fun j h => castDec_lat rfl (vtxOf_pos L' Vs' _ (j + 1) h1X').symm _ _ ((by with_unfolding_all exact ((castDec_lat rfl (vtxOf_pos L G.sp.Vs _ (j + 1) h1X) (G.sp.rowDecS j h) _ (G.sp.rowLat j h)) :)))`. Use `topDec := castDec (congrArg LSp.sp (vtxOf_pos L' Vs' _ _ h1X').symm) (congrArg LSp.sp (xOf_pos (P' _) Xs' _ h1X').symm) (copyDec% (castDec (congrArg LSp.sp (vtxOf_pos L G.sp.Vs _ _ h1X)) (congrArg LSp.sp (xOf_pos (G.sp.P _) G.sp.Xs _ h1X)) G.sp.topDec))`. Use `topLat := castDec_lat (vtxOf_pos L' Vs' _ _ h1X').symm (xOf_pos (P' _) Xs' _ h1X').symm _ _ ((by with_unfolding_all exact ((castDec_lat (vtxOf_pos L G.sp.Vs _ _ h1X) (xOf_pos (G.sp.P _) G.sp.Xs _ h1X) G.sp.topDec _ G.sp.topLat) :))) }`.

Use `⟨⟨pl', ch', sp'⟩, (by with_unfolding_all exact ((HEq.refl G.pl.v0) :)), (by with_unfolding_all exact ((HEq.refl G.pl.w) :)), (by with_unfolding_all exact ((HEq.refl G.ch.chiH) :)), (by with_unfolding_all exact ((HEq.refl G.ch.chi) :)), fun i j => ⟨(by with_unfolding_all exact ((H …` and prove the remaining obligations. Introduce `j`. Consider the cases of `j with`. Consider the case `zero`. Establish `hP : ∀ n, 1 ≤ n → HEq (P' n).sp (G.sp.P n).sp ∧ HEq (P' n).lat (G.sp.P n).lat`.

Introduce `n hn`. Consider the cases of `n with`. Consider the case `zero => omega`. Consider the case `succ n => exact ⟨(by with_unfolding_all exact ((HEq.refl (G.sp.P (n + 1)).sp) :)), (by with_unfolding_all exact ((HEq.refl (G.sp.P (n + 1)).lat) :))⟩`. Conclude with `(by with_unfolding_all exact ((hP _ h1X') :))`.

Consider the case `succ j => exact ⟨(by with_unfolding_all exact ((HEq.refl (G.V (.top (j + 1)))) :)), (by with_unfolding_all exact ((HEq.refl (G.Λ (.top (j + 1)))) :))⟩`. Introduce `j h h'`. Consider the cases of `j with`. Consider the case `zero`. Establish `hc : ∀ n (h1 : 1 ≤ n) (h2 : n ≤ (recOf L').R.m), HEq (sp'.colDec n h1 h2).ι (G.sp.colDec n h1 h2).ι ∧ HEq (sp'.colDec n h1 h2).a (G.sp.colDec n h1 h2).a`.

Introduce `n h1 h2`. Consider the cases of `n with`. Consider the case `zero => omega`. Consider the case `succ n => exact ⟨(by with_unfolding_all exact ((HEq.refl (G.sp.colDec (n + 1) h1 h2).ι) :)), (by with_unfolding_all exact ((HEq.refl (G.sp.colDec (n + 1) h1 h2).a) :))⟩`. Conclude with `(by with_unfolding_all exact ((hc _ h' le_rfl) :))`.

Consider the case `succ j`. Use `⟨(castDec_ι _ _ _).trans ?_, (castDec_a _ _ _).trans ?_⟩` and prove the remaining obligations. Conclude with `(by with_unfolding_all exact ((castDec_ι rfl (congrArg LSp.sp (vtxOf_pos L G.sp.Vs _ _ h1X)) (G.sp.rowDecS j h)) :))`. Conclude with `(by with_unfolding_all exact ((castDec_a rfl (congrArg LSp.sp (vtxOf_pos L G.sp.Vs _ _ h1X)) (G.sp.rowDecS j h)) :))`. Use `⟨(castDec_ι _ _ _).trans ?_, (castDec_a _ _ _).trans ?_⟩` and prove the remaining obligations.

Conclude with `(by with_unfolding_all exact ((castDec_ι (congrArg LSp.sp (vtxOf_pos L G.sp.Vs _ _ h1X)) (congrArg LSp.sp (xOf_pos (G.sp.P _) G.sp.Xs _ h1X)) G.sp.topDec) :))`. Conclude with `(by with_unfolding_all exact ((castDec_a (congrArg LSp.sp (vtxOf_pos L G.sp.Vs _ _ h1X)) (congrArg LSp.sp (xOf_pos (G.sp.P _) G.sp.Xs _ h1X)) G.sp.topDec) :))`.
-/
theorem carryG : CarryG := by
  intro X X' T T' L L' μ₀ μ₀' ι hA sc G
  obtain ⟨B, Cc, Wr, Vd, Ss, Nn, Gj⟩ := X
  obtain ⟨B', Cc', Wr', Vd', Ss', Nn', Gj'⟩ := X'
  cases B
  cases B'
  have hpre := hA.pre
  dsimp only at hpre
  subst hpre
  obtain ⟨f, f', hf, hC, hC'⟩ := hA.C
  have hf2 := eq_of_heq hf
  subst hf2
  have hPg : ∀ PP, PP ∈ L'.Pg ↔ PP ∈ L.Pg := by
    intro PP
    have h2 : PP ∈ L.Pg ↔ ∃ k, L.C.P.Div k PP := hA.is.Pg PP
    rw [hA.is'.Pg, h2, hC, hC']
    exact Iff.rfl
  have hQ : ∀ t, L'.Q t = L.Q (ι t) := fun t => eq_of_heq (hA.Q t)
  let pl' : Places L' :=
    { v0 := (by with_unfolding_all exact (G.pl.v0 :))
      basePlace_over_qZero := (by with_unfolding_all exact (G.pl.basePlace_over_qZero :))
      w := (by with_unfolding_all exact (G.pl.w :))
      w_over := (by with_unfolding_all exact (G.pl.w_over :))
      w_split := (by with_unfolding_all exact (G.pl.w_split :))
      w_g := fun v k h => (hPg _).2 ((by with_unfolding_all exact ((G.pl.w_g v k h) :)))
      w_de := (by with_unfolding_all exact (G.pl.w_de :))
      w_Q := fun t PP hPP h => (by with_unfolding_all exact ((G.pl.w_Q (ι t) PP (hQ t ▸ hPP) h) :))
      levelPlace_ne_basePlace := fun t PP hPP => (by with_unfolding_all exact ((G.pl.levelPlace_ne_basePlace (ι t) PP (hQ t ▸ hPP)) :)) }
  let ch' : Chars pl' sc.cGap :=
    { chiH := (by with_unfolding_all exact (G.ch.chiH :))
      chi := (by with_unfolding_all exact (G.ch.chi :))
      chi_eq := (by with_unfolding_all exact (G.ch.chi_eq :))
      triv := (by with_unfolding_all exact (G.ch.triv :))
      inf := (by with_unfolding_all exact (G.ch.inf :))
      unr := (by with_unfolding_all exact (G.ch.unr :))
      lev1 := (by with_unfolding_all exact (G.ch.lev1 :))
      wild := (by with_unfolding_all exact (G.ch.wild :))
      lev0 := (by with_unfolding_all exact (G.ch.lev0 :)) }
  have hmX := two_le_m_of L
  have hmX' := two_le_m_of L'
  have h1X := Nat.le_of_succ_le hmX
  have h1X' := Nat.le_of_succ_le hmX'
  obtain ⟨P₀, hP₀, d₀, hd₀⟩ := firstCore L' μ₀' hA.is'
  let Vs' : ℕ → ℕ → type_of% P₀ := fun i j => ⟨(by with_unfolding_all exact ((G.sp.Vs i j).sp :)), (by with_unfolding_all exact ((G.sp.Vs i j).lat :))⟩
  let Xs' : ℕ → type_of% P₀ := fun j => ⟨(by with_unfolding_all exact ((G.sp.Xs j).sp :)), (by with_unfolding_all exact ((G.sp.Xs j).lat :))⟩
  let P' : ℕ → type_of% P₀ := fun i => match i with
    | 0 => P₀
    | k + 1 => ⟨(by with_unfolding_all exact ((G.sp.P (k + 1)).sp :)), (by with_unfolding_all exact ((G.sp.P (k + 1)).lat :))⟩
  let sp' : Vertices L' (pl'.stA sc) (pl'.stAbar sc) :=
    { Vs := Vs'
      P := P'
      Xs := Xs'
      V_is := fun i j h1 h2 h3 => copyIsV% (G.sp.V_is i j h1 h2 h3)
      P_is := fun i hi => match i, hi with
        | 0, _ => hP₀
        | k + 1, hi => copyIsV% (G.sp.P_is (k + 1) hi)
      X_is := fun j h1 h2 => copyIsV% (G.sp.X_is j h1 h2)
      dec0 := d₀
      lat0 := hd₀
      colDec := fun i h h' => match i, h, h' with
        | 0, h, _ => absurd h (by omega)
        | k + 1, h, h' => copyDec% (G.sp.colDec (k + 1) h h')
      colLat := fun i h h' => match i, h, h' with
        | 0, h, _ => absurd h (by omega)
        | k + 1, h, h' => (by with_unfolding_all exact ((G.sp.colLat (k + 1) h h') :))
      rowDecS := fun j h => castDec rfl (congrArg LSp.sp (vtxOf_pos L' Vs' _ (j + 1) h1X').symm)
        (copyDec% (castDec rfl (congrArg LSp.sp (vtxOf_pos L G.sp.Vs _ (j + 1) h1X)) (G.sp.rowDecS j h)))
      rowLat := fun j h => castDec_lat rfl (vtxOf_pos L' Vs' _ (j + 1) h1X').symm _ _
        ((by with_unfolding_all exact ((castDec_lat rfl (vtxOf_pos L G.sp.Vs _ (j + 1) h1X) (G.sp.rowDecS j h) _ (G.sp.rowLat j h)) :)))
      topDec := castDec (congrArg LSp.sp (vtxOf_pos L' Vs' _ _ h1X').symm) (congrArg LSp.sp (xOf_pos (P' _) Xs' _ h1X').symm)
        (copyDec% (castDec (congrArg LSp.sp (vtxOf_pos L G.sp.Vs _ _ h1X)) (congrArg LSp.sp (xOf_pos (G.sp.P _) G.sp.Xs _ h1X))
          G.sp.topDec))
      topLat := castDec_lat (vtxOf_pos L' Vs' _ _ h1X').symm (xOf_pos (P' _) Xs' _ h1X').symm _ _
        ((by with_unfolding_all exact ((castDec_lat (vtxOf_pos L G.sp.Vs _ _ h1X) (xOf_pos (G.sp.P _) G.sp.Xs _ h1X) G.sp.topDec _ G.sp.topLat) :))) }
  refine ⟨⟨pl', ch', sp'⟩, (by with_unfolding_all exact ((HEq.refl G.pl.v0) :)), (by with_unfolding_all exact ((HEq.refl G.pl.w) :)), (by with_unfolding_all exact ((HEq.refl G.ch.chiH) :)), (by with_unfolding_all exact ((HEq.refl G.ch.chi) :)),
    fun i j => ⟨(by with_unfolding_all exact ((HEq.refl (G.V (.grid (i + 1) j))) :)), (by with_unfolding_all exact ((HEq.refl (G.Λ (.grid (i + 1) j))) :))⟩, ?_, ?_, ?_⟩
  · intro j
    cases j with
    | zero =>
      have hP : ∀ n, 1 ≤ n → HEq (P' n).sp (G.sp.P n).sp ∧ HEq (P' n).lat (G.sp.P n).lat := by
        intro n hn
        cases n with
        | zero => omega
        | succ n => exact ⟨(by with_unfolding_all exact ((HEq.refl (G.sp.P (n + 1)).sp) :)), (by with_unfolding_all exact ((HEq.refl (G.sp.P (n + 1)).lat) :))⟩
      exact (by with_unfolding_all exact ((hP _ h1X') :))
    | succ j => exact ⟨(by with_unfolding_all exact ((HEq.refl (G.V (.top (j + 1)))) :)), (by with_unfolding_all exact ((HEq.refl (G.Λ (.top (j + 1)))) :))⟩
  · intro j h h'
    cases j with
    | zero =>
      have hc : ∀ n (h1 : 1 ≤ n) (h2 : n ≤ (recOf L').R.m), HEq (sp'.colDec n h1 h2).ι (G.sp.colDec n h1 h2).ι ∧
          HEq (sp'.colDec n h1 h2).a (G.sp.colDec n h1 h2).a := by
        intro n h1 h2
        cases n with
        | zero => omega
        | succ n => exact ⟨(by with_unfolding_all exact ((HEq.refl (G.sp.colDec (n + 1) h1 h2).ι) :)), (by with_unfolding_all exact ((HEq.refl (G.sp.colDec (n + 1) h1 h2).a) :))⟩
      exact (by with_unfolding_all exact ((hc _ h' le_rfl) :))
    | succ j =>
      refine ⟨(castDec_ι _ _ _).trans ?_, (castDec_a _ _ _).trans ?_⟩
      · exact (by with_unfolding_all exact ((castDec_ι rfl (congrArg LSp.sp (vtxOf_pos L G.sp.Vs _ _ h1X)) (G.sp.rowDecS j h)) :))
      · exact (by with_unfolding_all exact ((castDec_a rfl (congrArg LSp.sp (vtxOf_pos L G.sp.Vs _ _ h1X)) (G.sp.rowDecS j h)) :))
  · refine ⟨(castDec_ι _ _ _).trans ?_, (castDec_a _ _ _).trans ?_⟩
    · exact (by with_unfolding_all exact ((castDec_ι (congrArg LSp.sp (vtxOf_pos L G.sp.Vs _ _ h1X))
        (congrArg LSp.sp (xOf_pos (G.sp.P _) G.sp.Xs _ h1X)) G.sp.topDec) :))
    · exact (by with_unfolding_all exact ((castDec_a (congrArg LSp.sp (vtxOf_pos L G.sp.Vs _ _ h1X))
        (congrArg LSp.sp (xOf_pos (G.sp.P _) G.sp.Xs _ h1X)) G.sp.topDec) :))

end GlobalTheory.RowEx.CarryGrid

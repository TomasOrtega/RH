import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ToPairMul

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.RowReal

/- English proof (translation)
Take `⟨i, hi, rfl⟩` from `List.mem_map.1 h`. Establish `hi' : (i : ℚ) + 1 ≤ n` using `by exact_mod_cast (List.mem_range.1 hi)`. Establish `h0 : (0 : ℚ) ≤ i` using `by positivity`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem block_bounds {x y : ℚ} {n : ℕ} (h : y ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block x n) :
    x - ((n : ℚ) - 1) / 2 ≤ y ∧ y ≤ x + ((n : ℚ) - 1) / 2 := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
  have hi' : (i : ℚ) + 1 ≤ n := by exact_mod_cast (List.mem_range.1 hi)
  have h0 : (0 : ℚ) ≤ i := by positivity
  constructor <;> linarith

/- English proof (translation)
Unfold `GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block`. Rewrite using `[List.pairwise_map]`. Use `List.pairwise_lt_range.imp fun {i j} h => ?_` and prove the remaining obligations. Establish `: (i : ℚ) < j` using `by exact_mod_cast h`. Use `show _ < _`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem block_pairwise (x : ℚ) (n : ℕ) : (GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block x n).Pairwise (· > ·) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block
  rw [List.pairwise_map]
  refine List.pairwise_lt_range.imp fun {i j} h => ?_
  have : (i : ℚ) < j := by exact_mod_cast h
  show _ < _
  linarith

/- English proof (translation)
Rewrite using `[List.pairwise_flatMap]`. Use `⟨fun i _ => hp i, (List.pairwise_lt_finRange n).imp fun {i j} hij x hx y hy => ?_⟩` and prove the remaining obligations. Combine the linear relations using `[(hb i x hx).1, (hb j y hy).2, hs i j hij]`.
-/
theorem pairwise_flatMap_band {n : ℕ} (f : Fin n → List ℚ) (lo hi : Fin n → ℚ)
    (hp : ∀ i, (f i).Pairwise (· > ·)) (hb : ∀ i, ∀ x ∈ f i, lo i ≤ x ∧ x ≤ hi i)
    (hs : ∀ i j : Fin n, i < j → hi j < lo i) : ((List.finRange n).flatMap f).Pairwise (· > ·) := by
  rw [List.pairwise_flatMap]
  refine ⟨fun i _ => hp i, (List.pairwise_lt_finRange n).imp fun {i j} hij x hx y hy => ?_⟩
  linarith [(hb i x hx).1, (hb j y hy).2, hs i j hij]

/- English proof (translation)
Use `set G := num D C τ with hG`. Use `set P := rowEntries D C τ with hPdef`. Establish `hGm : G.m = D.R.m` using `rfl`. Establish `hGk : G.k = D.R.k` using `rfl`. Establish `hGs : G.s = sLen D` using `rfl`.

Establish `hGt : G.t = D.R.t` using `rfl`. Establish `hGg : G.ga = gap D C` using `rfl`. Establish `hSm : (rowSizes D).m = D.R.m` using `rfl`. Establish `hSk : (rowSizes D).k = D.R.k` using `rfl`. Establish `hSs : (rowSizes D).s = sLen D` using `rfl`.

Establish `hSt : (rowSizes D).t = D.R.t` using `rfl`. Establish `hPa : ∀ l, P.a l = G.a l` using `fun _ => rfl`. Establish `hPc : ∀ i, P.c i = G.cen (i + 1)` using `fun _ => rfl`. Establish `hPv : ∀ i, P.v i = G.v (i + 2)` using `fun _ => rfl`. Establish `hPu : ∀ i, P.u i = G.vHalf (i + 2)` using `fun _ => rfl`.

Establish `hPb : ∀ j, P.b j = G.b (j + 1)` using `fun _ => rfl`. Establish `hPe : ∀ j, P.e j = G.e (j + 1)` using `fun _ => rfl`. Establish `hm2` using `D.R.two_le_m`. Establish `hk3` using `D.R.m_add_three_le_k`. Establish `hgap : sLen D + 2 < gap D C` using `by have := (isLeast_gap D C).1.2.1; omega`.

Establish `hgQ : (sLen D : ℚ) + 2 < G.ga` using `by rw [hGg]; exact_mod_cast hgap`. Establish `ht1 : (1 : ℚ) ≤ D.R.t` using `by exact_mod_cast D.R.t_odd.pos`. Establish `hle : ∀ {i j : ℕ}, i ≤ j → G.a j ≤ G.a i` using `fun h => by`. Break down `h.eq_or_lt with rfl | h` into its components or cases. Conclude with `le_rfl`.

Combine the linear relations using `[a_add_le (G := G) h]`. Establish `hcen : ∀ i : ℕ, 1 ≤ i → i ≤ D.R.m → |(G.cen i : ℚ) - (G.a i + G.ga / 2)| ≤ 1` using `fun i h1 h2 => by`. Rewrite using `[← G.mid_eq h1]`. Conclude with `num_nearMid D C τ i (Finset.mem_Icc.2 ⟨h1, h2⟩)`. Establish `hC : ∀ i : ℕ, 1 ≤ i → i ≤ D.R.m → ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (G.cen i : ℚ) (sLen D), G.a i + G.ga / 2 - ((sLen D : ℚ) + 1) / 2 ≤ x ∧ x ≤ G.a i + G.ga / 2 + ((sLen D : ℚ) + 1) / 2`.

Introduce `i h1 h2 x hx`. Establish `e1` using `block_bounds hx`. Establish `e2` using `abs_le.1 (hcen i h1 h2)`. Apply the tactic sequence `constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]`. Establish `hspec` using `GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D C) (cen D C τ)`.

Establish `hbe : ∀ j (h : j < D.R.m), ((D.R.t : ℚ) + 3) / 2 ≤ G.e (j + 1) - G.b (j + 1)` using `fun j h => by`. Use `(D.hc τ).gap_be ⟨j, h⟩` as an intermediate fact. Rewrite `this` using `[hspec.2.1 ⟨j, h⟩, hspec.2.2 ⟨j, h⟩]`. Conclude with `this`. Establish `heb : ∀ j (h : j + 1 < D.R.m), ((D.R.t : ℚ) + 3) / 2 ≤ G.b (j + 2) - G.e (j + 1)` using `fun j h => by`.

Use `(D.hc τ).gap_eb ⟨j, by omega⟩ h` as an intermediate fact. Rewrite `this` using `[hspec.2.1 ⟨j + 1, h⟩, hspec.2.2 ⟨j, by omega⟩]`. Conclude with `this`. Establish `hvle : ∀ i j, 2 ≤ i → i ≤ j → j ≤ D.R.k → G.v j ≤ G.v i` using `fun i j h1 h2 h3 => by`. Break down `h2.eq_or_lt with rfl | h` into its components or cases.

Conclude with `le_rfl`. Conclude with `(G.v_anti i j h1 h h3).le`. Establish `hble : ∀ i j, 1 ≤ i → i ≤ j → j ≤ D.R.m → G.b i ≤ G.b j` using `fun i j h1 h2 h3 => by`. Break down `h2.eq_or_lt with rfl | h` into its components or cases. Conclude with `le_rfl`.

Conclude with `(G.b_mono i j h1 h h3).le`. Establish `hvk : (-(G.b 1 : ℚ)) < G.v D.R.k - 1 / 2`. Establish `h1` using `(D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩`. Establish `h2` using `(D.hc τ).u_last_gt (by omega) (by omega)`. Establish `h3 : -(D.hc τ).b ⟨0, by omega⟩ < (D.hc τ).v ⟨D.R.k - 2, by omega⟩`.

Use `h2.trans (lt_of_eq_of_lt ?_ h1)` and prove the remaining obligations. Use `congr 1`. Use `ext`. Simplify using `only`. Use linear arithmetic over natural numbers and integers.

Rewrite `h3` using `[hspec.2.1 ⟨0, by omega⟩, hspec.1 ⟨D.R.k - 2, by omega⟩]`. Establish `h4 : -(G.b 1) < G.v D.R.k`. Rewrite `h3` using `[show D.R.k - 2 + 2 = D.R.k by omega]`. Conclude with `h3` after adjusting the coercions. Establish `h5 : ((-(G.b 1) + 1 : ℤ) : ℚ) ≤ G.v D.R.k` using `by exact_mod_cast h4`.

Move the coercions through the operations in `at h5`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨fun l => ⟨G.v 2 + ((G.m : ℤ) + 1 - ((l : ℕ) : ℤ)) * G.ga, ?_⟩, fun i => ⟨G.v (i + 2) - 1, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hPa]`. Unfold `GlobalTheory.SignedHC.GridData.a`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hPu]`. Unfold `GlobalTheory.SignedHC.GridData.vHalf`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `bX : ∀ (i : Fin (rowSizes D).m), ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (P.c i) (rowSizes D).s ++ [P.a i.succ], G.a (i + 1) ≤ x ∧ x ≤ G.a (i + 1) + G.ga / 2 + ((sLen D : ℚ) + 1) / 2`. Introduce `i x hx`. Establish `hi` using `i.2`. Rewrite `hx` using `[List.mem_append, List.mem_singleton, hPc, hPa, hSs, Fin.val_succ]`.

Break down `hx with hx | rfl` into its components or cases. Use `hC (i + 1) (by omega) (by omega) x hx` as an intermediate fact. Apply the tactic sequence `constructor <;> linarith [this.1, this.2]`. Prove the components needed by the constructor for the conclusion. Conclude with `le_rfl`.

Establish `: (0 : ℚ) ≤ G.ga` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `pX : (P.a 0 :: (List.finRange (rowSizes D).m).flatMap fun i => GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (P.c i) (rowSizes D).s ++ [P.a i.succ]).Pairwise (· > ·)`. Rewrite using `[List.pairwise_cons]`. Prove the components needed by the constructor for the conclusion.

Introduce `x hx`. Take `⟨i, -, hx⟩` from `List.mem_flatMap.1 hx`. Establish `h1` using `(bX i x hx).2`. Establish `h2` using `a_add_le (G := G) (show 0 < (i : ℕ) + 1 by omega)`. Rewrite using `[hPa]`.

Use `show x < G.a 0`. Combine the linear equalities and inequalities to obtain the conclusion. Use `pairwise_flatMap_band _ (fun i => G.a (i + 1)) (fun i => G.a (i + 1) + G.ga / 2 + ((sLen D : ℚ) + 1) / 2) (fun i => ?_) bX (fun i j hij => ?_)` and prove the remaining obligations. Rewrite using `[List.pairwise_append]`. Use `⟨block_pairwise _ _, List.pairwise_singleton _ _, fun x hx y hy => ?_⟩` and prove the remaining obligations.

Rewrite `hy` using `[List.mem_singleton]`. Substitute `hy` using the available equality. Rewrite `hx` using `[hPc, hSs]`. Use `hC (i + 1) (by omega) (by omega) x hx` as an intermediate fact. Rewrite using `[hPa, Fin.val_succ]`.

Use `show _ < _`. Combine the linear relations using `[this.1]`. Establish `h` using `a_add_le (G := G) (show (i : ℕ) + 1 < j + 1 by have : (i : ℕ) < j := hij; omega) show _ < _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `tX : ∀ x ∈ (P.a 0 :: (List.finRange (rowSizes D).m).flatMap fun i => GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (P.c i) (rowSizes D).s ++ [P.a i.succ]), G.a G.m ≤ x`.

Introduce `x hx`. Break down `List.mem_cons.1 hx with rfl | hx` into its components or cases. Rewrite using `[hPa]; exact hle (by simp)`. Take `⟨i, -, hx⟩` from `List.mem_flatMap.1 hx`. Use `i.2` as an intermediate fact.

Conclude with `(hle (show (i : ℕ) + 1 ≤ G.m by rw [hGm]; omega)).trans (bX i x hx).1`. Establish `bY : ∀ (i : Fin ((rowSizes D).k - 1)), ∀ y ∈ [(P.v i : ℚ), P.u i], (G.v (i + 2) : ℚ) - 1 / 2 ≤ y ∧ y ≤ G.v (i + 2)`. Introduce `i y hy`. Rewrite `hy` using `[hPv, hPu]`. Unfold `GlobalTheory.SignedHC.GridData.vHalf at hy`.

Simplify using `only [List.mem_cons, List.not_mem_nil, or_false] at hy`. Apply the tactic sequence `rcases hy with rfl | rfl <;> constructor <;> linarith`. Establish `pY : ((List.finRange ((rowSizes D).k - 1)).flatMap fun i => [(P.v i : ℚ), P.u i]).Pairwise (· > ·)`. Use `pairwise_flatMap_band _ (fun i => (G.v (i + 2) : ℚ) - 1 / 2) (fun i => (G.v (i + 2) : ℚ)) (fun i => ?_) bY (fun i j hij => ?_)` and prove the remaining obligations. Use `List.Pairwise.cons (fun y hy => ?_) (List.pairwise_singleton _ _)` and prove the remaining obligations.

Rewrite `hy` using `[List.mem_singleton]`. Substitute `hy` using the available equality. Rewrite using `[hPv, hPu]`. Unfold `GlobalTheory.SignedHC.GridData.vHalf`. Use `show _ < _`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hj : (j : ℕ) < D.R.k - 1` using `j.2`. Establish `hij' : (i : ℕ) < j` using `hij`. Establish `h` using `G.v_anti (i + 2) (j + 2) (by omega) (by omega) (by rw [hGk]; omega)`. Establish `h' : ((G.v (j + 2) + 1 : ℤ) : ℚ) ≤ G.v (i + 2)` using `by exact_mod_cast h`.

Move the coercions through the operations in `at h'`. Use `show _ < _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `tY : ∀ y ∈ ((List.finRange ((rowSizes D).k - 1)).flatMap fun i => [(P.v i : ℚ), P.u i]), (G.v D.R.k : ℚ) - 1 / 2 ≤ y ∧ y ≤ G.v 2`. Introduce `y hy`.

Take `⟨i, -, hy⟩` from `List.mem_flatMap.1 hy`. Establish `hi : (i : ℕ) < D.R.k - 1` using `i.2`. Establish `h1 : ((G.v D.R.k : ℤ) : ℚ) ≤ G.v (i + 2)` using `by exact_mod_cast hvle (i + 2) D.R.k (by omega) (by omega) le_rfl`. Establish `h2 : ((G.v (i + 2) : ℤ) : ℚ) ≤ G.v 2` using `by exact_mod_cast hvle 2 (i + 2) le_rfl (by omega) (by omega)`. Use `bY i y hy` as an intermediate fact.

Apply the tactic sequence `constructor <;> linarith [this.1, this.2]`. Establish `bZ : ∀ (j : Fin (rowSizes D).m), ∀ z ∈ ((-P.b j : ℚ) :: GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (-P.e j) (rowSizes D).t), -(G.e (j + 1) : ℚ) - ((D.R.t : ℚ) - 1) / 2 ≤ z ∧ z ≤ -(G.b (j + 1) : ℚ)`. Introduce `j z hz`. Establish `hj : (j : ℕ) < D.R.m` using `j.2`. Establish `h1` using `hbe j hj`.

Rewrite `hz` using `[List.mem_cons, hPb, hPe, hSt]`. Break down `hz with rfl | hz` into its components or cases. Apply the tactic sequence `constructor <;> linarith`. Use `block_bounds hz` as an intermediate fact. Apply the tactic sequence `constructor <;> linarith [this.1, this.2]`.

Establish `pZ : ((List.finRange (rowSizes D).m).flatMap fun j => (-P.b j : ℚ) :: GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (-P.e j) (rowSizes D).t).Pairwise (· > ·)`. Use `pairwise_flatMap_band _ (fun j => -(G.e (j + 1) : ℚ) - ((D.R.t : ℚ) - 1) / 2) (fun j => -(G.b (j + 1) : ℚ)) (fun j => ?_) bZ (fun i j hij => ?_)` and prove the remaining obligations. Establish `hj : (j : ℕ) < D.R.m` using `j.2`. Establish `h1` using `hbe j hj`. Rewrite using `[List.pairwise_cons]`.

Use `⟨fun z hz => ?_, block_pairwise _ _⟩` and prove the remaining obligations. Rewrite `*` using `[hPb, hPe, hSt]`. Use `block_bounds hz` as an intermediate fact. Use `show _ < _`. Combine the linear relations using `[this.2]`.

Establish `hj : (j : ℕ) < D.R.m` using `j.2`. Establish `hij' : (i : ℕ) < j` using `hij`. Establish `h1` using `heb i (by omega)`. Establish `h2 : ((G.b (i + 2) : ℤ) : ℚ) ≤ G.b (j + 1)` using `by exact_mod_cast hble (i + 2) (j + 1) (by omega) (by omega) (by omega)`. Use `show _ < _`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `tZ : ∀ z ∈ ((List.finRange (rowSizes D).m).flatMap fun j => (-P.b j : ℚ) :: GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (-P.e j) (rowSizes D).t), z ≤ -(G.b 1 : ℚ)`. Introduce `z hz`. Take `⟨j, -, hz⟩` from `List.mem_flatMap.1 hz`. Establish `hj : (j : ℕ) < D.R.m` using `j.2`.

Establish `h1 : ((G.b 1 : ℤ) : ℚ) ≤ G.b (j + 1)` using `by exact_mod_cast hble 1 (j + 1) le_rfl (by omega) (by omega)`. Combine the linear relations using `[(bZ j z hz).2]`. Establish `hv2 : (G.v 2 : ℚ) < G.a G.m`. Rewrite using `[G.a_m]`. Establish `: (0 : ℚ) ≤ G.ga` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `show (Entries.orderList P).Pairwise (· > ·)`. Rewrite using `[Entries.orderList, List.pairwise_append, List.pairwise_append]`. Use `⟨⟨pX, pY, fun x hx y hy => ?_⟩, pZ, fun x hx z hz => ?_⟩` and prove the remaining obligations. Establish `h1` using `tX x hx`.

Establish `h2` using `(tY y hy).2`. Use `show _ < _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3` using `tZ z hz show _ < _`. Break down `List.mem_append.1 hx with hx | hx` into its components or cases.

Establish `h1` using `tX x hx`. Establish `h2` using `tY _ (List.mem_flatMap.2 ⟨⟨0, by rw [hSk]; omega⟩, List.mem_finRange _, List.mem_cons_self⟩)`. Combine the linear relations using `[h2.1, h2.2]`. Establish `h1` using `(tY x hx).1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rowEntries_good (D : D7) (C : ℝ) (τ : D.what₂.Tau) : (rowEntries D C τ).Good := by
  set G := num D C τ with hG
  set P := rowEntries D C τ with hPdef
  have hGm : G.m = D.R.m := rfl
  have hGk : G.k = D.R.k := rfl
  have hGs : G.s = sLen D := rfl
  have hGt : G.t = D.R.t := rfl
  have hGg : G.ga = gap D C := rfl
  have hSm : (rowSizes D).m = D.R.m := rfl
  have hSk : (rowSizes D).k = D.R.k := rfl
  have hSs : (rowSizes D).s = sLen D := rfl
  have hSt : (rowSizes D).t = D.R.t := rfl
  have hPa : ∀ l, P.a l = G.a l := fun _ => rfl
  have hPc : ∀ i, P.c i = G.cen (i + 1) := fun _ => rfl
  have hPv : ∀ i, P.v i = G.v (i + 2) := fun _ => rfl
  have hPu : ∀ i, P.u i = G.vHalf (i + 2) := fun _ => rfl
  have hPb : ∀ j, P.b j = G.b (j + 1) := fun _ => rfl
  have hPe : ∀ j, P.e j = G.e (j + 1) := fun _ => rfl
  have hm2 := D.R.two_le_m
  have hk3 := D.R.m_add_three_le_k
  have hgap : sLen D + 2 < gap D C := by have := (isLeast_gap D C).1.2.1; omega
  have hgQ : (sLen D : ℚ) + 2 < G.ga := by rw [hGg]; exact_mod_cast hgap
  have ht1 : (1 : ℚ) ≤ D.R.t := by exact_mod_cast D.R.t_odd.pos
  have hle : ∀ {i j : ℕ}, i ≤ j → G.a j ≤ G.a i := fun h => by
    rcases h.eq_or_lt with rfl | h
    · exact le_rfl
    · linarith [a_add_le (G := G) h]
  have hcen : ∀ i : ℕ, 1 ≤ i → i ≤ D.R.m → |(G.cen i : ℚ) - (G.a i + G.ga / 2)| ≤ 1 := fun i h1 h2 => by
    rw [← G.mid_eq h1]; exact num_nearMid D C τ i (Finset.mem_Icc.2 ⟨h1, h2⟩)
  have hC : ∀ i : ℕ, 1 ≤ i → i ≤ D.R.m → ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (G.cen i : ℚ) (sLen D),
      G.a i + G.ga / 2 - ((sLen D : ℚ) + 1) / 2 ≤ x ∧ x ≤ G.a i + G.ga / 2 + ((sLen D : ℚ) + 1) / 2 := by
    intro i h1 h2 x hx
    have e1 := block_bounds hx
    have e2 := abs_le.1 (hcen i h1 h2)
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
  have hspec := GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D C) (cen D C τ)
  have hbe : ∀ j (h : j < D.R.m), ((D.R.t : ℚ) + 3) / 2 ≤ G.e (j + 1) - G.b (j + 1) := fun j h => by
    have := (D.hc τ).gap_be ⟨j, h⟩
    rw [hspec.2.1 ⟨j, h⟩, hspec.2.2 ⟨j, h⟩] at this
    exact this
  have heb : ∀ j (h : j + 1 < D.R.m), ((D.R.t : ℚ) + 3) / 2 ≤ G.b (j + 2) - G.e (j + 1) := fun j h => by
    have := (D.hc τ).gap_eb ⟨j, by omega⟩ h
    rw [hspec.2.1 ⟨j + 1, h⟩, hspec.2.2 ⟨j, by omega⟩] at this
    exact this
  have hvle : ∀ i j, 2 ≤ i → i ≤ j → j ≤ D.R.k → G.v j ≤ G.v i := fun i j h1 h2 h3 => by
    rcases h2.eq_or_lt with rfl | h
    · exact le_rfl
    · exact (G.v_anti i j h1 h h3).le
  have hble : ∀ i j, 1 ≤ i → i ≤ j → j ≤ D.R.m → G.b i ≤ G.b j := fun i j h1 h2 h3 => by
    rcases h2.eq_or_lt with rfl | h
    · exact le_rfl
    · exact (G.b_mono i j h1 h h3).le
  have hvk : (-(G.b 1 : ℚ)) < G.v D.R.k - 1 / 2 := by
    have h1 := (D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩
    have h2 := (D.hc τ).u_last_gt (by omega) (by omega)
    have h3 : -(D.hc τ).b ⟨0, by omega⟩ < (D.hc τ).v ⟨D.R.k - 2, by omega⟩ := by
      refine h2.trans (lt_of_eq_of_lt ?_ h1)
      congr 1
      ext
      simp only
      omega
    rw [hspec.2.1 ⟨0, by omega⟩, hspec.1 ⟨D.R.k - 2, by omega⟩] at h3
    have h4 : -(G.b 1) < G.v D.R.k := by
      rw [show D.R.k - 2 + 2 = D.R.k by omega] at h3
      exact_mod_cast h3
    have h5 : ((-(G.b 1) + 1 : ℤ) : ℚ) ≤ G.v D.R.k := by exact_mod_cast h4
    push_cast at h5
    linarith
  refine ⟨fun l => ⟨G.v 2 + ((G.m : ℤ) + 1 - ((l : ℕ) : ℤ)) * G.ga, ?_⟩, fun i => ⟨G.v (i + 2) - 1, ?_⟩, ?_⟩
  · rw [hPa]; unfold GlobalTheory.SignedHC.GridData.a; push_cast; ring
  · rw [hPu]; unfold GlobalTheory.SignedHC.GridData.vHalf; push_cast; ring

  have bX : ∀ (i : Fin (rowSizes D).m), ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (P.c i) (rowSizes D).s ++ [P.a i.succ],
      G.a (i + 1) ≤ x ∧ x ≤ G.a (i + 1) + G.ga / 2 + ((sLen D : ℚ) + 1) / 2 := by
    intro i x hx
    have hi := i.2
    rw [List.mem_append, List.mem_singleton, hPc, hPa, hSs, Fin.val_succ] at hx
    rcases hx with hx | rfl
    · have := hC (i + 1) (by omega) (by omega) x hx
      constructor <;> linarith [this.1, this.2]
    · constructor
      · exact le_rfl
      · have : (0 : ℚ) ≤ G.ga := by positivity
        linarith
  have pX : (P.a 0 :: (List.finRange (rowSizes D).m).flatMap fun i =>
      GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (P.c i) (rowSizes D).s ++ [P.a i.succ]).Pairwise (· > ·) := by
    rw [List.pairwise_cons]
    constructor
    · intro x hx
      obtain ⟨i, -, hx⟩ := List.mem_flatMap.1 hx
      have h1 := (bX i x hx).2
      have h2 := a_add_le (G := G) (show 0 < (i : ℕ) + 1 by omega)
      rw [hPa]
      show x < G.a 0
      linarith
    · refine pairwise_flatMap_band _ (fun i => G.a (i + 1)) (fun i => G.a (i + 1) + G.ga / 2 + ((sLen D : ℚ) + 1) / 2)
        (fun i => ?_) bX (fun i j hij => ?_)
      · rw [List.pairwise_append]
        refine ⟨block_pairwise _ _, List.pairwise_singleton _ _, fun x hx y hy => ?_⟩
        rw [List.mem_singleton] at hy
        subst hy
        rw [hPc, hSs] at hx
        have := hC (i + 1) (by omega) (by omega) x hx
        rw [hPa, Fin.val_succ]
        show _ < _
        linarith [this.1]
      · have h := a_add_le (G := G) (show (i : ℕ) + 1 < j + 1 by have : (i : ℕ) < j := hij; omega)
        show _ < _
        linarith
  have tX : ∀ x ∈ (P.a 0 :: (List.finRange (rowSizes D).m).flatMap fun i =>
      GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (P.c i) (rowSizes D).s ++ [P.a i.succ]), G.a G.m ≤ x := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [hPa]; exact hle (by simp)
    · obtain ⟨i, -, hx⟩ := List.mem_flatMap.1 hx
      have := i.2
      exact (hle (show (i : ℕ) + 1 ≤ G.m by rw [hGm]; omega)).trans (bX i x hx).1

  have bY : ∀ (i : Fin ((rowSizes D).k - 1)), ∀ y ∈ [(P.v i : ℚ), P.u i],
      (G.v (i + 2) : ℚ) - 1 / 2 ≤ y ∧ y ≤ G.v (i + 2) := by
    intro i y hy
    rw [hPv, hPu] at hy
    unfold GlobalTheory.SignedHC.GridData.vHalf at hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl <;> constructor <;> linarith
  have pY : ((List.finRange ((rowSizes D).k - 1)).flatMap fun i => [(P.v i : ℚ), P.u i]).Pairwise (· > ·) := by
    refine pairwise_flatMap_band _ (fun i => (G.v (i + 2) : ℚ) - 1 / 2) (fun i => (G.v (i + 2) : ℚ)) (fun i => ?_) bY
      (fun i j hij => ?_)
    · refine List.Pairwise.cons (fun y hy => ?_) (List.pairwise_singleton _ _)
      rw [List.mem_singleton] at hy
      subst hy
      rw [hPv, hPu]
      unfold GlobalTheory.SignedHC.GridData.vHalf
      show _ < _
      linarith
    · have hj : (j : ℕ) < D.R.k - 1 := j.2
      have hij' : (i : ℕ) < j := hij
      have h := G.v_anti (i + 2) (j + 2) (by omega) (by omega) (by rw [hGk]; omega)
      have h' : ((G.v (j + 2) + 1 : ℤ) : ℚ) ≤ G.v (i + 2) := by exact_mod_cast h
      push_cast at h'
      show _ < _
      linarith
  have tY : ∀ y ∈ ((List.finRange ((rowSizes D).k - 1)).flatMap fun i => [(P.v i : ℚ), P.u i]),
      (G.v D.R.k : ℚ) - 1 / 2 ≤ y ∧ y ≤ G.v 2 := by
    intro y hy
    obtain ⟨i, -, hy⟩ := List.mem_flatMap.1 hy
    have hi : (i : ℕ) < D.R.k - 1 := i.2
    have h1 : ((G.v D.R.k : ℤ) : ℚ) ≤ G.v (i + 2) := by exact_mod_cast hvle (i + 2) D.R.k (by omega) (by omega) le_rfl
    have h2 : ((G.v (i + 2) : ℤ) : ℚ) ≤ G.v 2 := by exact_mod_cast hvle 2 (i + 2) le_rfl (by omega) (by omega)
    have := bY i y hy
    constructor <;> linarith [this.1, this.2]

  have bZ : ∀ (j : Fin (rowSizes D).m), ∀ z ∈ ((-P.b j : ℚ) :: GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (-P.e j) (rowSizes D).t),
      -(G.e (j + 1) : ℚ) - ((D.R.t : ℚ) - 1) / 2 ≤ z ∧ z ≤ -(G.b (j + 1) : ℚ) := by
    intro j z hz
    have hj : (j : ℕ) < D.R.m := j.2
    have h1 := hbe j hj
    rw [List.mem_cons, hPb, hPe, hSt] at hz
    rcases hz with rfl | hz
    · constructor <;> linarith
    · have := block_bounds hz
      constructor <;> linarith [this.1, this.2]
  have pZ : ((List.finRange (rowSizes D).m).flatMap fun j =>
      (-P.b j : ℚ) :: GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (-P.e j) (rowSizes D).t).Pairwise (· > ·) := by
    refine pairwise_flatMap_band _ (fun j => -(G.e (j + 1) : ℚ) - ((D.R.t : ℚ) - 1) / 2) (fun j => -(G.b (j + 1) : ℚ))
      (fun j => ?_) bZ (fun i j hij => ?_)
    · have hj : (j : ℕ) < D.R.m := j.2
      have h1 := hbe j hj
      rw [List.pairwise_cons]
      refine ⟨fun z hz => ?_, block_pairwise _ _⟩
      rw [hPb, hPe, hSt] at *
      have := block_bounds hz
      show _ < _
      linarith [this.2]
    · have hj : (j : ℕ) < D.R.m := j.2
      have hij' : (i : ℕ) < j := hij
      have h1 := heb i (by omega)
      have h2 : ((G.b (i + 2) : ℤ) : ℚ) ≤ G.b (j + 1) := by exact_mod_cast hble (i + 2) (j + 1) (by omega) (by omega) (by omega)
      show _ < _
      linarith
  have tZ : ∀ z ∈ ((List.finRange (rowSizes D).m).flatMap fun j =>
      (-P.b j : ℚ) :: GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (-P.e j) (rowSizes D).t), z ≤ -(G.b 1 : ℚ) := by
    intro z hz
    obtain ⟨j, -, hz⟩ := List.mem_flatMap.1 hz
    have hj : (j : ℕ) < D.R.m := j.2
    have h1 : ((G.b 1 : ℤ) : ℚ) ≤ G.b (j + 1) := by exact_mod_cast hble 1 (j + 1) le_rfl (by omega) (by omega)
    linarith [(bZ j z hz).2]

  have hv2 : (G.v 2 : ℚ) < G.a G.m := by
    rw [G.a_m]
    have : (0 : ℚ) ≤ G.ga := by positivity
    linarith
  show (Entries.orderList P).Pairwise (· > ·)
  rw [Entries.orderList, List.pairwise_append, List.pairwise_append]
  refine ⟨⟨pX, pY, fun x hx y hy => ?_⟩, pZ, fun x hx z hz => ?_⟩
  · have h1 := tX x hx
    have h2 := (tY y hy).2
    show _ < _
    linarith
  · have h3 := tZ z hz
    show _ < _
    rcases List.mem_append.1 hx with hx | hx
    · have h1 := tX x hx
      have h2 := tY _ (List.mem_flatMap.2 ⟨⟨0, by rw [hSk]; omega⟩, List.mem_finRange _, List.mem_cons_self⟩)
      linarith [h2.1, h2.2]
    · have h1 := (tY x hx).1
      linarith

end GlobalTheory.RowReal

import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepJacquetWordMultiplicityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalCellMultiplicityZeroOfSplitColumnStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalCellMultiplicityOfColouringStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiExteriorTensorSmoothIrreducibleIsIrreducibleStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineProd

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons a l ih`. Distinguish the cases in `hp : p a`. Simplify using `[List.filter_cons, hp, ih]`.

Simplify using `[List.filter_cons, hp, ih]`.
-/
theorem sum_map_filter {β : Type*} (p : β → Prop) [DecidablePred p] (f : β → ℕ) (l : List β) :
    ((l.filter fun a => decide (p a)).map f).sum = (l.map fun j => if p j then f j else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hp : p a
    · simp [List.filter_cons, hp, ih]
    · simp [List.filter_cons, hp, ih]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `show ((List.map W.get (List.filter (fun p => decide (c p = i)) (List.finRange W.length))).map Sigma.fst).sum = _`. Rewrite using `[List.map_map, Fin.sum_univ_def]`. Conclude with `sum_map_filter (fun p => c p = i) (fun p => (W.get p).1) (List.finRange W.length)`.
-/
theorem deg_sub {h : ℕ} (W : List (IrrGL k)) (c : Fin W.length → Fin h) (i : Fin h) :
    ((sub W c i).map Sigma.fst).sum = ∑ j, if c j = i then (W.get j).1 else 0 := by
  show ((List.map W.get (List.filter (fun p => decide (c p = i)) (List.finRange W.length))).map
    Sigma.fst).sum = _
  rw [List.map_map, Fin.sum_univ_def]
  exact sum_map_filter (fun p => c p = i) (fun p => (W.get p).1) (List.finRange W.length)

/- English proof (translation)
Establish `h : ∀ a, (Γ.term a).1 = Γ.d` using `fun a => rfl`. Use `show ((List.ofFn Γ.term).reverse.map Sigma.fst).sum = Γ.len * Γ.d`. Rewrite using `[List.map_reverse, List.sum_reverse, List.map_ofFn, List.sum_ofFn]`. Simplify using `only [Function.comp_def, h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`.
-/
theorem deg_decWord (Γ : Segment k) : ((decWord Γ).map Sigma.fst).sum = Γ.deg := by
  have h : ∀ a, (Γ.term a).1 = Γ.d := fun a => rfl
  show ((List.ofFn Γ.term).reverse.map Sigma.fst).sum = Γ.len * Γ.d
  rw [List.map_reverse, List.sum_reverse, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_def, h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

def colourMat {h : ℕ} (W : List (IrrGL k)) (c : Fin W.length → Fin h) (i : Fin h) (j : Fin W.length) : ℕ :=
  if c j = i then (W.get j).1 else 0

/- English proof (translation)
Simplify using `[colourMat]`.
-/
theorem sum_colourMat {h : ℕ} (W : List (IrrGL k)) (c : Fin W.length → Fin h) (j : Fin W.length) :
    ∑ i, colourMat W c i j = (W.get j).1 := by
  simp [colourMat]

end GlobalTheory.CompanionTheory.FineProd

open GlobalTheory.CompanionTheory.FineProd in

/- English proof (translation)
Introduce `k _ _ _ _ hA hJ h N Γ x hd hΓ W hW`. Establish `hΓd : ∀ i, ((decWord (Γ i)).map Sigma.fst).sum = (x i).1` using `fun i => (deg_decWord _).trans (hΓ i).deg_eq`. Set `S : Finset (Fin W.length → Fin h)` to `Finset.univ.filter fun c => ∀ i, sub W c i = decWord (Γ i)`. Establish `hcount : shuffleCount W (fun i => decWord (Γ i)) = S.card`. Unfold `shuffleCount`.

Reduce the equality to equality of the corresponding arguments. Establish `hrowS : ∀ c ∈ S, ∀ i, ∑ j, colourMat W c i j = (x i).1` using `fun c hc i => by`. Establish `h1` using `(Finset.mem_filter.1 hc).2 i`. Establish `h2` using `deg_sub W c i`. Rewrite `h2` using `[h1, hΓd]`.

Conclude with `h2.symm`. Establish `hSdeg : ∀ c ∈ S, ∑ a, (W.get a).1 = N` using `fun c hc => by`. Rewrite using `[← hd, ← Finset.sum_congr rfl fun i _ => hrowS c hc i, Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun j _ => (sum_colourMat W c j).symm`. Establish `hpos : ∀ j, 0 < (W.get j).1` using `fun j => (hW _ (List.get_mem _ _)).1`.

Rewrite using `[hcount]`. Distinguish the cases in `hWd : ∑ a, (W.get a).1 = N`. Use `swap`. Establish `hSe : S = ∅` using `Finset.eq_empty_of_forall_notMem fun c hc => hWd (hSdeg c hc)`. Rewrite using `[hSe, jmL, dif_neg hWd]`.

Simplify using the standard rewrite rules. Set `m : Fin h → Type` to `fun i => Fin (x i).1`. Set `m' : Fin W.length → Type` to `fun j => Fin (W.get j).1`. Use `haveI : Fintype (SizeMatrix m m') := Fintype.ofFinite _`. Establish `hr : ∀ (b : SizeMatrix m m') i, ∑ j, b.1 i j = (x i).1` using `fun b i => by`.

Simplify `b.2.1 i` using `[m]`. Establish `hc : ∀ (b : SizeMatrix m m') j, ∑ i, b.1 i j = (W.get j).1` using `fun b j => by`. Simplify `b.2.2 j` using `[m']`. Establish `hτ : (piTensor fun j => (W.get j).rep).IsIrreducible` using `GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k _ _ fun j => (W.get j).2.rep`. Establish `key` using `((GlobalTheory.CompanionTheory.GeoLink.geometricLemma k).1).jhMult_eq (m := m) (m' := m') (stdBlocks (fun a => (x a).1) hd) (stdBlocks (fun a => (W.get a).1) hWd) (isSmooth_piTensor fun i => (x i).2.rep.smooth) (fun b i => stdBlocks (b.1 i) (hr b i)) (fun b j => stdBlocks (fun i …`.

Establish `hF : ∀ b : SizeMatrix m m', jhMult (piTensor fun j => (W.get j).rep) (cellFunctor (c` using `fun i j => Fin (b.1 i j)) (fun i => stdBlocks (b.1 i) (hr b i)) (fun j => stdBlocks (fun i => b.1 i j) (hc b j)) (piTensor fun i => (x i).rep)) = if ∃ c ∈ S, b.1 = colourMat W c then 1 else 0 := by`. Introduce `b`. Use `split_ifs with hb`. Take `⟨c, hcS, hbc⟩` from `hb`. Rewrite using `[GlobalTheory.T.cuspidal_cell_multiplicity_of_colouring x W b.1 (hr b) (hc b) c (fun i j => by rw [hbc]; rfl)]`.

Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Use `((GlobalTheory.T.segment_rep_jacquet_word_multiplicity hA hJ (Γ i) (x i).rep (hΓ i) (sub W c i) fun w hw => ?_).1 ((Finset.mem_filter.1 hcS).2 i))` and prove the remaining obligations. Take `⟨p, -, rfl⟩` from `List.mem_map.1 hw`. Conclude with `hW _ (List.get_mem _ _)`. Distinguish the cases in `hm : ∃ (j : Fin W.length) (i i' : Fin h), i ≠ i' ∧ b.1 i j ≠ 0 ∧ b.1 i' j ≠ 0`.

Take `⟨j, i, i', hii, h1, h2⟩` from `hm`. Conclude with `GlobalTheory.T.cuspidal_cell_multiplicity_zero_of_split_column hA x (fun j => W.get j) (fun j => hW _ (List.get_mem _ _)) b.1 (hr b) (hc b) j i i' hii h1 h2`. Use `push_neg at hm`. Establish `hex : ∀ j, ∃ i, b.1 i j ≠ 0` using `fun j => by`. Assume the negation of the conclusion as `hne`.

Use `push_neg at hne`. Use `hc b j` as an intermediate fact. Rewrite `this` using `[Finset.sum_eq_zero fun i _ => hne i]`. Conclude with `(hpos j).ne this`. Use `choose c hcj using hex`.

Establish `hzero : ∀ i j, c j ≠ i → b.1 i j = 0` using `fun i j hij => by`. Assume the negation of the conclusion as `hne`. Conclude with `hne (hm j (c j) i hij (hcj j))`. Establish `hbc : b.1 = colourMat W c`. Use function extensionality and compare the values at `i j`.

Unfold `colourMat`. Use `split_ifs with hij`. Substitute `hij` using the available equality. Rewrite using `[← hc b j]`. Conclude with `(Finset.sum_eq_single (c j) (fun i _ hi => hzero i j (Ne.symm hi)) (by simp)).symm`.

Conclude with `hzero i j hij`. Establish `hcS : c ∉ S` using `fun hcS => hb ⟨c, hcS, hbc⟩`. Establish `hex2 : ∃ i, sub W c i ≠ decWord (Γ i)`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`.

Conclude with `hcS (Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩)`. Take `⟨i, hi⟩` from `hex2`. Rewrite using `[GlobalTheory.T.cuspidal_cell_multiplicity_of_colouring x W b.1 (hr b) (hc b) c (fun i j => by rw [hbc]; rfl)]`. Use `Finset.prod_eq_zero (Finset.mem_univ i) ?_` and prove the remaining obligations. Use `(GlobalTheory.T.segment_rep_jacquet_word_multiplicity hA hJ (Γ i) (x i).rep (hΓ i) (sub W c i) (fun w hw => ?_)).2 hi` and prove the remaining obligations.

Take `⟨p, -, rfl⟩` from `List.mem_map.1 hw`. Conclude with `hW _ (List.get_mem _ _)`. Rewrite using `[jmL, dif_pos hWd]`. Use `Eq.trans key ?_` and prove the remaining obligations. Establish `hcard : (Finset.univ.filter fun b : SizeMatrix m m' => ∃ c ∈ S, b.1 = colourMat W c).card = S.card`.

Use `symm`. Set `mk : ∀ c, c ∈ S → SizeMatrix m m'` to `fun c hc => ⟨colourMat W c, fun i => by simpa [m] using hrowS c hc i, fun j => by simpa [m'] using sum_colourMat W c j⟩`. Use `Finset.card_bij mk (fun c hc => Finset.mem_filter.2 ⟨Finset.mem_univ _, c, hc, rfl⟩) ?_ ?_` and prove the remaining obligations. Introduce `c hc c' hc' he`. Use function extensionality and compare the values at `j`.

Establish `h1 : colourMat W c (c j) j = colourMat W c' (c j) j` using `congrFun (congrFun (congrArg Subtype.val he) (c j)) j`. Assume the negation of the conclusion as `hne`. Establish `h2 : c' j ≠ c j` using `fun e => hne e.symm`. Simplify using `only [colourMat, if_true, if_neg h2] at h1`. Conclude with `(hpos j).ne' h1`.

Introduce `b hb`. Take `⟨c, hc, hbc⟩` from `(Finset.mem_filter.1 hb).2`. Conclude with `⟨c, hc, Subtype.ext hbc.symm⟩`. Rewrite using `[Finset.sum_congr rfl fun b _ => hF b, Finset.sum_boole, hcard]`.
-/
theorem GlobalTheory.CompanionTheory.FineProd.jmL_prodIrr : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → ∀ {h N : ℕ} (Γ : Fin h → Segment k) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), (∀ i, IsLSeg (Γ i) (x i).rep) → ∀ W : List (IrrGL k), (∀ w ∈ W, w.IsCusp) → jmL W (prodIrr x hd) = (shuffleCount W (fun i => decWord (Γ i)) : ℕ∞) := by
  intro k _ _ _ _ hA hJ h N Γ x hd hΓ W hW
  classical
  have hΓd : ∀ i, ((decWord (Γ i)).map Sigma.fst).sum = (x i).1 := fun i =>
    (deg_decWord _).trans (hΓ i).deg_eq
  let S : Finset (Fin W.length → Fin h) := Finset.univ.filter fun c => ∀ i, sub W c i = decWord (Γ i)
  have hcount : shuffleCount W (fun i => decWord (Γ i)) = S.card := by
    unfold shuffleCount
    congr
  have hrowS : ∀ c ∈ S, ∀ i, ∑ j, colourMat W c i j = (x i).1 := fun c hc i => by
    have h1 := (Finset.mem_filter.1 hc).2 i
    have h2 := deg_sub W c i
    rw [h1, hΓd] at h2
    exact h2.symm
  have hSdeg : ∀ c ∈ S, ∑ a, (W.get a).1 = N := fun c hc => by
    rw [← hd, ← Finset.sum_congr rfl fun i _ => hrowS c hc i, Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => (sum_colourMat W c j).symm
  have hpos : ∀ j, 0 < (W.get j).1 := fun j => (hW _ (List.get_mem _ _)).1
  rw [hcount]
  by_cases hWd : ∑ a, (W.get a).1 = N
  swap
  · have hSe : S = ∅ := Finset.eq_empty_of_forall_notMem fun c hc => hWd (hSdeg c hc)
    rw [hSe, jmL, dif_neg hWd]
    simp
  let m : Fin h → Type := fun i => Fin (x i).1
  let m' : Fin W.length → Type := fun j => Fin (W.get j).1
  haveI : Fintype (SizeMatrix m m') := Fintype.ofFinite _
  have hr : ∀ (b : SizeMatrix m m') i, ∑ j, b.1 i j = (x i).1 := fun b i => by
    simpa [m] using b.2.1 i
  have hc : ∀ (b : SizeMatrix m m') j, ∑ i, b.1 i j = (W.get j).1 := fun b j => by
    simpa [m'] using b.2.2 j
  have hτ : (piTensor fun j => (W.get j).rep).IsIrreducible :=
    GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k _ _ fun j => (W.get j).2.rep
  have key := ((GlobalTheory.CompanionTheory.GeoLink.geometricLemma k).1).jhMult_eq (m := m) (m' := m')
    (stdBlocks (fun a => (x a).1) hd) (stdBlocks (fun a => (W.get a).1) hWd)
    (isSmooth_piTensor fun i => (x i).2.rep.smooth)
    (fun b i => stdBlocks (b.1 i) (hr b i)) (fun b j => stdBlocks (fun i => b.1 i j) (hc b j)) hτ
  have hF : ∀ b : SizeMatrix m m', jhMult (piTensor fun j => (W.get j).rep)
      (cellFunctor (c := fun i j => Fin (b.1 i j)) (fun i => stdBlocks (b.1 i) (hr b i))
        (fun j => stdBlocks (fun i => b.1 i j) (hc b j)) (piTensor fun i => (x i).rep)) =
      if ∃ c ∈ S, b.1 = colourMat W c then 1 else 0 := by
    intro b
    split_ifs with hb
    · obtain ⟨c, hcS, hbc⟩ := hb
      rw [GlobalTheory.T.cuspidal_cell_multiplicity_of_colouring x W b.1 (hr b) (hc b) c (fun i j => by rw [hbc]; rfl)]
      refine Finset.prod_eq_one fun i _ => ?_
      refine ((GlobalTheory.T.segment_rep_jacquet_word_multiplicity hA hJ (Γ i) (x i).rep (hΓ i) (sub W c i) fun w hw => ?_).1
        ((Finset.mem_filter.1 hcS).2 i))
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hw
      exact hW _ (List.get_mem _ _)
    · by_cases hm : ∃ (j : Fin W.length) (i i' : Fin h), i ≠ i' ∧ b.1 i j ≠ 0 ∧ b.1 i' j ≠ 0
      · obtain ⟨j, i, i', hii, h1, h2⟩ := hm
        exact GlobalTheory.T.cuspidal_cell_multiplicity_zero_of_split_column hA x (fun j => W.get j) (fun j => hW _ (List.get_mem _ _)) b.1 (hr b) (hc b) j i i' hii h1 h2
      · push_neg at hm
        have hex : ∀ j, ∃ i, b.1 i j ≠ 0 := fun j => by
          by_contra hne
          push_neg at hne
          have := hc b j
          rw [Finset.sum_eq_zero fun i _ => hne i] at this
          exact (hpos j).ne this
        choose c hcj using hex
        have hzero : ∀ i j, c j ≠ i → b.1 i j = 0 := fun i j hij => by
          by_contra hne
          exact hne (hm j (c j) i hij (hcj j))
        have hbc : b.1 = colourMat W c := by
          funext i j
          unfold colourMat
          split_ifs with hij
          · subst hij
            rw [← hc b j]
            exact (Finset.sum_eq_single (c j) (fun i _ hi => hzero i j (Ne.symm hi)) (by simp)).symm
          · exact hzero i j hij
        have hcS : c ∉ S := fun hcS => hb ⟨c, hcS, hbc⟩
        have hex2 : ∃ i, sub W c i ≠ decWord (Γ i) := by
          by_contra hne
          push_neg at hne
          exact hcS (Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩)
        obtain ⟨i, hi⟩ := hex2
        rw [GlobalTheory.T.cuspidal_cell_multiplicity_of_colouring x W b.1 (hr b) (hc b) c (fun i j => by rw [hbc]; rfl)]
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        refine (GlobalTheory.T.segment_rep_jacquet_word_multiplicity hA hJ (Γ i) (x i).rep (hΓ i) (sub W c i) (fun w hw => ?_)).2 hi
        obtain ⟨p, -, rfl⟩ := List.mem_map.1 hw
        exact hW _ (List.get_mem _ _)
  rw [jmL, dif_pos hWd]
  refine Eq.trans key ?_
  have hcard : (Finset.univ.filter fun b : SizeMatrix m m' => ∃ c ∈ S, b.1 = colourMat W c).card = S.card := by
    symm
    let mk : ∀ c, c ∈ S → SizeMatrix m m' := fun c hc =>
      ⟨colourMat W c, fun i => by simpa [m] using hrowS c hc i, fun j => by simpa [m'] using sum_colourMat W c j⟩
    refine Finset.card_bij mk (fun c hc => Finset.mem_filter.2 ⟨Finset.mem_univ _, c, hc, rfl⟩) ?_ ?_
    · intro c hc c' hc' he
      funext j
      have h1 : colourMat W c (c j) j = colourMat W c' (c j) j :=
        congrFun (congrFun (congrArg Subtype.val he) (c j)) j
      by_contra hne
      have h2 : c' j ≠ c j := fun e => hne e.symm
      simp only [colourMat, if_true, if_neg h2] at h1
      exact (hpos j).ne' h1
    · intro b hb
      obtain ⟨c, hc, hbc⟩ := (Finset.mem_filter.1 hb).2
      exact ⟨c, hc, Subtype.ext hbc.symm⟩
  rw [Finset.sum_congr rfl fun b _ => hF b, Finset.sum_boole, hcard]

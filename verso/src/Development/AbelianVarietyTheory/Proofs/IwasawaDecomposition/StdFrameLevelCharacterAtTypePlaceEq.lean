import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdMaximalCompactReductionPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.DIV

namespace GlobalTheory.MtChr

/- English proof (translation)
Use `Fintype.sum_of_injective (Fin.castLE hr) (Fin.castLE_injective hr) _ _ ?_ ?_` and prove the remaining obligations. Introduce `a ha`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg]`. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `ha ⟨⟨a.val, by omega⟩, Fin.ext rfl⟩`. Introduce `i`. Use `Fintype.sum_of_injective (Fin.castLE hr) (Fin.castLE_injective hr) _ _ ?_ ?_` and prove the remaining obligations. Introduce `b hb`. Rewrite using `[if_neg]`.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `hb ⟨⟨b.val, h2⟩, Fin.ext rfl⟩`. Introduce `j`. Distinguish the cases in `hh : supEdge i j`. Establish `h' : j.val = i.val + 1` using `hh`.

Rewrite using `[if_pos hh, if_pos (by simp only [Fin.val_castLE]; exact ⟨h'.symm, j.2⟩)]`. Establish `h' : ¬ j.val = i.val + 1` using `hh`. Rewrite using `[if_neg hh, if_neg (by simp only [Fin.val_castLE]; exact fun e => h' e.1.symm)]`.
-/
theorem sum_supEdge_castLE {R : Type} [AddCommMonoid R] {n r : ℕ} (hr : r ≤ n) (f : Fin n → Fin n → R) :
    (∑ i : Fin r, ∑ j : Fin r, if supEdge i j then f (Fin.castLE hr i) (Fin.castLE hr j) else 0) =
      ∑ a : Fin n, ∑ b : Fin n, if a.val + 1 = b.val ∧ b.val < r then f a b else 0 := by
  refine Fintype.sum_of_injective (Fin.castLE hr) (Fin.castLE_injective hr) _ _ ?_ ?_
  · intro a ha
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact ha ⟨⟨a.val, by omega⟩, Fin.ext rfl⟩
  · intro i
    refine Fintype.sum_of_injective (Fin.castLE hr) (Fin.castLE_injective hr) _ _ ?_ ?_
    · intro b hb
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hb ⟨⟨b.val, h2⟩, Fin.ext rfl⟩
    · intro j
      by_cases hh : supEdge i j
      · have h' : j.val = i.val + 1 := hh
        rw [if_pos hh, if_pos (by simp only [Fin.val_castLE]; exact ⟨h'.symm, j.2⟩)]
      · have h' : ¬ j.val = i.val + 1 := hh
        rw [if_neg hh, if_neg (by simp only [Fin.val_castLE]; exact fun e => h' e.1.symm)]

/- English proof (translation)
Unfold `blkOf`. Distinguish the cases in `h : a.val < r`. Simplify using `only [h, if_true]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [h, if_false]`.

Rewrite using `[Nat.div_eq_of_lt (by omega)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem blkOf_eq_one_iff {n r t : ℕ} (a : Fin n) (ha : a.val < r + t) : blkOf r t a = 1 ↔ r ≤ a.val := by
  unfold blkOf
  by_cases h : a.val < r
  · simp only [h, if_true]; omega
  · simp only [h, if_false]
    rw [Nat.div_eq_of_lt (by omega)]
    omega

/- English proof (translation)
Unfold `edgeSum`. Use `Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Use `split_ifs with hh`. Rewrite using `[Units.val_one, Matrix.one_apply_ne]`. Introduce `e`.

Rewrite `hh` using `[e]`. Unfold `supEdge at hh`. Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression.
-/
theorem edgeSum_supEdge_one {κ : Type} [CommRing κ] {r : ℕ} : edgeSum (κ := κ) (supEdge (r := r)) 1 = 0 := by
  unfold edgeSum
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with hh
  · rw [Units.val_one, Matrix.one_apply_ne]
    intro e; rw [e] at hh; unfold supEdge at hh; omega
  · rfl

/- English proof (translation)
Rewrite using `[RingHom.map_det]`. Rewrite using `[← Matrix.det_submatrix_equiv_self (Equiv.subtypeEquivRight hpq) (φ.mapMatrix _)]`. Use `congr 1`. Use extensionality with `a b`. Conclude with `(hMN a.1 b.1).symm`.
-/
theorem det_map_subtype {O k : Type} [CommRing O] [CommRing k] (φ : O →+* k) {n : ℕ} (M : Matrix (Fin n) (Fin n) O)
    (N : Matrix (Fin n) (Fin n) k) (hMN : ∀ a b, N a b = φ (M a b)) (p q : Fin n → Prop) [DecidablePred p] [DecidablePred q]
    (hpq : ∀ a, p a ↔ q a) :
    φ (Matrix.of fun a b : {y // q y} => M a.1 b.1).det = (N.submatrix (Subtype.val : {a // p a} → Fin n) Subtype.val).det := by
  rw [RingHom.map_det]
  rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeEquivRight hpq) (φ.mapMatrix _)]
  congr 1
  ext a b
  exact (hMN a.1 b.1).symm

end GlobalTheory.MtChr

set_option maxHeartbeats 2000000 in
/- English proof (translation)
Introduce `D hr Pg Q ψ chi xi s φ hφ0 hred hsw hPg hQ ψ₀ ξ hψ₀ hξ κ h htriv u hu`. Use `set Ld := GlobalTheory.MtIn.datV D D.R.nV hr Pg Q (P0 Pg D.R.r ψ) chi xi`. Use `set x := km D D.R.nV κ`. Establish `hL : x ∈ lev D.sp.cm 1 1 Ld` using `h`. Establish `hpar : x ∈ parLev D.sp.cm 1 1 Ld` using `hL.1`.

Establish `hP0 : rTup 1 Ld x ∈ (P0 Pg D.R.r ψ).conj.H` using `hL.2`. Take `⟨-, hStU, hout, -⟩` from `GlobalTheory.T.stdMaximalCompact_reduction_properties D D.R.nV`. Establish `hU : κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV` using `(hStU κ).1 (parLev_St hpar)`. Establish `hg : ∀ PP ∈ Pg, redFn 1 PP x ∈ blockTri (blkOf D.R.r D.R.t)` using `fun PP hP => parLev_g hpar hP`. Establish `triv : ∀ PP : Pl D.host.E, ¬ NG.OverPl PP s.v → redFn 1 PP x = 1`.

Introduce `PP hn`. Use `hout κ hU {s.v} (PP.under (𝓞 (maximalRealSubfield D.host.E))) PP htriv rfl ?_` and prove the remaining obligations. Introduce `hv`. Rewrite `hv` using `[Set.mem_singleton_iff]`. Conclude with `hn (hv ▸ rfl)`.

Use `choose hint hredv using hred κ hU`. Set `ι` to `(s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).subtype`. Set `M' : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E))` to `fun a b => ⟨_, hint a b⟩`. Set `Sn : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)` to `∑ a : Fin D.R.nV, ∑ b : Fin D.R.nV, if a.val + 1 = b.val ∧ b.val < D.R.r then M' a b else 0`. Establish `hSn : (Sn : s.v.adicCompletion (maximalRealSubfield D.host.E)) = NG.supDiag s D.R.r (s.loc D.R.nV κ)` using `by show ι Sn = _`.

Simplify using `only [Sn, map_sum]`. Unfold `NG.supDiag`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Use `split_ifs`. Both sides reduce to the same expression.

Conclude with `map_zero ι`. Establish `hφSn : φ Sn = edgeSum supEdge (upperLeftBlock hr (redFn 1 s.w x))`. Unfold `edgeSum`. Rewrite using `[upper_block_val_submatrix hr (blockTri_blkOf_le _ _ (hg s.w hsw))]`. Simplify using `only [Matrix.submatrix_apply]`.

Use `Eq.trans ?_ (GlobalTheory.MtChr.sum_supEdge_castLE hr (fun a b => (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w x).val a b)).symm` and prove the remaining obligations. Simplify using `only [Sn, map_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `(hredv a b).symm`.

Conclude with `map_zero φ`. Set `Md : Matrix {y : Fin D.R.nV // D.R.r ≤ y.val} {y : Fin D.R.nV // D.R.r ≤ y.val} (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E))` to `fun a b => M' a.1 b.1`. Establish `hdet : (Md.det : s.v.adicCompletion (maximalRealSubfield D.host.E)) = (u : s.v.adicCompletion (maximalRealSubfield D.host.E))`. Rewrite using `[hu]`. Use `show ι Md.det = _`.

Rewrite using `[RingHom.map_det]`. Unfold `NG.detDD`. Both sides reduce to the same expression. Establish `hφdet' : φ Md.det = (((redFn 1 s.w x).val).submatrix (Subtype.val : {a : Fin D.R.nV // blkOf D.R.r D.R.t a = 1} → Fin D.R.nV) Subtype.val).det` using `GlobalTheory.MtChr.det_map_subtype φ M' _ hredv _ _ (fun a => GlobalTheory.MtChr.blkOf_eq_one_iff a (lt_of_lt_of_eq a.2 rfl))`. Establish `hφdet : φ Md.det = ((dBlk (blkOf D.R.r D.R.t) 1 (redFn 1 s.w x) : (kP s.w)ˣ) : kP s.w)` using `hφdet'.trans (diag_block_det_val 1 (hg s.w hsw)).symm`.

Establish `hξu` using `hξ u Md.det _ hdet hφdet`. Establish `hA : ((ext1 (P0 Pg D.R.r ψ).conj.H (P0 Pg D.R.r ψ).conj.chi (rTup 1 Ld x) : ℂˣ) : ℂ) = (ψ s.w (edgeSum supEdge (upperLeftBlock hr (redFn 1 s.w x))))⁻¹` using `by erw [extendOne_of_mem _ hP0] show (((P0 Pg D.R.r ψ).chi⁻¹ ⟨_, hP0⟩ : ℂˣ) : ℂ) = _`. Rewrite using `[MonoidHom.inv_apply, Units.val_inv_eq_inv_val]`. Use `congr 1`. Use `show (((∏ PP : ↥Pg, (addCharHom (ψ PP.1) (supHom (kP PP.1) D.R.r)).comp (LevelP.prj _ PP)) ⟨_, hP0⟩ : ℂˣ) : ℂ) = _`.

Rewrite using `[MonoidHom.finsetProd_apply, Fintype.prod_eq_single ⟨s.w, hsw⟩]`. Both sides reduce to the same expression. Introduce `PP hne`. Apply `Units.ext` to reduce the goal to its premises. Use `show ψ PP.1 (edgeSum supEdge (upperLeftBlock hr (redFn 1 PP.1 x))) = 1`.

Rewrite using `[triv PP.1 (hPg PP.1 PP.2 (fun e => hne (Subtype.ext e)))]`. Unfold `upperLeftBlock`. Rewrite using `[blockDiagonalExtendByOnePrimeField_one, GlobalTheory.MtChr.edgeSum_supEdge_one, AddChar.map_zero_eq_one]`. Establish `hB : (∏ PP ∈ Pg, ∏ c ∈ Finset.range 1, (chi PP)⁻¹ (dBlk (blkOf D.R.r D.R.t) (c + 1) (redFn 1 PP x))) = (chi s.w)⁻¹ (dBlk (blkOf D.R.r D.R.t) 1 (redFn 1 s.w x))`. Rewrite using `[Finset.prod_eq_single_of_mem s.w hsw]`.

Rewrite using `[Finset.prod_range_one]`. Introduce `PP hP hne`. Rewrite using `[Finset.prod_range_one, triv PP (hPg PP hP hne)]`. Unfold `dBlk`. Rewrite using `[blockDiagonalExtendByOnePrimeField_one, map_one]`.

Establish `hC : (∏ PP ∈ Q, xi PP (dBlk (blk2 D.R.r) 1 (redFn 1 PP x))) = 1`. Use `Finset.prod_eq_one fun PP hP => ?_` and prove the remaining obligations. Rewrite using `[triv PP (hQ PP hP)]`. Unfold `dBlk`. Rewrite using `[blockDiagonalExtendByOnePrimeField_one, map_one]`.

Use `show ((ext1 (P0 Pg D.R.r ψ).conj.H (P0 Pg D.R.r ψ).conj.chi (rTup 1 Ld x) * (∏ PP ∈ Pg, ∏ c ∈ Finset.range 1, (chi PP)⁻¹ (dBlk (blkOf D.R.r D.R.t) (c + 1) (redFn 1 PP x))) * ∏ PP ∈ Q, xi PP (dBlk (blk2 D.R.r) 1 (redFn 1 PP x)) : ℂˣ) : ℂ) = _`. Rewrite using `[hB, hC, mul_one, Units.val_mul, hA, hξu, ← hSn, hψ₀, AddChar.map_neg_eq_inv, hφSn]`.
-/
theorem GlobalTheory.MtChr.levChar_std_uni : ∀ (D : D7) (hr : D.R.r ≤ D.R.nV) (Pg Q : Finset (Pl D.host.E)) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* kP s.w), (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1) → (∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV, ∀ a b, ∃ h : (s.loc D.R.nV κ).val a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)).val a b = φ ⟨_, h⟩) → s.w ∈ Pg → (∀ PP ∈ Pg, PP ≠ s.w → ¬ NG.OverPl PP s.v) → (∀ PP ∈ Q, ¬ NG.OverPl PP s.v) → ∀ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), (∀ x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), ψ₀ (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) = ψ s.w (-φ x)) → (∀ (u : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ) (x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) (w : (kP s.w)ˣ), (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) = u → φ x = w → ξ u = (chi s.w)⁻¹ w) → ∀ κ (h : κ ∈ stdJ (datV D D.R.nV hr Pg Q (P0 Pg D.R.r ψ) chi xi)), ReciprocityTheory.Aut.TrivOutside {s.v} κ → ∀ u : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ, (u : s.v.adicCompletion (maximalRealSubfield D.host.E)) = NG.detDD s D.R.r (s.loc D.R.nV κ) → ((stdX (datV D D.R.nV hr Pg Q (P0 Pg D.R.r ψ) chi xi) ⟨κ, h⟩ : ℂˣ) : ℂ) = ψ₀ (NG.supDiag s D.R.r (s.loc D.R.nV κ)) * ξ u := by
  intro D hr Pg Q ψ chi xi s φ hφ0 hred hsw hPg hQ ψ₀ ξ hψ₀ hξ κ h htriv u hu
  set Ld := GlobalTheory.MtIn.datV D D.R.nV hr Pg Q (P0 Pg D.R.r ψ) chi xi
  set x := km D D.R.nV κ
  have hL : x ∈ lev D.sp.cm 1 1 Ld := h
  have hpar : x ∈ parLev D.sp.cm 1 1 Ld := hL.1
  have hP0 : rTup 1 Ld x ∈ (P0 Pg D.R.r ψ).conj.H := hL.2
  obtain ⟨-, hStU, hout, -⟩ := GlobalTheory.T.stdMaximalCompact_reduction_properties D D.R.nV
  have hU : κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV := (hStU κ).1 (parLev_St hpar)
  have hg : ∀ PP ∈ Pg, redFn 1 PP x ∈ blockTri (blkOf D.R.r D.R.t) := fun PP hP => parLev_g hpar hP
  have triv : ∀ PP : Pl D.host.E, ¬ NG.OverPl PP s.v → redFn 1 PP x = 1 := by
    intro PP hn
    refine hout κ hU {s.v} (PP.under (𝓞 (maximalRealSubfield D.host.E))) PP htriv rfl ?_
    intro hv
    rw [Set.mem_singleton_iff] at hv
    exact hn (hv ▸ rfl)
  choose hint hredv using hred κ hU
  let ι := (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).subtype
  let M' : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) :=
    fun a b => ⟨_, hint a b⟩

  let Sn : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) :=
    ∑ a : Fin D.R.nV, ∑ b : Fin D.R.nV, if a.val + 1 = b.val ∧ b.val < D.R.r then M' a b else 0
  have hSn : (Sn : s.v.adicCompletion (maximalRealSubfield D.host.E)) = NG.supDiag s D.R.r (s.loc D.R.nV κ) := by
    show ι Sn = _
    simp only [Sn, map_sum]
    unfold NG.supDiag
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · rfl
    · exact map_zero ι
  have hφSn : φ Sn = edgeSum supEdge (upperLeftBlock hr (redFn 1 s.w x)) := by
    unfold edgeSum
    rw [upper_block_val_submatrix hr (blockTri_blkOf_le _ _ (hg s.w hsw))]
    simp only [Matrix.submatrix_apply]
    refine Eq.trans ?_ (GlobalTheory.MtChr.sum_supEdge_castLE hr (fun a b => (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w x).val a b)).symm
    simp only [Sn, map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · exact (hredv a b).symm
    · exact map_zero φ

  let Md : Matrix {y : Fin D.R.nV // D.R.r ≤ y.val} {y : Fin D.R.nV // D.R.r ≤ y.val}
      (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) := fun a b => M' a.1 b.1
  have hdet : (Md.det : s.v.adicCompletion (maximalRealSubfield D.host.E)) = (u : s.v.adicCompletion (maximalRealSubfield D.host.E)) := by
    rw [hu]
    show ι Md.det = _
    rw [RingHom.map_det]
    unfold NG.detDD
    rfl
  have hφdet' : φ Md.det = (((redFn 1 s.w x).val).submatrix (Subtype.val : {a : Fin D.R.nV // blkOf D.R.r D.R.t a = 1} → Fin D.R.nV) Subtype.val).det :=
    GlobalTheory.MtChr.det_map_subtype φ M' _ hredv _ _ (fun a => GlobalTheory.MtChr.blkOf_eq_one_iff a (lt_of_lt_of_eq a.2 rfl))
  have hφdet : φ Md.det = ((dBlk (blkOf D.R.r D.R.t) 1 (redFn 1 s.w x) : (kP s.w)ˣ) : kP s.w) :=
    hφdet'.trans (diag_block_det_val 1 (hg s.w hsw)).symm
  have hξu := hξ u Md.det _ hdet hφdet

  have hA : ((ext1 (P0 Pg D.R.r ψ).conj.H (P0 Pg D.R.r ψ).conj.chi (rTup 1 Ld x) : ℂˣ) : ℂ) =
      (ψ s.w (edgeSum supEdge (upperLeftBlock hr (redFn 1 s.w x))))⁻¹ := by
    erw [extendOne_of_mem _ hP0]
    show (((P0 Pg D.R.r ψ).chi⁻¹ ⟨_, hP0⟩ : ℂˣ) : ℂ) = _
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    congr 1
    show (((∏ PP : ↥Pg, (addCharHom (ψ PP.1) (supHom (kP PP.1) D.R.r)).comp (LevelP.prj _ PP)) ⟨_, hP0⟩ : ℂˣ) : ℂ) = _
    rw [MonoidHom.finsetProd_apply, Fintype.prod_eq_single ⟨s.w, hsw⟩]
    · rfl
    · intro PP hne
      apply Units.ext
      show ψ PP.1 (edgeSum supEdge (upperLeftBlock hr (redFn 1 PP.1 x))) = 1
      rw [triv PP.1 (hPg PP.1 PP.2 (fun e => hne (Subtype.ext e)))]
      unfold upperLeftBlock
      rw [blockDiagonalExtendByOnePrimeField_one, GlobalTheory.MtChr.edgeSum_supEdge_one, AddChar.map_zero_eq_one]
  have hB : (∏ PP ∈ Pg, ∏ c ∈ Finset.range 1, (chi PP)⁻¹ (dBlk (blkOf D.R.r D.R.t) (c + 1) (redFn 1 PP x))) =
      (chi s.w)⁻¹ (dBlk (blkOf D.R.r D.R.t) 1 (redFn 1 s.w x)) := by
    rw [Finset.prod_eq_single_of_mem s.w hsw]
    · rw [Finset.prod_range_one]
    · intro PP hP hne
      rw [Finset.prod_range_one, triv PP (hPg PP hP hne)]
      unfold dBlk
      rw [blockDiagonalExtendByOnePrimeField_one, map_one]
  have hC : (∏ PP ∈ Q, xi PP (dBlk (blk2 D.R.r) 1 (redFn 1 PP x))) = 1 := by
    refine Finset.prod_eq_one fun PP hP => ?_
    rw [triv PP (hQ PP hP)]
    unfold dBlk
    rw [blockDiagonalExtendByOnePrimeField_one, map_one]
  show ((ext1 (P0 Pg D.R.r ψ).conj.H (P0 Pg D.R.r ψ).conj.chi (rTup 1 Ld x) *
      (∏ PP ∈ Pg, ∏ c ∈ Finset.range 1, (chi PP)⁻¹ (dBlk (blkOf D.R.r D.R.t) (c + 1) (redFn 1 PP x))) *
      ∏ PP ∈ Q, xi PP (dBlk (blk2 D.R.r) 1 (redFn 1 PP x)) : ℂˣ) : ℂ) = _
  rw [hB, hC, mul_one, Units.val_mul, hA, hξu, ← hSn, hψ₀, AddChar.map_neg_eq_inv, hφSn]

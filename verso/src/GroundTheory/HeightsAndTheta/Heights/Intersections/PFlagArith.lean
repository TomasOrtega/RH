import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.FlagBundleSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StFlagMultiHomog
import GroundTheory.HeightsAndTheta.Heights.Intersections.StFlagConeTrdeg
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.StatementsIntDim
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

/- English proof (translation)
Take `⟨b, -, -, hsp, hb⟩` from `exists_linearIndepOn_extension (K := F) (v := M.col) (linearIndepOn_empty F M.col) (Set.empty_subset Set.univ)`. Establish `h1 : Submodule.span F (M.col '' b) = Submodule.span F (Set.range M.col)`. Use `le_antisymm (Submodule.span_mono (Set.image_subset_range _ _)) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hsp ⟨i, Set.mem_univ _, rfl⟩`.

Establish `h2 : Module.finrank F (Submodule.span F (M.col '' b)) = Fintype.card b`. Rewrite using `[Set.image_eq_range]`. Conclude with `finrank_span_eq_card hb`. Rewrite `h2` using `[h1, ← Matrix.rank_eq_finrank_span_cols, hM.rank_matrix, Fintype.card_fin]`. Establish `hS : b.toFinset.card = r` using `by rw [Set.toFinset_card]; exact h2.symm`.

Use `⟨b.toFinset, hS, ?_⟩` and prove the remaining obligations. Establish `hmem : ∀ c, b.toFinset.orderEmbOfFin hS c ∈ b` using `fun c => Set.mem_toFinset.1 (b.toFinset.orderEmbOfFin_mem hS c)`. Establish `hli : LinearIndependent F (M.submatrix id (b.toFinset.orderEmbOfFin hS)).col` using `hb.comp (fun c => ⟨_, hmem c⟩) fun c c' h => by`. Establish `h'` using `congrArg Subtype.val h`. Conclude with `(b.toFinset.orderEmbOfFin hS).injective h'`.

Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hli)).ne_zero`.
-/
theorem exists_minor_ne_zero {F : Type} [Field F] {r N : ℕ} (M : Matrix (Fin r) (Fin N) F)
    (hM : LinearIndependent F M.row) :
    ∃ (S : Finset (Fin N)) (hS : S.card = r), (M.submatrix id (S.orderEmbOfFin hS)).det ≠ 0 := by
  classical
  obtain ⟨b, -, -, hsp, hb⟩ := exists_linearIndepOn_extension (K := F) (v := M.col)
    (linearIndepOn_empty F M.col) (Set.empty_subset Set.univ)
  have h1 : Submodule.span F (M.col '' b) = Submodule.span F (Set.range M.col) := by
    refine le_antisymm (Submodule.span_mono (Set.image_subset_range _ _)) (Submodule.span_le.2 ?_)
    rintro _ ⟨i, rfl⟩
    exact hsp ⟨i, Set.mem_univ _, rfl⟩
  have h2 : Module.finrank F (Submodule.span F (M.col '' b)) = Fintype.card b := by
    rw [Set.image_eq_range]
    exact finrank_span_eq_card hb
  rw [h1, ← Matrix.rank_eq_finrank_span_cols, hM.rank_matrix, Fintype.card_fin] at h2
  have hS : b.toFinset.card = r := by rw [Set.toFinset_card]; exact h2.symm
  refine ⟨b.toFinset, hS, ?_⟩
  have hmem : ∀ c, b.toFinset.orderEmbOfFin hS c ∈ b := fun c =>
    Set.mem_toFinset.1 (b.toFinset.orderEmbOfFin_mem hS c)
  have hli : LinearIndependent F (M.submatrix id (b.toFinset.orderEmbOfFin hS)).col :=
    hb.comp (fun c => ⟨_, hmem c⟩) fun c c' h => by
      have h' := congrArg Subtype.val h
      exact (b.toFinset.orderEmbOfFin hS).injective h'
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hli)).ne_zero

section Flag

variable {K : Type} {ι : K → Type}

/- English proof (translation)
Simplify using `[flagMap]`.
-/
theorem flagMap_X_inr (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P))
    (j : Fin (n - 1)) (S : PluckerBlocks N1 n j) :
    flagMap P B (X (⟨Sum.inr j, S⟩ : Σ k, FlagBundleBlocks ι N1 n k)) =
      flagMinor (genMat (FnField P) n * B.map C) j S := by
  simp [flagMap]

/- English proof (translation)
Rewrite using `[flagMinor, flagMinor, RingHom.map_det, RingHom.mapMatrix_apply]`. Use `congr 1`. Use extensionality with `a b`. Simplify using `only [Matrix.map_apply, Matrix.submatrix_apply]`. Use `erw [Matrix.mul_apply]`.

Simplify using `[genMat]`.
-/
theorem eval_one_flagMinor (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P))
    (j : Fin (n - 1)) (S : PluckerBlocks N1 n j) :
    eval (fun q : Fin n × Fin n => if q.1 = q.2 then (1 : FnField P) else 0)
      (flagMinor (genMat (FnField P) n * B.map C) j S) = flagMinor B j S := by
  rw [flagMinor, flagMinor, RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext a b
  simp only [Matrix.map_apply, Matrix.submatrix_apply]
  erw [Matrix.mul_apply]
  simp [genMat]

/- English proof (translation)
Establish `hj : (j : ℕ) + 1 ≤ n` using `by have := j.2; omega`. Take `⟨S, hS, hne⟩` from `exists_minor_ne_zero (B.submatrix (Fin.castLE hj) id) (hB.comp _ (Fin.castLE_injective hj))`. Use `⟨⟨S, hS⟩, fun h => hne ?_⟩` and prove the remaining obligations. Rewrite `h` using `[flagIdeal, RingHom.mem_ker, flagMap_X_inr]`. Use `eval_one_flagMinor P B j ⟨S, hS⟩` as an intermediate fact.

Rewrite `this` using `[h, map_zero]`. Conclude with `this.symm`.
-/
theorem exists_X_inr_notMem (P : Ideal (MRing ι)) [P.IsPrime] {N1 n : ℕ}
    (B : Matrix (Fin n) (Fin N1) (FnField P)) (hB : LinearIndependent (FnField P) B)
    (j : Fin (n - 1)) : ∃ S : PluckerBlocks N1 n j, (X (⟨Sum.inr j, S⟩ : Σ k, FlagBundleBlocks ι N1 n k)) ∉ flagIdeal P B := by
  have hj : (j : ℕ) + 1 ≤ n := by have := j.2; omega
  obtain ⟨S, hS, hne⟩ := exists_minor_ne_zero (B.submatrix (Fin.castLE hj) id)
    (hB.comp _ (Fin.castLE_injective hj))
  refine ⟨⟨S, hS⟩, fun h => hne ?_⟩
  rw [flagIdeal, RingHom.mem_ker, flagMap_X_inr] at h
  have := eval_one_flagMinor P B j ⟨S, hS⟩
  rw [h, map_zero] at this
  exact this.symm

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Rewrite `ha` using `[← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]`. Establish `h' : a ∈ I.comap (C : ℤ →+* MRing ι)` using `ha`. Rewrite `h'` using `[show I.comap (C : ℤ →+* MRing ι) = ⊥ from h]`.

Conclude with `(Submodule.mem_bot ℤ).mp h'`.
-/
theorem algebraMap_int_injective (I : Ideal (MRing ι)) (h : IsHorizontal I) :
    Function.Injective (algebraMap ℤ (MRing ι ⧸ I)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at ha
  have h' : a ∈ I.comap (C : ℤ →+* MRing ι) := ha
  rw [show I.comap (C : ℤ →+* MRing ι) = ⊥ from h] at h'
  exact (Submodule.mem_bot ℤ).mp h'

end Flag

/- English proof (translation)
Introduce `K _ ι _ N1 t n P d c m B hP hc hB`. Use `hP.2.1.1` as an intermediate fact. Establish `hHor : IsHorizontal (flagIdeal P B)`. Establish `h` using `hP.2.2.1`. Rewrite `h` using `[← imageZ_flagIdeal P B]`.

Use `Eq.trans (Ideal.ext fun a => ?_) h` and prove the remaining obligations. Simplify using `only [Ideal.mem_comap, imageZ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_C]`. Establish `hprime : (flagIdeal P B).IsPrime` using `RingHom.ker_isPrime _`. Use `⟨⟨Sum.inl hP.1.some⟩, ⟨hprime, hMH K ι N1 t n P c m B hP.2.1.1 hP.2.1.2.1 hc.1 hB, ?_⟩, hHor, ?_⟩` and prove the remaining obligations. Introduce and unpack `(k | j)`.

Take `⟨i, hi⟩` from `hP.2.1.2.2 k`. Use `⟨i, fun h => hi ?_⟩` and prove the remaining obligations. Rewrite using `[← imageZ_flagIdeal P B]`. Use `show rename inlV (X ⟨k, i⟩) ∈ flagIdeal P B`. Rewrite using `[rename_X]` and apply the resulting hypothesis.

Take `⟨S, hS⟩` from `exists_X_inr_notMem P B hB.1 j`. Conclude with `⟨S, hS⟩`. Establish `dimP` using `hDim (MRing ι ⧸ P) (algebraMap_int_injective P hP.2.2.1)`. Establish `dimF` using `hDim (MRing (FlagBundleBlocks ι N1 n) ⧸ flagIdeal P B) (algebraMap_int_injective _ hHor)`. Rewrite `dimF` using `[hTr K ι N1 n P B hP.2.1.1 hP.2.2.1 hB.1]`.

Rewrite `dimP` using `[hP.2.2.2]`. Rewrite using `[dimF]`. Establish `hK : 0 < Fintype.card K` using `Fintype.card_pos_iff.2 hP.1`. Establish `h1 : ((d + Fintype.card K : ℕ) : ℕ∞) = (Algebra.trdeg ℤ (MRing ι ⧸ P)).toENat + 1`. Conclude with `dimP` after adjusting the coercions.

Simplify using `only [map_add, map_natCast, Fintype.card_sum, Fintype.card_fin]`. Generalize the expression as in `(Algebra.trdeg ℤ (MRing ι ⧸ P)).toENat = s at h1 ⊢`. Proceed by induction on `s using ENat.recTopCoe with`. Consider the case `top => simp at h1`. Consider the case `coe s`.

Normalize the coercions in `at h1 ⊢`. Rewrite using `[show s + (flagDim n + (n - 1)) + 1 = flagDim n + d + (Fintype.card K + (n - 1)) by omega]`.
-/
theorem FlagArith.proof (hMH : FlagMultiHomog.Statement) (hTr : FlagConeTrdeg.Statement)
    (hDim : IntDomainDim.Statement) : FlagArith.Statement := by
  intro K _ ι _ N1 t n P d c m B hP hc hB
  have := hP.2.1.1

  have hHor : IsHorizontal (flagIdeal P B) := by
    have h := hP.2.2.1
    rw [← imageZ_flagIdeal P B] at h
    refine Eq.trans (Ideal.ext fun a => ?_) h
    simp only [Ideal.mem_comap, imageZ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_C]
  have hprime : (flagIdeal P B).IsPrime := RingHom.ker_isPrime _
  refine ⟨⟨Sum.inl hP.1.some⟩, ⟨hprime, hMH K ι N1 t n P c m B hP.2.1.1 hP.2.1.2.1 hc.1 hB, ?_⟩, hHor, ?_⟩
  ·
    rintro (k | j)
    · obtain ⟨i, hi⟩ := hP.2.1.2.2 k
      refine ⟨i, fun h => hi ?_⟩
      rw [← imageZ_flagIdeal P B]
      show rename inlV (X ⟨k, i⟩) ∈ flagIdeal P B
      rwa [rename_X]
    · obtain ⟨S, hS⟩ := exists_X_inr_notMem P B hB.1 j
      exact ⟨S, hS⟩
  ·
    have dimP := hDim (MRing ι ⧸ P) (algebraMap_int_injective P hP.2.2.1)
    have dimF := hDim (MRing (FlagBundleBlocks ι N1 n) ⧸ flagIdeal P B) (algebraMap_int_injective _ hHor)
    rw [hTr K ι N1 n P B hP.2.1.1 hP.2.2.1 hB.1] at dimF
    rw [hP.2.2.2] at dimP
    rw [dimF]
    have hK : 0 < Fintype.card K := Fintype.card_pos_iff.2 hP.1
    have h1 : ((d + Fintype.card K : ℕ) : ℕ∞) = (Algebra.trdeg ℤ (MRing ι ⧸ P)).toENat + 1 := by
      exact_mod_cast dimP
    simp only [map_add, map_natCast, Fintype.card_sum, Fintype.card_fin]
    generalize (Algebra.trdeg ℤ (MRing ι ⧸ P)).toENat = s at h1 ⊢
    induction s using ENat.recTopCoe with
    | top => simp at h1
    | coe s =>
      norm_cast at h1 ⊢
      rw [show s + (flagDim n + (n - 1)) + 1 = flagDim n + d + (Fintype.card K + (n - 1)) by omega]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

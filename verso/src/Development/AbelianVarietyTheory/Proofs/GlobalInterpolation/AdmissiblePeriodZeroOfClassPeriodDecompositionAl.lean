import Mathlib
import Formalism.SharpRestriction.Divisibility.StatementFT.PeriodPointConditions
import Formalism.LocalToGlobal.HilbertRowConditions.RowPin
import Formalism.LocalToGlobal.HermitianForms.TiedBrRep
import Formalism.LocalRingCardinality.PosOfIsomEmb
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SharpRestriction.LevelLetterCocycles.TwGuard
import Formalism.SharpRestriction.Divisibility.ThetaNormsAndLinks
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes

noncomputable section

namespace GlobalTheory.PerRed

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw Formalism.L2.Forms Matrix NumberField
open scoped BigOperators

attribute [local instance] MemberForms.clsPFin

/- English proof (translation)
Set `_` to `D.host.cmStar`. Establish `hY : ∀ τ, ∃ Y : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ, IsUnit Y.det ∧ Yᴴ * (gramP D).map (embT D τ) * Y = 1`. Introduce `τ`. Establish `hs` using `D.sp.X'_sig (embT D τ)`. Rewrite `hs` using `[D.X'_posDef (embT D τ)]`.

Simplify using `only at hs`. Take `⟨e, P, hP⟩` from `hs`. Establish `hJ : Formalism.UG.Jpq D.sp.X'.rank 0 = 1`. Use extensionality with `i j`. Break down `i with i | i` into its components or cases.

Break down `j with j | j` into its components or cases. Simplify using `[Formalism.UG.Jpq, Matrix.one_apply]`. Conclude with `j.elim0`. Conclude with `i.elim0`. Establish `hcT : Formalism.UG.cT (starRingEnd ℂ) P.1 = P.1ᴴ`.

Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, Matrix.conjTranspose_apply]`. Rewrite `hP` using `[hcT, hJ]`. Set `f : Fin D.sp.X'.rank ≃ Fin (D.R.N D.R.m - 1)` to `finCongr (rankP D)`. Set `g : Fin (D.R.N D.R.m - 1) ≃ Fin D.sp.X'.rank ⊕ Fin 0` to `f.symm.trans e`.

Establish `hG : ((gramP D).map (embT D τ)).submatrix g.symm g.symm = (D.sp.X'.gram.map (embT D τ)).reindex e e`. Use extensionality with `i j`. Simplify using `[g, f, gramP, Matrix.reindex_apply, Matrix.submatrix_apply]`. Use `⟨P.1.submatrix g g, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_submatrix_equiv_self]`.

Conclude with `Matrix.isUnits_det_units P`. Establish `h1 : (gramP D).map (embT D τ) = (((gramP D).map (embT D τ)).submatrix g.symm g.symm).submatrix g g`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.conjTranspose_submatrix, h1, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hG, hP]`.

Conclude with `Matrix.submatrix_one_equiv g`. Use `choose Y hYu hY using hY`. Conclude with `⟨⟨Y, hYu⟩, fun τ => Or.inl (hY τ)⟩`.
-/
theorem exists_orthonormal_frame₂ (D : D7) : ∃ o : FrP D, o.IsON := by
  classical
  let _ := D.host.cmStar
  have hY : ∀ τ, ∃ Y : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ,
      IsUnit Y.det ∧ Yᴴ * (gramP D).map (embT D τ) * Y = 1 := by
    intro τ
    have hs := D.sp.X'_sig (embT D τ)
    rw [D.X'_posDef (embT D τ)] at hs
    dsimp only at hs
    obtain ⟨e, P, hP⟩ := hs
    have hJ : Formalism.UG.Jpq D.sp.X'.rank 0 = 1 := by
      ext i j
      rcases i with i | i
      · rcases j with j | j
        · simp [Formalism.UG.Jpq, Matrix.one_apply]
        · exact j.elim0
      · exact i.elim0
    have hcT : Formalism.UG.cT (starRingEnd ℂ) P.1 = P.1ᴴ := by
      ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
    rw [hcT, hJ] at hP
    let f : Fin D.sp.X'.rank ≃ Fin (D.R.N D.R.m - 1) := finCongr (rankP D)
    let g : Fin (D.R.N D.R.m - 1) ≃ Fin D.sp.X'.rank ⊕ Fin 0 := f.symm.trans e
    have hG : ((gramP D).map (embT D τ)).submatrix g.symm g.symm = (D.sp.X'.gram.map (embT D τ)).reindex e e := by
      ext i j
      simp [g, f, gramP, Matrix.reindex_apply, Matrix.submatrix_apply]
    refine ⟨P.1.submatrix g g, ?_, ?_⟩
    · rw [Matrix.det_submatrix_equiv_self]; exact Matrix.isUnits_det_units P
    · have h1 : (gramP D).map (embT D τ) = (((gramP D).map (embT D τ)).submatrix g.symm g.symm).submatrix g g := by
        ext i j; simp
      rw [Matrix.conjTranspose_submatrix, h1, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hG, hP]
      exact Matrix.submatrix_one_equiv g
  choose Y hYu hY using hY
  exact ⟨⟨Y, hYu⟩, fun τ => Or.inl (hY τ)⟩

section Split

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

/- English proof (translation)
Establish `hF` using `(T.valP.ptC z).1 hz`. Take `⟨g, hg, hres⟩` from `Submodule.mem_map.1 hF`. Establish `hval` using `(Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2) (T.clsP.y c) (Set.mem_univ _)`. Take `⟨Q0, hQ0, hfn⟩` from `Submodule.mem_map.1 hval`. Establish `hQ0' : Q0 ∈ CSpan (D.fm u).sg`.

Use `CSpan_shW (D.fm u).sg (fun _ => ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ))` as an intermediate fact. Unfold `sgT at hQ0`. Rewrite `hQ0` using `[this]`. Conclude with `hQ0`. Establish `he : T.valP.eW z c = fnOf _ (shiftOf (sgT u)) 1 Q0`.

Rewrite using `[hfn, ← hres]`. Both sides reduce to the same expression. Establish `hM : ∀ τ, IsUnit ((o.1 τ)⁻¹).det` using `fun τ => by`. Rewrite using `[Matrix.det_nonsing_inv]`. Conclude with `(o.2 τ).ringInverse`.

Use `⟨_, ?_, he.trans (fnOf_change _ _ _ _ hM Q0)⟩` and prove the remaining obligations. Conclude with `Submodule.smul_mem _ _ (blkRow_mem _ _ hQ0')`.
-/
theorem eW_rep_o (T : FormsTiedSym D u Ch chOf) (o : FrP D) (z : (D.mem u).P.Wrow) (hz : z ∈ (D.fm u).ptC)
    (c : (D.fm u).clsP) :
    ∃ Q ∈ CSpan (D.fm u).sg, T.valP.eW z c = fnOf _ (shiftOf (sgT u)) (fun τ => (o.1 τ)⁻¹) Q := by
  have hF := (T.valP.ptC z).1 hz
  obtain ⟨g, hg, hres⟩ := Submodule.mem_map.1 hF
  have hval := (Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2) (T.clsP.y c) (Set.mem_univ _)
  obtain ⟨Q0, hQ0, hfn⟩ := Submodule.mem_map.1 hval
  have hQ0' : Q0 ∈ CSpan (D.fm u).sg := by
    have := CSpan_shW (D.fm u).sg (fun _ => ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ))
    unfold sgT at hQ0
    rw [this] at hQ0
    exact hQ0
  have he : T.valP.eW z c = fnOf _ (shiftOf (sgT u)) 1 Q0 := by
    rw [hfn, ← hres]; rfl
  have hM : ∀ τ, IsUnit ((o.1 τ)⁻¹).det := fun τ => by
    rw [Matrix.det_nonsing_inv]; exact (o.2 τ).ringInverse
  refine ⟨_, ?_, he.trans (fnOf_change _ _ _ _ hM Q0)⟩
  exact Submodule.smul_mem _ _ (blkRow_mem _ _ hQ0')

/- English proof (translation)
Simplify using `[nfAll, Formalism.REAL.fockF]`.
-/
theorem nfAll_zero (n : ℕ) (lam : D.what₂.Tau → DomWeight n) : nfAll lam 0 0 = 0 := by
  simp [nfAll, Formalism.REAL.fockF]

open Classical in
/- English proof (translation)
Unfold `Formalism.MainNotions.RT.PeriodPointConditions.resC`. Rewrite using `[LinearEquiv.apply_symm_apply]`.
-/
theorem eW_resC (T : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (z : (D.mem u).P.Wrow) :
    T.valP.eW (Formalism.MainNotions.RT.PeriodPointConditions.resC T c z) = fun c' => if c' = c then T.valP.eW z c' else 0 := by
  classical
  unfold Formalism.MainNotions.RT.PeriodPointConditions.resC
  rw [LinearEquiv.apply_symm_apply]

/- English proof (translation)
Take `⟨o, ho⟩` from `exists_orthonormal_frame₂ D`. Use `choose P hP hPe using eW_rep_o T o a ha`. Use `choose Q hQ hQe using eW_rep_o T o b hb`. Rewrite using `[T.valP.ipP o ho a b P Q hP hQ hPe hQe]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Establish `hP' : ∀ c', (if c' = c then P c' else 0) ∈ CSpan (D.fm u).sg` using `fun c' => by split_ifs`. Conclude with `hP c'`. Conclude with `Submodule.zero_mem _`. Establish `hQ' : ∀ c', (if c' = c then Q c' else 0) ∈ CSpan (D.fm u).sg` using `fun c' => by split_ifs`. Conclude with `hQ c'`.

Conclude with `Submodule.zero_mem _`. Establish `hPe' : ∀ c', T.valP.eW (Formalism.MainNotions.RT.PeriodPointConditions.resC T c a) c' = fnOf _ (shiftOf (sgT u)) (fun τ => (o.1 τ)⁻¹) (if c' = c then P c' else 0)` using `fun c' => by`. Rewrite using `[eW_resC]`. Simplify using `only`. Use `split_ifs`.

Conclude with `hPe c'`. Conclude with `(map_zero _).symm`. Establish `hQe' : ∀ c', T.valP.eW (Formalism.MainNotions.RT.PeriodPointConditions.resC T c b) c' = fnOf _ (shiftOf (sgT u)) (fun τ => (o.1 τ)⁻¹) (if c' = c then Q c' else 0)` using `fun c' => by`. Rewrite using `[eW_resC]`. Simplify using `only`.

Use `split_ifs`. Conclude with `hQe c'`. Conclude with `(map_zero _).symm`. Rewrite using `[T.valP.ipP o ho _ _ _ _ hP' hQ' hPe' hQe', Finset.sum_eq_single c]`. Simplify using the standard rewrite rules.

Introduce `c' _ hc'`. Simplify using `[hc', nfAll_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ c) h`.
-/
theorem petersson_eq_sum_restrict (T : FormsTiedSym D u Ch chOf) (a b : (D.mem u).P.Wrow) (ha : a ∈ (D.fm u).ptC)
    (hb : b ∈ (D.fm u).ptC) :
    (D.fm u).ipP a b = ∑ c, (D.fm u).ipP (Formalism.MainNotions.RT.PeriodPointConditions.resC T c a) (Formalism.MainNotions.RT.PeriodPointConditions.resC T c b) := by
  classical
  obtain ⟨o, ho⟩ := exists_orthonormal_frame₂ D
  choose P hP hPe using eW_rep_o T o a ha
  choose Q hQ hQe using eW_rep_o T o b hb
  rw [T.valP.ipP o ho a b P Q hP hQ hPe hQe]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hP' : ∀ c', (if c' = c then P c' else 0) ∈ CSpan (D.fm u).sg := fun c' => by
    split_ifs
    · exact hP c'
    · exact Submodule.zero_mem _
  have hQ' : ∀ c', (if c' = c then Q c' else 0) ∈ CSpan (D.fm u).sg := fun c' => by
    split_ifs
    · exact hQ c'
    · exact Submodule.zero_mem _
  have hPe' : ∀ c', T.valP.eW (Formalism.MainNotions.RT.PeriodPointConditions.resC T c a) c' =
      fnOf _ (shiftOf (sgT u)) (fun τ => (o.1 τ)⁻¹) (if c' = c then P c' else 0) := fun c' => by
    rw [eW_resC]
    dsimp only
    split_ifs
    · exact hPe c'
    · exact (map_zero _).symm
  have hQe' : ∀ c', T.valP.eW (Formalism.MainNotions.RT.PeriodPointConditions.resC T c b) c' =
      fnOf _ (shiftOf (sgT u)) (fun τ => (o.1 τ)⁻¹) (if c' = c then Q c' else 0) := fun c' => by
    rw [eW_resC]
    dsimp only
    split_ifs
    · exact hQe c'
    · exact (map_zero _).symm
  rw [T.valP.ipP o ho _ _ _ _ hP' hQ' hPe' hQe', Finset.sum_eq_single c]
  · simp
  · intro c' _ hc'
    simp [hc', nfAll_zero]
  · intro h; exact absurd (Finset.mem_univ c) h

end Split

section Val

/- English proof (translation)
Establish `hp` using `D.what₂.places.resChar_prime w`. Establish `: Fact (D.what₂.places.resChar w).Prime` using `⟨hp⟩`. Take `⟨k, r, hr, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hn (D.what₂.places.resChar w) hp.ne_one`. Establish `hr0 : r ≠ 0` using `by rintro rfl; exact hr (dvd_zero _)`. Establish `hpk : ((D.what₂.places.resChar w : D.what₂.LL)) ^ k ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)`.

Establish `hrL : (r : D.what₂.LL) ≠ 0` using `Nat.cast_ne_zero.mpr hr0`. Establish `hv : padicValNat (D.what₂.places.resChar w) ((D.what₂.places.resChar w) ^ k * r) = k`. Rewrite using `[padicValNat.mul (pow_ne_zero _ hp.ne_zero) hr0, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hr, add_zero]`. Rewrite using `[hv]`. Establish `e1 : (((D.what₂.places.resChar w ^ k * r : ℕ)) : D.what₂.LL) = ((((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ^ k : 𝓞 D.what₂.LL) : D.what₂.LL) * ((r : 𝓞 D.what₂.LL) : D.what₂.LL)` using `by push_cast; ring`.

Establish `hpk' : ((((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ^ k : 𝓞 D.what₂.LL) : D.what₂.LL) ≠ 0` using `by push_cast; exact hpk`. Establish `hr' : ((r : 𝓞 D.what₂.LL) : D.what₂.LL) ≠ 0` using `by push_cast; exact hrL`. Rewrite using `[e1, SkeletonIndexLemmas.vAdd_mul _ hpk' hr', WeightDegreeSizes.vAdd_lpow]`. Establish `hr0' : vAdd (D.plEq w) ((r : 𝓞 D.what₂.LL) : D.what₂.LL) = 0`. Establish `hnn` using `ThetaNormsAndLinks.vAdd_nonneg_int (D.plEq w) (r : 𝓞 D.what₂.LL)`.

Establish `hrne : (r : 𝓞 D.what₂.LL) ≠ 0`. Introduce `h`. Apply `hr'` to reduce the goal to its premises. Rewrite using `[h]`. Simplify using the standard rewrite rules.

Establish `hnot : ¬ (0 < vAdd (D.plEq w) ((r : 𝓞 D.what₂.LL) : D.what₂.LL))`. Rewrite using `[vAdd_pos_iff_mem _ hrne]`. Introduce `hmem`. Establish `hpm` using `resChar_mem D w`. Establish `hcop : IsCoprime ((D.what₂.places.resChar w : ℕ) : ℤ) (r : ℤ)` using `Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hr)`.

Take `⟨a, b, hab⟩` from `hcop.map (Int.castRingHom (𝓞 D.what₂.LL))`. Establish `h1 : (1 : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal`. Rewrite using `[← hab]`. Use `Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)` and prove the remaining obligations. Simplify using `using hpm`.

Simplify using `using hmem`. Conclude with `(D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hr0']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vAdd_nat (D : D7) (w : D.what₂.places.Pl) (n : ℕ) (hn : n ≠ 0) :
    vAdd (D.plEq w) (n : D.what₂.LL) =
      (D.what₂.places.ramIdx w : ℤ) * (padicValNat (D.what₂.places.resChar w) n : ℤ) := by
  have hp := D.what₂.places.resChar_prime w
  have : Fact (D.what₂.places.resChar w).Prime := ⟨hp⟩
  obtain ⟨k, r, hr, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn (D.what₂.places.resChar w) hp.ne_one
  have hr0 : r ≠ 0 := by rintro rfl; exact hr (dvd_zero _)
  have hpk : ((D.what₂.places.resChar w : D.what₂.LL)) ^ k ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hrL : (r : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.mpr hr0
  have hv : padicValNat (D.what₂.places.resChar w) ((D.what₂.places.resChar w) ^ k * r) = k := by
    rw [padicValNat.mul (pow_ne_zero _ hp.ne_zero) hr0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hr, add_zero]
  rw [hv]
  have e1 : (((D.what₂.places.resChar w ^ k * r : ℕ)) : D.what₂.LL) =
      ((((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ^ k : 𝓞 D.what₂.LL) : D.what₂.LL) * ((r : 𝓞 D.what₂.LL) : D.what₂.LL) := by
    push_cast; ring
  have hpk' : ((((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ^ k : 𝓞 D.what₂.LL) : D.what₂.LL) ≠ 0 := by
    push_cast; exact hpk
  have hr' : ((r : 𝓞 D.what₂.LL) : D.what₂.LL) ≠ 0 := by push_cast; exact hrL
  rw [e1, SkeletonIndexLemmas.vAdd_mul _ hpk' hr', WeightDegreeSizes.vAdd_lpow]
  have hr0' : vAdd (D.plEq w) ((r : 𝓞 D.what₂.LL) : D.what₂.LL) = 0 := by
    have hnn := ThetaNormsAndLinks.vAdd_nonneg_int (D.plEq w) (r : 𝓞 D.what₂.LL)
    have hrne : (r : 𝓞 D.what₂.LL) ≠ 0 := by
      intro h; apply hr'; rw [h]; simp
    have hnot : ¬ (0 < vAdd (D.plEq w) ((r : 𝓞 D.what₂.LL) : D.what₂.LL)) := by
      rw [vAdd_pos_iff_mem _ hrne]
      intro hmem
      have hpm := resChar_mem D w
      have hcop : IsCoprime ((D.what₂.places.resChar w : ℕ) : ℤ) (r : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hr)
      obtain ⟨a, b, hab⟩ := hcop.map (Int.castRingHom (𝓞 D.what₂.LL))
      have h1 : (1 : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
        rw [← hab]
        refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
        · simpa using hpm
        · simpa using hmem
      exact (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    omega
  rw [hr0']; ring

/- English proof (translation)
Establish `h1` using `vAdd_nat D w n hn`. Establish `h2` using `vAdd_nat D w d hd0`. Establish `h3 : padicValNat (D.what₂.places.resChar w) n ≤ padicValNat (D.what₂.places.resChar w) d`. Establish `: Fact (D.what₂.places.resChar w).Prime` using `⟨D.what₂.places.resChar_prime w⟩`. Conclude with `(padicValNat_dvd_iff_le hd0).mp (dvd_trans pow_padicValNat_dvd hd)`.

Rewrite using `[h1, Int.cast_mul, Int.cast_natCast, Int.cast_natCast]`. Conclude with `mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h3) (by positivity)`.
-/
theorem vAdd_card_le (D : D7) (w : D.what₂.places.Pl) (n d : ℕ) (hn : n ≠ 0) (hd : n ∣ d) (hd0 : d ≠ 0) :
    (vAdd (D.plEq w) (n : D.what₂.LL) : ℝ) ≤
      (D.what₂.places.ramIdx w : ℝ) * (padicValNat (D.what₂.places.resChar w) d : ℝ) := by
  have h1 := vAdd_nat D w n hn
  have h2 := vAdd_nat D w d hd0
  have h3 : padicValNat (D.what₂.places.resChar w) n ≤ padicValNat (D.what₂.places.resChar w) d := by
    have : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    exact (padicValNat_dvd_iff_le hd0).mp (dvd_trans pow_padicValNat_dvd hd)
  rw [h1, Int.cast_mul, Int.cast_natCast, Int.cast_natCast]
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h3) (by positivity)

end Val

end GlobalTheory.PerRed

noncomputable section

namespace GlobalTheory.PerRed

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw Formalism.L2.Forms Matrix NumberField
open scoped BigOperators

attribute [local instance] MemberForms.clsPFin

section Main

/- English proof (translation)
Introduce `_hD u x hx F hFM _hFV`. Take `⟨Ch, chOf, T, hT⟩` from `h u`. Use `choose y hy hyv using hT x hx F hFM`. Establish `hcard : ∀ c, Nat.card ((D.fm u).stabilizer₂ c) ≠ 0` using `fun c => Nat.card_pos.ne'`. Establish `hdvd : ∀ c, Nat.card ((D.fm u).stabilizer₂ c) ∣ (D.mem u).C.DGam` using `fun c => dvd_trans (Subgroup.card_dvd_of_injective _ ((D.fm u).stabMap_inj c)) ((D.mem u).C.dvd_DGam D.R.m le_rfl _)`.

Use `⟨∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : D.what₂.LL)⁻¹ * y c, ?_, ?_⟩` and prove the remaining obligations. Establish `hz : (D.fm u).ptEmb x ∈ (D.fm u).ptC` using `((T.valP.rat _).1 ⟨x, rfl⟩).1`. Establish `hG : T.jM ((D.eMt u).symm F) ∈ (D.fm u).ptC` using `T.per.2.1 _`. Rewrite using `[T.per.2.2, petersson_eq_sum_restrict T _ _ hG hz, map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, map_inv₀, map_natCast, hy c]`. Unfold `Formalism.MainNotions.RT.PeriodPointConditions.pcL`. Establish `: ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (hcard c)`. Clear the denominators using the available nonvanishing facts. Introduce `w`.

Establish `hterm : ∀ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : D.what₂.LL)⁻¹ * y c = 0 ∨ -ur D w (vDG D u w) ≤ (vAdd (D.plEq w) (((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : D.what₂.LL)⁻¹ * y c) : ℝ)`. Introduce `c`. Distinguish the cases in `h0 : y c = 0`. Use `left`. Simplify using `[h0]`.

Use `right`. Establish `hpos : 0 ≤ vAdd (D.plEq w) (y c)` using `(hyv c w).resolve_left h0`. Establish `hpos' : (0 : ℝ) ≤ (vAdd (D.plEq w) (y c) : ℝ)` using `by exact_mod_cast hpos`. Establish `hc : ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : D.what₂.LL) ≠ 0` using `Nat.cast_ne_zero.mpr (hcard c)`. Rewrite using `[SkeletonIndexLemmas.vAdd_mul _ (inv_ne_zero hc) h0, SkeletonIndexLemmas.vAdd_inv]`.

Establish `hle` using `vAdd_card_le D w _ _ (hcard c) (hdvd c) (D.mem u).C.DGam_pos.ne'`. Simplify using `only [ur, vDG]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsum : ∀ s : Finset (D.fm u).clsP, (∑ c ∈ s, ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : D.what₂.LL)⁻¹ * y c) = 0 ∨ -ur D w (vDG D u w) ≤ (vAdd (D.plEq w) (∑ c ∈ s, ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : D.what₂.LL)⁻¹ * y c) : ℝ)`.

Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`.

Conclude with `WeightDegreeSizes.pair_add_ge D w (hterm a) ih`. Conclude with `hsum Finset.univ`.
-/
theorem admissiblePeriodZero_of_classPeriodDecomposition {D : D7} (h : ∀ u, Formalism.MainNotions.RT.PeriodPointConditions.PerDec0 D u) : Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl D := by
  classical
  intro _hD u x hx F hFM _hFV
  obtain ⟨Ch, chOf, T, hT⟩ := h u
  choose y hy hyv using hT x hx F hFM
  have hcard : ∀ c, Nat.card ((D.fm u).stabilizer₂ c) ≠ 0 := fun c => Nat.card_pos.ne'
  have hdvd : ∀ c, Nat.card ((D.fm u).stabilizer₂ c) ∣ (D.mem u).C.DGam := fun c =>
    dvd_trans (Subgroup.card_dvd_of_injective _ ((D.fm u).stabMap_inj c))
      ((D.mem u).C.dvd_DGam D.R.m le_rfl _)
  refine ⟨∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : D.what₂.LL)⁻¹ * y c, ?_, ?_⟩
  · have hz : (D.fm u).ptEmb x ∈ (D.fm u).ptC := ((T.valP.rat _).1 ⟨x, rfl⟩).1
    have hG : T.jM ((D.eMt u).symm F) ∈ (D.fm u).ptC := T.per.2.1 _
    rw [T.per.2.2, petersson_eq_sum_restrict T _ _ hG hz, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, map_inv₀, map_natCast, hy c]
    unfold Formalism.MainNotions.RT.PeriodPointConditions.pcL
    have : ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hcard c)
    field_simp
  · intro w
    have hterm : ∀ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : D.what₂.LL)⁻¹ * y c = 0 ∨
        -ur D w (vDG D u w) ≤ (vAdd (D.plEq w) (((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : D.what₂.LL)⁻¹ * y c) : ℝ) := by
      intro c
      by_cases h0 : y c = 0
      · left; simp [h0]
      right
      have hpos : 0 ≤ vAdd (D.plEq w) (y c) := (hyv c w).resolve_left h0
      have hpos' : (0 : ℝ) ≤ (vAdd (D.plEq w) (y c) : ℝ) := by exact_mod_cast hpos
      have hc : ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.mpr (hcard c)
      rw [SkeletonIndexLemmas.vAdd_mul _ (inv_ne_zero hc) h0, SkeletonIndexLemmas.vAdd_inv]
      have hle := vAdd_card_le D w _ _ (hcard c) (hdvd c) (D.mem u).C.DGam_pos.ne'
      simp only [ur, vDG]
      push_cast
      linarith
    have hsum : ∀ s : Finset (D.fm u).clsP,
        (∑ c ∈ s, ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : D.what₂.LL)⁻¹ * y c) = 0 ∨
        -ur D w (vDG D u w) ≤
          (vAdd (D.plEq w) (∑ c ∈ s, ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : D.what₂.LL)⁻¹ * y c) : ℝ) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.sum_insert ha]
        exact WeightDegreeSizes.pair_add_ge D w (hterm a) ih
    exact hsum Finset.univ

end Main

end GlobalTheory.PerRed

namespace GlobalTheory.PerRed

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

/- English proof (translation)
Introduce `_ h` and use `admissiblePeriodZero_of_classPeriodDecomposition h`.
-/
theorem periodClassSumWeyl_of_forall_perDec0 :
    ∀ D : D7, (∀ u, Formalism.MainNotions.RT.PeriodPointConditions.PerDec0 D u) → Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl D :=
  fun _ h => admissiblePeriodZero_of_classPeriodDecomposition h

end GlobalTheory.PerRed

import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.ExistsNeZeroMem
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBAt
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalKindPf

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open PI.ScalarPairDr.W
open scoped Matrix

section Cramer

variable {K : Type} [Field K] {r : ℕ}

/- English proof (translation)
Rewrite using `[Matrix.det_succ_column _ (Fin.last r), Finset.sum_eq_single (Fin.last r)]`. Simplify using `only [Matrix.updateCol_self, Pi.single_eq_same, Fin.succAbove_last]`. Establish `e : (A.updateCol (Fin.last r) (Pi.single (Fin.last r) c)).submatrix Fin.castSucc Fin.castSucc = A.submatrix Fin.castSucc Fin.castSucc`. Use extensionality with `i j`. Simplify using `[Matrix.updateCol_ne (Fin.castSucc_lt_last j).ne]`.

Rewrite using `[e, ← two_mul, pow_mul]`. Simplify using the standard rewrite rules. Introduce `i _ hi`. Simplify using `[Matrix.updateCol_self, Pi.single_eq_of_ne hi]`. Simplify using the standard rewrite rules.
-/
theorem det_updateCol_last_single (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (c : K) :
    (A.updateCol (Fin.last r) (Pi.single (Fin.last r) c)).det = c * (A.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_column _ (Fin.last r), Finset.sum_eq_single (Fin.last r)]
  · simp only [Matrix.updateCol_self, Pi.single_eq_same, Fin.succAbove_last]
    have e : (A.updateCol (Fin.last r) (Pi.single (Fin.last r) c)).submatrix Fin.castSucc Fin.castSucc =
        A.submatrix Fin.castSucc Fin.castSucc := by
      ext i j
      simp [Matrix.updateCol_ne (Fin.castSucc_lt_last j).ne]
    rw [e, ← two_mul, pow_mul]
    simp
  · intro i _ hi
    simp [Matrix.updateCol_self, Pi.single_eq_of_ne hi]
  · simp

/- English proof (translation)
Establish `h1 : Matrix.cramer A (A *ᵥ v) = A.det • v`. Rewrite using `[Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]`. Establish `h2` using `congrFun h1 (Fin.last r)`. Rewrite `h2` using `[h, Matrix.cramer_apply, det_updateCol_last_single, Pi.smul_apply, smul_eq_mul]`. Conclude with `h2.symm`.
-/
theorem cramer_last (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (v : Fin (r + 1) → K) (c : K)
    (h : A *ᵥ v = Pi.single (Fin.last r) c) :
    A.det * v (Fin.last r) = c * (A.submatrix Fin.castSucc Fin.castSucc).det := by
  have h1 : Matrix.cramer A (A *ᵥ v) = A.det • v := by
    rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  have h2 := congrFun h1 (Fin.last r)
  rw [h, Matrix.cramer_apply, det_updateCol_last_single, Pi.smul_apply, smul_eq_mul] at h2
  exact h2.symm

end Cramer

end Formalism.L2.SG.Pf.ScalKindPf

namespace Formalism.L2.SG.Pf.ScalKindPf

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open PI.ScalarPairDr.W
open scoped Matrix

section ZetaNonvanishing₂

variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable {S : HSpace E} (Λ : Submodule (𝓞 E) S.V) {r : ℕ} {T T' : E}

def wv (F' : LFlag S r T') (v : Fin (r + 1) → E) : S.V := ∑ j, v j • F'.fl.fvec j

/- English proof (translation)
Simplify using `only [wv, Matrix.mulVec, dotProduct, map_sum, map_smul, smul_eq_mul, zhat_apply]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`.
-/
theorem hT_wv (F : LFlag S r T) (F' : LFlag S r T') (v : Fin (r + 1) → E) (i : Fin (r + 1)) :
    S.hT (F.fl.fvec i) (wv F' v) = (Zhat F.fl F'.fl *ᵥ v) i := by
  simp only [wv, Matrix.mulVec, dotProduct, map_sum, map_smul, smul_eq_mul, zhat_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/- English proof (translation)
Simplify using `only [wv, Fin.sum_univ_castSucc, fvec_castSucc, fvec_last]`.
-/
theorem wv_eq (F' : LFlag S r T') (v : Fin (r + 1) → E) :
    wv F' v = (∑ a : Fin r, v (Fin.castSucc a) • F'.fl.e a) + v (Fin.last r) • F'.fl.z := by
  simp only [wv, Fin.sum_univ_castSucc, fvec_castSucc, fvec_last]

/- English proof (translation)
The claim follows from `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`.
-/
theorem sumX_mem (F' : LFlag S r T') (d : Fin r → E) : (∑ a : Fin r, d a • F'.fl.e a) ∈ Xsp F' :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/- English proof (translation)
Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => rw [fvec_last, if_pos rfl]`. Conclude with `F.fl.z_norm`. Consider the case `cast a => rw [fvec_castSucc, if_neg (Fin.castSucc_lt_last a).ne]`. Conclude with `F.fl.z_orth a`.
-/
theorem hermitian_frame_z (F : LFlag S r T) (i : Fin (r + 1)) :
    S.hT (F.fl.fvec i) F.fl.z = if i = Fin.last r then -T else 0 := by
  induction i using Fin.lastCases with
  | last => rw [fvec_last, if_pos rfl]; exact F.fl.z_norm
  | cast a => rw [fvec_castSucc, if_neg (Fin.castSucc_lt_last a).ne]; exact F.fl.z_orth a

/- English proof (translation)
Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => rw [fvec_last]`. Conclude with `Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`. Consider the case `cast a => rw [fvec_castSucc]`. Conclude with `Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)`.
-/
theorem fvec_mem_Xplus (F : LFlag S r T) (i : Fin (r + 1)) : F.fl.fvec i ∈ F.fl.Xplus := by
  induction i using Fin.lastCases with
  | last => rw [fvec_last]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  | cast a => rw [fvec_castSucc]; exact Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)

/- English proof (translation)
Establish `hDr` using `PI.ScalarPairDr.W.core Λ k F F' F'' β hz hz' hz'' hX hX' hX'' hn hT hG' hG'' hs hsc`. Establish `hU1` using `UUE_eq Λ F F' hz hz' hX hX'`. Establish `hU2` using `UUE_eq Λ F F'' hz hz'' hX hX''`. Establish `hd1 : finrank E (UUE Λ F F') = 2 * r + 2`. Rewrite using `[hU1, finrank_span_eq_card (PI.PairCorankPos.W.linIndep F.fl F'.fl hG')]`.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Establish `hd2 : finrank E (UUE Λ F F'') = 2 * r + 2`. Rewrite using `[hU2, finrank_span_eq_card (PI.PairCorankPos.W.linIndep F.fl F''.fl hG'')]`. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Establish `hH2 : finrank E (Hp Λ F F'') + 1 = k`. Use `finrank_orth S (UUE Λ F F'')` as an intermediate fact. Rewrite using `[Hp]`. Use linear arithmetic over natural numbers and integers.

Establish `hH1 : finrank E (Hp Λ F F') + 1 = k`. Use `finrank_orth S (UUE Λ F F')` as an intermediate fact. Rewrite using `[Hp]`. Use linear arithmetic over natural numbers and integers. Establish `hTh : finrank E (Th Λ F F' F'' β) + 1 = k`.

Unfold `s0 at hs`. Use linear arithmetic over natural numbers and integers. Establish `hThle : Th Λ F F' F'' β ≤ Hp Λ F F'`. Introduce and unpack `x ⟨p, hp, rfl⟩`. Conclude with `((mem_ThPairs Λ F F' F'' β p).1 hp).1`.

Establish `hTh''le : Th'' Λ F F' F'' β ≤ Hp Λ F F''`. Introduce and unpack `x ⟨p, hp, rfl⟩`. Conclude with `((mem_ThPairs Λ F F' F'' β p).1 hp).2.1`. Establish `hTh''eq : Th'' Λ F F' F'' β = Hp Λ F F''`. Use `Submodule.eq_of_le_of_finrank_eq hTh''le ?_` and prove the remaining obligations.

Set `f` to `(LinearMap.snd E S.V S.V).comp (ThPairs Λ F F' F'' β).subtype`. Establish `hker : LinearMap.ker f = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `p hp`. Establish `hm` using `(mem_ThPairs Λ F F' F'' β p.1).1 p.2`.

Establish `h2 : p.1.2 = 0` using `hp`. Establish `hx1 : p.1.1 ∈ F.fl.X`. Use `hm.2.2.1` as an intermediate fact. Rewrite `this` using `[h2, sub_zero]`. Then use the resulting hypothesis. Establish `h1 : p.1.1 = 0`.

Use `eq_zero_of_orth F.fl F'.fl hG' hx1 fun b => ?_` and prove the remaining obligations. Establish `hm1` using `hm.1`. Rewrite `hm1` using `[Hp, mem_orth]`. Conclude with `hm1 _ (by rw [hU1]; exact Submodule.subset_span ⟨Sum.inr b, rfl⟩)`. Conclude with `Subtype.ext (Prod.ext h1 h2)`.

Establish `hrange : LinearMap.range f = Th'' Λ F F' F'' β`. Rewrite using `[LinearMap.range_comp, Submodule.range_subtype]`. Both sides reduce to the same expression. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker f`. Rewrite `h1` using `[hker, hrange, finrank_bot]`.

Establish `h2 : finrank E (Th Λ F F' F'' β) ≤ finrank E (ThPairs Λ F F' F'' β)` using `Submodule.finrank_map_le _ _`. Establish `h3` using `Submodule.finrank_mono hTh''le`. Use linear arithmetic over natural numbers and integers. Establish `transfer : ∀ (α : E) (v : Fin (r + 1) → E), (∀ i, S.hT (F.fl.fvec i) (α • F.fl.z + wv F' v) = 0) → ∃ v'' : Fin (r + 1) → E, v'' (Fin.last r) = v (Fin.last r) ∧ ∀ i, S.hT (F.fl.fvec i) (α • F.fl.z + wv F'' v'') = 0`. Introduce `α v hv`.

Use `set y := α • F.fl.z + wv F' v with hy`. Establish `hyo : y ∈ orth S (Xplus F)`. Rewrite using `[Xplus, mem_orth_Xplus]`. Use `⟨fun a => ?_, ?_⟩` and prove the remaining obligations. Use `hv (Fin.castSucc a)` as an intermediate fact.

Rewrite `this` using `[fvec_castSucc]`. Then use the resulting hypothesis. Use `hv (Fin.last r)` as an intermediate fact. Rewrite `this` using `[fvec_last]`. Then use the resulting hypothesis. Establish `hyU1 : y ∈ UUE Λ F F'`. Rewrite using `[hU1]`.

Use `Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl (Fin.last r), by simp [fvec_last]⟩)) (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩))` and prove the remaining obligations. Establish `hyU2 : y ∈ UUE Λ F F''`. Rewrite using `[← orth_orth S (UUE Λ F F''), mem_orth]`. Introduce `w hw`. Establish `hw' : w ∈ Th'' Λ F F' F'' β` using `by rw [hTh''eq]; exact hw`.

Take `⟨p, hp, rfl⟩` from `hw'`. Establish `hm` using `(mem_ThPairs Λ F F' F'' β p).1 hp`. Establish `e1 : S.hT p.1 y = 0`. Use `(mem_orth S).1 hm.1 _ hyU1` as an intermediate fact. Rewrite using `[hT_swap, this, star_zero]`.

Establish `e2 : S.hT (p.1 - p.2) y = 0` using `(mem_orth S).1 hyo _ (Submodule.mem_sup_left hm.2.2.1)`. Establish `: p.2 = p.1 - (p.1 - p.2)` using `by abel`. Use `show S.hT p.2 y = 0`. Rewrite using `[this, hT_sub_left, e1, e2, sub_zero]`. Establish `hsg : SgRel F F' y 0 α (v (Fin.last r))`.

Use `⟨0, Submodule.zero_mem _, ∑ a : Fin r, v (Fin.castSucc a) • F'.fl.e a, sumX_mem F' _, ?_⟩` and prove the remaining obligations. Rewrite using `[hz, hz', hy, wv_eq]`. Normalize the expressions using the abelian group laws. Take `⟨x, hx, x₂, hx₂, heq⟩` from `(hsc y ⟨hyU1, hyo⟩ y ⟨hyU2, hyo⟩ 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) (by simp) (by simp) α (v (Fin.last r))).1 hsg`. Establish `hx₂' : x₂ ∈ F''.fl.X` using `hx₂`.

Rewrite `hx₂'` using `[FlagG.X, Submodule.mem_span_range_iff_exists_fun]`. Take `⟨d, hd⟩` from `hx₂'`. Use `⟨fun i => Fin.lastCases (v (Fin.last r)) d i, by simp, fun i => ?_⟩` and prove the remaining obligations. Establish `hw'' : α • F.fl.z + wv F'' (fun i => Fin.lastCases (v (Fin.last r)) d i) = y - x`. Rewrite using `[wv_eq]`.

Simplify using `only [Fin.lastCases_castSucc, Fin.lastCases_last]`. Rewrite using `[hd]`. Rewrite `heq` using `[hz, hz'']`. Rewrite `heq` using `[sub_zero]`. Rewrite using `[heq]`.

Normalize the expressions using the abelian group laws. Rewrite using `[hw'', map_sub, hv i]`. Establish `hxo` using `X_le_orth_Xplus F.fl hx`. Rewrite using `[(mem_orth S).1 hxo _ (fvec_mem_Xplus F i), sub_zero]`. Simplify using `only [Dr1, Dr, PI.PairCorankPos.W.Dl_top, PI.PairCorankPos.W.Dl_r] at hDr ⊢`.

Use `set A' := Zhat F.fl F'.fl with hA'def`. Use `set A'' := Zhat F.fl F''.fl with hA''def`. Distinguish the cases in `h0 : (A'.submatrix Fin.castSucc Fin.castSucc).det = 0`. Rewrite using `[h0, hDr.1 h0, mul_zero, mul_zero]`. Distinguish the cases in `hA : A'.det = 0`.

Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hA`. Establish `hvl : v (Fin.last r) ≠ 0`. Introduce `hl`. Apply `h0` to reduce the goal to its premises. Apply `Matrix.exists_mulVec_eq_zero_iff.1` to reduce the goal to its premises.

Use `⟨fun a => v (Fin.castSucc a), ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Apply `hv0` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Proceed by induction on `i using Fin.lastCases with`.

Consider the case `last => exact hl`. Consider the case `cast a => exact congrFun h a`. Use function extensionality and compare the values at `a`. Use `congrFun hv (Fin.castSucc a)` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hl, mul_zero, add_zero, Pi.zero_apply] at this`.

Simplify `this` using `[Matrix.mulVec, dotProduct, Matrix.submatrix_apply]`. Take `⟨v'', hl'', hv''⟩` from `transfer 0 v (fun i => by rw [zero_smul, zero_add, hT_wv, hv]; rfl)`. Establish `hA'' : A''.det = 0`. Use `Matrix.exists_mulVec_eq_zero_iff.1 ⟨v'', fun h => hvl (by rw [← hl'', h]; rfl), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Use `hv'' i` as an intermediate fact. Rewrite `this` using `[zero_smul, zero_add, hT_wv]`. Then use the resulting hypothesis. Rewrite using `[hA, hA'', zero_mul, zero_mul]`. Use `set b : Fin (r + 1) → E := Pi.single (Fin.last r) T with hb set v := A'⁻¹ *ᵥ b with hvdef`. Establish `hAv : A' *ᵥ v = b`.

Rewrite using `[hvdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hA), Matrix.one_mulVec]`. Establish `hvz : ∀ i, S.hT (F.fl.fvec i) ((1 : E) • F.fl.z + wv F' v) = 0` using `fun i => by`. Rewrite using `[one_smul, map_add, hermitian_frame_z, hT_wv, hAv]`. Distinguish the cases in `hi : i = Fin.last r`. Substitute `hi` using the available equality.

Simplify using `[hb]`. Simplify using `[hb, hi, Pi.single_eq_of_ne hi]`. Take `⟨v'', hl'', hv''⟩` from `transfer 1 v hvz`. Establish `hA''v : A'' *ᵥ v'' = b` using `funext fun i => by`. Use `hv'' i` as an intermediate fact.

Rewrite `this` using `[one_smul, map_add, hermitian_frame_z, hT_wv]`. Distinguish the cases in `hi : i = Fin.last r`. Substitute `hi` using the available equality. Rewrite `this` using `[if_pos rfl]`. Simplify using `only [hb, Pi.single_eq_same]`.

Take the linear combination `this`. Rewrite `this` using `[if_neg hi]`. Simplify using `only [hb, Pi.single_eq_of_ne hi]`. Take the linear combination `this`. Establish `c1` using `cramer_last A' v T hAv`.

Establish `c2` using `cramer_last A'' v'' T hA''v`. Rewrite `c2` using `[hl'']`. Apply `mul_left_cancel₀ hT` to reduce the goal to its premises. Take the linear combination `(-A'.det) * c2 + A''.det * c1`.
-/
theorem zeta_core (k : ℕ) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) (hz'' : F''.zt = F''.fl.z)
    (hX : Xsp F ≤ spanE S (XLam Λ F)) (hX' : Xsp F' ≤ spanE S (XLam Λ F'))
    (hX'' : Xsp F'' ≤ spanE S (XLam Λ F''))
    (hn : finrank E S.V = k + 2 * r + 1) (hT : T ≠ 0)
    (hG' : Gval F F' ≠ 0) (hG'' : Gval F F'' ≠ 0)
    (hs : s0 Λ F F' F'' β k = 1) (hsc : IsScalar Λ F F' F'' β) :
    Dr1 F F' * Dr F F'' = Dr1 F F'' * Dr F F' := by
  have hDr := PI.ScalarPairDr.W.core Λ k F F' F'' β hz hz' hz'' hX hX' hX'' hn hT hG' hG'' hs hsc
  have hU1 := UUE_eq Λ F F' hz hz' hX hX'
  have hU2 := UUE_eq Λ F F'' hz hz'' hX hX''
  have hd1 : finrank E (UUE Λ F F') = 2 * r + 2 := by
    rw [hU1, finrank_span_eq_card (PI.PairCorankPos.W.linIndep F.fl F'.fl hG')]
    simp
    omega
  have hd2 : finrank E (UUE Λ F F'') = 2 * r + 2 := by
    rw [hU2, finrank_span_eq_card (PI.PairCorankPos.W.linIndep F.fl F''.fl hG'')]
    simp
    omega
  have hH2 : finrank E (Hp Λ F F'') + 1 = k := by
    have := finrank_orth S (UUE Λ F F'')
    rw [Hp]
    omega
  have hH1 : finrank E (Hp Λ F F') + 1 = k := by
    have := finrank_orth S (UUE Λ F F')
    rw [Hp]
    omega
  have hTh : finrank E (Th Λ F F' F'' β) + 1 = k := by
    unfold s0 at hs
    omega
  have hThle : Th Λ F F' F'' β ≤ Hp Λ F F' := by
    rintro x ⟨p, hp, rfl⟩
    exact ((mem_ThPairs Λ F F' F'' β p).1 hp).1
  have hTh''le : Th'' Λ F F' F'' β ≤ Hp Λ F F'' := by
    rintro x ⟨p, hp, rfl⟩
    exact ((mem_ThPairs Λ F F' F'' β p).1 hp).2.1
  have hTh''eq : Th'' Λ F F' F'' β = Hp Λ F F'' := by
    refine Submodule.eq_of_le_of_finrank_eq hTh''le ?_
    let f := (LinearMap.snd E S.V S.V).comp (ThPairs Λ F F' F'' β).subtype
    have hker : LinearMap.ker f = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro p hp
      have hm := (mem_ThPairs Λ F F' F'' β p.1).1 p.2
      have h2 : p.1.2 = 0 := hp
      have hx1 : p.1.1 ∈ F.fl.X := by
        have := hm.2.2.1
        rwa [h2, sub_zero] at this
      have h1 : p.1.1 = 0 := by
        refine eq_zero_of_orth F.fl F'.fl hG' hx1 fun b => ?_
        have hm1 := hm.1
        rw [Hp, mem_orth] at hm1
        exact hm1 _ (by rw [hU1]; exact Submodule.subset_span ⟨Sum.inr b, rfl⟩)
      exact Subtype.ext (Prod.ext h1 h2)
    have hrange : LinearMap.range f = Th'' Λ F F' F'' β := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
      rfl
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    rw [hker, hrange, finrank_bot] at h1
    have h2 : finrank E (Th Λ F F' F'' β) ≤ finrank E (ThPairs Λ F F' F'' β) :=
      Submodule.finrank_map_le _ _
    have h3 := Submodule.finrank_mono hTh''le
    omega

  have transfer : ∀ (α : E) (v : Fin (r + 1) → E),
      (∀ i, S.hT (F.fl.fvec i) (α • F.fl.z + wv F' v) = 0) →
      ∃ v'' : Fin (r + 1) → E, v'' (Fin.last r) = v (Fin.last r) ∧
        ∀ i, S.hT (F.fl.fvec i) (α • F.fl.z + wv F'' v'') = 0 := by
    intro α v hv
    set y := α • F.fl.z + wv F' v with hy
    have hyo : y ∈ orth S (Xplus F) := by
      rw [Xplus, mem_orth_Xplus]
      refine ⟨fun a => ?_, ?_⟩
      · have := hv (Fin.castSucc a); rwa [fvec_castSucc] at this
      · have := hv (Fin.last r); rwa [fvec_last] at this
    have hyU1 : y ∈ UUE Λ F F' := by
      rw [hU1]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _
        (Submodule.subset_span ⟨Sum.inl (Fin.last r), by simp [fvec_last]⟩))
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩))
    have hyU2 : y ∈ UUE Λ F F'' := by
      rw [← orth_orth S (UUE Λ F F''), mem_orth]
      intro w hw
      have hw' : w ∈ Th'' Λ F F' F'' β := by rw [hTh''eq]; exact hw
      obtain ⟨p, hp, rfl⟩ := hw'
      have hm := (mem_ThPairs Λ F F' F'' β p).1 hp
      have e1 : S.hT p.1 y = 0 := by
        have := (mem_orth S).1 hm.1 _ hyU1
        rw [hT_swap, this, star_zero]
      have e2 : S.hT (p.1 - p.2) y = 0 :=
        (mem_orth S).1 hyo _ (Submodule.mem_sup_left hm.2.2.1)
      have : p.2 = p.1 - (p.1 - p.2) := by abel
      show S.hT p.2 y = 0
      rw [this, hT_sub_left, e1, e2, sub_zero]
    have hsg : SgRel F F' y 0 α (v (Fin.last r)) := by
      refine ⟨0, Submodule.zero_mem _, ∑ a : Fin r, v (Fin.castSucc a) • F'.fl.e a, sumX_mem F' _, ?_⟩
      rw [hz, hz', hy, wv_eq]
      abel
    obtain ⟨x, hx, x₂, hx₂, heq⟩ := (hsc y ⟨hyU1, hyo⟩ y ⟨hyU2, hyo⟩ 0 (Submodule.zero_mem _) 0
      (Submodule.zero_mem _) (by simp) (by simp) α (v (Fin.last r))).1 hsg
    have hx₂' : x₂ ∈ F''.fl.X := hx₂
    rw [FlagG.X, Submodule.mem_span_range_iff_exists_fun] at hx₂'
    obtain ⟨d, hd⟩ := hx₂'
    refine ⟨fun i => Fin.lastCases (v (Fin.last r)) d i, by simp, fun i => ?_⟩
    have hw'' : α • F.fl.z + wv F'' (fun i => Fin.lastCases (v (Fin.last r)) d i) = y - x := by
      rw [wv_eq]
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
      rw [hd]
      rw [hz, hz''] at heq
      rw [sub_zero] at heq
      rw [heq]
      abel
    rw [hw'', map_sub, hv i]
    have hxo := X_le_orth_Xplus F.fl hx
    rw [(mem_orth S).1 hxo _ (fvec_mem_Xplus F i), sub_zero]
  simp only [Dr1, Dr, PI.PairCorankPos.W.Dl_top, PI.PairCorankPos.W.Dl_r] at hDr ⊢
  set A' := Zhat F.fl F'.fl with hA'def
  set A'' := Zhat F.fl F''.fl with hA''def
  by_cases h0 : (A'.submatrix Fin.castSucc Fin.castSucc).det = 0
  · rw [h0, hDr.1 h0, mul_zero, mul_zero]
  by_cases hA : A'.det = 0
  · obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hA
    have hvl : v (Fin.last r) ≠ 0 := by
      intro hl
      apply h0
      apply Matrix.exists_mulVec_eq_zero_iff.1
      refine ⟨fun a => v (Fin.castSucc a), ?_, ?_⟩
      · intro h
        apply hv0
        funext i
        induction i using Fin.lastCases with
        | last => exact hl
        | cast a => exact congrFun h a
      · funext a
        have := congrFun hv (Fin.castSucc a)
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hl, mul_zero, add_zero,
          Pi.zero_apply] at this
        simpa [Matrix.mulVec, dotProduct, Matrix.submatrix_apply] using this
    obtain ⟨v'', hl'', hv''⟩ := transfer 0 v (fun i => by rw [zero_smul, zero_add, hT_wv, hv]; rfl)
    have hA'' : A''.det = 0 := by
      refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨v'', fun h => hvl (by rw [← hl'', h]; rfl), ?_⟩
      funext i
      have := hv'' i
      rwa [zero_smul, zero_add, hT_wv] at this
    rw [hA, hA'', zero_mul, zero_mul]
  · set b : Fin (r + 1) → E := Pi.single (Fin.last r) T with hb
    set v := A'⁻¹ *ᵥ b with hvdef
    have hAv : A' *ᵥ v = b := by
      rw [hvdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hA), Matrix.one_mulVec]
    have hvz : ∀ i, S.hT (F.fl.fvec i) ((1 : E) • F.fl.z + wv F' v) = 0 := fun i => by
      rw [one_smul, map_add, hermitian_frame_z, hT_wv, hAv]
      by_cases hi : i = Fin.last r
      · subst hi; simp [hb]
      · simp [hb, hi, Pi.single_eq_of_ne hi]
    obtain ⟨v'', hl'', hv''⟩ := transfer 1 v hvz
    have hA''v : A'' *ᵥ v'' = b := funext fun i => by
      have := hv'' i
      rw [one_smul, map_add, hermitian_frame_z, hT_wv] at this
      by_cases hi : i = Fin.last r
      · subst hi
        rw [if_pos rfl] at this
        simp only [hb, Pi.single_eq_same]
        linear_combination this
      · rw [if_neg hi] at this
        simp only [hb, Pi.single_eq_of_ne hi]
        linear_combination this
    have c1 := cramer_last A' v T hAv
    have c2 := cramer_last A'' v'' T hA''v
    rw [hl''] at c2
    apply mul_left_cancel₀ hT
    linear_combination (-A'.det) * c2 + A''.det * c1

end ZetaNonvanishing₂

end Formalism.L2.SG.Pf.ScalKindPf

namespace Formalism.L2.SG.Pf.ScalKindPf

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
open Formalism.L2.SG.LsDatumB
open scoped Matrix

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

/- English proof (translation)
Establish `hrow` using `hrows.1 P.lam P.mem`. Establish `hXF : Xsp (lf D F0) ≤ spanE (VS D) (XLam P.lam (lf D F0))`. Rewrite using `[hrow.2.2]`. Conclude with `PI.ScalarPairDr.W.X_le_spanE_XS D F0`. Establish `hXx : Xsp P.fst.1 ≤ spanE (VS D) (XLam P.lam P.fst.1)`.

Rewrite using `[P.fst.2.2.2.2]`. Conclude with `PI.ScalarPairDr.W.X_le_spanE_XS D P.fst.1.fl`. Establish `hXy : Xsp P.snd.1 ≤ spanE (VS D) (XLam P.lam P.snd.1)`. Rewrite using `[P.snd.2.2.2.2]`. Conclude with `PI.ScalarPairDr.W.X_le_spanE_XS D P.snd.1.fl`.

Conclude with `zeta_core P.lam D.R.k (lf D F0) P.fst.1 P.snd.1 P.beta rfl P.fst.2.1.2 P.snd.2.1.2 hXF hXx hXy (PI.UnitaryGroupMassFormula.BetaLUniq.finrank_hS D) (PI.ScalarPairDr.W.Tu_ne_zero D u) P.G_fst P.G_snd hsp.1 hsp.2`.
-/
theorem scalarZeta (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hrows : IsRowReps D F0 what₂)
    (P : Formalism.L2.SG.Corank.Pair D u u' F0 what₂) (hsp : P.scalarPair) :
    Dr1 (lf D F0) P.fst.1 * Dr (lf D F0) P.snd.1 = Dr1 (lf D F0) P.snd.1 * Dr (lf D F0) P.fst.1 := by
  have hrow := hrows.1 P.lam P.mem
  have hXF : Xsp (lf D F0) ≤ spanE (VS D) (XLam P.lam (lf D F0)) := by
    rw [hrow.2.2]
    exact PI.ScalarPairDr.W.X_le_spanE_XS D F0
  have hXx : Xsp P.fst.1 ≤ spanE (VS D) (XLam P.lam P.fst.1) := by
    rw [P.fst.2.2.2.2]
    exact PI.ScalarPairDr.W.X_le_spanE_XS D P.fst.1.fl
  have hXy : Xsp P.snd.1 ≤ spanE (VS D) (XLam P.lam P.snd.1) := by
    rw [P.snd.2.2.2.2]
    exact PI.ScalarPairDr.W.X_le_spanE_XS D P.snd.1.fl
  exact zeta_core P.lam D.R.k (lf D F0) P.fst.1 P.snd.1 P.beta rfl P.fst.2.1.2 P.snd.2.1.2 hXF hXx hXy
    (PI.UnitaryGroupMassFormula.BetaLUniq.finrank_hS D) (PI.ScalarPairDr.W.Tu_ne_zero D u) P.G_fst P.G_snd hsp.1 hsp.2

/- English proof (translation)
Take `⟨F', ⟨h, hmk⟩, -, hcell⟩` from `hat`. Establish `hTF` using `Formalism.L2.SG.Closed.TermFun_holds D u u' F0 Λ (hrows.1 Λ hΛ)`. Establish `hEq` using `Formalism.L2.SG.Closed.TermEqIff_holds D u u' F0 Λ (hrows.1 Λ hΛ)`. Establish `hrel` using `(hEq ⟨F', h⟩ x).1 hmk`. Conclude with `(hTF.2.1 ⟨F', h⟩ x hrel w).1 hcell`.
-/
theorem cell_of_at {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (hrows : IsRowReps D F0 what₂)
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Λ ∈ what₂) (x : Carrier (PD D Λ (lf D F0) u'))
    {w : Point D.host.E (D.R.rS + 1)} (hat : AtPt Λ (lf D F0) (PD D Λ (lf D F0) u') (mk Λ (lf D F0) _ x) w) :
    IsInCell (ZhatOM (ZhatL (lf D F0) x.1)) w := by
  obtain ⟨F', ⟨h, hmk⟩, -, hcell⟩ := hat
  have hTF := Formalism.L2.SG.Closed.TermFun_holds D u u' F0 Λ (hrows.1 Λ hΛ)
  have hEq := Formalism.L2.SG.Closed.TermEqIff_holds D u u' F0 Λ (hrows.1 Λ hΛ)
  have hrel := (hEq ⟨F', h⟩ x).1 hmk
  exact (hTF.2.1 ⟨F', h⟩ x hrel w).1 hcell

def sgnL (l : ℕ) : D.host.E := ∏ b : Fin l, ((-1 : D.host.E) ^ (D.R.rS - b.val))

/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)`.
-/
theorem sgnL_ne (l : ℕ) : sgnL (D := D) l ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)

/- English proof (translation)
Unfold `sgnL`. Rewrite using `[Fin.prod_univ_castSucc]`. Simplify using the standard rewrite rules.
-/
theorem sgnL_succ : sgnL (D := D) (D.R.rS + 1) = sgnL (D := D) D.R.rS := by
  unfold sgnL
  rw [Fin.prod_univ_castSucc]
  simp

/- English proof (translation)
Take `⟨L, U, hL, hU, hZ⟩` from `hc`. Establish `e1 : ((ptMat w).submatrix (Fin.castLE h) (Fin.castLE h)).det = (∏ b : Fin l, ((-1 : D.host.E) ^ (D.R.rS - b.val))) * ((ZhatL (lf D F0) F').submatrix (Fin.castLE h) (Fin.castLE h)).det`. Rewrite using `[← det_sub_loUni h L (ptMat w) U hL hU, ← hZ]`. Conclude with `det_sub_ZhatOM h _`. Establish `hD : Dmin w l = ((ptMat w).submatrix (Fin.castLE h) (Fin.castLE h)).det`.

Unfold `Dmin`. Rewrite using `[dif_pos h]`. Establish `hM : leadMinorE (ZhatL (lf D F0) F') l = ((ZhatL (lf D F0) F').submatrix (Fin.castLE h) (Fin.castLE h)).det`. Unfold `leadMinorE`. Rewrite using `[dif_pos h]`.

Rewrite using `[hD, hM, e1]`. Both sides reduce to the same expression.
-/
theorem dmin_eq {u u' : D.what₂.Word} {F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {w : Point D.host.E (D.R.rS + 1)} (hc : IsInCell (ZhatOM (ZhatL (lf D F0) F')) w) (l : ℕ) (h : l ≤ D.R.rS + 1) :
    Dmin w l = sgnL l * leadMinorE (ZhatL (lf D F0) F') l := by
  obtain ⟨L, U, hL, hU, hZ⟩ := hc
  have e1 : ((ptMat w).submatrix (Fin.castLE h) (Fin.castLE h)).det =
      (∏ b : Fin l, ((-1 : D.host.E) ^ (D.R.rS - b.val))) *
        ((ZhatL (lf D F0) F').submatrix (Fin.castLE h) (Fin.castLE h)).det := by
    rw [← det_sub_loUni h L (ptMat w) U hL hU, ← hZ]
    exact det_sub_ZhatOM h _
  have hD : Dmin w l = ((ptMat w).submatrix (Fin.castLE h) (Fin.castLE h)).det := by
    unfold Dmin
    rw [dif_pos h]
  have hM : leadMinorE (ZhatL (lf D F0) F') l =
      ((ZhatL (lf D F0) F').submatrix (Fin.castLE h) (Fin.castLE h)).det := by
    unfold leadMinorE
    rw [dif_pos h]
  rw [hD, hM, e1]
  rfl

/- English proof (translation)
Establish `h1` using `dmin_eq hc D.R.rS (Nat.le_succ _)`. Establish `h2` using `dmin_eq hc (D.R.rS + 1) le_rfl`. Unfold `kind zetaOf`. Rewrite using `[h1, h2, sgnL_succ]`. Establish `hs` using `sgnL_ne (D := D) D.R.rS`.

Distinguish the cases in `h0 : leadMinorE (ZhatL (lf D F0) F') D.R.rS = 0`. Establish `h0' : Dr (lf D F0) F' = 0` using `h0`. Rewrite using `[if_pos (by rw [h0, mul_zero]), if_pos h0']`. Establish `h0' : Dr (lf D F0) F' ≠ 0` using `h0`. Rewrite using `[if_neg (mul_ne_zero hs h0), if_neg h0', mul_div_mul_left _ _ hs]`.

Both sides reduce to the same expression.
-/
theorem kind_eq {u u' : D.what₂.Word} {F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {w : Point D.host.E (D.R.rS + 1)} (hc : IsInCell (ZhatOM (ZhatL (lf D F0) F')) w) :
    kind w = if Dr (lf D F0) F' = 0 then none else some (Dr1 (lf D F0) F' / Dr (lf D F0) F') := by
  have h1 := dmin_eq hc D.R.rS (Nat.le_succ _)
  have h2 := dmin_eq hc (D.R.rS + 1) le_rfl
  unfold kind zetaOf
  rw [h1, h2, sgnL_succ]
  have hs := sgnL_ne (D := D) D.R.rS
  by_cases h0 : leadMinorE (ZhatL (lf D F0) F') D.R.rS = 0
  · have h0' : Dr (lf D F0) F' = 0 := h0
    rw [if_pos (by rw [h0, mul_zero]), if_pos h0']
  · have h0' : Dr (lf D F0) F' ≠ 0 := h0
    rw [if_neg (mul_ne_zero hs h0), if_neg h0', mul_div_mul_left _ _ hs]
    rfl

end D7

end Formalism.L2.SG.Pf.ScalKindPf

namespace Formalism.L2.SG.Pf

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `γ γ' w w' hγ hγ' ⟨P, hP1, hP2, hsp⟩`. Substitute `hP1 hP2` using the available equality. Establish `hat1 : AtPt P.lam (lf D F0) (PD D P.lam (lf D F0) u') (mk P.lam (lf D F0) _ P.fst) w` using `hγ.2`. Establish `hat2 : AtPt P.lam (lf D F0) (PD D P.lam (lf D F0) u') (mk P.lam (lf D F0) _ P.snd) w'` using `hγ'.2`. Establish `hc1` using `ScalKindPf.cell_of_at hrows P.mem P.fst hat1`.

Establish `hc2` using `ScalKindPf.cell_of_at hrows P.mem P.snd hat2`. Rewrite using `[ScalKindPf.kind_eq hc1, ScalKindPf.kind_eq hc2]`. Establish `hDr` using `Formalism.L2.SG.Closed.ScalarDr_holds D u u' F0 what₂ hrows P hsp`. Establish `hZ` using `ScalKindPf.scalarZeta u u' F0 what₂ hrows P hsp`. Use `split_ifs with h1 h2 h2`.

Both sides reduce to the same expression. Conclude with `absurd (hDr.1 h1) h2`. Conclude with `absurd (hDr.2 h2) h1`. Rewrite using `[Option.some.injEq, div_eq_div_iff h1 h2]`. Conclude with `hZ`.
-/
theorem scalKind_of {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (hrows : IsRowReps D F0 what₂) :
    ScalKind u u' F0 what₂ := by
  intro γ γ' w w' hγ hγ' ⟨P, hP1, hP2, hsp⟩
  subst hP1 hP2
  have hat1 : AtPt P.lam (lf D F0) (PD D P.lam (lf D F0) u') (mk P.lam (lf D F0) _ P.fst) w := hγ.2
  have hat2 : AtPt P.lam (lf D F0) (PD D P.lam (lf D F0) u') (mk P.lam (lf D F0) _ P.snd) w' := hγ'.2
  have hc1 := ScalKindPf.cell_of_at hrows P.mem P.fst hat1
  have hc2 := ScalKindPf.cell_of_at hrows P.mem P.snd hat2
  rw [ScalKindPf.kind_eq hc1, ScalKindPf.kind_eq hc2]
  have hDr := Formalism.L2.SG.Closed.ScalarDr_holds D u u' F0 what₂ hrows P hsp
  have hZ := ScalKindPf.scalarZeta u u' F0 what₂ hrows P hsp
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hDr.1 h1) h2
  · exact absurd (hDr.2 h2) h1
  · rw [Option.some.injEq, div_eq_div_iff h1 h2]
    exact hZ

end Formalism.L2.SG.Pf

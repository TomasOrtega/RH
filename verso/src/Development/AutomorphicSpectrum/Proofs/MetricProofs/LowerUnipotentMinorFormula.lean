import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.LowMinor

open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

variable {N : ℕ}

/- English proof (translation)
Establish `key : minorIJ X C C = minorIJ Xᵀ C C`. Rewrite using `[minorIJ_eq_det X C C C.card rfl rfl, minorIJ_eq_det Xᵀ C C C.card rfl rfl, ← Matrix.transpose_submatrix, Matrix.det_transpose]`. Rewrite using `[key, minorIJ_self_of_triangular Xᵀ (fun i j hij => by simpa [Matrix.transpose_apply] using hX.2 j i hij) C]`. Conclude with `Finset.prod_eq_one (fun c _ => hX.1 c)`.
-/
theorem minorIJ_self_of_isLowerUni {X : Matrix (Fin N) (Fin N) ℂ} (hX : IsLowerUni X) (C : Finset (Fin N)) :
    minorIJ X C C = 1 := by
  have key : minorIJ X C C = minorIJ Xᵀ C C := by
    rw [minorIJ_eq_det X C C C.card rfl rfl, minorIJ_eq_det Xᵀ C C C.card rfl rfl,
      ← Matrix.transpose_submatrix, Matrix.det_transpose]
  rw [key, minorIJ_self_of_triangular Xᵀ (fun i j hij => by simpa [Matrix.transpose_apply] using hX.2 j i hij) C]
  exact Finset.prod_eq_one (fun c _ => hX.1 c)

/- English proof (translation)
Establish `ha : a' ∉ C` using `fun h => absurd (hmax a' h) (not_le.mpr hlt)`. Take `⟨n, hn⟩ : ∃ n, C.card = n + 1` from `⟨C.card - 1, by have := Finset.card_pos.mpr ⟨b', hb⟩; omega⟩`. Establish `hR : (insert a' (C.erase b')).card = n + 1`. Rewrite using `[Finset.card_insert_of_notMem (fun h => ha (Finset.mem_of_mem_erase h)), Finset.card_erase_of_mem hb, hn]`. Both sides reduce to the same expression.

Use `set eC := C.orderEmbOfFin hn with heC`. Establish `hlast : eC (Fin.last n) = b'`. Establish `hmem : b' ∈ Set.range eC` using `by rw [heC, Finset.range_orderEmbOfFin]; exact hb`. Take `⟨k, hk⟩` from `hmem`. Break down `(Fin.le_last k).lt_or_eq with h | h` into its components or cases.

Establish `h1 : eC k < eC (Fin.last n)` using `eC.strictMono h`. Establish `h2 : eC (Fin.last n) ∈ C` using `Finset.orderEmbOfFin_mem C hn _`. Conclude with `absurd (hmax _ h2) (not_le.mpr (hk ▸ h1))`. Rewrite using `[← h, hk]`. Establish `hlt' : ∀ k : Fin (n + 1), k ≠ Fin.last n → eC k < b'` using `fun k hk => hlast ▸ eC.strictMono (lt_of_le_of_ne (Fin.le_last k) hk)`.

Set `f : Fin (n + 1) → Fin N` to `fun k => if k = Fin.last n then a' else eC k`. Establish `hfmono : StrictMono f`. Introduce `i j hij`. Establish `hi : i ≠ Fin.last n` using `ne_of_lt (lt_of_lt_of_le hij (Fin.le_last j))`. Simplify using `only [f, if_neg hi]`.

Distinguish the cases in `hj : j = Fin.last n`. Rewrite using `[if_pos hj]`. Conclude with `(hlt' i hi).trans hlt`. Rewrite using `[if_neg hj]`. Conclude with `eC.strictMono hij`.

Establish `hfmem : ∀ k, f k ∈ insert a' (C.erase b')`. Introduce `k`. Simplify using `only [f]`. Use `split_ifs with hk`. Conclude with `Finset.mem_insert_self _ _`.

Conclude with `Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨(hlt' k hk).ne, Finset.orderEmbOfFin_mem C hn k⟩)`. Establish `hR' : ⇑((insert a' (C.erase b')).orderEmbOfFin hR) = f` using `(Finset.orderEmbOfFin_unique hR hfmem hfmono).symm`. Rewrite using `[minorIJ_eq_det X _ C (n + 1) hR hn, hR', Matrix.det_of_lowerTriangular]`. Establish `h1 : ∀ k : Fin n, X.submatrix f eC k.castSucc k.castSucc = 1`. Introduce `k`.

Use `show X (f k.castSucc) (eC k.castSucc) = 1`. Simplify using `only [f, if_neg (Fin.castSucc_lt_last k).ne]`. Conclude with `hX.1 _`. Rewrite using `[Fin.prod_univ_castSucc, Finset.prod_eq_one (fun k _ => h1 k), one_mul]`. Use `show X (if Fin.last n = Fin.last n then a' else eC (Fin.last n)) (eC (Fin.last n)) = X a' b'`.

Rewrite using `[if_pos rfl, hlast]`. Introduce `i j hij`. Establish `hij' : i < j` using `OrderDual.toDual_lt_toDual.mp hij`. Establish `hi : i ≠ Fin.last n` using `ne_of_lt (lt_of_lt_of_le hij' (Fin.le_last j))`. Simplify using `only [Matrix.submatrix_apply, f, if_neg hi]`.

Conclude with `hX.2 _ _ (eC.strictMono hij')`.
-/
theorem minorIJ_insert_erase_of_isLowerUni {X : Matrix (Fin N) (Fin N) ℂ} (hX : IsLowerUni X) {C : Finset (Fin N)}
    {a' b' : Fin N} (hb : b' ∈ C) (hmax : ∀ c ∈ C, c ≤ b') (hlt : b' < a') :
    minorIJ X (insert a' (C.erase b')) C = X a' b' := by
  have ha : a' ∉ C := fun h => absurd (hmax a' h) (not_le.mpr hlt)
  obtain ⟨n, hn⟩ : ∃ n, C.card = n + 1 :=
    ⟨C.card - 1, by have := Finset.card_pos.mpr ⟨b', hb⟩; omega⟩
  have hR : (insert a' (C.erase b')).card = n + 1 := by
    rw [Finset.card_insert_of_notMem (fun h => ha (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem hb, hn]
    rfl
  set eC := C.orderEmbOfFin hn with heC
  have hlast : eC (Fin.last n) = b' := by
    have hmem : b' ∈ Set.range eC := by rw [heC, Finset.range_orderEmbOfFin]; exact hb
    obtain ⟨k, hk⟩ := hmem
    rcases (Fin.le_last k).lt_or_eq with h | h
    · have h1 : eC k < eC (Fin.last n) := eC.strictMono h
      have h2 : eC (Fin.last n) ∈ C := Finset.orderEmbOfFin_mem C hn _
      exact absurd (hmax _ h2) (not_le.mpr (hk ▸ h1))
    · rw [← h, hk]
  have hlt' : ∀ k : Fin (n + 1), k ≠ Fin.last n → eC k < b' := fun k hk =>
    hlast ▸ eC.strictMono (lt_of_le_of_ne (Fin.le_last k) hk)
  let f : Fin (n + 1) → Fin N := fun k => if k = Fin.last n then a' else eC k
  have hfmono : StrictMono f := by
    intro i j hij
    have hi : i ≠ Fin.last n := ne_of_lt (lt_of_lt_of_le hij (Fin.le_last j))
    simp only [f, if_neg hi]
    by_cases hj : j = Fin.last n
    · rw [if_pos hj]; exact (hlt' i hi).trans hlt
    · rw [if_neg hj]; exact eC.strictMono hij
  have hfmem : ∀ k, f k ∈ insert a' (C.erase b') := by
    intro k
    simp only [f]
    split_ifs with hk
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨(hlt' k hk).ne, Finset.orderEmbOfFin_mem C hn k⟩)
  have hR' : ⇑((insert a' (C.erase b')).orderEmbOfFin hR) = f :=
    (Finset.orderEmbOfFin_unique hR hfmem hfmono).symm
  rw [minorIJ_eq_det X _ C (n + 1) hR hn, hR', Matrix.det_of_lowerTriangular]
  · have h1 : ∀ k : Fin n, X.submatrix f eC k.castSucc k.castSucc = 1 := by
      intro k
      show X (f k.castSucc) (eC k.castSucc) = 1
      simp only [f, if_neg (Fin.castSucc_lt_last k).ne]
      exact hX.1 _
    rw [Fin.prod_univ_castSucc, Finset.prod_eq_one (fun k _ => h1 k), one_mul]
    show X (if Fin.last n = Fin.last n then a' else eC (Fin.last n)) (eC (Fin.last n)) = X a' b'
    rw [if_pos rfl, hlast]
  · intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    have hi : i ≠ Fin.last n := ne_of_lt (lt_of_lt_of_le hij' (Fin.le_last j))
    simp only [Matrix.submatrix_apply, f, if_neg hi]
    exact hX.2 _ _ (eC.strictMono hij')

/- English proof (translation)
Establish `hc` using `c.isLt`. Use `⟨?_, fun x hx => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `simp only [stepCols, stepOf] split_ifs all_goals (try simp) all_goals omega`. Establish `hx'` using `x.isLt`. Simplify using `only [stepCols, stepOf] at hx`.

Rewrite using `[Fin.le_iff_val_le_val]`. Use `split_ifs at hx`. Apply the tactic sequence `all_goals (try simp at hx)`. Apply the tactic sequence `all_goals omega`.
-/
theorem mem_stepCols_stepOf (N j : ℕ) (c : Fin N) :
    c ∈ stepCols N j (stepOf N j c) ∧ ∀ x ∈ stepCols N j (stepOf N j c), x ≤ c := by
  have hc := c.isLt
  refine ⟨?_, fun x hx => ?_⟩
  · simp only [stepCols, stepOf]
    split_ifs
    all_goals (try simp)
    all_goals omega
  · have hx' := x.isLt
    simp only [stepCols, stepOf] at hx
    rw [Fin.le_iff_val_le_val]
    split_ifs at hx
    all_goals (try simp at hx)
    all_goals omega

/- English proof (translation)
Take `⟨hb, hmax⟩` from `mem_stepCols_stepOf N j b'`. Conclude with `⟨minorIJ_self_of_isLowerUni hX _, minorIJ_insert_erase_of_isLowerUni hX hb hmax hlt⟩`.
-/
theorem minorIJ_stepCols_of_isLowerUni (N j : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (a' b' : Fin N) (_hj : j ≤ N)
    (_hd : IsBlockDiag j X) (hX : IsLowerUni X) (hlt : b' < a') (_hs : (a' : ℕ) < N - j ↔ (b' : ℕ) < N - j) :
    minorIJ X (stepCols N j (stepOf N j b')) (stepCols N j (stepOf N j b')) = 1 ∧
      minorIJ X (insert a' ((stepCols N j (stepOf N j b')).erase b')) (stepCols N j (stepOf N j b')) = X a' b' := by
  obtain ⟨hb, hmax⟩ := mem_stepCols_stepOf N j b'
  exact ⟨minorIJ_self_of_isLowerUni hX _, minorIJ_insert_erase_of_isLowerUni hX hb hmax hlt⟩

end GlobalTheory.CompanionTheory.Ar.PB.WMan.LowMinor

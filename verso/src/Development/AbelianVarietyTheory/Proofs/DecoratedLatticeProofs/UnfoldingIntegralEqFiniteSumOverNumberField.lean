import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizerStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralPeriodicCompactSupportEqFiniteSumStatement
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.UnfoldSum

section Coord
variable {E k : Type} [Field E] [Field k] (ι : E →+* k)
variable {U U' : Type} [Fintype U] [DecidableEq U] [Fintype U'] [DecidableEq U'] {c n n' : ℕ}
  {d : U ≃ Fin n} {d' : U' ≃ Fin n'} {e : U ⊕ Fin c ≃ Fin (n + c)} {e' : U' ⊕ Fin (c + 1) ≃ Fin (n' + (c + 1))}

/- English proof (translation)
The claim follows from `he _`.
-/
theorem ord_inl (he : IsOrd (yPos (fun a => (d a).val) n) e) (a : U) : (e (.inl a)).val = (d a).val := he _

/- English proof (translation)
The claim follows from `he _`.
-/
theorem ord_inr (he : IsOrd (yPos (fun a => (d a).val) n) e) (i : Fin c) : (e (.inr i)).val = n + i.val := he _

/- English proof (translation)
The claim follows from `he _`.
-/
theorem ord_inl' (he : IsOrd (yPos (fun a => (d' a).val) n') e') (a : U') : (e' (.inl a)).val = (d' a).val := he _

/- English proof (translation)
The claim follows from `he _`.
-/
theorem ord_inr' (he : IsOrd (yPos (fun a => (d' a).val) n') e') (i : Fin (c + 1)) : (e' (.inr i)).val = n' + i.val := he _

/- English proof (translation)
Take `⟨r, s⟩` from `rs`. Apply the tactic sequence `rcases r with r | l <;> rcases s with s | i`. Simplify using `only [Free, Loc.IsFree, ord_inl he, ord_inl' he', false_iff]`. Use `(d' s).2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Simplify using `only [Free, Loc.IsFree, ord_inl he, ord_inr' he']`. Use `(d r).2` as an intermediate fact. Use `i.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `only [Free, Loc.IsFree, ord_inr he, ord_inl' he']`.

Use `(d' s).2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `only [Free, Loc.IsFree, ord_inr he, ord_inr' he']`. Use `i.2` as an intermediate fact. Use `l.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem free_iff (hc : 1 ≤ c) (he : IsOrd (yPos (fun a => (d a).val) n) e)
    (he' : IsOrd (yPos (fun a => (d' a).val) n') e') (rs : (U ⊕ Fin c) × (U' ⊕ Fin (c + 1))) :
    Free 1 rs ↔ Loc.IsFree n' n c (e rs.1).val (e' rs.2).val := by
  obtain ⟨r, s⟩ := rs
  rcases r with r | l <;> rcases s with s | i
  · simp only [Free, Loc.IsFree, ord_inl he, ord_inl' he', false_iff]
    have := (d' s).2; omega
  · simp only [Free, Loc.IsFree, ord_inl he, ord_inr' he']
    have := (d r).2; have := i.2; omega
  · simp only [Free, Loc.IsFree, ord_inr he, ord_inl' he']
    have := (d' s).2; omega
  · simp only [Free, Loc.IsFree, ord_inr he, ord_inr' he']
    have := i.2; have := l.2; omega

end Coord

section Coord2
variable {E k : Type} [Field E] [Field k] (ι : E →+* k)
variable {U U' : Type} [Fintype U] [DecidableEq U] [Fintype U'] [DecidableEq U'] {c n n' : ℕ}
  {d : U ≃ Fin n} {d' : U' ≃ Fin n'} {e : U ⊕ Fin c ≃ Fin (n + c)} {e' : U' ⊕ Fin (c + 1) ≃ Fin (n' + (c + 1))}

def freeEquiv (hc : 1 ≤ c) (he : IsOrd (yPos (fun a => (d a).val) n) e)
    (he' : IsOrd (yPos (fun a => (d' a).val) n') e') :
    {rs : (U ⊕ Fin c) × (U' ⊕ Fin (c + 1)) // Free 1 rs} ≃ Loc.FC n' (c + 1) n c :=
  Equiv.subtypeEquiv (e.prodCongr e') (free_iff hc he he')

/- English proof (translation)
Simplify using `[Loc.xx1, Matrix.toLin'_apply, mulVec_single_one]`.
-/
theorem unfoldingAffineLinearMap_apply_single (x₀ : (Fin n' → E) →ₗ[E] (Fin n → E)) (t : Loc.FC n' (c + 1) n c → E) (i : Fin (n + c))
    (j : Fin (n' + (c + 1))) :
    Loc.xx1 x₀ t (Pi.single j 1) i = if hf : Loc.IsFree n' n c i.1 j.1 then t ⟨(i, j), hf⟩
      else if hs : j.1 < n' then (if hl : i.1 < n then LinearMap.toMatrix' x₀ ⟨i.1, hl⟩ ⟨j.1, hs⟩ else 0)
      else if i.1 = n + (j.1 - n') then 1 else 0 := by
  simp [Loc.xx1, Matrix.toLin'_apply, mulVec_single_one]

/- English proof (translation)
Use extensionality with `r s`. Establish `hF` using `free_iff hc he he' (r, s)`. Simplify using `only [toLoc, unfoldingAffineLinearMap_apply_single]`. Distinguish the cases in `h : Free 1 (r, s)`. Establish `hf` using `hF.1 h`.

Rewrite using `[dif_pos hf]`. Simplify using `only [affPt, Matrix.add_apply, Matrix.of_apply, dif_pos h]`. Establish `hb : basePt c (toLoc ι d d' x₀) r s = 0`. Apply the tactic sequence `rcases r with r | l <;> rcases s with s | i`. Simplify using `[Free] at h`.

Simplify using `[basePt]`. Simplify using `[Free] at h`. Simplify using `only [Free] at h`. Simplify using `[basePt, Fin.val_eq_val, h.ne]`. Rewrite using `[hb, zero_add]`.

Both sides reduce to the same expression. Establish `hf : ¬ Loc.IsFree n' n c (e r).val (e' s).val` using `fun h' => h (hF.2 h')`. Rewrite using `[dif_neg hf]`. Simplify using `only [affPt, Matrix.add_apply, Matrix.of_apply, dif_neg h, add_zero]`. Apply the tactic sequence `rcases r with r | l <;> rcases s with s | i`.

Establish `hs : (e' (.inl s)).val < n'` using `by rw [ord_inl' he']; exact (d' s).2`. Establish `hl : (e (.inl r)).val < n` using `by rw [ord_inl he]; exact (d r).2`. Rewrite using `[dif_pos hs, dif_pos hl]`. Establish `h1 : (⟨(e (.inl r)).val, hl⟩ : Fin n) = d r` using `Fin.ext (ord_inl he r)`. Establish `h2 : (⟨(e' (.inl s)).val, hs⟩ : Fin n') = d' s` using `Fin.ext (ord_inl' he' s)`.

Rewrite using `[h1, h2]`. Simplify using `[basePt, LinearMap.toMatrix'_apply, toLoc]`. Establish `hs : ¬ (e' (.inr i)).val < n'` using `by rw [ord_inr' he']; omega`. Establish `hl : (e (.inl r)).val < n` using `by rw [ord_inl he]; exact (d r).2`. Rewrite using `[dif_neg hs, if_neg (by rw [ord_inr' he']; omega)]`.

Simplify using `[basePt]`. Establish `hs : (e' (.inl s)).val < n'` using `by rw [ord_inl' he']; exact (d' s).2`. Establish `hl : ¬ (e (.inr l)).val < n` using `by rw [ord_inr he]; omega`. Rewrite using `[dif_pos hs, dif_neg hl]`. Simplify using `[basePt]`.

Establish `hs : ¬ (e' (.inr i)).val < n'` using `by rw [ord_inr' he']; omega`. Rewrite using `[dif_neg hs]`. Simplify using `only [ord_inr he, ord_inr' he', basePt]`. Simplify using `[Fin.val_eq_val]`.
-/
theorem affPt_eq (hc : 1 ≤ c) (he : IsOrd (yPos (fun a => (d a).val) n) e)
    (he' : IsOrd (yPos (fun a => (d' a).val) n') e') (x₀ : (Fin n' → E) →ₗ[E] (Fin n → E))
    (t : Loc.FC n' (c + 1) n c → E) :
    affPt 1 (toLoc ι d d' x₀) (fun rs => ι (t (freeEquiv hc he he' rs))) = toLoc ι e e' (Loc.xx1 x₀ t) := by
  classical
  ext r s
  have hF := free_iff hc he he' (r, s)
  simp only [toLoc, unfoldingAffineLinearMap_apply_single]
  by_cases h : Free 1 (r, s)
  · have hf := hF.1 h
    rw [dif_pos hf]
    simp only [affPt, Matrix.add_apply, Matrix.of_apply, dif_pos h]
    have hb : basePt c (toLoc ι d d' x₀) r s = 0 := by
      rcases r with r | l <;> rcases s with s | i
      · simp [Free] at h
      · simp [basePt]
      · simp [Free] at h
      · simp only [Free] at h
        simp [basePt, Fin.val_eq_val, h.ne]
    rw [hb, zero_add]; rfl
  · have hf : ¬ Loc.IsFree n' n c (e r).val (e' s).val := fun h' => h (hF.2 h')
    rw [dif_neg hf]
    simp only [affPt, Matrix.add_apply, Matrix.of_apply, dif_neg h, add_zero]
    rcases r with r | l <;> rcases s with s | i
    · have hs : (e' (.inl s)).val < n' := by rw [ord_inl' he']; exact (d' s).2
      have hl : (e (.inl r)).val < n := by rw [ord_inl he]; exact (d r).2
      rw [dif_pos hs, dif_pos hl]
      have h1 : (⟨(e (.inl r)).val, hl⟩ : Fin n) = d r := Fin.ext (ord_inl he r)
      have h2 : (⟨(e' (.inl s)).val, hs⟩ : Fin n') = d' s := Fin.ext (ord_inl' he' s)
      rw [h1, h2]
      simp [basePt, LinearMap.toMatrix'_apply, toLoc]
    · have hs : ¬ (e' (.inr i)).val < n' := by rw [ord_inr' he']; omega
      have hl : (e (.inl r)).val < n := by rw [ord_inl he]; exact (d r).2
      rw [dif_neg hs, if_neg (by rw [ord_inr' he']; omega)]
      simp [basePt]
    · have hs : (e' (.inl s)).val < n' := by rw [ord_inl' he']; exact (d' s).2
      have hl : ¬ (e (.inr l)).val < n := by rw [ord_inr he]; omega
      rw [dif_pos hs, dif_neg hl]
      simp [basePt]
    · have hs : ¬ (e' (.inr i)).val < n' := by rw [ord_inr' he']; omega
      rw [dif_neg hs]
      simp only [ord_inr he, ord_inr' he', basePt]
      simp [Fin.val_eq_val]
end Coord2

section Coord3
variable {E k : Type} [Field E] [Field k] (ι : E →+* k)
variable {U U' : Type} [Fintype U] [DecidableEq U] [Fintype U'] [DecidableEq U'] {c n n' : ℕ}
  {d : U ≃ Fin n} {d' : U' ≃ Fin n'} {e : U ⊕ Fin c ≃ Fin (n + c)} {e' : U' ⊕ Fin (c + 1) ≃ Fin (n' + (c + 1))}

/- English proof (translation)
Simplify using `only [ch, Loc.chArg, toLoc, map_sum]`. Rewrite using `[← Fin.sum_univ_eq_sum_range (fun i => ι (Loc.atN (x (Loc.eN E (n' + (c + 1)) (n' + i + 1))) (n + i))) c]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h1 : Pi.single (e' (.inr i.succ)) (1 : E) = Loc.eN E (n' + (c + 1)) (n' + i.val + 1)`. Use function extensionality and compare the values at `l`.

Simplify using `only [Pi.single_apply, Loc.eN, Fin.ext_iff, ord_inr' he', Fin.val_succ]`. Both sides reduce to the same expression. Establish `h2 : n + i.val < n + c` using `by omega`. Establish `h3 : e (.inr i) = ⟨n + i.val, h2⟩` using `Fin.ext (ord_inr he i)`. Rewrite using `[h1, h3]`.

Simplify using `[Loc.atN, h2]`.
-/
theorem ch_eq (he : IsOrd (yPos (fun a => (d a).val) n) e)
    (he' : IsOrd (yPos (fun a => (d' a).val) n') e') (x : (Fin (n' + (c + 1)) → E) →ₗ[E] (Fin (n + c) → E)) :
    ch (toLoc ι e e' x) = ι (Loc.chArg x) := by
  simp only [ch, Loc.chArg, toLoc, map_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun i => ι (Loc.atN (x (Loc.eN E (n' + (c + 1)) (n' + i + 1))) (n + i))) c]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : Pi.single (e' (.inr i.succ)) (1 : E) = Loc.eN E (n' + (c + 1)) (n' + i.val + 1) := by
    funext l
    simp only [Pi.single_apply, Loc.eN, Fin.ext_iff, ord_inr' he', Fin.val_succ]
    rfl
  have h2 : n + i.val < n + c := by omega
  have h3 : e (.inr i) = ⟨n + i.val, h2⟩ := Fin.ext (ord_inr he i)
  rw [h1, h3]
  simp [Loc.atN, h2]

end Coord3

section Wt
variable {k : Type} [Field k]

def wt (ϖ : kˣ) {V : Type} {m : ℕ} : V ⊕ Fin m → k := Sum.elim 1 fun i => (ϖ : k) ^ (i.val + 1)

/- English proof (translation)
Apply the tactic sequence `rcases r with r | i <;> simp [wt]`.
-/
theorem wt_ne_zero (ϖ : kˣ) {V : Type} {m : ℕ} (r : V ⊕ Fin m) : wt ϖ r ≠ 0 := by
  rcases r with r | i <;> simp [wt]

variable {V V' : Type} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V'] {m m' : ℕ}

/- English proof (translation)
Express the relevant statement in the definitionally equal form `fromBlocks 1 0 0 (diagonal _) = _`. Rewrite using `[← diagonal_one, fromBlocks_diagonal]`. Both sides reduce to the same expression.
-/
theorem typeFrame_bas (ϖ : kˣ) : (typeFrame ϖ (Equiv.refl (V ⊕ Fin m))).bas.val = diagonal (wt ϖ) := by
  change fromBlocks 1 0 0 (diagonal _) = _
  rw [← diagonal_one, fromBlocks_diagonal]
  rfl

/- English proof (translation)
Use `Units.inv_eq_of_mul_eq_one_right ?_` and prove the remaining obligations. Rewrite using `[typeFrame_bas, diagonal_mul_diagonal]`. Rewrite using `[← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `r`.

Conclude with `mul_inv_cancel₀ (wt_ne_zero ϖ r)`.
-/
theorem typeFrame_bas_inv (ϖ : kˣ) :
    ((typeFrame ϖ (Equiv.refl (V ⊕ Fin m))).bas⁻¹).val = diagonal fun r => (wt ϖ r)⁻¹ := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [typeFrame_bas, diagonal_mul_diagonal]
  rw [← diagonal_one]
  congr 1
  funext r
  exact mul_inv_cancel₀ (wt_ne_zero ϖ r)

/- English proof (translation)
Simplify using `only [LatFrame.coords, typeFrame_bas, typeFrame_bas_inv, submatrix_apply, Equiv.refl_apply]`. Rewrite using `[mul_diagonal, diagonal_mul]`. Both sides reduce to the same expression.
-/
theorem coords_apply (ϖ : kˣ) (x : Matrix (V ⊕ Fin m) (V' ⊕ Fin m') k) (r : V ⊕ Fin m) (s : V' ⊕ Fin m') :
    (typeFrame ϖ (Equiv.refl (V ⊕ Fin m))).coords (typeFrame ϖ (Equiv.refl (V' ⊕ Fin m'))) x r s =
      (wt ϖ r)⁻¹ * x r s * wt ϖ s := by
  simp only [LatFrame.coords, typeFrame_bas, typeFrame_bas_inv, submatrix_apply, Equiv.refl_apply]
  rw [mul_diagonal, diagonal_mul]
  rfl

end Wt

section Val
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {U U' : Type} [Fintype U] [DecidableEq U] [Fintype U'] [DecidableEq U'] {c : ℕ}

/- English proof (translation)
Take `⟨r, s⟩` from `rs`. Apply the tactic sequence `rcases r with r | l <;> rcases s with s | i`. Simplify using `[Free] at h`. Conclude with `⟨i.val, by omega, by simp [wt, pow_succ]⟩`. Simplify using `[Free] at h`.

Simplify using `only [Free] at h`. Use `⟨i.val - l.val - 1, by omega, ?_⟩` and prove the remaining obligations. Simplify using `only [wt, Sum.elim_inr]`. Rewrite using `[← pow_add, ← pow_succ]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers.
-/
theorem free_wt (ϖ : kˣ) (rs : (U ⊕ Fin c) × (U' ⊕ Fin (c + 1))) (h : Free 1 rs) :
    ∃ m : ℕ, m + 1 ≤ c + 1 ∧ wt ϖ rs.2 = wt ϖ rs.1 * (ϖ : k) ^ m * ϖ := by
  obtain ⟨r, s⟩ := rs
  rcases r with r | l <;> rcases s with s | i
  · simp [Free] at h
  · exact ⟨i.val, by omega, by simp [wt, pow_succ]⟩
  · simp [Free] at h
  · simp only [Free] at h
    refine ⟨i.val - l.val - 1, by omega, ?_⟩
    simp only [wt, Sum.elim_inr]
    rw [← pow_add, ← pow_succ]
    congr 1
    omega

/- English proof (translation)
Take `⟨r, s⟩` from `rs`. Apply the tactic sequence `rcases r with r | l <;> rcases s with s | i`. Simplify using `[Free] at h`. Simplify using `[basePt]`. Simplify using `[Free] at h`.

Simplify using `only [Free] at h`. Simplify using `[basePt, Fin.val_eq_val, h.ne]`.
-/
theorem basePt_free (x₀ : Matrix U U' k) (rs : (U ⊕ Fin c) × (U' ⊕ Fin (c + 1))) (h : Free 1 rs) :
    basePt c x₀ rs.1 rs.2 = 0 := by
  obtain ⟨r, s⟩ := rs
  rcases r with r | l <;> rcases s with s | i
  · simp [Free] at h
  · simp [basePt]
  · simp [Free] at h
  · simp only [Free] at h
    simp [basePt, Fin.val_eq_val, h.ne]

/- English proof (translation)
Simplify using `only [affPt, Matrix.add_apply, Matrix.of_apply, basePt_free x₀ rs h, zero_add]`. Rewrite using `[dif_pos h]`.
-/
theorem affPt_free (x₀ : Matrix U U' k) (u : {rs : (U ⊕ Fin c) × (U' ⊕ Fin (c + 1)) // Free 1 rs} → k)
    (rs : (U ⊕ Fin c) × (U' ⊕ Fin (c + 1))) (h : Free 1 rs) : affPt 1 x₀ u rs.1 rs.2 = u ⟨rs, h⟩ := by
  classical
  simp only [affPt, Matrix.add_apply, Matrix.of_apply, basePt_free x₀ rs h, zero_add]
  rw [dif_pos h]

open Classical in

def freeMat (y : {rs : (U ⊕ Fin c) × (U' ⊕ Fin (c + 1)) // Free 1 rs} → k) : Matrix (U ⊕ Fin c) (U' ⊕ Fin (c + 1)) k :=
  Matrix.of fun r s => if h : Free 1 (r, s) then y ⟨(r, s), h⟩ else 0

/- English proof (translation)
Use extensionality with `r s`. Simplify using `only [affPt, freeMat, Matrix.add_apply, Matrix.of_apply, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem affPt_add (x₀ : Matrix U U' k) (u y : {rs : (U ⊕ Fin c) × (U' ⊕ Fin (c + 1)) // Free 1 rs} → k) :
    affPt 1 x₀ (u + y) = affPt 1 x₀ u + freeMat y := by
  classical
  ext r s
  simp only [affPt, freeMat, Matrix.add_apply, Matrix.of_apply, Pi.add_apply]
  split_ifs <;> ring

/- English proof (translation)
Simplify using `[ch, Finset.sum_add_distrib]`.
-/
theorem ch_add (x y : Matrix (U ⊕ Fin c) (U' ⊕ Fin (c + 1)) k) : ch (x + y) = ch x + ch y := by
  simp [ch, Finset.sum_add_distrib]

/- English proof (translation)
Take `⟨m, hm, hw⟩` from `free_wt ϖ rs h`. Establish `hI` using `hx rs.1 rs.2`. Rewrite `hI` using `[coords_apply, hw]`. Establish `e1 : (wt ϖ rs.1)⁻¹ * x rs.1 rs.2 * (wt ϖ rs.1 * (ϖ : k) ^ m * ϖ) = x rs.1 rs.2 * (ϖ : k) ^ (m + 1)`. Use `wt_ne_zero ϖ rs.1` as an intermediate fact.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite `hI` using `[e1, Valuation.mem_integer_iff]`. Establish `e2 : x rs.1 rs.2 = x rs.1 rs.2 * (ϖ : k) ^ (m + 1) * (ϖ : k) ^ (A - (m + 1)) * (((ϖ ^ A)⁻¹ : kˣ) : k)`. Rewrite using `[mul_assoc (x rs.1 rs.2), ← pow_add, Nat.add_sub_cancel' (by omega), Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ϖ.ne_zero), mul_one]`.

Rewrite using `[e2, map_mul, map_mul, map_pow]`. Use `mul_le_of_le_one_left zero_le' (mul_le_one' hI (pow_le_one' hv.le _))` and prove the remaining obligations.
-/
theorem free_bound (ϖ : kˣ) (hv : valuation k (ϖ : k) < 1) {A : ℕ} (hA : c + 1 ≤ A)
    {x : Matrix (U ⊕ Fin c) (U' ⊕ Fin (c + 1)) k}
    (hx : IntM ((typeFrame ϖ (Equiv.refl (U ⊕ Fin c))).coords (typeFrame ϖ (Equiv.refl (U' ⊕ Fin (c + 1)))) x))
    (rs : (U ⊕ Fin c) × (U' ⊕ Fin (c + 1))) (h : Free 1 rs) :
    valuation k (x rs.1 rs.2) ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k) := by
  obtain ⟨m, hm, hw⟩ := free_wt ϖ rs h
  have hI := hx rs.1 rs.2
  rw [coords_apply, hw] at hI
  have e1 : (wt ϖ rs.1)⁻¹ * x rs.1 rs.2 * (wt ϖ rs.1 * (ϖ : k) ^ m * ϖ) = x rs.1 rs.2 * (ϖ : k) ^ (m + 1) := by
    have := wt_ne_zero ϖ rs.1
    field_simp
    ring
  rw [e1, Valuation.mem_integer_iff] at hI
  have e2 : x rs.1 rs.2 = x rs.1 rs.2 * (ϖ : k) ^ (m + 1) * (ϖ : k) ^ (A - (m + 1)) * (((ϖ ^ A)⁻¹ : kˣ) : k) := by
    rw [mul_assoc (x rs.1 rs.2), ← pow_add, Nat.add_sub_cancel' (by omega), Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ϖ.ne_zero), mul_one]
  rw [e2, map_mul, map_mul, map_pow]
  refine mul_le_of_le_one_left zero_le' (mul_le_one' hI (pow_le_one' hv.le _))

/- English proof (translation)
Introduce `r s`. Rewrite using `[coords_apply]`. Distinguish the cases in `h : Free 1 (r, s)`. Take `⟨m, -, hw⟩` from `free_wt ϖ (r, s) h`. Simplify using `only [freeMat, Matrix.of_apply, dif_pos h]`.

Rewrite using `[hw]`. Establish `e1 : (wt ϖ r)⁻¹ * y ⟨(r, s), h⟩ * (wt ϖ r * (ϖ : k) ^ m * ϖ) = y ⟨(r, s), h⟩ * (ϖ : k) ^ m * ϖ`. Use `wt_ne_zero ϖ r` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Rewrite using `[e1, map_mul, map_mul, map_pow]`.

Establish `h1 : valuation k (y ⟨(r, s), h⟩) ≤ 1` using `(hy _).trans (by rw [map_pow]; exact pow_le_one' hv.le _)`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left zero_le' (mul_le_one' h1 (pow_le_one' hv.le _))) hv`. Simplify using `only [freeMat, Matrix.of_apply, dif_neg h, mul_zero, zero_mul, map_zero]`. Conclude with `zero_lt_one`.
-/
theorem free_small (ϖ : kˣ) (hv : valuation k (ϖ : k) < 1) {B : ℕ}
    (y : {rs : (U ⊕ Fin c) × (U' ⊕ Fin (c + 1)) // Free 1 rs} → k)
    (hy : ∀ i, valuation k (y i) ≤ valuation k ((ϖ : k) ^ B)) :
    MaxM ((typeFrame ϖ (Equiv.refl (U ⊕ Fin c))).coords (typeFrame ϖ (Equiv.refl (U' ⊕ Fin (c + 1)))) (freeMat y)) := by
  classical
  intro r s
  rw [coords_apply]
  by_cases h : Free 1 (r, s)
  · obtain ⟨m, -, hw⟩ := free_wt ϖ (r, s) h
    simp only [freeMat, Matrix.of_apply, dif_pos h]
    rw [hw]
    have e1 : (wt ϖ r)⁻¹ * y ⟨(r, s), h⟩ * (wt ϖ r * (ϖ : k) ^ m * ϖ) = y ⟨(r, s), h⟩ * (ϖ : k) ^ m * ϖ := by
      have := wt_ne_zero ϖ r
      field_simp
    rw [e1, map_mul, map_mul, map_pow]
    have h1 : valuation k (y ⟨(r, s), h⟩) ≤ 1 := (hy _).trans (by rw [map_pow]; exact pow_le_one' hv.le _)
    exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le' (mul_le_one' h1 (pow_le_one' hv.le _))) hv
  · simp only [freeMat, Matrix.of_apply, dif_neg h, mul_zero, zero_mul, map_zero]
    exact zero_lt_one

/- English proof (translation)
Rewrite using `[← Valuation.mem_integer_iff]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Establish `h : Free 1 ((Sum.inr i : U ⊕ Fin c), (Sum.inr i.succ : U' ⊕ Fin (c + 1)))`. Simplify using `[Free, Fin.val_succ]`. Simplify using `only [freeMat, Matrix.of_apply, dif_pos h, Valuation.mem_integer_iff]`.

Conclude with `(hy _).trans (by rw [map_pow]; exact pow_le_one' hv.le _)`.
-/
theorem ch_freeMat_int (ϖ : kˣ) (hv : valuation k (ϖ : k) < 1) {B : ℕ}
    (y : {rs : (U ⊕ Fin c) × (U' ⊕ Fin (c + 1)) // Free 1 rs} → k)
    (hy : ∀ i, valuation k (y i) ≤ valuation k ((ϖ : k) ^ B)) : valuation k (ch (freeMat y)) ≤ 1 := by
  classical
  rw [← Valuation.mem_integer_iff]
  refine sum_mem fun i _ => ?_
  have h : Free 1 ((Sum.inr i : U ⊕ Fin c), (Sum.inr i.succ : U' ⊕ Fin (c + 1))) := by
    simp [Free, Fin.val_succ]
  simp only [freeMat, Matrix.of_apply, dif_pos h, Valuation.mem_integer_iff]
  exact (hy _).trans (by rw [map_pow]; exact pow_le_one' hv.le _)

end Val

/- English proof (translation)
Unfold `SumAgree`. Introduce `E K k _ _ _ _ _ _ _ _ _ _ P q ι ϖ σ₀ ψ ν psi hC hU hψ hν hpsi U' U _ _ _ _ c n' c' n c₂ A B hc hc' hc₂ hA hB d' d e' e hoe' hoe Φ ΦE hΦ hsupp hper x₀`. Substitute `c' c₂` using the available equality. Establish `hq : ι (q : E) = (ϖ : k)` using `hC.unif.symm`. Establish `hq0 : (q : E) ≠ 0` using `fun h0 => ϖ.ne_zero (by rw [← hq, h0, map_zero])`.

Take `⟨-, -, -, -, -, -, hres, hrep⟩` from `GlobalTheory.T.residues_of_completionAtPrimeWithUniformizer E k P q ι ϖ hC hU`. Establish `hv : valuation k (ϖ : k) < 1` using `(hU ϖ).2 le_rfl`. Establish `hψ1 : ∀ b : k, valuation k b ≤ 1 → ψ b = 1` using `fun b hb => (hψ 1).2 le_rfl b (by simpa using hb)`. Establish `hA0 : ((ϖ : k) ^ A) ≠ 0` using `pow_ne_zero _ ϖ.ne_zero`. Establish `hinv : (((ϖ ^ A)⁻¹ : kˣ) : k) = ((ϖ : k) ^ A)⁻¹`.

Rewrite using `[Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]`. Establish `hιv : ∀ i : ℕ, ι ((i : E) / (q : E) ^ A) = (i : k) * ((ϖ : k) ^ A)⁻¹` using `fun i => by`. Rewrite using `[map_div₀, map_pow, map_natCast, hq, div_eq_mul_inv]`. Use `set T : Finset k := (LocE.valsQ E q A B).image ι with hTdef`. Establish `hmemT : ∀ t, t ∈ T ↔ ∃ i : ℕ, i < q ^ (A + B) ∧ (i : k) * ((ϖ : k) ^ A)⁻¹ = t` using `fun t => by`.

Simplify using `only [hTdef, LocE.valsQ, Finset.mem_image, Finset.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨i, hi, rfl⟩, rfl⟩`. Conclude with `⟨i, hi, (hιv i).symm⟩`. Introduce and unpack `⟨i, hi, rfl⟩`.

Conclude with `⟨_, ⟨i, hi, rfl⟩, hιv i⟩`. Establish `hnat : ∀ i : ℕ, valuation k (i : k) ≤ 1` using `fun i => by`. Rewrite using `[← Valuation.mem_integer_iff]`. Conclude with `natCast_mem _ i`. Establish `hT1 : ∀ t ∈ T, valuation k t ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k)`.

Introduce `t ht`. Take `⟨i, -, rfl⟩` from `(hmemT t).1 ht`. Rewrite using `[hinv, map_mul]`. Conclude with `mul_le_of_le_one_left zero_le' (hnat i)`. Establish `hT2 : ∀ x : k, valuation k x ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k) → ∃! t, t ∈ T ∧ valuation k (x - t) ≤ valuation k ((ϖ : k) ^ B)`.

Introduce `x hx`. Establish `hz : x * (ϖ : k) ^ A ∈ 𝒪[k]`. Rewrite using `[Valuation.mem_integer_iff, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hinv]`.

Use `gcongr`. Use `_ = 1 := by rw [← map_mul, inv_mul_cancel₀ hA0, map_one]`. Take `⟨i, ⟨hi, hzi⟩, huniq⟩` from `hrep (A + B) _ hz`. Establish `key : ∀ j : ℕ, valuation k (x - (j : k) * ((ϖ : k) ^ A)⁻¹) ≤ valuation k ((ϖ : k) ^ B) ↔ valuation k (x * (ϖ : k) ^ A - (j : k)) ≤ valuation k ((ϖ : k) ^ (A + B))` using `fun j => by`. Establish `e1 : x * (ϖ : k) ^ A - (j : k) = (x - (j : k) * ((ϖ : k) ^ A)⁻¹) * (ϖ : k) ^ A`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e1, pow_add, mul_comm ((ϖ : k) ^ A) ((ϖ : k) ^ B), map_mul, map_mul (valuation k) ((ϖ : k) ^ B)]`. Establish `: valuation k ((ϖ : k) ^ A) ≠ 0` using `by simpa using hA0`. Conclude with `(mul_le_mul_iff_of_pos_right (zero_lt_iff.2 this)).symm`. Use `⟨(i : k) * ((ϖ : k) ^ A)⁻¹, ⟨(hmemT _).2 ⟨i, hi, rfl⟩, (key i).2 hzi⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `t ⟨ht, htx⟩`. Take `⟨j, hj, rfl⟩` from `(hmemT t).1 ht`. Rewrite using `[huniq j ⟨hj, (key j).1 htx⟩]`. Use `set X₀ := toLoc ι d d' x₀ with hX₀`. Set `F : ({rs : (U ⊕ Fin c) × (U' ⊕ Fin (c + 1)) // Free 1 rs} → k) → ℂ` to `fun u => Φ (affPt 1 X₀ u) * (ψ (-ch (affPt 1 X₀ u)) : ℂ)`.

Establish `hF1 : ∀ u, F u ≠ 0 → ∀ i, valuation k (u i) ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k)`. Introduce `u hu i`. Establish `h1 : Φ (affPt 1 X₀ u) ≠ 0` using `left_ne_zero_of_mul hu`. Use `free_bound ϖ hv hA (hsupp _ h1) i.1 i.2` as an intermediate fact. Rewrite `this` using `[affPt_free]`. Then use the resulting hypothesis.

Establish `hF2 : ∀ u y, (∀ i, valuation k (y i) ≤ valuation k ((ϖ : k) ^ B)) → F (u + y) = F u`. Introduce `u y hy`. Simplify using `only [F, affPt_add, ch_add]`. Rewrite using `[hper _ _ (free_small ϖ hv y hy)]`. Use `congr 1`.

Rewrite using `[neg_add, AddChar.map_add_eq_mul, hψ1 (-ch (freeMat y)) (by rw [Valuation.map_neg]; exact ch_freeMat_int ϖ hv y hy), mul_one]`. Establish `key` using `GlobalTheory.T.integral_periodic_compactSupport_eq_finiteSum k ν hν ϖ hU A B T hT1 hT2 _ F hF1 hF2`. Establish `hL : opE ψ ν 1 Φ X₀ = ∫ u, F u ∂(Measure.pi fun _ => ν)` using `rfl`. Rewrite using `[hL, key]`. Simplify using `only [Loc.E1, map_mul, map_pow, map_inv₀, map_natCast, map_sum, hres]`.

Rewrite using `[Fintype.card_congr (freeEquiv hc hoe hoe')]`. Use `congr 1`. Use `symm`. Use `Finset.sum_nbij (fun t rs => ι (t (freeEquiv hc hoe hoe' rs))) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `t ht`.

Rewrite `ht`, the goal using `[Fintype.mem_piFinset]`. Conclude with `fun rs => Finset.mem_image_of_mem ι (ht _)`. Introduce `a _ b _ hab`. Use function extensionality and compare the values at `p`. Use `congrFun hab ((freeEquiv hc hoe hoe').symm p)` as an intermediate fact.

Simplify using `only [Equiv.apply_symm_apply] at this`. Conclude with `ι.injective this`. Introduce `u hu`. Rewrite `hu` using `[Finset.mem_coe, Fintype.mem_piFinset]`. Use `choose g hg1 hg2 using fun a => Finset.mem_image.1 (hu a)`.

Use `⟨fun p => g ((freeEquiv hc hoe hoe').symm p), ?_, funext fun rs => ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_coe, Fintype.mem_piFinset]`. Conclude with `fun p => hg1 _`. Simplify using `only [Equiv.symm_apply_apply, hg2]`. Introduce `t _`.

Simplify using `only [F]`. Rewrite using `[affPt_eq ι hc hoe hoe' x₀ t, hΦ, ch_eq ι hoe hoe']`. Distinguish the cases in `h0 : ΦE (Loc.xx1 x₀ t) = 0`. Simplify using `[h0]`. Use `congr 1`.

Use `set X := Loc.xx1 x₀ t`. Establish `hnz : Φ (toLoc ι e e' X) ≠ 0` using `by rw [hΦ]; exact (map_ne_zero σ₀).2 h0`. Establish `hI` using `hsupp _ hnz`. Establish `hint : ι ((q : E) * Loc.chArg X) ∈ 𝒪[k]`. Rewrite using `[map_mul, hq, ← ch_eq ι hoe hoe', ch, Finset.mul_sum]`.

Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Use `hI (Sum.inr i) (Sum.inr i.succ)` as an intermediate fact. Rewrite `this` using `[coords_apply]`. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [wt, Sum.elim_inr, Fin.val_succ]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hIA : IntAt P (-((q : E) * Loc.chArg X))` using `(hC.int _).1 (by rw [map_neg]; exact neg_mem hint)`. Establish `h2` using `hpsi _ hIA`. Rewrite `h2` using `[neg_div, mul_div_cancel_left₀ _ hq0]`.

Rewrite using `[← h2, map_neg]`.
-/
theorem sumAgree : SumAgree := by
  unfold SumAgree
  intro E K k _ _ _ _ _ _ _ _ _ _ P q ι ϖ σ₀ ψ ν psi hC hU hψ hν hpsi U' U _ _ _ _ c n' c' n c₂ A B hc hc' hc₂ hA hB
    d' d e' e hoe' hoe Φ ΦE hΦ hsupp hper x₀
  subst c' c₂
  classical
  have hq : ι (q : E) = (ϖ : k) := hC.unif.symm
  have hq0 : (q : E) ≠ 0 := fun h0 => ϖ.ne_zero (by rw [← hq, h0, map_zero])
  obtain ⟨-, -, -, -, -, -, hres, hrep⟩ := GlobalTheory.T.residues_of_completionAtPrimeWithUniformizer E k P q ι ϖ hC hU
  have hv : valuation k (ϖ : k) < 1 := (hU ϖ).2 le_rfl
  have hψ1 : ∀ b : k, valuation k b ≤ 1 → ψ b = 1 := fun b hb =>
    (hψ 1).2 le_rfl b (by simpa using hb)
  have hA0 : ((ϖ : k) ^ A) ≠ 0 := pow_ne_zero _ ϖ.ne_zero
  have hinv : (((ϖ ^ A)⁻¹ : kˣ) : k) = ((ϖ : k) ^ A)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
  have hιv : ∀ i : ℕ, ι ((i : E) / (q : E) ^ A) = (i : k) * ((ϖ : k) ^ A)⁻¹ := fun i => by
    rw [map_div₀, map_pow, map_natCast, hq, div_eq_mul_inv]
  set T : Finset k := (LocE.valsQ E q A B).image ι with hTdef
  have hmemT : ∀ t, t ∈ T ↔ ∃ i : ℕ, i < q ^ (A + B) ∧ (i : k) * ((ϖ : k) ^ A)⁻¹ = t := fun t => by
    simp only [hTdef, LocE.valsQ, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨i, hi, (hιv i).symm⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨_, ⟨i, hi, rfl⟩, hιv i⟩
  have hnat : ∀ i : ℕ, valuation k (i : k) ≤ 1 := fun i => by
    rw [← Valuation.mem_integer_iff]; exact natCast_mem _ i
  have hT1 : ∀ t ∈ T, valuation k t ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k) := by
    intro t ht
    obtain ⟨i, -, rfl⟩ := (hmemT t).1 ht
    rw [hinv, map_mul]
    exact mul_le_of_le_one_left zero_le' (hnat i)
  have hT2 : ∀ x : k, valuation k x ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k) →
      ∃! t, t ∈ T ∧ valuation k (x - t) ≤ valuation k ((ϖ : k) ^ B) := by
    intro x hx
    have hz : x * (ϖ : k) ^ A ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, map_mul]
      calc valuation k x * valuation k ((ϖ : k) ^ A)
          ≤ valuation k (((ϖ : k) ^ A)⁻¹) * valuation k ((ϖ : k) ^ A) := by
            rw [← hinv]; gcongr
        _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hA0, map_one]
    obtain ⟨i, ⟨hi, hzi⟩, huniq⟩ := hrep (A + B) _ hz
    have key : ∀ j : ℕ, valuation k (x - (j : k) * ((ϖ : k) ^ A)⁻¹) ≤ valuation k ((ϖ : k) ^ B) ↔
        valuation k (x * (ϖ : k) ^ A - (j : k)) ≤ valuation k ((ϖ : k) ^ (A + B)) := fun j => by
      have e1 : x * (ϖ : k) ^ A - (j : k) = (x - (j : k) * ((ϖ : k) ^ A)⁻¹) * (ϖ : k) ^ A := by
        field_simp
      rw [e1, pow_add, mul_comm ((ϖ : k) ^ A) ((ϖ : k) ^ B), map_mul, map_mul (valuation k) ((ϖ : k) ^ B)]
      have : valuation k ((ϖ : k) ^ A) ≠ 0 := by simpa using hA0
      exact (mul_le_mul_iff_of_pos_right (zero_lt_iff.2 this)).symm
    refine ⟨(i : k) * ((ϖ : k) ^ A)⁻¹, ⟨(hmemT _).2 ⟨i, hi, rfl⟩, (key i).2 hzi⟩, ?_⟩
    rintro t ⟨ht, htx⟩
    obtain ⟨j, hj, rfl⟩ := (hmemT t).1 ht
    rw [huniq j ⟨hj, (key j).1 htx⟩]
  set X₀ := toLoc ι d d' x₀ with hX₀
  let F : ({rs : (U ⊕ Fin c) × (U' ⊕ Fin (c + 1)) // Free 1 rs} → k) → ℂ :=
    fun u => Φ (affPt 1 X₀ u) * (ψ (-ch (affPt 1 X₀ u)) : ℂ)
  have hF1 : ∀ u, F u ≠ 0 → ∀ i, valuation k (u i) ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k) := by
    intro u hu i
    have h1 : Φ (affPt 1 X₀ u) ≠ 0 := left_ne_zero_of_mul hu
    have := free_bound ϖ hv hA (hsupp _ h1) i.1 i.2
    rwa [affPt_free] at this
  have hF2 : ∀ u y, (∀ i, valuation k (y i) ≤ valuation k ((ϖ : k) ^ B)) → F (u + y) = F u := by
    intro u y hy
    simp only [F, affPt_add, ch_add]
    rw [hper _ _ (free_small ϖ hv y hy)]
    congr 1
    rw [neg_add, AddChar.map_add_eq_mul, hψ1 (-ch (freeMat y)) (by rw [Valuation.map_neg]; exact ch_freeMat_int ϖ hv y hy), mul_one]
  have key := GlobalTheory.T.integral_periodic_compactSupport_eq_finiteSum k ν hν ϖ hU A B T hT1 hT2 _ F hF1 hF2
  have hL : opE ψ ν 1 Φ X₀ = ∫ u, F u ∂(Measure.pi fun _ => ν) := rfl
  rw [hL, key]
  simp only [Loc.E1, map_mul, map_pow, map_inv₀, map_natCast, map_sum, hres]
  rw [Fintype.card_congr (freeEquiv hc hoe hoe')]
  congr 1
  symm
  refine Finset.sum_nbij (fun t rs => ι (t (freeEquiv hc hoe hoe' rs))) ?_ ?_ ?_ ?_
  · intro t ht
    rw [Fintype.mem_piFinset] at ht ⊢
    exact fun rs => Finset.mem_image_of_mem ι (ht _)
  · intro a _ b _ hab
    funext p
    have := congrFun hab ((freeEquiv hc hoe hoe').symm p)
    simp only [Equiv.apply_symm_apply] at this
    exact ι.injective this
  · intro u hu
    rw [Finset.mem_coe, Fintype.mem_piFinset] at hu
    choose g hg1 hg2 using fun a => Finset.mem_image.1 (hu a)
    refine ⟨fun p => g ((freeEquiv hc hoe hoe').symm p), ?_, funext fun rs => ?_⟩
    · rw [Finset.mem_coe, Fintype.mem_piFinset]
      exact fun p => hg1 _
    · simp only [Equiv.symm_apply_apply, hg2]
  · intro t _
    simp only [F]
    rw [affPt_eq ι hc hoe hoe' x₀ t, hΦ, ch_eq ι hoe hoe']
    by_cases h0 : ΦE (Loc.xx1 x₀ t) = 0
    · simp [h0]
    congr 1
    set X := Loc.xx1 x₀ t
    have hnz : Φ (toLoc ι e e' X) ≠ 0 := by rw [hΦ]; exact (map_ne_zero σ₀).2 h0
    have hI := hsupp _ hnz
    have hint : ι ((q : E) * Loc.chArg X) ∈ 𝒪[k] := by
      rw [map_mul, hq, ← ch_eq ι hoe hoe', ch, Finset.mul_sum]
      refine sum_mem fun i _ => ?_
      have := hI (Sum.inr i) (Sum.inr i.succ)
      rw [coords_apply] at this
      convert this using 1
      simp only [wt, Sum.elim_inr, Fin.val_succ]
      field_simp
      ring
    have hIA : IntAt P (-((q : E) * Loc.chArg X)) := (hC.int _).1 (by rw [map_neg]; exact neg_mem hint)
    have h2 := hpsi _ hIA
    rw [neg_div, mul_div_cancel_left₀ _ hq0] at h2
    rw [← h2, map_neg]
end GlobalTheory.UnfoldSum

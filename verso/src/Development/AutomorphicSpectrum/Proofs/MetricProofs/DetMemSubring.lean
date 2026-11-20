import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
import Development.AutomorphicSpectrum.Proofs.MetricProofs.YvEqSumMinorsGMat

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

variable {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}

def tMat (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) :
    Matrix (Fin (p + q)) (Fin (p + q)) Ω :=
  (Matrix.fromBlocks (Ts (.inr τ)) 0 0 (Ts (.inl τ))).submatrix (blockEquiv p q).symm (blockEquiv p q).symm

def cMin (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (t : StepIx Ψ p q)
    (J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1)) (I : Finset (Fin (p + q))) : Ω :=
  if e : I.card = (t.2 : ℕ) + 1 then ((aExt C t.1).submatrix J (I.orderEmbOfFin e)).det else 0

open Classical in

def bExt (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω) (s : Ψ ⊕ Ψ) : Matrix (Fin (p + q)) (Fin (n s)) Ω :=
  fun a j => ∑ l, if posOf p q s l = a then B s l j else 0

def bMin (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω) (t : StepIx Ψ p q)
    (I : Finset (Fin (p + q))) (J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1)) : Ω :=
  if e : I.card = (t.2 : ℕ) + 1 then ((bExt B t.1).submatrix (I.orderEmbOfFin e) J).det else 0

variable (p q) in

def fullT (s : Ψ ⊕ Ψ) (h : 0 < rk Ψ p q s) : StepIx Ψ p q := ⟨s, ⟨rk Ψ p q s - 1, by omega⟩⟩

/- English proof (translation)
Introduce `hr`. Unfold `blkF at hr`. Use `split_ifs at hr with hp`. Take `⟨h1, h2⟩` from `hp`. Simplify using `only [Option.some.injEq, Sum.inr.injEq] at hr`.

Unfold `stepOf fullT at hr`. Establish `hv` using `r.2.isLt`. Use `split_ifs at hr with hlt`. Rewrite `hr` using `[Sigma.mk.inj_iff]`. Take `⟨hs, hx⟩` from `hr`.

Substitute `hs` using the available equality. Establish `hx'` using `congrArg Fin.val (eq_of_heq hx)`. Simplify using `[rk] at hx' h`. Use linear arithmetic over natural numbers and integers. Rewrite `hr` using `[Sigma.mk.inj_iff]`.

Take `⟨hs, hx⟩` from `hr`. Substitute `hs` using the available equality. Establish `hx'` using `congrArg Fin.val (eq_of_heq hx)`. Simplify using `[rk] at hx' h`. Use linear arithmetic over natural numbers and integers.
-/
theorem fullT_base (K₀ : Type) (s : Ψ ⊕ Ψ) (h : 0 < rk Ψ p q s) (r : Ψ × Fin (p + q)) :
    blkF Ψ p q K₀ r ≠ some (.inr (fullT p q s h)) := by
  intro hr
  unfold blkF at hr
  split_ifs at hr with hp
  obtain ⟨h1, h2⟩ := hp
  simp only [Option.some.injEq, Sum.inr.injEq] at hr
  unfold stepOf fullT at hr
  have hv := r.2.isLt
  split_ifs at hr with hlt
  · rw [Sigma.mk.inj_iff] at hr
    obtain ⟨hs, hx⟩ := hr
    subst hs
    have hx' := congrArg Fin.val (eq_of_heq hx)
    simp [rk] at hx' h
    omega
  · rw [Sigma.mk.inj_iff] at hr
    obtain ⟨hs, hx⟩ := hr
    subst hs
    have hx' := congrArg Fin.val (eq_of_heq hx)
    simp [rk] at hx' h
    omega

def baseFull (K₀ : Type) (s : Ψ ⊕ Ψ) (h : 0 < rk Ψ p q s) : NonPluckerBlocks (blkF Ψ p q K₀) :=
  ⟨.inr (fullT p q s h), fullT_base K₀ s h⟩

def baseInl {K₀ : Type} (k : K₀) : NonPluckerBlocks (blkF Ψ p q K₀) :=
  ⟨.inl k, fun r => by
    classical
    unfold blkF
    split_ifs <;> simp⟩

variable {K₀ : Type} {J₀ : K₀ → Type}

def xcOf [Fintype K₀] (x₀ : (Σ k, J₀ k) → Ω)
    (c : ∀ k : NonPluckerBlocks (blkF Ψ p q K₀), baseIdx (idx (p := p) (q := q) J₀ n) (blkF Ψ p q K₀) k) : Ω :=
  ∏ k, x₀ ⟨k, c (baseInl k)⟩

def rowsOf (c : ∀ k : NonPluckerBlocks (blkF Ψ p q K₀), baseIdx (idx (p := p) (q := q) J₀ n) (blkF Ψ p q K₀) k)
    (s : Ψ ⊕ Ψ) : Fin (rk Ψ p q s) → Fin (n s) :=
  fun a => c (baseFull K₀ s (by have := a.2; omega)) (Fin.cast (by have := a.2; show _ = rk Ψ p q s - 1 + 1; omega) a)

def zOf (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (c : ∀ k : NonPluckerBlocks (blkF Ψ p q K₀), baseIdx (idx (p := p) (q := q) J₀ n) (blkF Ψ p q K₀) k)
    (s : Ψ ⊕ Ψ) : Ω :=
  ((A s).submatrix (rowsOf c s) id).det

/- English proof (translation)
Simplify using `only [xb, baseFull, xv]`. Establish `e : rk Ψ p q s - 1 + 1 = rk Ψ p q s` using `by omega`. Rewrite using `[← Matrix.det_submatrix_equiv_self (finCongr e) ((A s).submatrix J id)]`. Both sides reduce to the same expression.
-/
theorem xb_full [Fintype Ψ] [Fintype K₀] [∀ k, Fintype (J₀ k)] (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (x₀ : (Σ k, J₀ k) → Ω) (s : Ψ ⊕ Ψ) (h : 0 < rk Ψ p q s) (J : Fin (rk Ψ p q s) → Fin (n s)) :
    xb A x₀ ⟨baseFull K₀ s h, fun a => J (Fin.cast (by show _ = rk Ψ p q s; have := a.2; show rk Ψ p q s - 1 + 1 = _; omega) a)⟩ =
      ((A s).submatrix J id).det := by
  simp only [xb, baseFull, xv]
  have e : rk Ψ p q s - 1 + 1 = rk Ψ p q s := by omega
  rw [← Matrix.det_submatrix_equiv_self (finCongr e) ((A s).submatrix J id)]
  rfl

/- English proof (translation)
The claim follows from `xb_full A x₀ s h (rowsOf c s)`.
-/
theorem xb_rowsOf [Fintype Ψ] [Fintype K₀] [∀ k, Fintype (J₀ k)] (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (x₀ : (Σ k, J₀ k) → Ω)
    (c : ∀ k : NonPluckerBlocks (blkF Ψ p q K₀), baseIdx (idx (p := p) (q := q) J₀ n) (blkF Ψ p q K₀) k)
    (s : Ψ ⊕ Ψ) (h : 0 < rk Ψ p q s) :
    xb A x₀ ⟨baseFull K₀ s h, c (baseFull K₀ s h)⟩ = zOf A c s :=
  xb_full A x₀ s h (rowsOf c s)

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Use `R.sum_mem fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Units.smul_def]`. Conclude with `R.zsmul_mem (R.prod_mem fun i _ => h _ _) _`.
-/
theorem det_mem_subring {ι : Type} [Fintype ι] [DecidableEq ι] (R : Subring Ω) (M : Matrix ι ι Ω)
    (h : ∀ a b, M a b ∈ R) : M.det ∈ R := by
  rw [Matrix.det_apply]
  refine R.sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact R.zsmul_mem (R.prod_mem fun i _ => h _ _) _

open Classical in

def sMin (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω) (t : StepIx Ψ p q)
    (I : Finset (Fin (p + q))) (J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1)) : Ω :=
  if StrictMono J then bMin B t I J else 0

/- English proof (translation)
Rewrite using `[← Nat.card_Ico lo hi]`. Apply `Finset.card_bij (fun (a : Fin N) _ => (a : ℕ))` to reduce the goal to its premises. Introduce `a ha`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at ha`. Simplify using `only [Finset.mem_Ico]`.

Use linear arithmetic over natural numbers and integers. Introduce `a _ b _ hab`. Conclude with `Fin.ext hab`. Introduce `b hb`. Simplify using `only [Finset.mem_Ico] at hb`.

Conclude with `⟨⟨b, by omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega, rfl⟩`.
-/
private theorem card_filter_fin_Ico (N lo hi : ℕ) (hh : hi ≤ N) :
    (Finset.univ.filter (fun a : Fin N => lo ≤ (a : ℕ) ∧ (a : ℕ) < hi)).card = hi - lo := by
  rw [← Nat.card_Ico lo hi]
  apply Finset.card_bij (fun (a : Fin N) _ => (a : ℕ))
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [Finset.mem_Ico]
    omega
  · intro a _ b _ hab
    exact Fin.ext hab
  · intro b hb
    simp only [Finset.mem_Ico] at hb
    exact ⟨⟨b, by omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega, rfl⟩

/- English proof (translation)
Establish `hv` using `r.2.isLt`. Unfold `stepCols`. Distinguish the cases in `hc : (r.2 : ℕ) < p`. Establish `hs : stepOf Ψ p q r = ⟨Sum.inl r.1, ⟨r.2, by simp [rk]; omega⟩⟩`. Unfold `stepOf`.

Rewrite using `[dif_pos hc]`. Establish `hc' : (r.2 : ℕ) + 1 ≤ p` using `hc`. Rewrite using `[hs]`. Simplify using `only [if_pos hc']`. Rewrite using `[card_filter_fin_Ico _ _ _ (by omega)]`.

Use linear arithmetic over natural numbers and integers. Establish `hs : stepOf Ψ p q r = ⟨Sum.inr r.1, ⟨r.2 - p, by simp [rk]; omega⟩⟩`. Unfold `stepOf`. Rewrite using `[dif_neg hc]`. Establish `hc' : ¬ ((r.2 : ℕ) + 1 ≤ p)` using `by omega`.

Rewrite using `[hs]`. Simplify using `only [if_neg hc']`. Use `card_filter_fin_Ico (p + q) 0 ((r.2 : ℕ) + 1 - p) (by omega)` as an intermediate fact. Simplify using `only [Nat.zero_le, true_and] at this`. Rewrite using `[this]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem card_stepCols (r : Ψ × Fin (p + q)) :
    (stepCols (p + q) p r.2).card = ((stepOf Ψ p q r).2 : ℕ) + 1 := by
  have hv := r.2.isLt
  unfold stepCols
  by_cases hc : (r.2 : ℕ) < p
  · have hs : stepOf Ψ p q r = ⟨Sum.inl r.1, ⟨r.2, by simp [rk]; omega⟩⟩ := by
      unfold stepOf
      rw [dif_pos hc]
    have hc' : (r.2 : ℕ) + 1 ≤ p := hc
    rw [hs]
    simp only [if_pos hc']
    rw [card_filter_fin_Ico _ _ _ (by omega)]
    omega
  · have hs : stepOf Ψ p q r = ⟨Sum.inr r.1, ⟨r.2 - p, by simp [rk]; omega⟩⟩ := by
      unfold stepOf
      rw [dif_neg hc]
    have hc' : ¬ ((r.2 : ℕ) + 1 ≤ p) := by omega
    rw [hs]
    simp only [if_neg hc']
    have := card_filter_fin_Ico (p + q) 0 ((r.2 : ℕ) + 1 - p) (by omega)
    simp only [Nat.zero_le, true_and] at this
    rw [this]
    omega

/- English proof (translation)
Introduce `a ha`. Take `⟨-, hsub⟩` from `h`. Establish `hmem` using `hsub ha`. Establish `hv` using `a.isLt`. Distinguish the cases in `hc : (r.2 : ℕ) < p`.

Establish `hs : stepOf Ψ p q r = ⟨Sum.inl r.1, ⟨r.2, by simp [rk]; omega⟩⟩`. Unfold `stepOf`. Rewrite using `[dif_pos hc]`. Establish `hc' : (r.2 : ℕ) + 1 ≤ p` using `hc`. Rewrite `hmem` using `[if_pos hc']`.

Simplify using `only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hmem`. Rewrite using `[hs]`. Use `⟨⟨a - q, by simp [rk]; omega⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [posOf, wEmb]`. Use `ext`.

Simplify using `only`. Use linear arithmetic over natural numbers and integers. Establish `hs : stepOf Ψ p q r = ⟨Sum.inr r.1, ⟨r.2 - p, by simp [rk]; omega⟩⟩`. Unfold `stepOf`. Rewrite using `[dif_neg hc]`.

Establish `hc' : ¬ ((r.2 : ℕ) + 1 ≤ p)` using `by omega`. Rewrite `hmem` using `[if_neg hc']`. Simplify using `only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hmem`. Rewrite using `[hs]`. Use `⟨⟨a, by simp [rk]; omega⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only [posOf, omEmb]`.
-/
theorem stepRows_pos (r : Ψ × Fin (p + q)) {I : Finset (Fin (p + q))} (h : IsStepRows (p + q) p r.2 I) :
    ∀ a ∈ I, ∃ l, posOf p q (stepOf Ψ p q r).1 l = a := by
  intro a ha
  obtain ⟨-, hsub⟩ := h
  have hmem := hsub ha
  have hv := a.isLt
  by_cases hc : (r.2 : ℕ) < p
  · have hs : stepOf Ψ p q r = ⟨Sum.inl r.1, ⟨r.2, by simp [rk]; omega⟩⟩ := by
      unfold stepOf
      rw [dif_pos hc]
    have hc' : (r.2 : ℕ) + 1 ≤ p := hc
    rw [if_pos hc'] at hmem
    simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rw [hs]
    refine ⟨⟨a - q, by simp [rk]; omega⟩, ?_⟩
    simp only [posOf, wEmb]
    ext
    simp only
    omega
  · have hs : stepOf Ψ p q r = ⟨Sum.inr r.1, ⟨r.2 - p, by simp [rk]; omega⟩⟩ := by
      unfold stepOf
      rw [dif_neg hc]
    have hc' : ¬ ((r.2 : ℕ) + 1 ≤ p) := by omega
    rw [if_neg hc'] at hmem
    simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rw [hs]
    refine ⟨⟨a, by simp [rk]; omega⟩, ?_⟩
    simp only [posOf, omEmb]

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

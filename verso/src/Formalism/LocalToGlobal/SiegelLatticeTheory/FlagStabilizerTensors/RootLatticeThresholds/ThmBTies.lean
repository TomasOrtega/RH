import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmBUse

noncomputable section

namespace Formalism.L2.SG.Pf.OrderedProducts

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.BesselShellMomentBounds Formalism.L2.SG.RowsConc Formalism.FourierDecayAlt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lists

def oprod {X : Type*} (G : ℕ → X × ℕ → ℝ) : ℕ → List (X × ℕ) → ℝ
  | _, [] => 1
  | a, b :: L => G (a + b.2) b * oprod G (a + b.2) L

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem oprod_cons {X : Type*} (G : ℕ → X × ℕ → ℝ) (a : ℕ) (b : X × ℕ) (L : List (X × ℕ)) :
    oprod G a (b :: L) = G (a + b.2) b * oprod G (a + b.2) L := rfl

/- English proof (translation)
The claim follows from `| [], a => by simp [oprod] | b :: L, a => by refine (Fin.prod_univ_succ _).trans ?_ rw [oprod_cons, ← fin_prod_oprod G L (a + b.2)] simp [pS, add_assoc]`.
-/
theorem fin_prod_oprod {K : Type} [Field K] (G : ℕ → K × ℕ → ℝ) :
    ∀ (L : List (K × ℕ)) (a : ℕ), ∏ i : Fin L.length, G (a + pS L ((i : ℕ) + 1)) L[i] = oprod G a L
  | [], a => by simp [oprod]
  | b :: L, a => by
    refine (Fin.prod_univ_succ _).trans ?_
    rw [oprod_cons, ← fin_prod_oprod G L (a + b.2)]
    simp [pS, add_assoc]

/- English proof (translation)
The claim follows from `| [] => by simp | x :: L => by refine (Fin.prod_univ_succ _).trans ?_ simp`.
-/
theorem fin_prod_list {X : Type*} (f : X → ℝ) : ∀ L : List X, ∏ i : Fin L.length, f L[i] = (L.map f).prod
  | [] => by simp
  | x :: L => by
    refine (Fin.prod_univ_succ _).trans ?_
    simp

end Lists

section Weights

variable (k r : ℕ) (T T' : ℝ)

def pW (L : List (ℂ × ℕ)) : ℝ := (L.map fun b => ‖b.1‖ ^ (2 * b.2)).prod

def gW : List (ℂ × ℕ) → ℝ
  | [] => 1
  | [b] => if b.2 = 1 then Complex.normSq b.1 - T * T' else ‖b.1‖ ^ (2 * b.2)
  | b :: c :: L => ‖b.1‖ ^ (2 * b.2) * gW (c :: L)

def eG (j : ℕ) (b : ℂ × ℕ) : ℝ := ‖b.1‖ ^ (2 * b.2 * (2 * (r + 1 - j) + b.2 - 1))

/- English proof (translation)
Establish `h : 2 * x + k + 1 + s - 3 = (k - 1) + (2 * x + s - 1)` using `by omega`. Rewrite using `[h, Nat.mul_add]`.
-/
theorem expo (k s x : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s) :
    2 * s * (2 * x + k + 1 + s - 3) = 2 * s * (k - 1) + 2 * s * (2 * x + s - 1) := by
  have h : 2 * x + k + 1 + s - 3 = (k - 1) + (2 * x + s - 1) := by omega
  rw [h, Nat.mul_add]

/- English proof (translation)
The claim follows from `| [], a, _, _ => by simp [ptWeightFrom, gW, oprod] | [(t, s)], a, hs, hl => by have hs1 : 1 ≤ s := hs (t, s) (by simp) simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hl by_cases h1 : s = 1 · subst h1 rw [ptWeightFrom, if_pos ⟨rfl, hl⟩] simp [ptW …`.
-/
theorem ptWeightFrom_eq (hk : 1 ≤ k) : ∀ (L : List (ℂ × ℕ)) (a : ℕ), (∀ b ∈ L, 1 ≤ b.2) →
    a + (L.map Prod.snd).sum = r + 1 → ptWeightFrom k r T T' a L = gW T T' L ^ (k - 1) * oprod (eG r) a L
  | [], a, _, _ => by simp [ptWeightFrom, gW, oprod]
  | [(t, s)], a, hs, hl => by
    have hs1 : 1 ≤ s := hs (t, s) (by simp)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hl
    by_cases h1 : s = 1
    · subst h1
      rw [ptWeightFrom, if_pos ⟨rfl, hl⟩]
      simp [ptWeightFrom, gW, oprod, eG, hl]
    · have hc : ¬ (s = 1 ∧ a + 1 = r + 1) := fun h => h1 h.1
      rw [ptWeightFrom, if_neg hc]
      simp only [ptWeightFrom, gW, oprod, eG, if_neg h1, mul_one]
      rw [hl, ← pow_mul, ← pow_add]
      congr 1
      have e := expo k s (r + 1 - (r + 1)) hk hs1
      simp only [Ml] at e ⊢
      rw [e]
  | (t, s) :: c :: L, a, hs, hl => by
    have hs1 : 1 ≤ s := hs (t, s) (by simp)
    have hc1 : 1 ≤ c.2 := hs c (by simp)
    have hsr : ∀ b ∈ c :: L, 1 ≤ b.2 := fun b hb => hs b (List.mem_cons_of_mem _ hb)
    simp only [List.map_cons, List.sum_cons] at hl
    have hl' : a + s + ((c :: L).map Prod.snd).sum = r + 1 := by
      simp only [List.map_cons, List.sum_cons]; omega
    have hn : ¬ (s = 1 ∧ a + 1 = r + 1) := by
      rintro ⟨rfl, h⟩; omega
    rw [ptWeightFrom, if_neg hn, ptWeightFrom_eq hk (c :: L) (a + s) hsr hl']
    simp only [gW, oprod_cons, eG]
    have e := expo k s (r + 1 - (a + s)) hk hs1
    simp only [Ml]
    rw [e, pow_add, pow_mul, mul_pow]
    ring

end Weights

section Minors

/- English proof (translation)
Establish `h1 : c.length - 1 + 1 = c.length` using `by omega`. Establish `h2` using `c.sizeUpTo_succ' ⟨c.length - 1, by omega⟩`. Simplify using `only [Fin.val_mk, h1, Composition.sizeUpTo_length] at h2`. Conclude with `h2.symm`.
-/
theorem comp_last {n : ℕ} (c : Composition (n + 1)) (h : 0 < c.length) :
    c.sizeUpTo (c.length - 1) + c.blocksFun ⟨c.length - 1, by omega⟩ = n + 1 := by
  have h1 : c.length - 1 + 1 = c.length := by omega
  have h2 := c.sizeUpTo_succ' ⟨c.length - 1, by omega⟩
  simp only [Fin.val_mk, h1, Composition.sizeUpTo_length] at h2
  exact h2.symm

/- English proof (translation)
Introduce `heq`. Establish `hlast` using `comp_last c h`. Establish `hpos` using `c.one_le_blocksFun ⟨c.length - 1, by omega⟩`. Break down `Nat.lt_or_ge q c.length with hq | hq` into its components or cases. Establish `hmono : c.sizeUpTo q ≤ c.sizeUpTo (c.length - 1)` using `c.monotone_sizeUpTo (by omega)`.

Use linear arithmetic over natural numbers and integers. Use `c.sizeUpTo_ofLength_le q hq` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem comp_not_end {n : ℕ} (c : Composition (n + 1)) (h : 0 < c.length)
    (hb : c.blocksFun ⟨c.length - 1, by omega⟩ ≠ 1) (q : ℕ) : n ≠ c.sizeUpTo q := by
  intro heq
  have hlast := comp_last c h
  have hpos := c.one_le_blocksFun ⟨c.length - 1, by omega⟩
  rcases Nat.lt_or_ge q c.length with hq | hq
  · have hmono : c.sizeUpTo q ≤ c.sizeUpTo (c.length - 1) := c.monotone_sizeUpTo (by omega)
    omega
  · have := c.sizeUpTo_ofLength_le q hq
    omega

/- English proof (translation)
Use `first`. Consider the case `exact c.length_pos_of_pos (Nat.succ_pos n)`. Consider the case `exact Composition.length_pos_of_pos c (Nat.succ_pos n)`.
-/
theorem comp_len_pos {n : ℕ} (c : Composition (n + 1)) : 0 < c.length := by
  first
    | exact c.length_pos_of_pos (Nat.succ_pos n)
    | exact Composition.length_pos_of_pos c (Nat.succ_pos n)

/- English proof (translation)
Unfold `toComp`. Simplify using `only [Composition.blocksFun]`. Use `first`. Consider the case `exact List.getElem_map Prod.snd`. Consider the case `exact List.getElem_map ..`.

Consider the case `exact List.get_map Prod.snd`. Consider the case `exact List.get_map ..`. Consider the case `(rw [List.get_eq_getElem]; simp)`.
-/
theorem blocksFun_toComp {K : Type} [Field K] {d : ℕ} (p : Point K d) (a : Fin (toComp p).length) :
    (toComp p).blocksFun a = (p.1[(a : ℕ)]'(lt_of_lt_of_eq a.2 (toComp_length p))).2 := by
  unfold toComp
  simp only [Composition.blocksFun]
  first
    | exact List.getElem_map Prod.snd
    | exact List.getElem_map ..
    | exact List.get_map Prod.snd
    | exact List.get_map ..
    | (rw [List.get_eq_getElem]; simp)

/- English proof (translation)
Simplify using `[pW, List.map_append, List.prod_append]`.
-/
theorem pW_append (L0 : List (ℂ × ℕ)) (t : ℂ) (s : ℕ) : pW (L0 ++ [(t, s)]) = pW L0 * ‖t‖ ^ (2 * s) := by
  simp [pW, List.map_append, List.prod_append]

/- English proof (translation)
Consider the cases of `L with`. Consider the case `nil => exact absurd rfl hL`. Consider the case `cons c L => first`. Consider the case `rfl`. Consider the case `simp [gW]`.
-/
theorem gW_cons (T T' : ℝ) (b : ℂ × ℕ) (L : List (ℂ × ℕ)) (hL : L ≠ []) :
    gW T T' (b :: L) = ‖b.1‖ ^ (2 * b.2) * gW T T' L := by
  cases L with
  | nil => exact absurd rfl hL
  | cons c L =>
    first
    | rfl
    | simp [gW]

/- English proof (translation)
The claim follows from `| [] => by simp [gW, pW] | b :: L0 => by rw [List.cons_append, gW_cons T T' b _ (by simp), gW_append T T' t s L0] simp [pW, mul_assoc]`.
-/
theorem gW_append (T T' : ℝ) (t : ℂ) (s : ℕ) : ∀ L0 : List (ℂ × ℕ),
    gW T T' (L0 ++ [(t, s)]) = pW L0 * (if s = 1 then Complex.normSq t - T * T' else ‖t‖ ^ (2 * s))
  | [] => by simp [gW, pW]
  | b :: L0 => by
    rw [List.cons_append, gW_cons T T' b _ (by simp), gW_append T T' t s L0]
    simp [pW, mul_assoc]

/- English proof (translation)
Establish `e1 : leadMinor (ptMat p) (r + 1) le_rfl = Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor (Formalism.HermitianLatticeCounting.ExpansionTerms.blockAntidiagonalMatrix (toComp p) (toT p)) (r + 1)`. Rewrite using `[← ptMat_eq]`. Conclude with `leadMinorK_eq _ _ _`. Establish `v` using `Formalism.HermitianLatticeCounting.Final.ExpansionTerms.e4aValue ℂ (r + 1) (toComp p) (toT p) (toComp p).length`. Rewrite `v` using `[(toComp p).sizeUpTo_length]`.

Rewrite using `[e1, v, map_prod, Finset.filter_true_of_mem (fun a _ => a.2)]`. Establish `h : ∀ a : Fin (toComp p).length, Complex.normSq ((-1) ^ ((toComp p).blocksFun a).choose 2 * toT p a ^ (toComp p).blocksFun a) = ‖(p.1[(a : ℕ)]'(lt_of_lt_of_eq a.2 (toComp_length p))).1‖ ^ (2 * (p.1[(a : ℕ)]'(lt_of_lt_of_eq a.2 (toComp_length p))).2)`. Introduce `a`. Rewrite using `[map_mul, map_pow, map_pow, Complex.normSq_neg, Complex.normSq_one, one_pow, one_mul, Complex.normSq_eq_norm_sq, ← pow_mul]`. Rewrite using `[blocksFun_toComp]`.

Both sides reduce to the same expression. Rewrite using `[Finset.prod_congr rfl fun a _ => h a, pW, ← fin_prod_list]`. Conclude with `Fintype.prod_equiv (finCongr (toComp_length p)) _ _ fun a => rfl`.
-/
theorem normSq_lead_top {r : ℕ} (p : Point ℂ (r + 1)) :
    Complex.normSq (leadMinor (ptMat p) (r + 1) le_rfl) = pW p.1 := by
  have e1 : leadMinor (ptMat p) (r + 1) le_rfl = Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor (Formalism.HermitianLatticeCounting.ExpansionTerms.blockAntidiagonalMatrix (toComp p) (toT p)) (r + 1) := by
    rw [← ptMat_eq]; exact leadMinorK_eq _ _ _
  have v := Formalism.HermitianLatticeCounting.Final.ExpansionTerms.e4aValue ℂ (r + 1) (toComp p) (toT p) (toComp p).length
  rw [(toComp p).sizeUpTo_length] at v
  rw [e1, v, map_prod, Finset.filter_true_of_mem (fun a _ => a.2)]
  have h : ∀ a : Fin (toComp p).length, Complex.normSq ((-1) ^ ((toComp p).blocksFun a).choose 2 * toT p a ^ (toComp p).blocksFun a) =
      ‖(p.1[(a : ℕ)]'(lt_of_lt_of_eq a.2 (toComp_length p))).1‖ ^ (2 * (p.1[(a : ℕ)]'(lt_of_lt_of_eq a.2 (toComp_length p))).2) := by
    intro a
    rw [map_mul, map_pow, map_pow, Complex.normSq_neg, Complex.normSq_one, one_pow, one_mul,
      Complex.normSq_eq_norm_sq, ← pow_mul]
    rw [blocksFun_toComp]
    rfl
  rw [Finset.prod_congr rfl fun a _ => h a, pW, ← fin_prod_list]
  exact Fintype.prod_equiv (finCongr (toComp_length p)) _ _ fun a => rfl

/- English proof (translation)
Establish `e0 : leadMinor (ptMat p) r (Nat.le_succ r) = Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor (Formalism.HermitianLatticeCounting.ExpansionTerms.blockAntidiagonalMatrix (toComp p) (toT p)) r`. Rewrite using `[← ptMat_eq]`. Conclude with `leadMinorK_eq _ _ _`. Rewrite using `[e0]`. Establish `hlen : (toComp p).length = L0.length + 1` using `by rw [toComp_length, hp]; simp`.

Establish `hb : (toComp p).blocksFun ⟨(toComp p).length - 1, by omega⟩ = s`. Establish `e1` using `comp_last (toComp p) (comp_len_pos _)`. Establish `e2 : (toComp p).sizeUpTo ((toComp p).length - 1) = (L0.map Prod.snd).sum`. Rewrite using `[sizeUpTo_toComp, hlen, Nat.add_sub_cancel]`. Unfold `pS`.

Rewrite using `[hp]`. Simplify using the standard rewrite rules. Establish `e3 : (L0.map Prod.snd).sum + s = r + 1`. Establish `e` using `p.2.2`. Rewrite `e` using `[hp]`.

Simplify using `using e`. Use linear arithmetic over natural numbers and integers. Conclude with `Formalism.HermitianLatticeCounting.Final.ExpansionTerms.e4aVanish ℂ (r + 1) (toComp p) (toT p) r (Nat.le_succ r) (comp_not_end (toComp p) (comp_len_pos _) (by rw [hb]; exact hs))`.
-/
theorem lead_r_zero {r : ℕ} (p : Point ℂ (r + 1)) (L0 : List (ℂ × ℕ)) (t : ℂ) (s : ℕ)
    (hp : p.1 = L0 ++ [(t, s)]) (hs : s ≠ 1) : leadMinor (ptMat p) r (Nat.le_succ r) = 0 := by
  have e0 : leadMinor (ptMat p) r (Nat.le_succ r) = Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor (Formalism.HermitianLatticeCounting.ExpansionTerms.blockAntidiagonalMatrix (toComp p) (toT p)) r := by
    rw [← ptMat_eq]; exact leadMinorK_eq _ _ _
  rw [e0]
  have hlen : (toComp p).length = L0.length + 1 := by rw [toComp_length, hp]; simp
  have hb : (toComp p).blocksFun ⟨(toComp p).length - 1, by omega⟩ = s := by
    have e1 := comp_last (toComp p) (comp_len_pos _)
    have e2 : (toComp p).sizeUpTo ((toComp p).length - 1) = (L0.map Prod.snd).sum := by
      rw [sizeUpTo_toComp, hlen, Nat.add_sub_cancel]
      unfold pS; rw [hp]; simp
    have e3 : (L0.map Prod.snd).sum + s = r + 1 := by
      have e := p.2.2; rw [hp] at e; simpa using e
    omega
  exact Formalism.HermitianLatticeCounting.Final.ExpansionTerms.e4aVanish ℂ (r + 1) (toComp p) (toT p) r (Nat.le_succ r)
    (comp_not_end (toComp p) (comp_len_pos _) (by rw [hb]; exact hs))

/- English proof (translation)
Establish `hne : p.1 ≠ []`. Introduce `h`. Establish `e` using `p.2.2`. Rewrite `e` using `[h]`. Simplify using `at e`.

Take `⟨L0, b, hp⟩ : ∃ L0 b, p.1 = L0 ++ [b]` from `⟨_, _, (List.dropLast_append_getLast hne).symm⟩`. Take `⟨t, s⟩` from `b`. Establish `ht : t ≠ 0` using `(p.2.1 (t, s) (by rw [hp]; simp)).1`. Establish `htop` using `normSq_lead_top p`. Rewrite `htop` using `[hp, pW_append]`.

Rewrite using `[hp, gW_append]`. Unfold `Gpt`. Distinguish the cases in `hs : s = 1`. Substitute `hs` using the available equality. Take `⟨h1, -⟩` from `last_block p t (by rw [hp]; simp)`.

Rewrite `htop`, the goal using `[h1, Complex.normSq_mul]`. Rewrite using `[if_pos rfl]`. Establish `hn : Complex.normSq t = ‖t‖ ^ (2 * 1)` using `by rw [Complex.normSq_eq_norm_sq]`. Establish `hpos : 0 < Complex.normSq t` using `Complex.normSq_pos.2 ht`. Establish `e : Complex.normSq (leadMinor (ptMat p) r (Nat.le_succ r)) = pW L0`.

Rewrite `htop` using `[← hn]`. Conclude with `mul_right_cancel₀ hpos.ne' htop`. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hs, lead_r_zero p L0 t s hp hs, map_zero, mul_zero, sub_zero, htop]`.
-/
theorem GPoint_eq_gW {r : ℕ} (T T' : ℝ) (p : Point ℂ (r + 1)) : Gpt T T' p = gW T T' p.1 := by
  have hne : p.1 ≠ [] := by
    intro h; have e := p.2.2; rw [h] at e; simp at e
  obtain ⟨L0, b, hp⟩ : ∃ L0 b, p.1 = L0 ++ [b] := ⟨_, _, (List.dropLast_append_getLast hne).symm⟩
  obtain ⟨t, s⟩ := b
  have ht : t ≠ 0 := (p.2.1 (t, s) (by rw [hp]; simp)).1
  have htop := normSq_lead_top p
  rw [hp, pW_append] at htop
  rw [hp, gW_append]
  unfold Gpt
  by_cases hs : s = 1
  · subst hs
    obtain ⟨h1, -⟩ := last_block p t (by rw [hp]; simp)
    rw [h1, Complex.normSq_mul] at htop ⊢
    rw [if_pos rfl]
    have hn : Complex.normSq t = ‖t‖ ^ (2 * 1) := by rw [Complex.normSq_eq_norm_sq]
    have hpos : 0 < Complex.normSq t := Complex.normSq_pos.2 ht
    have e : Complex.normSq (leadMinor (ptMat p) r (Nat.le_succ r)) = pW L0 := by
      rw [← hn] at htop; exact mul_right_cancel₀ hpos.ne' htop
    rw [e]; ring
  · rw [if_neg hs, lead_r_zero p L0 t s hp hs, map_zero, mul_zero, sub_zero, htop]

end Minors

section Rat

variable (D : D7)

/- English proof (translation)
Unfold `Formalism.BasicNotions.Host.rdE`. Use `Real.one_le_rpow ?_ (by positivity)` and prove the remaining obligations. Establish `h : (1 : ℤ) ≤ |NumberField.discr D.host.E|` using `Int.one_le_abs (NumberField.discr_ne_zero D.host.E)`. Establish `h' : (1 : ℝ) ≤ ((|NumberField.discr D.host.E| : ℤ) : ℝ)` using `by exact_mod_cast h`. Rewrite `h'` using `[Int.cast_abs]`. Then use the resulting hypothesis.
-/
theorem one_le_rd : 1 ≤ D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  refine Real.one_le_rpow ?_ (by positivity)
  have h : (1 : ℤ) ≤ |NumberField.discr D.host.E| := Int.one_le_abs (NumberField.discr_ne_zero D.host.E)
  have h' : (1 : ℝ) ≤ ((|NumberField.discr D.host.E| : ℤ) : ℝ) := by exact_mod_cast h
  rwa [Int.cast_abs] at h'

/- English proof (translation)
Establish `hpos : 0 < (toPts w).1.length` using `comp_len_pos _`. Unfold `DlastPt`. Rewrite using `[dif_pos hpos]`. Unfold `endMin`. Rewrite using `[E5minor_eq]`.

Establish `e : (toPts w).1.sizeUpTo (((⟨(toPts w).1.length - 1, by omega⟩ : Fin (toPts w).1.length) : ℕ) + 1) = D.R.rS + 1`. Simplify using `only [Nat.sub_add_cancel hpos, (toPts w).1.sizeUpTo_length]`. Rewrite using `[e, leadMinorK_eq, ptMat_eq]`. Both sides reduce to the same expression.
-/
theorem dlast_eq (w : Point D.host.E (D.R.rS + 1)) : DlastPt (toPts w) = leadMinorK (ptMat w) (D.R.rS + 1) le_rfl := by
  have hpos : 0 < (toPts w).1.length := comp_len_pos _
  unfold DlastPt
  rw [dif_pos hpos]
  unfold endMin
  rw [E5minor_eq]
  have e : (toPts w).1.sizeUpTo (((⟨(toPts w).1.length - 1, by omega⟩ : Fin (toPts w).1.length) : ℕ) + 1) = D.R.rS + 1 := by
    simp only [Nat.sub_add_cancel hpos, (toPts w).1.sizeUpTo_length]
  rw [e, leadMinorK_eq, ptMat_eq]
  rfl

/- English proof (translation)
Establish `hpos : 0 < (toPts w).1.length` using `comp_len_pos _`. Establish `hl` using `comp_last (toPts w).1 hpos`. Establish `eL : leadMinorK (ptMat w) D.R.rS (Nat.le_succ _) = Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor (Formalism.HermitianLatticeCounting.ExpansionTerms.blockAntidiagonalMatrix (toPts w).1 (toPts w).2) D.R.rS`. Rewrite using `[leadMinorK_eq, ptMat_eq]`. Both sides reduce to the same expression.

Rewrite using `[eL]`. Unfold `DrPt`. Rewrite using `[dif_pos hpos]`. Distinguish the cases in `hb : (toPts w).1.blocksFun ⟨(toPts w).1.length - 1, by omega⟩ = 1`. Rewrite using `[if_pos hb]`.

Establish `hr : D.R.rS = (toPts w).1.sizeUpTo ((toPts w).1.length - 1)` using `by omega`. Distinguish the cases in `h2 : 2 ≤ (toPts w).1.length`. Rewrite using `[dif_pos h2]`. Unfold `endMin`. Rewrite using `[E5minor_eq, congrArg (Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor _) hr]`.

Use `congr 2`. Simplify using `only`. Use linear arithmetic over natural numbers and integers. Rewrite using `[dif_neg h2]`. Establish `h1 : (toPts w).1.length - 1 = 0` using `by omega`.

Rewrite using `[congrArg (Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor _) hr, Formalism.HermitianLatticeCounting.Final.ExpansionTerms.e4aValue, h1]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg hb]`. Conclude with `(Formalism.HermitianLatticeCounting.Final.ExpansionTerms.e4aVanish D.host.E (D.R.rS + 1) (toPts w).1 (toPts w).2 D.R.rS (Nat.le_succ _) (comp_not_end (toPts w).1 hpos hb)).symm`.
-/
theorem dr_eq (w : Point D.host.E (D.R.rS + 1)) : DrPt (toPts w) = leadMinorK (ptMat w) D.R.rS (Nat.le_succ _) := by
  have hpos : 0 < (toPts w).1.length := comp_len_pos _
  have hl := comp_last (toPts w).1 hpos
  have eL : leadMinorK (ptMat w) D.R.rS (Nat.le_succ _) =
      Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor (Formalism.HermitianLatticeCounting.ExpansionTerms.blockAntidiagonalMatrix (toPts w).1 (toPts w).2) D.R.rS := by
    rw [leadMinorK_eq, ptMat_eq]; rfl
  rw [eL]
  unfold DrPt
  rw [dif_pos hpos]
  by_cases hb : (toPts w).1.blocksFun ⟨(toPts w).1.length - 1, by omega⟩ = 1
  · rw [if_pos hb]
    have hr : D.R.rS = (toPts w).1.sizeUpTo ((toPts w).1.length - 1) := by omega
    by_cases h2 : 2 ≤ (toPts w).1.length
    · rw [dif_pos h2]
      unfold endMin
      rw [E5minor_eq, congrArg (Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor _) hr]
      congr 2
      simp only
      omega
    · rw [dif_neg h2]
      have h1 : (toPts w).1.length - 1 = 0 := by omega
      rw [congrArg (Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor _) hr, Formalism.HermitianLatticeCounting.Final.ExpansionTerms.e4aValue, h1]
      simp
  · rw [if_neg hb]
    exact (Formalism.HermitianLatticeCounting.Final.ExpansionTerms.e4aVanish D.host.E (D.R.rS + 1) (toPts w).1 (toPts w).2 D.R.rS (Nat.le_succ _)
      (comp_not_end (toPts w).1 hpos hb)).symm

/- English proof (translation)
Unfold `GPt Gglob`. Rewrite using `[dlast_eq, dr_eq, Formalism.BasicNotions.Examples₂.star_eq_conj (H := D.host), Formalism.BasicNotions.Examples₂.star_eq_conj (H := D.host), Nat.cast_mul]`.
-/
theorem GPt_eq (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) : GPt (T * T') (toPts w) = Gglob D T T' w := by
  unfold GPt Gglob
  rw [dlast_eq, dr_eq, Formalism.BasicNotions.Examples₂.star_eq_conj (H := D.host), Formalism.BasicNotions.Examples₂.star_eq_conj (H := D.host), Nat.cast_mul]

end Rat

section Weight

variable (D : D7)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Fin.prod_univ_castSucc, mul_pow]`. Simplify using `only [Fin.val_castSucc, Fin.val_last]`.

Rewrite using `[ih]`. Unfold `alf`. Rewrite using `[show (D.host.rdE ^ (-((D.R.rS : ℤ) - (n : ℤ)))) ^ 2 = D.host.rdE ^ (-((D.R.rS : ℤ) - (n : ℤ)) * 2) by`. Rewrite using `[zpow_mul, zpow_two, sq], ← zpow_add₀ (rdE_pos D).ne']`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem alf_sq (n : ℕ) : (∏ i : Fin n, alf D i) ^ 2 = D.host.rdE ^ (-((n : ℤ) * (2 * (D.R.rS : ℤ) + 1 - n))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc, mul_pow]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    unfold alf
    rw [show (D.host.rdE ^ (-((D.R.rS : ℤ) - (n : ℤ)))) ^ 2 = D.host.rdE ^ (-((D.R.rS : ℤ) - (n : ℤ)) * 2) by
      rw [zpow_mul, zpow_two, sq], ← zpow_add₀ (rdE_pos D).ne']
    congr 1; push_cast; ring

/- English proof (translation)
Rewrite using `[alf_sq, ← zpow_natCast D.host.rdE, ← zpow_neg, sq, ← zpow_add₀ (rdE_pos D).ne']`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem alfq : ((∏ i : Fin D.R.rS, alf D i) ^ 2) ^ 2 = (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1)))⁻¹ := by
  rw [alf_sq, ← zpow_natCast D.host.rdE, ← zpow_neg, sq, ← zpow_add₀ (rdE_pos D).ne']
  congr 1; push_cast; ring

/- English proof (translation)
Unfold `rhoReal`. Rewrite using `[← zpow_natCast, ← zpow_neg]`. Use `congr 1`. Establish `h2 : 2 * (a + s) ≤ 2 * D.R.rS + 1 + s` using `by omega`. Move the coercions through the operations in `[Nat.cast_sub h2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem rho_eq (a s : ℕ) (hs : 1 ≤ s) (h : a + s ≤ D.R.rS + 1) :
    rhoReal D (a + 1) s = (D.host.rdE ^ (2 * D.R.rS + 1 + s - 2 * (a + s)))⁻¹ := by
  unfold rhoReal
  rw [← zpow_natCast, ← zpow_neg]
  congr 1
  have h2 : 2 * (a + s) ≤ 2 * D.R.rS + 1 + s := by omega
  push_cast [Nat.cast_sub h2]
  ring

/- English proof (translation)
The claim follows from `| [], a, _, _ => rfl | (t, s) :: L, a, hs, h => by have hs1 : 1 ≤ s := hs (t, s) (by simp) simp only [List.map_cons, List.sum_cons] at h rw [locBlocksFrom, oprod_cons, oprod_cons] dsimp only rw [eW_loc v L (a + s) (fun b hb => hs b (List.mem_cons_of_mem _ hb)) (by omega)] congr 1 …`.
-/
theorem eW_loc (v : D.what₂.Tau) : ∀ (L : List (D.host.E × ℕ)) (a : ℕ), (∀ b ∈ L, 1 ≤ b.2) →
    a + (L.map Prod.snd).sum ≤ D.R.rS + 1 →
    oprod (eG D.R.rS) a (locBlocksFrom D (rhoReal D) v a L) =
      oprod (fun j b => ((D.host.rdE ^ (2 * D.R.rS + 1 + b.2 - 2 * j))⁻¹ * ‖plEmb D v b.1‖) ^
        (2 * b.2 * (2 * (D.R.rS + 1 - j) + b.2 - 1))) a L
  | [], a, _, _ => rfl
  | (t, s) :: L, a, hs, h => by
    have hs1 : 1 ≤ s := hs (t, s) (by simp)
    simp only [List.map_cons, List.sum_cons] at h
    rw [locBlocksFrom, oprod_cons, oprod_cons]
    dsimp only
    rw [eW_loc v L (a + s) (fun b hb => hs b (List.mem_cons_of_mem _ hb)) (by omega)]
    congr 1
    simp only [eG]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (rhoReal_pos D _ _).le, rho_eq D a s hs1 (by omega)]

/- English proof (translation)
Establish `hP : 0 < ∏ i : Fin D.R.rS, alf D i` using `Finset.prod_pos fun i _ => alf_pos D i`. Establish `hQ : 0 < ((∏ i : Fin D.R.rS, alf D i) ^ 2) ^ 2` using `by positivity`. Establish `hloc : Gpt (T : ℝ) (T' : ℝ) (ptLoc D v w) = ((∏ i : Fin D.R.rS, alf D i) ^ 2) ^ 2 * (Complex.normSq (plEmb D v (leadMinorK (ptMat w) (D.R.rS + 1) le_rfl)) - (T : ℝ) * (T' : ℝ) * Complex.normSq (plEmb D v (leadMinorK (ptMat w) D.R.rS (Nat.le_succ _))))` using `GPoint_loc D _ _ v w`. Establish `e1 : plOf D v (GPt (T * T') (toPts w)) = |Complex.normSq (plEmb D v (leadMinorK (ptMat w) (D.R.rS + 1) le_rfl)) - (T : ℝ) * (T' : ℝ) * Complex.normSq (plEmb D v (leadMinorK (ptMat w) D.R.rS (Nat.le_succ _)))|`. Rewrite using `[plOf_apply, GPt_eq]`.

Use `show ‖plEmb D v (Gglob D T T' w)‖ = _`. Rewrite using `[plEmb_Gglob, Complex.norm_real, Real.norm_eq_abs]`. Establish `hXp : 0 < Complex.normSq (plEmb D v (leadMinorK (ptMat w) (D.R.rS + 1) le_rfl)) - (T : ℝ) * (T' : ℝ) * Complex.normSq (plEmb D v (leadMinorK (ptMat w) D.R.rS (Nat.le_succ _)))`. Rewrite `hG` using `[hloc]`. Conclude with `pos_of_mul_pos_right hG hQ.le`.

Rewrite using `[e1, abs_of_pos hXp, hloc, ← alfq D]`.
-/
theorem gpart (T T' : ℕ) (v : D.what₂.Tau) (w : Point D.host.E (D.R.rS + 1))
    (hG : 0 < Gpt (T : ℝ) (T' : ℝ) (ptLoc D v w)) :
    (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1)))⁻¹ * plOf D v (GPt (T * T') (toPts w)) =
      Gpt (T : ℝ) (T' : ℝ) (ptLoc D v w) := by
  have hP : 0 < ∏ i : Fin D.R.rS, alf D i := Finset.prod_pos fun i _ => alf_pos D i
  have hQ : 0 < ((∏ i : Fin D.R.rS, alf D i) ^ 2) ^ 2 := by positivity
  have hloc : Gpt (T : ℝ) (T' : ℝ) (ptLoc D v w) = ((∏ i : Fin D.R.rS, alf D i) ^ 2) ^ 2 *
      (Complex.normSq (plEmb D v (leadMinorK (ptMat w) (D.R.rS + 1) le_rfl)) -
        (T : ℝ) * (T' : ℝ) * Complex.normSq (plEmb D v (leadMinorK (ptMat w) D.R.rS (Nat.le_succ _)))) :=
    GPoint_loc D _ _ v w
  have e1 : plOf D v (GPt (T * T') (toPts w)) =
      |Complex.normSq (plEmb D v (leadMinorK (ptMat w) (D.R.rS + 1) le_rfl)) -
        (T : ℝ) * (T' : ℝ) * Complex.normSq (plEmb D v (leadMinorK (ptMat w) D.R.rS (Nat.le_succ _)))| := by
    rw [plOf_apply, GPt_eq]
    show ‖plEmb D v (Gglob D T T' w)‖ = _
    rw [plEmb_Gglob, Complex.norm_real, Real.norm_eq_abs]
  have hXp : 0 < Complex.normSq (plEmb D v (leadMinorK (ptMat w) (D.R.rS + 1) le_rfl)) -
        (T : ℝ) * (T' : ℝ) * Complex.normSq (plEmb D v (leadMinorK (ptMat w) D.R.rS (Nat.le_succ _))) := by
    rw [hloc] at hG; exact pos_of_mul_pos_right hG hQ.le
  rw [e1, abs_of_pos hXp, hloc, ← alfq D]

/- English proof (translation)
Establish `hk : 1 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Rewrite using `[ptWeightG_eq_prod]`. Unfold `nPt`. Use `symm`. Use `Fintype.prod_bijective (plOf D) (plOf_bij D) _ _ fun v => ?_` and prove the remaining obligations.

Unfold `nLoc ptWeight`. Rewrite using `[ptWeightFrom_eq D.R.k D.R.rS (T : ℝ) (T' : ℝ) hk _ 0 (fun b hb => ((ptLoc D v w).2.1 b hb).2) (by rw [zero_add]; exact (ptLoc D v w).2.2), ← GPoint_eq_gW, gpart D T T' v w (hG v)]`. Use `congr 1`. Use `show oprod (eG D.R.rS) 0 (locBlocksFrom D (rhoReal D) v 0 w.1) = _`. Rewrite using `[eW_loc D v w.1 0 (fun b hb => (w.2.1 b hb).2) (by rw [zero_add, w.2.2]), ← fin_prod_oprod]`.

Use `Fintype.prod_equiv (finCongr (toComp_length w).symm) _ _ fun i => ?_` and prove the remaining obligations. Simplify using `only [zero_add]`. Simplify using `[Composition.blocksFun, toComp, toPts, endIdx, plOf_apply, absV, finCongr]`. Both sides reduce to the same expression.
-/
theorem nPt_eq (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) (hG : ∀ v, 0 < Gpt (T : ℝ) (T' : ℝ) (ptLoc D v w)) :
    nPt D.host.rdE D.R.k (T * T') (toPts w) = ptWeightG D (rhoReal D) T T' w.1 := by
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  rw [ptWeightG_eq_prod]
  unfold nPt
  symm
  refine Fintype.prod_bijective (plOf D) (plOf_bij D) _ _ fun v => ?_
  unfold nLoc ptWeight
  rw [ptWeightFrom_eq D.R.k D.R.rS (T : ℝ) (T' : ℝ) hk _ 0 (fun b hb => ((ptLoc D v w).2.1 b hb).2)
    (by rw [zero_add]; exact (ptLoc D v w).2.2), ← GPoint_eq_gW, gpart D T T' v w (hG v)]
  congr 1
  show oprod (eG D.R.rS) 0 (locBlocksFrom D (rhoReal D) v 0 w.1) = _
  rw [eW_loc D v w.1 0 (fun b hb => (w.2.1 b hb).2) (by rw [zero_add, w.2.2]), ← fin_prod_oprod]
  refine Fintype.prod_equiv (finCongr (toComp_length w).symm) _ _ fun i => ?_
  simp only [zero_add]
  simp [Composition.blocksFun, toComp, toPts, endIdx, plOf_apply, absV, finCongr]
  rfl

end Weight

section Joint

variable (D : D7)

/- English proof (translation)
Establish `hrd` using `one_le_rd D`. Establish `hrd0 : 0 ≤ D.host.rdE` using `zero_le_one.trans hrd`. Establish `hle : ∀ (N : ℕ) (x : ℝ), 0 ≤ x → (D.host.rdE ^ N)⁻¹ * x ≤ x` using `fun N x hx => mul_le_of_le_one_left hx (inv_le_one_of_one_le₀ (one_le_pow₀ hrd))`. Establish `hnn : ∀ (N : ℕ) (x : ℝ), 0 ≤ x → 0 ≤ (D.host.rdE ^ N)⁻¹ * x` using `fun N x hx => mul_nonneg (inv_nonneg.2 (pow_nonneg hrd0 _)) hx`. Unfold `normWt`.

Use `mul_le_mul ?_ ?_ (Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun p _ => hnn _ _ (sq_nonneg _)) (Finset.prod_nonneg fun v _ => norm_nonneg _)` and prove the remaining obligations. Unfold `NGPt NF`. Rewrite using `[GPt_eq]`. Combine the equalities or inequalities in the displayed calculation. Unfold `NDPt`.

Use `(Finset.prod_le_prod (fun a _ => Finset.prod_nonneg fun p _ => hnn _ _ (sq_nonneg _)) (fun a _ => Finset.prod_le_prod (fun p _ => hnn _ _ (sq_nonneg _)) (fun p _ => hle _ _ (sq_nonneg _)))).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[blockEnds_prod]`. Use `symm`. Use `Fintype.prod_equiv (finCongr (toComp_length w).symm) _ _ fun a => ?_` and prove the remaining obligations. Establish `hle' : 0 + pS w.1 ((a : ℕ) + 1) ≤ D.R.rS + 1` using `by rw [zero_add]; exact (toComp w).sizeUpTo_le _`.

Rewrite using `[dif_pos hle', NE]`. Use `Fintype.prod_bijective (plOf D) (plOf_bij D) _ _ fun v => ?_` and prove the remaining obligations. Rewrite using `[plOf_apply]`. Use `congr 2`. Apply the tactic sequence `show _ = Formalism.HermitianLatticeCounting.ExpansionTerms.IndexedMinorEntry (toComp w).blocksFun (toT w) _`.

Rewrite using `[E5minor_eq, leadMinorK_eq, ptMat_eq]`. Simplify using `[sizeUpTo_toComp]`.
-/
theorem ng_le (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) :
    NGPt D.host.rdE (T * T') (toPts w) * NDPt D.host.rdE (toPts w) ≤ normWt D T T' w := by
  have hrd := one_le_rd D
  have hrd0 : 0 ≤ D.host.rdE := zero_le_one.trans hrd
  have hle : ∀ (N : ℕ) (x : ℝ), 0 ≤ x → (D.host.rdE ^ N)⁻¹ * x ≤ x := fun N x hx =>
    mul_le_of_le_one_left hx (inv_le_one_of_one_le₀ (one_le_pow₀ hrd))
  have hnn : ∀ (N : ℕ) (x : ℝ), 0 ≤ x → 0 ≤ (D.host.rdE ^ N)⁻¹ * x := fun N x hx =>
    mul_nonneg (inv_nonneg.2 (pow_nonneg hrd0 _)) hx
  unfold normWt
  refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun p _ => hnn _ _ (sq_nonneg _))
    (Finset.prod_nonneg fun v _ => norm_nonneg _)
  · unfold NGPt NF
    rw [GPt_eq]
    calc ∏ p, (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1)))⁻¹ * p (Gglob D T T' w)
        ≤ ∏ p : NumberField.InfinitePlace D.host.E, p (Gglob D T T' w) :=
          Finset.prod_le_prod (fun p _ => hnn _ _ (apply_nonneg p _)) (fun p _ => hle _ _ (apply_nonneg p _))
      _ = ∏ v, absV D v (Gglob D T T' w) :=
          (Fintype.prod_bijective (plOf D) (plOf_bij D) _ _ fun v => (plOf_apply D v _).symm).symm
  · unfold NDPt
    refine (Finset.prod_le_prod (fun a _ => Finset.prod_nonneg fun p _ => hnn _ _ (sq_nonneg _))
      (fun a _ => Finset.prod_le_prod (fun p _ => hnn _ _ (sq_nonneg _)) (fun p _ => hle _ _ (sq_nonneg _)))).trans
      (le_of_eq ?_)
    rw [blockEnds_prod]
    symm
    refine Fintype.prod_equiv (finCongr (toComp_length w).symm) _ _ fun a => ?_
    have hle' : 0 + pS w.1 ((a : ℕ) + 1) ≤ D.R.rS + 1 := by rw [zero_add]; exact (toComp w).sizeUpTo_le _
    rw [dif_pos hle', NE]
    refine Fintype.prod_bijective (plOf D) (plOf_bij D) _ _ fun v => ?_
    rw [plOf_apply]
    congr 2
    show _ = Formalism.HermitianLatticeCounting.ExpansionTerms.IndexedMinorEntry (toComp w).blocksFun (toT w) _
    rw [E5minor_eq, leadMinorK_eq, ptMat_eq]
    simp [sizeUpTo_toComp]

/- English proof (translation)
Establish `hrd0 : 0 ≤ D.host.rdE` using `zero_le_one.trans (one_le_rd D)`. Unfold `nPt`. Conclude with `Finset.prod_nonneg fun p _ => mul_nonneg (pow_nonneg (mul_nonneg (inv_nonneg.2 (pow_nonneg hrd0 _)) (apply_nonneg p _)) _) (Finset.prod_nonneg fun a _ => pow_nonneg (mul_nonneg (inv_nonneg.2 (pow_nonneg hrd0 _)) (apply_nonneg p _)) _)`.
-/
theorem nPt_nonneg (k TT : ℕ) (γ : PN.Pts D.host.E D.R.rS) : 0 ≤ nPt D.host.rdE k TT γ := by
  have hrd0 : 0 ≤ D.host.rdE := zero_le_one.trans (one_le_rd D)
  unfold nPt
  exact Finset.prod_nonneg fun p _ => mul_nonneg
    (pow_nonneg (mul_nonneg (inv_nonneg.2 (pow_nonneg hrd0 _)) (apply_nonneg p _)) _)
    (Finset.prod_nonneg fun a _ => pow_nonneg (mul_nonneg (inv_nonneg.2 (pow_nonneg hrd0 _)) (apply_nonneg p _)) _)

/- English proof (translation)
Establish `hrd0 : 0 ≤ D.host.rdE` using `zero_le_one.trans (one_le_rd D)`. Establish `hW : 0 ≤ wPt D w * ptWeightG D (rhoReal D) T T' w.1` using `mul_nonneg (wPt_pos D w).le (by rw [← nPt_eq D T T' w hG]; exact nPt_nonneg D _ _ _)`. Establish `h0 : 0 ≤ NGPt D.host.rdE (T * T') (toPts w) * NDPt D.host.rdE (toPts w)`. Unfold `NGPt NDPt`. Conclude with `mul_nonneg (Finset.prod_nonneg fun p _ => mul_nonneg (inv_nonneg.2 (pow_nonneg hrd0 _)) (apply_nonneg p _)) (Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun p _ => mul_nonneg (inv_nonneg.2 (pow_nonneg hrd0 _)) (sq_nonneg _))`.

Rewrite using `[one_mul, show Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight (toPts w) = wPt D w from (wPt_eq D w).symm, nPt_eq D T T' w hG, show ((A : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2) = ((A * (D.R.rS + 1) ^ 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]`. Conclude with `mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (ng_le D T T' w) _) hW`.
-/
theorem wt_core (T T' A : ℕ) (w : Point D.host.E (D.R.rS + 1)) (hG : ∀ v, 0 < Gpt (T : ℝ) (T' : ℝ) (ptLoc D v w)) :
    Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight (toPts w) * nPt D.host.rdE D.R.k (T * T') (toPts w) *
              (NGPt D.host.rdE (T * T') (toPts w) * NDPt D.host.rdE (toPts w)) ^ (A * (D.R.rS + 1) ^ 2) ≤
      1 * (wPt D w * ptWeightG D (rhoReal D) T T' w.1 *
        normWt D T T' w ^ ((A : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2)) := by
  have hrd0 : 0 ≤ D.host.rdE := zero_le_one.trans (one_le_rd D)
  have hW : 0 ≤ wPt D w * ptWeightG D (rhoReal D) T T' w.1 :=
    mul_nonneg (wPt_pos D w).le (by rw [← nPt_eq D T T' w hG]; exact nPt_nonneg D _ _ _)
  have h0 : 0 ≤ NGPt D.host.rdE (T * T') (toPts w) * NDPt D.host.rdE (toPts w) := by
    unfold NGPt NDPt
    exact mul_nonneg (Finset.prod_nonneg fun p _ => mul_nonneg (inv_nonneg.2 (pow_nonneg hrd0 _)) (apply_nonneg p _))
      (Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun p _ =>
        mul_nonneg (inv_nonneg.2 (pow_nonneg hrd0 _)) (sq_nonneg _))
  rw [one_mul, show Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight (toPts w) = wPt D w from (wPt_eq D w).symm, nPt_eq D T T' w hG,
    show ((A : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2) = ((A * (D.R.rS + 1) ^ 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (ng_le D T T' w) _) hW

end Joint

end Formalism.L2.SG.Pf.OrderedProducts

namespace Formalism.L2.SG.Pf

/- English proof (translation)
Introduce `D T T' A w hw` and use `Formalism.L2.SG.Pf.OrderedProducts.wt_core D T T' A w hw.2`.
-/
theorem weightConclusion : Formalism.L2.SG.ThmBUse.WtTieConc := fun D T T' A w hw =>
  Formalism.L2.SG.Pf.OrderedProducts.wt_core D T T' A w hw.2

end Formalism.L2.SG.Pf

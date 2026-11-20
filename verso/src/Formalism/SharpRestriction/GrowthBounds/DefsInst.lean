import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Formalism.SharpRestriction.GrowthBounds.DataG

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions

noncomputable section

namespace Formalism.MainNotions.G

def GAtP.SandwichE {p : ℕ} (G : GAtP p) (e : ℕ) : Prop :=
  G.Mna.map (((p : G.O) ^ e) • LinearMap.id) ≤ G.M ∧ G.M ≤ G.Mna

def epSet (D : D7) (p : ℕ) : Set ℕ :=
  {e | ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    D.what₂.places.resChar w = p → (D.gat u w hg).SandwichE e}

def EpDef {D : D7} {L : SizeData₂ D} (X : Inst D L) (Ce : ℝ) : Prop :=
  ∀ p, X.ep p = ⌈Ce * (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a⌉₊

/- English proof (translation)
Rewrite using `[h]`. Conclude with `Nat.ceil_lt_add_one h0`.
-/
theorem EpDef.lt {D : D7} {L : SizeData₂ D} {X : Inst D L} {Ce : ℝ} (h : EpDef X Ce) (p : ℕ)
    (h0 : 0 ≤ Ce * (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a) :
    (X.ep p : ℝ) < Ce * (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a + 1 := by
  rw [h]; exact Nat.ceil_lt_add_one h0

/- English proof (translation)
Establish `h0 : 0 ≤ Ce * (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a`. Use `mul_nonneg hCe (le_trans zero_le_one h1)` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Establish `h2` using `h.lt p h0`. Use polynomial arithmetic with `[h2, h1]`.
-/
theorem EpDef.le {D : D7} {L : SizeData₂ D} {X : Inst D L} {Ce : ℝ} (h : EpDef X Ce) (p : ℕ) (hCe : 0 ≤ Ce)
    (h1 : 1 ≤ (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a) :
    (X.ep p : ℝ) ≤ (Ce + 1) * (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a := by
  have h0 : 0 ≤ Ce * (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a := by
    have := mul_nonneg hCe (le_trans zero_le_one h1)
    calc (0 : ℝ) ≤ Ce * ((D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a) := this
      _ = _ := by ring
  have h2 := h.lt p h0
  nlinarith [h2, h1]

def EpLeast {D : D7} {L : SizeData₂ D} (X : Inst D L) : Prop := ∀ p, X.ep p = sInf (epSet D p)

def kapISet {D : D7} (L : SizeData₂ D) (K : Consts) (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) : Set ℝ :=
  {κ | 0 ≤ κ ∧
    ∀ (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
      [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
      (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
      UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w →
      ∀ lam0 : Fin n' → Fin (D.R.k - 1 + 1) → ℤ, IsBaseWeight TT a b ⌊cG L⌋₊ lam0 → IsDominant lam0 →
        LPprime (W := W) p n' ι σ w 1 lam0 ⌈tIf K L p n' TT a b⌉₊ (DIf K L p n') κ (8 * (DIf K L p n' + 1))}

/- English proof (translation)
Use `⟨zero_le_one, ?_⟩` and prove the remaining obligations. Introduce `W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w _ lam0 _ _`. Use `⟨by omega, fun Λ _ => ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, 0, by simp, ⟨0, 0, fun _ i => i.elim0⟩⟩⟩` and prove the remaining obligations.
-/
theorem one_mem_kapISet {D : D7} (L : SizeData₂ D) (K : Consts) (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) :
    (1 : ℝ) ∈ kapISet L K p n' TT a b := by
  refine ⟨zero_le_one, ?_⟩
  intro W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w _ lam0 _ _
  refine ⟨by omega, fun Λ _ => ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
    fun i => i.elim0, 0, by simp, ⟨0, 0, fun _ i => i.elim0⟩⟩⟩

def KapIDef {D : D7} {L : SizeData₂ D} (X : Inst D L) (K : Consts) : Prop :=
  ∀ (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ), X.kapI p n' TT a b = sInf (kapISet L K p n' TT a b)

/- English proof (translation)
Rewrite using `[h]`. Conclude with `csInf_le ⟨0, fun x hx => hx.1⟩ hκ`.
-/
theorem KapIDef.le {D : D7} {L : SizeData₂ D} {X : Inst D L} {K : Consts} (h : KapIDef X K) {p n' : ℕ}
    {TT : Finset (Fin n')} {a b : Fin n' → ℤ} {κ : ℝ} (hκ : κ ∈ kapISet L K p n' TT a b) :
    X.kapI p n' TT a b ≤ κ := by
  rw [h]
  exact csInf_le ⟨0, fun x hx => hx.1⟩ hκ

/- English proof (translation)
Assemble the required witnesses or components as `⟨by rw [h]; exact le_csInf ⟨1, one_mem_kapISet L K p n' TT a b⟩ (fun x hx => hx.1), h.le (one_mem_kapISet L K p n' TT a b)⟩`.
-/
theorem KapIDef.mem_Icc {D : D7} {L : SizeData₂ D} {X : Inst D L} {K : Consts} (h : KapIDef X K) (p n' : ℕ)
    (TT : Finset (Fin n')) (a b : Fin n' → ℤ) : 0 ≤ X.kapI p n' TT a b ∧ X.kapI p n' TT a b ≤ 1 :=
  ⟨by rw [h]; exact le_csInf ⟨1, one_mem_kapISet L K p n' TT a b⟩ (fun x hx => hx.1),
   h.le (one_mem_kapISet L K p n' TT a b)⟩

/- English proof (translation)
Use `set S := kapISet L K p n' TT a b with hS`. Establish `hne : S.Nonempty` using `⟨1, one_mem_kapISet L K p n' TT a b⟩`. Establish `hbd : BddBelow S` using `⟨0, fun x hx => hx.1⟩`. Use `⟨le_csInf hne (fun x hx => hx.1), ?_⟩` and prove the remaining obligations. Introduce `W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hset lam0 hb hd`.

Use `⟨by omega, fun Λ hΛ => ?_⟩` and prove the remaining obligations. Use `set d : ℝ := (dimV Kf lam0 : ℝ) with hdd`. Establish `hd0 : 0 ≤ d` using `Nat.cast_nonneg _`. Use `set c : ℝ := (1 - sInf S) * d with hc`. Establish `hgap : (0 < c ∧ (⌈c⌉₊ : ℝ) - 1 < c) ∨ c ≤ 0`.

Distinguish the cases in `h0 : c ≤ 0`. Conclude with `Or.inr h0`. Use `left`. Use `Nat.ceil_lt_add_one (le_of_lt (not_le.1 h0))` as an intermediate fact. Conclude with `⟨not_le.1 h0, by linarith⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨κ, hκS, hκ⟩ : ∃ κ ∈ S, c ≤ 0 ∨ (⌈c⌉₊ : ℝ) - 1 < (1 - κ) * d := by`. Break down `hgap with ⟨hcpos, hg⟩ | hg` into its components or cases. Establish `hdpos : 0 < d`. Break down `hd0.lt_or_eq with h | h` into its components or cases. Conclude with `h`.

It suffices to derive a contradiction. Establish `hc0 : c = 0` using `by rw [hc, ← h]; ring`. Rewrite `hcpos` using `[hc0]`. Conclude with `lt_irrefl _ hcpos`. Establish `hε : 0 < (c - ((⌈c⌉₊ : ℝ) - 1)) / d` using `div_pos (by linarith) hdpos`.

Take `⟨κ, hκS, hκlt⟩` from `exists_lt_of_csInf_lt hne (lt_add_of_pos_right (sInf S) hε)`. Use `⟨κ, hκS, Or.inr ?_⟩` and prove the remaining obligations. Establish `h1 : (κ - sInf S) * d < c - ((⌈c⌉₊ : ℝ) - 1)`. Establish `: κ - sInf S < (c - ((⌈c⌉₊ : ℝ) - 1)) / d` using `by linarith`. Conclude with `(lt_div_iff₀ hdpos).1 this`.

Establish `h2 : (1 - κ) * d = c - (κ - sInf S) * d` using `by rw [hc]; ring`. Rewrite using `[h2]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `⟨1, one_mem_kapISet L K p n' TT a b, Or.inl hg⟩`. Take `⟨M, e, F, h1, h2, h3, n, hn, hG⟩` from `(hκS.2 W Qq O Kf ι σ j w hset lam0 hb hd).2 Λ hΛ`.

Use `⟨M, e, F, h1, h2, h3, n, ?_, hG⟩` and prove the remaining obligations. Break down `hκ with h0 | hlt` into its components or cases. Conclude with `le_trans h0 (Nat.cast_nonneg n)`. Establish `h4 : (⌈c⌉₊ : ℝ) - 1 < (n : ℝ)` using `lt_of_lt_of_le hlt hn`. Establish `h5 : ⌈c⌉₊ ≤ n`.

Establish `: (⌈c⌉₊ : ℝ) < (n : ℝ) + 1` using `by linarith`. Establish `: ⌈c⌉₊ < n + 1` using `by exact_mod_cast this`. Use linear arithmetic over natural numbers and integers. Conclude with `le_trans (Nat.le_ceil c) (by exact_mod_cast h5)`.
-/
theorem sInf_mem_kapISet {D : D7} (L : SizeData₂ D) (K : Consts) (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) :
    sInf (kapISet L K p n' TT a b) ∈ kapISet L K p n' TT a b := by
  set S := kapISet L K p n' TT a b with hS
  have hne : S.Nonempty := ⟨1, one_mem_kapISet L K p n' TT a b⟩
  have hbd : BddBelow S := ⟨0, fun x hx => hx.1⟩
  refine ⟨le_csInf hne (fun x hx => hx.1), ?_⟩
  intro W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hset lam0 hb hd
  refine ⟨by omega, fun Λ hΛ => ?_⟩
  set d : ℝ := (dimV Kf lam0 : ℝ) with hdd
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  set c : ℝ := (1 - sInf S) * d with hc

  have hgap : (0 < c ∧ (⌈c⌉₊ : ℝ) - 1 < c) ∨ c ≤ 0 := by
    by_cases h0 : c ≤ 0
    · exact Or.inr h0
    · left
      have := Nat.ceil_lt_add_one (le_of_lt (not_le.1 h0))
      exact ⟨not_le.1 h0, by linarith⟩
  obtain ⟨κ, hκS, hκ⟩ : ∃ κ ∈ S, c ≤ 0 ∨ (⌈c⌉₊ : ℝ) - 1 < (1 - κ) * d := by
    rcases hgap with ⟨hcpos, hg⟩ | hg
    ·
      have hdpos : 0 < d := by
        rcases hd0.lt_or_eq with h | h
        · exact h
        · exfalso
          have hc0 : c = 0 := by rw [hc, ← h]; ring
          rw [hc0] at hcpos
          exact lt_irrefl _ hcpos
      have hε : 0 < (c - ((⌈c⌉₊ : ℝ) - 1)) / d := div_pos (by linarith) hdpos
      obtain ⟨κ, hκS, hκlt⟩ := exists_lt_of_csInf_lt hne (lt_add_of_pos_right (sInf S) hε)
      refine ⟨κ, hκS, Or.inr ?_⟩
      have h1 : (κ - sInf S) * d < c - ((⌈c⌉₊ : ℝ) - 1) := by
        have : κ - sInf S < (c - ((⌈c⌉₊ : ℝ) - 1)) / d := by linarith
        exact (lt_div_iff₀ hdpos).1 this
      have h2 : (1 - κ) * d = c - (κ - sInf S) * d := by rw [hc]; ring
      rw [h2]; linarith
    · exact ⟨1, one_mem_kapISet L K p n' TT a b, Or.inl hg⟩
  obtain ⟨M, e, F, h1, h2, h3, n, hn, hG⟩ := (hκS.2 W Qq O Kf ι σ j w hset lam0 hb hd).2 Λ hΛ
  refine ⟨M, e, F, h1, h2, h3, n, ?_, hG⟩
  rcases hκ with h0 | hlt
  · exact le_trans h0 (Nat.cast_nonneg n)
  · have h4 : (⌈c⌉₊ : ℝ) - 1 < (n : ℝ) := lt_of_lt_of_le hlt hn
    have h5 : ⌈c⌉₊ ≤ n := by
      have : (⌈c⌉₊ : ℝ) < (n : ℝ) + 1 := by linarith
      have : ⌈c⌉₊ < n + 1 := by exact_mod_cast this
      omega
    exact le_trans (Nat.le_ceil c) (by exact_mod_cast h5)

/- English proof (translation)
Rewrite using `[h]`. Conclude with `sInf_mem_kapISet L K p n' TT a b`.
-/
theorem KapIDef.mem {D : D7} {L : SizeData₂ D} {X : Inst D L} {K : Consts} (h : KapIDef X K) (p n' : ℕ)
    (TT : Finset (Fin n')) (a b : Fin n' → ℤ) : X.kapI p n' TT a b ∈ kapISet L K p n' TT a b := by
  rw [h]; exact sInf_mem_kapISet L K p n' TT a b

/- English proof (translation)
Assemble the required witnesses or components as `⟨{ X with kapI := fun p n' TT a b => sInf (kapISet L K p n' TT a b), ep := fun p => ⌈Ce * (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a⌉₊ }, rfl, rfl, fun _ => rfl, fun _ _ _ _ _ => rfl⟩`.
-/
theorem exists_inst_defs {D : D7} {L : SizeData₂ D} (X : Inst D L) (K : Consts) (Ce : ℝ) :
    ∃ X' : Inst D L, X'.bs = X.bs ∧ X'.off = X.off ∧ EpDef X' Ce ∧ KapIDef X' K :=
  ⟨{ X with kapI := fun p n' TT a b => sInf (kapISet L K p n' TT a b),
            ep := fun p => ⌈Ce * (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a⌉₊ },
    rfl, rfl, fun _ => rfl, fun _ _ _ _ _ => rfl⟩

end Formalism.MainNotions.G

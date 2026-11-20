import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquiv

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

noncomputable section

namespace GlobalTheory.CompanionTheory.ReorderRev

section Comb

variable {α : Type*} {h : ℕ}

def invSet (σ : Equiv.Perm (Fin h)) : Finset (Fin h × Fin h) :=
  Finset.univ.filter fun uv => uv.1 < uv.2 ∧ σ.symm uv.2 < σ.symm uv.1

/- English proof (translation)
Simplify using `only [Equiv.swap_apply_def] at hxy`. Simplify using `only [Fin.lt_def, Fin.ext_iff] at hxy ⊢`. Apply the tactic sequence `split_ifs at hxy <;> omega`.
-/
theorem swap_lt_swap {i j x y : Fin h} (hij : (j : ℕ) = i + 1)
    (hxy : Equiv.swap i j x < Equiv.swap i j y) : x < y ∨ (x = j ∧ y = i) := by
  simp only [Equiv.swap_apply_def] at hxy
  simp only [Fin.lt_def, Fin.ext_iff] at hxy ⊢
  split_ifs at hxy <;> omega

/- English proof (translation)
Introduce `x y hxy`. Rewrite `hxy` using `[Fin.lt_def]`. Establish `key : ∀ (d : ℕ) (y : Fin h), (y : ℕ) = x + d + 1 → g x < g y`. Introduce `d`. Proceed by induction on `d with`.

Consider the case `zero => intro y hy; exact hg x y (by omega)`. Consider the case `succ d ih`. Introduce `y hy`. Establish `hy1 : (y : ℕ) - 1 < h` using `by omega`. Conclude with `(ih ⟨y - 1, hy1⟩ (show (y : ℕ) - 1 = x + d + 1 by omega)).trans (hg ⟨y - 1, hy1⟩ y (show (y : ℕ) = ((y : ℕ) - 1) + 1 by omega))`.

Conclude with `key (y - x - 1) y (by omega)`.
-/
theorem strictMono_of_adj {g : Fin h → Fin h} (hg : ∀ p q : Fin h, (q : ℕ) = p + 1 → g p < g q) :
    StrictMono g := by
  intro x y hxy
  rw [Fin.lt_def] at hxy
  have key : ∀ (d : ℕ) (y : Fin h), (y : ℕ) = x + d + 1 → g x < g y := by
    intro d
    induction d with
    | zero => intro y hy; exact hg x y (by omega)
    | succ d ih =>
      intro y hy
      have hy1 : (y : ℕ) - 1 < h := by omega
      exact (ih ⟨y - 1, hy1⟩ (show (y : ℕ) - 1 = x + d + 1 by omega)).trans
        (hg ⟨y - 1, hy1⟩ y (show (y : ℕ) = ((y : ℕ) - 1) + 1 by omega))
  exact key (y - x - 1) y (by omega)

/- English proof (translation)
Proceed by induction on `hn : (invSet σ).card using Nat.strong_induction_on generalizing σ with`. Consider the case `_ n ih`. Distinguish the cases in `hd : ∃ p q : Fin h, (q : ℕ) = p + 1 ∧ σ q < σ p`. Take `⟨p, q, hpq, hlt⟩` from `hd set σ' : Equiv.Perm (Fin h) := (Equiv.swap p q).trans σ with hσ'`. Establish `hs : ∀ x, σ'.symm x = Equiv.swap p q (σ.symm x)` using `fun x => by simp [σ']`.

Establish `hinv : ∀ u v, u < v → σ'.symm v < σ'.symm u → σ.symm v < σ.symm u`. Introduce `u v huv h'`. Rewrite `h'` using `[hs, hs]`. Break down `swap_lt_swap hpq h' with h'' | ⟨h1, h2⟩` into its components or cases. Conclude with `h''`.

It suffices to derive a contradiction. Establish `e1 : v = σ q` using `by rw [← h1]; simp`. Establish `e2 : u = σ p` using `by rw [← h2]; simp`. Rewrite `huv` using `[e1, e2]`. Conclude with `lt_asymm huv hlt`.

Establish `hsub : invSet σ' ⊂ invSet σ`. Rewrite using `[Finset.ssubset_iff_of_subset]`. Use `⟨(σ q, σ p), ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [invSet, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]`. Conclude with `⟨hlt, by rw [Fin.lt_def]; omega⟩`.

Simplify using `only [invSet, Finset.mem_filter, Finset.mem_univ, true_and, hs, Equiv.symm_apply_apply, Equiv.swap_apply_left, Equiv.swap_apply_right, not_and]`. Introduce `_`. Rewrite using `[Fin.lt_def]`. Use linear arithmetic over natural numbers and integers. Introduce `uv huv`.

Simplify using `only [invSet, Finset.mem_filter, Finset.mem_univ, true_and] at huv ⊢`. Conclude with `⟨huv.1, hinv _ _ huv.1 huv.2⟩`. Establish `h1 : r f (f ∘ σ')` using `ih _ (hn ▸ Finset.card_lt_card hsub) σ' (fun u v huv h' => hσ u v huv (hinv u v huv h')) rfl`. Establish `h2 : f ∘ σ = (f ∘ σ') ∘ Equiv.swap p q`. Use function extensionality and compare the values at `x`.

Simplify using `[σ']`. Rewrite using `[h2]`. Use `htrans _ _ _ h1 (hswap _ p q hpq ?_)` and prove the remaining obligations. Use `hσ (σ q) (σ p) hlt (by simp only [Equiv.symm_apply_apply]; rw [Fin.lt_def]; omega)` as an intermediate fact. Simplify `this` using `[σ']`.

Use `push_neg at hd`. Establish `hm : StrictMono σ` using `strictMono_of_adj fun p q hpq => lt_of_le_of_ne (hd p q hpq) (fun e => by have := σ.injective e; rw [Fin.ext_iff] at this; omega)`. Establish `he : σ = 1` using `Equiv.ext fun x => congrFun (StrictMono.eq_id hm) x`. Substitute `he` using the available equality. Simplify using `using hrefl f`.
-/
theorem rel_comp_perm (r : (Fin h → α) → (Fin h → α) → Prop) (hrefl : ∀ f, r f f)
    (htrans : ∀ f g l, r f g → r g l → r f l) (U : α → α → Prop)
    (hswap : ∀ (f : Fin h → α) (i j : Fin h), (j : ℕ) = i + 1 → U (f i) (f j) → r f (f ∘ Equiv.swap i j))
    (f : Fin h → α) (σ : Equiv.Perm (Fin h))
    (hσ : ∀ u v, u < v → σ.symm v < σ.symm u → U (f u) (f v)) : r f (f ∘ σ) := by
  induction hn : (invSet σ).card using Nat.strong_induction_on generalizing σ with
  | _ n ih =>
  by_cases hd : ∃ p q : Fin h, (q : ℕ) = p + 1 ∧ σ q < σ p
  · obtain ⟨p, q, hpq, hlt⟩ := hd
    set σ' : Equiv.Perm (Fin h) := (Equiv.swap p q).trans σ with hσ'
    have hs : ∀ x, σ'.symm x = Equiv.swap p q (σ.symm x) := fun x => by simp [σ']
    have hinv : ∀ u v, u < v → σ'.symm v < σ'.symm u → σ.symm v < σ.symm u := by
      intro u v huv h'
      rw [hs, hs] at h'
      rcases swap_lt_swap hpq h' with h'' | ⟨h1, h2⟩
      · exact h''
      · exfalso
        have e1 : v = σ q := by rw [← h1]; simp
        have e2 : u = σ p := by rw [← h2]; simp
        rw [e1, e2] at huv
        exact lt_asymm huv hlt
    have hsub : invSet σ' ⊂ invSet σ := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨(σ q, σ p), ?_, ?_⟩
        · simp only [invSet, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
          exact ⟨hlt, by rw [Fin.lt_def]; omega⟩
        · simp only [invSet, Finset.mem_filter, Finset.mem_univ, true_and, hs, Equiv.symm_apply_apply,
            Equiv.swap_apply_left, Equiv.swap_apply_right, not_and]
          intro _
          rw [Fin.lt_def]; omega
      · intro uv huv
        simp only [invSet, Finset.mem_filter, Finset.mem_univ, true_and] at huv ⊢
        exact ⟨huv.1, hinv _ _ huv.1 huv.2⟩
    have h1 : r f (f ∘ σ') := ih _ (hn ▸ Finset.card_lt_card hsub) σ'
      (fun u v huv h' => hσ u v huv (hinv u v huv h')) rfl
    have h2 : f ∘ σ = (f ∘ σ') ∘ Equiv.swap p q := by
      funext x
      simp [σ']
    rw [h2]
    refine htrans _ _ _ h1 (hswap _ p q hpq ?_)
    have := hσ (σ q) (σ p) hlt (by simp only [Equiv.symm_apply_apply]; rw [Fin.lt_def]; omega)
    simpa [σ'] using this
  · push_neg at hd
    have hm : StrictMono σ := strictMono_of_adj fun p q hpq => lt_of_le_of_ne (hd p q hpq)
      (fun e => by have := σ.injective e; rw [Fin.ext_iff] at this; omega)
    have he : σ = 1 := Equiv.ext fun x => congrFun (StrictMono.eq_id hm) x
    subst he
    simpa using hrefl f

/- English proof (translation)
Establish `hi : i = Fin.natAdd p (Fin.castAdd s (0 : Fin 2))` using `Fin.ext (by simp [hp])`. Establish `hj : j = Fin.natAdd p (Fin.castAdd s (1 : Fin 2))` using `Fin.ext (by simp [hp, hij])`. Prove the components needed by the constructor for the conclusion. Use function extensionality and compare the values at `x`. Proceed by induction on `x using Fin.addCases with`.

Consider the case `left t => simp`. Consider the case `right t`. Rewrite using `[Fin.append_right]`. Proceed by induction on `t using Fin.addCases with`. Consider the case `left u`.

Rewrite using `[Fin.append_left]`. Use `fin_cases u`. Simplify using `[hi]`. Simplify using `[hj]`. Consider the case `right u => simp`.

Use function extensionality and compare the values at `x`. Proceed by induction on `x using Fin.addCases with`. Consider the case `left t`. Rewrite using `[Fin.append_left, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne]`. Conclude with `Fin.ne_of_val_ne (by simp; omega)`.

Conclude with `Fin.ne_of_val_ne (by simp; omega)`. Consider the case `right t`. Rewrite using `[Fin.append_right]`. Proceed by induction on `t using Fin.addCases with`. Consider the case `left u`.

Rewrite using `[Fin.append_left]`. Use `fin_cases u`. Simplify using `[hi, hj]`. Simplify using `[hi, hj]`. Consider the case `right u`.

Rewrite using `[Fin.append_right, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne]`. Conclude with `Fin.ne_of_val_ne (by simp; omega)`. Conclude with `Fin.ne_of_val_ne (by simp; omega)`.
-/
theorem append_decomp {p s : ℕ} (y : Fin (p + (2 + s)) → α) (i j : Fin (p + (2 + s))) (hp : (i : ℕ) = p)
    (hij : (j : ℕ) = i + 1) :
    y = Fin.append (fun t : Fin p => y (Fin.castAdd (2 + s) t))
      (Fin.append ![y i, y j] fun t : Fin s => y (Fin.natAdd p (Fin.natAdd 2 t))) ∧
    y ∘ Equiv.swap i j = Fin.append (fun t : Fin p => y (Fin.castAdd (2 + s) t))
      (Fin.append ![y j, y i] fun t : Fin s => y (Fin.natAdd p (Fin.natAdd 2 t))) := by
  have hi : i = Fin.natAdd p (Fin.castAdd s (0 : Fin 2)) := Fin.ext (by simp [hp])
  have hj : j = Fin.natAdd p (Fin.castAdd s (1 : Fin 2)) := Fin.ext (by simp [hp, hij])
  constructor
  · funext x
    induction x using Fin.addCases with
    | left t => simp
    | right t =>
      rw [Fin.append_right]
      induction t using Fin.addCases with
      | left u =>
        rw [Fin.append_left]
        fin_cases u
        · simp [hi]
        · simp [hj]
      | right u => simp
  · funext x
    induction x using Fin.addCases with
    | left t =>
      rw [Fin.append_left, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne]
      · exact Fin.ne_of_val_ne (by simp; omega)
      · exact Fin.ne_of_val_ne (by simp; omega)
    | right t =>
      rw [Fin.append_right]
      induction t using Fin.addCases with
      | left u =>
        rw [Fin.append_left]
        fin_cases u
        · simp [hi, hj]
        · simp [hi, hj]
      | right u =>
        rw [Fin.append_right, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne]
        · exact Fin.ne_of_val_ne (by simp; omega)
        · exact Fin.ne_of_val_ne (by simp; omega)

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, _, append_decomp y i j hp hij⟩`.
-/
theorem exists_append_decomp {p s : ℕ} (y : Fin (p + (2 + s)) → α) (i j : Fin (p + (2 + s)))
    (hp : (i : ℕ) = p) (hij : (j : ℕ) = i + 1) :
    ∃ (P : Fin p → α) (S : Fin s → α), y = Fin.append P (Fin.append ![y i, y j] S) ∧
      y ∘ Equiv.swap i j = Fin.append P (Fin.append ![y j, y i] S) :=
  ⟨_, _, append_decomp y i j hp hij⟩

end Comb

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `⟨.refl _⟩`.
-/
theorem prodIrr_congr {h N : ℕ} {x x' : Fin h → IrrGL k} (e : x = x') (hd : ∑ a, (x a).1 = N)
    (hd' : ∑ a, (x' a).1 = N) : Nonempty ((prodIrr x hd).Equiv (prodIrr x' hd')) := by
  subst e
  exact ⟨.refl _⟩

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hy : ∑ i, (Fin.append Q S i).1 = q + u`. Rewrite using `[Fin.sum_univ_add]`. Simplify using `only [Fin.append_left, Fin.append_right, hq, hu]`. Establish `hy' : ∑ i, (Fin.append Q' S i).1 = q + u`. Rewrite using `[Fin.sum_univ_add]`.

Simplify using `only [Fin.append_left, Fin.append_right, hq', hu]`. Take `⟨E₁⟩` from `GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append k _ _ _ _ P (Fin.append Q S) hr hy h₁`. Take `⟨E₂⟩` from `GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append k _ _ _ _ P (Fin.append Q' S) hr hy' h₂`. Take `⟨F₁⟩` from `GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append k _ _ _ _ Q S hq hu hy`. Take `⟨F₂⟩` from `GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append k _ _ _ _ Q' S hq' hu hy'`.

Take `⟨G⟩` from `C`. Conclude with `⟨E₁.symm.trans ((prod₂Equiv (.refl _) (F₁.symm.trans ((prod₂Equiv G (.refl _)).trans F₂))).trans E₂)⟩`.
-/
theorem prodIrr_append_middle {p m m' s r q u : ℕ} (P : Fin p → IrrGL k) (Q : Fin m → IrrGL k)
    (Q' : Fin m' → IrrGL k) (S : Fin s → IrrGL k) (hr : ∑ i, (P i).1 = r) (hq : ∑ i, (Q i).1 = q)
    (hq' : ∑ i, (Q' i).1 = q) (hu : ∑ i, (S i).1 = u)
    (C : Nonempty ((prodIrr Q hq).Equiv (prodIrr Q' hq')))
    (h₁ : ∑ i, (Fin.append P (Fin.append Q S) i).1 = r + (q + u))
    (h₂ : ∑ i, (Fin.append P (Fin.append Q' S) i).1 = r + (q + u)) :
    Nonempty ((prodIrr (Fin.append P (Fin.append Q S)) h₁).Equiv
      (prodIrr (Fin.append P (Fin.append Q' S)) h₂)) := by
  have hy : ∑ i, (Fin.append Q S i).1 = q + u := by
    rw [Fin.sum_univ_add]; simp only [Fin.append_left, Fin.append_right, hq, hu]
  have hy' : ∑ i, (Fin.append Q' S i).1 = q + u := by
    rw [Fin.sum_univ_add]; simp only [Fin.append_left, Fin.append_right, hq', hu]
  obtain ⟨E₁⟩ := GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append k _ _ _ _ P (Fin.append Q S) hr hy h₁
  obtain ⟨E₂⟩ := GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append k _ _ _ _ P (Fin.append Q' S) hr hy' h₂
  obtain ⟨F₁⟩ := GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append k _ _ _ _ Q S hq hu hy
  obtain ⟨F₂⟩ := GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append k _ _ _ _ Q' S hq' hu hy'
  obtain ⟨G⟩ := C
  exact ⟨E₁.symm.trans ((prod₂Equiv (.refl _) (F₁.symm.trans ((prod₂Equiv G (.refl _)).trans F₂))).trans E₂)⟩

set_option maxHeartbeats 400000 in

/- English proof (translation)
Establish `hex : ∃ p s, h = p + (2 + s) ∧ (i : ℕ) = p` using `⟨i, h - i - 2, by have := j.isLt; omega, rfl⟩`. Take `⟨p, s, hh, hp⟩` from `hex`. Substitute `hh` using the available equality. Establish `hdec` using `exists_append_decomp y i j hp hij`. Take `⟨P, S, ey, ey'⟩` from `hdec`.

Establish `hr0 : ∃ r, ∑ t, (P t).1 = r` using `⟨_, rfl⟩`. Establish `hq0 : ∃ q, ∑ t, (![y i, y j] t).1 = q` using `⟨_, rfl⟩`. Establish `hu0 : ∃ u, ∑ t, (S t).1 = u` using `⟨_, rfl⟩`. Take `⟨r, hr⟩` from `hr0`. Take `⟨q, hq⟩` from `hq0`.

Take `⟨u, hu⟩` from `hu0`. Establish `hq' : ∑ t, (![y j, y i] t).1 = q`. Rewrite using `[← hq]`. Apply the tactic sequence `simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> omega`. Establish `h₁ : ∑ a, (Fin.append P (Fin.append ![y i, y j] S) a).1 = r + (q + u)`.

Rewrite using `[Fin.sum_univ_add, Fin.sum_univ_add]`. Simplify using `only [Fin.append_left, Fin.append_right, hr, hq, hu]`. Establish `h₂ : ∑ a, (Fin.append P (Fin.append ![y j, y i] S) a).1 = r + (q + u)`. Rewrite using `[Fin.sum_univ_add, Fin.sum_univ_add]`. Simplify using `only [Fin.append_left, Fin.append_right, hr, hq', hu]`.

Establish `hN : N = r + (q + u)`. Rewrite using `[← hd, ← h₁, ← ey]`. Substitute `hN` using the available equality. Establish `A` using `prodIrr_congr ey hd h₁`. Establish `B` using `prodIrr_append_middle P _ _ S hr hq hq' hu (C q hq hq') h₁ h₂`.

Establish `D` using `prodIrr_congr ey'.symm h₂ hd'`. Conclude with `A.elim fun A => B.elim fun B => D.elim fun D => ⟨A.trans (B.trans D)⟩`.
-/
theorem prodIrr_swap_adj {h N : ℕ} (y : Fin h → IrrGL k) (i j : Fin h) (hij : (j : ℕ) = i + 1)
    (C : ∀ (q : ℕ) (hq : ∑ t, (![y i, y j] t).1 = q) (hq' : ∑ t, (![y j, y i] t).1 = q),
      Nonempty ((prodIrr ![y i, y j] hq).Equiv (prodIrr ![y j, y i] hq')))
    (hd : ∑ a, (y a).1 = N) (hd' : ∑ a, ((y ∘ Equiv.swap i j) a).1 = N) :
    Nonempty ((prodIrr y hd).Equiv (prodIrr (y ∘ Equiv.swap i j) hd')) := by
  have hex : ∃ p s, h = p + (2 + s) ∧ (i : ℕ) = p := ⟨i, h - i - 2, by have := j.isLt; omega, rfl⟩
  obtain ⟨p, s, hh, hp⟩ := hex
  subst hh
  have hdec := exists_append_decomp y i j hp hij
  obtain ⟨P, S, ey, ey'⟩ := hdec
  have hr0 : ∃ r, ∑ t, (P t).1 = r := ⟨_, rfl⟩
  have hq0 : ∃ q, ∑ t, (![y i, y j] t).1 = q := ⟨_, rfl⟩
  have hu0 : ∃ u, ∑ t, (S t).1 = u := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ := hr0
  obtain ⟨q, hq⟩ := hq0
  obtain ⟨u, hu⟩ := hu0
  have hq' : ∑ t, (![y j, y i] t).1 = q := by
    rw [← hq]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> omega
  have h₁ : ∑ a, (Fin.append P (Fin.append ![y i, y j] S) a).1 = r + (q + u) := by
    rw [Fin.sum_univ_add, Fin.sum_univ_add]; simp only [Fin.append_left, Fin.append_right, hr, hq, hu]
  have h₂ : ∑ a, (Fin.append P (Fin.append ![y j, y i] S) a).1 = r + (q + u) := by
    rw [Fin.sum_univ_add, Fin.sum_univ_add]; simp only [Fin.append_left, Fin.append_right, hr, hq', hu]
  have hN : N = r + (q + u) := by
    rw [← hd, ← h₁, ← ey]
  subst hN
  have A := prodIrr_congr ey hd h₁
  have B := prodIrr_append_middle P _ _ S hr hq hq' hu (C q hq hq') h₁ h₂
  have D := prodIrr_congr ey'.symm h₂ hd'
  exact A.elim fun A => B.elim fun B => D.elim fun D => ⟨A.trans (B.trans D)⟩

end Rep

section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Take `⟨⟨Γ, hΓ⟩, h1, h2⟩` from `h`. Establish `hf : ∀ D : Segment k, D.first ∈ D.carrier` using `fun D => Segment.mem_carrier.2 ⟨0, D.len_pos, by simp⟩`. Take `⟨a, -, ha⟩` from `Segment.mem_carrier.1 (show Δ.first ∈ Γ.carrier by rw [hΓ]; exact Or.inl (hf Δ))`. Take `⟨b, -, hb⟩` from `Segment.mem_carrier.1 (show Δ'.first ∈ Γ.carrier by rw [hΓ]; exact Or.inr (hf Δ'))`. Break down `lt_trichotomy a b with hab | rfl | hab` into its components or cases.

Use `left`. Use `⟨⟨⟨Γ, hΓ⟩, h1, h2⟩, b - a, by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[← hb, ← ha, IrrGL.nu_nu]`. Use `congr 1`. Move the coercions through the operations in `[Nat.cast_sub hab.le]`.

Expand and normalize the polynomial expressions, which then agree. It suffices to derive a contradiction. Establish `hff : Δ.first = Δ'.first` using `ha.symm.trans hb`. Break down `le_total Δ.len Δ'.len with hl | hl` into its components or cases. Use `h1 fun x hx => ?_` and prove the remaining obligations.

Take `⟨c, hc, rfl⟩` from `Segment.mem_carrier.1 hx`. Conclude with `Segment.mem_carrier.2 ⟨c, by omega, by rw [hff]⟩`. Use `h2 fun x hx => ?_` and prove the remaining obligations. Take `⟨c, hc, rfl⟩` from `Segment.mem_carrier.1 hx`. Conclude with `Segment.mem_carrier.2 ⟨c, by omega, by rw [hff]⟩`.

Use `right`. Use `⟨⟨⟨Γ, by rw [Set.union_comm]; exact hΓ⟩, h2, h1⟩, a - b, by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[← ha, ← hb, IrrGL.nu_nu]`. Use `congr 1`. Move the coercions through the operations in `[Nat.cast_sub hab.le]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem precedes_or_of_linked {Δ Δ' : Segment k} (h : Δ.Linked Δ') : Δ.Precedes Δ' ∨ Δ'.Precedes Δ := by
  obtain ⟨⟨Γ, hΓ⟩, h1, h2⟩ := h
  have hf : ∀ D : Segment k, D.first ∈ D.carrier := fun D => Segment.mem_carrier.2 ⟨0, D.len_pos, by simp⟩
  obtain ⟨a, -, ha⟩ := Segment.mem_carrier.1 (show Δ.first ∈ Γ.carrier by rw [hΓ]; exact Or.inl (hf Δ))
  obtain ⟨b, -, hb⟩ := Segment.mem_carrier.1 (show Δ'.first ∈ Γ.carrier by rw [hΓ]; exact Or.inr (hf Δ'))
  rcases lt_trichotomy a b with hab | rfl | hab
  · left
    refine ⟨⟨⟨Γ, hΓ⟩, h1, h2⟩, b - a, by omega, ?_⟩
    rw [← hb, ← ha, IrrGL.nu_nu]
    congr 1
    push_cast [Nat.cast_sub hab.le]
    ring
  · exfalso
    have hff : Δ.first = Δ'.first := ha.symm.trans hb
    rcases le_total Δ.len Δ'.len with hl | hl
    · refine h1 fun x hx => ?_
      obtain ⟨c, hc, rfl⟩ := Segment.mem_carrier.1 hx
      exact Segment.mem_carrier.2 ⟨c, by omega, by rw [hff]⟩
    · refine h2 fun x hx => ?_
      obtain ⟨c, hc, rfl⟩ := Segment.mem_carrier.1 hx
      exact Segment.mem_carrier.2 ⟨c, by omega, by rw [hff]⟩
  · right
    refine ⟨⟨⟨Γ, by rw [Set.union_comm]; exact hΓ⟩, h2, h1⟩, a - b, by omega, ?_⟩
    rw [← ha, ← hb, IrrGL.nu_nu]
    congr 1
    push_cast [Nat.cast_sub hab.le]
    ring

/- English proof (translation)
Introduce `k _ _ _ _ _ hc h N Γ σ y hd hd' hΓ hΓσ hL`. Set `f : Fin h → Segment k × IrrGL k` to `fun a => (Γ a, y a)`. Set `r : (Fin h → Segment k × IrrGL k) → (Fin h → Segment k × IrrGL k) → Prop` to `fun g g' => (∑ a, (g a).2.1 = ∑ a, (g' a).2.1) ∧ ∀ (M : ℕ) (h₁ : ∑ a, (g a).2.1 = M) (h₂ : ∑ a, (g' a).2.1 = M), Nonempty ((prodIrr (fun a => (g a).2) h₁).Equiv (prodIrr (fun a => (g' a).2) h₂))`. Set `U : Segment k × IrrGL k → Segment k × IrrGL k → Prop` to `fun u v => ¬ u.1.Linked v.1 ∧ IsLSeg u.1 u.2.rep ∧ IsLSeg v.1 v.2.rep`. Establish `hrefl : ∀ g, r g g` using `fun g => ⟨rfl, fun M h₁ h₂ => ⟨.refl _⟩⟩`.

Establish `htrans : ∀ g g' g'', r g g' → r g' g'' → r g g''`. Introduce and unpack `g g' g'' ⟨s₁, e₁⟩ ⟨s₂, e₂⟩`. Use `⟨s₁.trans s₂, fun M h₁ h₃ => ?_⟩` and prove the remaining obligations. Establish `A` using `e₁ M h₁ (s₁.symm.trans h₁)`. Establish `B` using `e₂ M (s₁.symm.trans h₁) h₃`.

Conclude with `A.elim fun A => B.elim fun B => ⟨A.trans B⟩`. Establish `hswap : ∀ (g : Fin h → Segment k × IrrGL k) (i j : Fin h), (j : ℕ) = i + 1 → U (g i) (g j) → r g (g ∘ Equiv.swap i j)`. Introduce and unpack `g i j hij ⟨hl, hi, hj⟩`. Use `⟨(Equiv.sum_comp (Equiv.swap i j) fun a => (g a).2.1).symm, fun M h₁ h₂ => ?_⟩` and prove the remaining obligations. Conclude with `prodIrr_swap_adj (fun a => (g a).2) i j hij (fun q hq hq' => hc (g i).1 (g j).1 (g i).2 (g j).2 q hq hq' hl hi hj) h₁ h₂`.

Establish `hinv : ∀ u v, u < v → σ.symm v < σ.symm u → U (f u) (f v)`. Introduce `u v huv hvu`. Use `⟨fun hlk => ?_, hL u, hL v⟩` and prove the remaining obligations. Break down `precedes_or_of_linked hlk with hp | hp` into its components or cases. Use `hΓσ _ _ hvu` as an intermediate fact.

Simplify using `only [Function.comp_apply, Equiv.apply_symm_apply] at this`. Conclude with `this hp`. Conclude with `hΓ u v huv hp`. Conclude with `(rel_comp_perm r hrefl htrans U hswap f σ hinv).2 N hd hd'`.
-/
theorem prodIrr_equiv_of_isRevOrdered : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LUnlinkedComm k →
    ∀ {h N : ℕ} (Γ : Fin h → Segment k) (σ : Equiv.Perm (Fin h)) (y : Fin h → IrrGL k)
      (hd : ∑ a, (y a).1 = N) (hd' : ∑ a, (y (σ a)).1 = N), IsRevOrdered Γ → IsRevOrdered (Γ ∘ σ) →
      (∀ i, IsLSeg (Γ i) (y i).rep) → Nonempty ((prodIrr y hd).Equiv (prodIrr (y ∘ σ) hd')) := by
  intro k _ _ _ _ _ hc h N Γ σ y hd hd' hΓ hΓσ hL
  let f : Fin h → Segment k × IrrGL k := fun a => (Γ a, y a)
  let r : (Fin h → Segment k × IrrGL k) → (Fin h → Segment k × IrrGL k) → Prop := fun g g' =>
    (∑ a, (g a).2.1 = ∑ a, (g' a).2.1) ∧ ∀ (M : ℕ) (h₁ : ∑ a, (g a).2.1 = M) (h₂ : ∑ a, (g' a).2.1 = M),
      Nonempty ((prodIrr (fun a => (g a).2) h₁).Equiv (prodIrr (fun a => (g' a).2) h₂))
  let U : Segment k × IrrGL k → Segment k × IrrGL k → Prop := fun u v =>
    ¬ u.1.Linked v.1 ∧ IsLSeg u.1 u.2.rep ∧ IsLSeg v.1 v.2.rep
  have hrefl : ∀ g, r g g := fun g => ⟨rfl, fun M h₁ h₂ => ⟨.refl _⟩⟩
  have htrans : ∀ g g' g'', r g g' → r g' g'' → r g g'' := by
    rintro g g' g'' ⟨s₁, e₁⟩ ⟨s₂, e₂⟩
    refine ⟨s₁.trans s₂, fun M h₁ h₃ => ?_⟩
    have A := e₁ M h₁ (s₁.symm.trans h₁)
    have B := e₂ M (s₁.symm.trans h₁) h₃
    exact A.elim fun A => B.elim fun B => ⟨A.trans B⟩
  have hswap : ∀ (g : Fin h → Segment k × IrrGL k) (i j : Fin h), (j : ℕ) = i + 1 → U (g i) (g j) →
      r g (g ∘ Equiv.swap i j) := by
    rintro g i j hij ⟨hl, hi, hj⟩
    refine ⟨(Equiv.sum_comp (Equiv.swap i j) fun a => (g a).2.1).symm, fun M h₁ h₂ => ?_⟩
    exact prodIrr_swap_adj (fun a => (g a).2) i j hij
      (fun q hq hq' => hc (g i).1 (g j).1 (g i).2 (g j).2 q hq hq' hl hi hj) h₁ h₂
  have hinv : ∀ u v, u < v → σ.symm v < σ.symm u → U (f u) (f v) := by
    intro u v huv hvu
    refine ⟨fun hlk => ?_, hL u, hL v⟩
    rcases precedes_or_of_linked hlk with hp | hp
    · have := hΓσ _ _ hvu
      simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
      exact this hp
    · exact hΓ u v huv hp
  exact (rel_comp_perm r hrefl htrans U hswap f σ hinv).2 N hd hd'

end Main

end GlobalTheory.CompanionTheory.ReorderRev

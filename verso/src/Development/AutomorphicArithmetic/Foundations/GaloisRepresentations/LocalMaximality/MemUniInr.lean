import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private def phiT {d : ℕ} : Fin (d + 1) ⊕ₗ Fin d → Fin (d + 1) := fun t => Sum.elim id Fin.succ (ofLex t)

private def cT {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E) :
    Fin (d + 1) ⊕ₗ Fin d → S :=
  app (fun _ => 1) (fun l : Fin d => (T.X l.succ : S))

/- English proof (translation)
Apply the tactic sequence `rcases t with i | l <;> rfl`.
-/
private lemma rowT_eq {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)
    (t : Fin (d + 1) ⊕ₗ Fin d) : T.rowT t = Pi.single (phiT t) (cT T t) := by
  rcases t with i | l <;> rfl

/- English proof (translation)
Rewrite using `[← Matrix.det_transpose, Matrix.det_apply]`. Simplify using `only [Matrix.transpose_apply, Matrix.of_apply, Pi.single_apply]`. Rewrite using `[Finset.sum_congr rfl fun σ _ => by rw [Fintype.prod_ite_zero]]`. Distinguish the cases in `hg : Function.Bijective g`. Use `right`.

Use `⟨hg, Equiv.Perm.sign (Equiv.ofBijective g hg), ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single (Equiv.ofBijective g hg)]`. Rewrite using `[if_pos (show ∀ i, (Equiv.ofBijective g hg) i = g i from fun i => rfl)]`. Introduce `σ _ hσ`. Rewrite using `[if_neg, smul_zero]`.

Introduce `h`. Conclude with `hσ (Equiv.ext fun i => h i)`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Use `left`.

Use `Finset.sum_eq_zero fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg, smul_zero]`. Introduce `h`. Establish `hgσ : g = σ` using `funext fun i => (h i).symm`. Conclude with `hg (hgσ ▸ σ.bijective)`.
-/
private lemma det_single {S : Type} [CommRing S] {n : ℕ} (g : Fin n → Fin n) (v : Fin n → S) :
    (Matrix.of fun a b => (Pi.single (g a) (v a) : Fin n → S) b).det = 0 ∨
      (Function.Bijective g ∧ ∃ ε : ℤˣ,
        (Matrix.of fun a b => (Pi.single (g a) (v a) : Fin n → S) b).det = ε • ∏ a, v a) := by
  classical
  rw [← Matrix.det_transpose, Matrix.det_apply]
  simp only [Matrix.transpose_apply, Matrix.of_apply, Pi.single_apply]
  rw [Finset.sum_congr rfl fun σ _ => by rw [Fintype.prod_ite_zero]]
  by_cases hg : Function.Bijective g
  · right
    refine ⟨hg, Equiv.Perm.sign (Equiv.ofBijective g hg), ?_⟩
    rw [Finset.sum_eq_single (Equiv.ofBijective g hg)]
    · rw [if_pos (show ∀ i, (Equiv.ofBijective g hg) i = g i from fun i => rfl)]
    · intro σ _ hσ
      rw [if_neg, smul_zero]
      intro h
      exact hσ (Equiv.ext fun i => h i)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · left
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [if_neg, smul_zero]
    intro h
    have hgσ : g = σ := funext fun i => (h i).symm
    exact hg (hgσ ▸ σ.bijective)

/- English proof (translation)
Simplify using `only [detC, dif_pos h, rowT_eq]`.
-/
private lemma detC_eq {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)
    (s : Finset (Fin (d + 1) ⊕ₗ Fin d)) (h : s.card = d + 1) :
    detC T.rowT s = (Matrix.of fun a b => (Pi.single (phiT (s.orderEmbOfFin h a)) (cT T (s.orderEmbOfFin h a)) :
      Fin (d + 1) → S) b).det := by
  simp only [detC, dif_pos h, rowT_eq]

/- English proof (translation)
Establish `hf' : ∀ a, s.orderEmbOfFin h a = f a` using `fun a => (congrFun (Finset.orderEmbOfFin_unique h hfs hf) a).symm`. Rewrite using `[detC_eq T s h]`. Simplify using `only [hf', hφ]`. Rewrite using `[show (Matrix.of fun a b => (Pi.single a (cT T (f a)) : Fin (d + 1) → S) b) = Matrix.diagonal (fun a => cT T (f a)) from ?_]`. Conclude with `Matrix.det_diagonal`.

Use extensionality with `a b`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.diagonal_apply_ne _ hab, Pi.single_apply, Ne.symm hab]`.
-/
private lemma detC_id {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)
    (s : Finset (Fin (d + 1) ⊕ₗ Fin d)) (h : s.card = d + 1) (f : Fin (d + 1) → Fin (d + 1) ⊕ₗ Fin d)
    (hfs : ∀ a, f a ∈ s) (hf : StrictMono f) (hφ : ∀ a, phiT (f a) = a) :
    detC T.rowT s = ∏ a, cT T (f a) := by
  have hf' : ∀ a, s.orderEmbOfFin h a = f a := fun a =>
    (congrFun (Finset.orderEmbOfFin_unique h hfs hf) a).symm
  rw [detC_eq T s h]
  simp only [hf', hφ]
  rw [show (Matrix.of fun a b => (Pi.single a (cT T (f a)) : Fin (d + 1) → S) b) =
      Matrix.diagonal (fun a => cT T (f a)) from ?_]
  · exact Matrix.det_diagonal
  · ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · simp [Matrix.diagonal_apply_ne _ hab, Pi.single_apply, Ne.symm hab]

/- English proof (translation)
Simplify using `[uni]`.
-/
private lemma mem_uni_inl {d : ℕ} (I : Finset (Fin (d + 1))) (L : Finset (Fin d)) (i : Fin (d + 1)) :
    toLex (Sum.inl i) ∈ uni I L ↔ i ∈ I := by
  simp [uni]

/- English proof (translation)
Simplify using `[uni]`.
-/
private lemma mem_uni_inr {d : ℕ} (I : Finset (Fin (d + 1))) (L : Finset (Fin d)) (l : Fin d) :
    toLex (Sum.inr l) ∈ uni I L ↔ l ∈ L := by
  simp [uni]

/- English proof (translation)
Simplify using `[uni]`.
-/
private lemma card_uni' {d : ℕ} (I : Finset (Fin (d + 1))) (L : Finset (Fin d)) :
    (uni I L).card = I.card + L.card := by
  simp [uni]

/- English proof (translation)
Rewrite using `[uni, Finset.prod_map, Finset.prod_disjSum]`. Both sides reduce to the same expression.
-/
private lemma prod_uni' {d : ℕ} {S : Type} [CommMonoid S] (I : Finset (Fin (d + 1))) (L : Finset (Fin d))
    (c : Fin (d + 1) ⊕ₗ Fin d → S) :
    ∏ t ∈ uni I L, c t = (∏ i ∈ I, c (toLex (Sum.inl i))) * ∏ l ∈ L, c (toLex (Sum.inr l)) := by
  rw [uni, Finset.prod_map, Finset.prod_disjSum]
  rfl

/- English proof (translation)
Use `conv_rhs => rw [← Finset.map_orderEmbOfFin_univ s h]`. Rewrite using `[Finset.prod_map]`. Both sides reduce to the same expression.
-/
private lemma prod_emb {α M : Type} [LinearOrder α] [CommMonoid M] (s : Finset α) {k : ℕ} (h : s.card = k) (c : α → M) :
    ∏ a, c (s.orderEmbOfFin h a) = ∏ t ∈ s, c t := by
  conv_rhs => rw [← Finset.map_orderEmbOfFin_univ s h]
  rw [Finset.prod_map]
  rfl

/- English proof (translation)
Establish `key` using `hD S S (Algebra.lmul ℂ S) (Fin (d + 1) ⊕ₗ Fin d) (d + 1) T.rowT (fun _ => 1) 1`. Establish `h1 : (fun l => Algebra.lmul ℂ S (∑ b, T.rowT l b * 1)) = fun t => Algebra.lmul ℂ S (app (fun _ => (1 : S)) (fun l : Fin d => (T.X l.succ : S)) t)`. Use function extensionality and compare the values at `t`. Rewrite using `[show (∑ b, T.rowT t b * 1) = cT T t by simp [rowT_eq]]`. Both sides reduce to the same expression.

Establish `h2 : (fun s => Algebra.lmul ℂ S (detC T.rowT s) 1) = detC T.rowT`. Use function extensionality and compare the values at `s`. Simplify using the standard rewrite rules. Rewrite `key` using `[h1, h2]`. Conclude with `key`.
-/
private theorem wd_lmul_app_detC_eq_zero_of_det (hD : Det) {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E]
    [Module ℂ E] (T : Sys d S E) :
    (wd fun t => (Algebra.lmul ℂ S) (app (fun _ => (1 : S)) (fun l : Fin d => (T.X l.succ : S)) t))
      (detC T.rowT) = 0 := by
  have key := hD S S (Algebra.lmul ℂ S) (Fin (d + 1) ⊕ₗ Fin d) (d + 1) T.rowT (fun _ => 1) 1
  have h1 : (fun l => Algebra.lmul ℂ S (∑ b, T.rowT l b * 1)) =
      fun t => Algebra.lmul ℂ S (app (fun _ => (1 : S)) (fun l : Fin d => (T.X l.succ : S)) t) := by
    funext t
    rw [show (∑ b, T.rowT t b * 1) = cT T t by simp [rowT_eq]]
    rfl
  have h2 : (fun s => Algebra.lmul ℂ S (detC T.rowT s) 1) = detC T.rowT := by
    funext s
    simp
  rw [h1, h2] at key
  exact key

/- English proof (translation)
Rewrite using `[detC_id T (uni Finset.univ ∅) (by simp [card_uni']) (fun a => toLex (Sum.inl a)) (fun a => (mem_uni_inl _ _ a).2 (Finset.mem_univ a)) Sum.Lex.inl_strictMono (fun a => rfl)]`. Simplify using `[cT, app]`.
-/
private theorem detC_uni_univ_empty {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) : detC T.rowT (uni Finset.univ ∅) = 1 := by
  rw [detC_id T (uni Finset.univ ∅) (by simp [card_uni']) (fun a => toLex (Sum.inl a))
    (fun a => (mem_uni_inl _ _ a).2 (Finset.mem_univ a)) Sum.Lex.inl_strictMono (fun a => rfl)]
  simp [cT, app]

/- English proof (translation)
Set `f : Fin (d + 1) → Fin (d + 1) ⊕ₗ Fin d` to `fun a => Fin.cases (motive := fun _ => Fin (d + 1) ⊕ₗ Fin d) (toLex (Sum.inl 0)) (fun l => toLex (Sum.inr l)) a`. Establish `hfs : ∀ a, f a ∈ uni {0} Finset.univ`. Introduce `a`. Consider the cases of `a using Fin.cases with`. Consider the case `zero => exact (mem_uni_inl _ _ 0).2 (Finset.mem_singleton_self 0)`.

Consider the case `succ l => exact (mem_uni_inr _ _ l).2 (Finset.mem_univ l)`. Establish `hf : StrictMono f`. Introduce `a b hab`. Consider the cases of `a using Fin.cases with`. Consider the case `zero`.

Consider the cases of `b using Fin.cases with`. Consider the case `zero => exact absurd hab (lt_irrefl _)`. Consider the case `succ l => exact Sum.Lex.inl_lt_inr _ _`. Consider the case `succ i`. Consider the cases of `b using Fin.cases with`.

Consider the case `zero => exact absurd hab (Fin.not_lt_zero _)`. Consider the case `succ l => exact Sum.Lex.inr_strictMono (Fin.succ_lt_succ_iff.1 hab)`. Establish `hφ : ∀ a, phiT (f a) = a`. Introduce `a`. Apply the tactic sequence `cases a using Fin.cases <;> rfl`.

Establish `hcard : (uni ({0} : Finset (Fin (d + 1))) (Finset.univ : Finset (Fin d))).card = d + 1`. Rewrite using `[card_uni', Finset.card_singleton, Finset.card_univ, Fintype.card_fin, add_comm]`. Rewrite using `[detC_id T _ hcard f hfs hf hφ, Fin.prod_univ_succ]`. Simplify using `[f, cT, app]`.
-/
private theorem detC_uni_singleton_zero_univ {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) : detC T.rowT (uni {0} Finset.univ) = ∏ l : Fin d, (T.X l.succ : S) := by
  let f : Fin (d + 1) → Fin (d + 1) ⊕ₗ Fin d := fun a =>
    Fin.cases (motive := fun _ => Fin (d + 1) ⊕ₗ Fin d) (toLex (Sum.inl 0)) (fun l => toLex (Sum.inr l)) a
  have hfs : ∀ a, f a ∈ uni {0} Finset.univ := by
    intro a
    cases a using Fin.cases with
    | zero => exact (mem_uni_inl _ _ 0).2 (Finset.mem_singleton_self 0)
    | succ l => exact (mem_uni_inr _ _ l).2 (Finset.mem_univ l)
  have hf : StrictMono f := by
    intro a b hab
    cases a using Fin.cases with
    | zero =>
      cases b using Fin.cases with
      | zero => exact absurd hab (lt_irrefl _)
      | succ l => exact Sum.Lex.inl_lt_inr _ _
    | succ i =>
      cases b using Fin.cases with
      | zero => exact absurd hab (Fin.not_lt_zero _)
      | succ l => exact Sum.Lex.inr_strictMono (Fin.succ_lt_succ_iff.1 hab)
  have hφ : ∀ a, phiT (f a) = a := by
    intro a
    cases a using Fin.cases <;> rfl
  have hcard : (uni ({0} : Finset (Fin (d + 1))) (Finset.univ : Finset (Fin d))).card = d + 1 := by
    rw [card_uni', Finset.card_singleton, Finset.card_univ, Fintype.card_fin, add_comm]
  rw [detC_id T _ hcard f hfs hf hφ, Fin.prod_univ_succ]
  simp [f, cT, app]

/- English proof (translation)
Distinguish the cases in `hc : (uni I L).card = d + 1`. Use `swap`. Use `left`. Simplify using `only [detC, dif_neg hc]`. Break down `det_single (fun a => phiT ((uni I L).orderEmbOfFin hc a)) (fun a => cT T ((uni I L).orderEmbOfFin hc a)) with h0 | ⟨hbij, ε, hε⟩` into its components or cases.

Use `left`. Rewrite using `[detC_eq T _ hc]`. Conclude with `h0`. Use `right`. Establish `hdet` using `(detC_eq T _ hc).trans hε`.

Establish `hmem : ∀ t, t ∈ uni I L ↔ ∃ a, (uni I L).orderEmbOfFin hc a = t`. Introduce `t`. Rewrite using `[← Finset.mem_coe, ← Finset.range_orderEmbOfFin (uni I L) hc, Set.mem_range]`. Establish `h0I : 0 ∈ I`. Take `⟨a, ha⟩` from `hbij.2 0`.

Use `replace ha : phiT ((uni I L).orderEmbOfFin hc a) = 0 := ha`. Establish `hA : (uni I L).orderEmbOfFin hc a ∈ uni I L` using `Finset.orderEmbOfFin_mem _ hc a`. Generalize the expression as in `(uni I L).orderEmbOfFin hc a = t at ha hA`. Break down `t with i | l` into its components or cases. Express the relevant statement in the definitionally equal form `i = 0 at ha`.

Substitute `ha` using the available equality. Conclude with `(mem_uni_inl I L _).1 hA`. Conclude with `absurd ha (Fin.succ_ne_zero l)`. Establish `hcard : I.card + L.card = d + 1`. Rewrite using `[← card_uni']`.

Conclude with `hc`. Establish `hcompl : Iᶜ = L.map (Fin.succEmb d)`. Use extensionality with `m`. Simplify using `only [Finset.mem_compl, Finset.mem_map, Fin.coe_succEmb]`. Prove the components needed by the constructor for the conclusion.

Introduce `hm`. Take `⟨a, ha⟩` from `hbij.2 m`. Use `replace ha : phiT ((uni I L).orderEmbOfFin hc a) = m := ha`. Establish `hA : (uni I L).orderEmbOfFin hc a ∈ uni I L` using `Finset.orderEmbOfFin_mem _ hc a`. Generalize the expression as in `(uni I L).orderEmbOfFin hc a = t at ha hA`.

Break down `t with i | l` into its components or cases. Express the relevant statement in the definitionally equal form `i = m at ha`. Substitute `ha` using the available equality. Conclude with `absurd ((mem_uni_inl I L _).1 hA) hm`. Conclude with `⟨l, (mem_uni_inr I L l).1 hA, ha⟩`.

Introduce and unpack `⟨l, hl, rfl⟩ hI`. Take `⟨a, ha⟩` from `(hmem (toLex (Sum.inl l.succ))).1 ((mem_uni_inl I L _).2 hI)`. Take `⟨b, hb⟩` from `(hmem (toLex (Sum.inr l))).1 ((mem_uni_inr I L _).2 hl)`. Establish `hab : a = b` using `hbij.1 (by show phiT ((uni I L).orderEmbOfFin hc a) = phiT ((uni I L).orderEmbOfFin hc b)`. Rewrite using `[ha, hb]`.

Use the proof step `rfl)`. Rewrite `ha` using `[hab, hb]`. Conclude with `Sum.inl_ne_inr (toLex.injective ha.symm)`. Use `⟨h0I, hcard, ε, ?_⟩` and prove the remaining obligations. Rewrite using `[hdet, prod_emb (uni I L) hc (cT T), prod_uni', hcompl, Finset.prod_map]`.

Simplify using `[cT, app]`.
-/
private theorem detC_uni_eq_zero_or_eq_unit_smul_prod_compl {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) (I : Finset (Fin (d + 1))) (L : Finset (Fin d)) :
    detC T.rowT (uni I L) = 0 ∨
      0 ∈ I ∧ I.card + L.card = d + 1 ∧ ∃ ε : ℤˣ, detC T.rowT (uni I L) = ε • ∏ m ∈ Iᶜ, (T.X m : S) := by
  by_cases hc : (uni I L).card = d + 1
  swap
  · left
    simp only [detC, dif_neg hc]
  rcases det_single (fun a => phiT ((uni I L).orderEmbOfFin hc a))
      (fun a => cT T ((uni I L).orderEmbOfFin hc a)) with h0 | ⟨hbij, ε, hε⟩
  · left
    rw [detC_eq T _ hc]
    exact h0
  · right
    have hdet := (detC_eq T _ hc).trans hε
    have hmem : ∀ t, t ∈ uni I L ↔ ∃ a, (uni I L).orderEmbOfFin hc a = t := by
      intro t
      rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin (uni I L) hc, Set.mem_range]
    have h0I : 0 ∈ I := by
      obtain ⟨a, ha⟩ := hbij.2 0
      replace ha : phiT ((uni I L).orderEmbOfFin hc a) = 0 := ha
      have hA : (uni I L).orderEmbOfFin hc a ∈ uni I L := Finset.orderEmbOfFin_mem _ hc a
      generalize (uni I L).orderEmbOfFin hc a = t at ha hA
      rcases t with i | l
      · change i = 0 at ha
        subst ha
        exact (mem_uni_inl I L _).1 hA
      · exact absurd ha (Fin.succ_ne_zero l)
    have hcard : I.card + L.card = d + 1 := by
      rw [← card_uni']
      exact hc
    have hcompl : Iᶜ = L.map (Fin.succEmb d) := by
      ext m
      simp only [Finset.mem_compl, Finset.mem_map, Fin.coe_succEmb]
      constructor
      · intro hm
        obtain ⟨a, ha⟩ := hbij.2 m
        replace ha : phiT ((uni I L).orderEmbOfFin hc a) = m := ha
        have hA : (uni I L).orderEmbOfFin hc a ∈ uni I L := Finset.orderEmbOfFin_mem _ hc a
        generalize (uni I L).orderEmbOfFin hc a = t at ha hA
        rcases t with i | l
        · change i = m at ha
          subst ha
          exact absurd ((mem_uni_inl I L _).1 hA) hm
        · exact ⟨l, (mem_uni_inr I L l).1 hA, ha⟩
      · rintro ⟨l, hl, rfl⟩ hI
        obtain ⟨a, ha⟩ := (hmem (toLex (Sum.inl l.succ))).1 ((mem_uni_inl I L _).2 hI)
        obtain ⟨b, hb⟩ := (hmem (toLex (Sum.inr l))).1 ((mem_uni_inr I L _).2 hl)
        have hab : a = b := hbij.1 (by
          show phiT ((uni I L).orderEmbOfFin hc a) = phiT ((uni I L).orderEmbOfFin hc b)
          rw [ha, hb]
          rfl)
        rw [hab, hb] at ha
        exact Sum.inl_ne_inr (toLex.injective ha.symm)
    refine ⟨h0I, hcard, ε, ?_⟩
    rw [hdet, prod_emb (uni I L) hc (cT T), prod_uni', hcompl, Finset.prod_map]
    simp [cT, app]

/- English proof (translation)
Introduce `hD d S E _ _ _ _ T`. Conclude with `⟨wd_lmul_app_detC_eq_zero_of_det hD T, detC_uni_univ_empty T, detC_uni_singleton_zero_univ T, detC_uni_eq_zero_or_eq_unit_smul_prod_compl T⟩`.
-/
theorem UpperTheory.Gal.productCup_of_system.thT_of :
    Det → ThT := by
  intro hD d S E _ _ _ _ T
  exact ⟨wd_lmul_app_detC_eq_zero_of_det hD T, detC_uni_univ_empty T, detC_uni_singleton_zero_univ T, detC_uni_eq_zero_or_eq_unit_smul_prod_compl T⟩

import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.LamPolySmulRight

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

/- English proof (translation)
Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Rewrite `this` using `[Fin.val_last, Fin.val_zero]`. Use linear arithmetic over natural numbers and integers.
-/
theorem last_ne_zero'' (m : ℕ) (hm : 1 ≤ m) : Fin.last m ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_last, Fin.val_zero] at this
  omega

/- English proof (translation)
Unfold `lamAt`. Use `split_ifs`. Both sides reduce to the same expression. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem lamAt_add' {n' m : ℕ} (X Y : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') :
    lamAt (X + Y) s = lamAt X s + lamAt Y s := by
  unfold lamAt
  split_ifs
  · rfl
  · funext i
    simp only [Pi.add_apply]
    ring

/- English proof (translation)
Unfold `lamAt`. Use `split_ifs`. Both sides reduce to the same expression. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.sub_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem lamAt_sub' {n' m : ℕ} (X Y : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') :
    lamAt (X - Y) s = lamAt X s - lamAt Y s := by
  unfold lamAt
  split_ifs
  · rfl
  · funext i
    simp only [Pi.sub_apply]
    ring

/- English proof (translation)
Unfold `lamAt dualW`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem lamAt_dualW {n' m : ℕ} (lo : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') :
    lamAt (dualW lo) s = dualWt (lamAt lo s) := by
  unfold lamAt dualW
  split_ifs <;> rfl

/- English proof (translation)
Introduce `i j hij`. Simplify using `only [dualWt]`. Use `h (Fin.rev_le_rev.mpr hij)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem dualWt_anti {m : ℕ} (mu : Fin (m + 1) → ℤ) (h : Antitone mu) : Antitone (dualWt mu) := by
  intro i j hij
  simp only [dualWt]
  have := h (Fin.rev_le_rev.mpr hij)
  linarith

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[dualWt]`.
-/
theorem dualWt_zero (m : ℕ) : dualWt (0 : Fin (m + 1) → ℤ) = 0 := by
  funext i
  simp [dualWt]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [flatW, wtPQ, dif_pos s.2]`.
-/
theorem flatW_top {n' : ℕ} (m : ℕ) {TT : Finset (Fin n')} (al be : TT → ℕ) (s : TT) :
    flatW m al be s.val = wtPQ m (al s) (be s) := by
  funext i
  simp only [flatW, wtPQ, dif_pos s.2]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [flatW, dif_neg hs, Pi.zero_apply]`.
-/
theorem flatW_off {n' : ℕ} (m : ℕ) {TT : Finset (Fin n')} (al be : TT → ℕ) (s : Fin n') (hs : s ∉ TT) :
    flatW m al be s = 0 := by
  funext i
  simp only [flatW, dif_neg hs, Pi.zero_apply]

/- English proof (translation)
Use function extensionality and compare the values at `s i`. Simplify using `only [flatW, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> push_cast <;> ring`.
-/
theorem flatW_add {n' : ℕ} (m : ℕ) {TT : Finset (Fin n')} (al be al' be' : TT → ℕ) :
    flatW m (fun s => al s + al' s) (fun s => be s + be' s) = flatW m al be + flatW m al' be' := by
  funext s i
  simp only [flatW, Pi.add_apply]
  split_ifs <;> push_cast <;> ring

/- English proof (translation)
Simplify using `only [Pi.sub_apply, wtPQ]`. Use `split_ifs with h1 h2`. Substitute `h1` using the available equality. Rewrite using `[h0]`. Expand and normalize the polynomial expressions, which then agree.

Substitute `h2` using the available equality. Rewrite using `[hl]`. Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lo_apply (m : ℕ) (ccl P Q : ℕ) (lam : Fin (m + 1) → ℤ) (h0 : lam 0 = (P : ℤ) + ccl)
    (hl : lam (Fin.last m) = -((Q : ℤ) + ccl)) (i : Fin (m + 1)) :
    (lam - wtPQ m P Q) i = if i = 0 then (ccl : ℤ) else if i = Fin.last m then -(ccl : ℤ) else lam i := by
  simp only [Pi.sub_apply, wtPQ]
  split_ifs with h1 h2
  · subst h1
    rw [h0]
    ring
  · subst h2
    rw [hl]
    ring
  · ring

/- English proof (translation)
Establish `hl0` using `last_ne_zero'' m hm`. Establish `hc : (0 : ℤ) ≤ ccl` using `Nat.cast_nonneg _`. Establish `hab : ∀ k : Fin (m + 1), k ≠ 0 → k ≠ Fin.last m → -(ccl : ℤ) ≤ lam k ∧ lam k ≤ ccl`. Introduce `k hk0 hkl`. Use `abs_le.mp (hmid k ?_ ?_)` and prove the remaining obligations.

Conclude with `Nat.pos_of_ne_zero fun h => hk0 (Fin.ext h)`. Establish `h1` using `k.isLt`. Establish `h2 : k.val ≠ m` using `fun h => hkl (Fin.ext (by rw [Fin.val_last]; exact h))`. Use linear arithmetic over natural numbers and integers. Introduce `i j hij`.

Rewrite using `[lo_apply m ccl P Q lam h0 hl i, lo_apply m ccl P Q lam h0 hl j]`. Distinguish the cases in `hj0 : j = 0`. Establish `hi0 : i = 0` using `le_antisymm (hj0 ▸ hij) (Fin.zero_le _)`. Rewrite using `[if_pos hj0, if_pos hi0]`. Distinguish the cases in `hil : i = Fin.last m`.

Establish `hjl : j = Fin.last m` using `le_antisymm (Fin.le_last _) (hil ▸ hij)`. Rewrite using `[if_neg hj0, if_pos hjl, if_neg (hil ▸ hl0), if_pos hil]`. Rewrite using `[if_neg hj0]`. Distinguish the cases in `hjl : j = Fin.last m`. Rewrite using `[if_pos hjl]`.

Distinguish the cases in `hi0 : i = 0`. Rewrite using `[if_pos hi0]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[if_neg hi0, if_neg hil]`. Combine the linear relations using `[(hab i hi0 hil).1]`.

Rewrite using `[if_neg hjl]`. Distinguish the cases in `hi0 : i = 0`. Rewrite using `[if_pos hi0]`. Combine the linear relations using `[(hab j hj0 hjl).2]`. Rewrite using `[if_neg hi0, if_neg hil]`.

Conclude with `hlam hij`.
-/
theorem lo_anti (m : ℕ) (hm : 1 ≤ m) (ccl P Q : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (h0 : lam 0 = (P : ℤ) + ccl) (hl : lam (Fin.last m) = -((Q : ℤ) + ccl))
    (hmid : ∀ i : Fin (m + 1), 0 < i.val → i.val < m → |lam i| ≤ ccl) : Antitone (lam - wtPQ m P Q) := by
  have hl0 := last_ne_zero'' m hm
  have hc : (0 : ℤ) ≤ ccl := Nat.cast_nonneg _
  have hab : ∀ k : Fin (m + 1), k ≠ 0 → k ≠ Fin.last m → -(ccl : ℤ) ≤ lam k ∧ lam k ≤ ccl := by
    intro k hk0 hkl
    refine abs_le.mp (hmid k ?_ ?_)
    · exact Nat.pos_of_ne_zero fun h => hk0 (Fin.ext h)
    · have h1 := k.isLt
      have h2 : k.val ≠ m := fun h => hkl (Fin.ext (by rw [Fin.val_last]; exact h))
      omega
  intro i j hij
  rw [lo_apply m ccl P Q lam h0 hl i, lo_apply m ccl P Q lam h0 hl j]
  by_cases hj0 : j = 0
  · have hi0 : i = 0 := le_antisymm (hj0 ▸ hij) (Fin.zero_le _)
    rw [if_pos hj0, if_pos hi0]
  by_cases hil : i = Fin.last m
  · have hjl : j = Fin.last m := le_antisymm (Fin.le_last _) (hil ▸ hij)
    rw [if_neg hj0, if_pos hjl, if_neg (hil ▸ hl0), if_pos hil]
  rw [if_neg hj0]
  by_cases hjl : j = Fin.last m
  · rw [if_pos hjl]
    by_cases hi0 : i = 0
    · rw [if_pos hi0]
      linarith
    · rw [if_neg hi0, if_neg hil]
      linarith [(hab i hi0 hil).1]
  · rw [if_neg hjl]
    by_cases hi0 : i = 0
    · rw [if_pos hi0]
      linarith [(hab j hj0 hjl).2]
    · rw [if_neg hi0, if_neg hil]
      exact hlam hij

/- English proof (translation)
Rewrite using `[rename_rename]`. Conclude with `congrArg (fun φ => φ f) rename_id`.
-/
theorem bE_snd {K : Type} [Field K] {α : Type} (b : Bool) (f : MvPolynomial α K) :
    rename (Prod.snd : Bool × α → α) (rename (fun v => (b, v)) f) = f := by
  rw [rename_rename]
  exact congrArg (fun φ => φ f) rename_id

/- English proof (translation)
Use `haveI := R.std.1.frac_O`. Establish `hinj : Function.Injective (algebraMap R.O R.Kf)` using `IsFractionRing.injective R.O R.Kf`. Establish `hz` using `tn_nuOf_zero m`. Set `abelian₂ : MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf →ₗ[R.Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf` to `(rename (Prod.snd : Bool × (Fin (m + 1) × Fin (m + 1)) → Fin (m + 1) × Fin (m + 1))).toLinearMap`. Establish `hLam : ∀ v t : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf, abelian₂ (blockEmb R.Kf true v * blockEmb R.Kf false t) = v * t`.

Introduce `v t`. Simplify using `only [abelian₂, AlgHom.toLinearMap_apply, map_mul, blockEmb, bE_snd]`. Establish `hlat : ∀ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf) (c : R.Kf), IsUnit g.det → c ≠ 0 → IsLattice R.O (colSpan R.O (g * lb_D (m + 1) 1 c))` using `fun g c hg hc => ⟨_, by rw [Matrix.det_mul]; exact hg.mul (lb_D_det _ _ c hc), rfl⟩`. Establish `h1H : ∀ Λ : Submodule R.O (Fin (m + 1) → R.Kf), IsLattice R.O Λ → (1 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) ∈ H0 R.O m 0 Λ` using `fun Λ hΛ => (invariant_sections_zero_weight_iff m Λ hΛ 1).mpr ⟨1, by simp⟩`. Use `⟨abelian₂, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `v hv t ht`. Rewrite using `[hLam]`. Rewrite `hv`, `ht`, the goal using `[hz]`. Rewrite using `[tn_const _ _ v hv, tn_const _ _ t ht, ← C_mul]`. Conclude with `tn_C_mem _ _ _`.

Introduce `Λ hΛ v hv t ht`. Rewrite using `[hLam]`. Take `⟨a, rfl⟩` from `(invariant_sections_zero_weight_iff m Λ hΛ v).mp hv`. Take `⟨b, rfl⟩` from `(invariant_sections_zero_weight_iff m Λ hΛ t).mp ht`. Conclude with `(invariant_sections_zero_weight_iff m Λ hΛ _).mpr ⟨a * b, by rw [map_mul, C_mul]⟩`.

Introduce `g hg`. Use `⟨1, 1, fun _ => 1, fun _ => 1, fun _ => 0, by simp, fun _ => le_rfl, ?_, ?_⟩` and prove the remaining obligations. Introduce `a' b F _`. Rewrite using `[hLam, Subsingleton.elim a' b]`. Simplify using the standard rewrite rules.

Introduce `c hc`. Establish `hL` using `hlat g c hg hc`. Simplify using `only [Pi.zero_apply, zpow_zero, one_smul]`. Use `⟨h1H _ hL, ?_, fun _ => h1H _ hL, fun _ => h1H _ hL⟩` and prove the remaining obligations. Introduce and unpack `⟨z', hz', he⟩`.

Take `⟨d, rfl⟩` from `(invariant_sections_zero_weight_iff m _ hL z').mp hz'`. Establish `h2 : (C (algebraMap R.O R.Kf 1) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) = C (algebraMap R.O R.Kf (R.w * d))`. Rewrite using `[map_one, map_one, map_mul, C_mul, tn_smulC]`. Conclude with `he`. Establish `h3` using `hinj (MvPolynomial.C_injective _ _ h2)`.

Conclude with `R.std.2.1.not_isUnit (IsUnit.of_mul_eq_one _ h3.symm)`.
-/
theorem posOK_zero {p n' : ℕ} (R : RS p n') (m : ℕ) : PosOK R m 0 0 0 0 0 0 1 0 := by
  haveI := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  have hz := tn_nuOf_zero m

  let abelian₂ : MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf →ₗ[R.Kf]
      MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf :=
    (rename (Prod.snd : Bool × (Fin (m + 1) × Fin (m + 1)) → Fin (m + 1) × Fin (m + 1))).toLinearMap
  have hLam : ∀ v t : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf,
      abelian₂ (blockEmb R.Kf true v * blockEmb R.Kf false t) = v * t := by
    intro v t
    simp only [abelian₂, AlgHom.toLinearMap_apply, map_mul, blockEmb, bE_snd]
  have hlat : ∀ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf) (c : R.Kf), IsUnit g.det → c ≠ 0 →
      IsLattice R.O (colSpan R.O (g * lb_D (m + 1) 1 c)) :=
    fun g c hg hc => ⟨_, by rw [Matrix.det_mul]; exact hg.mul (lb_D_det _ _ c hc), rfl⟩
  have h1H : ∀ Λ : Submodule R.O (Fin (m + 1) → R.Kf), IsLattice R.O Λ →
      (1 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) ∈ H0 R.O m 0 Λ :=
    fun Λ hΛ => (invariant_sections_zero_weight_iff m Λ hΛ 1).mpr ⟨1, by simp⟩
  refine ⟨abelian₂, ?_, ?_, ?_⟩
  · intro v hv t ht
    rw [hLam]
    rw [hz] at hv ht ⊢
    rw [tn_const _ _ v hv, tn_const _ _ t ht, ← C_mul]
    exact tn_C_mem _ _ _
  · intro Λ hΛ v hv t ht
    rw [hLam]
    obtain ⟨a, rfl⟩ := (invariant_sections_zero_weight_iff m Λ hΛ v).mp hv
    obtain ⟨b, rfl⟩ := (invariant_sections_zero_weight_iff m Λ hΛ t).mp ht
    exact (invariant_sections_zero_weight_iff m Λ hΛ _).mpr ⟨a * b, by rw [map_mul, C_mul]⟩
  · intro g hg
    refine ⟨1, 1, fun _ => 1, fun _ => 1, fun _ => 0, by simp, fun _ => le_rfl, ?_, ?_⟩
    · intro a' b F _
      rw [hLam, Subsingleton.elim a' b]
      simp
    · intro c hc
      have hL := hlat g c hg hc
      simp only [Pi.zero_apply, zpow_zero, one_smul]
      refine ⟨h1H _ hL, ?_, fun _ => h1H _ hL, fun _ => h1H _ hL⟩
      rintro ⟨z', hz', he⟩
      obtain ⟨d, rfl⟩ := (invariant_sections_zero_weight_iff m _ hL z').mp hz'
      have h2 : (C (algebraMap R.O R.Kf 1) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) =
          C (algebraMap R.O R.Kf (R.w * d)) := by
        rw [map_one, map_one, map_mul, C_mul, tn_smulC]
        exact he
      have h3 := hinj (MvPolynomial.C_injective _ _ h2)
      exact R.std.2.1.not_isUnit (IsUnit.of_mul_eq_one _ h3.symm)

/- English proof (translation)
Take `⟨abelian₂, hA, hB, hC⟩` from `h1 p n' R mm hmm a ccl P Q lam hlam h0 hl hmid h8`. Use `⟨abelian₂, hA, hB, fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨nb, z0, s, s', ka, e1, e2, e3, e4⟩` from `hC g hg`. Use `⟨nb, z0, s, s', ka, e1, e2, e3, fun c hc => ?_⟩` and prove the remaining obligations. Establish `hl0` using `last_ne_zero'' (mm + 1) (by omega)`.

Establish `z1 : (wtPQ (mm + 1) (2 * ccl) (2 * ccl)) 0 = ((2 * ccl : ℕ) : ℤ)` using `by simp [wtPQ]`. Establish `z2 : (lam - wtPQ (mm + 1) P Q) 0 = ((ccl : ℕ) : ℤ)`. Rewrite using `[lo_apply (mm + 1) ccl P Q lam h0 hl, if_pos rfl]`. Establish `z3 : (dualWt (lam - wtPQ (mm + 1) P Q)) 0 = ((ccl : ℕ) : ℤ)`. Simplify using `only [dualWt, Fin.rev_zero]`.

Rewrite using `[lo_apply (mm + 1) ccl P Q lam h0 hl, if_neg hl0, if_pos rfl, neg_neg]`. Rewrite using `[z1, z2, z3, zpow_natCast, zpow_natCast]`. Conclude with `e4 c hc`.
-/
theorem posOK_top (h1 : CloudOne) {p n' : ℕ} (R : RS p n') (mm : ℕ) (hmm : 1 ≤ mm) (a ccl P Q : ℕ)
    (lam : Fin (mm + 1 + 1) → ℤ) (hlam : Antitone lam) (h0 : lam 0 = (P : ℤ) + ccl)
    (hl : lam (Fin.last (mm + 1)) = -((Q : ℤ) + ccl))
    (hmid : ∀ i : Fin (mm + 1 + 1), 0 < i.val → i.val < mm + 1 → |lam i| ≤ ccl) (h8 : 2 * ccl ≤ 8 * a) :
    PosOK R (mm + 1) lam (wtPQ (mm + 1) P Q) (wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl))
      (wtPQ (mm + 1) (2 * ccl) (2 * ccl)) (lam - wtPQ (mm + 1) P Q) (dualWt (lam - wtPQ (mm + 1) P Q))
      (weylDim mm (fun j => lam j.castSucc.succ)) ⌈kappaOneExponent p a (mm + 1)⌉₊ := by
  obtain ⟨abelian₂, hA, hB, hC⟩ := h1 p n' R mm hmm a ccl P Q lam hlam h0 hl hmid h8
  refine ⟨abelian₂, hA, hB, fun g hg => ?_⟩
  obtain ⟨nb, z0, s, s', ka, e1, e2, e3, e4⟩ := hC g hg
  refine ⟨nb, z0, s, s', ka, e1, e2, e3, fun c hc => ?_⟩
  have hl0 := last_ne_zero'' (mm + 1) (by omega)
  have z1 : (wtPQ (mm + 1) (2 * ccl) (2 * ccl)) 0 = ((2 * ccl : ℕ) : ℤ) := by simp [wtPQ]
  have z2 : (lam - wtPQ (mm + 1) P Q) 0 = ((ccl : ℕ) : ℤ) := by
    rw [lo_apply (mm + 1) ccl P Q lam h0 hl, if_pos rfl]
  have z3 : (dualWt (lam - wtPQ (mm + 1) P Q)) 0 = ((ccl : ℕ) : ℤ) := by
    simp only [dualWt, Fin.rev_zero]
    rw [lo_apply (mm + 1) ccl P Q lam h0 hl, if_neg hl0, if_pos rfl, neg_neg]
  rw [z1, z2, z3, zpow_natCast, zpow_natCast]
  exact e4 c hc

/- English proof (translation)
Take `⟨h0, hl, hm⟩` from `(hBase s.val).1 s.2`. Take `⟨hA, hB⟩` from `hAB s`. Conclude with `⟨by rw [h0]; linarith, by rw [hl]; linarith, hm⟩`.
-/
theorem top_hyps {n' mm : ℕ} (TT : Finset (Fin n')) (ccl : ℕ) (aw bw : Fin n' → ℤ)
    (lam0 : Fin n' → Fin (mm + 1 + 1) → ℤ) (A B : TT → ℕ) (hBase : IsBaseWeight TT aw bw ccl lam0)
    (hAB : ∀ s : TT, (A s : ℤ) = aw s - ccl ∧ (B s : ℤ) = bw s - ccl) (s : TT) :
    lam0 s.val 0 = (A s : ℤ) + ccl ∧ lam0 s.val (Fin.last (mm + 1)) = -((B s : ℤ) + ccl) ∧
      ∀ i : Fin (mm + 1 + 1), 0 < i.val → i.val < mm + 1 → |lam0 s.val i| ≤ ccl := by
  obtain ⟨h0, hl, hm⟩ := (hBase s.val).1 s.2
  obtain ⟨hA, hB⟩ := hAB s
  exact ⟨by rw [h0]; linarith, by rw [hl]; linarith, hm⟩

/- English proof (translation)
Take `⟨t0, tl, tm⟩` from `top_hyps TT ccl aw bw lam0 A B hBase hAB s`. Establish `hl0` using `last_ne_zero'' (mm + 1) (by omega)`. Establish `hflat : ∀ al be : TT → ℕ, lamAt (flatW (mm + 1) al be) s.val = if Even s.val.val then wtPQ (mm + 1) (al s) (be s) else wtPQ (mm + 1) (be s) (al s)`. Introduce `al be`. Unfold `lamAt`.

Use `split_ifs with he`. Conclude with `flatW_top (mm + 1) al be s`. Use function extensionality and compare the values at `i`. Rewrite using `[flatW_top]`. Simplify using `only [wtPQ]`.

Distinguish the cases in `hi0 : i = 0`. Substitute `hi0` using the available equality. Simplify using `[Fin.rev_zero, hl0]`. Distinguish the cases in `hil : i = Fin.last (mm + 1)`. Substitute `hil` using the available equality.

Simplify using `[Fin.rev_last, hl0]`. Establish `h1 : i.rev ≠ 0` using `fun h => hil (by rw [← Fin.rev_rev i, h, Fin.rev_zero])`. Establish `h2 : i.rev ≠ Fin.last (mm + 1)` using `fun h => hi0 (by rw [← Fin.rev_rev i, h, Fin.rev_last])`. Simplify using `[hi0, hil, h1, h2]`. Rewrite using `[lamAt_sub', lamAt_dualW, lamAt_sub', hflat, hflat, hflat]`.

Rewrite using `[show cloudAt lam0 s.val = fun j => lamAt lam0 s.val j.castSucc.succ from rfl]`. Distinguish the cases in `he : Even s.val.val`. Simplify using `only [if_pos he]`. Establish `hlam' : lamAt lam0 s.val = lam0 s.val`. Unfold `lamAt`.

Rewrite using `[if_pos he]`. Rewrite using `[hlam']`. Conclude with `posOK_top h1 R mm hmm a ccl (A s) (B s) (lam0 s.val) (hDom s.val) t0 tl tm h8`. Simplify using `only [if_neg he]`. Establish `hlam' : lamAt lam0 s.val = fun i => -lam0 s.val i.rev`.

Unfold `lamAt`. Rewrite using `[if_neg he]`. Rewrite using `[hlam']`. Use `posOK_top h1 R mm hmm a ccl (B s) (A s) _ (dualWt_anti _ (hDom s.val)) ?_ ?_ ?_ h8` and prove the remaining obligations. Simplify using `only [Fin.rev_zero]`.

Rewrite using `[tl]`. Apply the tactic sequence `try ring`. Simplify using `only [Fin.rev_last]`. Rewrite using `[t0]`. Apply the tactic sequence `try ring`.

Introduce `i hi1 hi2`. Rewrite using `[abs_neg]`. Use `tm i.rev ?_ ?_` and prove the remaining obligations. Rewrite using `[Fin.val_rev]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Fin.val_rev]`. Use linear arithmetic over natural numbers and integers.
-/
theorem posOK_at_top (h1 : CloudOne) {p n' : ℕ} (R : RS p n') (mm : ℕ) (hmm : 1 ≤ mm) (TT : Finset (Fin n'))
    (a ccl : ℕ) (aw bw : Fin n' → ℤ) (lam0 : Fin n' → Fin (mm + 1 + 1) → ℤ) (A B : TT → ℕ)
    (hBase : IsBaseWeight TT aw bw ccl lam0) (hDom : IsDominant lam0)
    (hAB : ∀ s : TT, (A s : ℤ) = aw s - ccl ∧ (B s : ℤ) = bw s - ccl) (h8 : 2 * ccl ≤ 8 * a) (s : TT) :
    PosOK R (mm + 1) (lamAt lam0 s.val) (lamAt (flatW (mm + 1) A B) s.val)
      (lamAt (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) s.val)
      (lamAt (flatW (mm + 1) (fun _ : TT => 2 * ccl) (fun _ : TT => 2 * ccl)) s.val)
      (lamAt (lam0 - flatW (mm + 1) A B) s.val) (lamAt (dualW (lam0 - flatW (mm + 1) A B)) s.val)
      (weylDim mm (cloudAt lam0 s.val)) ⌈kappaOneExponent p a (mm + 1)⌉₊ := by
  obtain ⟨t0, tl, tm⟩ := top_hyps TT ccl aw bw lam0 A B hBase hAB s
  have hl0 := last_ne_zero'' (mm + 1) (by omega)

  have hflat : ∀ al be : TT → ℕ, lamAt (flatW (mm + 1) al be) s.val =
      if Even s.val.val then wtPQ (mm + 1) (al s) (be s) else wtPQ (mm + 1) (be s) (al s) := by
    intro al be
    unfold lamAt
    split_ifs with he
    · exact flatW_top (mm + 1) al be s
    · funext i
      rw [flatW_top]
      simp only [wtPQ]
      by_cases hi0 : i = 0
      · subst hi0
        simp [Fin.rev_zero, hl0]
      · by_cases hil : i = Fin.last (mm + 1)
        · subst hil
          simp [Fin.rev_last, hl0]
        · have h1 : i.rev ≠ 0 := fun h => hil (by rw [← Fin.rev_rev i, h, Fin.rev_zero])
          have h2 : i.rev ≠ Fin.last (mm + 1) := fun h => hi0 (by rw [← Fin.rev_rev i, h, Fin.rev_last])
          simp [hi0, hil, h1, h2]
  rw [lamAt_sub', lamAt_dualW, lamAt_sub', hflat, hflat, hflat]
  rw [show cloudAt lam0 s.val = fun j => lamAt lam0 s.val j.castSucc.succ from rfl]
  by_cases he : Even s.val.val
  · simp only [if_pos he]
    have hlam' : lamAt lam0 s.val = lam0 s.val := by
      unfold lamAt
      rw [if_pos he]
    rw [hlam']
    exact posOK_top h1 R mm hmm a ccl (A s) (B s) (lam0 s.val) (hDom s.val) t0 tl tm h8
  · simp only [if_neg he]
    have hlam' : lamAt lam0 s.val = fun i => -lam0 s.val i.rev := by
      unfold lamAt
      rw [if_neg he]
    rw [hlam']
    refine posOK_top h1 R mm hmm a ccl (B s) (A s) _ (dualWt_anti _ (hDom s.val)) ?_ ?_ ?_ h8
    · simp only [Fin.rev_zero]
      rw [tl]
      try ring
    · simp only [Fin.rev_last]
      rw [t0]
      try ring
    · intro i hi1 hi2
      rw [abs_neg]
      refine tm i.rev ?_ ?_
      · rw [Fin.val_rev]
        omega
      · rw [Fin.val_rev]
        omega

end Formalism.MainNotions.flipOneThree.Pf

end

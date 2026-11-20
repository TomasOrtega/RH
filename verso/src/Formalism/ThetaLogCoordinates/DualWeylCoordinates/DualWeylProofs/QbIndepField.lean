import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.BCoreT
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.StatementA

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

def qb_ev (M : GLMod n) (F : Type) [CommRing F] (nu : Fin n → ℤ) (x : M.ι → F) : M.ι → GLCoord F n :=
  Matrix.mulVec ((prMu M nu).map (Int.castRingHom (GLCoord F n)))
    (Matrix.mulVec (M.A.map (mapCoord F)) (fun i => algebraMap F (GLCoord F n) (x i)))

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma qb_ev_apply (M : GLMod n) (F : Type) [CommRing F] (nu : Fin n → ℤ) (x : M.ι → F) (i : M.ι) :
    qb_ev M F nu x i =
      ∑ k, (prMu M nu i k : GLCoord F n) * ∑ l, mapCoord F (M.A k l) * algebraMap F (GLCoord F n) (x l) := rfl

def qb_evL (M : GLMod n) (F : Type) [CommRing F] (nu : Fin n → ℤ) : (M.ι → F) →ₗ[F] (M.ι → GLCoord F n) where
  toFun := qb_ev M F nu
  map_add' x y := by
    funext i
    simp only [qb_ev_apply, Pi.add_apply, map_add, mul_add, sum_add_distrib]
  map_smul' a x := by
    funext i
    simp only [qb_ev_apply, Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, mul_sum]
    rw [Algebra.smul_def, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun l _ => ?_
    ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma qb_evL_apply (M : GLMod n) (F : Type) [CommRing F] (nu : Fin n → ℤ) (x : M.ι → F) :
    qb_evL M F nu x = qb_ev M F nu x := rfl

variable [NeZero n]

/- English proof (translation)
Simplify using `only [qb_equiv_apply, mul_sum]`. Rewrite using `[sum_comm]`. Use `sum_congr rfl fun K _ => ?_` and prove the remaining obligations. Establish `h2` using `congrArg (Int.cast : ℤ → GLCoord ℤ n) (qb_prMu_ph CF j nu i K)`. Move the coercions through the operations in `at h2`.

Simplify using `only [← mul_assoc, ← sum_mul]`. Rewrite using `[h2]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem qb_keyZ {M : GLMod n} (CF : ColFam M) (j : CF.J) (I : TIdx (CF.mu j)) (nu : Fin n → ℤ) (i : M.ι) :
    ∑ k, (prMu M nu i k : GLCoord ℤ n) * ∑ l, M.A k l * (CF.ph j l I : GLCoord ℤ n) =
      ∑ K, if qb_wtT (CF.mu j) K = nu then (CF.ph j i K : GLCoord ℤ n) * TMat (CF.mu j) K I else 0 := by
  simp only [qb_equiv_apply, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun K _ => ?_
  have h2 := congrArg (Int.cast : ℤ → GLCoord ℤ n) (qb_prMu_ph CF j nu i K)
  push_cast at h2
  simp only [← mul_assoc, ← sum_mul]
  rw [h2]
  split_ifs <;> simp

/- English proof (translation)
Establish `h` using `congrArg (mapCoord F) (qb_keyZ CF j I nu i)`. Simplify using `only [map_sum, map_mul, map_intCast, apply_ite (mapCoord F), map_zero] at h`. Rewrite using `[← h, qb_ev_apply]`. Simplify using `only [ColFam.vec, map_intCast]`.
-/
theorem qb_key {M : GLMod n} (CF : ColFam M) (F : Type) [CommRing F] (j : CF.J) (I : TIdx (CF.mu j))
    (nu : Fin n → ℤ) (i : M.ι) :
    qb_ev M F nu (fun i => (CF.vec j I i : F)) i =
      ∑ K, if qb_wtT (CF.mu j) K = nu then (CF.ph j i K : GLCoord F n) * mapCoord F (TMat (CF.mu j) K I)
        else 0 := by
  have h := congrArg (mapCoord F) (qb_keyZ CF j I nu i)
  simp only [map_sum, map_mul, map_intCast, apply_ite (mapCoord F), map_zero] at h
  rw [← h, qb_ev_apply]
  simp only [ColFam.vec, map_intCast]

/- English proof (translation)
Rewrite using `[qb_key]`. Simplify using `only [qb_wtT_eq_iff (CF.dom j), sum_ite_eq', mem_univ, if_true, brk]`.
-/
theorem qb_key_eq {M : GLMod n} (CF : ColFam M) (F : Type) [CommRing F] (j : CF.J) (I : TIdx (CF.mu j)) (i : M.ι) :
    qb_ev M F (CF.mu j) (fun i => (CF.vec j I i : F)) i =
      (CF.ph j i (canT (CF.mu j)) : GLCoord F n) * mapCoord F (brk (CF.mu j) I) := by
  rw [qb_key]
  simp only [qb_wtT_eq_iff (CF.dom j), sum_ite_eq', mem_univ, if_true, brk]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[qb_key]`. Conclude with `sum_eq_zero fun K _ => if_neg (by intro hK; exact h (by rw [← hK]; exact qb_wtT_le (CF.dom j) K))`.
-/
theorem qb_key_zero {M : GLMod n} (CF : ColFam M) (F : Type) [CommRing F] (j : CF.J) (I : TIdx (CF.mu j))
    (nu : Fin n → ℤ) (h : ¬ DomLE nu (CF.mu j)) :
    qb_ev M F nu (fun i => (CF.vec j I i : F)) = 0 := by
  funext i
  rw [qb_key]
  exact sum_eq_zero fun K _ => if_neg (by intro hK; exact h (by rw [← hK]; exact qb_wtT_le (CF.dom j) K))

/- English proof (translation)
Introduce `j`. Assume the negation of the conclusion as `hne`. Choose the witnesses or unpack the hypotheses as in `⟨l, hl⟩ : ∃ l : Module.Dual k W, l (f j) ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Conclude with `hne ((Module.forall_dual_apply_eq_zero_iff k (f j)).1 hcon)`. Use `hl (Fintype.linearIndependent_iff.1 hc (fun j => l (f j)) ?_ j)` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Use `congrArg l (h i)` as an intermediate fact. Simplify `this` using `[map_sum, mul_comm]`.
-/
lemma qb_indep_ext {k W κ ι : Type*} [Field k] [AddCommGroup W] [Module k W] [Fintype κ] (c : κ → ι → k)
    (hc : LinearIndependent k c) (f : κ → W) (h : ∀ i, ∑ j, c j i • f j = 0) : ∀ j, f j = 0 := by
  intro j
  by_contra hne
  obtain ⟨l, hl⟩ : ∃ l : Module.Dual k W, l (f j) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne ((Module.forall_dual_apply_eq_zero_iff k (f j)).1 hcon)
  refine hl (Fintype.linearIndependent_iff.1 hc (fun j => l (f j)) ?_ j)
  funext i
  have := congrArg l (h i)
  simpa [map_sum, mul_comm] using this

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `a ha`. Take `⟨p, hp⟩` from `CharP.exists F`. Break down `CharP.char_is_prime_or_zero F p with hpp | rfl` into its components or cases. Use `haveI := Fact.mk hpp`.

Use `letI := ZMod.algebra F p`. Use `qb_indep_ext (k := ZMod p) _ (CF.indepP p hpp nu) a fun i => ?_` and prove the remaining obligations. Use `congrFun ha i` as an intermediate fact. Simplify `this` using `[Algebra.smul_def, mul_comm]`. Use `haveI := CharP.charP_to_charZero F`.

Use `qb_indep_ext (k := ℚ) _ (CF.indepQ nu) a fun i => ?_` and prove the remaining obligations. Use `congrFun ha i` as an intermediate fact. Simplify `this` using `[Algebra.smul_def, mul_comm]`.
-/
theorem qb_indepF {M : GLMod n} (CF : ColFam M) (F : Type) [Field F] (nu : Fin n → ℤ) :
    LinearIndependent F
      (fun j : {j : CF.J // CF.mu j = nu} => fun i => ((CF.ph j.1 i (canT (CF.mu j.1)) : ℤ) : F)) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  obtain ⟨p, hp⟩ := CharP.exists F
  rcases CharP.char_is_prime_or_zero F p with hpp | rfl
  · haveI := Fact.mk hpp
    letI := ZMod.algebra F p
    refine qb_indep_ext (k := ZMod p) _ (CF.indepP p hpp nu) a fun i => ?_
    have := congrFun ha i
    simpa [Algebra.smul_def, mul_comm] using this
  · haveI := CharP.charP_to_charZero F
    refine qb_indep_ext (k := ℚ) _ (CF.indepQ nu) a fun i => ?_
    have := congrFun ha i
    simpa [Algebra.smul_def, mul_comm] using this

instance qb_fintypeStd (mu : Fin n → ℤ) : Fintype {I : TIdx mu // StdT I} := Fintype.ofFinite _

abbrev qb_Idx {M : GLMod n} (CF : ColFam M) := Σ j : CF.J, {I : TIdx (CF.mu j) // StdT I}

def qb_vecF {M : GLMod n} (CF : ColFam M) (F : Type) [CommRing F] (x : qb_Idx CF) : M.ι → F :=
  fun i => (CF.vec x.1 x.2.1 i : F)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma qb_vecF_def {M : GLMod n} (CF : ColFam M) (F : Type) [CommRing F] (x : qb_Idx CF) :
    qb_vecF CF F x = fun i => (CF.vec x.1 x.2.1 i : F) := rfl

/- English proof (translation)
Rewrite `h0` using `[← qb_evL_apply, map_sum]`. Simplify using `only [map_smul, qb_evL_apply] at h0`. Set `f : CF.J → GLCoord F n` to `fun j => ∑ I : {I : TIdx (CF.mu j) // StdT I}, a ⟨j, I⟩ • mapCoord F (brk (CF.mu j) I.1)`. Establish `h2 : ∀ (x : qb_Idx CF) (i : M.ι), (a x • qb_ev M F nu (qb_vecF CF F x)) i = if CF.mu x.1 = nu then (CF.ph x.1 i (canT (CF.mu x.1)) : GLCoord F n) * (a x • mapCoord F (brk (CF.mu x.1) x.2.1)) else 0`. Introduce `x i`.

Use `split_ifs with hx`. Substitute `hx` using the available equality. Rewrite using `[Pi.smul_apply, qb_vecF_def, qb_key_eq, mul_smul_comm]`. Distinguish the cases in `hax : a x = 0`. Rewrite using `[hax, zero_smul]`.

Both sides reduce to the same expression. Rewrite using `[qb_vecF_def, qb_key_zero CF F x.1 x.2.1 nu (fun hle => hx (hmax x hax hle)), smul_zero]`. Both sides reduce to the same expression. Establish `h3 : ∀ i, ∑ j : {j : CF.J // CF.mu j = nu}, ((CF.ph j.1 i (canT (CF.mu j.1)) : ℤ) : F) • f j.1 = 0`. Introduce `i`.

Establish `h4` using `congrFun h0 i`. Rewrite `h4` using `[Finset.sum_apply, Pi.zero_apply]`. Simplify using `only [h2] at h4`. Rewrite `h4` using `[Fintype.sum_sigma]`. Rewrite using `[← sum_subtype (univ.filter fun j => CF.mu j = nu) (by simp) (fun j => ((CF.ph j i (canT (CF.mu j)) : ℤ) : F) • f j), sum_filter]`.

Use `Eq.trans ?_ h4` and prove the remaining obligations. Use `sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `split_ifs with hj`. Simplify using `only [f, Algebra.smul_def, map_intCast, mul_sum]`. Simplify using the standard rewrite rules.

Establish `h5` using `qb_indep_ext (k := F) _ (qb_indepF CF F nu) (fun j => f j.1) h3`. Introduce and unpack `⟨j, I⟩ hj`. Conclude with `Fintype.linearIndependent_iff.1 (hA n (CF.mu j) (CF.dom j) F) (fun I => a ⟨j, I⟩) (h5 ⟨j, hj⟩) I`.
-/
theorem qb_nonvanish (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (F : Type) [Field F] (a : qb_Idx CF → F)
    (nu : Fin n → ℤ) (hmax : ∀ x, a x ≠ 0 → DomLE nu (CF.mu x.1) → CF.mu x.1 = nu)
    (h0 : qb_ev M F nu (∑ x, a x • qb_vecF CF F x) = 0) : ∀ x, CF.mu x.1 = nu → a x = 0 := by
  rw [← qb_evL_apply, map_sum] at h0
  simp only [map_smul, qb_evL_apply] at h0
  let f : CF.J → GLCoord F n := fun j => ∑ I : {I : TIdx (CF.mu j) // StdT I}, a ⟨j, I⟩ • mapCoord F (brk (CF.mu j) I.1)
  have h2 : ∀ (x : qb_Idx CF) (i : M.ι), (a x • qb_ev M F nu (qb_vecF CF F x)) i =
      if CF.mu x.1 = nu then (CF.ph x.1 i (canT (CF.mu x.1)) : GLCoord F n) *
        (a x • mapCoord F (brk (CF.mu x.1) x.2.1)) else 0 := by
    intro x i
    split_ifs with hx
    · subst hx
      rw [Pi.smul_apply, qb_vecF_def, qb_key_eq, mul_smul_comm]
    · by_cases hax : a x = 0
      · rw [hax, zero_smul]; rfl
      · rw [qb_vecF_def, qb_key_zero CF F x.1 x.2.1 nu (fun hle => hx (hmax x hax hle)), smul_zero]; rfl
  have h3 : ∀ i, ∑ j : {j : CF.J // CF.mu j = nu}, ((CF.ph j.1 i (canT (CF.mu j.1)) : ℤ) : F) • f j.1 = 0 := by
    intro i
    have h4 := congrFun h0 i
    rw [Finset.sum_apply, Pi.zero_apply] at h4
    simp only [h2] at h4
    rw [Fintype.sum_sigma] at h4
    rw [← sum_subtype (univ.filter fun j => CF.mu j = nu) (by simp)
      (fun j => ((CF.ph j i (canT (CF.mu j)) : ℤ) : F) • f j), sum_filter]
    refine Eq.trans ?_ h4
    refine sum_congr rfl fun j _ => ?_
    split_ifs with hj
    · simp only [f, Algebra.smul_def, map_intCast, mul_sum]
    · simp
  have h5 := qb_indep_ext (k := F) _ (qb_indepF CF F nu) (fun j => f j.1) h3
  rintro ⟨j, I⟩ hj
  exact Fintype.linearIndependent_iff.1 (hA n (CF.mu j) (CF.dom j) F) (fun I => a ⟨j, I⟩) (h5 ⟨j, hj⟩) I

/- English proof (translation)
Introduce `x0 hx0`. Assume the negation of the conclusion as `hn`. Set `s : Finset (Fin n → ℤ)` to `(univ.filter fun x => a x ≠ 0).image fun x => CF.mu x.1`. Establish `hs0 : CF.mu x0.1 ∈ s` using `mem_image.2 ⟨x0, by simp [hx0], rfl⟩`. Take `⟨nu, hnu, hle, hmax⟩` from `qb_exists_max_above s hs0`.

Take `⟨x1, hx1, rfl⟩` from `mem_image.1 hnu`. Establish `hx1' : a x1 ≠ 0` using `(mem_filter.1 hx1).2`. Establish `hout : CF.mu x1.1 ∉ pi` using `fun hin => hn (hpi.2 _ hin _ (CF.dom _) hle)`. Conclude with `hx1' (qb_nonvanish hA CF F a (CF.mu x1.1) (fun x hx hle' => hmax _ (mem_image.2 ⟨x, by simp [hx], rfl⟩) hle') (h _ (CF.dom _) hout) x1 rfl)`.
-/
theorem qb_supp_in (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (F : Type) [Field F] (a : qb_Idx CF → F)
    (pi : Set (Fin n → ℤ)) (hpi : DomLowerSet pi)
    (h : ∀ mu, Dominant mu → mu ∉ pi → qb_ev M F mu (∑ x, a x • qb_vecF CF F x) = 0) :
    ∀ x, a x ≠ 0 → CF.mu x.1 ∈ pi := by
  classical
  intro x0 hx0
  by_contra hn
  let s : Finset (Fin n → ℤ) := (univ.filter fun x => a x ≠ 0).image fun x => CF.mu x.1
  have hs0 : CF.mu x0.1 ∈ s := mem_image.2 ⟨x0, by simp [hx0], rfl⟩
  obtain ⟨nu, hnu, hle, hmax⟩ := qb_exists_max_above s hs0
  obtain ⟨x1, hx1, rfl⟩ := mem_image.1 hnu
  have hx1' : a x1 ≠ 0 := (mem_filter.1 hx1).2
  have hout : CF.mu x1.1 ∉ pi := fun hin => hn (hpi.2 _ hin _ (CF.dom _) hle)
  exact hx1' (qb_nonvanish hA CF F a (CF.mu x1.1)
    (fun x hx hle' => hmax _ (mem_image.2 ⟨x, by simp [hx], rfl⟩) hle') (h _ (CF.dom _) hout) x1 rfl)

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `a ha x`. Assume the negation of the conclusion as `hx`. Use `qb_supp_in hA CF F a ∅ ⟨fun _ h => h.elim, fun _ h => h.elim⟩ (fun mu _ _ => ?_) x hx` and prove the remaining obligations. Rewrite using `[ha, ← qb_evL_apply, map_zero]`.
-/
theorem qb_indep_field (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (F : Type) [Field F] :
    LinearIndependent F (qb_vecF CF F) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha x
  by_contra hx
  refine qb_supp_in hA CF F a ∅ ⟨fun _ h => h.elim, fun _ h => h.elim⟩ (fun mu _ _ => ?_) x hx
  rw [ha, ← qb_evL_apply, map_zero]

end Formalism.InvariantFactorPaths.ColumnFamilies

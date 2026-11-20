import Mathlib
import ReciprocityTheory.DualLattices.FormalChartAtZero

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨i, rfl⟩` from `hy`. Conclude with `⟨Ideal.subset_span ⟨i, rfl⟩, fun j => by simp⟩`. Consider the case `zero => exact ⟨by simp, fun j => by simp⟩`.

Consider the case `add y z _ _ hy hz`. Conclude with `⟨by simpa using add_mem hy.1 hz.1, fun j => by simpa using add_mem (hy.2 j) (hz.2 j)⟩`. Consider the case `smul r y _ hy`. Use `⟨?_, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[smul_eq_mul, TrivSqZeroExt.fst_mul]`.

Conclude with `Ideal.mul_mem_left _ _ hy.1`. Rewrite using `[smul_eq_mul, TrivSqZeroExt.snd_mul]`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]`. Conclude with `add_mem (Ideal.mul_mem_left _ _ (hy.2 j)) (Ideal.mul_mem_left _ _ hy.1)`.
-/
private lemma chartFirstOrder_mem_span {S : Type} [CommRing S] {g : ℕ} (a : Fin g → S)
    (x : TrivSqZeroExt S (Fin g → S))
    (hx : x ∈ Ideal.span (Set.range fun i => (TrivSqZeroExt.inl (a i) : TrivSqZeroExt S (Fin g → S)))) :
    x.fst ∈ Ideal.span (Set.range a) ∧ ∀ j, x.snd j ∈ Ideal.span (Set.range a) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact ⟨Ideal.subset_span ⟨i, rfl⟩, fun j => by simp⟩
  | zero => exact ⟨by simp, fun j => by simp⟩
  | add y z _ _ hy hz =>
    exact ⟨by simpa using add_mem hy.1 hz.1, fun j => by simpa using add_mem (hy.2 j) (hz.2 j)⟩
  | smul r y _ hy =>
    refine ⟨?_, fun j => ?_⟩
    · rw [smul_eq_mul, TrivSqZeroExt.fst_mul]
      exact Ideal.mul_mem_left _ _ hy.1
    · rw [smul_eq_mul, TrivSqZeroExt.snd_mul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op]
      exact add_mem (Ideal.mul_mem_left _ _ (hy.2 j)) (Ideal.mul_mem_left _ _ hy.1)

/- English proof (translation)
Introduce `H R₀ _ g B K ch S _ _ a ha`. Establish `nat : ∀ (T : Type) [CommRing T] [Algebra R₀ T] (T' : Type) [CommRing T'] [Algebra R₀ T'] (φ : T →ₐ[R₀] T') (x y : Fin g → T), (∀ i, IsNilpotent (x i)) → (∀ i, IsNilpotent (y i)) → ∀ k, φ (fAdd ch.F x y k) = fAdd ch.F (fun i => φ (x i)) (fun i => φ (y i)) k`. Introduce `T _ _ T' _ _ φ x y hx hy k`. Establish `h` using `((H (ch.F k) T (Sum.elim x y)).2 (by rintro (i | i); exacts [hx i, hy i])).1 T' φ`. Unfold `fAdd`.

Rewrite using `[h]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `cases i <;> rfl`. Set `T` to `TrivSqZeroExt S (Fin g → S)`.

Set `a' : Fin g → T` to `fun i => TrivSqZeroExt.inl (a i)`. Set `e' : Fin g → T` to `fun j => TrivSqZeroExt.inr (Pi.single j 1)`. Establish `ha' : ∀ i, IsNilpotent (a' i)` using `fun i => (ha i).map (TrivSqZeroExt.inlHom S (Fin g → S))`. Establish `he' : ∀ i, IsNilpotent (e' i)` using `fun i => ⟨2, by`. Rewrite using `[pow_two]`.

Conclude with `TrivSqZeroExt.inr_mul_inr _ _ _⟩`. Establish `hfst : ∀ k, (fAdd ch.F a' e' k).fst = a k`. Introduce `k`. Establish `h` using `nat T S (TrivSqZeroExt.fstHom R₀ S (Fin g → S)) a' e' ha' he' k`. Establish `h2` using `congrFun (ch.F_unit S a ha) k`.

Rewrite using `[← h2]`. Conclude with `h`. Use `⟨fun k j => (fAdd ch.F a' e' k).snd j, ?_, ?_⟩` and prove the remaining obligations. Introduce `k j`. Set `J : Ideal T` to `Ideal.span (Set.range a')`.

Establish `h` using `nat T (T ⧸ J) (Ideal.Quotient.mkₐ R₀ J) a' e' ha' he' k`. Establish `h0 : (fun i => Ideal.Quotient.mkₐ R₀ J (a' i)) = 0`. Use function extensionality and compare the values at `i`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)`. Establish `hn : ∀ i, IsNilpotent (Ideal.Quotient.mkₐ R₀ J (e' i))` using `fun i => (he' i).map _`.

Rewrite `h` using `[h0, ch.F_comm _ 0 _ (fun _ => IsNilpotent.zero) hn, ch.F_unit _ _ hn]`. Establish `hm : fAdd ch.F a' e' k - e' k ∈ J` using `Ideal.Quotient.eq.1 h`. Use `(chartFirstOrder_mem_span a _ hm).2 j` as an intermediate fact. Rewrite `this` using `[TrivSqZeroExt.snd_sub]`. Establish `h1 : (1 : Matrix (Fin g) (Fin g) S) k j = (e' k).snd j`.

Simplify using `only [e', TrivSqZeroExt.snd_inr, Matrix.one_apply, Pi.single_apply, eq_comm]`. Rewrite using `[h1]`. Conclude with `this`. Introduce `e he`. Set `l : (Fin g → S) →ₗ[R₀] S` to `{ toFun := fun v => v ⬝ᵥ e map_add' := fun v w => add_dotProduct _ _ _ map_smul' := fun r v => smul_dotProduct _ _ _ }`.

Establish `hl : ∀ v, l v = v ⬝ᵥ e` using `fun _ => rfl`. Set `φ : T →ₐ[R₀] S` to `TrivSqZeroExt.lift (AlgHom.id R₀ S) l (fun v w => by`. Simplify using `only [hl, dotProduct, Finset.sum_mul_sum]`. Use `Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_mul_mul_comm, he, mul_zero])`.

Use the proof step `(fun r v => by simp [hl])`. Use the proof step `(fun r v => by simp [hl, mul_comm])`. Establish `hφ : ∀ x : T, φ x = x.fst + x.snd ⬝ᵥ e` using `fun _ => rfl`. Use function extensionality and compare the values at `k`. Establish `h` using `nat T S φ a' e' ha' he' k`.

Establish `e1 : (fun i => φ (a' i)) = a`. Use function extensionality and compare the values at `i`. Simplify using `[hφ, a']`. Establish `e2 : (fun i => φ (e' i)) = e`. Use function extensionality and compare the values at `i`.

Simplify using `[hφ, e']`. Rewrite `h` using `[e1, e2, hφ, hfst]`. Rewrite using `[← h]`. Both sides reduce to the same expression.
-/
theorem chart_fAdd_firstOrder :
  (∀ {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : ι → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S), (∀ i, IsNilpotent (a i)) →
    ∃ M : Matrix (Fin g) (Fin g) S, (∀ k j, M k j - (1 : Matrix (Fin g) (Fin g) S) k j ∈ Ideal.span (Set.range a)) ∧
      ∀ e : Fin g → S, (∀ i j, e i * e j = 0) → fAdd ch.F a e = a + M *ᵥ e) := by
  intro H R₀ _ g B K ch S _ _ a ha

  have nat : ∀ (T : Type) [CommRing T] [Algebra R₀ T] (T' : Type) [CommRing T'] [Algebra R₀ T']
      (φ : T →ₐ[R₀] T') (x y : Fin g → T), (∀ i, IsNilpotent (x i)) → (∀ i, IsNilpotent (y i)) →
      ∀ k, φ (fAdd ch.F x y k) = fAdd ch.F (fun i => φ (x i)) (fun i => φ (y i)) k := by
    intro T _ _ T' _ _ φ x y hx hy k
    have h := ((H (ch.F k) T (Sum.elim x y)).2 (by rintro (i | i); exacts [hx i, hy i])).1 T' φ
    unfold fAdd
    rw [h]
    congr 1
    funext i
    cases i <;> rfl

  let T := TrivSqZeroExt S (Fin g → S)
  let a' : Fin g → T := fun i => TrivSqZeroExt.inl (a i)
  let e' : Fin g → T := fun j => TrivSqZeroExt.inr (Pi.single j 1)
  have ha' : ∀ i, IsNilpotent (a' i) := fun i => (ha i).map (TrivSqZeroExt.inlHom S (Fin g → S))
  have he' : ∀ i, IsNilpotent (e' i) := fun i => ⟨2, by
    rw [pow_two]; exact TrivSqZeroExt.inr_mul_inr _ _ _⟩
  have hfst : ∀ k, (fAdd ch.F a' e' k).fst = a k := by
    intro k
    have h := nat T S (TrivSqZeroExt.fstHom R₀ S (Fin g → S)) a' e' ha' he' k
    have h2 := congrFun (ch.F_unit S a ha) k
    rw [← h2]
    exact h
  refine ⟨fun k j => (fAdd ch.F a' e' k).snd j, ?_, ?_⟩
  · intro k j
    let J : Ideal T := Ideal.span (Set.range a')
    have h := nat T (T ⧸ J) (Ideal.Quotient.mkₐ R₀ J) a' e' ha' he' k
    have h0 : (fun i => Ideal.Quotient.mkₐ R₀ J (a' i)) = 0 := by
      funext i
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
    have hn : ∀ i, IsNilpotent (Ideal.Quotient.mkₐ R₀ J (e' i)) := fun i => (he' i).map _
    rw [h0, ch.F_comm _ 0 _ (fun _ => IsNilpotent.zero) hn, ch.F_unit _ _ hn] at h
    have hm : fAdd ch.F a' e' k - e' k ∈ J := Ideal.Quotient.eq.1 h
    have := (chartFirstOrder_mem_span a _ hm).2 j
    rw [TrivSqZeroExt.snd_sub] at this
    have h1 : (1 : Matrix (Fin g) (Fin g) S) k j = (e' k).snd j := by
      simp only [e', TrivSqZeroExt.snd_inr, Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [h1]
    exact this
  · intro e he
    let l : (Fin g → S) →ₗ[R₀] S :=
      { toFun := fun v => v ⬝ᵥ e
        map_add' := fun v w => add_dotProduct _ _ _
        map_smul' := fun r v => smul_dotProduct _ _ _ }
    have hl : ∀ v, l v = v ⬝ᵥ e := fun _ => rfl
    let φ : T →ₐ[R₀] S := TrivSqZeroExt.lift (AlgHom.id R₀ S) l
      (fun v w => by
        simp only [hl, dotProduct, Finset.sum_mul_sum]
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        rw [mul_mul_mul_comm, he, mul_zero])
      (fun r v => by simp [hl])
      (fun r v => by simp [hl, mul_comm])
    have hφ : ∀ x : T, φ x = x.fst + x.snd ⬝ᵥ e := fun _ => rfl
    funext k
    have h := nat T S φ a' e' ha' he' k
    have e1 : (fun i => φ (a' i)) = a := by
      funext i; simp [hφ, a']
    have e2 : (fun i => φ (e' i)) = e := by
      funext i; simp [hφ, e']
    rw [e1, e2, hφ, hfst] at h
    rw [← h]
    rfl

end GlobalTheory

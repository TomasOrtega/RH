import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]`.
-/
private theorem fix_mul {V : Type} [Monoid V] {l n : ℕ} {x : V} (h : x ^ l ^ n = x) (m : ℕ) : x ^ l ^ (n * m) = x := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

/- English proof (translation)
Take `⟨a, ha, hxa⟩` from `hx`. Take `⟨b, hb, hzb⟩` from `hz`. Use `⟨a * b, Nat.mul_pos ha hb, fix_mul hxa b, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.mul_comm]`. Conclude with `fix_mul hzb a`.
-/
private theorem fix_both {V : Type} [Monoid V] {l : ℕ} {x z : V} (hx : ∃ n : ℕ, 0 < n ∧ x ^ l ^ n = x)
    (hz : ∃ n : ℕ, 0 < n ∧ z ^ l ^ n = z) : ∃ n : ℕ, 0 < n ∧ x ^ l ^ n = x ∧ z ^ l ^ n = z := by
  obtain ⟨a, ha, hxa⟩ := hx
  obtain ⟨b, hb, hzb⟩ := hz
  refine ⟨a * b, Nat.mul_pos ha hb, fix_mul hxa b, ?_⟩
  rw [Nat.mul_comm]
  exact fix_mul hzb a

/- English proof (translation)
Introduce `l _ O _ _ _ Γ _ R _ _ ρ V _ _ _ y hy u hu hum hu0`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `key : ∀ v ∈ Algebra.adjoin O (mono ρ 0), ∃ n : ℕ, 0 < n ∧ (y v) ^ l ^ n = y v`. Introduce `v hv`.

Proceed by induction on `hv using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Apply `hcon` to reduce the goal to its premises. Take `⟨L, hL, rfl⟩` from `hx`. Use `⟨L, hL, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_list_prod, List.map_map]`. Both sides reduce to the same expression. Consider the case `algebraMap r`. Set `g : O →+* V` to `y.comp (algebraMap O R)`. Establish `hg : ∀ a ∈ maximalIdeal O, g a = 0` using `hy`.

Set `f : ResidueField O →+* V` to `Ideal.Quotient.lift (maximalIdeal O) g hg`. Establish `hf : Function.Injective f` using `f.injective`. Use `haveI : CharP (ResidueField O) l := f.charP hf l`. Use `letI : Fintype (ResidueField O) := Fintype.ofFinite _`. Take `⟨m, -, hm⟩` from `FiniteField.card (ResidueField O) l`.

Use `⟨m, m.pos, ?_⟩` and prove the remaining obligations. Establish `h1 : y (algebraMap O R r) = f (IsLocalRing.residue O r)` using `(Ideal.Quotient.lift_mk (maximalIdeal O) g hg).symm`. Rewrite using `[h1, ← map_pow, ← hm, FiniteField.pow_card]`. Consider the case `add x z _ _ hx hz`. Take `⟨n, hn, hxn, hzn⟩` from `fix_both hx hz`.

Conclude with `⟨n, hn, by rw [map_add, add_pow_char_pow, hxn, hzn]⟩`. Consider the case `mul x z _ _ hx hz`. Take `⟨n, hn, hxn, hzn⟩` from `fix_both hx hz`. Conclude with `⟨n, hn, by rw [map_mul, mul_pow, hxn, hzn]⟩`. Take `⟨n, hn, hun⟩` from `key u hu`.

Take `⟨k, hk⟩ : ∃ k, l ^ n = k + 1 + 1` from `⟨l ^ n - 2, by`. Use `Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt` as an intermediate fact. Use the proof step `omega⟩`. Apply `hu0` to reduce the goal to its premises. Establish `hmem : y u ^ (k + 1) ∈ maximalIdeal V` using `Ideal.pow_mem_of_mem _ hum _ (Nat.succ_pos k)`.

Establish `hunit : IsUnit (1 - y u ^ (k + 1))` using `IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ((mem_maximalIdeal _).mp hmem)`. Establish `h0 : y u * (1 - y u ^ (k + 1)) = 0`. Rewrite using `[mul_sub, mul_one, ← pow_succ', ← hk, hun, sub_self]`. Conclude with `hunit.mul_left_eq_zero.mp h0`.
-/
theorem UpperTheory.V.Ws.Po.nonAlg :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] (Γ : Type) [Group Γ] (R : Type) [CommRing R] [Algebra O R]
      (ρ : Γ →* M4 R) (V : Type) [CommRing V] [IsLocalRing V] [CharP V l] (y : R →+* V), (∀ a ∈ maximalIdeal O, y (algebraMap O R a) = 0) →
      ∀ u ∈ Algebra.adjoin O (mono ρ 0), y u ∈ maximalIdeal V → y u ≠ 0 →
      ∃ x ∈ mono (mapRep y ρ) 0, ∀ n : ℕ, 0 < n → x ^ l ^ n ≠ x := by
  intro l _ O _ _ _ Γ _ R _ _ ρ V _ _ _ y hy u hu hum hu0
  by_contra hcon
  push_neg at hcon
  have key : ∀ v ∈ Algebra.adjoin O (mono ρ 0), ∃ n : ℕ, 0 < n ∧ (y v) ^ l ^ n = y v := by
    intro v hv
    induction hv using Algebra.adjoin_induction with
    | mem x hx =>
      apply hcon
      obtain ⟨L, hL, rfl⟩ := hx
      refine ⟨L, hL, ?_⟩
      rw [map_list_prod, List.map_map]
      rfl
    | algebraMap r =>
      let g : O →+* V := y.comp (algebraMap O R)
      have hg : ∀ a ∈ maximalIdeal O, g a = 0 := hy
      let f : ResidueField O →+* V := Ideal.Quotient.lift (maximalIdeal O) g hg
      have hf : Function.Injective f := f.injective
      haveI : CharP (ResidueField O) l := f.charP hf l
      letI : Fintype (ResidueField O) := Fintype.ofFinite _
      obtain ⟨m, -, hm⟩ := FiniteField.card (ResidueField O) l
      refine ⟨m, m.pos, ?_⟩
      have h1 : y (algebraMap O R r) = f (IsLocalRing.residue O r) :=
        (Ideal.Quotient.lift_mk (maximalIdeal O) g hg).symm
      rw [h1, ← map_pow, ← hm, FiniteField.pow_card]
    | add x z _ _ hx hz =>
      obtain ⟨n, hn, hxn, hzn⟩ := fix_both hx hz
      exact ⟨n, hn, by rw [map_add, add_pow_char_pow, hxn, hzn]⟩
    | mul x z _ _ hx hz =>
      obtain ⟨n, hn, hxn, hzn⟩ := fix_both hx hz
      exact ⟨n, hn, by rw [map_mul, mul_pow, hxn, hzn]⟩
  obtain ⟨n, hn, hun⟩ := key u hu
  obtain ⟨k, hk⟩ : ∃ k, l ^ n = k + 1 + 1 :=
    ⟨l ^ n - 2, by
      have := Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt
      omega⟩
  apply hu0
  have hmem : y u ^ (k + 1) ∈ maximalIdeal V := Ideal.pow_mem_of_mem _ hum _ (Nat.succ_pos k)
  have hunit : IsUnit (1 - y u ^ (k + 1)) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ((mem_maximalIdeal _).mp hmem)
  have h0 : y u * (1 - y u ^ (k + 1)) = 0 := by
    rw [mul_sub, mul_one, ← pow_succ', ← hk, hun, sub_self]
  exact hunit.mul_left_eq_zero.mp h0

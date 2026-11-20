import Mathlib

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

variable {K I : Type} {M : Type} [AddCommGroup M] [Module ℂ M] {V : Type} [AddCommGroup V] [Module ℂ V]

def wordX (X : I → Module.End ℂ M) (l : List I) : Module.End ℂ M := (l.map X).prod

def filtX (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) (n : ℕ) : Submodule ℂ M :=
  Submodule.span ℂ {y | ∃ (l : List I) (v : V), l.length ≤ n ∧ y = wordX X l (ι v)}

/- English proof (translation)
Simplify using `[wordX]`.
-/
theorem wordX_cons (X : I → Module.End ℂ M) (a : I) (l : List I) (y : M) :
    wordX X (a :: l) y = X a (wordX X l y) := by
  simp [wordX]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[filtX, Submodule.span_le]`. Introduce and unpack `_ ⟨l, v, hl, rfl⟩`. Establish `: l = []` using `List.length_eq_zero_iff.1 (Nat.le_zero.1 hl)`. Substitute `this` using the available equality.

Conclude with `⟨v, by simp [wordX]⟩`. Introduce and unpack `_ ⟨v, rfl⟩`. Conclude with `Submodule.subset_span ⟨[], v, le_rfl, by simp [wordX]⟩`.
-/
theorem filtX_zero (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) : filtX X ι 0 = LinearMap.range ι := by
  apply le_antisymm
  · rw [filtX, Submodule.span_le]
    rintro _ ⟨l, v, hl, rfl⟩
    have : l = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hl)
    subst this
    exact ⟨v, by simp [wordX]⟩
  · rintro _ ⟨v, rfl⟩
    exact Submodule.subset_span ⟨[], v, le_rfl, by simp [wordX]⟩

/- English proof (translation)
Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨l, v, hl, rfl⟩`. Conclude with `⟨l, v, hl.trans h, rfl⟩`.
-/
theorem filtX_mono (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) {m n : ℕ} (h : m ≤ n) :
    filtX X ι m ≤ filtX X ι n := by
  refine Submodule.span_mono ?_
  rintro _ ⟨l, v, hl, rfl⟩
  exact ⟨l, v, hl.trans h, rfl⟩

/- English proof (translation)
Establish `: filtX X ι n ≤ (filtX X ι (n + 1)).comap (X i)`. Rewrite using `[filtX, Submodule.span_le]`. Introduce and unpack `_ ⟨l, v, hl, rfl⟩`. Conclude with `Submodule.subset_span ⟨i :: l, v, by simpa using hl, (wordX_cons X i l _).symm⟩`. Conclude with `fun x hx => this hx`.
-/
theorem filtX_X (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) (n : ℕ) (i : I) :
    ∀ x ∈ filtX X ι n, X i x ∈ filtX X ι (n + 1) := by
  have : filtX X ι n ≤ (filtX X ι (n + 1)).comap (X i) := by
    rw [filtX, Submodule.span_le]
    rintro _ ⟨l, v, hl, rfl⟩
    exact Submodule.subset_span ⟨i :: l, v, by simpa using hl, (wordX_cons X i l _).symm⟩
  exact fun x hx => this hx

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [filtX_zero]`. Use `infer_instance`. Consider the case `succ n ih => classical`. Establish `hle : filtX X ι (n + 1) ≤ filtX X ι n ⊔ ⨆ i, (filtX X ι n).map (X i)`.

Rewrite using `[filtX, Submodule.span_le]`. Introduce and unpack `_ ⟨l, v, hl, rfl⟩`. Consider the cases of `l with`. Consider the case `nil => exact Submodule.mem_sup_left (Submodule.subset_span ⟨[], v, Nat.zero_le _, rfl⟩)`. Consider the case `cons a l`.

Use `Submodule.mem_sup_right (Submodule.mem_iSup_of_mem a ?_)` and prove the remaining obligations. Conclude with `⟨wordX X l (ι v), Submodule.subset_span ⟨l, v, by simpa using hl, rfl⟩, (wordX_cons X a l _).symm⟩`. Conclude with `Submodule.finiteDimensional_of_le hle`.
-/
theorem filtX_fd [Fintype I] [FiniteDimensional ℂ V] (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) (n : ℕ) :
    FiniteDimensional ℂ (filtX X ι n) := by
  induction n with
  | zero => rw [filtX_zero]; infer_instance
  | succ n ih =>
    classical
    have hle : filtX X ι (n + 1) ≤ filtX X ι n ⊔ ⨆ i, (filtX X ι n).map (X i) := by
      rw [filtX, Submodule.span_le]
      rintro _ ⟨l, v, hl, rfl⟩
      cases l with
      | nil => exact Submodule.mem_sup_left (Submodule.subset_span ⟨[], v, Nat.zero_le _, rfl⟩)
      | cons a l =>
        refine Submodule.mem_sup_right (Submodule.mem_iSup_of_mem a ?_)
        exact ⟨wordX X l (ι v), Submodule.subset_span ⟨l, v, by simpa using hl, rfl⟩, (wordX_cons X a l _).symm⟩
    exact Submodule.finiteDimensional_of_le hle

/- English proof (translation)
Use `conv_lhs => rw [filtX]`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨l, v, hl, rfl⟩`. Distinguish the cases in `h : l.length ≤ n`. Conclude with `Submodule.mem_sup_left (Submodule.subset_span ⟨l, v, h, rfl⟩)`.

Establish `h' : l.length = n + 1` using `by omega`. Use `Submodule.mem_sup_right (Submodule.subset_span ⟨fun i => l.get (i.cast h'.symm), v, ?_⟩)` and prove the remaining obligations. Use `congr 2`. Apply `List.ext_getElem` to reduce the goal to its premises. Simplify using `[h']`.

Introduce `m h1 h2`. Rewrite using `[List.getElem_ofFn]`. Simplify using the standard rewrite rules.
-/
theorem filtX_succ_le (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) (n : ℕ) :
    filtX X ι (n + 1) ≤ filtX X ι n ⊔
      Submodule.span ℂ {y | ∃ (w : Fin (n + 1) → I) (v : V), y = wordX X (List.ofFn w) (ι v)} := by
  conv_lhs => rw [filtX]
  rw [Submodule.span_le]
  rintro _ ⟨l, v, hl, rfl⟩
  by_cases h : l.length ≤ n
  · exact Submodule.mem_sup_left (Submodule.subset_span ⟨l, v, h, rfl⟩)
  · have h' : l.length = n + 1 := by omega
    refine Submodule.mem_sup_right (Submodule.subset_span ⟨fun i => l.get (i.cast h'.symm), v, ?_⟩)
    congr 2
    apply List.ext_getElem
    · simp [h']
    · intro m h1 h2
      rw [List.getElem_ofFn]
      simp

/- English proof (translation)
Establish `key : ∀ (l : List I) (v : V), e k (wordX X l (ι v)) ∈ filtX X ι l.length`. Introduce `l v`. Proceed by induction on `l with`. Consider the case `nil`. Establish `: e k (wordX X [] (ι v)) = wordX X [] (ι (ρ k v))` using `by simp [wordX, hι]`.

Rewrite using `[this]`. Conclude with `Submodule.subset_span ⟨[], _, le_rfl, rfl⟩`. Consider the case `cons a l ih`. Establish `h` using `LinearMap.congr_fun (h1 k a) (wordX X l (ι v))`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply] at h`.

Rewrite using `[wordX_cons, sub_eq_iff_eq_add.1 h, List.length_cons]`. Use `Submodule.add_mem _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_) (filtX_X X ι _ a _ ih)` and prove the remaining obligations. Conclude with `filtX_X X ι _ j _ (Submodule.subset_span ⟨l, v, le_rfl, rfl⟩)`. Establish `: filtX X ι n ≤ (filtX X ι n).comap (e k)` using `by conv_lhs => rw [filtX]`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨l, v, hl, rfl⟩`. Conclude with `filtX_mono X ι hl (key l v)`. Conclude with `fun x hx => this hx`.
-/
theorem filtX_e [Fintype I] (e : K → Module.End ℂ M) (X : I → Module.End ℂ M) (c : K → Matrix I I ℂ)
    (h1 : ∀ k i, e k * X i - X i * e k = ∑ j, c k j i • X j) (ρ : K → Module.End ℂ V)
    (ι : V →ₗ[ℂ] M) (hι : ∀ k v, ι (ρ k v) = e k (ι v)) (n : ℕ) (k : K) :
    ∀ x ∈ filtX X ι n, e k x ∈ filtX X ι n := by
  have key : ∀ (l : List I) (v : V), e k (wordX X l (ι v)) ∈ filtX X ι l.length := by
    intro l v
    induction l with
    | nil =>
      have : e k (wordX X [] (ι v)) = wordX X [] (ι (ρ k v)) := by simp [wordX, hι]
      rw [this]
      exact Submodule.subset_span ⟨[], _, le_rfl, rfl⟩
    | cons a l ih =>
      have h := LinearMap.congr_fun (h1 k a) (wordX X l (ι v))
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply] at h
      rw [wordX_cons, sub_eq_iff_eq_add.1 h, List.length_cons]
      refine Submodule.add_mem _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
        (filtX_X X ι _ a _ ih)
      exact filtX_X X ι _ j _ (Submodule.subset_span ⟨l, v, le_rfl, rfl⟩)
  have : filtX X ι n ≤ (filtX X ι n).comap (e k) := by
    conv_lhs => rw [filtX]
    rw [Submodule.span_le]
    rintro _ ⟨l, v, hl, rfl⟩
    exact filtX_mono X ι hl (key l v)
  exact fun x hx => this hx

/- English proof (translation)
Proceed by induction on `h generalizing n with`. Consider the case `nil => simp`. Consider the case `@cons a l l' hp ih`. Rewrite using `[wordX_cons, wordX_cons, ← map_sub]`. Consider the cases of `n with`.

Consider the case `zero`. Establish `h0 : l = []` using `List.length_eq_zero_iff.1 (by simpa using hn)`. Substitute `h0` using the available equality. Establish `h0' : l' = []` using `hp.nil_eq.symm`. Substitute `h0'` using the available equality.

Simplify using the standard rewrite rules. Consider the case `succ n => exact filtX_X X ι n a _ (ih n (by simpa using hn))`. Consider the case `swap a b l`. Establish `hl : l.length ≤ n` using `by simp only [List.length_cons] at hn; omega`. Establish `hm : wordX X l (ι v) ∈ filtX X ι n` using `Submodule.subset_span ⟨l, v, hl, rfl⟩`.

Establish `hall : ∀ E ∈ Submodule.span ℂ (Set.range e), E (wordX X l (ι v)) ∈ filtX X ι n`. Introduce `E hE`. Proceed by induction on `hE using Submodule.span_induction with`. Consider the case `mem E hE`. Take `⟨k, rfl⟩` from `hE`.

Conclude with `filtX_e e X c h1 ρ ι hι n k _ hm`. Consider the case `zero => simp`. Consider the case `add E F _ _ h1 h2 => exact Submodule.add_mem _ h1 h2`. Consider the case `smul a E _ h1 => exact Submodule.smul_mem _ a h1`. Simplify using `only [wordX_cons]`.

Conclude with `hall _ (h2 b a)`. Consider the case `trans p1 p2 ih1 ih2`. Use `Submodule.add_mem _ (ih1 n hn) (ih2 n (p1.length_eq ▸ hn))` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem filtX_perm [Fintype I] (e : K → Module.End ℂ M) (X : I → Module.End ℂ M) (c : K → Matrix I I ℂ)
    (h1 : ∀ k i, e k * X i - X i * e k = ∑ j, c k j i • X j)
    (h2 : ∀ i j, X i * X j - X j * X i ∈ Submodule.span ℂ (Set.range e)) (ρ : K → Module.End ℂ V)
    (ι : V →ₗ[ℂ] M) (hι : ∀ k v, ι (ρ k v) = e k (ι v)) {l l' : List I} (h : l.Perm l') (n : ℕ)
    (hn : l.length ≤ n + 1) (v : V) : wordX X l (ι v) - wordX X l' (ι v) ∈ filtX X ι n := by
  induction h generalizing n with
  | nil => simp
  | @cons a l l' hp ih =>
    rw [wordX_cons, wordX_cons, ← map_sub]
    cases n with
    | zero =>
      have h0 : l = [] := List.length_eq_zero_iff.1 (by simpa using hn)
      subst h0
      have h0' : l' = [] := hp.nil_eq.symm
      subst h0'
      simp
    | succ n => exact filtX_X X ι n a _ (ih n (by simpa using hn))
  | swap a b l =>
    have hl : l.length ≤ n := by simp only [List.length_cons] at hn; omega
    have hm : wordX X l (ι v) ∈ filtX X ι n := Submodule.subset_span ⟨l, v, hl, rfl⟩
    have hall : ∀ E ∈ Submodule.span ℂ (Set.range e), E (wordX X l (ι v)) ∈ filtX X ι n := by
      intro E hE
      induction hE using Submodule.span_induction with
      | mem E hE =>
        obtain ⟨k, rfl⟩ := hE
        exact filtX_e e X c h1 ρ ι hι n k _ hm
      | zero => simp
      | add E F _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
      | smul a E _ h1 => exact Submodule.smul_mem _ a h1
    simp only [wordX_cons]
    exact hall _ (h2 b a)
  | trans p1 p2 ih1 ih2 =>
    have := Submodule.add_mem _ (ih1 n hn) (ih2 n (p1.length_eq ▸ hn))
    rwa [sub_add_sub_cancel] at this

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [wordX]`. Consider the case `succ n ih`. Establish `hc : ∀ (a : I) (l : List I), wordX X (a :: l) = X a * wordX X l` using `fun a l => by simp [wordX]`. Establish `u0 : ∀ j, List.ofFn (Function.update w 0 j) = j :: List.ofFn (fun i : Fin n => w i.succ)`.

Introduce `j`. Rewrite using `[List.ofFn_succ]`. Simplify using `[Function.update_of_ne (Fin.succ_ne_zero _)]`. Establish `us : ∀ (i : Fin n) j, List.ofFn (Function.update w i.succ j) = w 0 :: List.ofFn (Function.update (fun i : Fin n => w i.succ) i j)`. Introduce `i j`.

Rewrite using `[List.ofFn_succ, Function.update_of_ne (Fin.succ_ne_zero i).symm]`. Use `congr 2`. Use function extensionality and compare the values at `m`. Distinguish the cases in `hm : m = i`. Substitute `hm` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne hm, Function.update_of_ne (fun h => hm (Fin.succ_injective _ h))]`. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `only [u0, us, hc]`. Rewrite using `[List.ofFn_succ, hc, ← mul_assoc, sub_eq_iff_eq_add.1 (h1 k (w 0)), add_mul, mul_assoc, ih (fun i => w i.succ), mul_add, Finset.sum_mul, Finset.mul_sum]`.

Simplify using `only [Finset.mul_sum, mul_smul_comm, smul_mul_assoc, mul_assoc]`. Normalize the expressions using the abelian group laws.
-/
theorem wordX_comm [Fintype I] (e : K → Module.End ℂ M) (X : I → Module.End ℂ M) (c : K → Matrix I I ℂ)
    (h1 : ∀ k i, e k * X i - X i * e k = ∑ j, c k j i • X j) (k : K) (n : ℕ) (w : Fin n → I) :
    e k * wordX X (List.ofFn w) = wordX X (List.ofFn w) * e k +
      ∑ i, ∑ j, c k j (w i) • wordX X (List.ofFn (Function.update w i j)) := by
  induction n with
  | zero => simp [wordX]
  | succ n ih =>
    have hc : ∀ (a : I) (l : List I), wordX X (a :: l) = X a * wordX X l := fun a l => by simp [wordX]
    have u0 : ∀ j, List.ofFn (Function.update w 0 j) = j :: List.ofFn (fun i : Fin n => w i.succ) := by
      intro j
      rw [List.ofFn_succ]
      simp [Function.update_of_ne (Fin.succ_ne_zero _)]
    have us : ∀ (i : Fin n) j, List.ofFn (Function.update w i.succ j) =
        w 0 :: List.ofFn (Function.update (fun i : Fin n => w i.succ) i j) := by
      intro i j
      rw [List.ofFn_succ, Function.update_of_ne (Fin.succ_ne_zero i).symm]
      congr 2
      funext m
      by_cases hm : m = i
      · subst hm; simp
      · rw [Function.update_of_ne hm, Function.update_of_ne (fun h => hm (Fin.succ_injective _ h))]
    rw [Fin.sum_univ_succ]
    simp only [u0, us, hc]
    rw [List.ofFn_succ, hc, ← mul_assoc, sub_eq_iff_eq_add.1 (h1 k (w 0)), add_mul, mul_assoc,
      ih (fun i => w i.succ), mul_add, Finset.sum_mul, Finset.mul_sum]
    simp only [Finset.mul_sum, mul_smul_comm, smul_mul_assoc, mul_assoc]
    abel

end PositivityTheory.KReal

end

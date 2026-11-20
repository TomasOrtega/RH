import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClOfSelf
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M GlobalTheory.CompanionTheory.WordProd

namespace GlobalTheory.CompanionTheory.WordProd.Intl

def consEmb {m k : ℕ} (σ : Fin m ↪o Fin k) : Fin (m + 1) ↪o Fin (k + 1) :=
  OrderEmbedding.ofStrictMono
    (Fin.cons (α := fun _ => Fin (k + 1)) 0 (fun a => (σ a).succ)) (by
      intro a b hab
      induction a using Fin.cases with
      | zero =>
        induction b using Fin.cases with
        | zero => exact absurd hab (lt_irrefl _)
        | succ b => simp [Fin.succ_pos]
      | succ a =>
        induction b using Fin.cases with
        | zero => exact absurd hab (Fin.not_lt_zero _)
        | succ b => simpa using hab)

def shiftEmb {m k : ℕ} (σ : Fin m ↪o Fin k) : Fin m ↪o Fin (k + 1) :=
  OrderEmbedding.ofStrictMono (fun a => (σ a).succ) (fun a b h => by simpa using h)

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `exact Fin.cons_zero (α := fun _ => Fin (k + 1)) _ _`. Consider the case `(show Fin.cons (α := fun _ => Fin (k + 1)) 0 (fun a => (σ a).succ) 0 = 0; simp)`.
-/
@[simp] theorem consEmb_zero {m k : ℕ} (σ : Fin m ↪o Fin k) : consEmb σ 0 = 0 := by
  first
    | rfl
    | exact Fin.cons_zero (α := fun _ => Fin (k + 1)) _ _
    | (show Fin.cons (α := fun _ => Fin (k + 1)) 0 (fun a => (σ a).succ) 0 = 0; simp)

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `exact Fin.cons_succ (α := fun _ => Fin (k + 1)) _ _ _`. Consider the case `(show Fin.cons (α := fun _ => Fin (k + 1)) 0 (fun a => (σ a).succ) a.succ = (σ a).succ; simp)`.
-/
@[simp] theorem consEmb_succ {m k : ℕ} (σ : Fin m ↪o Fin k) (a : Fin m) :
    consEmb σ a.succ = (σ a).succ := by
  first
    | rfl
    | exact Fin.cons_succ (α := fun _ => Fin (k + 1)) _ _ _
    | (show Fin.cons (α := fun _ => Fin (k + 1)) 0 (fun a => (σ a).succ) a.succ = (σ a).succ; simp)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem shiftEmb_apply {m k : ℕ} (σ : Fin m ↪o Fin k) (a : Fin m) :
    shiftEmb σ a = (σ a).succ := rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, consEmb_zero σ⟩`.
-/
theorem zero_mem_range_consEmb {m k : ℕ} (σ : Fin m ↪o Fin k) :
    (0 : Fin (k + 1)) ∈ Set.range (consEmb σ) := ⟨0, consEmb_zero σ⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha⟩`. Consider the cases of `a using Fin.cases with`. Consider the case `zero`. Rewrite `ha` using `[GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_zero]`.

Conclude with `absurd ha.symm (Fin.succ_ne_zero j)`. Consider the case `succ a`. Rewrite `ha` using `[GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_succ]`. Conclude with `⟨a, Fin.succ_injective _ ha⟩`. Introduce and unpack `⟨a, rfl⟩`.

Conclude with `⟨a.succ, GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_succ σ a⟩`.
-/
theorem succ_mem_range_consEmb {m k : ℕ} (σ : Fin m ↪o Fin k) (j : Fin k) :
    j.succ ∈ Set.range (consEmb σ) ↔ j ∈ Set.range σ := by
  constructor
  · rintro ⟨a, ha⟩
    cases a using Fin.cases with
    | zero =>
      rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_zero] at ha
      exact absurd ha.symm (Fin.succ_ne_zero j)
    | succ a =>
      rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_succ] at ha
      exact ⟨a, Fin.succ_injective _ ha⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a.succ, GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_succ σ a⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha⟩`. Rewrite `ha` using `[GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply]`. Conclude with `⟨a, Fin.succ_injective _ ha⟩`. Introduce and unpack `⟨a, rfl⟩`.

Conclude with `⟨a, GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply σ a⟩`.
-/
theorem succ_mem_range_shiftEmb {m k : ℕ} (σ : Fin m ↪o Fin k) (j : Fin k) :
    j.succ ∈ Set.range (shiftEmb σ) ↔ j ∈ Set.range σ := by
  constructor
  · rintro ⟨a, ha⟩
    rw [GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply] at ha
    exact ⟨a, Fin.succ_injective _ ha⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply σ a⟩

/- English proof (translation)
Introduce `T u v w h`. Proceed by induction on `h with`. Consider the case `nil`. Apply the tactic sequence `refine ⟨fun j => Fin.elim0 j, (OrderIso.refl _).toOrderEmbedding, (OrderIso.refl _).toOrderEmbedding, ?_, ?_, ?_, ?_⟩ <;> intro j <;> exact Fin.elim0 j`. Consider the case `@left a u v w _ ih`.

Take `⟨r, σ₀, σ₁, h0, h1, hu, hv⟩` from `ih`. Use `⟨(Fin.cons (0 : Fin 2) r : Fin (w.length + 1) → Fin 2), GlobalTheory.CompanionTheory.WordProd.Intl.consEmb σ₀, GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb σ₁, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j`. Take `rfl | ⟨j, rfl⟩` from `Fin.eq_zero_or_eq_succ (n := w.length) j`. Simplify using `only [Fin.cons_zero, true_iff]`.

Conclude with `GlobalTheory.CompanionTheory.WordProd.Intl.zero_mem_range_consEmb σ₀`. Rewrite using `[Fin.cons_succ, GlobalTheory.CompanionTheory.WordProd.Intl.succ_mem_range_consEmb]`. Conclude with `h0 j`. Introduce `j`. Take `rfl | ⟨j, rfl⟩` from `Fin.eq_zero_or_eq_succ (n := w.length) j`.

Simplify using `only [Fin.cons_zero]`. Prove the components needed by the constructor for the conclusion. Introduce `hc`. Conclude with `absurd hc (by decide)`. Introduce and unpack `⟨x, hx⟩`.

Rewrite `hx` using `[GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply]`. Conclude with `absurd hx (Fin.succ_ne_zero _)`. Rewrite using `[Fin.cons_succ, GlobalTheory.CompanionTheory.WordProd.Intl.succ_mem_range_shiftEmb]`. Conclude with `h1 j`. Introduce `x`.

Take `rfl | ⟨x, rfl⟩` from `Fin.eq_zero_or_eq_succ (n := u.length) x`. Rewrite using `[GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_zero]`. Simplify using the standard rewrite rules. Rewrite using `[GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_succ] first`. Consider the case `exact hu x`.

Consider the case `simpa using hu x`. Introduce `x`. Rewrite using `[GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply]`. Use `first`. Consider the case `exact hv x`.

Consider the case `simpa using hv x`. Consider the case `@right a u v w _ ih`. Take `⟨r, σ₀, σ₁, h0, h1, hu, hv⟩` from `ih`. Use `⟨(Fin.cons (1 : Fin 2) r : Fin (w.length + 1) → Fin 2), GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb σ₀, GlobalTheory.CompanionTheory.WordProd.Intl.consEmb σ₁, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j`.

Take `rfl | ⟨j, rfl⟩` from `Fin.eq_zero_or_eq_succ (n := w.length) j`. Simplify using `only [Fin.cons_zero]`. Prove the components needed by the constructor for the conclusion. Introduce `hc`. Conclude with `absurd hc (by decide)`.

Introduce and unpack `⟨x, hx⟩`. Rewrite `hx` using `[GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply]`. Conclude with `absurd hx (Fin.succ_ne_zero _)`. Rewrite using `[Fin.cons_succ, GlobalTheory.CompanionTheory.WordProd.Intl.succ_mem_range_shiftEmb]`. Conclude with `h0 j`.

Introduce `j`. Take `rfl | ⟨j, rfl⟩` from `Fin.eq_zero_or_eq_succ (n := w.length) j`. Simplify using `only [Fin.cons_zero, true_iff]`. Conclude with `GlobalTheory.CompanionTheory.WordProd.Intl.zero_mem_range_consEmb σ₁`. Rewrite using `[Fin.cons_succ, GlobalTheory.CompanionTheory.WordProd.Intl.succ_mem_range_consEmb]`.

Conclude with `h1 j`. Introduce `x`. Rewrite using `[GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply]`. Use `first`. Consider the case `exact hu x`.

Consider the case `simpa using hu x`. Introduce `x`. Take `rfl | ⟨x, rfl⟩` from `Fin.eq_zero_or_eq_succ (n := v.length) x`. Rewrite using `[GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_zero]`. Simplify using the standard rewrite rules.

Rewrite using `[GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_succ] first`. Consider the case `exact hv x`. Consider the case `simpa using hv x`.
-/
theorem interleave_embeddings : ∀ {T : Type 1} {u v w : List T}, Zc.Comb.Interleave u v w →
    ∃ (r : Fin w.length → Fin 2) (σ₀ : Fin u.length ↪o Fin w.length)
      (σ₁ : Fin v.length ↪o Fin w.length),
      (∀ j, r j = 0 ↔ j ∈ Set.range σ₀) ∧ (∀ j, r j = 1 ↔ j ∈ Set.range σ₁) ∧
      (∀ a, w.get (σ₀ a) = u.get a) ∧ (∀ a, w.get (σ₁ a) = v.get a) := by
  intro T u v w h
  induction h with
  | nil =>
    refine ⟨fun j => Fin.elim0 j, (OrderIso.refl _).toOrderEmbedding,
      (OrderIso.refl _).toOrderEmbedding, ?_, ?_, ?_, ?_⟩ <;> intro j <;> exact Fin.elim0 j
  | @left a u v w _ ih =>
    obtain ⟨r, σ₀, σ₁, h0, h1, hu, hv⟩ := ih
    refine ⟨(Fin.cons (0 : Fin 2) r : Fin (w.length + 1) → Fin 2), GlobalTheory.CompanionTheory.WordProd.Intl.consEmb σ₀,
      GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb σ₁, ?_, ?_, ?_, ?_⟩
    · intro j
      obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ (n := w.length) j
      · simp only [Fin.cons_zero, true_iff]
        exact GlobalTheory.CompanionTheory.WordProd.Intl.zero_mem_range_consEmb σ₀
      · rw [Fin.cons_succ, GlobalTheory.CompanionTheory.WordProd.Intl.succ_mem_range_consEmb]
        exact h0 j
    · intro j
      obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ (n := w.length) j
      · simp only [Fin.cons_zero]
        constructor
        · intro hc
          exact absurd hc (by decide)
        · rintro ⟨x, hx⟩
          rw [GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply] at hx
          exact absurd hx (Fin.succ_ne_zero _)
      · rw [Fin.cons_succ, GlobalTheory.CompanionTheory.WordProd.Intl.succ_mem_range_shiftEmb]
        exact h1 j
    · intro x
      obtain rfl | ⟨x, rfl⟩ := Fin.eq_zero_or_eq_succ (n := u.length) x
      · rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_zero]
        simp
      · rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_succ]
        first
          | exact hu x
          | simpa using hu x
    · intro x
      rw [GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply]
      first
        | exact hv x
        | simpa using hv x
  | @right a u v w _ ih =>
    obtain ⟨r, σ₀, σ₁, h0, h1, hu, hv⟩ := ih
    refine ⟨(Fin.cons (1 : Fin 2) r : Fin (w.length + 1) → Fin 2), GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb σ₀,
      GlobalTheory.CompanionTheory.WordProd.Intl.consEmb σ₁, ?_, ?_, ?_, ?_⟩
    · intro j
      obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ (n := w.length) j
      · simp only [Fin.cons_zero]
        constructor
        · intro hc
          exact absurd hc (by decide)
        · rintro ⟨x, hx⟩
          rw [GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply] at hx
          exact absurd hx (Fin.succ_ne_zero _)
      · rw [Fin.cons_succ, GlobalTheory.CompanionTheory.WordProd.Intl.succ_mem_range_shiftEmb]
        exact h0 j
    · intro j
      obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ (n := w.length) j
      · simp only [Fin.cons_zero, true_iff]
        exact GlobalTheory.CompanionTheory.WordProd.Intl.zero_mem_range_consEmb σ₁
      · rw [Fin.cons_succ, GlobalTheory.CompanionTheory.WordProd.Intl.succ_mem_range_consEmb]
        exact h1 j
    · intro x
      rw [GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply]
      first
        | exact hu x
        | simpa using hu x
    · intro x
      obtain rfl | ⟨x, rfl⟩ := Fin.eq_zero_or_eq_succ (n := v.length) x
      · rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_zero]
        simp
      · rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_succ]
        first
          | exact hv x
          | simpa using hv x

end GlobalTheory.CompanionTheory.WordProd.Intl

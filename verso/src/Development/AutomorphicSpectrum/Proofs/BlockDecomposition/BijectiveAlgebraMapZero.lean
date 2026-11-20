import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Coproduct

/- English proof (translation)
Take `⟨z, hz, -⟩` from `h.ex A (RingHom.id A) (fun i => i.elim0) (fun i => i.elim0)`. Establish `hzx : ∀ a, z (algebraMap A K a) = a` using `fun a => by`. Simplify using `using congrArg (fun f : A →+* A => f a) hz`. Establish `hid : (algebraMap A K).comp z = RingHom.id K`. Use `h.uniq K _ _ ?_ (fun i => i.elim0)` and prove the remaining obligations.

Use extensionality with `a`. Simplify using `[hzx]`. Use `Function.bijective_iff_has_inverse.mpr ⟨z, hzx, fun k => ?_⟩` and prove the remaining obligations. Simplify using `using congrArg (fun f : K →+* K => f k) hid`.
-/
theorem bijective_algebraMap_zero {A B K : Type} [CommRing A] [CommRing B] [CommRing K]
    [Algebra A B] [Algebra A K] {ι : Fin 0 → (B →ₐ[A] K)} (h : IsWP ι) :
    Function.Bijective (algebraMap A K) := by
  obtain ⟨z, hz, -⟩ := h.ex A (RingHom.id A) (fun i => i.elim0) (fun i => i.elim0)
  have hzx : ∀ a, z (algebraMap A K a) = a := fun a => by
    simpa using congrArg (fun f : A →+* A => f a) hz
  have hid : (algebraMap A K).comp z = RingHom.id K := by
    refine h.uniq K _ _ ?_ (fun i => i.elim0)
    ext a
    simp [hzx]
  refine Function.bijective_iff_has_inverse.mpr ⟨z, hzx, fun k => ?_⟩
  simpa using congrArg (fun f : K →+* K => f k) hid

/- English proof (translation)
Take `⟨z, hz, hy⟩` from `h.ex B (algebraMap A B) (fun _ => RingHom.id B) (fun _ => RingHom.id_comp _)`. Establish `hzi : ∀ b, z (ι 0 b) = b` using `fun b => by`. Simplify using `using congrArg (fun f : B →+* B => f b) (hy 0)`. Establish `hza : ∀ a, z (algebraMap A K a) = algebraMap A B a` using `fun a => by`. Simplify using `using congrArg (fun f : A →+* B => f a) hz`.

Establish `hid : ((ι 0 : B →ₐ[A] K) : B →+* K).comp z = RingHom.id K`. Use `h.uniq K _ _ ?_ (fun i => ?_)` and prove the remaining obligations. Use extensionality with `a`. Simplify using `[hza]`. Take `rfl : i = 0` from `Subsingleton.elim _ _`.

Use extensionality with `b`. Simplify using `[hzi]`. Use `Function.bijective_iff_has_inverse.mpr ⟨z, hzi, fun k => ?_⟩` and prove the remaining obligations. Simplify using `using congrArg (fun f : K →+* K => f k) hid`.
-/
theorem bijective_one {A B K : Type} [CommRing A] [CommRing B] [CommRing K]
    [Algebra A B] [Algebra A K] {ι : Fin 1 → (B →ₐ[A] K)} (h : IsWP ι) :
    Function.Bijective (ι 0) := by
  obtain ⟨z, hz, hy⟩ := h.ex B (algebraMap A B) (fun _ => RingHom.id B)
    (fun _ => RingHom.id_comp _)
  have hzi : ∀ b, z (ι 0 b) = b := fun b => by
    simpa using congrArg (fun f : B →+* B => f b) (hy 0)
  have hza : ∀ a, z (algebraMap A K a) = algebraMap A B a := fun a => by
    simpa using congrArg (fun f : A →+* B => f a) hz
  have hid : ((ι 0 : B →ₐ[A] K) : B →+* K).comp z = RingHom.id K := by
    refine h.uniq K _ _ ?_ (fun i => ?_)
    · ext a
      simp [hza]
    · obtain rfl : i = 0 := Subsingleton.elim _ _
      ext b
      simp [hzi]
  refine Function.bijective_iff_has_inverse.mpr ⟨z, hzi, fun k => ?_⟩
  simpa using congrArg (fun f : K →+* K => f k) hid

/- English proof (translation)
Establish `key : ∀ (n : ℕ) (k : Fin (n + 1)), ∃ d : K n →ₐ[A] K (n + 1), ∀ i, d.comp (ι n i) = ι (n + 1) (k.succAbove i)`. Introduce `n k`. Take `⟨z, hz, hy⟩` from `(h n).ex (K (n + 1)) (algebraMap A (K (n + 1))) (fun i => (ι (n + 1) (k.succAbove i) : B →+* K (n + 1))) (fun i => by ext a; simp)`. Use `⟨{ z with commutes' := fun a => congrArg (fun f : A →+* K (n + 1) => f a) hz }, fun i => ?_⟩` and prove the remaining obligations. Use extensionality with `b`.

Conclude with `congrArg (fun f : B →+* K (n + 1) => f b) (hy i)`. Use `choose δ hδ using key`. Conclude with `⟨δ, hδ⟩`.
-/
theorem exists_coface {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)]
    (ι : ∀ n, Fin n → (B →ₐ[A] K n)) (h : ∀ n, IsWP (ι n)) :
    ∃ δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1)),
      ∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i) := by
  have key : ∀ (n : ℕ) (k : Fin (n + 1)), ∃ d : K n →ₐ[A] K (n + 1),
      ∀ i, d.comp (ι n i) = ι (n + 1) (k.succAbove i) := by
    intro n k
    obtain ⟨z, hz, hy⟩ := (h n).ex (K (n + 1)) (algebraMap A (K (n + 1)))
      (fun i => (ι (n + 1) (k.succAbove i) : B →+* K (n + 1)))
      (fun i => by ext a; simp)
    refine ⟨{ z with commutes' := fun a => congrArg (fun f : A →+* K (n + 1) => f a) hz },
      fun i => ?_⟩
    ext b
    exact congrArg (fun f : B →+* K (n + 1) => f b) (hy i)
  choose δ hδ using key
  exact ⟨δ, hδ⟩

/- English proof (translation)
Introduce `A _ B _ _ K _ _ ι h`. Conclude with `⟨bijective_algebraMap_zero (h 0), bijective_one (h 1), exists_coface K ι h⟩`.
-/
theorem coproduct_low_and_coface : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n)), (∀ n, IsWP (ι n)) → Function.Bijective (algebraMap A (K 0)) ∧ Function.Bijective (ι 1 0) ∧ ∃ δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1)), ∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i) := by
  intro A _ B _ _ K _ _ ι h
  exact ⟨bijective_algebraMap_zero (h 0), bijective_one (h 1), exists_coface K ι h⟩

end GlobalTheory.CompanionTheory.Coproduct

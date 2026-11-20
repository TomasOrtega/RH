import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitsOfSplitOn

noncomputable section

open TensorProduct

namespace UpperTheory.Ru.crystallineComparison

section Alg

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

/- English proof (translation)
Take `⟨t, ht, ht1⟩` from `Algebra.FormallyUnramified.iff_exists_tensorProduct.1 (inferInstance : Algebra.FormallyUnramified R A)`. Set `f : A ⊗[R] A →ₐ[R] A` to `Algebra.TensorProduct.lift ((Algebra.ofId R A).comp σ) (AlgHom.id R A) fun _ _ => Commute.all _ _`. Establish `hf : ∀ x y, f (x ⊗ₜ y) = algebraMap R A (σ x) * y` using `fun x y => by`. Simplify using `[f, Algebra.ofId_apply]`. Establish `key : ∀ a, a * f t = algebraMap R A (σ a) * f t` using `fun a => by`.

Use `congrArg f (ht a)` as an intermediate fact. Rewrite `this` using `[map_mul, map_sub, hf, hf, map_zero, map_one, map_one, one_mul, mul_one, sub_mul, sub_eq_zero]`. Conclude with `this`. Establish `h1 : σ (f t) = 1`. Establish `: (σ.comp f) = σ.comp (Algebra.TensorProduct.lmul' R)`.

Apply the tactic sequence `ext x <;> simp [hf]`. Establish `h2` using `DFunLike.congr_fun this t`. Simplify `h2` using `[ht1]`. Use `⟨f t, ?_, h1, key⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f t * f t = f t`.

Rewrite using `[key, h1, map_one, one_mul]`.
-/
private lemma exists_idem [Algebra.FormallyUnramified R A] [Module.Finite R A] (σ : A →ₐ[R] R) :
    ∃ e : A, IsIdempotentElem e ∧ σ e = 1 ∧ ∀ a, a * e = algebraMap R A (σ a) * e := by
  obtain ⟨t, ht, ht1⟩ := Algebra.FormallyUnramified.iff_exists_tensorProduct.1
    (inferInstance : Algebra.FormallyUnramified R A)
  let f : A ⊗[R] A →ₐ[R] A :=
    Algebra.TensorProduct.lift ((Algebra.ofId R A).comp σ) (AlgHom.id R A) fun _ _ => Commute.all _ _
  have hf : ∀ x y, f (x ⊗ₜ y) = algebraMap R A (σ x) * y := fun x y => by
    simp [f, Algebra.ofId_apply]
  have key : ∀ a, a * f t = algebraMap R A (σ a) * f t := fun a => by
    have := congrArg f (ht a)
    rw [map_mul, map_sub, hf, hf, map_zero, map_one, map_one, one_mul, mul_one, sub_mul, sub_eq_zero] at this
    exact this
  have h1 : σ (f t) = 1 := by
    have : (σ.comp f) = σ.comp (Algebra.TensorProduct.lmul' R) := by
      ext x <;> simp [hf]
    have h2 := DFunLike.congr_fun this t
    simpa [ht1] using h2
  refine ⟨f t, ?_, h1, key⟩
  change f t * f t = f t
  rw [key, h1, map_one, one_mul]

/- English proof (translation)
Establish `: Finite (K ⊗[R] A →ₐ[K] K)` using `inferInstance`. Use `Finite.of_injective (fun f : A →ₐ[R] K => (Algebra.TensorProduct.lift (AlgHom.id K K) f fun _ _ => Commute.all _ _ : K ⊗[R] A →ₐ[K] K)) ?_` and prove the remaining obligations. Introduce `f g h`. Use extensionality with `a`. Simplify using `using DFunLike.congr_fun h (1 ⊗ₜ a)`.
-/
private lemma finite_algHom (K : Type) [Field K] [Algebra R K] [Module.Finite R A] : Finite (A →ₐ[R] K) := by
  have : Finite (K ⊗[R] A →ₐ[K] K) := inferInstance
  refine Finite.of_injective (fun f : A →ₐ[R] K =>
    (Algebra.TensorProduct.lift (AlgHom.id K K) f fun _ _ => Commute.all _ _ : K ⊗[R] A →ₐ[K] K)) ?_
  intro f g h
  ext a
  simpa using DFunLike.congr_fun h (1 ⊗ₜ a)

/- English proof (translation)
Establish `hf : IsIdempotentElem (1 - e)` using `he.one_sub`. Establish `: IsLocalization.Away (1 - e) (A ⧸ Ideal.span {e})` using `IsLocalization.away_of_isIdempotentElem hf (by simp [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]) Ideal.Quotient.mk_surjective`. Establish `: Algebra.FormallyEtale A (A ⧸ Ideal.span {e})` using `Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (1 - e))`. Establish `: Algebra.FinitePresentation A (A ⧸ Ideal.span {e})` using `Algebra.FinitePresentation.quotient ⟨{e}, by simp⟩`. Establish `: Algebra.Etale A (A ⧸ Ideal.span {e})` using `⟨inferInstance, inferInstance⟩`.

Conclude with `Algebra.Etale.comp R A _`.
-/
private lemma quot_etale [Algebra.Etale R A] {e : A} (he : IsIdempotentElem e) :
    Algebra.Etale R (A ⧸ Ideal.span {e}) := by
  have hf : IsIdempotentElem (1 - e) := he.one_sub
  have : IsLocalization.Away (1 - e) (A ⧸ Ideal.span {e}) :=
    IsLocalization.away_of_isIdempotentElem hf (by simp [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker])
      Ideal.Quotient.mk_surjective
  have : Algebra.FormallyEtale A (A ⧸ Ideal.span {e}) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (1 - e))
  have : Algebra.FinitePresentation A (A ⧸ Ideal.span {e}) :=
    Algebra.FinitePresentation.quotient ⟨{e}, by simp⟩
  have : Algebra.Etale A (A ⧸ Ideal.span {e}) := ⟨inferInstance, inferInstance⟩
  exact Algebra.Etale.comp R A _

/- English proof (translation)
Establish `hfin : Finite (A →ₐ[R] K)` using `finite_algHom K`. Set `π : A →ₐ[R] A ⧸ Ideal.span {e}` to `Ideal.Quotient.mkₐ R _`. Establish `hπ : Function.Surjective π` using `Ideal.Quotient.mk_surjective`. Establish `hπe : π e = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)`. Establish `hB : Finite (A ⧸ Ideal.span {e} →ₐ[R] K)` using `Finite.of_injective (fun g => g.comp π) fun g g' h => by`.

Use extensionality with `x`. Take `⟨a, rfl⟩` from `hπ x`. Conclude with `DFunLike.congr_fun h a`. Set `F : Option (A ⧸ Ideal.span {e} →ₐ[R] K) → (A →ₐ[R] K)` to `fun o => o.elim ((Algebra.ofId R K).comp σ) fun g => g.comp π`. Establish `hF : Function.Bijective F`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `(_ | g) (_ | g') h`. Both sides reduce to the same expression. Use `DFunLike.congr_fun h e` as an intermediate fact. Simplify using `[F, h1, hπe, Algebra.ofId_apply] at this`.

Use `DFunLike.congr_fun h e` as an intermediate fact. Simplify using `[F, h1, hπe, Algebra.ofId_apply] at this`. Use `congr 1`. Use extensionality with `x`. Take `⟨a, rfl⟩` from `hπ x`.

Conclude with `DFunLike.congr_fun h a`. Introduce `f`. Establish `hfe : IsIdempotentElem (f e)` using `hi.map f`. Break down `IsIdempotentElem.iff_eq_zero_or_one.1 hfe with h0 | h0` into its components or cases. Establish `hk : ∀ a ∈ Ideal.span {e}, f a = 0` using `fun a ha => by`.

Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 ha`. Rewrite using `[map_mul, h0, mul_zero]`. Use `⟨some (Ideal.Quotient.liftₐ _ f hk), ?_⟩` and prove the remaining obligations. Use extensionality with `a`. Simplify using `only [F, π, Option.elim, AlgHom.comp_apply]`.

Conclude with `Ideal.Quotient.lift_mk _ _ _`. Use `⟨none, ?_⟩` and prove the remaining obligations. Use extensionality with `a`. Use `congrArg f (he a)` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul, h0, mul_one, mul_one, f.commutes]`.

Simplify using `[F, this, Algebra.ofId_apply]`. Rewrite using `[← Nat.card_congr (Equiv.ofBijective F hF), Finite.card_option]`.
-/
private lemma card_quot [Module.Finite R A] {e : A} (σ : A →ₐ[R] R) (h1 : σ e = 1)
    (he : ∀ a, a * e = algebraMap R A (σ a) * e) (hi : IsIdempotentElem e) (K : Type) [Field K] [Algebra R K] :
    Nat.card (A →ₐ[R] K) = Nat.card (A ⧸ Ideal.span {e} →ₐ[R] K) + 1 := by
  have hfin : Finite (A →ₐ[R] K) := finite_algHom K
  let π : A →ₐ[R] A ⧸ Ideal.span {e} := Ideal.Quotient.mkₐ R _
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hπe : π e = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  have hB : Finite (A ⧸ Ideal.span {e} →ₐ[R] K) :=
    Finite.of_injective (fun g => g.comp π) fun g g' h => by
      ext x
      obtain ⟨a, rfl⟩ := hπ x
      exact DFunLike.congr_fun h a
  let F : Option (A ⧸ Ideal.span {e} →ₐ[R] K) → (A →ₐ[R] K) := fun o =>
    o.elim ((Algebra.ofId R K).comp σ) fun g => g.comp π
  have hF : Function.Bijective F := by
    constructor
    · rintro (_ | g) (_ | g') h
      · rfl
      · have := DFunLike.congr_fun h e
        simp [F, h1, hπe, Algebra.ofId_apply] at this
      · have := DFunLike.congr_fun h e
        simp [F, h1, hπe, Algebra.ofId_apply] at this
      · congr 1
        ext x
        obtain ⟨a, rfl⟩ := hπ x
        exact DFunLike.congr_fun h a
    · intro f
      have hfe : IsIdempotentElem (f e) := hi.map f
      rcases IsIdempotentElem.iff_eq_zero_or_one.1 hfe with h0 | h0
      · have hk : ∀ a ∈ Ideal.span {e}, f a = 0 := fun a ha => by
          obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
          rw [map_mul, h0, mul_zero]
        refine ⟨some (Ideal.Quotient.liftₐ _ f hk), ?_⟩
        ext a
        simp only [F, π, Option.elim, AlgHom.comp_apply]
        exact Ideal.Quotient.lift_mk _ _ _
      · refine ⟨none, ?_⟩
        ext a
        have := congrArg f (he a)
        rw [map_mul, map_mul, h0, mul_one, mul_one, f.commutes] at this
        simp [F, this, Algebra.ofId_apply]
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Finite.card_option]

/- English proof (translation)
Set `π : A →ₐ[R] A ⧸ Ideal.span {e}` to `Ideal.Quotient.mkₐ R _`. Establish `hπ : Function.Surjective π` using `Ideal.Quotient.mk_surjective`. Establish `hπe : π e = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)`. Use `⟨Fin.cons σ fun i => (z i).comp π, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b h`.

Establish `h0 : σ a = σ b` using `congrFun h 0`. Establish `hs : ∀ i : Fin d, z i (π a) = z i (π b)` using `fun i => congrFun h i.succ`. Establish `hab : π a = π b` using `hz.1 (funext hs)`. Establish `hmem : a - b ∈ Ideal.span {e}`. Use `Ideal.Quotient.eq.1 hab` and prove the remaining obligations.

Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 hmem`. Establish `h2 : (a - b) * e = 0`. Rewrite using `[he, map_sub, h0, sub_self, map_zero, zero_mul]`. Establish `h3 : (a - b) * e = a - b`. Rewrite using `[← hc, mul_assoc, hi.eq]`.

Conclude with `sub_eq_zero.1 (h3.symm.trans h2)`. Introduce `v`. Take `⟨b, hb⟩` from `hz.2 fun i => v i.succ`. Take `⟨a, rfl⟩` from `hπ b`. Use `⟨a * (1 - e) + algebraMap R A (v 0) * e, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `[h1]`. Establish `h2 : π (a * (1 - e) + algebraMap R A (v 0) * e) = π a`. Simplify using `only [map_add, map_mul, map_sub, map_one, hπe, sub_zero, mul_one, mul_zero, add_zero]`.

Express the relevant statement in the definitionally equal form `z i (π _) = v i.succ`. Rewrite using `[h2]`. Conclude with `congrFun hb i`.
-/
private lemma split_step [Module.Finite R A] [Algebra.Etale R A] {e : A} (σ : A →ₐ[R] R) (h1 : σ e = 1)
    (he : ∀ a, a * e = algebraMap R A (σ a) * e) (hi : IsIdempotentElem e) {d : ℕ}
    (z : Fin d → (A ⧸ Ideal.span {e} →ₐ[R] R))
    (hz : Function.Bijective fun (b : A ⧸ Ideal.span {e}) i => z i b) :
    ∃ w : Fin (d + 1) → (A →ₐ[R] R), Function.Bijective fun a i => w i a := by
  let π : A →ₐ[R] A ⧸ Ideal.span {e} := Ideal.Quotient.mkₐ R _
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hπe : π e = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  refine ⟨Fin.cons σ fun i => (z i).comp π, ?_, ?_⟩
  · intro a b h
    have h0 : σ a = σ b := congrFun h 0
    have hs : ∀ i : Fin d, z i (π a) = z i (π b) := fun i => congrFun h i.succ
    have hab : π a = π b := hz.1 (funext hs)
    have hmem : a - b ∈ Ideal.span {e} := by
      refine Ideal.Quotient.eq.1 hab
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
    have h2 : (a - b) * e = 0 := by
      rw [he, map_sub, h0, sub_self, map_zero, zero_mul]
    have h3 : (a - b) * e = a - b := by
      rw [← hc, mul_assoc, hi.eq]
    exact sub_eq_zero.1 (h3.symm.trans h2)
  · intro v
    obtain ⟨b, hb⟩ := hz.2 fun i => v i.succ
    obtain ⟨a, rfl⟩ := hπ b
    refine ⟨a * (1 - e) + algebraMap R A (v 0) * e, ?_⟩
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [h1]
    · have h2 : π (a * (1 - e) + algebraMap R A (v 0) * e) = π a := by
        simp only [map_add, map_mul, map_sub, map_one, hπe, sub_zero, mul_one, mul_zero, add_zero]
      change z i (π _) = v i.succ
      rw [h2]
      exact congrFun hb i

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero`. Introduce `A _ _ _ _ hd`. Use `⟨Fin.elim0, ?_, fun v => ⟨0, Subsingleton.elim _ _⟩⟩` and prove the remaining obligations. Establish `: Subsingleton A`.

Assume the negation of the conclusion as `hn`. Establish `: Nontrivial A` using `not_subsingleton_iff_nontrivial.1 hn`. Take `⟨m, hm⟩` from `Ideal.exists_maximal A`. Use `letI := Ideal.Quotient.field m`. Establish `h0` using `hd (AlgebraicClosure (A ⧸ m))`.

Establish `hfin` using `finite_algHom (R := R) (A := A) (AlgebraicClosure (A ⧸ m))`. Establish `hne : Nonempty (A →ₐ[R] AlgebraicClosure (A ⧸ m))` using `⟨IsScalarTower.toAlgHom R A _⟩`. Use `Nat.card_pos (α := A →ₐ[R] AlgebraicClosure (A ⧸ m))` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `fun a b _ => Subsingleton.elim a b`.

Consider the case `succ d ih`. Introduce `A _ _ _ _ hd`. Establish `hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R A))`. Introduce `p`. Establish `h0` using `hd (AlgebraicClosure p.asIdeal.ResidueField)`.

Establish `hne : Nonempty (A →ₐ[R] AlgebraicClosure p.asIdeal.ResidueField)`. Use `Nat.card_pos_iff.1 (h0 ▸ Nat.succ_pos d : 0 < Nat.card (A →ₐ[R] AlgebraicClosure p.asIdeal.ResidueField))` as an intermediate fact. Conclude with `this.1`. Take `⟨g⟩` from `hne`. Use `⟨⟨RingHom.ker g, RingHom.ker_isPrime _⟩, ?_⟩` and prove the remaining obligations.

Use extensionality with `x`. Establish `h2 : (algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)) (algebraMap R p.asIdeal.ResidueField x) = g (algebraMap R A x)`. Rewrite using `[g.commutes, ← IsScalarTower.algebraMap_apply]`. Express the relevant statement in the definitionally equal form `g (algebraMap R A x) = 0 ↔ x ∈ p.asIdeal`. Rewrite using `[← h2, map_eq_zero, Ideal.algebraMap_residueField_eq_zero]`.

Take `⟨σ⟩` from `H A inferInstance hsurj`. Take `⟨e, hi, h1, he⟩` from `exists_idem σ`. Use `quot_etale (R := R) hi` as an intermediate fact. Take `⟨z, hz⟩` from `ih (A ⧸ Ideal.span {e}) fun K _ _ _ => by`. Use `card_quot σ h1 he hi K` as an intermediate fact.

Use `hd K` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `split_step σ h1 he hi z hz`.
-/
private lemma split_alg (H : ∀ (A : Type) [CommRing A] [Algebra R A], Algebra.Etale R A →
      Function.Surjective (PrimeSpectrum.comap (algebraMap R A)) → Nonempty (A →ₐ[R] R)) (d : ℕ) :
    ∀ (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A] [Algebra.Etale R A],
      (∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra R K], Nat.card (A →ₐ[R] K) = d) →
      ∃ z : Fin d → (A →ₐ[R] R), Function.Bijective fun a i => z i a := by
  induction d with
  | zero =>
    intro A _ _ _ _ hd
    refine ⟨Fin.elim0, ?_, fun v => ⟨0, Subsingleton.elim _ _⟩⟩
    have : Subsingleton A := by
      by_contra hn
      have : Nontrivial A := not_subsingleton_iff_nontrivial.1 hn
      obtain ⟨m, hm⟩ := Ideal.exists_maximal A
      letI := Ideal.Quotient.field m
      have h0 := hd (AlgebraicClosure (A ⧸ m))
      have hfin := finite_algHom (R := R) (A := A) (AlgebraicClosure (A ⧸ m))
      have hne : Nonempty (A →ₐ[R] AlgebraicClosure (A ⧸ m)) := ⟨IsScalarTower.toAlgHom R A _⟩
      have := Nat.card_pos (α := A →ₐ[R] AlgebraicClosure (A ⧸ m))
      omega
    exact fun a b _ => Subsingleton.elim a b
  | succ d ih =>
    intro A _ _ _ _ hd
    have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R A)) := by
      intro p
      have h0 := hd (AlgebraicClosure p.asIdeal.ResidueField)
      have hne : Nonempty (A →ₐ[R] AlgebraicClosure p.asIdeal.ResidueField) := by
        have := Nat.card_pos_iff.1 (h0 ▸ Nat.succ_pos d : 0 < Nat.card (A →ₐ[R] AlgebraicClosure p.asIdeal.ResidueField))
        exact this.1
      obtain ⟨g⟩ := hne
      refine ⟨⟨RingHom.ker g, RingHom.ker_isPrime _⟩, ?_⟩
      ext x
      have h2 : (algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField))
          (algebraMap R p.asIdeal.ResidueField x) = g (algebraMap R A x) := by
        rw [g.commutes, ← IsScalarTower.algebraMap_apply]
      change g (algebraMap R A x) = 0 ↔ x ∈ p.asIdeal
      rw [← h2, map_eq_zero, Ideal.algebraMap_residueField_eq_zero]
    obtain ⟨σ⟩ := H A inferInstance hsurj
    obtain ⟨e, hi, h1, he⟩ := exists_idem σ
    have := quot_etale (R := R) hi
    obtain ⟨z, hz⟩ := ih (A ⧸ Ideal.span {e}) fun K _ _ _ => by
      have := card_quot σ h1 he hi K
      have := hd K
      omega
    exact split_step σ h1 he hi z hz

end Alg

/- English proof (translation)
Establish `hr : ∀ s, τ s ∈ g.range` using `fun s => by`. Take `⟨p, hp, h0⟩` from `hψ s`. Use `hc _ ⟨p, hp, ?_⟩` and prove the remaining obligations. Use `Polynomial.hom_eval₂ p ψ τ s` as an intermediate fact. Rewrite `this` using `[h0, map_zero, hτ]`.

Conclude with `this.symm`. Set `e : U ≃+* g.range` to `RingEquiv.ofBijective g.rangeRestrict ⟨fun a b h => hg (congrArg Subtype.val h), RingHom.rangeRestrict_surjective g⟩`. Use `⟨(e.symm : g.range →+* U).comp (τ.codRestrict g.range hr), ?_⟩` and prove the remaining obligations. Use extensionality with `s`. Use `e.apply_symm_apply (τ.codRestrict g.range hr s)` as an intermediate fact.

Conclude with `congrArg Subtype.val this`.
-/
private lemma lift_integral {U R S : Type} [CommRing U] [CommRing R] [CommRing S] (g : U →+* R)
    (hg : Function.Injective g) (hc : ∀ x : R, g.IsIntegralElem x → ∃ u, g u = x) (ψ : U →+* S)
    (hψ : ψ.IsIntegral) (τ : S →+* R) (hτ : τ.comp ψ = g) : ∃ τ' : S →+* U, g.comp τ' = τ := by
  have hr : ∀ s, τ s ∈ g.range := fun s => by
    obtain ⟨p, hp, h0⟩ := hψ s
    refine hc _ ⟨p, hp, ?_⟩
    have := Polynomial.hom_eval₂ p ψ τ s
    rw [h0, map_zero, hτ] at this
    exact this.symm
  let e : U ≃+* g.range := RingEquiv.ofBijective g.rangeRestrict
    ⟨fun a b h => hg (congrArg Subtype.val h), RingHom.rangeRestrict_surjective g⟩
  refine ⟨(e.symm : g.range →+* U).comp (τ.codRestrict g.range hr), ?_⟩
  ext s
  have := e.apply_symm_apply (τ.codRestrict g.range hr s)
  exact congrArg Subtype.val this

section Sch

open CategoryTheory Limits AlgebraicGeometry

/- English proof (translation)
Establish `: IsAffine P` using `isAffine_of_isAffineHom q`. Set `ψ : CommRingCat.of U ⟶ Γ(P, ⊤)` to `Spec.preimage (P.isoSpec.inv ≫ q)`. Establish `hψ : Spec.map ψ = P.isoSpec.inv ≫ q` using `Spec.map_preimage _`. Set `τ : Γ(P, ⊤) ⟶ CommRingCat.of R` to `Spec.preimage (t ≫ P.isoSpec.hom)`. Establish `hτ : Spec.map τ = t ≫ P.isoSpec.hom` using `Spec.map_preimage _`.

Establish `hfin : ψ.hom.Finite` using `(IsFinite.SpecMap_iff ψ).1 (by rw [hψ]; infer_instance)`. Establish `hcomp : ψ ≫ τ = CommRingCat.ofHom g` using `Spec.map_injective (by`. Rewrite using `[Spec.map_comp, hψ, hτ, Category.assoc, Iso.hom_inv_id_assoc, ht])`. Take `⟨τ', hτ'⟩` from `lift_integral g hg hc ψ.hom hfin.to_isIntegral τ.hom (congrArg CommRingCat.Hom.hom hcomp)`. Establish `h1 : CommRingCat.ofHom τ' ≫ CommRingCat.ofHom g = τ`.

Use extensionality with `a`. Conclude with `DFunLike.congr_fun hτ' a`. Establish `h2 : ψ ≫ CommRingCat.ofHom τ' = 𝟙 _`. Use extensionality with `a`. Apply `hg` to reduce the goal to its premises.

Use `DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcomp) a` as an intermediate fact. Establish `h3` using `DFunLike.congr_fun hτ' (ψ.hom a)`. Simplify using `using h3.trans this`. Use `⟨Spec.map (CommRingCat.ofHom τ') ≫ P.isoSpec.inv, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← hψ, ← Spec.map_comp, h2, Spec.map_id]`.

Rewrite using `[← Category.assoc, ← Spec.map_comp, h1, hτ, Category.assoc, Iso.hom_inv_id, Category.comp_id]`.
-/
private lemma extend_pt {U R : Type} [CommRing U] [CommRing R] (g : U →+* R)
    (hg : Function.Injective g) (hc : ∀ x : R, g.IsIntegralElem x → ∃ u, g u = x) {P : Scheme.{0}}
    (q : P ⟶ Spec (CommRingCat.of U)) [IsFinite q] (t : Spec (CommRingCat.of R) ⟶ P)
    (ht : t ≫ q = Spec.map (CommRingCat.ofHom g)) :
    ∃ t' : Spec (CommRingCat.of U) ⟶ P, t' ≫ q = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom g) ≫ t' = t := by
  have : IsAffine P := isAffine_of_isAffineHom q
  let ψ : CommRingCat.of U ⟶ Γ(P, ⊤) := Spec.preimage (P.isoSpec.inv ≫ q)
  have hψ : Spec.map ψ = P.isoSpec.inv ≫ q := Spec.map_preimage _
  let τ : Γ(P, ⊤) ⟶ CommRingCat.of R := Spec.preimage (t ≫ P.isoSpec.hom)
  have hτ : Spec.map τ = t ≫ P.isoSpec.hom := Spec.map_preimage _
  have hfin : ψ.hom.Finite := (IsFinite.SpecMap_iff ψ).1 (by rw [hψ]; infer_instance)
  have hcomp : ψ ≫ τ = CommRingCat.ofHom g := Spec.map_injective (by
    rw [Spec.map_comp, hψ, hτ, Category.assoc, Iso.hom_inv_id_assoc, ht])
  obtain ⟨τ', hτ'⟩ := lift_integral g hg hc ψ.hom hfin.to_isIntegral τ.hom
    (congrArg CommRingCat.Hom.hom hcomp)
  have h1 : CommRingCat.ofHom τ' ≫ CommRingCat.ofHom g = τ := by
    ext a
    exact DFunLike.congr_fun hτ' a
  have h2 : ψ ≫ CommRingCat.ofHom τ' = 𝟙 _ := by
    ext a
    apply hg
    have := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcomp) a
    have h3 := DFunLike.congr_fun hτ' (ψ.hom a)
    simpa using h3.trans this
  refine ⟨Spec.map (CommRingCat.ofHom τ') ≫ P.isoSpec.inv, ?_, ?_⟩
  · rw [Category.assoc, ← hψ, ← Spec.map_comp, h2, Spec.map_id]
  · rw [← Category.assoc, ← Spec.map_comp, h1, hτ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/- English proof (translation)
Establish `: IsAffine W` using `isAffine_of_isAffineHom q`. Set `ψ : CommRingCat.of R ⟶ Γ(W, ⊤)` to `Spec.preimage (W.isoSpec.inv ≫ q)`. Establish `hψ : Spec.map ψ = W.isoSpec.inv ≫ q` using `Spec.map_preimage _`. Use `letI : Algebra R Γ(W, ⊤) := ψ.hom.toAlgebra`. Establish `hfin : Module.Finite R Γ(W, ⊤)` using `(IsFinite.SpecMap_iff ψ).1 (by rw [hψ]; infer_instance)`.

Establish `het : Algebra.Etale R Γ(W, ⊤)`. Establish `h1 : Etale (Spec.map ψ)` using `by rw [hψ]; infer_instance`. Establish `h2` using `(HasRingHomProperty.Spec_iff (P := @Etale)).1 h1`. Conclude with `(RingHom.etale_algebraMap).1 h2`. Establish `Hr : ∀ (A : Type) [CommRing A] [Algebra R A], Algebra.Etale R A → Function.Surjective (PrimeSpectrum.comap (algebraMap R A)) → Nonempty (A →ₐ[R] R)`.

Introduce `A _ _ hA hs`. Establish `h1 : Etale (Spec.map (CommRingCat.ofHom (algebraMap R A)))` using `(HasRingHomProperty.Spec_iff (P := @Etale)).2 ((RingHom.etale_algebraMap).2 hA)`. Establish `h2 : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R A)))` using `⟨hs⟩`. Take `⟨s, hs⟩` from `H _ _ h1 h2`. Set `σ : CommRingCat.of A ⟶ CommRingCat.of R` to `Spec.preimage s`.

Establish `hσ : Spec.map σ = s` using `Spec.map_preimage _`. Establish `h3 : CommRingCat.ofHom (algebraMap R A) ≫ σ = 𝟙 _` using `Spec.map_injective (by`. Rewrite using `[Spec.map_comp, hσ, hs, Spec.map_id])`. Conclude with `⟨{ σ.hom with commutes' := fun r => DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h3) r }⟩`. Establish `hc : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra R K], Nat.card (Γ(W, ⊤) →ₐ[R] K) = d`.

Introduce `K _ _ _`. Rewrite using `[← hd K]`. Use `Nat.card_congr (Equiv.ofBijective (fun f => ⟨Spec.map (CommRingCat.ofHom f.toRingHom) ≫ W.isoSpec.inv, ?_⟩) ⟨?_, ?_⟩)` and prove the remaining obligations. Rewrite using `[Category.assoc, ← hψ, ← Spec.map_comp]`. Use `congr 1`.

Use extensionality with `r`. Conclude with `f.commutes r`. Introduce `f f' h`. Establish `h1` using `(cancel_mono W.isoSpec.inv).1 (congrArg Subtype.val h)`. Establish `h2` using `Spec.map_injective h1`.

Use extensionality with `a`. Conclude with `DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h2) a`. Introduce and unpack `⟨w, hw⟩`. Set `φ : Γ(W, ⊤) ⟶ CommRingCat.of K` to `Spec.preimage (w ≫ W.isoSpec.hom)`. Establish `hφ : Spec.map φ = w ≫ W.isoSpec.hom` using `Spec.map_preimage _`.

Establish `h3 : ψ ≫ φ = CommRingCat.ofHom (algebraMap R K)` using `Spec.map_injective (by`. Rewrite using `[Spec.map_comp, hψ, hφ, Category.assoc, Iso.hom_inv_id_assoc, hw])`. Use `⟨{ φ.hom with commutes' := fun r => DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h3) r }, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Spec.map (CommRingCat.ofHom φ.hom) ≫ W.isoSpec.inv = w`.

Rewrite using `[CommRingCat.ofHom_hom, hφ, Category.assoc, Iso.hom_inv_id, Category.comp_id]`. Take `⟨z, hz⟩` from `split_alg Hr d Γ(W, ⊤) hc`. Use `⟨fun i => Spec.map (CommRingCat.ofHom (z i).toRingHom) ≫ W.isoSpec.inv, fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← hψ, ← Spec.map_comp, ← Spec.map_id]`. Use `congr 1`.

Use extensionality with `r`. Conclude with `(z i).commutes r`. Set `Φ : Γ(W, ⊤) →+* (Fin d → R)` to `Pi.ringHom fun i => (z i).toRingHom`. Establish `hΦ : IsIso (CommRingCat.ofHom Φ)` using `(ConcreteCategory.isIso_iff_bijective _).2 hz`. Establish `he : Sigma.desc (fun i => Spec.map (CommRingCat.ofHom (z i).toRingHom) ≫ W.isoSpec.inv) = sigmaSpec (fun _ : Fin d => CommRingCat.of R) ≫ Spec.map (CommRingCat.ofHom Φ) ≫ W.isoSpec.inv`.

Use `Sigma.hom_ext _ _ fun i => ?_` and prove the remaining obligations. Rewrite using `[Sigma.ι_desc, ι_sigmaSpec_assoc, ← Category.assoc, ← Spec.map_comp]`. Both sides reduce to the same expression. Rewrite using `[he]`. Use `infer_instance`.
-/
private lemma split_sch {R : Type} [CommRing R]
    (H : ∀ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), Etale f → Surjective f → ∃ s, s ≫ f = 𝟙 _)
    (d : ℕ) {W : Scheme.{0}} (q : W ⟶ Spec (CommRingCat.of R)) [IsFinite q] [Etale q]
    (hd : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra R K],
      Nat.card {w : Spec (CommRingCat.of K) ⟶ W // w ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R K))} = d) :
    ∃ s : Fin d → (Spec (CommRingCat.of R) ⟶ W), (∀ i, s i ≫ q = 𝟙 _) ∧ IsIso (Sigma.desc s) := by
  have : IsAffine W := isAffine_of_isAffineHom q
  let ψ : CommRingCat.of R ⟶ Γ(W, ⊤) := Spec.preimage (W.isoSpec.inv ≫ q)
  have hψ : Spec.map ψ = W.isoSpec.inv ≫ q := Spec.map_preimage _
  letI : Algebra R Γ(W, ⊤) := ψ.hom.toAlgebra
  have hfin : Module.Finite R Γ(W, ⊤) := (IsFinite.SpecMap_iff ψ).1 (by rw [hψ]; infer_instance)
  have het : Algebra.Etale R Γ(W, ⊤) := by
    have h1 : Etale (Spec.map ψ) := by rw [hψ]; infer_instance
    have h2 := (HasRingHomProperty.Spec_iff (P := @Etale)).1 h1
    exact (RingHom.etale_algebraMap).1 h2
  have Hr : ∀ (A : Type) [CommRing A] [Algebra R A], Algebra.Etale R A →
      Function.Surjective (PrimeSpectrum.comap (algebraMap R A)) → Nonempty (A →ₐ[R] R) := by
    intro A _ _ hA hs
    have h1 : Etale (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
      (HasRingHomProperty.Spec_iff (P := @Etale)).2 ((RingHom.etale_algebraMap).2 hA)
    have h2 : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R A))) := ⟨hs⟩
    obtain ⟨s, hs⟩ := H _ _ h1 h2
    let σ : CommRingCat.of A ⟶ CommRingCat.of R := Spec.preimage s
    have hσ : Spec.map σ = s := Spec.map_preimage _
    have h3 : CommRingCat.ofHom (algebraMap R A) ≫ σ = 𝟙 _ := Spec.map_injective (by
      rw [Spec.map_comp, hσ, hs, Spec.map_id])
    exact ⟨{ σ.hom with
      commutes' := fun r => DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h3) r }⟩
  have hc : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra R K], Nat.card (Γ(W, ⊤) →ₐ[R] K) = d := by
    intro K _ _ _
    rw [← hd K]
    refine Nat.card_congr (Equiv.ofBijective (fun f => ⟨Spec.map (CommRingCat.ofHom f.toRingHom) ≫ W.isoSpec.inv, ?_⟩) ⟨?_, ?_⟩)
    · rw [Category.assoc, ← hψ, ← Spec.map_comp]
      congr 1
      ext r
      exact f.commutes r
    · intro f f' h
      have h1 := (cancel_mono W.isoSpec.inv).1 (congrArg Subtype.val h)
      have h2 := Spec.map_injective h1
      ext a
      exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h2) a
    · rintro ⟨w, hw⟩
      let φ : Γ(W, ⊤) ⟶ CommRingCat.of K := Spec.preimage (w ≫ W.isoSpec.hom)
      have hφ : Spec.map φ = w ≫ W.isoSpec.hom := Spec.map_preimage _
      have h3 : ψ ≫ φ = CommRingCat.ofHom (algebraMap R K) := Spec.map_injective (by
        rw [Spec.map_comp, hψ, hφ, Category.assoc, Iso.hom_inv_id_assoc, hw])
      refine ⟨{ φ.hom with
        commutes' := fun r => DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h3) r }, ?_⟩
      apply Subtype.ext
      change Spec.map (CommRingCat.ofHom φ.hom) ≫ W.isoSpec.inv = w
      rw [CommRingCat.ofHom_hom, hφ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨z, hz⟩ := split_alg Hr d Γ(W, ⊤) hc
  refine ⟨fun i => Spec.map (CommRingCat.ofHom (z i).toRingHom) ≫ W.isoSpec.inv, fun i => ?_, ?_⟩
  · rw [Category.assoc, ← hψ, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext r
    exact (z i).commutes r
  · let Φ : Γ(W, ⊤) →+* (Fin d → R) := Pi.ringHom fun i => (z i).toRingHom
    have hΦ : IsIso (CommRingCat.ofHom Φ) :=
      (ConcreteCategory.isIso_iff_bijective _).2 hz
    have he : Sigma.desc (fun i => Spec.map (CommRingCat.ofHom (z i).toRingHom) ≫ W.isoSpec.inv) =
        sigmaSpec (fun _ : Fin d => CommRingCat.of R) ≫ Spec.map (CommRingCat.ofHom Φ) ≫ W.isoSpec.inv := by
      refine Sigma.hom_ext _ _ fun i => ?_
      rw [Sigma.ι_desc, ι_sigmaSpec_assoc, ← Category.assoc, ← Spec.map_comp]
      rfl
    rw [he]
    infer_instance

end Sch

end UpperTheory.Ru.crystallineComparison

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.crystallineComparison in

/- English proof (translation)
Introduce `l hl Y T U _ hnz hcl hsec y`. Set `R` to `Localization.Away (l : U)`. Set `x : Spec (CommRingCat.of R) ⟶ Y` to `awayPt l U ≫ y`. Establish `hunit : IsUnit ((l : ℕ) : R)`. Use `IsLocalization.Away.algebraMap_isUnit (S := R) (l : U)` as an intermediate fact.

Simplify using `using this`. Set `V : Y.Opens` to `Y.basicOpen (l : Γ(Y, ⊤))`. Establish `hV : Set.range x ⊆ Set.range V.ι`. Establish `hu : IsUnit (x.appTop (l : Γ(Y, ⊤)))`. Use `hunit.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom` as an intermediate fact.

Rewrite `this` using `[map_natCast]`. Rewrite using `[map_natCast]`. Conclude with `this`. Establish `hpre : x ⁻¹ᵁ V = ⊤`. Rewrite using `[Scheme.preimage_basicOpen]`.

Conclude with `Scheme.basicOpen_of_isUnit _ hu`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨a, rfl⟩`. Establish `: a ∈ x ⁻¹ᵁ V` using `hpre ▸ trivial`. Conclude with `this`.

Set `x' : Spec (CommRingCat.of R) ⟶ V.toScheme` to `IsOpenImmersion.lift V.ι x hV`. Establish `hx' : x' ≫ V.ι = x` using `IsOpenImmersion.lift_fac _ _ _`. Establish `sq : IsPullback (pullback.fst (T.p ∣_ V) x' ≫ (T.p ⁻¹ᵁ V).ι) (pullback.snd (T.p ∣_ V) x') T.p x`. Rewrite using `[← hx']`. Conclude with `(IsPullback.of_hasPullback (T.p ∣_ V) x').paste_horiz (isPullback_morphismRestrict T.p V).flip`.

Establish `het0 : Etale (T.p ∣_ V)` using `T.et`. Establish `het1 : Etale (pullback.snd (T.p ∣_ V) x')` using `inferInstance`. Establish `het : Etale (pullback.snd T.p x)`. Establish `: pullback.snd T.p x = sq.isoPullback.inv ≫ pullback.snd (T.p ∣_ V) x'`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Use `infer_instance`. Establish `hfin0 : IsFinite T.p` using `T.fin`. Establish `hdeg : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra R K], Nat.card {w : Spec (CommRingCat.of K) ⟶ pullback T.p x // w ≫ pullback.snd T.p x = Spec.map (CommRingCat.ofHom (algebraMap R K))} = T.d`. Introduce `K _ _ _`.

Establish `hl0 : ((l : ℕ) : K) ≠ 0`. Use `hunit.map (algebraMap R K)` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Conclude with `this.ne_zero`. Rewrite using `[← T.deg K hl0 (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ x)]`.

Use `Nat.card_congr (Equiv.ofBijective (fun w => ⟨w.1 ≫ pullback.fst T.p x, ?_⟩) ⟨?_, ?_⟩)` and prove the remaining obligations. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, w.2]`. Introduce and unpack `⟨w, hw⟩ ⟨w', hw'⟩ h`. Apply `Subtype.ext` to reduce the goal to its premises. Use `pullback.hom_ext (congrArg Subtype.val h) (hw.trans hw'.symm)` and prove the remaining obligations.

Introduce and unpack `⟨w, hw⟩`. Conclude with `⟨⟨pullback.lift w _ hw, pullback.lift_snd _ _ _⟩, Subtype.ext (pullback.lift_fst _ _ _)⟩`. Take `⟨s, hs, hiso⟩` from `split_sch hsec T.d (pullback.snd T.p x) hdeg`. Establish `hinj : Function.Injective (algebraMap U R)` using `IsLocalization.injective R (Submonoid.powers_le.2 hnz)`. Establish `hext : ∀ i, ∃ t' : Spec (CommRingCat.of U) ⟶ pullback T.p y, t' ≫ pullback.snd T.p y = 𝟙 _ ∧ awayPt l U ≫ t' ≫ pullback.fst T.p y = s i ≫ pullback.fst T.p x`.

Introduce `i`. Establish `hc : s i ≫ pullback.fst T.p x ≫ T.p = awayPt l U ≫ y`. Rewrite using `[pullback.condition, ← Category.assoc, hs, Category.id_comp]`. Take `⟨t', h1, h2⟩` from `extend_pt (algebraMap U R) hinj hcl (pullback.snd T.p y) (pullback.lift (s i ≫ pullback.fst T.p x) (awayPt l U) (by rw [Category.assoc, hc])) (pullback.lift_snd _ _ _)`. Use `⟨t', h1, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Category.assoc, h2, pullback.lift_fst]`. Use `choose t' ht1 ht2 using hext`. Use `⟨fun i => t' i ≫ pullback.fst T.p y, fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, ht1, Category.id_comp]`. Establish `hz : ∀ i, (awayPt l U ≫ t' i ≫ pullback.fst T.p y) ≫ T.p = awayPt l U ≫ y` using `fun i => by`.

Rewrite using `[ht2, Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]`. Use `⟨hz, ?_⟩` and prove the remaining obligations. Use `hiso using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Use `pullback.hom_ext ?_ ?_` and prove the remaining obligations.

Rewrite using `[pullback.lift_fst]`. Conclude with `ht2 i`. Rewrite using `[pullback.lift_snd, hs]`.
-/
theorem UpperTheory.Ru.crystallineComparison.splitEx :
    UpperTheory.Ru.crystallineComparison.SplitEx := by
  intro l hl Y T U _ hnz hcl hsec y
  let R := Localization.Away (l : U)
  let x : Spec (CommRingCat.of R) ⟶ Y := awayPt l U ≫ y
  have hunit : IsUnit ((l : ℕ) : R) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := R) (l : U)
    simpa using this

  let V : Y.Opens := Y.basicOpen (l : Γ(Y, ⊤))
  have hV : Set.range x ⊆ Set.range V.ι := by
    have hu : IsUnit (x.appTop (l : Γ(Y, ⊤))) := by
      have := hunit.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      rw [map_natCast] at this
      rw [map_natCast]
      exact this
    have hpre : x ⁻¹ᵁ V = ⊤ := by
      rw [Scheme.preimage_basicOpen]
      exact Scheme.basicOpen_of_isUnit _ hu
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨a, rfl⟩
    have : a ∈ x ⁻¹ᵁ V := hpre ▸ trivial
    exact this
  let x' : Spec (CommRingCat.of R) ⟶ V.toScheme := IsOpenImmersion.lift V.ι x hV
  have hx' : x' ≫ V.ι = x := IsOpenImmersion.lift_fac _ _ _
  have sq : IsPullback (pullback.fst (T.p ∣_ V) x' ≫ (T.p ⁻¹ᵁ V).ι) (pullback.snd (T.p ∣_ V) x') T.p x := by
    rw [← hx']
    exact (IsPullback.of_hasPullback (T.p ∣_ V) x').paste_horiz (isPullback_morphismRestrict T.p V).flip
  have het0 : Etale (T.p ∣_ V) := T.et
  have het1 : Etale (pullback.snd (T.p ∣_ V) x') := inferInstance
  have het : Etale (pullback.snd T.p x) := by
    have : pullback.snd T.p x = sq.isoPullback.inv ≫ pullback.snd (T.p ∣_ V) x' := by
      simp
    rw [this]
    infer_instance
  have hfin0 : IsFinite T.p := T.fin
  have hdeg : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra R K],
      Nat.card {w : Spec (CommRingCat.of K) ⟶ pullback T.p x //
        w ≫ pullback.snd T.p x = Spec.map (CommRingCat.ofHom (algebraMap R K))} = T.d := by
    intro K _ _ _
    have hl0 : ((l : ℕ) : K) ≠ 0 := by
      have := hunit.map (algebraMap R K)
      rw [map_natCast] at this
      exact this.ne_zero
    rw [← T.deg K hl0 (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ x)]
    refine Nat.card_congr (Equiv.ofBijective (fun w => ⟨w.1 ≫ pullback.fst T.p x, ?_⟩) ⟨?_, ?_⟩)
    · rw [Category.assoc, pullback.condition, ← Category.assoc, w.2]
    · rintro ⟨w, hw⟩ ⟨w', hw'⟩ h
      apply Subtype.ext
      refine pullback.hom_ext (congrArg Subtype.val h) (hw.trans hw'.symm)
    · rintro ⟨w, hw⟩
      exact ⟨⟨pullback.lift w _ hw, pullback.lift_snd _ _ _⟩, Subtype.ext (pullback.lift_fst _ _ _)⟩
  obtain ⟨s, hs, hiso⟩ := split_sch hsec T.d (pullback.snd T.p x) hdeg
  have hinj : Function.Injective (algebraMap U R) :=
    IsLocalization.injective R (Submonoid.powers_le.2 hnz)
  have hext : ∀ i, ∃ t' : Spec (CommRingCat.of U) ⟶ pullback T.p y,
      t' ≫ pullback.snd T.p y = 𝟙 _ ∧ awayPt l U ≫ t' ≫ pullback.fst T.p y = s i ≫ pullback.fst T.p x := by
    intro i
    have hc : s i ≫ pullback.fst T.p x ≫ T.p = awayPt l U ≫ y := by
      rw [pullback.condition, ← Category.assoc, hs, Category.id_comp]
    obtain ⟨t', h1, h2⟩ := extend_pt (algebraMap U R) hinj hcl (pullback.snd T.p y)
      (pullback.lift (s i ≫ pullback.fst T.p x) (awayPt l U) (by rw [Category.assoc, hc]))
      (pullback.lift_snd _ _ _)
    refine ⟨t', h1, ?_⟩
    rw [← Category.assoc, h2, pullback.lift_fst]
  choose t' ht1 ht2 using hext
  refine ⟨fun i => t' i ≫ pullback.fst T.p y, fun i => ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, ht1, Category.id_comp]
  · have hz : ∀ i, (awayPt l U ≫ t' i ≫ pullback.fst T.p y) ≫ T.p = awayPt l U ≫ y := fun i => by
      rw [ht2, Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
    refine ⟨hz, ?_⟩
    convert hiso using 2
    funext i
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst]
      exact ht2 i
    · rw [pullback.lift_snd, hs]

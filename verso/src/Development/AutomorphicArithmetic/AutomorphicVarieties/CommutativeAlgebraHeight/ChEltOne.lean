import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.BcChiTmul

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section
variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)

/- English proof (translation)
Establish `h` using `D.nat (Polynomial S) (Polynomial T) (Polynomial.mapAlgHom f) (Polynomial.X ⊗ₜ 1 - Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S (Polynomial S)) (AlgHom.id A E) y)`. Use `Eq.trans ?_ h` and prove the remaining obligations. Unfold `Det.chiS`. Use `congr 1`. Rewrite using `[map_sub]`.

Use `congr 1`. Simplify using the standard rewrite rules. Use `clear h`. Proceed by induction on `y with`. Consider the case `zero => simp`.

Consider the case `tmul s x => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
private theorem chiS_map (S T : Type) [CommRing S] [Algebra A S] [CommRing T] [Algebra A T] (f : S →ₐ[A] T)
    (y : S ⊗[A] E) :
    D.chiS T (Algebra.TensorProduct.map f (AlgHom.id A E) y) = (D.chiS S y).map (f : S →+* T) := by
  have h := D.nat (Polynomial S) (Polynomial T) (Polynomial.mapAlgHom f) (Polynomial.X ⊗ₜ 1 -
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S (Polynomial S)) (AlgHom.id A E) y)
  refine Eq.trans ?_ h
  unfold Det.chiS
  congr 1
  rw [map_sub]
  congr 1
  · simp
  · clear h
    induction y with
    | zero => simp
    | tmul s x => simp
    | add a b ha hb => simp only [map_add, ha, hb]

/- English proof (translation)
Rewrite using `[chiS_map]`. Generalize the expression as in `D.chiS S y = p`. Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp only [Polynomial.map_add, map_add, hp, hq]`. Consider the case `monomial k a`.

Simplify using `[Polynomial.aeval_monomial, Algebra.TensorProduct.algebraMap_apply]`.
-/
private theorem F_map (S T : Type) [CommRing S] [Algebra A S] [CommRing T] [Algebra A T] (f : S →ₐ[A] T)
    (y : S ⊗[A] E) :
    Polynomial.aeval (Algebra.TensorProduct.map f (AlgHom.id A E) y)
      (D.chiS T (Algebra.TensorProduct.map f (AlgHom.id A E) y)) =
      Algebra.TensorProduct.map f (AlgHom.id A E) (Polynomial.aeval y (D.chiS S y)) := by
  rw [chiS_map]
  generalize D.chiS S y = p
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.map_add, map_add, hp, hq]
  | monomial k a =>
    simp [Polynomial.aeval_monomial, Algebra.TensorProduct.algebraMap_apply]

/- English proof (translation)
Establish `hw : ∃ s : Finset (ι →₀ ℕ), ∀ t, s ⊆ t → w = ∑ α ∈ t, (MvPolynomial.monomial α (1 : A)) ⊗ₜ[A] TensorProduct.lid A E ((MvPolynomial.lcoeff A α).rTensor E w)` using `by clear h`. Proceed by induction on `w with`. Consider the case `zero => exact ⟨∅, by simp⟩`. Consider the case `add a b ha hb`. Take `⟨s, hs⟩` from `ha`.

Take `⟨s', hs'⟩` from `hb`. Use `⟨s ∪ s', fun t ht => ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, tmul_add, Finset.sum_add_distrib]`. Rewrite using `[← hs t (Finset.subset_union_left.trans ht), ← hs' t (Finset.subset_union_right.trans ht)]`. Consider the case `tmul p z`.

Use `⟨p.support, fun t ht => ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, MvPolynomial.lcoeff_apply, ← smul_tmul, ← sum_tmul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]`. Use `congr 1`. Use `conv_lhs => rw [p.as_sum]`. Use `Finset.sum_subset ht fun α _ hα => ?_` and prove the remaining obligations.

Rewrite using `[MvPolynomial.notMem_support_iff.1 hα, map_zero]`. Take `⟨s, hs⟩` from `hw`. Rewrite using `[hs s le_rfl, map_sum]`. Use `Submodule.sum_mem _ fun α _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.map_tmul, ← mul_one (f _), ← smul_eq_mul, ← smul_tmul']`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h α, rfl⟩)`.
-/
private theorem expand {ι : Type} (S : Type) [CommRing S] [Algebra A S] (f : MvPolynomial ι A →ₐ[A] S)
    (N : Set E) (w : MvPolynomial ι A ⊗[A] E)
    (h : ∀ α, TensorProduct.lid A E ((MvPolynomial.lcoeff A α).rTensor E w) ∈ N) :
    Algebra.TensorProduct.map f (AlgHom.id A E) w ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' N) := by
  classical
  have hw : ∃ s : Finset (ι →₀ ℕ), ∀ t, s ⊆ t → w = ∑ α ∈ t, (MvPolynomial.monomial α (1 : A)) ⊗ₜ[A]
      TensorProduct.lid A E ((MvPolynomial.lcoeff A α).rTensor E w) := by
    clear h
    induction w with
    | zero => exact ⟨∅, by simp⟩
    | add a b ha hb =>
      obtain ⟨s, hs⟩ := ha
      obtain ⟨s', hs'⟩ := hb
      refine ⟨s ∪ s', fun t ht => ?_⟩
      simp only [map_add, tmul_add, Finset.sum_add_distrib]
      rw [← hs t (Finset.subset_union_left.trans ht), ← hs' t (Finset.subset_union_right.trans ht)]
    | tmul p z =>
      refine ⟨p.support, fun t ht => ?_⟩
      simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, MvPolynomial.lcoeff_apply, ← smul_tmul,
        ← sum_tmul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      congr 1
      conv_lhs => rw [p.as_sum]
      refine Finset.sum_subset ht fun α _ hα => ?_
      rw [MvPolynomial.notMem_support_iff.1 hα, map_zero]
  obtain ⟨s, hs⟩ := hw
  rw [hs s le_rfl, map_sum]
  refine Submodule.sum_mem _ fun α _ => ?_
  rw [Algebra.TensorProduct.map_tmul, ← mul_one (f _), ← smul_eq_mul, ← smul_tmul']
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h α, rfl⟩)

/- English proof (translation)
Take `⟨k, s, x, rfl⟩` from `TensorProduct.exists_sum_tmul_eq y`. Establish `: ∑ j, s j ⊗ₜ[A] x j = Algebra.TensorProduct.map (MvPolynomial.aeval s) (AlgHom.id A E) (Det.gen (A` using `A) x) := by`. Simplify using `[Det.gen, map_sum]`. Rewrite using `[this, F_map]`. Conclude with `expand S _ _ _ fun α => TwoSidedIdeal.subset_span ⟨k, x, α, rfl⟩`.
-/
private theorem part1 (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] E) :
    Polynomial.aeval y (D.chiS S y) ∈
      Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (D.CH : Set E)) := by
  obtain ⟨k, s, x, rfl⟩ := TensorProduct.exists_sum_tmul_eq y
  have : ∑ j, s j ⊗ₜ[A] x j =
      Algebra.TensorProduct.map (MvPolynomial.aeval s) (AlgHom.id A E) (Det.gen (A := A) x) := by
    simp [Det.gen, map_sum]
  rw [this, F_map]
  exact expand S _ _ _ fun α => TwoSidedIdeal.subset_span ⟨k, x, α, rfl⟩

/- English proof (translation)
It suffices to establish `H : ∀ p : P, g.rTensor E (p • w) ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' N) by`. Simplify using `using H 1`. Proceed by induction on `h using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨z, hz, rfl⟩` from `hx`.

Introduce `p`. Rewrite using `[smul_tmul', LinearMap.rTensor_tmul, ← mul_one (g _), ← smul_eq_mul, ← smul_tmul']`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hz, rfl⟩)`. Consider the case `zero => intro p`. Simplify using the standard rewrite rules.

Consider the case `add x y _ _ hx hy => intro p`. Rewrite using `[smul_add, map_add]`. Conclude with `add_mem (hx p) (hy p)`. Consider the case `smul a x _ hx => intro p`. Rewrite using `[smul_smul]`.

Conclude with `hx _`.
-/
private theorem rT_mem (P S : Type) [CommRing P] [Algebra A P] [CommRing S] [Algebra A S] (g : P →ₗ[A] S)
    (N : Set E) (w : P ⊗[A] E) (h : w ∈ Submodule.span P ((fun z : E => (1 : P) ⊗ₜ[A] z) '' N)) :
    g.rTensor E w ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' N) := by
  suffices H : ∀ p : P, g.rTensor E (p • w) ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' N) by
    simpa using H 1
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    intro p
    rw [smul_tmul', LinearMap.rTensor_tmul, ← mul_one (g _), ← smul_eq_mul, ← smul_tmul']
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hz, rfl⟩)
  | zero => intro p; simp
  | add x y _ _ hx hy => intro p; rw [smul_add, map_add]; exact add_mem (hx p) (hy p)
  | smul a x _ hx => intro p; rw [smul_smul]; exact hx _

/- English proof (translation)
Unfold `Det.chElt`. Generalize the expression as in `Det.gen (A := S) x = y`. Establish `h1 : (D.baseChange S).chiS (MvPolynomial (Fin k) S) y = D.chiS _ (Det.cancel A E S (MvPolynomial (Fin k) S) y)`. Unfold `Det.chiS`. Rewrite using `[(d_bc D S).1]`.

Use `congr 1`. Rewrite using `[map_sub]`. Use `congr 1`. Rewrite using `[Algebra.TensorProduct.one_def, Det.cancel_tmul]`. Simplify using the standard rewrite rules.

Proceed by induction on `y with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul s y`. Proceed by induction on `y with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [tmul_add, map_add, ha, hb]`. Consider the case `tmul b z => simp [Det.cancel_tmul]`. Rewrite using `[h1, Polynomial.aeval_algHom_apply]`. Generalize the expression as in `Polynomial.aeval y (D.chiS _ (Det.cancel A E S (MvPolynomial (Fin k) S) y)) = w`.

Proceed by induction on `w with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul s y`. Proceed by induction on `y with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [tmul_add, map_add, ha, hb]`. Consider the case `tmul b z`. Rewrite using `[Det.cancel_tmul, mul_comm]`. Simplify using `[smul_tmul', MvPolynomial.coeff_C_mul, mul_comm b]`.
-/
private theorem chElt_bc (S : Type) [CommRing S] [Algebra A S] {k : ℕ} (x : Fin k → S ⊗[A] E) (α : Fin k →₀ ℕ) :
    (D.baseChange S).chElt x α = ((MvPolynomial.lcoeff S α).restrictScalars A).rTensor E
      (Polynomial.aeval (Det.cancel A E S (MvPolynomial (Fin k) S) (Det.gen x))
        (D.chiS _ (Det.cancel A E S (MvPolynomial (Fin k) S) (Det.gen x)))) := by
  unfold Det.chElt
  generalize Det.gen (A := S) x = y
  have h1 : (D.baseChange S).chiS (MvPolynomial (Fin k) S) y =
      D.chiS _ (Det.cancel A E S (MvPolynomial (Fin k) S) y) := by
    unfold Det.chiS
    rw [(d_bc D S).1]
    congr 1
    rw [map_sub]
    congr 1
    · rw [Algebra.TensorProduct.one_def, Det.cancel_tmul]; simp
    · induction y with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul s y =>
        induction y with
        | zero => simp
        | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
        | tmul b z => simp [Det.cancel_tmul]
  rw [h1, Polynomial.aeval_algHom_apply]
  generalize Polynomial.aeval y (D.chiS _ (Det.cancel A E S (MvPolynomial (Fin k) S) y)) = w
  induction w with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul s y =>
    induction y with
    | zero => simp
    | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
    | tmul b z =>
      rw [Det.cancel_tmul, mul_comm]
      simp [smul_tmul', MvPolynomial.coeff_C_mul, mul_comm b]

/- English proof (translation)
Rewrite using `[chElt_bc]`. Establish `: Det.cancel A E S (MvPolynomial (Fin k) S) (Det.gen fun i => (1 : S) ⊗ₜ[A] x i) = Algebra.TensorProduct.map (MvPolynomial.mapAlgHom (Algebra.ofId A S)) (AlgHom.id A E) (Det.gen (A` using `A) x) := by`. Simplify using `[Det.gen, map_sum, Det.cancel_tmul]`. Rewrite using `[this, F_map]`. Unfold `Det.chElt`.

Generalize the expression as in `Polynomial.aeval (Det.gen (A := A) x) (D.chiS (MvPolynomial (Fin k) A) (Det.gen x)) = w`. Proceed by induction on `w with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, tmul_add, ha, hb]`. Consider the case `tmul s y`.

Simplify using `[MvPolynomial.coeff_map, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, smul_tmul]`.
-/
private theorem chElt_one (S : Type) [CommRing S] [Algebra A S] {k : ℕ} (x : Fin k → E) (α : Fin k →₀ ℕ) :
    (D.baseChange S).chElt (fun i => (1 : S) ⊗ₜ[A] x i) α = (1 : S) ⊗ₜ[A] D.chElt x α := by
  rw [chElt_bc]
  have : Det.cancel A E S (MvPolynomial (Fin k) S) (Det.gen fun i => (1 : S) ⊗ₜ[A] x i) =
      Algebra.TensorProduct.map (MvPolynomial.mapAlgHom (Algebra.ofId A S)) (AlgHom.id A E)
        (Det.gen (A := A) x) := by
    simp [Det.gen, map_sum, Det.cancel_tmul]
  rw [this, F_map]
  unfold Det.chElt
  generalize Polynomial.aeval (Det.gen (A := A) x) (D.chiS (MvPolynomial (Fin k) A) (Det.gen x)) = w
  induction w with
  | zero => simp
  | add a b ha hb => simp only [map_add, tmul_add, ha, hb]
  | tmul s y =>
    simp [MvPolynomial.coeff_map, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, smul_tmul]

/- English proof (translation)
Proceed by induction on `h using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨z, hz, rfl⟩` from `hx`. Proceed by induction on `u with`. Consider the case `zero => simp`.

Consider the case `add a b ha hb => rw [add_mul, mul_add]`. Conclude with `⟨add_mem ha.1 hb.1, add_mem ha.2 hb.2⟩`. Consider the case `tmul s e`. Establish `key : ∀ t ∈ I, s ⊗ₜ[A] t ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (I : Set E))`. Introduce `t ht`.

Rewrite using `[← mul_one s, ← smul_eq_mul, ← smul_tmul']`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ht, rfl⟩)`. Simplify using `only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Conclude with `⟨key _ (I.mul_mem_left _ _ hz), key _ (I.mul_mem_right _ _ hz)⟩`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [add_mul, mul_add]`. Conclude with `⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩`. Consider the case `smul a x _ hx`. Rewrite using `[mul_smul_comm, smul_mul_assoc]`. Conclude with `⟨Submodule.smul_mem _ _ hx.1, Submodule.smul_mem _ _ hx.2⟩`.
-/
private theorem span_mul (S : Type) [CommRing S] [Algebra A S] (I : TwoSidedIdeal E) (w : S ⊗[A] E)
    (h : w ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (I : Set E))) (u : S ⊗[A] E) :
    u * w ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (I : Set E)) ∧
    w * u ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (I : Set E)) := by
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    induction u with
    | zero => simp
    | add a b ha hb => rw [add_mul, mul_add]; exact ⟨add_mem ha.1 hb.1, add_mem ha.2 hb.2⟩
    | tmul s e =>
      have key : ∀ t ∈ I, s ⊗ₜ[A] t ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (I : Set E)) := by
        intro t ht
        rw [← mul_one s, ← smul_eq_mul, ← smul_tmul']
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ht, rfl⟩)
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      exact ⟨key _ (I.mul_mem_left _ _ hz), key _ (I.mul_mem_right _ _ hz)⟩
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul, mul_add]; exact ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
  | smul a x _ hx =>
    rw [mul_smul_comm, smul_mul_assoc]
    exact ⟨Submodule.smul_mem _ _ hx.1, Submodule.smul_mem _ _ hx.2⟩

/- English proof (translation)
Use extensionality with `w`. Simplify using `only [SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Unfold `Det.CH at h`.

Proceed by induction on `h using TwoSidedIdeal.span_induction with`. Consider the case `mem x hx`. Take `⟨k, x, α, rfl⟩` from `hx`. Rewrite using `[chElt_bc]`. Conclude with `rT_mem _ _ _ _ _ (part1 D _ _)`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`. Consider the case `neg x _ hx => exact neg_mem hx`. Consider the case `left_absorb a x _ hx => exact (span_mul S _ _ hx a).1`. Consider the case `right_absorb b x _ hx => exact (span_mul S _ _ hx b).2`.

Introduce `h`. Proceed by induction on `h using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨z, hz, rfl⟩` from `hx`. Express the relevant statement in the definitionally equal form `z ∈ TwoSidedIdeal.span _ at hz`.

Proceed by induction on `hz using TwoSidedIdeal.span_induction with`. Consider the case `mem x hx`. Take `⟨k, x, α, rfl⟩` from `hx`. Conclude with `TwoSidedIdeal.subset_span ⟨k, _, α, (chElt_one D S x α).symm⟩`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => simp only [tmul_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => simp only [tmul_neg]`. Conclude with `neg_mem hx`. Consider the case `left_absorb a x _ hx`.

Use `TwoSidedIdeal.mul_mem_left _ ((1 : S) ⊗ₜ[A] a) _ hx` as an intermediate fact. Simplify using `using this`. Consider the case `right_absorb b x _ hx`. Use `TwoSidedIdeal.mul_mem_right _ _ ((1 : S) ⊗ₜ[A] b) hx` as an intermediate fact. Simplify using `using this`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`. Consider the case `smul a x _ hx => rw [Algebra.smul_def]`. Conclude with `TwoSidedIdeal.mul_mem_left _ _ _ hx`.
-/
private theorem part2 (S : Type) [CommRing S] [Algebra A S] :
    ((D.baseChange S).CH : Set (S ⊗[A] E)) =
      Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (D.CH : Set E)) := by
  ext w
  simp only [SetLike.mem_coe]
  constructor
  · intro h
    unfold Det.CH at h
    induction h using TwoSidedIdeal.span_induction with
    | mem x hx =>
      obtain ⟨k, x, α, rfl⟩ := hx
      rw [chElt_bc]
      exact rT_mem _ _ _ _ _ (part1 D _ _)
    | zero => simp
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
    | left_absorb a x _ hx => exact (span_mul S _ _ hx a).1
    | right_absorb b x _ hx => exact (span_mul S _ _ hx b).2
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      change z ∈ TwoSidedIdeal.span _ at hz
      induction hz using TwoSidedIdeal.span_induction with
      | mem x hx =>
        obtain ⟨k, x, α, rfl⟩ := hx
        exact TwoSidedIdeal.subset_span ⟨k, _, α, (chElt_one D S x α).symm⟩
      | zero => simp
      | add x y _ _ hx hy => simp only [tmul_add]; exact add_mem hx hy
      | neg x _ hx => simp only [tmul_neg]; exact neg_mem hx
      | left_absorb a x _ hx =>
        have := TwoSidedIdeal.mul_mem_left _ ((1 : S) ⊗ₜ[A] a) _ hx
        simpa using this
      | right_absorb b x _ hx =>
        have := TwoSidedIdeal.mul_mem_right _ _ ((1 : S) ⊗ₜ[A] b) hx
        simpa using this
    | zero => simp
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => rw [Algebra.smul_def]; exact TwoSidedIdeal.mul_mem_left _ _ _ hx

end

/- English proof (translation)
Introduce `n A E _ _ _ D S _ _`. Use `⟨part1 D S, part2 D S, fun h => ?_⟩` and prove the remaining obligations. Establish `hb : ∀ (T : Type) [CommRing T] [Algebra A T], Submodule.span T ((fun z : E => (1 : T) ⊗ₜ[A] z) '' (D.CH : Set E)) = ⊥`. Introduce `T _ _`. Rewrite using `[Submodule.span_eq_bot]`.

Introduce and unpack `_ ⟨z, hz, rfl⟩`. Rewrite `hz` using `[show D.CH = ⊥ from h]`. Establish `: z = 0` using `by simpa using hz`. Simplify using `[this]`. Use `⟨?_, fun x => ?_⟩` and prove the remaining obligations.

Use `eq_bot_iff.2 fun w hw => ?_` and prove the remaining obligations. Establish `: w ∈ ((D.baseChange S).CH : Set (S ⊗[A] E))` using `hw`. Rewrite `this` using `[part2, hb]`. Simplify using `using this`. Establish `h1` using `part1 D A (1 ⊗ₜ x)`.

Rewrite `h1` using `[hb, Submodule.mem_bot]`. Establish `h2 : D.chiS A (1 ⊗ₜ x) = D.chi x` using `by simp [Det.chiS, Det.chi]`. Rewrite `h1` using `[h2]`. Establish `h3` using `congrArg (Algebra.TensorProduct.lid A E) h1`. Rewrite `h3` using `[← Polynomial.aeval_algHom_apply]`.

Simplify using `using h3`.
-/
theorem UpperTheory.V.CA.d_chS :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (S : Type) [CommRing S] [Algebra A S], (∀ y : S ⊗[A] E, Polynomial.aeval y (D.chiS S y) ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (D.CH : Set E))) ∧ ((D.baseChange S).CH : Set (S ⊗[A] E)) = Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (D.CH : Set E)) ∧ (D.IsCH → (D.baseChange S).IsCH ∧ ∀ x : E, Polynomial.aeval x (D.chi x) = 0) := by
  intro n A E _ _ _ D S _ _
  refine ⟨part1 D S, part2 D S, fun h => ?_⟩
  have hb : ∀ (T : Type) [CommRing T] [Algebra A T],
      Submodule.span T ((fun z : E => (1 : T) ⊗ₜ[A] z) '' (D.CH : Set E)) = ⊥ := by
    intro T _ _
    rw [Submodule.span_eq_bot]
    rintro _ ⟨z, hz, rfl⟩
    rw [show D.CH = ⊥ from h] at hz
    have : z = 0 := by simpa using hz
    simp [this]
  refine ⟨?_, fun x => ?_⟩
  · refine eq_bot_iff.2 fun w hw => ?_
    have : w ∈ ((D.baseChange S).CH : Set (S ⊗[A] E)) := hw
    rw [part2, hb] at this
    simpa using this
  · have h1 := part1 D A (1 ⊗ₜ x)
    rw [hb, Submodule.mem_bot] at h1
    have h2 : D.chiS A (1 ⊗ₜ x) = D.chi x := by simp [Det.chiS, Det.chi]
    rw [h2] at h1
    have h3 := congrArg (Algebra.TensorProduct.lid A E) h1
    rw [← Polynomial.aeval_algHom_apply] at h3
    simpa using h3

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EqZeroOfForallLTensorEqZero

open TensorProduct

namespace GlobalTheory.LocalCoord

/- English proof (translation)
Use `letI := Fintype.ofFinite k`. Use `letI := Ideal.Quotient.field m`. Use `haveI : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)`. Use `haveI : Finite (A ⧸ m) := Module.finite_of_finite k`. Use `letI := Fintype.ofFinite (A ⧸ m)`.

Establish `hpow : ∀ (n : ℕ) (a : A), (FiniteField.frobeniusAlgHom k A ^ n) a = a ^ (Fintype.card k ^ n)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro a`. Simplify using the standard rewrite rules.

Consider the case `succ n ih`. Introduce `a`. Rewrite using `[pow_succ', AlgHom.mul_apply, ih, FiniteField.coe_frobeniusAlgHom, pow_succ, pow_mul]`. Establish `hc : Fintype.card (A ⧸ m) = Fintype.card k ^ Module.finrank k (A ⧸ m)` using `Module.card_eq_pow_finrank`. Use `⟨FiniteField.frobeniusAlgHom k A ^ Module.finrank k (A ⧸ m), fun a => ?_, fun a => ?_⟩` and prove the remaining obligations.

Rewrite using `[hpow, ← hc, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, FiniteField.pow_card, sub_self]`. Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_le (Fintype.one_lt_card (α := A ⧸ m))`. Conclude with `⟨a ^ d, by rw [hpow, ← hc, hd]; ring⟩`.
-/
theorem exists_frobenius (k A : Type) [Field k] [Finite k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (m : Ideal A) (hm : m.IsMaximal) :
    ∃ F : A →ₐ[k] A, (∀ a, a - F a ∈ m) ∧ ∀ a, ∃ c, F a = a * a * c := by
  letI := Fintype.ofFinite k
  letI := Ideal.Quotient.field m
  haveI : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  haveI : Finite (A ⧸ m) := Module.finite_of_finite k
  letI := Fintype.ofFinite (A ⧸ m)
  have hpow : ∀ (n : ℕ) (a : A),
      (FiniteField.frobeniusAlgHom k A ^ n) a = a ^ (Fintype.card k ^ n) := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [pow_succ', AlgHom.mul_apply, ih, FiniteField.coe_frobeniusAlgHom, pow_succ, pow_mul]
  have hc : Fintype.card (A ⧸ m) = Fintype.card k ^ Module.finrank k (A ⧸ m) :=
    Module.card_eq_pow_finrank
  refine ⟨FiniteField.frobeniusAlgHom k A ^ Module.finrank k (A ⧸ m), fun a => ?_, fun a => ?_⟩
  · rw [hpow, ← hc, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, FiniteField.pow_card,
      sub_self]
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Fintype.one_lt_card (α := A ⧸ m))
    exact ⟨a ^ d, by rw [hpow, ← hc, hd]; ring⟩

/- English proof (translation)
Set `E : K ⊗[k] A →ₗ[K] W` to `D.liftBaseChange K`. Establish `hψ : ∀ (c : K) (a : A), χ (φ (c ⊗ₜ a)) = c * χ (φ (1 ⊗ₜ a))`. Introduce `c a`. Rewrite using `[← smul_eq_mul, ← map_smul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Establish `hE : ∀ x y, E (x * y) = χ (φ x) • E y + χ (φ y) • E x`.

Introduce `x y`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x x' h h' => simp only [add_mul, map_add, h, h', add_smul, smul_add]`. Normalize the expressions using the abelian group laws.

Consider the case `tmul c a`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add y y' h h' => simp only [mul_add, map_add, h, h', add_smul, smul_add]`. Normalize the expressions using the abelian group laws.

Consider the case `tmul d b`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, hψ c, hψ d]`. Simplify using `only [E, LinearMap.liftBaseChange_tmul, hD, smul_add, smul_smul]`. Apply the tactic sequence `congr 2 <;> ring`. Establish `hEN : ∀ x ∈ nilradical (K ⊗[k] A), E x = 0`.

Introduce `x hx`. Use `haveI : IsReduced (A ⧸ nilradical A) := (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)`. Use `haveI := GlobalTheory.ReducedAlg.isReduced_field_tensor (k := k) K (A ⧸ nilradical A)`. Set `π` to `Algebra.TensorProduct.map (AlgHom.id k K) (Ideal.Quotient.mkₐ k (nilradical A))`. Establish `h0 : π x = 0` using `((mem_nilradical.mp hx).map π).eq_zero`.

Set `D' : (A ⧸ nilradical A) →ₗ[k] W` to `(((nilradical A).restrictScalars k).liftQ D (fun a ha => hN a ha)).comp (Submodule.Quotient.restrictScalarsEquiv k (nilradical A)).symm.toLinearMap`. Establish `key : ∀ y, E y = D'.liftBaseChange K (π y)`. Introduce `y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add y y' h h' => simp only [map_add, h, h']`. Consider the case `tmul d b => rfl`. Rewrite using `[key, h0, map_zero]`. Use `choose l hl using hφ`. Use `⟨fun i => E (l (t i)), fun a ha => ?_⟩` and prove the remaining obligations.

Take `⟨c, hc⟩` from `Ideal.mem_span_range_iff_exists_fun.mp (hb _ ha)`. Establish `h1 : E (l s * 1 ⊗ₜ a - ∑ i, l (c i) * l (t i)) = 0`. Use `hEN _ (hker ?_)` and prove the remaining obligations. Rewrite using `[RingHom.mem_ker, map_sub, map_mul, map_sum]`. Simplify using `only [map_mul, hl, hc, sub_self]`.

Rewrite `h1` using `[map_sub, map_sum, sub_eq_zero]`. Simplify using `only [hE, hl, ha, ht, zero_smul, add_zero] at h1`. Establish `h2 : E (1 ⊗ₜ a) = D a` using `by simp [E]`. Rewrite `h1` using `[h2]`. Rewrite using `[← Submodule.smul_mem_iff _ hs, h1]`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem span_of_derivation {k A K B W : Type} [Field k] [PerfectField k] [CommRing A]
    [Algebra k A] [Field K] [Algebra k K] [CommRing B] [Algebra K B] [AddCommGroup W]
    [Module K W] [Module k W] [IsScalarTower k K W]
    (φ : K ⊗[k] A →ₐ[K] B) (χ : B →ₐ[K] K) {g : ℕ}
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ ≤ nilradical _)
    (t : Fin g → B) (s : B) (hs : χ s ≠ 0) (ht : ∀ i, χ (t i) = 0)
    (hb : ∀ b, χ b = 0 → s * b ∈ Ideal.span (Set.range t))
    (D : A →ₗ[k] W)
    (hD : ∀ a b, D (a * b) = χ (φ (1 ⊗ₜ a)) • D b + χ (φ (1 ⊗ₜ b)) • D a)
    (hN : ∀ a ∈ nilradical A, D a = 0) :
    ∃ w : Fin g → W, ∀ a, χ (φ (1 ⊗ₜ a)) = 0 → D a ∈ Submodule.span K (Set.range w) := by
  classical
  let E : K ⊗[k] A →ₗ[K] W := D.liftBaseChange K
  have hψ : ∀ (c : K) (a : A), χ (φ (c ⊗ₜ a)) = c * χ (φ (1 ⊗ₜ a)) := by
    intro c a
    rw [← smul_eq_mul, ← map_smul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hE : ∀ x y, E (x * y) = χ (φ x) • E y + χ (φ y) • E x := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' h h' => simp only [add_mul, map_add, h, h', add_smul, smul_add]; abel
    | tmul c a =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' h h' => simp only [mul_add, map_add, h, h', add_smul, smul_add]; abel
      | tmul d b =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, hψ c, hψ d]
        simp only [E, LinearMap.liftBaseChange_tmul, hD, smul_add, smul_smul]
        congr 2 <;> ring
  have hEN : ∀ x ∈ nilradical (K ⊗[k] A), E x = 0 := by
    intro x hx
    haveI : IsReduced (A ⧸ nilradical A) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
    haveI := GlobalTheory.ReducedAlg.isReduced_field_tensor (k := k) K (A ⧸ nilradical A)
    let π := Algebra.TensorProduct.map (AlgHom.id k K) (Ideal.Quotient.mkₐ k (nilradical A))
    have h0 : π x = 0 := ((mem_nilradical.mp hx).map π).eq_zero
    let D' : (A ⧸ nilradical A) →ₗ[k] W :=
      (((nilradical A).restrictScalars k).liftQ D (fun a ha => hN a ha)).comp
        (Submodule.Quotient.restrictScalarsEquiv k (nilradical A)).symm.toLinearMap
    have key : ∀ y, E y = D'.liftBaseChange K (π y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' h h' => simp only [map_add, h, h']
      | tmul d b => rfl
    rw [key, h0, map_zero]
  choose l hl using hφ
  refine ⟨fun i => E (l (t i)), fun a ha => ?_⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hb _ ha)
  have h1 : E (l s * 1 ⊗ₜ a - ∑ i, l (c i) * l (t i)) = 0 := by
    refine hEN _ (hker ?_)
    rw [RingHom.mem_ker, map_sub, map_mul, map_sum]
    simp only [map_mul, hl, hc, sub_self]
  rw [map_sub, map_sum, sub_eq_zero] at h1
  simp only [hE, hl, ha, ht, zero_smul, add_zero] at h1
  have h2 : E (1 ⊗ₜ a) = D a := by simp [E]
  rw [h2] at h1
  rw [← Submodule.smul_mem_iff _ hs, h1]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Introduce `k A K B _ _ _ _ _ _ _ _ _ φ χ g m hφ hker hm hmax ⟨t, s, hs, ht, hb⟩ _`. Use `letI := Ideal.Quotient.field m`. Use `haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A`. Take `⟨F, hF, hF2⟩` from `exists_frobenius k A m hmax`. Set `ι : A →ₐ[k] K` to `((χ.comp φ).restrictScalars k).comp Algebra.TensorProduct.includeRight`.

Establish `hι : ∀ a, ι a = χ (φ (1 ⊗ₜ a))` using `fun a => rfl`. Set `ι' : (A ⧸ m) →+* K` to `Ideal.Quotient.lift m ι fun a ha => (hm a).mp ha`. Set `N' : Submodule (A ⧸ m) m.Cotangent` to `Submodule.span _ {y | ∃ x : m, (x : A) ∈ nilradical A ∧ m.toCotangent x = y}`. Use `haveI : Module.Finite A m.Cotangent := Module.Finite.of_surjective m.toCotangent m.toCotangent_surjective`. Use `haveI : Module.Finite (A ⧸ m) m.Cotangent := Module.Finite.of_restrictScalars_finite A _ _`.

Set `r` to `Module.finrank (A ⧸ m) (m.Cotangent ⧸ N')`. Set `b` to `Module.finBasis (A ⧸ m) (m.Cotangent ⧸ N')`. Set `p : m → m.Cotangent ⧸ N'` to `fun x => N'.mkQ (m.toCotangent x)`. Establish `hpadd : ∀ x y, p (x + y) = p x + p y` using `fun x y => by simp only [p, map_add]`. Establish `hpsmul : ∀ (a : A) x, p (a • x) = Ideal.Quotient.mk m a • p x` using `fun a x => by`.

Simplify using `only [p, map_smul]`. Both sides reduce to the same expression. Establish `hpsurj : Function.Surjective p` using `N'.mkQ_surjective.comp m.toCotangent_surjective`. Set `L : m → Fin r → K` to `fun x j => ι' (b.repr (p x) j)`. Establish `hLadd : ∀ x y, L (x + y) = L x + L y` using `fun x y => by`.

Use extensionality with `j`. Simplify using `only [L, hpadd, map_add, Finsupp.add_apply, Pi.add_apply]`. Establish `hLsmul : ∀ (a : A) x, L (a • x) = ι a • L x` using `fun a x => by`. Use extensionality with `j`. Simplify using `only [L, hpsmul, map_smul, Finsupp.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul]`.

Both sides reduce to the same expression. Set `D : A →ₗ[k] Fin r → K` to `{ toFun := fun a => L ⟨a - F a, hF a⟩ map_add' := fun a a' => by`. Rewrite using `[← hLadd]`. Use `congr 1`. Use `ext`.

Simplify using `only [map_add, Submodule.coe_add]`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `map_smul' := fun c a => by`. Rewrite using `[RingHom.id_apply, ← algebraMap_smul K c (L _), ← ι.commutes, ← hLsmul]`. Use `congr 1`.

Use `ext`. Express the relevant statement in the definitionally equal form `c • a - F (c • a) = algebraMap k A c * (a - F a)`. Rewrite using `[map_smul, ← Algebra.smul_def, smul_sub] }`. Establish `hιF : ∀ a, ι (F a) = ι a` using `fun a => by`. Use `(hm _).mp (hF a)` as an intermediate fact.

Rewrite `this` using `[← hι, map_sub, sub_eq_zero]`. Conclude with `this.symm`. Take `⟨w, hw⟩` from `span_of_derivation φ χ hφ hker t s hs ht hb D (fun a a' => by`. Express the relevant statement in the definitionally equal form `L _ = ι a • L _ + ι a' • L _`. Rewrite using `[← hιF a', ← hLsmul, ← hLsmul, ← hLadd]`.

Use `congr 1`. Use `ext`. Simplify using `only [map_mul, Submodule.coe_add, SetLike.val_smul, smul_eq_mul]`. Use the proof step `ring) (fun a ha => by`. Establish `: p ⟨a - F a, hF a⟩ = 0`.

Use `(Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨_, ?_, rfl⟩)` and prove the remaining obligations. Conclude with `sub_mem ha ((mem_nilradical.mp ha).map F)`. Express the relevant statement in the definitionally equal form `L _ = 0`. Use extensionality with `j`. Simplify using `[L, this])`.

Use `choose v hv using hpsurj`. Establish `hDL : ∀ x : m, D x = L x` using `fun x => by`. Take `⟨c, hc⟩` from `hF2 x`. Establish `h1 : L x = L ⟨x - F x, hF x⟩ + L ((x * c : A) • x)`. Rewrite using `[← hLadd]`.

Use `congr 1`. Use `ext`. Simplify using `only [hc, Submodule.coe_add, SetLike.val_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, hLsmul, map_mul, hι, (hm _).mp x.2, zero_mul, zero_smul, add_zero]`.

Both sides reduce to the same expression. Establish `hrg : r ≤ g`. Establish `htop : Submodule.span K (Set.range w) = ⊤`. Rewrite using `[eq_top_iff, ← (Pi.basisFun K (Fin r)).span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`.

Establish `: Pi.basisFun K (Fin r) j = D (v (b j))`. Rewrite using `[hDL]`. Use extensionality with `i`. Simplify using `only [L, hv, Module.Basis.repr_self, Pi.basisFun_apply, Finsupp.single_apply, Pi.single_apply]`. Distinguish the cases in `h : j = i`.

Simplify using `[h]`. Simplify using `[h, Ne.symm h]`. Rewrite using `[this]`. Conclude with `hw _ ((hm _).mp (v (b j)).2)`. Use `finrank_range_le_card (R := K) w` as an intermediate fact.

Rewrite `this` using `[Set.finrank, htop, finrank_top, Module.finrank_fin_fun, Fintype.card_fin]`. Then use the resulting hypothesis. Set `u : Fin g → A` to `fun i => if h : i.1 < r then (v (b ⟨i.1, h⟩) : A) else 0`. Establish `hu : ∀ j : Fin r, (v (b j) : A) ∈ Ideal.span (Set.range u)` using `fun j => Ideal.subset_span ⟨⟨j.1, lt_of_lt_of_le j.2 hrg⟩, by simp [u]⟩`. Establish `hle : m ≤ (Ideal.span (Set.range u) ⊔ nilradical A) ⊔ m • m` using `by set J := (Ideal.span (Set.range u) ⊔ nilradical A) ⊔ m • m with hJ`. Establish `hk : ∀ y ∈ N', ∀ x : m, m.toCotangent x = y → (x : A) ∈ J`.

Introduce `y hy`. Establish `: ∃ z : m, (z : A) ∈ nilradical A ∧ m.toCotangent z = y`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y h => exact h`. Consider the case `zero => exact ⟨0, zero_mem _, map_zero _⟩`.

Consider the case `add y y' _ _ h h'`. Take `⟨z, hz, rfl⟩` from `h`. Take `⟨z', hz', rfl⟩` from `h'`. Conclude with `⟨z + z', add_mem hz hz', map_add _ _ _⟩`. Consider the case `smul c y _ h`.

Take `⟨z, hz, rfl⟩` from `h`. Take `⟨c, rfl⟩` from `Ideal.Quotient.mk_surjective c`. Conclude with `⟨c • z, Ideal.mul_mem_left _ _ hz, by rw [map_smul]; rfl⟩`. Take `⟨z, hz, rfl⟩` from `this`. Introduce `x hx`.

Establish `h2` using `m.toCotangent_eq.mp hx`. Establish `: (x : A) = z + (x - z)` using `by ring`. Rewrite using `[this]`. Use `add_mem (Ideal.mem_sup_left (Ideal.mem_sup_right hz)) (Ideal.mem_sup_right ?_)` and prove the remaining obligations. Rewrite `h2` using `[pow_two]`. Then use the resulting hypothesis.

Establish `hall : ∀ y : m.Cotangent ⧸ N', ∃ z : m, (z : A) ∈ J ∧ p z = y`. Introduce `y`. Establish `hy : y ∈ Submodule.span (A ⧸ m) (Set.range b)` using `by rw [b.span_eq]; trivial`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y h`.

Take `⟨j, rfl⟩` from `h`. Conclude with `⟨v (b j), Ideal.mem_sup_left (Ideal.mem_sup_left (hu j)), hv _⟩`. Consider the case `zero => exact ⟨0, zero_mem _, by simp [p]⟩`. Consider the case `add y y' _ _ h h'`. Take `⟨z, hz, rfl⟩` from `h`.

Take `⟨z', hz', rfl⟩` from `h'`. Conclude with `⟨z + z', add_mem hz hz', hpadd _ _⟩`. Consider the case `smul c y _ h`. Take `⟨z, hz, rfl⟩` from `h`. Take `⟨c, rfl⟩` from `Ideal.Quotient.mk_surjective c`.

Conclude with `⟨c • z, Ideal.mul_mem_left _ _ hz, hpsmul _ _⟩`. Introduce `a ha`. Take `⟨z, hz, hp⟩` from `hall (p ⟨a, ha⟩)`. Establish `h3` using `hk _ ((Submodule.Quotient.eq N').mp hp.symm) (⟨a, ha⟩ - z) (map_sub _ _ _)`. Establish `: a = (a - z) + z` using `by ring`.

Rewrite using `[this]`. Conclude with `add_mem h3 hz`. Take `⟨c, hc, hcle⟩` from `Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup (IsNoetherian.noetherian m) le_rfl hle`. Use `⟨u, c, fun h => hmax.ne_top ?_, fun i => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.eq_top_iff_one]`.

Use `sub_mem h hc` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Simplify using `only [u] split_ifs`. Conclude with `Subtype.prop _`. Conclude with `zero_mem _`.

Conclude with `hcle (Submodule.smul_mem_pointwise_smul a c m ha)`.
-/
theorem exists_local_coordinates :
    ∀ (k A K B : Type) [Field k] [Finite k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [Field K] [Algebra k K] [CommRing B] [Algebra K B] (φ : TensorProduct k K A →ₐ[K] B) (χ : B →ₐ[K] K) (g : ℕ) (m : Ideal A), Function.Surjective φ → RingHom.ker φ ≤ nilradical _ → (∀ a : A, a ∈ m ↔ χ (φ (1 ⊗ₜ a)) = 0) → m.IsMaximal → (∃ (t : Fin g → B) (s : B), χ s ≠ 0 ∧ (∀ i, χ (t i) = 0) ∧ ∀ b, χ b = 0 → s * b ∈ Ideal.span (Set.range t)) → IsReduced B → ∃ (u : Fin g → A) (s : A), s ∉ m ∧ (∀ i, u i ∈ m) ∧ ∀ a ∈ m, s * a ∈ Ideal.span (Set.range u) ⊔ nilradical A := by
  intro k A K B _ _ _ _ _ _ _ _ _ φ χ g m hφ hker hm hmax ⟨t, s, hs, ht, hb⟩ _
  classical
  letI := Ideal.Quotient.field m
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨F, hF, hF2⟩ := exists_frobenius k A m hmax
  let ι : A →ₐ[k] K := ((χ.comp φ).restrictScalars k).comp Algebra.TensorProduct.includeRight
  have hι : ∀ a, ι a = χ (φ (1 ⊗ₜ a)) := fun a => rfl
  let ι' : (A ⧸ m) →+* K := Ideal.Quotient.lift m ι fun a ha => (hm a).mp ha
  let N' : Submodule (A ⧸ m) m.Cotangent :=
    Submodule.span _ {y | ∃ x : m, (x : A) ∈ nilradical A ∧ m.toCotangent x = y}
  haveI : Module.Finite A m.Cotangent :=
    Module.Finite.of_surjective m.toCotangent m.toCotangent_surjective
  haveI : Module.Finite (A ⧸ m) m.Cotangent := Module.Finite.of_restrictScalars_finite A _ _
  let r := Module.finrank (A ⧸ m) (m.Cotangent ⧸ N')
  let b := Module.finBasis (A ⧸ m) (m.Cotangent ⧸ N')
  let p : m → m.Cotangent ⧸ N' := fun x => N'.mkQ (m.toCotangent x)
  have hpadd : ∀ x y, p (x + y) = p x + p y := fun x y => by simp only [p, map_add]
  have hpsmul : ∀ (a : A) x, p (a • x) = Ideal.Quotient.mk m a • p x := fun a x => by
    simp only [p, map_smul]; rfl
  have hpsurj : Function.Surjective p := N'.mkQ_surjective.comp m.toCotangent_surjective
  let L : m → Fin r → K := fun x j => ι' (b.repr (p x) j)
  have hLadd : ∀ x y, L (x + y) = L x + L y := fun x y => by
    ext j; simp only [L, hpadd, map_add, Finsupp.add_apply, Pi.add_apply]
  have hLsmul : ∀ (a : A) x, L (a • x) = ι a • L x := fun a x => by
    ext j
    simp only [L, hpsmul, map_smul, Finsupp.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul]
    rfl
  let D : A →ₗ[k] Fin r → K :=
    { toFun := fun a => L ⟨a - F a, hF a⟩
      map_add' := fun a a' => by
        rw [← hLadd]; congr 1; ext; simp only [map_add, Submodule.coe_add]; ring
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← algebraMap_smul K c (L _), ← ι.commutes, ← hLsmul]
        congr 1; ext
        change c • a - F (c • a) = algebraMap k A c * (a - F a)
        rw [map_smul, ← Algebra.smul_def, smul_sub] }
  have hιF : ∀ a, ι (F a) = ι a := fun a => by
    have := (hm _).mp (hF a)
    rw [← hι, map_sub, sub_eq_zero] at this
    exact this.symm
  obtain ⟨w, hw⟩ := span_of_derivation φ χ hφ hker t s hs ht hb D (fun a a' => by
      change L _ = ι a • L _ + ι a' • L _
      rw [← hιF a', ← hLsmul, ← hLsmul, ← hLadd]
      congr 1; ext
      simp only [map_mul, Submodule.coe_add, SetLike.val_smul, smul_eq_mul]
      ring) (fun a ha => by
      have : p ⟨a - F a, hF a⟩ = 0 := by
        refine (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨_, ?_, rfl⟩)
        exact sub_mem ha ((mem_nilradical.mp ha).map F)
      change L _ = 0
      ext j
      simp [L, this])
  choose v hv using hpsurj
  have hDL : ∀ x : m, D x = L x := fun x => by
    obtain ⟨c, hc⟩ := hF2 x
    have h1 : L x = L ⟨x - F x, hF x⟩ + L ((x * c : A) • x) := by
      rw [← hLadd]; congr 1; ext
      simp only [hc, Submodule.coe_add, SetLike.val_smul, smul_eq_mul]
      ring
    rw [h1, hLsmul, map_mul, hι, (hm _).mp x.2, zero_mul, zero_smul, add_zero]
    rfl
  have hrg : r ≤ g := by
    have htop : Submodule.span K (Set.range w) = ⊤ := by
      rw [eq_top_iff, ← (Pi.basisFun K (Fin r)).span_eq, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have : Pi.basisFun K (Fin r) j = D (v (b j)) := by
        rw [hDL]
        ext i
        simp only [L, hv, Module.Basis.repr_self, Pi.basisFun_apply, Finsupp.single_apply,
          Pi.single_apply]
        by_cases h : j = i
        · simp [h]
        · simp [h, Ne.symm h]
      rw [this]
      exact hw _ ((hm _).mp (v (b j)).2)
    have := finrank_range_le_card (R := K) w
    rwa [Set.finrank, htop, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at this
  let u : Fin g → A := fun i => if h : i.1 < r then (v (b ⟨i.1, h⟩) : A) else 0
  have hu : ∀ j : Fin r, (v (b j) : A) ∈ Ideal.span (Set.range u) := fun j =>
    Ideal.subset_span ⟨⟨j.1, lt_of_lt_of_le j.2 hrg⟩, by simp [u]⟩
  have hle : m ≤ (Ideal.span (Set.range u) ⊔ nilradical A) ⊔ m • m := by
    set J := (Ideal.span (Set.range u) ⊔ nilradical A) ⊔ m • m with hJ
    have hk : ∀ y ∈ N', ∀ x : m, m.toCotangent x = y → (x : A) ∈ J := by
      intro y hy
      have : ∃ z : m, (z : A) ∈ nilradical A ∧ m.toCotangent z = y := by
        induction hy using Submodule.span_induction with
        | mem y h => exact h
        | zero => exact ⟨0, zero_mem _, map_zero _⟩
        | add y y' _ _ h h' =>
          obtain ⟨z, hz, rfl⟩ := h
          obtain ⟨z', hz', rfl⟩ := h'
          exact ⟨z + z', add_mem hz hz', map_add _ _ _⟩
        | smul c y _ h =>
          obtain ⟨z, hz, rfl⟩ := h
          obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
          exact ⟨c • z, Ideal.mul_mem_left _ _ hz, by rw [map_smul]; rfl⟩
      obtain ⟨z, hz, rfl⟩ := this
      intro x hx
      have h2 := m.toCotangent_eq.mp hx
      have : (x : A) = z + (x - z) := by ring
      rw [this]
      refine add_mem (Ideal.mem_sup_left (Ideal.mem_sup_right hz)) (Ideal.mem_sup_right ?_)
      rwa [pow_two] at h2
    have hall : ∀ y : m.Cotangent ⧸ N', ∃ z : m, (z : A) ∈ J ∧ p z = y := by
      intro y
      have hy : y ∈ Submodule.span (A ⧸ m) (Set.range b) := by rw [b.span_eq]; trivial
      induction hy using Submodule.span_induction with
      | mem y h =>
        obtain ⟨j, rfl⟩ := h
        exact ⟨v (b j), Ideal.mem_sup_left (Ideal.mem_sup_left (hu j)), hv _⟩
      | zero => exact ⟨0, zero_mem _, by simp [p]⟩
      | add y y' _ _ h h' =>
        obtain ⟨z, hz, rfl⟩ := h
        obtain ⟨z', hz', rfl⟩ := h'
        exact ⟨z + z', add_mem hz hz', hpadd _ _⟩
      | smul c y _ h =>
        obtain ⟨z, hz, rfl⟩ := h
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
        exact ⟨c • z, Ideal.mul_mem_left _ _ hz, hpsmul _ _⟩
    intro a ha
    obtain ⟨z, hz, hp⟩ := hall (p ⟨a, ha⟩)
    have h3 := hk _ ((Submodule.Quotient.eq N').mp hp.symm) (⟨a, ha⟩ - z) (map_sub _ _ _)
    have : a = (a - z) + z := by ring
    rw [this]
    exact add_mem h3 hz
  obtain ⟨c, hc, hcle⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (IsNoetherian.noetherian m) le_rfl hle
  refine ⟨u, c, fun h => hmax.ne_top ?_, fun i => ?_, fun a ha => ?_⟩
  · rw [Ideal.eq_top_iff_one]
    have := sub_mem h hc
    rwa [sub_sub_cancel] at this
  · simp only [u]
    split_ifs
    · exact Subtype.prop _
    · exact zero_mem _
  · exact hcle (Submodule.smul_mem_pointwise_smul a c m ha)

end GlobalTheory.LocalCoord

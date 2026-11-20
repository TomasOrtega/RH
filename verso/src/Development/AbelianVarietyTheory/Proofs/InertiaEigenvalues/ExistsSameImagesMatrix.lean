import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantSchwartzMemSpanLatticeIndicators

namespace GlobalTheory.DownLift.SplitGen

section Matrices

variable (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
  [Field K] [Algebra O K] [IsFractionRing O K] (n r : ℕ)

def invFun (d : O) : Submodule ℂ (Matrix (Fin n) (Fin r) K → ℂ) where
  carrier := {Φ | (∀ x (z : Matrix (Fin n) (Fin r) O), Φ (x + (d • z).map (algebraMap O K)) = Φ x) ∧
    (∀ x, Φ x ≠ 0 → ∃ z : Matrix (Fin n) (Fin r) O, algebraMap O K d • x = z.map (algebraMap O K)) ∧
    ∀ (h : GL (Fin n) O) x, Φ ((h : Matrix _ _ O).map (algebraMap O K) * x) = Φ x}
  zero_mem' := ⟨fun _ _ => rfl, fun _ h => absurd rfl h, fun _ _ => rfl⟩
  add_mem' := by
    rintro a b ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    refine ⟨fun x z => by simp only [Pi.add_apply, a1, b1], fun x hx => ?_, fun h x => by simp only [Pi.add_apply, a3, b3]⟩
    by_cases h : a x = 0
    · exact b2 x fun h' => hx (by simp [h, h'])
    · exact a2 x h
  smul_mem' := by
    rintro c a ⟨a1, a2, a3⟩
    exact ⟨fun x z => by simp only [Pi.smul_apply, a1], fun x hx => a2 x fun h => hx (by simp [h]),
      fun h x => by simp only [Pi.smul_apply, a3]⟩

variable {O K n r}

variable (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (n r : ℕ) in
variable {O K n r} in
/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨k, hk⟩` from `IsDiscreteValuationRing.ideal_eq_span_pow_irreducible (s := Ideal.span {d ^ 2}) (by rw [Ne, Ideal.span_singleton_eq_bot]; exact pow_ne_zero 2 hd) hϖ`. Use `IsLocalRing.finite_quotient_iff.mpr ⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[hk, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]`.
-/
private lemma finite_quotient_span_sq {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {d : O} (hd : d ≠ 0) :
    Finite (O ⧸ Ideal.span {d ^ 2}) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {d ^ 2}) (by rw [Ne, Ideal.span_singleton_eq_bot]; exact pow_ne_zero 2 hd) hϖ
  refine IsLocalRing.finite_quotient_iff.mpr ⟨k, ?_⟩
  rw [hk, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]

variable (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (n r : ℕ) in
variable {O K n r} in
/- English proof (translation)
Take `⟨k, b⟩` from `Submodule.basisOfPid (Pi.basisFun R (Fin m)) N`. Establish `hk : k = m`. Apply `le_antisymm` to reduce the goal to its premises. Establish `h` using `Submodule.finrank_le N`. Rewrite `h` using `[Module.finrank_eq_card_basis b, Fintype.card_fin, Module.finrank_fin_fun]`. Then use the resulting hypothesis.

Establish `hinj : Function.Injective (c • LinearMap.id : (Fin m → R) →ₗ[R] (Fin m → R))` using `fun v w hvw => smul_right_injective _ hc (by simpa using hvw)`. Establish `h1` using `LinearMap.finrank_range_of_inj hinj`. Establish `h2 : LinearMap.range (c • LinearMap.id : (Fin m → R) →ₗ[R] (Fin m → R)) ≤ N`. Introduce and unpack `_ ⟨v, rfl⟩`. Simplify using `using hN v`.

Establish `h3` using `Submodule.finrank_mono h2`. Rewrite `h3` using `[h1, Module.finrank_eq_card_basis b, Fintype.card_fin, Module.finrank_fin_fun]`. Then use the resulting hypothesis. Substitute `hk` using the available equality. Set `B : Matrix (Fin k) (Fin k) R` to `Matrix.of fun i j => (b i : Fin k → R) j`. Establish `hmem : ∀ v, v ∈ N ↔ ∃ w, v = Matrix.vecMul w B`.

Introduce `v`. Prove the components needed by the constructor for the conclusion. Introduce `hv`. Use `⟨b.repr ⟨v, hv⟩, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg Subtype.val (b.sum_repr ⟨v, hv⟩)`.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h`. Use extensionality with `j`. Establish `hj` using `congrFun h j`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hj`. Rewrite using `[← hj]`.

Simplify using `[Matrix.vecMul, dotProduct, B]`. Introduce and unpack `⟨w, rfl⟩`. Establish `: Matrix.vecMul w B = ∑ i, w i • (b i : Fin k → R)`. Use extensionality with `j`. Simplify using `[Matrix.vecMul, dotProduct, B, Finset.sum_apply]`.

Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2`. Use `⟨B, ?_, hmem⟩` and prove the remaining obligations. Establish `hrow : ∀ i, ∃ w, c • Pi.single i 1 = Matrix.vecMul w B` using `fun i => (hmem _).1 (hN _)`. Use `choose W hW using hrow`.

Establish `hWB : Matrix.of W * B = c • (1 : Matrix (Fin k) (Fin k) R)`. Use extensionality with `i j`. Use `congrFun (hW i) j` as an intermediate fact. Simplify using `only [Matrix.vecMul, dotProduct] at this`. Simplify using `[Matrix.mul_apply, Matrix.one_apply, ← this, Pi.single_apply, eq_comm]`.

Introduce `h0`. Use `congrArg Matrix.det hWB` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one]`. Conclude with `pow_ne_zero _ hc this.symm`.
-/
private lemma exists_matrix_vecMul_span_eq_of_smul_mem {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {m : ℕ} (N : Submodule R (Fin m → R)) {c : R} (hc : c ≠ 0) (hN : ∀ v, c • v ∈ N) :
    ∃ B : Matrix (Fin m) (Fin m) R, B.det ≠ 0 ∧ ∀ v, v ∈ N ↔ ∃ w, v = Matrix.vecMul w B := by
  classical
  obtain ⟨k, b⟩ := Submodule.basisOfPid (Pi.basisFun R (Fin m)) N
  have hk : k = m := by
    apply le_antisymm
    · have h := Submodule.finrank_le N
      rwa [Module.finrank_eq_card_basis b, Fintype.card_fin, Module.finrank_fin_fun] at h
    · have hinj : Function.Injective (c • LinearMap.id : (Fin m → R) →ₗ[R] (Fin m → R)) :=
        fun v w hvw => smul_right_injective _ hc (by simpa using hvw)
      have h1 := LinearMap.finrank_range_of_inj hinj
      have h2 : LinearMap.range (c • LinearMap.id : (Fin m → R) →ₗ[R] (Fin m → R)) ≤ N := by
        rintro _ ⟨v, rfl⟩; simpa using hN v
      have h3 := Submodule.finrank_mono h2
      rwa [h1, Module.finrank_eq_card_basis b, Fintype.card_fin, Module.finrank_fin_fun] at h3
  subst hk
  let B : Matrix (Fin k) (Fin k) R := Matrix.of fun i j => (b i : Fin k → R) j
  have hmem : ∀ v, v ∈ N ↔ ∃ w, v = Matrix.vecMul w B := by
    intro v
    constructor
    · intro hv
      refine ⟨b.repr ⟨v, hv⟩, ?_⟩
      have h := congrArg Subtype.val (b.sum_repr ⟨v, hv⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h
      ext j
      have hj := congrFun h j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hj
      rw [← hj]
      simp [Matrix.vecMul, dotProduct, B]
    · rintro ⟨w, rfl⟩
      have : Matrix.vecMul w B = ∑ i, w i • (b i : Fin k → R) := by
        ext j; simp [Matrix.vecMul, dotProduct, B, Finset.sum_apply]
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2
  refine ⟨B, ?_, hmem⟩
  have hrow : ∀ i, ∃ w, c • Pi.single i 1 = Matrix.vecMul w B := fun i => (hmem _).1 (hN _)
  choose W hW using hrow
  have hWB : Matrix.of W * B = c • (1 : Matrix (Fin k) (Fin k) R) := by
    ext i j
    have := congrFun (hW i) j
    simp only [Matrix.vecMul, dotProduct] at this
    simp [Matrix.mul_apply, Matrix.one_apply, ← this, Pi.single_apply, eq_comm]
  intro h0
  have := congrArg Matrix.det hWB
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ hc this.symm

variable (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (n r : ℕ) in
variable {O K n r} in

/- English proof (translation)
Use `set ι := algebraMap O K with hι`. Establish `hιinj : Function.Injective ι` using `IsFractionRing.injective O K`. Establish `hιd : ι d ≠ 0` using `fun h => hd (hιinj (by rw [h, map_zero]))`. Establish `hPer : ∀ i x (z : Matrix (Fin n) (Fin r) O), M i f (x + (d • z).map ι) = M i f x` using `fun i => by obtain ⟨a, -, -⟩ := hP i; exact a`. Establish `hSupp : ∀ i x, M i f x ≠ 0 → ∃ z : Matrix (Fin n) (Fin r) O, ι d • x = z.map ι` using `fun i => by obtain ⟨-, a, -⟩ := hP i; exact a`.

Establish `hInv : ∀ i (h : GL (Fin n) O) x, M i f ((h : Matrix (Fin n) (Fin n) O).map ι * x) = M i f x` using `fun i => by obtain ⟨-, -, a⟩ := hP i; exact a`. Use `haveI := finite_quotient_span_sq (O := O) hd`. Use `haveI : Finite (Submodule O (Fin r → O ⧸ Ideal.span {d ^ 2})) := Finite.of_injective (fun N : Submodule O (Fin r → O ⧸ Ideal.span {d ^ 2}) => (N : Set (Fin r → O ⧸ Ideal.span {d ^ 2}))) SetLike.coe_injective`. Use `letI : Fintype (Submodule O (Fin r → O ⧸ Ideal.span {d ^ 2})) := Fintype.ofFinite _`. Set `red : Matrix (Fin n) (Fin r) O → Fin n → Fin r → O ⧸ Ideal.span {d ^ 2}` to `fun y a b => Ideal.Quotient.mk _ (y a b)`.

Set `ρ : Matrix (Fin n) (Fin r) K → Option (Submodule O (Fin r → O ⧸ Ideal.span {d ^ 2}))` to `fun x => if h : ∃ y : Matrix (Fin n) (Fin r) O, ι d • x = y.map ι then some (Submodule.span O (Set.range (red h.choose))) else none`. Establish `hnone : ∀ i x, ρ x = none → M i f x = 0`. Introduce `i x hx`. Assume the negation of the conclusion as `h0`. Establish `hx'` using `hSupp i x h0`.

Simplify using `[ρ, hx'] at hx`. Establish `hfib : ∀ i x x', ρ x = ρ x' → M i f x = M i f x'`. Introduce `i x x' hxx`. Distinguish the cases in `hx : ∃ y : Matrix (Fin n) (Fin r) O, ι d • x = y.map ι`. Establish `hx' : ∃ y : Matrix (Fin n) (Fin r) O, ι d • x' = y.map ι`.

Assume the negation of the conclusion as `hx'`. Simplify using `[ρ, hx, hx'] at hxx`. Simplify using `only [ρ, hx, hx', dite_true, Option.some.injEq] at hxx`. Take `⟨h, hh⟩` from `_root_.GlobalTheory.exists_GL_of_span_range_eq O _ n _ _ hxx`. Establish `hy` using `hx.choose_spec`.

Establish `hy'` using `hx'.choose_spec`. Establish `hdiff : ∀ a b, ∃ c, hx'.choose a b = ((h : Matrix (Fin n) (Fin n) O) * hx.choose) a b + c * d ^ 2`. Introduce `a b`. Establish `hs : ∀ c a : O, c • (Ideal.Quotient.mk (Ideal.span {d ^ 2}) a) = Ideal.Quotient.mk (Ideal.span {d ^ 2}) (c * a)` using `fun c a => by`. Rewrite using `[Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul]`.

Establish `e` using `congrFun (hh a) b`. Simplify using `only [red, Finset.sum_apply, Pi.smul_apply, hs, ← map_sum, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at e`. Take `⟨c, hc⟩` from `e`. Conclude with `⟨c, by rw [Matrix.mul_apply]; linear_combination -hc⟩`. Use `choose z hz using hdiff`.

Establish `hx'eq : x' = (h : Matrix (Fin n) (Fin n) O).map ι * x + (d • Matrix.of z).map ι`. Apply `smul_right_injective _ hιd` to reduce the goal to its premises. Use extensionality with `a b`. Establish `e1 : ι d * x' a b = ι (hx'.choose a b)`. Simplify using `using congrFun (congrFun hy' a) b`.

Establish `e2 : ∀ k, ι d * x k b = ι (hx.choose k b)` using `fun k => by`. Simplify using `using congrFun (congrFun hy k) b`. Simplify using `only [smul_eq_mul, Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, mul_add, Finset.mul_sum]`. Rewrite using `[e1, hz a b]`. Simplify using `only [Matrix.mul_apply, map_add, map_sum, map_mul, map_pow, smul_eq_mul]`.

Establish `: ∀ k, ι d * (ι ((h : Matrix (Fin n) (Fin n) O) a k) * x k b) = ι ((h : Matrix (Fin n) (Fin n) O) a k) * ι (hx.choose k b)` using `fun k => by rw [← e2 k]; ring`. Simplify using `only [this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hx'eq, hPer, hInv]`. Establish `hx' : ¬ ∃ y : Matrix (Fin n) (Fin r) O, ι d • x' = y.map ι`.

Introduce `hx'`. Simplify using `[ρ, hx, hx'] at hxx`. Rewrite using `[hnone i x (by simp [ρ, hx]), hnone i x' (by simp [ρ, hx'])]`. Establish `hlow : ∀ l : Submodule O (Fin r → O ⧸ Ideal.span {d ^ 2}), ∃ g : GL (Fin r) K, {x : Matrix (Fin n) (Fin r) K | ∃ z : Matrix (Fin n) (Fin r) O, x * (g : Matrix _ _ K) = z.map ι} = {x | ∃ l', ρ x = some l' ∧ l' ≤ l}`. Introduce `l`.

Set `N₀ : Submodule O (Fin r → O)` to `l.comap ((Ideal.Quotient.mkₐ O (Ideal.span {d ^ 2})).toLinearMap.compLeft (Fin r))`. Establish `hmemN : ∀ v, v ∈ N₀ ↔ (fun j => Ideal.Quotient.mk (Ideal.span {d ^ 2}) (v j)) ∈ l` using `fun v => Iff.rfl`. Establish `hN : ∀ v, d ^ 2 • v ∈ N₀`. Introduce `v`. Rewrite using `[hmemN]`.

Use `l.zero_mem` and compare the differences between its conclusion and the goal. Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_mul_right _ _))`. Take `⟨B, hB, hBmem⟩` from `exists_matrix_vecMul_span_eq_of_smul_mem N₀ (pow_ne_zero 2 hd) hN`. Set `A : Matrix (Fin r) (Fin r) K` to `(ι d)⁻¹ • B.map ι`.

Establish `hA : IsUnit A.det`. Rewrite using `[isUnit_iff_ne_zero, Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `mul_ne_zero (pow_ne_zero _ (inv_ne_zero hιd)) fun h => hB (hιinj (by rw [h, map_zero]))`. Use `⟨(Matrix.nonsingInvUnit A hA)⁻¹, ?_⟩` and prove the remaining obligations. Establish `hgA : (((Matrix.nonsingInvUnit A hA)⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = A⁻¹`.

Rewrite using `[Matrix.coe_units_inv]`. Both sides reduce to the same expression. Establish `key : ∀ x (z : Matrix (Fin n) (Fin r) O), x * A⁻¹ = z.map ι ↔ ι d • x = (z * B).map ι`. Introduce `x z`. Establish `hAinv : A⁻¹ * A = 1` using `Matrix.nonsing_inv_mul A hA`.

Establish `hAA : A * A⁻¹ = 1` using `Matrix.mul_nonsing_inv A hA`. Establish `hzB : (z * B).map ι = z.map ι * B.map ι` using `Matrix.map_mul`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `: x = z.map ι * A` using `by rw [← h, Matrix.mul_assoc, hAinv, Matrix.mul_one]`.

Rewrite using `[this, hzB]`. Simplify using `[A, Matrix.mul_smul, smul_smul, hιd]`. Introduce `h`. Establish `: x = z.map ι * A`. Apply `smul_right_injective _ hιd` to reduce the goal to its premises.

Simplify using `only`. Rewrite using `[h, hzB]`. Simplify using `[A, Matrix.mul_smul, smul_smul, hιd]`. Rewrite using `[this, Matrix.mul_assoc, hAA, Matrix.mul_one]`. Use extensionality with `x`.

Simplify using `only [Set.mem_setOf_eq, hgA, key]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz⟩ replace hz := (key x z).1 hz`. Establish `hx : ∃ y : Matrix (Fin n) (Fin r) O, ι d • x = y.map ι` using `⟨_, hz⟩`. Use `⟨_, dif_pos hx, ?_⟩` and prove the remaining obligations.

Establish `hy : hx.choose = z * B` using `Matrix.map_injective hιinj (hx.choose_spec.symm.trans hz)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`. Establish `: hx.choose a ∈ N₀` using `(hBmem _).2 ⟨z a, by`. Rewrite using `[hy]`.

Use extensionality with `j`. Simplify using `[Matrix.mul_apply, Matrix.vecMul, dotProduct]⟩`. Conclude with `this`. Introduce and unpack `⟨l', hl', hle⟩`. Establish `hx : ∃ y : Matrix (Fin n) (Fin r) O, ι d • x = y.map ι`.

Assume the negation of the conclusion as `hx`. Simplify using `[ρ, hx] at hl'`. Simplify using `only [ρ, hx, dite_true, Option.some.injEq] at hl'`. Establish `hrow : ∀ a, ∃ w, hx.choose a = Matrix.vecMul w B` using `fun a => (hBmem _).1 (hle (hl' ▸ Submodule.subset_span ⟨a, rfl⟩))`. Use `choose w hw using hrow`.

Use `⟨Matrix.of w, (key x _).2 (hx.choose_spec.trans ?_)⟩` and prove the remaining obligations. Use `congr 1`. Use extensionality with `a j`. Rewrite using `[hw a]`. Simplify using `[Matrix.mul_apply, Matrix.vecMul, dotProduct]`.

Use `choose g hg using hlow`. It suffices to establish `hS : (fun i => M i f) ∈ G.map (LinearMap.pi M) by`. Take `⟨F, hF, hFe⟩` from `hS`. Conclude with `⟨F, hF, fun i => by simpa using congrFun hFe i⟩`. Set `E : Matrix (Fin n) (Fin r) K → (Matrix (Fin n) (Fin r) K → ℂ) →ₗ[ℂ] (I → Matrix (Fin n) (Fin r) K → ℂ)` to `fun x₀ => LinearMap.pi fun i => M i f x₀ • LinearMap.id`.

Establish `hE : ∀ x₀ φ, φ ∈ Submodule.span ℂ {Ψ | ∃ l, Ψ = {x | ∃ l', ρ x = some l' ∧ l' ≤ l}.indicator fun _ => (1 : ℂ)} → E x₀ φ ∈ G.map (LinearMap.pi M)`. Introduce `x₀ φ hφ`. Establish `hle : Submodule.span ℂ {Ψ | ∃ l, Ψ = {x | ∃ l', ρ x = some l' ∧ l' ≤ l}.indicator fun _ => (1 : ℂ)} ≤ (G.map (LinearMap.pi M)).comap (E x₀)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨l, rfl⟩`.

Take `⟨F, hF, hFe⟩` from `hG x₀ (g l)`. Use `⟨F, hF, funext fun i => ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.pi_apply, E, LinearMap.smul_apply, LinearMap.id_apply]`. Rewrite using `[hFe i, hg l]`. Conclude with `hle hφ`.

Set `rep : Submodule O (Fin r → O ⧸ Ideal.span {d ^ 2}) → Matrix (Fin n) (Fin r) K` to `fun l => if h : ∃ x, ρ x = some l then h.choose else 0`. Establish `hdecomp : (fun i => M i f) = ∑ l, E (rep l) ({x | ρ x = some l}.indicator fun _ => (1 : ℂ))`. Use function extensionality and compare the values at `i x`. Simplify using `only [Finset.sum_apply, E, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, Set.indicator_apply, Set.mem_setOf_eq, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Break down `hρ : ρ x with _ | l0` into its components or cases.

Simplify using `[hnone i x hρ]`. Rewrite using `[Finset.sum_eq_single l0 (fun l _ hl => by simp [Ne.symm hl]) (by simp), if_pos rfl]`. Establish `h : ∃ x', ρ x' = some l0` using `⟨x, hρ⟩`. Simplify using `only [rep, h, dite_true]`. Conclude with `hfib i _ _ (hρ.trans h.choose_spec.symm)`.

Rewrite using `[hdecomp]`. Use `Submodule.sum_mem _ fun l _ => hE _ _ ?_` and prove the remaining obligations. Apply `_root_.GlobalTheory.mem_span_indicator_lowerSets` to reduce the goal to its premises. Introduce `x hx`. Simplify using `[Set.indicator_apply, hx]`.

Introduce `x x' hxx`. Simplify using `[Set.indicator_apply, hxx]`.
-/
theorem _root_.GlobalTheory.DownLift.SplitGen.exists_same_images_matrix (hr : r ≤ n) {d : O} (hd : d ≠ 0) {V I : Type}
    [AddCommGroup V] [Module ℂ V]
    (M : I → V →ₗ[ℂ] (Matrix (Fin n) (Fin r) K → ℂ)) (f : V) (G : Submodule ℂ V)
    (hP : ∀ i, M i f ∈ _root_.GlobalTheory.DownLift.SplitGen.invFun O K n r d)
    (hG : ∀ z (g : GL (Fin r) K), ∃ F ∈ G, ∀ i, M i F = M i f z • Set.indicator
      {x : Matrix (Fin n) (Fin r) K | ∃ z : Matrix (Fin n) (Fin r) O, x * (g : Matrix _ _ K) = z.map (algebraMap O K)}
      (fun _ => (1 : ℂ))) :
    ∃ F ∈ G, ∀ i, M i F = M i f := by

  classical
  set ι := algebraMap O K with hι
  have hιinj : Function.Injective ι := IsFractionRing.injective O K
  have hιd : ι d ≠ 0 := fun h => hd (hιinj (by rw [h, map_zero]))
  have hPer : ∀ i x (z : Matrix (Fin n) (Fin r) O), M i f (x + (d • z).map ι) = M i f x :=
    fun i => by obtain ⟨a, -, -⟩ := hP i; exact a
  have hSupp : ∀ i x, M i f x ≠ 0 → ∃ z : Matrix (Fin n) (Fin r) O, ι d • x = z.map ι :=
    fun i => by obtain ⟨-, a, -⟩ := hP i; exact a
  have hInv : ∀ i (h : GL (Fin n) O) x, M i f ((h : Matrix (Fin n) (Fin n) O).map ι * x) = M i f x :=
    fun i => by obtain ⟨-, -, a⟩ := hP i; exact a
  haveI := finite_quotient_span_sq (O := O) hd
  haveI : Finite (Submodule O (Fin r → O ⧸ Ideal.span {d ^ 2})) :=
    Finite.of_injective (fun N : Submodule O (Fin r → O ⧸ Ideal.span {d ^ 2}) =>
      (N : Set (Fin r → O ⧸ Ideal.span {d ^ 2}))) SetLike.coe_injective
  letI : Fintype (Submodule O (Fin r → O ⧸ Ideal.span {d ^ 2})) := Fintype.ofFinite _
  let red : Matrix (Fin n) (Fin r) O → Fin n → Fin r → O ⧸ Ideal.span {d ^ 2} :=
    fun y a b => Ideal.Quotient.mk _ (y a b)
  let ρ : Matrix (Fin n) (Fin r) K → Option (Submodule O (Fin r → O ⧸ Ideal.span {d ^ 2})) := fun x =>
    if h : ∃ y : Matrix (Fin n) (Fin r) O, ι d • x = y.map ι then
      some (Submodule.span O (Set.range (red h.choose))) else none
  have hnone : ∀ i x, ρ x = none → M i f x = 0 := by
    intro i x hx
    by_contra h0
    have hx' := hSupp i x h0
    simp [ρ, hx'] at hx
  have hfib : ∀ i x x', ρ x = ρ x' → M i f x = M i f x' := by
    intro i x x' hxx
    by_cases hx : ∃ y : Matrix (Fin n) (Fin r) O, ι d • x = y.map ι
    · have hx' : ∃ y : Matrix (Fin n) (Fin r) O, ι d • x' = y.map ι := by
        by_contra hx'
        simp [ρ, hx, hx'] at hxx
      simp only [ρ, hx, hx', dite_true, Option.some.injEq] at hxx
      obtain ⟨h, hh⟩ := _root_.GlobalTheory.exists_GL_of_span_range_eq O _ n _ _ hxx
      have hy := hx.choose_spec
      have hy' := hx'.choose_spec
      have hdiff : ∀ a b, ∃ c, hx'.choose a b = ((h : Matrix (Fin n) (Fin n) O) * hx.choose) a b + c * d ^ 2 := by
        intro a b
        have hs : ∀ c a : O, c • (Ideal.Quotient.mk (Ideal.span {d ^ 2}) a) =
            Ideal.Quotient.mk (Ideal.span {d ^ 2}) (c * a) := fun c a => by
          rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul]
        have e := congrFun (hh a) b
        simp only [red, Finset.sum_apply, Pi.smul_apply, hs, ← map_sum, Ideal.Quotient.eq,
          Ideal.mem_span_singleton'] at e
        obtain ⟨c, hc⟩ := e
        exact ⟨c, by rw [Matrix.mul_apply]; linear_combination -hc⟩
      choose z hz using hdiff
      have hx'eq : x' = (h : Matrix (Fin n) (Fin n) O).map ι * x + (d • Matrix.of z).map ι := by
        apply smul_right_injective _ hιd
        ext a b
        have e1 : ι d * x' a b = ι (hx'.choose a b) := by
          simpa using congrFun (congrFun hy' a) b
        have e2 : ∀ k, ι d * x k b = ι (hx.choose k b) := fun k => by
          simpa using congrFun (congrFun hy k) b
        simp only [smul_eq_mul, Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.map_apply,
          Matrix.of_apply, mul_add, Finset.mul_sum]
        rw [e1, hz a b]
        simp only [Matrix.mul_apply, map_add, map_sum, map_mul, map_pow, smul_eq_mul]
        have : ∀ k, ι d * (ι ((h : Matrix (Fin n) (Fin n) O) a k) * x k b) = ι ((h : Matrix (Fin n) (Fin n) O) a k) * ι (hx.choose k b) :=
          fun k => by rw [← e2 k]; ring
        simp only [this]
        ring
      rw [hx'eq, hPer, hInv]
    · have hx' : ¬ ∃ y : Matrix (Fin n) (Fin r) O, ι d • x' = y.map ι := by
        intro hx'
        simp [ρ, hx, hx'] at hxx
      rw [hnone i x (by simp [ρ, hx]), hnone i x' (by simp [ρ, hx'])]

  have hlow : ∀ l : Submodule O (Fin r → O ⧸ Ideal.span {d ^ 2}), ∃ g : GL (Fin r) K,
      {x : Matrix (Fin n) (Fin r) K | ∃ z : Matrix (Fin n) (Fin r) O, x * (g : Matrix _ _ K) = z.map ι} =
      {x | ∃ l', ρ x = some l' ∧ l' ≤ l} := by
    intro l
    let N₀ : Submodule O (Fin r → O) :=
      l.comap ((Ideal.Quotient.mkₐ O (Ideal.span {d ^ 2})).toLinearMap.compLeft (Fin r))
    have hmemN : ∀ v, v ∈ N₀ ↔ (fun j => Ideal.Quotient.mk (Ideal.span {d ^ 2}) (v j)) ∈ l :=
      fun v => Iff.rfl
    have hN : ∀ v, d ^ 2 • v ∈ N₀ := by
      intro v
      rw [hmemN]
      convert l.zero_mem
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_mul_right _ _))
    obtain ⟨B, hB, hBmem⟩ := exists_matrix_vecMul_span_eq_of_smul_mem N₀ (pow_ne_zero 2 hd) hN
    let A : Matrix (Fin r) (Fin r) K := (ι d)⁻¹ • B.map ι
    have hA : IsUnit A.det := by
      rw [isUnit_iff_ne_zero, Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hιd)) fun h => hB (hιinj (by rw [h, map_zero]))
    refine ⟨(Matrix.nonsingInvUnit A hA)⁻¹, ?_⟩
    have hgA : (((Matrix.nonsingInvUnit A hA)⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = A⁻¹ := by
      rw [Matrix.coe_units_inv]; rfl
    have key : ∀ x (z : Matrix (Fin n) (Fin r) O), x * A⁻¹ = z.map ι ↔ ι d • x = (z * B).map ι := by
      intro x z
      have hAinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
      have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
      have hzB : (z * B).map ι = z.map ι * B.map ι := Matrix.map_mul
      constructor
      · intro h
        have : x = z.map ι * A := by rw [← h, Matrix.mul_assoc, hAinv, Matrix.mul_one]
        rw [this, hzB]
        simp [A, Matrix.mul_smul, smul_smul, hιd]
      · intro h
        have : x = z.map ι * A := by
          apply smul_right_injective _ hιd
          simp only
          rw [h, hzB]
          simp [A, Matrix.mul_smul, smul_smul, hιd]
        rw [this, Matrix.mul_assoc, hAA, Matrix.mul_one]
    ext x
    simp only [Set.mem_setOf_eq, hgA, key]
    constructor
    · rintro ⟨z, hz⟩
      replace hz := (key x z).1 hz
      have hx : ∃ y : Matrix (Fin n) (Fin r) O, ι d • x = y.map ι := ⟨_, hz⟩
      refine ⟨_, dif_pos hx, ?_⟩
      have hy : hx.choose = z * B := Matrix.map_injective hιinj (hx.choose_spec.symm.trans hz)
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      have : hx.choose a ∈ N₀ := (hBmem _).2 ⟨z a, by
        rw [hy]; ext j; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]⟩
      exact this
    · rintro ⟨l', hl', hle⟩
      have hx : ∃ y : Matrix (Fin n) (Fin r) O, ι d • x = y.map ι := by
        by_contra hx
        simp [ρ, hx] at hl'
      simp only [ρ, hx, dite_true, Option.some.injEq] at hl'
      have hrow : ∀ a, ∃ w, hx.choose a = Matrix.vecMul w B := fun a =>
        (hBmem _).1 (hle (hl' ▸ Submodule.subset_span ⟨a, rfl⟩))
      choose w hw using hrow
      refine ⟨Matrix.of w, (key x _).2 (hx.choose_spec.trans ?_)⟩
      congr 1
      ext a j
      rw [hw a]
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  choose g hg using hlow
  suffices hS : (fun i => M i f) ∈ G.map (LinearMap.pi M) by
    obtain ⟨F, hF, hFe⟩ := hS
    exact ⟨F, hF, fun i => by simpa using congrFun hFe i⟩
  let E : Matrix (Fin n) (Fin r) K →
      (Matrix (Fin n) (Fin r) K → ℂ) →ₗ[ℂ] (I → Matrix (Fin n) (Fin r) K → ℂ) :=
    fun x₀ => LinearMap.pi fun i => M i f x₀ • LinearMap.id
  have hE : ∀ x₀ φ, φ ∈ Submodule.span ℂ
      {Ψ | ∃ l, Ψ = {x | ∃ l', ρ x = some l' ∧ l' ≤ l}.indicator fun _ => (1 : ℂ)} →
      E x₀ φ ∈ G.map (LinearMap.pi M) := by
    intro x₀ φ hφ
    have hle : Submodule.span ℂ
        {Ψ | ∃ l, Ψ = {x | ∃ l', ρ x = some l' ∧ l' ≤ l}.indicator fun _ => (1 : ℂ)} ≤
        (G.map (LinearMap.pi M)).comap (E x₀) := by
      rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      obtain ⟨F, hF, hFe⟩ := hG x₀ (g l)
      refine ⟨F, hF, funext fun i => ?_⟩
      simp only [LinearMap.pi_apply, E, LinearMap.smul_apply, LinearMap.id_apply]
      rw [hFe i, hg l]
    exact hle hφ
  let rep : Submodule O (Fin r → O ⧸ Ideal.span {d ^ 2}) → Matrix (Fin n) (Fin r) K :=
    fun l => if h : ∃ x, ρ x = some l then h.choose else 0
  have hdecomp : (fun i => M i f) =
      ∑ l, E (rep l) ({x | ρ x = some l}.indicator fun _ => (1 : ℂ)) := by
    funext i x
    simp only [Finset.sum_apply, E, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.id_apply,
      Pi.smul_apply, Set.indicator_apply, Set.mem_setOf_eq, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rcases hρ : ρ x with _ | l0
    · simp [hnone i x hρ]
    · rw [Finset.sum_eq_single l0 (fun l _ hl => by simp [Ne.symm hl]) (by simp), if_pos rfl]
      have h : ∃ x', ρ x' = some l0 := ⟨x, hρ⟩
      simp only [rep, h, dite_true]
      exact hfib i _ _ (hρ.trans h.choose_spec.symm)
  rw [hdecomp]
  refine Submodule.sum_mem _ fun l _ => hE _ _ ?_
  apply _root_.GlobalTheory.mem_span_indicator_lowerSets
  · intro x hx
    simp [Set.indicator_apply, hx]
  · intro x x' hxx
    simp [Set.indicator_apply, hxx]

end Matrices

end GlobalTheory.DownLift.SplitGen

import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoUpperBoundOfEdgeCount

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems

section Gen

variable {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ}

def emb (w : Fin k → W) : Fin k → Qq := fun i => algebraMap W Qq (w i)

abbrev mapM (N : Matrix (Fin k) (Fin k) W) : Matrix (Fin k) (Fin k) Qq := (algebraMap W Qq).mapMatrix N

/- English proof (translation)
Unfold `colSpan`. Rewrite using `[Submodule.mem_span_range_iff_exists_fun]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Use `⟨y, funext fun i => ?_⟩` and prove the remaining obligations.

Simplify using `[Finset.sum_apply, Algebra.smul_def, mul_comm]`. Introduce and unpack `⟨y, rfl⟩`. Use `⟨y, funext fun i => ?_⟩` and prove the remaining obligations. Simplify using `[Finset.sum_apply, Algebra.smul_def, mul_comm]`.
-/
theorem mem_colSpan_iff (h : Matrix (Fin k) (Fin k) Qq) (x : Fin k → Qq) :
    x ∈ colSpan W h ↔ ∃ y : Fin k → W, x = fun i => ∑ c, h i c * algebraMap W Qq (y c) := by
  unfold colSpan
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, funext fun i => ?_⟩
    simp [Finset.sum_apply, Algebra.smul_def, mul_comm]
  · rintro ⟨y, rfl⟩
    refine ⟨y, funext fun i => ?_⟩
    simp [Finset.sum_apply, Algebra.smul_def, mul_comm]

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨c, rfl⟩`. Use `(mem_colSpan_iff h _).2 ⟨fun j => N j c, funext fun i => ?_⟩` and prove the remaining obligations. Simplify using `[Matrix.mul_apply, mapM, RingHom.mapMatrix_apply, Matrix.map_apply]`.
-/
theorem colSpan_mul_le (h : Matrix (Fin k) (Fin k) Qq) (N : Matrix (Fin k) (Fin k) W) :
    colSpan W (h * mapM N) ≤ colSpan W h := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨c, rfl⟩
  refine (mem_colSpan_iff h _).2 ⟨fun j => N j c, funext fun i => ?_⟩
  simp [Matrix.mul_apply, mapM, RingHom.mapMatrix_apply, Matrix.map_apply]

/- English proof (translation)
Use `le_antisymm (colSpan_mul_le h N) ?_` and prove the remaining obligations. Establish `h1 : h * mapM N * mapM N⁻¹ = h`. Rewrite using `[Matrix.mul_assoc, ← map_mul, Matrix.mul_nonsing_inv N hN, map_one, Matrix.mul_one]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem colSpan_unimod (h : Matrix (Fin k) (Fin k) Qq) (N : Matrix (Fin k) (Fin k) W) (hN : IsUnit N.det) :
    colSpan W (h * mapM N) = colSpan W h := by
  refine le_antisymm (colSpan_mul_le h N) ?_
  have h1 : h * mapM N * mapM N⁻¹ = h := by
    rw [Matrix.mul_assoc, ← map_mul, Matrix.mul_nonsing_inv N hN, map_one, Matrix.mul_one]
  calc colSpan W h = colSpan W (h * mapM N * mapM N⁻¹) := by rw [h1]
    _ ≤ colSpan W (h * mapM N) := colSpan_mul_le _ _

/- English proof (translation)
Unfold `colSpan`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Use `congr 2`.
-/
theorem map_colSpan (g : GL (Fin k) Qq) (h : Matrix (Fin k) (Fin k) Qq) :
    (colSpan W h).map (nt_phi W g) = colSpan W ((g : Matrix (Fin k) (Fin k) Qq) * h) := by
  unfold colSpan
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2

def dj (j : Fin k) (c : Qq) : Matrix (Fin k) (Fin k) Qq := Matrix.diagonal fun i => if i = j then c else 1

/- English proof (translation)
Simplify using `[dj, Matrix.det_diagonal]`.
-/
theorem dj_det (j : Fin k) (c : Qq) : (dj j c).det = c := by
  simp [dj, Matrix.det_diagonal]

/- English proof (translation)
Simplify using `only [dj, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem dj_mul (j : Fin k) (c d : Qq) : dj j c * dj j d = dj j (c * d) := by
  simp only [dj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

/- English proof (translation)
Simplify using `[dj]`.
-/
theorem dj_one (j : Fin k) : dj j (1 : Qq) = 1 := by
  simp [dj]

end Gen

section Base

variable {p n' : ℕ} (R : RS p n') {k : ℕ}

/- English proof (translation)
Use `haveI := R.std.1.frac_alt`. Conclude with `IsFractionRing.injective R.W R.Qq`.
-/
theorem RS.injW : Function.Injective (algebraMap R.W R.Qq) := by
  haveI := R.std.1.frac_alt
  exact IsFractionRing.injective R.W R.Qq

/- English proof (translation)
Establish `h1 : (p : R.W) ≠ 0` using `R.std.1.p_unif.ne_zero`. Rewrite using `[← map_natCast (algebraMap R.W R.Qq)]`. Conclude with `fun h => h1 ((map_eq_zero_iff _ (RS.injW R)).1 h)`.
-/
theorem RS.pQ_ne : (p : R.Qq) ≠ 0 := by
  have h1 : (p : R.W) ≠ 0 := R.std.1.p_unif.ne_zero
  rw [← map_natCast (algebraMap R.W R.Qq)]
  exact fun h => h1 ((map_eq_zero_iff _ (RS.injW R)).1 h)

def embLin (R : RS p n') (k : ℕ) : (Fin k → R.W) →ₗ[R.W] (Fin k → R.Qq) where
  toFun := emb
  map_add' := by intro x y; funext i; simp [emb]
  map_smul' := by intro c x; funext i; simp [emb, Algebra.smul_def]

/- English proof (translation)
Introduce `x y hxy`. Use function extensionality and compare the values at `i`. Conclude with `RS.injW R (congrFun hxy i)`.
-/
theorem embLin_inj : Function.Injective (embLin R k) := by
  intro x y hxy
  funext i
  exact RS.injW R (congrFun hxy i)

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[mem_colSpan_iff, LinearMap.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Use `⟨y, funext fun i => ?_⟩` and prove the remaining obligations.

Simplify using `[embLin, emb, Matrix.one_apply]`. Introduce and unpack `⟨y, rfl⟩`. Use `⟨y, funext fun i => ?_⟩` and prove the remaining obligations. Simplify using `[embLin, emb, Matrix.one_apply]`.
-/
theorem colSpan_one_eq : colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) = LinearMap.range (embLin R k) := by
  ext x
  rw [mem_colSpan_iff, LinearMap.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, funext fun i => ?_⟩
    simp [embLin, emb, Matrix.one_apply]
  · rintro ⟨y, rfl⟩
    refine ⟨y, funext fun i => ?_⟩
    simp [embLin, emb, Matrix.one_apply]

/- English proof (translation)
Rewrite using `[mem_colSpan_iff]`. Apply the tactic sequence `constructor <;> rintro ⟨y, rfl⟩ <;> refine ⟨y, funext fun i => ?_⟩ <;>`. Apply the tactic sequence `by_cases hij : i = j <;> simp [dj, emb, Matrix.diagonal_apply, hij]`.
-/
theorem mem_dj_iff (j : Fin k) (x : Fin k → R.Qq) :
    x ∈ colSpan R.W (dj j (p : R.Qq)) ↔ ∃ y : Fin k → R.W, x = emb (fun i => (if i = j then (p : R.W) else 1) * y i) := by
  rw [mem_colSpan_iff]
  constructor <;> rintro ⟨y, rfl⟩ <;> refine ⟨y, funext fun i => ?_⟩ <;>
    by_cases hij : i = j <;> simp [dj, emb, Matrix.diagonal_apply, hij]

/- English proof (translation)
Establish `hstd` using `R.std.1`. Establish `htgt : ∀ x, x ∈ colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) ↔ ∃ y, embLin R k y = x`. Introduce `x`. Rewrite using `[colSpan_one_eq R]`. Conclude with `LinearMap.mem_range`.

Establish `hsrc : ∀ x, x ∈ colSpan R.W (dj j (p : R.Qq)) ↔ ∃ y : Fin k → R.W, x = emb y ∧ y j ∈ Ideal.span {(p : R.W)}`. Introduce `x`. Rewrite using `[mem_dj_iff R]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`.

Use `⟨_, rfl, ?_⟩` and prove the remaining obligations. Simplify using `only [if_pos rfl]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`. Introduce and unpack `⟨y, rfl, hy⟩`. Take `⟨z, hz⟩` from `Ideal.mem_span_singleton'.1 hy`.

Use `⟨fun i => if i = j then z else y i, ?_⟩` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using `[← hz, mul_comm]`. Simplify using `[hij]`. Set `e` to `LinearEquiv.ofInjective (embLin R k) (embLin_inj R)`. Set `E : colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) ≃ₗ[R.W] (Fin k → R.W)` to `(LinearEquiv.ofEq _ _ (colSpan_one_eq R)).trans e.symm`. Establish `hE : ∀ x, emb (E x) = (x : Fin k → R.Qq)`.

Introduce `x`. Establish `h2` using `congrArg Subtype.val (e.apply_symm_apply (LinearEquiv.ofEq _ _ (colSpan_one_eq R) x))`. Rewrite `h2` using `[LinearEquiv.ofInjective_apply]`. Conclude with `h2`. Set `ψ : colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) →ₗ[R.W] R.W ⧸ Ideal.span {(p : R.W)}` to `(Ideal.span {(p : R.W)}).mkQ ∘ₗ LinearMap.proj j ∘ₗ E.toLinearMap`.

Establish `hψ : ∀ x, ψ x = (Submodule.Quotient.mk (E x j) : R.W ⧸ Ideal.span {(p : R.W)})` using `fun x => rfl`. Establish `hsurj : Function.Surjective ψ`. Introduce `q`. Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Use `⟨E.symm (Pi.single j a), ?_⟩` and prove the remaining obligations.

Rewrite using `[hψ, LinearEquiv.apply_symm_apply, Pi.single_eq_same]`. Establish `hker : Submodule.comap (colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq)).subtype (colSpan R.W (dj j (p : R.Qq))) = LinearMap.ker ψ`. Use extensionality with `x`. Rewrite using `[Submodule.mem_comap, LinearMap.mem_ker, hψ, Submodule.Quotient.mk_eq_zero, Submodule.subtype_apply, hsrc]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, hyj⟩`. Establish `hxy : E x = y` using `embLin_inj R ((hE x).trans hy)`. Rewrite using `[hxy]`. Conclude with `hyj`. Introduce `h`.

Conclude with `⟨E x, (hE x).symm, h⟩`. Use `⟨⟨dj j (p : R.Qq), ?_, rfl⟩, ⟨1, by simp, rfl⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[dj_det]`. Conclude with `isUnit_iff_ne_zero.2 (RS.pQ_ne R)`. Introduce `x hx`.

Take `⟨y, rfl, -⟩` from `(hsrc x).1 hx`. Conclude with `(htgt _).2 ⟨y, rfl⟩`. Introduce `x hx`. Take `⟨y, rfl⟩` from `(htgt x).1 hx`. Use `(hsrc _).2 ⟨(p : R.W) • y, ?_, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Simplify using `[embLin, emb, Algebra.smul_def]`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`. Use `show Nat.card (↥(colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq)) ⧸ Submodule.comap (colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq)).subtype (colSpan R.W (dj j (p : R.Qq)))) = p ^ (n' * 1)`.

Rewrite using `[hker, Nat.card_congr (ψ.quotKerEquivOfSurjective hsurj).toEquiv, hstd.res_card, mul_one]`.
-/
theorem baseEdge (j : Fin k) :
    IsEdge p n' 1 (⟨colSpan R.W (dj j (p : R.Qq)), colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq)⟩ :
      Edge R.W R.Qq k) := by
  classical
  have hstd := R.std.1
  have htgt : ∀ x, x ∈ colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) ↔ ∃ y, embLin R k y = x := by
    intro x
    rw [colSpan_one_eq R]
    exact LinearMap.mem_range
  have hsrc : ∀ x, x ∈ colSpan R.W (dj j (p : R.Qq)) ↔
      ∃ y : Fin k → R.W, x = emb y ∧ y j ∈ Ideal.span {(p : R.W)} := by
    intro x
    rw [mem_dj_iff R]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨_, rfl, ?_⟩
      simp only [if_pos rfl]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · rintro ⟨y, rfl, hy⟩
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hy
      refine ⟨fun i => if i = j then z else y i, ?_⟩
      congr 1
      funext i
      by_cases hij : i = j
      · subst hij
        simp [← hz, mul_comm]
      · simp [hij]
  let e := LinearEquiv.ofInjective (embLin R k) (embLin_inj R)
  let E : colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) ≃ₗ[R.W] (Fin k → R.W) :=
    (LinearEquiv.ofEq _ _ (colSpan_one_eq R)).trans e.symm
  have hE : ∀ x, emb (E x) = (x : Fin k → R.Qq) := by
    intro x
    have h2 := congrArg Subtype.val (e.apply_symm_apply (LinearEquiv.ofEq _ _ (colSpan_one_eq R) x))
    rw [LinearEquiv.ofInjective_apply] at h2
    exact h2
  let ψ : colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) →ₗ[R.W] R.W ⧸ Ideal.span {(p : R.W)} :=
    (Ideal.span {(p : R.W)}).mkQ ∘ₗ LinearMap.proj j ∘ₗ E.toLinearMap
  have hψ : ∀ x, ψ x = (Submodule.Quotient.mk (E x j) : R.W ⧸ Ideal.span {(p : R.W)}) := fun x => rfl
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine ⟨E.symm (Pi.single j a), ?_⟩
    rw [hψ, LinearEquiv.apply_symm_apply, Pi.single_eq_same]
  have hker : Submodule.comap (colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq)).subtype
      (colSpan R.W (dj j (p : R.Qq))) = LinearMap.ker ψ := by
    ext x
    rw [Submodule.mem_comap, LinearMap.mem_ker, hψ, Submodule.Quotient.mk_eq_zero, Submodule.subtype_apply, hsrc]
    constructor
    · rintro ⟨y, hy, hyj⟩
      have hxy : E x = y := embLin_inj R ((hE x).trans hy)
      rw [hxy]
      exact hyj
    · intro h
      exact ⟨E x, (hE x).symm, h⟩
  refine ⟨⟨dj j (p : R.Qq), ?_, rfl⟩, ⟨1, by simp, rfl⟩, ?_, ?_, ?_⟩
  · rw [dj_det]
    exact isUnit_iff_ne_zero.2 (RS.pQ_ne R)
  · intro x hx
    obtain ⟨y, rfl, -⟩ := (hsrc x).1 hx
    exact (htgt _).2 ⟨y, rfl⟩
  · intro x hx
    obtain ⟨y, rfl⟩ := (htgt x).1 hx
    refine (hsrc _).2 ⟨(p : R.W) • y, ?_, ?_⟩
    · funext i
      simp [embLin, emb, Algebra.smul_def]
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · show Nat.card (↥(colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq)) ⧸
      Submodule.comap (colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq)).subtype
        (colSpan R.W (dj j (p : R.Qq)))) = p ^ (n' * 1)
    rw [hker, Nat.card_congr (ψ.quotKerEquivOfSurjective hsurj).toEquiv, hstd.res_card, mul_one]

end Base

end Formalism.MainNotions.flipOneThree.Pf

end

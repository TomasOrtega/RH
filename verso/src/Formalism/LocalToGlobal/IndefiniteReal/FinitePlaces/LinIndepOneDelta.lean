import Formalism.LocalToGlobal.IndefiniteReal.InjectiveDecompositionAction

noncomputable section

open scoped TensorProduct

namespace Formalism.IndefR.Fin.U1

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero F]

/- English proof (translation)
Establish `hex : ∃ e : E, e ∉ (algebraMap F E).range`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hsurj : Function.Surjective (Algebra.linearMap F E)` using `fun e => by`. Take `⟨x, hx⟩` from `hne e`.

Conclude with `⟨x, hx⟩`. Establish `hinj : Function.Injective (Algebra.linearMap F E)` using `(algebraMap F E).injective`. Establish `hfr` using `(LinearEquiv.ofBijective (Algebra.linearMap F E) ⟨hinj, hsurj⟩).finrank_eq`. Rewrite `hfr` using `[Module.finrank_self, h2]`. Evaluate the numerical expressions using `at hfr`.

Take `⟨e, he⟩` from `hex`. Use `⟨e - σ e, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, hinv]`. Normalize the expressions using the abelian group laws. Introduce `h0`.

Apply `he` to reduce the goal to its premises. Rewrite using `[← hfix]`. Conclude with `(sub_eq_zero.mp h0).symm`.
-/
theorem exists_delta (σ : E →ₐ[F] E) (hinv : ∀ e, σ (σ e) = e)
    (hfix : ∀ e, σ e = e ↔ e ∈ (algebraMap F E).range) (h2 : Module.finrank F E = 2) :
    ∃ δ : E, σ δ = -δ ∧ δ ≠ 0 := by
  have hex : ∃ e : E, e ∉ (algebraMap F E).range := by
    by_contra hne
    push_neg at hne
    have hsurj : Function.Surjective (Algebra.linearMap F E) := fun e => by
      obtain ⟨x, hx⟩ := hne e
      exact ⟨x, hx⟩
    have hinj : Function.Injective (Algebra.linearMap F E) := (algebraMap F E).injective
    have hfr := (LinearEquiv.ofBijective (Algebra.linearMap F E) ⟨hinj, hsurj⟩).finrank_eq
    rw [Module.finrank_self, h2] at hfr
    norm_num at hfr
  obtain ⟨e, he⟩ := hex
  refine ⟨e - σ e, ?_, ?_⟩
  · rw [map_sub, hinv]
    abel
  · intro h0
    apply he
    rw [← hfix]
    exact (sub_eq_zero.mp h0).symm

variable (σ : E →ₐ[F] E) (δ : E)

/- English proof (translation)
Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t h`. Establish `h' : σ (s • (1 : E) + t • δ) = 0` using `by rw [h, map_zero]`. Rewrite `h'` using `[map_add, map_smul, map_smul, map_one, hδ]`. Establish `hs : (2 : F) • (s • (1 : E)) = 0`.

Rewrite using `[two_smul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hs0 : s = 0`. Rewrite `hs` using `[smul_smul, smul_eq_zero]`. Break down `hs with hs | hs` into its components or cases.

Break down `mul_eq_zero.mp hs with h2' | h2'` into its components or cases. Conclude with `absurd h2' two_ne_zero`. Conclude with `h2'`. Conclude with `absurd hs one_ne_zero`. Substitute `hs0` using the available equality.

Use `⟨rfl, ?_⟩` and prove the remaining obligations. Rewrite `h` using `[zero_smul, zero_add, smul_eq_zero]`. Conclude with `h.resolve_right hδ0`.
-/
theorem linIndep_one_delta (hδ : σ δ = -δ) (hδ0 : δ ≠ 0) : LinearIndependent F ![(1 : E), δ] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h' : σ (s • (1 : E) + t • δ) = 0 := by rw [h, map_zero]
  rw [map_add, map_smul, map_smul, map_one, hδ] at h'
  have hs : (2 : F) • (s • (1 : E)) = 0 := by
    rw [two_smul]
    calc s • (1 : E) + s • 1 = (s • 1 + t • δ) + (s • 1 + t • -δ) := by rw [smul_neg]; abel
      _ = 0 := by rw [h, h', add_zero]
  have hs0 : s = 0 := by
    rw [smul_smul, smul_eq_zero] at hs
    rcases hs with hs | hs
    · rcases mul_eq_zero.mp hs with h2' | h2'
      · exact absurd h2' two_ne_zero
      · exact h2'
    · exact absurd hs one_ne_zero
  subst hs0
  refine ⟨rfl, ?_⟩
  rw [zero_smul, zero_add, smul_eq_zero] at h
  exact h.resolve_right hδ0

end Gen

section Coords

variable {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero F]
variable (σ : E →ₐ[F] E) (δ : E) (hδ : σ δ = -δ) (hδ0 : δ ≠ 0) (h2 : Module.finrank F E = 2)
variable (R : Type) [CommRing R] [Algebra F R]

def bE : Module.Basis (Fin 2) F E :=
  basisOfLinearIndependentOfCardEqFinrank (linIndep_one_delta σ δ hδ hδ0) (by simp [h2])

/- English proof (translation)
Simplify using `[bE, coe_basisOfLinearIndependentOfCardEqFinrank]`.
-/
theorem bE_zero : bE σ δ hδ hδ0 h2 0 = 1 := by
  simp [bE, coe_basisOfLinearIndependentOfCardEqFinrank]
/- English proof (translation)
Simplify using `[bE, coe_basisOfLinearIndependentOfCardEqFinrank]`.
-/
theorem bE_one : bE σ δ hδ hδ0 h2 1 = δ := by
  simp [bE, coe_basisOfLinearIndependentOfCardEqFinrank]

def bR : Module.Basis (Fin 2) R (R ⊗[F] E) := Algebra.TensorProduct.basis R (bE σ δ hδ hδ0 h2)

def mkE (a b : R) : R ⊗[F] E := a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] δ

/- English proof (translation)
Simplify using `only [mkE, bR, Algebra.TensorProduct.basis_apply, bE_zero, bE_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.
-/
theorem mkE_eq (a b : R) :
    mkE δ R a b = a • bR σ δ hδ hδ0 h2 R 0 + b • bR σ δ hδ hδ0 h2 R 1 := by
  simp only [mkE, bR, Algebra.TensorProduct.basis_apply, bE_zero, bE_one, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]

def cP : R ⊗[F] E →ₗ[R] R := (bR σ δ hδ hδ0 h2 R).coord 0

def cQ : R ⊗[F] E →ₗ[R] R := (bR σ δ hδ hδ0 h2 R).coord 1

/- English proof (translation)
Rewrite using `[mkE_eq σ δ hδ hδ0 h2 R]`. Simplify using `[cP, Module.Basis.coord_apply, Finsupp.single_apply]`.
-/
theorem re_mk (a b : R) : cP σ δ hδ hδ0 h2 R (mkE δ R a b) = a := by
  rw [mkE_eq σ δ hδ hδ0 h2 R]
  simp [cP, Module.Basis.coord_apply, Finsupp.single_apply]

/- English proof (translation)
Rewrite using `[mkE_eq σ δ hδ hδ0 h2 R]`. Simplify using `[cQ, Module.Basis.coord_apply, Finsupp.single_apply]`.
-/
theorem cQ_mkE (a b : R) : cQ σ δ hδ hδ0 h2 R (mkE δ R a b) = b := by
  rw [mkE_eq σ δ hδ hδ0 h2 R]
  simp [cQ, Module.Basis.coord_apply, Finsupp.single_apply]

/- English proof (translation)
Rewrite using `[mkE_eq σ δ hδ hδ0 h2 R]`. Establish `hx` using `(bR σ δ hδ hδ0 h2 R).sum_repr x`. Rewrite `hx` using `[Fin.sum_univ_two]`. Simplify `hx` using `[cP, cQ, Module.Basis.coord_apply]`.
-/
theorem mkE_cP_cQ (x : R ⊗[F] E) :
    mkE δ R (cP σ δ hδ hδ0 h2 R x) (cQ σ δ hδ hδ0 h2 R x) = x := by
  rw [mkE_eq σ δ hδ hδ0 h2 R]
  have hx := (bR σ δ hδ hδ0 h2 R).sum_repr x
  rw [Fin.sum_univ_two] at hx
  simpa [cP, cQ, Module.Basis.coord_apply] using hx

include σ hδ hδ0 h2 in
/- English proof (translation)
Establish `h1` using `congrArg (cP σ δ hδ hδ0 h2 R) h`. Establish `h2'` using `congrArg (cQ σ δ hδ hδ0 h2 R) h`. Rewrite `h1` using `[re_mk, re_mk]`. Rewrite `h2'` using `[cQ_mkE, cQ_mkE]`. Conclude with `⟨h1, h2'⟩`.
-/
theorem mkE_inj {a b a' b' : R} (h : mkE (F := F) δ R a b = mkE (F := F) δ R a' b') : a = a' ∧ b = b' := by
  have h1 := congrArg (cP σ δ hδ hδ0 h2 R) h
  have h2' := congrArg (cQ σ δ hδ hδ0 h2 R) h
  rw [re_mk, re_mk] at h1
  rw [cQ_mkE, cQ_mkE] at h2'
  exact ⟨h1, h2'⟩

end Coords

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (σ : E →ₐ[F] E) (δ : E) (hδ : σ δ = -δ) (Δ : F) (hΔ : algebraMap F E Δ = δ * δ)
variable (R : Type) [CommRing R] [Algebra F R]

include hΔ in
/- English proof (translation)
Simplify using `only [mkE, add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Rewrite using `[← hΔ, Algebra.algebraMap_eq_smul_one (A := E) Δ, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def Δ (b * b'), TensorProduct.add_tmul, TensorProduct.add_tmul]`. Normalize the expressions using the abelian group laws.
-/
theorem mkE_mul (a b a' b' : R) :
    mkE (F := F) δ R a b * mkE (F := F) δ R a' b' =
      mkE (F := F) δ R (a * a' + algebraMap F R Δ * (b * b')) (a * b' + b * a') := by
  simp only [mkE, add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [← hΔ, Algebra.algebraMap_eq_smul_one (A := E) Δ, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    Algebra.smul_def Δ (b * b'), TensorProduct.add_tmul, TensorProduct.add_tmul]
  abel

/- English proof (translation)
Simplify using `[mkE, Algebra.TensorProduct.one_def]`.
-/
theorem mkE_one : mkE (F := F) δ R 1 0 = 1 := by
  simp [mkE, Algebra.TensorProduct.one_def]

/- English proof (translation)
Simplify using `[mkE]`.
-/
theorem mkE_zero : mkE (F := F) δ R 0 0 = 0 := by
  simp [mkE]

/- English proof (translation)
Simplify using `only [mkE, TensorProduct.add_tmul]`. Normalize the expressions using the abelian group laws.
-/
theorem mkE_add (a b a' b' : R) :
    mkE (F := F) δ R a b + mkE (F := F) δ R a' b' = mkE (F := F) δ R (a + a') (b + b') := by
  simp only [mkE, TensorProduct.add_tmul]
  abel

/- English proof (translation)
Simplify using `only [mkE, TensorProduct.sub_tmul]`. Normalize the expressions using the abelian group laws.
-/
theorem mkE_sub (a b a' b' : R) :
    mkE (F := F) δ R a b - mkE (F := F) δ R a' b' = mkE (F := F) δ R (a - a') (b - b') := by
  simp only [mkE, TensorProduct.sub_tmul]
  abel

/- English proof (translation)
Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Simplify using `[mkE]`.
-/
theorem algebraMap_eq_mkE (a : R) : algebraMap R (R ⊗[F] E) a = mkE (F := F) δ R a 0 := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul,
    mul_one]
  simp [mkE]

/- English proof (translation)
Rewrite using `[← Algebra.smul_def]`. Simplify using `only [mkE, smul_add, TensorProduct.smul_tmul', smul_eq_mul]`.
-/
theorem smul_mkE (r a b : R) : algebraMap R (R ⊗[F] E) r * mkE (F := F) δ R a b = mkE (F := F) δ R (r * a) (r * b) := by
  rw [← Algebra.smul_def]
  simp only [mkE, smul_add, TensorProduct.smul_tmul', smul_eq_mul]

include hδ in
/- English proof (translation)
Simplify using `only [mkE, map_add, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one, hδ, TensorProduct.tmul_neg, TensorProduct.neg_tmul]`.
-/
theorem conj_mkE (a b : R) :
    (Algebra.TensorProduct.map (AlgHom.id F R) σ) (mkE (F := F) δ R a b) = mkE (F := F) δ R a (-b) := by
  simp only [mkE, map_add, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one, hδ,
    TensorProduct.tmul_neg, TensorProduct.neg_tmul]

include hΔ in
/- English proof (translation)
Rewrite using `[mkE_mul δ Δ hΔ R, show a * a + algebraMap F R Δ * (b * -b) = a * a - algebraMap F R Δ * (b * b) by ring, show a * -b + b * a = 0 by ring]`.
-/
theorem mkE_norm (a b : R) :
    mkE (F := F) δ R a b * mkE (F := F) δ R a (-b) = mkE (F := F) δ R (a * a - algebraMap F R Δ * (b * b)) 0 := by
  rw [mkE_mul δ Δ hΔ R, show a * a + algebraMap F R Δ * (b * -b) = a * a - algebraMap F R Δ * (b * b) by ring,
    show a * -b + b * a = 0 by ring]

/- English proof (translation)
Rewrite using `[Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_add, ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one (A := E) α, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one]`. Both sides reduce to the same expression.
-/
theorem incl_eq_mkE (α β : F) :
    (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E) (algebraMap F E α + algebraMap F E β * δ) =
      mkE (F := F) δ R (algebraMap F R α) (algebraMap F R β) := by
  rw [Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_add, ← Algebra.smul_def,
    Algebra.algebraMap_eq_smul_one (A := E) α, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul,
    ← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one]
  rfl

end Alg

end Formalism.IndefR.Fin.U1

end

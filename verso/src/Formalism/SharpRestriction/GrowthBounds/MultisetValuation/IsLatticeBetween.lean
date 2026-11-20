import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.CountLoc

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf.Cnt

open Formalism.MainNotions.G

section Gen

variable {R : Type*} [CommRing R] {M M1 M2 : Type*} [AddCommGroup M] [AddCommGroup M1] [AddCommGroup M2]
  [Module R M] [Module R M1] [Module R M2]

/- English proof (translation)
Establish `e1` using `(f1.quotKerEquivOfSurjective h1).toEquiv`. Establish `e2` using `(f2.quotKerEquivOfSurjective h2).toEquiv`. Establish `e3` using `(Submodule.quotEquivOfEq _ _ hk).toEquiv`. Conclude with `Nat.card_congr (e1.symm.trans (e3.trans e2))`.
-/
theorem card_eq_of_ker_eq (f1 : M →ₗ[R] M1) (f2 : M →ₗ[R] M2) (h1 : Function.Surjective f1)
    (h2 : Function.Surjective f2) (hk : LinearMap.ker f1 = LinearMap.ker f2) : Nat.card M1 = Nat.card M2 := by
  have e1 := (f1.quotKerEquivOfSurjective h1).toEquiv
  have e2 := (f2.quotKerEquivOfSurjective h2).toEquiv
  have e3 := (Submodule.quotEquivOfEq _ _ hk).toEquiv
  exact Nat.card_congr (e1.symm.trans (e3.trans e2))

/- English proof (translation)
Establish `hmem : ∀ m, φ m ∈ T` using `fun m => hφ ▸ LinearMap.mem_range_self φ m`. Set `f1 : M →ₗ[R] (↥T ⧸ Submodule.comap T.subtype S)` to `(Submodule.comap T.subtype S).mkQ.comp (φ.codRestrict T hmem)`. Apply `card_eq_of_ker_eq f1 f2 _ h2` to reduce the goal to its premises. Use extensionality with `m`. Rewrite using `[LinearMap.mem_ker, LinearMap.mem_ker, ← hk m]`.

Use `show (Submodule.comap T.subtype S).mkQ (φ.codRestrict T hmem m) = 0 ↔ _`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Both sides reduce to the same expression. Introduce `y`. Take `⟨⟨t, ht⟩, rfl⟩` from `Submodule.mkQ_surjective _ y`.

Rewrite `ht` using `[← hφ]`. Take `⟨m, rfl⟩` from `ht`. Conclude with `⟨m, rfl⟩`.
-/
theorem card_quot (T S : Submodule R M1) (φ : M →ₗ[R] M1) (hφ : LinearMap.range φ = T) (f2 : M →ₗ[R] M2)
    (h2 : Function.Surjective f2) (hk : ∀ m, φ m ∈ S ↔ f2 m = 0) :
    Nat.card (↥T ⧸ Submodule.comap T.subtype S) = Nat.card M2 := by
  have hmem : ∀ m, φ m ∈ T := fun m => hφ ▸ LinearMap.mem_range_self φ m
  let f1 : M →ₗ[R] (↥T ⧸ Submodule.comap T.subtype S) :=
    (Submodule.comap T.subtype S).mkQ.comp (φ.codRestrict T hmem)
  apply card_eq_of_ker_eq f1 f2 _ h2
  · ext m
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ← hk m]
    show (Submodule.comap T.subtype S).mkQ (φ.codRestrict T hmem m) = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rfl
  · intro y
    obtain ⟨⟨t, ht⟩, rfl⟩ := Submodule.mkQ_surjective _ y
    rw [← hφ] at ht
    obtain ⟨m, rfl⟩ := ht
    exact ⟨m, rfl⟩

end Gen

variable {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {n : ℕ}

def psi (g : Matrix (Fin n) (Fin n) Qq) : (Fin n → W) →ₗ[W] (Fin n → Qq) :=
  ((Matrix.mulVecLin g).restrictScalars W).comp ((Algebra.linearMap W Qq).compLeft (Fin n))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem psi_apply (g : Matrix (Fin n) (Fin n) Qq) (w : Fin n → W) :
    psi g w = g.mulVec (fun c => algebraMap W Qq (w c)) := rfl

/- English proof (translation)
Unfold `colSpan`. Rewrite using `[Submodule.mem_span_range_iff_exists_fun]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Use `⟨y, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Simplify using `only [Finset.sum_apply, Matrix.mulVec, dotProduct, Algebra.smul_def]`. Conclude with `Finset.sum_congr rfl fun c _ => mul_comm _ _`. Introduce and unpack `⟨y, rfl⟩`. Use `⟨y, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Simplify using `only [Finset.sum_apply, Matrix.mulVec, dotProduct, Algebra.smul_def]`. Conclude with `Finset.sum_congr rfl fun c _ => mul_comm _ _`.
-/
theorem mem_colSpan (G : Matrix (Fin n) (Fin n) Qq) (x : Fin n → Qq) :
    x ∈ colSpan W G ↔ ∃ y : Fin n → W, x = G.mulVec (fun c => algebraMap W Qq (y c)) := by
  unfold colSpan
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    funext i
    simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, Algebra.smul_def]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    funext i
    simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, Algebra.smul_def]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[LinearMap.mem_range, mem_colSpan]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨y, rfl⟩`.

Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨y, rfl⟩`.
-/
theorem range_psi (g : Matrix (Fin n) (Fin n) Qq) : LinearMap.range (psi (W := W) g) = colSpan W g := by
  ext x
  rw [LinearMap.mem_range, mem_colSpan]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, rfl⟩

/- English proof (translation)
Use `congrArg (g⁻¹).mulVec h` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g hg]`.
-/
theorem mulVec_cancel (g : Matrix (Fin n) (Fin n) Qq) (hg : IsUnit g.det) {u v : Fin n → Qq}
    (h : g.mulVec u = g.mulVec v) : u = v := by
  have := congrArg (g⁻¹).mulVec h
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g hg] using this

/- English proof (translation)
Introduce `a b h`. Use `mulVec_cancel g hg h` as an intermediate fact. Use function extensionality and compare the values at `c`. Conclude with `hinj (congrFun this c)`.
-/
theorem psi_inj (hinj : Function.Injective (algebraMap W Qq)) (g : Matrix (Fin n) (Fin n) Qq) (hg : IsUnit g.det) :
    Function.Injective (psi (W := W) g) := by
  intro a b h
  have := mulVec_cancel g hg h
  funext c
  exact hinj (congrFun this c)

/- English proof (translation)
Rewrite using `[psi_apply, psi_apply, Matrix.smul_mulVec]`.
-/
theorem psi_smul_mat (c : Qq) (g : Matrix (Fin n) (Fin n) Qq) (w : Fin n → W) :
    psi (c • g) w = c • psi g w := by
  rw [psi_apply, psi_apply, Matrix.smul_mulVec]

/- English proof (translation)
Establish `hinj` using `psi_inj (IsFractionRing.injective W Qq) g hg`. Use `set Sb : Submodule W (Fin n → W) := S.comap (psi g) with hSb`. Take `⟨m, ⟨bS⟩⟩` from `Submodule.nonempty_basis_of_pid (Pi.basisFun W (Fin n)) Sb`. Establish `hfin : Module.Finite W Sb` using `Module.Finite.of_basis bS`. Establish `hfr : Module.finrank W Sb = m` using `by rw [Module.finrank_eq_card_basis bS, Fintype.card_fin]`.

Set `c : Fin m → (Fin n → Qq)` to `fun i => psi g (bS i : Fin n → W)`. Establish `hliW : LinearIndependent W c`. Use `bS.linearIndependent.map' ((psi g).comp Sb.subtype) (by rw [LinearMap.ker_comp, LinearMap.ker_eq_bot.2 hinj, Submodule.comap_bot, Submodule.ker_subtype])` as an intermediate fact. Conclude with `this`. Establish `hliQ : LinearIndependent Qq c` using `(LinearIndependent.iff_fractionRing W Qq).1 hliW`.

Establish `hmn : m ≤ n`. Use `hliQ.fintype_card_le_finrank` as an intermediate fact. Simplify using `using this`. Establish `hnm : n ≤ m`. Establish `hmem : ∀ i : Fin n, π • (Pi.basisFun W (Fin n) i) ∈ Sb`.

Introduce `i`. Use `show psi g (π • (Pi.basisFun W (Fin n) i)) ∈ S`. Rewrite using `[map_smul]`. Conclude with `h2 _ (by rw [← range_psi]; exact LinearMap.mem_range_self _ _)`. Establish `hli : LinearIndependent W (fun i : Fin n => (⟨π • (Pi.basisFun W (Fin n) i), hmem i⟩ : Sb))`.

Apply `LinearIndependent.of_comp Sb.subtype` to reduce the goal to its premises. Use `(Pi.basisFun W (Fin n)).linearIndependent.map' (π • (LinearMap.id : (Fin n → W) →ₗ[W] (Fin n → W))) (by` as an intermediate fact. Rewrite using `[LinearMap.ker_eq_bot]`. Introduce `a b hab`. Conclude with `smul_right_injective _ hπ hab)`.

Conclude with `this`. Use `hli.fintype_card_le_finrank` as an intermediate fact. Rewrite `this` using `[hfr]`. Simplify using `using this`. Take `rfl : m = n` from `le_antisymm hmn hnm`.

Use `⟨Matrix.of fun a b => c b a, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.isUnit_iff_isUnit_det]`. Rewrite using `[← Matrix.linearIndependent_cols_iff_isUnit]`. Conclude with `hliQ`. Unfold `colSpan`.

Establish `e1 : (Set.range fun b : Fin m => fun a => (Matrix.of fun a b => c b a) a b) = (psi g).comp Sb.subtype '' Set.range bS`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[e1, ← Submodule.map_span, bS.span_eq, Submodule.map_comp, Submodule.map_subtype_top, hSb, Submodule.map_comap_eq, range_psi, inf_eq_right.2 h1]`.
-/
theorem isLattice_between [IsDomain W] [IsPrincipalIdealRing W] [IsFractionRing W Qq] (π : W) (hπ : π ≠ 0)
    (g : Matrix (Fin n) (Fin n) Qq) (hg : IsUnit g.det) (S : Submodule W (Fin n → Qq))
    (h1 : S ≤ colSpan W g) (h2 : ∀ y ∈ colSpan W g, π • y ∈ S) : IsLattice W S := by
  classical
  have hinj := psi_inj (IsFractionRing.injective W Qq) g hg
  set Sb : Submodule W (Fin n → W) := S.comap (psi g) with hSb
  obtain ⟨m, ⟨bS⟩⟩ := Submodule.nonempty_basis_of_pid (Pi.basisFun W (Fin n)) Sb
  have hfin : Module.Finite W Sb := Module.Finite.of_basis bS
  have hfr : Module.finrank W Sb = m := by rw [Module.finrank_eq_card_basis bS, Fintype.card_fin]
  let c : Fin m → (Fin n → Qq) := fun i => psi g (bS i : Fin n → W)
  have hliW : LinearIndependent W c := by
    have := bS.linearIndependent.map' ((psi g).comp Sb.subtype)
      (by rw [LinearMap.ker_comp, LinearMap.ker_eq_bot.2 hinj, Submodule.comap_bot, Submodule.ker_subtype])
    exact this
  have hliQ : LinearIndependent Qq c := (LinearIndependent.iff_fractionRing W Qq).1 hliW
  have hmn : m ≤ n := by
    have := hliQ.fintype_card_le_finrank
    simpa using this
  have hnm : n ≤ m := by
    have hmem : ∀ i : Fin n, π • (Pi.basisFun W (Fin n) i) ∈ Sb := by
      intro i
      show psi g (π • (Pi.basisFun W (Fin n) i)) ∈ S
      rw [map_smul]
      exact h2 _ (by rw [← range_psi]; exact LinearMap.mem_range_self _ _)
    have hli : LinearIndependent W (fun i : Fin n => (⟨π • (Pi.basisFun W (Fin n) i), hmem i⟩ : Sb)) := by
      apply LinearIndependent.of_comp Sb.subtype
      have := (Pi.basisFun W (Fin n)).linearIndependent.map' (π • (LinearMap.id : (Fin n → W) →ₗ[W] (Fin n → W)))
        (by
          rw [LinearMap.ker_eq_bot]
          intro a b hab
          exact smul_right_injective _ hπ hab)
      exact this
    have := hli.fintype_card_le_finrank
    rw [hfr] at this
    simpa using this
  obtain rfl : m = n := le_antisymm hmn hnm
  refine ⟨Matrix.of fun a b => c b a, ?_, ?_⟩
  · rw [← Matrix.isUnit_iff_isUnit_det]
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hliQ
  · unfold colSpan
    have e1 : (Set.range fun b : Fin m => fun a => (Matrix.of fun a b => c b a) a b) =
        (psi g).comp Sb.subtype '' Set.range bS := by
      rw [← Set.range_comp]
      rfl
    rw [e1, ← Submodule.map_span, bS.span_eq, Submodule.map_comp, Submodule.map_subtype_top, hSb,
      Submodule.map_comap_eq, range_psi, inf_eq_right.2 h1]

end Formalism.MainNotions.FormalGroupSystem.Pf.Cnt

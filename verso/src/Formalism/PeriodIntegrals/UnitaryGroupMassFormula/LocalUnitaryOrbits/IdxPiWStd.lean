import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.PairHermSmulRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.LatBasOHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.MemUnifOIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CountUOfBas

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

/- English proof (translation)
Set `φ : (Fin (2 * n) → v.adicCompletionIntegers F) →+ latA v Λ` to `{ toFun := fun c => ⟨∑ i, (c i : Fv F v) • b i, (hmem _).2 ⟨c, rfl⟩⟩ map_zero' := by ext1; simp map_add' := fun c d => by ext1`. Simplify using `[add_smul, Finset.sum_add_distrib] }`. Establish `hφs : Function.Surjective φ`. Introduce and unpack `⟨x, hx⟩`. Take `⟨c, rfl⟩` from `(hmem x).1 hx`.

Conclude with `⟨c, rfl⟩`. Establish `key : ((lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)).comap φ = AddSubgroup.pi Set.univ (fun _ => unifO v ϖ)`. Use extensionality with `c`. Rewrite using `[AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨z, hz, hze⟩ i _`. Take `⟨d, rfl⟩` from `(hmem z).1 hz`. Use `⟨d i, ?_⟩` and prove the remaining obligations. Establish `e : ∑ i, (c i : Fv F v) • b i = ∑ i, (ϖ * d i) • b i`. Establish `: (DistribMulAction.toAddMonoidHom (Fin n → Fv F v ⊗[F] E) (sc (E` using `E) v ϖ)) (∑ i, (d i : Fv F v) • b i) = ∑ i, (ϖ * d i) • b i := by show sc (E := E) v ϖ • ∑ i, (d i : Fv F v) • b i = _`.

Rewrite using `[Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => sc_smul_smul v ϖ _ _`. Rewrite using `[← this, hze]`. Both sides reduce to the same expression. Establish `h0` using `Fintype.linearIndependent_iff.1 hb (fun i => (c i : Fv F v) - ϖ * d i) (by simp only [sub_smul, Finset.sum_sub_distrib, e, sub_self])`.

Conclude with `sub_eq_zero.1 (h0 i)`. Introduce `h choose d hd using fun i => h i (Set.mem_univ i)`. Use `⟨∑ i, (d i : Fv F v) • b i, (hmem _).2 ⟨d, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show sc (E := E) v ϖ • ∑ i, (d i : Fv F v) • b i = ∑ i, (c i : Fv F v) • b i`. Rewrite using `[Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[sc_smul_smul, hd i]`. Rewrite using `[AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hφs, key, AddSubgroup.index_pi]`. Simplify using `only [hR ϖ hϖ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.
-/
theorem latIdx (b : Fin (2 * n) → Fin n → Fv F v ⊗[F] E) (hb : LinearIndependent (Fv F v) b)
    (hmem : ∀ x, x ∈ latLoc (E := E) v Λ ↔
      ∃ c : Fin (2 * n) → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i)
    (hR : ResIdx v) (ϖ : Fv F v) (hϖ : IsUnif v ϖ) :
    (lattice₂ v Λ ϖ).relIndex (latA v Λ) = (Ideal.absNorm v.asIdeal) ^ (2 * n) := by
  let φ : (Fin (2 * n) → v.adicCompletionIntegers F) →+ latA v Λ :=
    { toFun := fun c => ⟨∑ i, (c i : Fv F v) • b i, (hmem _).2 ⟨c, rfl⟩⟩
      map_zero' := by ext1; simp
      map_add' := fun c d => by
        ext1
        simp [add_smul, Finset.sum_add_distrib] }
  have hφs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := (hmem x).1 hx
    exact ⟨c, rfl⟩
  have key : ((lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)).comap φ =
      AddSubgroup.pi Set.univ (fun _ => unifO v ϖ) := by
    ext c
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
    constructor
    · rintro ⟨z, hz, hze⟩ i _
      obtain ⟨d, rfl⟩ := (hmem z).1 hz
      refine ⟨d i, ?_⟩
      have e : ∑ i, (c i : Fv F v) • b i = ∑ i, (ϖ * d i) • b i := by
        have : (DistribMulAction.toAddMonoidHom (Fin n → Fv F v ⊗[F] E) (sc (E := E) v ϖ))
            (∑ i, (d i : Fv F v) • b i) = ∑ i, (ϖ * d i) • b i := by
          show sc (E := E) v ϖ • ∑ i, (d i : Fv F v) • b i = _
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => sc_smul_smul v ϖ _ _
        rw [← this, hze]
        rfl
      have h0 := Fintype.linearIndependent_iff.1 hb (fun i => (c i : Fv F v) - ϖ * d i)
        (by simp only [sub_smul, Finset.sum_sub_distrib, e, sub_self])
      exact sub_eq_zero.1 (h0 i)
    · intro h
      choose d hd using fun i => h i (Set.mem_univ i)
      refine ⟨∑ i, (d i : Fv F v) • b i, (hmem _).2 ⟨d, rfl⟩, ?_⟩
      show sc (E := E) v ϖ • ∑ i, (d i : Fv F v) • b i = ∑ i, (c i : Fv F v) • b i
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sc_smul_smul, hd i]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hφs, key, AddSubgroup.index_pi]
  simp only [hR ϖ hϖ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/- English proof (translation)
Establish `hV` using `latIdx v Λ b hb hmem hR ϖ hϖ`. Rewrite using `[AddSubgroup.relIndex, ← redT_ker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 (redT_surj v Λ a ϖ), AddSubgroup.card_top, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin a), Fintype.card_fin]`. Establish `hq : Nat.card (latA v Λ ⧸ (lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)) = (Ideal.absNorm v.asIdeal) ^ (2 * n)`. Rewrite using `[← hV, AddSubgroup.relIndex, AddSubgroup.index]`. Rewrite using `[hq, ← pow_mul]`.
-/
theorem lamIdx (a : ℕ) (b : Fin (2 * n) → Fin n → Fv F v ⊗[F] E) (hb : LinearIndependent (Fv F v) b)
    (hmem : ∀ x, x ∈ latLoc (E := E) v Λ ↔
      ∃ c : Fin (2 * n) → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i)
    (hR : ResIdx v) (ϖ : Fv F v) (hϖ : IsUnif v ϖ) :
    (lamP v Λ a ϖ).relIndex (lamA v Λ a) = (Ideal.absNorm v.asIdeal) ^ (2 * n * a) := by
  have hV := latIdx v Λ b hb hmem hR ϖ hϖ
  rw [AddSubgroup.relIndex, ← redT_ker, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.2 (redT_surj v Λ a ϖ), AddSubgroup.card_top, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin a),
    Fintype.card_fin]
  have hq : Nat.card (latA v Λ ⧸ (lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)) =
      (Ideal.absNorm v.asIdeal) ^ (2 * n) := by
    rw [← hV, AddSubgroup.relIndex, AddSubgroup.index]
  rw [hq, ← pow_mul]

/- English proof (translation)
Establish `: FiniteDimensional F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Establish `h2 : Module.finrank F E = 2` using `hCM.2.2.1`. Take `⟨m, b, hli, hmem, hsp⟩` from `exists_basO v L hLat`. Establish `hm : m = 2 * n`. Establish `h1` using `Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)`.

Rewrite `h1` using `[Fintype.card_fin]`. Rewrite using `[← h1, Module.finrank_pi_fintype]`. Simplify using `only [Module.finrank_baseChange, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Substitute `hm` using the available equality.

Conclude with `⟨b, hli, hmem⟩`.
-/
theorem basis_of (hCM : IsCMExt F E σ) (L : Submodule (𝓞 E) (Fin n → E)) (hLat : Submodule.IsLattice E L) :
    ∃ b : Fin (2 * n) → (Fin n → Fv F v ⊗[F] E), LinearIndependent (Fv F v) b ∧
      ∀ x, x ∈ latLoc (E := E) v (L : Set (Fin n → E)) ↔
        ∃ c : Fin (2 * n) → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i := by
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  obtain ⟨m, b, hli, hmem, hsp⟩ := exists_basO v L hLat
  have hm : m = 2 * n := by
    have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
    rw [Fintype.card_fin] at h1
    rw [← h1, Module.finrank_pi_fintype]
    simp only [Module.finrank_baseChange, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  subst hm
  exact ⟨b, hli, hmem⟩

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[Algebra.smul_def]`. Both sides reduce to the same expression.
-/
theorem smul_tup {a : ℕ} (ϖ : Fv F v) (p : TupV (E := E) v n a) : ϖ • p = sc (E := E) v ϖ • p := by
  funext i j
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Algebra.smul_def]
  rfl

/- English proof (translation)
Introduce and unpack `⟨L, hLat, rfl⟩ _ ϖ hϖ`. Take `⟨b, hb, hmem⟩` from `basis_of σ v hS.1 L hLat`. Establish `e : smulSub ϖ (LW v (L : Set (Fin n → E)) a) = lamP v (L : Set (Fin n → E)) a ϖ`. Use extensionality with `X`. Rewrite using `[mem_smulSub, lamP, AddSubgroup.mem_map]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, hp, rfl⟩`. Conclude with `⟨p, hp, by rw [DistribMulAction.toAddMonoidHom_apply, smul_tup]⟩`. Introduce and unpack `⟨p, hp, rfl⟩`. Conclude with `⟨p, hp, by rw [DistribMulAction.toAddMonoidHom_apply, smul_tup]⟩`.

Establish `e2 : LW v (L : Set (Fin n → E)) a = lamA v (L : Set (Fin n → E)) a` using `AddSubgroup.ext fun _ => Iff.rfl`. Rewrite using `[e, e2, lamIdx v _ a b hb hmem (resIdx_holds v) ϖ hϖ, qv]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem idxPiW_std (a : ℕ) (hS : StdHyp σ J ψ) : IdxPiW v Λ a := by
  rintro ⟨L, hLat, rfl⟩ _ ϖ hϖ
  obtain ⟨b, hb, hmem⟩ := basis_of σ v hS.1 L hLat
  have e : smulSub ϖ (LW v (L : Set (Fin n → E)) a) = lamP v (L : Set (Fin n → E)) a ϖ := by
    ext X
    rw [mem_smulSub, lamP, AddSubgroup.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, by rw [DistribMulAction.toAddMonoidHom_apply, smul_tup]⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, by rw [DistribMulAction.toAddMonoidHom_apply, smul_tup]⟩
  have e2 : LW v (L : Set (Fin n → E)) a = lamA v (L : Set (Fin n → E)) a := AddSubgroup.ext fun _ => Iff.rfl
  rw [e, e2, lamIdx v _ a b hb hmem (resIdx_holds v) ϖ hϖ, qv]
  push_cast
  ring

end PI.OmLocU.SdB

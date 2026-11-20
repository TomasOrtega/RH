import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOfStepsX

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def LatBasOP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∃ b : Fin (2 * n) → (Fin n → Fv F v ⊗[F] E), LinearIndependent (Fv F v) b ∧
    ∀ x, x ∈ latLoc (E := E) v Λ ↔ ∃ c : Fin (2 * n) → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i

def IdxVP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    (lattice₂ v Λ ϖ).relIndex (latA v Λ) = (Ideal.absNorm v.asIdeal) ^ (2 * n)

/- English proof (translation)
Introduce and unpack `⟨⟨hCM, -⟩, ⟨L, hLat, rfl⟩, -⟩`. Establish `: FiniteDimensional F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Establish `h2 : Module.finrank F E = 2` using `hCM.2.2.1`. Take `⟨m, b, hli, hmem, hsp⟩` from `exists_basO v L hLat`. Establish `hm : m = 2 * n`.

Establish `h1` using `Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)`. Rewrite `h1` using `[Fintype.card_fin]`. Rewrite using `[← h1, Module.finrank_pi_fintype]`. Simplify using `only [Module.finrank_baseChange, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Substitute `hm` using the available equality. Conclude with `⟨b, hli, hmem⟩`.
-/
theorem localLattice_hasBasis (a : ℕ) (Y : TupV (E := E) v n a) : LatBasOP σ J ψ v Λ a Y := by
  classical
  rintro ⟨⟨hCM, -⟩, ⟨L, hLat, rfl⟩, -⟩
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
Introduce `hG ϖ hϖ`. Take `⟨b, hb, hmem⟩` from `hB hG`. Set `φ : (Fin (2 * n) → v.adicCompletionIntegers F) →+ latA v Λ` to `{ toFun := fun c => ⟨∑ i, (c i : Fv F v) • b i, (hmem _).2 ⟨c, rfl⟩⟩ map_zero' := by ext1; simp map_add' := fun c d => by ext1`. Simplify using `[add_smul, Finset.sum_add_distrib] }`. Establish `hφs : Function.Surjective φ`.

Introduce and unpack `⟨x, hx⟩`. Take `⟨c, rfl⟩` from `(hmem x).1 hx`. Conclude with `⟨c, rfl⟩`. Establish `key : ((lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)).comap φ = AddSubgroup.pi Set.univ (fun _ => unifO v ϖ)`. Use extensionality with `c`.

Rewrite using `[AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, hze⟩ i _`. Take `⟨d, rfl⟩` from `(hmem z).1 hz`. Use `⟨d i, ?_⟩` and prove the remaining obligations.

Establish `e : ∑ i, (c i : Fv F v) • b i = ∑ i, (ϖ * d i) • b i`. Establish `: (DistribMulAction.toAddMonoidHom (Fin n → Fv F v ⊗[F] E) (sc (E` using `E) v ϖ)) (∑ i, (d i : Fv F v) • b i) = ∑ i, (ϖ * d i) • b i := by show sc (E := E) v ϖ • ∑ i, (d i : Fv F v) • b i = _`. Rewrite using `[Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => sc_smul_smul v ϖ _ _`. Rewrite using `[← this, hze]`.

Both sides reduce to the same expression. Establish `h0` using `Fintype.linearIndependent_iff.1 hb (fun i => (c i : Fv F v) - ϖ * d i) (by simp only [sub_smul, Finset.sum_sub_distrib, e, sub_self])`. Conclude with `sub_eq_zero.1 (h0 i)`. Introduce `h choose d hd using fun i => h i (Set.mem_univ i)`. Use `⟨∑ i, (d i : Fv F v) • b i, (hmem _).2 ⟨d, rfl⟩, ?_⟩` and prove the remaining obligations.

Use `show sc (E := E) v ϖ • ∑ i, (d i : Fv F v) • b i = ∑ i, (c i : Fv F v) • b i`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[sc_smul_smul, hd i]`. Rewrite using `[AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hφs, key, AddSubgroup.index_pi]`.

Simplify using `only [hR ϖ hϖ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.
-/
theorem idxVP_of (a : ℕ) (Y : TupV (E := E) v n a) (hB : LatBasOP σ J ψ v Λ a Y) (hR : ResIdx v) :
    IdxVP σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  obtain ⟨b, hb, hmem⟩ := hB hG
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
Introduce `hG ϖ hϖ`. Establish `hV` using `h hG ϖ hϖ`. Rewrite using `[AddSubgroup.relIndex, ← redT_ker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 (redT_surj v Λ a ϖ), AddSubgroup.card_top, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin a), Fintype.card_fin]`. Establish `hq : Nat.card (latA v Λ ⧸ (lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)) = (Ideal.absNorm v.asIdeal) ^ (2 * n)`. Rewrite using `[← hV, AddSubgroup.relIndex, AddSubgroup.index]`.

Rewrite using `[hq, ← pow_mul]`.
-/
theorem idxP_of (a : ℕ) (Y : TupV (E := E) v n a) (h : IdxVP σ J ψ v Λ a Y) : IdxP σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have hV := h hG ϖ hϖ
  rw [AddSubgroup.relIndex, ← redT_ker, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.2 (redT_surj v Λ a ϖ), AddSubgroup.card_top, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin a),
    Fintype.card_fin]
  have hq : Nat.card (latA v Λ ⧸ (lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)) =
      (Ideal.absNorm v.asIdeal) ^ (2 * n) := by
    rw [← hV, AddSubgroup.relIndex, AddSubgroup.index]
  rw [hq, ← pow_mul]

/- English proof (translation)
Introduce `hG ϖ hϖ`. Use `PI.VolStabSW.secondCountable_Fv F v` as an intermediate fact. Establish `: IsModuleTopology (Fv F v) (Fv F v ⊗[F] E)` using `⟨rfl⟩`. Establish `: IsTopologicalAddGroup (Fv F v ⊗[F] E)` using `IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)`. Establish `: BorelSpace (Fv F v ⊗[F] E)` using `⟨rfl⟩`.

Establish `hOpen` using `(lamOC_holds v Λ a hG.2.1).1`. Use `⟨inferInstance, hOpen.measurableSet, ?_⟩` and prove the remaining obligations. Establish `e : (lamP v Λ a ϖ : Set (TupV (E` using `E) v n a)) = (fun X => ϖ • X) '' LamT v Λ a := by`. Unfold `lamP`. Rewrite using `[AddSubgroup.coe_map]`.

Use `congr 1`. Use function extensionality and compare the values at `X`. Use function extensionality and compare the values at `i p`. Use `show sc (E := E) v ϖ * X i p = ϖ • X i p`. Rewrite using `[Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `(isOpenMap_smul₀ (unif_ne_zero v hϖ) _ hOpen).measurableSet`.
-/
theorem MeasP₂ (a : ℕ) (Y : TupV (E := E) v n a) : MeasP σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have := PI.VolStabSW.secondCountable_Fv F v
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hOpen := (lamOC_holds v Λ a hG.2.1).1
  refine ⟨inferInstance, hOpen.measurableSet, ?_⟩
  have e : (lamP v Λ a ϖ : Set (TupV (E := E) v n a)) = (fun X => ϖ • X) '' LamT v Λ a := by
    unfold lamP
    rw [AddSubgroup.coe_map]
    congr 1
    funext X
    funext i p
    show sc (E := E) v ϖ * X i p = ϖ • X i p
    rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
    rfl
  rw [e]
  exact (isOpenMap_smul₀ (unif_ne_zero v hϖ) _ hOpen).measurableSet

/- English proof (translation)
The claim follows from `idxP_of σ J ψ v Λ a Y (idxVP_of σ J ψ v Λ a Y (localLattice_hasBasis σ J ψ v Λ a Y) (resIdx_holds v))`.
-/
theorem idxP_holds (a : ℕ) (Y : TupV (E := E) v n a) : IdxP σ J ψ v Λ a Y :=
  idxP_of σ J ψ v Λ a Y (idxVP_of σ J ψ v Λ a Y (localLattice_hasBasis σ J ψ v Λ a Y) (resIdx_holds v))

end Gen

section Loc

open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

/- English proof (translation)
The claim follows from `omVBadT_of_steps X u' ψ hStd hLat hGram hExt hPC hPD (fun v => MeasP₂ _ _ _ _ _ _ _) (fun v => idxP_holds _ _ _ _ _ _ _) hCl`.
-/
theorem omVBadT_of_primDual_cls (hStd : OmVStd X ψ) (hLat : OmVLat X) (hGram : OmVGram X u')
    (hExt : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ExtP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hPC : ∀ v : PlX X, PrimCos X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS))
    (hPD : ∀ v : PlX X, PrimDual X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS))
    (hCl : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ClsP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v)) :
    OmVBadT X u' ψ :=
  omVBadT_of_steps X u' ψ hStd hLat hGram hExt hPC hPD (fun v => MeasP₂ _ _ _ _ _ _ _)
    (fun v => idxP_holds _ _ _ _ _ _ _) hCl

/- English proof (translation)
The claim follows from `omVBadT_of_primDual_cls X u' ψ hStd hLat hGram hExt hPC hPD hCl`.
-/
theorem omVBadT_of_fourX (hStd : Formalism.L2.SG.Pf.NcX.OmVSt.OmVStd X ψ) (hLat : Formalism.L2.SG.Pf.NcX.OmVSt.OmVLat X)
    (hGram : Formalism.L2.SG.Pf.NcX.OmVSt.OmVGram X u')
    (hExt : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ExtP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hPC : ∀ v : PlX X, PrimCos X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS))
    (hPD : ∀ v : PlX X, PrimDual X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS))
    (hCl : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ClsP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v)) :
    Formalism.L2.SG.Pf.NcX.OmVSt.OmVBadT X u' ψ :=
  omVBadT_of_primDual_cls X u' ψ hStd hLat hGram hExt hPC hPD hCl

end Loc

end PI.OmVd

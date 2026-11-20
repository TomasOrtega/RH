import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.PrimIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FFInertB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.UnitaryOrbitCounting
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.UnitNormOfRes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.EtaSpHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ResAlgOfSp

noncomputable section

namespace PI.OmVg

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmLocU.Red
  PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

/- English proof (translation)
Use `set Φ := phi σ J v Λ hSD he π a with hΦ`. Set `eq : (lamA v Λ a ⧸ (lamP v Λ a ϖ).addSubgroupOf (lamA v Λ a)) ≃+ (Fin a → Fin n → K)` to `(QuotientAddGroup.quotientAddEquivOfEq (phi_ker σ J v Λ hSD he he1 hπ a)).trans (QuotientAddGroup.quotientKerEquivOfSurjective Φ (phi_surj σ J v Λ hSD he he1 hπ a))`. Establish `heq : ∀ x : lamA v Λ a, eq (QuotientAddGroup.mk x) = Φ x` using `fun x => rfl`. Use `set P : (Fin a → Fin n → K) → Prop := fun M => ffGram τ 1 M = (fun i j => π ⟨T i j, hT i j⟩) ∧ LinearIndependent K M with hP`. Establish `hset : PI.OmVd.clsP σ J v Λ a ϖ T = {q | P (eq q)}`.

Use extensionality with `q`. Proceed by induction on `q using QuotientAddGroup.induction_on with`. Consider the case `H x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, ⟨hyP, hyN⟩, hyx⟩ show P (eq (QuotientAddGroup.mk x))`.

Rewrite using `[← hyx, heq]`. Conclude with `⟨(nearT_iff σ J v Λ hcm hJ hSD he he1 hπ T hT y).1 hyN, (prim_iff σ J v Λ hSD he he1 hL hϖ hπ y).1 hyP⟩`. Introduce `hx`. Establish `h2 : P (eq (QuotientAddGroup.mk x))` using `hx`. Rewrite `h2` using `[heq]`.

Conclude with `⟨x, ⟨(prim_iff σ J v Λ hSD he he1 hL hϖ hπ x).2 h2.2, (nearT_iff σ J v Λ hcm hJ hSD he he1 hπ T hT x).2 h2.1⟩, rfl⟩`. Rewrite using `[hset]`. Conclude with `Nat.card_congr (Equiv.subtypeEquiv (p := fun q => q ∈ {q | P (eq q)}) eq.toEquiv (fun q => Iff.rfl))`.
-/
theorem card_clsP (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (hcm : IsCMExt F E σ) (hJ : ∀ i j, σ (J j i) = J i j) (hSD : IsSDLoc σ J v Λ)
    {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) (he1 : gramR (Fv F v) σ J e = 1)
    {ϖ : Fv F v} (hϖ : IsUnif v ϖ) {K : Type} [CommRing K] (τ : K →+* K) (π : OR (E := E) v →+* K)
    (hπ : IsRes σ v ϖ τ π) {a : ℕ} (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))
    (hT : ∀ i j, T i j ∈ OR (E := E) v) :
    Nat.card (PI.OmVd.clsP σ J v Λ a ϖ T) =
      Nat.card {X : Fin a → Fin n → K //
        ffGram τ 1 X = (fun i j => π ⟨T i j, hT i j⟩) ∧ LinearIndependent K X} := by
  set Φ := phi σ J v Λ hSD he π a with hΦ
  let eq : (lamA v Λ a ⧸ (lamP v Λ a ϖ).addSubgroupOf (lamA v Λ a)) ≃+ (Fin a → Fin n → K) :=
    (QuotientAddGroup.quotientAddEquivOfEq (phi_ker σ J v Λ hSD he he1 hπ a)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective Φ (phi_surj σ J v Λ hSD he he1 hπ a))
  have heq : ∀ x : lamA v Λ a, eq (QuotientAddGroup.mk x) = Φ x := fun x => rfl
  set P : (Fin a → Fin n → K) → Prop := fun M =>
    ffGram τ 1 M = (fun i j => π ⟨T i j, hT i j⟩) ∧ LinearIndependent K M with hP
  have hset : PI.OmVd.clsP σ J v Λ a ϖ T = {q | P (eq q)} := by
    ext q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      constructor
      · rintro ⟨y, ⟨hyP, hyN⟩, hyx⟩
        show P (eq (QuotientAddGroup.mk x))
        rw [← hyx, heq]
        exact ⟨(nearT_iff σ J v Λ hcm hJ hSD he he1 hπ T hT y).1 hyN,
          (prim_iff σ J v Λ hSD he he1 hL hϖ hπ y).1 hyP⟩
      · intro hx
        have h2 : P (eq (QuotientAddGroup.mk x)) := hx
        rw [heq] at h2
        exact ⟨x, ⟨(prim_iff σ J v Λ hSD he he1 hL hϖ hπ x).2 h2.2,
          (nearT_iff σ J v Λ hcm hJ hSD he he1 hπ T hT x).2 h2.1⟩, rfl⟩
  rw [hset]
  exact Nat.card_congr (Equiv.subtypeEquiv (p := fun q => q ∈ {q | P (eq q)}) eq.toEquiv (fun q => Iff.rfl))

def GramCor (ϖ : Fv F v) {a : ℕ} (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) : Prop :=
  ∃ i₀ : Fin a, (∀ j, T i₀ j ∈ PO (E := E) v ϖ) ∧ (∀ j, T j i₀ ∈ PO (E := E) v ϖ) ∧
    ∃ w ∈ OEv (E := E) v, (T + Matrix.single i₀ i₀ 1).det * w = 1

/- English proof (translation)
Take `⟨i₀, hr, hc, w, hw, hd⟩` from `hC`. Use `⟨i₀, fun j => (hπ.2.1 _).2 (hr j), fun j => (hπ.2.1 _).2 (hc j), ?_⟩` and prove the remaining obligations. Establish `hT' : ∀ i j, (T + Matrix.single i₀ i₀ 1 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ OR (E` using `E) v := by`. Introduce `i j`. Rewrite using `[Matrix.add_apply, Matrix.single_apply]`.

Use `split_ifs`. Conclude with `(OR (E := E) v).add_mem (hT i j) (OR (E := E) v).one_mem`. Simplify using `using hT i j`. Use `det_red v π _ hT' hw hd using 2` and compare the differences between its conclusion and the goal. Use `congr 1`.

Use extensionality with `i j`. Distinguish the cases in `h : i₀ = i ∧ i₀ = j`. Take `⟨h1', h2'⟩` from `h`. Substitute `h1'` using the available equality. Substitute `h2'` using the available equality.

Establish `h1 : (⟨(T + Matrix.single i₀ i₀ 1 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i₀ i₀, hT' i₀ i₀⟩ : OR (E` using `E) v) = ⟨T i₀ i₀, hT i₀ i₀⟩ + 1 := by`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[Matrix.add_apply]`. Rewrite using `[h1, map_add, map_one]`. Use `show π ⟨T i₀ i₀, hT i₀ i₀⟩ + (Matrix.single i₀ i₀ 1 : Matrix (Fin a) (Fin a) K) i₀ i₀ = _`.

Simplify using the standard rewrite rules. Establish `h1 : (⟨(T + Matrix.single i₀ i₀ 1 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j, hT' i j⟩ : OR (E` using `E) v) = ⟨T i j, hT i j⟩ := by`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[Matrix.add_apply, Matrix.single_apply, h]`. Rewrite using `[h1]`.

Use `show π ⟨T i j, hT i j⟩ + (Matrix.single i₀ i₀ 1 : Matrix (Fin a) (Fin a) K) i j = _`. Simplify using `[Matrix.single_apply, h]`.
-/
theorem corOne_red {ϖ : Fv F v} {K : Type} [CommRing K] {τ : K →+* K} {π : OR (E := E) v →+* K}
    (hπ : IsRes σ v ϖ τ π) {a : ℕ} (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))
    (hT : ∀ i j, T i j ∈ OR (E := E) v) (hC : GramCor v ϖ T) :
    PI.OmVd.CorOne (fun i j => π ⟨T i j, hT i j⟩ : Matrix (Fin a) (Fin a) K) := by
  obtain ⟨i₀, hr, hc, w, hw, hd⟩ := hC
  refine ⟨i₀, fun j => (hπ.2.1 _).2 (hr j), fun j => (hπ.2.1 _).2 (hc j), ?_⟩
  have hT' : ∀ i j, (T + Matrix.single i₀ i₀ 1 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ OR (E := E) v := by
    intro i j
    rw [Matrix.add_apply, Matrix.single_apply]
    split_ifs
    · exact (OR (E := E) v).add_mem (hT i j) (OR (E := E) v).one_mem
    · simpa using hT i j
  convert det_red v π _ hT' hw hd using 2
  congr 1
  ext i j
  by_cases h : i₀ = i ∧ i₀ = j
  · obtain ⟨h1', h2'⟩ := h
    subst h1'
    subst h2'
    have h1 : (⟨(T + Matrix.single i₀ i₀ 1 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i₀ i₀, hT' i₀ i₀⟩ :
        OR (E := E) v) = ⟨T i₀ i₀, hT i₀ i₀⟩ + 1 := by
      apply Subtype.ext
      simp [Matrix.add_apply]
    rw [h1, map_add, map_one]
    show π ⟨T i₀ i₀, hT i₀ i₀⟩ + (Matrix.single i₀ i₀ 1 : Matrix (Fin a) (Fin a) K) i₀ i₀ = _
    simp
  · have h1 : (⟨(T + Matrix.single i₀ i₀ 1 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j, hT' i j⟩ :
        OR (E := E) v) = ⟨T i j, hT i j⟩ := by
      apply Subtype.ext
      simp [Matrix.add_apply, Matrix.single_apply, h]
    rw [h1]
    show π ⟨T i j, hT i j⟩ + (Matrix.single i₀ i₀ 1 : Matrix (Fin a) (Fin a) K) i j = _
    simp [Matrix.single_apply, h]

/- English proof (translation)
Introduce `hG ϖ hϖ`. Establish `hR : ResAlg σ J ψ v` using `resAlg_of_sp σ J ψ v (etaSp_holds σ J ψ v)`. Establish `hU : Orb.UnitV σ J ψ v Λ` using `Orb.unitV_of σ J ψ v Λ (NormOneUnitFixedPoints.normOne_of σ J ψ v hR) (UnN.unitNorm_of_res σ J ψ v Λ hR)`. Establish `hstd` using `hG.1`. Establish `hcm` using `hstd.1`.

Establish `hJ : ∀ i j, σ (J j i) = J i j` using `hstd.2.1.1`. Establish `hL` using `hG.2.1`. Establish `hSD : IsSDLoc σ J v Λ` using `hG.2.2.1`. Take `⟨e, he, he1⟩` from `oBas1_of_unitV σ J ψ v Λ hU hstd hL hSD hG.2.2.2.1`. Establish `hY` using `hG.2.2.2.2.2.1`.

Establish `hT : ∀ i j, gramR (Fv F v) σ J Y i j ∈ OR (E` using `E) v := fun i j => (hSD (Y j)).1 (hY j) (Y i) (hY i)`. Establish `hconj : ∀ i j, gramR (Fv F v) σ J Y i j = sigR (Fv F v) σ (gramR (Fv F v) σ J Y j i)` using `fun i j => (Orb.hR_conj σ J v hcm hJ (Y j) (Y i)).symm`. Take `⟨k, _, _, hk, h⟩` from `hR hstd hG.2.2.2.1 ϖ hϖ`. Use `⟨k, inferInstance, inferInstance, hk, ?_⟩` and prove the remaining obligations. Break down `h with ⟨hη, K, _, _, σ', π, hσ, h2, hne, hπ⟩ | ⟨hη, π, hπ⟩` into its components or cases.

Use `Or.inl ⟨hη, K, inferInstance, inferInstance, σ', 1, fun i j => π ⟨_, hT i j⟩, hσ, h2, hne, ?_, by simp, ?_, corOne_red σ v hπ _ hT (hC ϖ hϖ), card_clsP σ J v Λ hL hcm hJ hSD he he1 hϖ (σ' : K →+* K) π hπ _ hT⟩` and prove the remaining obligations. Introduce `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h, Ne.symm h]`. Introduce `i j`. Conclude with `(hπ.2.2 _ _ (hconj i j)).symm`. Use `Or.inr ⟨hη, 1, fun i j => π ⟨_, hT i j⟩, ?_, by simp, ?_, corOne_red σ v hπ _ hT (hC ϖ hϖ), card_clsP σ J v Λ hL hcm hJ hSD he he1 hϖ (RingEquiv.prodComm (R := k) (S := k)).toRingHom π hπ _ hT⟩` and prove the remaining obligations. Introduce `i j`.

Distinguish the cases in `h : i = j`. Apply the tactic sequence `subst h; ext <;> simp`. Apply the tactic sequence `ext <;> simp [h, Ne.symm h]`. Introduce `i j`. Conclude with `(hπ.2.2 _ _ (hconj i j)).symm`.
-/
theorem redP_of_gramCor (a : ℕ) (Y : TupV (E := E) v n a)
    (hC : ∀ ϖ : Fv F v, IsUnif v ϖ → GramCor v ϖ (gramR (Fv F v) σ J Y)) :
    PI.OmVd.RedP σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have hR : ResAlg σ J ψ v := resAlg_of_sp σ J ψ v (etaSp_holds σ J ψ v)
  have hU : Orb.UnitV σ J ψ v Λ :=
    Orb.unitV_of σ J ψ v Λ (NormOneUnitFixedPoints.normOne_of σ J ψ v hR) (UnN.unitNorm_of_res σ J ψ v Λ hR)
  have hstd := hG.1
  have hcm := hstd.1
  have hJ : ∀ i j, σ (J j i) = J i j := hstd.2.1.1
  have hL := hG.2.1
  have hSD : IsSDLoc σ J v Λ := hG.2.2.1
  obtain ⟨e, he, he1⟩ := oBas1_of_unitV σ J ψ v Λ hU hstd hL hSD hG.2.2.2.1
  have hY := hG.2.2.2.2.2.1
  have hT : ∀ i j, gramR (Fv F v) σ J Y i j ∈ OR (E := E) v := fun i j =>
    (hSD (Y j)).1 (hY j) (Y i) (hY i)
  have hconj : ∀ i j, gramR (Fv F v) σ J Y i j = sigR (Fv F v) σ (gramR (Fv F v) σ J Y j i) := fun i j =>
    (Orb.hR_conj σ J v hcm hJ (Y j) (Y i)).symm
  obtain ⟨k, _, _, hk, h⟩ := hR hstd hG.2.2.2.1 ϖ hϖ
  refine ⟨k, inferInstance, inferInstance, hk, ?_⟩
  rcases h with ⟨hη, K, _, _, σ', π, hσ, h2, hne, hπ⟩ | ⟨hη, π, hπ⟩
  · refine Or.inl ⟨hη, K, inferInstance, inferInstance, σ', 1, fun i j => π ⟨_, hT i j⟩, hσ, h2, hne, ?_,
      by simp, ?_, corOne_red σ v hπ _ hT (hC ϖ hϖ),
      card_clsP σ J v Λ hL hcm hJ hSD he he1 hϖ (σ' : K →+* K) π hπ _ hT⟩
    · intro i j
      by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]
    · intro i j
      exact (hπ.2.2 _ _ (hconj i j)).symm
  · refine Or.inr ⟨hη, 1, fun i j => π ⟨_, hT i j⟩, ?_, by simp, ?_, corOne_red σ v hπ _ hT (hC ϖ hϖ),
      card_clsP σ J v Λ hL hcm hJ hSD he he1 hϖ (RingEquiv.prodComm (R := k) (S := k)).toRingHom π hπ _ hT⟩
    · intro i j
      by_cases h : i = j
      · subst h; ext <;> simp
      · ext <;> simp [h, Ne.symm h]
    · intro i j
      exact (hπ.2.2 _ _ (hconj i j)).symm

end PI.OmVg

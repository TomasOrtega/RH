import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalProductMultiplicity
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockEmbeddingFactors
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockProductIsomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrrParIffCuspidalProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelTransportEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviTensorBlockExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviPiTensorRepresentationIsIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalPiTensorNoBlockUnipotentFixedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCuspidalFactorAtBlockLeviPiTensorStatement

noncomputable section
namespace GlobalTheory.HcIrr
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV Polynomial CategoryTheory

/- English proof (translation)
Take `⟨hn, hW⟩` from `hirr`. Use `⟨Ψ.toEquiv.nontrivial, fun W hinv => ?_⟩` and prove the remaining obligations. Establish `hinv' : ∀ g, ∀ v ∈ W.map (Ψ : V →ₗ[ℂ] V'), ρ' g v ∈ W.map (Ψ : V →ₗ[ℂ] V')`. Introduce and unpack `g _ ⟨w, hw, rfl⟩`. Conclude with `⟨ρ (A g) w, hinv _ _ hw, h g w⟩`.

Break down `hW _ hinv' with h0 | h1` into its components or cases. Use `left`. Use `eq_bot_iff.2 fun v hv => ?_` and prove the remaining obligations. Establish `hv' : Ψ v ∈ W.map (Ψ : V →ₗ[ℂ] V')` using `⟨v, hv, rfl⟩`. Rewrite `hv'` using `[h0, Submodule.mem_bot]`.

Simplify using `using hv'`. Use `right`. Use `eq_top_iff.2 fun v _ => ?_` and prove the remaining obligations. Establish `: Ψ v ∈ W.map (Ψ : V →ₗ[ℂ] V')` using `h1 ▸ Submodule.mem_top`. Take `⟨w, hw, hwv⟩` from `this`.

Rewrite using `[← Ψ.injective hwv]` and apply the resulting hypothesis.
-/
theorem isIrrRep_of_equiv {G V V' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (A : G → G) (hA : Function.Surjective A)
    (Ψ : V ≃ₗ[ℂ] V') (h : ∀ g v, Ψ (ρ (A g) v) = ρ' g (Ψ v)) (hirr : IsIrrRep ρ') : IsIrrRep ρ := by
  obtain ⟨hn, hW⟩ := hirr
  refine ⟨Ψ.toEquiv.nontrivial, fun W hinv => ?_⟩
  have hinv' : ∀ g, ∀ v ∈ W.map (Ψ : V →ₗ[ℂ] V'), ρ' g v ∈ W.map (Ψ : V →ₗ[ℂ] V') := by
    rintro g _ ⟨w, hw, rfl⟩
    exact ⟨ρ (A g) w, hinv _ _ hw, h g w⟩
  rcases hW _ hinv' with h0 | h1
  · left
    refine eq_bot_iff.2 fun v hv => ?_
    have hv' : Ψ v ∈ W.map (Ψ : V →ₗ[ℂ] V') := ⟨v, hv, rfl⟩
    rw [h0, Submodule.mem_bot] at hv'
    simpa using hv'
  · right
    refine eq_top_iff.2 fun v _ => ?_
    have : Ψ v ∈ W.map (Ψ : V →ₗ[ℂ] V') := h1 ▸ Submodule.mem_top
    obtain ⟨w, hw, hwv⟩ := this
    rwa [← Ψ.injective hwv]

/- English proof (translation)
Use `haveI := h`. Use `⟨?_, fun W hW => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`. Establish `: (⊥ : Subrepresentation ρ) = ⊤` using `Subrepresentation.ext (Subsingleton.elim (α := Submodule ℂ V) _ _)`.

Conclude with `bot_ne_top this`. Break down `eq_bot_or_eq_top (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation ρ) with h0 | h1` into its components or cases. Conclude with `Or.inl (congrArg Subrepresentation.toSubmodule h0)`. Conclude with `Or.inr (congrArg Subrepresentation.toSubmodule h1)`.
-/
theorem isIrrRep_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : IsIrrRep ρ := by
  haveI := h
  refine ⟨?_, fun W hW => ?_⟩
  · by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have : (⊥ : Subrepresentation ρ) = ⊤ := Subrepresentation.ext (Subsingleton.elim (α := Submodule ℂ V) _ _)
    exact bot_ne_top this
  · rcases eq_bot_or_eq_top (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation ρ) with h0 | h1
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h0)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

/- English proof (translation)
Set `L : hcSpace K b lam ≃ₗ[ℂ] Representation.coindV (blockTri (κ` to `K) (natBlocks b)).subtype (leviTensor b lam) := { toFun := fun f => ⟨f.1, fun p x => f.2 (Subgroup.inclusion (blockTri_le_parab b) p) x⟩ invFun := fun f => ⟨f.1, fun p x => f.2 (Subgroup.inclusion (parab_le_blockTri b) p) x⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl …`. Conclude with `isIrrRep_of_equiv (hcRep K b lam) _ id Function.surjective_id L (fun _ _ => rfl) (isIrrRep_of_isIrreducible _ h)`.
-/
theorem isIrrRep_hcRep_of_parInd (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    (h : (GlobalTheory.FinGL.parInd (natBlocks b) (leviTensor b lam)).IsIrreducible) : IsIrrRep (hcRep K b lam) := by
  let L : hcSpace K b lam ≃ₗ[ℂ] Representation.coindV (blockTri (κ := K) (natBlocks b)).subtype (leviTensor b lam) :=
    { toFun := fun f => ⟨f.1, fun p x => f.2 (Subgroup.inclusion (blockTri_le_parab b) p) x⟩
      invFun := fun f => ⟨f.1, fun p x => f.2 (Subgroup.inclusion (parab_le_blockTri b) p) x⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact isIrrRep_of_equiv (hcRep K b lam) _ id Function.surjective_id L (fun _ _ => rfl)
    (isIrrRep_of_isIrreducible _ h)

/- English proof (translation)
Set `e : Fin r ≃ Fin r` to `(Tuple.sort b).symm`. Set `b' : Fin r → Fin s` to `b ∘ e.symm`. Set `ec : ∀ c, {i // b i = c} ≃ {k // b' k = c}` to `fun c => e.subtypeEquiv (fun i => by simp [b'])`. Set `lam' : ∀ c : Fin s, FDRep ℂ (GL {k // b' k = c} K)` to `fun c => transp (ec c) (lam c)`. Set `A : GL (Fin r) K ≃* GL (Fin r) K` to `(glEquiv K e).symm`.

Establish `hpar : ∀ p : parab K b', A p.1 ∈ parab K b`. Introduce `p`. Take `⟨h1, h2⟩` from `p.2`. Use `⟨fun i j hij => ?_, fun i j hij => ?_⟩` and prove the remaining obligations. Use `show Matrix.reindex e.symm e.symm (p.1 : Matrix (Fin r) (Fin r) K) i j = 0`.

Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]`. Conclude with `h1 _ _ (by simpa [b'] using hij)`. Rewrite using `[← map_inv] show Matrix.reindex e.symm e.symm ((p.1⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j = 0`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]`. Conclude with `h2 _ _ (by simpa [b'] using hij)`.

Establish `hpar' : ∀ q : parab K b, A.symm q.1 ∈ parab K b'`. Introduce `q`. Take `⟨h1, h2⟩` from `q.2`. Use `⟨fun i j hij => ?_, fun i j hij => ?_⟩` and prove the remaining obligations. Use `show Matrix.reindex e e (q.1 : Matrix (Fin r) (Fin r) K) i j = 0`.

Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_apply]`. Conclude with `h1 _ _ hij`. Rewrite using `[← map_inv] show Matrix.reindex e e ((q.1⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j = 0`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_apply]`. Conclude with `h2 _ _ hij`.

Establish `hlevi : ∀ (p : parab K b') (c : Fin s), levi K b c ⟨A p.1, hpar p⟩ = (glEquiv K (ec c)).symm (levi K b' c p)`. Introduce `p c`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Both sides reduce to the same expression.

Establish `hinfl : ∀ p : parab K b', infl K b lam ⟨A p.1, hpar p⟩ = infl K b' lam' p`. Introduce `p`. Unfold `infl`. Use `congr 1`. Establish `hinfl' : ∀ q : parab K b, infl K b lam q = infl K b' lam' ⟨A.symm q.1, hpar' q⟩`.

Introduce `q`. Rewrite using `[← hinfl]`. Use `congr 2`. Conclude with `Subtype.ext (A.apply_symm_apply q.1).symm`. Set `Ψ : hcSpace K b lam ≃ₗ[ℂ] hcSpace K b' lam'` to `{ toFun := fun F => ⟨fun x => F.1 (A x), fun p x => by show F.1 (A (p.1 * x)) = infl K b' lam' p (F.1 (A x))`.

Rewrite using `[map_mul, ← hinfl]`. Conclude with `F.2 ⟨A p.1, hpar p⟩ (A x)⟩`. Use `invFun := fun F => ⟨fun x => F.1 (A.symm x), fun q x => by show F.1 (A.symm (q.1 * x)) = infl K b lam q (F.1 (A.symm x))`. Rewrite using `[map_mul, hinfl']`. Conclude with `F.2 ⟨A.symm q.1, hpar' q⟩ (A.symm x)⟩`.

Use the proof step `map_add' := fun F G => rfl`. Use the proof step `map_smul' := fun a F => rfl`. Use `left_inv := fun F => Subtype.ext (_root_.funext fun x => congrArg F.1 (A.apply_symm_apply x))`. Use `right_inv := fun F => Subtype.ext (_root_.funext fun x => congrArg F.1 (A.symm_apply_apply x)) }`. Use `⟨b', lam', hb.comp e.symm.surjective, ?_, fun c => ⟨Formalism.L2.PT.simple_transp _ (hl c).1, Formalism.L2.PT.isCuspidal_transp _ (hl c).2⟩, fun c => GlobalTheory.SerOSys.TranspLabel.labO_transp O (ec c) (lam c), ?_⟩` and prove the remaining obligations.

Conclude with `Tuple.monotone_sort b`. Use `isIrrRep_of_equiv _ _ A A.surjective Ψ fun g F => ?_` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Use `show F.1 (A x * A g) = F.1 (A (x * g))`.

Rewrite using `[map_mul]`.
-/
theorem exists_sorted {C : LabelConv K} (O : LabelMap K C) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (hb : Function.Surjective b)
    (hl : ∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) :
    ∃ (b' : Fin r → Fin s) (lam' : ∀ c : Fin s, FDRep ℂ (GL {i // b' i = c} K)), Function.Surjective b' ∧
      Monotone b' ∧ (∀ c, Simple (lam' c) ∧ IsCuspidal K (lam' c)) ∧ (∀ c, labO O (lam' c) = labO O (lam c)) ∧
      (IsIrrRep (hcRep K b' lam') → IsIrrRep (hcRep K b lam)) := by
  let e : Fin r ≃ Fin r := (Tuple.sort b).symm
  let b' : Fin r → Fin s := b ∘ e.symm
  let ec : ∀ c, {i // b i = c} ≃ {k // b' k = c} := fun c => e.subtypeEquiv (fun i => by simp [b'])
  let lam' : ∀ c : Fin s, FDRep ℂ (GL {k // b' k = c} K) := fun c => transp (ec c) (lam c)
  let A : GL (Fin r) K ≃* GL (Fin r) K := (glEquiv K e).symm
  have hpar : ∀ p : parab K b', A p.1 ∈ parab K b := by
    intro p
    obtain ⟨h1, h2⟩ := p.2
    refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · show Matrix.reindex e.symm e.symm (p.1 : Matrix (Fin r) (Fin r) K) i j = 0
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
      exact h1 _ _ (by simpa [b'] using hij)
    · rw [← map_inv]
      show Matrix.reindex e.symm e.symm ((p.1⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j = 0
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
      exact h2 _ _ (by simpa [b'] using hij)
  have hpar' : ∀ q : parab K b, A.symm q.1 ∈ parab K b' := by
    intro q
    obtain ⟨h1, h2⟩ := q.2
    refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · show Matrix.reindex e e (q.1 : Matrix (Fin r) (Fin r) K) i j = 0
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
      exact h1 _ _ hij
    · rw [← map_inv]
      show Matrix.reindex e e ((q.1⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j = 0
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
      exact h2 _ _ hij
  have hlevi : ∀ (p : parab K b') (c : Fin s),
      levi K b c ⟨A p.1, hpar p⟩ = (glEquiv K (ec c)).symm (levi K b' c p) := by
    intro p c
    apply Units.ext
    ext i j
    rfl
  have hinfl : ∀ p : parab K b', infl K b lam ⟨A p.1, hpar p⟩ = infl K b' lam' p := by
    intro p
    unfold infl
    congr 1
  have hinfl' : ∀ q : parab K b, infl K b lam q = infl K b' lam' ⟨A.symm q.1, hpar' q⟩ := by
    intro q
    rw [← hinfl]
    congr 2
    exact Subtype.ext (A.apply_symm_apply q.1).symm
  let Ψ : hcSpace K b lam ≃ₗ[ℂ] hcSpace K b' lam' :=
    { toFun := fun F => ⟨fun x => F.1 (A x), fun p x => by
        show F.1 (A (p.1 * x)) = infl K b' lam' p (F.1 (A x))
        rw [map_mul, ← hinfl]
        exact F.2 ⟨A p.1, hpar p⟩ (A x)⟩
      invFun := fun F => ⟨fun x => F.1 (A.symm x), fun q x => by
        show F.1 (A.symm (q.1 * x)) = infl K b lam q (F.1 (A.symm x))
        rw [map_mul, hinfl']
        exact F.2 ⟨A.symm q.1, hpar' q⟩ (A.symm x)⟩
      map_add' := fun F G => rfl
      map_smul' := fun a F => rfl
      left_inv := fun F => Subtype.ext (_root_.funext fun x => congrArg F.1 (A.apply_symm_apply x))
      right_inv := fun F => Subtype.ext (_root_.funext fun x => congrArg F.1 (A.symm_apply_apply x)) }
  refine ⟨b', lam', hb.comp e.symm.surjective, ?_, fun c => ⟨Formalism.L2.PT.simple_transp _ (hl c).1,
    Formalism.L2.PT.isCuspidal_transp _ (hl c).2⟩, fun c => GlobalTheory.SerOSys.TranspLabel.labO_transp O (ec c) (lam c), ?_⟩
  · exact Tuple.monotone_sort b
  · refine isIrrRep_of_equiv _ _ A A.surjective Ψ fun g F => ?_
    apply Subtype.ext
    funext x
    show F.1 (A x * A g) = F.1 (A (x * g))
    rw [map_mul]

/- English proof (translation)
Rewrite using `[← GlobalTheory.SerOSys.TranspLabel.labO_transp O e σ, ← GlobalTheory.SerOSys.TranspLabel.labO_transp O e' σ']`. Unfold `labO`. Apply `O.lab_iso` to reduce the goal to its premises. Conclude with `⟨GlobalTheory.SerOSys.TranspLabel.repIsoOf _ _ M fun γ v => hM _ v⟩`.
-/
theorem labO_eq_of_readings {C : LabelConv K} (O : LabelMap K C) {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (d : ℕ) (e : α ≃ Fin d) (e' : β ≃ Fin d) (σ : FDRep ℂ (GL α K))
    (σ' : FDRep ℂ (GL β K)) (M : (σ : Type) ≃ₗ[ℂ] (σ' : Type))
    (hM : ∀ g v, M (σ.ρ ((glEquiv K e).symm g) v) = σ'.ρ ((glEquiv K e').symm g) (M v)) :
    labO O σ = labO O σ' := by
  rw [← GlobalTheory.SerOSys.TranspLabel.labO_transp O e σ, ← GlobalTheory.SerOSys.TranspLabel.labO_transp O e' σ']
  unfold labO
  apply O.lab_iso
  exact ⟨GlobalTheory.SerOSys.TranspLabel.repIsoOf _ _ M fun γ v => hM _ v⟩

/- English proof (translation)
Introduce and unpack `_ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne ⟨d, h, h', W, _, _, ρ, hf, hf'⟩`. Take `⟨e, L, hL⟩` from `GlobalTheory.T.hasCuspidalFactorAtBlock_leviPiTensor K r s b lam hs (b i) d h W ρ hf`. Take `⟨e', L', hL'⟩` from `GlobalTheory.T.hasCuspidalFactorAtBlock_leviPiTensor K r s b lam hs (b j) d h' W ρ hf'`. Establish `hlab : labO O (lam (b i)) = labO O (lam (b j))`. Use `labO_eq_of_readings O d e e' _ _ (L.symm.trans L') fun g v => ?_` and prove the remaining obligations.

Take `⟨w, rfl⟩` from `L.surjective v`. Rewrite using `[← hL]`. Simplify using `[hL']`. Conclude with `hne (congrArg (fun c : Fin s => (c : ℕ)) (hinj hlab))`.
-/
theorem distinctFactors {C : LabelConv K} (O : LabelMap K C) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (hs : ∀ c, Simple (lam c))
    (hinj : Function.Injective (fun c => labO O (lam c))) :
    GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors.DistinctFactors (natBlocks b) (leviTensor b lam) := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne ⟨d, h, h', W, _, _, ρ, hf, hf'⟩
  obtain ⟨e, L, hL⟩ := GlobalTheory.T.hasCuspidalFactorAtBlock_leviPiTensor K r s b lam hs (b i) d h W ρ hf
  obtain ⟨e', L', hL'⟩ := GlobalTheory.T.hasCuspidalFactorAtBlock_leviPiTensor K r s b lam hs (b j) d h' W ρ hf'
  have hlab : labO O (lam (b i)) = labO O (lam (b j)) := by
    refine labO_eq_of_readings O d e e' _ _ (L.symm.trans L') fun g v => ?_
    obtain ⟨w, rfl⟩ := L.surjective v
    rw [← hL]
    simp [hL']
  exact hne (congrArg (fun c : Fin s => (c : ℕ)) (hinj hlab))

/- English proof (translation)
Establish `hd : GlobalTheory.FinGL.IsCuspDatum (natBlocks b) (leviTensor b lam)` using `{ mono := fun i j hij => hm hij irr := GlobalTheory.T.leviPiTensorRepresentation_isIrreducible K r s b lam fun c => (hl c).1 infl := fun p hp => by`. Rewrite using `[leviTensor_apply]`. Establish `: ∀ c, (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) p)) = LinearMap.id`. Introduce `c`. Establish `h1 : levi K b c (Subgroup.inclusion (blockTri_le_parab b) p) = 1`.

Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `x y`. Use `hp x.1 y.1 (by simp [natBlocks, x.2, y.2])` as an intermediate fact. Use `show ((p : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) x.1 y.1 = (1 : Matrix _ _ K) x y`. Rewrite using `[this]`.

Simplify using `[Matrix.one_apply, Subtype.ext_iff]`. Rewrite using `[h1, map_one]`. Both sides reduce to the same expression. Simplify using `only [this]`. Conclude with `PiTensorProduct.map_id`.

Use `cusp := fun S hS y hy => GlobalTheory.T.cuspidal_piTensor_no_blockUnipotent_fixed K r s b lam (fun c => (hl c).2) S hS y hy }`. Conclude with `isIrrRep_hcRep_of_parInd b lam ((GlobalTheory.CuspFactor.irrPar_iff_cuspidalProduct.1 GlobalTheory.FinGL.IrrProduct.irrPar).1 K r _ _ _ hd (distinctFactors O b lam (fun c => (hl c).1) hinj))`.
-/
theorem isIrrRep_of_monotone {C : LabelConv K} (O : LabelMap K C) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    (hl : ∀ c, Simple (lam c) ∧ IsCuspidal K (lam c))
    (hinj : Function.Injective (fun c => labO O (lam c))) (hm : Monotone b) : IsIrrRep (hcRep K b lam) := by
  have hd : GlobalTheory.FinGL.IsCuspDatum (natBlocks b) (leviTensor b lam) :=
    { mono := fun i j hij => hm hij
      irr := GlobalTheory.T.leviPiTensorRepresentation_isIrreducible K r s b lam fun c => (hl c).1
      infl := fun p hp => by
        rw [leviTensor_apply]
        have : ∀ c, (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) p)) = LinearMap.id := by
          intro c
          have h1 : levi K b c (Subgroup.inclusion (blockTri_le_parab b) p) = 1 := by
            apply Units.ext
            ext x y
            have := hp x.1 y.1 (by simp [natBlocks, x.2, y.2])
            show ((p : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) x.1 y.1 = (1 : Matrix _ _ K) x y
            rw [this]
            simp [Matrix.one_apply, Subtype.ext_iff]
          rw [h1, map_one]
          rfl
        simp only [this]
        exact PiTensorProduct.map_id
      cusp := fun S hS y hy => GlobalTheory.T.cuspidal_piTensor_no_blockUnipotent_fixed K r s b lam (fun c => (hl c).2) S hS y hy }
  exact isIrrRep_hcRep_of_parInd b lam
    ((GlobalTheory.CuspFactor.irrPar_iff_cuspidalProduct.1 GlobalTheory.FinGL.IrrProduct.irrPar).1 K r _ _ _ hd
      (distinctFactors O b lam (fun c => (hl c).1) hinj))

/- English proof (translation)
Introduce `K _ _ _ r s b lam hb hl C O hinj`. Take `⟨b', lam', hb', hm, hl', hlab, hback⟩` from `exists_sorted O b lam hb hl`. Conclude with `hback (isIrrRep_of_monotone O b' lam' hl' (fun c c' h => hinj (by simpa [hlab] using h)) hm)`.
-/
theorem isIrrRep_hcRep : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), Function.Surjective b →
    (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → ∀ (C : LabelConv K) (O : LabelMap K C),
    Function.Injective (fun c => labO O (lam c)) → IsIrrRep (hcRep K b lam) := by
  intro K _ _ _ r s b lam hb hl C O hinj
  obtain ⟨b', lam', hb', hm, hl', hlab, hback⟩ := exists_sorted O b lam hb hl
  exact hback (isIrrRep_of_monotone O b' lam' hl'
    (fun c c' h => hinj (by simpa [hlab] using h)) hm)

end GlobalTheory.HcIrr

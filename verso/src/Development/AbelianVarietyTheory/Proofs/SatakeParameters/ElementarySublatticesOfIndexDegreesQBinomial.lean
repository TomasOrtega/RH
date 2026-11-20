import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QBinomialSumCardQuotientSubspacesStatement

noncomputable section

namespace GlobalTheory.LatHecke

open IsLocalRing

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] {r : ℕ}

abbrev Red (N : Submodule O (Fin r → K)) : Type := N ⧸ (maximalIdeal O • ⊤ : Submodule O N)

instance Red.instModule (N : Submodule O (Fin r → K)) : Module (ResidueField O) (Red N) :=
  inferInstanceAs (Module (O ⧸ maximalIdeal O) (Red N))

instance Red.instTower (N : Submodule O (Fin r → K)) : IsScalarTower O (ResidueField O) (Red N) := by
  refine ⟨fun a b x => ?_⟩
  obtain ⟨b, rfl⟩ := residue_surjective b
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change (a • residue O b) • (Submodule.Quotient.mk x : Red N) = a • (residue O b • (Submodule.Quotient.mk x : Red N))
  have h : ∀ (c : O) (y : N), residue O c • (Submodule.Quotient.mk y : Red N) = Submodule.Quotient.mk (c • y) :=
    fun c y => rfl
  have h2 : a • residue O b = residue O (a * b) := by
    rw [Algebra.smul_def]; simp [ResidueField.algebraMap_eq]
  rw [h2, h, h, mul_smul]; rfl

def pull (N : Submodule O (Fin r → K)) (W : Submodule (ResidueField O) (Red N)) : Submodule O N :=
  (W.restrictScalars O).comap (Submodule.mkQ _)

/- English proof (translation)
Introduce `x hx`. Establish `: Submodule.mkQ (maximalIdeal O • ⊤ : Submodule O N) x = 0`. Simplify using `using hx`. Simplify using `[pull, this]`.
-/
theorem smul_top_le_pull (N : Submodule O (Fin r → K)) (W : Submodule (ResidueField O) (Red N)) :
    (maximalIdeal O • ⊤ : Submodule O N) ≤ pull N W := by
  intro x hx
  have : Submodule.mkQ (maximalIdeal O • ⊤ : Submodule O N) x = 0 := by
    simpa using hx
  simp [pull, this]

/- English proof (translation)
Set `f : N →ₗ[O] (Red N ⧸ W)` to `(W.mkQ.restrictScalars O) ∘ₗ (Submodule.mkQ _)`. Establish `hs : Function.Surjective f` using `(Submodule.mkQ_surjective W).comp (Submodule.mkQ_surjective _)`. Establish `hk : LinearMap.ker f = pull N W`. Use extensionality with `x`. Simplify using `[f, pull, LinearMap.mem_ker]`.

Conclude with `Nat.card_congr ((Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hs)).toEquiv`.
-/
theorem card_quot_pull (N : Submodule O (Fin r → K)) (W : Submodule (ResidueField O) (Red N)) :
    Nat.card (N ⧸ pull N W) = Nat.card (Red N ⧸ W) := by
  let f : N →ₗ[O] (Red N ⧸ W) := (W.mkQ.restrictScalars O) ∘ₗ (Submodule.mkQ _)
  have hs : Function.Surjective f :=
    (Submodule.mkQ_surjective W).comp (Submodule.mkQ_surjective _)
  have hk : LinearMap.ker f = pull N W := by
    ext x
    simp [f, pull, LinearMap.mem_ker]
  exact Nat.card_congr
    ((Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hs)).toEquiv

/- English proof (translation)
Introduce `W W' h`. Apply `Submodule.restrictScalars_injective O` to reduce the goal to its premises. Conclude with `Submodule.comap_injective_of_surjective (Submodule.mkQ_surjective _) h`.
-/
theorem pull_injective (N : Submodule O (Fin r → K)) :
    Function.Injective (pull (O := O) N) := by
  intro W W' h
  apply Submodule.restrictScalars_injective O
  exact Submodule.comap_injective_of_surjective (Submodule.mkQ_surjective _) h

/- English proof (translation)
Set `W : Submodule (ResidueField O) (Red N)` to `{ carrier := ((C.map (Submodule.mkQ (maximalIdeal O • ⊤ : Submodule O N)) : Submodule O (Red N)) : Set (Red N)) add_mem' := fun ha hb => Submodule.add_mem _ ha hb zero_mem' := Submodule.zero_mem _ smul_mem' := by`. Introduce `c x hx`. Take `⟨c, rfl⟩` from `residue_surjective c`. Establish `: residue O c • x = c • x`. Rewrite using `[← algebraMap_smul (ResidueField O) c x]`.

Both sides reduce to the same expression. Rewrite using `[this]`. Establish `hx' : x ∈ C.map (Submodule.mkQ (maximalIdeal O • ⊤ : Submodule O N))` using `hx`. Conclude with `(C.map (Submodule.mkQ (maximalIdeal O • ⊤ : Submodule O N))).smul_mem c hx' }`. Use `⟨W, ?_⟩` and prove the remaining obligations.

Establish `: W.restrictScalars O = C.map (Submodule.mkQ _)`. Use extensionality with `x`. Both sides reduce to the same expression. Rewrite using `[pull, this, Submodule.comap_map_mkQ, sup_eq_right.2 hC]`.
-/
theorem exists_pull (N : Submodule O (Fin r → K)) (C : Submodule O N)
    (hC : (maximalIdeal O • ⊤ : Submodule O N) ≤ C) :
    ∃ W : Submodule (ResidueField O) (Red N), pull N W = C := by
  let W : Submodule (ResidueField O) (Red N) :=
    { carrier := ((C.map (Submodule.mkQ (maximalIdeal O • ⊤ : Submodule O N)) : Submodule O (Red N)) : Set (Red N))
      add_mem' := fun ha hb => Submodule.add_mem _ ha hb
      zero_mem' := Submodule.zero_mem _
      smul_mem' := by
        intro c x hx
        obtain ⟨c, rfl⟩ := residue_surjective c
        have : residue O c • x = c • x := by
          rw [← algebraMap_smul (ResidueField O) c x]; rfl
        rw [this]
        have hx' : x ∈ C.map (Submodule.mkQ (maximalIdeal O • ⊤ : Submodule O N)) := hx
        exact (C.map (Submodule.mkQ (maximalIdeal O • ⊤ : Submodule O N))).smul_mem c hx' }
  refine ⟨W, ?_⟩
  have : W.restrictScalars O = C.map (Submodule.mkQ _) := by
    ext x; rfl
  rw [pull, this, Submodule.comap_map_mkQ, sup_eq_right.2 hC]

variable [IsFractionRing O K]

/- English proof (translation)
Rewrite using `[Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]`.
-/
theorem map_subtype_smul_top (N : Submodule O (Fin r → K)) :
    (maximalIdeal O • ⊤ : Submodule O N).map N.subtype = maximalIdeal O • N := by
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]

def toLat (L : Lat O K r) (W : Submodule (ResidueField O) (Red L.1)) : Lat O K r :=
  ⟨(pull L.1 W).map L.1.subtype,
    { fg := by
        haveI : Module.Finite O L.1 := Module.Finite.iff_fg.2 L.2.fg
        exact (IsNoetherian.noetherian (pull L.1 W)).map _
      span_eq_top := by
        have hle : (maximalIdeal O • L.1 : Submodule O (Fin r → K)) ≤ (pull L.1 W).map L.1.subtype := by
          rw [← map_subtype_smul_top]
          exact Submodule.map_mono (smul_top_le_pull _ _)
        rw [eq_top_iff, ← (maxMul L).2.span_eq_top]
        exact Submodule.span_mono hle }⟩

/- English proof (translation)
Introduce `W W' h`. Apply `pull_injective L.1` to reduce the goal to its premises. Conclude with `Submodule.map_injective_of_injective L.1.injective_subtype (congrArg Subtype.val h)`.
-/
theorem toLat_injective (L : Lat O K r) : Function.Injective (toLat L) := by
  intro W W' h
  apply pull_injective L.1
  exact Submodule.map_injective_of_injective L.1.injective_subtype (congrArg Subtype.val h)

/- English proof (translation)
Establish `h1 : (toLat L W).1.toAddSubgroup.relIndex L.1.toAddSubgroup = Nat.card (L.1 ⧸ (toLat L W).1.comap L.1.subtype)` using `rfl`. Establish `h2 : (toLat L W).1.comap L.1.subtype = pull L.1 W` using `Submodule.comap_map_eq_of_injective L.1.injective_subtype _`. Rewrite using `[h1, h2, card_quot_pull]`.
-/
theorem card_quot_toLat [Finite (ResidueField O)] (L : Lat O K r)
    (W : Submodule (ResidueField O) (Red L.1)) :
    (toLat L W).1.toAddSubgroup.relIndex L.1.toAddSubgroup = Nat.card (Red L.1 ⧸ W) := by
  have h1 : (toLat L W).1.toAddSubgroup.relIndex L.1.toAddSubgroup
      = Nat.card (L.1 ⧸ (toLat L W).1.comap L.1.subtype) := rfl
  have h2 : (toLat L W).1.comap L.1.subtype = pull L.1 W :=
    Submodule.comap_map_eq_of_injective L.1.injective_subtype _
  rw [h1, h2, card_quot_pull]

/- English proof (translation)
Establish `hc : (maximalIdeal O • L.1).comap L.1.subtype = (maximalIdeal O • ⊤ : Submodule O L.1)`. Rewrite using `[← map_subtype_smul_top]`. Conclude with `Submodule.comap_map_eq_of_injective L.1.injective_subtype _`. Establish `h1 : (maxMul L).1.toAddSubgroup.relIndex L.1.toAddSubgroup = Nat.card (L.1 ⧸ (maximalIdeal O • L.1).comap L.1.subtype)` using `rfl`. Rewrite using `[← relIndex_maxMul L, h1, hc]`.
-/
theorem card_red [Finite (ResidueField O)] (L : Lat O K r) :
    Nat.card (Red L.1) = qRes O ^ r := by
  have hc : (maximalIdeal O • L.1).comap L.1.subtype = (maximalIdeal O • ⊤ : Submodule O L.1) := by
    rw [← map_subtype_smul_top]
    exact Submodule.comap_map_eq_of_injective L.1.injective_subtype _
  have h1 : (maxMul L).1.toAddSubgroup.relIndex L.1.toAddSubgroup
      = Nat.card (L.1 ⧸ (maximalIdeal O • L.1).comap L.1.subtype) := rfl
  rw [← relIndex_maxMul L, h1, hc]

/- English proof (translation)
The claim follows from `Nat.finite_of_card_ne_zero (by rw [card_red]; exact (pow_pos (lt_of_lt_of_le two_pos two_le_qRes) _).ne')`.
-/
theorem finite_red [Finite (ResidueField O)] (L : Lat O K r) : Finite (Red L.1) :=
  Nat.finite_of_card_ne_zero (by
    rw [card_red]; exact (pow_pos (lt_of_lt_of_le two_pos two_le_qRes) _).ne')

/- English proof (translation)
Use `haveI := finite_red L`. Use `haveI : Module.Finite (ResidueField O) (Red L.1) := Module.Finite.of_finite`. Establish `h` using `card_red L`. Rewrite `h` using `[Module.natCard_eq_pow_finrank (K := ResidueField O)]`. Conclude with `Nat.pow_right_injective (two_le_qRes (O := O)) h`.
-/
theorem finrank_red [Finite (ResidueField O)] (L : Lat O K r) :
    Module.finrank (ResidueField O) (Red L.1) = r := by
  haveI := finite_red L
  haveI : Module.Finite (ResidueField O) (Red L.1) := Module.Finite.of_finite
  have h := card_red L
  rw [Module.natCard_eq_pow_finrank (K := ResidueField O)] at h
  exact Nat.pow_right_injective (two_le_qRes (O := O)) h

/- English proof (translation)
Use `haveI := finite_red L`. Establish `hidx : ∀ W : Submodule (ResidueField O) (Red L.1), (toLat L W).1.toAddSubgroup.relIndex L.1.toAddSubgroup = qRes O ^ Module.finrank (ResidueField O) (Red L.1 ⧸ W)`. Introduce `W`. Use `haveI : Finite (Red L.1 ⧸ W) := Finite.of_surjective _ (Submodule.mkQ_surjective W)`. Use `haveI : Module.Finite (ResidueField O) (Red L.1 ⧸ W) := Module.Finite.of_finite`.

Rewrite using `[card_quot_toLat, Module.natCard_eq_pow_finrank (K := ResidueField O)]`. Both sides reduce to the same expression. Establish `hle : ∀ W : Submodule (ResidueField O) (Red L.1), (toLat L W).1 ≤ L.1` using `fun W => Submodule.map_subtype_le _ _`. Establish `hlow : ∀ W : Submodule (ResidueField O) (Red L.1), maximalIdeal O • L.1 ≤ (toLat L W).1` using `fun W => by`. Rewrite using `[← map_subtype_smul_top]`.

Conclude with `Submodule.map_mono (smul_top_le_pull _ _)`. Set `f : {W : Submodule (ResidueField O) (Red L.1) // Module.finrank (ResidueField O) (Red L.1 ⧸ W) = j} → subElem j L` to `fun W => ⟨toLat L W.1, ⟨hle W.1, by rw [hidx, W.2]⟩, hlow W.1⟩`. Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion. Introduce `W W' h`.

Conclude with `Subtype.ext (toLat_injective L (congrArg (fun x => x.1) h))`. Introduce and unpack `⟨M, ⟨h1, h2⟩, h3⟩`. Establish `hC : (maximalIdeal O • ⊤ : Submodule O L.1) ≤ M.1.comap L.1.subtype`. Rewrite using `[← Submodule.map_le_iff_le_comap, map_subtype_smul_top]`. Conclude with `h3`.

Take `⟨W, hW⟩` from `exists_pull L.1 _ hC`. Establish `hM : toLat L W = M`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(pull L.1 W).map L.1.subtype = M.1`. Rewrite using `[hW, Submodule.map_comap_subtype, inf_eq_right.2 h1]`.

Establish `hj : Module.finrank (ResidueField O) (Red L.1 ⧸ W) = j`. Use `hidx W` as an intermediate fact. Rewrite `this` using `[hM, h2]`. Conclude with `(Nat.pow_right_injective (two_le_qRes (O := O)) this).symm`. Conclude with `⟨⟨W, hj⟩, Subtype.ext hM⟩`.

Rewrite using `[← Nat.card_coe_set_eq]`. Conclude with `(Nat.card_congr (Equiv.ofBijective f hf)).symm`.
-/
theorem ncard_subElem [Finite (ResidueField O)] (L : Lat O K r) (j : ℕ) :
    (subElem j L).ncard = Nat.card
      {W : Submodule (ResidueField O) (Red L.1) // Module.finrank (ResidueField O) (Red L.1 ⧸ W) = j} := by
  haveI := finite_red L
  have hidx : ∀ W : Submodule (ResidueField O) (Red L.1),
      (toLat L W).1.toAddSubgroup.relIndex L.1.toAddSubgroup
        = qRes O ^ Module.finrank (ResidueField O) (Red L.1 ⧸ W) := by
    intro W
    haveI : Finite (Red L.1 ⧸ W) := Finite.of_surjective _ (Submodule.mkQ_surjective W)
    haveI : Module.Finite (ResidueField O) (Red L.1 ⧸ W) := Module.Finite.of_finite
    rw [card_quot_toLat, Module.natCard_eq_pow_finrank (K := ResidueField O)]
    rfl
  have hle : ∀ W : Submodule (ResidueField O) (Red L.1), (toLat L W).1 ≤ L.1 := fun W =>
    Submodule.map_subtype_le _ _
  have hlow : ∀ W : Submodule (ResidueField O) (Red L.1),
      maximalIdeal O • L.1 ≤ (toLat L W).1 := fun W => by
    rw [← map_subtype_smul_top]
    exact Submodule.map_mono (smul_top_le_pull _ _)
  let f : {W : Submodule (ResidueField O) (Red L.1) //
      Module.finrank (ResidueField O) (Red L.1 ⧸ W) = j} → subElem j L :=
    fun W => ⟨toLat L W.1, ⟨hle W.1, by rw [hidx, W.2]⟩, hlow W.1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro W W' h
      exact Subtype.ext (toLat_injective L (congrArg (fun x => x.1) h))
    · rintro ⟨M, ⟨h1, h2⟩, h3⟩
      have hC : (maximalIdeal O • ⊤ : Submodule O L.1) ≤ M.1.comap L.1.subtype := by
        rw [← Submodule.map_le_iff_le_comap, map_subtype_smul_top]
        exact h3
      obtain ⟨W, hW⟩ := exists_pull L.1 _ hC
      have hM : toLat L W = M := by
        apply Subtype.ext
        change (pull L.1 W).map L.1.subtype = M.1
        rw [hW, Submodule.map_comap_subtype, inf_eq_right.2 h1]
      have hj : Module.finrank (ResidueField O) (Red L.1 ⧸ W) = j := by
        have := hidx W
        rw [hM, h2] at this
        exact (Nat.pow_right_injective (two_le_qRes (O := O)) this).symm
      exact ⟨⟨W, hj⟩, Subtype.ext hM⟩
  rw [← Nat.card_coe_set_eq]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

/- English proof (translation)
Introduce `O K _ _ _ _ _ _ _ r L`. Use `⟨subIdx_zero L, subElem_zero L, fun k hk => subElem_eq_empty hk L, fun X => ?_⟩` and prove the remaining obligations. Use `haveI := finite_red L`. Use `haveI : Module.Finite (ResidueField O) (Red L.1) := Module.Finite.of_finite`. Establish `h` using `GlobalTheory.T.qBinomial_sum_card_quotient_subspaces (ResidueField O) (Red L.1) X`.

Rewrite `h` using `[finrank_red L]`. Simplify using `only [ncard_subElem L]`. Conclude with `h`.
-/
theorem subElem_degrees : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ)
    (L : Lat O K r), subIdx 0 L = {L} ∧ subElem 0 L = {L} ∧ (∀ k, r < k → subElem k L = ∅) ∧
      ∀ X : ℂ, ∑ k ∈ Finset.range (r + 1), (-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2) *
        ((subElem k L).ncard : ℂ) * X ^ k = ∏ i ∈ Finset.range r, (1 - (qRes O : ℂ) ^ i * X) := by
  intro O K _ _ _ _ _ _ _ r L
  refine ⟨subIdx_zero L, subElem_zero L, fun k hk => subElem_eq_empty hk L, fun X => ?_⟩
  haveI := finite_red L
  haveI : Module.Finite (ResidueField O) (Red L.1) := Module.Finite.of_finite
  have h := GlobalTheory.T.qBinomial_sum_card_quotient_subspaces (ResidueField O) (Red L.1) X
  rw [finrank_red L] at h
  simp only [ncard_subElem L]
  exact h

end GlobalTheory.LatHecke

import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.OpenSlices.LatticeIndices.RelIndexLatConj
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.Unimodularity.UnimodOfIndexSym
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.SymmetricIndices.DetMulLeftEq

noncomputable section

open Matrix GroundTheory.Automorphic ValuativeRel

namespace PositivityTheory.RgUd.TP.Loc.Uni

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc.SLF PositivityTheory.RgUd.T.Desc.SLT PositivityTheory.RgUd.T.Desc.SLT.Bi PositivityTheory.RgUd.TP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

/- English proof (translation)
Take `⟨c, -, hc⟩` from `exists_shift Z g hg`. Use `⟨c, fun r hr => ?_⟩` and prove the remaining obligations. Establish `hg' : g⁻¹ ∈ Gz Z` using `(GzS Z).inv_mem hg`. Establish `hL : Lat Z r = (Lat Z 0).map (smulA (pi k ^ r))` using `by simpa using Lat_add Z r 0`. Establish `hmem : ∀ y ∈ Lat Z 0, pi k ^ r • conjA g⁻¹ y ∈ Lat Z 0`.

Introduce `y hy`. Establish `h1 : smulA (pi k ^ r) y ∈ Lat Z ((r - c) + c)`. Rewrite using `[show r - c + c = r by omega, hL]; exact ⟨y, hy, rfl⟩`. Establish `h2` using `(hc _ _ h1).2`. Rewrite `h2` using `[conjA_smulA]`.

Conclude with `Lat_anti Z (Nat.zero_le _) h2`. Set `ϖ : 𝒪[k]` to `GLnLocal.uniformizer k`. Establish `hϖ0 : ϖ ≠ 0` using `(GLnLocal.irreducible_uniformizer k).ne_zero`. Establish `hϖk : ((ϖ ^ r : 𝒪[k]) : k) = pi k ^ r` using `by simp [ϖ]`. Set `f1 : LatO Z →ₗ[𝒪[k]] LatO Z` to `(ϖ ^ r) • LinearMap.id`.

Set `f2 : LatO Z →ₗ[𝒪[k]] LatO Z` to `{ toFun := fun y => ⟨pi k ^ r • conjA g⁻¹ y, hmem y y.2⟩ map_add' := fun x y => Subtype.ext (by simp [mul_add, add_mul, smul_add]) map_smul' := fun a y => Subtype.ext (by`. Express the relevant statement in the definitionally equal form `pi k ^ r • conjA g⁻¹ ((a : k) • (y : Matrix (Fin n) (Fin n) k)) = (a : k) • (pi k ^ r • conjA g⁻¹ (y : Matrix (Fin n) (Fin n) k))`. Rewrite using `[← smulA_apply (a : k), conjA_smulA, smulA_apply, smul_comm]) }`. Set `B` to `Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))`. Set `F1 : B →ₗ[k] B` to `(pi k ^ r) • LinearMap.id`.

Set `F2 : B →ₗ[k] B` to `(pi k ^ r) • conjB Z g⁻¹ hg'`. Establish `t1` using `det_transfer Z F1 f1 (fun x => by`. Express the relevant statement in the definitionally equal form `pi k ^ r • (x : Matrix (Fin n) (Fin n) k) = ((ϖ ^ r : 𝒪[k]) : k) • (x : Matrix (Fin n) (Fin n) k)`. Rewrite using `[hϖk])`. Establish `t2` using `det_transfer Z F2 f2 (fun x => rfl)`.

Establish `dF : LinearMap.det F1 = LinearMap.det F2`. Simplify using `only [F1, F2, LinearMap.det_smul, LinearMap.det_id, det_conjB Z τ hsym hnd g⁻¹ hg']`. Establish `df : LinearMap.det f1 = LinearMap.det f2` using `Subtype.val_injective (t1.trans (dF.trans t2.symm))`. Establish `hf1 : LinearMap.det f1 ≠ 0`. Simplify using `only [f1, LinearMap.det_smul, LinearMap.det_id, mul_one]`.

Conclude with `pow_ne_zero _ (pow_ne_zero _ hϖ0)`. Establish `i1 : (Lat Z r).relIndex (Lat Z 0) = Nat.card (LatO Z ⧸ LinearMap.range f1)`. Use `relIndex_eq_card Z _ f1 fun x => ?_` and prove the remaining obligations. Rewrite using `[hL, AddSubgroup.mem_map]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, rfl⟩`. Use `⟨⟨y, hy⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((ϖ ^ r : 𝒪[k]) : k) • y = smulA (pi k ^ r) y`. Rewrite using `[hϖk]`. Both sides reduce to the same expression.

Introduce and unpack `⟨y, rfl⟩`. Use `⟨y, y.2, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `smulA (pi k ^ r) (y : Matrix (Fin n) (Fin n) k) = ((ϖ ^ r : 𝒪[k]) : k) • (y : Matrix (Fin n) (Fin n) k)`. Rewrite using `[hϖk]`. Both sides reduce to the same expression.

Establish `i2 : ((Lat Z r).map (conjA g⁻¹)).relIndex (Lat Z 0) = Nat.card (LatO Z ⧸ LinearMap.range f2)`. Use `relIndex_eq_card Z _ f2 fun x => ?_` and prove the remaining obligations. Rewrite using `[hL, AddSubgroup.map_map, AddSubgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`.

Use `⟨⟨y, hy⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `pi k ^ r • conjA g⁻¹ y = conjA g⁻¹ (smulA (pi k ^ r) y)`. Rewrite using `[conjA_smulA]`. Both sides reduce to the same expression. Introduce and unpack `⟨y, rfl⟩`.

Use `⟨y, y.2, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `conjA g⁻¹ (smulA (pi k ^ r) (y : Matrix (Fin n) (Fin n) k)) = pi k ^ r • conjA g⁻¹ (y : Matrix (Fin n) (Fin n) k)`. Rewrite using `[conjA_smulA]`. Both sides reduce to the same expression. Establish `c1` using `PI.NGStepBBW.card_coker_endo f1 hf1`.

Establish `c2` using `PI.NGStepBBW.card_coker_endo f2 (df ▸ hf1)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[i1, i2, c1, c2, df]`. Rewrite using `[i1, c1]`. Conclude with `card_quot_ne_zero hf1`.
-/
theorem core' (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (τ : Matrix (Fin n) (Fin n) k →ₗ[k] k)
    (hsym : ∀ x ∈ Bz Z, ∀ y ∈ Bz Z, τ (x * y) = τ (y * x))
    (hnd : ∀ x ∈ Bz Z, (∀ y ∈ Bz Z, τ (x * y) = 0) → x = 0) (g : GL (Fin n) k)
    (hg : g ∈ Gz Z) : ∃ c : ℕ, ∀ r ≥ c, ((Lat Z r).map (conjA g⁻¹)).relIndex (Lat Z 0) = (Lat Z r).relIndex (Lat Z 0) ∧
      (Lat Z r).relIndex (Lat Z 0) ≠ 0 := by
  obtain ⟨c, -, hc⟩ := exists_shift Z g hg
  refine ⟨c, fun r hr => ?_⟩
  have hg' : g⁻¹ ∈ Gz Z := (GzS Z).inv_mem hg
  have hL : Lat Z r = (Lat Z 0).map (smulA (pi k ^ r)) := by simpa using Lat_add Z r 0
  have hmem : ∀ y ∈ Lat Z 0, pi k ^ r • conjA g⁻¹ y ∈ Lat Z 0 := by
    intro y hy
    have h1 : smulA (pi k ^ r) y ∈ Lat Z ((r - c) + c) := by
      rw [show r - c + c = r by omega, hL]; exact ⟨y, hy, rfl⟩
    have h2 := (hc _ _ h1).2
    rw [conjA_smulA] at h2
    exact Lat_anti Z (Nat.zero_le _) h2
  let ϖ : 𝒪[k] := GLnLocal.uniformizer k
  have hϖ0 : ϖ ≠ 0 := (GLnLocal.irreducible_uniformizer k).ne_zero
  have hϖk : ((ϖ ^ r : 𝒪[k]) : k) = pi k ^ r := by simp [ϖ]
  let f1 : LatO Z →ₗ[𝒪[k]] LatO Z := (ϖ ^ r) • LinearMap.id
  let f2 : LatO Z →ₗ[𝒪[k]] LatO Z :=
    { toFun := fun y => ⟨pi k ^ r • conjA g⁻¹ y, hmem y y.2⟩
      map_add' := fun x y => Subtype.ext (by simp [mul_add, add_mul, smul_add])
      map_smul' := fun a y => Subtype.ext (by
        change pi k ^ r • conjA g⁻¹ ((a : k) • (y : Matrix (Fin n) (Fin n) k)) =
          (a : k) • (pi k ^ r • conjA g⁻¹ (y : Matrix (Fin n) (Fin n) k))
        rw [← smulA_apply (a : k), conjA_smulA, smulA_apply, smul_comm]) }
  let B := Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))
  let F1 : B →ₗ[k] B := (pi k ^ r) • LinearMap.id
  let F2 : B →ₗ[k] B := (pi k ^ r) • conjB Z g⁻¹ hg'
  have t1 := det_transfer Z F1 f1 (fun x => by
    change pi k ^ r • (x : Matrix (Fin n) (Fin n) k) = ((ϖ ^ r : 𝒪[k]) : k) • (x : Matrix (Fin n) (Fin n) k)
    rw [hϖk])
  have t2 := det_transfer Z F2 f2 (fun x => rfl)
  have dF : LinearMap.det F1 = LinearMap.det F2 := by
    simp only [F1, F2, LinearMap.det_smul, LinearMap.det_id,
      det_conjB Z τ hsym hnd g⁻¹ hg']
  have df : LinearMap.det f1 = LinearMap.det f2 := Subtype.val_injective (t1.trans (dF.trans t2.symm))
  have hf1 : LinearMap.det f1 ≠ 0 := by
    simp only [f1, LinearMap.det_smul, LinearMap.det_id, mul_one]
    exact pow_ne_zero _ (pow_ne_zero _ hϖ0)
  have i1 : (Lat Z r).relIndex (Lat Z 0) = Nat.card (LatO Z ⧸ LinearMap.range f1) := by
    refine relIndex_eq_card Z _ f1 fun x => ?_
    rw [hL, AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨y, hy⟩, ?_⟩
      change ((ϖ ^ r : 𝒪[k]) : k) • y = smulA (pi k ^ r) y
      rw [hϖk]; rfl
    · rintro ⟨y, rfl⟩
      refine ⟨y, y.2, ?_⟩
      change smulA (pi k ^ r) (y : Matrix (Fin n) (Fin n) k) = ((ϖ ^ r : 𝒪[k]) : k) • (y : Matrix (Fin n) (Fin n) k)
      rw [hϖk]; rfl
  have i2 : ((Lat Z r).map (conjA g⁻¹)).relIndex (Lat Z 0) = Nat.card (LatO Z ⧸ LinearMap.range f2) := by
    refine relIndex_eq_card Z _ f2 fun x => ?_
    rw [hL, AddSubgroup.map_map, AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨y, hy⟩, ?_⟩
      change pi k ^ r • conjA g⁻¹ y = conjA g⁻¹ (smulA (pi k ^ r) y)
      rw [conjA_smulA]; rfl
    · rintro ⟨y, rfl⟩
      refine ⟨y, y.2, ?_⟩
      change conjA g⁻¹ (smulA (pi k ^ r) (y : Matrix (Fin n) (Fin n) k)) = pi k ^ r • conjA g⁻¹ (y : Matrix (Fin n) (Fin n) k)
      rw [conjA_smulA]; rfl
  have c1 := PI.NGStepBBW.card_coker_endo f1 hf1
  have c2 := PI.NGStepBBW.card_coker_endo f2 (df ▸ hf1)
  refine ⟨?_, ?_⟩
  · rw [i1, i2, c1, c2, df]
  · rw [i1, c1]
    exact card_quot_ne_zero hf1

/- English proof (translation)
Introduce `n Z hZ g hg`. Take `⟨τ, hsym, hnd, -⟩` from `hT n Z hZ`. Take `⟨c0, hc01, hc0⟩` from `exists_shift Z g hg`. Take `⟨c1, hc1⟩` from `core' Z τ hsym hnd g hg`. Use `⟨c0 + c1, fun m hm m' hm' => ?_⟩` and prove the remaining obligations.

Establish `h1m : 1 ≤ m` using `by omega`. Take `⟨r, rfl⟩ : ∃ r, m' = m + r` from `⟨m' - m, by omega⟩`. Establish `hr : c1 ≤ r` using `by omega`. Use `⟨Lc_le Z g hg c0 hc0 h1m (by omega), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[relIndex_Lc_conj Z g hg c0 hc0 h1m (by omega) (by omega), relIndex_Lc Z h1m (by omega), Bi.relIndex_lat_conj, Bi.relIndex_lat]`.

Conclude with `(hc1 r hr).1`. Rewrite using `[relIndex_Lc Z h1m (by omega), Bi.relIndex_lat]`. Conclude with `(hc1 r hr).2`.
-/
theorem indexSym' (hT : TraceForm k) : IndexSym (k := k) := by
  intro n Z hZ g hg
  obtain ⟨τ, hsym, hnd, -⟩ := hT n Z hZ
  obtain ⟨c0, hc01, hc0⟩ := exists_shift Z g hg
  obtain ⟨c1, hc1⟩ := core' Z τ hsym hnd g hg
  refine ⟨c0 + c1, fun m hm m' hm' => ?_⟩
  have h1m : 1 ≤ m := by omega
  obtain ⟨r, rfl⟩ : ∃ r, m' = m + r := ⟨m' - m, by omega⟩
  have hr : c1 ≤ r := by omega
  refine ⟨Lc_le Z g hg c0 hc0 h1m (by omega), ?_, ?_⟩
  · rw [relIndex_Lc_conj Z g hg c0 hc0 h1m (by omega) (by omega), relIndex_Lc Z h1m (by omega),
      Bi.relIndex_lat_conj, Bi.relIndex_lat]
    exact (hc1 r hr).1
  · rw [relIndex_Lc Z h1m (by omega), Bi.relIndex_lat]
    exact (hc1 r hr).2

/- English proof (translation)
Introduce `hT` and use `PositivityTheory.RgUd.T.Desc.SLF.Un2.unimod_of_indexSym (indexSym' hT)`.
-/
theorem unimod (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    TraceForm k → PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k) := fun hT =>
  PositivityTheory.RgUd.T.Desc.SLF.Un2.unimod_of_indexSym (indexSym' hT)

end PositivityTheory.RgUd.TP.Loc.Uni

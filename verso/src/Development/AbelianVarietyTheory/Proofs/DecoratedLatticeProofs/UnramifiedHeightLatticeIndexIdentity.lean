import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationDivZpowOrd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexScaledMaxIdealStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section
namespace GlobalTheory.HeckeLatIndex

/- English proof (translation)
Introduce `k _ _ _ _ D _ _ κ hκ v hv i`. Establish `hent : ∀ j, valuation k (κ.1 i j) ≤ 1` using `fun j => (Valuation.mem_integer_iff _ _).1 (((GlobalTheory.SplitFlip.mem_KO_iff κ).1 hκ).1 i j)`. Rewrite using `[Matrix.mulVec, dotProduct]`. Conclude with `Valuation.map_sum_lt _ one_ne_zero fun j _ => by`. Rewrite using `[map_mul]`.

Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (hent j)) (hv j)`.
-/
theorem ko_pres : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (κ : GL D k), κ ∈ KO k D → ∀ v : D → k, (∀ i, valuation k (v i) < 1) → ∀ i, valuation k (κ.1.mulVec v i) < 1 := by
  intro k _ _ _ _ D _ _ κ hκ v hv i
  have hent : ∀ j, valuation k (κ.1 i j) ≤ 1 := fun j =>
    (Valuation.mem_integer_iff _ _).1 (((GlobalTheory.SplitFlip.mem_KO_iff κ).1 hκ).1 i j)
  rw [Matrix.mulVec, dotProduct]
  exact Valuation.map_sum_lt _ one_ne_zero fun j _ => by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hent j)) (hv j)

/- English proof (translation)
The claim follows from `GlobalTheory.T.relIndex_inf_mul_relIndex_inf_eq_resCard_pow`.
-/
theorem line_index : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (c : ℤ) (L P : AddSubgroup k), (∀ x, x ∈ L ↔ valuation k x < 1) → (∀ x, x ∈ P ↔ valuation k (((ϖ ^ c : kˣ) : k) * x) < 1) → (P ⊓ L).relIndex P * (P ⊓ L).relIndex L = resCard k ^ c.natAbs := GlobalTheory.T.relIndex_inf_mul_relIndex_inf_eq_resCard_pow

/- English proof (translation)
Set `g : (∀ i, B i) →+ (AddSubgroup.pi Set.univ B)` to `{ toFun := fun v => ⟨fun i => (v i : G), fun i _ => (v i).2⟩ map_zero' := rfl map_add' := fun _ _ => rfl }`. Establish `hg : Function.Surjective g` using `fun x => ⟨fun i => ⟨x.1 i, x.2 i (Set.mem_univ i)⟩, rfl⟩`. Establish `hc : ((AddSubgroup.pi Set.univ A).addSubgroupOf (AddSubgroup.pi Set.univ B)).comap g = AddSubgroup.pi Set.univ fun i => (A i).addSubgroupOf (B i)`. Use extensionality with `v`. Simplify using `[g, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]`.

Rewrite using `[AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hg, hc]`. Repeatedly rewrite using `[AddSubgroup.relIndex, AddSubgroup.index, ← Nat.card_pi]`. Use `Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)` and prove the remaining obligations. Rewrite using `[QuotientAddGroup.leftRel_pi]`.
-/
theorem relIndex_pi_univ {ι G : Type} [Fintype ι] [AddCommGroup G] (A B : ι → AddSubgroup G) :
    (AddSubgroup.pi Set.univ A).relIndex (AddSubgroup.pi Set.univ B) = ∏ i, (A i).relIndex (B i) := by
  let g : (∀ i, B i) →+ (AddSubgroup.pi Set.univ B) :=
    { toFun := fun v => ⟨fun i => (v i : G), fun i _ => (v i).2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hg : Function.Surjective g := fun x => ⟨fun i => ⟨x.1 i, x.2 i (Set.mem_univ i)⟩, rfl⟩
  have hc : ((AddSubgroup.pi Set.univ A).addSubgroupOf (AddSubgroup.pi Set.univ B)).comap g =
      AddSubgroup.pi Set.univ fun i => (A i).addSubgroupOf (B i) := by
    ext v
    simp [g, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hg, hc]
  simp_rw [AddSubgroup.relIndex, AddSubgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientAddGroup.leftRel_pi]

/- English proof (translation)
Introduce `k _ _ _ _ D _ _ ϖ hϖ e L P hL hP`. Set `L₀ : AddSubgroup k` to `(valuation k).ltAddSubgroup 1`. Establish `hL₀ : ∀ x, x ∈ L₀ ↔ valuation k x < 1` using `fun x => Iff.rfl`. Set `Pi : D → AddSubgroup k` to `fun i => L₀.comap (AddMonoidHom.mulLeft ((ϖ ^ e i : kˣ) : k))`. Establish `hPi : ∀ i x, x ∈ Pi i ↔ valuation k (((ϖ ^ e i : kˣ) : k) * x) < 1` using `fun i x => Iff.rfl`.

Establish `eL : L = AddSubgroup.pi Set.univ fun _ => L₀`. Use extensionality with `v`. Rewrite using `[hL]`. Simplify using `[AddSubgroup.mem_pi, hL₀]`. Establish `eP : P = AddSubgroup.pi Set.univ Pi`.

Use extensionality with `v`. Rewrite using `[hP]`. Simplify using `[AddSubgroup.mem_pi, hPi]`. Establish `eI : P ⊓ L = AddSubgroup.pi Set.univ fun i => Pi i ⊓ L₀`. Use extensionality with `v`.

Rewrite using `[AddSubgroup.mem_inf, eP, eL]`. Simplify using `[AddSubgroup.mem_pi, forall_and]`. Rewrite using `[eI, eP, eL, relIndex_pi_univ, relIndex_pi_univ]`. Establish `h1 : ∀ i, (Pi i ⊓ L₀).relIndex (Pi i) * (Pi i ⊓ L₀).relIndex L₀ = resCard k ^ (e i).natAbs` using `fun i => line_index k ϖ hϖ (e i) L₀ (Pi i) hL₀ (hPi i)`. Rewrite using `[← Nat.cast_mul, ← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_pow_eq_pow_sum]`.

Establish `hs : sumAbs e = ((∑ i, (e i).natAbs : ℕ) : ℤ)`. Unfold `sumAbs`. Use `push_cast`. Simplify using `[Int.natCast_natAbs]`. Rewrite using `[hs, zpow_natCast]`.

Use `push_cast`. Both sides reduce to the same expression.
-/
theorem diag_index : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (e : D → ℤ) (L P : AddSubgroup (D → k)), (∀ v, v ∈ L ↔ ∀ i, valuation k (v i) < 1) → (∀ v, v ∈ P ↔ ∀ i, valuation k (((ϖ ^ e i : kˣ) : k) * v i) < 1) → (((P ⊓ L).relIndex P : ℕ) : ℝ) * (((P ⊓ L).relIndex L : ℕ) : ℝ) = (resCard k : ℝ) ^ (sumAbs e) := by
  intro k _ _ _ _ D _ _ ϖ hϖ e L P hL hP
  let L₀ : AddSubgroup k := (valuation k).ltAddSubgroup 1
  have hL₀ : ∀ x, x ∈ L₀ ↔ valuation k x < 1 := fun x => Iff.rfl
  let Pi : D → AddSubgroup k := fun i => L₀.comap (AddMonoidHom.mulLeft ((ϖ ^ e i : kˣ) : k))
  have hPi : ∀ i x, x ∈ Pi i ↔ valuation k (((ϖ ^ e i : kˣ) : k) * x) < 1 := fun i x => Iff.rfl
  have eL : L = AddSubgroup.pi Set.univ fun _ => L₀ := by
    ext v; rw [hL]; simp [AddSubgroup.mem_pi, hL₀]
  have eP : P = AddSubgroup.pi Set.univ Pi := by
    ext v; rw [hP]; simp [AddSubgroup.mem_pi, hPi]
  have eI : P ⊓ L = AddSubgroup.pi Set.univ fun i => Pi i ⊓ L₀ := by
    ext v; rw [AddSubgroup.mem_inf, eP, eL]; simp [AddSubgroup.mem_pi, forall_and]
  rw [eI, eP, eL, relIndex_pi_univ, relIndex_pi_univ]
  have h1 : ∀ i, (Pi i ⊓ L₀).relIndex (Pi i) * (Pi i ⊓ L₀).relIndex L₀ = resCard k ^ (e i).natAbs :=
    fun i => line_index k ϖ hϖ (e i) L₀ (Pi i) hL₀ (hPi i)
  rw [← Nat.cast_mul, ← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun i _ => h1 i),
    Finset.prod_pow_eq_pow_sum]
  have hs : sumAbs e = ((∑ i, (e i).natAbs : ℕ) : ℤ) := by
    unfold sumAbs; push_cast; simp [Int.natCast_natAbs]
  rw [hs, zpow_natCast]
  push_cast
  rfl

/- English proof (translation)
Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Conclude with `(hS w).1 hw`. Introduce `hv`.

Establish `hgv : g.1.mulVec ((g⁻¹).1.mulVec v) = v`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Use `⟨(g⁻¹).1.mulVec v, (hS _).2 (by rw [hgv]; exact hv), hgv⟩` and prove the remaining obligations.
-/
theorem map_eq_of_preimage {k : Type} [Field k] {D : Type} [Fintype D] [DecidableEq D] (g : GL D k)
    (S T : AddSubgroup (D → k)) (hS : ∀ w, w ∈ S ↔ g.1.mulVec w ∈ T) :
    S.map (Matrix.mulVecLin g.1).toAddMonoidHom = T := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (hS w).1 hw
  · intro hv
    have hgv : g.1.mulVec ((g⁻¹).1.mulVec v) = v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    refine ⟨(g⁻¹).1.mulVec v, (hS _).2 (by rw [hgv]; exact hv), hgv⟩

/- English proof (translation)
Introduce `v w h`. Establish `h' : (g⁻¹).1.mulVec (g.1.mulVec v) = (g⁻¹).1.mulVec (g.1.mulVec w)` using `congrArg _ h`. Simplify `h'` using `[Matrix.mulVec_mulVec, ← Units.val_mul]`.
-/
theorem mulVec_injective {k : Type} [Field k] {D : Type} [Fintype D] [DecidableEq D] (g : GL D k) :
    Function.Injective (Matrix.mulVecLin g.1).toAddMonoidHom := by
  intro v w h
  have h' : (g⁻¹).1.mulVec (g.1.mulVec v) = (g⁻¹).1.mulVec (g.1.mulVec w) := congrArg _ h
  simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using h'

/- English proof (translation)
Rewrite using `[hL, hL]`. Use `⟨ko_pres k D κ hκ w, fun h => ?_⟩` and prove the remaining obligations. Use `ko_pres k D κ⁻¹ (inv_mem hκ) _ h` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Then use the resulting hypothesis.
-/
theorem ko_mem_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {D : Type} [Fintype D] [DecidableEq D] (κ : GL D k) (hκ : κ ∈ KO k D) (L : AddSubgroup (D → k))
    (hL : ∀ v, v ∈ L ↔ ∀ i, valuation k (v i) < 1) (w : D → k) : w ∈ L ↔ κ.1.mulVec w ∈ L := by
  rw [hL, hL]
  refine ⟨ko_pres k D κ hκ w, fun h => ?_⟩
  have := ko_pres k D κ⁻¹ (inv_mem hκ) _ h
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this

/- English proof (translation)
Introduce `k _ _ _ _ D _ _ h κ κ' hκ hκ' L P P' hL hP hP'`. Establish `h1 : ∀ w, w ∈ P' ↔ κ'.1.mulVec w ∈ P` using `fun w => by`. Rewrite using `[hP', hP, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← ko_mem_iff κ hκ L hL]`. Establish `h2 : ∀ w, w ∈ L ↔ κ'.1.mulVec w ∈ L` using `ko_mem_iff κ' hκ' L hL`. Establish `m1` using `map_eq_of_preimage κ' P' P h1`.

Establish `m2` using `map_eq_of_preimage κ' L L h2`. Establish `hinj` using `mulVec_injective κ'`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← AddSubgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.map_inf_eq _ _ _ hinj, m1, m2]`. Rewrite using `[← AddSubgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.map_inf_eq _ _ _ hinj, m1, m2]`.
-/
theorem ko_index : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (h κ κ' : GL D k), κ ∈ KO k D → κ' ∈ KO k D → ∀ (L P P' : AddSubgroup (D → k)), (∀ v, v ∈ L ↔ ∀ i, valuation k (v i) < 1) → (∀ v, v ∈ P ↔ h.1.mulVec v ∈ L) → (∀ v, v ∈ P' ↔ (κ * h * κ').1.mulVec v ∈ L) → (P' ⊓ L).relIndex P' = (P ⊓ L).relIndex P ∧ (P' ⊓ L).relIndex L = (P ⊓ L).relIndex L := by
  intro k _ _ _ _ D _ _ h κ κ' hκ hκ' L P P' hL hP hP'
  have h1 : ∀ w, w ∈ P' ↔ κ'.1.mulVec w ∈ P := fun w => by
    rw [hP', hP, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← ko_mem_iff κ hκ L hL]
  have h2 : ∀ w, w ∈ L ↔ κ'.1.mulVec w ∈ L := ko_mem_iff κ' hκ' L hL
  have m1 := map_eq_of_preimage κ' P' P h1
  have m2 := map_eq_of_preimage κ' L L h2
  have hinj := mulVec_injective κ'
  constructor
  · rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.map_inf_eq _ _ _ hinj, m1, m2]
  · rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.map_inf_eq _ _ _ hinj, m1, m2]

/- English proof (translation)
Introduce `k _ _ _ _ D _ _ ϖ hϖ H hH h L P hL hP`. Establish `hq : (0 : ℝ) < resCard k` using `by exact_mod_cast (show 0 < resCard k by unfold resCard; exact Nat.card_pos)`. Take `⟨x, hx, y, hy, e, rfl⟩` from `GlobalTheory.LocalCartan.cartan_decomposition k D ϖ h hϖ`. Set `t : GL D k` to `torusElt k D ϖ e`. Set `Pt : AddSubgroup (D → k)` to `L.comap (Matrix.mulVecLin t.1).toAddMonoidHom`.

Establish `hPt : ∀ v, v ∈ Pt ↔ t.1.mulVec v ∈ L` using `fun v => Iff.rfl`. Take `⟨e1, e2⟩` from `ko_index k D t x y hx hy L Pt P hL hPt hP`. Establish `hd` using `diag_index k D ϖ hϖ e L Pt hL (fun v => by`. Rewrite using `[hPt, hL]`. Simplify using `[t, torusElt, val_diagT, Matrix.mulVec_diagonal])`.

Establish `hH1 : H (x * t * y) = H t` using `by rw [(hH.1 y hy _).2, (hH.1 x hx _).1]`. Rewrite using `[e1, e2, mul_assoc, hd]`. Express the relevant statement in the definitionally equal form `H (x * t * y) * _ = 1`. Rewrite using `[hH1, hH.2 e, ← zpow_add₀ hq.ne']`. Simplify using the standard rewrite rules.
-/
theorem hgt_mul_index : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ H : GL D k → ℝ, IsHgt ϖ H → ∀ (h : GL D k) (L P : AddSubgroup (D → k)), (∀ v, v ∈ L ↔ ∀ i, valuation k (v i) < 1) → (∀ v, v ∈ P ↔ h.1.mulVec v ∈ L) → H h * (((P ⊓ L).relIndex P : ℕ) : ℝ) * (((P ⊓ L).relIndex L : ℕ) : ℝ) = 1 := by
  intro k _ _ _ _ D _ _ ϖ hϖ H hH h L P hL hP
  have hq : (0 : ℝ) < resCard k := by exact_mod_cast (show 0 < resCard k by unfold resCard; exact Nat.card_pos)
  obtain ⟨x, hx, y, hy, e, rfl⟩ := GlobalTheory.LocalCartan.cartan_decomposition k D ϖ h hϖ
  let t : GL D k := torusElt k D ϖ e
  let Pt : AddSubgroup (D → k) := L.comap (Matrix.mulVecLin t.1).toAddMonoidHom
  have hPt : ∀ v, v ∈ Pt ↔ t.1.mulVec v ∈ L := fun v => Iff.rfl
  obtain ⟨e1, e2⟩ := ko_index k D t x y hx hy L Pt P hL hPt hP
  have hd := diag_index k D ϖ hϖ e L Pt hL (fun v => by
    rw [hPt, hL]
    simp [t, torusElt, val_diagT, Matrix.mulVec_diagonal])
  have hH1 : H (x * t * y) = H t := by rw [(hH.1 y hy _).2, (hH.1 x hx _).1]
  rw [e1, e2, mul_assoc, hd]
  change H (x * t * y) * _ = 1
  rw [hH1, hH.2 e, ← zpow_add₀ hq.ne']
  simp

/- English proof (translation)
Introduce `k _ _ _ _ D _ _ ϖ hϖ H hH m g s hg L Lm large₂ hL hLm hLg`. Establish `hq : (0 : ℝ) < resCard k` using `by exact_mod_cast (show 0 < resCard k by unfold resCard; exact Nat.card_pos)`. Take `⟨κ, hκ, κ', hκ', hgeq⟩` from `hg`. Establish `hgL : ∀ v, v ∈ L → g.1.mulVec v ∈ L`. Introduce `v hv`.

Rewrite using `[hgeq, hL]`. Establish `h1` using `ko_pres k D κ' hκ' v ((hL v).1 hv)`. Establish `h2 : ∀ i, valuation k ((torusElt k D ϖ (indic s)).1.mulVec (κ'.1.mulVec v) i) < 1`. Introduce `i`. Simplify using `only [torusElt, val_diagT, Matrix.mulVec_diagonal, map_mul]`.

Establish `hle : valuation k ((ϖ ^ indic s i : kˣ) : k) ≤ 1`. Unfold `indic`. Use `split_ifs`. Simplify using `only [zpow_one]`. Rewrite using `[hϖ]`.

Conclude with `uniformizer_lt_one.le`. Simplify using the standard rewrite rules. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' hle) (h1 i)`. Establish `h3` using `ko_pres k D κ hκ _ h2`. Simplify `h3` using `[Matrix.mulVec_mulVec, Units.val_mul, Matrix.mul_assoc]`.

Establish `hLgL : large₂ ≤ L`. Introduce `v hv`. Establish `: g.1.mulVec ((g⁻¹).1.mulVec v) = v`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Rewrite using `[← this]`.

Conclude with `hgL _ ((hLg v).1 hv)`. Use `set φ := (Matrix.mulVecLin g.1).toAddMonoidHom with hφ`. Establish `hinj : Function.Injective φ` using `mulVec_injective g`. Set `P₁ : AddSubgroup (D → k)` to `L.comap (Matrix.mulVecLin (m * g).1).toAddMonoidHom`. Set `P₂ : AddSubgroup (D → k)` to `L.comap (Matrix.mulVecLin g.1).toAddMonoidHom`.

Establish `hP₁ : ∀ v, v ∈ P₁ ↔ (m * g).1.mulVec v ∈ L` using `fun v => Iff.rfl`. Establish `hP₂ : ∀ v, v ∈ P₂ ↔ g.1.mulVec v ∈ L` using `fun v => Iff.rfl`. Establish `mP₁ : P₁.map φ = Lm` using `map_eq_of_preimage g P₁ Lm fun w => by`. Rewrite using `[hP₁, hLm, Units.val_mul, Matrix.mulVec_mulVec]`. Establish `mL : L.map φ = large₂`.

Use `map_eq_of_preimage g L large₂ fun w => ?_` and prove the remaining obligations. Rewrite using `[hLg, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Establish `mP₂ : P₂.map φ = L` using `map_eq_of_preimage g P₂ L hP₂`. Establish `k₁` using `hgt_mul_index k D ϖ hϖ H hH m L Lm hL hLm`. Establish `k₂` using `hgt_mul_index k D ϖ hϖ H hH (m * g) L P₁ hL hP₁`.

Establish `k₃` using `hgt_mul_index k D ϖ hϖ H hH g L P₂ hL hP₂`. Rewrite `k₂` using `[← AddSubgroup.relIndex_map_map_of_injective (f := φ) _ _ hinj, ← AddSubgroup.relIndex_map_map_of_injective (f := φ) (P₁ ⊓ L) L hinj, AddSubgroup.map_inf_eq _ _ _ hinj, mP₁, mL]`. Establish `hLP₂ : L ≤ P₂` using `fun v hv => hgL v hv`. Rewrite `k₃` using `[inf_eq_right.2 hLP₂, AddSubgroup.relIndex_self, ← AddSubgroup.relIndex_map_map_of_injective (f := φ) _ _ hinj, mL, mP₂]`. Establish `hHg : H g = (resCard k : ℝ) ^ (-(s.card : ℤ))`.

Rewrite using `[hgeq, (hH.1 κ' hκ' _).2, (hH.1 κ hκ _).1, hH.2]`. Use `congr 2`. Unfold `sumAbs indic`. Apply the tactic sequence `rw [Finset.sum_congr rfl (fun i _ => show |(if i ∈ s then (1:ℤ) else 0)| = if i ∈ s then 1 else 0 by split_ifs <;> simp)]`. Simplify using the standard rewrite rules.

Rewrite `k₃` using `[hHg]`. Establish `t₁` using `AddSubgroup.relIndex_mul_relIndex (Lm ⊓ large₂) (Lm ⊓ L) Lm (inf_le_inf_left _ hLgL) inf_le_left`. Establish `t₂` using `AddSubgroup.relIndex_mul_relIndex (Lm ⊓ large₂) large₂ L inf_le_right hLgL`. Establish `t₃` using `AddSubgroup.relIndex_mul_relIndex (Lm ⊓ large₂) (Lm ⊓ L) L (inf_le_inf_left _ hLgL) inf_le_right`. Establish `hQ : (large₂.relIndex L : ℝ) = (resCard k : ℝ) ^ s.card`.

Establish `hne : (resCard k : ℝ) ^ (-(s.card : ℤ)) ≠ 0` using `by positivity`. Establish `hne' : (resCard k : ℝ) ^ s.card ≠ 0` using `by positivity`. Rewrite `k₃` using `[_root_.zpow_neg, zpow_natCast, Nat.cast_one, mul_one, inv_mul_eq_one₀ hne']`. Conclude with `k₃.symm`. Establish `e1 : (((Lm ⊓ large₂).relIndex Lm : ℕ) : ℝ) = ((Lm ⊓ large₂).relIndex (Lm ⊓ L) : ℕ) * ((Lm ⊓ L).relIndex Lm : ℕ)`.

Rewrite using `[← t₁]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (resCard k : ℝ) ^ s.card * (((Lm ⊓ large₂).relIndex large₂ : ℕ) : ℝ) = ((Lm ⊓ large₂).relIndex (Lm ⊓ L) : ℕ) * ((Lm ⊓ L).relIndex L : ℕ)`. Rewrite using `[← hQ]`.

Use `congrArg (fun n : ℕ => (n : ℝ)) (t₂.trans t₃.symm)` as an intermediate fact. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Take the linear combination `(-(((Lm ⊓ large₂).relIndex (Lm ⊓ L) : ℕ) : ℝ) ^ 2 * H (m * g)) * k₁ + ((resCard k : ℝ) ^ s.card * H m) * k₂ + (-(H m * H (m * g) * (resCard k : ℝ) ^ s.card * (((Lm ⊓ large₂).relIndex large₂ : ℕ) : ℝ))) * e1 + (-(H m * H (m * g) * (((Lm ⊓ large₂).relIndex (Lm ⊓ L) : ℕ) : ℝ) * (((L …`.
-/
theorem index_identity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ H : GL D k → ℝ, IsHgt ϖ H → ∀ (m g : GL D k) (s : Finset D), (∃ κ ∈ KO k D, ∃ κ' ∈ KO k D, g = κ * torusElt k D ϖ (indic s) * κ') → ∀ (L Lm large₂ : AddSubgroup (D → k)), (∀ v, v ∈ L ↔ ∀ i, valuation k (v i) < 1) → (∀ v, v ∈ Lm ↔ m.1.mulVec v ∈ L) → (∀ v, v ∈ large₂ ↔ (g⁻¹).1.mulVec v ∈ L) → (((Lm ⊓ large₂).relIndex (Lm ⊓ L) : ℕ) : ℝ) ^ 2 * H (m * g) = (resCard k : ℝ) ^ s.card * H m := by
  intro k _ _ _ _ D _ _ ϖ hϖ H hH m g s hg L Lm large₂ hL hLm hLg
  have hq : (0 : ℝ) < resCard k := by exact_mod_cast (show 0 < resCard k by unfold resCard; exact Nat.card_pos)
  obtain ⟨κ, hκ, κ', hκ', hgeq⟩ := hg

  have hgL : ∀ v, v ∈ L → g.1.mulVec v ∈ L := by
    intro v hv
    rw [hgeq, hL]
    have h1 := ko_pres k D κ' hκ' v ((hL v).1 hv)
    have h2 : ∀ i, valuation k ((torusElt k D ϖ (indic s)).1.mulVec (κ'.1.mulVec v) i) < 1 := by
      intro i
      simp only [torusElt, val_diagT, Matrix.mulVec_diagonal, map_mul]
      have hle : valuation k ((ϖ ^ indic s i : kˣ) : k) ≤ 1 := by
        unfold indic
        split_ifs
        · simp only [zpow_one]
          rw [hϖ]
          exact uniformizer_lt_one.le
        · simp
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hle) (h1 i)
    have h3 := ko_pres k D κ hκ _ h2
    simpa [Matrix.mulVec_mulVec, Units.val_mul, Matrix.mul_assoc] using h3
  have hLgL : large₂ ≤ L := by
    intro v hv
    have : g.1.mulVec ((g⁻¹).1.mulVec v) = v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [← this]
    exact hgL _ ((hLg v).1 hv)
  set φ := (Matrix.mulVecLin g.1).toAddMonoidHom with hφ
  have hinj : Function.Injective φ := mulVec_injective g

  let P₁ : AddSubgroup (D → k) := L.comap (Matrix.mulVecLin (m * g).1).toAddMonoidHom
  let P₂ : AddSubgroup (D → k) := L.comap (Matrix.mulVecLin g.1).toAddMonoidHom
  have hP₁ : ∀ v, v ∈ P₁ ↔ (m * g).1.mulVec v ∈ L := fun v => Iff.rfl
  have hP₂ : ∀ v, v ∈ P₂ ↔ g.1.mulVec v ∈ L := fun v => Iff.rfl
  have mP₁ : P₁.map φ = Lm := map_eq_of_preimage g P₁ Lm fun w => by
    rw [hP₁, hLm, Units.val_mul, Matrix.mulVec_mulVec]
  have mL : L.map φ = large₂ := by
    refine map_eq_of_preimage g L large₂ fun w => ?_
    rw [hLg, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have mP₂ : P₂.map φ = L := map_eq_of_preimage g P₂ L hP₂
  have k₁ := hgt_mul_index k D ϖ hϖ H hH m L Lm hL hLm
  have k₂ := hgt_mul_index k D ϖ hϖ H hH (m * g) L P₁ hL hP₁
  have k₃ := hgt_mul_index k D ϖ hϖ H hH g L P₂ hL hP₂
  rw [← AddSubgroup.relIndex_map_map_of_injective (f := φ) _ _ hinj,
    ← AddSubgroup.relIndex_map_map_of_injective (f := φ) (P₁ ⊓ L) L hinj,
    AddSubgroup.map_inf_eq _ _ _ hinj, mP₁, mL] at k₂
  have hLP₂ : L ≤ P₂ := fun v hv => hgL v hv
  rw [inf_eq_right.2 hLP₂, AddSubgroup.relIndex_self, ← AddSubgroup.relIndex_map_map_of_injective (f := φ) _ _ hinj,
    mL, mP₂] at k₃
  have hHg : H g = (resCard k : ℝ) ^ (-(s.card : ℤ)) := by
    rw [hgeq, (hH.1 κ' hκ' _).2, (hH.1 κ hκ _).1, hH.2]
    congr 2
    unfold sumAbs indic
    rw [Finset.sum_congr rfl (fun i _ => show |(if i ∈ s then (1:ℤ) else 0)| = if i ∈ s then 1 else 0 by split_ifs <;> simp)]
    simp
  rw [hHg] at k₃

  have t₁ := AddSubgroup.relIndex_mul_relIndex (Lm ⊓ large₂) (Lm ⊓ L) Lm (inf_le_inf_left _ hLgL) inf_le_left
  have t₂ := AddSubgroup.relIndex_mul_relIndex (Lm ⊓ large₂) large₂ L inf_le_right hLgL
  have t₃ := AddSubgroup.relIndex_mul_relIndex (Lm ⊓ large₂) (Lm ⊓ L) L (inf_le_inf_left _ hLgL) inf_le_right
  have hQ : (large₂.relIndex L : ℝ) = (resCard k : ℝ) ^ s.card := by
    have hne : (resCard k : ℝ) ^ (-(s.card : ℤ)) ≠ 0 := by positivity
    have hne' : (resCard k : ℝ) ^ s.card ≠ 0 := by positivity
    rw [_root_.zpow_neg, zpow_natCast, Nat.cast_one, mul_one, inv_mul_eq_one₀ hne'] at k₃
    exact k₃.symm
  have e1 : (((Lm ⊓ large₂).relIndex Lm : ℕ) : ℝ) = ((Lm ⊓ large₂).relIndex (Lm ⊓ L) : ℕ) * ((Lm ⊓ L).relIndex Lm : ℕ) := by
    rw [← t₁]; push_cast; ring
  have e2 : (resCard k : ℝ) ^ s.card * (((Lm ⊓ large₂).relIndex large₂ : ℕ) : ℝ) = ((Lm ⊓ large₂).relIndex (Lm ⊓ L) : ℕ) * ((Lm ⊓ L).relIndex L : ℕ) := by
    rw [← hQ]
    have := congrArg (fun n : ℕ => (n : ℝ)) (t₂.trans t₃.symm)
    push_cast at this
    linarith
  linear_combination (-(((Lm ⊓ large₂).relIndex (Lm ⊓ L) : ℕ) : ℝ) ^ 2 * H (m * g)) * k₁ + ((resCard k : ℝ) ^ s.card * H m) * k₂
    + (-(H m * H (m * g) * (resCard k : ℝ) ^ s.card * (((Lm ⊓ large₂).relIndex large₂ : ℕ) : ℝ))) * e1
    + (-(H m * H (m * g) * (((Lm ⊓ large₂).relIndex (Lm ⊓ L) : ℕ) : ℝ) * (((Lm ⊓ L).relIndex Lm : ℕ) : ℝ))) * e2

end GlobalTheory.HeckeLatIndex

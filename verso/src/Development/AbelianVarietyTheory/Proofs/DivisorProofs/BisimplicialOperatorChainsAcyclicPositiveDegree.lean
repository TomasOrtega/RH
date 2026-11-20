import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwOCommD
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ

noncomputable section
namespace GlobalTheory.EZ.Acyc
open GlobalTheory.EZ.AWChain

def cone {a p : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk a) :
    SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk a :=
  SimplexCategory.mkHom ⟨fun j => Fin.cases 0 (fun i => α.toOrderHom i) j, by
    intro i j h
    induction i using Fin.cases with
    | zero => exact Fin.zero_le _
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd h (by simp [Fin.le_def])
      | succ j => exact α.toOrderHom.monotone (Fin.succ_le_succ_iff.mp h)⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cone_zero {a p : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk a) :
    (cone α).toOrderHom 0 = 0 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cone_succ {a p : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk a) (j : Fin (p + 1)) :
    (cone α).toOrderHom j.succ = α.toOrderHom j := rfl

abbrev Ix (a b p q : ℕ) : Type :=
  ((op (SimplexCategory.mk a), op (SimplexCategory.mk b)) : SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) ⟶
    (op (SimplexCategory.mk p), op (SimplexCategory.mk q))

def c1 {a b p q : ℕ} (g : Ix a b p q) : Ix a b (p + 1) q := ((cone g.1.unop).op, g.2)

def c2 {a b p q : ℕ} (g : Ix a b p q) : Ix a b 0 (q + 1) := ((idc a 0).op, (cone g.2.unop).op)

def H1 {a b p q : ℕ} : (bo a b ⟶ bo p q) →+ (bo a b ⟶ bo (p + 1) q) :=
  Finsupp.mapDomain.addMonoidHom (c1 (a := a) (b := b) (p := p) (q := q))

def H2 {a b p q : ℕ} : (bo a b ⟶ bo p q) →+ (bo a b ⟶ bo 0 (q + 1)) :=
  Finsupp.mapDomain.addMonoidHom (c2 (a := a) (b := b) (p := p) (q := q))

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Finsupp.mapDomain c1 (Finsupp.single ((α.op, β.op) : Ix a b p q) (1 : ℤ)) = Finsupp.single (((cone α).op, β.op) : Ix a b (p + 1) q) (1 : ℤ)`. Rewrite using `[Finsupp.mapDomain_single]`. Both sides reduce to the same expression.
-/
theorem bisimplicialChainConeFirstIndex_operatorOfSimplexMaps {a b p q : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk a)
    (β : SimplexCategory.mk q ⟶ SimplexCategory.mk b) : H1 (bop α β) = bop (cone α) β := by
  change Finsupp.mapDomain c1 (Finsupp.single ((α.op, β.op) : Ix a b p q) (1 : ℤ)) =
    Finsupp.single (((cone α).op, β.op) : Ix a b (p + 1) q) (1 : ℤ)
  rw [Finsupp.mapDomain_single]
  rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Finsupp.mapDomain c2 (Finsupp.single ((α.op, β.op) : Ix a b p q) (1 : ℤ)) = Finsupp.single (((idc a 0).op, (cone β).op) : Ix a b 0 (q + 1)) (1 : ℤ)`. Rewrite using `[Finsupp.mapDomain_single]`. Both sides reduce to the same expression.
-/
theorem bisimplicialChainConeSecondIndex_operatorOfSimplexMaps {a b p q : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk a)
    (β : SimplexCategory.mk q ⟶ SimplexCategory.mk b) : H2 (bop α β) = bop (idc a 0) (cone β) := by
  change Finsupp.mapDomain c2 (Finsupp.single ((α.op, β.op) : Ix a b p q) (1 : ℤ)) =
    Finsupp.single (((idc a 0).op, (cone β).op) : Ix a b 0 (q + 1)) (1 : ℤ)
  rw [Finsupp.mapDomain_single]
  rfl

/- English proof (translation)
Proceed by induction on `f using Finsupp.induction_linear with`. Consider the case `zero => exact h0`. Consider the case `add f g hf hg => exact hadd _ _ hf hg`. Consider the case `single g r`. Establish `e : (Finsupp.single g r : bo a b ⟶ bo p q) = r • bop g.1.unop g.2.unop`.

Express the relevant statement in the definitionally equal form `Finsupp.single g r = r • Finsupp.single (g : Ix a b p q) (1 : ℤ)`. Rewrite using `[Finsupp.smul_single_one]`. Rewrite using `[e]`. Conclude with `hsm _ _ (hb _ _)`.
-/
theorem hom_induct {a b p q : ℕ} (P : (bo a b ⟶ bo p q) → Prop) (h0 : P 0)
    (hadd : ∀ f g, P f → P g → P (f + g)) (hsm : ∀ (r : ℤ) f, P f → P (r • f))
    (hb : ∀ α β, P (bop α β)) (f : bo a b ⟶ bo p q) : P f := by
  induction f using Finsupp.induction_linear with
  | zero => exact h0
  | add f g hf hg => exact hadd _ _ hf hg
  | single g r =>
    have e : (Finsupp.single g r : bo a b ⟶ bo p q) = r • bop g.1.unop g.2.unop := by
      change Finsupp.single g r = r • Finsupp.single (g : Ix a b p q) (1 : ℤ)
      rw [Finsupp.smul_single_one]
    rw [e]
    exact hsm _ _ (hb _ _)

/- English proof (translation)
Apply `hom_ext'` to reduce the goal to its premises. Introduce `j`. Establish `hj` using `j.isLt`. Rewrite using `[idc_apply]`. Express the relevant statement in the definitionally equal form `min n (j : ℕ) = j`.

Use linear arithmetic over natural numbers and integers.
-/
theorem idc_self' (n : ℕ) : idc n n = 𝟙 _ := by
  apply hom_ext'; intro j; have hj := j.isLt
  rw [idc_apply]; change min n (j : ℕ) = j; omega

/- English proof (translation)
Apply the tactic sequence `unfold faceFun; split_ifs <;> omega`.
-/
theorem faceFun_succ (i j : ℕ) : faceFun (i + 1) (j + 1) = faceFun i j + 1 := by
  unfold faceFun; split_ifs <;> omega

/- English proof (translation)
Apply `hom_ext'` to reduce the goal to its premises. Introduce `j`. Rewrite using `[comp_apply']`. Establish `: (fc (p + 1) p 0).toOrderHom j = j.succ`. Apply `Fin.ext` to reduce the goal to its premises.

Rewrite using `[fc_apply, faceFun_ge (Nat.zero_le _)]`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite using `[this, cone_succ]`.
-/
theorem simplexClampedFaceHom_zero_comp_simplexConeMap {a p : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk a) :
    fc (p + 1) p 0 ≫ cone α = α := by
  apply hom_ext'; intro j
  rw [comp_apply']
  have : (fc (p + 1) p 0).toOrderHom j = j.succ := by
    apply Fin.ext; rw [fc_apply, faceFun_ge (Nat.zero_le _)]; simp; omega
  rw [this, cone_succ]

/- English proof (translation)
Apply `hom_ext'` to reduce the goal to its premises. Introduce `j`. Rewrite using `[comp_apply']`. Proceed by induction on `j using Fin.cases with`. Consider the case `zero`.

Establish `: (fc (p + 1 + 1) (p + 1) (i + 1)).toOrderHom 0 = 0`. Apply `Fin.ext; rw [fc_apply, faceFun_lt (by simp)]; simp` to reduce the goal to its premises. Rewrite using `[this, cone_zero, cone_zero]`. Consider the case `succ j`. Establish `hj` using `j.isLt`.

Establish `: (fc (p + 1 + 1) (p + 1) (i + 1)).toOrderHom j.succ = ((fc (p + 1) p i).toOrderHom j).succ`. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[Fin.val_succ, fc_apply, fc_apply, Fin.val_succ, faceFun_succ]`. Apply the tactic sequence `have : faceFun i j ≤ j + 1 := by unfold faceFun; split_ifs <;> omega`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[this, cone_succ, cone_succ, comp_apply']`.
-/
theorem faceSucc_cone {a p : ℕ} (α : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk a) (i : ℕ) :
    fc (p + 1 + 1) (p + 1) (i + 1) ≫ cone α = cone (fc (p + 1) p i ≫ α) := by
  apply hom_ext'; intro j
  rw [comp_apply']
  induction j using Fin.cases with
  | zero =>
    have : (fc (p + 1 + 1) (p + 1) (i + 1)).toOrderHom 0 = 0 := by
      apply Fin.ext; rw [fc_apply, faceFun_lt (by simp)]; simp
    rw [this, cone_zero, cone_zero]
  | succ j =>
    have hj := j.isLt
    have : (fc (p + 1 + 1) (p + 1) (i + 1)).toOrderHom j.succ = ((fc (p + 1) p i).toOrderHom j).succ := by
      apply Fin.ext
      rw [Fin.val_succ, fc_apply, fc_apply, Fin.val_succ, faceFun_succ]
      have : faceFun i j ≤ j + 1 := by unfold faceFun; split_ifs <;> omega
      omega
    rw [this, cone_succ, cone_succ, comp_apply']

/- English proof (translation)
Apply `hom_ext'` to reduce the goal to its premises. Introduce `j`. Establish `hj : (j : ℕ) = 0` using `by have := j.isLt; omega`. Establish `e : j = 0` using `Fin.ext hj`. Substitute `e` using the available equality.

Rewrite using `[comp_apply']`. Establish `: (fc 1 0 1).toOrderHom 0 = 0`. Apply `Fin.ext; rw [fc_apply, faceFun_lt (by simp)]; simp` to reduce the goal to its premises. Rewrite using `[this, cone_zero, idc_apply]`. Simplify using the standard rewrite rules.
-/
theorem simplexClampedFaceHom_one_comp_simplexConeMap_zero {a : ℕ} (α : SimplexCategory.mk 0 ⟶ SimplexCategory.mk a) :
    fc 1 0 1 ≫ cone α = idc a 0 := by
  apply hom_ext'; intro j
  have hj : (j : ℕ) = 0 := by have := j.isLt; omega
  have e : j = 0 := Fin.ext hj
  subst e
  rw [comp_apply']
  have : (fc 1 0 1).toOrderHom 0 = 0 := by
    apply Fin.ext; rw [fc_apply, faceFun_lt (by simp)]; simp
  rw [this, cone_zero, idc_apply]; simp

/- English proof (translation)
The claim follows from `simplexClampedFaceHom_zero_comp_simplexConeMap (p := 0) α`.
-/
theorem face_zero_cone_identity {a : ℕ} (α : SimplexCategory.mk 0 ⟶ SimplexCategory.mk a) : fc 1 0 0 ≫ cone α = α :=
  simplexClampedFaceHom_zero_comp_simplexConeMap (p := 0) α

/- English proof (translation)
The claim follows from `dT_h 0 q`.
-/
theorem bisimplicialTotalDifferentialOperator_one_zero_eq_sum (q : ℕ) : dT 1 q 0 q = ∑ i ∈ Finset.range (0 + 1 + 1), ((-1 : ℤ) ^ i) • bop (fc 1 0 i) (idc q q) :=
  dT_h 0 q

/- English proof (translation)
Use `hom_induct (fun f => H1 f ≫ dT (p + 1 + 1) q (p + 1) q = f - H1 (f ≫ dT (p + 1) q p q)) ?_ ?_ ?_ ?_ f` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `f g hf hg`. Simplify using `only [map_add, Preadditive.add_comp, Preadditive.add_comp, hf, hg]`. Normalize the expressions using the abelian group laws.

Introduce `r f hf`. Simplify using `only [map_zsmul, Preadditive.zsmul_comp, hf, smul_sub]`. Introduce `α β`. Rewrite using `[bisimplicialChainConeFirstIndex_operatorOfSimplexMaps, dT_h (p + 1) q, dT_h p q]`. Simplify using `only [Preadditive.comp_sum, Preadditive.comp_zsmul, bop_comp, map_sum, map_zsmul, bisimplicialChainConeFirstIndex_operatorOfSimplexMaps]`.

Rewrite using `[Finset.sum_range_succ' _ (p + 1 + 1)]`. Simplify using `only [simplexClampedFaceHom_zero_comp_simplexConeMap, faceSucc_cone, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib, pow_zero, one_smul, idc_self', Category.id_comp]`. Normalize the expressions using the abelian group laws.
-/
theorem idA {a b p q : ℕ} (f : bo a b ⟶ bo (p + 1) q) :
    H1 f ≫ dT (p + 1 + 1) q (p + 1) q = f - H1 (f ≫ dT (p + 1) q p q) := by
  refine hom_induct (fun f => H1 f ≫ dT (p + 1 + 1) q (p + 1) q = f - H1 (f ≫ dT (p + 1) q p q)) ?_ ?_ ?_ ?_ f
  · simp
  · intro f g hf hg; simp only [map_add, Preadditive.add_comp, Preadditive.add_comp, hf, hg]; abel
  · intro r f hf; simp only [map_zsmul, Preadditive.zsmul_comp, hf, smul_sub]
  · intro α β
    rw [bisimplicialChainConeFirstIndex_operatorOfSimplexMaps, dT_h (p + 1) q, dT_h p q]
    simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, bop_comp, map_sum, map_zsmul, bisimplicialChainConeFirstIndex_operatorOfSimplexMaps]
    rw [Finset.sum_range_succ' _ (p + 1 + 1)]
    simp only [simplexClampedFaceHom_zero_comp_simplexConeMap, faceSucc_cone, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib, pow_zero,
      one_smul, idc_self', Category.id_comp]
    abel

/- English proof (translation)
Use `hom_induct (fun f => H1 f ≫ dT (p + 1) (q + 1) (p + 1) q = -H1 (f ≫ dT p (q + 1) p q)) ?_ ?_ ?_ ?_ f` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `f g hf hg`. Simplify using `only [map_add, Preadditive.add_comp, hf, hg, neg_add]`. Introduce `r f hf`.

Simplify using `only [map_zsmul, Preadditive.zsmul_comp, hf, smul_neg]`. Introduce `α β`. Rewrite using `[bisimplicialChainConeFirstIndex_operatorOfSimplexMaps, dT_v (p + 1) q, dT_v p q]`. Simplify using `only [Preadditive.comp_sum, Preadditive.comp_zsmul, Preadditive.comp_neg, bop_comp, map_sum, map_zsmul, bisimplicialChainConeFirstIndex_operatorOfSimplexMaps, idc_self', Category.id_comp, pow_succ, mul_neg_one, neg_smul]`.
-/
theorem idB {a b p q : ℕ} (f : bo a b ⟶ bo p (q + 1)) :
    H1 f ≫ dT (p + 1) (q + 1) (p + 1) q = -H1 (f ≫ dT p (q + 1) p q) := by
  refine hom_induct (fun f => H1 f ≫ dT (p + 1) (q + 1) (p + 1) q = -H1 (f ≫ dT p (q + 1) p q)) ?_ ?_ ?_ ?_ f
  · simp
  · intro f g hf hg; simp only [map_add, Preadditive.add_comp, hf, hg, neg_add]
  · intro r f hf; simp only [map_zsmul, Preadditive.zsmul_comp, hf, smul_neg]
  · intro α β
    rw [bisimplicialChainConeFirstIndex_operatorOfSimplexMaps, dT_v (p + 1) q, dT_v p q]
    simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, Preadditive.comp_neg, bop_comp, map_sum, map_zsmul,
      bisimplicialChainConeFirstIndex_operatorOfSimplexMaps, idc_self', Category.id_comp, pow_succ, mul_neg_one, neg_smul]

/- English proof (translation)
Use `hom_induct (fun f => H1 f ≫ dT 1 (q + 1) 0 (q + 1) + H2 f ≫ dT 0 (q + 1 + 1) 0 (q + 1) = f - H2 (f ≫ dT 0 (q + 1) 0 q)) ?_ ?_ ?_ ?_ f` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `f g hf hg`. Simplify using `only [map_add, Preadditive.add_comp] at hf hg ⊢`. Rewrite using `[show H1 f ≫ dT 1 (q + 1) 0 (q + 1) + H1 g ≫ dT 1 (q + 1) 0 (q + 1) + (H2 f ≫ dT 0 (q + 1 + 1) 0 (q + 1) + H2 g ≫ dT 0 (q + 1 + 1) 0 (q + 1)) = (H1 f ≫ dT 1 (q + 1) 0 (q + 1) + H2 f ≫ dT 0 (q + 1 + 1) 0 (q + 1)) + (H1 g ≫ dT 1 (q + 1) 0 (q + 1) + H2 g ≫ dT 0 (q + 1 + 1) 0 (q + 1) …`.

Normalize the expressions using the abelian group laws. Introduce `r f hf`. Simplify using `only [map_zsmul, Preadditive.zsmul_comp, ← smul_add, hf, smul_sub]`. Introduce `α β`. Rewrite using `[bisimplicialChainConeFirstIndex_operatorOfSimplexMaps, bisimplicialChainConeSecondIndex_operatorOfSimplexMaps, bisimplicialTotalDifferentialOperator_one_zero_eq_sum, dT_v 0 (q + 1), dT_v 0 q]`.

Simplify using `only [Preadditive.comp_sum, Preadditive.comp_zsmul, bop_comp, map_sum, map_zsmul, bisimplicialChainConeSecondIndex_operatorOfSimplexMaps]`. Rewrite using `[Finset.sum_range_succ' _ (q + 1 + 1)]`. Simplify using `only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, face_zero_cone_identity, simplexClampedFaceHom_one_comp_simplexConeMap_zero, simplexClampedFaceHom_zero_comp_simplexConeMap, faceSucc_cone, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib, pow_zero, one_smul, i …`. Normalize the expressions using the abelian group laws.
-/
theorem idC {a b q : ℕ} (f : bo a b ⟶ bo 0 (q + 1)) :
    H1 f ≫ dT 1 (q + 1) 0 (q + 1) + H2 f ≫ dT 0 (q + 1 + 1) 0 (q + 1) = f - H2 (f ≫ dT 0 (q + 1) 0 q) := by
  refine hom_induct (fun f => H1 f ≫ dT 1 (q + 1) 0 (q + 1) + H2 f ≫ dT 0 (q + 1 + 1) 0 (q + 1) =
    f - H2 (f ≫ dT 0 (q + 1) 0 q)) ?_ ?_ ?_ ?_ f
  · simp
  · intro f g hf hg
    simp only [map_add, Preadditive.add_comp] at hf hg ⊢
    rw [show H1 f ≫ dT 1 (q + 1) 0 (q + 1) + H1 g ≫ dT 1 (q + 1) 0 (q + 1) +
      (H2 f ≫ dT 0 (q + 1 + 1) 0 (q + 1) + H2 g ≫ dT 0 (q + 1 + 1) 0 (q + 1)) =
      (H1 f ≫ dT 1 (q + 1) 0 (q + 1) + H2 f ≫ dT 0 (q + 1 + 1) 0 (q + 1)) +
      (H1 g ≫ dT 1 (q + 1) 0 (q + 1) + H2 g ≫ dT 0 (q + 1 + 1) 0 (q + 1)) by abel, hf, hg]
    abel
  · intro r f hf
    simp only [map_zsmul, Preadditive.zsmul_comp, ← smul_add, hf, smul_sub]
  · intro α β
    rw [bisimplicialChainConeFirstIndex_operatorOfSimplexMaps, bisimplicialChainConeSecondIndex_operatorOfSimplexMaps, bisimplicialTotalDifferentialOperator_one_zero_eq_sum, dT_v 0 (q + 1), dT_v 0 q]
    simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, bop_comp, map_sum, map_zsmul, bisimplicialChainConeSecondIndex_operatorOfSimplexMaps]
    rw [Finset.sum_range_succ' _ (q + 1 + 1)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, face_zero_cone_identity, simplexClampedFaceHom_one_comp_simplexConeMap_zero, simplexClampedFaceHom_zero_comp_simplexConeMap,
      faceSucc_cone, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib, pow_zero, one_smul, idc_self',
      Category.id_comp, smul_neg]
    abel

/- English proof (translation)
Use `hom_induct (fun f => H2 (f ≫ dT 1 q 0 q) = 0) ?_ ?_ ?_ ?_ f` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `f g hf hg`. Simplify using `only [map_add, Preadditive.add_comp, hf, hg, add_zero]`. Introduce `r f hf`.

Simplify using `only [map_zsmul, Preadditive.zsmul_comp, hf, smul_zero]`. Introduce `α β`. Rewrite using `[bisimplicialTotalDifferentialOperator_one_zero_eq_sum]`. Simplify using `[Preadditive.comp_sum, Preadditive.comp_zsmul, bop_comp, map_sum, map_zsmul, bisimplicialChainConeSecondIndex_operatorOfSimplexMaps, Finset.sum_range_succ]`.
-/
theorem idD {a b q : ℕ} (f : bo a b ⟶ bo 1 q) : H2 (f ≫ dT 1 q 0 q) = 0 := by
  refine hom_induct (fun f => H2 (f ≫ dT 1 q 0 q) = 0) ?_ ?_ ?_ ?_ f
  · simp
  · intro f g hf hg; simp only [map_add, Preadditive.add_comp, hf, hg, add_zero]
  · intro r f hf; simp only [map_zsmul, Preadditive.zsmul_comp, hf, smul_zero]
  · intro α β
    rw [bisimplicialTotalDifferentialOperator_one_zero_eq_sum]
    simp [Preadditive.comp_sum, Preadditive.comp_zsmul, bop_comp, map_sum, map_zsmul, bisimplicialChainConeSecondIndex_operatorOfSimplexMaps,
      Finset.sum_range_succ]

/- English proof (translation)
Rewrite using `[Finset.sum_eq_add (c + 1, d) (c, d + 1) (by simp)]`. Introduce and unpack `x hx ⟨h1, h2⟩`. Rewrite using `[dT_zero, Limits.comp_zero]`. Introduce and unpack `⟨e1, e2⟩`. Conclude with `h1 (Prod.ext e1 e2)`.

Introduce and unpack `⟨e1, e2⟩`. Conclude with `h2 (Prod.ext e1 e2)`. Introduce `h; exact absurd (by rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega) h`. Introduce `h; exact absurd (by rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega) h`.
-/
theorem sum_dT {a b : ℕ} (u : ∀ a' b' : ℕ, bo a b ⟶ bo a' b') (c d : ℕ) :
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (c + d + 1), u x.1 x.2 ≫ dT x.1 x.2 c d =
      u (c + 1) d ≫ dT (c + 1) d c d + u c (d + 1) ≫ dT c (d + 1) c d := by
  rw [Finset.sum_eq_add (c + 1, d) (c, d + 1) (by simp)]
  · rintro x hx ⟨h1, h2⟩
    rw [dT_zero, Limits.comp_zero]
    · rintro ⟨e1, e2⟩; exact h1 (Prod.ext e1 e2)
    · rintro ⟨e1, e2⟩; exact h2 (Prod.ext e1 e2)
  · intro h; exact absurd (by rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega) h
  · intro h; exact absurd (by rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega) h

def wfill {a b : ℕ} (z : ∀ a' b' : ℕ, bo a b ⟶ bo a' b') : ∀ a' b' : ℕ, bo a b ⟶ bo a' b'
  | 0, 0 => 0
  | 0, q + 1 => H2 (z 0 q)
  | p + 1, q => H1 (z p q)

end GlobalTheory.EZ.Acyc

namespace GlobalTheory.EZ
open GlobalTheory.EZ.Acyc

/- English proof (translation)
Introduce `a b k hk z hz`. Use `⟨wfill z, fun c d hcd => ?_⟩` and prove the remaining obligations. Substitute `hcd` using the available equality. Rewrite using `[sum_dT]`. Establish `cyc : ∀ c' d', c' + d' + 1 = c + d → z (c' + 1) d' ≫ dT (c' + 1) d' c' d' + z c' (d' + 1) ≫ dT c' (d' + 1) c' d' = 0`.

Introduce `c' d' h`. Use `hz c' d' h` as an intermediate fact. Rewrite `this` using `[← h, sum_dT]`. Conclude with `this`. Consider the cases of `c with`.

Consider the case `succ p => show H1 (z (p + 1) d) ≫ dT (p + 1 + 1) d (p + 1) d + H1 (z p (d + 1)) ≫ dT (p + 1) (d + 1) (p + 1) d = _`. Establish `h2 : H1 (z (p + 1) d ≫ dT (p + 1) d p d) + H1 (z p (d + 1) ≫ dT p (d + 1) p d) = 0`. Rewrite using `[← map_add, cyc p d (by omega), map_zero]`. Rewrite using `[idA, idB, ← sub_eq_add_neg, sub_sub, h2, sub_zero]`. Consider the case `zero`.

Take `⟨q, rfl⟩ : ∃ q, d = q + 1` from `⟨d - 1, by omega⟩`. Use `show H1 (z 0 (q + 1)) ≫ dT 1 (q + 1) 0 (q + 1) + H2 (z 0 (q + 1)) ≫ dT 0 (q + 1 + 1) 0 (q + 1) = _`. Rewrite using `[idC]`. Establish `h3 : z 0 (q + 1) ≫ dT 0 (q + 1) 0 q = -(z 1 q ≫ dT 1 q 0 q)`. Use `cyc 0 q (by omega)` as an intermediate fact.

Rewrite using `[eq_neg_iff_add_eq_zero, add_comm]`. Conclude with `this`. Rewrite using `[h3, map_neg, idD, neg_zero, sub_zero]`.
-/
theorem totChains_acyclic : ∀ a b k : ℕ, 1 ≤ k → ∀ z : ∀ a' b' : ℕ, bo a b ⟶ bo a' b',
    (∀ c d : ℕ, c + d + 1 = k → ∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, z x.1 x.2 ≫ dT x.1 x.2 c d = 0) →
    ∃ w : ∀ a' b' : ℕ, bo a b ⟶ bo a' b', ∀ c d : ℕ, c + d = k →
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (k + 1), w x.1 x.2 ≫ dT x.1 x.2 c d = z c d := by
  intro a b k hk z hz
  refine ⟨wfill z, fun c d hcd => ?_⟩
  subst hcd
  rw [sum_dT]
  have cyc : ∀ c' d', c' + d' + 1 = c + d →
      z (c' + 1) d' ≫ dT (c' + 1) d' c' d' + z c' (d' + 1) ≫ dT c' (d' + 1) c' d' = 0 := by
    intro c' d' h
    have := hz c' d' h
    rw [← h, sum_dT] at this
    exact this
  cases c with
  | succ p =>
    show H1 (z (p + 1) d) ≫ dT (p + 1 + 1) d (p + 1) d + H1 (z p (d + 1)) ≫ dT (p + 1) (d + 1) (p + 1) d = _
    have h2 : H1 (z (p + 1) d ≫ dT (p + 1) d p d) + H1 (z p (d + 1) ≫ dT p (d + 1) p d) = 0 := by
      rw [← map_add, cyc p d (by omega), map_zero]
    rw [idA, idB, ← sub_eq_add_neg, sub_sub, h2, sub_zero]
  | zero =>
    obtain ⟨q, rfl⟩ : ∃ q, d = q + 1 := ⟨d - 1, by omega⟩
    show H1 (z 0 (q + 1)) ≫ dT 1 (q + 1) 0 (q + 1) + H2 (z 0 (q + 1)) ≫ dT 0 (q + 1 + 1) 0 (q + 1) = _
    rw [idC]
    have h3 : z 0 (q + 1) ≫ dT 0 (q + 1) 0 q = -(z 1 q ≫ dT 1 q 0 q) := by
      have := cyc 0 q (by omega)
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact this
    rw [h3, map_neg, idD, neg_zero, sub_zero]

end GlobalTheory.EZ

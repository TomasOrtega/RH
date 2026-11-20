import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.GramMapSecondProjTranspose

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

/- English proof (translation)
Establish `h1 : ∀ x : E, ph1 g x = (g.e x).1` using `fun x => rfl`. Simplify using `only [HermSp.ZZplusOf, hs, Matrix.of_apply]`. Apply the tactic sequence `split_ifs with hab <;> simp only [h1, map_sub, AlgEquiv.apply_symm_apply, map_zero, Prod.fst_zero, Prod.fst_sub, sub_zero, add_zero] <;> ring`.
-/
theorem zzPlus_firstProj_corner (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) (a b : Fin (r + 1)) :
    ph1 g (HermSp.ZZplusOf M Zh T T' a b) =
      (g.q : F)⁻¹ * ph1 g (Zh a b) + (if a = Fin.last r ∧ b = Fin.last r then T / (g.q : F) else 0) := by
  have h1 : ∀ x : E, ph1 g x = (g.e x).1 := fun x => rfl
  simp only [HermSp.ZZplusOf, hs, Matrix.of_apply]
  split_ifs with hab <;> simp only [h1, map_sub, AlgEquiv.apply_symm_apply, map_zero, Prod.fst_zero, Prod.fst_sub,
    sub_zero, add_zero] <;> ring

/- English proof (translation)
Establish `h2 : ∀ x : E, ph2 g x = (g.e x).2` using `fun x => rfl`. Simplify using `only [HermSp.ZZplusOf, hs, Matrix.of_apply]`. Apply the tactic sequence `split_ifs with hab <;> simp only [h2, map_sub, AlgEquiv.apply_symm_apply, map_zero, Prod.snd_zero, Prod.snd_sub, sub_zero, add_zero] <;> ring`.
-/
theorem zzPlus_secondProj_corner (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) (a b : Fin (r + 1)) :
    ph2 g (HermSp.ZZplusOf M Zh T T' a b) =
      -((g.q : F)⁻¹ * ph2 g (Zh b a)) + (if a = Fin.last r ∧ b = Fin.last r then -(T' / (g.q : F)) else 0) := by
  have h2 : ∀ x : E, ph2 g x = (g.e x).2 := fun x => rfl
  simp only [HermSp.ZZplusOf, hs, Matrix.of_apply]
  split_ifs with hab <;> simp only [h2, map_sub, AlgEquiv.apply_symm_apply, map_zero, Prod.snd_zero, Prod.snd_sub,
    sub_zero, add_zero] <;> ring

def lamV (g : SplitG M.L) (m : Fin (r + 1) → M.R) : Ix r → F :=
  Sum.elim (fun a => -(ph2 g (m a)) / (g.q : F)) (fun a => ph1 g (m a) / (g.q : F))

/- English proof (translation)
Rewrite using `[AddSubmonoidClass.coe_finset_sum, map_sum]`.
-/
theorem firstProj_ring_sum (s : Finset (Fin (r + 1))) (f : Fin (r + 1) → M.R) :
    ph1 g ((∑ j ∈ s, f j : M.R) : E) = ∑ j ∈ s, ph1 g (f j : E) := by
  rw [AddSubmonoidClass.coe_finset_sum, map_sum]

/- English proof (translation)
Rewrite using `[AddSubmonoidClass.coe_finset_sum, map_sum]`.
-/
theorem secondProj_ring_sum (s : Finset (Fin (r + 1))) (f : Fin (r + 1) → M.R) :
    ph2 g ((∑ j ∈ s, f j : M.R) : E) = ∑ j ∈ s, ph2 g (f j : E) := by
  rw [AddSubmonoidClass.coe_finset_sum, map_sum]

/- English proof (translation)
Use `show (g.e (algebraMap F E (c : F))).1 = c`. Rewrite using `[AlgEquiv.commutes]`. Both sides reduce to the same expression.
-/
theorem firstProj_diagonalEmbed (hs : M.split = some g) (c : 𝒪[F]) : ph1 g ((dgR hs c : M.R) : E) = c := by
  show (g.e (algebraMap F E (c : F))).1 = c
  rw [AlgEquiv.commutes]
  rfl

/- English proof (translation)
Use `show (g.e (algebraMap F E (c : F))).2 = c`. Rewrite using `[AlgEquiv.commutes]`. Both sides reduce to the same expression.
-/
theorem secondProj_diagonalEmbed (hs : M.split = some g) (c : 𝒪[F]) : ph2 g ((dgR hs c : M.R) : E) = c := by
  show (g.e (algebraMap F E (c : F))).2 = c
  rw [AlgEquiv.commutes]
  rfl

/- English proof (translation)
Conclude with `Finset.sum_congr rfl fun x _ => by ring`.
-/
theorem sum_comm3 {n : Type} [Fintype n] (a b : n → F) (c : F) :
    ∑ x, a x * b x * c = ∑ x, c * b x * a x := by
  exact Finset.sum_congr rfl fun x _ => by ring

/- English proof (translation)
Establish `hZe : ∀ i j, ((Z.Z i j : M.R) : E) = HermSp.ZZplusOf M Zh T T' i j` using `fun i j => by`. Rewrite using `[← hZ]`. Both sides reduce to the same expression. Establish `hT1 : ph1 g (TT : E) = T` using `by rw [firstProj_apply, hTT]`. Establish `hT2 : ph2 g (TT : E) = T'` using `by rw [secondProj_apply, hTT]`.

Establish `hq` using `q_ne g`. Take `⟨Zf, rfl⟩ : ∃ Zf : Fin (r + 1) → Fin (r + 1) → E, Matrix.of Zf = Zh` from `⟨Zh, rfl⟩`. Establish `hsum1 : ∀ i, ∑ x, (g.e (Zf i x)).1 * (g.e (m x : E)).1 * (g.q : F)⁻¹ = ∑ x, (g.q : F)⁻¹ * (g.e (m x : E)).1 * (g.e (Zf i x)).1` using `fun i => Finset.sum_congr rfl fun x _ => by ring`. Establish `hsum2 : ∀ i, ∑ x, (g.e (Zf x i)).2 * (g.e (m x : E)).2 * (g.q : F)⁻¹ = ∑ x, (g.q : F)⁻¹ * (g.e (m x : E)).2 * (g.e (Zf x i)).2` using `fun i => Finset.sum_congr rfl fun x _ => by ring`. Establish `hsum3 : ∀ i, ∑ x, (g.e (Zf x i)).2 * (g.e (m x : E)).2 / (g.q : F) = ∑ x, (g.e (m x : E)).2 * (g.e (Zf x i)).2 / (g.q : F)` using `fun i => Finset.sum_congr rfl fun x _ => by ring`.

Use function extensionality and compare the values at `k`. Break down `k with i | i` into its components or cases. Simplify using `only [uV, Sum.elim_inl, llMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, map_sub, map_mul, firstProj_ring_sum, hZe, zzPlus_firstProj_corner hs, hT1, firstProj_diagonalEm …`. Distinguish the cases in `hi : i = Fin.last r`. Substitute `hi` using the available equality.

Simplify using `[Pi.single_apply, firstProj_apply, secondProj_apply, Finset.sum_add_distrib, add_mul, Finset.mul_sum, ite_and]`. Clear the denominators using the available nonvanishing facts. Use `first`. Consider the case `done`. Consider the case `(simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; done)`.

Consider the case `(simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring)`. Consider the case `(simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring_nf)`. Simplify using `[Pi.single_apply, hi, firstProj_apply, secondProj_apply, Finset.sum_add_distrib, add_mul, Finset.mul_sum, ite_and]`. Clear the denominators using the available nonvanishing facts. Use `first`.

Consider the case `done`. Consider the case `(simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; done)`. Consider the case `(simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring)`. Consider the case `(simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring_nf)`. Simplify using `only [uV, Sum.elim_inr, llMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, map_sub, map_mul, secondProj_ring_sum, hZe, zzPlus_secondProj_corner hs, hT2, secondProj_diagona …`.

Distinguish the cases in `hi : i = Fin.last r`. Substitute `hi` using the available equality. Simplify using `[Pi.single_apply, firstProj_apply, secondProj_apply, Finset.sum_add_distrib, add_mul, Finset.mul_sum, ite_and]`. Clear the denominators using the available nonvanishing facts. Use `first`.

Consider the case `done`. Consider the case `(simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; done)`. Consider the case `(simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring)`. Consider the case `(simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring_nf)`. Simplify using `[Pi.single_apply, hi, firstProj_apply, secondProj_apply, Finset.sum_add_distrib, add_mul, Finset.mul_sum, ite_and]`.

Clear the denominators using the available nonvanishing facts. Use `first`. Consider the case `done`. Consider the case `(simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; done)`. Consider the case `(simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring)`.

Consider the case `(simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring_nf)`.
-/
theorem uV_llMap (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (Z : M.Mat (r + 1)) (TT : M.R) (hZ : Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T')
    (hTT : g.e (TT : E) = (T, T')) (m : Fin (r + 1) → M.R) :
    uV g (llMap hs Z TT m) = Matrix.vecMul (lamV g m) (gHat g Zh T T') := by
  have hZe : ∀ i j, ((Z.Z i j : M.R) : E) = HermSp.ZZplusOf M Zh T T' i j := fun i j => by
    rw [← hZ]; rfl
  have hT1 : ph1 g (TT : E) = T := by rw [firstProj_apply, hTT]
  have hT2 : ph2 g (TT : E) = T' := by rw [secondProj_apply, hTT]
  have hq := q_ne g
  obtain ⟨Zf, rfl⟩ : ∃ Zf : Fin (r + 1) → Fin (r + 1) → E, Matrix.of Zf = Zh := ⟨Zh, rfl⟩
  have hsum1 : ∀ i, ∑ x, (g.e (Zf i x)).1 * (g.e (m x : E)).1 * (g.q : F)⁻¹ =
      ∑ x, (g.q : F)⁻¹ * (g.e (m x : E)).1 * (g.e (Zf i x)).1 := fun i => Finset.sum_congr rfl fun x _ => by ring
  have hsum2 : ∀ i, ∑ x, (g.e (Zf x i)).2 * (g.e (m x : E)).2 * (g.q : F)⁻¹ =
      ∑ x, (g.q : F)⁻¹ * (g.e (m x : E)).2 * (g.e (Zf x i)).2 := fun i => Finset.sum_congr rfl fun x _ => by ring
  have hsum3 : ∀ i, ∑ x, (g.e (Zf x i)).2 * (g.e (m x : E)).2 / (g.q : F) =
      ∑ x, (g.e (m x : E)).2 * (g.e (Zf x i)).2 / (g.q : F) := fun i => Finset.sum_congr rfl fun x _ => by ring
  funext k
  rcases k with i | i
  · simp only [uV, Sum.elim_inl, llMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, map_sub, map_mul, firstProj_ring_sum,
      hZe, zzPlus_firstProj_corner hs, hT1, firstProj_diagonalEmbed, trO_coe, Matrix.vecMul, Fintype.sum_sum_type, lamV, Sum.elim_inr,
      gHat, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.of_apply, Matrix.transpose_apply,
      Matrix.map_apply, eV]
    by_cases hi : i = Fin.last r
    · subst hi
      simp [Pi.single_apply, firstProj_apply, secondProj_apply, Finset.sum_add_distrib, add_mul, Finset.mul_sum, ite_and]
      field_simp
      first
        | done
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; done)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring_nf)
    · simp [Pi.single_apply, hi, firstProj_apply, secondProj_apply, Finset.sum_add_distrib, add_mul, Finset.mul_sum, ite_and]
      field_simp
      first
        | done
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; done)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring_nf)
  · simp only [uV, Sum.elim_inr, llMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, map_sub, map_mul, secondProj_ring_sum,
      hZe, zzPlus_secondProj_corner hs, hT2, secondProj_diagonalEmbed, trO_coe, Matrix.vecMul, Fintype.sum_sum_type, lamV, Sum.elim_inl,
      gHat, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Matrix.transpose_apply,
      Matrix.map_apply, eV]
    by_cases hi : i = Fin.last r
    · subst hi
      simp [Pi.single_apply, firstProj_apply, secondProj_apply, Finset.sum_add_distrib, add_mul, Finset.mul_sum, ite_and]
      field_simp
      first
        | done
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; done)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring_nf)
    · simp [Pi.single_apply, hi, firstProj_apply, secondProj_apply, Finset.sum_add_distrib, add_mul, Finset.mul_sum, ite_and]
      field_simp
      first
        | done
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; done)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring_nf)

/- English proof (translation)
Establish `hq : (g.q : F) ≠ 0` using `fun h => g.q_irr.ne_zero (Subtype.ext h)`. Unfold `dotProduct lamV uV`. Rewrite using `[Fintype.sum_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr]`. Rewrite using `[← Finset.sum_add_distrib]`.

Apply `sum_mem` to reduce the goal to its premises. Introduce `a _`. Take `⟨hm1, hm2, cm, hcm⟩` from `comp_of_mem_R hs (m a).2`. Take `⟨hw1, hw2, cw, hcw⟩` from `comp_of_mem_R hs (w a).2`. Establish `key : -(ph2 g (m a : E)) / (g.q : F) * ph1 g (w a : E) + ph1 g (m a : E) / (g.q : F) * ph2 g (w a : E) = (cm : F) * (g.e (w a : E)).2 - (g.e (m a : E)).2 * (cw : F)` using `by show -((g.e (m a : E)).2) / (g.q : F) * (g.e (w a : E)).1 + (g.e (m a : E)).1 / (g.q : F) * (g.e (w a : E)).2 = _`.

Establish `e1 : (g.e (m a : E)).1 = (g.e (m a : E)).2 + (g.q : F) * cm` using `by linear_combination hcm`. Establish `e2 : (g.e (w a : E)).1 = (g.e (w a : E)).2 + (g.q : F) * cw` using `by linear_combination hcw`. Rewrite using `[e1, e2]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[key]`. Conclude with `sub_mem (mul_mem cm.2 hw2) (mul_mem hm2 cw.2)`.
-/
theorem lamV_dot_mem (hs : M.split = some g) (m w : Fin (r + 1) → M.R) :
    dotProduct (lamV g m) (uV g w) ∈ 𝒪[F] := by
  classical
  have hq : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
  unfold dotProduct lamV uV
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [← Finset.sum_add_distrib]
  apply sum_mem
  intro a _
  obtain ⟨hm1, hm2, cm, hcm⟩ := comp_of_mem_R hs (m a).2
  obtain ⟨hw1, hw2, cw, hcw⟩ := comp_of_mem_R hs (w a).2
  have key : -(ph2 g (m a : E)) / (g.q : F) * ph1 g (w a : E) + ph1 g (m a : E) / (g.q : F) * ph2 g (w a : E) =
      (cm : F) * (g.e (w a : E)).2 - (g.e (m a : E)).2 * (cw : F) := by
    show -((g.e (m a : E)).2) / (g.q : F) * (g.e (w a : E)).1 +
      (g.e (m a : E)).1 / (g.q : F) * (g.e (w a : E)).2 = _
    have e1 : (g.e (m a : E)).1 = (g.e (m a : E)).2 + (g.q : F) * cm := by linear_combination hcm
    have e2 : (g.e (w a : E)).1 = (g.e (w a : E)).2 + (g.q : F) * cw := by linear_combination hcw
    rw [e1, e2]
    field_simp
    ring
  rw [key]
  exact sub_mem (mul_mem cm.2 hw2) (mul_mem hm2 cw.2)

/- English proof (translation)
Rewrite using `[Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hG, Matrix.vecMul_one]`.
-/
theorem dot_inv_vecMul {n : Type} [Fintype n] [DecidableEq n] (G : Matrix n n F) (hG : IsUnit G.det)
    (lam x : n → F) : dotProduct (Matrix.vecMul lam G) (Matrix.mulVec G⁻¹ x) = dotProduct lam x := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hG, Matrix.vecMul_one]

/- English proof (translation)
Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG, Matrix.one_mulVec]`.
-/
theorem dot_inv_mulVec {n : Type} [Fintype n] [DecidableEq n] (G : Matrix n n F) (hG : IsUnit G.det)
    (mu x : n → F) : dotProduct x (Matrix.mulVec G⁻¹ (Matrix.mulVec G mu)) = dotProduct x mu := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG, Matrix.one_mulVec]

/- English proof (translation)
Establish `hcj1 : ∀ x : E, ph1 g (M.L.cj x) = ph2 g x` using `fun x => by show (g.e (M.L.cj x)).1 = (g.e x).2`. Rewrite using `[g.e_cj]`. Both sides reduce to the same expression. Establish `hcj2 : ∀ x : E, ph2 g (M.L.cj x) = ph1 g x` using `fun x => by show (g.e (M.L.cj x)).2 = (g.e x).1`. Rewrite using `[g.e_cj]`.

Both sides reduce to the same expression. Unfold `gHat`. Rewrite using `[Matrix.fromBlocks_transpose, Matrix.transpose_transpose]`. Use `congr 1`. Use extensionality with `a b`.

Simplify using `only [Matrix.of_apply, Matrix.transpose_apply]`. Conclude with `if_congr and_comm rfl rfl`. Use extensionality with `a b`. Simplify using `only [Matrix.map_apply, hcj2]`. Use extensionality with `a b`.

Simplify using `only [Matrix.transpose_apply, Matrix.map_apply, hcj1]`. Use extensionality with `a b`. Simplify using `only [Matrix.of_apply, Matrix.transpose_apply]`. Conclude with `if_congr and_comm rfl rfl`.
-/
theorem gHat_cj (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    gHat g (Zh.map M.L.cj) T T' = (gHat g Zh T T').transpose := by
  have hcj1 : ∀ x : E, ph1 g (M.L.cj x) = ph2 g x := fun x => by
    show (g.e (M.L.cj x)).1 = (g.e x).2
    rw [g.e_cj]
    rfl
  have hcj2 : ∀ x : E, ph2 g (M.L.cj x) = ph1 g x := fun x => by
    show (g.e (M.L.cj x)).2 = (g.e x).1
    rw [g.e_cj]
    rfl
  unfold gHat
  rw [Matrix.fromBlocks_transpose, Matrix.transpose_transpose]
  congr 1
  · ext a b
    simp only [Matrix.of_apply, Matrix.transpose_apply]
    exact if_congr and_comm rfl rfl
  · ext a b
    simp only [Matrix.map_apply, hcj2]
  · ext a b
    simp only [Matrix.transpose_apply, Matrix.map_apply, hcj1]
  · ext a b
    simp only [Matrix.of_apply, Matrix.transpose_apply]
    exact if_congr and_comm rfl rfl

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

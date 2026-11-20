import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticChangeOfGoodModelsIntertwines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAdeleE
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
open GlobalTheory.DblDatum

noncomputable section

namespace GlobalTheory.DblIntw

/- English proof (translation)
Simplify using `only [symp, hTens, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, dblGram, blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, mu …`.
-/
theorem symp_dblGram_right {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) (ξ : A) {n d : ℕ}
    (J : Matrix (Fin n) (Fin n) A) (J' : Matrix (Fin d) (Fin d) A) (u v : Matrix (Fin n) (Fin (d + d)) A) :
    symp c ξ J (dblGram finSumFinEquiv J') u v =
      symp c ξ J J' (u.submatrix id (finSumFinEquiv ∘ Sum.inl)) (v.submatrix id (finSumFinEquiv ∘ Sum.inl)) -
      symp c ξ J J' (u.submatrix id (finSumFinEquiv ∘ Sum.inr)) (v.submatrix id (finSumFinEquiv ∘ Sum.inr)) := by
  simp only [symp, hTens, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, dblGram, blkMat,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, mul_neg, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg, mul_add, map_add,
    map_neg, id, Function.comp_apply, Finset.sum_add_distrib]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Set `S : Matrix (Fin n) (Fin (d + d)) (AE F E) ≃ₗ[AF F] Matrix (Fin n) (Fin d) (AE F E) × Matrix (Fin n) (Fin d) (AE F E)` to `(Matrix.transposeLinearEquiv (Fin n) (Fin (d + d)) (AF F) (AE F E)).trans (((LinearEquiv.funCongrLeft (AF F) (Fin n → AE F E) finSumFinEquiv).trans (LinearEquiv.sumArrowLequivProdArrow _ _ (AF F) _)).trans ((Matrix.transposeLinearEquiv (Fin d) (Fin n) (AF F) (AE F E)).prodCongr ( …`. Set `G : (Fin n × Fin d ⊕ Fin n × Fin d → AF F) ≃ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)` to `LinearEquiv.sumArrowLequivProdArrow _ _ (AF F) _`. Set `T` to `(LinearEquiv.prodProdProdComm (AF F) (Fin n × Fin d → AF F) (Fin n × Fin d → AF F) (Fin n × Fin d → AF F) (Fin n × Fin d → AF F)).trans ((LinearEquiv.refl (AF F) _).prodCongr ((LinearEquiv.refl (AF F) (Fin n × Fin d → AF F)).prodCongr (LinearEquiv.neg (AF F) (M := Fin n × Fin d → …`. Use `⟨S.trans ((co'.e.prodCongr co'.e).trans (T.trans (G.symm.prodCongr G.symm))), fun u => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> rcases k with k | k <;> rfl`.
-/
theorem exists_dblEquiv {σ : E →ₐ[F] E} {n d : ℕ}
    {JX : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin d) (Fin d) E}
    (co' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW)) (Fin n × Fin d)) :
    ∃ D : Matrix (Fin n) (Fin (d + d)) (AE F E) ≃ₗ[AF F]
      (Fin n × Fin d ⊕ Fin n × Fin d → AF F) × (Fin n × Fin d ⊕ Fin n × Fin d → AF F), ∀ u, D u = dblE co' u := by
  let S : Matrix (Fin n) (Fin (d + d)) (AE F E) ≃ₗ[AF F]
      Matrix (Fin n) (Fin d) (AE F E) × Matrix (Fin n) (Fin d) (AE F E) :=
    (Matrix.transposeLinearEquiv (Fin n) (Fin (d + d)) (AF F) (AE F E)).trans
      (((LinearEquiv.funCongrLeft (AF F) (Fin n → AE F E) finSumFinEquiv).trans
        (LinearEquiv.sumArrowLequivProdArrow _ _ (AF F) _)).trans
        ((Matrix.transposeLinearEquiv (Fin d) (Fin n) (AF F) (AE F E)).prodCongr
          (Matrix.transposeLinearEquiv (Fin d) (Fin n) (AF F) (AE F E))))
  let G : (Fin n × Fin d ⊕ Fin n × Fin d → AF F) ≃ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    LinearEquiv.sumArrowLequivProdArrow _ _ (AF F) _
  let T := (LinearEquiv.prodProdProdComm (AF F) (Fin n × Fin d → AF F) (Fin n × Fin d → AF F) (Fin n × Fin d → AF F)
    (Fin n × Fin d → AF F)).trans ((LinearEquiv.refl (AF F) _).prodCongr
      ((LinearEquiv.refl (AF F) (Fin n × Fin d → AF F)).prodCongr (LinearEquiv.neg (AF F) (M := Fin n × Fin d → AF F))))
  refine ⟨S.trans ((co'.e.prodCongr co'.e).trans (T.trans (G.symm.prodCongr G.symm))), fun u => ?_⟩
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> rcases k with k | k <;> rfl

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `F E _ _ _ _ _ m k ι _ e hrat y z`. Use `haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial`. Set `I : Matrix (Fin m) (Fin k) E →ₗ[F] Matrix (Fin m) (Fin k) (AE F E)` to `(Algebra.TensorProduct.includeRight (R := F) (A := AF F) (B := E)).toLinearMap.mapMatrix`. Set `L : Matrix (Fin m) (Fin k) E →ₗ[F] (ι → AF F) × (ι → AF F)` to `(e.toLinearMap.restrictScalars F).comp I`. Establish `hL : ∀ x, L x = e (incM F x)` using `fun x => rfl`.

Set `r : (ι → F) →ₗ[F] (ι → AF F)` to `LinearMap.pi fun i => (Algebra.linearMap F (AF F)).comp (LinearMap.proj i)`. Set `R : ((ι → F) × (ι → F)) →ₗ[F] (ι → AF F) × (ι → AF F)` to `LinearMap.prodMap r r`. Establish `hR : ∀ y z, R (y, z) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))` using `fun _ _ => rfl`. Establish `hAinj : Function.Injective (algebraMap F (AF F))` using `AdeleRing.algebraMap_injective _ _`. Establish `hrinj : Function.Injective r` using `fun a b h => funext fun i => hAinj (congrFun h i)`.

Establish `hRinj : Function.Injective R` using `fun a b h => Prod.ext (hrinj (congrArg Prod.fst h)) (hrinj (congrArg Prod.snd h))`. Establish `hIinj : Function.Injective I` using `fun a b h => Matrix.ext fun i j => Algebra.TensorProduct.includeRight_injective hAinj (congrFun (congrFun h i) j)`. Establish `hLinj : Function.Injective L` using `e.injective.comp hIinj`. Establish `hle : LinearMap.range L ≤ LinearMap.range R`. Introduce and unpack `_ ⟨x, rfl⟩`.

Take `⟨y', z', h⟩` from `hrat x`. Conclude with `⟨(y', z'), by rw [hR, hL, h]⟩`. Establish `hdim : Fintype.card (Fin m) * Fintype.card (Fin k) * Module.finrank F E = Fintype.card ι + Fintype.card ι`. Establish `h1` using `e.finrank_eq`. Rewrite `h1` using `[Module.finrank_matrix, Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fintype_fun_eq_card]`.

Conclude with `h1`. Establish `hfin : Module.finrank F (LinearMap.range L) = Module.finrank F (LinearMap.range R)`. Rewrite using `[LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hRinj, Module.finrank_matrix, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hdim]`. Establish `heq` using `Submodule.eq_of_le_of_finrank_eq hle hfin`. Take `⟨x, hx⟩ : (R (y, z)) ∈ LinearMap.range L` from `heq ▸ ⟨(y, z), rfl⟩`.

Conclude with `⟨x, by rw [← hL, hx, hR]⟩`.
-/
theorem rat_onto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (m k : ℕ)
    (ι : Type) [Fintype ι] (e : Matrix (Fin m) (Fin k) (AE F E) ≃ₗ[AF F] (ι → AF F) × (ι → AF F)),
    (∀ x : Matrix (Fin m) (Fin k) E, ∃ y z : ι → F,
      e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∀ y z : ι → F, ∃ x : Matrix (Fin m) (Fin k) E,
      e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
  intro F E _ _ _ _ _ m k ι _ e hrat y z
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  let I : Matrix (Fin m) (Fin k) E →ₗ[F] Matrix (Fin m) (Fin k) (AE F E) :=
    (Algebra.TensorProduct.includeRight (R := F) (A := AF F) (B := E)).toLinearMap.mapMatrix
  let L : Matrix (Fin m) (Fin k) E →ₗ[F] (ι → AF F) × (ι → AF F) := (e.toLinearMap.restrictScalars F).comp I
  have hL : ∀ x, L x = e (incM F x) := fun x => rfl
  let r : (ι → F) →ₗ[F] (ι → AF F) :=
    LinearMap.pi fun i => (Algebra.linearMap F (AF F)).comp (LinearMap.proj i)
  let R : ((ι → F) × (ι → F)) →ₗ[F] (ι → AF F) × (ι → AF F) := LinearMap.prodMap r r
  have hR : ∀ y z, R (y, z) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := fun _ _ => rfl
  have hAinj : Function.Injective (algebraMap F (AF F)) := AdeleRing.algebraMap_injective _ _
  have hrinj : Function.Injective r := fun a b h => funext fun i => hAinj (congrFun h i)
  have hRinj : Function.Injective R := fun a b h => Prod.ext (hrinj (congrArg Prod.fst h)) (hrinj (congrArg Prod.snd h))
  have hIinj : Function.Injective I := fun a b h => Matrix.ext fun i j =>
    Algebra.TensorProduct.includeRight_injective hAinj (congrFun (congrFun h i) j)
  have hLinj : Function.Injective L := e.injective.comp hIinj
  have hle : LinearMap.range L ≤ LinearMap.range R := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y', z', h⟩ := hrat x
    exact ⟨(y', z'), by rw [hR, hL, h]⟩
  have hdim : Fintype.card (Fin m) * Fintype.card (Fin k) * Module.finrank F E = Fintype.card ι + Fintype.card ι := by
    have h1 := e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at h1
    exact h1
  have hfin : Module.finrank F (LinearMap.range L) = Module.finrank F (LinearMap.range R) := by
    rw [LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hRinj, Module.finrank_matrix,
      Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hdim]
  have heq := Submodule.eq_of_le_of_finrank_eq hle hfin
  obtain ⟨x, hx⟩ : (R (y, z)) ∈ LinearMap.range L := heq ▸ ⟨(y, z), rfl⟩
  exact ⟨x, by rw [← hL, hx, hR]⟩

/- English proof (translation)
Introduce `F _ _ ι _ _ G hrat hω`. Set `P : (ι ⊕ ι → AF F) ≃ₗ[AF F] (ι → AF F) × (ι → AF F)` to `LinearEquiv.sumArrowLequivProdArrow _ _ (AF F) _`. Set `Gs : (ι ⊕ ι → AF F) →ₗ[AF F] (ι ⊕ ι → AF F)` to `P.symm.toLinearMap ∘ₗ G ∘ₗ P.toLinearMap`. Establish `hP : ∀ w : (ι → AF F) × (ι → AF F), P.symm w = Sum.elim w.1 w.2` using `fun w => by`. Apply the tactic sequence `funext k; rcases k with k | k <;> rfl`.

Establish `hP' : ∀ v : ι ⊕ ι → AF F, P v = (v ∘ Sum.inl, v ∘ Sum.inr)` using `fun v => rfl`. Establish `hGs : ∀ v, Gs v = Sum.elim (G (P v)).1 (G (P v)).2` using `fun v => hP _`. Establish `hent : ∀ i j, ∃ q : F, LinearMap.toMatrix' Gs i j = algebraMap F (AF F) q`. Introduce `i j`. Take `⟨y', z', h⟩` from `hrat ((Pi.single j (1 : F)) ∘ Sum.inl) ((Pi.single j (1 : F)) ∘ Sum.inr)`.

Use `⟨Sum.elim y' z' i, ?_⟩` and prove the remaining obligations. Establish `hs : (Pi.single j (1 : AF F) : ι ⊕ ι → AF F) = fun k => algebraMap F (AF F) ((Pi.single j (1 : F) : ι ⊕ ι → F) k)`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[hk]`. Rewrite using `[LinearMap.toMatrix'_apply, hs, hGs, hP']`. Set `w0 : (ι → AF F) × (ι → AF F)` to `(fun k => algebraMap F (AF F) ((Pi.single j (1 : F) ∘ Sum.inl) k), fun k => algebraMap F (AF F) ((Pi.single j (1 : F) ∘ Sum.inr) k))`. Express the relevant statement in the definitionally equal form `Sum.elim (G w0).1 (G w0).2 i = _`.

Rewrite using `[show G w0 = _ from h]`. Apply the tactic sequence `rcases i with i | i <;> rfl`. Use `choose a' ha using hent`. Set `a : Matrix (ι ⊕ ι) (ι ⊕ ι) F` to `Matrix.of a'`. Establish `hM : a.map (algebraMap F (AF F)) = LinearMap.toMatrix' Gs` using `by ext i j; exact (ha i j).symm`.

Establish `hact : ∀ w, G w = GlobalTheory.RatWeilOp.act (a.map (algebraMap F (AF F))) w`. Introduce `w`. Rewrite using `[hM, GlobalTheory.RatWeilOp.act, LinearMap.toMatrix'_mulVec, hGs, hP']`. Rewrite using `[show ((Sum.elim w.1 w.2) ∘ Sum.inl, (Sum.elim w.1 w.2) ∘ Sum.inr) = w from Prod.ext rfl rfl]`. Both sides reduce to the same expression.

Use `⟨a, ?_, hact⟩` and prove the remaining obligations. Establish `hJ : ∀ v v' : ι ⊕ ι → AF F, v ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) F).map (algebraMap F (AF F)) *ᵥ v') = (v ∘ Sum.inl) ⬝ᵥ (v' ∘ Sum.inr) - (v' ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inr)`. Introduce `v v'`. Establish `hJA : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) F).map (algebraMap F (AF F)) = Matrix.fromBlocks 0 1 (-1) 0`. Apply the tactic sequence `ext (i | i) (j | j) <;> simp [Matrix.one_apply, apply_ite (algebraMap F (AF F))]`.

Rewrite using `[hJA, Matrix.fromBlocks_mulVec, ← Sum.elim_comp_inl_inr v, sumElim_dotProduct_sumElim]`. Simplify using `only [Matrix.zero_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec, zero_add, add_zero, dotProduct_neg, Sum.elim_comp_inl, Sum.elim_comp_inr, dotProduct_comm (v' ∘ Sum.inl)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hinj : Function.Injective (Matrix.map · (algebraMap F (AF F)) : Matrix (ι ⊕ ι) (ι ⊕ ι) F → Matrix (ι ⊕ ι) (ι ⊕ ι) (AF F))` using `Matrix.map_injective (AdeleRing.algebraMap_injective _ _)`. Apply `hinj` to reduce the goal to its premises.

Simplify using `only`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hM]`. Establish `key : ∀ (X : Matrix (ι ⊕ ι) (ι ⊕ ι) (AF F)) i j, X i j = Pi.single i 1 ⬝ᵥ (X *ᵥ Pi.single j 1)` using `fun X i j => by`. Simplify using `[Matrix.mulVec_single_one]`. Use `Matrix.ext fun i j => (key _ i j).trans (Eq.trans ?_ (key _ i j).symm)` and prove the remaining obligations.

Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, hJ, hJ, hGs, hGs]`. Simplify using `only [Sum.elim_comp_inl, Sum.elim_comp_inr]`. Rewrite using `[hω]`. Both sides reduce to the same expression.
-/
theorem rat_symp : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι]
    (G : ((ι → AF F) × (ι → AF F)) →ₗ[AF F] ((ι → AF F) × (ι → AF F))),
    (∀ y z : ι → F, ∃ y' z' : ι → F,
      G (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) =
        (fun i => algebraMap F (AF F) (y' i), fun i => algebraMap F (AF F) (z' i))) →
    (∀ w w', (G w).1 ⬝ᵥ (G w').2 - (G w').1 ⬝ᵥ (G w).2 = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) →
    ∃ a : Matrix (ι ⊕ ι) (ι ⊕ ι) F, aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0 ∧
      ∀ w, G w = GlobalTheory.RatWeilOp.act (a.map (algebraMap F (AF F))) w := by
  intro F _ _ ι _ _ G hrat hω
  let P : (ι ⊕ ι → AF F) ≃ₗ[AF F] (ι → AF F) × (ι → AF F) := LinearEquiv.sumArrowLequivProdArrow _ _ (AF F) _
  let Gs : (ι ⊕ ι → AF F) →ₗ[AF F] (ι ⊕ ι → AF F) := P.symm.toLinearMap ∘ₗ G ∘ₗ P.toLinearMap
  have hP : ∀ w : (ι → AF F) × (ι → AF F), P.symm w = Sum.elim w.1 w.2 := fun w => by
    funext k; rcases k with k | k <;> rfl
  have hP' : ∀ v : ι ⊕ ι → AF F, P v = (v ∘ Sum.inl, v ∘ Sum.inr) := fun v => rfl
  have hGs : ∀ v, Gs v = Sum.elim (G (P v)).1 (G (P v)).2 := fun v => hP _
  have hent : ∀ i j, ∃ q : F, LinearMap.toMatrix' Gs i j = algebraMap F (AF F) q := by
    intro i j
    obtain ⟨y', z', h⟩ := hrat ((Pi.single j (1 : F)) ∘ Sum.inl) ((Pi.single j (1 : F)) ∘ Sum.inr)
    refine ⟨Sum.elim y' z' i, ?_⟩
    have hs : (Pi.single j (1 : AF F) : ι ⊕ ι → AF F) = fun k => algebraMap F (AF F) ((Pi.single j (1 : F) : ι ⊕ ι → F) k) := by
      funext k; by_cases hk : k = j
      · subst hk; simp
      · simp [hk]
    rw [LinearMap.toMatrix'_apply, hs, hGs, hP']
    let w0 : (ι → AF F) × (ι → AF F) := (fun k => algebraMap F (AF F) ((Pi.single j (1 : F) ∘ Sum.inl) k),
      fun k => algebraMap F (AF F) ((Pi.single j (1 : F) ∘ Sum.inr) k))
    change Sum.elim (G w0).1 (G w0).2 i = _
    rw [show G w0 = _ from h]
    rcases i with i | i <;> rfl
  choose a' ha using hent
  let a : Matrix (ι ⊕ ι) (ι ⊕ ι) F := Matrix.of a'
  have hM : a.map (algebraMap F (AF F)) = LinearMap.toMatrix' Gs := by ext i j; exact (ha i j).symm
  have hact : ∀ w, G w = GlobalTheory.RatWeilOp.act (a.map (algebraMap F (AF F))) w := by
    intro w
    rw [hM, GlobalTheory.RatWeilOp.act, LinearMap.toMatrix'_mulVec, hGs, hP']
    rw [show ((Sum.elim w.1 w.2) ∘ Sum.inl, (Sum.elim w.1 w.2) ∘ Sum.inr) = w from Prod.ext rfl rfl]
    rfl
  refine ⟨a, ?_, hact⟩
  have hJ : ∀ v v' : ι ⊕ ι → AF F,
      v ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) F).map (algebraMap F (AF F)) *ᵥ v') =
        (v ∘ Sum.inl) ⬝ᵥ (v' ∘ Sum.inr) - (v' ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inr) := by
    intro v v'
    have hJA : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) F).map (algebraMap F (AF F)) =
        Matrix.fromBlocks 0 1 (-1) 0 := by
      ext (i | i) (j | j) <;> simp [Matrix.one_apply, apply_ite (algebraMap F (AF F))]
    rw [hJA, Matrix.fromBlocks_mulVec, ← Sum.elim_comp_inl_inr v, sumElim_dotProduct_sumElim]
    simp only [Matrix.zero_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec, zero_add, add_zero, dotProduct_neg,
      Sum.elim_comp_inl, Sum.elim_comp_inr, dotProduct_comm (v' ∘ Sum.inl)]
    ring
  have hinj : Function.Injective (Matrix.map · (algebraMap F (AF F)) :
      Matrix (ι ⊕ ι) (ι ⊕ ι) F → Matrix (ι ⊕ ι) (ι ⊕ ι) (AF F)) :=
    Matrix.map_injective (AdeleRing.algebraMap_injective _ _)
  apply hinj
  simp only
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hM]
  have key : ∀ (X : Matrix (ι ⊕ ι) (ι ⊕ ι) (AF F)) i j, X i j = Pi.single i 1 ⬝ᵥ (X *ᵥ Pi.single j 1) := fun X i j => by
    simp [Matrix.mulVec_single_one]
  refine Matrix.ext fun i j => (key _ i j).trans (Eq.trans ?_ (key _ i j).symm)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, hJ, hJ, hGs, hGs]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
  rw [hω]
  rfl

/- English proof (translation)
Introduce `l hl g hg`. Establish `hspan` using `GlobalTheory.T.schwartzBruhat_finiteAdeles_mem_span_restrictedProducts F κ g hg`. Use `clear hg`. Proceed by induction on `hspan using Submodule.span_induction with`. Consider the case `mem p hp`.

Take `⟨φ, hφ, hs, rfl⟩` from `hp`. Establish `hφF : GlobalTheory.RatWeilOp.IsFam φ` using `⟨hφ, hs⟩`. Establish `h2` using `h.isFam hφF`. Take `⟨T, hT⟩` from `hl (fun y => ∏ᶠ v, ev v (φ v) fun i => evalV F v (y i)) ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ h2.1 h2.2, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ h2.1 h2.2⟩`. Use `⟨T.comp ei, fun f => ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← hT]`. Conclude with `congrArg l (h.2.2.2.2.2 f φ hφF).1`. Consider the case `zero`. Use `⟨0, fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[show pureA F f 0 = 0 from funext fun _ => mul_zero _, map_zero]`.

Both sides reduce to the same expression. Consider the case `add x y _ _ hx hy`. Take `⟨T₁, h₁⟩` from `hx`. Take `⟨T₂, h₂⟩` from `hy`. Use `⟨T₁ + T₂, fun f => ?_⟩` and prove the remaining obligations.

Rewrite using `[show pureA F f (x + y) = pureA F f x + pureA F f y from funext fun _ => mul_add _ _ _, map_add, h₁, h₂]`. Both sides reduce to the same expression. Consider the case `smul r x _ hx`. Take `⟨T₁, h₁⟩` from `hx`. Use `⟨r • T₁, fun f => ?_⟩` and prove the remaining obligations.

Rewrite using `[show pureA F f (r • x) = r • pureA F f x from funext fun _ => mul_left_comm _ _ _, map_smul, h₁]`. Both sides reduce to the same expression.
-/
theorem op_adm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} {a : Matrix (κ ⊕ κ) (κ ⊕ κ) F}
    {e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ} {c : ℂ} {ei : SInf F κ →L[ℂ] SInf F κ}
    {ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ} (h : GlobalTheory.RatWeilOp.IsOp ψ a e c ei ev) :
    ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ e ∈ (adeleClass F).adm κ := by
  intro l hl g hg
  have hspan := GlobalTheory.T.schwartzBruhat_finiteAdeles_mem_span_restrictedProducts F κ g hg
  clear hg
  induction hspan using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨φ, hφ, hs, rfl⟩ := hp
    have hφF : GlobalTheory.RatWeilOp.IsFam φ := ⟨hφ, hs⟩
    have h2 := h.isFam hφF
    obtain ⟨T, hT⟩ := hl (fun y => ∏ᶠ v, ev v (φ v) fun i => evalV F v (y i))
      ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ h2.1 h2.2, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ h2.1 h2.2⟩
    refine ⟨T.comp ei, fun f => ?_⟩
    rw [LinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← hT]
    exact congrArg l (h.2.2.2.2.2 f φ hφF).1
  | zero =>
    refine ⟨0, fun f => ?_⟩
    rw [show pureA F f 0 = 0 from funext fun _ => mul_zero _, map_zero]
    rfl
  | add x y _ _ hx hy =>
    obtain ⟨T₁, h₁⟩ := hx
    obtain ⟨T₂, h₂⟩ := hy
    refine ⟨T₁ + T₂, fun f => ?_⟩
    rw [show pureA F f (x + y) = pureA F f x + pureA F f y from funext fun _ => mul_add _ _ _, map_add, h₁, h₂]
    rfl
  | smul r x _ hx =>
    obtain ⟨T₁, h₁⟩ := hx
    refine ⟨r • T₁, fun f => ?_⟩
    rw [show pureA F f (r • x) = r • pureA F f x from funext fun _ => mul_left_comm _ _ _, map_smul, h₁]
    rfl

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB n d JX JW JW₂ hJ co' hco' co hco`. Set `τ : (Fin n × Fin d ⊕ Fin n × Fin d) ≃ Fin n × Fin (d + d)` to `(Equiv.prodSumDistrib (Fin n) (Fin d) (Fin d)).symm.trans ((Equiv.refl _).prodCongr finSumFinEquiv)`. Take `⟨D, hD⟩` from `exists_dblEquiv co'`. Set `Rr : ((Fin n × Fin (d + d) → AF F) × (Fin n × Fin (d + d) → AF F)) ≃ₗ[AF F] ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) × (Fin n × Fin d ⊕ Fin n × Fin d → AF F))` to `(LinearEquiv.funCongrLeft (AF F) (AF F) τ).prodCongr (LinearEquiv.funCongrLeft (AF F) (AF F) τ)`. Set `G` to `(D.symm.trans co.e).trans Rr`.

Establish `hG : ∀ u, G (D u) = ((co.e u).1 ∘ τ, (co.e u).2 ∘ τ)` using `fun u => by`. Simplify using `only [G, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]`. Both sides reduce to the same expression. Establish `hdot : ∀ p q : Fin n × Fin (d + d) → AF F, (p ∘ τ) ⬝ᵥ (q ∘ τ) = p ⬝ᵥ q` using `fun p q => by`. Simplify using `only [dotProduct]`.

Conclude with `τ.sum_comp (fun i => p i * q i)`. Establish `hGrat : ∀ y z : Fin n × Fin d ⊕ Fin n × Fin d → F, ∃ y' z' : Fin n × Fin d ⊕ Fin n × Fin d → F, G (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) = (fun i => algebraMap F (AF F) (y' i), fun i => algebraMap F (AF F) (z' i))`. Introduce `y z`. Take `⟨x₁, h₁⟩` from `rat_onto F E n d _ co'.e hco' (y ∘ Sum.inl) (z ∘ Sum.inl)`. Take `⟨x₂, h₂⟩` from `rat_onto F E n d _ co'.e hco' (y ∘ Sum.inr) (-(z ∘ Sum.inr))`.

Set `x : Matrix (Fin n) (Fin (d + d)) E` to `fun i j => Sum.elim (x₁ i) (x₂ i) (finSumFinEquiv.symm j)`. Establish `ht : topC (incM F x) = incM F x₁`. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `inclR (F := F) (AF F) (Sum.elim (x₁ i) (x₂ i) (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j)))) = _`. Rewrite using `[Equiv.symm_apply_apply]`.

Both sides reduce to the same expression. Establish `hb : botC (incM F x) = incM F x₂`. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `inclR (F := F) (AF F) (Sum.elim (x₁ i) (x₂ i) (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j)))) = _`. Rewrite using `[Equiv.symm_apply_apply]`.

Both sides reduce to the same expression. Establish `hx : D (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))`. Rewrite using `[hD, dblE, ht, hb, h₁, h₂]`. Apply the tactic sequence `refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> rcases k with k | k <;> simp`. Take `⟨y', z', h⟩` from `hco x`.

Conclude with `⟨y' ∘ τ, z' ∘ τ, by rw [← hx, hG, h]; rfl⟩`. Establish `hGω : ∀ w w', (G w).1 ⬝ᵥ (G w').2 - (G w').1 ⬝ᵥ (G w).2 = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2`. Introduce `w w'`. Take `⟨u, rfl⟩` from `D.surjective w`. Take `⟨u', rfl⟩` from `D.surjective w'`.

Rewrite using `[hG, hG, hdot, hdot, ← co.form, hJ, GlobalTheory.DefDoubling.incM_dblGram, symp_dblGram_right, co'.form, co'.form, hD, hD]`. Simplify using `only [dblE, topC, botC, sumElim_dotProduct_sumElim, dotProduct_neg, neg_dotProduct]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨a, ha, hGa⟩` from `rat_symp F _ G.toLinearMap hGrat hGω`. Take `⟨e₀, c, ei, ev, h⟩` from `GlobalTheory.RatWeilOp.hasOp_of_symplectic hB.cm.1 hB.std a ha`.

Establish `hR : Set.BijOn (GlobalTheory.DblBox.reix (R` using `AF F) τ) (schA F (Fin n × Fin d ⊕ Fin n × Fin d) : Set _) (schA F (Fin n × Fin (d + d)) : Set _) := ⟨fun φ hφ => GlobalTheory.DblBox.reix_mem_schA τ hφ, (GlobalTheory.DblBox.reix τ).injective.injOn, fun Φ hΦ => ⟨(GlobalTheory.DblBox.reix τ).symm Φ, by rw [GlobalTheory.DblBox.reix …`. Use `⟨(GlobalTheory.DblBox.reix τ).toLinearMap ∘ₗ e₀, c, h.1, hR.comp (h.bijOn hB.std), fun l hl => ?_, fun u Ψ hΨ => ?_, fun Ψ hΨ => ?_⟩` and prove the remaining obligations. Conclude with `op_adm h _ (GlobalTheory.DblBox.comp_reix_mem_adm τ hl)`. Establish `h1 : GlobalTheory.RatWeilOp.act (a.map (algebraMap F (AF F))) (dblE co' u) = ((co.e u).1 ∘ τ, (co.e u).2 ∘ τ)`. Rewrite using `[← hD, ← hG u]`.

Conclude with `(hGa _).symm`. Establish `h2` using `GlobalTheory.DblBox.schr_reix B.ψ τ ((co.e u).1 ∘ τ) ((co.e u).2 ∘ τ) (e₀ Ψ)`. Establish `h3 : ∀ p : Fin n × Fin (d + d) → AF F, p ∘ τ ∘ τ.symm = p` using `fun p => by`. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules.

Rewrite `h2` using `[Function.comp_assoc, Function.comp_assoc, h3, h3]`. Rewrite using `[LinearMap.comp_apply, h.Heisenberg₂ _ Ψ hΨ, h1, LinearEquiv.coe_coe, ← h2, Darboux.rho]`. Both sides reduce to the same expression. Rewrite using `[LinearMap.comp_apply, LinearEquiv.coe_coe, GlobalTheory.DblBox.thetaSum_reix, h.theta Ψ hΨ]`.
-/
theorem doubling_intertwiner : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) (JW₂ : Matrix (Fin (d + d)) (Fin (d + d)) E),
    JW₂ = dblGram finSumFinEquiv JW →
    ∀ co' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW)) (Fin n × Fin d),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co'.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW₂)) (Fin n × Fin (d + d)),
      (∀ x : Matrix (Fin n) (Fin (d + d)) E, ∃ y z : Fin n × Fin (d + d) → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ (e : ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin (d + d) → AF F) → ℂ)) (c : ℂ), c ≠ 0 ∧
      Set.BijOn e (schA F (Fin n × Fin d ⊕ Fin n × Fin d) : Set _) (schA F (Fin n × Fin (d + d)) : Set _) ∧
      (∀ l ∈ (adeleClass F).adm (Fin n × Fin (d + d)), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) ∧
      (∀ u, ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), e (schr B.ψ (dblE co' u) Ψ) = co.rho B.ψ u (e Ψ)) ∧
      ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), thetaSum F (e Ψ) = c * thetaSum F Ψ := by
  intro F E _ _ _ _ _ σ B hB n d JX JW JW₂ hJ co' hco' co hco
  classical
  let τ : (Fin n × Fin d ⊕ Fin n × Fin d) ≃ Fin n × Fin (d + d) :=
    (Equiv.prodSumDistrib (Fin n) (Fin d) (Fin d)).symm.trans ((Equiv.refl _).prodCongr finSumFinEquiv)
  obtain ⟨D, hD⟩ := exists_dblEquiv co'
  let Rr : ((Fin n × Fin (d + d) → AF F) × (Fin n × Fin (d + d) → AF F)) ≃ₗ[AF F]
      ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) × (Fin n × Fin d ⊕ Fin n × Fin d → AF F)) :=
    (LinearEquiv.funCongrLeft (AF F) (AF F) τ).prodCongr (LinearEquiv.funCongrLeft (AF F) (AF F) τ)
  let G := (D.symm.trans co.e).trans Rr
  have hG : ∀ u, G (D u) = ((co.e u).1 ∘ τ, (co.e u).2 ∘ τ) := fun u => by
    simp only [G, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]; rfl
  have hdot : ∀ p q : Fin n × Fin (d + d) → AF F, (p ∘ τ) ⬝ᵥ (q ∘ τ) = p ⬝ᵥ q := fun p q => by
    simp only [dotProduct]; exact τ.sum_comp (fun i => p i * q i)
  have hGrat : ∀ y z : Fin n × Fin d ⊕ Fin n × Fin d → F, ∃ y' z' : Fin n × Fin d ⊕ Fin n × Fin d → F,
      G (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) =
        (fun i => algebraMap F (AF F) (y' i), fun i => algebraMap F (AF F) (z' i)) := by
    intro y z
    obtain ⟨x₁, h₁⟩ := rat_onto F E n d _ co'.e hco' (y ∘ Sum.inl) (z ∘ Sum.inl)
    obtain ⟨x₂, h₂⟩ := rat_onto F E n d _ co'.e hco' (y ∘ Sum.inr) (-(z ∘ Sum.inr))
    let x : Matrix (Fin n) (Fin (d + d)) E := fun i j => Sum.elim (x₁ i) (x₂ i) (finSumFinEquiv.symm j)
    have ht : topC (incM F x) = incM F x₁ := by
      ext i j
      change inclR (F := F) (AF F) (Sum.elim (x₁ i) (x₂ i) (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j)))) = _
      rw [Equiv.symm_apply_apply]; rfl
    have hb : botC (incM F x) = incM F x₂ := by
      ext i j
      change inclR (F := F) (AF F) (Sum.elim (x₁ i) (x₂ i) (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j)))) = _
      rw [Equiv.symm_apply_apply]; rfl
    have hx : D (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
      rw [hD, dblE, ht, hb, h₁, h₂]
      refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> rcases k with k | k <;> simp
    obtain ⟨y', z', h⟩ := hco x
    exact ⟨y' ∘ τ, z' ∘ τ, by rw [← hx, hG, h]; rfl⟩
  have hGω : ∀ w w', (G w).1 ⬝ᵥ (G w').2 - (G w').1 ⬝ᵥ (G w).2 = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 := by
    intro w w'
    obtain ⟨u, rfl⟩ := D.surjective w
    obtain ⟨u', rfl⟩ := D.surjective w'
    rw [hG, hG, hdot, hdot, ← co.form, hJ, GlobalTheory.DefDoubling.incM_dblGram, symp_dblGram_right, co'.form, co'.form,
      hD, hD]
    simp only [dblE, topC, botC, sumElim_dotProduct_sumElim, dotProduct_neg, neg_dotProduct]
    ring
  obtain ⟨a, ha, hGa⟩ := rat_symp F _ G.toLinearMap hGrat hGω
  obtain ⟨e₀, c, ei, ev, h⟩ := GlobalTheory.RatWeilOp.hasOp_of_symplectic hB.cm.1 hB.std a ha
  have hR : Set.BijOn (GlobalTheory.DblBox.reix (R := AF F) τ) (schA F (Fin n × Fin d ⊕ Fin n × Fin d) : Set _)
      (schA F (Fin n × Fin (d + d)) : Set _) :=
    ⟨fun φ hφ => GlobalTheory.DblBox.reix_mem_schA τ hφ, (GlobalTheory.DblBox.reix τ).injective.injOn,
      fun Φ hΦ => ⟨(GlobalTheory.DblBox.reix τ).symm Φ, by rw [GlobalTheory.DblBox.reix_symm]; exact GlobalTheory.DblBox.reix_mem_schA τ.symm hΦ,
        (GlobalTheory.DblBox.reix τ).apply_symm_apply Φ⟩⟩
  refine ⟨(GlobalTheory.DblBox.reix τ).toLinearMap ∘ₗ e₀, c, h.1, hR.comp (h.bijOn hB.std), fun l hl => ?_, fun u Ψ hΨ => ?_,
    fun Ψ hΨ => ?_⟩
  · exact op_adm h _ (GlobalTheory.DblBox.comp_reix_mem_adm τ hl)
  · have h1 : GlobalTheory.RatWeilOp.act (a.map (algebraMap F (AF F))) (dblE co' u) = ((co.e u).1 ∘ τ, (co.e u).2 ∘ τ) := by
      rw [← hD, ← hG u]; exact (hGa _).symm
    have h2 := GlobalTheory.DblBox.schr_reix B.ψ τ ((co.e u).1 ∘ τ) ((co.e u).2 ∘ τ) (e₀ Ψ)
    have h3 : ∀ p : Fin n × Fin (d + d) → AF F, p ∘ τ ∘ τ.symm = p := fun p => by
      funext k; simp
    rw [Function.comp_assoc, Function.comp_assoc, h3, h3] at h2
    rw [LinearMap.comp_apply, h.Heisenberg₂ _ Ψ hΨ, h1, LinearEquiv.coe_coe, ← h2, Darboux.rho]
    rfl
  · rw [LinearMap.comp_apply, LinearEquiv.coe_coe, GlobalTheory.DblBox.thetaSum_reix, h.theta Ψ hΨ]

end GlobalTheory.DblIntw

end

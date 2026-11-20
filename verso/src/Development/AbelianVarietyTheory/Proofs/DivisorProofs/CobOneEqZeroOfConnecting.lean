import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgebraPullbackTwoConvMulSymmetricCocycleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackMulPOfPTorsionInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryTranslationInvariantPTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSymmetricCocyclesOfPullbackMulPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionAdditiveFnPDivGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivCocycleMemRangeCobOfPullbackMulPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFunctionCartierDualTangentBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeBijectiveOfPEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFunctionsFlatBaseChangeBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveSemilinearLiftBaseChangeBijectiveStatement

set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv

namespace GlobalTheory

namespace PDiv

/- English proof (translation)
Use `letI : Algebra R A' := ((algebraMap R' A').comp σ).toAlgebra`. Establish `h` using `map_pow (f.pts A' fun _ => rfl) (toConv (AlgHom.id R' A')) k`. Establish `h1` using `DFunLike.congr_fun (congrArg ofConv h) a`. Establish `h2` using `DFunLike.congr_fun (comp_mulBy_pts (f.pts A' (fun _ => rfl) (toConv (AlgHom.id R' A'))).ofConv k) a`. Establish `h3` using `DFunLike.congr_fun (comp_mulBy_pts (AlgHom.id R' A') k) (f a)`.

Conclude with `h2.trans (h1.symm.trans h3.symm)`.
-/
theorem SemiBialgHom.map_mulBy {R R' A A' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}
    [CommRing A] [Bialgebra R A] [CommRing A'] [Bialgebra R' A'] [IsCocomm R A] [IsCocomm R' A']
    (f : SemiBialgHom σ A A') (k : ℕ) (a : A) : f (mulBy R A k a) = mulBy R' A' k (f a) := by
  letI : Algebra R A' := ((algebraMap R' A').comp σ).toAlgebra
  have h := map_pow (f.pts A' fun _ => rfl) (toConv (AlgHom.id R' A')) k
  have h1 := DFunLike.congr_fun (congrArg ofConv h) a
  have h2 := DFunLike.congr_fun
    (comp_mulBy_pts (f.pts A' (fun _ => rfl) (toConv (AlgHom.id R' A'))).ofConv k) a
  have h3 := DFunLike.congr_fun (comp_mulBy_pts (AlgHom.id R' A') k) (f a)
  exact h2.trans (h1.symm.trans h3.symm)

end PDiv

namespace PDivGroup

open PDiv

variable {p : ℕ} {R R' : Type} [CommRing R] [CommRing R'] {G H : PDivGroup p R}

/- English proof (translation)
Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Take `⟨c, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Set `B : G.funs` to `⟨fun n => LinearMap.mul' R _ (TensorProduct.map (f.app n : H.A n →ₗ[R] G.A n) (g.app n : H.A n →ₗ[R] G.A n) (c.1 n)), fun n => by dsimp only`. Rewrite using `[← (c.2 n).2]`. Generalize the expression as in `c.1 (n + 1) = t`.

Proceed by induction on `t with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul x y => simp [res_app]⟩`. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (cocyclesMap (f + g) c) = Submodule.Quotient.mk (cocyclesMap f c + cocyclesMap g c)`.

Use `(Submodule.Quotient.eq _).2 ⟨B, Subtype.ext (funext fun n => ?_)⟩` and prove the remaining obligations. Conclude with `eq_sub_iff_add_eq'.2 (T.bialgebraPullbackTwo_convMul_symmetricCocycle (f.app n) (g.app n) (c.1 n) (c.2 n).1).symm`.
-/
theorem vecExtMap_add (f g : G ⟶ H) : vecExtMap (f + g) = vecExtMap f + vecExtMap g := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  let B : G.funs := ⟨fun n => LinearMap.mul' R _ (TensorProduct.map (f.app n : H.A n →ₗ[R] G.A n)
      (g.app n : H.A n →ₗ[R] G.A n) (c.1 n)), fun n => by
    dsimp only
    rw [← (c.2 n).2]
    generalize c.1 (n + 1) = t
    induction t with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => simp [res_app]⟩
  change Submodule.Quotient.mk (cocyclesMap (f + g) c) =
    Submodule.Quotient.mk (cocyclesMap f c + cocyclesMap g c)
  refine (Submodule.Quotient.eq _).2 ⟨B, Subtype.ext (funext fun n => ?_)⟩
  exact eq_sub_iff_add_eq'.2 (T.bialgebraPullbackTwo_convMul_symmetricCocycle (f.app n) (g.app n) (c.1 n) (c.2 n).1).symm

/- English proof (translation)
The claim follows from `LinearMap.ext fun x => by obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun _ => pullTwo_id _))`.
-/
theorem vecExtMap_id : vecExtMap (𝟙 G) = LinearMap.id :=
  LinearMap.ext fun x => by
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun _ => pullTwo_id _))

/- English proof (translation)
Take `⟨c, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Both sides reduce to the same expression.
-/
theorem SemiHom.ofHom_vecExt (f : G ⟶ H) (x : H.VecExt) :
    (SemiHom.ofHom f).vecExt x = vecExtMap f x := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

variable [Fact p.Prime] (G)

/- English proof (translation)
Establish `h` using `map_nsmul (AddMonoidHom.mk' (vecExtMap (G := G) (H := G)) vecExtMap_add) p (𝟙 G)`. Rewrite `h` using `[← Nat.cast_smul_eq_nsmul ℤ_[p], ← Nat.cast_smul_eq_nsmul R, hp, zero_smul]`. Conclude with `h`.
-/
theorem vecExtMap_natCast_smul_id (hp : (p : R) = 0) : vecExtMap ((p : ℤ_[p]) • 𝟙 G) = 0 := by
  have h := map_nsmul (AddMonoidHom.mk' (vecExtMap (G := G) (H := G)) vecExtMap_add) p (𝟙 G)
  rw [← Nat.cast_smul_eq_nsmul ℤ_[p], ← Nat.cast_smul_eq_nsmul R, hp, zero_smul] at h
  exact h

/- English proof (translation)
Rewrite using `[← natCast_smul_id_app]`. Both sides reduce to the same expression.
-/
theorem cocyclesMap_natCast_val (c : G.cocycles) (n : ℕ) :
    (cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c).1 n = pullbackTwo (mulBy R (G.A n) p) (c.1 n) := by
  rw [← natCast_smul_id_app]; rfl

/- English proof (translation)
Take `⟨c, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Take `⟨B, hB⟩` from `(Submodule.Quotient.mk_eq_zero _).1 (LinearMap.congr_fun (G.vecExtMap_natCast_smul_id hp) (Submodule.Quotient.mk c))`. Set `K : G.funs` to `⟨fun n => algebraMap R _ (counit (B.1 1)), fun n => AlgHomClass.commutes (G.res n) _⟩`. Establish `hK : funsMap ((p : ℤ_[p]) • 𝟙 G) K = K` using `Subtype.ext (funext fun n => AlgHomClass.commutes (Hom.app _ n) _)`. Use `⟨_, c - G.cob K, B - K, (Submodule.Quotient.eq _).2 ⟨-K, by simp⟩, ?_, ?_, rfl⟩` and prove the remaining obligations.

Rewrite using `[map_sub, map_sub, cocyclesMap_cob, hK, hB]`. Express the relevant statement in the definitionally equal form `counit (R := R) (B.1 1 - algebraMap R _ (counit (B.1 1))) = 0`. Rewrite using `[map_sub, counit_algebraMap, sub_self]`.
-/
theorem exists_connecting (hp : (p : R) = 0) (x : G.VecExt) : ∃ b : G.A 1, (∃ (c : G.cocycles) (B : G.funs), Submodule.Quotient.mk c = x ∧
      G.cob B = cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c ∧ Coalgebra.counit (R := R) b = 0 ∧ B.1 1 = b) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨B, hB⟩ := (Submodule.Quotient.mk_eq_zero _).1
    (LinearMap.congr_fun (G.vecExtMap_natCast_smul_id hp) (Submodule.Quotient.mk c))
  let K : G.funs := ⟨fun n => algebraMap R _ (counit (B.1 1)), fun n => AlgHomClass.commutes (G.res n) _⟩
  have hK : funsMap ((p : ℤ_[p]) • 𝟙 G) K = K :=
    Subtype.ext (funext fun n => AlgHomClass.commutes (Hom.app _ n) _)
  refine ⟨_, c - G.cob K, B - K, (Submodule.Quotient.eq _).2 ⟨-K, by simp⟩, ?_, ?_, rfl⟩
  · rw [map_sub, map_sub, cocyclesMap_cob, hK, hB]
  · change counit (R := R) (B.1 1 - algebraMap R _ (counit (B.1 1))) = 0
    rw [map_sub, counit_algebraMap, sub_self]

variable {G}

/- English proof (translation)
Take `⟨c, B, -, h1, h2, rfl⟩` from `h`. Establish `hm : ∀ a : G.A 1, mulBy R _ p a = algebraMap R _ (counit a)` using `G.resOne_mulBy 0`. Establish `h3 : cobOne R _ (B.1 1) = pullbackTwo (mulBy R (G.A 1) p) (c.1 1)` using `(congrArg (fun c : G.cocycles => c.1 1) h1).trans (G.cocyclesMap_natCast_val c 1)`. Establish `h4 : (mulBy R (G.A 1) p).comp (mulBy R (G.A 1) p) = mulBy R (G.A 1) p` using `BialgHom.ext fun a => by rw [BialgHom.comp_apply, hm, hm, counit_algebraMap]`. Rewrite using `[h3, ← h4, pullTwo_comp, ← h3, pullTwo_cobOne, hm, h2, map_zero, map_zero]`.
-/
theorem cobOne_eq_zero_of_connecting {x : G.VecExt} {b : G.A 1} (h : (∃ (c : G.cocycles) (B : G.funs), Submodule.Quotient.mk c = x ∧
      G.cob B = cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c ∧ Coalgebra.counit (R := R) b = 0 ∧ B.1 1 = b)) :
    cobOne R _ b = 0 := by
  obtain ⟨c, B, -, h1, h2, rfl⟩ := h
  have hm : ∀ a : G.A 1, mulBy R _ p a = algebraMap R _ (counit a) := G.resOne_mulBy 0
  have h3 : cobOne R _ (B.1 1) = pullbackTwo (mulBy R (G.A 1) p) (c.1 1) :=
    (congrArg (fun c : G.cocycles => c.1 1) h1).trans (G.cocyclesMap_natCast_val c 1)
  have h4 : (mulBy R (G.A 1) p).comp (mulBy R (G.A 1) p) = mulBy R (G.A 1) p :=
    BialgHom.ext fun a => by rw [BialgHom.comp_apply, hm, hm, counit_algebraMap]
  rw [h3, ← h4, pullTwo_comp, ← h3, pullTwo_cobOne, hm, h2, map_zero, map_zero]

/- English proof (translation)
Take `⟨c, B, rfl, h1, h2, rfl⟩` from `h`. Take `⟨c', B', h0, h1', h2', rfl⟩` from `h'`. Take `⟨D, hD⟩` from `(Submodule.Quotient.eq _).1 h0`. Establish `h3 : B' - B - funsMap ((p : ℤ_[p]) • 𝟙 G) D = 0` using `G.eq_zero_of_cob_eq_zero hp (by`. Rewrite using `[map_sub, map_sub, h1, h1', ← cocyclesMap_cob, hD, map_sub, sub_self])`.

Establish `h4 : B'.1 1 - B.1 1 = algebraMap R _ (counit (D.1 1))`. Rewrite using `[← G.resOne_mulBy 0, resOne_zero, ← natCast_smul_id_app]`. Conclude with `congrArg (fun z : G.funs => z.1 1) (sub_eq_zero.1 h3)`. Establish `h5` using `congrArg (counit (R := R)) h4`. Rewrite `h5` using `[map_sub, h2, h2', sub_zero, counit_algebraMap]`.

Rewrite `h4` using `[← h5, map_zero, sub_eq_zero]`. Conclude with `h4.symm`.
-/
theorem connecting_unique (hp : (p : R) = 0) {x : G.VecExt} {b b' : G.A 1}
    (h : (∃ (c : G.cocycles) (B : G.funs), Submodule.Quotient.mk c = x ∧
      G.cob B = cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c ∧ Coalgebra.counit (R := R) b = 0 ∧ B.1 1 = b))
    (h' : (∃ (c : G.cocycles) (B : G.funs), Submodule.Quotient.mk c = x ∧
      G.cob B = cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c ∧ Coalgebra.counit (R := R) b' = 0 ∧ B.1 1 = b')) : b = b' := by
  obtain ⟨c, B, rfl, h1, h2, rfl⟩ := h
  obtain ⟨c', B', h0, h1', h2', rfl⟩ := h'
  obtain ⟨D, hD⟩ := (Submodule.Quotient.eq _).1 h0
  have h3 : B' - B - funsMap ((p : ℤ_[p]) • 𝟙 G) D = 0 := G.eq_zero_of_cob_eq_zero hp (by
    rw [map_sub, map_sub, h1, h1', ← cocyclesMap_cob, hD, map_sub, sub_self])
  have h4 : B'.1 1 - B.1 1 = algebraMap R _ (counit (D.1 1)) := by
    rw [← G.resOne_mulBy 0, resOne_zero, ← natCast_smul_id_app]
    exact congrArg (fun z : G.funs => z.1 1) (sub_eq_zero.1 h3)
  have h5 := congrArg (counit (R := R)) h4
  rw [map_sub, h2, h2', sub_zero, counit_algebraMap] at h5
  rw [← h5, map_zero, sub_eq_zero] at h4
  exact h4.symm

/- English proof (translation)
Take `⟨B, hB, hB'⟩` from `T.exists_extension_additive_fn_pDivGroup G b hb`. Use `choose c hc using fun n => T.exists_pullback_mulP_of_pTorsion_invariant G n _ (T.coboundary_translation_invariant_pTorsion G n _ b (hB' n)).1 (T.coboundary_translation_invariant_pTorsion G n _ b (hB' n)).2`. Establish `h1 : ∀ n, pullbackTwo (G.res n) (c (n + 1)) = c n` using `fun n => G.pullbackTwo_mulP_injective n (by`. Rewrite using `[← pullTwo_comp, mulP_comp_res, ← res_comp_mulP, pullTwo_comp, hc, hc, pullTwo_cobOne, B.2])`. Set `c' : G.cocycles` to `⟨c, fun n => ⟨T.mem_symmetricCocycles_of_pullback_mulP G n _ (hc n ▸ cobOne_mem _), h1 n⟩⟩`.

Establish `h2 : ∀ n, (G.cob B).1 (n + 1) = (cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c').1 (n + 1)` using `fun n => by`. Rewrite using `[cocyclesMap_natCast_val, ← mulP_comp_res, pullTwo_comp]`. Conclude with `(hc n).symm.trans (congrArg _ (h1 n).symm)`. Use `⟨_, c', B, rfl, Subtype.ext (funext fun n => ?_), (mulBy_of_cobOne_eq_zero hb 0).2, hB⟩` and prove the remaining obligations. Rewrite using `[← ((G.cob B).2 n).2, h2, ((cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c').2 n).2]`.
-/
theorem exists_of_cobOne_eq_zero {b : G.A 1} (hb : cobOne R _ b = 0) :
    ∃ x : G.VecExt, (∃ (c : G.cocycles) (B : G.funs), Submodule.Quotient.mk c = x ∧
      G.cob B = cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c ∧ Coalgebra.counit (R := R) b = 0 ∧ B.1 1 = b) := by
  obtain ⟨B, hB, hB'⟩ := T.exists_extension_additive_fn_pDivGroup G b hb
  choose c hc using fun n => T.exists_pullback_mulP_of_pTorsion_invariant G n _ (T.coboundary_translation_invariant_pTorsion G n _ b (hB' n)).1 (T.coboundary_translation_invariant_pTorsion G n _ b (hB' n)).2
  have h1 : ∀ n, pullbackTwo (G.res n) (c (n + 1)) = c n := fun n => G.pullbackTwo_mulP_injective n (by
    rw [← pullTwo_comp, mulP_comp_res, ← res_comp_mulP, pullTwo_comp, hc, hc, pullTwo_cobOne, B.2])
  let c' : G.cocycles := ⟨c, fun n => ⟨T.mem_symmetricCocycles_of_pullback_mulP G n _ (hc n ▸ cobOne_mem _), h1 n⟩⟩
  have h2 : ∀ n, (G.cob B).1 (n + 1) = (cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c').1 (n + 1) := fun n => by
    rw [cocyclesMap_natCast_val, ← mulP_comp_res, pullTwo_comp]
    exact (hc n).symm.trans (congrArg _ (h1 n).symm)
  refine ⟨_, c', B, rfl, Subtype.ext (funext fun n => ?_), (mulBy_of_cobOne_eq_zero hb 0).2, hB⟩
  rw [← ((G.cob B).2 n).2, h2, ((cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c').2 n).2]

variable (G)

def extChar (hp : (p : R) = 0) : G.VecExt →ₗ[R] LinearMap.ker (cobOne R (G.A 1)) where
  toFun x := ⟨(G.exists_connecting hp x).choose,
    cobOne_eq_zero_of_connecting (G.exists_connecting hp x).choose_spec⟩
  map_add' x y := Subtype.ext (connecting_unique hp (G.exists_connecting hp _).choose_spec (by
    obtain ⟨c, B, h0, h1, h2, h3⟩ := (G.exists_connecting hp x).choose_spec
    obtain ⟨c', B', h0', h1', h2', h3'⟩ := (G.exists_connecting hp y).choose_spec
    refine ⟨c + c', B + B', by rw [← h0, ← h0']; rfl, by rw [map_add, map_add, h1, h1'], ?_,
      congrArg₂ (· + ·) h3 h3'⟩
    exact (map_add _ _ _).trans (by rw [h2, h2', add_zero])))
  map_smul' r x := Subtype.ext (connecting_unique hp (G.exists_connecting hp _).choose_spec (by
    obtain ⟨c, B, h0, h1, h2, h3⟩ := (G.exists_connecting hp x).choose_spec
    refine ⟨r • c, r • B, by rw [← h0]; rfl, by rw [map_smul, map_smul, h1], ?_,
      congrArg (r • ·) h3⟩
    exact (map_smul _ _ _).trans (by rw [h2, smul_zero])))

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => h ▸ (G.exists_connecting hp x).choose_spec, connecting_unique hp (G.exists_connecting hp x).choose_spec⟩`.
-/
theorem extChar_eq_iff (hp : (p : R) = 0) (x : G.VecExt) (b : G.A 1) :
    (G.extChar hp x).1 = b ↔ (∃ (c : G.cocycles) (B : G.funs), Submodule.Quotient.mk c = x ∧
      G.cob B = cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c ∧ Coalgebra.counit (R := R) b = 0 ∧ B.1 1 = b) :=
  ⟨fun h => h ▸ (G.exists_connecting hp x).choose_spec,
    connecting_unique hp (G.exists_connecting hp x).choose_spec⟩

/- English proof (translation)
Use `⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun b => ?_⟩` and prove the remaining obligations. Take `⟨c, B, rfl, h1, -, h3⟩` from `(G.extChar_eq_iff hp x 0).1 (congrArg Subtype.val hx)`. Conclude with `(Submodule.Quotient.mk_eq_zero _).2 (T.pDivCocycle_mem_range_cob_of_pullback_mulP G c B h1 h3)`. Take `⟨x, hx⟩` from `exists_of_cobOne_eq_zero b.2`. Conclude with `⟨x, Subtype.ext ((G.extChar_eq_iff hp x _).2 hx)⟩`.
-/
theorem extChar_bijective (hp : (p : R) = 0) : Function.Bijective (G.extChar hp) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun b => ?_⟩
  · obtain ⟨c, B, rfl, h1, -, h3⟩ := (G.extChar_eq_iff hp x 0).1 (congrArg Subtype.val hx)
    exact (Submodule.Quotient.mk_eq_zero _).2 (T.pDivCocycle_mem_range_cob_of_pullback_mulP G c B h1 h3)
  · obtain ⟨x, hx⟩ := exists_of_cobOne_eq_zero b.2
    exact ⟨x, Subtype.ext ((G.extChar_eq_iff hp x _).2 hx)⟩

def extCharEquiv (hp : (p : R) = 0) : G.VecExt ≃ₗ[R] LinearMap.ker (cobOne R (G.A 1)) :=
  LinearEquiv.ofBijective _ (G.extChar_bijective hp)

variable {G}

/- English proof (translation)
Take `⟨c, B, rfl, h1, h2, rfl⟩` from `h`. Use `⟨s.cocycles c, s.funs B, rfl, ?_, by rw [(s.app 1).counit_map, h2, map_zero], rfl⟩` and prove the remaining obligations. Rewrite using `[← s.cocycles_cob, h1]`. Use `Subtype.ext (funext fun n => ?_)` and prove the remaining obligations. Rewrite using `[SemiHom.cocycles_val, cocyclesMap_natCast_val, cocyclesMap_natCast_val, SemiHom.cocycles_val]`.

Generalize the expression as in `c.1 n = t`. Proceed by induction on `t with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul x y => simp [SemiBialgHom.map_mulBy]`.
-/
theorem SemiHom.connecting {σ : R →+* R'} {G' : PDivGroup p R'} (s : SemiHom σ G' G)
    {x : G.VecExt} {b : G.A 1} (h : (∃ (c : G.cocycles) (B : G.funs), Submodule.Quotient.mk c = x ∧
      G.cob B = cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c ∧ Coalgebra.counit (R := R) b = 0 ∧ B.1 1 = b)) :
    (∃ (c : G'.cocycles) (B : G'.funs), Submodule.Quotient.mk c = s.vecExt x ∧
      G'.cob B = cocyclesMap ((p : ℤ_[p]) • 𝟙 G') c ∧ Coalgebra.counit (R := R') (s.app 1 b) = 0 ∧ B.1 1 = (s.app 1 b)) := by
  obtain ⟨c, B, rfl, h1, h2, rfl⟩ := h
  refine ⟨s.cocycles c, s.funs B, rfl, ?_, by rw [(s.app 1).counit_map, h2, map_zero], rfl⟩
  rw [← s.cocycles_cob, h1]
  refine Subtype.ext (funext fun n => ?_)
  rw [SemiHom.cocycles_val, cocyclesMap_natCast_val, cocyclesMap_natCast_val, SemiHom.cocycles_val]
  generalize c.1 n = t
  induction t with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp [SemiBialgHom.map_mulBy]

/- English proof (translation)
The claim follows from `Subtype.ext ((G'.extChar_eq_iff hp' _ _).2 (s.connecting ((G.extChar_eq_iff hp x _).1 rfl)))`.
-/
theorem SemiHom.extChar_vecExt {σ : R →+* R'} {G' : PDivGroup p R'} (s : SemiHom σ G' G)
    (hp : (p : R) = 0) (hp' : (p : R') = 0) (x : G.VecExt) :
    G'.extChar hp' (s.vecExt x) = (s.app 1).prim (G.extChar hp x) :=
  Subtype.ext ((G'.extChar_eq_iff hp' _ _).2 (s.connecting ((G.extChar_eq_iff hp x _).1 rfl)))

/- English proof (translation)
Rewrite using `[← SemiHom.ofHom_vecExt, SemiHom.extChar_vecExt _ hp]`. Both sides reduce to the same expression.
-/
theorem extChar_vecExtMap (hp : (p : R) = 0) (f : G ⟶ H) (x : H.VecExt) :
    (G.extChar hp (vecExtMap f x)).1 = f.app 1 (H.extChar hp x).1 := by
  rw [← SemiHom.ofHom_vecExt, SemiHom.extChar_vecExt _ hp]
  rfl

omit [Fact p.Prime] in
variable (G) in

/- English proof (translation)
The claim follows from `(LinearEquiv.ofBijective _ (G.dual.omegaLevel_one_bijective hp)).dualMap.bijective.comp T.additiveFunctionCartierDualTangent_bijective`.
-/
theorem primLie_bijective (hp : (p : R) = 0) : Function.Bijective G.primLie :=
  (LinearEquiv.ofBijective _ (G.dual.omegaLevel_one_bijective hp)).dualMap.bijective.comp T.additiveFunctionCartierDualTangent_bijective

/- English proof (translation)
The claim follows from `LinearMap.ext fun w => by obtain ⟨φ, hφ⟩ := AugCot.d_surjective _ (w.1 1) rw [G.primLie_apply b' w φ hφ.symm, lieMap_apply, H.primLie_apply b _ (CartierDual.map (f.app 1) φ) (by rw [omegaMap_val, ← hφ]; exact cotMap_d _ _), h] rfl`.
-/
theorem primLie_naturality (f : G ⟶ H) (b : LinearMap.ker (cobOne R (H.A 1)))
    (b' : LinearMap.ker (cobOne R (G.A 1))) (h : b'.1 = f.app 1 b.1) :
    G.primLie b' = lieMap H.dual G.dual (dualHom G H f) (H.primLie b) :=
  LinearMap.ext fun w => by
    obtain ⟨φ, hφ⟩ := AugCot.d_surjective _ (w.1 1)
    rw [G.primLie_apply b' w φ hφ.symm, lieMap_apply,
      H.primLie_apply b _ (CartierDual.map (f.app 1) φ) (by rw [omegaMap_val, ← hφ]; exact cotMap_d _ _), h]
    rfl

omit [Fact p.Prime] in

/- English proof (translation)
Take `⟨φ, hφ⟩` from `AugCot.d_surjective _ (w.1 1)`. Rewrite using `[G.primLie_apply b w φ hφ.symm, G'.primLie_apply _ _ (t.app 1 φ) (by rw [SemiHom.omega_val, ← hφ]; exact SemiBialgHom.cot_d _ _)]`. Conclude with `h φ b.1`.
-/
theorem SemiHom.primLie_prim {σ : R →+* R'} {G' : PDivGroup p R'} (s : SemiHom σ G' G)
    (t : SemiHom σ G'.dual G.dual)
    (h : ∀ (φ : CartierDual R (G.A 1)) (a : G.A 1),
      (show CartierDual R' (G'.A 1) from t.app 1 φ) (s.app 1 a) = σ (φ a))
    (b : LinearMap.ker (cobOne R (G.A 1))) (w : G.dual.omega) :
    G'.primLie ((s.app 1).prim b) (t.omega w) = σ (G.primLie b w) := by
  obtain ⟨φ, hφ⟩ := AugCot.d_surjective _ (w.1 1)
  rw [G.primLie_apply b w φ hφ.symm, G'.primLie_apply _ _ (t.app 1 φ)
    (by rw [SemiHom.omega_val, ← hφ]; exact SemiBialgHom.cot_d _ _)]
  exact h φ b.1

variable (G) in

/- English proof (translation)
Set `t` to `(semiHomEquiv G.dual (G.baseChange R').dual).symm (PerfdLat.dualBaseChange R' G).hom`. Set `s : SemiHom (algebraMap R R') (G.baseChange R').dual G.dual` to `t`. Rewrite using `[← SemiHom.ofHom_omega, (G.dual.toBase R').omega_omega _ s fun _ _ => rfl]`. Use `SemiHom.primLie_prim _ s (fun φ a => ?_) b w` and prove the remaining obligations. Use `(CartierDual.baseChange_tmul_tmul R' 1 1 φ a).trans ?_` and prove the remaining obligations.

Rewrite using `[mul_one, Algebra.algebraMap_eq_smul_one]`.
-/
theorem primLie_toBase [Algebra R R'] (b : LinearMap.ker (cobOne R (G.A 1))) (w : G.dual.omega) :
    (G.baseChange R').primLie (((G.toBase R').app 1).prim b)
      (omegaMap _ _ (PerfdLat.dualBaseChange R' G).hom ((G.dual.toBase R').omega w)) =
      algebraMap R R' (G.primLie b w) := by
  let t := (semiHomEquiv G.dual (G.baseChange R').dual).symm (PerfdLat.dualBaseChange R' G).hom
  let s : SemiHom (algebraMap R R') (G.baseChange R').dual G.dual := t
  rw [← SemiHom.ofHom_omega, (G.dual.toBase R').omega_omega _ s fun _ _ => rfl]
  refine SemiHom.primLie_prim _ s (fun φ a => ?_) b w
  refine (CartierDual.baseChange_tmul_tmul R' 1 1 φ a).trans ?_
  rw [mul_one, Algebra.algebraMap_eq_smul_one]

variable (G) in

def rigToLie (hp : (p : R) = 0) : G.RigExt →ₗ[R] G.dual.Lie :=
  G.primLie ∘ₗ G.extChar hp ∘ₗ G.rigToExt

variable (G) in

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rigToLie_apply (hp : (p : R) = 0) (x : G.RigExt) :
    G.rigToLie hp x = G.primLie (G.extChar hp (G.rigToExt x)) := rfl

variable (G) in

/- English proof (translation)
The claim follows from `(G.primLie_bijective hp).2.comp ((G.extChar_bijective hp).2.comp G.rigToExt_surjective)`.
-/
theorem rigToLie_surjective (hp : (p : R) = 0) : Function.Surjective (G.rigToLie hp) :=
  (G.primLie_bijective hp).2.comp ((G.extChar_bijective hp).2.comp G.rigToExt_surjective)

variable (G) in

/- English proof (translation)
Introduce `x` and use `by rw [← G.exact_rigOfOmega_rigToExt x, rigToLie_apply, map_eq_zero_iff _ (G.primLie_bijective hp).1, map_eq_zero_iff _ (G.extChar_bijective hp).1]`.
-/
theorem exact_rigOfOmega_rigToLie (hp : (p : R) = 0) :
    Function.Exact G.rigOfOmega (G.rigToLie hp) := fun x => by
  rw [← G.exact_rigOfOmega_rigToExt x, rigToLie_apply,
    map_eq_zero_iff _ (G.primLie_bijective hp).1, map_eq_zero_iff _ (G.extChar_bijective hp).1]

/- English proof (translation)
Rewrite using `[rigToLie_apply, rigToExt_rigExtMap]`. Conclude with `primLie_naturality f _ _ (extChar_vecExtMap hp f _)`.
-/
theorem rigToLie_rigExtMap (hp : (p : R) = 0) (f : G ⟶ H) (x : H.RigExt) :
    G.rigToLie hp (rigExtMap f x) = lieMap H.dual G.dual (dualHom G H f) (H.rigToLie hp x) := by
  rw [rigToLie_apply, rigToExt_rigExtMap]
  exact primLie_naturality f _ _ (extChar_vecExtMap hp f _)

section BaseChange

variable (G R') [Algebra R R']

omit [Fact p.Prime] in

/- English proof (translation)
Break down `h with h | h` into its components or cases. Conclude with `T.additiveFunctions_flatBaseChange_bijective R'`. Conclude with `T.primitive_semilinearLift_baseChange_bijective R' (.of_equiv (LinearEquiv.ofBijective _ (G.dual.omegaLevel_one_bijective hp)))`.
-/
theorem liftSemi_prim_bijective (hp : (p : R) = 0)
    (h : Module.Flat R R' ∨ Module.Projective R G.dual.omega) :
    Function.Bijective (liftSemi ((G.toBase R').app 1).prim) := by
  rcases h with h | h
  · exact T.additiveFunctions_flatBaseChange_bijective R'
  · exact T.primitive_semilinearLift_baseChange_bijective R'
      (.of_equiv (LinearEquiv.ofBijective _ (G.dual.omegaLevel_one_bijective hp)))

/- English proof (translation)
Establish `hp' : (p : R') = 0` using `by rw [← map_natCast (algebraMap R R'), hp, map_zero]`. Establish `e : ((G.baseChange R').extChar hp') ∘ (liftSemi (G.toBase R').vecExt) = liftSemi ((G.toBase R').app 1).prim ∘ (G.extCharEquiv hp).baseChange R R' _ _`. Use function extensionality and compare the values at `fun x => by`. Proceed by induction on `x with`. Consider the case `zero => simp`.

Consider the case `add x y hx hy => simpa only [Function.comp_apply, map_add] using congrArg₂ (· + ·) hx hy`. Consider the case `tmul r x`. Simplify using `only [Function.comp_apply, liftSemi_tmul, map_smul, LinearEquiv.baseChange_tmul, SemiHom.extChar_vecExt _ hp]`. Both sides reduce to the same expression. Rewrite using `[← Function.Bijective.of_comp_iff' ((G.baseChange R').extChar_bijective hp'), e]`.

Conclude with `(G.liftSemi_prim_bijective R' hp h).comp (LinearEquiv.bijective _)`.
-/
theorem liftSemi_vecExt_bijective (hp : (p : R) = 0)
    (h : Module.Flat R R' ∨ Module.Projective R G.dual.omega) :
    Function.Bijective (liftSemi (G.toBase R').vecExt) := by
  have hp' : (p : R') = 0 := by rw [← map_natCast (algebraMap R R'), hp, map_zero]
  have e : ((G.baseChange R').extChar hp') ∘ (liftSemi (G.toBase R').vecExt) =
      liftSemi ((G.toBase R').app 1).prim ∘ (G.extCharEquiv hp).baseChange R R' _ _ :=
    funext fun x => by
      induction x with
      | zero => simp
      | add x y hx hy => simpa only [Function.comp_apply, map_add] using congrArg₂ (· + ·) hx hy
      | tmul r x =>
        simp only [Function.comp_apply, liftSemi_tmul, map_smul, LinearEquiv.baseChange_tmul,
          SemiHom.extChar_vecExt _ hp]
        rfl
  rw [← Function.Bijective.of_comp_iff' ((G.baseChange R').extChar_bijective hp'), e]
  exact (G.liftSemi_prim_bijective R' hp h).comp (LinearEquiv.bijective _)

/- English proof (translation)
Establish `hp' : (p : R') = 0` using `by rw [← map_natCast (algebraMap R R'), hp, map_zero]`. Establish `h1` using `T.omega_baseChange_bijective_of_p_eq_zero G R' hp`. Establish `h3` using `G.liftSemi_vecExt_bijective R' hp h`. Establish `s1 : ∀ y, liftSemi (G.toBase R').rig (G.rigOfOmega.lTensor R' y) = (G.baseChange R').rigOfOmega (liftSemi (G.toBase R').omega y)` using `fun y => by`. Proceed by induction on `y with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul r x => simp [SemiHom.rig_rigOfOmega]`. Establish `s2 : ∀ y, (G.baseChange R').rigToExt (liftSemi (G.toBase R').rig y) = liftSemi (G.toBase R').vecExt (G.rigToExt.lTensor R' y)` using `fun y => by`. Proceed by induction on `y with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul r x => simp [SemiHom.rigToExt_rig]`. Use `⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun z => ?_⟩` and prove the remaining obligations. Establish `k` using `s2 x`.

Rewrite `k` using `[hx, map_zero, eq_comm, map_eq_zero_iff _ h3.1]`. Take `⟨y, rfl⟩` from `(lTensor_exact R' G.exact_rigOfOmega_rigToExt G.rigToExt_surjective x).1 k`. Rewrite `hx` using `[s1, map_eq_zero_iff _ ((G.baseChange R').rigOfOmega_injective_of_eq_zero hp'), map_eq_zero_iff _ h1.1]`. Rewrite using `[hx, map_zero]`. Take `⟨u, hu⟩` from `h3.2 ((G.baseChange R').rigToExt z)`.

Take `⟨x, rfl⟩` from `LinearMap.lTensor_surjective R' G.rigToExt_surjective u`. Take `⟨w, hw⟩` from `((G.baseChange R').exact_rigOfOmega_rigToExt (z - liftSemi (G.toBase R').rig x)).1 (by rw [map_sub, s2, hu, sub_self])`. Take `⟨y, rfl⟩` from `h1.2 w`. Use `⟨x + G.rigOfOmega.lTensor R' y, (map_add _ _ _).trans ?_⟩` and prove the remaining obligations. Conclude with `(congrArg (_ + ·) ((s1 y).trans hw)).trans (add_sub_cancel _ _)`.
-/
theorem liftSemi_rig_bijective (hp : (p : R) = 0)
    (h : Module.Flat R R' ∨ Module.Projective R G.dual.omega) :
    Function.Bijective (liftSemi (G.toBase R').rig) := by
  have hp' : (p : R') = 0 := by rw [← map_natCast (algebraMap R R'), hp, map_zero]
  have h1 := T.omega_baseChange_bijective_of_p_eq_zero G R' hp
  have h3 := G.liftSemi_vecExt_bijective R' hp h
  have s1 : ∀ y, liftSemi (G.toBase R').rig (G.rigOfOmega.lTensor R' y) =
      (G.baseChange R').rigOfOmega (liftSemi (G.toBase R').omega y) := fun y => by
    induction y with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r x => simp [SemiHom.rig_rigOfOmega]
  have s2 : ∀ y, (G.baseChange R').rigToExt (liftSemi (G.toBase R').rig y) =
      liftSemi (G.toBase R').vecExt (G.rigToExt.lTensor R' y) := fun y => by
    induction y with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r x => simp [SemiHom.rigToExt_rig]
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun z => ?_⟩
  · have k := s2 x
    rw [hx, map_zero, eq_comm, map_eq_zero_iff _ h3.1] at k
    obtain ⟨y, rfl⟩ := (lTensor_exact R' G.exact_rigOfOmega_rigToExt G.rigToExt_surjective x).1 k
    rw [s1, map_eq_zero_iff _ ((G.baseChange R').rigOfOmega_injective_of_eq_zero hp'),
      map_eq_zero_iff _ h1.1] at hx
    rw [hx, map_zero]
  · obtain ⟨u, hu⟩ := h3.2 ((G.baseChange R').rigToExt z)
    obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective R' G.rigToExt_surjective u
    obtain ⟨w, hw⟩ := ((G.baseChange R').exact_rigOfOmega_rigToExt
      (z - liftSemi (G.toBase R').rig x)).1 (by rw [map_sub, s2, hu, sub_self])
    obtain ⟨y, rfl⟩ := h1.2 w
    refine ⟨x + G.rigOfOmega.lTensor R' y, (map_add _ _ _).trans ?_⟩
    exact (congrArg (_ + ·) ((s1 y).trans hw)).trans (add_sub_cancel _ _)

end BaseChange

end PDivGroup

end GlobalTheory

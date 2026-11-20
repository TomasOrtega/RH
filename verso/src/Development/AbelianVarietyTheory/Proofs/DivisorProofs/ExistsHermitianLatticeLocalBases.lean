import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TripleSpaceW

open scoped ComplexOrder

/- English proof (translation)
Take `⟨e, P, hP⟩` from `h`. Use `⟨by simpa using (Fintype.card_congr e).symm, (P.1.submatrix e id).map star, ?_⟩` and prove the remaining obligations. Establish `hJ : (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Formalism.UG.Jpq p q` using `rfl`. Rewrite using `[hJ, ← hP]`. Use extensionality with `k l`.

Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, id, Formalism.UG.cT, Matrix.reindex_apply, star_star]`. Rewrite using `[← e.symm.sum_comp]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[← e.symm.sum_comp]`.

Conclude with `Finset.sum_congr rfl fun i _ => by rw [e.apply_symm_apply]; rfl`. Rewrite using `[e.apply_symm_apply]`.
-/
theorem hasSig_of_hasSignature {n p q : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature M p q) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig M p q := by
  obtain ⟨e, P, hP⟩ := h
  refine ⟨by simpa using (Fintype.card_congr e).symm, (P.1.submatrix e id).map star, ?_⟩
  have hJ : (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Formalism.UG.Jpq p q := rfl
  rw [hJ, ← hP]
  ext k l
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, id, Formalism.UG.cT,
    Matrix.reindex_apply, star_star]
  rw [← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  · rw [← e.symm.sum_comp]
    exact Finset.sum_congr rfl fun i _ => by rw [e.apply_symm_apply]; rfl
  · rw [e.apply_symm_apply]

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Use `⟨h1, ?_, fun x hx => ?_⟩` and prove the remaining obligations. Use `congrArg (fun A : Matrix (Fin k) (Fin k) ℂ => A.map (starRingEnd ℂ)) h2` as an intermediate fact. Simplify using `only [Matrix.map_mul] at this`. Rewrite using `[← this]`.

Use `congr 2`. Use extensionality with `a b`. Simplify using `[Matrix.conjTranspose_apply]`. Establish `hsG : sᴴ * G = G * s`. Combine the equalities or inequalities in the displayed calculation.

Establish `e1 : (s *ᵥ x) ⬝ᵥ G.map (starRingEnd ℂ) *ᵥ star x = star (star x ⬝ᵥ (G * s) *ᵥ x)`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use extensionality with `a`. Simplify using `[Matrix.mulVec, dotProduct, star_sum]`.

Use `_ = star (star (s *ᵥ x) ⬝ᵥ G *ᵥ x) := by rw [Matrix.star_dotProduct, star_star, dotProduct_comm]`. Use `_ = star (star x ⬝ᵥ (G * s) *ᵥ x) := by`. Rewrite using `[← hsG, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (star x) sᴴ, ← Matrix.star_mulVec]`. Use `h3.dotProduct_mulVec_pos hx` as an intermediate fact. Rewrite using `[e1, Complex.star_def, Complex.conj_re]`.

Conclude with `(Complex.lt_def.1 this).1`.
-/
theorem isCartan_map_conj {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (G.map (starRingEnd ℂ)) s := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, fun x hx => ?_⟩
  · have := congrArg (fun A : Matrix (Fin k) (Fin k) ℂ => A.map (starRingEnd ℂ)) h2
    simp only [Matrix.map_mul] at this
    rw [← this]
    congr 2
    ext a b
    simp [Matrix.conjTranspose_apply]
  · have hsG : sᴴ * G = G * s := by
      calc sᴴ * G = sᴴ * G * (s * s) := by rw [h1, Matrix.mul_one]
        _ = G * s := by rw [← Matrix.mul_assoc, h2]
    have e1 : (s *ᵥ x) ⬝ᵥ G.map (starRingEnd ℂ) *ᵥ star x = star (star x ⬝ᵥ (G * s) *ᵥ x) := by
      calc (s *ᵥ x) ⬝ᵥ G.map (starRingEnd ℂ) *ᵥ star x = (s *ᵥ x) ⬝ᵥ star (G *ᵥ x) := by
            congr 1; ext a; simp [Matrix.mulVec, dotProduct, star_sum]
        _ = star (star (s *ᵥ x) ⬝ᵥ G *ᵥ x) := by rw [Matrix.star_dotProduct, star_star, dotProduct_comm]
        _ = star (star x ⬝ᵥ (G * s) *ᵥ x) := by
            rw [← hsG, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (star x) sᴴ, ← Matrix.star_mulVec]
    have := h3.dotProduct_mulVec_pos hx
    rw [e1, Complex.star_def, Complex.conj_re]
    exact (Complex.lt_def.1 this).1

section ConjLat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def conjO (r : 𝓞 E) : 𝓞 E := ⟨star (r : E), (RingOfIntegers.isIntegral_coe r).map (starRingEnd E).toIntAlgHom⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_conjO (r : 𝓞 E) : ((conjO r : 𝓞 E) : E) = star (r : E) := rfl

/- English proof (translation)
Use extensionality with `i`. Simplify using `only [Pi.star_apply, Pi.smul_apply, Algebra.smul_def, star_mul']`. Both sides reduce to the same expression.
-/
theorem star_smulO (r : 𝓞 E) (y : Fin n → E) : star (r • y) = conjO r • star y := by
  ext i
  simp only [Pi.star_apply, Pi.smul_apply, Algebra.smul_def, star_mul']
  rfl

def conjSub (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) where
  carrier := {y | star y ∈ Λ}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, star_add] at ha hb ⊢; exact Λ.add_mem ha hb
  zero_mem' := by simp only [Set.mem_setOf_eq, star_zero]; exact Λ.zero_mem
  smul_mem' := fun r y hy => by
    have e : star (r • y) = conjO r • star y := star_smulO r y
    simp only [Set.mem_setOf_eq] at hy ⊢
    rw [e]; exact Λ.smul_mem _ hy

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_conjSub {Λ : Submodule (𝓞 E) (Fin n → E)} {y : Fin n → E} : y ∈ conjSub Λ ↔ star y ∈ Λ := Iff.rfl

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x h => exact Submodule.subset_span ⟨x, h, rfl⟩`. Consider the case `zero => rw [star_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x z _ _ hx hz => rw [star_add]`.

Conclude with `Submodule.add_mem _ hx hz`. Consider the case `smul a x _ hx => rw [hc]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem star_mem_span {R : Type} [CommRing R] [Module R (Fin n → E)] (c : R → R)
    (hc : ∀ (r : R) (y : Fin n → E), star (r • y) = c r • star y) {s : Set (Fin n → E)} {y : Fin n → E}
    (hy : y ∈ Submodule.span R s) : star y ∈ Submodule.span R (star '' s) := by
  induction hy using Submodule.span_induction with
  | mem x h => exact Submodule.subset_span ⟨x, h, rfl⟩
  | zero => rw [star_zero]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [star_add]; exact Submodule.add_mem _ hx hz
  | smul a x _ hx => rw [hc]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Use extensionality with `i`. Simplify using `[star_mul']`.
-/
theorem star_smulE (r : E) (y : Fin n → E) : star (r • y) = star r • star y := by
  ext i; simp [star_mul']

/- English proof (translation)
Take `⟨S, hS⟩` from `h.fg`. Establish `e : conjSub Λ = Submodule.span (𝓞 E) (star '' (S : Set (Fin n → E)))`. Use `le_antisymm (fun y hy => ?_) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Use `star_mem_span conjO star_smulO (hS ▸ (mem_conjSub.1 hy))` as an intermediate fact. Rewrite `this` using `[star_star]`. Then use the resulting hypothesis.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite using `[SetLike.mem_coe, mem_conjSub, star_star, ← hS]`. Conclude with `Submodule.subset_span hx`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e, Submodule.fg_def]`.

Conclude with `⟨_, S.finite_toSet.image _, rfl⟩`. Use `eq_top_iff.2 fun v _ => ?_` and prove the remaining obligations. Establish `hv : star v ∈ Submodule.span E (Λ : Set (Fin n → E))` using `h.span_eq_top ▸ Submodule.mem_top`. Use `star_mem_span star star_smulE hv` as an intermediate fact. Rewrite `this` using `[star_star]`.

Use `Submodule.span_mono ?_ this` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite using `[SetLike.mem_coe, mem_conjSub, star_star]`. Conclude with `hx`.
-/
theorem conjSub_isLattice {Λ : Submodule (𝓞 E) (Fin n → E)} (h : Λ.IsLattice E) : (conjSub Λ).IsLattice E := by
  obtain ⟨S, hS⟩ := h.fg
  have e : conjSub Λ = Submodule.span (𝓞 E) (star '' (S : Set (Fin n → E))) := by
    refine le_antisymm (fun y hy => ?_) (Submodule.span_le.2 ?_)
    · have := star_mem_span conjO star_smulO (hS ▸ (mem_conjSub.1 hy))
      rwa [star_star] at this
    · rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, mem_conjSub, star_star, ← hS]
      exact Submodule.subset_span hx
  refine ⟨?_, ?_⟩
  · rw [e, Submodule.fg_def]
    exact ⟨_, S.finite_toSet.image _, rfl⟩
  · refine eq_top_iff.2 fun v _ => ?_
    have hv : star v ∈ Submodule.span E (Λ : Set (Fin n → E)) := h.span_eq_top ▸ Submodule.mem_top
    have := star_mem_span star star_smulE hv
    rw [star_star] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_conjSub, star_star]
    exact hx

/- English proof (translation)
Use `⟨fun ⟨b, hb⟩ => hb ▸ (RingOfIntegers.isIntegral_coe b).map (starRingEnd E).toIntAlgHom, fun h => ?_⟩` and prove the remaining obligations. Establish `h' : IsIntegral ℤ z` using `by simpa [starRingEnd_apply] using h.map (starRingEnd E).toIntAlgHom`. Conclude with `⟨⟨z, h'⟩, rfl⟩`.
-/
theorem exists_coe_iff (z : E) : (∃ b : 𝓞 E, (b : E) = z) ↔ IsIntegral ℤ (star z) := by
  refine ⟨fun ⟨b, hb⟩ => hb ▸ (RingOfIntegers.isIntegral_coe b).map (starRingEnd E).toIntAlgHom, fun h => ?_⟩
  have h' : IsIntegral ℤ z := by simpa [starRingEnd_apply] using h.map (starRingEnd E).toIntAlgHom
  exact ⟨⟨z, h'⟩, rfl⟩

end ConjLat

end GlobalTheory.TripleSpaceW

namespace GlobalTheory.FunObj

/- English proof (translation)
Introduce `D T L sc G μ₀ hL W i j B τf hemb`. Establish `hX : (Node.grid ((i : ℕ) + 1) ((j : ℕ) + 1)).InRange D.R.m` using `⟨i.2, j.2⟩`. Establish `hV` using `node_isV G hL hX`. Use `haveI hlat : (GlobalTheory.TripleSpaceW.conjSub (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)))).IsLattice D.host.E := GlobalTheory.TripleSpaceW.conjSub_isLattice hV.sd.1`. Use `choose bas0 hbas0 using fun v : B.P => GlobalTheory.AdelicU.exists_isSplitBasis (B.τ v) (GlobalTheory.TripleSpaceW.conjSub (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)))) (GlobalTheory.AdelicU.isCMExt_host D)`.

Establish `hq : Node.neg D.R.m (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)) = (D.R.m - j - 1) / 2` using `by show (D.R.m - ((j : ℕ) + 1)) / 2 = _`. Rewrite using `[Nat.sub_sub]`. Establish `hherm : ∀ a b, star ((spW G i j).gram b a) = (spW G i j).gram a b` using `fun a b => (spW G i j).herm.eq ((spW G i j).frame b) ((spW G i j).frame a)`. Use `⟨GlobalTheory.TripleSpaceW.conjSub (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))), fun v => if h : v ∈ B.P then bas0 ⟨v, h⟩ else 1, ⟨fun a b => ?_, fun w => ?_, hlat, fun y => ?_, fun w => ?_, fun v => ?_⟩⟩` and prove the remaining obligations. Use `show star (((1 : D.host.E) • (spW G i j).gram) b a) = ((1 : D.host.E) • (spW G i j).gram) a b`.

Rewrite using `[one_smul]`. Conclude with `hherm a b`. Use `show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (((1 : D.host.E) • (spW G i j).gram).map (B.emb w).1) _ _`. Establish `hs` using `hV.sigOK (B.emb w).1`. Rewrite `hs` using `[hV.sig, hq, ← hV.rank]`.

Rewrite using `[one_smul]`. Conclude with `GlobalTheory.TripleSpaceW.hasSig_of_hasSignature hs`. Establish `hσ : ∀ z : D.host.E, D.sp.cm.sig z = star z` using `fun _ => rfl`. Establish `hh' : ∀ a b, star ((spW G i j).gram a b) = (spW G i j).gram b a` using `fun a b => hherm b a`. Establish `key : ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig ((1 : D.host.E) • (spW G i j).gram) y x = star (∑ a, ∑ b, star ((star x) a) * (spW G i j).gram a b * (star y) b)` using `fun x => by`.

Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, one_smul, dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, Pi.star_apply, hσ, hh', Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `show star y ∈ G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ↔ _`.

Rewrite using `[hV.sd.2 (star y)]`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Rewrite using `[key, ← GlobalTheory.TripleSpaceW.exists_coe_iff]`. Conclude with `h _ hx`.

Introduce `h x' hx'`. Use `h (star x') (by rw [GlobalTheory.TripleSpaceW.mem_conjSub, star_star]; exact hx')` as an intermediate fact. Rewrite `this` using `[key, ← GlobalTheory.TripleSpaceW.exists_coe_iff, star_star]`. Conclude with `this`. Establish `e : ((1 : D.host.E) • (spW G i j).gram).map (B.emb w).1 = (gramAt D (spW G i j) (τf w)).map (starRingEnd ℂ)`.

Use extensionality with `a b`. Simplify using `only [one_smul, Matrix.map_apply, hemb, gramAt]`. Use `show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (((1 : D.host.E) • (spW G i j).gram).map (B.emb w).1) _`. Rewrite using `[e]`. Conclude with `GlobalTheory.TripleSpaceW.isCartan_map_conj (W.cart_is _ hX (τf w))`.

Use `show GlobalTheory.AdelicU.IsSplitBasis (B.τ v) _ (if h : v.1 ∈ B.P then bas0 ⟨v.1, h⟩ else 1)`. Rewrite using `[dif_pos v.2]`. Conclude with `hbas0 v`.
-/
theorem isHerm_spaceW : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (W : G.Weil)
    (i j : Fin D.R.m) (B : Base D.host.F D.host.E) (τf : InfinitePlace D.host.F → D.what₂.Tau),
    (∀ w x, (B.emb w).1 x = conj (tauE D (τf w) x)) →
    ∃ (Λ : Submodule (𝓞 D.host.E) (Fin (spW G i j).rank → D.host.E))
      (bas : ∀ v : HeightOneSpectrum (𝓞 D.host.F), GL (Fin (spW G i j).rank) (Fv D.host.F v)),
      Spc.IsHerm D.sp.cm.sig B
        (Spc.mk ((1 : D.host.E) • (spW G i j).gram) Λ (fun w => W.cart (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)) (τf w)) bas)
        ((spW G i j).rank - (D.R.m - j - 1) / 2) ((D.R.m - j - 1) / 2) := by
  intro D T L sc G μ₀ hL W i j B τf hemb
  have hX : (Node.grid ((i : ℕ) + 1) ((j : ℕ) + 1)).InRange D.R.m := ⟨i.2, j.2⟩
  have hV := node_isV G hL hX
  haveI hlat : (GlobalTheory.TripleSpaceW.conjSub (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)))).IsLattice D.host.E :=
    GlobalTheory.TripleSpaceW.conjSub_isLattice hV.sd.1
  choose bas0 hbas0 using fun v : B.P =>
    GlobalTheory.AdelicU.exists_isSplitBasis (B.τ v) (GlobalTheory.TripleSpaceW.conjSub (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))))
      (GlobalTheory.AdelicU.isCMExt_host D)
  have hq : Node.neg D.R.m (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)) = (D.R.m - j - 1) / 2 := by
    show (D.R.m - ((j : ℕ) + 1)) / 2 = _
    rw [Nat.sub_sub]
  have hherm : ∀ a b, star ((spW G i j).gram b a) = (spW G i j).gram a b := fun a b =>
    (spW G i j).herm.eq ((spW G i j).frame b) ((spW G i j).frame a)
  refine ⟨GlobalTheory.TripleSpaceW.conjSub (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))),
    fun v => if h : v ∈ B.P then bas0 ⟨v, h⟩ else 1, ⟨fun a b => ?_, fun w => ?_, hlat, fun y => ?_, fun w => ?_, fun v => ?_⟩⟩
  · show star (((1 : D.host.E) • (spW G i j).gram) b a) = ((1 : D.host.E) • (spW G i j).gram) a b
    rw [one_smul]
    exact hherm a b
  · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (((1 : D.host.E) • (spW G i j).gram).map (B.emb w).1) _ _
    have hs := hV.sigOK (B.emb w).1
    rw [hV.sig, hq, ← hV.rank] at hs
    rw [one_smul]
    exact GlobalTheory.TripleSpaceW.hasSig_of_hasSignature hs
  · have hσ : ∀ z : D.host.E, D.sp.cm.sig z = star z := fun _ => rfl
    have hh' : ∀ a b, star ((spW G i j).gram a b) = (spW G i j).gram b a := fun a b => hherm b a
    have key : ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig ((1 : D.host.E) • (spW G i j).gram) y x =
        star (∑ a, ∑ b, star ((star x) a) * (spW G i j).gram a b * (star y) b) := fun x => by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, one_smul, dotProduct, Matrix.mulVec, star_sum, star_mul', star_star,
        Pi.star_apply, hσ, hh', Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    show star y ∈ G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ↔ _
    rw [hV.sd.2 (star y)]
    constructor
    · intro h x hx
      rw [key, ← GlobalTheory.TripleSpaceW.exists_coe_iff]
      exact h _ hx
    · intro h x' hx'
      have := h (star x') (by rw [GlobalTheory.TripleSpaceW.mem_conjSub, star_star]; exact hx')
      rw [key, ← GlobalTheory.TripleSpaceW.exists_coe_iff, star_star] at this
      exact this
  · have e : ((1 : D.host.E) • (spW G i j).gram).map (B.emb w).1 =
        (gramAt D (spW G i j) (τf w)).map (starRingEnd ℂ) := by
      ext a b
      simp only [one_smul, Matrix.map_apply, hemb, gramAt]
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (((1 : D.host.E) • (spW G i j).gram).map (B.emb w).1) _
    rw [e]
    exact GlobalTheory.TripleSpaceW.isCartan_map_conj (W.cart_is _ hX (τf w))
  · show GlobalTheory.AdelicU.IsSplitBasis (B.τ v) _ (if h : v.1 ∈ B.P then bas0 ⟨v.1, h⟩ else 1)
    rw [dif_pos v.2]
    exact hbas0 v

end GlobalTheory.FunObj

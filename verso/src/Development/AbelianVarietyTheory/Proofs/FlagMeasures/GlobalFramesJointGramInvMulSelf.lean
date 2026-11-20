import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GamInv

/- English proof (translation)
Simplify using `[hf, mul_add, Finset.sum_add_distrib]`.
-/
theorem hf_add_right {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) {n : ℕ}
    (H : Matrix (Fin n) (Fin n) E) (x y z : Fin n → E) :
    hf L H x (y + z) = hf L H x y + hf L H x z := by
  simp [hf, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_smul_right {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) {n : ℕ}
    (H : Matrix (Fin n) (Fin n) E) (x z : Fin n → E) (c : E) :
    hf L H x (c • z) = L.cj c * hf L H x z := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Introduce `F E _ _ _ _ _ sig A r k G`. Use `set g : Fin (r + 1) ⊕ Fin (r + 1) → Fin (k + 2 * r + 1) → E := Sum.elim G.f G.f' with hg`. Take `⟨M, hM⟩` from `Ideal.exists_maximal (𝓞 F)`. Set `p : HeightOneSpectrum (𝓞 F)` to `⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩`. Take `⟨hinj, -, -, -, hform, hind⟩` from `GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p`.

Use `haveI := (A.loc p).lf`. Use `haveI := (A.loc p).char0`. Take `⟨hli, hco, -⟩` from `GlobalTheory.FrameBasic.main (A.L p) r k (G.S p)`. Use `set S := G.S p with hS`. Use `set Ep := (A.loc p).Ep`.

Set `s : Fin (r + 1) ⊕ Fin (r + 1) → Epˣ` to `fun q => Units.map (algebraMap (A.loc p).Fp Ep).toMonoidHom (G.c p ^ (r - (Sum.elim (fun a : Fin (r + 1) => (a : ℕ)) (fun a => (a : ℕ)) q)))`. Establish `hu : ∀ q, A.bc p (g q) = ((s q : Epˣ) : Ep) • Sum.elim S.f S.f' q`. Introduce `q`. Break down `q with a | a` into its components or cases. Simplify using `only [hg, Sum.elim_inl, s, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]`.

Conclude with `(G.f_eq p a).symm`. Simplify using `only [hg, Sum.elim_inr, s, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]`. Conclude with `(G.f'_eq p a).symm`. Establish `hgli : LinearIndependent E g`. Set `e` to `(finSumFinEquiv (m := r + 1) (n := r + 1))`.

Use `(linearIndependent_equiv e.symm).1 ((hind _ (g ∘ e.symm)).2 ?_)` and prove the remaining obligations. Establish `: (fun q => A.bc p (g q)) = s • Sum.elim S.f S.f'`. Use function extensionality and compare the values at `q`. Rewrite using `[hu]`. Both sides reduce to the same expression.

Establish `h2 : LinearIndependent Ep (fun q => A.bc p (g q))`. Rewrite using `[this]`. Conclude with `hli.units_smul s`. Conclude with `(linearIndependent_equiv e.symm).2 h2`. Establish `hME : S.ME = Submodule.span Ep (Set.range (Sum.elim S.f S.f'))`.

Establish `h1 : ∀ v : Fin (r + 1) → S.V, S.spanTo v (r + 1) = Submodule.span Ep (Set.range v)`. Introduce `v`. Unfold `Frames.spanTo`. Use `congr 1`. Use extensionality with `y`.

Simplify using `only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]`. Conclude with `⟨fun ⟨a, _, h⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨a, a.isLt, h⟩⟩`. Rewrite using `[Frames.ME, h1, h1, Set.Sum.elim_range, Submodule.span_union]`. Use `set Γ : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E := Matrix.of fun k l => ∑ i, ∑ j, g k i * G.Hm i j * sig (g l j) with hΓ`. Establish `key : ∀ v : Fin (r + 1) ⊕ Fin (r + 1) → E, Matrix.vecMul v Γ = 0 → v = 0`.

Introduce `v hv`. Use `set x : Fin (k + 2 * r + 1) → E := ∑ q, v q • g q with hx`. Establish `hx0 : ∀ l, ∑ i, ∑ j, x i * G.Hm i j * sig (g l j) = 0`. Introduce `l`. Establish `h : Matrix.vecMul v Γ l = 0` using `congrFun hv l`.

Rewrite using `[← h]`. Simplify using `only [Matrix.vecMul, dotProduct, hΓ, Matrix.of_apply, hx, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, Pi.zero_apply]`. Use `symm`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => by ring`. Establish `hloc : ∀ q, hf (A.L p) S.Hm (A.bc p x) (A.bc p (g q)) = 0`. Introduce `q`. Rewrite using `[G.Hm_eq p, hform, hx0, map_zero]`.

Establish `hbcx : A.bc p x = ∑ q, (A.loc p).ιE (v q) • A.bc p (g q)`. Use function extensionality and compare the values at `i`. Simplify using `[Places.bc, hx, Finset.sum_apply, map_sum]`. Establish `hmem : A.bc p x ∈ S.ME`. Rewrite using `[hbcx, hME]`.

Use `Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Rewrite using `[hu]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)`. Establish `hperp : A.bc p x ∈ S.W0` using `by show ∀ y ∈ S.ME, hf (A.L p) S.Hm (A.bc p x) y = 0`. Introduce `y hy`.

Rewrite `hy` using `[hME]`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨q, rfl⟩` from `hy`. Establish `e1 : Sum.elim S.f S.f' q = ((s q)⁻¹ : Epˣ) • A.bc p (g q)`.

Rewrite using `[hu, ← Units.smul_def, inv_smul_smul]`. Rewrite using `[e1, Units.smul_def, hf_smul_right, hloc q, mul_zero]`. Consider the case `zero => simp [hf]`. Consider the case `add y z _ _ hy hz => rw [hf_add_right, hy, hz, add_zero]`. Consider the case `smul c y _ hy => rw [hf_smul_right, hy, mul_zero]`.

Establish `hbot : A.bc p x = 0`. Establish `h : A.bc p x ∈ S.ME ⊓ S.W0` using `⟨hmem, hperp⟩`. Rewrite `h` using `[hco.inf_eq_bot]`. Conclude with `(Submodule.mem_bot _).1 h`. Establish `hx00 : x = 0` using `hinj (by rw [hbot]; funext i; simp [Places.bc])`.

Use function extensionality and compare the values at `q`. Conclude with `Fintype.linearIndependent_iff.1 hgli v (by rw [← hx]; exact hx00) q`. Establish `hU : IsUnit Γ` using `Matrix.vecMul_injective_iff_isUnit.1 fun a b h => sub_eq_zero.1 (key _ (by rw [Matrix.sub_vecMul]; exact sub_eq_zero.2 h))`. Conclude with `Matrix.nonsing_inv_mul Γ ((Matrix.isUnit_iff_isUnit_det Γ).1 hU)`.
-/
theorem main : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k), (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j))⁻¹ * (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j)) = 1 := by
  intro F E _ _ _ _ _ sig A r k G
  classical
  set g : Fin (r + 1) ⊕ Fin (r + 1) → Fin (k + 2 * r + 1) → E := Sum.elim G.f G.f' with hg
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  let p : HeightOneSpectrum (𝓞 F) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩
  obtain ⟨hinj, -, -, -, hform, hind⟩ := GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  obtain ⟨hli, hco, -⟩ := GlobalTheory.FrameBasic.main (A.L p) r k (G.S p)
  set S := G.S p with hS
  set Ep := (A.loc p).Ep
  let s : Fin (r + 1) ⊕ Fin (r + 1) → Epˣ := fun q =>
    Units.map (algebraMap (A.loc p).Fp Ep).toMonoidHom (G.c p ^ (r - (Sum.elim (fun a : Fin (r + 1) => (a : ℕ)) (fun a => (a : ℕ)) q)))
  have hu : ∀ q, A.bc p (g q) = ((s q : Epˣ) : Ep) • Sum.elim S.f S.f' q := by
    intro q
    rcases q with a | a
    · simp only [hg, Sum.elim_inl, s, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]
      exact (G.f_eq p a).symm
    · simp only [hg, Sum.elim_inr, s, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]
      exact (G.f'_eq p a).symm
  have hgli : LinearIndependent E g := by
    let e := (finSumFinEquiv (m := r + 1) (n := r + 1))
    refine (linearIndependent_equiv e.symm).1 ((hind _ (g ∘ e.symm)).2 ?_)
    have : (fun q => A.bc p (g q)) = s • Sum.elim S.f S.f' := by
      funext q; rw [hu]; rfl
    have h2 : LinearIndependent Ep (fun q => A.bc p (g q)) := by
      rw [this]; exact hli.units_smul s
    exact (linearIndependent_equiv e.symm).2 h2
  have hME : S.ME = Submodule.span Ep (Set.range (Sum.elim S.f S.f')) := by
    have h1 : ∀ v : Fin (r + 1) → S.V, S.spanTo v (r + 1) = Submodule.span Ep (Set.range v) := by
      intro v
      unfold Frames.spanTo
      congr 1
      ext y
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
      exact ⟨fun ⟨a, _, h⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨a, a.isLt, h⟩⟩
    rw [Frames.ME, h1, h1, Set.Sum.elim_range, Submodule.span_union]
  set Γ : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
    Matrix.of fun k l => ∑ i, ∑ j, g k i * G.Hm i j * sig (g l j) with hΓ
  have key : ∀ v : Fin (r + 1) ⊕ Fin (r + 1) → E, Matrix.vecMul v Γ = 0 → v = 0 := by
    intro v hv
    set x : Fin (k + 2 * r + 1) → E := ∑ q, v q • g q with hx
    have hx0 : ∀ l, ∑ i, ∑ j, x i * G.Hm i j * sig (g l j) = 0 := by
      intro l
      have h : Matrix.vecMul v Γ l = 0 := congrFun hv l
      rw [← h]
      simp only [Matrix.vecMul, dotProduct, hΓ, Matrix.of_apply, hx, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Finset.sum_mul, Finset.mul_sum, Pi.zero_apply]
      symm
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => by ring
    have hloc : ∀ q, hf (A.L p) S.Hm (A.bc p x) (A.bc p (g q)) = 0 := by
      intro q
      rw [G.Hm_eq p, hform, hx0, map_zero]
    have hbcx : A.bc p x = ∑ q, (A.loc p).ιE (v q) • A.bc p (g q) := by
      funext i
      simp [Places.bc, hx, Finset.sum_apply, map_sum]
    have hmem : A.bc p x ∈ S.ME := by
      rw [hbcx, hME]
      refine Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ ?_
      rw [hu]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
    have hperp : A.bc p x ∈ S.W0 := by
      show ∀ y ∈ S.ME, hf (A.L p) S.Hm (A.bc p x) y = 0
      intro y hy
      rw [hME] at hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨q, rfl⟩ := hy
        have e1 : Sum.elim S.f S.f' q = ((s q)⁻¹ : Epˣ) • A.bc p (g q) := by
          rw [hu, ← Units.smul_def, inv_smul_smul]
        rw [e1, Units.smul_def, hf_smul_right, hloc q, mul_zero]
      | zero => simp [hf]
      | add y z _ _ hy hz => rw [hf_add_right, hy, hz, add_zero]
      | smul c y _ hy => rw [hf_smul_right, hy, mul_zero]
    have hbot : A.bc p x = 0 := by
      have h : A.bc p x ∈ S.ME ⊓ S.W0 := ⟨hmem, hperp⟩
      rw [hco.inf_eq_bot] at h
      exact (Submodule.mem_bot _).1 h
    have hx00 : x = 0 := hinj (by rw [hbot]; funext i; simp [Places.bc])
    funext q
    exact Fintype.linearIndependent_iff.1 hgli v (by rw [← hx]; exact hx00) q
  have hU : IsUnit Γ := Matrix.vecMul_injective_iff_isUnit.1 fun a b h =>
    sub_eq_zero.1 (key _ (by rw [Matrix.sub_vecMul]; exact sub_eq_zero.2 h))
  exact Matrix.nonsing_inv_mul Γ ((Matrix.isUnit_iff_isUnit_det Γ).1 hU)

end GlobalTheory.HL.GamInv

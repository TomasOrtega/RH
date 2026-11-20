import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StProjBundleFibre
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermOfIsPullHermInl
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section LinSubst

variable {Φ : Type} [Field Φ] {σ : Type} [Fintype σ] {n : ℕ}

def linSubst (ℓ : σ → Fin n → Φ) : MvPolynomial σ Φ →ₐ[Φ] MvPolynomial (Fin n) Φ :=
  aeval fun q => ∑ a, C (ℓ q a) * X a

def linKerForms (ℓ : σ → Fin n → Φ) : Set (MvPolynomial σ Φ) :=
  {f | ∃ μ : σ → Φ, (∀ b, ∑ q, μ q * ℓ q b = 0) ∧ f = ∑ q, C (μ q) * X q}

/- English proof (translation)
Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, mul_assoc]`.
-/
theorem sum_C_mul_linForm {τ ρ : Type} [Fintype τ] [Fintype ρ] (c : ρ → Φ) (ν : ρ → τ → Φ) :
    ∑ a, C (c a) * ∑ q, C (ν a q) * (X q : MvPolynomial τ Φ) = ∑ q, C (∑ a, c a * ν a q) * X q := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, mul_assoc]

/- English proof (translation)
Rewrite using `[← sum_C_mul_linForm μ ℓ]`. Simplify using `only [linSubst, map_sum, map_mul, aeval_C, aeval_X, MvPolynomial.algebraMap_eq]`.
-/
theorem linSubst_linForm (ℓ : σ → Fin n → Φ) (μ : σ → Φ) :
    linSubst ℓ (∑ q, C (μ q) * X q) = ∑ b, C (∑ q, μ q * ℓ q b) * X b := by
  rw [← sum_C_mul_linForm μ ℓ]
  simp only [linSubst, map_sum, map_mul, aeval_C, aeval_X, MvPolynomial.algebraMap_eq]

/- English proof (translation)
Use `le_antisymm (fun f hf => ?_) ?_` and prove the remaining obligations. Use `set I := Ideal.span (linKerForms ℓ)`. Set `ρ : MvPolynomial (Fin n) Φ →ₐ[Φ] MvPolynomial σ Φ ⧸ I` to `aeval fun a => Ideal.Quotient.mk I (∑ q, C (ν a q) * X q)`. Establish `hρ : ρ.comp (linSubst ℓ) = Ideal.Quotient.mkₐ Φ I`. Use `MvPolynomial.algHom_ext fun q => ?_` and prove the remaining obligations.

Rewrite using `[AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]`. Establish `h1 : ρ (linSubst ℓ (X q)) = Ideal.Quotient.mk I (∑ q', C (∑ a, ℓ q a * ν a q') * X q')`. Rewrite using `[← sum_C_mul_linForm]`. Simplify using `only [ρ, linSubst, aeval_X, map_sum, map_mul, aeval_C]`. Both sides reduce to the same expression.

Rewrite using `[h1, Ideal.Quotient.eq]`. Use `Ideal.subset_span ⟨fun q' => ∑ a, ℓ q a * ν a q' - if q' = q then 1 else 0, fun b => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, mul_assoc]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.mul_sum, hν, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Simplify using the standard rewrite rules. Simplify using `[sub_mul, Finset.sum_sub_distrib, apply_ite C, ite_mul]`. Establish `h2` using `congrArg (fun φ => φ f) hρ`. Simplify using `only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h2`. Rewrite `hf` using `[RingHom.mem_ker]`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, ← h2]`. Use `erw [hf]`. Conclude with `map_zero ρ`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `f ⟨μ, hμ, rfl⟩`.

Rewrite using `[SetLike.mem_coe, RingHom.mem_ker]`. Use `erw [linSubst_linForm]`. Simplify using `[hμ]`.
-/
theorem ker_linSubst (ℓ : σ → Fin n → Φ) (ν : Fin n → σ → Φ)
    (hν : ∀ a b, ∑ q, ν a q * ℓ q b = if a = b then 1 else 0) :
    RingHom.ker (linSubst ℓ) = Ideal.span (linKerForms ℓ) := by
  classical
  refine le_antisymm (fun f hf => ?_) ?_
  · set I := Ideal.span (linKerForms ℓ)
    let ρ : MvPolynomial (Fin n) Φ →ₐ[Φ] MvPolynomial σ Φ ⧸ I :=
      aeval fun a => Ideal.Quotient.mk I (∑ q, C (ν a q) * X q)
    have hρ : ρ.comp (linSubst ℓ) = Ideal.Quotient.mkₐ Φ I := by
      refine MvPolynomial.algHom_ext fun q => ?_
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
      have h1 : ρ (linSubst ℓ (X q)) =
          Ideal.Quotient.mk I (∑ q', C (∑ a, ℓ q a * ν a q') * X q') := by
        rw [← sum_C_mul_linForm]
        simp only [ρ, linSubst, aeval_X, map_sum, map_mul, aeval_C]
        rfl
      rw [h1, Ideal.Quotient.eq]
      refine Ideal.subset_span ⟨fun q' => ∑ a, ℓ q a * ν a q' - if q' = q then 1 else 0, fun b => ?_, ?_⟩
      · simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, mul_assoc]
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum, hν, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        simp
      · simp [sub_mul, Finset.sum_sub_distrib, apply_ite C, ite_mul]
    have h2 := congrArg (fun φ => φ f) hρ
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h2
    rw [RingHom.mem_ker] at hf
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← h2]
    erw [hf]
    exact map_zero ρ
  · rw [Ideal.span_le]
    rintro f ⟨μ, hμ, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    erw [linSubst_linForm]
    simp [hμ]

end LinSubst

section Main

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Establish `h : (aeval (genPt P) : MRing ι →ₐ[ℤ] FnField P).toRingHom = (algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P)` using `MvPolynomial.ringHom_ext (fun r => by rw [show (C r : MvPolynomial _ ℤ) = (r : MvPolynomial _ ℤ) from eq_intCast C r, map_intCast, map_intCast]) (fun p => by simp [genPt])`. Conclude with `RingHom.congr_fun h f`.
-/
theorem aeval_genPt_eq_mk (P : Ideal (MRing ι)) {_ : Algebra ℤ (FnField P)} (f : MRing ι) :
    aeval (genPt P) f = algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P f) := by
  have h : (aeval (genPt P) : MRing ι →ₐ[ℤ] FnField P).toRingHom =
      (algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P) :=
    MvPolynomial.ringHom_ext (fun r => by rw [show (C r : MvPolynomial _ ℤ) = (r : MvPolynomial _ ℤ) from
      eq_intCast C r, map_intCast, map_intCast])
      (fun p => by simp [genPt])
  exact RingHom.congr_fun h f

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Simplify using `[projBundleMap]`.
-/
theorem projBundleMap_X_inr (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P))
    (u : Unit) (j : Fin N1) :
    projBundleMap P B (X ⟨Sum.inr u, j⟩) = ∑ a, C (B a j) * X a := by
  simp [projBundleMap]

def projBundlePt (P : Ideal (MRing ι)) [P.IsPrime] {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    (Σ k, PBlk ι N1 k) → FractionRing (MvPolynomial (Fin n) (FnField P)) :=
  fun p => algebraMap (MvPolynomial (Fin n) (FnField P)) _ (projBundleMap P B (X p))

omit [Fintype K] [∀ k, Fintype (ι k)] in
/- English proof (translation)
Establish `h : (aeval (projBundlePt P B) : MRing (PBlk ι N1) →ₐ[ℤ] _).toRingHom = (algebraMap (MvPolynomial (Fin n) (FnField P)) (FractionRing (MvPolynomial (Fin n) (FnField P)))).comp (projBundleMap P B)` using `MvPolynomial.ringHom_ext (fun r => by rw [show (C r : MvPolynomial _ ℤ) = (r : MvPolynomial _ ℤ) from eq_intCast C r, map_intCast, map_intCast]) (fun p => by simp [projBundlePt])`. Conclude with `RingHom.congr_fun h f`.
-/
theorem aeval_projBundlePt (P : Ideal (MRing ι)) [P.IsPrime] {N1 n : ℕ}
    (B : Matrix (Fin n) (Fin N1) (FnField P)) {_ : Algebra ℤ (FractionRing (MvPolynomial (Fin n) (FnField P)))}
    (f : MRing (PBlk ι N1)) :
    aeval (projBundlePt P B) f = algebraMap (MvPolynomial (Fin n) (FnField P)) _ (projBundleMap P B f) := by
  have h : (aeval (projBundlePt P B) : MRing (PBlk ι N1) →ₐ[ℤ] _).toRingHom =
      (algebraMap (MvPolynomial (Fin n) (FnField P)) (FractionRing (MvPolynomial (Fin n) (FnField P)))).comp
        (projBundleMap P B) :=
    MvPolynomial.ringHom_ext (fun r => by rw [show (C r : MvPolynomial _ ℤ) = (r : MvPolynomial _ ℤ) from
      eq_intCast C r, map_intCast, map_intCast])
      (fun p => by simp [projBundlePt])
  exact RingHom.congr_fun h f

def projBundleGenFibre (P : Ideal (MRing ι)) [P.IsPrime] {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    GenFibre (inlV (ι₂ := fun _ : Unit => Fin N1)) (projBundleIdeal P B) where
  Φ := FnField P
  Φ' := FractionRing (MvPolynomial (Fin n) (FnField P))
  x := genPt P
  x' := projBundlePt P B
  ker_x := by
    rw [imageZ_projBundleIdeal]
    ext f
    rw [RingHom.mem_ker]
    exact (Eq.congr_left (aeval_genPt_eq_mk P f)).trans
      ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).trans Ideal.Quotient.eq_zero_iff_mem)
  gen c := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MRing ι ⧸ P) c
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨f, g, ?_, ?_⟩
    · exact fun h => IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb ((aeval_genPt_eq_mk P g).symm.trans h)
    · exact (congrArg₂ (· / ·) (aeval_genPt_eq_mk P f) (aeval_genPt_eq_mk P g)).symm
  genericFibre_ker_target := by
    ext f
    rw [RingHom.mem_ker]
    exact (Eq.congr_left (aeval_projBundlePt P B f)).trans
      ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).trans RingHom.mem_ker.symm)
  compat p := by
    obtain ⟨k, i⟩ := p
    simp [projBundlePt, inlV, projBundleMap, IsScalarTower.algebraMap_apply (FnField P)
      (MvPolynomial (Fin n) (FnField P)) (FractionRing (MvPolynomial (Fin n) (FnField P)))]

end Main

section Fibre

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] in

/- English proof (translation)
Break down `k with ⟨k | u, hk⟩` into its components or cases. Conclude with `absurd ⟨k, rfl⟩ hk`. Break down `k' with ⟨k' | u', hk'⟩` into its components or cases. Conclude with `absurd ⟨k', rfl⟩ hk'`. Both sides reduce to the same expression.
-/
theorem fibreBlock_inl_subsingleton (k k' : FibreBlock (Sum.inl : K → K ⊕ Unit)) : k = k' := by
  rcases k with ⟨k | u, hk⟩
  · exact absurd ⟨k, rfl⟩ hk
  rcases k' with ⟨k' | u', hk'⟩
  · exact absurd ⟨k', rfl⟩ hk'
  rfl

omit [Fintype K] [∀ k, Fintype (ι k)] in

def fibreCoordEquiv (ι : K → Type) (N1 : ℕ) :
    (Σ k : FibreBlock (Sum.inl : K → K ⊕ Unit), fibreIdx (PBlk ι N1) Sum.inl k) ≃ Fin N1 where
  toFun
    | ⟨⟨.inl k, h⟩, _⟩ => absurd ⟨k, rfl⟩ h
    | ⟨⟨.inr _, _⟩, j⟩ => j
  invFun j := ⟨⟨.inr (), by rintro ⟨k, hk⟩; cases hk⟩, j⟩
  left_inv := by
    rintro ⟨⟨k | u, h⟩, j⟩
    · exact absurd ⟨k, rfl⟩ h
    · rfl
  right_inv _ := rfl

/- English proof (translation)
Introduce `s hs k`. Take `⟨q, -, hq⟩` from `Finset.mem_biUnion.1 (support_sum hs)`. Rewrite `hq` using `[C_mul_X_eq_monomial]`. Establish `hs'` using `support_monomial_subset hq`. Rewrite `hs'` using `[Finset.mem_singleton]`.

Substitute `hs'` using the available equality. Take `⟨qk, qi⟩` from `q`. Take `rfl : qk = k` from `fibreBlock_inl_subsingleton _ _`. Simplify using `[Finsupp.single_apply]`.
-/
theorem isMultiHomog_linForm {Φ : Type} [Field Φ] {N1 : ℕ}
    (μ : (Σ k : FibreBlock (Sum.inl : K → K ⊕ Unit), fibreIdx (PBlk ι N1) Sum.inl k) → Φ) :
    IsMultiHomog (∑ q, C (μ q) * X q : MRingOver Φ (fibreIdx (PBlk ι N1) Sum.inl)) fun _ => 1 := by
  classical
  intro s hs k
  obtain ⟨q, -, hq⟩ := Finset.mem_biUnion.1 (support_sum hs)
  rw [C_mul_X_eq_monomial] at hq
  have hs' := support_monomial_subset hq
  rw [Finset.mem_singleton] at hs'
  subst hs'
  obtain ⟨qk, qi⟩ := q
  obtain rfl : qk = k := fibreBlock_inl_subsingleton _ _
  simp [Finsupp.single_apply]

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Establish `h : ∀ f, aeval (fun q : Σ k : FibreBlock (Sum.inl : K → K ⊕ Unit), fibreIdx (PBlk ι N1) Sum.inl k => projBundlePt P B ⟨q.1.1, q.2⟩) f = algebraMap (MvPolynomial (Fin n) (FnField P)) (FractionRing (MvPolynomial (Fin n) (FnField P))) (linSubst (fun q a => B a (fibreCoordEquiv ι N1 …`. Introduce `f`. Establish `e : (aeval fun q : Σ k : FibreBlock (Sum.inl : K → K ⊕ Unit), fibreIdx (PBlk ι N1) Sum.inl k => projBundlePt P B ⟨q.1.1, q.2⟩) = (IsScalarTower.toAlgHom (FnField P) (MvPolynomial (Fin n) (FnField P)) (FractionRing (MvPolynomial (Fin n) (FnField P)))).comp (linSubst fun q a => B a …`. Use `MvPolynomial.algHom_ext fun q => ?_` and prove the remaining obligations. Break down `q with ⟨⟨k | u, hk⟩, j⟩` into its components or cases.

Conclude with `absurd ⟨k, rfl⟩ hk`. Simplify using `only [aeval_X, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', linSubst, projBundlePt]`. Conclude with `congrArg _ (projBundleMap_X_inr P B u j)`. Rewrite using `[e, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']`. Use extensionality with `f`.

Rewrite using `[fibreIdeal, RingHom.mem_ker]`. Conclude with `(Eq.congr_left (h f)).trans ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).trans RingHom.mem_ker.symm)`.
-/
theorem fibreIdeal_projBundleGenFibre (P : Ideal (MRing ι)) [P.IsPrime] {N1 n : ℕ}
    (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    fibreIdeal Sum.inl (projBundleGenFibre P B) =
      RingHom.ker (linSubst fun q a => B a (fibreCoordEquiv ι N1 q)) := by
  have h : ∀ f, aeval (fun q : Σ k : FibreBlock (Sum.inl : K → K ⊕ Unit), fibreIdx (PBlk ι N1) Sum.inl k =>
      projBundlePt P B ⟨q.1.1, q.2⟩) f =
      algebraMap (MvPolynomial (Fin n) (FnField P)) (FractionRing (MvPolynomial (Fin n) (FnField P)))
        (linSubst (fun q a => B a (fibreCoordEquiv ι N1 q)) f) := by
    intro f
    have e : (aeval fun q : Σ k : FibreBlock (Sum.inl : K → K ⊕ Unit), fibreIdx (PBlk ι N1) Sum.inl k =>
        projBundlePt P B ⟨q.1.1, q.2⟩) =
        (IsScalarTower.toAlgHom (FnField P) (MvPolynomial (Fin n) (FnField P))
          (FractionRing (MvPolynomial (Fin n) (FnField P)))).comp
          (linSubst fun q a => B a (fibreCoordEquiv ι N1 q)) := by
      refine MvPolynomial.algHom_ext fun q => ?_
      rcases q with ⟨⟨k | u, hk⟩, j⟩
      · exact absurd ⟨k, rfl⟩ hk
      · simp only [aeval_X, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', linSubst, projBundlePt]
        exact congrArg _ (projBundleMap_X_inr P B u j)
    rw [e, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
  ext f
  rw [fibreIdeal, RingHom.mem_ker]
  exact (Eq.congr_left (h f)).trans
    ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).trans RingHom.mem_ker.symm)

end Fibre

/- English proof (translation)
Introduce `K _ ι _ N1 t P d c m B hP _ hB`. Establish `: P.IsPrime` using `hP.2.1.1`. Use `set e := fibreCoordEquiv ι N1`. Use `set ℓ : (Σ k : FibreBlock (Sum.inl : K → K ⊕ Unit), fibreIdx (PBlk ι N1) Sum.inl k) → Fin 2 → FnField P := fun q a => B a (e q) with hℓ`. Take `⟨g, hg⟩` from `(Fintype.linearCombination (FnField P) B).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hB.1.fintypeLinearCombination_injective)`.

Establish `hν : ∀ a b, ∑ q, g (Pi.single (e q) 1) a * ℓ q b = if a = b then 1 else 0`. Introduce `a b`. Establish `h1 : ∑ q, g (Pi.single (e q) 1) a * ℓ q b = g (B b) a`. Rewrite using `[Fintype.sum_equiv e (fun q => g (Pi.single (e q) 1) a * ℓ q b) (fun j => g (Pi.single j 1) a * B b j) (fun q => rfl)]`. Establish `hB' : B b = ∑ j, B b j • Pi.single j (1 : FnField P)`.

Use extensionality with `i`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `conv_rhs => rw [hB']`. Rewrite using `[map_sum, Finset.sum_apply]`. Simplify using `[mul_comm]`.

Establish `h2 : B b = Fintype.linearCombination (FnField P) B (Pi.single b 1)`. Conclude with `((Fintype.linearCombination_apply_single (FnField P) B b (1 : FnField P)).trans (one_smul _ _)).symm`. Rewrite using `[h1, h2, ← LinearMap.comp_apply, hg, LinearMap.id_apply, Pi.single_apply]`. Use `⟨projBundleGenFibre P B, linKerForms ℓ, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `f ⟨μ, -, rfl⟩`.

Conclude with `isMultiHomog_linForm μ`. Rewrite using `[fibreIdeal_projBundleGenFibre, ker_linSubst ℓ (fun a q => g (Pi.single (e q) 1) a) hν]`. Conclude with `rfl`.
-/
theorem ProjBundleFibreLine.proof : ProjBundleFibreLine.Statement := by
  intro K _ ι _ N1 t P d c m B hP _ hB
  have : P.IsPrime := hP.2.1.1
  classical
  set e := fibreCoordEquiv ι N1
  set ℓ : (Σ k : FibreBlock (Sum.inl : K → K ⊕ Unit), fibreIdx (PBlk ι N1) Sum.inl k) → Fin 2 → FnField P :=
    fun q a => B a (e q) with hℓ
  obtain ⟨g, hg⟩ := (Fintype.linearCombination (FnField P) B).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hB.1.fintypeLinearCombination_injective)
  have hν : ∀ a b, ∑ q, g (Pi.single (e q) 1) a * ℓ q b = if a = b then 1 else 0 := by
    intro a b
    have h1 : ∑ q, g (Pi.single (e q) 1) a * ℓ q b = g (B b) a := by
      rw [Fintype.sum_equiv e (fun q => g (Pi.single (e q) 1) a * ℓ q b)
        (fun j => g (Pi.single j 1) a * B b j) (fun q => rfl)]
      have hB' : B b = ∑ j, B b j • Pi.single j (1 : FnField P) := by
        ext i
        simp [Finset.sum_apply, Pi.single_apply]
      conv_rhs => rw [hB']
      rw [map_sum, Finset.sum_apply]
      simp [mul_comm]
    have h2 : B b = Fintype.linearCombination (FnField P) B (Pi.single b 1) := by
      exact ((Fintype.linearCombination_apply_single (FnField P) B b (1 : FnField P)).trans (one_smul _ _)).symm
    rw [h1, h2, ← LinearMap.comp_apply, hg, LinearMap.id_apply, Pi.single_apply]
  refine ⟨projBundleGenFibre P B, linKerForms ℓ, ?_, ?_⟩
  · rintro f ⟨μ, -, rfl⟩
    exact isMultiHomog_linForm μ
  · rw [fibreIdeal_projBundleGenFibre, ker_linSubst ℓ (fun a q => g (Pi.single (e q) 1) a) hν]
    exact rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

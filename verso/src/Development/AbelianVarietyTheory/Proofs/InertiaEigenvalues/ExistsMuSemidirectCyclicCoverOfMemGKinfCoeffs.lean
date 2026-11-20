import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.KinfCover

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a]

/- English proof (translation)
The claim follows from `IsFractionRing.injective (OCb l) (Cb l) ((congrArg (WittVector.coeff · n) (galW_inclW g w)).symm.trans (autCb_alg l (galTilt l g) (w.coeff n)))`.
-/
theorem sigA_coeff_pt (g : GQ l) (w : Ainf l) (n : ℕ) : (Per.σA g w).coeff n = Per.σF g (w.coeff n) :=
  IsFractionRing.injective (OCb l) (Cb l)
    ((congrArg (WittVector.coeff · n) (galW_inclW g w)).symm.trans (autCb_alg l (galTilt l g) (w.coeff n)))

/- English proof (translation)
Set `ρ : Fq l a →+* Fq l a` to `((Per.σF g).comp (Fq.val l a)).codRestrict (resSub l a) fun x => by`. Rewrite using `[mem_resSub, RingHom.comp_apply, ← map_pow]`. Conclude with `congrArg (Per.σF g) (mem_resSub.1 x.2)`. Establish `hρ : ∀ x, Fq.val l a (ρ x) = Per.σF g (Fq.val l a x)` using `fun _ => rfl`. Use `letI : Algebra (ZMod l) (Fq l a) := ZMod.algebra _ l`.

Use `Fintype.ofFinite (Fq l a)` as an intermediate fact. Set `ψ : Fq l a →ₐ[ZMod l] Fq l a` to `{ ρ with commutes' := fun r => RingHom.congr_fun (RingHom.ext_zmod (ρ.comp (algebraMap (ZMod l) (Fq l a))) (algebraMap (ZMod l) _)) r }`. Take `⟨j, hj⟩` from `(FiniteField.bijective_frobeniusAlgHom_pow (ZMod l) (Fq l a)).2 ψ`. Establish `hpow : ∀ x, ρ x = x ^ l ^ (j : ℕ)` using `fun x => by`. Establish `h1 : ψ x = x ^ l ^ (j : ℕ)`.

Rewrite using `[← hj]`. Simplify using `only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]`. Conclude with `h1`. Use `⟨j, fun w => WittVector.ext fun n => ?_⟩` and prove the remaining obligations. Use `(sigA_coeff_pt g (wA l a w) n).trans ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Per.σF g (Fq.val l a (w.coeff n)) = Fq.val l a (((sigma l a ^ (j : ℕ)) w).coeff n)`. Rewrite using `[coeff_sigma_pow, ← hpow, hρ]`.
-/
theorem exists_sigma_pow (g : GQ l) :
    ∃ m : ℕ, ∀ w : Wq l a, Per.σA g (wA l a w) = wA l a ((sigma l a ^ m) w) := by
  let ρ : Fq l a →+* Fq l a := ((Per.σF g).comp (Fq.val l a)).codRestrict (resSub l a) fun x => by
    rw [mem_resSub, RingHom.comp_apply, ← map_pow]
    exact congrArg (Per.σF g) (mem_resSub.1 x.2)
  have hρ : ∀ x, Fq.val l a (ρ x) = Per.σF g (Fq.val l a x) := fun _ => rfl
  letI : Algebra (ZMod l) (Fq l a) := ZMod.algebra _ l
  have := Fintype.ofFinite (Fq l a)
  let ψ : Fq l a →ₐ[ZMod l] Fq l a :=
    { ρ with commutes' := fun r =>
        RingHom.congr_fun (RingHom.ext_zmod (ρ.comp (algebraMap (ZMod l) (Fq l a))) (algebraMap (ZMod l) _)) r }
  obtain ⟨j, hj⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod l) (Fq l a)).2 ψ
  have hpow : ∀ x, ρ x = x ^ l ^ (j : ℕ) := fun x => by
    have h1 : ψ x = x ^ l ^ (j : ℕ) := by
      rw [← hj]
      simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]
    exact h1
  refine ⟨j, fun w => WittVector.ext fun n => ?_⟩
  refine (sigA_coeff_pt g (wA l a w) n).trans ?_
  change Per.σF g (Fq.val l a (w.coeff n)) = Fq.val l a (((sigma l a ^ (j : ℕ)) w).coeff n)
  rw [coeff_sigma_pow, ← hpow, hρ]

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O] (t : Wq l a →ₐ[ℤ_[l]] O)

/- English proof (translation)
Proceed by induction on `m generalizing τ with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[pow_succ', AlgEquiv.mul_apply, emb_sigma, ih, show τ - 1 - (m : ZMod a) = τ - ((m + 1 : ℕ) : ZMod a) by push_cast; ring]`.
-/
theorem emb_sigma_pow (m : ℕ) (τ : ZMod a) (w : Wq l a) :
    emb t τ ((sigma l a ^ m) w) = emb t (τ - m) w := by
  induction m generalizing τ with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', AlgEquiv.mul_apply, emb_sigma, ih,
      show τ - 1 - (m : ZMod a) = τ - ((m + 1 : ℕ) : ZMod a) by push_cast; ring]

/- English proof (translation)
Take `⟨y, rfl⟩` from `(splitHom_bijective t).2 x`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Conclude with `(map_zero (constA t)).symm`. Consider the case `tmul o w`.

Establish `: (fun τ => splitHom t (o ⊗ₜ w) (τ - m)) = splitHom t (o ⊗ₜ (sigma l a ^ m) w)`. Use function extensionality and compare the values at `fun τ => by rw [splitHom_tmul, splitHom_tmul, emb_sigma_pow]`. Rewrite using `[this, constA_splitHom, constA_splitHom]`. Conclude with `(galOA_tmul g o _).trans (congrArg (fun y : Ainf l => o ⊗ₜ[ℤ_[l]] y) (hm w))`. Consider the case `add y y' h h'`.

Rewrite using `[map_add, map_add, map_add, h, h', ← map_add]`. Both sides reduce to the same expression.
-/
theorem galOA_constA_shift {g : GQ l} {m : ℕ}
    (hm : ∀ w : Wq l a, Per.σA g (wA l a w) = wA l a ((sigma l a ^ m) w)) (x : ZMod a → O) :
    galOA O g (constA t x) = constA t fun τ => x (τ - m) := by
  obtain ⟨y, rfl⟩ := (splitHom_bijective t).2 x
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact (map_zero (constA t)).symm
  | tmul o w =>
    have : (fun τ => splitHom t (o ⊗ₜ w) (τ - m)) = splitHom t (o ⊗ₜ (sigma l a ^ m) w) :=
      funext fun τ => by rw [splitHom_tmul, splitHom_tmul, emb_sigma_pow]
    rw [this, constA_splitHom, constA_splitHom]
    exact (galOA_tmul g o _).trans (congrArg (fun y : Ainf l => o ⊗ₜ[ℤ_[l]] y) (hm w))
  | add y y' h h' =>
    rw [map_add, map_add, map_add, h, h', ← map_add]
    rfl

/- English proof (translation)
Rewrite using `[idem, galOA_constA_shift t hm, idem]`. Use `congr 1`. Use `ext1 σ`. Simplify using `only [Pi.single_apply, sub_eq_iff_eq_add]`.
-/
theorem galOA_idem {g : GQ l} {m : ℕ}
    (hm : ∀ w : Wq l a, Per.σA g (wA l a w) = wA l a ((sigma l a ^ m) w)) (τ : ZMod a) :
    galOA O g (idem (constA t) τ) = idem (constA t) (τ + m) := by
  rw [idem, galOA_constA_shift t hm, idem]
  congr 1
  ext1 σ
  simp only [Pi.single_apply, sub_eq_iff_eq_add]

variable {e : ℕ} [NeZero e] (ϖ : PiSys l e)

/- English proof (translation)
Establish `hfix : ∀ n, k (ϖ.seq n ^ e) = ϖ.seq n ^ e` using `fun n => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk _ (IntermediateField.subset_adjoin _ _ ⟨n, rfl⟩)`. Use `Perfection.ext fun n => ?_` and prove the remaining obligations. Establish `key : ∀ x : Perfection (ModP (OC l) l) l, Perfection.coeff (ModP (OC l) l) l n (x ^ e) = Perfection.coeff (ModP (OC l) l) l n x ^ e` using `fun x => map_pow _ _ _`. Use `(key (ϖ.kummer k)).trans (Eq.trans ?_ (map_one (Perfection.coeff (ModP (OC l) l) l n)).symm)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ (ϖ.ratio k n) ^ e = 1`.

Rewrite using `[← map_pow, ← map_one (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}))]`. Use `congr 1`. Use `Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[SubmonoidClass.coe_pow, PiSys.coe_ratio, ← map_pow, div_pow, ← map_pow, hfix, div_self (pow_ne_zero _ (ϖ.seq_ne_zero n)), map_one]`. Both sides reduce to the same expression.
-/
theorem kummer_pow {k : GQ l} (hk : k ∈ ϖ.GKinf) : ϖ.kummer k ^ e = 1 := by
  have hfix : ∀ n, k (ϖ.seq n ^ e) = ϖ.seq n ^ e := fun n =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk _ (IntermediateField.subset_adjoin _ _ ⟨n, rfl⟩)
  refine Perfection.ext fun n => ?_
  have key : ∀ x : Perfection (ModP (OC l) l) l,
      Perfection.coeff (ModP (OC l) l) l n (x ^ e) = Perfection.coeff (ModP (OC l) l) l n x ^ e :=
    fun x => map_pow _ _ _
  refine (key (ϖ.kummer k)).trans (Eq.trans ?_ (map_one (Perfection.coeff (ModP (OC l) l) l n)).symm)
  change Ideal.Quotient.mk _ (ϖ.ratio k n) ^ e = 1
  rw [← map_pow, ← map_one (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}))]
  congr 1
  refine Subtype.ext ?_
  rw [SubmonoidClass.coe_pow, PiSys.coe_ratio, ← map_pow, div_pow, ← map_pow, hfix,
    div_self (pow_ne_zero _ (ϖ.seq_ne_zero n)), map_one]
  rfl

/- English proof (translation)
Establish `h1` using `kummer_pow ϖ hk`. Establish `h2 : ϖ.kummer k ∈ resSub l a`. Rewrite using `[mem_resSub, ← hsucc, pow_succ, h1, one_mul]`. Conclude with `⟨(⟨_, h2⟩ : Fq l a), rfl, Fq.val_injective l a (((map_pow (Fq.val l a) _ e).trans h1).trans (map_one _).symm)⟩`.
-/
theorem exists_kummer_eq (hsucc : e + 1 = l ^ a) {k : GQ l} (hk : k ∈ ϖ.GKinf) :
    ∃ z : Fq l a, Fq.val l a z = ϖ.kummer k ∧ z ^ e = 1 := by
  have h1 := kummer_pow ϖ hk
  have h2 : ϖ.kummer k ∈ resSub l a := by
    rw [mem_resSub, ← hsucc, pow_succ, h1, one_mul]
  exact ⟨(⟨_, h2⟩ : Fq l a), rfl, Fq.val_injective l a (((map_pow (Fq.val l a) _ e).trans h1).trans (map_one _).symm)⟩

variable [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]

omit [Fact l.Prime] in
/- English proof (translation)
Use extensionality with `n`. Rewrite using `[coeff_rescale, coeff_C]`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem rescale_C_eq {R : Type} [CommRing R] (b r : R) : rescale b (C r) = C r := by
  ext n
  rw [coeff_rescale, coeff_C]
  split_ifs with h
  · subst h; simp
  · simp

/- English proof (translation)
Use `set c : ZMod a → O := fun τ => emb t τ (WittVector.teichmuller l z) with hc`. Establish `hu : constA t c = 1 ⊗ₜ wA l a (WittVector.teichmuller l z)` using `constA_emb t _`. Establish `hk : galOA O k (ϖ.teichR O) = constA t c * ϖ.teichR O`. Rewrite using `[ϖ.galOA_teichR O k, hu, PiSys.mu, tmul_sub, ← Algebra.TensorProduct.one_def, add_sub_cancel, wA_teich, hz]`. Establish `hX' : ((galOA O k).toRingHom.comp (ϖ.evO O).toRingHom) X = constA t c * ϖ.teichR O`.

Express the relevant statement in the definitionally equal form `galOA O k (ϖ.evO O X) = _`. Rewrite using `[PiSys.evO_X, hk]`. Use `RingHom.congr_fun (ringHom_ext_of_sep ((galOA O k).toRingHom.comp (ϖ.evO O).toRingHom) ((glue (constA t) (ϖ.evO O)).toRingHom.comp (Pi.ringHom fun τ => rescale (c τ))) (fun r => ?_) ?_ ?_) h` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `galOA O k (ϖ.evO O (C r)) = glue (constA t) (ϖ.evO O) (fun τ => rescale (c τ) (C r))`. Simplify using `only [rescale_C_eq]`.

Rewrite using `[glue_const]`. Establish `h2 : ϖ.evO O (C r) = algebraMap O _ r` using `(ϖ.evO O).commutes r`. Rewrite using `[h2, AlgHom.commutes]`. Rewrite using `[hX']`. Express the relevant statement in the definitionally equal form `_ = glue (constA t) (ϖ.evO O) (fun τ => rescale (c τ) X)`.

Simplify using `only [rescale_X]`. Rewrite using `[glue_apply, eq_sum_idem (constA t) c, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, PiSys.evO_X, show ϖ.evO O (C (c τ)) = algebraMap O _ (c τ) from (ϖ.evO O).commutes _, mul_assoc]`. Introduce `x hx`.

Use `ϖ.sep_teichR O x fun n => ?_` and prove the remaining obligations. Take `⟨y, hy⟩` from `hx n`. Conclude with `⟨constA t c ^ n * y, by rw [hy, hX', mul_pow]; ring⟩`.
-/
theorem galOA_evO {k : GQ l} (z : Fq l a) (hz : Fq.val l a z = ϖ.kummer k) (h : O⟦X⟧) :
    galOA O k (ϖ.evO O h) =
      glue (constA t) (ϖ.evO O) fun τ => rescale (emb t τ (WittVector.teichmuller l z)) h := by
  set c : ZMod a → O := fun τ => emb t τ (WittVector.teichmuller l z) with hc
  have hu : constA t c = 1 ⊗ₜ wA l a (WittVector.teichmuller l z) := constA_emb t _
  have hk : galOA O k (ϖ.teichR O) = constA t c * ϖ.teichR O := by
    rw [ϖ.galOA_teichR O k, hu, PiSys.mu, tmul_sub, ← Algebra.TensorProduct.one_def, add_sub_cancel,
      wA_teich, hz]
  have hX' : ((galOA O k).toRingHom.comp (ϖ.evO O).toRingHom) X = constA t c * ϖ.teichR O := by
    change galOA O k (ϖ.evO O X) = _
    rw [PiSys.evO_X, hk]
  refine RingHom.congr_fun (ringHom_ext_of_sep ((galOA O k).toRingHom.comp (ϖ.evO O).toRingHom)
    ((glue (constA t) (ϖ.evO O)).toRingHom.comp (Pi.ringHom fun τ => rescale (c τ))) (fun r => ?_) ?_ ?_) h
  · change galOA O k (ϖ.evO O (C r)) = glue (constA t) (ϖ.evO O) (fun τ => rescale (c τ) (C r))
    simp only [rescale_C_eq]
    rw [glue_const]
    have h2 : ϖ.evO O (C r) = algebraMap O _ r := (ϖ.evO O).commutes r
    rw [h2, AlgHom.commutes]
  · rw [hX']
    change _ = glue (constA t) (ϖ.evO O) (fun τ => rescale (c τ) X)
    simp only [rescale_X]
    rw [glue_apply, eq_sum_idem (constA t) c, Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul, PiSys.evO_X, show ϖ.evO O (C (c τ)) = algebraMap O _ (c τ) from (ϖ.evO O).commutes _,
      mul_assoc]
  · intro x hx
    refine ϖ.sep_teichR O x fun n => ?_
    obtain ⟨y, hy⟩ := hx n
    exact ⟨constA t c ^ n * y, by rw [hy, hX', mul_pow]; ring⟩

variable (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a]

/- English proof (translation)
Take `⟨m, hm⟩` from `exists_sigma_pow (a := a) k`. Take `⟨z, hz, hze⟩` from `exists_kummer_eq (a := a) ϖ (TameDescentExponentData.succ_eq (K := K) (l := l) (e := e) (a := a)) hk`. Set `ζ : rootsOfUnity e K` to `rootsOfUnity.mkOfPowEq (algebraMap O K (t (WittVector.teichmuller l z))) (by`. Rewrite using `[← map_pow, ← map_pow, ← map_pow, hze, map_one, map_one, map_one])`. Use `⟨⟨ζ, Multiplicative.ofAdd (m : ZMod a)⟩, fun f f' hf' => ?_⟩` and prove the remaining obligations.

Use `set c : ZMod a → O := fun τ => emb t τ (WittVector.teichmuller l z) with hc`. Establish `hroot : ∀ τ, TameGal.root (⟨ζ, Multiplicative.ofAdd (m : ZMod a)⟩ : TameGal K l e a) τ = algebraMap O K (c τ)` using `fun τ => by`. Establish `h1 : c τ = t (WittVector.teichmuller l z) ^ l ^ (-τ).val`. Express the relevant statement in the definitionally equal form `t ((sigma l a ^ (-τ).val) (WittVector.teichmuller l z)) = _`. Rewrite using `[sigma_pow_teich, map_pow]`.

Rewrite using `[h1, map_pow]`. Express the relevant statement in the definitionally equal form `(((ζ ^ l ^ (-τ).val : rootsOfUnity e K) : Kˣ) : K) = _`. Rewrite using `[SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, rootsOfUnity.coe_mkOfPowEq]`. Establish `hf'' : ∀ τ, f' τ = equivA O K (rescale (c τ) ((equivA O K).symm (f (τ - m))))` using `fun τ => by`. Use `Subtype.ext ?_` and prove the remaining obligations.

Rewrite using `[hf' τ, ringAct_apply, hroot, coe_equivA, ← rescale_map, ← coe_equivA, AlgEquiv.apply_symm_apply]`. Both sides reduce to the same expression. Establish `hRHS : ϖ.iTot t K f' = ∑ τ, idem (constA t) τ * ϖ.evO O (rescale (c τ) ((equivA O K).symm (f (τ - m))))`. Rewrite using `[PiSys.iTot, glue_apply]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[hf'' τ, PiSys.iA_equivA]`. Rewrite using `[hRHS, PiSys.iTot, glue_apply, map_sum]`. Use `Fintype.sum_equiv (Equiv.addRight (m : ZMod a)) _ _ fun σ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, galOA_idem t hm, Equiv.coe_addRight, add_sub_cancel_right]`. Express the relevant statement in the definitionally equal form `_ * galOA O k (ϖ.evO O ((equivA O K).symm (f σ))) = _`.

Rewrite using `[galOA_evO t ϖ z hz, idem_mul_glue]`.
-/
theorem exists_covers {k : GQ l} (hk : k ∈ ϖ.GKinf) : ∃ γ : TameGal K l e a, Covers K t ϖ k γ := by
  obtain ⟨m, hm⟩ := exists_sigma_pow (a := a) k
  obtain ⟨z, hz, hze⟩ := exists_kummer_eq (a := a) ϖ (TameDescentExponentData.succ_eq (K := K) (l := l) (e := e) (a := a)) hk
  let ζ : rootsOfUnity e K := rootsOfUnity.mkOfPowEq (algebraMap O K (t (WittVector.teichmuller l z))) (by
    rw [← map_pow, ← map_pow, ← map_pow, hze, map_one, map_one, map_one])
  refine ⟨⟨ζ, Multiplicative.ofAdd (m : ZMod a)⟩, fun f f' hf' => ?_⟩
  set c : ZMod a → O := fun τ => emb t τ (WittVector.teichmuller l z) with hc
  have hroot : ∀ τ, TameGal.root (⟨ζ, Multiplicative.ofAdd (m : ZMod a)⟩ : TameGal K l e a) τ =
      algebraMap O K (c τ) := fun τ => by
    have h1 : c τ = t (WittVector.teichmuller l z) ^ l ^ (-τ).val := by
      change t ((sigma l a ^ (-τ).val) (WittVector.teichmuller l z)) = _
      rw [sigma_pow_teich, map_pow]
    rw [h1, map_pow]
    change (((ζ ^ l ^ (-τ).val : rootsOfUnity e K) : Kˣ) : K) = _
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, rootsOfUnity.coe_mkOfPowEq]
  have hf'' : ∀ τ, f' τ = equivA O K (rescale (c τ) ((equivA O K).symm (f (τ - m)))) := fun τ => by
    refine Subtype.ext ?_
    rw [hf' τ, ringAct_apply, hroot, coe_equivA, ← rescale_map, ← coe_equivA, AlgEquiv.apply_symm_apply]
    rfl
  have hRHS : ϖ.iTot t K f' =
      ∑ τ, idem (constA t) τ * ϖ.evO O (rescale (c τ) ((equivA O K).symm (f (τ - m)))) := by
    rw [PiSys.iTot, glue_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hf'' τ, PiSys.iA_equivA]
  rw [hRHS, PiSys.iTot, glue_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.addRight (m : ZMod a)) _ _ fun σ => ?_
  rw [map_mul, galOA_idem t hm, Equiv.coe_addRight, add_sub_cancel_right]
  change _ * galOA O k (ϖ.evO O ((equivA O K).symm (f σ))) = _
  rw [galOA_evO t ϖ z hz, idem_mul_glue]

end GlobalTheory.KinfCover

open GlobalTheory.KinfCover in

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ K _ _ _ _ _ _ _ _ _ _ t ϖ _ hk` and use `exists_covers t ϖ K hk`.
-/
theorem GlobalTheory.KinfCover.exists_covers_of_mem_GKinf : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), ∀ k ∈ ϖ.GKinf, ∃ γ : TameGal K l e a, Covers K t ϖ k γ :=
  fun _ _ _ _ _ _ _ K _ _ _ _ _ _ _ _ _ _ t ϖ _ hk => exists_covers t ϖ K hk

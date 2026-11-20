import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.FixOfPerp

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

variable {k r : ℕ}

/- English proof (translation)
Establish `hF : ∀ w : Fin (r + 1) → EE k r, Orthonormal ℂ w → (∀ a b, inner ℂ (w a) (HE k r (w b)) = 0) → Orthonormal ℂ (Sum.elim w (fun a => HE k r (w a)))`. Introduce `w hw hwi`. Rewrite `hw`, the goal using `[orthonormal_iff_ite]`. Introduce and unpack `(a | a) (b | b)`. Simplify using `[hw]`.

Simplify using `[hwi]`. Simplify using `[HE_adj, hwi]`. Simplify using `[HE_adj, HE_HE, hw]`. Establish `hcard : Module.finrank ℂ (EE k r) = Fintype.card ((Fin (r + 1) ⊕ Fin (r + 1)) ⊕ Fin (k - 1))` using `by simp; omega`. Establish `hres : ∀ w : Fin (r + 1) ⊕ Fin (r + 1) → EE k r, Orthonormal ℂ w → Orthonormal ℂ ((Set.range (Sum.inl : _ → (Fin (r + 1) ⊕ Fin (r + 1)) ⊕ Fin (k - 1))).restrict (Sum.elim w 0))`.

Introduce `w hw`. Rewrite `hw`, the goal using `[orthonormal_iff_ite]`. Introduce and unpack `⟨x, hx⟩ ⟨y, hy⟩`. Take `⟨p, rfl⟩` from `hx`. Take `⟨q, rfl⟩` from `hy`.

Express the relevant statement in the definitionally equal form `inner ℂ (w p) (w q) = _`. Rewrite using `[hw p q]`. Distinguish the cases in `hpq : p = q`. Substitute `hpq` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl]`.

Rewrite using `[if_neg hpq, if_neg]`. Introduce `h`. Conclude with `hpq (Sum.inl_injective (congrArg Subtype.val h))`. Take `⟨bP, hbP⟩` from `Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard (hres _ (hF c hc hci))`. Take `⟨bQ, hbQ⟩` from `Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard (hres _ (hF u hu hui))`.

Establish `hP : ∀ p, bP (Sum.inl p) = Sum.elim c (fun a => HE k r (c a)) p` using `fun p => hbP _ ⟨p, rfl⟩`. Establish `hQ : ∀ p, bQ (Sum.inl p) = Sum.elim u (fun a => HE k r (u a)) p` using `fun p => hbQ _ ⟨p, rfl⟩`. Use `set κL := bP.repr.trans bQ.repr.symm with hκL`. Establish `hκb : ∀ i, κL (bP i) = bQ i` using `fun i => by simp [hκL]`. Establish `hc1 : ∀ a, κL (c a) = u a` using `fun a => by`.

Use `hκb (Sum.inl (Sum.inl a))` as an intermediate fact. Rewrite `this` using `[hP, hQ]`. Then use the resulting hypothesis. Establish `hc2 : ∀ a, κL (HE k r (c a)) = HE k r (u a)` using `fun a => by`. Use `hκb (Sum.inl (Sum.inr a))` as an intermediate fact. Rewrite `this` using `[hP, hQ]`. Then use the resulting hypothesis.

Establish `hfix : ∀ (b : OrthonormalBasis ((Fin (r + 1) ⊕ Fin (r + 1)) ⊕ Fin (k - 1)) ℂ (EE k r)) (w : Fin (r + 1) → EE k r), Orthonormal ℂ w → (∀ a b, inner ℂ (w a) (HE k r (w b)) = 0) → (∀ p, b (Sum.inl p) = Sum.elim w (fun a => HE k r (w a)) p) → ∀ j, HE k r (b (Sum.inr j)) = b (Sum.inr …`. Introduce `b w hw hwi hb j`. Use `fix_of_perp w hw hwi _ (fun a => ?_) (fun a => ?_)` and prove the remaining obligations. Use `hb (Sum.inl a)` as an intermediate fact. Simplify using `only [Sum.elim_inl] at this`.

Rewrite using `[← this]; exact b.orthonormal.2 (by simp)`. Use `hb (Sum.inr a)` as an intermediate fact. Simplify using `only [Sum.elim_inr] at this`. Rewrite using `[← this]; exact b.orthonormal.2 (by simp)`. Use `⟨κL, hc1, fun x => ?_⟩` and prove the remaining obligations.

Establish `key : (κL.toLinearEquiv.toLinearMap).comp (HE k r) = (HE k r).comp κL.toLinearEquiv.toLinearMap`. Use `bP.toBasis.ext fun i => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, OrthonormalBasis.coe_toBasis, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]`. Break down `i with (a | a) | j` into its components or cases. Rewrite using `[hP, Sum.elim_inl, hc2, hc1]`.

Rewrite using `[hP, Sum.elim_inr, HE_HE, hc1, hc2, HE_HE]`. Rewrite using `[hfix bP c hc hci hP j, hκb, hfix bQ u hu hui hQ j]`. Simplify using `using LinearMap.congr_fun key x`.
-/
theorem exists_K (hk : 1 ≤ k) (c u : Fin (r + 1) → EE k r) (hc : Orthonormal ℂ c) (hu : Orthonormal ℂ u)
    (hci : ∀ a b, inner ℂ (c a) (HE k r (c b)) = 0) (hui : ∀ a b, inner ℂ (u a) (HE k r (u b)) = 0) :
    ∃ κL : EE k r ≃ₗᵢ[ℂ] EE k r, (∀ a, κL (c a) = u a) ∧ ∀ x, κL (HE k r x) = HE k r (κL x) := by
  have hF : ∀ w : Fin (r + 1) → EE k r, Orthonormal ℂ w → (∀ a b, inner ℂ (w a) (HE k r (w b)) = 0) →
      Orthonormal ℂ (Sum.elim w (fun a => HE k r (w a))) := by
    intro w hw hwi
    rw [orthonormal_iff_ite] at hw ⊢
    rintro (a | a) (b | b)
    · simp [hw]
    · simp [hwi]
    · simp [HE_adj, hwi]
    · simp [HE_adj, HE_HE, hw]
  have hcard : Module.finrank ℂ (EE k r) = Fintype.card ((Fin (r + 1) ⊕ Fin (r + 1)) ⊕ Fin (k - 1)) := by
    simp; omega
  have hres : ∀ w : Fin (r + 1) ⊕ Fin (r + 1) → EE k r, Orthonormal ℂ w →
      Orthonormal ℂ ((Set.range (Sum.inl : _ → (Fin (r + 1) ⊕ Fin (r + 1)) ⊕ Fin (k - 1))).restrict
        (Sum.elim w 0)) := by
    intro w hw
    rw [orthonormal_iff_ite] at hw ⊢
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    change inner ℂ (w p) (w q) = _
    rw [hw p q]
    by_cases hpq : p = q
    · subst hpq; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg hpq, if_neg]; intro h; exact hpq (Sum.inl_injective (congrArg Subtype.val h))
  obtain ⟨bP, hbP⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard (hres _ (hF c hc hci))
  obtain ⟨bQ, hbQ⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard (hres _ (hF u hu hui))
  have hP : ∀ p, bP (Sum.inl p) = Sum.elim c (fun a => HE k r (c a)) p := fun p => hbP _ ⟨p, rfl⟩
  have hQ : ∀ p, bQ (Sum.inl p) = Sum.elim u (fun a => HE k r (u a)) p := fun p => hbQ _ ⟨p, rfl⟩
  set κL := bP.repr.trans bQ.repr.symm with hκL
  have hκb : ∀ i, κL (bP i) = bQ i := fun i => by simp [hκL]
  have hc1 : ∀ a, κL (c a) = u a := fun a => by
    have := hκb (Sum.inl (Sum.inl a)); rwa [hP, hQ] at this
  have hc2 : ∀ a, κL (HE k r (c a)) = HE k r (u a) := fun a => by
    have := hκb (Sum.inl (Sum.inr a)); rwa [hP, hQ] at this
  have hfix : ∀ (b : OrthonormalBasis ((Fin (r + 1) ⊕ Fin (r + 1)) ⊕ Fin (k - 1)) ℂ (EE k r))
      (w : Fin (r + 1) → EE k r), Orthonormal ℂ w → (∀ a b, inner ℂ (w a) (HE k r (w b)) = 0) →
      (∀ p, b (Sum.inl p) = Sum.elim w (fun a => HE k r (w a)) p) →
      ∀ j, HE k r (b (Sum.inr j)) = b (Sum.inr j) := by
    intro b w hw hwi hb j
    refine fix_of_perp w hw hwi _ (fun a => ?_) (fun a => ?_)
    · have := hb (Sum.inl a); simp only [Sum.elim_inl] at this
      rw [← this]; exact b.orthonormal.2 (by simp)
    · have := hb (Sum.inr a); simp only [Sum.elim_inr] at this
      rw [← this]; exact b.orthonormal.2 (by simp)
  refine ⟨κL, hc1, fun x => ?_⟩
  have key : (κL.toLinearEquiv.toLinearMap).comp (HE k r) = (HE k r).comp κL.toLinearEquiv.toLinearMap := by
    refine bP.toBasis.ext fun i => ?_
    simp only [LinearMap.comp_apply, OrthonormalBasis.coe_toBasis, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv]
    rcases i with (a | a) | j
    · rw [hP, Sum.elim_inl, hc2, hc1]
    · rw [hP, Sum.elim_inr, HE_HE, hc1, hc2, HE_HE]
    · rw [hfix bP c hc hci hP j, hκb, hfix bQ u hu hui hQ j]
  simpa using LinearMap.congr_fun key x

/- English proof (translation)
Take `⟨κL, hκc, hκH⟩` from `exists_K hk c u hc hu hci hui`. Use `set κ : Mat k r := Matrix.toEuclideanLin.symm κL.toLinearEquiv.toLinearMap with hκdef`. Establish `hκ : ∀ v, (WithLp.toLp 2 (κ *ᵥ v) : EE k r) = κL (WithLp.toLp 2 v)`. Introduce `v`. Establish `h1 : Matrix.toEuclideanLin κ = κL.toLinearEquiv.toLinearMap` using `LinearEquiv.apply_symm_apply _ _`.

Use `LinearMap.congr_fun h1 (WithLp.toLp 2 v)` as an intermediate fact. Rewrite `this` using `[Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp]`. Conclude with `this`. Establish `hunit : κᴴ * κ = 1`. Use extensionality with `i j`.

Establish `h2 : inner ℂ (WithLp.toLp 2 (κ *ᵥ Pi.single i 1) : EE k r) (WithLp.toLp 2 (κ *ᵥ Pi.single j 1)) = inner ℂ (WithLp.toLp 2 (Pi.single i 1) : EE k r) (WithLp.toLp 2 (Pi.single j 1))`. Rewrite using `[hκ, hκ, LinearIsometryEquiv.inner_map_map]`. Simplify using `only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, dotProduct] at h2`. Simplify using `only [mul_apply, conjTranspose_apply, one_apply]`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `[mulVec_single, mul_comm]`. Simplify using `[Pi.single_apply, eq_comm]`. Establish `hv : ∀ v, κ *ᵥ (Hpk k r *ᵥ v) = Hpk k r *ᵥ (κ *ᵥ v)`. Introduce `v`.

Use `hκH (WithLp.toLp 2 v)` as an intermediate fact. Rewrite `this` using `[HE_apply, WithLp.ofLp_toLp, ← hκ, ← hκ, HE_apply, WithLp.ofLp_toLp]`. Simplify using `using congrArg WithLp.ofLp this`. Establish `hcomm : κ * Hpk k r = Hpk k r * κ`. Use extensionality with `i j`.

Use `congrFun (hv (Pi.single j 1)) i` as an intermediate fact. Rewrite `this` using `[mulVec_mulVec, mulVec_mulVec]`. Simplify `this` using `[mulVec, dotProduct, Pi.single_apply]`. Use `⟨κ, ⟨?_, hunit⟩, fun a => ?_⟩` and prove the remaining obligations. Use `show κᴴ * Hpk k r * κ = Hpk k r`.

Rewrite using `[Matrix.mul_assoc, ← hcomm, ← Matrix.mul_assoc, hunit, Matrix.one_mul]`. Rewrite using `[hκ, WithLp.toLp_ofLp, hκc]`.
-/
theorem exists_Kmat (hk : 1 ≤ k) (c u : Fin (r + 1) → EE k r) (hc : Orthonormal ℂ c) (hu : Orthonormal ℂ u)
    (hci : ∀ a b, inner ℂ (c a) (HE k r (c b)) = 0) (hui : ∀ a b, inner ℂ (u a) (HE k r (u b)) = 0) :
    ∃ κ ∈ Kset k r, ∀ a, (WithLp.toLp 2 (κ *ᵥ (c a).ofLp) : EE k r) = u a := by
  obtain ⟨κL, hκc, hκH⟩ := exists_K hk c u hc hu hci hui
  set κ : Mat k r := Matrix.toEuclideanLin.symm κL.toLinearEquiv.toLinearMap with hκdef
  have hκ : ∀ v, (WithLp.toLp 2 (κ *ᵥ v) : EE k r) = κL (WithLp.toLp 2 v) := by
    intro v
    have h1 : Matrix.toEuclideanLin κ = κL.toLinearEquiv.toLinearMap := LinearEquiv.apply_symm_apply _ _
    have := LinearMap.congr_fun h1 (WithLp.toLp 2 v)
    rw [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp] at this
    exact this
  have hunit : κᴴ * κ = 1 := by
    ext i j
    have h2 : inner ℂ (WithLp.toLp 2 (κ *ᵥ Pi.single i 1) : EE k r) (WithLp.toLp 2 (κ *ᵥ Pi.single j 1)) =
        inner ℂ (WithLp.toLp 2 (Pi.single i 1) : EE k r) (WithLp.toLp 2 (Pi.single j 1)) := by
      rw [hκ, hκ, LinearIsometryEquiv.inner_map_map]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, dotProduct] at h2
    simp only [mul_apply, conjTranspose_apply, one_apply]
    convert h2 using 1
    · refine Finset.sum_congr rfl fun m _ => ?_
      simp [mulVec_single, mul_comm]
    · simp [Pi.single_apply, eq_comm]
  have hv : ∀ v, κ *ᵥ (Hpk k r *ᵥ v) = Hpk k r *ᵥ (κ *ᵥ v) := by
    intro v
    have := hκH (WithLp.toLp 2 v)
    rw [HE_apply, WithLp.ofLp_toLp, ← hκ, ← hκ, HE_apply, WithLp.ofLp_toLp] at this
    simpa using congrArg WithLp.ofLp this
  have hcomm : κ * Hpk k r = Hpk k r * κ := by
    ext i j
    have := congrFun (hv (Pi.single j 1)) i
    rw [mulVec_mulVec, mulVec_mulVec] at this
    simpa [mulVec, dotProduct, Pi.single_apply] using this
  refine ⟨κ, ⟨?_, hunit⟩, fun a => ?_⟩
  · show κᴴ * Hpk k r * κ = Hpk k r
    rw [Matrix.mul_assoc, ← hcomm, ← Matrix.mul_assoc, hunit, Matrix.one_mul]
  · rw [hκ, WithLp.toLp_ofLp, hκc]

/- English proof (translation)
Use `first`. Consider the case `(simp [bvec, PiLp.inner_apply, Pi.single_apply])`. Consider the case `(show inner ℂ (EuclideanSpace.single i (1 : ℂ)) (WithLp.toLp 2 v : EE k r) = v i`. Rewrite using `[EuclideanSpace.inner_single_left]`. Use the proof step `simp)`.
-/
theorem inner_bvec (i : Fin (2 * r + k + 1)) (v : Fin (2 * r + k + 1) → ℂ) :
    inner ℂ (WithLp.toLp 2 (bvec i) : EE k r) (WithLp.toLp 2 v) = v i := by
  first
    | (simp [bvec, PiLp.inner_apply, Pi.single_apply])
    | (show inner ℂ (EuclideanSpace.single i (1 : ℂ)) (WithLp.toLp 2 v : EE k r) = v i
       rw [EuclideanSpace.inner_single_left]; simp)

/- English proof (translation)
Unfold `phiV`. Distinguish the cases in `hb : (b : ℕ) < r`. Rewrite using `[dif_pos hb, if_pos hb] show (Pi.single (esI k r ⟨b.val, hb⟩) (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) i = _`. Rewrite using `[Pi.single_apply]`. Distinguish the cases in `hi : (i : ℕ) = 2 * r + k - b.val`.

Rewrite using `[if_pos hi, if_pos (show i = esI k r ⟨b.val, hb⟩ from Fin.ext hi)]`. Rewrite using `[if_neg hi, if_neg (show ¬ i = esI k r ⟨b.val, hb⟩ from fun h => hi (congrArg Fin.val h))]`. Rewrite using `[dif_neg hb, if_neg hb]`. Simplify using `[epsV, bvec, Pi.single_apply, Fin.ext_iff]`. Apply the tactic sequence `have e1 : ((wI k r 0 : Fin (2 * r + k + 1)) : ℕ) = r := by first | rfl | simp [wI]`.

Apply the tactic sequence `have e2 : ((wI k r (Fin.last k) : Fin (2 * r + k + 1)) : ℕ) = r + k := by first | rfl | simp [wI]`. Rewrite using `[e1, e2]`.
-/
theorem phiV_apply (b : Fin (r + 1)) (i : Fin (2 * r + k + 1)) :
    phiV k r b i = if b.val < r then (if i.val = 2 * r + k - b.val then 1 else 0) else
      ((Real.sqrt 2)⁻¹ : ℂ) * ((if i.val = r then 1 else 0) + (if i.val = r + k then 1 else 0)) := by
  unfold phiV
  by_cases hb : (b : ℕ) < r
  · rw [dif_pos hb, if_pos hb]
    show (Pi.single (esI k r ⟨b.val, hb⟩) (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) i = _
    rw [Pi.single_apply]
    by_cases hi : (i : ℕ) = 2 * r + k - b.val
    · rw [if_pos hi, if_pos (show i = esI k r ⟨b.val, hb⟩ from Fin.ext hi)]
    · rw [if_neg hi, if_neg (show ¬ i = esI k r ⟨b.val, hb⟩ from fun h => hi (congrArg Fin.val h))]
  · rw [dif_neg hb, if_neg hb]
    simp [epsV, bvec, Pi.single_apply, Fin.ext_iff]
    have e1 : ((wI k r 0 : Fin (2 * r + k + 1)) : ℕ) = r := by first | rfl | simp [wI]
    have e2 : ((wI k r (Fin.last k) : Fin (2 * r + k + 1)) : ℕ) = r + k := by first | rfl | simp [wI]
    rw [e1, e2]

/- English proof (translation)
Use extensionality with `i`. Distinguish the cases in `ha : a.val < r`. Simplify using `[ha, phiV_apply, bvec, Pi.single_apply, Fin.ext_iff]`. Simplify using `[ha, phiV_apply, bvec, Pi.single_apply, Fin.ext_iff, mul_add, mul_ite]`.
-/
theorem toLp_phiV (a : Fin (r + 1)) : (WithLp.toLp 2 (phiV k r a) : EE k r) =
    if a.val < r then WithLp.toLp 2 (bvec ⟨2 * r + k - a.val, by omega⟩) else
      ((Real.sqrt 2)⁻¹ : ℂ) • (WithLp.toLp 2 (bvec ⟨r, by omega⟩) + WithLp.toLp 2 (bvec ⟨r + k, by omega⟩)) := by
  ext i
  by_cases ha : a.val < r
  · simp [ha, phiV_apply, bvec, Pi.single_apply, Fin.ext_iff]
  · simp [ha, phiV_apply, bvec, Pi.single_apply, Fin.ext_iff, mul_add, mul_ite]

/- English proof (translation)
Establish `h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2`. Rewrite using `[← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num`. Establish `hs : star ((Real.sqrt 2 : ℂ))⁻¹ = ((Real.sqrt 2 : ℂ))⁻¹` using `by first`. Consider the case `(rw [star_inv₀]; congr 1; exact Complex.conj_ofReal _)`. Consider the case `simp`.

Rewrite using `[hs, ← mul_inv, h2]`. Evaluate the numerical expressions.
-/
theorem hcc : star ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = 1 / 2 := by
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hs : star ((Real.sqrt 2 : ℂ))⁻¹ = ((Real.sqrt 2 : ℂ))⁻¹ := by
    first
      | (rw [star_inv₀]; congr 1; exact Complex.conj_ofReal _)
      | simp
  rw [hs, ← mul_inv, h2]; norm_num

/- English proof (translation)
Establish `key : (starRingEnd ℂ) ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2` using `hcc`. Rewrite using `[orthonormal_iff_ite]`. Introduce `a b`. Establish `hA` using `a.isLt`. Establish `hB` using `b.isLt`.

Rewrite using `[toLp_phiV]`. Distinguish the cases in `ha : a.val < r`. Apply the tactic sequence `rw [if_pos ha, inner_bvec, phiV_apply] split_ifs <;> first`. Consider the case `rfl`. Consider the case `(exfalso; (try simp only [Fin.val_mk, Fin.ext_iff] at *) <;> omega)`.

Consider the case `simp`. Apply the tactic sequence `rw [if_neg ha, inner_smul_left, inner_add_left, inner_bvec, inner_bvec, phiV_apply, phiV_apply] split_ifs <;> first`. Consider the case `(exfalso; (try simp only [Fin.val_mk, Fin.ext_iff] at *) <;> omega)`. Consider the case `(exfalso; exact ‹¬a = b› (Fin.ext (by omega)))`. Consider the case `(exfalso; simp_all; done)`.

Consider the case `(exfalso; simp_all <;> omega)`. Consider the case `(simp; done)`. Consider the case `(simp only [add_zero, zero_add, mul_one]; linear_combination (2 : ℂ) * key)`.
-/
theorem qe_orth (hk : 1 ≤ k) : Orthonormal ℂ (fun a => (WithLp.toLp 2 (phiV k r a) : EE k r)) := by
  have key : (starRingEnd ℂ) ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := hcc
  rw [orthonormal_iff_ite]
  intro a b
  have hA := a.isLt
  have hB := b.isLt
  rw [toLp_phiV]
  by_cases ha : a.val < r
  · rw [if_pos ha, inner_bvec, phiV_apply]
    split_ifs <;> first
      | rfl
      | (exfalso; (try simp only [Fin.val_mk, Fin.ext_iff] at *) <;> omega)
      | simp
  · rw [if_neg ha, inner_smul_left, inner_add_left, inner_bvec, inner_bvec, phiV_apply, phiV_apply]
    split_ifs <;> first
      | (exfalso; (try simp only [Fin.val_mk, Fin.ext_iff] at *) <;> omega)
      | (exfalso; exact ‹¬a = b› (Fin.ext (by omega)))
      | (exfalso; simp_all; done)
      | (exfalso; simp_all <;> omega)
      | (simp; done)
      | (simp only [add_zero, zero_add, mul_one]; linear_combination (2 : ℂ) * key)

end ReciprocityTheory.ChartRestriction.DS.Xi.GS

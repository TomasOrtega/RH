import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsRowFrame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacterArgumentFirstParabolicShift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralDivUniformizerOfRedZero

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.TwU Classical GlobalTheory.QNormal GlobalTheory.UnfoldLaw

noncomputable section

namespace GlobalTheory.UnfoldTwoSided

section Affine

variable {F : Type} [Field F] {n' c' n c : ℕ} {r : (Fin (n' + c') → F) ≃ₗ[F] (Fin (n' + c') → F)} {g : (Fin n' → F) ≃ₗ[F] (Fin n' → F)}

/- English proof (translation)
Take `⟨h1, -, h3⟩` from `(Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.unfoldingAffineSpace_mem_iff_intrinsic F n' c' n c hc hc' xj (Loc.xx1 xj t)).1 ⟨t, rfl⟩`. Generalize the expression as in `Loc.xx1 xj t = x at h1 h3`. Unfold `Loc.chArg Loc.n1Arg`. Rewrite using `[show c' - 1 = c by omega, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations.

Establish `b3` using `Proof.unfoldingCharacterArgument_comp_unipotentRadicals.atN_map h1 h3 (Finset.mem_range.1 hi) (hr.2.2 (i + 1))`. Establish `b4 : Loc.atN (Loc.eN F (n' + c') (n' + (i + 1))) (n' + i) = 0` using `Proof.unfoldingCharacterArgument_comp_unipotentRadicals.atN_eN_succ _ _`. Simplify using `only [map_sub, atN_sub, b4] at b3`. Express the relevant statement in the definitionally equal form `Loc.atN (x (r (Loc.eN F (n' + c') (n' + (i + 1))))) (n + i) = Loc.atN (x (Loc.eN F (n' + c') (n' + (i + 1)))) (n + i) + Loc.atN (r (Loc.eN F (n' + c') (n' + (i + 1)))) (n' + i)`. Take the linear combination `b3`.
-/
theorem chArg_right (hc : 1 ≤ c) (hc' : c' = c + 1) (hr : Loc.R1cond F n' c' r) (xj : (Fin n' → F) →ₗ[F] (Fin n → F))
    (t : Loc.FC n' c' n c → F) : Loc.chArg (Loc.xx1 xj t ∘ₗ r.toLinearMap) = Loc.chArg (Loc.xx1 xj t) + Loc.n1Arg r := by
  obtain ⟨h1, -, h3⟩ := (Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.unfoldingAffineSpace_mem_iff_intrinsic F n' c' n c hc hc' xj (Loc.xx1 xj t)).1 ⟨t, rfl⟩
  generalize Loc.xx1 xj t = x at h1 h3
  unfold Loc.chArg Loc.n1Arg
  rw [show c' - 1 = c by omega, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have b3 := Proof.unfoldingCharacterArgument_comp_unipotentRadicals.atN_map h1 h3 (Finset.mem_range.1 hi) (hr.2.2 (i + 1))
  have b4 : Loc.atN (Loc.eN F (n' + c') (n' + (i + 1))) (n' + i) = 0 := Proof.unfoldingCharacterArgument_comp_unipotentRadicals.atN_eN_succ _ _
  simp only [map_sub, atN_sub, b4] at b3
  change Loc.atN (x (r (Loc.eN F (n' + c') (n' + (i + 1))))) (n + i) =
    Loc.atN (x (Loc.eN F (n' + c') (n' + (i + 1)))) (n + i) + Loc.atN (r (Loc.eN F (n' + c') (n' + (i + 1)))) (n' + i)
  linear_combination b3

/- English proof (translation)
Take `⟨y, T, b, h⟩` from `Proof.unipotentRadicals_act_affine_unfoldingSpaces.affine_action Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.unfoldingAffineSpace_mem_iff_intrinsic F n' c' n c hc hc' 1 (one_mem _) r hr (xj ∘ₗ g.toLinearMap)`. Take `rfl : y = xj` from `LinearMap.ext fun v => by`. Take `⟨v, rfl⟩` from `g.surjective v`. Use `LinearMap.congr_fun (h 0) (Loc.inX F n' c' v)` as an intermediate fact. Express the relevant statement in the definitionally equal form `Loc.xx1 y 0 (r (Loc.inX F n' c' v)) = _ at this`.

Rewrite `this` using `[hg, unfoldingAffinePointMap_apply_inclusion, unfoldingAffinePointMap_apply_inclusion]`. Conclude with `inX_injective this`. Conclude with `⟨T.toEquiv.trans (Equiv.addRight b), h⟩`.
-/
theorem exists_move_right (hc : 1 ≤ c) (hc' : c' = c + 1) (hr : r ∈ Loc.R1 F n' c')
    (hg : ∀ x, r (Loc.inX F n' c' x) = Loc.inX F n' c' (g x)) (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) :
    ∃ T : (Loc.FC n' c' n c → F) ≃ (Loc.FC n' c' n c → F),
      ∀ t, Loc.xx1 xj t ∘ₗ r.toLinearMap = Loc.xx1 (xj ∘ₗ g.toLinearMap) (T t) := by
  obtain ⟨y, T, b, h⟩ := Proof.unipotentRadicals_act_affine_unfoldingSpaces.affine_action Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.unfoldingAffineSpace_mem_iff_intrinsic F n' c' n c hc hc' 1 (one_mem _) r hr
    (xj ∘ₗ g.toLinearMap)
  obtain rfl : y = xj := LinearMap.ext fun v => by
    obtain ⟨v, rfl⟩ := g.surjective v
    have := LinearMap.congr_fun (h 0) (Loc.inX F n' c' v)
    change Loc.xx1 y 0 (r (Loc.inX F n' c' v)) = _ at this
    rw [hg, unfoldingAffinePointMap_apply_inclusion, unfoldingAffinePointMap_apply_inclusion] at this
    exact inX_injective this
  exact ⟨T.toEquiv.trans (Equiv.addRight b), h⟩

end Affine

section Local

open Proof.NormalFormAtPrime Proof.boxSum_ne_zero_invariant_affineChange

variable {E : Type} [Field E] [NumberField E] {K : Type} [Field K] {P : HeightOneSpectrum (𝓞 E)} {n' c' n c : ℕ}

/- English proof (translation)
Establish `q0` using `qOf_ne_zero P`. Establish `hqk : ∀ k : ℕ, ∀ z ∈ H, (qOf P : E) ^ k • z ∈ H` using `fun k z hz => by`. Proceed by induction on `k with`. Consider the case `zero => simpa using hz`. Consider the case `succ k ih => rw [pow_succ', mul_smul]`.

Conclude with `hq _ ih`. Establish `hneg : ∀ {u : E}, IntAt P ((qOf P : E) ^ D * u) → IntAt P ((qOf P : E) ^ D * -u)` using `fun h => by`. Simplify using `using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg h`. Establish `hpt : ∀ t, integrand psi Psi xj' (T t) * a = (psi d)⁻¹ * b * integrand psi Psi xj t`. Introduce `t`.

Unfold `integrand`. Rewrite using `[← hT, mul_right_comm, law]`. Distinguish the cases in `h0 : Psi (Loc.xx1 xj t) = 0`. Simplify using `[h0]`. Establish `a1` using `hch _ (hs _ h0)`.

Establish `a2` using `hch _ ((hH _).2 (hs _ h0))`. Rewrite `a2`, the goal using `[hd]`. Establish `a3 : IntAt P ((qOf P : E) ^ D * d)`. Use `a2.add (hneg a1) using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Establish `a4` using `hpsi.1 _ _ a3 (hneg a3)`. Rewrite `a4` using `[add_neg_cancel, hpsi.2 0 (IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P)]`. Rewrite using `[neg_add, hpsi.1 _ _ (hneg a1) (hneg a3), ← eq_inv_of_mul_eq_one_right a4.symm]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsupp : ∀ y t, integrand psi Psi y t ≠ 0 → t ∈ lat P (Loc.FC n' c' n c) ((qOf P : E) ^ A)` using `fun y t h p => by`.

Use `(intHom_iff _).1 (hb _ (hs _ (left_ne_zero_of_mul h))) p.1.2 p.1.1` as an intermediate fact. Rewrite `this` using `[LinearMap.smul_apply, Pi.smul_apply, Proof.unipotentRadicals_act_affine_unfoldingSpaces.unfoldingAffineLinearMap_apply_freeEntry]`. Conclude with `intAt_pow_mono hA this`. Set `M : AddSubgroup (Loc.FC n' c' n c → E)` to `H.comap (((qOf P : E) ^ D)⁻¹ • Proof.unipotentRadicals_act_affine_unfoldingSpaces.linPart (0 : (Fin n' → E) →ₗ[E] (Fin n → E))).toAddMonoidHom`. Establish `mM : ∀ u, u ∈ M ↔ ((qOf P : E) ^ D)⁻¹ • Proof.unipotentRadicals_act_affine_unfoldingSpaces.linPart (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) u ∈ H` using `fun u => Iff.rfl`.

Establish `key` using `sum_reps_equiv (M₀ := lat P (Loc.FC n' c' n c) ((qOf P : E) ^ B)⁻¹) (M := M) (M₁ := lat P (Loc.FC n' c' n c) ((qOf P : E) ^ A)) (Fintype.piFinset fun _ => LocE.valsQ E (qOf P) A B) (fun u hu => by`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hB`. Establish `h1 : IntHom P (((qOf P : E) ^ (m + D + k))⁻¹ • Proof.unipotentRadicals_act_affine_unfoldingSpaces.linPart (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) u)` using `(intHom_iff _).2 fun s l => by`. Rewrite using `[LinearMap.smul_apply, Pi.smul_apply, linPart_single, smul_eq_mul]`. Use `split_ifs`.

Conclude with `hu _`. Simplify using `using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P`. Rewrite using `[mM]`. Use `hqk k _ (hb' _ h1) using 1` and compare the differences between its conclusion and the goal. Rewrite using `[smul_smul, smul_smul]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Use the proof step `ring)`. Use the proof step `(fun u hu p => by`. Use `(intHom_iff _).1 (hb _ (hqk D _ ((mM u).1 hu))) p.1.2 p.1.1` as an intermediate fact.

Rewrite `this` using `[smul_inv_smul₀ (pow_ne_zero _ q0), LinearMap.smul_apply, Pi.smul_apply, linPart_single, dif_pos p.2]`. Conclude with `intAt_pow_mono hA this)`. Use the proof step `(fun s hs s' hs' h => funext fun i => (Proof.rationalFractions_represent_primeNormQuotient.valsQ_reps E P hP A B).1 _ (Fintype.mem_piFinset.1 hs i) _ (Fintype.mem_piFinset.1 hs' i) (h i))`. Use the proof step `(fun v hv => by choose s hs hs' using fun i => (Proof.rationalFractions_represent_primeNormQuotient.valsQ_reps E P hP A B).2 (v i) (hv i)`. Conclude with `⟨s, Fintype.mem_piFinset.2 hs, hs'⟩)`.

Use `T (fun s t => by`. Rewrite using `[mM, mM, ← affineFreeParam_first_sub_eq_linearPart xj', ← affineFreeParam_first_sub_eq_linearPart xj, ← hT, ← hT, ← map_sub, ← map_smul, hH])`. Use the proof step `(fun t => integrand psi Psi xj' t * a)`. Use the proof step `(fun t u hu => by`. Take `⟨z, hz, e⟩ : ∃ z ∈ H, Loc.xx1 xj' (t + u) = Loc.xx1 xj' t + (qOf P : E) ^ D • z` from `⟨_, (mM u).1 hu, by rw [smul_inv_smul₀ (pow_ne_zero _ q0), ← sub_eq_iff_eq_add', affineFreeParam_first_sub_eq_linearPart, add_sub_cancel_left]⟩`.

Unfold `integrand`. Rewrite using `[e]`. Generalize the expression as in `Loc.xx1 xj' t = y`. Establish `e1 : Psi (y + (qOf P : E) ^ D • z) = Psi y`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hD`.

Rewrite using `[pow_add, pow_one, mul_smul, hi _ _ (hqk d z hz)]`. Rewrite using `[e1]`. Distinguish the cases in `h0 : Psi y = 0`. Simplify using `[h0]`. Establish `a1` using `IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (hch _ hz)`.

Rewrite using `[chArg_add_smul, neg_add, hpsi.1 _ _ (hneg (hch _ (hs _ h0))) (intAt_pow_mul D a1), hpsi.2 _ a1, mul_one])`. Use the proof step `(fun t h => hsupp _ t (left_ne_zero_of_mul h))`. Use the proof step `(fun t h => hsupp xj t (right_ne_zero_of_mul (hpt t ▸ h)))`. Simplify using `only [hpt] at key`. Rewrite `key` using `[← Finset.mul_sum, ← Finset.sum_mul]`.

Unfold `Loc.E1`. Unfold `integrand at key`. Rewrite using `[mul_assoc, ← key]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem unfold_change [CharZero K] (hP : IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P) {psi : E → K} {D : ℕ}
    (hD : 1 ≤ D) (hpsi : CharTo P D psi) (H : AddSubgroup ((Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)))
    (hq : ∀ z ∈ H, (qOf P : E) • z ∈ H) {m : ℕ} (hb : ∀ z ∈ H, IntHom P ((qOf P : E) ^ m • z))
    (hb' : ∀ z, IntHom P z → (qOf P : E) ^ m • z ∈ H) (hch : ∀ z ∈ H, IntAt P ((qOf P : E) ^ D * Loc.chArg z))
    {Psi : Loc.SF E K (n' + c') (n + c)} (hs : ∀ y, Psi y ≠ 0 → y ∈ H) (hi : ∀ y, ∀ z ∈ H, Psi (y + (qOf P : E) • z) = Psi y)
    (σ : ((Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)) →ₗ[E] ((Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)))
    (hH : ∀ z, σ z ∈ H ↔ z ∈ H) {a b : K} (law : ∀ y, Psi (σ y) * a = b * Psi y)
    {xj xj' : (Fin n' → E) →ₗ[E] (Fin n → E)} (T : (Loc.FC n' c' n c → E) ≃ (Loc.FC n' c' n c → E))
    (hT : ∀ t, σ (Loc.xx1 xj t) = Loc.xx1 xj' (T t)) {d : E}
    (hd : ∀ t, Loc.chArg (σ (Loc.xx1 xj t)) = Loc.chArg (Loc.xx1 xj t) + d) {A B : ℕ} (hA : m ≤ A) (hB : m + D ≤ B) (wt : K) :
    Loc.E1 psi (LocE.valsQ E (qOf P) A B) wt Psi xj' * a =
      (psi d)⁻¹ * b * Loc.E1 psi (LocE.valsQ E (qOf P) A B) wt Psi xj := by
  have q0 := qOf_ne_zero P
  have hqk : ∀ k : ℕ, ∀ z ∈ H, (qOf P : E) ^ k • z ∈ H := fun k z hz => by
    induction k with
    | zero => simpa using hz
    | succ k ih => rw [pow_succ', mul_smul]; exact hq _ ih
  have hneg : ∀ {u : E}, IntAt P ((qOf P : E) ^ D * u) → IntAt P ((qOf P : E) ^ D * -u) := fun h => by
    simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg h
  have hpt : ∀ t, integrand psi Psi xj' (T t) * a = (psi d)⁻¹ * b * integrand psi Psi xj t := by
    intro t
    unfold integrand
    rw [← hT, mul_right_comm, law]
    by_cases h0 : Psi (Loc.xx1 xj t) = 0
    · simp [h0]
    have a1 := hch _ (hs _ h0)
    have a2 := hch _ ((hH _).2 (hs _ h0))
    rw [hd] at a2 ⊢
    have a3 : IntAt P ((qOf P : E) ^ D * d) := by
      convert a2.add (hneg a1) using 1
      ring
    have a4 := hpsi.1 _ _ a3 (hneg a3)
    rw [add_neg_cancel, hpsi.2 0 (IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P)] at a4
    rw [neg_add, hpsi.1 _ _ (hneg a1) (hneg a3), ← eq_inv_of_mul_eq_one_right a4.symm]
    ring
  have hsupp : ∀ y t, integrand psi Psi y t ≠ 0 → t ∈ lat P (Loc.FC n' c' n c) ((qOf P : E) ^ A) := fun y t h p => by
    have := (intHom_iff _).1 (hb _ (hs _ (left_ne_zero_of_mul h))) p.1.2 p.1.1
    rw [LinearMap.smul_apply, Pi.smul_apply, Proof.unipotentRadicals_act_affine_unfoldingSpaces.unfoldingAffineLinearMap_apply_freeEntry] at this
    exact intAt_pow_mono hA this
  let M : AddSubgroup (Loc.FC n' c' n c → E) :=
    H.comap (((qOf P : E) ^ D)⁻¹ • Proof.unipotentRadicals_act_affine_unfoldingSpaces.linPart (0 : (Fin n' → E) →ₗ[E] (Fin n → E))).toAddMonoidHom
  have mM : ∀ u, u ∈ M ↔ ((qOf P : E) ^ D)⁻¹ • Proof.unipotentRadicals_act_affine_unfoldingSpaces.linPart (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) u ∈ H :=
    fun u => Iff.rfl
  have key := sum_reps_equiv (M₀ := lat P (Loc.FC n' c' n c) ((qOf P : E) ^ B)⁻¹) (M := M)
    (M₁ := lat P (Loc.FC n' c' n c) ((qOf P : E) ^ A)) (Fintype.piFinset fun _ => LocE.valsQ E (qOf P) A B)
    (fun u hu => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hB
      have h1 : IntHom P (((qOf P : E) ^ (m + D + k))⁻¹ • Proof.unipotentRadicals_act_affine_unfoldingSpaces.linPart (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) u) :=
        (intHom_iff _).2 fun s l => by
          rw [LinearMap.smul_apply, Pi.smul_apply, linPart_single, smul_eq_mul]
          split_ifs
          · exact hu _
          · simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P
      rw [mM]
      convert hqk k _ (hb' _ h1) using 1
      rw [smul_smul, smul_smul]
      congr 1
      field_simp
      ring)
    (fun u hu p => by
      have := (intHom_iff _).1 (hb _ (hqk D _ ((mM u).1 hu))) p.1.2 p.1.1
      rw [smul_inv_smul₀ (pow_ne_zero _ q0), LinearMap.smul_apply, Pi.smul_apply, linPart_single, dif_pos p.2] at this
      exact intAt_pow_mono hA this)
    (fun s hs s' hs' h => funext fun i => (Proof.rationalFractions_represent_primeNormQuotient.valsQ_reps E P hP A B).1 _ (Fintype.mem_piFinset.1 hs i) _
      (Fintype.mem_piFinset.1 hs' i) (h i))
    (fun v hv => by
      choose s hs hs' using fun i => (Proof.rationalFractions_represent_primeNormQuotient.valsQ_reps E P hP A B).2 (v i) (hv i)
      exact ⟨s, Fintype.mem_piFinset.2 hs, hs'⟩)
    T (fun s t => by
      rw [mM, mM, ← affineFreeParam_first_sub_eq_linearPart xj', ← affineFreeParam_first_sub_eq_linearPart xj, ← hT, ← hT, ← map_sub, ← map_smul, hH])
    (fun t => integrand psi Psi xj' t * a)
    (fun t u hu => by
      obtain ⟨z, hz, e⟩ : ∃ z ∈ H, Loc.xx1 xj' (t + u) = Loc.xx1 xj' t + (qOf P : E) ^ D • z :=
        ⟨_, (mM u).1 hu, by rw [smul_inv_smul₀ (pow_ne_zero _ q0), ← sub_eq_iff_eq_add', affineFreeParam_first_sub_eq_linearPart, add_sub_cancel_left]⟩
      unfold integrand
      rw [e]
      generalize Loc.xx1 xj' t = y
      have e1 : Psi (y + (qOf P : E) ^ D • z) = Psi y := by
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hD
        rw [pow_add, pow_one, mul_smul, hi _ _ (hqk d z hz)]
      rw [e1]
      by_cases h0 : Psi y = 0
      · simp [h0]
      have a1 := IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (hch _ hz)
      rw [chArg_add_smul, neg_add, hpsi.1 _ _ (hneg (hch _ (hs _ h0))) (intAt_pow_mul D a1), hpsi.2 _ a1, mul_one])
    (fun t h => hsupp _ t (left_ne_zero_of_mul h))
    (fun t h => hsupp xj t (right_ne_zero_of_mul (hpt t ▸ h)))
  simp only [hpt] at key
  rw [← Finset.mul_sum, ← Finset.sum_mul] at key
  unfold Loc.E1
  unfold integrand at key
  rw [mul_assoc, ← key]
  ring

end Local

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ}

/- English proof (translation)
Distinguish the cases in `hP : P.1 ∈ Pr.vGs`. Take `⟨i, hi⟩ : ∃ i, P.1 ∈ Pr.vG i` from `(Finset.mem_union.mp hP).elim (fun h => ⟨0, h⟩) fun h => ⟨1, h⟩`. Establish `hq : qOf P.1 = Pr.g i` using `hPr.vG_norm i _ hi`. Use `(GlobalTheory.TypePrimeUnif.typePrime_mem_and_notMem_sq hX hPr i P.1 hi).2` as an intermediate fact. Conclude with `⟨hq ▸ hPr.g_prime i, hq ▸ this⟩`.

Conclude with `Proof.NormalFormAtPrime.twistDegOne_of_isSel sel mu hX.rankE hsel P hP`.
-/
theorem degOne_bad (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (P : rowSG Pr sel mu) : IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1 := by
  by_cases hP : P.1 ∈ Pr.vGs
  · obtain ⟨i, hi⟩ : ∃ i, P.1 ∈ Pr.vG i := (Finset.mem_union.mp hP).elim (fun h => ⟨0, h⟩) fun h => ⟨1, h⟩
    have hq : qOf P.1 = Pr.g i := hPr.vG_norm i _ hi
    have := (GlobalTheory.TypePrimeUnif.typePrime_mem_and_notMem_sq hX hPr i P.1 hi).2
    exact ⟨hq ▸ hPr.g_prime i, hq ▸ this⟩
  · exact Proof.NormalFormAtPrime.twistDegOne_of_isSel sel mu hX.rankE hsel P hP

/- English proof (translation)
Establish `hm` using `hL.hm`. Establish `hch` using `chArg_depth hL hi al be P`. Establish `hdeep` using `fun A B hA hB => hL.deep A B hA hB i hi al be P`. Generalize the expression as in `L.h i al P = h' at *`. Generalize the expression as in `L.h (i + 1) be P = h at *`.

Take `⟨m, hb, hb'⟩ : ∃ m : ℕ, (∀ z ∈ movedHom (lamYat (Pr` from `Pr) (R := R) i P.1) (lamYat (Pr := Pr) (R := R) (i + 1) P.1) h' h, IntHom P.1 ((qOf P.1 : X.E) ^ m • z)) ∧ ∀ z, IntHom P.1 z → (qOf P.1 : X.E) ^ m • z ∈ movedHom (lamYat (Pr := Pr) (R := R) i P.1) (lamYat (Pr := Pr) (R := R) (i + 1) P.1) h' h := movedHom_bdd _ _ h' h`. Take `⟨hs, hinv⟩` from `phiAt_mod Ch mu cst.sharp (i := i) (by omega) P.1`. Establish `key` using `unfold_change (K := X.K) (hP1 P) (n' := R.N i) (c' := cOf R i) (n := R.N (i + 1)) (c := cOf R (i + 1)) (hL.cst_ok.D_pos P) ⟨hL.cst_ok.psi_add P, hL.cst_ok.psi_int P⟩ (movedHom (lamYat (Pr := Pr) (R := R) i P.1) (lamYat (Pr := Pr) (R := R) (i + 1) P.1) h' h) (fun z hz v hv => by`. Rewrite using `[LinearMap.smul_apply, map_smul, Nat.cast_smul_eq_nsmul]`. Conclude with `nsmul_mem (hz v hv) _)`.

Use `hb hb' hch (Psi := omPhi Ch sel mu cst i P h' h)`. Use the proof step `(fun y hy => hs _ (right_ne_zero_of_mul hy))`. Use the proof step `(fun y z hz => by`. Unfold `omPhi Loc.om`. Rewrite using `[← hinv (h.symm.toLinearMap ∘ₗ y ∘ₗ h'.toLinearMap) (h.symm.toLinearMap ∘ₗ z ∘ₗ h'.toLinearMap) hz, LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul])`.

Use `σ hH (a := a) (b := b)`. Use the proof step `(fun y => by`. Unfold `omPhi Loc.om`. Rewrite using `[mul_assoc, law]`. Use the proof step `ring)`.

Use `T hT hd`. Use the proof step `(A := cst.A + m) (B := cst.B + (m + cst.D P)) (by omega) (by omega) (((qOf P.1 : X.K) ^ (cst.B + (m + cst.D P)))⁻¹)`. Establish `hd` using `hdeep (cst.A + m) (cst.B + (m + cst.D P)) (by omega) (by omega)`. Unfold `XiAt`. Rewrite using `[← hd, mul_assoc, mul_left_comm (_ * _)]`.

Conclude with `congrArg _ key`.
-/
theorem xiAt_change (hP1 : ∀ P : rowSG Pr sel mu, IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1) (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < m2)
    (al : L.β i) (be : L.β (i + 1)) (P : rowSG Pr sel mu)
    (σ : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1)) →ₗ[X.E] HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1)))
    (hH : ∀ z, σ z ∈ movedHom (lamYat (Pr := Pr) (R := R) i P.1) (lamYat (Pr := Pr) (R := R) (i + 1) P.1) (L.h i al P) (L.h (i + 1) be P) ↔
      z ∈ movedHom (lamYat (Pr := Pr) (R := R) i P.1) (lamYat (Pr := Pr) (R := R) (i + 1) P.1) (L.h i al P) (L.h (i + 1) be P))
    {a b : X.K} (law : ∀ y, PhiAt Ch mu cst.sharp i P.1 ((L.h (i + 1) be P).symm.toLinearMap ∘ₗ σ y ∘ₗ (L.h i al P).toLinearMap) * a =
      b * PhiAt Ch mu cst.sharp i P.1 ((L.h (i + 1) be P).symm.toLinearMap ∘ₗ y ∘ₗ (L.h i al P).toLinearMap))
    {x x' : HomE X.E (R.N i) (R.N (i + 1))}
    (T : (Loc.FC (R.N i) (cOf R i) (R.N (i + 1)) (cOf R (i + 1)) → X.E) ≃ (Loc.FC (R.N i) (cOf R i) (R.N (i + 1)) (cOf R (i + 1)) → X.E))
    (hT : ∀ t, σ (Loc.xx1 x t) = Loc.xx1 x' (T t)) {d : X.E}
    (hd : ∀ t, Loc.chArg (σ (Loc.xx1 x t)) = Loc.chArg (Loc.xx1 x t) + d) :
    XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) x' * a =
      (cst.psi P d)⁻¹ * b * XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) x := by
  have hm := hL.hm
  have hch := chArg_depth hL hi al be P
  have hdeep := fun A B hA hB => hL.deep A B hA hB i hi al be P
  generalize L.h i al P = h' at *
  generalize L.h (i + 1) be P = h at *
  obtain ⟨m, hb, hb'⟩ : ∃ m : ℕ,
      (∀ z ∈ movedHom (lamYat (Pr := Pr) (R := R) i P.1) (lamYat (Pr := Pr) (R := R) (i + 1) P.1) h' h,
        IntHom P.1 ((qOf P.1 : X.E) ^ m • z)) ∧ ∀ z, IntHom P.1 z → (qOf P.1 : X.E) ^ m • z ∈
          movedHom (lamYat (Pr := Pr) (R := R) i P.1) (lamYat (Pr := Pr) (R := R) (i + 1) P.1) h' h :=
    movedHom_bdd _ _ h' h
  obtain ⟨hs, hinv⟩ := phiAt_mod Ch mu cst.sharp (i := i) (by omega) P.1
  have key := unfold_change (K := X.K) (hP1 P) (n' := R.N i) (c' := cOf R i) (n := R.N (i + 1)) (c := cOf R (i + 1))
    (hL.cst_ok.D_pos P) ⟨hL.cst_ok.psi_add P, hL.cst_ok.psi_int P⟩
    (movedHom (lamYat (Pr := Pr) (R := R) i P.1) (lamYat (Pr := Pr) (R := R) (i + 1) P.1) h' h)
    (fun z hz v hv => by
      rw [LinearMap.smul_apply, map_smul, Nat.cast_smul_eq_nsmul]
      exact nsmul_mem (hz v hv) _)
    hb hb' hch (Psi := omPhi Ch sel mu cst i P h' h)
    (fun y hy => hs _ (right_ne_zero_of_mul hy))
    (fun y z hz => by
      unfold omPhi Loc.om
      rw [← hinv (h.symm.toLinearMap ∘ₗ y ∘ₗ h'.toLinearMap) (h.symm.toLinearMap ∘ₗ z ∘ₗ h'.toLinearMap) hz,
        LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul])
    σ hH (a := a) (b := b)
    (fun y => by
      unfold omPhi Loc.om
      rw [mul_assoc, law]
      ring)
    T hT hd
    (A := cst.A + m) (B := cst.B + (m + cst.D P)) (by omega) (by omega) (((qOf P.1 : X.K) ^ (cst.B + (m + cst.D P)))⁻¹)
  have hd := hdeep (cst.A + m) (cst.B + (m + cst.D P)) (by omega) (by omega)
  unfold XiAt
  rw [← hd, mul_assoc, mul_left_comm (_ * _)]
  exact congrArg _ key

/- English proof (translation)
Use `hr.2` as an intermediate fact. Simplify `this` using `[Subgroup.mem_comap]`.
-/
theorem conj_mem {k : Type} [CommRing k] {n c : ℕ} {J : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))}
    {h r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : r ∈ Loc.Cbe J h) : h⁻¹ * r * h ∈ J := by
  have := hr.2
  simpa [Subgroup.mem_comap] using this

/- English proof (translation)
Establish `hm` using `hL.hm`. Establish `hc : 1 ≤ cOf R (i + 1)` using `by unfold cOf; omega`. Establish `hc' : cOf R i = cOf R (i + 1) + 1` using `by unfold cOf; omega`. Establish `hk` using `conj_mem hr`. Establish `hdet : LinearEquiv.det ((L.h (i + 1) be P)⁻¹ * r * L.h (i + 1) be P) = LinearEquiv.det g`.

Rewrite using `[map_mul, map_mul, map_inv, inv_mul_cancel_comm, det_first_parabolic_eq_det_block hr.1.1 hg]`. Establish `hmove : ∀ y : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1)), (L.h (i + 1) be P).symm.toLinearMap ∘ₗ (r.toLinearMap ∘ₗ y) ∘ₗ (L.h i al P).toLinearMap = ((L.h (i + 1) be P)⁻¹ * r * L.h (i + 1) be P).toLinearMap ∘ₗ ((L.h (i + 1) be P).symm.toLinearMap ∘ₗ y ∘ₗ (L.h i al P) …` using `fun y => LinearMap.ext fun v => by`. Express the relevant statement in the definitionally equal form `(L.h (i + 1) be P).symm (r _) = (L.h (i + 1) be P).symm (r ((L.h (i + 1) be P) ((L.h (i + 1) be P).symm _)))`. Rewrite using `[LinearEquiv.apply_symm_apply]`. Both sides reduce to the same expression.

Take `⟨T, hT⟩` from `exists_move hc hc' hr.1 hg x`. Use `xiAt_change hP1 hL hi al be P (LinearMap.llcomp X.E _ _ _ r.toLinearMap) (fun z => forall₂_congr fun v _ => ?_) (fun y => ?_) T hT (characterArgument_first_parabolic_shift hc hc' hr.1.1 x)` and prove the remaining obligations. Use `jat_le _ _ _ hk ((L.h (i + 1) be P).symm (z (L.h i al P v)))` as an intermediate fact. Rewrite using `[← this]`. Conclude with `(LinearMap.congr_fun (hmove z) v) ▸ Iff.rfl`.

Rewrite using `[← hdet, ← DatumLaw.phiAt_target Ch sel mu cst cst.sharp (by omega) P hk, ← hmove]`. Both sides reduce to the same expression.
-/
theorem xiAt_left (hP1 : ∀ P : rowSG Pr sel mu, IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1) (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < m2)
    (al : L.β i) (be : L.β (i + 1)) (P : rowSG Pr sel mu) {r : AutY X R (i + 1)} {g : Sp X.E (R.N (i + 1)) ≃ₗ[X.E] Sp X.E (R.N (i + 1))}
    (hr : r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp (i + 1) P.1) (L.h (i + 1) be P))
    (hg : ∀ x, r (Loc.inX X.E (R.N (i + 1)) (cOf R (i + 1)) x) = Loc.inX X.E (R.N (i + 1)) (cOf R (i + 1)) (g x))
    (x : HomE X.E (R.N i) (R.N (i + 1))) :
    XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) (g.toLinearMap ∘ₗ x) *
        muAt Ch sel mu cst i P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      chiInv Ch sel mu cst (i + 1) P (L.h (i + 1) be P) r * XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) x := by
  have hm := hL.hm
  have hc : 1 ≤ cOf R (i + 1) := by unfold cOf; omega
  have hc' : cOf R i = cOf R (i + 1) + 1 := by unfold cOf; omega
  have hk := conj_mem hr
  have hdet : LinearEquiv.det ((L.h (i + 1) be P)⁻¹ * r * L.h (i + 1) be P) = LinearEquiv.det g := by
    rw [map_mul, map_mul, map_inv, inv_mul_cancel_comm, det_first_parabolic_eq_det_block hr.1.1 hg]
  have hmove : ∀ y : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1)),
      (L.h (i + 1) be P).symm.toLinearMap ∘ₗ (r.toLinearMap ∘ₗ y) ∘ₗ (L.h i al P).toLinearMap =
        ((L.h (i + 1) be P)⁻¹ * r * L.h (i + 1) be P).toLinearMap ∘ₗ
          ((L.h (i + 1) be P).symm.toLinearMap ∘ₗ y ∘ₗ (L.h i al P).toLinearMap) := fun y => LinearMap.ext fun v => by
    change (L.h (i + 1) be P).symm (r _) = (L.h (i + 1) be P).symm (r ((L.h (i + 1) be P) ((L.h (i + 1) be P).symm _)))
    rw [LinearEquiv.apply_symm_apply]
    rfl
  obtain ⟨T, hT⟩ := exists_move hc hc' hr.1 hg x
  refine xiAt_change hP1 hL hi al be P (LinearMap.llcomp X.E _ _ _ r.toLinearMap) (fun z => forall₂_congr fun v _ => ?_)
    (fun y => ?_) T hT (characterArgument_first_parabolic_shift hc hc' hr.1.1 x)
  · have := jat_le _ _ _ hk ((L.h (i + 1) be P).symm (z (L.h i al P v)))
    rw [← this]
    exact (LinearMap.congr_fun (hmove z) v) ▸ Iff.rfl
  · rw [← hdet, ← DatumLaw.phiAt_target Ch sel mu cst cst.sharp (by omega) P hk, ← hmove]
    rfl

/- English proof (translation)
Establish `hm` using `hL.hm`. Establish `hc : 1 ≤ cOf R (i + 1)` using `by unfold cOf; omega`. Establish `hc' : cOf R i = cOf R (i + 1) + 1` using `by unfold cOf; omega`. Establish `hk` using `conj_mem hr`. Establish `hdet : LinearEquiv.det ((L.h i al P)⁻¹ * r * L.h i al P) = LinearEquiv.det g`.

Rewrite using `[map_mul, map_mul, map_inv, inv_mul_cancel_comm, det_first_parabolic_eq_det_block hr.1.1 hg]`. Establish `hmove : ∀ v, L.h i al P (((L.h i al P)⁻¹ * r * L.h i al P) v) = r (L.h i al P v)` using `fun v => LinearEquiv.apply_symm_apply _ _`. Take `⟨T, hT⟩` from `exists_move_right hc hc' hr.1 hg x`. Use `xiAt_change hP1 hL hi al be P (LinearMap.lcomp X.E _ r.toLinearMap) (fun z => ⟨fun hz v hv => ?_, fun hz v hv => ?_⟩) (fun y => ?_) T hT (chArg_right hc hc' hr.1.1 x)` and prove the remaining obligations. Take `⟨w, rfl⟩` from `((L.h i al P)⁻¹ * r * L.h i al P).surjective v`.

Rewrite using `[hmove]`. Conclude with `hz w ((jat_le _ _ _ hk w).1 hv)`. Use `hz _ ((jat_le _ _ _ hk v).2 hv)` as an intermediate fact. Rewrite `this` using `[hmove]`. Then use the resulting hypothesis. Rewrite using `[← hdet, ← DatumLaw.phiAt_source Ch sel mu cst cst.sharp (by omega) P hk]`.

Use `congr 2`. Conclude with `LinearMap.ext fun v => congrArg (fun w => (L.h (i + 1) be P).symm (y w)) (hmove v).symm`.
-/
theorem xiAt_right (hP1 : ∀ P : rowSG Pr sel mu, IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1) (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < m2)
    (al : L.β i) (be : L.β (i + 1)) (P : rowSG Pr sel mu) {r : AutY X R i} {g : Sp X.E (R.N i) ≃ₗ[X.E] Sp X.E (R.N i)}
    (hr : r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp i P.1) (L.h i al P))
    (hg : ∀ x, r (Loc.inX X.E (R.N i) (cOf R i) x) = Loc.inX X.E (R.N i) (cOf R i) (g x))
    (x : HomE X.E (R.N i) (R.N (i + 1))) :
    XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) (x ∘ₗ g.toLinearMap) *
        muAt Ch sel mu cst i P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      chiInv Ch sel mu cst i P (L.h i al P) r * XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) x := by
  have hm := hL.hm
  have hc : 1 ≤ cOf R (i + 1) := by unfold cOf; omega
  have hc' : cOf R i = cOf R (i + 1) + 1 := by unfold cOf; omega
  have hk := conj_mem hr
  have hdet : LinearEquiv.det ((L.h i al P)⁻¹ * r * L.h i al P) = LinearEquiv.det g := by
    rw [map_mul, map_mul, map_inv, inv_mul_cancel_comm, det_first_parabolic_eq_det_block hr.1.1 hg]
  have hmove : ∀ v, L.h i al P (((L.h i al P)⁻¹ * r * L.h i al P) v) = r (L.h i al P v) := fun v =>
    LinearEquiv.apply_symm_apply _ _
  obtain ⟨T, hT⟩ := exists_move_right hc hc' hr.1 hg x
  refine xiAt_change hP1 hL hi al be P (LinearMap.lcomp X.E _ r.toLinearMap) (fun z => ⟨fun hz v hv => ?_, fun hz v hv => ?_⟩)
    (fun y => ?_) T hT (chArg_right hc hc' hr.1.1 x)
  · obtain ⟨w, rfl⟩ := ((L.h i al P)⁻¹ * r * L.h i al P).surjective v
    rw [hmove]
    exact hz w ((jat_le _ _ _ hk w).1 hv)
  · have := hz _ ((jat_le _ _ _ hk v).2 hv)
    rwa [hmove] at this
  · rw [← hdet, ← DatumLaw.phiAt_source Ch sel mu cst cst.sharp (by omega) P hk]
    congr 2
    exact LinearMap.ext fun v => congrArg (fun w => (L.h (i + 1) be P).symm (y w)) (hmove v).symm

end Chain

/- English proof (translation)
Introduce `X Pr R Ch sel S mu cst L G m2 hX hPr _ hsel hL i hi al be P r r' g g' hr hr' hg hg' x`. Establish `hP1` using `fun P : rowSG Pr sel mu => degOne_bad hX.ok hPr hsel P`. Establish `h1` using `xiAt_left hP1 hL hi al be P hr' hg' (inFr g g' x)`. Establish `h2` using `xiAt_right hP1 hL hi al be P hr hg x`. Rewrite `h1` using `[show g'.toLinearMap ∘ₗ inFr g g' x = x ∘ₗ g.toLinearMap from LinearMap.ext fun v => g'.apply_symm_apply _]`.

Rewrite using `[mul_assoc, mul_assoc, ← h1, ← h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem xiAt_two_sided : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.AbelianUnramifiedExtensionConditions → Pr.Ok → Ch.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (i : ℕ), i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)) (P : rowSG Pr sel mu) (r : AutY X R i) (r' : AutY X R (i + 1)) (g : Sp X.E (R.N i) ≃ₗ[X.E] Sp X.E (R.N i)) (g' : Sp X.E (R.N (i + 1)) ≃ₗ[X.E] Sp X.E (R.N (i + 1))), r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp i P.1) (L.h i al P) → r' ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp (i + 1) P.1) (L.h (i + 1) be P) → (∀ x, r (Loc.inX X.E (R.N i) (cOf R i) x) = Loc.inX X.E (R.N i) (cOf R i) (g x)) → (∀ x, r' (Loc.inX X.E (R.N (i + 1)) (cOf R (i + 1)) x) = Loc.inX X.E (R.N (i + 1)) (cOf R (i + 1)) (g' x)) → ∀ x, muAt Ch sel mu cst i P (LinearEquiv.det g : X.Eˣ) * chiInv Ch sel mu cst (i + 1) P (L.h (i + 1) be P) r' * XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) (inFr g g' x) = muAt Ch sel mu cst i P (LinearEquiv.det g' : X.Eˣ) * chiInv Ch sel mu cst i P (L.h i al P) r * XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) x := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr _ hsel hL i hi al be P r r' g g' hr hr' hg hg' x
  have hP1 := fun P : rowSG Pr sel mu => degOne_bad hX.ok hPr hsel P
  have h1 := xiAt_left hP1 hL hi al be P hr' hg' (inFr g g' x)
  have h2 := xiAt_right hP1 hL hi al be P hr hg x
  rw [show g'.toLinearMap ∘ₗ inFr g g' x = x ∘ₗ g.toLinearMap from LinearMap.ext fun v => g'.apply_symm_apply _] at h1
  rw [mul_assoc, mul_assoc, ← h1, ← h2]
  ring

end GlobalTheory.UnfoldTwoSided

end

import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalUnfoldingNonvanishingIffEventuallyNonzero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotMemVGsOfMemQE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevQFiniteIndexAndRoot

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Classical GlobalTheory.QNormal GlobalTheory.UnfoldLaw

noncomputable section

namespace GlobalTheory.SrcDoubleCoset

section Local

open Proof.NormalFormAtPrime Proof.boxSum_ne_zero_invariant_affineChange

variable {E : Type} [Field E] [NumberField E] {K : Type} [Field K] {P : HeightOneSpectrum (𝓞 E)} {n' c' n c : ℕ}

/- English proof (translation)
Establish `q0` using `qOf_ne_zero P`. Establish `hqk : ∀ k : ℕ, ∀ z ∈ H, (qOf P : E) ^ k • z ∈ H` using `fun k z hz => by`. Proceed by induction on `k with`. Consider the case `zero => simpa using hz`. Consider the case `succ k ih => rw [pow_succ', mul_smul]`.

Conclude with `hq _ ih`. Establish `hneg : ∀ {u : E}, IntAt P ((qOf P : E) ^ D * u) → IntAt P ((qOf P : E) ^ D * -u)` using `fun h => by`. Simplify using `using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg h`. Establish `hpt : ∀ t, integrand psi Psi₁ xj' (T t) * a = (psi d)⁻¹ * b * integrand psi Psi₂ xj t`. Introduce `t`.

Unfold `integrand`. Rewrite using `[← hT, mul_right_comm, law]`. Distinguish the cases in `h0 : Psi₂ (Loc.xx1 xj t) = 0`. Simplify using `[h0]`. Establish `a1` using `hch _ (hs₂ _ h0)`.

Establish `a2` using `hch _ ((hH _).2 (hs₂ _ h0))`. Rewrite `a2`, the goal using `[hd]`. Establish `a3 : IntAt P ((qOf P : E) ^ D * d)`. Use `a2.add (hneg a1) using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Establish `a4` using `hpsi.1 _ _ a3 (hneg a3)`. Rewrite `a4` using `[add_neg_cancel, hpsi.2 0 (IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P)]`. Rewrite using `[neg_add, hpsi.1 _ _ (hneg a1) (hneg a3), ← eq_inv_of_mul_eq_one_right a4.symm]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsupp : ∀ Ψ : Loc.SF E K (n' + c') (n + c), (∀ y, Ψ y ≠ 0 → y ∈ H) → ∀ y t, integrand psi Ψ y t ≠ 0 → t ∈ lat P (Loc.FC n' c' n c) ((qOf P : E) ^ A)` using `fun Ψ hs y t h p => by`.

Use `(intHom_iff _).1 (hb _ (hs _ (left_ne_zero_of_mul h))) p.1.2 p.1.1` as an intermediate fact. Rewrite `this` using `[LinearMap.smul_apply, Pi.smul_apply, Proof.unipotentRadicals_act_affine_unfoldingSpaces.unfoldingAffineLinearMap_apply_freeEntry]`. Conclude with `intAt_pow_mono hA this`. Set `M : AddSubgroup (Loc.FC n' c' n c → E)` to `H.comap (((qOf P : E) ^ D)⁻¹ • Proof.unipotentRadicals_act_affine_unfoldingSpaces.linPart (0 : (Fin n' → E) →ₗ[E] (Fin n → E))).toAddMonoidHom`. Establish `mM : ∀ u, u ∈ M ↔ ((qOf P : E) ^ D)⁻¹ • Proof.unipotentRadicals_act_affine_unfoldingSpaces.linPart (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) u ∈ H` using `fun u => Iff.rfl`.

Establish `key` using `sum_reps_equiv (M₀ := lat P (Loc.FC n' c' n c) ((qOf P : E) ^ B)⁻¹) (M := M) (M₁ := lat P (Loc.FC n' c' n c) ((qOf P : E) ^ A)) (Fintype.piFinset fun _ => LocE.valsQ E (qOf P) A B) (fun u hu => by`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hB`. Establish `h1 : IntHom P (((qOf P : E) ^ (m + D + k))⁻¹ • Proof.unipotentRadicals_act_affine_unfoldingSpaces.linPart (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) u)` using `(intHom_iff _).2 fun s l => by`. Rewrite using `[LinearMap.smul_apply, Pi.smul_apply, linPart_single, smul_eq_mul]`. Use `split_ifs`.

Conclude with `hu _`. Simplify using `using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P`. Rewrite using `[mM]`. Use `hqk k _ (hb' _ h1) using 1` and compare the differences between its conclusion and the goal. Rewrite using `[smul_smul, smul_smul]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Use the proof step `ring)`. Use the proof step `(fun u hu p => by`. Use `(intHom_iff _).1 (hb _ (hqk D _ ((mM u).1 hu))) p.1.2 p.1.1` as an intermediate fact.

Rewrite `this` using `[smul_inv_smul₀ (pow_ne_zero _ q0), LinearMap.smul_apply, Pi.smul_apply, linPart_single, dif_pos p.2]`. Conclude with `intAt_pow_mono hA this)`. Use the proof step `(fun s hs s' hs' h => funext fun i => (Proof.rationalFractions_represent_primeNormQuotient.valsQ_reps E P hP A B).1 _ (Fintype.mem_piFinset.1 hs i) _ (Fintype.mem_piFinset.1 hs' i) (h i))`. Use the proof step `(fun v hv => by choose s hs hs' using fun i => (Proof.rationalFractions_represent_primeNormQuotient.valsQ_reps E P hP A B).2 (v i) (hv i)`. Conclude with `⟨s, Fintype.mem_piFinset.2 hs, hs'⟩)`.

Use `T (fun s t => by`. Rewrite using `[mM, mM, ← affineFreeParam_first_sub_eq_linearPart xj', ← affineFreeParam_first_sub_eq_linearPart xj, ← hT, ← hT, ← map_sub, ← map_smul, hH])`. Use the proof step `(fun t => integrand psi Psi₁ xj' t * a)`. Use the proof step `(fun t u hu => by`. Take `⟨z, hz, e⟩ : ∃ z ∈ H, Loc.xx1 xj' (t + u) = Loc.xx1 xj' t + (qOf P : E) ^ D • z` from `⟨_, (mM u).1 hu, by rw [smul_inv_smul₀ (pow_ne_zero _ q0), ← sub_eq_iff_eq_add', affineFreeParam_first_sub_eq_linearPart, add_sub_cancel_left]⟩`.

Unfold `integrand`. Rewrite using `[e]`. Generalize the expression as in `Loc.xx1 xj' t = y`. Establish `e1 : Psi₁ (y + (qOf P : E) ^ D • z) = Psi₁ y`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hD`.

Rewrite using `[pow_add, pow_one, mul_smul, hi _ _ (hqk d z hz)]`. Rewrite using `[e1]`. Distinguish the cases in `h0 : Psi₁ y = 0`. Simplify using `[h0]`. Establish `a1` using `IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (hch _ hz)`.

Rewrite using `[chArg_add_smul, neg_add, hpsi.1 _ _ (hneg (hch _ (hs₁ _ h0))) (intAt_pow_mul D a1), hpsi.2 _ a1, mul_one])`. Use the proof step `(fun t h => hsupp Psi₁ hs₁ _ t (left_ne_zero_of_mul h))`. Use the proof step `(fun t h => hsupp Psi₂ hs₂ xj t (right_ne_zero_of_mul (hpt t ▸ h)))`. Simplify using `only [hpt] at key`. Rewrite `key` using `[← Finset.mul_sum, ← Finset.sum_mul]`.

Unfold `Loc.E1`. Unfold `integrand at key`. Rewrite using `[mul_assoc, ← key]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem unfold_change₂ [CharZero K] (hP : IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P) {psi : E → K} {D : ℕ}
    (hD : 1 ≤ D) (hpsi : CharTo P D psi) (H : AddSubgroup ((Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)))
    (hq : ∀ z ∈ H, (qOf P : E) • z ∈ H) {m : ℕ} (hb : ∀ z ∈ H, IntHom P ((qOf P : E) ^ m • z))
    (hb' : ∀ z, IntHom P z → (qOf P : E) ^ m • z ∈ H) (hch : ∀ z ∈ H, IntAt P ((qOf P : E) ^ D * Loc.chArg z))
    {Psi₁ Psi₂ : Loc.SF E K (n' + c') (n + c)} (hs₁ : ∀ y, Psi₁ y ≠ 0 → y ∈ H) (hs₂ : ∀ y, Psi₂ y ≠ 0 → y ∈ H)
    (hi : ∀ y, ∀ z ∈ H, Psi₁ (y + (qOf P : E) • z) = Psi₁ y)
    (σ : ((Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)) →ₗ[E] ((Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)))
    (hH : ∀ z, σ z ∈ H ↔ z ∈ H) {a b : K} (law : ∀ y, Psi₁ (σ y) * a = b * Psi₂ y)
    {xj xj' : (Fin n' → E) →ₗ[E] (Fin n → E)} (T : (Loc.FC n' c' n c → E) ≃ (Loc.FC n' c' n c → E))
    (hT : ∀ t, σ (Loc.xx1 xj t) = Loc.xx1 xj' (T t)) {d : E}
    (hd : ∀ t, Loc.chArg (σ (Loc.xx1 xj t)) = Loc.chArg (Loc.xx1 xj t) + d) {A B : ℕ} (hA : m ≤ A) (hB : m + D ≤ B) (wt : K) :
    Loc.E1 psi (LocE.valsQ E (qOf P) A B) wt Psi₁ xj' * a =
      (psi d)⁻¹ * b * Loc.E1 psi (LocE.valsQ E (qOf P) A B) wt Psi₂ xj := by
  have q0 := qOf_ne_zero P
  have hqk : ∀ k : ℕ, ∀ z ∈ H, (qOf P : E) ^ k • z ∈ H := fun k z hz => by
    induction k with
    | zero => simpa using hz
    | succ k ih => rw [pow_succ', mul_smul]; exact hq _ ih
  have hneg : ∀ {u : E}, IntAt P ((qOf P : E) ^ D * u) → IntAt P ((qOf P : E) ^ D * -u) := fun h => by
    simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg h
  have hpt : ∀ t, integrand psi Psi₁ xj' (T t) * a = (psi d)⁻¹ * b * integrand psi Psi₂ xj t := by
    intro t
    unfold integrand
    rw [← hT, mul_right_comm, law]
    by_cases h0 : Psi₂ (Loc.xx1 xj t) = 0
    · simp [h0]
    have a1 := hch _ (hs₂ _ h0)
    have a2 := hch _ ((hH _).2 (hs₂ _ h0))
    rw [hd] at a2 ⊢
    have a3 : IntAt P ((qOf P : E) ^ D * d) := by
      convert a2.add (hneg a1) using 1
      ring
    have a4 := hpsi.1 _ _ a3 (hneg a3)
    rw [add_neg_cancel, hpsi.2 0 (IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P)] at a4
    rw [neg_add, hpsi.1 _ _ (hneg a1) (hneg a3), ← eq_inv_of_mul_eq_one_right a4.symm]
    ring
  have hsupp : ∀ Ψ : Loc.SF E K (n' + c') (n + c), (∀ y, Ψ y ≠ 0 → y ∈ H) →
      ∀ y t, integrand psi Ψ y t ≠ 0 → t ∈ lat P (Loc.FC n' c' n c) ((qOf P : E) ^ A) := fun Ψ hs y t h p => by
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
    (fun t => integrand psi Psi₁ xj' t * a)
    (fun t u hu => by
      obtain ⟨z, hz, e⟩ : ∃ z ∈ H, Loc.xx1 xj' (t + u) = Loc.xx1 xj' t + (qOf P : E) ^ D • z :=
        ⟨_, (mM u).1 hu, by rw [smul_inv_smul₀ (pow_ne_zero _ q0), ← sub_eq_iff_eq_add', affineFreeParam_first_sub_eq_linearPart, add_sub_cancel_left]⟩
      unfold integrand
      rw [e]
      generalize Loc.xx1 xj' t = y
      have e1 : Psi₁ (y + (qOf P : E) ^ D • z) = Psi₁ y := by
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hD
        rw [pow_add, pow_one, mul_smul, hi _ _ (hqk d z hz)]
      rw [e1]
      by_cases h0 : Psi₁ y = 0
      · simp [h0]
      have a1 := IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (hch _ hz)
      rw [chArg_add_smul, neg_add, hpsi.1 _ _ (hneg (hch _ (hs₁ _ h0))) (intAt_pow_mul D a1), hpsi.2 _ a1, mul_one])
    (fun t h => hsupp Psi₁ hs₁ _ t (left_ne_zero_of_mul h))
    (fun t h => hsupp Psi₂ hs₂ xj t (right_ne_zero_of_mul (hpt t ▸ h)))
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
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hz v hv`. Establish `h1 : h.symm (z v) ∈ lamYat (Pr` using `Pr) (R := R) (i + 1) P := hz v hv`. Establish `h2` using `(hh (h.symm (z v))).2 h1`. Rewrite `h2` using `[LinearEquiv.apply_symm_apply]`. Then use the resulting hypothesis.

Introduce `hz v hv show h.symm (z v) ∈ _`. Conclude with `(inv_mem hh (z v)).2 (hz v hv)`.
-/
theorem mem_moved {i : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} {h : AutY X R (i + 1)}
    (hh : h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P)) (z : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))) :
    z ∈ movedHom (lamYat (Pr := Pr) (R := R) i P) (lamYat (Pr := Pr) (R := R) (i + 1) P) (1 : AutY X R i) h ↔
      ∀ v ∈ lamYat (Pr := Pr) (R := R) i P, z v ∈ lamYat (Pr := Pr) (R := R) (i + 1) P := by
  constructor
  · intro hz v hv
    have h1 : h.symm (z v) ∈ lamYat (Pr := Pr) (R := R) (i + 1) P := hz v hv
    have h2 := (hh (h.symm (z v))).2 h1
    rwa [LinearEquiv.apply_symm_apply] at h2
  · intro hz v hv
    show h.symm (z v) ∈ _
    exact (inv_mem hh (z v)).2 (hz v hv)

/- English proof (translation)
Establish `hc : cOf R i = cOf R (i + 1) + 1` using `by unfold cOf; omega`. Unfold `Loc.chArg`. Rewrite using `[Finset.mul_sum]`. Use `intAt_sum _ _ fun s hs => ?_` and prove the remaining obligations. Establish `hs` using `Finset.mem_range.1 hs`.

Establish `l1 : R.N (i + 1) + s < R.N (i + 1) + cOf R (i + 1)` using `by omega`. Establish `l2 : R.N i + s + 1 < R.N i + cOf R i` using `by omega`. Unfold `Loc.atN`. Rewrite using `[dif_pos l1, Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.eN_eq_single l2]`. Establish `h1` using `hz`.

Unfold `lamYat at h1`. Simplify using `only [if_pos hP] at h1`. Establish `h2` using `LastSteps.mem_homS_sclLat.1 h1 ⟨_, l1⟩ ⟨_, l2⟩`. Establish `e : LocE.scE (R.N i) (fun i => i + 1) (R.N i + s + 1) - LocE.scE (R.N (i + 1)) (fun i => i + 1) (R.N (i + 1) + s) = 1`. Unfold `LocE.scE`.

Rewrite using `[if_neg (by omega), if_neg (by omega)]`. Simplify using `only`. Use linear arithmetic over natural numbers and integers. Rewrite `h2` using `[e, zpow_one, mul_comm]`. Conclude with `h2`.
-/
theorem intAt_chArg_G {i : ℕ} (hi : i + 2 ≤ R.m) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    (z : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1)))
    (hz : ∀ v ∈ lamYat (Pr := Pr) (R := R) i P, z v ∈ lamYat (Pr := Pr) (R := R) (i + 1) P) :
    IntAt P ((qOf P : X.E) * Loc.chArg z) := by
  have hc : cOf R i = cOf R (i + 1) + 1 := by unfold cOf; omega
  unfold Loc.chArg
  rw [Finset.mul_sum]
  refine intAt_sum _ _ fun s hs => ?_
  have hs := Finset.mem_range.1 hs
  have l1 : R.N (i + 1) + s < R.N (i + 1) + cOf R (i + 1) := by omega
  have l2 : R.N i + s + 1 < R.N i + cOf R i := by omega
  unfold Loc.atN
  rw [dif_pos l1, Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.eN_eq_single l2]
  have h1 := hz
  unfold lamYat at h1
  simp only [if_pos hP] at h1
  have h2 := LastSteps.mem_homS_sclLat.1 h1 ⟨_, l1⟩ ⟨_, l2⟩
  have e : LocE.scE (R.N i) (fun i => i + 1) (R.N i + s + 1) - LocE.scE (R.N (i + 1)) (fun i => i + 1) (R.N (i + 1) + s) = 1 := by
    unfold LocE.scE
    rw [if_neg (by omega), if_neg (by omega)]
    dsimp only
    omega
  rw [e, zpow_one, mul_comm] at h2
  exact h2

end Chain

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ}

/- English proof (translation)
Establish `hm` using `hL.hm`. Establish `hc : 1 ≤ cOf R (i + 1)` using `by unfold cOf; omega`. Establish `hc' : cOf R i = cOf R (i + 1) + 1` using `by unfold cOf; omega`. Establish `hok` using `hL.cst_ok`. Establish `hP1` using `UnfoldTwoSided.degOne_bad hX hPr hsel P`.

Establish `hD1` using `hL.depthG P hP`. Establish `hκs : κ ∈ stabL X.E _ (lamYat (Pr` using `Pr) (R := R) i P.1) := jat_le _ _ _ hκ`. Establish `hrs : r ∈ stabL X.E _ (lamYat (Pr` using `Pr) (R := R) i P.1) := by`. Establish `e' : r = a₂ * κ⁻¹ * a₁⁻¹` using `by rw [e]; group`. Rewrite using `[e']`.

Conclude with `mul_mem (mul_mem ha₂ (inv_mem hκs)) (inv_mem ha₁)`. Substitute `e` using the available equality. Establish `hmu : ∀ {j : ℕ} {g : AutY X R j}, g ∈ stabL X.E _ (lamYat (Pr` using `Pr) (R := R) j P.1) → muAt Ch sel mu cst i P ((LinearEquiv.det g : X.Eˣ) : X.E) ≠ 0 := by`. Introduce `j g hg`. Establish `hu : IsUnit (redP P.1 ((LinearEquiv.det g : X.Eˣ) : X.E))`.

Unfold `lamYat at hg`. Rewrite `hg` using `[if_pos hP]`. Conclude with `LastSteps.isUnit_det_of_stab hg`. Unfold `muAt`. Rewrite using `[LastSteps.locChar_unit _ _ hu]`.

Unfold `LocE.unitV`. Rewrite using `[dif_pos hu]`. Conclude with `Units.ne_zero _`. Establish `hsq : cst.sq P ≠ 0`. Introduce `e0`.

Use `hok.sq_sq P` as an intermediate fact. Rewrite `this` using `[e0, zero_pow two_ne_zero]`. Conclude with `hP1.1.ne_zero (by exact_mod_cast this.symm)`. Establish `hS₁ : omScal Ch sel mu cst i P a₁ h ≠ 0`. Unfold `omScal`.

Conclude with `mul_ne_zero (mul_ne_zero (mul_ne_zero (hmu ha₁) (inv_ne_zero (hmu hh))) (zpow_ne_zero _ hsq)) (zpow_ne_zero _ hsq)`. Establish `hb0 : omScal Ch sel mu cst i P a₁ h * muAt Ch sel mu cst i P ((LinearEquiv.det κ : X.Eˣ) : X.E) ≠ 0` using `mul_ne_zero hS₁ (hmu hκs)`. Establish `hpd : cst.psi P (Loc.n1Arg r) ≠ 0`. Establish `hint : IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * Loc.n1Arg r)`. Rewrite using `[hD1, pow_one]`.

Establish `hr'` using `hrs`. Unfold `lamYat at hr'`. Rewrite `hr'` using `[if_pos hP]`. Conclude with `Mem.LevFin.intAt_n1Arg_G (Proof.NormalFormAtPrime.qOf_ne_zero _) r hr'`. Conclude with `left_ne_zero_of_mul ((Mem.Col2.IdxEx.psi_mul_neg (Mem.Col2.IdxEx.charTo hok P) hint).trans_ne one_ne_zero)`.

Take `⟨m, hb, hb'⟩ : ∃ m : ℕ, (∀ z ∈ movedHom (lamYat (Pr` from `Pr) (R := R) i P.1) (lamYat (Pr := Pr) (R := R) (i + 1) P.1) (1 : AutY X R i) h, IntHom P.1 ((qOf P.1 : X.E) ^ m • z)) ∧ ∀ z, IntHom P.1 z → (qOf P.1 : X.E) ^ m • z ∈ movedHom (lamYat (Pr := Pr) (R := R) i P.1) (lamYat (Pr := Pr) (R := R) (i + 1) P.1) (1 : AutY X R i) h := movedH …`. Take `⟨hs, hinv⟩` from `phiAt_mod Ch mu cst.sharp (i := i) (by omega) P.1`. Establish `supp : ∀ {a : AutY X R i}, a ∈ stabL X.E _ (lamYat (Pr` using `Pr) (R := R) i P.1) → ∀ y, omPhi Ch sel mu cst i P a h y ≠ 0 → y ∈ movedHom (lamYat (Pr := Pr) (R := R) i P.1) (lamYat (Pr := Pr) (R := R) (i + 1) P.1) (1 : AutY X R i) h := by`. Introduce `a ha y hy`. Rewrite using `[mem_moved hh]`.

Introduce `v hv`. Rewrite `hy` using `[omPhi_eq]`. Establish `h1` using `hs _ (right_ne_zero_of_mul hy) (a⁻¹ v) ((inv_mem ha v).2 hv)`. Express the relevant statement in the definitionally equal form `h.symm (y (a (a⁻¹ v))) ∈ _ at h1`. Rewrite `h1` using `[show a (a⁻¹ v) = v from LinearEquiv.apply_symm_apply a v]`.

Establish `h2` using `(hh _).2 h1`. Rewrite `h2` using `[LinearEquiv.apply_symm_apply]`. Then use the resulting hypothesis. Use `⟨max H.choose m, max H.choose_spec.choose (m + cst.D P), fun A B hA hB => ?_⟩` and prove the remaining obligations. Take `⟨xj, hx⟩` from `Function.ne_iff.1 (H.choose_spec.choose_spec A B (le_of_max_le_left hA) (le_of_max_le_left hB))`. Take `⟨g, hg⟩` from `exists_res hr`.

Take `⟨T, hT⟩` from `UnfoldTwoSided.exists_move_right hc hc' hr hg xj`. Establish `key` using `unfold_change₂ (K := X.K) hP1 (n' := R.N i) (c' := cOf R i) (n := R.N (i + 1)) (c := cOf R (i + 1)) (hok.D_pos P) (Mem.Col2.IdxEx.charTo hok P) (movedHom (lamYat (Pr := Pr) (R := R) i P.1) (lamYat (Pr := Pr) (R := R) (i + 1) P.1) (1 : AutY X R i) h) (fun z hz => by`. Rewrite `hz`, the goal using `[mem_moved hh]`. Introduce `v hv`. Rewrite using `[LinearMap.smul_apply, Nat.cast_smul_eq_nsmul]`.

Conclude with `nsmul_mem (hz v hv) _)`. Use `hb hb'`. Use the proof step `(fun z hz => by`. Rewrite using `[hD1, pow_one]`. Conclude with `intAt_chArg_G (by omega) hP z ((mem_moved hh z).1 hz))`.

Use the proof step `(Psi₁ := omPhi Ch sel mu cst i P a₁ h) (Psi₂ := omPhi Ch sel mu cst i P (r * a₁ * κ) h)`. Use the proof step `(supp ha₁) (supp ha₂)`. Use the proof step `(fun y z hz => by`. Rewrite using `[omPhi_eq, omPhi_eq, ← hinv (h.symm.toLinearMap ∘ₗ y ∘ₗ a₁.toLinearMap) (h.symm.toLinearMap ∘ₗ z ∘ₗ a₁.toLinearMap) (fun v hv => (inv_mem hh _).2 ((mem_moved hh z).1 hz (a₁ v) ((ha₁ v).2 hv))), LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul])`. Use the proof step `(LinearMap.lcomp X.E _ r.toLinearMap)`.

Use the proof step `(fun z => by`. Rewrite using `[mem_moved hh, mem_moved hh]`. Prove the components needed by the constructor for the conclusion. Introduce `hz v hv`. Use `hz (r⁻¹ v) ((inv_mem hrs v).2 hv)` as an intermediate fact.

Express the relevant statement in the definitionally equal form `z (r (r⁻¹ v)) ∈ _ at this`. Rewrite `this` using `[show r (r⁻¹ v) = v from LinearEquiv.apply_symm_apply r v]`. Then use the resulting hypothesis. Introduce `hz v hv`. Conclude with `hz (r v) ((hrs v).2 hv))`. Use the proof step `(a := omScal Ch sel mu cst i P (r * a₁ * κ) h * lamRow Ch mu cst.sharp i P.1 κ.toLinearMap)`.

Use the proof step `(b := omScal Ch sel mu cst i P a₁ h * muAt Ch sel mu cst i P ((LinearEquiv.det κ : X.Eˣ) : X.E))`. Use the proof step `(fun y => by`. Use `DatumLaw.phiAt_source Ch sel mu cst cst.sharp (by omega) P hκ (h.symm.toLinearMap ∘ₗ (LinearMap.lcomp X.E _ r.toLinearMap y) ∘ₗ a₁.toLinearMap)` as an intermediate fact. Establish `e2 : h.symm.toLinearMap ∘ₗ y ∘ₗ (r * a₁ * κ).toLinearMap = (h.symm.toLinearMap ∘ₗ (LinearMap.lcomp X.E _ r.toLinearMap y) ∘ₗ a₁.toLinearMap) ∘ₗ κ.toLinearMap` using `LinearMap.ext fun v => rfl`. Rewrite using `[omPhi_eq, omPhi_eq, e2]`.

Take the linear combination `(-(omScal Ch sel mu cst i P a₁ h * omScal Ch sel mu cst i P (r * a₁ * κ) h)) * this)`. Use `T hT (d := Loc.n1Arg r) (fun t => UnfoldTwoSided.chArg_right hc hc' hr.1 xj t)`. Use the proof step `(A := A) (B := B) (le_of_max_le_right hA) (le_of_max_le_right hB) (((qOf P.1 : X.K) ^ B)⁻¹)`. Use `Function.ne_iff.2 ⟨xj ∘ₗ g.toLinearMap, fun h0 => hx ?_⟩` and prove the remaining obligations. Establish `h0' : Loc.E1 (cst.psi P) (LocE.valsQ X.E (qOf P.1) A B) (((qOf P.1 : X.K) ^ B)⁻¹) (omPhi Ch sel mu cst i P a₁ h) (xj ∘ₗ g.toLinearMap) = 0` using `h0`.

Rewrite `key` using `[h0', zero_mul]`. Use `(mul_eq_zero.1 key.symm).resolve_left (mul_ne_zero (inv_ne_zero hpd) hb0)` as an intermediate fact. Conclude with `this`.
-/
theorem unfoldedDatum_ne_zero_of_doubleCoset_source (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < m2)
    (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) {a₁ a₂ : AutY X R i} {h : AutY X R (i + 1)}
    (ha₁ : a₁ ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1)) (ha₂ : a₂ ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1))
    (hh : h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1)) {r κ : AutY X R i}
    (hr : r ∈ Loc.R1 X.E (R.N i) (cOf R i)) (hκ : κ ∈ Jat (Pr := Pr) cst.sharp i P.1) (e : a₂ = r * a₁ * κ)
    (H : FiniteSumNonzeroLargeDepth Ch sel mu cst i P a₂ h) : FiniteSumNonzeroLargeDepth Ch sel mu cst i P a₁ h := by
  have hm := hL.hm
  have hc : 1 ≤ cOf R (i + 1) := by unfold cOf; omega
  have hc' : cOf R i = cOf R (i + 1) + 1 := by unfold cOf; omega
  have hok := hL.cst_ok
  have hP1 := UnfoldTwoSided.degOne_bad hX hPr hsel P
  have hD1 := hL.depthG P hP
  have hκs : κ ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1) := jat_le _ _ _ hκ
  have hrs : r ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1) := by
    have e' : r = a₂ * κ⁻¹ * a₁⁻¹ := by rw [e]; group
    rw [e']
    exact mul_mem (mul_mem ha₂ (inv_mem hκs)) (inv_mem ha₁)
  subst e

  have hmu : ∀ {j : ℕ} {g : AutY X R j}, g ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P.1) →
      muAt Ch sel mu cst i P ((LinearEquiv.det g : X.Eˣ) : X.E) ≠ 0 := by
    intro j g hg
    have hu : IsUnit (redP P.1 ((LinearEquiv.det g : X.Eˣ) : X.E)) := by
      unfold lamYat at hg
      rw [if_pos hP] at hg
      exact LastSteps.isUnit_det_of_stab hg
    unfold muAt
    rw [LastSteps.locChar_unit _ _ hu]
    unfold LocE.unitV
    rw [dif_pos hu]
    exact Units.ne_zero _
  have hsq : cst.sq P ≠ 0 := by
    intro e0
    have := hok.sq_sq P
    rw [e0, zero_pow two_ne_zero] at this
    exact hP1.1.ne_zero (by exact_mod_cast this.symm)
  have hS₁ : omScal Ch sel mu cst i P a₁ h ≠ 0 := by
    unfold omScal
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hmu ha₁) (inv_ne_zero (hmu hh))) (zpow_ne_zero _ hsq)) (zpow_ne_zero _ hsq)
  have hb0 : omScal Ch sel mu cst i P a₁ h * muAt Ch sel mu cst i P ((LinearEquiv.det κ : X.Eˣ) : X.E) ≠ 0 :=
    mul_ne_zero hS₁ (hmu hκs)
  have hpd : cst.psi P (Loc.n1Arg r) ≠ 0 := by
    have hint : IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * Loc.n1Arg r) := by
      rw [hD1, pow_one]
      have hr' := hrs
      unfold lamYat at hr'
      rw [if_pos hP] at hr'
      exact Mem.LevFin.intAt_n1Arg_G (Proof.NormalFormAtPrime.qOf_ne_zero _) r hr'
    exact left_ne_zero_of_mul ((Mem.Col2.IdxEx.psi_mul_neg (Mem.Col2.IdxEx.charTo hok P) hint).trans_ne one_ne_zero)

  obtain ⟨m, hb, hb'⟩ : ∃ m : ℕ,
      (∀ z ∈ movedHom (lamYat (Pr := Pr) (R := R) i P.1) (lamYat (Pr := Pr) (R := R) (i + 1) P.1) (1 : AutY X R i) h,
        IntHom P.1 ((qOf P.1 : X.E) ^ m • z)) ∧ ∀ z, IntHom P.1 z → (qOf P.1 : X.E) ^ m • z ∈
          movedHom (lamYat (Pr := Pr) (R := R) i P.1) (lamYat (Pr := Pr) (R := R) (i + 1) P.1) (1 : AutY X R i) h :=
    movedHom_bdd _ _ 1 h
  obtain ⟨hs, hinv⟩ := phiAt_mod Ch mu cst.sharp (i := i) (by omega) P.1
  have supp : ∀ {a : AutY X R i}, a ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1) → ∀ y, omPhi Ch sel mu cst i P a h y ≠ 0 →
      y ∈ movedHom (lamYat (Pr := Pr) (R := R) i P.1) (lamYat (Pr := Pr) (R := R) (i + 1) P.1) (1 : AutY X R i) h := by
    intro a ha y hy
    rw [mem_moved hh]
    intro v hv
    rw [omPhi_eq] at hy
    have h1 := hs _ (right_ne_zero_of_mul hy) (a⁻¹ v) ((inv_mem ha v).2 hv)
    change h.symm (y (a (a⁻¹ v))) ∈ _ at h1
    rw [show a (a⁻¹ v) = v from LinearEquiv.apply_symm_apply a v] at h1
    have h2 := (hh _).2 h1
    rwa [LinearEquiv.apply_symm_apply] at h2
  refine ⟨max H.choose m, max H.choose_spec.choose (m + cst.D P), fun A B hA hB => ?_⟩
  obtain ⟨xj, hx⟩ := Function.ne_iff.1 (H.choose_spec.choose_spec A B (le_of_max_le_left hA) (le_of_max_le_left hB))
  obtain ⟨g, hg⟩ := exists_res hr
  obtain ⟨T, hT⟩ := UnfoldTwoSided.exists_move_right hc hc' hr hg xj
  have key := unfold_change₂ (K := X.K) hP1 (n' := R.N i) (c' := cOf R i) (n := R.N (i + 1)) (c := cOf R (i + 1))
    (hok.D_pos P) (Mem.Col2.IdxEx.charTo hok P)
    (movedHom (lamYat (Pr := Pr) (R := R) i P.1) (lamYat (Pr := Pr) (R := R) (i + 1) P.1) (1 : AutY X R i) h)
    (fun z hz => by
      rw [mem_moved hh] at hz ⊢
      intro v hv
      rw [LinearMap.smul_apply, Nat.cast_smul_eq_nsmul]
      exact nsmul_mem (hz v hv) _)
    hb hb'
    (fun z hz => by
      rw [hD1, pow_one]
      exact intAt_chArg_G (by omega) hP z ((mem_moved hh z).1 hz))
    (Psi₁ := omPhi Ch sel mu cst i P a₁ h) (Psi₂ := omPhi Ch sel mu cst i P (r * a₁ * κ) h)
    (supp ha₁) (supp ha₂)
    (fun y z hz => by
      rw [omPhi_eq, omPhi_eq, ← hinv (h.symm.toLinearMap ∘ₗ y ∘ₗ a₁.toLinearMap) (h.symm.toLinearMap ∘ₗ z ∘ₗ a₁.toLinearMap)
        (fun v hv => (inv_mem hh _).2 ((mem_moved hh z).1 hz (a₁ v) ((ha₁ v).2 hv))),
        LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul])
    (LinearMap.lcomp X.E _ r.toLinearMap)
    (fun z => by
      rw [mem_moved hh, mem_moved hh]
      constructor
      · intro hz v hv
        have := hz (r⁻¹ v) ((inv_mem hrs v).2 hv)
        change z (r (r⁻¹ v)) ∈ _ at this
        rwa [show r (r⁻¹ v) = v from LinearEquiv.apply_symm_apply r v] at this
      · intro hz v hv
        exact hz (r v) ((hrs v).2 hv))
    (a := omScal Ch sel mu cst i P (r * a₁ * κ) h * lamRow Ch mu cst.sharp i P.1 κ.toLinearMap)
    (b := omScal Ch sel mu cst i P a₁ h * muAt Ch sel mu cst i P ((LinearEquiv.det κ : X.Eˣ) : X.E))
    (fun y => by
      have := DatumLaw.phiAt_source Ch sel mu cst cst.sharp (by omega) P hκ
        (h.symm.toLinearMap ∘ₗ (LinearMap.lcomp X.E _ r.toLinearMap y) ∘ₗ a₁.toLinearMap)
      have e2 : h.symm.toLinearMap ∘ₗ y ∘ₗ (r * a₁ * κ).toLinearMap =
          (h.symm.toLinearMap ∘ₗ (LinearMap.lcomp X.E _ r.toLinearMap y) ∘ₗ a₁.toLinearMap) ∘ₗ κ.toLinearMap :=
        LinearMap.ext fun v => rfl
      rw [omPhi_eq, omPhi_eq, e2]
      linear_combination (-(omScal Ch sel mu cst i P a₁ h * omScal Ch sel mu cst i P (r * a₁ * κ) h)) * this)
    T hT (d := Loc.n1Arg r) (fun t => UnfoldTwoSided.chArg_right hc hc' hr.1 xj t)
    (A := A) (B := B) (le_of_max_le_right hA) (le_of_max_le_right hB) (((qOf P.1 : X.K) ^ B)⁻¹)
  refine Function.ne_iff.2 ⟨xj ∘ₗ g.toLinearMap, fun h0 => hx ?_⟩
  have h0' : Loc.E1 (cst.psi P) (LocE.valsQ X.E (qOf P.1) A B) (((qOf P.1 : X.K) ^ B)⁻¹) (omPhi Ch sel mu cst i P a₁ h)
      (xj ∘ₗ g.toLinearMap) = 0 := h0
  rw [h0', zero_mul] at key
  have := (mul_eq_zero.1 key.symm).resolve_left (mul_ne_zero (inv_ne_zero hpd) hb0)
  exact this

end Main

/- English proof (translation)
Introduce `X Pr R Ch sel S mu cst L G m2 hX hPr _ hsel _ hL i hi P hP hal h hal_st h_st hdc`. Take `⟨r, hr, κ, hκ, e⟩` from `hdc`. Prove the components needed by the constructor for the conclusion. Conclude with `unfoldedDatum_ne_zero_of_doubleCoset_source hX hPr hsel hL hi P hP (one_mem _) hal_st h_st hr hκ e`. Conclude with `unfoldedDatum_ne_zero_of_doubleCoset_source hX hPr hsel hL hi P hP hal_st (one_mem _) h_st (inv_mem hr) (inv_mem hκ) (by rw [e]; group)`.
-/
theorem unfoldedDatum_ne_zero_iff_doubleCoset' : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → Ch.Ok → IsSel X sel → cst.sharp = true → L.Ok Ch sel mu cst G m2 → ∀ i, i < m2 → ∀ (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → ∀ (hal : AutY X R i) (h : AutY X R (i + 1)), hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1) → h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1) → SameDC (Pr := Pr) cst.sharp i P.1 1 hal → (FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h ↔ FiniteSumNonzeroLargeDepth Ch sel mu cst i P 1 h) := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr _ hsel _ hL i hi P hP hal h hal_st h_st hdc
  obtain ⟨r, hr, κ, hκ, e⟩ := hdc
  constructor
  · exact unfoldedDatum_ne_zero_of_doubleCoset_source hX hPr hsel hL hi P hP (one_mem _) hal_st h_st hr hκ e
  · exact unfoldedDatum_ne_zero_of_doubleCoset_source hX hPr hsel hL hi P hP hal_st (one_mem _) h_st (inv_mem hr) (inv_mem hκ) (by rw [e]; group)

end GlobalTheory.SrcDoubleCoset

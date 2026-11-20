import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IndicatorFunctionIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairOperatorStatement

open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity GlobalTheory.PairOp

noncomputable section
namespace GlobalTheory.KernelComm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type}

section Indicator
variable [Fintype n'] (q : Unif k) {P₁ : Pair k n'} {e₁ : n' → k} (he : P₁.HasVal e₁ 1) (Q : Pair k n)
  (x : Matrix n n' k)
include he

open Classical in

/- English proof (translation)
Establish `hm : ∀ Q₁ : Pair k n, Maps P₁ Q₁ x ↔ (∀ y ∈ P₁.ker, x *ᵥ y ∈ Q₁.ker) ∧ Q₁.HasVal (x *ᵥ e₁) 1` using `fun Q₁ => by`. Rewrite using `[maps_iff_glue he Q₁.hasVal_vec, Pair.hasVal_one_iff Q₁.hasVal_vec]`. Rewrite using `[midInd, mulVec_smul]`. Use `split_ifs with h`. Establish `hg : IsGlue Q.lat (x *ᵥ e₁)` using `(isGlue_iff q).2 ⟨Q.isLat, fun h0 => one_ne_zero (h.2.unique (Pair.mem_ker.1 (Pair.smul_mem_ker q.mem_max h0))), h.2.mem⟩`.

Rewrite using `[Finset.sum_eq_single_of_mem (glue hg)]`. Conclude with `if_pos ((hm _).2 ⟨by rw [glue_ker]; exact h.1, glue_hasVal hg⟩)`. Conclude with `Finset.mem_filter.2 ⟨mem_withKer.2 (glue_ker hg), (cross_hasVal q (glue_ker hg).symm (glue_hasVal hg)).unique h.2⟩`. Conclude with `fun Q₁ h1 h2 => if_neg fun h3 => h2 ((eq_glue_iff hg).2 ⟨mem_withKer.1 (Finset.mem_filter.1 h1).1, ((hm _).1 h3).2⟩)`. Use `Finset.sum_eq_zero fun Q₁ h1 => if_neg fun h3 => h ?_` and prove the remaining obligations.

Take `⟨h1, h2⟩` from `Finset.mem_filter.1 h1`. Rewrite `h1` using `[mem_withKer]`. Conclude with `⟨h1 ▸ ((hm _).1 h3).1, h2 ▸ cross_hasVal q h1.symm ((hm _).1 h3).2⟩`.
-/
theorem sum_target :
    ∑ Q₁ ∈ withKer Q.lat with cross q Q₁ Q = 1, phiOne P₁ Q₁ x = midInd q P₁.ker e₁ Q x := by
  have hm : ∀ Q₁ : Pair k n, Maps P₁ Q₁ x ↔ (∀ y ∈ P₁.ker, x *ᵥ y ∈ Q₁.ker) ∧ Q₁.HasVal (x *ᵥ e₁) 1 := fun Q₁ => by
    rw [maps_iff_glue he Q₁.hasVal_vec, Pair.hasVal_one_iff Q₁.hasVal_vec]
  rw [midInd, mulVec_smul]
  split_ifs with h
  · have hg : IsGlue Q.lat (x *ᵥ e₁) := (isGlue_iff q).2 ⟨Q.isLat, fun h0 =>
      one_ne_zero (h.2.unique (Pair.mem_ker.1 (Pair.smul_mem_ker q.mem_max h0))), h.2.mem⟩
    rw [Finset.sum_eq_single_of_mem (glue hg)]
    · exact if_pos ((hm _).2 ⟨by rw [glue_ker]; exact h.1, glue_hasVal hg⟩)
    · exact Finset.mem_filter.2 ⟨mem_withKer.2 (glue_ker hg),
        (cross_hasVal q (glue_ker hg).symm (glue_hasVal hg)).unique h.2⟩
    · exact fun Q₁ h1 h2 => if_neg fun h3 =>
        h2 ((eq_glue_iff hg).2 ⟨mem_withKer.1 (Finset.mem_filter.1 h1).1, ((hm _).1 h3).2⟩)
  · refine Finset.sum_eq_zero fun Q₁ h1 => if_neg fun h3 => h ?_
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 h1
    rw [mem_withKer] at h1
    exact ⟨h1 ▸ ((hm _).1 h3).1, h2 ▸ cross_hasVal q h1.symm ((hm _).1 h3).2⟩

open Classical in

/- English proof (translation)
Rewrite using `[midInd]`. Establish `hq : q.1 • e₁ ∈ P₁.ker` using `Pair.smul_mem_ker q.mem_max he.mem`. Use `split_ifs with h`. Set `f : P₁.ker →ₗ[𝒪[k]] 𝓀[k]` to `Q.fn ∘ₗ ((Matrix.mulVecLin x).restrictScalars 𝒪[k]).restrict h.1`. Establish `hf : ∀ y : P₁.ker, Q.HasVal (x *ᵥ y) (f y)` using `fun y => ⟨h.1 y y.2, rfl⟩`.

Establish `h1 : f ⟨_, hq⟩ = 1` using `(hf ⟨_, hq⟩).unique h.2`. Set `R : Pair k n'` to `⟨P₁.ker, P₁.ker_isLat, f, fun h0 => by simp [h0] at h1⟩`. Establish `hR : Maps R Q x` using `⟨h.1, fun _ => rfl⟩`. Rewrite using `[Finset.sum_eq_single_of_mem R]`. Conclude with `(if_pos hR).symm`.

Conclude with `Finset.mem_filter.2 ⟨mem_withLat.2 rfl, (cross_hasVal q (P := R) rfl he).unique ⟨hq, h1⟩⟩`. Use `fun P hP h2 => if_neg fun h3 => h2 (Pair.ext fun y a => ?_)` and prove the remaining obligations. Establish `hl : P.lat = R.lat` using `mem_withLat.1 (Finset.mem_filter.1 hP).1`. Rewrite `hR`, `h3` using `[maps_iff_hasVal]`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Establish `h4` using `R.hasVal_fn ⟨y, hl ▸ hy.mem⟩`. Conclude with `(hR _ _ h4).unique (h3 _ _ hy) ▸ h4`. Introduce `hy`. Establish `h4` using `P.hasVal_fn ⟨y, hl ▸ hy.mem⟩`.

Conclude with `(h3 _ _ h4).unique (hR _ _ hy) ▸ h4`. Use `(Finset.sum_eq_zero fun P h1 => if_neg fun h3 => h ?_).symm` and prove the remaining obligations. Take `⟨h1, h2⟩` from `Finset.mem_filter.1 h1`. Rewrite `h1` using `[mem_withLat]`. Conclude with `⟨h1 ▸ h3.1, maps_iff_hasVal.1 h3 _ _ (h2 ▸ cross_hasVal q h1 he)⟩`.
-/
theorem sum_source :
    midInd q P₁.ker e₁ Q x = ∑ P ∈ withLat P₁.ker with cross q P₁ P = 1, phiOne P Q x := by
  rw [midInd]
  have hq : q.1 • e₁ ∈ P₁.ker := Pair.smul_mem_ker q.mem_max he.mem
  split_ifs with h
  · let f : P₁.ker →ₗ[𝒪[k]] 𝓀[k] := Q.fn ∘ₗ ((Matrix.mulVecLin x).restrictScalars 𝒪[k]).restrict h.1
    have hf : ∀ y : P₁.ker, Q.HasVal (x *ᵥ y) (f y) := fun y => ⟨h.1 y y.2, rfl⟩
    have h1 : f ⟨_, hq⟩ = 1 := (hf ⟨_, hq⟩).unique h.2
    let R : Pair k n' := ⟨P₁.ker, P₁.ker_isLat, f, fun h0 => by simp [h0] at h1⟩
    have hR : Maps R Q x := ⟨h.1, fun _ => rfl⟩
    rw [Finset.sum_eq_single_of_mem R]
    · exact (if_pos hR).symm
    · exact Finset.mem_filter.2 ⟨mem_withLat.2 rfl, (cross_hasVal q (P := R) rfl he).unique ⟨hq, h1⟩⟩
    · refine fun P hP h2 => if_neg fun h3 => h2 (Pair.ext fun y a => ?_)
      have hl : P.lat = R.lat := mem_withLat.1 (Finset.mem_filter.1 hP).1
      rw [maps_iff_hasVal] at hR h3
      constructor
      · intro hy
        have h4 := R.hasVal_fn ⟨y, hl ▸ hy.mem⟩
        exact (hR _ _ h4).unique (h3 _ _ hy) ▸ h4
      · intro hy
        have h4 := P.hasVal_fn ⟨y, hl ▸ hy.mem⟩
        exact (h3 _ _ h4).unique (hR _ _ hy) ▸ h4
  · refine (Finset.sum_eq_zero fun P h1 => if_neg fun h3 => h ?_).symm
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 h1
    rw [mem_withLat] at h1
    exact ⟨h1 ▸ h3.1, maps_iff_hasVal.1 h3 _ _ (h2 ▸ cross_hasVal q h1 he)⟩

end Indicator

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ q _ _ he Q x` and use `⟨sum_target q he Q x, sum_source q he Q x⟩`.
-/
theorem indicatorIdentity : IndicatorIdentity := fun _ _ _ _ _ _ _ _ _ q _ _ he Q x =>
  ⟨sum_target q he Q x, sum_source q he Q x⟩

/- English proof (translation)
Use `letI := Fintype.ofFinite (Red L)`. Use `letI := Fintype.ofFinite (Module.Dual 𝓀[k] (Red L))`. Establish `hc : Fintype.card (Red L) = Fintype.card (Module.Dual 𝓀[k] (Red L))`. Rewrite using `[← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := 𝓀[k]), Module.natCard_eq_pow_finrank (K := 𝓀[k]) (V := Module.Dual 𝓀[k] (Red L)), Subspace.dual_finrank_eq]`. Rewrite using `[Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, sum_withKer L q, sum_withLat L]`.

Simplify using `[hc]`.
-/
theorem card_withKer (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] :
    (withKer L).card = (withLat L).card := by
  classical
  letI := Fintype.ofFinite (Red L)
  letI := Fintype.ofFinite (Module.Dual 𝓀[k] (Red L))
  have hc : Fintype.card (Red L) = Fintype.card (Module.Dual 𝓀[k] (Red L)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := 𝓀[k]),
      Module.natCard_eq_pow_finrank (K := 𝓀[k]) (V := Module.Dual 𝓀[k] (Red L)), Subspace.dual_finrank_eq]
  rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, sum_withKer L q, sum_withLat L]
  simp [hc]

variable [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨i⟩ : Nonempty n := by`. Assume the negation of the conclusion as `h`. Use `haveI := not_nonempty_iff.1 h`. Conclude with `P.fn_ne (LinearMap.ext fun y => by rw [Subsingleton.elim y 0]; simp)`. Take `⟨a, rfl⟩` from `MulAction.exists_smul_eq (GL n k) (stdPair k i) P`.

Establish `hdet : (Matrix.diagonal (Function.update (1 : n → k) i (q.1 : k))).det = (q.1 : k)`. Simplify using `[Matrix.det_diagonal, Finset.prod_update_of_mem]`. Set `d : GL n k` to `Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdet ▸ q.ne_zero)`. Establish `hd : ∀ (y : n → k) j, (d • y) j = Function.update (1 : n → k) i (q.1 : k) j * y j` using `fun y j => Matrix.mulVec_diagonal _ _ _`. Establish `h1 : d⁻¹ • (stdPair k i).ker = (stdPair k i).lat`.

Use extensionality with `y`. Rewrite using `[mem_smul_iff, inv_inv, Pair.mem_ker, stdPair_hasVal]`. Express the relevant statement in the definitionally equal form `_ ↔ y ∈ stdLat k n`. Rewrite using `[mem_stdLat]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h, h0⟩ j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Take `⟨s, hs⟩` from `q.mem_max_iff.1 ((residue_eq_zero_iff _).1 h0)`. Establish `h2 : (q.1 : k) * y j = q.1 * s` using `by simpa [hd] using congrArg Subtype.val hs`.

Rewrite using `[mul_left_cancel₀ q.ne_zero h2]`. Conclude with `s.2`. Simplify `h j` using `[hd, hj]`. Introduce `h`. Use `⟨fun j => ?_, (residue_eq_zero_iff _).2 (q.mem_max_iff.2 ⟨⟨y i, h i⟩, Subtype.ext (by simp [hd])⟩)⟩` and prove the remaining obligations.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify `mul_mem q.1.2 (h j)` using `[hd]`. Simplify `h j` using `[hd, hj]`. Use `⟨a * d⁻¹ * a⁻¹, by rw [Pair.smul_ker, Pair.smul_lat, mul_smul, mul_smul, inv_smul_smul, h1], ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, map_mul, map_inv, map_inv, mul_inv_cancel_comm, _root_.inv_inj]`. Conclude with `Units.ext hdet`.
-/
theorem exists_det (q : Unif k) (P : Pair k n) :
    ∃ d : GL n k, d • P.ker = P.lat ∧ Matrix.GeneralLinearGroup.det d = q.unit⁻¹ := by
  obtain ⟨i⟩ : Nonempty n := by
    by_contra h
    haveI := not_nonempty_iff.1 h
    exact P.fn_ne (LinearMap.ext fun y => by rw [Subsingleton.elim y 0]; simp)
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq (GL n k) (stdPair k i) P
  have hdet : (Matrix.diagonal (Function.update (1 : n → k) i (q.1 : k))).det = (q.1 : k) := by
    simp [Matrix.det_diagonal, Finset.prod_update_of_mem]
  let d : GL n k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdet ▸ q.ne_zero)
  have hd : ∀ (y : n → k) j, (d • y) j = Function.update (1 : n → k) i (q.1 : k) j * y j := fun y j =>
    Matrix.mulVec_diagonal _ _ _
  have h1 : d⁻¹ • (stdPair k i).ker = (stdPair k i).lat := by
    ext y
    rw [mem_smul_iff, inv_inv, Pair.mem_ker, stdPair_hasVal]
    change _ ↔ y ∈ stdLat k n
    rw [mem_stdLat]
    constructor
    · rintro ⟨h, h0⟩ j
      by_cases hj : j = i
      · subst hj
        obtain ⟨s, hs⟩ := q.mem_max_iff.1 ((residue_eq_zero_iff _).1 h0)
        have h2 : (q.1 : k) * y j = q.1 * s := by simpa [hd] using congrArg Subtype.val hs
        rw [mul_left_cancel₀ q.ne_zero h2]
        exact s.2
      · simpa [hd, hj] using h j
    · intro h
      refine ⟨fun j => ?_, (residue_eq_zero_iff _).2 (q.mem_max_iff.2 ⟨⟨y i, h i⟩, Subtype.ext (by simp [hd])⟩)⟩
      by_cases hj : j = i
      · subst hj
        simpa [hd] using mul_mem q.1.2 (h j)
      · simpa [hd, hj] using h j
  refine ⟨a * d⁻¹ * a⁻¹, by rw [Pair.smul_ker, Pair.smul_lat, mul_smul, mul_smul, inv_smul_smul, h1], ?_⟩
  rw [map_mul, map_mul, map_inv, map_inv, mul_inv_cancel_comm, _root_.inv_inj]
  exact Units.ext hdet

/- English proof (translation)
Take `⟨d, hd, hdet⟩` from `exists_det q P`. Use `valuation_det_of_fix P.ker (h := d⁻¹ * g) (by rw [mul_smul, hg, ← hd, inv_smul_smul])` as an intermediate fact. Rewrite `this` using `[map_mul, map_inv, hdet, inv_inv, mul_comm]`. Then use the resulting hypothesis.
-/
theorem valuation_det (q : Unif k) (P : Pair k n) {g : GL n k} (hg : g • P.ker = P.lat) :
    valuation k ((Matrix.GeneralLinearGroup.det g * q.unit : kˣ) : k) = 1 := by
  obtain ⟨d, hd, hdet⟩ := exists_det q P
  have := valuation_det_of_fix P.ker (h := d⁻¹ * g) (by rw [mul_smul, hg, ← hd, inv_smul_smul])
  rwa [map_mul, map_inv, hdet, inv_inv, mul_comm] at this

variable {V' V : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V]
  {μ : kˣ →* ℂˣ} {π' : Representation ℂ (GL n' k) V'} {π : Representation ℂ (GL n k) V}
  {θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V}
  (hμ : IsUnram μ) (hθ : IsEquivTheta μ π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n)

def KK : Form k n' V' →ₗ[ℂ] Form k n V :=
  (EqForm π).subtype ∘ₗ (evalEquiv π Q₀).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict _ (θ.flip (phiOneSB P₀ Q₀) ∘ₗ LinearMap.proj P₀) fun φ => theta_mem hμ hθ P₀ Q₀ (φ P₀)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem K_eq (φ : EqForm π') : (K hμ hθ P₀ Q₀ φ).1 = KK hμ hθ P₀ Q₀ φ.1 := rfl

/- English proof (translation)
The claim follows from `formOf_mem _ _ _`.
-/
theorem KK_mem (φ : Form k n' V') : KK hμ hθ P₀ Q₀ φ ∈ EqForm π := formOf_mem _ _ _

/- English proof (translation)
The claim follows from `formOf_smul π Q₀ _ h`.
-/
theorem KK_smul (φ : Form k n' V') (h : GL n k) :
    KK hμ hθ P₀ Q₀ φ (h • Q₀) = π h (θ (φ P₀) (phiOneSB P₀ Q₀)) := formOf_smul π Q₀ _ h

/- English proof (translation)
Use extensionality with `Q`. Take `⟨g, rfl⟩` from `MulAction.exists_smul_eq (GL n k) Q₀ Q`. Rewrite using `[h g, h' g, e]`.
-/
theorem eq_of_base {φ φ' : Form k n V} (h : φ ∈ EqForm π) (h' : φ' ∈ EqForm π) (e : φ Q₀ = φ' Q₀) : φ = φ' := by
  ext Q
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n k) Q₀ Q
  rw [h g, h' g, e]

/- English proof (translation)
Rewrite using `[KK_smul, hφ g, ← map_smul]`. Use `(hθ g h _ _ _ ?_).symm` and prove the remaining obligations. Use extensionality with `x`. Establish `m : ∀ z : kˣ, valuation k ((z * u : kˣ) : k) = 1 → μ z = (μ u)⁻¹ ∧ nabs k z = (nabs k u)⁻¹` using `fun z hz => ⟨eq_inv_of_mul_eq_one_left (by rw [← map_mul, hμ _ hz]), eq_inv_of_mul_eq_one_left (by rw [← nabs_mul, (nabs_eq_one_iff _).2 hz])⟩`. Establish `hp : 0 < (nabs k u)⁻¹` using `inv_pos.2 (nabs_pos k u)`.

Simplify using `only [om, (m _ hg).1, (m _ hg).2, (m _ hh).1, (m _ hh).2, phiOneSB, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, phiOne_smul, Units.mul_inv, one_mul]`. Rewrite using `[← Complex.ofReal_mul, ← Real.rpow_add hp]`. Use `congr 3`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem KK_move {φ : Form k n' V'} (hφ : φ ∈ EqForm π') (u : kˣ) (g : GL n' k) (h : GL n k)
    (hg : valuation k ((Matrix.GeneralLinearGroup.det g * u : kˣ) : k) = 1)
    (hh : valuation k ((Matrix.GeneralLinearGroup.det h * u : kˣ) : k) = 1) :
    KK hμ hθ P₀ Q₀ φ (h • Q₀) =
      (((nabs k u)⁻¹ ^ (((Fintype.card n : ℝ) - Fintype.card n') / 2) : ℝ) : ℂ) •
        θ (φ (g • P₀)) (phiOneSB (g • P₀) (h • Q₀)) := by
  rw [KK_smul, hφ g, ← map_smul]
  refine (hθ g h _ _ _ ?_).symm
  ext x
  have m : ∀ z : kˣ, valuation k ((z * u : kˣ) : k) = 1 → μ z = (μ u)⁻¹ ∧ nabs k z = (nabs k u)⁻¹ := fun z hz =>
    ⟨eq_inv_of_mul_eq_one_left (by rw [← map_mul, hμ _ hz]),
      eq_inv_of_mul_eq_one_left (by rw [← nabs_mul, (nabs_eq_one_iff _).2 hz])⟩
  have hp : 0 < (nabs k u)⁻¹ := inv_pos.2 (nabs_pos k u)
  simp only [om, (m _ hg).1, (m _ hg).2, (m _ hh).1, (m _ hh).2, phiOneSB, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul, phiOne_smul, Units.mul_inv, one_mul]
  rw [← Complex.ofReal_mul, ← Real.rpow_add hp]
  congr 3
  ring

/- English proof (translation)
Take `⟨g, rfl⟩` from `MulAction.exists_smul_eq (GL n' k) P₀ P`. Take `⟨h, rfl⟩` from `MulAction.exists_smul_eq (GL n k) Q₀ Q`. Rewrite using `[KK_move hμ hθ P₀ Q₀ hφ 1 g h (by simpa only [mul_one] using valuation_det_of_fix _ hP) (by simpa only [mul_one] using valuation_det_of_fix _ hQ)]`. Simplify using `[nabs_one]`.
-/
theorem KK_same {φ : Form k n' V'} (hφ : φ ∈ EqForm π') {P : Pair k n'} {Q : Pair k n} (hP : P.lat = P₀.lat)
    (hQ : Q.lat = Q₀.lat) : KK hμ hθ P₀ Q₀ φ Q = θ (φ P) (phiOneSB P Q) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n' k) P₀ P
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) Q₀ Q
  rw [KK_move hμ hθ P₀ Q₀ hφ 1 g h (by simpa only [mul_one] using valuation_det_of_fix _ hP)
    (by simpa only [mul_one] using valuation_det_of_fix _ hQ)]
  simp [nabs_one]

/- English proof (translation)
Take `⟨g, rfl⟩` from `MulAction.exists_smul_eq (GL n' k) P₀ P`. Take `⟨h, rfl⟩` from `MulAction.exists_smul_eq (GL n k) Q₀ Q`. Rewrite `hP`, `hQ` using `[Pair.smul_ker]`. Rewrite using `[KK_move hμ hθ P₀ Q₀ hφ q.unit g h (valuation_det q _ hP) (valuation_det q _ hQ), nabs_uniformiser q.2 (x := q.unit) rfl, inv_inv, ht, scal]`. Use `congr 4`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem KK_up {t : ℕ} (ht : Fintype.card n = Fintype.card n' + (t + 1)) (q : Unif k) {φ : Form k n' V'}
    (hφ : φ ∈ EqForm π') {P : Pair k n'} {Q : Pair k n} (hP : P.ker = P₀.lat)
    (hQ : Q.ker = Q₀.lat) : KK hμ hθ P₀ Q₀ φ Q = scal k t • θ (φ P) (phiOneSB P Q) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n' k) P₀ P
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) Q₀ Q
  rw [Pair.smul_ker] at hP hQ
  rw [KK_move hμ hθ P₀ Q₀ hφ q.unit g h (valuation_det q _ hP) (valuation_det q _ hQ),
    nabs_uniformiser q.2 (x := q.unit) rfl, inv_inv, ht, scal]
  congr 4
  push_cast
  ring

/- English proof (translation)
Use `eq_of_base Q₀ (U_mem_EqForm q (KK_mem hμ hθ P₀ Q₀ φ)) (Submodule.smul_mem _ _ (KK_mem hμ hθ P₀ Q₀ _)) ?_` and prove the remaining obligations. Establish `h1 : ∀ P₁ ∈ withKer P₀.lat, U q (KK hμ hθ P₀ Q₀ φ) Q₀ = scal k t • ∑ P ∈ withLat P₀.lat, if cross q P₁ P = 1 then θ (φ P₁) (phiOneSB P Q₀) else 0` using `fun P₁ hP => by`. Rewrite `hP` using `[mem_withKer]`. Rewrite using `[U_apply, Finset.sum_congr rfl fun Q₁ hQ => KK_up hμ hθ P₀ Q₀ ht q hφ hP (mem_withKer.1 (Finset.mem_filter.1 hQ).1), ← Finset.smul_sum, ← Finset.sum_filter, ← map_sum, ← map_sum, ← hP]`. Use `congr 2`.

Use `Subtype.ext (funext fun x => ?_)` and prove the remaining obligations. Simplify using `only [Submodule.coe_sum, Finset.sum_apply, phiOneSB]`. Conclude with `(sum_target q P₁.hasVal_vec Q₀ x).trans (sum_source q P₁.hasVal_vec Q₀ x)`. Establish `h2 : ∀ P ∈ withLat P₀.lat, KK hμ hθ P₀ Q₀ (U q φ) Q₀ = ∑ P₁ ∈ withKer P₀.lat, if cross q P₁ P = 1 then θ (φ P₁) (phiOneSB P Q₀) else 0` using `fun P hP => by`. Rewrite `hP` using `[mem_withLat]`.

Rewrite using `[KK_same hμ hθ P₀ Q₀ (U_mem_EqForm q hφ) hP rfl, U_apply, map_sum, LinearMap.sum_apply, hP, Finset.sum_filter]`. Establish `h3` using `Finset.sum_congr rfl h1`. Rewrite `h3` using `[← Finset.smul_sum, Finset.sum_comm, ← Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const, card_withKer q, smul_comm, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ]`. Use `smul_right_injective V ?_ h3` and prove the remaining obligations. Conclude with `(Finset.card_pos.2 ⟨P₀, mem_withLat.2 rfl⟩).ne'` after adjusting the coercions.
-/
theorem U_KK {t : ℕ} (ht : Fintype.card n = Fintype.card n' + (t + 1)) (q : Unif k) {φ : Form k n' V'}
    (hφ : φ ∈ EqForm π') : U q (KK hμ hθ P₀ Q₀ φ) = scal k t • KK hμ hθ P₀ Q₀ (U q φ) := by
  classical
  refine eq_of_base Q₀ (U_mem_EqForm q (KK_mem hμ hθ P₀ Q₀ φ)) (Submodule.smul_mem _ _ (KK_mem hμ hθ P₀ Q₀ _)) ?_
  have h1 : ∀ P₁ ∈ withKer P₀.lat, U q (KK hμ hθ P₀ Q₀ φ) Q₀ =
      scal k t • ∑ P ∈ withLat P₀.lat, if cross q P₁ P = 1 then θ (φ P₁) (phiOneSB P Q₀) else 0 := fun P₁ hP => by
    rw [mem_withKer] at hP
    rw [U_apply, Finset.sum_congr rfl fun Q₁ hQ =>
      KK_up hμ hθ P₀ Q₀ ht q hφ hP (mem_withKer.1 (Finset.mem_filter.1 hQ).1), ← Finset.smul_sum,
      ← Finset.sum_filter, ← map_sum, ← map_sum, ← hP]
    congr 2
    refine Subtype.ext (funext fun x => ?_)
    simp only [Submodule.coe_sum, Finset.sum_apply, phiOneSB]
    exact (sum_target q P₁.hasVal_vec Q₀ x).trans (sum_source q P₁.hasVal_vec Q₀ x)
  have h2 : ∀ P ∈ withLat P₀.lat, KK hμ hθ P₀ Q₀ (U q φ) Q₀ =
      ∑ P₁ ∈ withKer P₀.lat, if cross q P₁ P = 1 then θ (φ P₁) (phiOneSB P Q₀) else 0 := fun P hP => by
    rw [mem_withLat] at hP
    rw [KK_same hμ hθ P₀ Q₀ (U_mem_EqForm q hφ) hP rfl, U_apply, map_sum, LinearMap.sum_apply, hP,
      Finset.sum_filter]
  have h3 := Finset.sum_congr rfl h1
  rw [← Finset.smul_sum, Finset.sum_comm, ← Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const,
    card_withKer q, smul_comm, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at h3
  refine smul_right_injective V ?_ h3
  exact_mod_cast (Finset.card_pos.2 ⟨P₀, mem_withLat.2 rfl⟩).ne'

/- English proof (translation)
Use `eq_of_base Q₀ (KK_mem hμ hθ P₀ Q₀ _) (dia_mem_EqForm s (KK_mem hμ hθ P₀ Q₀ φ)) ?_` and prove the remaining obligations. Rewrite using `[dia_apply, KK_same hμ hθ P₀ Q₀ hφ (P := s • P₀) (Q := s • Q₀) rfl rfl, KK_same hμ hθ P₀ Q₀ (dia_mem_EqForm s hφ) rfl rfl, dia_apply]`. Use `congr 1`. Conclude with `Subtype.ext (phiOne_dia s).symm`.
-/
theorem KK_dia (s : 𝓀[k]ˣ) {φ : Form k n' V'} (hφ : φ ∈ EqForm π') :
    KK hμ hθ P₀ Q₀ (dia s φ) = dia s (KK hμ hθ P₀ Q₀ φ) := by
  refine eq_of_base Q₀ (KK_mem hμ hθ P₀ Q₀ _) (dia_mem_EqForm s (KK_mem hμ hθ P₀ Q₀ φ)) ?_
  rw [dia_apply, KK_same hμ hθ P₀ Q₀ hφ (P := s • P₀) (Q := s • Q₀) rfl rfl,
    KK_same hμ hθ P₀ Q₀ (dia_mem_EqForm s hφ) rfl rfl, dia_apply]
  congr 1
  exact Subtype.ext (phiOne_dia s).symm

/- English proof (translation)
Establish `: Nm (KK hμ hθ P₀ Q₀ φ) = KK hμ hθ P₀ Q₀ (Nm φ)`. Simplify using `only [Nm, LinearMap.sum_apply, map_sum, KK_dia hμ hθ P₀ Q₀ _ hφ]`. Rewrite `this` using `[show Nm φ = 0 from h, map_zero]`. Conclude with `this`.
-/
theorem KK_ram {φ : Form k n' V'} (hφ : φ ∈ EqForm π') (h : φ ∈ Mram k n' V') : KK hμ hθ P₀ Q₀ φ ∈ Mram k n V := by
  have : Nm (KK hμ hθ P₀ Q₀ φ) = KK hμ hθ P₀ Q₀ (Nm φ) := by
    simp only [Nm, LinearMap.sum_apply, map_sum, KK_dia hμ hθ P₀ Q₀ _ hφ]
  rw [show Nm φ = 0 from h, map_zero] at this
  exact this

/- English proof (translation)
Establish `h1 : GsStar χ (KK hμ hθ P₀ Q₀ φ) = KK hμ hθ P₀ Q₀ (GsStar χ φ)`. Simplify using `only [GsStar, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, KK_dia hμ hθ P₀ Q₀ _ hφ]`. Establish `h2 : GsStar χ φ ∈ EqForm π'`. Simplify using `only [GsStar, LinearMap.sum_apply, LinearMap.smul_apply]`. Conclude with `sum_mem fun c _ => Submodule.smul_mem _ _ (dia_mem_EqForm _ hφ)`.

Rewrite using `[FFStar_eq_U_GsStar q χ h, FFStar_eq_U_GsStar q χ (KK_ram hμ hθ P₀ Q₀ hφ h), h1, U_KK hμ hθ P₀ Q₀ ht q h2]`.
-/
theorem FFStar_KK {t : ℕ} (ht : Fintype.card n = Fintype.card n' + (t + 1)) (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
    {φ : Form k n' V'} (hφ : φ ∈ EqForm π') (h : φ ∈ Mram k n' V') :
    FFStar q χ (KK hμ hθ P₀ Q₀ φ) = scal k t • KK hμ hθ P₀ Q₀ (FFStar q χ φ) := by
  have h1 : GsStar χ (KK hμ hθ P₀ Q₀ φ) = KK hμ hθ P₀ Q₀ (GsStar χ φ) := by
    simp only [GsStar, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, KK_dia hμ hθ P₀ Q₀ _ hφ]
  have h2 : GsStar χ φ ∈ EqForm π' := by
    simp only [GsStar, LinearMap.sum_apply, LinearMap.smul_apply]
    exact sum_mem fun c _ => Submodule.smul_mem _ _ (dia_mem_EqForm _ hφ)
  rw [FFStar_eq_U_GsStar q χ h, FFStar_eq_U_GsStar q χ (KK_ram hμ hθ P₀ Q₀ hφ h), h1, U_KK hμ hθ P₀ Q₀ ht q h2]

/- English proof (translation)
Rewrite using `[scal, ← sq, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]`. Rewrite using `[show ((t : ℝ) + 1) / 2 * (2 : ℕ) = ((t + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem scal_mul_scal (t : ℕ) : scal k t * scal k t = (resCard k : ℂ) ^ (t + 1) := by
  rw [scal, ← sq, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  rw [show ((t : ℝ) + 1) / 2 * (2 : ℕ) = ((t + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  push_cast
  rfl

/- English proof (translation)
Establish `h1` using `mem_ram (FF_dia q χ) h`. Establish `h2` using `FF_mem_EqForm q χ hφ`. Establish `h3` using `congrArg (FF q χ) (FFStar_KK hμ hθ P₀ Q₀ ht q χ h2 h1)`. Rewrite `h3` using `[FF_FFStar_ram q hχ (KK_ram hμ hθ P₀ Q₀ h2 h1), FFStar_FF_ram q hχ h, map_smul, map_smul, map_smul, ht, pow_add, ← scal_mul_scal, smul_smul]`. Establish `hs : scal k t ≠ 0` using `fun h0 => by`.

Use `scal_mul_scal (k := k) t` as an intermediate fact. Rewrite `this` using `[h0, mul_zero]`. Conclude with `pow_ne_zero _ resCard_ne_zero this.symm`. Use `smul_right_injective _ (mul_ne_zero hs (pow_ne_zero (Fintype.card n') (resCard_ne_zero (k := k)))) ?_` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[← h3, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem FF_KK {t : ℕ} (ht : Fintype.card n = Fintype.card n' + (t + 1)) (q : Unif k) {χ : AddChar 𝓀[k] ℂ}
    (hχ : χ ≠ 1) {φ : Form k n' V'} (hφ : φ ∈ EqForm π') (h : φ ∈ Mram k n' V') :
    FF q χ (KK hμ hθ P₀ Q₀ φ) = scal k t • KK hμ hθ P₀ Q₀ (FF q χ φ) := by
  have h1 := mem_ram (FF_dia q χ) h
  have h2 := FF_mem_EqForm q χ hφ
  have h3 := congrArg (FF q χ) (FFStar_KK hμ hθ P₀ Q₀ ht q χ h2 h1)
  rw [FF_FFStar_ram q hχ (KK_ram hμ hθ P₀ Q₀ h2 h1), FFStar_FF_ram q hχ h, map_smul, map_smul, map_smul, ht,
    pow_add, ← scal_mul_scal, smul_smul] at h3
  have hs : scal k t ≠ 0 := fun h0 => by
    have := scal_mul_scal (k := k) t
    rw [h0, mul_zero] at this
    exact pow_ne_zero _ resCard_ne_zero this.symm
  refine smul_right_injective _ (mul_ne_zero hs (pow_ne_zero (Fintype.card n') (resCard_ne_zero (k := k)))) ?_
  simp only
  rw [← h3, smul_smul]
  congr 1
  ring

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ _ _ _ ht q _ hψ _ hμ _ _ _ _ _ _ _ _ _ _ _ _ hθ P₀ Q₀` and use `⟨fun φ => U_KK hμ hθ P₀ Q₀ ht q φ.2, fun s φ => KK_dia hμ hθ P₀ Q₀ s φ.2, fun φ h => ⟨KK_ram hμ hθ P₀ Q₀ φ.2 h, FF_KK hμ hθ P₀ Q₀ ht q (resChar_ne_one hψ q) φ.2 h, FFStar_KK hμ hθ P₀ Q₀ ht q _ φ.2 h⟩⟩`.
-/
theorem operatorRules : OperatorRules :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ ht q _ hψ _ hμ _ _ _ _ _ _ _ _ _ _ _ _ hθ P₀ Q₀ =>
    ⟨fun φ => U_KK hμ hθ P₀ Q₀ ht q φ.2, fun s φ => KK_dia hμ hθ P₀ Q₀ s φ.2, fun φ h =>
      ⟨KK_ram hμ hθ P₀ Q₀ φ.2 h, FF_KK hμ hθ P₀ Q₀ ht q (resChar_ne_one hψ q) φ.2 h,
        FFStar_KK hμ hθ P₀ Q₀ ht q _ φ.2 h⟩⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨indicatorIdentity, operatorRules⟩`.
-/
theorem kernelsCommute : KernelsCommute := ⟨indicatorIdentity, operatorRules⟩

end GlobalTheory.KernelComm

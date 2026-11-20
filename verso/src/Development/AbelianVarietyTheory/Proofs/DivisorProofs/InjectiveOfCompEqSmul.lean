import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff

set_option autoImplicit false

noncomputable section

open CategoryTheory WittVector GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.Published GlobalTheory.PerfdLat
open scoped ChangeOfRings Pointwise

namespace GlobalTheory.PerfdLat.HodgeTateBal

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Set `B` to `Localization.Away a`. Establish `hc : w ∘ₗ u = a • LinearMap.id` using `LinearMap.ext h`. Establish `hs : Function.Surjective (w.baseChange B)` using `fun y => by`. Take `⟨v, hv⟩` from `IsLocalization.Away.algebraMap_isUnit (S := B) a`. Use `⟨u.baseChange B ((v⁻¹ : Bˣ) • y), ?_⟩` and prove the remaining obligations.

Rewrite using `[← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hc, LinearMap.baseChange_smul, LinearMap.baseChange_id, LinearMap.smul_apply, LinearMap.id_apply, ← algebraMap_smul B a, ← hv, Units.smul_def, smul_smul, Units.mul_inv, one_smul]`. Establish `hb` using `Module.bijective_of_surjective_of_rankAtStalk_eq hs fun q _ => by`. Rewrite using `[Module.rankAtStalk_baseChange, Module.rankAtStalk_baseChange, hr]`. Use `(injective_iff_map_eq_zero _).2 fun m hm => ?_` and prove the remaining obligations. Establish `h1 : TensorProduct.mk R B M 1 m = 0` using `hb.1 (by simp [hm])`.

Take `⟨⟨_, k, rfl⟩, hk⟩` from `(IsLocalizedModule.eq_zero_iff (Submonoid.powers a) _).1 h1`. Establish `h2 : IsSMulRegular M a` using `Module.Flat.isSMulRegular_of_isRegular ((Commute.isRegular_iff (Commute.all a)).2 (isLeftRegular_iff.2 ha))`. Conclude with `(h2.pow k) (hk.trans (smul_zero _).symm)`.
-/
theorem injective_of_comp_eq_smul' {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [Module.Finite R M] [Module.Flat R M] [Module.Finite R N] [Module.Flat R N]
    (hr : Module.rankAtStalk (R := R) M = Module.rankAtStalk N) (u : N →ₗ[R] M) (w : M →ₗ[R] N) {a : R}
    (ha : IsSMulRegular R a) (h : ∀ x, w (u x) = a • x) : Function.Injective w := by
  let B := Localization.Away a
  have hc : w ∘ₗ u = a • LinearMap.id := LinearMap.ext h
  have hs : Function.Surjective (w.baseChange B) := fun y => by
    obtain ⟨v, hv⟩ := IsLocalization.Away.algebraMap_isUnit (S := B) a
    refine ⟨u.baseChange B ((v⁻¹ : Bˣ) • y), ?_⟩
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hc, LinearMap.baseChange_smul, LinearMap.baseChange_id,
      LinearMap.smul_apply, LinearMap.id_apply, ← algebraMap_smul B a, ← hv, Units.smul_def, smul_smul, Units.mul_inv,
      one_smul]
  have hb := Module.bijective_of_surjective_of_rankAtStalk_eq hs fun q _ => by
    rw [Module.rankAtStalk_baseChange, Module.rankAtStalk_baseChange, hr]
  refine (injective_iff_map_eq_zero _).2 fun m hm => ?_
  have h1 : TensorProduct.mk R B M 1 m = 0 := hb.1 (by simp [hm])
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers a) _).1 h1
  have h2 : IsSMulRegular M a := Module.Flat.isSMulRegular_of_isRegular
    ((Commute.isRegular_iff (Commute.all a)).2 (isLeftRegular_iff.2 ha))
  exact (h2.pow k) (hk.trans (smul_zero _).symm)

/- English proof (translation)
Establish `hc : ∀ (n : ℕ) (a : Ainf p S.R), ((phiInv p S.R)^[n] a).coeff 0 = (_root_.frobeniusEquiv (PreTilt S.R p) p).symm^[n] (a.coeff 0)` using `fun n a => by`. Proceed by induction on `n with`. Consider the case `zero => rfl`. Consider the case `succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]`. Both sides reduce to the same expression.

Establish `hp : ∀ (n : ℕ) (a : Ainf p S.R), (phiInv p S.R)^[n] (a * p) = (phiInv p S.R)^[n] a * p` using `fun n a => by`. Proceed by induction on `n with`. Consider the case `zero => rfl`. Consider the case `succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul, map_natCast]`. Establish `key : ∀ (k : ℕ) (a : Ainf p S.R), (∀ n, fontaineTheta S.R p ((phiInv p S.R)^[n + 1] a) = 0) → a ∈ Ideal.span {(p : Ainf p S.R) ^ k}` using `fun k => by`.

Proceed by induction on `k with`. Consider the case `zero => intro a _`. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `a h`.

Establish `h0 : (_root_.frobeniusEquiv (PreTilt S.R p) p).symm (a.coeff 0) = 0` using `Perfection.ext fun n => by`. Establish `h1` using `mk_fontaineTheta ((phiInv p S.R)^[n + 1] a)`. Rewrite `h1` using `[h, map_zero, hc, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add, ← PreTilt.coeff_frobeniusEquiv_symm]`. Conclude with `h1.symm.trans (map_zero _).symm`. Take `⟨b, rfl⟩` from `Ideal.mem_span_singleton'.1 ((mem_span_p_iff_coeff_zero_eq_zero a).2 ((map_eq_zero_iff _ (RingEquiv.injective _)).1 h0))`.

Rewrite using `[pow_succ, ← Ideal.span_singleton_mul_span_singleton]`. Use `Ideal.mul_mem_mul (ih b fun n => S.reg ?_) (Ideal.mem_span_singleton_self _)` and prove the remaining obligations. Establish `h1` using `h n`. Rewrite `h1` using `[hp, map_mul, map_natCast]`. Simplify `h1` using `[mul_comm]`.

Use extensionality with `m`. Simplify using `using (mem_span_p_pow_iff_le_coeff_eq_zero a (m + 1)).1 (key _ a h) m m.lt_succ_self`.
-/
theorem eq_zero_of_theta_phiInv' (S : CycPerfd p) (a : Ainf p S.R)
    (h : ∀ n, fontaineTheta S.R p ((phiInv p S.R)^[n + 1] a) = 0) : a = 0 := by
  have hc : ∀ (n : ℕ) (a : Ainf p S.R), ((phiInv p S.R)^[n] a).coeff 0 =
      (_root_.frobeniusEquiv (PreTilt S.R p) p).symm^[n] (a.coeff 0) := fun n a => by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl
  have hp : ∀ (n : ℕ) (a : Ainf p S.R), (phiInv p S.R)^[n] (a * p) = (phiInv p S.R)^[n] a * p := fun n a => by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul, map_natCast]
  have key : ∀ (k : ℕ) (a : Ainf p S.R), (∀ n, fontaineTheta S.R p ((phiInv p S.R)^[n + 1] a) = 0) →
      a ∈ Ideal.span {(p : Ainf p S.R) ^ k} := fun k => by
    induction k with
    | zero => intro a _; simp
    | succ k ih =>
      intro a h
      have h0 : (_root_.frobeniusEquiv (PreTilt S.R p) p).symm (a.coeff 0) = 0 := Perfection.ext fun n => by
        have h1 := mk_fontaineTheta ((phiInv p S.R)^[n + 1] a)
        rw [h, map_zero, hc, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add,
          ← PreTilt.coeff_frobeniusEquiv_symm] at h1
        exact h1.symm.trans (map_zero _).symm
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1
        ((mem_span_p_iff_coeff_zero_eq_zero a).2 ((map_eq_zero_iff _ (RingEquiv.injective _)).1 h0))
      rw [pow_succ, ← Ideal.span_singleton_mul_span_singleton]
      refine Ideal.mul_mem_mul (ih b fun n => S.reg ?_) (Ideal.mem_span_singleton_self _)
      have h1 := h n
      rw [hp, map_mul, map_natCast] at h1
      simpa [mul_comm] using h1
  ext m
  simpa using (mem_span_p_pow_iff_le_coeff_eq_zero a (m + 1)).1 (key _ a h) m m.lt_succ_self

/- English proof (translation)
The claim follows from `IsSMulRegular.of_right_eq_zero_of_smul fun a ha => eq_zero_of_theta_phiInv' S a fun n => by have h : ∀ n, muN S n * (phiInv p S.R)^[n] a = 0 := fun n => by induction n with | zero => exact ha | succ n ih => rw [Function.iterate_succ_apply', ← phiInv_muN, ← map_mul, ih, map_zero] …`.
-/
theorem isSMulRegular_mu' (S : CycPerfd p) : IsSMulRegular (Ainf p S.R) (Sandwich.mu S.ε) :=
  IsSMulRegular.of_right_eq_zero_of_smul fun a ha => eq_zero_of_theta_phiInv' S a fun n => by
    have h : ∀ n, muN S n * (phiInv p S.R)^[n] a = 0 := fun n => by
      induction n with
      | zero => exact ha
      | succ n ih => rw [Function.iterate_succ_apply', ← phiInv_muN, ← map_mul, ih, map_zero]
    have h1 := congrArg (fontaineTheta S.R p) (h (n + 1))
    rw [map_mul, theta_muN, map_zero] at h1
    exact (isSMulRegular_zeta_sub_one S n).right_eq_zero_of_smul h1

variable (D : PrismData p) {S : CycPerfd p}

/- English proof (translation)
Express the relevant statement in the definitionally equal form `lieMap _ H H.bidual.inv (D.lie S H.dual (D.map S H.dual G.dual (dualHom G H f) m)) = lieMap G H f (lieMap _ G G.bidual.inv (D.lie S G.dual m))`. Rewrite using `[D.lie_map, ← LinearMap.comp_apply, ← lieMap_comp, dualHom_dualHom_bidual_inv, lieMap_comp, LinearMap.comp_apply]`.
-/
theorem toLie_covMap (G H : PDivGroup p S.R) (f : G ⟶ H) (m : D.Cov G) :
    D.toLie H (D.covMap G H f m) = lieMap G H f (D.toLie G m) := by
  change lieMap _ H H.bidual.inv (D.lie S H.dual (D.map S H.dual G.dual (dualHom G H f) m)) =
    lieMap G H f (lieMap _ G G.bidual.inv (D.lie S G.dual m))
  rw [D.lie_map, ← LinearMap.comp_apply, ← lieMap_comp, dualHom_dualHom_bidual_inv, lieMap_comp, LinearMap.comp_apply]

def lieVal (S : CycPerfd p) : S.R := D.toLie (PDivGroup.mu p S.R) (D.e S) (dlogT p S.R)

/- English proof (translation)
Take `⟨m, hm⟩` from `D.toLie_surjective (PDivGroup.mu p S.R) (muLieGen p S.R)`. Establish `h1 : D.toLie (PDivGroup.mu p S.R) m = fontaineTheta S.R p (D.eCoord S m) • D.toLie _ (D.e S)` using `by conv_lhs => rw [← D.eCoord_smul m]`. Conclude with `map_smulₛₗ _ _ _`. Establish `h2` using `LinearMap.congr_fun (hm.symm.trans h1) (dlogT p S.R)`. Rewrite `h2` using `[muLieGen_dlogT, LinearMap.smul_apply, smul_eq_mul]`.

Conclude with `IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans h2.symm)`.
-/
theorem isUnit_lieVal (S : CycPerfd p) : IsUnit (lieVal D S) := by
  obtain ⟨m, hm⟩ := D.toLie_surjective (PDivGroup.mu p S.R) (muLieGen p S.R)
  have h1 : D.toLie (PDivGroup.mu p S.R) m = fontaineTheta S.R p (D.eCoord S m) • D.toLie _ (D.e S) := by
    conv_lhs => rw [← D.eCoord_smul m]
    exact map_smulₛₗ _ _ _
  have h2 := LinearMap.congr_fun (hm.symm.trans h1) (dlogT p S.R)
  rw [muLieGen_dlogT, LinearMap.smul_apply, smul_eq_mul] at h2
  exact IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans h2.symm)

variable {G : PDivGroup p S.R} (c : ConstTate (eps S) G)

/- English proof (translation)
Establish `h1` using `congrArg (D.toLie (PDivGroup.mu p S.R)) (coord_smul_e D c m j)`. Rewrite `h1` using `[map_smulₛₗ, toLie_covMap, lieMap_charHom]`. Establish `h2` using `LinearMap.congr_fun h1 (dlogT p S.R)`. Rewrite `h2` using `[LinearMap.smul_apply, LinearMap.smul_apply, muLieGen_dlogT, smul_eq_mul, smul_eq_mul, mul_one]`. Conclude with `h2`.
-/
theorem theta_coord_mul (m : D.Cov G) (j : Fin G.height) :
    fontaineTheta S.R p (coord D c m j) * lieVal D S = c.alDual (D.toLie G m) j := by
  have h1 := congrArg (D.toLie (PDivGroup.mu p S.R)) (coord_smul_e D c m j)
  rw [map_smulₛₗ, toLie_covMap, lieMap_charHom] at h1
  have h2 := LinearMap.congr_fun h1 (dlogT p S.R)
  rw [LinearMap.smul_apply, LinearMap.smul_apply, muLieGen_dlogT, smul_eq_mul, smul_eq_mul, mul_one] at h2
  exact h2

/- English proof (translation)
Establish `h : ∀ i, D.map S G.dual (PDivGroup.mu p S.R) (dualChar G (c.t i)) (D.l S) ∈ D.Fil G` using `fun i => (D.mem_Fil G _).2 ⟨D.map S G.dual (PDivGroup.mu p S.R) (dualChar G (c.t i)) (D.l S), by`. Rewrite using `[← D.map_φ, D.φ_l, map_smul]⟩`. Establish `h1 : inj D c y ∈ D.Fil G`. Rewrite using `[inj_apply]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h i)`.

Conclude with `LinearMap.mem_ker.1 h1`.
-/
theorem toLie_inj (y : Fin G.height → Ainf p S.R) : D.toLie G (inj D c y) = 0 := by
  have h : ∀ i, D.map S G.dual (PDivGroup.mu p S.R) (dualChar G (c.t i)) (D.l S) ∈ D.Fil G := fun i =>
    (D.mem_Fil G _).2 ⟨D.map S G.dual (PDivGroup.mu p S.R) (dualChar G (c.t i)) (D.l S), by
      rw [← D.map_φ, D.φ_l, map_smul]⟩
  have h1 : inj D c y ∈ D.Fil G := by
    rw [inj_apply]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h i)
  exact LinearMap.mem_ker.1 h1

/- English proof (translation)
The claim follows from `injective_of_comp_eq_smul' (funext fun q => by haveI := q.nontrivial rw [D.rank_eq S G.dual q, Module.rankAtStalk_eq_finrank_of_free] simp) (inj D c) (coord D c) (isSMulRegular_mu' S) (coord_inj D c)`.
-/
theorem coord_injective : Function.Injective (coord D c) :=
  injective_of_comp_eq_smul' (funext fun q => by
      haveI := q.nontrivial
      rw [D.rank_eq S G.dual q, Module.rankAtStalk_eq_finrank_of_free]
      simp)
    (inj D c) (coord D c) (isSMulRegular_mu' S) (coord_inj D c)

end GlobalTheory.PerfdLat.HodgeTateBal

namespace GlobalTheory.PerfdLat

open HodgeTateBal in

/- English proof (translation)
Introduce `p _ D S`. Take `⟨v, hv⟩` from `isUnit_lieVal D S`. Use `⟨v⁻¹, fun G c => ?_⟩` and prove the remaining obligations. Establish `hb : ∀ m, b D c m = ((v⁻¹ : (S.R)ˣ) : S.R) • c.alDual (D.toLie G m)` using `fun m => funext fun j => by`. Rewrite using `[Pi.smul_apply, smul_eq_mul, b_apply, ← theta_coord_mul D c m j, ← hv, mul_comm (fontaineTheta S.R p _), ← mul_assoc, Units.inv_mul, one_mul]`.

Use `⟨hb, (injective_iff_map_eq_zero _).2 fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨m, rfl⟩` from `D.toLie_surjective G x`. Establish `h0 : ∀ j, coord D c m j ∈ Ideal.span {xi S.ε}` using `fun j => by`. Rewrite using `[← S.ker_eq, RingHom.mem_ker]`. Establish `h1` using `congrFun (hb m) j`.

Rewrite `h1` using `[hx, smul_zero]`. Conclude with `h1`. Use `choose y hy using fun j => Ideal.mem_span_singleton'.1 (h0 j)`. Establish `e : Sandwich.mu S.ε = xi S.ε * muN S 1` using `(xiN_mul_muN S 0).symm`. Establish `hc : coord D c (muN S 1 • m) = coord D c (inj D c y)`.

Rewrite using `[coord_inj, map_smul]`. Use function extensionality and compare the values at `j`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← hy j, e]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : D.toLie G (muN S 1 • m) = 0` using `(coord_injective D c hc).symm ▸ toLie_inj D c y`. Rewrite `h2` using `[map_smulₛₗ, theta_muN]`. Use `LinearMap.ext fun w => ?_` and prove the remaining obligations. Establish `h3` using `LinearMap.congr_fun h2 w`. Rewrite `h3` using `[LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul]`.

Conclude with `(isSMulRegular_zeta_sub_one S 0).right_eq_zero_of_smul h3`.
-/
theorem b_eq_unit_smul_alDual : ∀ (p : ℕ) [Fact p.Prime] (D : PrismData p) (S : CycPerfd p), ∃ u : (S.R)ˣ,
    ∀ (G : PDivGroup p S.R) (c : ConstTate (eps S) G),
      (∀ m, b D c m = (u : S.R) • c.alDual (D.toLie G m)) ∧ Function.Injective c.alDual := by
  intro p _ D S
  obtain ⟨v, hv⟩ := isUnit_lieVal D S
  refine ⟨v⁻¹, fun G c => ?_⟩
  have hb : ∀ m, b D c m = ((v⁻¹ : (S.R)ˣ) : S.R) • c.alDual (D.toLie G m) := fun m => funext fun j => by
    rw [Pi.smul_apply, smul_eq_mul, b_apply, ← theta_coord_mul D c m j, ← hv, mul_comm (fontaineTheta S.R p _),
      ← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨hb, (injective_iff_map_eq_zero _).2 fun x hx => ?_⟩
  obtain ⟨m, rfl⟩ := D.toLie_surjective G x
  have h0 : ∀ j, coord D c m j ∈ Ideal.span {xi S.ε} := fun j => by
    rw [← S.ker_eq, RingHom.mem_ker]
    have h1 := congrFun (hb m) j
    rw [hx, smul_zero] at h1
    exact h1
  choose y hy using fun j => Ideal.mem_span_singleton'.1 (h0 j)
  have e : Sandwich.mu S.ε = xi S.ε * muN S 1 := (xiN_mul_muN S 0).symm
  have hc : coord D c (muN S 1 • m) = coord D c (inj D c y) := by
    rw [coord_inj, map_smul]
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← hy j, e]
    ring
  have h2 : D.toLie G (muN S 1 • m) = 0 := (coord_injective D c hc).symm ▸ toLie_inj D c y
  rw [map_smulₛₗ, theta_muN] at h2
  refine LinearMap.ext fun w => ?_
  have h3 := LinearMap.congr_fun h2 w
  rw [LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul] at h3
  exact (isSMulRegular_zeta_sub_one S 0).right_eq_zero_of_smul h3

end GlobalTheory.PerfdLat

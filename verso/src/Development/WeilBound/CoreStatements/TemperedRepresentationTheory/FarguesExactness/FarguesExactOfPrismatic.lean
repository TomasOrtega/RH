import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTatePairingSandwich
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedInOfIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichOfPrismaticDieudonneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupOmegaFiniteFreeAndPSqMemDlogSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeAtOfPrismaticDieudonneAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCobOneOfIntegral

noncomputable section

open TensorProduct GlobalTheory GlobalTheory.PDivGroup

namespace PositivityTheory.Tls2.Jfarg

/- English proof (translation)
Establish `hle : LinearMap.ker f ≤ LinearMap.ker φ` using `fun y hy => h y hy`. Set `g : LinearMap.range f →ₗ[O] O` to `((LinearMap.ker f).liftQ φ hle).comp f.quotKerEquivRange.symm.toLinearMap`. Set `c : N →ₗ[O] LinearMap.range f` to `LinearMap.codRestrict (LinearMap.range f) (κ • LinearMap.id) (fun w => by simpa using hκ w)`. Use `⟨g.comp c, fun y => ?_⟩` and prove the remaining obligations. Establish `hc : c (f y) = ⟨f (κ • y), LinearMap.mem_range_self f _⟩` using `Subtype.ext (by simp [c])`.

Rewrite using `[LinearMap.comp_apply, hc]`. Use `show κ * φ y = (LinearMap.ker f).liftQ φ hle (f.quotKerEquivRange.symm ⟨f (κ • y), LinearMap.mem_range_self f _⟩)`. Rewrite using `[LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply, map_smul, smul_eq_mul]`.
-/
theorem exists_factor {O M N : Type} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
    (f : M →ₗ[O] N) (φ : M →ₗ[O] O) (h : ∀ y, f y = 0 → φ y = 0) (κ : O)
    (hκ : ∀ w, κ • w ∈ LinearMap.range f) : ∃ l : N →ₗ[O] O, ∀ y, κ * φ y = l (f y) := by
  have hle : LinearMap.ker f ≤ LinearMap.ker φ := fun y hy => h y hy
  let g : LinearMap.range f →ₗ[O] O :=
    ((LinearMap.ker f).liftQ φ hle).comp f.quotKerEquivRange.symm.toLinearMap
  let c : N →ₗ[O] LinearMap.range f :=
    LinearMap.codRestrict (LinearMap.range f) (κ • LinearMap.id) (fun w => by simpa using hκ w)
  refine ⟨g.comp c, fun y => ?_⟩
  have hc : c (f y) = ⟨f (κ • y), LinearMap.mem_range_self f _⟩ := Subtype.ext (by simp [c])
  rw [LinearMap.comp_apply, hc]
  show κ * φ y = (LinearMap.ker f).liftQ φ hle
    (f.quotKerEquivRange.symm ⟨f (κ • y), LinearMap.mem_range_self f _⟩)
  rw [LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply,
    map_smul, smul_eq_mul]

/- English proof (translation)
Establish `key : ∀ k m, ζ (m + k) ^ (p ^ k) = ζ m`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro m`. Simplify using the standard rewrite rules.

Consider the case `succ k ih`. Introduce `m`. Rewrite using `[pow_succ', pow_mul, ← Nat.add_assoc, h, ih]`. Consider the cases of `n with`. Consider the case `zero => simpa [h0] using (IsPrimitiveRoot.one : IsPrimitiveRoot (1 : O) 1)`.

Consider the case `succ m`. Establish `hfin : ζ (m + 1) ^ p ^ (m + 1) = 1`. Use `key (m + 1) 0` as an intermediate fact. Simplify `this` using `[h0]`. Establish `hnot : ¬ ζ (m + 1) ^ p ^ m = 1`.

Use `key m 1` as an intermediate fact. Rewrite `this` using `[show 1 + m = m + 1 by omega]`. Rewrite using `[this]`. Conclude with `h1`. Establish `ho` using `orderOf_eq_prime_pow hnot hfin`.

Rewrite using `[← ho]`. Conclude with `IsPrimitiveRoot.orderOf _`.
-/
theorem primitive {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {ζ : ℕ → O} (h0 : ζ 0 = 1)
    (h : ∀ n, ζ (n + 1) ^ p = ζ n) (h1 : ζ 1 ≠ 1) (n : ℕ) : IsPrimitiveRoot (ζ n) (p ^ n) := by
  have key : ∀ k m, ζ (m + k) ^ (p ^ k) = ζ m := by
    intro k
    induction k with
    | zero => intro m; simp
    | succ k ih =>
      intro m
      rw [pow_succ', pow_mul, ← Nat.add_assoc, h, ih]
  cases n with
  | zero => simpa [h0] using (IsPrimitiveRoot.one : IsPrimitiveRoot (1 : O) 1)
  | succ m =>
    have hfin : ζ (m + 1) ^ p ^ (m + 1) = 1 := by
      have := key (m + 1) 0
      simpa [h0] using this
    have hnot : ¬ ζ (m + 1) ^ p ^ m = 1 := by
      have := key m 1
      rw [show 1 + m = m + 1 by omega] at this
      rw [this]
      exact h1
    have ho := orderOf_eq_prime_pow hnot hfin
    rw [← ho]
    exact IsPrimitiveRoot.orderOf _

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ hv hp hO G ζ h0 h h1 B hB x`. Use `haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)`. Use `haveI : Fact ¬IsUnit (p : O) := ⟨fun hu => by`. Use `hv.one_of_isUnit hu` as an intermediate fact. Rewrite `this` using `[map_natCast]`.

Conclude with `hp.ne this⟩`. Establish `hp0 : (p : O) ≠ 0` using `fun h => by`. Establish `h5 : algebraMap O C (p : O) = 0` using `by rw [h, map_zero]`. Rewrite `h5` using `[map_natCast]`. Conclude with `Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero h5`.

Take `⟨ε, hε₁⟩` from `ReciprocityTheory.PGsh.exists_eps (p := p) C _ O hv`. Establish `hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε` using `GlobalTheory.PrismModel.isPrimitiveSystem_of_one hε₁`. Establish `hS` using `GlobalTheory.T.hodgeTateSandwich_of_prismaticDieudonne hP p C v O hv ε hε`. Establish `hζ : Function.Bijective fun a : ℤ_[p] => a • muTate O ζ h0 h` using `smul_muTate_bijective ζ h0 h (primitive h0 h h1)`. Take `⟨B₀, hB₀, -, -⟩` from `GlobalTheory.PointGroup.exists_form hv G _ hζ`.

Establish `hk` using `(GlobalTheory.DetInv.HTKer.ker_hodgeTateLinear p C v O ε hε hS G _ B₀ hv hζ hB₀).1 x`. Take `⟨-, -, hc⟩` from `GlobalTheory.T.pDivGroup_omega_finite_free_and_p_sq_mem_dlog_span p C v O ε hε hv hS G`. Establish `hBB : ∀ (z : O ⊗[ℤ_[p]] G.Tate) (χ : G.dual.Tate), (TensorProduct.rid ℤ_[p] O) ((B₀.flip χ).baseChange O z) = B z (1 ⊗ₜ χ)` using `fun z χ => by`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]`. Consider the case `tmul c t`. Take `⟨a, ha, hb⟩` from `hB t χ`. Establish `e : B₀ t χ = a` using `hζ.1 ((hB₀ t χ).symm.trans ha)`. Establish `h4 : (c ⊗ₜ t : O ⊗[ℤ_[p]] G.Tate) = c • (1 ⊗ₜ t)` using `by rw [smul_tmul', smul_eq_mul, mul_one]`.

Rewrite using `[LinearMap.baseChange_tmul, LinearMap.flip_apply, TensorProduct.rid_tmul, e, h4, map_smul, LinearMap.smul_apply, hb, Algebra.smul_def, smul_eq_mul, mul_comm]`. Simplify using `only [hBB] at hk`. Rewrite using `[hk]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, l, hc0, hl⟩ y hy`.

Establish `h2 : ∀ z, c * B x z = l (dlogLinear G z)` using `fun z => by`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, mul_add, ha, hb]`. Consider the case `tmul d χ`.

Establish `h5 : (d ⊗ₜ χ : O ⊗[ℤ_[p]] G.dual.Tate) = d • (1 ⊗ₜ χ)`. Rewrite using `[smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[dlogLinear_tmul, map_smul, ← hl, h5, map_smul, smul_eq_mul, smul_eq_mul, mul_left_comm]`. Establish `h3` using `h2 y`. Rewrite `h3` using `[hy, map_zero]`.

Conclude with `(mul_eq_zero.1 h3).resolve_left hc0`. Introduce `hx`. Establish `hle : Submodule.span O (Set.range (dlog G)) ≤ LinearMap.range (dlogLinear G)` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨χ, rfl⟩`. Conclude with `⟨1 ⊗ₜ χ, by rw [dlogLinear_tmul, one_smul]⟩)`.

Take `⟨l, hl⟩` from `exists_factor (dlogLinear G) (B x) hx ((p : O) ^ 2) fun w => hle (hc w)`. Conclude with `⟨(p : O) ^ 2, l, pow_ne_zero _ hp0, fun χ => by rw [hl, dlogLinear_tmul, one_smul]⟩`.
-/
theorem farguesExact_of_hodge (hP : GlobalTheory.Published.PrismaticDieudonneHodge) : GlobalTheory.CompanionTheory.Ar.HT.FarguesExact := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO G ζ h0 h h1 B hB x
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : Fact ¬IsUnit (p : O) := ⟨fun hu => by
    have := hv.one_of_isUnit hu
    rw [map_natCast] at this
    exact hp.ne this⟩
  have hp0 : (p : O) ≠ 0 := fun h => by
    have h5 : algebraMap O C (p : O) = 0 := by rw [h, map_zero]
    rw [map_natCast] at h5
    exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero h5
  obtain ⟨ε, hε₁⟩ := ReciprocityTheory.PGsh.exists_eps (p := p) C _ O hv
  have hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε := GlobalTheory.PrismModel.isPrimitiveSystem_of_one hε₁
  have hS := GlobalTheory.T.hodgeTateSandwich_of_prismaticDieudonne hP p C v O hv ε hε
  have hζ : Function.Bijective fun a : ℤ_[p] => a • muTate O ζ h0 h :=
    smul_muTate_bijective ζ h0 h (primitive h0 h h1)
  obtain ⟨B₀, hB₀, -, -⟩ := GlobalTheory.PointGroup.exists_form hv G _ hζ
  have hk := (GlobalTheory.DetInv.HTKer.ker_hodgeTateLinear p C v O ε hε hS G _ B₀ hv hζ hB₀).1 x
  obtain ⟨-, -, hc⟩ := GlobalTheory.T.pDivGroup_omega_finite_free_and_p_sq_mem_dlog_span p C v O ε hε hv hS G
  have hBB : ∀ (z : O ⊗[ℤ_[p]] G.Tate) (χ : G.dual.Tate),
      (TensorProduct.rid ℤ_[p] O) ((B₀.flip χ).baseChange O z) = B z (1 ⊗ₜ χ) := fun z χ => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
    | tmul c t =>
      obtain ⟨a, ha, hb⟩ := hB t χ
      have e : B₀ t χ = a := hζ.1 ((hB₀ t χ).symm.trans ha)
      have h4 : (c ⊗ₜ t : O ⊗[ℤ_[p]] G.Tate) = c • (1 ⊗ₜ t) := by rw [smul_tmul', smul_eq_mul, mul_one]
      rw [LinearMap.baseChange_tmul, LinearMap.flip_apply, TensorProduct.rid_tmul, e, h4, map_smul,
        LinearMap.smul_apply, hb, Algebra.smul_def, smul_eq_mul, mul_comm]
  simp only [hBB] at hk
  rw [hk]
  constructor
  · rintro ⟨c, l, hc0, hl⟩ y hy
    have h2 : ∀ z, c * B x z = l (dlogLinear G z) := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add, mul_add, ha, hb]
      | tmul d χ =>
        have h5 : (d ⊗ₜ χ : O ⊗[ℤ_[p]] G.dual.Tate) = d • (1 ⊗ₜ χ) := by
          rw [smul_tmul', smul_eq_mul, mul_one]
        rw [dlogLinear_tmul, map_smul, ← hl, h5, map_smul, smul_eq_mul, smul_eq_mul, mul_left_comm]
    have h3 := h2 y
    rw [hy, map_zero] at h3
    exact (mul_eq_zero.1 h3).resolve_left hc0
  · intro hx
    have hle : Submodule.span O (Set.range (dlog G)) ≤ LinearMap.range (dlogLinear G) :=
      Submodule.span_le.2 (by
        rintro _ ⟨χ, rfl⟩
        exact ⟨1 ⊗ₜ χ, by rw [dlogLinear_tmul, one_smul]⟩)
    obtain ⟨l, hl⟩ := exists_factor (dlogLinear G) (B x) hx ((p : O) ^ 2) fun w => hle (hc w)
    exact ⟨(p : O) ^ 2, l, pow_ne_zero _ hp0, fun χ => by rw [hl, dlogLinear_tmul, one_smul]⟩

end PositivityTheory.Tls2.Jfarg

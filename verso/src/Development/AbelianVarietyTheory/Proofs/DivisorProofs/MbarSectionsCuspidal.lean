import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Filter Topology AlgebraicGeometry
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal TensorProduct

namespace GlobalTheory.CovHt.Link.ApproxSec

section Local

variable {X : Scheme.{0}} [IsIntegral X] {x : X} {f : X.functionField}

/- English proof (translation)
The claim follows from `have ⟨a, ha⟩ := hf; ⟨a ^ n, by rw [map_pow, ha]⟩`.
-/
theorem regAt_pow (hf : RegAt x f) (n : ℕ) : RegAt x (f ^ n) :=
  have ⟨a, ha⟩ := hf; ⟨a ^ n, by rw [map_pow, ha]⟩

/- English proof (translation)
The claim follows from `have ⟨a, hu, ha⟩ := hf; ⟨a ^ n, hu.pow n, by rw [map_pow, ha]⟩`.
-/
theorem unitAt_pow (hf : UnitAt x f) (n : ℕ) : UnitAt x (f ^ n) :=
  have ⟨a, hu, ha⟩ := hf; ⟨a ^ n, hu.pow n, by rw [map_pow, ha]⟩

/- English proof (translation)
The claim follows from `have ⟨a, hu, ha⟩ := hf; ⟨a ^ n, Ideal.pow_mem_of_mem _ hu n hn, by rw [map_pow, ha]⟩`.
-/
theorem zeroAt_pow (hf : ZeroAt x f) {n : ℕ} (hn : 0 < n) : ZeroAt x (f ^ n) :=
  have ⟨a, hu, ha⟩ := hf; ⟨a ^ n, Ideal.pow_mem_of_mem _ hu n hn, by rw [map_pow, ha]⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `h`. Conclude with `IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hn (ha ▸ isIntegral_algebraMap)`.
-/
theorem regAt_of_pow (hx : IsIntegrallyClosed (X.presheaf.stalk x)) {n : ℕ} (hn : 0 < n)
    (h : RegAt x (f ^ n)) : RegAt x f := by
  obtain ⟨a, ha⟩ := h
  exact IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hn (ha ▸ isIntegral_algebraMap)

/- English proof (translation)
Take `⟨d, hd⟩` from `Δ.exists_isEqn x`. Take `⟨b, hb⟩` from `B.exists_isEqn x`. Take `⟨g, hg⟩` from `Λ.exists_isEqn x`. Establish `h₁` using `(hd.nsmul a).add (hb.nsmul m)`. Rewrite `h₁` using `[e]`.

Establish `h₂` using `(h₁.iff_unitAt.1 (hg.nsmul _)).regAt`. Establish `h₃` using `(hd.nsmul τ).regularAt_iff.1 hf`. Establish `h₄` using `CartierDiv.eff_iff.1 hB x b hb`. Establish `h₅` using `(regAt_pow h₃ a).mul (regAt_pow h₂ τ)`. Establish `key : (f * (g ^ τ : X.functionFieldˣ)) ^ (n * a) = (b : X.functionField) ^ (m * τ) * ((f ^ n * (d ^ τ : X.functionFieldˣ)) ^ a * (((g ^ (n * a) : X.functionFieldˣ) : X.functionField) / (d ^ a * b ^ m : X.functionFieldˣ)) ^ τ)`.

Use `d.ne_zero` as an intermediate fact. Use `b.ne_zero` as an intermediate fact. Simplify using `only [Units.val_pow_eq_pow_val, Units.val_mul, div_pow, mul_pow, ← pow_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `h₆` using `regAt_of_pow hx (Nat.mul_pos hn ha) (key ▸ (regAt_pow h₄ _).mul h₅)`. Use `⟨(hg.nsmul τ).regularAt_iff.2 h₆, fun h => (hg.nsmul τ).vanishesAt_iff.2 (zeroAt_iff.2 ⟨h₆, fun hu => ?_⟩)⟩` and prove the remaining obligations. Establish `h₇ : ZeroAt x (b : X.functionField)` using `zeroAt_iff.2 ⟨h₄, hb.mem_supp_iff.1 h⟩`. Conclude with `(zeroAt_iff.1 ((zeroAt_pow h₇ (Nat.mul_pos hm hτ)).mul h₅)).2 (key ▸ unitAt_pow hu _)`.
-/
theorem local_sec (hx : IsIntegrallyClosed (X.presheaf.stalk x)) {Δ B Λ : CartierDiv X} {a m n τ : ℕ} (ha : 0 < a)
    (hm : 0 < m) (hn : 0 < n) (hτ : 0 < τ) (e : a • Δ + m • B = (n * a) • Λ) (hB : B.Eff)
    (hf : (τ • Δ).RegularAt x (f ^ n)) : (τ • Λ).RegularAt x f ∧ (x ∈ B.supp → (τ • Λ).VanishesAt x f) := by
  obtain ⟨d, hd⟩ := Δ.exists_isEqn x
  obtain ⟨b, hb⟩ := B.exists_isEqn x
  obtain ⟨g, hg⟩ := Λ.exists_isEqn x
  have h₁ := (hd.nsmul a).add (hb.nsmul m)
  rw [e] at h₁
  have h₂ := (h₁.iff_unitAt.1 (hg.nsmul _)).regAt
  have h₃ := (hd.nsmul τ).regularAt_iff.1 hf
  have h₄ := CartierDiv.eff_iff.1 hB x b hb
  have h₅ := (regAt_pow h₃ a).mul (regAt_pow h₂ τ)
  have key : (f * (g ^ τ : X.functionFieldˣ)) ^ (n * a) = (b : X.functionField) ^ (m * τ) *
      ((f ^ n * (d ^ τ : X.functionFieldˣ)) ^ a *
        (((g ^ (n * a) : X.functionFieldˣ) : X.functionField) / (d ^ a * b ^ m : X.functionFieldˣ)) ^ τ) := by
    have := d.ne_zero
    have := b.ne_zero
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, div_pow, mul_pow, ← pow_mul]
    field_simp
    ring
  have h₆ := regAt_of_pow hx (Nat.mul_pos hn ha) (key ▸ (regAt_pow h₄ _).mul h₅)
  refine ⟨(hg.nsmul τ).regularAt_iff.2 h₆, fun h => (hg.nsmul τ).vanishesAt_iff.2 (zeroAt_iff.2 ⟨h₆, fun hu => ?_⟩)⟩
  have h₇ : ZeroAt x (b : X.functionField) := zeroAt_iff.2 ⟨h₄, hb.mem_supp_iff.1 h⟩
  exact (zeroAt_iff.1 ((zeroAt_pow h₇ (Nat.mul_pos hm hτ)).mul h₅)).2 (key ▸ unitAt_pow hu _)

end Local

/- English proof (translation)
Establish `hnum : 0 < r.num` using `Rat.num_pos.2 hr`. Establish `h : (1 : ℚ) ⊗ₜ[ℤ] (r.den • Δ + (n * r.num.natAbs) • B) = 1 ⊗ₜ ((n * r.den) • Λ)`. Establish `h₁` using `congrArg (((n : ℚ) * r.den) • ·) (eq_sub_iff_add_eq.1 e)`. Establish `h₂ : (n : ℚ) * r.den * r = (n * r.num.natAbs : ℕ)`. Rewrite using `[mul_assoc, Rat.den_mul_eq_num, Nat.cast_mul, ← Int.cast_natCast (R := ℚ) r.num.natAbs, Int.natAbs_of_nonneg hnum.le]`.

Establish `h₃ : (n : ℚ) * r.den * (n : ℚ)⁻¹ = r.den`. Establish `: (n : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 hn.ne'`. Clear the denominators using the available nonvanishing facts. Simplify using `only [smul_add, TensorProduct.smul_tmul', smul_eq_mul, h₂, h₃] at h₁`. Simplify using `only [TensorProduct.tmul_add, ← natCast_zsmul, ← TensorProduct.smul_tmul, zsmul_eq_mul, Int.cast_natCast]`.

Simplify using `using h₁`. Take `⟨q, hq, h⟩` from `one_tmul_eq_iff.1 h`. Use `⟨q * r.den, q * (n * r.num.natAbs), Nat.mul_pos hq r.den_pos, Nat.mul_pos hq (Nat.mul_pos hn (Int.natAbs_pos.2 hnum.ne')), ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, mul_smul q, ← smul_add, h, smul_smul, mul_left_comm]`.
-/
theorem clear_den {F : Type} [Field F] {Y : Var F} {Δ B Λ : Y.Dv} {n : ℕ} (hn : 0 < n) {r : ℚ} (hr : 0 < r)
    (e : ((n : ℚ)⁻¹ ⊗ₜ[ℤ] Δ : ℚ ⊗[ℤ] Y.Dv) = 1 ⊗ₜ Λ - r ⊗ₜ B) :
    ∃ a m : ℕ, 0 < a ∧ 0 < m ∧ a • Δ + m • B = (n * a) • Λ := by
  have hnum : 0 < r.num := Rat.num_pos.2 hr
  have h : (1 : ℚ) ⊗ₜ[ℤ] (r.den • Δ + (n * r.num.natAbs) • B) = 1 ⊗ₜ ((n * r.den) • Λ) := by
    have h₁ := congrArg (((n : ℚ) * r.den) • ·) (eq_sub_iff_add_eq.1 e)
    have h₂ : (n : ℚ) * r.den * r = (n * r.num.natAbs : ℕ) := by
      rw [mul_assoc, Rat.den_mul_eq_num, Nat.cast_mul, ← Int.cast_natCast (R := ℚ) r.num.natAbs,
        Int.natAbs_of_nonneg hnum.le]
    have h₃ : (n : ℚ) * r.den * (n : ℚ)⁻¹ = r.den := by
      have : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
      field_simp
    simp only [smul_add, TensorProduct.smul_tmul', smul_eq_mul, h₂, h₃] at h₁
    simp only [TensorProduct.tmul_add, ← natCast_zsmul, ← TensorProduct.smul_tmul, zsmul_eq_mul, Int.cast_natCast]
    simpa using h₁
  obtain ⟨q, hq, h⟩ := one_tmul_eq_iff.1 h
  refine ⟨q * r.den, q * (n * r.num.natAbs), Nat.mul_pos hq r.den_pos,
    Nat.mul_pos hq (Nat.mul_pos hn (Int.natAbs_pos.2 hnum.ne')), ?_⟩
  rw [mul_smul, mul_smul q, ← smul_add, h, smul_smul, mul_left_comm]

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A}

open Classical in

/- English proof (translation)
Establish `e (σ : D.host.E →+* ℂ) (k : ℕ) : letterOf S.Dw (.inl (σ, k)) = some z ↔ σ = z.1 ∧ k = z.2`. Take `⟨ρ, a⟩` from `z`. Simplify using `only [letterOf]`. Prove the components needed by the constructor for the conclusion. Introduce `h split_ifs at h with hk`.

Take `⟨rfl, h2⟩` from `Sigma.mk.inj_iff.1 (Option.some.inj h)`. Conclude with `⟨rfl, by simpa [Fin.ext_iff] using h2⟩`. Introduce and unpack `⟨rfl, rfl⟩`. Rewrite using `[dif_pos a.isLt]`. Simplify using `only [rootEx, rootSym]`.

Apply the tactic sequence `split_ifs <;> rw [expo_single] <;> simp_all`.
-/
theorem rootEx_apply (τ : D.host.E →+* ℂ) (i : ℕ) (z : Letter S.Dw) :
    rootEx S.Dw τ i z = if i < S.Dw.p then (if τ = z.1 ∧ i = z.2 then 1 else 0)
      else -(if conjEmb τ = z.1 ∧ S.Dw.p + S.Dw.q - 1 - i = z.2 then 1 else 0) := by
  have e (σ : D.host.E →+* ℂ) (k : ℕ) : letterOf S.Dw (.inl (σ, k)) = some z ↔ σ = z.1 ∧ k = z.2 := by
    obtain ⟨ρ, a⟩ := z
    simp only [letterOf]
    constructor
    · intro h
      split_ifs at h with hk
      obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 (Option.some.inj h)
      exact ⟨rfl, by simpa [Fin.ext_iff] using h2⟩
    · rintro ⟨rfl, rfl⟩
      rw [dif_pos a.isLt]
  simp only [rootEx, rootSym]
  split_ifs <;> rw [expo_single] <;> simp_all

/- English proof (translation)
Take `⟨τ, a⟩` from `z`. Establish `hN` using `S.rank_eq`. Establish `ha` using `a.isLt`. Express the relevant statement in the definitionally equal form `_ = (wtOf S.Dw u 0).1 (τ, a)`. Simplify using `only [rootExp, rootEx_apply, ← L.ψ_val]`.

Distinguish the cases in `h : τ (A.H.rt : D.host.E) = A.H.rt0`. Establish `hp : (a : ℕ) < S.Dw.p` using `by simpa [Datum.mult, h] using ha`. Rewrite using `[wtOf_big u 0 ⟨τ, h⟩ a hp, Finset.sum_eq_single (L.ψ.symm ⟨τ, h⟩, ⟨a, by omega⟩) ?_ (by simp)]`. Simplify using `[hp]`. Introduce and unpack `⟨t, i⟩ _ hne dsimp only split_ifs with h1 h2 h3`.

Conclude with `absurd (Prod.ext (L.ψ.eq_symm_apply.2 (Subtype.ext h2.1)) (Fin.ext h2.2)) hne`. Simplify using the standard rewrite rules. Conclude with `absurd (h3.1 ▸ h) (conj_not_mem (L.ψ t))`. Simplify using the standard rewrite rules. Establish `hq : (a : ℕ) < S.Dw.q` using `by simpa [Datum.mult, h] using ha`.

Establish `e` using `wtOf_small u 0 ⟨conjEmb τ, conj_mem h⟩ a hq`. Simplify using `only [conjEmb_conjEmb] at e`. Rewrite using `[e, Finset.sum_eq_single (L.ψ.symm ⟨conjEmb τ, conj_mem h⟩, ⟨S.Dw.p + (S.Dw.q - 1 - a), by omega⟩) ?_ (by simp)]`. Establish `e₁ : S.Dw.p + S.Dw.q - 1 - (S.Dw.p + (S.Dw.q - 1 - (a : ℕ))) = a` using `by omega`. Simplify using `[e₁, conjEmb_conjEmb]`.

Introduce and unpack `⟨t, i⟩ _ hne dsimp only split_ifs with h1 h2 h3`. Conclude with `absurd (h2.1 ▸ (L.ψ t).2) h`. Simplify using the standard rewrite rules. Use `absurd (Prod.ext (L.ψ.eq_symm_apply.2 (Subtype.ext ?_)) (Fin.ext ?_)) hne` and prove the remaining obligations. Conclude with `(conjEmb_conjEmb _).symm.trans (congrArg conjEmb h3.1)`.

Use `i.isLt` as an intermediate fact. Use `h3.2` as an intermediate fact. Simplify using `only`. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules.
-/
theorem sum_rootExp (L : CmList A) (u : AllWt.Weight S.Dw) (z : Letter S.Dw) :
    ∑ x : DV.Rt D.what₂.Tau N, u (L.ψ x.1) (Fin.cast S.rank_eq.symm x.2) * rootExp S x z = exOf S.Dw u 0 (some z) := by
  classical
  obtain ⟨τ, a⟩ := z
  have hN := S.rank_eq
  have ha := a.isLt
  change _ = (wtOf S.Dw u 0).1 (τ, a)
  simp only [rootExp, rootEx_apply, ← L.ψ_val]
  by_cases h : τ (A.H.rt : D.host.E) = A.H.rt0
  · have hp : (a : ℕ) < S.Dw.p := by simpa [Datum.mult, h] using ha
    rw [wtOf_big u 0 ⟨τ, h⟩ a hp, Finset.sum_eq_single (L.ψ.symm ⟨τ, h⟩, ⟨a, by omega⟩) ?_ (by simp)]
    · simp [hp]
    · rintro ⟨t, i⟩ _ hne
      dsimp only
      split_ifs with h1 h2 h3
      · exact absurd (Prod.ext (L.ψ.eq_symm_apply.2 (Subtype.ext h2.1)) (Fin.ext h2.2)) hne
      · simp
      · exact absurd (h3.1 ▸ h) (conj_not_mem (L.ψ t))
      · simp
  · have hq : (a : ℕ) < S.Dw.q := by simpa [Datum.mult, h] using ha
    have e := wtOf_small u 0 ⟨conjEmb τ, conj_mem h⟩ a hq
    simp only [conjEmb_conjEmb] at e
    rw [e, Finset.sum_eq_single (L.ψ.symm ⟨conjEmb τ, conj_mem h⟩, ⟨S.Dw.p + (S.Dw.q - 1 - a), by omega⟩) ?_ (by simp)]
    · have e₁ : S.Dw.p + S.Dw.q - 1 - (S.Dw.p + (S.Dw.q - 1 - (a : ℕ))) = a := by omega
      simp [e₁, conjEmb_conjEmb]
    · rintro ⟨t, i⟩ _ hne
      dsimp only
      split_ifs with h1 h2 h3
      · exact absurd (h2.1 ▸ (L.ψ t).2) h
      · simp
      · refine absurd (Prod.ext (L.ψ.eq_symm_apply.2 (Subtype.ext ?_)) (Fin.ext ?_)) hne
        · exact (conjEmb_conjEmb _).symm.trans (congrArg conjEmb h3.1)
        · have := i.isLt
          have := h3.2
          dsimp only
          omega
      · simp

variable {s : FinalTheorems S κ} (Φ : s.Flag) (k : s.Comp)

/- English proof (translation)
Establish `e (c : ℤ) (Δ : (Φ.C k).Y.Dv) : (c : ℚ) ⊗ₜ[ℤ] Δ = 1 ⊗ₜ (c • Δ)`. Rewrite using `[← TensorProduct.smul_tmul, zsmul_eq_mul, mul_one]`. Rewrite using `[← GlobalTheory.ShFam.DeKeyTrue.divOf_neg_exOf]`. Simplify using `only [qL, e, ← TensorProduct.tmul_sum, ← TensorProduct.tmul_neg, ← sum_rootExp L u]`. Use `congr 1`.

Simplify using `only [divOf, Finset.smul_sum, smul_smul, neg_smul, Finset.sum_smul, Finset.sum_neg_distrib]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem qL_int (L : CmList A) (u : AllWt.Weight S.Dw) :
    qL Φ k (fun t i => (u (L.ψ t) (Fin.cast S.rank_eq.symm i) : ℚ)) = 1 ⊗ₜ (Φ.C k).Lw u := by
  have e (c : ℤ) (Δ : (Φ.C k).Y.Dv) : (c : ℚ) ⊗ₜ[ℤ] Δ = 1 ⊗ₜ (c • Δ) := by
    rw [← TensorProduct.smul_tmul, zsmul_eq_mul, mul_one]
  rw [← GlobalTheory.ShFam.DeKeyTrue.divOf_neg_exOf]
  simp only [qL, e, ← TensorProduct.tmul_sum, ← TensorProduct.tmul_neg, ← sum_rootExp L u]
  congr 1
  simp only [divOf, Finset.smul_sum, smul_smul, neg_smul, Finset.sum_smul, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]

/- English proof (translation)
Proceed by induction on `τ with`. Consider the case `zero => rw [zero_nsmul, zero_nsmul, FlagCpt.Lw_zero]`. Consider the case `succ n ih => rw [succ_nsmul, succ_nsmul, FlagCpt.Lw_add, ih]`.
-/
theorem Lw_nsmul (u : AllWt.Weight S.Dw) (τ : ℕ) : (Φ.C k).Lw (τ • u) = τ • (Φ.C k).Lw u := by
  induction τ with
  | zero => rw [zero_nsmul, zero_nsmul, FlagCpt.Lw_zero]
  | succ n ih => rw [succ_nsmul, succ_nsmul, FlagCpt.Lw_add, ih]

/- English proof (translation)
Introduce `D A N j S κ s Φ L x P B u r hr k τ hτ f hf`. Establish `e : wtR L u = fun t i => ((u (L.ψ t) (Fin.cast S.rank_eq.symm i) : ℚ) : ℝ)`. Use function extensionality and compare the values at `t i`. Simplify using `[wtR]`. Rewrite `hf` using `[e, mbarOf_cast P B _ hr]`.

Establish `h` using `P.qDiv_mbarQ k B (fun t i => (u (L.ψ t) (Fin.cast S.rank_eq.symm i) : ℚ)) r`. Rewrite `h` using `[qL_int]`. Take `⟨a, m, ha, hm, h⟩` from `clear_den (PNat.pos _) hr h`. Establish `hl (y : (Φ.C k).Y.X)` using `local_sec (x := y) (have := (Φ.C k).Y.isNormalScheme; inferInstance) ha hm (PNat.pos _) hτ h (P.eff_bd k) (Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 hf y)`. Rewrite using `[IsCuspSec, Lw_nsmul]`.

Conclude with `⟨Var.mem_riemannRochSpace_iff_regularAt_everywhere.2 fun y => (hl y).1, fun y hy => (hl y).2 ((P.mem_supp_bd k y).2 (((Φ.C k).bd_supp y).1 hy))⟩`.
-/
theorem isCuspSec_of_mem_secs : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (L : CmList A) (x : ToroidalCompactificationData s) (P : Mean4O.PolOf x Φ) (B : ℝ) (u : AllWt.Weight S.Dw) (r : ℚ), 0 < r → ∀ (k : s.Comp) (τ : ℕ), 1 ≤ τ → ∀ f ∈ (mbarOf P B (wtR L u) r k).secs τ, IsCuspSec Φ k (τ • u) f := by
  intro D A N j S κ s Φ L x P B u r hr k τ hτ f hf
  have e : wtR L u = fun t i => ((u (L.ψ t) (Fin.cast S.rank_eq.symm i) : ℚ) : ℝ) := by
    funext t i; simp [wtR]
  rw [e, mbarOf_cast P B _ hr] at hf
  have h := P.qDiv_mbarQ k B (fun t i => (u (L.ψ t) (Fin.cast S.rank_eq.symm i) : ℚ)) r
  rw [qL_int] at h
  obtain ⟨a, m, ha, hm, h⟩ := clear_den (PNat.pos _) hr h
  have hl (y : (Φ.C k).Y.X) := local_sec (x := y) (have := (Φ.C k).Y.isNormalScheme; inferInstance) ha hm (PNat.pos _) hτ h
    (P.eff_bd k) (Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 hf y)
  rw [IsCuspSec, Lw_nsmul]
  exact ⟨Var.mem_riemannRochSpace_iff_regularAt_everywhere.2 fun y => (hl y).1, fun y hy => (hl y).2 ((P.mem_supp_bd k y).2 (((Φ.C k).bd_supp y).1 hy))⟩

end GlobalTheory.CovHt.Link.ApproxSec

end

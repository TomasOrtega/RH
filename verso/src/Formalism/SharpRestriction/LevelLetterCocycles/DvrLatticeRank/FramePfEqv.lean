import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfNat
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfB

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n}

section Ring

/- English proof (translation)
Introduce `δ hδ`. Establish `h1` using `congrArg (W.γA δ) h`. Rewrite `h1` using `[map_mul, ha δ hδ, hb δ hδ]`. Apply `W.EE_inj` to reduce the goal to its premises. Apply `hbu.mul_left_cancel` to reduce the goal to its premises.

Rewrite using `[← map_mul, ← map_mul, ← h1, ← h]`.
-/
theorem framepf_Δ_cancel {a b u : LetA O n} (ha : a ∈ W.AΔ) (hb : b ∈ W.AΔ)
    (hbu : IsUnit (algebraMap (LetA O n) W.EE b)) (h : a = b * u) : u ∈ W.AΔ := by
  intro δ hδ
  have h1 := congrArg (W.γA δ) h
  rw [map_mul, ha δ hδ, hb δ hδ] at h1
  apply W.EE_inj
  apply hbu.mul_left_cancel
  rw [← map_mul, ← map_mul, ← h1, ← h]

/- English proof (translation)
Introduce `δ hδ`. Rewrite using `[gradNPf_γA_comm, ha δ hδ]`.
-/
theorem framepf_γA_Δ (g : W.Gam) {a : LetA O n} (ha : a ∈ W.AΔ) : W.γA g a ∈ W.AΔ := by
  intro δ hδ
  rw [gradNPf_γA_comm, ha δ hδ]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show W.γ₀ g (W.γ₀ g⁻¹ (a i)) = a i`. Rewrite using `[← AlgHom.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgHom.one_apply]`.
-/
theorem framepf_γA_inv (g : W.Gam) (a : LetA O n) : W.γA g (W.γA g⁻¹ a) = a := by
  funext i
  show W.γ₀ g (W.γ₀ g⁻¹ (a i)) = a i
  rw [← AlgHom.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgHom.one_apply]

/- English proof (translation)
Establish `hπ : ∀ g : W.Gam, ∃ a : LetA O n, W.γA g letπ = letπ * a` using `fun g => by`. Take `⟨t, ht⟩` from `Formalism.MainNotions.LiftingTheory.wmap_γAX W g 0`. Conclude with `⟨_, ht⟩`. Establish `hc : ∀ x y : LetA O n, letπ * x = letπ * y → x = y` using `fun x y h => by`. Apply `W.EE_inj` to reduce the goal to its premises.

Apply `W.EE_π.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[← map_mul, ← map_mul, h]`. Take `⟨a, ha⟩` from `hπ g`. Take `⟨a', ha'⟩` from `hπ g⁻¹`. Establish `h1 : a * W.γA g a' = 1`.

Apply `hc` to reduce the goal to its premises. Rewrite using `[← mul_assoc, ← ha, ← map_mul, ← ha', framepf_γA_inv, mul_one]`. Establish `h2 : a * W.γA g W.q = W.q * W.φA a`. Apply `hc` to reduce the goal to its premises. Rewrite using `[← mul_assoc, ← ha, ← map_mul, ← W.φA_π, ← W.φA_γA, ha, map_mul, W.φA_π, mul_assoc]`.

Use `⟨W.φA a * W.γA g a', ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← h2, mul_right_comm, h1, one_mul]`.
-/
theorem framepf_γA_q (g : W.Gam) : ∃ t : LetA O n, W.γA g W.q = W.q * t := by
  have hπ : ∀ g : W.Gam, ∃ a : LetA O n, W.γA g letπ = letπ * a := fun g => by
    obtain ⟨t, ht⟩ := Formalism.MainNotions.LiftingTheory.wmap_γAX W g 0
    exact ⟨_, ht⟩
  have hc : ∀ x y : LetA O n, letπ * x = letπ * y → x = y := fun x y h => by
    apply W.EE_inj
    apply W.EE_π.mul_left_cancel
    rw [← map_mul, ← map_mul, h]
  obtain ⟨a, ha⟩ := hπ g
  obtain ⟨a', ha'⟩ := hπ g⁻¹
  have h1 : a * W.γA g a' = 1 := by
    apply hc
    rw [← mul_assoc, ← ha, ← map_mul, ← ha', framepf_γA_inv, mul_one]
  have h2 : a * W.γA g W.q = W.q * W.φA a := by
    apply hc
    rw [← mul_assoc, ← ha, ← map_mul, ← W.φA_π, ← W.φA_γA, ha, map_mul, W.φA_π, mul_assoc]
  refine ⟨W.φA a * W.γA g a', ?_⟩
  rw [← mul_assoc, ← h2, mul_right_comm, h1, one_mul]

variable {e s' : ℕ} {π' : LetA O n} {E : ZMod n → Polynomial O}
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E)
include hR

/- English proof (translation)
Introduce `δ hδ`. Use function extensionality and compare the values at `i`. Use `show W.γ₀ δ (Polynomial.aeval (π' i) (E i)) = Polynomial.aeval (π' i) (E i)`. Rewrite using `[← Polynomial.aeval_algHom_apply]`. Conclude with `congrArg (fun p => Polynomial.aeval p (E i)) (congrFun (hR.1 δ hδ) i)`.
-/
theorem framepf_E_Δ : Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ W.AΔ := by
  intro δ hδ
  funext i
  show W.γ₀ δ (Polynomial.aeval (π' i) (E i)) = Polynomial.aeval (π' i) (E i)
  rw [← Polynomial.aeval_algHom_apply]
  exact congrArg (fun p => Polynomial.aeval p (E i)) (congrFun (hR.1 δ hδ) i)

/- English proof (translation)
Take `⟨w, hw⟩` from `hR.2.2.2.2.1`. Establish `h` using `Formalism.MainNotions.LiftingTheory.liftb_Q_unit W`. Rewrite `h` using `[Formalism.MainNotions.LiftingTheory.wmap_Q_one W hs, hw, map_mul]`. Conclude with `isUnit_of_mul_isUnit_right h`.
-/
theorem framepf_E_unit (hs : W.s = 1) :
    IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  have h := Formalism.MainNotions.LiftingTheory.liftb_Q_unit W
  rw [Formalism.MainNotions.LiftingTheory.wmap_Q_one W hs, hw, map_mul] at h
  exact isUnit_of_mul_isUnit_right h

/- English proof (translation)
Take `⟨w, hw⟩` from `hR.2.2.1`. Rewrite using `[hw, map_mul, map_pow]`. Conclude with `(w.isUnit.map _).mul (W.EE_π.pow _)`.
-/
theorem framepf_π_unit : IsUnit (algebraMap (LetA O n) W.EE π') := by
  obtain ⟨w, hw⟩ := hR.2.2.1
  rw [hw, map_mul, map_pow]
  exact (w.isUnit.map _).mul (W.EE_π.pow _)

/- English proof (translation)
Take `⟨w, hw⟩` from `hR.2.2.2.2.2.1`. Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_le hM`. Establish `he : W.φA π' ^ M = π' ^ M * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ (4 * h') * ((w : LetA O n) ^ M * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ d)`. Rewrite using `[hw, mul_pow, mul_pow, ← pow_mul, hd, pow_add]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨_, framepf_Δ_cancel (W.AΔ.pow_mem (fun δ hδ => ?_) M) (W.AΔ.mul_mem (W.AΔ.pow_mem hR.1 _) (W.AΔ.pow_mem (framepf_E_Δ hR) _)) ?_ he, he⟩` and prove the remaining obligations. Rewrite using `[← W.φA_γA, hR.1 δ hδ]`. Rewrite using `[map_mul, map_pow, map_pow]`. Conclude with `((framepf_π_unit hR).pow _).mul ((framepf_E_unit hR hs).pow _)`.
-/
theorem framepf_φπ (hs : W.s = 1) (h' M : ℕ) (hM : 4 * h' ≤ s' * M) :
    ∃ u ∈ W.AΔ, W.φA π' ^ M = π' ^ M * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ (4 * h') * u := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.2.1
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hM
  have he : W.φA π' ^ M = π' ^ M * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ (4 * h') *
      ((w : LetA O n) ^ M * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ d) := by
    rw [hw, mul_pow, mul_pow, ← pow_mul, hd, pow_add]
    ring
  refine ⟨_, framepf_Δ_cancel (W.AΔ.pow_mem (fun δ hδ => ?_) M)
    (W.AΔ.mul_mem (W.AΔ.pow_mem hR.1 _) (W.AΔ.pow_mem (framepf_E_Δ hR) _)) ?_ he, he⟩
  · rw [← W.φA_γA, hR.1 δ hδ]
  · rw [map_mul, map_pow, map_pow]
    exact ((framepf_π_unit hR).pow _).mul ((framepf_E_unit hR hs).pow _)

/- English proof (translation)
Take `⟨w, hw⟩` from `hR.2.2.2.2.2.2.1`. Establish `he : W.γA W.gam π' = π' * (1 + w * Formalism.MainNotions.DeltaInvariantLattices.Eat E π')`. Take the linear combination `hw`. Conclude with `⟨_, framepf_Δ_cancel (framepf_γA_Δ _ hR.1) hR.1 (framepf_π_unit hR) he, he⟩`.
-/
theorem framepf_γπ : ∃ f ∈ W.AΔ, W.γA W.gam π' = π' * f := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.2.2.1
  have he : W.γA W.gam π' = π' * (1 + w * Formalism.MainNotions.DeltaInvariantLattices.Eat E π') := by
    linear_combination hw
  exact ⟨_, framepf_Δ_cancel (framepf_γA_Δ _ hR.1) hR.1 (framepf_π_unit hR) he, he⟩

/- English proof (translation)
Take `⟨w, hw⟩` from `hR.2.2.2.2.1`. Take `⟨t, ht⟩` from `framepf_γA_q (W := W) g`. Establish `hE : Formalism.MainNotions.DeltaInvariantLattices.Eat E π' = ((w⁻¹ : (LetA O n)ˣ) : LetA O n) * W.q`. Rewrite using `[hw, Units.inv_mul_cancel_left]`. Establish `he : W.γA g (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') = Formalism.MainNotions.DeltaInvariantLattices.Eat E π' * (W.γA g ((w⁻¹ : (LetA O n)ˣ) : LetA O n) * w * t)` using `by conv_lhs => rw [hE, map_mul, ht, hw]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨_, framepf_Δ_cancel (framepf_γA_Δ _ (framepf_E_Δ hR)) (framepf_E_Δ hR) (framepf_E_unit hR hs) he, he⟩`.
-/
theorem framepf_γE (hs : W.s = 1) (g : W.Gam) :
    ∃ t ∈ W.AΔ, W.γA g (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') = Formalism.MainNotions.DeltaInvariantLattices.Eat E π' * t := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  obtain ⟨t, ht⟩ := framepf_γA_q (W := W) g
  have hE : Formalism.MainNotions.DeltaInvariantLattices.Eat E π' = ((w⁻¹ : (LetA O n)ˣ) : LetA O n) * W.q := by
    rw [hw, Units.inv_mul_cancel_left]
  have he : W.γA g (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') =
      Formalism.MainNotions.DeltaInvariantLattices.Eat E π' * (W.γA g ((w⁻¹ : (LetA O n)ˣ) : LetA O n) * w * t) := by
    conv_lhs => rw [hE, map_mul, ht, hw]
    ring
  exact ⟨_, framepf_Δ_cancel (framepf_γA_Δ _ (framepf_E_Δ hR)) (framepf_E_Δ hR)
    (framepf_E_unit hR hs) he, he⟩

/- English proof (translation)
Take `⟨t, htΔ, ht⟩` from `framepf_γE hR hs g⁻¹`. Use `⟨W.γA g t, framepf_γA_Δ g htΔ, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul, ← ht, framepf_γA_inv]`.
-/
theorem framepf_γE' (hs : W.s = 1) (g : W.Gam) :
    ∃ t ∈ W.AΔ, Formalism.MainNotions.DeltaInvariantLattices.Eat E π' = W.γA g (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') * t := by
  obtain ⟨t, htΔ, ht⟩ := framepf_γE hR hs g⁻¹
  refine ⟨W.γA g t, framepf_γA_Δ g htΔ, ?_⟩
  rw [← map_mul, ← ht, framepf_γA_inv]

end Ring

section Stab

variable {T : LocLat G Qp LL O} (π' Eπ : LetA O n) (h' M : ℕ) (c : ZMod n)

/- English proof (translation)
Take `⟨⟨h1, h2⟩, h3⟩` from `hp`. Use `⟨⟨(Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1))).smul_mem a h1, (mem_DelS W T _).2 fun δ hδ => ?_⟩, (mem_letS W T c _).2 ?_⟩` and prove the remaining obligations. Rewrite using `[gradNPf_γD_smul, ha δ hδ, (mem_DelS W T p).1 h2 δ hδ]`. Rewrite using `[smul_comm, (mem_letS W T c p).1 h3]`.
-/
theorem framepf_PcS_smul {a : LetA O n} (ha : a ∈ W.AΔ) {p : W.DD T} (hp : p ∈ PcS W T c) :
    a • p ∈ PcS W T c := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp
  refine ⟨⟨(Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1))).smul_mem a h1, (mem_DelS W T _).2 fun δ hδ => ?_⟩,
    (mem_letS W T c _).2 ?_⟩
  · rw [gradNPf_γD_smul, ha δ hδ, (mem_DelS W T p).1 h2 δ hδ]
  · rw [smul_comm, (mem_letS W T c p).1 h3]

/- English proof (translation)
Take `⟨p, hp, rfl⟩` from `hy`. Conclude with `⟨a • p, framepf_PcS_smul c ha hp, smul_comm _ a p⟩`.
-/
theorem framepf_JP_smul {a : LetA O n} (ha : a ∈ W.AΔ) {y : W.DD T} (hy : y ∈ JP W T π' Eπ h' M c) :
    a • y ∈ JP W T π' Eπ h' M c := by
  obtain ⟨p, hp, rfl⟩ := hy
  exact ⟨a • p, framepf_PcS_smul c ha hp, smul_comm _ a p⟩

/- English proof (translation)
Take `⟨t, rfl⟩` from `hx`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul b s`. Use `⟨((⟨a, ha⟩ : ↥W.AΔ) * b) ⊗ₜ s, ?_⟩` and prove the remaining obligations.

Use `show algebraMap (LetA O n) W.EE ((letE c : LetA O n) * (a * b)) ⊗ₜ[O] (s : LcQ W T π' c) = (algebraMap (LetA O n) W.EE a * algebraMap (LetA O n) W.EE ((letE c : LetA O n) * b)) ⊗ₜ[O] (s : LcQ W T π' c)`. Rewrite using `[← map_mul, mul_left_comm]`. Consider the case `add x y hx hy => rw [map_add, map_add]`. Conclude with `Submodule.add_mem _ hx hy`.
-/
theorem framepf_toLA_smul {a : LetA O n} (ha : a ∈ W.AΔ) {x : LA W T π' c}
    (hx : x ∈ LinearMap.range (toLA W T π' c ⊤)) :
    smulLA W T π' c a x ∈ LinearMap.range (toLA W T π' c ⊤) := by
  obtain ⟨t, rfl⟩ := hx
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b s =>
    refine ⟨((⟨a, ha⟩ : ↥W.AΔ) * b) ⊗ₜ s, ?_⟩
    show algebraMap (LetA O n) W.EE ((letE c : LetA O n) * (a * b)) ⊗ₜ[O] (s : LcQ W T π' c) =
      (algebraMap (LetA O n) W.EE a * algebraMap (LetA O n) W.EE ((letE c : LetA O n) * b)) ⊗ₜ[O]
        (s : LcQ W T π' c)
    rw [← map_mul, mul_left_comm]
  | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy

/- English proof (translation)
Take `⟨t, ht, rfl⟩` from `hx`. Use `⟨_, framepf_toLA_smul π' c ha ht, ?_⟩` and prove the remaining obligations. Simplify using `only [framepf_smulLA_alg]`. Conclude with `smul_comm _ _ _`.
-/
theorem framepf_JLA_smul {a : LetA O n} (ha : a ∈ W.AΔ) {x : LA W T π' c}
    (hx : x ∈ JLA W T π' Eπ h' M c) : smulLA W T π' c a x ∈ JLA W T π' Eπ h' M c := by
  obtain ⟨t, ht, rfl⟩ := hx
  refine ⟨_, framepf_toLA_smul π' c ha ht, ?_⟩
  simp only [framepf_smulLA_alg]
  exact smul_comm _ _ _

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul e ℓ => show W.γE W.gamK (algebraMap (LetA O n) W.EE a * e) ⊗ₜ[O] ℓ = (algebraMap (LetA O n) W.EE (W.γA W.gamK a) * W.γE W.gamK e) ⊗ₜ[O] ℓ`. Rewrite using `[map_mul, W.γE_ext]`. Both sides reduce to the same expression.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem framepf_γLA_smulLA (a : LetA O n) (x : LA W T π' c) :
    γLA W T π' c (smulLA W T π' c a x) = smulLA W T π' c (W.γA W.gamK a) (γLA W T π' c x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e ℓ =>
    show W.γE W.gamK (algebraMap (LetA O n) W.EE a * e) ⊗ₜ[O] ℓ =
      (algebraMap (LetA O n) W.EE (W.γA W.gamK a) * W.γE W.gamK e) ⊗ₜ[O] ℓ
    rw [map_mul, W.γE_ext]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Take `⟨t, rfl⟩` from `hx`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul b s`. Use `⟨(⟨W.γA W.gamK b, framepf_γA_Δ _ b.2⟩ : ↥W.AΔ) ⊗ₜ s, ?_⟩` and prove the remaining obligations.

Use `show algebraMap (LetA O n) W.EE ((letE c : LetA O n) * W.γA W.gamK b) ⊗ₜ[O] (s : LcQ W T π' c) = W.γE W.gamK (algebraMap (LetA O n) W.EE ((letE c : LetA O n) * b)) ⊗ₜ[O] (s : LcQ W T π' c)`. Rewrite using `[W.γE_ext, ← Formalism.MainNotions.LiftingTheory.wmap_γA_letE W W.gamK c, ← map_mul, Formalism.MainNotions.LiftingTheory.wmap_γA_letE]`. Both sides reduce to the same expression. Consider the case `add x y hx hy => rw [map_add, map_add]`. Conclude with `Submodule.add_mem _ hx hy`.
-/
theorem framepf_γLA_toLA {x : LA W T π' c} (hx : x ∈ LinearMap.range (toLA W T π' c ⊤)) :
    γLA W T π' c x ∈ LinearMap.range (toLA W T π' c ⊤) := by
  obtain ⟨t, rfl⟩ := hx
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b s =>
    refine ⟨(⟨W.γA W.gamK b, framepf_γA_Δ _ b.2⟩ : ↥W.AΔ) ⊗ₜ s, ?_⟩
    show algebraMap (LetA O n) W.EE ((letE c : LetA O n) * W.γA W.gamK b) ⊗ₜ[O] (s : LcQ W T π' c) =
      W.γE W.gamK (algebraMap (LetA O n) W.EE ((letE c : LetA O n) * b)) ⊗ₜ[O] (s : LcQ W T π' c)
    rw [W.γE_ext, ← Formalism.MainNotions.LiftingTheory.wmap_γA_letE W W.gamK c, ← map_mul, Formalism.MainNotions.LiftingTheory.wmap_γA_letE]
    rfl
  | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy

/- English proof (translation)
Take `⟨⟨h1, h2⟩, h3⟩` from `hp`. Use `⟨⟨?_, gradNPf_DelS_γ W T g h2⟩, gradNPf_letS_γ W T g c h3⟩` and prove the remaining obligations. Use `show W.γD T g p ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1))`. Establish `h1' : p ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1))` using `h1`. Use `clear h1 h2 h3`.

Proceed by induction on `h1' using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨_, ⟨z, hz, rfl⟩, rfl⟩` from `hx`. Rewrite using `[← W.φγ_comm]`. Conclude with `Submodule.subset_span ⟨_, ⟨W.γD T g z, W.N_Γ T g z hz, (γD_letE W T g _ z).symm⟩, rfl⟩`.

Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul s x _ hx => rw [gradNPf_γD_smul]`.

Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem framepf_γD_PcS (g : W.Gam) {p : W.DD T} (hp : p ∈ PcS W T c) : W.γD T g p ∈ PcS W T c := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp
  refine ⟨⟨?_, gradNPf_DelS_γ W T g h2⟩, gradNPf_letS_γ W T g c h3⟩
  show W.γD T g p ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1))
  have h1' : p ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1)) := h1
  clear h1 h2 h3
  induction h1' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hx
    rw [← W.φγ_comm]
    exact Submodule.subset_span ⟨_, ⟨W.γD T g z, W.N_Γ T g z hz, (γD_letE W T g _ z).symm⟩, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul s x _ hx => rw [gradNPf_γD_smul]; exact Submodule.smul_mem _ _ hx

variable {f t t' : LetA O n} (hfΔ : f ∈ W.AΔ) (hf : W.γA W.gamK π' = π' * f)
    (htΔ : t ∈ W.AΔ) (ht : W.γA W.gamK Eπ = Eπ * t)
    (ht'Δ : t' ∈ W.AΔ) (ht' : Eπ = W.γA W.gamK Eπ * t')

include hf ht in
/- English proof (translation)
Rewrite using `[map_mul, map_pow, map_pow, hf, ht]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem framepf_γ_JJ : W.γA W.gamK (π' ^ M * Eπ ^ (3 * h')) =
    π' ^ M * Eπ ^ (3 * h') * (f ^ M * t ^ (3 * h')) := by
  rw [map_mul, map_pow, map_pow, hf, ht]
  ring

include hfΔ hf htΔ ht in
/- English proof (translation)
Take `⟨p, hp, rfl⟩` from `hy`. Use `⟨(f ^ M * t ^ (3 * h')) • W.γD T W.gamK p, framepf_PcS_smul c (W.AΔ.mul_mem (W.AΔ.pow_mem hfΔ _) (W.AΔ.pow_mem htΔ _)) (framepf_γD_PcS c _ hp), ?_⟩` and prove the remaining obligations. Use `show (π' ^ M * Eπ ^ (3 * h')) • _ = W.γD T W.gamK ((π' ^ M * Eπ ^ (3 * h')) • p)`. Rewrite using `[gradNPf_γD_smul, framepf_γ_JJ π' Eπ h' M hf ht, mul_smul (π' ^ M * Eπ ^ (3 * h'))]`. Both sides reduce to the same expression.
-/
theorem framepf_γ_JP {y : W.DD T} (hy : y ∈ JP W T π' Eπ h' M c) :
    W.γD T W.gamK y ∈ JP W T π' Eπ h' M c := by
  obtain ⟨p, hp, rfl⟩ := hy
  refine ⟨(f ^ M * t ^ (3 * h')) • W.γD T W.gamK p, framepf_PcS_smul c
    (W.AΔ.mul_mem (W.AΔ.pow_mem hfΔ _) (W.AΔ.pow_mem htΔ _)) (framepf_γD_PcS c _ hp), ?_⟩
  show (π' ^ M * Eπ ^ (3 * h')) • _ = W.γD T W.gamK ((π' ^ M * Eπ ^ (3 * h')) • p)
  rw [gradNPf_γD_smul, framepf_γ_JJ π' Eπ h' M hf ht, mul_smul (π' ^ M * Eπ ^ (3 * h'))]
  rfl

include hfΔ hf htΔ ht in
/- English proof (translation)
Take `⟨z, hz, rfl⟩` from `hx`. Use `⟨_, framepf_toLA_smul π' c (W.AΔ.mul_mem (W.AΔ.pow_mem hfΔ M) (W.AΔ.pow_mem htΔ (3 * h'))) (framepf_γLA_toLA π' c hz), ?_⟩` and prove the remaining obligations. Rewrite using `[framepf_γLA_smulLA, framepf_γ_JJ π' Eπ h' M hf ht]`. Simplify using `only [framepf_smulLA_alg]`. Rewrite using `[smul_smul, ← map_mul]`.
-/
theorem framepf_γ_JLA {x : LA W T π' c} (hx : x ∈ JLA W T π' Eπ h' M c) :
    γLA W T π' c x ∈ JLA W T π' Eπ h' M c := by
  obtain ⟨z, hz, rfl⟩ := hx
  refine ⟨_, framepf_toLA_smul π' c
    (W.AΔ.mul_mem (W.AΔ.pow_mem hfΔ M) (W.AΔ.pow_mem htΔ (3 * h'))) (framepf_γLA_toLA π' c hz), ?_⟩
  rw [framepf_γLA_smulLA, framepf_γ_JJ π' Eπ h' M hf ht]
  simp only [framepf_smulLA_alg]
  rw [smul_smul, ← map_mul]

include ht'Δ ht' in
/- English proof (translation)
Establish `h` using `framepf_toLA_smul π' c (W.AΔ.pow_mem ht'Δ h') (framepf_γLA_toLA π' c hx)`. Rewrite `h` using `[framepf_γLA_smulLA]`. Use `show smulLA W T π' c _ _ ∈ LinearMap.range (toLA W T π' c ⊤)`. Simplify using `only [framepf_smulLA_alg] at h ⊢`. Rewrite `h` using `[smul_smul, ← map_mul, map_pow (W.γA W.gamK), ← mul_pow, mul_comm, ← ht']`.

Conclude with `h`.
-/
theorem framepf_γ_LamLA {x : LA W T π' c} (hx : x ∈ LamLA W T π' Eπ h' c ⊤) :
    γLA W T π' c x ∈ LamLA W T π' Eπ h' c ⊤ := by
  have h := framepf_toLA_smul π' c (W.AΔ.pow_mem ht'Δ h') (framepf_γLA_toLA π' c hx)
  rw [framepf_γLA_smulLA] at h
  show smulLA W T π' c _ _ ∈ LinearMap.range (toLA W T π' c ⊤)
  simp only [framepf_smulLA_alg] at h ⊢
  rw [smul_smul, ← map_mul, map_pow (W.γA W.gamK), ← mul_pow, mul_comm, ← ht'] at h
  exact h

include ht'Δ ht' in

/- English proof (translation)
Take `⟨z, hz⟩` from `hx`. Establish `key : ∀ z : ↥W.AΔ ⊗[O] ↥(⊤ : Submodule O (LcQ W T π' c)), ∃ p ∈ PcS W T c, W.γD T W.gamK (Ψ (toLA W T π' c ⊤ z)) - Ψ (γLA W T π' c (toLA W T π' c ⊤ z)) = (π' ^ M * Eπ ^ (4 * h')) • p`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, Submodule.zero_mem _, by simp⟩`.

Consider the case `tmul a s`. Establish `e : toLA W T π' c ⊤ (a ⊗ₜ s) = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a) ⊗ₜ (s : LcQ W T π' c)` using `rfl`. Establish `e' : ∀ (ε : W.EE) (ℓ : LcQ W T π' c), γLA W T π' c (ε ⊗ₜ ℓ) = W.γE W.gamK ε ⊗ₜ ℓ` using `fun _ _ => rfl`. Take `⟨⟨d, hd, hde⟩, hΔ⟩` from `(mem_PiNS W T π' M _).1 (hγ s)`. Establish `hdΔ` using `invLiftPf_quot_Δ W T π' hu hΔπ M d hd (by rw [hde]; exact hΔ)`.

Establish `haΔ` using `framepf_γA_Δ W.gamK a.2`. Use `⟨((letE c : LetA O n) * W.γA W.gamK a * u) • W.φD T d, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show _ ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1))`. Rewrite using `[mul_assoc, mul_comm, mul_smul, ← φD_letE]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨d, hd, rfl⟩, rfl⟩)`.

Use `show _ ∈ DelS W T`. Rewrite using `[mem_DelS]`. Introduce `δ hδ`. Rewrite using `[gradNPf_γD_smul, ← W.φγ_comm, hdΔ.2 δ hδ, map_mul, map_mul, huΔ δ hδ, haΔ δ hδ, Formalism.MainNotions.LiftingTheory.wmap_γA_letE]`. Use `show _ ∈ letS W T c`.

Rewrite using `[mem_letS, smul_smul, ← mul_assoc, ← mul_assoc, Formalism.MainNotions.LiftingTheory.wmap_letE_idem]`. Rewrite using `[e, e', hΨ, hΨ, W.γD_smul, ← smul_sub, ← W.φγ_comm, ← map_sub, ← hde, Formalism.MainNotions.LiftingTheory.wmap_φD_smul, map_pow, hφ, W.γE_ext, algebraMap_smul, smul_smul, smul_smul, show letγ (W.γ₀ W.gamK) = W.γA W.gamK from rfl, map_mul, Formalism.MainNotions.LiftingTheory.wmap_ …`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Consider the case `add x y hx hy`.

Take `⟨p, hp, hpe⟩` from `hx`. Take `⟨q, hq, hqe⟩` from `hy`. Use `⟨p + q, Submodule.add_mem _ hp hq, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, ← hpe, ← hqe]`. Simplify using `only [map_add]`.

Normalize the expressions using the abelian group laws. Take `⟨p, hp, hpe⟩` from `key z`. Use `⟨t' ^ h' • p, framepf_PcS_smul c (W.AΔ.pow_mem ht'Δ _) hp, ?_⟩` and prove the remaining obligations. Use `show (π' ^ M * Eπ ^ (3 * h')) • (t' ^ h' • p) = _`. Rewrite using `[← sub_eq_zero]`.

Apply `gradNPf_tf W T (Eπ ^ h') (by rw [map_pow]; exact huE.pow _)` to reduce the goal to its premises. Rewrite `hpe` using `[hz, framepf_γLA_smulLA, framepf_Ψ_smulLA, framepf_Ψ_smulLA, gradNPf_γD_smul, ← smul_sub]`. Establish `hΛ : Eπ ^ h' = t' ^ h' * W.γA W.gamK (Eπ ^ h')`. Rewrite using `[map_pow, ← mul_pow, mul_comm, ← ht']`. Establish `h2 : Eπ ^ h' • (W.γD T W.gamK (Ψ x) - Ψ (γLA W T π' c x)) = t' ^ h' • ((π' ^ M * Eπ ^ (4 * h')) • p)`.

Rewrite using `[← hpe, smul_smul, ← hΛ]`. Rewrite using `[smul_sub, h2, smul_smul, smul_smul, smul_smul, ← sub_smul, show Eπ ^ h' * (π' ^ M * Eπ ^ (3 * h')) * t' ^ h' - t' ^ h' * (π' ^ M * Eπ ^ (4 * h')) = 0 by ring, zero_smul]`.
-/
theorem framepf_Ψα_γ (hu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (huE : IsUnit (algebraMap (LetA O n) W.EE Eπ)) (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (u : LetA O n) (huΔ : u ∈ W.AΔ) (hφ : W.φA π' ^ M = π' ^ M * Eπ ^ (4 * h') * u)
    (hh : LcQ W T π' c →ₗ[O] W.DD T)
    (hγ : ∀ ℓ, W.γD T W.gamK (hh ℓ) - hh ℓ ∈ PiNS W T π' M)
    (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (hΨ : ∀ e ℓ, Ψ (e ⊗ₜ ℓ) = e • W.φD T (hh ℓ))
    (x : LA W T π' c) (hx : x ∈ LamLA W T π' Eπ h' c ⊤) :
    W.γD T W.gamK (Ψ x) - Ψ (γLA W T π' c x) ∈ JP W T π' Eπ h' M c := by
  obtain ⟨z, hz⟩ := hx
  have key : ∀ z : ↥W.AΔ ⊗[O] ↥(⊤ : Submodule O (LcQ W T π' c)), ∃ p ∈ PcS W T c,
      W.γD T W.gamK (Ψ (toLA W T π' c ⊤ z)) - Ψ (γLA W T π' c (toLA W T π' c ⊤ z)) =
        (π' ^ M * Eπ ^ (4 * h')) • p := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | tmul a s =>
      have e : toLA W T π' c ⊤ (a ⊗ₜ s) =
        algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a) ⊗ₜ (s : LcQ W T π' c) := rfl
      have e' : ∀ (ε : W.EE) (ℓ : LcQ W T π' c), γLA W T π' c (ε ⊗ₜ ℓ) = W.γE W.gamK ε ⊗ₜ ℓ :=
        fun _ _ => rfl
      obtain ⟨⟨d, hd, hde⟩, hΔ⟩ := (mem_PiNS W T π' M _).1 (hγ s)
      have hdΔ := invLiftPf_quot_Δ W T π' hu hΔπ M d hd (by rw [hde]; exact hΔ)
      have haΔ := framepf_γA_Δ W.gamK a.2
      refine ⟨((letE c : LetA O n) * W.γA W.gamK a * u) • W.φD T d, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · show _ ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1))
        rw [mul_assoc, mul_comm, mul_smul, ← φD_letE]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨d, hd, rfl⟩, rfl⟩)
      · show _ ∈ DelS W T
        rw [mem_DelS]
        intro δ hδ
        rw [gradNPf_γD_smul, ← W.φγ_comm, hdΔ.2 δ hδ, map_mul, map_mul, huΔ δ hδ, haΔ δ hδ,
          Formalism.MainNotions.LiftingTheory.wmap_γA_letE]
      · show _ ∈ letS W T c
        rw [mem_letS, smul_smul, ← mul_assoc, ← mul_assoc, Formalism.MainNotions.LiftingTheory.wmap_letE_idem]
      · rw [e, e', hΨ, hΨ, W.γD_smul, ← smul_sub, ← W.φγ_comm, ← map_sub, ← hde,
          Formalism.MainNotions.LiftingTheory.wmap_φD_smul, map_pow, hφ, W.γE_ext, algebraMap_smul, smul_smul, smul_smul,
          show letγ (W.γ₀ W.gamK) = W.γA W.gamK from rfl, map_mul, Formalism.MainNotions.LiftingTheory.wmap_γA_letE]
        congr 1
        ring
    | add x y hx hy =>
      obtain ⟨p, hp, hpe⟩ := hx
      obtain ⟨q, hq, hqe⟩ := hy
      refine ⟨p + q, Submodule.add_mem _ hp hq, ?_⟩
      rw [smul_add, ← hpe, ← hqe]
      simp only [map_add]
      abel
  obtain ⟨p, hp, hpe⟩ := key z
  refine ⟨t' ^ h' • p, framepf_PcS_smul c (W.AΔ.pow_mem ht'Δ _) hp, ?_⟩
  show (π' ^ M * Eπ ^ (3 * h')) • (t' ^ h' • p) = _
  rw [← sub_eq_zero]
  apply gradNPf_tf W T (Eπ ^ h') (by rw [map_pow]; exact huE.pow _)
  rw [hz, framepf_γLA_smulLA, framepf_Ψ_smulLA, framepf_Ψ_smulLA, gradNPf_γD_smul, ← smul_sub] at hpe
  have hΛ : Eπ ^ h' = t' ^ h' * W.γA W.gamK (Eπ ^ h') := by
    rw [map_pow, ← mul_pow, mul_comm, ← ht']
  have h2 : Eπ ^ h' • (W.γD T W.gamK (Ψ x) - Ψ (γLA W T π' c x)) =
      t' ^ h' • ((π' ^ M * Eπ ^ (4 * h')) • p) := by
    rw [← hpe, smul_smul, ← hΛ]
  rw [smul_sub, h2, smul_smul, smul_smul, smul_smul, ← sub_smul,
    show Eπ ^ h' * (π' ^ M * Eπ ^ (3 * h')) * t' ^ h' - t' ^ h' * (π' ^ M * Eπ ^ (4 * h')) = 0 by ring,
    zero_smul]

include hfΔ hf htΔ ht ht'Δ ht' in

/- English proof (translation)
Establish `hL` using `framepf_γ_LamLA π' Eπ h' c ht'Δ ht' (hΦ y hy)`. Establish `h1` using `hJ _ (Submodule.sub_mem _ (framepf_γ_JP π' Eπ h' M c hfΔ hf htΔ ht (hαβ y hy)) (hΨγ _ (hΦ y hy)))`. Establish `h2` using `Submodule.sub_mem _ (hβα _ hL) h1`. Rewrite `h2` using `[map_sub (W.γD T W.gamK), sub_sub_sub_cancel_left, map_sub Φ, sub_sub_sub_cancel_left, map_smul, LinearMap.map_smul_of_tower, ← smul_sub]`. Conclude with `hsat _ (Submodule.sub_mem _ (hΦ _ hgy) hL) h2`.
-/
theorem framepf_Ψβ_γ (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T)
    (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c) (lam : O)
    (hΨγ : ∀ x ∈ LamLA W T π' Eπ h' c ⊤,
      W.γD T W.gamK (Ψ x) - Ψ (γLA W T π' c x) ∈ JP W T π' Eπ h' M c)
    (hΦ : ∀ y ∈ LamPS W T Eπ h' c, Φ y ∈ LamLA W T π' Eπ h' c ⊤)
    (hJ : ∀ y ∈ JP W T π' Eπ h' M c, Φ y ∈ JLA W T π' Eπ h' M c)
    (hαβ : ∀ y ∈ LamPS W T Eπ h' c, Ψ (Φ y) - lam • y ∈ JP W T π' Eπ h' M c)
    (hβα : ∀ x ∈ LamLA W T π' Eπ h' c ⊤, Φ (Ψ x) - lam • x ∈ JLA W T π' Eπ h' M c)
    (hsat : ∀ x ∈ LamLA W T π' Eπ h' c ⊤, lam • x ∈ JLA W T π' Eπ h' M c → x ∈ JLA W T π' Eπ h' M c)
    (y : W.DD T) (hy : y ∈ LamPS W T Eπ h' c) (hgy : W.γD T W.gamK y ∈ LamPS W T Eπ h' c) :
    Φ (W.γD T W.gamK y) - γLA W T π' c (Φ y) ∈ JLA W T π' Eπ h' M c := by
  have hL := framepf_γ_LamLA π' Eπ h' c ht'Δ ht' (hΦ y hy)
  have h1 := hJ _ (Submodule.sub_mem _ (framepf_γ_JP π' Eπ h' M c hfΔ hf htΔ ht (hαβ y hy))
    (hΨγ _ (hΦ y hy)))
  have h2 := Submodule.sub_mem _ (hβα _ hL) h1
  rw [map_sub (W.γD T W.gamK), sub_sub_sub_cancel_left, map_sub Φ, sub_sub_sub_cancel_left,
    map_smul, LinearMap.map_smul_of_tower, ← smul_sub] at h2
  exact hsat _ (Submodule.sub_mem _ (hΦ _ hgy) hL) h2

end Stab

end Local

end Formalism.MainNotions.N.Ln34

end

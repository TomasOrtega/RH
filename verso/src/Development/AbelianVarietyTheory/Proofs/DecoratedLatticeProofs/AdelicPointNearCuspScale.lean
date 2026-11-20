import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuantitativeMahlerCriterionUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalConjUnipotentRadicalIsotropicStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPosNoShortIntegralVectorFromPointStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShortVectorCuspUnipotentCoverAllInstancesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnitaryUnipotentRadical
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AdelClassFin
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrgCountableField
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.DensRat
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

noncomputable section

namespace GlobalTheory.CuspGeo

/- English proof (translation)
Distinguish the cases in `h : ∃ i, N i ≤ a`. Take `⟨i₀, hi₀⟩` from `h`. Establish `hbdd : BddBelow (Set.range N)` using `⟨t, by rintro _ ⟨i, rfl⟩; exact hN i⟩`. Use `haveI : Nonempty ι := ⟨i₀⟩`. Establish `hl : t ≤ ⨅ i, N i` using `le_ciInf hN`.

Establish `hle : ∀ i, ⨅ i, N i ≤ N i` using `fun i => ciInf_le hbdd i`. Use `⟨min (2 * ⨅ i, N i) a, lt_min (by linarith) ha, min_le_right _ _, fun i => ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `hle i`. Establish `h2` using `min_le_left (2 * ⨅ i, N i) a`. Combine the linear equalities and inequalities to obtain the conclusion.

Break down `le_total (2 * ⨅ i, N i) a with h2 | h2` into its components or cases. Use `right`. Rewrite using `[min_eq_left h2]`. Take `⟨i, hi⟩` from `exists_lt_of_ciInf_lt (show ⨅ i, N i < 2 * ⨅ i, N i by linarith)`. Conclude with `⟨i, hi.le⟩`.

Use `left`. Conclude with `min_eq_right h2`. Use `push_neg at h`. Conclude with `⟨a, ha, le_rfl, fun i => by linarith [h i], Or.inl rfl⟩`.
-/
theorem exists_scale_of_bdd {ι : Type*} (N : ι → ℝ) (t a : ℝ) (ht : 0 < t) (hN : ∀ i, t ≤ N i) (ha : 0 < a) :
    ∃ m : ℝ, 0 < m ∧ m ≤ a ∧ (∀ i, m / 2 ≤ N i) ∧ (m = a ∨ ∃ i, N i ≤ m) := by
  by_cases h : ∃ i, N i ≤ a
  · obtain ⟨i₀, hi₀⟩ := h
    have hbdd : BddBelow (Set.range N) := ⟨t, by rintro _ ⟨i, rfl⟩; exact hN i⟩
    haveI : Nonempty ι := ⟨i₀⟩
    have hl : t ≤ ⨅ i, N i := le_ciInf hN
    have hle : ∀ i, ⨅ i, N i ≤ N i := fun i => ciInf_le hbdd i
    refine ⟨min (2 * ⨅ i, N i) a, lt_min (by linarith) ha, min_le_right _ _, fun i => ?_, ?_⟩
    · have h1 := hle i
      have h2 := min_le_left (2 * ⨅ i, N i) a
      linarith
    · rcases le_total (2 * ⨅ i, N i) a with h2 | h2
      · right
        rw [min_eq_left h2]
        obtain ⟨i, hi⟩ := exists_lt_of_ciInf_lt (show ⨅ i, N i < 2 * ⨅ i, N i by linarith)
        exact ⟨i, hi.le⟩
      · left
        exact min_eq_right h2
  · push_neg at h
    exact ⟨a, ha, le_rfl, fun i => by linarith [h i], Or.inl rfl⟩

/- English proof (translation)
Use `⟨(m / s₀) ^ ((((n + 1 : ℕ) : ℝ))⁻¹), Real.rpow_pos_of_pos (div_pos hm hs) _, ?_⟩` and prove the remaining obligations. Rewrite using `[Real.rpow_inv_natCast_pow (div_pos hm hs).le (Nat.succ_ne_zero n)]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_root_scale (n : ℕ) (s₀ m : ℝ) (hs : 0 < s₀) (hm : 0 < m) :
    ∃ η : ℝ, 0 < η ∧ s₀ * η ^ (n + 1) = m := by
  refine ⟨(m / s₀) ^ ((((n + 1 : ℕ) : ℝ))⁻¹), Real.rpow_pos_of_pos (div_pos hm hs) _, ?_⟩
  rw [Real.rpow_inv_natCast_pow (div_pos hm hs).le (Nat.succ_ne_zero n)]
  field_simp

/- English proof (translation)
Take `⟨t, ht, hNS⟩` from `GlobalTheory.T.exists_pos_noShortIntegralVectorFromPoint I y`. Take `⟨m, hm0, hma, hmN, hmc⟩` from `exists_scale_of_bdd (ι := {u // IntVec I u ∧ u ≠ 0}) (fun u => ‖vec I y u.1‖) t (s₀ * η₀ ^ (I.n + 1)) ht (fun u => hNS u.1 u.2.1 u.2.2) (by positivity)`. Take `⟨η, hη0, hηm⟩` from `exists_root_scale I.n s₀ m hs hm0`. Establish `hpow : η ^ (I.n + 1) ≤ η₀ ^ (I.n + 1)` using `le_of_mul_le_mul_left (by rw [hηm]; exact hma) hs`. Use `⟨η, hη0, (pow_le_pow_iff_left₀ hη0.le hη.le (Nat.succ_ne_zero _)).1 hpow, fun u hu hu0 => ?_, ?_⟩` and prove the remaining obligations.

Establish `h1` using `hmN ⟨u, hu, hu0⟩`. Establish `h2 : s₀ / 2 * η ^ (I.n + 1) = m / 2` using `by rw [← hηm]; ring`. Rewrite using `[h2]`. Conclude with `h1`. Break down `hmc with h | ⟨⟨u, hu, hu0⟩, hle⟩` into its components or cases.

Use `left`. Establish `: η₀ ^ (I.n + 1) ≤ η ^ (I.n + 1)` using `le_of_mul_le_mul_left (by rw [hηm, h]) hs`. Conclude with `(pow_le_pow_iff_left₀ hη.le hη0.le (Nat.succ_ne_zero _)).1 this`. Use `right`. Conclude with `⟨u, hu, hu0, hηm ▸ hle⟩`.
-/
theorem exists_scale_real (I : AutInst) (y : I.Ginf) (s₀ η₀ : ℝ) (hs : 0 < s₀) (hη : 0 < η₀) :
    ∃ η : ℝ, 0 < η ∧ η ≤ η₀ ∧ NoShort I y (s₀ / 2 * η ^ (I.n + 1)) ∧
      (η₀ ≤ η ∨ ∃ u, IntVec I u ∧ u ≠ 0 ∧ ‖vec I y u‖ ≤ s₀ * η ^ (I.n + 1)) := by
  obtain ⟨t, ht, hNS⟩ := GlobalTheory.T.exists_pos_noShortIntegralVectorFromPoint I y
  obtain ⟨m, hm0, hma, hmN, hmc⟩ := exists_scale_of_bdd (ι := {u // IntVec I u ∧ u ≠ 0})
    (fun u => ‖vec I y u.1‖) t (s₀ * η₀ ^ (I.n + 1)) ht (fun u => hNS u.1 u.2.1 u.2.2) (by positivity)
  obtain ⟨η, hη0, hηm⟩ := exists_root_scale I.n s₀ m hs hm0
  have hpow : η ^ (I.n + 1) ≤ η₀ ^ (I.n + 1) := le_of_mul_le_mul_left (by rw [hηm]; exact hma) hs
  refine ⟨η, hη0, (pow_le_pow_iff_left₀ hη0.le hη.le (Nat.succ_ne_zero _)).1 hpow, fun u hu hu0 => ?_, ?_⟩
  · have h1 := hmN ⟨u, hu, hu0⟩
    have h2 : s₀ / 2 * η ^ (I.n + 1) = m / 2 := by rw [← hηm]; ring
    rw [h2]
    exact h1
  · rcases hmc with h | ⟨⟨u, hu, hu0⟩, hle⟩
    · left
      have : η₀ ^ (I.n + 1) ≤ η ^ (I.n + 1) := le_of_mul_le_mul_left (by rw [hηm, h]) hs
      exact (pow_le_pow_iff_left₀ hη.le hη0.le (Nat.succ_ne_zero _)).1 this
    · right
      exact ⟨u, hu, hu0, hηm ▸ hle⟩

/- English proof (translation)
Introduce `v i j` and use `(h v i j).trans hab`.
-/
theorem close_mono (I : AutInst) {u : I.Ginf} {a b : ℝ} (h : Close I u a) (hab : a ≤ b) : Close I u b :=
  fun v i j => (h v i j).trans hab

end GlobalTheory.CuspGeo

noncomputable section

namespace GlobalTheory.CuspGeo

open Formalism.MainNotions.LeviCoordinates in

/- English proof (translation)
Introduce `I Kp hKo`. Establish `hmem : ∀ {g : I.GA}, g ∈ I.GFset ↔ g ∈ rr_GF I` using `fun {g} => by`. Rewrite using `[← SetLike.mem_coe, rr_GF_coe]`. Take `⟨-, -, -, hKsC, hKsO, ⟨Ks, hKs⟩, -⟩` from `GlobalTheory.CongTop.adelic_topology I`. Use `set Kq : Subgroup I.Gf := Kp ⊓ Ks with hKq`.

Establish `hKqO : IsOpen (Kq : Set I.Gf)`. Rewrite using `[hKq, Subgroup.coe_inf, hKs]`. Conclude with `hKo.inter hKsO`. Establish `hKqC : IsCompact (Kq : Set I.Gf)` using `hKsC.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hKqO) (by rw [← hKs]; exact fun z hz => (Subgroup.mem_inf.1 hz).2)`. Take `⟨S, hS⟩` from `adelic_class_set_finite I Kq hKqO`.

Use `set U : Set I.Gf := {g | ∀ s ∈ S, s⁻¹ * g * s ∈ Kq} with hUdef`. Establish `hU : U ∈ 𝓝 (1 : I.Gf)`. Establish `: ∀ s ∈ S, ∀ᶠ g in 𝓝 (1 : I.Gf), s⁻¹ * g * s ∈ Kq` using `fun s _ => (hKqO.preimage (by fun_prop : Continuous fun g : I.Gf => s⁻¹ * g * s)).mem_nhds (by simp)`. Conclude with `(Filter.eventually_all_finset S).2 this`. Take `⟨s₀, η₀, Cs, hs₀, hη₀, hSC⟩` from `GlobalTheory.T.shortVectorCuspUnipotentCover_all_instances I U hU`.

Take `⟨b, CH, KH, hKH, hHt⟩` from `GlobalTheory.T.quantitativeMahlerCriterion_unitaryGroup I`. Use `set s₁ := min s₀ 1 with hs₁`. Use `set η₁ := min η₀ 1 with hη₁`. Establish `hs₁0 : 0 < s₁` using `lt_min hs₀ one_pos`. Establish `hη₁0 : 0 < η₁` using `lt_min hη₀ one_pos`.

Use `set C := max (CH / (s₁ / 2) ^ b) Cs with hC`. Use `⟨(I.n + 1) * b, C, η₁, (fun p : I.Gf × I.Gf × I.Gf => p.1 * p.2.1 * p.2.2) '' (KH ×ˢ ((S : Set I.Gf) ×ˢ (Kq : Set I.Gf))), hη₁0, (hKH.prod (S.finite_toSet.isCompact.prod hKqC)).image (by fun_prop), fun x => ?_⟩` and prove the remaining obligations. Take `⟨γf, ⟨γE, hγE, hγEf⟩, s, hsS, k, hk, hx2⟩` from `hS x.2`. Use `set γ₀ : I.GA := (fun v => Formalism.L2.S.S7.DensRat.ratReal I γE hγE v, γf) with hγ₀def`. Establish `hγ₀ : γ₀ ∈ I.GFset` using `⟨γE, hγE, fun _ => rfl, hγEf⟩`.

Use `set y : I.Ginf := γ₀.1⁻¹ * x.1 with hy`. Establish `hx : x = γ₀ * ((y, s * k) : I.GA)` using `Prod.ext (by simp [hy]) (by simp [hγ₀def, hx2, mul_assoc])`. Take `⟨η, hη0, hηle, hNS, hcase⟩` from `exists_scale_real I y s₁ η₁ hs₁0 hη₁0`. Establish `hη1 : η ≤ 1` using `hηle.trans (min_le_right _ _)`. Use `set t := s₁ / 2 * η ^ (I.n + 1) with ht`.

Establish `ht0 : 0 < t` using `by positivity`. Establish `ht1 : t ≤ 1`. Establish `h1 : s₁ ≤ 1` using `min_le_right _ _`. Establish `h2 : η ^ (I.n + 1) ≤ 1` using `pow_le_one₀ hη0.le hη1`. Establish `h3 : 0 ≤ η ^ (I.n + 1)` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Take `⟨γ₁, hγ₁, hγ₁K, hγ₁b⟩` from `hHt y t ht0 ht1 hNS`. Use `⟨η, hη0, hη1, ⟨γ₁ * γ₀⁻¹, hmem.2 ((rr_GF I).mul_mem (hmem.1 hγ₁) ((rr_GF I).inv_mem (hmem.1 hγ₀))), ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `⟨(γ₁.2, s, k), ⟨hγ₁K, hsS, hk⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hx]`.

Simplify using `[mul_assoc]`. Introduce `v i j`. Establish `e1 : (γ₁ * γ₀⁻¹ * x).1 = γ₁.1 * y` using `by rw [hx]; simp [mul_assoc]`. Rewrite using `[e1]`. Establish `hb` using `hγ₁b v i j`.

Establish `hpos : 0 < (s₁ / 2) ^ b` using `by positivity`. Establish `e2 : t ^ b = (s₁ / 2) ^ b * η ^ ((I.n + 1) * b)` using `by rw [ht, mul_pow, pow_mul]`. Rewrite `hb` using `[e2]`. Establish `h3 : ‖uMat ((γ₁.1 * y) v) i j‖ * η ^ ((I.n + 1) * b) ≤ CH / (s₁ / 2) ^ b`. Rewrite using `[le_div_iff₀ hpos]`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h3.trans (le_max_left _ _)`. Break down `hcase with h | ⟨u, hu, hu0, hul⟩` into its components or cases. Conclude with `Or.inl h`. Use `right`.

Establish `hul' : ‖vec I y u‖ ≤ s₀ * η ^ (I.n + 1)` using `hul.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))`. Take `⟨W, hW, hcov⟩` from `hSC y η hη0 (hηle.trans (min_le_left _ _)) ⟨u, hu, hu0, hul'⟩`. Take `⟨W', hW', hconj⟩` from `GlobalTheory.T.rational_conj_unipotentRadical_isotropic I γ₀ hγ₀ W hW`. Take `⟨⟨N, hN⟩, -, hpart, hdense, -⟩` from `GlobalTheory.UnipApprox.strong_approximation I W hW`. Use `⟨W', hW', fun m hm => ?_⟩` and prove the remaining obligations.

Establish `hm' : γ₀⁻¹ * m * γ₀ ∈ I.NA W` using `hconj m hm`. Take `⟨γ₂, ⟨hγ₂, hγ₂N⟩, hγ₂U⟩` from `hdense U hU _ hm'`. Use `set m'' := γ₂⁻¹ * (γ₀⁻¹ * m * γ₀) with hm''`. Establish `hm''N : m'' ∈ I.NA W`. Rewrite `hm'`, `hγ₂N`, the goal using `[← hN]`.

Conclude with `N.mul_mem (N.inv_mem hγ₂N) hm'`. Take `⟨γ₃, hγ₃, hγ₃U, hclose⟩` from `hcov m''.1 (hpart m'' hm''N).1`. Use `⟨γ₀ * γ₂ * γ₃⁻¹ * γ₀⁻¹, hmem.2 ((rr_GF I).mul_mem ((rr_GF I).mul_mem ((rr_GF I).mul_mem (hmem.1 hγ₀) (hmem.1 hγ₂)) ((rr_GF I).inv_mem (hmem.1 hγ₃))) ((rr_GF I).inv_mem (hmem.1 hγ₀))), y⁻¹ * (γ₃.1 * m''.1) * y, (s * k)⁻¹ * (γ₃.2 * m''.2) * (s * k), ?_, ?_, close_mono I hclose (mul …` and prove the remaining obligations. Establish `e : (s * k)⁻¹ * (γ₃.2 * m''.2) * (s * k) = k⁻¹ * ((s⁻¹ * γ₃.2 * s) * (s⁻¹ * m''.2 * s)) * k` using `by group`. Rewrite using `[e]`.

Establish `hk' : k⁻¹ * ((s⁻¹ * γ₃.2 * s) * (s⁻¹ * m''.2 * s)) * k ∈ Kq` using `Kq.mul_mem (Kq.mul_mem (Kq.inv_mem hk) (Kq.mul_mem (hγ₃U s hsS) (hγ₂U s hsS))) hk`. Conclude with `(Subgroup.mem_inf.1 hk').1`. Establish `hyu : ((y, s * k) : I.GA) * (y⁻¹ * (γ₃.1 * m''.1) * y, (s * k)⁻¹ * (γ₃.2 * m''.2) * (s * k)) = γ₃ * m'' * (y, s * k)` using `Prod.ext (by simp; group) (by simp; group)`. Establish `hmm : m = γ₀ * γ₂ * m'' * γ₀⁻¹` using `by rw [hm'']; group`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem nearInst : ∀ I : AutInst, NearInst I := by
  intro I Kp hKo
  have hmem : ∀ {g : I.GA}, g ∈ I.GFset ↔ g ∈ rr_GF I := fun {g} => by
    rw [← SetLike.mem_coe, rr_GF_coe]
  obtain ⟨-, -, -, hKsC, hKsO, ⟨Ks, hKs⟩, -⟩ := GlobalTheory.CongTop.adelic_topology I
  set Kq : Subgroup I.Gf := Kp ⊓ Ks with hKq
  have hKqO : IsOpen (Kq : Set I.Gf) := by
    rw [hKq, Subgroup.coe_inf, hKs]; exact hKo.inter hKsO
  have hKqC : IsCompact (Kq : Set I.Gf) :=
    hKsC.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hKqO)
      (by rw [← hKs]; exact fun z hz => (Subgroup.mem_inf.1 hz).2)
  obtain ⟨S, hS⟩ := adelic_class_set_finite I Kq hKqO
  set U : Set I.Gf := {g | ∀ s ∈ S, s⁻¹ * g * s ∈ Kq} with hUdef
  have hU : U ∈ 𝓝 (1 : I.Gf) := by
    have : ∀ s ∈ S, ∀ᶠ g in 𝓝 (1 : I.Gf), s⁻¹ * g * s ∈ Kq := fun s _ =>
      (hKqO.preimage (by fun_prop : Continuous fun g : I.Gf => s⁻¹ * g * s)).mem_nhds (by simp)
    exact (Filter.eventually_all_finset S).2 this
  obtain ⟨s₀, η₀, Cs, hs₀, hη₀, hSC⟩ := GlobalTheory.T.shortVectorCuspUnipotentCover_all_instances I U hU
  obtain ⟨b, CH, KH, hKH, hHt⟩ := GlobalTheory.T.quantitativeMahlerCriterion_unitaryGroup I
  set s₁ := min s₀ 1 with hs₁
  set η₁ := min η₀ 1 with hη₁
  have hs₁0 : 0 < s₁ := lt_min hs₀ one_pos
  have hη₁0 : 0 < η₁ := lt_min hη₀ one_pos
  set C := max (CH / (s₁ / 2) ^ b) Cs with hC
  refine ⟨(I.n + 1) * b, C, η₁, (fun p : I.Gf × I.Gf × I.Gf => p.1 * p.2.1 * p.2.2) '' (KH ×ˢ ((S : Set I.Gf) ×ˢ (Kq : Set I.Gf))),
    hη₁0, (hKH.prod (S.finite_toSet.isCompact.prod hKqC)).image (by fun_prop), fun x => ?_⟩
  obtain ⟨γf, ⟨γE, hγE, hγEf⟩, s, hsS, k, hk, hx2⟩ := hS x.2
  set γ₀ : I.GA := (fun v => Formalism.L2.S.S7.DensRat.ratReal I γE hγE v, γf) with hγ₀def
  have hγ₀ : γ₀ ∈ I.GFset := ⟨γE, hγE, fun _ => rfl, hγEf⟩
  set y : I.Ginf := γ₀.1⁻¹ * x.1 with hy
  have hx : x = γ₀ * ((y, s * k) : I.GA) :=
    Prod.ext (by simp [hy]) (by simp [hγ₀def, hx2, mul_assoc])
  obtain ⟨η, hη0, hηle, hNS, hcase⟩ := exists_scale_real I y s₁ η₁ hs₁0 hη₁0
  have hη1 : η ≤ 1 := hηle.trans (min_le_right _ _)
  set t := s₁ / 2 * η ^ (I.n + 1) with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    have h1 : s₁ ≤ 1 := min_le_right _ _
    have h2 : η ^ (I.n + 1) ≤ 1 := pow_le_one₀ hη0.le hη1
    have h3 : 0 ≤ η ^ (I.n + 1) := by positivity
    nlinarith
  obtain ⟨γ₁, hγ₁, hγ₁K, hγ₁b⟩ := hHt y t ht0 ht1 hNS
  refine ⟨η, hη0, hη1, ⟨γ₁ * γ₀⁻¹, hmem.2 ((rr_GF I).mul_mem (hmem.1 hγ₁) ((rr_GF I).inv_mem (hmem.1 hγ₀))), ?_, ?_⟩, ?_⟩
  · refine ⟨(γ₁.2, s, k), ⟨hγ₁K, hsS, hk⟩, ?_⟩
    rw [hx]
    simp [mul_assoc]
  · intro v i j
    have e1 : (γ₁ * γ₀⁻¹ * x).1 = γ₁.1 * y := by rw [hx]; simp [mul_assoc]
    rw [e1]
    have hb := hγ₁b v i j
    have hpos : 0 < (s₁ / 2) ^ b := by positivity
    have e2 : t ^ b = (s₁ / 2) ^ b * η ^ ((I.n + 1) * b) := by rw [ht, mul_pow, pow_mul]
    rw [e2] at hb
    have h3 : ‖uMat ((γ₁.1 * y) v) i j‖ * η ^ ((I.n + 1) * b) ≤ CH / (s₁ / 2) ^ b := by
      rw [le_div_iff₀ hpos]; linarith
    exact h3.trans (le_max_left _ _)
  rcases hcase with h | ⟨u, hu, hu0, hul⟩
  · exact Or.inl h
  right
  have hul' : ‖vec I y u‖ ≤ s₀ * η ^ (I.n + 1) :=
    hul.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  obtain ⟨W, hW, hcov⟩ := hSC y η hη0 (hηle.trans (min_le_left _ _)) ⟨u, hu, hu0, hul'⟩
  obtain ⟨W', hW', hconj⟩ := GlobalTheory.T.rational_conj_unipotentRadical_isotropic I γ₀ hγ₀ W hW
  obtain ⟨⟨N, hN⟩, -, hpart, hdense, -⟩ := GlobalTheory.UnipApprox.strong_approximation I W hW
  refine ⟨W', hW', fun m hm => ?_⟩
  have hm' : γ₀⁻¹ * m * γ₀ ∈ I.NA W := hconj m hm
  obtain ⟨γ₂, ⟨hγ₂, hγ₂N⟩, hγ₂U⟩ := hdense U hU _ hm'
  set m'' := γ₂⁻¹ * (γ₀⁻¹ * m * γ₀) with hm''
  have hm''N : m'' ∈ I.NA W := by
    rw [← hN] at hm' hγ₂N ⊢
    exact N.mul_mem (N.inv_mem hγ₂N) hm'
  obtain ⟨γ₃, hγ₃, hγ₃U, hclose⟩ := hcov m''.1 (hpart m'' hm''N).1
  refine ⟨γ₀ * γ₂ * γ₃⁻¹ * γ₀⁻¹, hmem.2 ((rr_GF I).mul_mem ((rr_GF I).mul_mem ((rr_GF I).mul_mem (hmem.1 hγ₀)
    (hmem.1 hγ₂)) ((rr_GF I).inv_mem (hmem.1 hγ₃))) ((rr_GF I).inv_mem (hmem.1 hγ₀))),
    y⁻¹ * (γ₃.1 * m''.1) * y, (s * k)⁻¹ * (γ₃.2 * m''.2) * (s * k), ?_, ?_,
    close_mono I hclose (mul_le_mul_of_nonneg_right (le_max_right _ _) hη0.le)⟩
  · have e : (s * k)⁻¹ * (γ₃.2 * m''.2) * (s * k) = k⁻¹ * ((s⁻¹ * γ₃.2 * s) * (s⁻¹ * m''.2 * s)) * k := by group
    rw [e]
    have hk' : k⁻¹ * ((s⁻¹ * γ₃.2 * s) * (s⁻¹ * m''.2 * s)) * k ∈ Kq :=
      Kq.mul_mem (Kq.mul_mem (Kq.inv_mem hk) (Kq.mul_mem (hγ₃U s hsS) (hγ₂U s hsS))) hk
    exact (Subgroup.mem_inf.1 hk').1
  · have hyu : ((y, s * k) : I.GA) * (y⁻¹ * (γ₃.1 * m''.1) * y, (s * k)⁻¹ * (γ₃.2 * m''.2) * (s * k)) =
        γ₃ * m'' * (y, s * k) := Prod.ext (by simp; group) (by simp; group)
    have hmm : m = γ₀ * γ₂ * m'' * γ₀⁻¹ := by rw [hm'']; group
    calc m * x = γ₀ * γ₂ * γ₃⁻¹ * (γ₃ * m'' * (y, s * k)) := by rw [hmm, hx]; group
      _ = _ := by rw [← hyu, hx]; group

end GlobalTheory.CuspGeo

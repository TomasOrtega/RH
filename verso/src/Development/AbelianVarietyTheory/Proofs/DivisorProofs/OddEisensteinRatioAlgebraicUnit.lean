import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackConstantSqEqDet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMapRingOfIntegersLeOne

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

namespace GlobalTheory.VacUnit

open Formalism.MainNotions.TaylorLogMetric (hYY LocBasis YYl)
open Formalism.MainNotions.StandardLatticesGL3 (OnB LaB pullB KLat)

/- English proof (translation)
Rewrite `h`, the goal using `[mem_algebraicClosure_iff]`. Conclude with `h.of_pow hn`.
-/
theorem mem_Qbar_of_pow {x : ℂ} {n : ℕ} (hn : 0 < n) (h : x ^ n ∈ Qbar) : x ∈ Qbar := by
  rw [mem_algebraicClosure_iff] at h ⊢
  exact h.of_pow hn

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one`. Consider the case `exact _root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one`. Consider the case `(apply _root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one ..)`.
-/
theorem norm_int_le {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] (f : K →+* ℂ_[p]) (c : 𝓞 K) :
    ‖f (c : K)‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one
  | exact _root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one
  | (apply _root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one ..)

/- English proof (translation)
Establish `h1 : (s : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (s : ℚ_[p])` using `by simp`. Rewrite using `[h1, norm_algebraMap', Padic.norm_natCast_eq_one_iff]`. Conclude with `h.symm`.
-/
theorem norm_nat_coprime {p : ℕ} [Fact p.Prime] {s : ℕ} (h : Nat.Coprime s p) : ‖(s : ℂ_[p])‖ = 1 := by
  have h1 : (s : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (s : ℚ_[p]) := by simp
  rw [h1, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact h.symm

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_prod]`. Use `mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one ℂ_[p] _) (Finset.prod_nonneg fun _ _ => norm_nonneg _) ?_` and prove the remaining obligations. Conclude with `Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => h _ _`.
-/
theorem norm_det_le {p : ℕ} [Fact p.Prime] {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ_[p]) (h : ∀ i j, ‖M i j‖ ≤ 1) :
    ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rw [norm_mul, norm_prod]
  refine mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one ℂ_[p] _) (Finset.prod_nonneg fun _ _ => norm_nonneg _) ?_
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => h _ _

variable {D : D7} {N N' r : ℕ}

/- English proof (translation)
Simplify using `only [hYY, ← smul_eq_mul, ← map_smul, ← map_sum]`. Use `congr 1`. Simplify using `only [Matrix.sum_apply, Matrix.smul_apply, Finset.smul_sum, smul_eq_mul, Finset.sum_mul, smul_mul_assoc]`. Use `symm`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.
-/
theorem hYY_comb (c : Fin r → D.host.K) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (y : Matrix (Fin N') (Fin N) D.host.E) : hYY D (∑ k, c k • b k) y = ∑ k, c k * hYY D (b k) y := by
  simp only [hYY, ← smul_eq_mul, ← map_smul, ← map_sum]
  congr 1
  simp only [Matrix.sum_apply, Matrix.smul_apply, Finset.smul_sum, smul_eq_mul, Finset.sum_mul, smul_mul_assoc]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]

/- English proof (translation)
Take `⟨s, hs, hY⟩` from `hl'.2.1 j`. Take `⟨t, ht, c, hc⟩` from `hl.2.2 _ hY`. Establish `hst : Nat.Coprime (t * s) p` using `Nat.Coprime.mul_left ht hs`. Establish `h0 : ((t * s : ℕ) : D.host.K) ≠ 0`. Introduce `h`.

Establish `h1` using `norm_nat_coprime hst`. Rewrite `h1` using `[← map_natCast f, h]`. Simplify using `at h1`. Use `⟨fun i => ((t * s : ℕ) : D.host.K)⁻¹ * (c i : D.host.K), fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_inv₀, map_natCast, norm_mul, norm_inv, norm_nat_coprime hst, inv_one, one_mul]`.

Conclude with `norm_int_le f _`. Establish `h2 : ((t * s : ℕ) : D.host.K) • b' j = ∑ i, (c i : D.host.K) • b i`. Rewrite `hc` using `[smul_smul, ← Nat.cast_mul, Nat.cast_smul_eq_nsmul]`. Rewrite using `[Nat.cast_smul_eq_nsmul, hc]`. Both sides reduce to the same expression.

Simplify using `only [mul_smul]`. Rewrite using `[← Finset.smul_sum, ← h2, smul_smul, inv_mul_cancel₀ h0, one_smul]`.
-/
theorem exists_coord {p : ℕ} [Fact p.Prime] (f : D.host.K →+* ℂ_[p])
    {Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)}
    {b b' : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hl : LocBasis D p Y b) (hl' : LocBasis D p Y b') (j : Fin r) :
    ∃ a : Fin r → D.host.K, (∀ i, ‖f (a i)‖ ≤ 1) ∧ b' j = ∑ i, a i • b i := by
  obtain ⟨s, hs, hY⟩ := hl'.2.1 j
  obtain ⟨t, ht, c, hc⟩ := hl.2.2 _ hY
  have hst : Nat.Coprime (t * s) p := Nat.Coprime.mul_left ht hs
  have h0 : ((t * s : ℕ) : D.host.K) ≠ 0 := by
    intro h
    have h1 := norm_nat_coprime hst
    rw [← map_natCast f, h] at h1
    simp at h1
  refine ⟨fun i => ((t * s : ℕ) : D.host.K)⁻¹ * (c i : D.host.K), fun i => ?_, ?_⟩
  · rw [map_mul, map_inv₀, map_natCast, norm_mul, norm_inv, norm_nat_coprime hst, inv_one, one_mul]
    exact norm_int_le f _
  · have h2 : ((t * s : ℕ) : D.host.K) • b' j = ∑ i, (c i : D.host.K) • b i := by
      rw [smul_smul, ← Nat.cast_mul, Nat.cast_smul_eq_nsmul] at hc
      rw [Nat.cast_smul_eq_nsmul, hc]
      rfl
    simp only [mul_smul]
    rw [← Finset.smul_sum, ← h2, smul_smul, inv_mul_cancel₀ h0, one_smul]

/- English proof (translation)
Use `choose a ha hab using exists_coord f hl hl'`. Use `choose a' ha' hab' using exists_coord f hl' hl`. Establish `hM : ∀ i j, hYY D (b' j) (b i) = a j i`. Introduce `i j`. Rewrite using `[hab j, hYY_comb]`.

Simplify using `[hb.1 _ i]`. Establish `hMM : (Matrix.of fun i j => hYY D (b' j) (b i)) * (Matrix.of fun j k => a' k j) = 1`. Use extensionality with `i k`. Establish `h1` using `hb.1 k i`. Use `conv_lhs at h1 => rw [hab' k, hYY_comb]`.

Rewrite using `[Matrix.mul_apply, Matrix.one_apply, if_congr (eq_comm (a := i)) rfl rfl, ← h1]`. Simplify using `[mul_comm]`. Establish `hd` using `congrArg (fun A => ‖f (Matrix.det A)‖) hMM`. Simplify using `only [Matrix.det_mul, map_mul, norm_mul, Matrix.det_one, map_one, norm_one] at hd`. Establish `h1 : ‖f (Matrix.of fun i j => hYY D (b' j) (b i)).det‖ ≤ 1`.

Rewrite using `[RingHom.map_det]`. Conclude with `norm_det_le _ fun i j => by simpa [hM] using ha j i`. Establish `h2 : ‖f (Matrix.of fun j k => a' k j).det‖ ≤ 1`. Rewrite using `[RingHom.map_det]`. Conclude with `norm_det_le _ fun i j => by simpa using ha' j i`.

Use `le_antisymm h1 ?_` and prove the remaining obligations. Rewrite using `[← hd]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) h2`.
-/
theorem norm_det_eq_one {p : ℕ} [Fact p.Prime] (f : D.host.K →+* ℂ_[p])
    {Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)}
    {b b' : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : OnB D b)
    (hl : LocBasis D p Y b) (hl' : LocBasis D p Y b') :
    ‖f (Matrix.of fun i j => hYY D (b' j) (b i)).det‖ = 1 := by
  choose a ha hab using exists_coord f hl hl'
  choose a' ha' hab' using exists_coord f hl' hl
  have hM : ∀ i j, hYY D (b' j) (b i) = a j i := by
    intro i j
    rw [hab j, hYY_comb]
    simp [hb.1 _ i]
  have hMM : (Matrix.of fun i j => hYY D (b' j) (b i)) * (Matrix.of fun j k => a' k j) = 1 := by
    ext i k
    have h1 := hb.1 k i
    conv_lhs at h1 => rw [hab' k, hYY_comb]
    rw [Matrix.mul_apply, Matrix.one_apply, if_congr (eq_comm (a := i)) rfl rfl, ← h1]
    simp [mul_comm]
  have hd := congrArg (fun A => ‖f (Matrix.det A)‖) hMM
  simp only [Matrix.det_mul, map_mul, norm_mul, Matrix.det_one, map_one, norm_one] at hd
  have h1 : ‖f (Matrix.of fun i j => hYY D (b' j) (b i)).det‖ ≤ 1 := by
    rw [RingHom.map_det]
    exact norm_det_le _ fun i j => by simpa [hM] using ha j i
  have h2 : ‖f (Matrix.of fun j k => a' k j).det‖ ≤ 1 := by
    rw [RingHom.map_det]
    exact norm_det_le _ fun i j => by simpa using ha' j i
  refine le_antisymm h1 ?_
  rw [← hd]
  exact mul_le_of_le_one_right (norm_nonneg _) h2

noncomputable def phiK (D : D7) : D.host.K →+* Qbar :=
  (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).codRestrict Qbar.toSubring fun x => by
    change _ ∈ Qbar
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom
      (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).toRatAlgHom

/- English proof (translation)
Establish `hSD : ∀ n, Formalism.MainNotions.StandardLatticesGL3.SD D (stdL D n)` using `fun n => by`. Take `⟨Lt, h1, h2, -⟩` from `GlobalTheory.NormSum.exists_lattice_of_adelic_point D n`. Conclude with `h2 ▸ (h1 1).2`. Take `⟨b, ε, hb, hl, hε, hεn, -, he⟩` from `h₁.2.2.2.2 p lam (by simp)`. Take `⟨b', ε', hb', hl', hε', hεn', -, he'⟩` from `h₂.2.2.2.2 p lam (by simp)`.

Take `⟨c, ζ, m, hm, hζ, hc, hpull⟩` from `GlobalTheory.UnitaryTheta.const_sq_eq_det D ⊤ δ hC t0 ht N N' _ b b' hb hb'`. Take `⟨μ, hμ, hI3⟩` from `hI.mu ⊤ δ hC N N' _ _ (La0 D (tor0 D ⊤ δ) N N') (Or.inl ⟨_, b, hb, rfl⟩) (Or.inl ⟨_, b', hb', rfl⟩) (Or.inr ⟨_, _, hSD N, hSD N', rfl⟩) _ (GlobalTheory.UnitaryTheta.pullB_mem D ⊤ δ hC t0 ht N N' _ b hb).1`. Take `⟨z, hz⟩` from `Function.ne_iff.1 hne`. Establish `e2` using `congrFun hκ z`. Rewrite `e2` using `[he', hpull, Pi.smul_apply, smul_eq_mul]`.

Rewrite `e2`, `hz` using `[he]`. Simplify using `only [GlobalTheory.UnitaryTheta.iop_smul, hI3] at e2`. Establish `hz'` using `right_ne_zero_of_mul hz`. Establish `key : κ * ε = ε' * c * μ`. Apply `mul_right_cancel₀ hz'` to reduce the goal to its premises.

Take the linear combination `-e2`. Establish `hζQ : ζ ∈ Qbar` using `mem_Qbar_of_pow hm (hζ ▸ one_mem _)`. Establish `hμQ : μ ∈ Qbar` using `mem_Qbar_of_pow (n := 8) (by norm_num) (hμ ▸ one_mem _)`. Use `set u := phiK D (Matrix.of fun i j => hYY D (b' j) (b i)).det with hu`. Establish `hun : ‖lam u‖ = 1` using `norm_det_eq_one (lam.comp (phiK D)) hb hl hl'`.

Express the relevant statement in the definitionally equal form `c ^ 2 = ζ * (u : ℂ) at hc`. Establish `hcQ : c ∈ Qbar` using `mem_Qbar_of_pow (n := 2) (by norm_num) (hc ▸ mul_mem hζQ u.2)`. Rewrite `hεn` using `[lamC, dif_pos hε]`. Rewrite `hεn'` using `[lamC, dif_pos hε']`. Establish `hε0 : ε ≠ 0` using `left_ne_zero_of_mul hz`.

Establish `hκQ : κ ∈ Qbar`. Rewrite using `[eq_div_of_mul_eq hε0 key]`. Conclude with `div_mem (mul_mem (mul_mem hε' hcQ) hμQ) hε`. Use `⟨hκQ, ?_⟩` and prove the remaining obligations. Rewrite using `[lamC, dif_pos hκQ]`.

Establish `root : ∀ (x : Qbar) (n : ℕ), 0 < n → (x : ℂ) ^ n = 1 → ‖lam x‖ = 1`. Introduce `x n hn hx`. Establish `: x ^ n = 1` using `Subtype.ext (by simpa using hx)`. Establish `h` using `congrArg (fun y => ‖lam y‖) this`. Simplify using `only [map_pow, norm_pow, map_one, norm_one] at h`.

Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h`. Establish `hcn : ‖lam ⟨c, hcQ⟩‖ = 1`. Establish `: (⟨c, hcQ⟩ : Qbar) ^ 2 = ⟨ζ, hζQ⟩ * u` using `Subtype.ext (by simpa using hc)`. Establish `h` using `congrArg (fun y => ‖lam y‖) this`. Simplify using `only [map_pow, norm_pow, map_mul, norm_mul, hun, root ⟨ζ, hζQ⟩ m hm hζ, mul_one] at h`.

Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h`. Establish `: (⟨κ, hκQ⟩ : Qbar) * ⟨ε, hε⟩ = ⟨ε', hε'⟩ * ⟨c, hcQ⟩ * ⟨μ, hμQ⟩` using `Subtype.ext key`. Establish `h` using `congrArg (fun y => ‖lam y‖) this`. Simplify `h` using `only [map_mul, norm_mul, hεn, hεn', hcn, root ⟨μ, hμQ⟩ 8 (by norm_num) hμ, mul_one]`.
-/
theorem at_place (hI : GlobalTheory.NormSum.Inp D) {δ t0 : ℂ} (hC : Crv D ⊤ δ) (ht : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0)
    {e₁ e₂ : VC D N N' → ℂ} (h₁ : oddE0 D ⊤ δ t0 N N' e₁) (h₂ : oddE0 D ⊤ δ t0 N N' e₂) (hne : e₁ ≠ 0) {κ : ℂ}
    (hκ : e₂ = κ • e₁) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : κ ∈ Qbar ∧ ‖lamC lam κ‖ = 1 := by
  have hSD : ∀ n, Formalism.MainNotions.StandardLatticesGL3.SD D (stdL D n) := fun n => by
    obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D n
    exact h2 ▸ (h1 1).2
  obtain ⟨b, ε, hb, hl, hε, hεn, -, he⟩ := h₁.2.2.2.2 p lam (by simp)
  obtain ⟨b', ε', hb', hl', hε', hεn', -, he'⟩ := h₂.2.2.2.2 p lam (by simp)
  obtain ⟨c, ζ, m, hm, hζ, hc, hpull⟩ := GlobalTheory.UnitaryTheta.const_sq_eq_det D ⊤ δ hC t0 ht N N' _ b b' hb hb'
  obtain ⟨μ, hμ, hI3⟩ := hI.mu ⊤ δ hC N N' _ _ (La0 D (tor0 D ⊤ δ) N N') (Or.inl ⟨_, b, hb, rfl⟩)
    (Or.inl ⟨_, b', hb', rfl⟩) (Or.inr ⟨_, _, hSD N, hSD N', rfl⟩) _
    (GlobalTheory.UnitaryTheta.pullB_mem D ⊤ δ hC t0 ht N N' _ b hb).1
  obtain ⟨z, hz⟩ := Function.ne_iff.1 hne
  have e2 := congrFun hκ z
  rw [he', hpull, Pi.smul_apply, smul_eq_mul] at e2
  rw [he] at e2 hz
  simp only [GlobalTheory.UnitaryTheta.iop_smul, hI3] at e2
  have hz' := right_ne_zero_of_mul hz
  have key : κ * ε = ε' * c * μ := by
    apply mul_right_cancel₀ hz'
    linear_combination -e2
  have hζQ : ζ ∈ Qbar := mem_Qbar_of_pow hm (hζ ▸ one_mem _)
  have hμQ : μ ∈ Qbar := mem_Qbar_of_pow (n := 8) (by norm_num) (hμ ▸ one_mem _)
  set u := phiK D (Matrix.of fun i j => hYY D (b' j) (b i)).det with hu
  have hun : ‖lam u‖ = 1 := norm_det_eq_one (lam.comp (phiK D)) hb hl hl'
  change c ^ 2 = ζ * (u : ℂ) at hc
  have hcQ : c ∈ Qbar := mem_Qbar_of_pow (n := 2) (by norm_num) (hc ▸ mul_mem hζQ u.2)
  rw [lamC, dif_pos hε] at hεn
  rw [lamC, dif_pos hε'] at hεn'
  have hε0 : ε ≠ 0 := left_ne_zero_of_mul hz
  have hκQ : κ ∈ Qbar := by
    rw [eq_div_of_mul_eq hε0 key]
    exact div_mem (mul_mem (mul_mem hε' hcQ) hμQ) hε
  refine ⟨hκQ, ?_⟩
  rw [lamC, dif_pos hκQ]
  have root : ∀ (x : Qbar) (n : ℕ), 0 < n → (x : ℂ) ^ n = 1 → ‖lam x‖ = 1 := by
    intro x n hn hx
    have : x ^ n = 1 := Subtype.ext (by simpa using hx)
    have h := congrArg (fun y => ‖lam y‖) this
    simp only [map_pow, norm_pow, map_one, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h
  have hcn : ‖lam ⟨c, hcQ⟩‖ = 1 := by
    have : (⟨c, hcQ⟩ : Qbar) ^ 2 = ⟨ζ, hζQ⟩ * u := Subtype.ext (by simpa using hc)
    have h := congrArg (fun y => ‖lam y‖) this
    simp only [map_pow, norm_pow, map_mul, norm_mul, hun, root ⟨ζ, hζQ⟩ m hm hζ, mul_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  have : (⟨κ, hκQ⟩ : Qbar) * ⟨ε, hε⟩ = ⟨ε', hε'⟩ * ⟨c, hcQ⟩ * ⟨μ, hμQ⟩ := Subtype.ext key
  have h := congrArg (fun y => ‖lam y‖) this
  simpa only [map_mul, norm_mul, hεn, hεn', hcn, root ⟨μ, hμQ⟩ 8 (by norm_num) hμ, mul_one] using h

/- English proof (translation)
Introduce `D hI δ t0 hC ht N N' e₁ e₂ h₁ h₂ hne κ hκ`. Use `⟨?_, fun p _ lam => (at_place hI hC ht h₁ h₂ hne hκ p lam).2⟩` and prove the remaining obligations. Use `haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩`. Use `haveI : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ`. Conclude with `(at_place hI hC ht h₁ h₂ hne hκ 2 (IsAlgClosed.lift (R := ℚ) (S := Qbar) (M := ℂ_[2])).toRingHom).1`.
-/
theorem vac_unit : ∀ {D : D7}, GlobalTheory.NormSum.Inp D → ∀ {δ t0 : ℂ}, Crv D ⊤ δ → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → ∀ {N N' : ℕ} {e₁ e₂ : VC D N N' → ℂ},
  oddE0 D ⊤ δ t0 N N' e₁ → oddE0 D ⊤ δ t0 N N' e₂ → e₁ ≠ 0 → ∀ κ : ℂ, e₂ = κ • e₁ →
  κ ∈ Qbar ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ‖lamC lam κ‖ = 1 := by
  intro D hI δ t0 hC ht N N' e₁ e₂ h₁ h₂ hne κ hκ
  refine ⟨?_, fun p _ lam => (at_place hI hC ht h₁ h₂ hne hκ p lam).2⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  exact (at_place hI hC ht h₁ h₂ hne hκ 2 (IsAlgClosed.lift (R := ℚ) (S := Qbar) (M := ℂ_[2])).toRingHom).1

end GlobalTheory.VacUnit

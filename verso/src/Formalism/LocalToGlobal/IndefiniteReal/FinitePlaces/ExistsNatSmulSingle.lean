import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PairingRankOneMemInverseDifferent
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsNatSmulMem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin.PDA

open Formalism.IndefR.Fin Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Use `⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩` and prove the remaining obligations. Establish `: Ideal.absNorm (Ideal.span {b}) ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`. Conclude with `hb`. Use linear arithmetic over natural numbers and integers.

Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))`. Conclude with `⟨c, by rw [← hc, mul_comm]⟩`.
-/
theorem exists_nat_eq_mul {K : Type} [Field K] [NumberField K] (b : 𝓞 K) (hb : b ≠ 0) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ c : 𝓞 K, (m : 𝓞 K) = b * c := by
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · have : Ideal.absNorm (Ideal.span {b}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb
    omega
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
    exact ⟨c, by rw [← hc, mul_comm]⟩

/- English proof (translation)
Take `⟨⟨a, b⟩, h⟩` from `IsLocalization.surj (nonZeroDivisors (𝓞 K)) e`. Take `⟨m, hm, c, hc⟩` from `exists_nat_eq_mul (b : 𝓞 K) (nonZeroDivisors.ne_zero b.2)`. Use `⟨m, hm, a * c, ?_⟩` and prove the remaining obligations. Establish `h1 : (m : K) = algebraMap (𝓞 K) K b * algebraMap (𝓞 K) K c`. Rewrite using `[← map_mul, ← hc, map_natCast]`.

Simplify using `only at h`. Rewrite using `[map_mul, h1, ← h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_nat_mul_mem {K : Type} [Field K] [NumberField K] (e : K) :
    ∃ m : ℕ, 1 ≤ m ∧ (m : K) * e ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) e
  obtain ⟨m, hm, c, hc⟩ := exists_nat_eq_mul (b : 𝓞 K) (nonZeroDivisors.ne_zero b.2)
  refine ⟨m, hm, a * c, ?_⟩
  have h1 : (m : K) = algebraMap (𝓞 K) K b * algebraMap (𝓞 K) K c := by
    rw [← map_mul, ← hc, map_natCast]
  simp only at h
  rw [map_mul, h1, ← h]
  ring

/- English proof (translation)
Use `choose k hk hPk using h`. Use `⟨∏ i, k i, Finset.prod_pos fun i _ => hk i, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]`. Conclude with `hP i _ _ (hPk i)`.
-/
lemma uniform_nat {ι : Type*} [Fintype ι] (P : ι → ℕ → Prop) (hP : ∀ i k m, P i k → P i (m * k))
    (h : ∀ i, ∃ k, 0 < k ∧ P i k) : ∃ k, 0 < k ∧ ∀ i, P i k := by
  classical
  choose k hk hPk using h
  refine ⟨∏ i, k i, Finset.prod_pos fun i _ => hk i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  exact hP i _ _ (hPk i)

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.ExistsNatSmulMem.exists_nat_smul_mem hΛ x`.
-/
lemma exists_nat_smul_mem {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hΛ : Submodule.IsLattice D.host.E Λ) (x : Fin n → D.host.E) :
    ∃ N : ℕ, 0 < N ∧ (N : D.host.E) • x ∈ Λ :=
  _root_.UpperTheory.Reformulated.B.ExistsNatSmulMem.exists_nat_smul_mem hΛ x

/- English proof (translation)
Use `uniform_nat (fun j m => (m : D.host.E) • (Pi.single j 1 : Fin n → D.host.E) ∈ Λ) (fun j k m h => ?_) (fun j => exists_nat_smul_mem hΛ _)` and prove the remaining obligations. Rewrite using `[Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul]`. Conclude with `Λ.nsmul_mem h m`.
-/
lemma exists_nat_smul_single {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hΛ : Submodule.IsLattice D.host.E Λ) :
    ∃ m : ℕ, 0 < m ∧ ∀ j, (m : D.host.E) • (Pi.single j 1 : Fin n → D.host.E) ∈ Λ := by
  refine uniform_nat (fun j m => (m : D.host.E) • (Pi.single j 1 : Fin n → D.host.E) ∈ Λ) (fun j k m h => ?_)
    (fun j => exists_nat_smul_mem hΛ _)
  rw [Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul]
  exact Λ.nsmul_mem h m

/- English proof (translation)
The claim follows from `uniform_nat (fun j c => (c : D.host.E) * v j ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) (fun j k m h => by push_cast; rw [mul_assoc]; exact mul_mem (natCast_mem _ m) h) (fun j => by obtain ⟨m, hm, h⟩ := exists_nat_mul_mem (v j); exact ⟨m, hm, h⟩)`.
-/
lemma exists_nat_denom {n : ℕ} (v : Fin n → D.host.E) :
    ∃ c : ℕ, 0 < c ∧ ∀ j, (c : D.host.E) * v j ∈ (algebraMap (𝓞 D.host.E) D.host.E).range :=
  uniform_nat (fun j c => (c : D.host.E) * v j ∈ (algebraMap (𝓞 D.host.E) D.host.E).range)
    (fun j k m h => by push_cast; rw [mul_assoc]; exact mul_mem (natCast_mem _ m) h)
    (fun j => by obtain ⟨m, hm, h⟩ := exists_nat_mul_mem (v j); exact ⟨m, hm, h⟩)

/- English proof (translation)
Establish `: Module.Finite (𝓞 D.host.E) Λ` using `Module.Finite.iff_fg.2 hΛ.fg`. Establish `: Module.Flat (𝓞 D.host.E) Λ`. Rewrite using `[IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]`. Introduce `x hx`. Take `⟨a, ha⟩` from `(Submodule.mem_torsion_iff x).1 hx`.

Rewrite using `[Submodule.mem_bot]`. Rewrite `ha` using `[Submonoid.smul_def]`. Conclude with `(smul_eq_zero.1 ha).resolve_left (nonZeroDivisors.coe_ne_zero a)`. Establish `: Module.FinitePresentation (𝓞 D.host.E) Λ` using `Module.finitePresentation_of_finite _ _`. Conclude with `Module.Flat.projective_of_finitePresentation`.
-/
theorem lattice_projective {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hΛ : Submodule.IsLattice D.host.E Λ) : Module.Projective (𝓞 D.host.E) Λ := by
  have : Module.Finite (𝓞 D.host.E) Λ := Module.Finite.iff_fg.2 hΛ.fg
  have : Module.Flat (𝓞 D.host.E) Λ := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).1 hx
    rw [Submodule.mem_bot]
    rw [Submonoid.smul_def] at ha
    exact (smul_eq_zero.1 ha).resolve_left (nonZeroDivisors.coe_ne_zero a)
  have : Module.FinitePresentation (𝓞 D.host.E) Λ := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

/- English proof (translation)
Simplify using `only [hF, dotProduct, mulVec, Finset.mul_sum, mul_assoc]`.
-/
theorem hF_eq_dot (S : HSp D) (x y : Fin S.rank → D.host.E) :
    hF S x y = (fun a => star (x a)) ⬝ᵥ (S.gram *ᵥ y) := by
  simp only [hF, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Unfold `hF`. Simplify using `only [star_sum, star_mul', star_star, star_gram]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hF_swap (S : HSp D) (x y : Fin S.rank → D.host.E) : hF S x y = star (hF S y x) := by
  unfold hF
  simp only [star_sum, star_mul', star_star, star_gram]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

def repV (S : HSp D) (w : Fin S.rank → D.host.E) : Fin S.rank → D.host.E :=
  fun k => star ((w ᵥ* S.gram⁻¹) k)

/- English proof (translation)
Establish `h1 : S.gram⁻¹ * S.gram = 1` using `Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (Formalism.MainNotions.S.Inh.tie_gram_det_ne S))`. Establish `h2 : (fun a => star (repV S w a)) = w ᵥ* S.gram⁻¹`. Use function extensionality and compare the values at `a`. Simplify using `[repV]`. Rewrite using `[hF_eq_dot, h2, dotProduct_mulVec, vecMul_vecMul, h1, vecMul_one]`.
-/
theorem hF_repV (S : HSp D) (w v : Fin S.rank → D.host.E) : hF S (repV S w) v = w ⬝ᵥ v := by
  have h1 : S.gram⁻¹ * S.gram = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (Formalism.MainNotions.S.Inh.tie_gram_det_ne S))
  have h2 : (fun a => star (repV S w a)) = w ᵥ* S.gram⁻¹ := by
    funext a; simp [repV]
  rw [hF_eq_dot, h2, dotProduct_mulVec, vecMul_vecMul, h1, vecMul_one]

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Use `lattice_projective hS.1` as an intermediate fact. Establish `: Module.Finite (𝓞 D.host.E) ΛS` using `Module.Finite.iff_fg.2 hS.1.fg`. Take `⟨N, f, hf⟩` from `Module.Finite.exists_fin' (𝓞 D.host.E) ΛS`. Take `⟨σ, hσ⟩` from `Module.projective_lifting_property f LinearMap.id hf`. Set `gg : Fin N → ΛS` to `fun i => f (fun j => if i = j then 1 else 0)`.

Establish `hrep : ∀ x : ΛS, ∑ i, σ x i • gg i = x`. Introduce `x`. Establish `h1 : f (σ x) = x` using `LinearMap.congr_fun hσ x`. Establish `h2 : f (σ x) = ∑ i, σ x i • gg i` using `by conv_lhs => rw [pi_eq_sum_univ (σ x)]`. Rewrite using `[map_sum]`.

Simplify using `only [map_smul, gg]`. Rewrite using `[← h2, h1]`. Set `A` to `algebraMap (𝓞 D.host.E) D.host.E`. Take `⟨m, hm, hmS⟩` from `exists_nat_smul_single hS.1`. Establish `hm0 : (m : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 hm.ne'`.

Set `em : Fin S.rank → ΛS` to `fun j => ⟨(m : D.host.E) • (Pi.single j 1 : Fin S.rank → D.host.E), hmS j⟩`. Set `w : Fin N → Fin S.rank → D.host.E` to `fun i j => A (σ (em j) i) / m`. Establish `hw : ∀ i j, A (σ (em j) i) = m * w i j`. Introduce `i j`. Simplify using `only [w]`.

Clear the denominators using the available nonvanishing facts. Establish `hagree : ∀ (x : ΛS) (i : Fin N), A (σ x i) = w i ⬝ᵥ (x : Fin S.rank → D.host.E)`. Introduce `x i`. Take `⟨c, hc, hcx⟩` from `exists_nat_denom (x : Fin S.rank → D.host.E)`. Establish `hcx' : ∀ j, ∃ y, A y = (c : D.host.E) * (x : Fin S.rank → D.host.E) j` using `fun j => RingHom.mem_range.1 (hcx j)`.

Use `choose o ho using hcx'`. Establish `hc0 : (c : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 hc.ne'`. Establish `hx : ((c * m : ℕ) : 𝓞 D.host.E) • x = ∑ j, o j • em j`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `k`.

Simplify using `only [Submodule.coe_smul, Submodule.coe_sum, Finset.sum_apply, Pi.smul_apply, em]`. Rewrite using `[Finset.sum_eq_single k (fun j _ hj => by simp [Ne.symm hj]) (by simp)]`. Simplify using `only [Pi.single_eq_same, smul_eq_mul, mul_one, Algebra.smul_def]`. Use `ho k` as an intermediate fact. Simplify using `only [A] at this`.

Rewrite using `[map_natCast, this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h3` using `congrArg (fun y => A (σ y i)) hx`. Simplify using `only [map_smul, map_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, map_mul, map_natCast] at h3`.

Apply `mul_left_cancel₀ (mul_ne_zero hc0 hm0)` to reduce the goal to its premises. Rewrite using `[dotProduct, Finset.mul_sum]`. Establish `e1 : ((c * m : ℕ) : D.host.E) = (c : D.host.E) * m` using `by push_cast; ring`. Rewrite `h3` using `[e1]`. Rewrite using `[h3]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[ho j, hw i j]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcol : ∀ j, ∑ i, w i j • (gg i : Fin S.rank → D.host.E) = Pi.single j 1`. Introduce `j`.

Establish `h` using `congrArg (fun y : ΛS => (y : Fin S.rank → D.host.E)) (hrep (em j))`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h`. Establish `h' : ∑ i, A (σ (em j) i) • (gg i : Fin S.rank → D.host.E) = (m : D.host.E) • Pi.single j 1` using `(Finset.sum_congr rfl fun i _ => algebraMap_smul D.host.E _ _).trans h`. Simplify using `only [hw, mul_smul, ← Finset.smul_sum] at h'`. Conclude with `smul_right_injective _ hm0 h'`.

Use `⟨N, fun i => (gg i : Fin S.rank → D.host.E), fun i => repV S (w i), fun i => (gg i).2, fun i => ?_, fun v => ?_⟩` and prove the remaining obligations. Use `(hS.2 (repV S (w i))).2 fun x hx => ⟨starO (σ ⟨x, hx⟩ i), ?_⟩` and prove the remaining obligations. Rewrite using `[coe_starO]`. Use `show star (A (σ ⟨x, hx⟩ i)) = hF S x (repV S (w i))`. Rewrite using `[hF_swap, hF_repV, hagree]`.

Simplify using `only [hF_repV, dotProduct, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, mul_comm]`. Use `_ = ∑ j, v j • (Pi.single j 1 : Fin S.rank → D.host.E) := by simp only [hcol]`. Use `_ = v := by`. Use function extensionality and compare the values at `k`.

Simplify using `[Finset.sum_apply, Pi.single_apply]`.
-/
theorem selfDual_basis (S : HSp D) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (hS : IsSelfDualC S ΛS) :
    ∃ (N : ℕ) (g s' : Fin N → Fin S.rank → D.host.E), (∀ i, g i ∈ ΛS) ∧ (∀ i, s' i ∈ ΛS) ∧
      ∀ v : Fin S.rank → D.host.E, ∑ i, hF S (s' i) v • g i = v := by
  classical
  have := lattice_projective hS.1
  have : Module.Finite (𝓞 D.host.E) ΛS := Module.Finite.iff_fg.2 hS.1.fg
  obtain ⟨N, f, hf⟩ := Module.Finite.exists_fin' (𝓞 D.host.E) ΛS
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property f LinearMap.id hf
  let gg : Fin N → ΛS := fun i => f (fun j => if i = j then 1 else 0)
  have hrep : ∀ x : ΛS, ∑ i, σ x i • gg i = x := by
    intro x
    have h1 : f (σ x) = x := LinearMap.congr_fun hσ x
    have h2 : f (σ x) = ∑ i, σ x i • gg i := by
      conv_lhs => rw [pi_eq_sum_univ (σ x)]
      rw [map_sum]
      simp only [map_smul, gg]
    rw [← h2, h1]
  let A := algebraMap (𝓞 D.host.E) D.host.E
  obtain ⟨m, hm, hmS⟩ := exists_nat_smul_single hS.1
  have hm0 : (m : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  let em : Fin S.rank → ΛS := fun j => ⟨(m : D.host.E) • (Pi.single j 1 : Fin S.rank → D.host.E), hmS j⟩
  let w : Fin N → Fin S.rank → D.host.E := fun i j => A (σ (em j) i) / m
  have hw : ∀ i j, A (σ (em j) i) = m * w i j := by
    intro i j; simp only [w]; field_simp

  have hagree : ∀ (x : ΛS) (i : Fin N), A (σ x i) = w i ⬝ᵥ (x : Fin S.rank → D.host.E) := by
    intro x i
    obtain ⟨c, hc, hcx⟩ := exists_nat_denom (x : Fin S.rank → D.host.E)
    have hcx' : ∀ j, ∃ y, A y = (c : D.host.E) * (x : Fin S.rank → D.host.E) j := fun j => RingHom.mem_range.1 (hcx j)
    choose o ho using hcx'
    have hc0 : (c : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
    have hx : ((c * m : ℕ) : 𝓞 D.host.E) • x = ∑ j, o j • em j := by
      apply Subtype.ext
      funext k
      simp only [Submodule.coe_smul, Submodule.coe_sum, Finset.sum_apply, Pi.smul_apply, em]
      rw [Finset.sum_eq_single k (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
      simp only [Pi.single_eq_same, smul_eq_mul, mul_one, Algebra.smul_def]
      have := ho k
      simp only [A] at this
      rw [map_natCast, this]
      push_cast; ring
    have h3 := congrArg (fun y => A (σ y i)) hx
    simp only [map_smul, map_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, map_mul, map_natCast] at h3
    apply mul_left_cancel₀ (mul_ne_zero hc0 hm0)
    rw [dotProduct, Finset.mul_sum]
    have e1 : ((c * m : ℕ) : D.host.E) = (c : D.host.E) * m := by push_cast; ring
    rw [e1] at h3
    rw [h3]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ho j, hw i j]; ring

  have hcol : ∀ j, ∑ i, w i j • (gg i : Fin S.rank → D.host.E) = Pi.single j 1 := by
    intro j
    have h := congrArg (fun y : ΛS => (y : Fin S.rank → D.host.E)) (hrep (em j))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    have h' : ∑ i, A (σ (em j) i) • (gg i : Fin S.rank → D.host.E) = (m : D.host.E) • Pi.single j 1 :=
      (Finset.sum_congr rfl fun i _ => algebraMap_smul D.host.E _ _).trans h
    simp only [hw, mul_smul, ← Finset.smul_sum] at h'
    exact smul_right_injective _ hm0 h'
  refine ⟨N, fun i => (gg i : Fin S.rank → D.host.E), fun i => repV S (w i), fun i => (gg i).2, fun i => ?_, fun v => ?_⟩
  · refine (hS.2 (repV S (w i))).2 fun x hx => ⟨starO (σ ⟨x, hx⟩ i), ?_⟩
    rw [coe_starO]
    show star (A (σ ⟨x, hx⟩ i)) = hF S x (repV S (w i))
    rw [hF_swap, hF_repV, hagree]
  · simp only [hF_repV, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    calc ∑ j, ∑ i, (w i j * v j) • (gg i : Fin S.rank → D.host.E)
        = ∑ j, v j • ∑ i, w i j • (gg i : Fin S.rank → D.host.E) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul, mul_comm]
      _ = ∑ j, v j • (Pi.single j 1 : Fin S.rank → D.host.E) := by simp only [hcol]
      _ = v := by
          funext k
          simp [Finset.sum_apply, Pi.single_apply]

end Formalism.IndefR.Fin.PDA

end

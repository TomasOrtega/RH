import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.TauCentralScalar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.GrpNorm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.DvTransferIdxOf

noncomputable section

namespace PI.Dv.TIW

open PI.Dv NumberField

section Orth

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] (T : GoodSet K G)

/- English proof (translation)
Simplify using `[MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single_apply, Finsupp.single_apply]`.
-/
theorem coeff_sum_of (a : G → K) (g : G) :
    (∑ y : G, a y • MonoidAlgebra.of K G y).coeff g = a g := by
  classical
  simp [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.of_apply,
    MonoidAlgebra.coeff_single_apply, Finsupp.single_apply]

/- English proof (translation)
Introduce `h`. Use `tau_eS T s` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `zero_ne_one this`.
-/
theorem eS_ne_zero (s : T.S) : eS T s ≠ 0 := by
  intro h
  have := tau_eS T s
  rw [h, map_zero] at this
  exact zero_ne_one this

/- English proof (translation)
Take `⟨μ, hμ⟩` from `tau_central_scalar T t (eS T s) (fun z => eS_central T s z)`. Take `⟨ν, hν⟩` from `tau_central_scalar T s (eS T t) (fun z => eS_central T t z)`. Establish `h1 : eS T s * eS T t = μ • eS T t` using `by rw [mul_eS T t, hμ, theta_smul, theta_one]`. Establish `h2 : eS T s * eS T t = ν • eS T s`. Rewrite using `[← eS_central T t (eS T s), mul_eS T s, hν, theta_smul, theta_one]`.

Assume the negation of the conclusion as `hne`. Establish `hμ0 : μ ≠ 0` using `fun h => hne (by rw [h1, h, zero_smul])`. Establish `h3 : eS T t = (μ⁻¹ * ν) • eS T s`. Rewrite using `[mul_smul, ← h2, h1, smul_smul, inv_mul_cancel₀ hμ0, one_smul]`. Use `set κ := μ⁻¹ * ν with hκ`.

Establish `hsne` using `eS_ne_zero T s`. Establish `htne` using `eS_ne_zero T t`. Establish `h4 : κ = 1`. Establish `e1 : eS T t = (κ * κ) • eS T s` using `by conv_lhs => rw [← eS_idem T t, h3]`. Rewrite using `[smul_mul_smul_comm, eS_idem]`.

Establish `e2 : (κ * κ - κ) • eS T s = 0` using `by rw [sub_smul, ← e1, ← h3, sub_self]`. Break down `smul_eq_zero.mp e2 with h | h` into its components or cases. Establish `hκ0 : κ ≠ 0` using `fun h0 => htne (by rw [h3, h0, zero_smul])`. Establish `: κ * (κ - 1) = 0` using `by rw [mul_sub, mul_one]; exact h`. Break down `mul_eq_zero.mp this with h' | h'` into its components or cases.

Conclude with `absurd h' hκ0`. Conclude with `sub_eq_zero.mp h'`. Conclude with `absurd h hsne`. Establish `h5 : eS T t = eS T s` using `by rw [h3, h4, one_smul]`. Establish `hc : ∀ g : G, (((Module.finrank K (T.W t) : ℕ) : K) / ((Fintype.card G : ℕ) : K) * LinearMap.trace K (T.W t) (T.tau t g⁻¹)) = (((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s g⁻¹))`.

Introduce `g`. Use `congrArg (fun z : MonoidAlgebra K G => z.coeff g) h5` as an intermediate fact. Simplify using `only [eS] at this`. Rewrite `this` using `[coeff_sum_of, coeff_sum_of]`. Then use the resulting hypothesis. Establish `hG0 : ((Fintype.card G : ℕ) : K) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`.

Establish `hd : Module.finrank K (T.W t) = Module.finrank K (T.W s)`. Use `hc 1` as an intermediate fact. Simplify using `only [inv_one, map_one, LinearMap.trace_one] at this`. Clear denominators, using `at this` for the nonvanishing conditions. Establish `h' : ((Module.finrank K (T.W t) ^ 2 : ℕ) : K) = ((Module.finrank K (T.W s) ^ 2 : ℕ) : K)` using `by push_cast; linear_combination this`.

Conclude with `Nat.pow_left_injective (by norm_num : 2 ≠ 0) (by exact_mod_cast h')`. Establish `hdK : ((Module.finrank K (T.W s) : ℕ) : K) ≠ 0`. Establish `: 0 < Module.finrank K (T.W s)` using `Module.finrank_pos`. Conclude with `this.ne'` after adjusting the coercions. Apply `hst` to reduce the goal to its premises.

Apply `T.inj` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Use `hc g⁻¹` as an intermediate fact. Rewrite `this` using `[hd, inv_inv]`. Establish `hne0 : ((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) ≠ 0` using `div_ne_zero hdK hG0`.

Conclude with `(mul_left_cancel₀ hne0 this).symm`.
-/
theorem eS_orth (s t : T.S) (hst : s ≠ t) : eS T s * eS T t = 0 := by
  obtain ⟨μ, hμ⟩ := tau_central_scalar T t (eS T s) (fun z => eS_central T s z)
  obtain ⟨ν, hν⟩ := tau_central_scalar T s (eS T t) (fun z => eS_central T t z)
  have h1 : eS T s * eS T t = μ • eS T t := by rw [mul_eS T t, hμ, theta_smul, theta_one]
  have h2 : eS T s * eS T t = ν • eS T s := by
    rw [← eS_central T t (eS T s), mul_eS T s, hν, theta_smul, theta_one]
  by_contra hne
  have hμ0 : μ ≠ 0 := fun h => hne (by rw [h1, h, zero_smul])
  have h3 : eS T t = (μ⁻¹ * ν) • eS T s := by
    rw [mul_smul, ← h2, h1, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  set κ := μ⁻¹ * ν with hκ
  have hsne := eS_ne_zero T s
  have htne := eS_ne_zero T t
  have h4 : κ = 1 := by
    have e1 : eS T t = (κ * κ) • eS T s := by
      conv_lhs => rw [← eS_idem T t, h3]
      rw [smul_mul_smul_comm, eS_idem]
    have e2 : (κ * κ - κ) • eS T s = 0 := by rw [sub_smul, ← e1, ← h3, sub_self]
    rcases smul_eq_zero.mp e2 with h | h
    · have hκ0 : κ ≠ 0 := fun h0 => htne (by rw [h3, h0, zero_smul])
      have : κ * (κ - 1) = 0 := by rw [mul_sub, mul_one]; exact h
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hκ0
      · exact sub_eq_zero.mp h'
    · exact absurd h hsne
  have h5 : eS T t = eS T s := by rw [h3, h4, one_smul]
  have hc : ∀ g : G, (((Module.finrank K (T.W t) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
      LinearMap.trace K (T.W t) (T.tau t g⁻¹)) = (((Module.finrank K (T.W s) : ℕ) : K) /
      ((Fintype.card G : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s g⁻¹)) := by
    intro g
    have := congrArg (fun z : MonoidAlgebra K G => z.coeff g) h5
    simp only [eS] at this
    rwa [coeff_sum_of, coeff_sum_of] at this
  have hG0 : ((Fintype.card G : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hd : Module.finrank K (T.W t) = Module.finrank K (T.W s) := by
    have := hc 1
    simp only [inv_one, map_one, LinearMap.trace_one] at this
    field_simp at this
    have h' : ((Module.finrank K (T.W t) ^ 2 : ℕ) : K) = ((Module.finrank K (T.W s) ^ 2 : ℕ) : K) := by
      push_cast; linear_combination this
    exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) (by exact_mod_cast h')
  have hdK : ((Module.finrank K (T.W s) : ℕ) : K) ≠ 0 := by
    have : 0 < Module.finrank K (T.W s) := Module.finrank_pos
    exact_mod_cast this.ne'
  apply hst
  apply T.inj
  funext g
  have := hc g⁻¹
  rw [hd, inv_inv] at this
  have hne0 : ((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) ≠ 0 := div_ne_zero hdK hG0
  exact (mul_left_cancel₀ hne0 this).symm

/- English proof (translation)
Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `eS_idem T s`. Conclude with `eS_orth T s t h`.
-/
theorem eS_mul_eS (s t : T.S) : eS T s * eS T t = if s = t then eS T s else 0 := by
  split_ifs with h
  · subst h; exact eS_idem T s
  · exact eS_orth T s t h

end Orth

section Eps

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

open Classical in

def chiT (P : Pair K G) (x : G) : K := if h : x ∈ P.H then (((P.chi ⟨x, h⟩)⁻¹ : Kˣ) : K) else 0

def epsS (P : Pair K G) : MonoidAlgebra K G := ∑ x : G, chiT P x • MonoidAlgebra.of K G x

/- English proof (translation)
Rewrite using `[eps, epsS]`. Use `congr 1`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ P.H`. Simplify using `only [chiT, dif_pos hx]`.

Simplify using `only [chiT, dif_neg hx, zero_smul]`.
-/
theorem eps_eq (P : Pair K G) : eps P = ((Nat.card P.H : ℕ) : K)⁻¹ • epsS P := by
  classical
  rw [eps, epsS]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ P.H
  · simp only [chiT, dif_pos hx]
  · simp only [chiT, dif_neg hx, zero_smul]

/- English proof (translation)
Distinguish the cases in `hx : x ∈ P.H`. Establish `hhx : (h : G) * x ∈ P.H` using `P.H.mul_mem h.2 hx`. Simplify using `only [chiT, dif_pos hx, dif_pos hhx]`. Establish `: (⟨(h : G) * x, hhx⟩ : P.H) = h * ⟨x, hx⟩` using `rfl`. Rewrite using `[this, map_mul, mul_inv_rev, Units.val_mul, ← mul_assoc, mul_right_comm, Units.mul_inv, one_mul]`.

Establish `hhx : (h : G) * x ∉ P.H` using `fun hh => hx (by simpa using P.H.mul_mem (P.H.inv_mem h.2) hh)`. Simplify using `only [chiT, dif_neg hx, dif_neg hhx, mul_zero]`.
-/
theorem chiT_mul (P : Pair K G) (h : P.H) (x : G) :
    chiT P x = ((P.chi h : Kˣ) : K) * chiT P ((h : G) * x) := by
  classical
  by_cases hx : x ∈ P.H
  · have hhx : (h : G) * x ∈ P.H := P.H.mul_mem h.2 hx
    simp only [chiT, dif_pos hx, dif_pos hhx]
    have : (⟨(h : G) * x, hhx⟩ : P.H) = h * ⟨x, hx⟩ := rfl
    rw [this, map_mul, mul_inv_rev, Units.val_mul, ← mul_assoc, mul_right_comm, Units.mul_inv, one_mul]
  · have hhx : (h : G) * x ∉ P.H := fun hh => hx (by simpa using P.H.mul_mem (P.H.inv_mem h.2) hh)
    simp only [chiT, dif_neg hx, dif_neg hhx, mul_zero]

/- English proof (translation)
Simplify using `only [chiT, dif_pos hx]`.
-/
theorem chiT_of_mem (P : Pair K G) (x : G) (hx : x ∈ P.H) :
    chiT P x = (((P.chi ⟨x, hx⟩)⁻¹ : Kˣ) : K) := by
  classical
  simp only [chiT, dif_pos hx]

/- English proof (translation)
Simplify using `only [chiT, dif_neg hx]`.
-/
theorem chiT_of_not_mem (P : Pair K G) (x : G) (hx : x ∉ P.H) : chiT P x = 0 := by
  classical
  simp only [chiT, dif_neg hx]

/- English proof (translation)
Rewrite using `[epsS, Finset.mul_sum, Finset.smul_sum]`. Use `Fintype.sum_equiv (Equiv.mulLeft (h : G)) _ _ (fun x => ?_)` and prove the remaining obligations. Simplify using `only [Equiv.coe_mulLeft]`. Rewrite using `[mul_smul_comm, ← map_mul, smul_smul, ← chiT_mul]`.
-/
theorem of_mul_epsS (P : Pair K G) (h : P.H) :
    MonoidAlgebra.of K G (h : G) * epsS P = ((P.chi h : Kˣ) : K) • epsS P := by
  rw [epsS, Finset.mul_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (h : G)) _ _ (fun x => ?_)
  simp only [Equiv.coe_mulLeft]
  rw [mul_smul_comm, ← map_mul, smul_smul, ← chiT_mul]

/- English proof (translation)
The claim follows from `Nat.card_pos`.
-/
theorem card_H_pos (P : Pair K G) : 0 < Nat.card P.H := Nat.card_pos

/- English proof (translation)
Use `nth_rewrite 1 [epsS]`. Rewrite using `[Finset.sum_mul]`. Establish `: ∀ x : G, (chiT P x • MonoidAlgebra.of K G x) * epsS P = (if x ∈ P.H then (1 : K) else 0) • epsS P`. Introduce `x`. Distinguish the cases in `hx : x ∈ P.H`.

Rewrite using `[if_pos hx, smul_mul_assoc, of_mul_epsS P ⟨x, hx⟩, smul_smul, chiT_of_mem P x hx, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero _)]`. Rewrite using `[if_neg hx, chiT_of_not_mem P x hx, zero_smul, zero_mul, zero_smul]`. Rewrite using `[Finset.sum_congr rfl fun x _ => this x, ← Finset.sum_smul, Finset.sum_boole]`. Use `congr 1`. Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_subtype]`.
-/
theorem epsS_mul_epsS (P : Pair K G) : epsS P * epsS P = ((Nat.card P.H : ℕ) : K) • epsS P := by
  classical
  nth_rewrite 1 [epsS]
  rw [Finset.sum_mul]
  have : ∀ x : G, (chiT P x • MonoidAlgebra.of K G x) * epsS P = (if x ∈ P.H then (1 : K) else 0) • epsS P := by
    intro x
    by_cases hx : x ∈ P.H
    · rw [if_pos hx, smul_mul_assoc, of_mul_epsS P ⟨x, hx⟩, smul_smul, chiT_of_mem P x hx,
        Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero _)]
    · rw [if_neg hx, chiT_of_not_mem P x hx, zero_smul, zero_mul, zero_smul]
  rw [Finset.sum_congr rfl fun x _ => this x, ← Finset.sum_smul, Finset.sum_boole]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/- English proof (translation)
Rewrite using `[eps_eq, smul_mul_smul_comm, epsS_mul_epsS, smul_smul]`. Establish `: ((Nat.card P.H : ℕ) : K) ≠ 0` using `by exact_mod_cast (card_H_pos P).ne'`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.
-/
theorem eps_idem (P : Pair K G) : eps P * eps P = eps P := by
  rw [eps_eq, smul_mul_smul_comm, epsS_mul_epsS, smul_smul]
  have : ((Nat.card P.H : ℕ) : K) ≠ 0 := by exact_mod_cast (card_H_pos P).ne'
  congr 1
  field_simp

/- English proof (translation)
Rewrite using `[eps_eq, smul_mul_assoc, epsS_mul_epsS, smul_smul]`. Establish `: ((Nat.card P.H : ℕ) : K) ≠ 0` using `by exact_mod_cast (card_H_pos P).ne'`. Rewrite using `[inv_mul_cancel₀ this, one_smul]`.
-/
theorem eps_mul_epsS (P : Pair K G) : eps P * epsS P = epsS P := by
  rw [eps_eq, smul_mul_assoc, epsS_mul_epsS, smul_smul]
  have : ((Nat.card P.H : ℕ) : K) ≠ 0 := by exact_mod_cast (card_H_pos P).ne'
  rw [inv_mul_cancel₀ this, one_smul]

end Eps

section RankOne

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/- English proof (translation)
Take `⟨v, hv0, hv⟩` from `finrank_eq_one_iff'.mp h1`. Take `⟨β, hβ⟩` from `hv ⟨p (X v), LinearMap.mem_range_self p _⟩`. Establish `hβ' : p (X v) = β • (v : W)`. Use `congrArg Subtype.val hβ` as an intermediate fact. Simplify using `using this.symm`.

Establish `key : p * X * p = β • p`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `w`. Take `⟨c, hc⟩` from `hv ⟨p w, LinearMap.mem_range_self p w⟩`. Establish `hc' : p w = c • (v : W)` using `by have := congrArg Subtype.val hc; simpa using this.symm`.

Simplify using `only [Module.End.mul_apply, LinearMap.smul_apply]`. Rewrite using `[hc', map_smul, map_smul, hβ', smul_comm]`. Establish `htp : LinearMap.trace K W p = 1`. Rewrite using `[(LinearMap.IsIdempotentElem.isProj_range p hp).trace, h1, Nat.cast_one]`. Establish `htr : LinearMap.trace K W (p * X) = β`.

Establish `: LinearMap.trace K W (p * X * p) = LinearMap.trace K W (p * X)`. Rewrite using `[LinearMap.trace_mul_comm, ← mul_assoc, hp]`. Rewrite using `[← this, key, map_smul, htp, smul_eq_mul, mul_one]`. Rewrite using `[htr, key]`.
-/
theorem rank_one_sandwich (p : Module.End K W) (hp : p * p = p) (h1 : Module.finrank K (LinearMap.range p) = 1)
    (X : Module.End K W) : p * X * p = LinearMap.trace K W (p * X) • p := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp h1
  obtain ⟨β, hβ⟩ := hv ⟨p (X v), LinearMap.mem_range_self p _⟩
  have hβ' : p (X v) = β • (v : W) := by
    have := congrArg Subtype.val hβ; simpa using this.symm
  have key : p * X * p = β • p := by
    apply LinearMap.ext; intro w
    obtain ⟨c, hc⟩ := hv ⟨p w, LinearMap.mem_range_self p w⟩
    have hc' : p w = c • (v : W) := by have := congrArg Subtype.val hc; simpa using this.symm
    simp only [Module.End.mul_apply, LinearMap.smul_apply]
    rw [hc', map_smul, map_smul, hβ', smul_comm]
  have htp : LinearMap.trace K W p = 1 := by
    rw [(LinearMap.IsIdempotentElem.isProj_range p hp).trace, h1, Nat.cast_one]
  have htr : LinearMap.trace K W (p * X) = β := by
    have : LinearMap.trace K W (p * X * p) = LinearMap.trace K W (p * X) := by
      rw [LinearMap.trace_mul_comm, ← mul_assoc, hp]
    rw [← this, key, map_smul, htp, smul_eq_mul, mul_one]
  rw [htr, key]

end RankOne

section Integral

variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]

def ιO : MonoidAlgebra (𝓞 K) G →ₐ[𝓞 K] MonoidAlgebra K G :=
  MonoidAlgebra.mapAlgHom G (Algebra.ofId (𝓞 K) K)

def IntR (z : MonoidAlgebra K G) : Prop := z ∈ (ιO (K := K) (G := G)).range

/- English proof (translation)
Take `⟨w, rfl⟩` from `hz`. Introduce `g`. Conclude with `⟨w.coeff g, by simp [ιO]⟩`.
-/
theorem intEl_of_intR (z : MonoidAlgebra K G) (hz : IntR z) : IntEl z := by
  obtain ⟨w, rfl⟩ := hz
  intro g
  exact ⟨w.coeff g, by simp [ιO]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨MonoidAlgebra.of (𝓞 K) G g, by simp [ιO, MonoidAlgebra.of_apply]⟩`.
-/
theorem intR_of (g : G) : IntR (MonoidAlgebra.of K G g) :=
  ⟨MonoidAlgebra.of (𝓞 K) G g, by simp [ιO, MonoidAlgebra.of_apply]⟩

/- English proof (translation)
The claim follows from `Subalgebra.mul_mem _ hz hz'`.
-/
theorem intR_mul {z z' : MonoidAlgebra K G} (hz : IntR z) (hz' : IntR z') : IntR (z * z') :=
  Subalgebra.mul_mem _ hz hz'

/- English proof (translation)
The claim follows from `Subalgebra.zero_mem _`.
-/
theorem intR_zero : IntR (0 : MonoidAlgebra K G) := Subalgebra.zero_mem _

/- English proof (translation)
The claim follows from `Subalgebra.sum_mem _ hf`.
-/
theorem intR_sum {ι : Type} (s : Finset ι) (f : ι → MonoidAlgebra K G) (hf : ∀ i ∈ s, IntR (f i)) :
    IntR (∑ i ∈ s, f i) := Subalgebra.sum_mem _ hf

/- English proof (translation)
Take `⟨u, rfl⟩` from `hc`. Rewrite using `[algebraMap_smul]`. Conclude with `Subalgebra.smul_mem _ hz u`.
-/
theorem intR_smul (c : K) (hc : c ∈ Set.range (algebraMap (𝓞 K) K)) {z : MonoidAlgebra K G} (hz : IntR z) :
    IntR (c • z) := by
  obtain ⟨u, rfl⟩ := hc
  rw [algebraMap_smul]
  exact Subalgebra.smul_mem _ hz u

/- English proof (translation)
Assemble the required witnesses or components as `⟨IsIntegralClosure.mk' (𝓞 K) x hx, IsIntegralClosure.algebraMap_mk' _ _ _⟩`.
-/
theorem mem_O_of_isIntegral (x : K) (hx : IsIntegral ℤ x) : x ∈ Set.range (algebraMap (𝓞 K) K) :=
  ⟨IsIntegralClosure.mk' (𝓞 K) x hx, IsIntegralClosure.algebraMap_mk' _ _ _⟩

/- English proof (translation)
The claim follows from `mem_O_of_isIntegral x (IsIntegral.of_pow hn (by rw [hx]; exact isIntegral_one))`.
-/
theorem mem_O_of_pow (x : K) (n : ℕ) (hn : 0 < n) (hx : x ^ n = 1) : x ∈ Set.range (algebraMap (𝓞 K) K) :=
  mem_O_of_isIntegral x (IsIntegral.of_pow hn (by rw [hx]; exact isIntegral_one))

/- English proof (translation)
Rewrite using `[← Fintype.card_pos_iff, NumberField.Embeddings.card]`. Conclude with `Module.finrank_pos`.
-/
theorem exists_embedding : Nonempty (K →+* ℂ) := by
  rw [← Fintype.card_pos_iff, NumberField.Embeddings.card]
  exact Module.finrank_pos

/- English proof (translation)
Rewrite using `[← Units.val_pow_eq_pow_val, inv_pow, ← map_pow, Nat.card_eq_fintype_card, pow_card_eq_one, map_one, inv_one, Units.val_one]`.
-/
theorem chi_inv_pow (P : Pair K G) (h : P.H) : ((((P.chi h)⁻¹ : Kˣ) : K)) ^ (Nat.card P.H) = 1 := by
  classical
  rw [← Units.val_pow_eq_pow_val, inv_pow, ← map_pow, Nat.card_eq_fintype_card, pow_card_eq_one, map_one,
    inv_one, Units.val_one]

/- English proof (translation)
Use `intR_sum _ _ fun x _ => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ P.H`. Rewrite using `[chiT_of_mem P x hx]`. Conclude with `intR_smul _ (mem_O_of_pow _ _ (card_H_pos P) (chi_inv_pow P ⟨x, hx⟩)) (intR_of x)`. Rewrite using `[chiT_of_not_mem P x hx, zero_smul]`.

Conclude with `intR_zero`.
-/
theorem intR_epsS (P : Pair K G) : IntR (epsS P) := by
  refine intR_sum _ _ fun x _ => ?_
  by_cases hx : x ∈ P.H
  · rw [chiT_of_mem P x hx]
    exact intR_smul _ (mem_O_of_pow _ _ (card_H_pos P) (chi_inv_pow P ⟨x, hx⟩)) (intR_of x)
  · rw [chiT_of_not_mem P x hx, zero_smul]; exact intR_zero

/- English proof (translation)
Take `⟨σ⟩` from `exists_embedding (K := K)`. Establish `h` using `(trace_end_finite_order (τ g) (Fintype.card G) Fintype.card_pos (by rw [← map_pow, pow_card_eq_one, map_one]) σ).2`. Conclude with `mem_O_of_isIntegral _ h`.
-/
theorem trace_tau_mem {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (τ : Representation K G W) (g : G) : LinearMap.trace K W (τ g) ∈ Set.range (algebraMap (𝓞 K) K) := by
  obtain ⟨σ⟩ := exists_embedding (K := K)
  have h := (trace_end_finite_order (τ g) (Fintype.card G) Fintype.card_pos
    (by rw [← map_pow, pow_card_eq_one, map_one]) σ).2
  exact mem_O_of_isIntegral _ h

/- English proof (translation)
The claim follows from `(trace_end_finite_order (τ g) (Fintype.card G) Fintype.card_pos (by rw [← map_pow, pow_card_eq_one, map_one]) σ).1`.
-/
theorem norm_trace_tau_le {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (τ : Representation K G W) (g : G) (σ : K →+* ℂ) :
    ‖σ (LinearMap.trace K W (τ g))‖ ≤ Module.finrank K W :=
  (trace_end_finite_order (τ g) (Fintype.card G) Fintype.card_pos
    (by rw [← map_pow, pow_card_eq_one, map_one]) σ).1

/- English proof (translation)
Establish `hG0 : ((Fintype.card G : ℕ) : K) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`. Rewrite using `[eS, Finset.smul_sum]`. Use `intR_sum _ _ fun x _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul]`. Use `intR_smul _ ?_ (intR_of x)` and prove the remaining obligations.

Establish `: ((Fintype.card G : ℕ) : K) * (((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s x⁻¹)) = ((Module.finrank K (T.W s) : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s x⁻¹)`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Take `⟨u, hu⟩` from `trace_tau_mem (T.tau s) x⁻¹`. Conclude with `⟨(Module.finrank K (T.W s) : 𝓞 K) * u, by rw [map_mul, hu, map_natCast]⟩`.
-/
theorem intR_card_eS (T : GoodSet K G) (s : T.S) : IntR (((Fintype.card G : ℕ) : K) • eS T s) := by
  have hG0 : ((Fintype.card G : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [eS, Finset.smul_sum]
  refine intR_sum _ _ fun x _ => ?_
  rw [smul_smul]
  refine intR_smul _ ?_ (intR_of x)
  have : ((Fintype.card G : ℕ) : K) * (((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
      LinearMap.trace K (T.W s) (T.tau s x⁻¹)) =
      ((Module.finrank K (T.W s) : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s x⁻¹) := by
    field_simp
  rw [this]
  obtain ⟨u, hu⟩ := trace_tau_mem (T.tau s) x⁻¹
  exact ⟨(Module.finrank K (T.W s) : 𝓞 K) * u, by rw [map_mul, hu, map_natCast]⟩

end Integral

end PI.Dv.TIW

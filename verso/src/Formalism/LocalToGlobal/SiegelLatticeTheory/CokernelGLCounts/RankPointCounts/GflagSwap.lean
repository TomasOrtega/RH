import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PairingOmegaPrimeZ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Lemmas
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub

noncomputable section

open Matrix Module

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

open Formalism.MainNotions.S Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

/- English proof (translation)
Establish `h1 : ∀ a, ∀ y ∈ F.X, S.hT (F.e a) y = 0`. Introduce `a y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => obtain ⟨b, rfl⟩ := hy`. Conclude with `F.e_iso a b`.

Consider the case `zero => simp`. Consider the case `add y z _ _ h1 h2 => simp [map_add, h1, h2]`. Consider the case `smul c y _ h => simp [map_smul, h]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨a, rfl⟩ := hx`.

Conclude with `h1 a x' hx'`. Consider the case `zero => simp`. Consider the case `add y z _ _ h1 h2 => simp [map_add, LinearMap.add_apply, h1, h2]`. Consider the case `smul c y _ h => simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h]`.
-/
theorem hT_X_X (F : FlagG S r T) {x x' : S.V} (hx : x ∈ F.X) (hx' : x' ∈ F.X) : S.hT x x' = 0 := by
  have h1 : ∀ a, ∀ y ∈ F.X, S.hT (F.e a) y = 0 := by
    intro a y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨b, rfl⟩ := hy; exact F.e_iso a b
    | zero => simp
    | add y z _ _ h1 h2 => simp [map_add, h1, h2]
    | smul c y _ h => simp [map_smul, h]
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h1 a x' hx'
  | zero => simp
  | add y z _ _ h1 h2 => simp [map_add, LinearMap.add_apply, h1, h2]
  | smul c y _ h => simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h]

/- English proof (translation)
Use `first`. Consider the case `exact (S.herm x y).symm`. Consider the case `exact (S.herm.eq x y).symm`. Consider the case `simpa using (S.herm x y).symm`.
-/
private theorem hT_swap_eq_star (x y : S.V) : S.hT y x = star (S.hT x y) := by
  first
  | exact (S.herm x y).symm
  | exact (S.herm.eq x y).symm
  | simpa using (S.herm x y).symm

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, rfl⟩` from `hx`. Rewrite using `[hT_swap_eq_star, F.z_orth a, star_zero]`. Consider the case `zero => simp`.

Consider the case `add y z _ _ h1 h2 => simp [map_add, h1, h2]`. Consider the case `smul c y _ h => simp [map_smul, h]`.
-/
theorem hT_z_X (F : FlagG S r T) {x : S.V} (hx : x ∈ F.X) : S.hT F.z x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [hT_swap_eq_star, F.z_orth a, star_zero]
  | zero => simp
  | add y z _ _ h1 h2 => simp [map_add, h1, h2]
  | smul c y _ h => simp [map_smul, h]

def Qsp (F : FlagG S r T) (H : Submodule E S.V) : Submodule E S.V :=
  Lat.orth S (F.X ⊔ Submodule.span E {F.z} ⊔ H)

/- English proof (translation)
Simplify using `only [Qsp, Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun x hx => h x ?_, h F.z ?_, fun x hx => h x ?_⟩` and prove the remaining obligations. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_left hx)`.

Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))`. Conclude with `Submodule.mem_sup_right hx`. Introduce and unpack `⟨h1, h2, h3⟩ x hx`. Establish `hle : F.X ⊔ Submodule.span E {F.z} ⊔ H ≤ LinearMap.ker (S.hT.flip v)`. Use `sup_le (sup_le ?_ ?_) ?_` and prove the remaining obligations.

Introduce `y hy`. Simplify using `using h1 y hy`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`. Simplify using `using h2`. Introduce `y hy`.

Simplify using `using h3 y hy`. Simplify using `using hle hx`.
-/
theorem mem_Qsp (F : FlagG S r T) (H : Submodule E S.V) {v : S.V} :
    v ∈ Qsp F H ↔ (∀ x ∈ F.X, S.hT x v = 0) ∧ S.hT F.z v = 0 ∧ ∀ h ∈ H, S.hT h v = 0 := by
  simp only [Qsp, Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h
    refine ⟨fun x hx => h x ?_, h F.z ?_, fun x hx => h x ?_⟩
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left hx)
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
    · exact Submodule.mem_sup_right hx
  · rintro ⟨h1, h2, h3⟩ x hx
    have hle : F.X ⊔ Submodule.span E {F.z} ⊔ H ≤ LinearMap.ker (S.hT.flip v) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro y hy; simpa using h1 y hy
      · rw [Submodule.span_le, Set.singleton_subset_iff]; simpa using h2
      · intro y hy; simpa using h3 y hy
    simpa using hle hx

/- English proof (translation)
Set `b` to `Module.finBasis E U`. Set `ψ : S.V →ₗ[E] (Fin (finrank E U) → E)` to `LinearMap.pi (fun i => S.hT ((b i : U) : S.V))`. Establish `hker : LinearMap.ker ψ = Lat.orth S U`. Use extensionality with `y`. Simplify using `only [LinearMap.mem_ker, Lat.orth, Submodule.mem_iInf]`.

Prove the components needed by the constructor for the conclusion. Introduce `hy x hx`. Establish `hyi : ∀ i, S.hT ((b i : U) : S.V) y = 0` using `fun i => by`. Simplify `congrFun hy i` using `[ψ]`. Establish `hxs : x = ∑ i, b.repr ⟨x, hx⟩ i • ((b i : U) : S.V)`.

Use `congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)` as an intermediate fact. Rewrite `this` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul] at this`. Conclude with `this.symm`. Rewrite using `[hxs, map_sum, LinearMap.sum_apply]`.

Simplify using `[LinearMap.map_smulₛₗ, hyi]`. Introduce `h`. Use function extensionality and compare the values at `i`. Simplify `h _ (b i).2` using `[ψ]`. Establish `hrange : LinearMap.range ψ = ⊤`.

Assume the negation of the conclusion as `hne`. Take `⟨f, hf0, hf⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)`. Use `set c : Fin (finrank E U) → E := fun i => f (fun j => if i = j then 1 else 0) with hc`. Establish `hfw : ∀ w, f w = ∑ i, w i * c i` using `fun w => by`. Rewrite using `[LinearMap.pi_apply_eq_sum_univ f w]`.

Simplify using `[c, smul_eq_mul]`. Establish `hu : (∑ i, star (c i) • ((b i : U) : S.V)) = 0`. Apply `S.nondeg.1` to reduce the goal to its premises. Introduce `y`. Establish `h1 : f (ψ y) = 0` using `hf (LinearMap.mem_range_self ψ y)`.

Rewrite `h1` using `[hfw]`. Rewrite using `[map_sum, LinearMap.sum_apply]`. Simplify using `only [LinearMap.map_smulₛₗ, starRingEnd_apply, star_star, LinearMap.smul_apply, smul_eq_mul]`. Rewrite using `[← h1]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using `[ψ, mul_comm]`. Establish `hli : LinearIndependent E (fun i => ((b i : U) : S.V))` using `b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)`. Establish `hc0 : ∀ i, c i = 0`. Introduce `i`. Use `(Fintype.linearIndependent_iff.1 hli) (fun i => star (c i)) hu i` as an intermediate fact.

Simplify using `using this`. Apply `hf0` to reduce the goal to its premises. Conclude with `LinearMap.ext fun w => by simp [hfw, hc0]`. Use `LinearMap.finrank_range_add_finrank_ker ψ` as an intermediate fact. Rewrite `this` using `[hrange, finrank_top, Module.finrank_fin_fun, hker]`.

Use linear arithmetic over natural numbers and integers.
-/
private theorem finrank_add_finrank_orth_le (U : Submodule E S.V) :
    finrank E U + finrank E (Lat.orth S U) ≤ finrank E S.V := by
  classical
  let b := Module.finBasis E U
  let ψ : S.V →ₗ[E] (Fin (finrank E U) → E) := LinearMap.pi (fun i => S.hT ((b i : U) : S.V))
  have hker : LinearMap.ker ψ = Lat.orth S U := by
    ext y
    simp only [LinearMap.mem_ker, Lat.orth, Submodule.mem_iInf]
    constructor
    · intro hy x hx
      have hyi : ∀ i, S.hT ((b i : U) : S.V) y = 0 := fun i => by
        simpa [ψ] using congrFun hy i
      have hxs : x = ∑ i, b.repr ⟨x, hx⟩ i • ((b i : U) : S.V) := by
        have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this.symm
      rw [hxs, map_sum, LinearMap.sum_apply]
      simp [LinearMap.map_smulₛₗ, hyi]
    · intro h
      funext i
      simpa [ψ] using h _ (b i).2
  have hrange : LinearMap.range ψ = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    set c : Fin (finrank E U) → E := fun i => f (fun j => if i = j then 1 else 0) with hc
    have hfw : ∀ w, f w = ∑ i, w i * c i := fun w => by
      rw [LinearMap.pi_apply_eq_sum_univ f w]; simp [c, smul_eq_mul]
    have hu : (∑ i, star (c i) • ((b i : U) : S.V)) = 0 := by
      apply S.nondeg.1
      intro y
      have h1 : f (ψ y) = 0 := hf (LinearMap.mem_range_self ψ y)
      rw [hfw] at h1
      rw [map_sum, LinearMap.sum_apply]
      simp only [LinearMap.map_smulₛₗ, starRingEnd_apply, star_star, LinearMap.smul_apply, smul_eq_mul]
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [ψ, mul_comm]
    have hli : LinearIndependent E (fun i => ((b i : U) : S.V)) :=
      b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
    have hc0 : ∀ i, c i = 0 := by
      intro i
      have := (Fintype.linearIndependent_iff.1 hli) (fun i => star (c i)) hu i
      simpa using this
    apply hf0
    exact LinearMap.ext fun w => by simp [hfw, hc0]
  have := LinearMap.finrank_range_add_finrank_ker ψ
  rw [hrange, finrank_top, Module.finrank_fin_fun, hker] at this
  omega

/- English proof (translation)
Establish `hw0 : w ≠ 0` using `fun h => hw (h ▸ A.zero_mem)`. Use `Submodule.finrank_sup_add_finrank_inf_eq A (Submodule.span E {w})` as an intermediate fact. Establish `hinf : A ⊓ Submodule.span E {w} = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `u hu`.

Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hu.2`. Rewrite using `[Submodule.mem_bot]`. Assume the negation of the conclusion as `hc0`. Establish `hc : c ≠ 0` using `by rintro rfl; exact hc0 (zero_smul _ _)`. Apply `hw` to reduce the goal to its premises.

Use `A.smul_mem c⁻¹ hu.1` as an intermediate fact. Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hc, one_smul]`. Then use the resulting hypothesis. Rewrite `this` using `[hinf, finrank_bot, add_zero, finrank_span_singleton hw0]`. Conclude with `this`.
-/
private theorem finrank_sup_span_singleton_of_not_mem' (A : Submodule E S.V) {w : S.V} (hw : w ∉ A) :
    finrank E ↥(A ⊔ Submodule.span E {w}) = finrank E A + 1 := by
  have hw0 : w ≠ 0 := fun h => hw (h ▸ A.zero_mem)
  have := Submodule.finrank_sup_add_finrank_inf_eq A (Submodule.span E {w})
  have hinf : A ⊓ Submodule.span E {w} = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu.2
    rw [Submodule.mem_bot]
    by_contra hc0
    have hc : c ≠ 0 := by rintro rfl; exact hc0 (zero_smul _ _)
    apply hw
    have := A.smul_mem c⁻¹ hu.1
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hw0] at this
  exact this

/- English proof (translation)
Establish `hXQ : F.X ≤ Qsp F H`. Introduce `x hx`. Rewrite using `[mem_Qsp]`. Use `⟨fun x' hx' => hT_X_X F hx' hx, hT_z_X F hx, fun h hh => ?_⟩` and prove the remaining obligations. Rewrite using `[hT_swap_eq_star, hXH x hx h hh, star_zero]`.

Establish `hXr : finrank E F.X = r` using `by show finrank E (Submodule.span E (Set.range F.e)) = r`. Rewrite using `[finrank_span_eq_card F.e_indep, Fintype.card_fin]`. Establish `hzXH : F.z ∉ F.X ⊔ H`. Introduce `hz`. Take `⟨x, hx, h, hh, hxh⟩` from `Submodule.mem_sup.1 hz`.

Establish `h1 : S.hT F.z F.z = 0`. Combine the equalities or inequalities in the displayed calculation. Use `F.z_norm` as an intermediate fact. Rewrite `this` using `[h1]`. Conclude with `hT (neg_eq_zero.1 this.symm)`.

Establish `hXH_fin : finrank E ↥(F.X ⊔ H) = r + finrank E H`. Use `Submodule.finrank_sup_add_finrank_inf_eq F.X H` as an intermediate fact. Establish `hinf : F.X ⊓ H = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`.

Rewrite using `[Submodule.mem_bot]`. Conclude with `hdisj x hx.1 hx.2`. Rewrite `this` using `[hinf, finrank_bot, add_zero, hXr]`. Conclude with `this`. Establish `hU : F.X ⊔ Submodule.span E {F.z} ⊔ H = (F.X ⊔ H) ⊔ Submodule.span E {F.z}` using `sup_right_comm _ _ _`.

Establish `hU_fin : finrank E ↥(F.X ⊔ Submodule.span E {F.z} ⊔ H) = r + finrank E H + 1`. Rewrite using `[hU, finrank_sup_span_singleton_of_not_mem' _ hzXH, hXH_fin]`. Establish `hQ : finrank E (Qsp F H) ≤ r + 1`. Use `finrank_add_finrank_orth_le (F.X ⊔ Submodule.span E {F.z} ⊔ H)` as an intermediate fact. Use `show finrank E (Lat.orth S (F.X ⊔ Submodule.span E {F.z} ⊔ H)) ≤ r + 1`.

Use linear arithmetic over natural numbers and integers. Establish `hy0X : y0 ∉ F.X` using `fun h => hy00 (hT_X_X F h h)`. Establish `hle : F.X ⊔ Submodule.span E {y0} ≤ Qsp F H` using `sup_le hXQ (by rw [Submodule.span_le, Set.singleton_subset_iff]; exact hy0)`. Establish `hfin2 : finrank E ↥(F.X ⊔ Submodule.span E {y0}) = r + 1`. Rewrite using `[finrank_sup_span_singleton_of_not_mem' _ hy0X, hXr]`.

Establish `heq : F.X ⊔ Submodule.span E {y0} = Qsp F H` using `Submodule.eq_of_le_of_finrank_le hle (by omega)`. Rewrite `hv` using `[← heq]`. Take `⟨x, hx, w, hw, rfl⟩` from `Submodule.mem_sup.1 hv`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hw`. Establish `h1 : S.hT y0 x = 0`.

Rewrite using `[hT_swap_eq_star, ((mem_Qsp F H).1 hy0).1 x hx, star_zero]`. Establish `h2 : c * S.hT y0 y0 = 0`. Use `hvy` as an intermediate fact. Simplify using `only [brS, map_add, map_smul, smul_eq_mul, h1, zero_add] at this`. Conclude with `this`.

Establish `hc : c = 0`. Break down `mul_eq_zero.1 h2 with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h hy00`. Simplify `hx` using `[hc]`.
-/
theorem line (F : FlagG S r T) (hT : T ≠ 0) (H : Submodule E S.V) (hXH : ∀ x ∈ F.X, ∀ h ∈ H, S.hT x h = 0)
    (hzH : ∀ h ∈ H, S.hT F.z h = 0) (hdisj : ∀ x ∈ F.X, x ∈ H → x = 0)
    (hdim : finrank E H + 2 * r + 2 = finrank E S.V) {y0 v : S.V} (hy0 : y0 ∈ Qsp F H)
    (hy00 : brS S y0 y0 ≠ 0) (hv : v ∈ Qsp F H) (hvy : brS S v y0 = 0) : v ∈ F.X := by
  classical
  have hXQ : F.X ≤ Qsp F H := by
    intro x hx
    rw [mem_Qsp]
    refine ⟨fun x' hx' => hT_X_X F hx' hx, hT_z_X F hx, fun h hh => ?_⟩
    rw [hT_swap_eq_star, hXH x hx h hh, star_zero]
  have hXr : finrank E F.X = r := by
    show finrank E (Submodule.span E (Set.range F.e)) = r
    rw [finrank_span_eq_card F.e_indep, Fintype.card_fin]
  have hzXH : F.z ∉ F.X ⊔ H := by
    intro hz
    obtain ⟨x, hx, h, hh, hxh⟩ := Submodule.mem_sup.1 hz
    have h1 : S.hT F.z F.z = 0 := by
      calc S.hT F.z F.z = S.hT F.z (x + h) := by rw [hxh]
        _ = 0 := by rw [map_add, hT_z_X F hx, hzH h hh, add_zero]
    have := F.z_norm
    rw [h1] at this
    exact hT (neg_eq_zero.1 this.symm)
  have hXH_fin : finrank E ↥(F.X ⊔ H) = r + finrank E H := by
    have := Submodule.finrank_sup_add_finrank_inf_eq F.X H
    have hinf : F.X ⊓ H = ⊥ := by
      rw [eq_bot_iff]; intro x hx; rw [Submodule.mem_bot]; exact hdisj x hx.1 hx.2
    rw [hinf, finrank_bot, add_zero, hXr] at this
    exact this
  have hU : F.X ⊔ Submodule.span E {F.z} ⊔ H = (F.X ⊔ H) ⊔ Submodule.span E {F.z} :=
    sup_right_comm _ _ _
  have hU_fin : finrank E ↥(F.X ⊔ Submodule.span E {F.z} ⊔ H) = r + finrank E H + 1 := by
    rw [hU, finrank_sup_span_singleton_of_not_mem' _ hzXH, hXH_fin]
  have hQ : finrank E (Qsp F H) ≤ r + 1 := by
    have := finrank_add_finrank_orth_le (F.X ⊔ Submodule.span E {F.z} ⊔ H)
    show finrank E (Lat.orth S (F.X ⊔ Submodule.span E {F.z} ⊔ H)) ≤ r + 1
    omega
  have hy0X : y0 ∉ F.X := fun h => hy00 (hT_X_X F h h)
  have hle : F.X ⊔ Submodule.span E {y0} ≤ Qsp F H :=
    sup_le hXQ (by rw [Submodule.span_le, Set.singleton_subset_iff]; exact hy0)
  have hfin2 : finrank E ↥(F.X ⊔ Submodule.span E {y0}) = r + 1 := by
    rw [finrank_sup_span_singleton_of_not_mem' _ hy0X, hXr]
  have heq : F.X ⊔ Submodule.span E {y0} = Qsp F H :=
    Submodule.eq_of_le_of_finrank_le hle (by omega)
  rw [← heq] at hv
  obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
  have h1 : S.hT y0 x = 0 := by
    rw [hT_swap_eq_star, ((mem_Qsp F H).1 hy0).1 x hx, star_zero]
  have h2 : c * S.hT y0 y0 = 0 := by
    have := hvy
    simp only [brS, map_add, map_smul, smul_eq_mul, h1, zero_add] at this
    exact this
  have hc : c = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact h
    · exact absurd h hy00
  simpa [hc] using hx

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Matrix.conjTranspose_apply]`. Simplify using `only [Zhat]`. Conclude with `brS_swap (F'.fvec a) (F.fvec b)`.
-/
theorem zhat_swap (F : FlagG S r T) (F' : FlagG S r T') : Zhat F' F = (Zhat F F')ᴴ := by
  ext a b
  rw [Matrix.conjTranspose_apply]
  simp only [Zhat]
  exact brS_swap (F'.fvec a) (F.fvec b)

/- English proof (translation)
Unfold `Dl leadMinorE`. Rewrite using `[zhat_swap]`. Use `split_ifs with h`. Rewrite using `[← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose]`. Simplify using the standard rewrite rules.
-/
theorem Dl_swap (F : FlagG S r T) (F' : FlagG S r T') (l : ℕ) : Dl F' F l = star (Dl F F' l) := by
  unfold Dl leadMinorE
  rw [zhat_swap]
  split_ifs with h
  · rw [← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose]
  · simp

/- English proof (translation)
Unfold `Gflag`. Simplify using `only [Dl_swap F F', star_star]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Gflag_swap (F : FlagG S r T) (F' : FlagG S r T') : Gflag F' F = Gflag F F' := by
  unfold Gflag
  simp only [Dl_swap F F', star_star]
  ring

end Formalism.L2.SG.NGCut.NormalVectorPairings

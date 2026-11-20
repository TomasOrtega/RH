import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPfA
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.PhibOLComplete

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MQ

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries

section Div

variable {O : Type} [CommRing O]

/- English proof (translation)
Use `haveI : Fact p.Prime := ⟨hp⟩`. Use `set I : Ideal O := Ideal.span {((p : ℕ) : O)} with hI`. Establish `hjac : I ≤ (⊥ : Ideal O).jacobson` using `by first`. Consider the case `exact IsAdicComplete.le_jacobson_bot I`. Consider the case `exact IsAdicComplete.le_jacobson_bot (I := I)`.

Establish `hIne : I ≠ ⊤`. Introduce `h`. Rewrite `hjac` using `[h, top_le_iff, Ideal.jacobson_eq_top_iff]`. Conclude with `bot_ne_top hjac`. Establish `hp2 : ((p : ℕ) : O) ∈ nonunits O` using `mem_nonunits_iff.2 (fun hu => hIne (Ideal.span_singleton_eq_top.2 hu))`.

Use `haveI hch : CharP (O ⧸ I) p := CharP.quotient O p hp2`. Use `haveI : Nontrivial (O ⧸ I) := by first`. Consider the case `exact Ideal.Quotient.nontrivial_iff.2 hIne`. Consider the case `exact Submodule.Quotient.nontrivial_of_lt_top _ hIne.lt_top`. Consider the case `exact Ideal.Quotient.nontrivial_of_lt_top hIne.lt_top`.

Establish `hinj : Function.Injective (algebraMap (O ⧸ I) (PowerSeries (O ⧸ I)))`. Introduce `a b hab`. Use `first`. Consider the case `simpa using congrArg (PowerSeries.constantCoeff (O ⧸ I)) hab`. Consider the case `simpa using congrArg PowerSeries.constantCoeff hab`.

Consider the case `simpa using congrArg (PowerSeries.coeff 0) hab`. Consider the case `exact PowerSeries.C_injective hab`. Use `haveI : CharP (PowerSeries (O ⧸ I)) p := charP_of_injective_algebraMap hinj p`. Establish `hmap : PowerSeries.map (Ideal.Quotient.mk I) (((1 + PowerSeries.X) ^ p - 1) ^ N) = PowerSeries.X ^ (p * N)`. Simplify using `only [map_pow, map_sub, map_add, map_one, PowerSeries.map_X]`.

Rewrite using `[add_pow_char, one_pow, add_sub_cancel_left, ← pow_mul]`. Establish `key : ∀ c : O, Ideal.Quotient.mk I c = 1 → IsUnit c`. Introduce `c hc`. Establish `hmem : c - 1 ∈ I`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, hc, map_one, sub_self]`.

Establish `hj` using `(Ideal.mem_jacobson_bot.1 (hjac hmem)) 1`. Simplify using `using hj`. Establish `hdiv : (((1 + PowerSeries.X) ^ p - 1) ^ N : PowerSeries O).IsWeierstrassDivisorAt I` using `by show IsUnit _`. Rewrite using `[hmap, PowerSeries.order_X_pow, ENat.toNat_coe]`. Apply `key` to reduce the goal to its premises.

Rewrite using `[← PowerSeries.coeff_map, hmap, PowerSeries.coeff_X_pow_self]`. Establish `hW` using `hdiv.isWeierstrassDivisionAt_div_mod f`. Use `⟨hdiv.div f, hdiv.mod f, ?_, ?_⟩` and prove the remaining obligations. Establish `hd` using `hW.degree_lt`. Rewrite `hd` using `[hmap, PowerSeries.order_X_pow, ENat.toNat_coe]`.

Conclude with `hd` after adjusting the coercions. Conclude with `hW.eq_mul_add`.
-/
theorem phibN_div (p : ℕ) (hp : p.Prime) [Nontrivial O] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] (N : ℕ)
    (f : PowerSeries O) : ∃ (Q : PowerSeries O) (R : Polynomial O), R.degree < ((p * N : ℕ) : WithBot ℕ) ∧
      f = ((1 + PowerSeries.X) ^ p - 1) ^ N * Q + (R : PowerSeries O) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set I : Ideal O := Ideal.span {((p : ℕ) : O)} with hI
  have hjac : I ≤ (⊥ : Ideal O).jacobson := by
    first
    | exact IsAdicComplete.le_jacobson_bot I
    | exact IsAdicComplete.le_jacobson_bot (I := I)
  have hIne : I ≠ ⊤ := by
    intro h
    rw [h, top_le_iff, Ideal.jacobson_eq_top_iff] at hjac
    exact bot_ne_top hjac
  have hp2 : ((p : ℕ) : O) ∈ nonunits O :=
    mem_nonunits_iff.2 (fun hu => hIne (Ideal.span_singleton_eq_top.2 hu))
  haveI hch : CharP (O ⧸ I) p := CharP.quotient O p hp2
  haveI : Nontrivial (O ⧸ I) := by
    first
    | exact Ideal.Quotient.nontrivial_iff.2 hIne
    | exact Submodule.Quotient.nontrivial_of_lt_top _ hIne.lt_top
    | exact Ideal.Quotient.nontrivial_of_lt_top hIne.lt_top
  have hinj : Function.Injective (algebraMap (O ⧸ I) (PowerSeries (O ⧸ I))) := by
    intro a b hab
    first
    | simpa using congrArg (PowerSeries.constantCoeff (O ⧸ I)) hab
    | simpa using congrArg PowerSeries.constantCoeff hab
    | simpa using congrArg (PowerSeries.coeff 0) hab
    | exact PowerSeries.C_injective hab
  haveI : CharP (PowerSeries (O ⧸ I)) p := charP_of_injective_algebraMap hinj p
  have hmap : PowerSeries.map (Ideal.Quotient.mk I) (((1 + PowerSeries.X) ^ p - 1) ^ N) =
      PowerSeries.X ^ (p * N) := by
    simp only [map_pow, map_sub, map_add, map_one, PowerSeries.map_X]
    rw [add_pow_char, one_pow, add_sub_cancel_left, ← pow_mul]
  have key : ∀ c : O, Ideal.Quotient.mk I c = 1 → IsUnit c := by
    intro c hc
    have hmem : c - 1 ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hc, map_one, sub_self]
    have hj := (Ideal.mem_jacobson_bot.1 (hjac hmem)) 1
    simpa using hj
  have hdiv : (((1 + PowerSeries.X) ^ p - 1) ^ N : PowerSeries O).IsWeierstrassDivisorAt I := by
    show IsUnit _
    rw [hmap, PowerSeries.order_X_pow, ENat.toNat_coe]
    apply key
    rw [← PowerSeries.coeff_map, hmap, PowerSeries.coeff_X_pow_self]
  have hW := hdiv.isWeierstrassDivisionAt_div_mod f
  refine ⟨hdiv.div f, hdiv.mod f, ?_, ?_⟩
  · have hd := hW.degree_lt
    rw [hmap, PowerSeries.order_X_pow, ENat.toNat_coe] at hd
    exact_mod_cast hd
  · exact hW.eq_mul_add

end Div

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

/- English proof (translation)
Rewrite `hg`, `hh`, the goal using `[W.DelF_def]`. Take `⟨k₁, hk₁, h₁⟩` from `hg`. Take `⟨k₂, hk₂, h₂⟩` from `hh`. Conclude with `⟨k₁ * k₂, Nat.mul_pos hk₁ hk₂, by`. Rewrite using `[mul_pow, pow_mul, h₁, one_pow, one_mul, mul_comm k₁ k₂, pow_mul, h₂, one_pow]⟩`.
-/
theorem delF_mul' {g h : W.Gam} (hg : g ∈ W.DelF) (hh : h ∈ W.DelF) : g * h ∈ W.DelF := by
  rw [W.DelF_def] at hg hh ⊢
  obtain ⟨k₁, hk₁, h₁⟩ := hg
  obtain ⟨k₂, hk₂, h₂⟩ := hh
  exact ⟨k₁ * k₂, Nat.mul_pos hk₁ hk₂, by
    rw [mul_pow, pow_mul, h₁, one_pow, one_mul, mul_comm k₁ k₂, pow_mul, h₂, one_pow]⟩

/- English proof (translation)
Rewrite `hg`, the goal using `[W.DelF_def]`. Take `⟨k, hk, h⟩` from `hg`. Conclude with `⟨k, hk, by rw [inv_pow, h, inv_one]⟩`.
-/
theorem delF_inv' {g : W.Gam} (hg : g ∈ W.DelF) : g⁻¹ ∈ W.DelF := by
  rw [W.DelF_def] at hg ⊢
  obtain ⟨k, hk, h⟩ := hg
  exact ⟨k, hk, by rw [inv_pow, h, inv_one]⟩

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show W.γ₀ (g * h) (a i) = W.γ₀ g (W.γ₀ h (a i))`. Rewrite using `[map_mul, AlgHom.mul_apply]`.
-/
theorem γA_mul' (g h : W.Gam) (a : LetA O n) : W.γA (g * h) a = W.γA g (W.γA h a) := by
  funext i
  show W.γ₀ (g * h) (a i) = W.γ₀ g (W.γ₀ h (a i))
  rw [map_mul, AlgHom.mul_apply]

/- English proof (translation)
Use `show ∀ δ ∈ W.DelF, W.γA δ (letE c : LetA O n) = letE c`. Introduce `δ _`. Use function extensionality and compare the values at `i`. Use `show W.γ₀ δ ((letE c : LetA O n) i) = (letE c : LetA O n) i`. Simplify using `only [letE, Pi.single_apply]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem letE_mem (c : ZMod n) : (letE c : LetA O n) ∈ W.AΔ := by
  show ∀ δ ∈ W.DelF, W.γA δ (letE c : LetA O n) = letE c
  intro δ _
  funext i
  show W.γ₀ δ ((letE c : LetA O n) i) = (letE c : LetA O n) i
  simp only [letE, Pi.single_apply]
  split_ifs <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [letE, Pi.mul_apply, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem letE_mul_self' (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  funext j
  simp only [letE, Pi.mul_apply, Pi.single_apply]
  split_ifs <;> simp

def avg (u : Oˣ) (x : LetA O n) : LetA O n := ((u⁻¹ : Oˣ) : O) • ∑ δ ∈ W.DelF, W.γA δ x

/- English proof (translation)
Use `show ∀ δ ∈ W.DelF, W.γA δ (avg W u x) = avg W u x`. Introduce `δ' hδ'`. Unfold `avg`. Rewrite using `[map_smul, map_sum]`. Use `congr 1`.

Use `Finset.sum_nbij' (fun δ => δ' * δ) (fun δ => δ'⁻¹ * δ) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `a ha`. Conclude with `delF_mul' W hδ' ha`. Introduce `a ha`. Conclude with `delF_mul' W (delF_inv' W hδ') ha`.

Introduce `a _`. Conclude with `inv_mul_cancel_left δ' a`. Introduce `a _`. Conclude with `mul_inv_cancel_left δ' a`. Introduce `a _`.

Conclude with `(γA_mul' W δ' a x).symm`.
-/
theorem avg_mem (u : Oˣ) (x : LetA O n) : avg W u x ∈ W.AΔ := by
  show ∀ δ ∈ W.DelF, W.γA δ (avg W u x) = avg W u x
  intro δ' hδ'
  unfold avg
  rw [map_smul, map_sum]
  congr 1
  refine Finset.sum_nbij' (fun δ => δ' * δ) (fun δ => δ'⁻¹ * δ) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    exact delF_mul' W hδ' ha
  · intro a ha
    exact delF_mul' W (delF_inv' W hδ') ha
  · intro a _
    exact inv_mul_cancel_left δ' a
  · intro a _
    exact mul_inv_cancel_left δ' a
  · intro a _
    exact (γA_mul' W δ' a x).symm

/- English proof (translation)
Establish `hx' : ∀ δ ∈ W.DelF, W.γA δ x = x` using `hx`. Unfold `avg`. Rewrite using `[Finset.sum_congr rfl (fun δ hδ => hx' δ hδ), Finset.sum_const, ← Nat.cast_smul_eq_nsmul O, ← hu, smul_smul, Units.inv_mul, one_smul]`.
-/
theorem avg_self (u : Oˣ) (hu : (u : O) = (W.DelF.card : ℕ)) {x : LetA O n} (hx : x ∈ W.AΔ) :
    avg W u x = x := by
  have hx' : ∀ δ ∈ W.DelF, W.γA δ x = x := hx
  unfold avg
  rw [Finset.sum_congr rfl (fun δ hδ => hx' δ hδ), Finset.sum_const, ← Nat.cast_smul_eq_nsmul O, ← hu,
    smul_smul, Units.inv_mul, one_smul]

/- English proof (translation)
Simplify using `only [avg, map_add, Finset.sum_add_distrib, smul_add]`.
-/
theorem avg_add (u : Oˣ) (x y : LetA O n) : avg W u (x + y) = avg W u x + avg W u y := by
  simp only [avg, map_add, Finset.sum_add_distrib, smul_add]

/- English proof (translation)
Establish `hy' : ∀ δ ∈ W.DelF, W.γA δ y = y` using `hy`. Establish `hs : ∑ δ ∈ W.DelF, W.γA δ (y * x) = y * ∑ δ ∈ W.DelF, W.γA δ x`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl (fun δ hδ => by rw [map_mul, hy' δ hδ])`. Unfold `avg`.

Rewrite using `[hs, mul_smul_comm]`.
-/
theorem avg_mul_left (u : Oˣ) {y : LetA O n} (hy : y ∈ W.AΔ) (x : LetA O n) :
    avg W u (y * x) = y * avg W u x := by
  have hy' : ∀ δ ∈ W.DelF, W.γA δ y = y := hy
  have hs : ∑ δ ∈ W.DelF, W.γA δ (y * x) = y * ∑ δ ∈ W.DelF, W.γA δ x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun δ hδ => by rw [map_mul, hy' δ hδ])
  unfold avg
  rw [hs, mul_smul_comm]

/- English proof (translation)
Simplify using `only [avg, map_sum, Finset.smul_sum]`. Conclude with `Finset.sum_comm`.
-/
theorem avg_sum (u : Oˣ) {ι : Type} (s : Finset ι) (f : ι → LetA O n) :
    avg W u (∑ i ∈ s, f i) = ∑ i ∈ s, avg W u (f i) := by
  simp only [avg, map_sum, Finset.smul_sum]
  exact Finset.sum_comm

/- English proof (translation)
Use `set N := s' + 2 * h' with hN`. Use `⟨PD.p * N, fun i => ⟨avg W u ((letπ : LetA O n) ^ (i : ℕ)), avg_mem W u _⟩, fun a => ?_⟩` and prove the remaining obligations. Take `⟨Q, R, hR, hf⟩` from `phibN_div (O := O) PD.p hp N ((a : LetA O n) c)`. Use `set A1 : PowerSeries O := (w₁ : LetA O n) c`. Use `set B1 : PowerSeries O := ((w₁⁻¹ : (LetA O n)ˣ) : LetA O n) c`.

Use `set A2 : PowerSeries O := (w₂ : LetA O n) c`. Use `set B2 : PowerSeries O := ((w₂⁻¹ : (LetA O n)ˣ) : LetA O n) c`. Establish `h1 : A1 * B1 = 1`. Use `congrFun (Units.mul_inv w₁) c` as an intermediate fact. Simplify using `using this`.

Establish `h2 : A2 * B2 = 1`. Use `congrFun (Units.mul_inv w₂) c` as an intermediate fact. Simplify using `using this`. Establish `hq0 : W.q₀ = A2 * Eπ c`. Use `congrFun hq c` as an intermediate fact.

Simplify `this` using `[LocWach.q]`. Establish `hEc : Eπ c = B2 * W.q₀`. Rewrite using `[hq0, ← mul_assoc, mul_comm B2 A2, h2, one_mul]`. Establish `hπc : π' c = A1 * PowerSeries.X ^ s'`. Use `congrFun hπ c` as an intermediate fact.

Simplify `this` using `[letπ]`. Establish `hφb : (1 + PowerSeries.X) ^ PD.p - 1 = PowerSeries.X * W.q₀`. Rewrite using `[W.q₀_def, add_comm]`. Establish `key : A1 * B1 * (A2 * B2) ^ (2 * h') = 1` using `by rw [h1, h2, one_pow, one_mul]`. Use `set s₀ : LetA O n := fun _ => PowerSeries.X ^ (2 * h') * W.q₀ ^ s' * B1 * A2 ^ (2 * h') * Q with hs₀`.

Use `set Rt : LetA O n := fun _ => (R : PowerSeries O) with hRt`. Establish `hcl : (letE c : LetA O n) * a = (letE c : LetA O n) * Rt + (letE c : LetA O n) * (π' * Eπ ^ (2 * h') * s₀)`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = c`. Substitute `hi` using the available equality.

Simplify using `only [Pi.add_apply, Pi.mul_apply, letE, Pi.single_eq_same, one_mul, Pi.pow_apply, hs₀, hRt]`. Rewrite using `[hf, hφb, hπc, hEc]`. Take the linear combination `(-(PowerSeries.X ^ (s' + 2 * h') * W.q₀ ^ (s' + 2 * h') * Q)) * key`. Simplify using `[letE, Pi.single_apply, hi]`. Establish `hR' : Rt = ∑ i : Fin (PD.p * N), algebraMap O (LetA O n) (R.coeff i) * (letπ : LetA O n) ^ (i : ℕ)`.

Establish `hdeg : ∀ m, PD.p * N ≤ m → R.coeff m = 0` using `fun m hm => Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hR (by exact_mod_cast hm))`. Use function extensionality and compare the values at `j`. Use `show (R : PowerSeries O) = (∑ i : Fin (PD.p * N), algebraMap O (LetA O n) (R.coeff i) * (letπ : LetA O n) ^ (i : ℕ)) j`. Rewrite using `[Finset.sum_apply]`. Use extensionality with `k`.

Rewrite using `[Polynomial.coeff_coe, map_sum]`. Establish `ht : ∀ i : Fin (PD.p * N), PowerSeries.coeff k ((algebraMap O (LetA O n) (R.coeff i) * (letπ : LetA O n) ^ (i : ℕ)) j) = if k = (i : ℕ) then R.coeff k else 0`. Introduce `i`. Establish `e : (algebraMap O (LetA O n) (R.coeff i) * (letπ : LetA O n) ^ (i : ℕ)) j = R.coeff i • PowerSeries.X ^ (i : ℕ)`. Rewrite using `[← Algebra.smul_def]`.

Both sides reduce to the same expression. Rewrite using `[e, map_smul, PowerSeries.coeff_X_pow, smul_eq_mul]`. Use `split_ifs with h`. Rewrite using `[h, mul_one]`. Rewrite using `[mul_zero]`.

Rewrite using `[Finset.sum_congr rfl (fun i _ => ht i), Fin.sum_univ_eq_sum_range (fun i => if k = i then R.coeff k else 0) (PD.p * N), Finset.sum_ite_eq]`. Use `split_ifs with hk`. Both sides reduce to the same expression. Rewrite `hk` using `[Finset.mem_range, not_lt]`. Conclude with `hdeg k hk`.

Establish `hg : π' * Eπ ^ (2 * h') ∈ W.AΔ` using `mul_mem hπΔ (pow_mem hEΔ _)`. Establish `hae : (letE c : LetA O n) * a ∈ W.AΔ` using `mul_mem (letE_mem W c) a.2`. Use `⟨fun i => R.coeff i, ⟨avg W u s₀, avg_mem W u _⟩, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[avg_add, avg_mul_left W u (letE_mem W c), avg_mul_left W u (letE_mem W c), avg_mul_left W u hg]`.

Use `_ = _ := by`. Rewrite using `[hR', avg_sum]`. Use `congr 2`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[avg_mul_left W u (Subalgebra.algebraMap_mem _ _)]`.
-/
theorem div_at (hp : PD.p.Prime) [Nontrivial O] [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    (s' h' : ℕ) (π' Eπ : LetA O n) (w₁ w₂ : (LetA O n)ˣ) (hπ : π' = w₁ * (letπ : LetA O n) ^ s') (hq : W.q = w₂ * Eπ)
    (u : Oˣ) (hu : (u : O) = (W.DelF.card : ℕ)) (hπΔ : π' ∈ W.AΔ) (hEΔ : Eπ ∈ W.AΔ) (c : ZMod n) :
    ∃ (D : ℕ) (S : Fin D → ↥W.AΔ), ∀ a : ↥W.AΔ, ∃ (co : Fin D → O) (s : ↥W.AΔ),
      (letE c : LetA O n) * a = (letE c : LetA O n) * (∑ r, algebraMap O (LetA O n) (co r) * (S r : LetA O n)) +
        (letE c : LetA O n) * (π' * Eπ ^ (2 * h') * s) := by
  classical
  set N := s' + 2 * h' with hN
  refine ⟨PD.p * N, fun i => ⟨avg W u ((letπ : LetA O n) ^ (i : ℕ)), avg_mem W u _⟩, fun a => ?_⟩
  obtain ⟨Q, R, hR, hf⟩ := phibN_div (O := O) PD.p hp N ((a : LetA O n) c)
  set A1 : PowerSeries O := (w₁ : LetA O n) c
  set B1 : PowerSeries O := ((w₁⁻¹ : (LetA O n)ˣ) : LetA O n) c
  set A2 : PowerSeries O := (w₂ : LetA O n) c
  set B2 : PowerSeries O := ((w₂⁻¹ : (LetA O n)ˣ) : LetA O n) c
  have h1 : A1 * B1 = 1 := by
    have := congrFun (Units.mul_inv w₁) c
    simpa using this
  have h2 : A2 * B2 = 1 := by
    have := congrFun (Units.mul_inv w₂) c
    simpa using this
  have hq0 : W.q₀ = A2 * Eπ c := by
    have := congrFun hq c
    simpa [LocWach.q] using this
  have hEc : Eπ c = B2 * W.q₀ := by
    rw [hq0, ← mul_assoc, mul_comm B2 A2, h2, one_mul]
  have hπc : π' c = A1 * PowerSeries.X ^ s' := by
    have := congrFun hπ c
    simpa [letπ] using this
  have hφb : (1 + PowerSeries.X) ^ PD.p - 1 = PowerSeries.X * W.q₀ := by
    rw [W.q₀_def, add_comm]
  have key : A1 * B1 * (A2 * B2) ^ (2 * h') = 1 := by rw [h1, h2, one_pow, one_mul]
  set s₀ : LetA O n := fun _ => PowerSeries.X ^ (2 * h') * W.q₀ ^ s' * B1 * A2 ^ (2 * h') * Q with hs₀
  set Rt : LetA O n := fun _ => (R : PowerSeries O) with hRt
  have hcl : (letE c : LetA O n) * a = (letE c : LetA O n) * Rt + (letE c : LetA O n) * (π' * Eπ ^ (2 * h') * s₀) := by
    funext i
    by_cases hi : i = c
    · subst hi
      simp only [Pi.add_apply, Pi.mul_apply, letE, Pi.single_eq_same, one_mul, Pi.pow_apply, hs₀, hRt]
      rw [hf, hφb, hπc, hEc]
      linear_combination (-(PowerSeries.X ^ (s' + 2 * h') * W.q₀ ^ (s' + 2 * h') * Q)) * key
    · simp [letE, Pi.single_apply, hi]
  have hR' : Rt = ∑ i : Fin (PD.p * N), algebraMap O (LetA O n) (R.coeff i) * (letπ : LetA O n) ^ (i : ℕ) := by
    have hdeg : ∀ m, PD.p * N ≤ m → R.coeff m = 0 := fun m hm =>
      Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hR (by exact_mod_cast hm))
    funext j
    show (R : PowerSeries O) = (∑ i : Fin (PD.p * N), algebraMap O (LetA O n) (R.coeff i) * (letπ : LetA O n) ^ (i : ℕ)) j
    rw [Finset.sum_apply]
    ext k
    rw [Polynomial.coeff_coe, map_sum]
    have ht : ∀ i : Fin (PD.p * N), PowerSeries.coeff k ((algebraMap O (LetA O n) (R.coeff i) * (letπ : LetA O n) ^ (i : ℕ)) j) =
        if k = (i : ℕ) then R.coeff k else 0 := by
      intro i
      have e : (algebraMap O (LetA O n) (R.coeff i) * (letπ : LetA O n) ^ (i : ℕ)) j = R.coeff i • PowerSeries.X ^ (i : ℕ) := by
        rw [← Algebra.smul_def]
        rfl
      rw [e, map_smul, PowerSeries.coeff_X_pow, smul_eq_mul]
      split_ifs with h
      · rw [h, mul_one]
      · rw [mul_zero]
    rw [Finset.sum_congr rfl (fun i _ => ht i),
      Fin.sum_univ_eq_sum_range (fun i => if k = i then R.coeff k else 0) (PD.p * N), Finset.sum_ite_eq]
    split_ifs with hk
    · rfl
    · rw [Finset.mem_range, not_lt] at hk
      exact hdeg k hk
  have hg : π' * Eπ ^ (2 * h') ∈ W.AΔ := mul_mem hπΔ (pow_mem hEΔ _)
  have hae : (letE c : LetA O n) * a ∈ W.AΔ := mul_mem (letE_mem W c) a.2
  refine ⟨fun i => R.coeff i, ⟨avg W u s₀, avg_mem W u _⟩, ?_⟩
  calc (letE c : LetA O n) * a = avg W u ((letE c : LetA O n) * a) := (avg_self W u hu hae).symm
    _ = avg W u ((letE c : LetA O n) * Rt + (letE c : LetA O n) * (π' * Eπ ^ (2 * h') * s₀)) := by rw [hcl]
    _ = (letE c : LetA O n) * avg W u Rt + (letE c : LetA O n) * (π' * Eπ ^ (2 * h') * avg W u s₀) := by
      rw [avg_add, avg_mul_left W u (letE_mem W c), avg_mul_left W u (letE_mem W c), avg_mul_left W u hg]
    _ = _ := by
      rw [hR', avg_sum]
      congr 2
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [avg_mul_left W u (Subalgebra.algebraMap_mem _ _)]

end Formalism.MainNotions.N.Ln34.MQ

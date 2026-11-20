import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.LinIndToLp

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

variable {k r : ℕ}

def sigI (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩

def sgnI (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sigI_val (i : Fin (2 * r + k + 1)) :
    (sigI k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := rfl

/- English proof (translation)
Unfold `Hpk sgnI`. Simplify using `only [Fin.ext_iff, sigI_val]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem hpk_apply (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = sigI k r i then sgnI k r i else 0 := by
  unfold Hpk sgnI
  simp only [Fin.ext_iff, sigI_val]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Apply the tactic sequence `apply Fin.ext; rw [sigI_val, sigI_val]; split_ifs <;> omega`.
-/
theorem sig_sig (i : Fin (2 * r + k + 1)) : sigI k r (sigI k r i) = i := by
  apply Fin.ext; rw [sigI_val, sigI_val]; split_ifs <;> omega

/- English proof (translation)
Apply the tactic sequence `unfold sgnI; rw [sigI_val]; split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem sgn_sig (i : Fin (2 * r + k + 1)) : sgnI k r (sigI k r i) = sgnI k r i := by
  unfold sgnI; rw [sigI_val]; split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Apply the tactic sequence `unfold sgnI; split_ifs <;> norm_num`.
-/
theorem sgn_mul_self (i : Fin (2 * r + k + 1)) : sgnI k r i * sgnI k r i = 1 := by
  unfold sgnI; split_ifs <;> norm_num

/- English proof (translation)
Apply the tactic sequence `unfold sgnI; split_ifs <;> simp`.
-/
theorem star_sgn (i : Fin (2 * r + k + 1)) : star (sgnI k r i) = sgnI k r i := by
  unfold sgnI; split_ifs <;> simp

/- English proof (translation)
Simplify using `only [mulVec, dotProduct, hpk_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
theorem hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = sgnI k r i * v (sigI k r i) := by
  simp only [mulVec, dotProduct, hpk_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[hpk_mulVec, hpk_mulVec, sig_sig, sgn_sig, ← mul_assoc, sgn_mul_self, one_mul]`.
-/
theorem hpk_invol (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  funext i; rw [hpk_mulVec, hpk_mulVec, sig_sig, sgn_sig, ← mul_assoc, sgn_mul_self, one_mul]

abbrev EE (k r : ℕ) := EuclideanSpace ℂ (Fin (2 * r + k + 1))

def HE (k r : ℕ) : EE k r →ₗ[ℂ] EE k r := Matrix.toEuclideanLin (Hpk k r)

/- English proof (translation)
The claim follows from `Matrix.toEuclideanLin_apply _ _`.
-/
theorem HE_apply (x : EE k r) : HE k r x = WithLp.toLp 2 (Hpk k r *ᵥ x.ofLp) := Matrix.toEuclideanLin_apply _ _

/- English proof (translation)
Rewrite using `[HE_apply, HE_apply, WithLp.ofLp_toLp, hpk_invol]`.
-/
theorem HE_HE (x : EE k r) : HE k r (HE k r x) = x := by
  rw [HE_apply, HE_apply, WithLp.ofLp_toLp, hpk_invol]

def sigE (k r : ℕ) : Fin (2 * r + k + 1) ≃ Fin (2 * r + k + 1) := ⟨sigI k r, sigI k r, sig_sig, sig_sig⟩

/- English proof (translation)
Simplify using `only [HE_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, hpk_mulVec, Pi.star_apply]`. Use `Fintype.sum_equiv (sigE k r) _ _ (fun i => ?_)` and prove the remaining obligations. Simplify using `only [sigE, Equiv.coe_fn_mk, sig_sig, sgn_sig, star_mul', star_sgn]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem HE_adj (x y : EE k r) : inner ℂ (HE k r x) y = inner ℂ x (HE k r y) := by
  simp only [HE_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, hpk_mulVec, Pi.star_apply]
  refine Fintype.sum_equiv (sigE k r) _ _ (fun i => ?_)
  simp only [sigE, Equiv.coe_fn_mk, sig_sig, sgn_sig, star_mul', star_sgn]; ring

/- English proof (translation)
Rewrite using `[HE_apply, EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, WithLp.ofLp_toLp, herm, dotProduct_comm]`.
-/
theorem herm_eq (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = inner ℂ (WithLp.toLp 2 w : EE k r) (HE k r (WithLp.toLp 2 v)) := by
  rw [HE_apply, EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, WithLp.ofLp_toLp, herm,
    dotProduct_comm]

/- English proof (translation)
Use `set Vm : Submodule ℂ (EE k r) := LinearMap.ker (HE k r + LinearMap.id) with hVm`. Use `set d : Fin (r + 1) → EE k r := fun a => c a - HE k r (c a) with hd`. Establish `hdV : ∀ a, d a ∈ Vm` using `fun a => by`. Simplify using `only [hVm, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, hd, map_sub, HE_HE]`. Normalize the expressions using the abelian group laws.

Establish `hdd : ∀ a b, inner ℂ (d a) (d b) = if a = b then 2 else 0`. Introduce `a b`. Simplify using `only [hd, inner_sub_left, inner_sub_right, HE_adj, HE_HE, hiso, orthonormal_iff_ite.1 hc]`. Apply the tactic sequence `split_ifs <;> norm_num`. Establish `hind : LinearIndependent ℂ d`.

Use `linearIndependent_of_ne_zero_of_inner_eq_zero (fun a h => ?_) (fun a b hab => ?_)` and prove the remaining obligations. Use `hdd a a` as an intermediate fact. Rewrite `this` using `[h, inner_zero_left, if_pos rfl]`. Evaluate the numerical expressions using `at this`. Use `show inner ℂ (d a) (d b) = 0`.

Rewrite using `[hdd, if_neg hab]`. Establish `hfin : Module.finrank ℂ Vm ≤ r + 1`. Apply the tactic sequence `let idx : Fin (r + 1) → Fin (2 * r + k + 1) := fun a => ⟨if a.val < r then a.val else r + k, by split_ifs <;> omega⟩`. Set `π : Vm →ₗ[ℂ] (Fin (r + 1) → ℂ)` to `{ toFun := fun v a => (v : EE k r).ofLp (idx a) map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hinj : Function.Injective π`.

Use `(injective_iff_map_eq_zero π).2 fun v hv => ?_` and prove the remaining obligations. Establish `hx : ∀ i, sgnI k r i * (v : EE k r).ofLp (sigI k r i) = -(v : EE k r).ofLp i`. Introduce `i`. Establish `h1` using `v.2`. Simplify using `only [hVm, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply] at h1`.

Establish `h2` using `congrArg (fun z : EE k r => z.ofLp i) h1`. Simplify using `only [HE_apply, WithLp.ofLp_add, WithLp.ofLp_toLp, Pi.add_apply, hpk_mulVec, WithLp.ofLp_zero, Pi.zero_apply] at h2`. Take the linear combination `h2`. Establish `h0 : ∀ i : Fin (2 * r + k + 1), i.val < r → (v : EE k r).ofLp i = 0`. Introduce `i hi`.

Use `congrFun hv ⟨i.val, by omega⟩` as an intermediate fact. Establish `e : idx ⟨i.val, by omega⟩ = i` using `Fin.ext (by simp [idx, hi])`. Express the relevant statement in the definitionally equal form `(v : EE k r).ofLp (idx ⟨i.val, by omega⟩) = 0 at this`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Establish `hrk : ∀ i : Fin (2 * r + k + 1), i.val = r + k → (v : EE k r).ofLp i = 0`.

Introduce `i hi`. Use `congrFun hv ⟨r, by omega⟩` as an intermediate fact. Establish `e : idx ⟨r, by omega⟩ = i` using `Fin.ext (by simp [idx, hi])`. Express the relevant statement in the definitionally equal form `(v : EE k r).ofLp (idx ⟨r, by omega⟩) = 0 at this`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.

Establish `hall : ∀ i, (v : EE k r).ofLp i = 0`. Introduce `i`. Distinguish the cases in `h1 : i.val < r`. Conclude with `h0 i h1`. Distinguish the cases in `h2 : i.val = r + k`.

Conclude with `hrk i h2`. Establish `hs` using `hx i`. Distinguish the cases in `h3 : i.val < r + k`. Apply the tactic sequence `have e1 : sigI k r i = i := Fin.ext (by rw [sigI_val]; split_ifs <;> omega)`. Establish `e2 : sgnI k r i = 1` using `by unfold sgnI; rw [if_neg h2]`.

Rewrite `hs` using `[e1, e2, one_mul]`. Establish `h4 : (2 : ℂ) * (v : EE k r).ofLp i = 0` using `by linear_combination hs`. Simplify using `using h4`. Apply the tactic sequence `have e3 : (sigI k r i).val < r := by rw [sigI_val]; split_ifs <;> omega`. Rewrite `hs` using `[h0 _ e3, mul_zero]`.

Conclude with `neg_eq_zero.1 hs.symm`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (v : EE k r) = 0`. Use extensionality with `i`. Simplify using `using hall i`.

Simplify using `using LinearMap.finrank_le_finrank_of_injective hinj`. Establish `hspan : Submodule.span ℂ (Set.range d) = Vm`. Apply `Submodule.eq_of_le_of_finrank_le` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`.

Conclude with `hdV a`. Rewrite using `[finrank_span_eq_card hind, Fintype.card_fin]`. Conclude with `hfin`. Establish `heV : x - HE k r x ∈ Vm`. Simplify using `only [hVm, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, map_sub, HE_HE]`.

Normalize the expressions using the abelian group laws. Rewrite `heV` using `[← hspan]`. Take `⟨coef, hcoef⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).1 heV`. Establish `hxd : ∀ a, inner ℂ x (d a) = 0` using `fun a => by`. Rewrite using `[hd, inner_sub_right, inner_eq_zero_symm.1 (hx1 a), inner_eq_zero_symm.1 (hx2 a), sub_zero]`.

Establish `hxe : inner ℂ x (x - HE k r x) = 0`. Rewrite using `[← hcoef, inner_sum]; exact Finset.sum_eq_zero fun a _ => by rw [inner_smul_right, hxd, mul_zero]`. Establish `h1 : inner ℂ (HE k r x) (x - HE k r x) = -inner ℂ x (x - HE k r x)`. Simplify using `only [HE_adj, map_sub, HE_HE, inner_sub_right]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hee : inner ℂ (x - HE k r x) (x - HE k r x) = 0`. Rewrite using `[inner_sub_left, h1, hxe]`. Expand and normalize the polynomial expressions, which then agree. Use `inner_self_eq_zero.1 hee` as an intermediate fact. Rewrite `this` using `[sub_eq_zero]`.

Conclude with `this.symm`.
-/
theorem fix_of_perp (c : Fin (r + 1) → EE k r) (hc : Orthonormal ℂ c)
    (hiso : ∀ a b, inner ℂ (c a) (HE k r (c b)) = 0) (x : EE k r)
    (hx1 : ∀ a, inner ℂ (c a) x = 0) (hx2 : ∀ a, inner ℂ (HE k r (c a)) x = 0) : HE k r x = x := by
  set Vm : Submodule ℂ (EE k r) := LinearMap.ker (HE k r + LinearMap.id) with hVm
  set d : Fin (r + 1) → EE k r := fun a => c a - HE k r (c a) with hd
  have hdV : ∀ a, d a ∈ Vm := fun a => by
    simp only [hVm, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, hd, map_sub, HE_HE]; abel
  have hdd : ∀ a b, inner ℂ (d a) (d b) = if a = b then 2 else 0 := by
    intro a b
    simp only [hd, inner_sub_left, inner_sub_right, HE_adj, HE_HE, hiso, orthonormal_iff_ite.1 hc]
    split_ifs <;> norm_num
  have hind : LinearIndependent ℂ d := by
    refine linearIndependent_of_ne_zero_of_inner_eq_zero (fun a h => ?_) (fun a b hab => ?_)
    · have := hdd a a; rw [h, inner_zero_left, if_pos rfl] at this; norm_num at this
    · show inner ℂ (d a) (d b) = 0
      rw [hdd, if_neg hab]
  have hfin : Module.finrank ℂ Vm ≤ r + 1 := by
    let idx : Fin (r + 1) → Fin (2 * r + k + 1) := fun a =>
      ⟨if a.val < r then a.val else r + k, by split_ifs <;> omega⟩
    let π : Vm →ₗ[ℂ] (Fin (r + 1) → ℂ) :=
      { toFun := fun v a => (v : EE k r).ofLp (idx a)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective π := by
      refine (injective_iff_map_eq_zero π).2 fun v hv => ?_
      have hx : ∀ i, sgnI k r i * (v : EE k r).ofLp (sigI k r i) = -(v : EE k r).ofLp i := by
        intro i
        have h1 := v.2
        simp only [hVm, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply] at h1
        have h2 := congrArg (fun z : EE k r => z.ofLp i) h1
        simp only [HE_apply, WithLp.ofLp_add, WithLp.ofLp_toLp, Pi.add_apply, hpk_mulVec, WithLp.ofLp_zero,
          Pi.zero_apply] at h2
        linear_combination h2
      have h0 : ∀ i : Fin (2 * r + k + 1), i.val < r → (v : EE k r).ofLp i = 0 := by
        intro i hi
        have := congrFun hv ⟨i.val, by omega⟩
        have e : idx ⟨i.val, by omega⟩ = i := Fin.ext (by simp [idx, hi])
        change (v : EE k r).ofLp (idx ⟨i.val, by omega⟩) = 0 at this
        rwa [e] at this
      have hrk : ∀ i : Fin (2 * r + k + 1), i.val = r + k → (v : EE k r).ofLp i = 0 := by
        intro i hi
        have := congrFun hv ⟨r, by omega⟩
        have e : idx ⟨r, by omega⟩ = i := Fin.ext (by simp [idx, hi])
        change (v : EE k r).ofLp (idx ⟨r, by omega⟩) = 0 at this
        rwa [e] at this
      have hall : ∀ i, (v : EE k r).ofLp i = 0 := by
        intro i
        by_cases h1 : i.val < r
        · exact h0 i h1
        by_cases h2 : i.val = r + k
        · exact hrk i h2
        have hs := hx i
        by_cases h3 : i.val < r + k
        · have e1 : sigI k r i = i := Fin.ext (by rw [sigI_val]; split_ifs <;> omega)
          have e2 : sgnI k r i = 1 := by unfold sgnI; rw [if_neg h2]
          rw [e1, e2, one_mul] at hs
          have h4 : (2 : ℂ) * (v : EE k r).ofLp i = 0 := by linear_combination hs
          simpa using h4
        · have e3 : (sigI k r i).val < r := by rw [sigI_val]; split_ifs <;> omega
          rw [h0 _ e3, mul_zero] at hs
          exact neg_eq_zero.1 hs.symm
      apply Subtype.ext
      show (v : EE k r) = 0
      ext i
      simpa using hall i
    simpa using LinearMap.finrank_le_finrank_of_injective hinj
  have hspan : Submodule.span ℂ (Set.range d) = Vm := by
    apply Submodule.eq_of_le_of_finrank_le
    · rw [Submodule.span_le]; rintro _ ⟨a, rfl⟩; exact hdV a
    · rw [finrank_span_eq_card hind, Fintype.card_fin]; exact hfin
  have heV : x - HE k r x ∈ Vm := by
    simp only [hVm, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, map_sub, HE_HE]; abel
  rw [← hspan] at heV
  obtain ⟨coef, hcoef⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 heV
  have hxd : ∀ a, inner ℂ x (d a) = 0 := fun a => by
    rw [hd, inner_sub_right, inner_eq_zero_symm.1 (hx1 a), inner_eq_zero_symm.1 (hx2 a), sub_zero]
  have hxe : inner ℂ x (x - HE k r x) = 0 := by
    rw [← hcoef, inner_sum]; exact Finset.sum_eq_zero fun a _ => by rw [inner_smul_right, hxd, mul_zero]
  have h1 : inner ℂ (HE k r x) (x - HE k r x) = -inner ℂ x (x - HE k r x) := by
    simp only [HE_adj, map_sub, HE_HE, inner_sub_right]; ring
  have hee : inner ℂ (x - HE k r x) (x - HE k r x) = 0 := by
    rw [inner_sub_left, h1, hxe]; ring
  have := inner_self_eq_zero.1 hee
  rw [sub_eq_zero] at this; exact this.symm

end ReciprocityTheory.ChartRestriction.DS.Xi.GS

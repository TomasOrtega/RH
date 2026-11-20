import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussAbsMulSupportFinite

namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

noncomputable def mS {κ : Type} (S : Finset (κ →₀ ℕ)) (j : Fin S.card) : κ →₀ ℕ :=
  (S.equivFin.symm j : κ →₀ ℕ)

/- English proof (translation)
Introduce `i j h`. Conclude with `S.equivFin.symm.injective (Subtype.ext h)`.
-/
theorem mS_injective {κ : Type} (S : Finset (κ →₀ ℕ)) : Function.Injective (mS S) := by
  intro i j h
  exact S.equivFin.symm.injective (Subtype.ext h)

noncomputable def polyOf {κ : Type} (S : Finset (κ →₀ ℕ)) (p : Fin S.card → K) : MvPolynomial κ K :=
  ∑ j, MvPolynomial.monomial (mS S j) (p j)

/- English proof (translation)
Unfold `polyOf`. Rewrite using `[MvPolynomial.coeff_sum]`. Simplify using `only [MvPolynomial.coeff_monomial]`. Rewrite using `[Finset.sum_eq_single j]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Rewrite using `[if_neg]`. Introduce `h`. Conclude with `hb (mS_injective S h)`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ j) h`.
-/
theorem polyOf_coeff {κ : Type} (S : Finset (κ →₀ ℕ)) (p : Fin S.card → K) (j : Fin S.card) :
    (polyOf S p).coeff (mS S j) = p j := by
  classical
  unfold polyOf
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (mS_injective S h)
  · intro h
    exact absurd (Finset.mem_univ j) h

def coordVec {κ : Type} {T : Finset (κ →₀ ℕ)} {r : ℕ} (e : T ≃ Fin r) (P : MvPolynomial κ K) :
    Fin r → K :=
  fun i => P.coeff (e.symm i : κ →₀ ℕ)

noncomputable def bG {κ : Type} (G : MvPolynomial κ K) (S : Finset (κ →₀ ℕ)) {T : Finset (κ →₀ ℕ)}
    {r : ℕ} (e : T ≃ Fin r) (j : Fin S.card) : Fin r → K :=
  coordVec e (G * MvPolynomial.monomial (mS S j) 1)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [bG, coordVec, polyOf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, MvPolynomial.coeff_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[show MvPolynomial.monomial (mS S j) (p j) = MvPolynomial.C (p j) * MvPolynomial.monomial (mS S j) 1 by`. Rewrite using `[MvPolynomial.C_mul_monomial, mul_one]]`.

Rewrite using `[mul_left_comm G, MvPolynomial.coeff_C_mul]`.
-/
theorem sum_smul_bG {κ : Type} (G : MvPolynomial κ K) (S : Finset (κ →₀ ℕ)) {T : Finset (κ →₀ ℕ)}
    {r : ℕ} (e : T ≃ Fin r) (p : Fin S.card → K) :
    ∑ j, p j • bG G S e j = coordVec e (G * polyOf S p) := by
  funext i
  simp only [bG, coordVec, polyOf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show MvPolynomial.monomial (mS S j) (p j) =
      MvPolynomial.C (p j) * MvPolynomial.monomial (mS S j) 1 by
    rw [MvPolynomial.C_mul_monomial, mul_one]]
  rw [mul_left_comm G, MvPolynomial.coeff_C_mul]

/- English proof (translation)
Introduce `s hs`. Rewrite `hs` using `[polyOf, Finset.mul_sum]`. Take `⟨j, -, hj⟩` from `Finset.mem_biUnion.mp (MvPolynomial.support_sum hs)`. Establish `hm : mS S j ∈ S` using `(S.equivFin.symm j).2`. Apply `hST _ hm` to reduce the goal to its premises.

Rewrite `hj`, the goal using `[MvPolynomial.mem_support_iff]`. Rewrite using `[show MvPolynomial.monomial (mS S j) (p j) = MvPolynomial.C (p j) * MvPolynomial.monomial (mS S j) 1 by`. Rewrite `hj` using `[MvPolynomial.C_mul_monomial, mul_one], mul_left_comm G, MvPolynomial.coeff_C_mul]`. Conclude with `right_ne_zero_of_mul hj`.
-/
theorem support_polyOf {κ : Type} [DecidableEq κ] (G : MvPolynomial κ K) (S T : Finset (κ →₀ ℕ))
    (hST : ∀ m ∈ S, (G * MvPolynomial.monomial m 1).support ⊆ T) (p : Fin S.card → K) :
    (G * polyOf S p).support ⊆ T := by
  intro s hs
  rw [polyOf, Finset.mul_sum] at hs
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hs)
  have hm : mS S j ∈ S := (S.equivFin.symm j).2
  apply hST _ hm
  rw [MvPolynomial.mem_support_iff] at hj ⊢
  rw [show MvPolynomial.monomial (mS S j) (p j) =
      MvPolynomial.C (p j) * MvPolynomial.monomial (mS S j) 1 by
    rw [MvPolynomial.C_mul_monomial, mul_one], mul_left_comm G, MvPolynomial.coeff_C_mul] at hj
  exact right_ne_zero_of_mul hj

/- English proof (translation)
Use extensionality with `s`. Rewrite using `[MvPolynomial.coeff_zero]`. Assume the negation of the conclusion as `hs`. Establish `hsT : s ∈ T` using `hP (MvPolynomial.mem_support_iff.mpr hs)`. Establish `h1` using `congrFun h (e ⟨s, hsT⟩)`.

Simplify using `only [coordVec, Equiv.symm_apply_apply, Pi.zero_apply] at h1`. Conclude with `hs h1`.
-/
theorem eq_zero_of_coord {κ : Type} {T : Finset (κ →₀ ℕ)} {r : ℕ} (e : T ≃ Fin r)
    (P : MvPolynomial κ K) (hP : P.support ⊆ T) (h : coordVec e P = 0) : P = 0 := by
  ext s
  rw [MvPolynomial.coeff_zero]
  by_contra hs
  have hsT : s ∈ T := hP (MvPolynomial.mem_support_iff.mpr hs)
  have h1 := congrFun h (e ⟨s, hsT⟩)
  simp only [coordVec, Equiv.symm_apply_apply, Pi.zero_apply] at h1
  exact hs h1

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `p hp j`. Establish `h1 : G * polyOf S p = 0` using `eq_zero_of_coord e _ (support_polyOf G S T hST p) (by rw [← sum_smul_bG]; exact hp)`. Establish `h2 : polyOf S p = 0` using `(mul_eq_zero.mp h1).resolve_left hG`. Rewrite using `[← polyOf_coeff S p j, h2, MvPolynomial.coeff_zero]`.
-/
theorem linInd_bG {κ : Type} [DecidableEq κ] (G : MvPolynomial κ K) (hG : G ≠ 0)
    (S T : Finset (κ →₀ ℕ)) {r : ℕ} (e : T ≃ Fin r)
    (hST : ∀ m ∈ S, (G * MvPolynomial.monomial m 1).support ⊆ T) :
    LinearIndependent K (bG G S e) := by
  rw [Fintype.linearIndependent_iff]
  intro p hp j
  have h1 : G * polyOf S p = 0 :=
    eq_zero_of_coord e _ (support_polyOf G S T hST p) (by rw [← sum_smul_bG]; exact hp)
  have h2 : polyOf S p = 0 := (mul_eq_zero.mp h1).resolve_left hG
  rw [← polyOf_coeff S p j, h2, MvPolynomial.coeff_zero]

/- English proof (translation)
Rewrite using `[← NumberField.FinitePlace.mk_maximalIdeal w]`. Conclude with `NumberField.FinitePlace.norm_le_one K _ y`.
-/
theorem w_int_le_one (w : FinitePlace K) (y : 𝓞 K) : w (y : K) ≤ 1 := by
  rw [← NumberField.FinitePlace.mk_maximalIdeal w]
  exact NumberField.FinitePlace.norm_le_one K _ y

/- English proof (translation)
Use `set G := MvPolynomial.map (algebraMap (𝓞 K) K) G₀ with hGdef`. Establish `hG' : G ≠ 0`. Introduce `h0`. Apply `hG` to reduce the goal to its premises. Conclude with `MvPolynomial.map_injective _ (FaithfulSMul.algebraMap_injective (𝓞 K) K) (by rw [← hGdef, h0, map_zero])`.

Distinguish the cases in `hP : polyOf S p = 0`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[← polyOf_coeff S p j, hP, MvPolynomial.coeff_zero]`. Simplify using the standard rewrite rules. Apply `int_of_le_one` to reduce the goal to its premises.

Introduce `w`. Establish `hGP : ReciprocityTheory.MultiplicativeHeights.gaussAbs w (G * polyOf S p) ≤ 1`. Use `ReciprocityTheory.MultiplicativeHeights.gauss_abs_le_of_coeff_le w _ zero_le_one fun t => ?_` and prove the remaining obligations. Distinguish the cases in `ht : t ∈ T`. Take `⟨y, hy⟩` from `hint (e ⟨t, ht⟩)`.

Establish `: (G * polyOf S p).coeff t = (y : K)` using `by rw [hy]; simp [coordVec]`. Rewrite using `[this]`. Conclude with `w_int_le_one w y`. Rewrite using `[MvPolynomial.notMem_support_iff.mp (fun h => ht (support_polyOf G S T hST p h)), map_zero]`. Conclude with `zero_le_one`.

Rewrite `hGP` using `[ReciprocityTheory.MultiplicativeHeights.gauss_abs_mul w _ _ hG' hP]`. Establish `h1` using `ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs w (polyOf S p) (mS S j)`. Establish `h2` using `ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs w G s`. Rewrite `h1` using `[polyOf_coeff]`. Rewrite `h2` using `[hGdef, MvPolynomial.coeff_map]`.

Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem gauss_int {κ : Type} [Fintype κ] [DecidableEq κ] (G₀ : MvPolynomial κ (𝓞 K))
    (hG : G₀ ≠ 0) (S T : Finset (κ →₀ ℕ)) {r : ℕ} (e : T ≃ Fin r)
    (hST : ∀ m ∈ S, (MvPolynomial.map (algebraMap (𝓞 K) K) G₀ * MvPolynomial.monomial m 1).support ⊆ T)
    (p : Fin S.card → K)
    (hint : ∀ i, ∃ y : 𝓞 K, (y : K) =
      coordVec e (MvPolynomial.map (algebraMap (𝓞 K) K) G₀ * polyOf S p) i)
    (j : Fin S.card) (s : κ →₀ ℕ) : ∃ y : 𝓞 K, (y : K) = p j * ((G₀.coeff s : 𝓞 K) : K) := by
  set G := MvPolynomial.map (algebraMap (𝓞 K) K) G₀ with hGdef
  have hG' : G ≠ 0 := by
    intro h0; apply hG
    exact MvPolynomial.map_injective _ (FaithfulSMul.algebraMap_injective (𝓞 K) K) (by rw [← hGdef, h0, map_zero])
  by_cases hP : polyOf S p = 0
  · refine ⟨0, ?_⟩
    rw [← polyOf_coeff S p j, hP, MvPolynomial.coeff_zero]; simp
  apply int_of_le_one
  intro w
  have hGP : ReciprocityTheory.MultiplicativeHeights.gaussAbs w (G * polyOf S p) ≤ 1 := by
    refine ReciprocityTheory.MultiplicativeHeights.gauss_abs_le_of_coeff_le w _ zero_le_one fun t => ?_
    by_cases ht : t ∈ T
    · obtain ⟨y, hy⟩ := hint (e ⟨t, ht⟩)
      have : (G * polyOf S p).coeff t = (y : K) := by rw [hy]; simp [coordVec]
      rw [this]
      exact w_int_le_one w y
    · rw [MvPolynomial.notMem_support_iff.mp (fun h => ht (support_polyOf G S T hST p h)), map_zero]
      exact zero_le_one
  rw [ReciprocityTheory.MultiplicativeHeights.gauss_abs_mul w _ _ hG' hP] at hGP
  have h1 := ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs w (polyOf S p) (mS S j)
  have h2 := ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs w G s
  rw [polyOf_coeff] at h1
  rw [hGdef, MvPolynomial.coeff_map] at h2
  rw [map_mul]
  calc w (p j) * w ((G₀.coeff s : 𝓞 K) : K)
      ≤ ReciprocityTheory.MultiplicativeHeights.gaussAbs w (polyOf S p) * ReciprocityTheory.MultiplicativeHeights.gaussAbs w G :=
        mul_le_mul h1 h2 (apply_nonneg w _) (le_trans (apply_nonneg w _) h1)
    _ = ReciprocityTheory.MultiplicativeHeights.gaussAbs w G * ReciprocityTheory.MultiplicativeHeights.gaussAbs w (polyOf S p) := mul_comm _ _
    _ ≤ 1 := hGP

end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors

namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Set `f : (Fin k → L) →+ (AddSubgroup.pi Set.univ fun _ : Fin k => L)` to `{ toFun := fun g => ⟨fun i => (g i : M), fun i _ => (g i).2⟩ map_zero' := Subtype.ext (funext fun _ => rfl) map_add' := fun _ _ => Subtype.ext (funext fun _ => rfl) }`. Establish `hsurj : Function.Surjective f`. Introduce `x`. Use `⟨fun i => ⟨(x : Fin k → M) i, ?_⟩, Subtype.ext rfl⟩` and prove the remaining obligations. Use `first`.

Consider the case `exact x.2 i (Set.mem_univ i)`. Consider the case `exact AddSubgroup.mem_pi.mp x.2 i (Set.mem_univ i)`. Establish `hcomap : AddSubgroup.comap f ((AddSubgroup.pi Set.univ fun _ : Fin k => H).addSubgroupOf (AddSubgroup.pi Set.univ fun _ : Fin k => L)) = AddSubgroup.pi Set.univ fun _ : Fin k => H.addSubgroupOf L`. Use extensionality with `g`. Simplify using `only [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]`.

Apply the tactic sequence `all_goals rfl`. Unfold `AddSubgroup.relIndex`. Rewrite using `[← AddSubgroup.index_comap_of_surjective ((AddSubgroup.pi Set.univ fun _ : Fin k => H).addSubgroupOf (AddSubgroup.pi Set.univ fun _ : Fin k => L)) hsurj, hcomap, AddSubgroup.index_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.
-/
theorem relIndex_pi_const {M : Type*} [AddCommGroup M] (H L : AddSubgroup M) (k : ℕ) :
    (AddSubgroup.pi Set.univ fun _ : Fin k => H).relIndex (AddSubgroup.pi Set.univ fun _ : Fin k => L)
      = H.relIndex L ^ k := by
  let f : (Fin k → L) →+ (AddSubgroup.pi Set.univ fun _ : Fin k => L) :=
    { toFun := fun g => ⟨fun i => (g i : M), fun i _ => (g i).2⟩
      map_zero' := Subtype.ext (funext fun _ => rfl)
      map_add' := fun _ _ => Subtype.ext (funext fun _ => rfl) }
  have hsurj : Function.Surjective f := by
    intro x
    refine ⟨fun i => ⟨(x : Fin k → M) i, ?_⟩, Subtype.ext rfl⟩
    first
    | exact x.2 i (Set.mem_univ i)
    | exact AddSubgroup.mem_pi.mp x.2 i (Set.mem_univ i)
  have hcomap : AddSubgroup.comap f ((AddSubgroup.pi Set.univ fun _ : Fin k => H).addSubgroupOf
      (AddSubgroup.pi Set.univ fun _ : Fin k => L)) =
      AddSubgroup.pi Set.univ fun _ : Fin k => H.addSubgroupOf L := by
    ext g
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
    all_goals rfl
  unfold AddSubgroup.relIndex
  rw [← AddSubgroup.index_comap_of_surjective ((AddSubgroup.pi Set.univ fun _ : Fin k => H).addSubgroupOf
      (AddSubgroup.pi Set.univ fun _ : Fin k => L)) hsurj, hcomap, AddSubgroup.index_pi,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

noncomputable def phiB {k r : ℕ} (b : Fin k → Fin r → K) : (Fin k → K) →+ (Fin r → K) :=
  AddMonoidHom.mk' (fun p => ∑ j, p j • b j) (by
    intro p q
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib])

/- English proof (translation)
Use `set G := MvPolynomial.map (algebraMap (𝓞 K) K) G₀ with hGdef`. Establish `hG' : G ≠ 0`. Introduce `h0`. Apply `hG` to reduce the goal to its premises. Conclude with `MvPolynomial.map_injective _ (FaithfulSMul.algebraMap_injective (𝓞 K) K) (by rw [← hGdef, h0, map_zero])`.

Use `set b := bG G S e with hbdef`. Use `set Φ := phiB b with hΦdef`. Establish `hΦ : Function.Injective Φ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `p hp`.

Establish `hli` using `linInd_bG G hG' S T e hST`. Rewrite `hli` using `[Fintype.linearIndependent_iff]`. Conclude with `funext (hli p hp)`. Use `set O1 := (1 : Submodule (𝓞 K) K).toAddSubgroup with hO1`. Use `set I1 := ((((contId G₀ : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).toAddSubgroup with hI1`.

Establish `hspan : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup = (AddSubgroup.pi Set.univ fun _ : Fin S.card => O1).map Φ`. Use extensionality with `x`. Simplify using `only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hx`. Use `⟨fun j => (c j : K), fun j _ => ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(c j : K) ∈ O1`. Rewrite using `[hO1, Submodule.mem_toAddSubgroup, Submodule.mem_one]`. Conclude with `⟨c j, rfl⟩`.

Rewrite using `[← hc]`. Simplify using `only [hΦdef, phiB, AddMonoidHom.mk'_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Conclude with `algebraMap_smul K (c j) (b j)`. Introduce and unpack `⟨p, hp, rfl⟩`.

Establish `hc : ∀ j, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = p j` using `fun j => by`. Establish `: p j ∈ O1` using `hp j (Set.mem_univ j)`. Rewrite `this` using `[hO1, Submodule.mem_toAddSubgroup, Submodule.mem_one]`. Then use the resulting hypothesis. Use `choose c hc using hc`. Use `(Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mpr ⟨c, ?_⟩` and prove the remaining obligations.

Simplify using `only [hΦdef, phiB, AddMonoidHom.mk'_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← hc j]`. Conclude with `(algebraMap_smul K (c j) (b j)).symm`. Establish `hB : (ReciprocityTheory.MultiplicativeHeights.satSub (stdLat K r) b).toAddSubgroup ≤ (AddSubgroup.pi Set.univ fun _ : Fin S.card => I1).map Φ`.

Introduce `x hx`. Rewrite `hx` using `[Submodule.mem_toAddSubgroup]`. Take `⟨hxL, hxK⟩` from `hx`. Take `⟨p, hp⟩` from `(Submodule.mem_span_range_iff_exists_fun K).mp hxK`. Use `AddSubgroup.mem_map.mpr ⟨p, fun j _ => ?_, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `p j ∈ I1`. Rewrite using `[hI1, Submodule.mem_toAddSubgroup]`. Use `mem_inv_of G₀ hG (p j) fun s => ?_` and prove the remaining obligations. Use `gauss_int G₀ hG S T e hST p ?_ j s` and prove the remaining obligations. Introduce `i`.

Establish `h1` using `(Submodule.mem_pi.mp hxL) i (Set.mem_univ i)`. Rewrite `h1` using `[Submodule.mem_one]`. Take `⟨y, hy⟩` from `h1`. Use `⟨y, ?_⟩` and prove the remaining obligations. Rewrite using `[← sum_smul_bG, hp]`.

Conclude with `hy`. Simplify using `only [hΦdef, phiB, AddMonoidHom.mk'_apply]`. Conclude with `hp`. Establish `hidx : O1.relIndex I1 = Ideal.absNorm (contId G₀)`. Use `relIndex_inv G₀ hG` as an intermediate fact.

Conclude with `this` after adjusting the coercions. Establish `hN0 : Ideal.absNorm (contId G₀) ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `contId_ne_bot G₀ hG`. Establish `hpi` using `relIndex_pi_const O1 I1 S.card`.

Rewrite `hpi` using `[hidx]`. Establish `hmm : ((AddSubgroup.pi Set.univ fun _ : Fin S.card => O1).map Φ).relIndex ((AddSubgroup.pi Set.univ fun _ : Fin S.card => I1).map Φ) = Ideal.absNorm (contId G₀) ^ S.card`. Rewrite using `[AddSubgroup.relIndex_map_map_of_injective _ _ hΦ, hpi]`. Establish `hle` using `AddSubgroup.relIndex_le_of_le_right hB (by rw [hmm]; exact pow_ne_zero _ hN0)`. Rewrite `hle` using `[hmm, ← hspan]`.

Establish `hN1 : (1 : ℝ) ≤ (Ideal.absNorm (contId G₀) : ℝ)`. Conclude with `Nat.one_le_iff_ne_zero.mpr hN0` after adjusting the coercions. Break down `Nat.eq_zero_or_pos ((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex (ReciprocityTheory.MultiplicativeHeights.satSub (stdLat K r) b).toAddSubgroup) with h0 | hpos` into its components or cases. Rewrite using `[h0, Nat.cast_zero, Real.log_zero]`. Conclude with `mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hN1)`.

Rewrite using `[← Real.log_pow]`. Use `Real.log_le_log (by exact_mod_cast hpos) ?_` and prove the remaining obligations. Conclude with `hle` after adjusting the coercions.
-/
theorem log_relIndex_le {κ : Type} [Fintype κ] [DecidableEq κ] (G₀ : MvPolynomial κ (𝓞 K))
    (hG : G₀ ≠ 0) (S T : Finset (κ →₀ ℕ)) {r : ℕ} (e : T ≃ Fin r)
    (hST : ∀ m ∈ S,
      (MvPolynomial.map (algebraMap (𝓞 K) K) G₀ * MvPolynomial.monomial m 1).support ⊆ T) :
    Real.log ((Submodule.span (𝓞 K)
        (Set.range (bG (MvPolynomial.map (algebraMap (𝓞 K) K) G₀) S e))).toAddSubgroup.relIndex
      (ReciprocityTheory.MultiplicativeHeights.satSub (stdLat K r)
        (bG (MvPolynomial.map (algebraMap (𝓞 K) K) G₀) S e)).toAddSubgroup : ℝ) ≤
      S.card * Real.log (Ideal.absNorm (contId G₀) : ℝ) := by
  set G := MvPolynomial.map (algebraMap (𝓞 K) K) G₀ with hGdef
  have hG' : G ≠ 0 := by
    intro h0; apply hG
    exact MvPolynomial.map_injective _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)
      (by rw [← hGdef, h0, map_zero])
  set b := bG G S e with hbdef
  set Φ := phiB b with hΦdef
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    have hli := linInd_bG G hG' S T e hST
    rw [Fintype.linearIndependent_iff] at hli
    exact funext (hli p hp)
  set O1 := (1 : Submodule (𝓞 K) K).toAddSubgroup with hO1
  set I1 := ((((contId G₀ : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) :
    Submodule (𝓞 K) K).toAddSubgroup with hI1
  have hspan : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup =
      (AddSubgroup.pi Set.univ fun _ : Fin S.card => O1).map Φ := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map]
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hx
      refine ⟨fun j => (c j : K), fun j _ => ?_, ?_⟩
      · change (c j : K) ∈ O1
        rw [hO1, Submodule.mem_toAddSubgroup, Submodule.mem_one]; exact ⟨c j, rfl⟩
      · rw [← hc]
        simp only [hΦdef, phiB, AddMonoidHom.mk'_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact algebraMap_smul K (c j) (b j)
    · rintro ⟨p, hp, rfl⟩
      have hc : ∀ j, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = p j := fun j => by
        have : p j ∈ O1 := hp j (Set.mem_univ j)
        rwa [hO1, Submodule.mem_toAddSubgroup, Submodule.mem_one] at this
      choose c hc using hc
      refine (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mpr ⟨c, ?_⟩
      simp only [hΦdef, phiB, AddMonoidHom.mk'_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hc j]
      exact (algebraMap_smul K (c j) (b j)).symm
  have hB : (ReciprocityTheory.MultiplicativeHeights.satSub (stdLat K r) b).toAddSubgroup ≤
      (AddSubgroup.pi Set.univ fun _ : Fin S.card => I1).map Φ := by
    intro x hx
    rw [Submodule.mem_toAddSubgroup] at hx
    obtain ⟨hxL, hxK⟩ := hx
    obtain ⟨p, hp⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hxK
    refine AddSubgroup.mem_map.mpr ⟨p, fun j _ => ?_, ?_⟩
    · change p j ∈ I1
      rw [hI1, Submodule.mem_toAddSubgroup]
      refine mem_inv_of G₀ hG (p j) fun s => ?_
      refine gauss_int G₀ hG S T e hST p ?_ j s
      intro i
      have h1 := (Submodule.mem_pi.mp hxL) i (Set.mem_univ i)
      rw [Submodule.mem_one] at h1
      obtain ⟨y, hy⟩ := h1
      refine ⟨y, ?_⟩
      rw [← sum_smul_bG, hp]
      exact hy
    · simp only [hΦdef, phiB, AddMonoidHom.mk'_apply]
      exact hp
  have hidx : O1.relIndex I1 = Ideal.absNorm (contId G₀) := by
    have := relIndex_inv G₀ hG
    exact_mod_cast this
  have hN0 : Ideal.absNorm (contId G₀) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact contId_ne_bot G₀ hG
  have hpi := relIndex_pi_const O1 I1 S.card
  rw [hidx] at hpi
  have hmm : ((AddSubgroup.pi Set.univ fun _ : Fin S.card => O1).map Φ).relIndex
      ((AddSubgroup.pi Set.univ fun _ : Fin S.card => I1).map Φ) =
      Ideal.absNorm (contId G₀) ^ S.card := by
    rw [AddSubgroup.relIndex_map_map_of_injective _ _ hΦ, hpi]
  have hle := AddSubgroup.relIndex_le_of_le_right hB (by rw [hmm]; exact pow_ne_zero _ hN0)
  rw [hmm, ← hspan] at hle
  have hN1 : (1 : ℝ) ≤ (Ideal.absNorm (contId G₀) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN0
  rcases Nat.eq_zero_or_pos ((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex
      (ReciprocityTheory.MultiplicativeHeights.satSub (stdLat K r) b).toAddSubgroup) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hN1)
  · rw [← Real.log_pow]
    refine Real.log_le_log (by exact_mod_cast hpos) ?_
    exact_mod_cast hle

end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors

namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors

open NumberField

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Rewrite using `[Finset.sum_subset hP (fun s _ hs => by`. Establish `h0 : P.coeff s = 0`. Assume the negation of the conclusion as `h`. Conclude with `hs (MvPolynomial.mem_support_iff.mpr h)`. Rewrite using `[h0, zero_mul])]`.

Rewrite using `[← Finset.sum_coe_sort T]`. Conclude with `Fintype.sum_equiv e _ _ (fun t => by simp)`.
-/
theorem sum_support_eq {κ : Type} {T : Finset (κ →₀ ℕ)} {r : ℕ} (e : T ≃ Fin r)
    (P Q : MvPolynomial κ ℂ) (hP : P.support ⊆ T) :
    ∑ s ∈ P.support, P.coeff s * star (Q.coeff s) =
      ∑ i : Fin r, P.coeff (e.symm i : κ →₀ ℕ) * star (Q.coeff (e.symm i : κ →₀ ℕ)) := by
  rw [Finset.sum_subset hP (fun s _ hs => by
    have h0 : P.coeff s = 0 := by
      by_contra h
      exact hs (MvPolynomial.mem_support_iff.mpr h)
    rw [h0, zero_mul])]
  rw [← Finset.sum_coe_sort T]
  exact Fintype.sum_equiv e _ _ (fun t => by simp)

/- English proof (translation)
Establish `hσG : MvPolynomial.map σ G ≠ 0`. Introduce `h0`. Apply `hG` to reduce the goal to its premises. Conclude with `MvPolynomial.map_injective σ σ.injective (by rw [h0, map_zero])`. Establish `hgram` using `ReciprocityTheory.MultiplicativeHeights.Closed.gram κ (MvPolynomial.map σ G) S hσG`.

Establish `hmap : ∀ m : κ →₀ ℕ, MvPolynomial.map σ G * MvPolynomial.monomial m 1 = MvPolynomial.map σ (G * MvPolynomial.monomial m 1)`. Introduce `m`. Rewrite using `[map_mul, MvPolynomial.map_monomial, σ.map_one]`. Establish `heq : (ReciprocityTheory.MultiplicativeHeights.gramC (1 : Matrix (Fin r) (Fin r) ℂ) σ (bG G S e)).det = (Matrix.of fun m m' : S => ReciprocityTheory.MultiplicativeHeights.polyInner (MvPolynomial.map σ G * MvPolynomial.monomial (m : κ →₀ ℕ) 1) (MvPolynomial.map σ G * MvPolynomial. …`. Rewrite using `[← Matrix.det_submatrix_equiv_self S.equivFin.symm, ← Matrix.det_transpose]`.

Use `congr 1`. Use extensionality with `i j`. Simplify using `only [Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.of_apply, ReciprocityTheory.MultiplicativeHeights.gramC, Matrix.one_mulVec, ReciprocityTheory.MultiplicativeHeights.polyInner]`. Rewrite using `[sum_support_eq e]`. Simplify using `only [dotProduct, hmap, MvPolynomial.coeff_map, ReciprocityTheory.MultiplicativeHeights.embVec, bG, coordVec, mS, Pi.star_apply]`.

Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Rewrite using `[hmap]`. Conclude with `(MvPolynomial.support_map_subset _ _).trans (hST _ (S.equivFin.symm i).2)`. Establish `h1` using `Real.log_le_log (Real.exp_pos _) hgram`.

Rewrite `h1` using `[Real.log_exp, ← heq]`. Conclude with `h1`.
-/
theorem gram_le {κ : Type} [Fintype κ] [DecidableEq κ] (G : MvPolynomial κ K) (hG : G ≠ 0)
    (S T : Finset (κ →₀ ℕ)) {r : ℕ} (e : T ≃ Fin r)
    (hST : ∀ m ∈ S, (G * MvPolynomial.monomial m 1).support ⊆ T) (σ : K →+* ℂ) :
    2 * (S.card : ℝ) * ReciprocityTheory.MultiplicativeHeights.torusMean (MvPolynomial.map σ G) ≤
      Real.log (ReciprocityTheory.MultiplicativeHeights.gramC (1 : Matrix (Fin r) (Fin r) ℂ) σ (bG G S e)).det.re := by
  have hσG : MvPolynomial.map σ G ≠ 0 := by
    intro h0; apply hG
    exact MvPolynomial.map_injective σ σ.injective (by rw [h0, map_zero])
  have hgram := ReciprocityTheory.MultiplicativeHeights.Closed.gram κ (MvPolynomial.map σ G) S hσG
  have hmap : ∀ m : κ →₀ ℕ, MvPolynomial.map σ G * MvPolynomial.monomial m 1 =
      MvPolynomial.map σ (G * MvPolynomial.monomial m 1) := by
    intro m
    rw [map_mul, MvPolynomial.map_monomial, σ.map_one]
  have heq : (ReciprocityTheory.MultiplicativeHeights.gramC (1 : Matrix (Fin r) (Fin r) ℂ) σ (bG G S e)).det =
      (Matrix.of fun m m' : S => ReciprocityTheory.MultiplicativeHeights.polyInner
        (MvPolynomial.map σ G * MvPolynomial.monomial (m : κ →₀ ℕ) 1)
        (MvPolynomial.map σ G * MvPolynomial.monomial (m' : κ →₀ ℕ) 1)).det := by
    rw [← Matrix.det_submatrix_equiv_self S.equivFin.symm, ← Matrix.det_transpose]
    congr 1
    ext i j
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.of_apply, ReciprocityTheory.MultiplicativeHeights.gramC,
      Matrix.one_mulVec, ReciprocityTheory.MultiplicativeHeights.polyInner]
    rw [sum_support_eq e]
    · simp only [dotProduct, hmap, MvPolynomial.coeff_map, ReciprocityTheory.MultiplicativeHeights.embVec, bG, coordVec, mS,
        Pi.star_apply]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [mul_comm]
    · rw [hmap]
      exact (MvPolynomial.support_map_subset _ _).trans (hST _ (S.equivFin.symm i).2)
  have h1 := Real.log_le_log (Real.exp_pos _) hgram
  rw [Real.log_exp, ← heq] at h1
  exact h1

end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors

namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors

open NumberField
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K)) (F.support.image fun s => F.coeff s)`. Establish `hy : ∀ s, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = (b : 𝓞 K) • F.coeff s`. Introduce `s`. Distinguish the cases in `hs : s ∈ F.support`. Conclude with `RingHom.mem_rangeS.mp (hb _ (Finset.mem_image_of_mem _ hs))`.

Establish `h0 : F.coeff s = 0`. Assume the negation of the conclusion as `h`. Conclude with `hs (MvPolynomial.mem_support_iff.mpr h)`. Conclude with `⟨0, by rw [map_zero, h0, smul_zero]⟩`. Use `choose y hy using hy`.

Use `⟨algebraMap (𝓞 K) K b, ∑ s ∈ F.support, MvPolynomial.monomial s (y s), ?_, ?_⟩` and prove the remaining obligations. Conclude with `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2`. Rewrite using `[map_sum]`. Simplify using `only [MvPolynomial.map_monomial, hy]`. Use `conv_rhs => rw [MvPolynomial.as_sum F]`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.C_mul_monomial, Algebra.smul_def]`.
-/
theorem exists_int_multiple {κ : Type} (F : MvPolynomial κ K) :
    ∃ (c : K) (G₀ : MvPolynomial κ (𝓞 K)), c ≠ 0 ∧
      MvPolynomial.map (algebraMap (𝓞 K) K) G₀ = MvPolynomial.C c * F := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (F.support.image fun s => F.coeff s)
  have hy : ∀ s, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = (b : 𝓞 K) • F.coeff s := by
    intro s
    by_cases hs : s ∈ F.support
    · exact RingHom.mem_rangeS.mp (hb _ (Finset.mem_image_of_mem _ hs))
    · have h0 : F.coeff s = 0 := by
        by_contra h
        exact hs (MvPolynomial.mem_support_iff.mpr h)
      exact ⟨0, by rw [map_zero, h0, smul_zero]⟩
  choose y hy using hy
  refine ⟨algebraMap (𝓞 K) K b, ∑ s ∈ F.support, MvPolynomial.monomial s (y s), ?_, ?_⟩
  · exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  · rw [map_sum]
    simp only [MvPolynomial.map_monomial, hy]
    conv_rhs => rw [MvPolynomial.as_sum F]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [MvPolynomial.C_mul_monomial, Algebra.smul_def]

end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors

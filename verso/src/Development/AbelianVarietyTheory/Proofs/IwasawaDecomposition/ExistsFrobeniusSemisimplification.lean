import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowEqPowOfWeilDegreeEqSmoothStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilGroupIsSemisimpleOfSemisimpleFrobStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

section Lin

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/- English proof (translation)
Establish `key : ∀ (μ : ℂ) (k : ℕ), (f - (c * μ) • (1 : End ℂ V)) ^ k * N = c ^ k • (N * (f - μ • (1 : End ℂ V)) ^ k)`. Introduce `μ k`. Establish `h1 : (f - (c * μ) • (1 : End ℂ V)) * N = c • (N * (f - μ • (1 : End ℂ V)))`. Rewrite using `[sub_mul, h, mul_sub, smul_sub]`. Simplify using `[smul_smul]`.

Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ', mul_assoc, ih, mul_smul_comm, ← mul_assoc, h1, smul_mul_assoc, smul_smul, mul_assoc, ← pow_succ', ← pow_succ]`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations.

Establish `hv : v ∈ ⨆ μ, f.maxGenEigenspace μ`. Rewrite using `[End.iSup_maxGenEigenspace_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hv using Submodule.iSup_induction' with`. Consider the case `mem μ v hv`.

Establish `h1` using `End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil hv hc hs.isFinitelySemisimple hn`. Establish `h2 : N v ∈ f.maxGenEigenspace (c * μ)`. Rewrite `hv`, the goal using `[End.mem_maxGenEigenspace]`. Take `⟨k, hk⟩` from `hv`. Use `⟨k, ?_⟩` and prove the remaining obligations.

Use `LinearMap.congr_fun (key μ k) v` as an intermediate fact. Simplify `this` using `[hk]`. Establish `h3` using `End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil h2 hc hs.isFinitelySemisimple hn`. Simplify using `[h1, h3, smul_smul]`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem semisimplePart_mul_eq {f s N : End ℂ V} {c : ℂ} (hc : Commute f s) (hs : s.IsSemisimple)
    (hn : IsNilpotent (f - s)) (h : f * N = c • (N * f)) : s * N = c • (N * s) := by
  have key : ∀ (μ : ℂ) (k : ℕ), (f - (c * μ) • (1 : End ℂ V)) ^ k * N =
      c ^ k • (N * (f - μ • (1 : End ℂ V)) ^ k) := by
    intro μ k
    have h1 : (f - (c * μ) • (1 : End ℂ V)) * N = c • (N * (f - μ • (1 : End ℂ V))) := by
      rw [sub_mul, h, mul_sub, smul_sub]
      simp [smul_smul]
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_assoc, ih, mul_smul_comm, ← mul_assoc, h1, smul_mul_assoc, smul_smul,
        mul_assoc, ← pow_succ', ← pow_succ]
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ ⨆ μ, f.maxGenEigenspace μ := by
    rw [End.iSup_maxGenEigenspace_eq_top]; trivial
  induction hv using Submodule.iSup_induction' with
  | mem μ v hv =>
    have h1 := End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil hv hc
      hs.isFinitelySemisimple hn
    have h2 : N v ∈ f.maxGenEigenspace (c * μ) := by
      rw [End.mem_maxGenEigenspace] at hv ⊢
      obtain ⟨k, hk⟩ := hv
      refine ⟨k, ?_⟩
      have := LinearMap.congr_fun (key μ k) v
      simpa [hk] using this
    have h3 := End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil h2 hc
      hs.isFinitelySemisimple hn
    simp [h1, h3, smul_smul]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]

end Lin

/- English proof (translation)
Rewrite using `[← mul_geom_sum]`. Use `Commute.isNilpotent_mul_right ?_ hu` and prove the remaining obligations. Conclude with `Commute.sum_right _ _ _ fun i _ => ((Commute.refl u).pow_right i).sub_left (Commute.one_left _)`.
-/
theorem isNilpotent_pow_sub_one {R : Type*} [Ring R] {u : R} (hu : IsNilpotent (u - 1)) (k : ℕ) :
    IsNilpotent (u ^ k - 1) := by
  rw [← mul_geom_sum]
  refine Commute.isNilpotent_mul_right ?_ hu
  exact Commute.sum_right _ _ _ fun i _ =>
    ((Commute.refl u).pow_right i).sub_left (Commute.one_left _)

/- English proof (translation)
Use `set L : End ℂ R := LinearMap.mulLeft ℂ (u : R) with hL`. Use `set M : End ℂ R := LinearMap.mulRight ℂ ((u⁻¹ : Rˣ) : R) with hM`. Establish `hLM : Commute L M` using `LinearMap.commute_mulLeft_right _ _`. Establish `hu' : IsNilpotent (((u⁻¹ : Rˣ) : R) - 1)`. Establish `: ((u⁻¹ : Rˣ) : R) - 1 = -(((u : R) - 1) * (u⁻¹ : Rˣ))` using `by simp [sub_mul]`.

Rewrite using `[this]`. Use `(Commute.isNilpotent_mul_right ?_ hu).neg` and prove the remaining obligations. Conclude with `(Commute.refl (u : R)).units_inv_right.sub_left (Commute.one_left _)`. Establish `hL1 : IsNilpotent (L - 1)`. Establish `: L - 1 = LinearMap.mulLeft ℂ ((u : R) - 1)` using `by ext; simp [hL, sub_mul]`.

Rewrite using `[this]`. Conclude with `(LinearMap.isNilpotent_mulLeft_iff _ _).mpr hu`. Establish `hM1 : IsNilpotent (M - 1)`. Establish `: M - 1 = LinearMap.mulRight ℂ (((u⁻¹ : Rˣ) : R) - 1)` using `by ext; simp [hM, mul_sub]`. Rewrite using `[this]`.

Conclude with `(LinearMap.isNilpotent_mulRight_iff _ _).mpr hu'`. Establish `hU : IsNilpotent (L * M - 1)`. Establish `: L * M - 1 = (L - 1) * M + (M - 1)` using `by noncomm_ring`. Rewrite using `[this]`. Establish `c1 : Commute (L - 1) M` using `hLM.sub_left (Commute.one_left _)`.

Use `Commute.isNilpotent_add ?_ (c1.isNilpotent_mul_right hL1) hM1` and prove the remaining obligations. Conclude with `(c1.mul_left (Commute.refl M)).sub_right (Commute.one_right _)`. Use `set U := L * M with hUdef`. Establish `hsum : IsUnit (∑ i ∈ Finset.range m, U ^ i)`. Establish `e : ∑ i ∈ Finset.range m, U ^ i = algebraMap ℂ (End ℂ R) (m : ℂ) + ∑ i ∈ Finset.range m, (U ^ i - 1)`.

Simplify using `[Finset.sum_sub_distrib]`. Rewrite using `[e]`. Use `IsNilpotent.isUnit_add_left_of_commute ?_ ?_ ?_` and prove the remaining obligations. Use `Commute.isNilpotent_sum (fun i _ => isNilpotent_pow_sub_one hU i) fun i j _ _ => ?_` and prove the remaining obligations. Conclude with `(((Commute.refl U).pow_pow i j).sub_left (Commute.one_left _)).sub_right (Commute.one_right _)`.

Conclude with `(IsUnit.mk0 (m : ℂ) (by exact_mod_cast hm.ne')).map _`. Conclude with `Algebra.commute_algebraMap_right _ _`. Establish `h1 : (U ^ m - 1) T = 0`. Rewrite using `[hUdef, hLM.mul_pow, hL, hM, LinearMap.pow_mulLeft, LinearMap.pow_mulRight]`. Simplify using `only [LinearMap.sub_apply, End.mul_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, End.one_apply]`.

Rewrite using `[← mul_assoc, h.eq, mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[← geom_sum_mul, End.mul_apply]`. Establish `h2 : (U - 1) T = 0`. Use `((End.isUnit_iff _).mp hsum).1` as an intermediate fact.

Conclude with `this (by rw [h1, map_zero])`. Establish `h3 : (u : R) * (T * (u⁻¹ : Rˣ)) = T`. Simplify `h2` using `[hUdef, hL, hM, sub_eq_zero]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem commute_of_commute_pow {R : Type*} [Ring R] [Algebra ℂ R] {u : Rˣ} {T : R} {m : ℕ}
    (hm : 0 < m) (hu : IsNilpotent ((u : R) - 1)) (h : Commute ((u : R) ^ m) T) :
    Commute (u : R) T := by
  set L : End ℂ R := LinearMap.mulLeft ℂ (u : R) with hL
  set M : End ℂ R := LinearMap.mulRight ℂ ((u⁻¹ : Rˣ) : R) with hM
  have hLM : Commute L M := LinearMap.commute_mulLeft_right _ _
  have hu' : IsNilpotent (((u⁻¹ : Rˣ) : R) - 1) := by
    have : ((u⁻¹ : Rˣ) : R) - 1 = -(((u : R) - 1) * (u⁻¹ : Rˣ)) := by simp [sub_mul]
    rw [this]
    refine (Commute.isNilpotent_mul_right ?_ hu).neg
    exact (Commute.refl (u : R)).units_inv_right.sub_left (Commute.one_left _)
  have hL1 : IsNilpotent (L - 1) := by
    have : L - 1 = LinearMap.mulLeft ℂ ((u : R) - 1) := by ext; simp [hL, sub_mul]
    rw [this]; exact (LinearMap.isNilpotent_mulLeft_iff _ _).mpr hu
  have hM1 : IsNilpotent (M - 1) := by
    have : M - 1 = LinearMap.mulRight ℂ (((u⁻¹ : Rˣ) : R) - 1) := by ext; simp [hM, mul_sub]
    rw [this]; exact (LinearMap.isNilpotent_mulRight_iff _ _).mpr hu'
  have hU : IsNilpotent (L * M - 1) := by
    have : L * M - 1 = (L - 1) * M + (M - 1) := by noncomm_ring
    rw [this]
    have c1 : Commute (L - 1) M := hLM.sub_left (Commute.one_left _)
    refine Commute.isNilpotent_add ?_ (c1.isNilpotent_mul_right hL1) hM1
    exact (c1.mul_left (Commute.refl M)).sub_right (Commute.one_right _)
  set U := L * M with hUdef
  have hsum : IsUnit (∑ i ∈ Finset.range m, U ^ i) := by
    have e : ∑ i ∈ Finset.range m, U ^ i =
        algebraMap ℂ (End ℂ R) (m : ℂ) + ∑ i ∈ Finset.range m, (U ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [e]
    refine IsNilpotent.isUnit_add_left_of_commute ?_ ?_ ?_
    · refine Commute.isNilpotent_sum (fun i _ => isNilpotent_pow_sub_one hU i) fun i j _ _ => ?_
      exact (((Commute.refl U).pow_pow i j).sub_left (Commute.one_left _)).sub_right
        (Commute.one_right _)
    · exact (IsUnit.mk0 (m : ℂ) (by exact_mod_cast hm.ne')).map _
    · exact Algebra.commute_algebraMap_right _ _
  have h1 : (U ^ m - 1) T = 0 := by
    rw [hUdef, hLM.mul_pow, hL, hM, LinearMap.pow_mulLeft, LinearMap.pow_mulRight]
    simp only [LinearMap.sub_apply, End.mul_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, End.one_apply]
    rw [← mul_assoc, h.eq, mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
      ← Units.val_mul, inv_pow]
    simp
  rw [← geom_sum_mul, End.mul_apply] at h1
  have h2 : (U - 1) T = 0 := by
    have := ((End.isUnit_iff _).mp hsum).1
    exact this (by rw [h1, map_zero])
  have h3 : (u : R) * (T * (u⁻¹ : Rˣ)) = T := by
    simpa [hUdef, hL, hM, sub_eq_zero] using h2
  calc (u : R) * T = (u : R) * (T * (u⁻¹ : Rˣ)) * u := by simp [mul_assoc]
    _ = T * u := by rw [h3]

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h V _ _ _ ρ N hρ hN hc`. Take `⟨n, hn, s, hs, hnil, hss, hf⟩` from `End.exists_isNilpotent_isSemisimple (f := ρ (frob h))`. Use `set f := ρ (frob h) with hfdef`. Establish `hfn : Commute f n` using `Algebra.commute_of_mem_adjoin_self hn`. Establish `hfs : Commute f s` using `Algebra.commute_of_mem_adjoin_self hs`.

Establish `hsub : f - s = n` using `by rw [hf]; simp`. Establish `hns : Commute n s` using `by rw [← hsub]; exact hfs.sub_left (Commute.refl s)`. Establish `hfu : IsUnit f` using `(Group.isUnit (frob h)).map ρ`. Establish `hsu : IsUnit s`. Establish `: s = f + -n` using `by rw [← hsub]; simp`.

Rewrite using `[this]`. Conclude with `hnil.neg.isUnit_add_left_of_commute hfu hfn.symm.neg_left`. Take `⟨S, rfl⟩` from `hsu`. Take `⟨F, hF⟩` from `hfu`. Establish `hFS : Commute F S`.

Conclude with `Units.ext (by rw [Units.val_mul, Units.val_mul, hF]; exact hfs.eq)`. Use `set u : (End ℂ V)ˣ := S⁻¹ * F with hu`. Establish `huS : Commute u S` using `(Commute.refl S).inv_left.mul_left hFS`. Establish `hSu : S * u = F` using `by simp [hu]`. Establish `hSu' : (S : End ℂ V) * u = f` using `by rw [← Units.val_mul, hSu, hF]`.

Establish `huS' : Commute (u : End ℂ V) (S : End ℂ V)` using `huS.units_val`. Establish `hunil : IsNilpotent ((u : End ℂ V) - 1)`. Establish `: (u : End ℂ V) - 1 = n * (S⁻¹ : (End ℂ V)ˣ)`. Rewrite using `[hns.units_inv_right.eq, ← hsub, hu, Units.val_mul, hF, mul_sub]`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `hns.units_inv_right.isNilpotent_mul_right hnil`. Establish `huN : Commute (u : End ℂ V) N`. Establish `h1` using `hc (frob h)`. Establish `h2` using `semisimplePart_mul_eq hfs hss (hsub ▸ hnil) h1`.

Establish `hq : ((normV w : ℕ) : ℂ) ^ deg (frob h) ≠ 0` using `zpow_ne_zero _ (Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot)`. Establish `h3 : (S : End ℂ V) * ((u : End ℂ V) * N) = S * (N * u)`. Rewrite using `[← mul_assoc, hSu', h1, ← mul_assoc, h2, smul_mul_assoc, mul_assoc, hSu']`. Conclude with `(Units.mul_right_inj S).mp h3`. Establish `huρ : ∀ τ, Commute (u : End ℂ V) (ρ τ)`.

Introduce `τ`. Take `⟨m, hm, e⟩` from `GlobalTheory.T.exists_pow_eq_pow_of_weilDegree_eq_smooth E Ω A w h V ρ hρ (frob h) (τ * frob h * τ⁻¹) (by simp)`. Establish `c1 : f ^ m * ρ τ = (1 : ℂ) • (ρ τ * f ^ m)`. Rewrite using `[one_smul]`. Use `conv_lhs => rw [hfdef, e]`.

Rewrite using `[hfdef, ← map_pow, ← map_pow, ← map_mul, ← map_mul, conj_pow]`. Simplify using the standard rewrite rules. Establish `epow : f ^ m = (S : End ℂ V) ^ m * (u : End ℂ V) ^ m`. Rewrite using `[← huS'.symm.mul_pow, hSu']`. Establish `c2` using `semisimplePart_mul_eq (hfs.pow_pow m m) (hss.pow m) (by`.

Establish `: f ^ m - (S : End ℂ V) ^ m = ((u : End ℂ V) ^ m - 1) * (S : End ℂ V) ^ m`. Rewrite using `[epow, sub_mul, (huS'.pow_pow m m).eq, one_mul]`. Rewrite using `[this]`. Conclude with `((huS'.pow_pow m m).sub_left (Commute.one_left _)).isNilpotent_mul_right (isNilpotent_pow_sub_one hunil m)) c1`. Rewrite `c1`, `c2` using `[one_smul]`.

Use `commute_of_commute_pow hm hunil ?_` and prove the remaining obligations. Establish `h3 : ((S ^ m : (End ℂ V)ˣ) : End ℂ V) * ((u : End ℂ V) ^ m * ρ τ) = (S ^ m : (End ℂ V)ˣ) * (ρ τ * (u : End ℂ V) ^ m)`. Rewrite using `[Units.val_pow_eq_pow_val, ← mul_assoc, ← epow, c1, ← mul_assoc, c2, mul_assoc, ← epow]`. Conclude with `(Units.mul_right_inj _).mp h3`. Set `ρ' : Representation ℂ (Weil h) V` to `{ toFun := fun σ => ρ σ * ((u ^ (-deg σ) : (End ℂ V)ˣ) : End ℂ V) map_one' := by simp map_mul' := fun σ τ => by`.

Use `((huρ τ).units_zpow_left (-deg σ)).eq` as an intermediate fact. Rewrite using `[map_mul, deg_mul, neg_add, zpow_add, Units.val_mul]`. Simplify using `only [mul_assoc]`. Rewrite using `[← mul_assoc _ (ρ τ) (Units.val (u ^ (-deg τ))), this, mul_assoc] }`. Establish `hρ' : ∀ σ, ρ' σ = ρ σ * ((u ^ (-deg σ) : (End ℂ V)ˣ) : End ℂ V)` using `fun _ => rfl`.

Establish `hsm : IsSmooth ρ'` using `.of_open hρ (by simp) fun σ hσ => by`. Establish `: ρ (ineIncl h σ) = 1` using `hσ`. Rewrite using `[hρ', this]`. Simplify using the standard rewrite rules. Establish `hfr : ρ' (frob h) = S`.

Rewrite using `[hρ', deg_frob, ← hfdef, ← hSu', mul_assoc, ← Units.val_mul]`. Simplify using the standard rewrite rules. Use `⟨⟨ρ', N, hsm, GlobalTheory.T.weilGroup_isSemisimple_of_semisimple_frob E Ω A w h V ρ' hsm (frob h) deg_frob (hfr ▸ hss), hN, fun σ => ?_⟩, u, rfl, hunil, huN, huρ, fun σ => ?_⟩` and prove the remaining obligations. Rewrite using `[hρ', mul_assoc, (huN.units_zpow_left (-deg σ)).eq, ← mul_assoc, hc, smul_mul_assoc, mul_assoc]`. Use `show _ = ρ' σ * _`.

Rewrite using `[hρ', mul_assoc, ← Units.val_mul, ← zpow_add]`. Simplify using the standard rewrite rules.
-/
theorem exists_frobenius_semisimplification : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ (Weil h) V) (N : End ℂ V), IsSmooth ρ → IsNilpotent N → (∀ σ, ρ σ * N = ((normV w : ℕ) : ℂ) ^ deg σ • (N * ρ σ)) → ∃ (a : WDRep h V) (u : (End ℂ V)ˣ), a.N = N ∧ IsNilpotent ((u : End ℂ V) - 1) ∧ Commute (u : End ℂ V) N ∧ (∀ σ, Commute (u : End ℂ V) (ρ σ)) ∧ ∀ σ, ρ σ = a.ρ σ * ((u ^ deg σ : (End ℂ V)ˣ) : End ℂ V) := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ ρ N hρ hN hc
  obtain ⟨n, hn, s, hs, hnil, hss, hf⟩ := End.exists_isNilpotent_isSemisimple (f := ρ (frob h))
  set f := ρ (frob h) with hfdef
  have hfn : Commute f n := Algebra.commute_of_mem_adjoin_self hn
  have hfs : Commute f s := Algebra.commute_of_mem_adjoin_self hs
  have hsub : f - s = n := by rw [hf]; simp
  have hns : Commute n s := by rw [← hsub]; exact hfs.sub_left (Commute.refl s)
  have hfu : IsUnit f := (Group.isUnit (frob h)).map ρ
  have hsu : IsUnit s := by
    have : s = f + -n := by rw [← hsub]; simp
    rw [this]
    exact hnil.neg.isUnit_add_left_of_commute hfu hfn.symm.neg_left
  obtain ⟨S, rfl⟩ := hsu
  obtain ⟨F, hF⟩ := hfu
  have hFS : Commute F S := by
    exact Units.ext (by rw [Units.val_mul, Units.val_mul, hF]; exact hfs.eq)
  set u : (End ℂ V)ˣ := S⁻¹ * F with hu
  have huS : Commute u S := (Commute.refl S).inv_left.mul_left hFS
  have hSu : S * u = F := by simp [hu]
  have hSu' : (S : End ℂ V) * u = f := by rw [← Units.val_mul, hSu, hF]
  have huS' : Commute (u : End ℂ V) (S : End ℂ V) := huS.units_val
  have hunil : IsNilpotent ((u : End ℂ V) - 1) := by
    have : (u : End ℂ V) - 1 = n * (S⁻¹ : (End ℂ V)ˣ) := by
      rw [hns.units_inv_right.eq, ← hsub, hu, Units.val_mul, hF, mul_sub]; simp
    rw [this]
    exact hns.units_inv_right.isNilpotent_mul_right hnil
  have huN : Commute (u : End ℂ V) N := by
    have h1 := hc (frob h)
    have h2 := semisimplePart_mul_eq hfs hss (hsub ▸ hnil) h1
    have hq : ((normV w : ℕ) : ℂ) ^ deg (frob h) ≠ 0 :=
      zpow_ne_zero _ (Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot)
    have h3 : (S : End ℂ V) * ((u : End ℂ V) * N) = S * (N * u) := by
      rw [← mul_assoc, hSu', h1, ← mul_assoc, h2, smul_mul_assoc, mul_assoc, hSu']
    exact (Units.mul_right_inj S).mp h3
  have huρ : ∀ τ, Commute (u : End ℂ V) (ρ τ) := by
    intro τ
    obtain ⟨m, hm, e⟩ := GlobalTheory.T.exists_pow_eq_pow_of_weilDegree_eq_smooth E Ω A w h V ρ hρ (frob h) (τ * frob h * τ⁻¹) (by simp)
    have c1 : f ^ m * ρ τ = (1 : ℂ) • (ρ τ * f ^ m) := by
      rw [one_smul]
      conv_lhs => rw [hfdef, e]
      rw [hfdef, ← map_pow, ← map_pow, ← map_mul, ← map_mul, conj_pow]
      simp
    have epow : f ^ m = (S : End ℂ V) ^ m * (u : End ℂ V) ^ m := by
      rw [← huS'.symm.mul_pow, hSu']
    have c2 := semisimplePart_mul_eq (hfs.pow_pow m m) (hss.pow m) (by
      have : f ^ m - (S : End ℂ V) ^ m = ((u : End ℂ V) ^ m - 1) * (S : End ℂ V) ^ m := by
        rw [epow, sub_mul, (huS'.pow_pow m m).eq, one_mul]
      rw [this]
      exact ((huS'.pow_pow m m).sub_left (Commute.one_left _)).isNilpotent_mul_right
        (isNilpotent_pow_sub_one hunil m)) c1
    rw [one_smul] at c1 c2
    refine commute_of_commute_pow hm hunil ?_
    have h3 : ((S ^ m : (End ℂ V)ˣ) : End ℂ V) * ((u : End ℂ V) ^ m * ρ τ) =
        (S ^ m : (End ℂ V)ˣ) * (ρ τ * (u : End ℂ V) ^ m) := by
      rw [Units.val_pow_eq_pow_val, ← mul_assoc, ← epow, c1, ← mul_assoc, c2, mul_assoc, ← epow]
    exact (Units.mul_right_inj _).mp h3
  let ρ' : Representation ℂ (Weil h) V :=
    { toFun := fun σ => ρ σ * ((u ^ (-deg σ) : (End ℂ V)ˣ) : End ℂ V)
      map_one' := by simp
      map_mul' := fun σ τ => by
        have := ((huρ τ).units_zpow_left (-deg σ)).eq
        rw [map_mul, deg_mul, neg_add, zpow_add, Units.val_mul]
        simp only [mul_assoc]
        rw [← mul_assoc _ (ρ τ) (Units.val (u ^ (-deg τ))), this, mul_assoc] }
  have hρ' : ∀ σ, ρ' σ = ρ σ * ((u ^ (-deg σ) : (End ℂ V)ˣ) : End ℂ V) := fun _ => rfl
  have hsm : IsSmooth ρ' := .of_open hρ (by simp) fun σ hσ => by
    have : ρ (ineIncl h σ) = 1 := hσ
    rw [hρ', this]; simp
  have hfr : ρ' (frob h) = S := by
    rw [hρ', deg_frob, ← hfdef, ← hSu', mul_assoc, ← Units.val_mul]; simp
  refine ⟨⟨ρ', N, hsm, GlobalTheory.T.weilGroup_isSemisimple_of_semisimple_frob E Ω A w h V ρ' hsm (frob h) deg_frob (hfr ▸ hss), hN,
    fun σ => ?_⟩, u, rfl, hunil, huN, huρ, fun σ => ?_⟩
  · rw [hρ', mul_assoc, (huN.units_zpow_left (-deg σ)).eq, ← mul_assoc, hc, smul_mul_assoc,
      mul_assoc]
  · show _ = ρ' σ * _
    rw [hρ', mul_assoc, ← Units.val_mul, ← zpow_add]; simp

end GlobalTheory.WeilDeligne

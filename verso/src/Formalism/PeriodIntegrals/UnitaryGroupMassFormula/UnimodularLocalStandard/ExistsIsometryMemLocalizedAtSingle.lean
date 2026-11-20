import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.StdHSingleZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Imports

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}

/- English proof (translation)
Take `⟨n, hln, hn⟩` from `hv`. Establish `hn0 : n ≠ 0`. Introduce and unpack `rfl`. Conclude with `hln (dvd_zero l)`. Use `set S := stdLat (cmL a b d ha hd lam hlam) m`.

Establish `hmem : (S.addSubgroupOf Λ).index • (⟨n • v, hn⟩ : Λ) ∈ S.addSubgroupOf Λ` using `AddSubgroup.nsmul_index_mem _ _`. Rewrite `hmem` using `[AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_nsmul, smul_smul]`. Establish `hN : (S.addSubgroupOf Λ).index * n ≠ 0` using `mul_ne_zero h1 hn0`. Conclude with `isKv_of_nsmul hN (isKv_of_mem hmem)`.
-/
lemma isKv_of_sat {m : Type*} [Fintype m] [DecidableEq m] {l : ℕ} (hl : l.Prime) {Λ : AddSubgroup (m → ℂ)}
    (h1 : relIdx (stdLat (cmL a b d ha hd lam hlam) m) Λ ≠ 0) {v : m → ℂ} (hv : SatMem l Λ v) :
    IsKv b d lam v := by
  obtain ⟨n, hln, hn⟩ := hv
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hln (dvd_zero l)
  set S := stdLat (cmL a b d ha hd lam hlam) m
  have hmem : (S.addSubgroupOf Λ).index • (⟨n • v, hn⟩ : Λ) ∈ S.addSubgroupOf Λ :=
    AddSubgroup.nsmul_index_mem _ _
  rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_nsmul, smul_smul] at hmem
  have hN : (S.addSubgroupOf Λ).index * n ≠ 0 := mul_ne_zero h1 hn0
  exact isKv_of_nsmul hN (isKv_of_mem hmem)

/- English proof (translation)
Establish `himg : ∀ (g : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)) (Λ : AddSubgroup (m → ℂ)), (∀ z ∈ Λ, cmTheta b d • z ∈ Λ) → ∀ z ∈ imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ, cmTheta b d • z ∈ imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ`. Introduce `g Λ hΛ z hz`. Take `⟨w, hw, rfl⟩` from `(mem_imgLat_iff g Λ z).1 hz`. Conclude with `(mem_imgLat_iff g Λ _).2 ⟨_, hΛ w hw, map_smul g _ w⟩`. Establish `hαK : (lam * ((x * a : ℂ) + y * cmTheta b d)) / lam = (x * a : ℂ) + y * cmTheta b d`.

Clear the denominators using the available nonvanishing facts. Establish `hα0 : lam * ((x * a : ℂ) + y * cmTheta b d) ≠ 0`. Introduce `h0`. Rewrite `h0` using `[alpha_eq (ha := ha) (hd := hd) (hlam := hlam)]`. Take `⟨hx0, hy0⟩` from `LinearIndependent.pair_iff.1 (cmL a b d ha hd lam hlam).indep _ _ h0`.

Establish `hx : x = 0` using `by exact_mod_cast hx0`. Establish `hy : y = 0` using `by exact_mod_cast hy0`. Apply `hQ` to reduce the goal to its premises. Simplify using `[hx, hy]`. Proceed by induction on `T using Finset.induction_on with`.

Consider the case `empty`. Establish `hid : ∀ Λ : AddSubgroup (m → ℂ), imgLat ((LinearEquiv.refl ℂ (m → ℂ) : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)) : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ = Λ`. Introduce `Λ`. Use extensionality with `z`. Rewrite using `[mem_imgLat_iff]`.

Simplify using the standard rewrite rules. Use `⟨LinearEquiv.refl ℂ (m → ℂ), fun _ _ => rfl, ?_, ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[hid, relIdx, AddSubgroup.relIndex_self]`. Conclude with `one_ne_zero`. Rewrite using `[hid, relIdx, AddSubgroup.relIndex_self]`.

Conclude with `one_ne_zero`. Consider the case `insert i₀ T hi₀ ih`. Take `⟨g, hgI, hg1, hg2, hgT⟩` from `ih`. Establish `hc` using `comm_img g hg1 hg2 h1 h2`. Establish `hsd'` using `selfDual_img _ g hgI hsd`.

Establish `hθ'` using `himg g Λa hθ`. Take `⟨v, hvS, hvT, hvv⟩` from `hkey a b c d ha hd lam hlam hok m _ hsd' hθ' hc.1 hc.2 l hl x y hQ T i₀ hi₀ hgT`. Establish `hvK : IsKv b d lam v` using `isKv_of_sat hl hc.1 hvS`. Establish `hK : ∀ s : ℂ, s = 1 ∨ s = -1 → IsK b d (s * (lam * ((x * a : ℂ) + y * cmTheta b d)) / lam)`. Introduce `s hs`.

Establish `hb : IsK b d ((x * a : ℂ) + y * cmTheta b d)` using `⟨x * a, y, 1, one_ne_zero, by push_cast; ring⟩`. Break down `hs with rfl | rfl` into its components or cases. Rewrite using `[one_mul, hαK]`. Conclude with `hb`. Rewrite using `[neg_one_mul, neg_div, hαK]`.

Conclude with `isK_neg hb`. Establish `hee : stdH (cmL a b d ha hd lam hlam) m (Pi.single i₀ (lam * ((x * a : ℂ) + y * cmTheta b d))) (Pi.single i₀ (lam * ((x * a : ℂ) + y * cmTheta b d))) ≠ 0`. Rewrite using `[stdH_kappa _ hlam, Finset.sum_eq_single i₀ (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (fun h => absurd (Finset.mem_univ i₀) h), Pi.single_eq_same]`. Conclude with `mul_ne_zero (kappa_ne _ hlam) (mul_ne_zero (div_ne_zero hα0 hlam) ((map_ne_zero _).2 (div_ne_zero hα0 hlam)))`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs, hne⟩ : ∃ s : ℂ, (s = 1 ∨ s = -1) ∧ stdH (cmL a b d ha hd lam hlam) m v v - stdH (cmL a b d ha hd lam hlam) m v (Pi.single i₀ (s * (lam * ((x * a : ℂ) + y * cmTheta b d)))) ≠ 0 := by`.

Distinguish the cases in `h : stdH (cmL a b d ha hd lam hlam) m v v - stdH (cmL a b d ha hd lam hlam) m v (Pi.single i₀ (1 * (lam * ((x * a : ℂ) + y * cmTheta b d)))) = 0`. Use `⟨-1, Or.inr rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[neg_one_mul, Pi.single_neg, map_neg]`. Rewrite `h` using `[one_mul, sub_eq_zero]`. Rewrite using `[sub_neg_eq_add, ← h, ← two_mul, hvv]`.

Conclude with `mul_ne_zero two_ne_zero hee`. Conclude with `⟨1, Or.inl rfl, h⟩`. Establish `hss : s * s = 1`. Apply the tactic sequence `rcases hs with rfl | rfl <;> norm_num`. Establish `hvv' : stdH (cmL a b d ha hd lam hlam) m v v = stdH (cmL a b d ha hd lam hlam) m (Pi.single i₀ (s * (lam * ((x * a : ℂ) + y * cmTheta b d)))) (Pi.single i₀ (s * (lam * ((x * a : ℂ) + y * cmTheta b d))))`.

Rewrite using `[hvv]`. Break down `hs with rfl | rfl` into its components or cases. Simplify using `only [one_mul]`. Simplify using `only [neg_one_mul, Pi.single_neg, map_neg, LinearMap.neg_apply, neg_neg]`. Take `⟨σ, hσI, hσ1, hσ2, hσv, hσfix⟩` from `qrefl_to hok v _ hvv' hne hvK (isKv_single (hK s hs) i₀)`.

Use `⟨g.trans σ, isom_trans _ g σ hgI hσI, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[imgLat_trans]`. Conclude with `(comm_img σ hσ1 hσ2 hg1 hg2).1`. Rewrite using `[imgLat_trans]`. Conclude with `(comm_img σ hσ1 hσ2 hg1 hg2).2`.

Introduce `j hj`. Rewrite using `[imgLat_trans]`. Break down `Finset.mem_insert.1 hj with rfl | hjT` into its components or cases. Take `⟨n, hln, hn⟩` from `hvS`. Use `⟨n, hln, (mem_imgLat_iff σ _ _).2 ⟨s • n • v, ?_, ?_⟩⟩` and prove the remaining obligations.

Break down `hs with rfl | rfl` into its components or cases. Rewrite using `[one_smul]` and apply the resulting hypothesis. Rewrite using `[neg_one_smul]`. Conclude with `AddSubgroup.neg_mem _ hn`. Rewrite using `[map_smul, map_nsmul, hσv, smul_comm, ← Pi.single_smul', smul_eq_mul, ← mul_assoc, hss, one_mul]`.

Take `⟨n, hln, hn⟩` from `hgT j hjT`. Use `⟨n, hln, (mem_imgLat_iff σ _ _).2 ⟨_, hn, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[map_nsmul, hσfix]`. Apply `stdH_single_zero` to reduce the goal to its premises. Establish `hne' : j ≠ i₀` using `fun h => hi₀ (h ▸ hjT)`.

Simplify using `[hvT j hjT, Pi.single_eq_of_ne hne']`.
-/
lemma exists_isometry_memLocalizedAt_single (hkey : KeyRep) (hok : CmOK a b c d) (m : Type) [Fintype m] [DecidableEq m]
    (Λa : AddSubgroup (m → ℂ)) (hsd : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λa)
    (hθ : ∀ x ∈ Λa, cmTheta b d • x ∈ Λa)
    (h1 : relIdx (stdLat (cmL a b d ha hd lam hlam) m) Λa ≠ 0)
    (h2 : relIdx Λa (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0)
    {l : ℕ} (hl : l.Prime) (x y : ℤ) (hQ : ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2) (T : Finset m) :
    ∃ g : (m → ℂ) ≃ₗ[ℂ] (m → ℂ),
      IsIsom (stdH (cmL a b d ha hd lam hlam) m) (stdH (cmL a b d ha hd lam hlam) m) (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) ∧
      relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat (cmL a b d ha hd lam hlam) m)) ≠ 0 ∧
      relIdx (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat (cmL a b d ha hd lam hlam) m)) (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 ∧
      ∀ j ∈ T, SatMem l (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d))) := by
  classical
  have himg : ∀ (g : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)) (Λ : AddSubgroup (m → ℂ)), (∀ z ∈ Λ, cmTheta b d • z ∈ Λ) →
      ∀ z ∈ imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ, cmTheta b d • z ∈ imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ := by
    intro g Λ hΛ z hz
    obtain ⟨w, hw, rfl⟩ := (mem_imgLat_iff g Λ z).1 hz
    exact (mem_imgLat_iff g Λ _).2 ⟨_, hΛ w hw, map_smul g _ w⟩
  have hαK : (lam * ((x * a : ℂ) + y * cmTheta b d)) / lam = (x * a : ℂ) + y * cmTheta b d := by
    field_simp
  have hα0 : lam * ((x * a : ℂ) + y * cmTheta b d) ≠ 0 := by
    intro h0
    rw [alpha_eq (ha := ha) (hd := hd) (hlam := hlam)] at h0
    obtain ⟨hx0, hy0⟩ := LinearIndependent.pair_iff.1 (cmL a b d ha hd lam hlam).indep _ _ h0
    have hx : x = 0 := by exact_mod_cast hx0
    have hy : y = 0 := by exact_mod_cast hy0
    apply hQ
    simp [hx, hy]
  induction T using Finset.induction_on with
  | empty =>
    have hid : ∀ Λ : AddSubgroup (m → ℂ),
        imgLat ((LinearEquiv.refl ℂ (m → ℂ) : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)) : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ = Λ := by
      intro Λ
      ext z
      rw [mem_imgLat_iff]
      simp
    refine ⟨LinearEquiv.refl ℂ (m → ℂ), fun _ _ => rfl, ?_, ?_, by simp⟩
    · rw [hid, relIdx, AddSubgroup.relIndex_self]
      exact one_ne_zero
    · rw [hid, relIdx, AddSubgroup.relIndex_self]
      exact one_ne_zero
  | insert i₀ T hi₀ ih =>
    obtain ⟨g, hgI, hg1, hg2, hgT⟩ := ih
    have hc := comm_img g hg1 hg2 h1 h2
    have hsd' := selfDual_img _ g hgI hsd
    have hθ' := himg g Λa hθ
    obtain ⟨v, hvS, hvT, hvv⟩ := hkey a b c d ha hd lam hlam hok m _ hsd' hθ' hc.1 hc.2 l hl x y hQ T i₀ hi₀ hgT
    have hvK : IsKv b d lam v := isKv_of_sat hl hc.1 hvS
    have hK : ∀ s : ℂ, s = 1 ∨ s = -1 →
        IsK b d (s * (lam * ((x * a : ℂ) + y * cmTheta b d)) / lam) := by
      intro s hs
      have hb : IsK b d ((x * a : ℂ) + y * cmTheta b d) :=
        ⟨x * a, y, 1, one_ne_zero, by push_cast; ring⟩
      rcases hs with rfl | rfl
      · rw [one_mul, hαK]
        exact hb
      · rw [neg_one_mul, neg_div, hαK]
        exact isK_neg hb
    have hee : stdH (cmL a b d ha hd lam hlam) m (Pi.single i₀ (lam * ((x * a : ℂ) + y * cmTheta b d)))
        (Pi.single i₀ (lam * ((x * a : ℂ) + y * cmTheta b d))) ≠ 0 := by
      rw [stdH_kappa _ hlam, Finset.sum_eq_single i₀ (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
        (fun h => absurd (Finset.mem_univ i₀) h), Pi.single_eq_same]
      exact mul_ne_zero (kappa_ne _ hlam)
        (mul_ne_zero (div_ne_zero hα0 hlam) ((map_ne_zero _).2 (div_ne_zero hα0 hlam)))
    obtain ⟨s, hs, hne⟩ : ∃ s : ℂ, (s = 1 ∨ s = -1) ∧
        stdH (cmL a b d ha hd lam hlam) m v v - stdH (cmL a b d ha hd lam hlam) m v
          (Pi.single i₀ (s * (lam * ((x * a : ℂ) + y * cmTheta b d)))) ≠ 0 := by
      by_cases h : stdH (cmL a b d ha hd lam hlam) m v v - stdH (cmL a b d ha hd lam hlam) m v
          (Pi.single i₀ (1 * (lam * ((x * a : ℂ) + y * cmTheta b d)))) = 0
      · refine ⟨-1, Or.inr rfl, ?_⟩
        rw [neg_one_mul, Pi.single_neg, map_neg]
        rw [one_mul, sub_eq_zero] at h
        rw [sub_neg_eq_add, ← h, ← two_mul, hvv]
        exact mul_ne_zero two_ne_zero hee
      · exact ⟨1, Or.inl rfl, h⟩
    have hss : s * s = 1 := by
      rcases hs with rfl | rfl <;> norm_num
    have hvv' : stdH (cmL a b d ha hd lam hlam) m v v =
        stdH (cmL a b d ha hd lam hlam) m (Pi.single i₀ (s * (lam * ((x * a : ℂ) + y * cmTheta b d))))
          (Pi.single i₀ (s * (lam * ((x * a : ℂ) + y * cmTheta b d)))) := by
      rw [hvv]
      rcases hs with rfl | rfl
      · simp only [one_mul]
      · simp only [neg_one_mul, Pi.single_neg, map_neg, LinearMap.neg_apply, neg_neg]
    obtain ⟨σ, hσI, hσ1, hσ2, hσv, hσfix⟩ :=
      qrefl_to hok v _ hvv' hne hvK (isKv_single (hK s hs) i₀)
    refine ⟨g.trans σ, isom_trans _ g σ hgI hσI, ?_, ?_, ?_⟩
    · rw [imgLat_trans]
      exact (comm_img σ hσ1 hσ2 hg1 hg2).1
    · rw [imgLat_trans]
      exact (comm_img σ hσ1 hσ2 hg1 hg2).2
    · intro j hj
      rw [imgLat_trans]
      rcases Finset.mem_insert.1 hj with rfl | hjT
      · obtain ⟨n, hln, hn⟩ := hvS
        refine ⟨n, hln, (mem_imgLat_iff σ _ _).2 ⟨s • n • v, ?_, ?_⟩⟩
        · rcases hs with rfl | rfl
          · rwa [one_smul]
          · rw [neg_one_smul]
            exact AddSubgroup.neg_mem _ hn
        · rw [map_smul, map_nsmul, hσv, smul_comm, ← Pi.single_smul', smul_eq_mul, ← mul_assoc, hss, one_mul]
      · obtain ⟨n, hln, hn⟩ := hgT j hjT
        refine ⟨n, hln, (mem_imgLat_iff σ _ _).2 ⟨_, hn, ?_⟩⟩
        rw [map_nsmul, hσfix]
        apply stdH_single_zero
        have hne' : j ≠ i₀ := fun h => hi₀ (h ▸ hjT)
        simp [hvT j hjT, Pi.single_eq_of_ne hne']

/- English proof (translation)
Introduce `a b c d ha hd lam hlam hok m _ _ Λa hsd hθ h1 h2 l hl`. Take `⟨x, y, hQ⟩` from `exists_good_form hok hl`. Take `⟨g, hgI, hg1, hg2, hgT⟩` from `exists_isometry_memLocalizedAt_single hkey hok m Λa hsd hθ h1 h2 hl x y hQ Finset.univ`. Establish `hc` using `comm_img g hg1 hg2 h1 h2`. Establish `hsd'` using `selfDual_img _ g hgI hsd`.

Establish `hθ' : ∀ z ∈ imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa, cmTheta b d • z ∈ imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa`. Introduce `z hz`. Take `⟨w, hw, rfl⟩` from `(mem_imgLat_iff g Λa z).1 hz`. Conclude with `(mem_imgLat_iff g Λa _).2 ⟨_, hθ w hw, map_smul g _ w⟩`. Take `⟨n, hln, hn⟩` from `sat_std_of_all hok hl x y hQ _ hsd' hθ' (fun j => hgT j (Finset.mem_univ j))`.

Use `⟨g, hgI, hc.1, ?_, hc.2⟩` and prove the remaining obligations. Introduce `hdvd`. Establish `hfi : ((stdLat (cmL a b d ha hd lam hlam) m).addSubgroupOf (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa)).FiniteIndex` using `⟨hc.1⟩`. Establish `: Fact l.Prime` using `⟨hl⟩`. Take `⟨q, hq⟩` from `exists_prime_addOrderOf_dvd_card' l hdvd`.

Establish `hnq : n • q = 0`. Proceed by induction on `q using QuotientAddGroup.induction_on with`. Consider the case `H w`. Rewrite using `[← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_nsmul]`. Conclude with `hn w w.2`.

Establish `h` using `addOrderOf_dvd_of_nsmul_eq_zero hnq`. Rewrite `h` using `[hq]`. Conclude with `hln h`.
-/
theorem stepB_of_key (hkey : KeyRep) : StepB := by
  intro a b c d ha hd lam hlam hok m _ _ Λa hsd hθ h1 h2 l hl
  obtain ⟨x, y, hQ⟩ := exists_good_form hok hl
  obtain ⟨g, hgI, hg1, hg2, hgT⟩ := exists_isometry_memLocalizedAt_single hkey hok m Λa hsd hθ h1 h2 hl x y hQ Finset.univ
  have hc := comm_img g hg1 hg2 h1 h2
  have hsd' := selfDual_img _ g hgI hsd
  have hθ' : ∀ z ∈ imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa, cmTheta b d • z ∈ imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := (mem_imgLat_iff g Λa z).1 hz
    exact (mem_imgLat_iff g Λa _).2 ⟨_, hθ w hw, map_smul g _ w⟩
  obtain ⟨n, hln, hn⟩ := sat_std_of_all hok hl x y hQ _ hsd' hθ' (fun j => hgT j (Finset.mem_univ j))
  refine ⟨g, hgI, hc.1, ?_, hc.2⟩
  intro hdvd
  have hfi : ((stdLat (cmL a b d ha hd lam hlam) m).addSubgroupOf
      (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa)).FiniteIndex := ⟨hc.1⟩
  have : Fact l.Prime := ⟨hl⟩
  obtain ⟨q, hq⟩ := exists_prime_addOrderOf_dvd_card' l hdvd
  have hnq : n • q = 0 := by
    induction q using QuotientAddGroup.induction_on with
    | H w =>
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf,
        AddSubgroup.coe_nsmul]
      exact hn w w.2
  have h := addOrderOf_dvd_of_nsmul_eq_zero hnq
  rw [hq] at h
  exact hln h

/- English proof (translation)
The claim follows from `target_of (stepB_of_key hkey) stepC`.
-/
theorem target_of_key (hkey : KeyRep) : PI.UnimodLocStd := target_of (stepB_of_key hkey) stepC

end PI.UnitaryGroupMassFormula.UnimodLocStd

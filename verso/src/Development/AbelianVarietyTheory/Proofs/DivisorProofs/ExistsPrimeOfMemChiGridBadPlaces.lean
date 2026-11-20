import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeCharTrivOnRealSubfieldInfinityType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.ResidueEisenstein
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.WAddOneLtOfDvd

noncomputable section

namespace GlobalTheory.GridChars

section General

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open GlobalTheory.Mem.Chr.AntiExist GlobalTheory.ModelChar

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
Use `continuous_of_continuousAt_one θ ?_` and prove the remaining obligations. Establish `hc : Continuous fun x : (v.adicCompletion L)ˣ => (x : v.adicCompletion L) - 1` using `Units.continuous_val.sub continuous_const`. Establish `hn : {x : (v.adicCompletion L)ˣ | Valued.v ((x : v.adicCompletion L) - 1) ≤ WithZero.exp (-2 : ℤ)} ∈ nhds (1 : (v.adicCompletion L)ˣ)` using `((GlobalTheory.Mem.UnitOpen.isOpen_val_le v (-2)).preimage hc).mem_nhds (by simp)`. Use `(continuousAt_const (y := (1 : ℂˣ))).congr ?_` and prove the remaining obligations. Use `filter_upwards [hn] with x hx`.

Use `(h x ?_ hx).symm` and prove the remaining obligations. Establish `hlt : Valued.v ((x : v.adicCompletion L) - 1) < 1`. Use `lt_of_le_of_lt hx ?_` and prove the remaining obligations. Rewrite using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Evaluate the numerical expressions.

Use `Valuation.map_one_add_of_lt (Valued.v : Valuation (v.adicCompletion L) _) hlt` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem continuous_of_level {v : HeightOneSpectrum (𝓞 L)} {θ : (v.adicCompletion L)ˣ →* ℂˣ}
    (h : ∀ x, IsUnitAt v x → Valued.v ((x : v.adicCompletion L) - 1) ≤ WithZero.exp (-2 : ℤ) → θ x = 1) :
    Continuous θ := by
  refine continuous_of_continuousAt_one θ ?_
  have hc : Continuous fun x : (v.adicCompletion L)ˣ => (x : v.adicCompletion L) - 1 :=
    Units.continuous_val.sub continuous_const
  have hn : {x : (v.adicCompletion L)ˣ | Valued.v ((x : v.adicCompletion L) - 1) ≤ WithZero.exp (-2 : ℤ)} ∈
      nhds (1 : (v.adicCompletion L)ˣ) :=
    ((GlobalTheory.Mem.UnitOpen.isOpen_val_le v (-2)).preimage hc).mem_nhds (by simp)
  refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
  filter_upwards [hn] with x hx
  refine (h x ?_ hx).symm
  have hlt : Valued.v ((x : v.adicCompletion L) - 1) < 1 := by
    refine lt_of_le_of_lt hx ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have := Valuation.map_one_add_of_lt (Valued.v : Valuation (v.adicCompletion L) _) hlt
  rwa [add_sub_cancel] at this

/- English proof (translation)
Introduce `x y h` and use `by rw [← finEv_local_self v x, h, finEv_local_self]`.
-/
theorem localIdele_inj (v : HeightOneSpectrum (𝓞 L)) : Function.Injective (localIdele L v) := fun x y h => by
  rw [← finEv_local_self v x, h, finEv_local_self]

open Classical in

/- English proof (translation)
Establish `hcc : ∀ x, c.toRingEquiv (c.toRingEquiv x) = x` using `conj_conj h`. Take `⟨C, hC⟩` from `exists_isConjI L c.toRingEquiv`. Take `⟨ψ0, hψ0, hψ0u, hψ0i, -, hψ0N, hψ0d⟩` from `exists_modelChar L I φ h.bij e ∅ (fun _ => 1) (by simp)`. Take `⟨ψ, hψe⟩ : ∃ ψ : Ideles L →* ℂˣ, ∀ a, ψ a = ψ0 a * ∏ v ∈ S, θ v (Units.map (finEv v) a)` from `⟨ψ0 * ∏ v ∈ S, (θ v).comp (Units.map (finEv v)), fun a => by`. Rewrite using `[MonoidHom.mul_apply, MonoidHom.finsetProd_apply]`.

Use the proof step `rfl⟩`. Establish `hψ : Continuous ψ`. Rewrite using `[show (ψ : Ideles L → ℂˣ) = _ from funext hψe]`. Conclude with `hψ0.mul (continuous_finsetProd _ fun v hv => (hθc v hv).comp (Continuous.units_map _ (continuous_finEv v)))`. Establish `hψu : ∀ x, ‖((ψ x : ℂˣ) : ℂ)‖ = 1` using `fun x => by`.

Rewrite using `[hψe, Units.val_mul, Units.coe_prod, norm_mul, norm_prod, hψ0u, one_mul]`. Conclude with `Finset.prod_eq_one fun v hv => hθu v hv _`. Establish `hψi : ∀ i (k : Lˣ), ((ψ (infIdele L (InfinitePlace.mk (φ i)) (atInf _ k)) : ℂˣ) : ℂ) = (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ e i` using `fun i k => by`. Rewrite using `[hψe, Finset.prod_eq_one fun v _ => by rw [finEv_inf, map_one], mul_one, hψ0i]`. Establish `hψS : ∀ v ∈ S, ∀ x, ψ (localIdele L v x) = θ v x` using `fun v hv x => by`.

Rewrite using `[hψe, hψ0N v (by simp), one_mul, Finset.prod_eq_single_of_mem v hv, finEv_local_self]`. Introduce `w _ hw`. Rewrite using `[finEv_local_ne hw, map_one]`. Establish `hψN : ∀ v ∉ S, ∀ x, ψ (localIdele L v x) = 1` using `fun v hv x => by`. Rewrite using `[hψe, hψ0N v (by simp), one_mul]`.

Use `Finset.prod_eq_one fun w hw => ?_` and prove the remaining obligations. Rewrite using `[finEv_local_ne (fun hh : w = v => hv (hh ▸ hw)), map_one]`. Establish `h1 : ∀ k : Lˣ, (∃ m : ℕ, 0 < m ∧ (k : L) ^ m = 1) → ψ (diagUnits L k) = 1` using `fun k hk => by`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hψe, hψ0d, Finset.prod_empty, mul_one, Units.val_mul, Units.val_one, ← hpar k hk]`.

Use `congr 1`. Rewrite using `[(GlobalTheory.InfTypeLocal.infType_iff_local L I φ h.bij ψ0 hψ0 _).2 hψ0i]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Take `⟨m, hm, hkm⟩` from `hk`. Rewrite using `[Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hkm, map_one]) hm.ne', Complex.ofReal_one, div_one]`.

Take `⟨χ, hχu, hχ⟩` from `exists_anti h hC ψ hψ hψu h1`. Establish `hfix : ∀ z, C z = z → χ.1 z = 1` using `fun z hz => by`. Rewrite using `[hχ z (by rw [hz, div_self']; exact one_mem _), hz, div_self', map_one]`. Establish `hloc : ∀ v v' x x', C (localIdele L v x) = localIdele L v' x' → IsUnitAt v x → IsUnitAt v' x' → χ.loc v x = ψ (localIdele L v x) / ψ (localIdele L v' x')` using `fun v v' x x' hx h1 h2 => by show χ.1 (localIdele L v x) = _`. Rewrite using `[hχ _ (by rw [hx]; exact div_mem (loc_mem h1) (loc_mem h2)), hx, map_div]`.

Use `⟨χ, hχu, ⟨fun v k => ?_, fun w k => ?_⟩, ?_, fun v hv x hx => ?_, fun w hwS v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[← hfix _ (conj_locF h hC v k)]`. Unfold `HChar.resFin locF`. Rewrite using `[MonoidHom.finsetProd_apply, map_prod]`. Both sides reduce to the same expression.

Unfold `HChar.resInf`. Rewrite using `[MonoidHom.finsetProd_apply]`. Use `Finset.prod_eq_one fun w' _ => hfix (infIdele L w' (atInf w' (upF F k))) ?_` and prove the remaining obligations. Rewrite using `[conj_inf h hC, conj_upF]`. Use `(GlobalTheory.InfTypeLocal.infType_iff_local L I φ h.bij χ.1 χ.2.1 _).2 fun i k => ?_` and prove the remaining obligations.

Rewrite using `[hχ _ (by rw [conj_inf h hC]; exact div_mem (inf_mem _ _) (inf_mem _ _)), conj_inf h hC, ← map_div, ← map_div, hψi, Units.val_div_eq_div_val, map_div₀]`. Establish `e1 : φ i ((Units.map (MonoidHomClass.toMonoidHom c.toRingEquiv) k : Lˣ) : L) = (starRingEnd ℂ) (φ i k)` using `h.embedding_conj (φ i) k`. Rewrite using `[e1]`. Use `phase_div (φ i k) (by simp) (-e i)` as an intermediate fact. Rewrite `this` using `[neg_neg, neg_mul_neg]`. Then use the resulting hypothesis.

Take `⟨v', hc', -⟩` from `existsUnique_conjPl c.toRingEquiv v`. Take `⟨x', e1, e2, -⟩` from `conj_loc hC hc' x`. Rewrite using `[hloc v v' x x' e1 hx (e2.trans hx), hψN v (fun hS' => hv v hS' rfl), hψN v' (fun hS' => hv v' hS' ((under_eq_iff_conjPl c h.rank h.ne v v').2 (Or.inr hc')).symm), div_one]`. Break down `(under_eq_iff_conjPl c h.rank h.ne w v).1 hv with rfl | hw'` into its components or cases. Use `⟨id, fun k => ⟨_, rfl⟩, fun _ => Iff.rfl, fun _ => rfl, fun _ _ hx => hx, fun x hx => ?_⟩` and prove the remaining obligations.

Take `⟨w', hw', -⟩` from `existsUnique_conjPl c.toRingEquiv v`. Take `⟨x', e1, e2, -⟩` from `conj_loc hC hw' x`. Rewrite using `[hloc v w' x x' e1 hx (e2.trans hx), hψS v hwS, hψN w' (hS v hwS w' hw'), div_one]`. Both sides reduce to the same expression. Use `choose σ e1 e2 e3 using conj_loc hC (conjPl_symm hcc hw')`.

Use `⟨σ, fun k => ⟨atFin v (Units.map (MonoidHomClass.toMonoidHom c.toRingEquiv) k), localIdele_inj w ?_⟩, fun x => by unfold IsUnitAt; rw [e2], e3, fun x n hx => localIdele_inj w ?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[← e1, hC.loc v w (conjPl_symm hcc hw')]`. Use `congr 2`. Conclude with `Units.ext (hcc k)`. Rewrite using `[map_pow, ← e1, ← map_pow, ← map_pow, hx, map_one, map_one, map_one]`.

Rewrite using `[hloc v w x _ (e1 x) hx ((e2 x).trans hx), hψN v (hS w hwS v hw'), hψS w hwS, one_div, inv_eq_one]`.
-/
theorem exists_hecke_level {F : Type} [Field F] [NumberField F] [Algebra F L] {c : L ≃ₐ[F] L} {I : Type} [Fintype I]
    {φ : I → L →+* ℂ} (h : CMData F c φ) (e : I → ℤ) (S : Finset (HeightOneSpectrum (𝓞 L)))
    (θ : ∀ v : HeightOneSpectrum (𝓞 L), (v.adicCompletion L)ˣ →* ℂˣ) (hθc : ∀ v ∈ S, Continuous (θ v))
    (hθu : ∀ v ∈ S, ∀ x, ‖((θ v x : ℂˣ) : ℂ)‖ = 1)
    (hS : ∀ w ∈ S, ∀ w', ConjPl c.toRingEquiv w w' → w' ∉ S)
    (hpar : ∀ k : Lˣ, (∃ m : ℕ, 0 < m ∧ (k : L) ^ m = 1) →
      (∏ i, φ i (k : L) ^ e i) * ((∏ w ∈ S, θ w (atFin w k) : ℂˣ) : ℂ) = 1) :
    ∃ χ : HChar L, χ.IsUnitary ∧ χ.TrivOn F ∧ χ.HasInf φ (fun i => 2 * e i) ∧
      (∀ v, (∀ w ∈ S, v.under (𝓞 F) ≠ w.under (𝓞 F)) → χ.UnrAt v) ∧
      ∀ w ∈ S, ∀ v : HeightOneSpectrum (𝓞 L), v.under (𝓞 F) = w.under (𝓞 F) →
        ∃ σ : (v.adicCompletion L)ˣ → (w.adicCompletion L)ˣ,
          (∀ k : Lˣ, ∃ x, σ x = atFin w k) ∧ (∀ x, IsUnitAt w (σ x) ↔ IsUnitAt v x) ∧
          (∀ x, Valued.v ((σ x : w.adicCompletion L) - 1) = Valued.v ((x : v.adicCompletion L) - 1)) ∧
          (∀ x (n : ℕ), x ^ n = 1 → σ x ^ n = 1) ∧ ∀ x, IsUnitAt v x → (χ.loc v x = 1 ↔ θ w (σ x) = 1) := by
  have hcc : ∀ x, c.toRingEquiv (c.toRingEquiv x) = x := conj_conj h
  obtain ⟨C, hC⟩ := exists_isConjI L c.toRingEquiv
  obtain ⟨ψ0, hψ0, hψ0u, hψ0i, -, hψ0N, hψ0d⟩ := exists_modelChar L I φ h.bij e ∅ (fun _ => 1) (by simp)
  obtain ⟨ψ, hψe⟩ : ∃ ψ : Ideles L →* ℂˣ, ∀ a, ψ a = ψ0 a * ∏ v ∈ S, θ v (Units.map (finEv v) a) :=
    ⟨ψ0 * ∏ v ∈ S, (θ v).comp (Units.map (finEv v)), fun a => by
      rw [MonoidHom.mul_apply, MonoidHom.finsetProd_apply]; rfl⟩
  have hψ : Continuous ψ := by
    rw [show (ψ : Ideles L → ℂˣ) = _ from funext hψe]
    exact hψ0.mul (continuous_finsetProd _ fun v hv => (hθc v hv).comp (Continuous.units_map _ (continuous_finEv v)))
  have hψu : ∀ x, ‖((ψ x : ℂˣ) : ℂ)‖ = 1 := fun x => by
    rw [hψe, Units.val_mul, Units.coe_prod, norm_mul, norm_prod, hψ0u, one_mul]
    exact Finset.prod_eq_one fun v hv => hθu v hv _
  have hψi : ∀ i (k : Lˣ), ((ψ (infIdele L (InfinitePlace.mk (φ i)) (atInf _ k)) : ℂˣ) : ℂ) =
      (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ e i := fun i k => by
    rw [hψe, Finset.prod_eq_one fun v _ => by rw [finEv_inf, map_one], mul_one, hψ0i]
  have hψS : ∀ v ∈ S, ∀ x, ψ (localIdele L v x) = θ v x := fun v hv x => by
    rw [hψe, hψ0N v (by simp), one_mul, Finset.prod_eq_single_of_mem v hv, finEv_local_self]
    intro w _ hw
    rw [finEv_local_ne hw, map_one]
  have hψN : ∀ v ∉ S, ∀ x, ψ (localIdele L v x) = 1 := fun v hv x => by
    rw [hψe, hψ0N v (by simp), one_mul]
    refine Finset.prod_eq_one fun w hw => ?_
    rw [finEv_local_ne (fun hh : w = v => hv (hh ▸ hw)), map_one]
  have h1 : ∀ k : Lˣ, (∃ m : ℕ, 0 < m ∧ (k : L) ^ m = 1) → ψ (diagUnits L k) = 1 := fun k hk => by
    apply Units.ext
    rw [hψe, hψ0d, Finset.prod_empty, mul_one, Units.val_mul, Units.val_one, ← hpar k hk]
    congr 1
    · rw [(GlobalTheory.InfTypeLocal.infType_iff_local L I φ h.bij ψ0 hψ0 _).2 hψ0i]
      refine Finset.prod_congr rfl fun i _ => ?_
      obtain ⟨m, hm, hkm⟩ := hk
      rw [Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hkm, map_one]) hm.ne', Complex.ofReal_one, div_one]
  obtain ⟨χ, hχu, hχ⟩ := exists_anti h hC ψ hψ hψu h1
  have hfix : ∀ z, C z = z → χ.1 z = 1 := fun z hz => by
    rw [hχ z (by rw [hz, div_self']; exact one_mem _), hz, div_self', map_one]
  have hloc : ∀ v v' x x', C (localIdele L v x) = localIdele L v' x' → IsUnitAt v x → IsUnitAt v' x' →
      χ.loc v x = ψ (localIdele L v x) / ψ (localIdele L v' x') := fun v v' x x' hx h1 h2 => by
    show χ.1 (localIdele L v x) = _
    rw [hχ _ (by rw [hx]; exact div_mem (loc_mem h1) (loc_mem h2)), hx, map_div]
  refine ⟨χ, hχu, ⟨fun v k => ?_, fun w k => ?_⟩, ?_, fun v hv x hx => ?_, fun w hwS v hv => ?_⟩
  · rw [← hfix _ (conj_locF h hC v k)]
    unfold HChar.resFin locF
    rw [MonoidHom.finsetProd_apply, map_prod]
    rfl
  · unfold HChar.resInf
    rw [MonoidHom.finsetProd_apply]
    refine Finset.prod_eq_one fun w' _ => hfix (infIdele L w' (atInf w' (upF F k))) ?_
    rw [conj_inf h hC, conj_upF]
  · refine (GlobalTheory.InfTypeLocal.infType_iff_local L I φ h.bij χ.1 χ.2.1 _).2 fun i k => ?_
    rw [hχ _ (by rw [conj_inf h hC]; exact div_mem (inf_mem _ _) (inf_mem _ _)), conj_inf h hC, ← map_div, ← map_div,
      hψi, Units.val_div_eq_div_val, map_div₀]
    have e1 : φ i ((Units.map (MonoidHomClass.toMonoidHom c.toRingEquiv) k : Lˣ) : L) = (starRingEnd ℂ) (φ i k) :=
      h.embedding_conj (φ i) k
    rw [e1]
    have := phase_div (φ i k) (by simp) (-e i)
    rwa [neg_neg, neg_mul_neg] at this
  · obtain ⟨v', hc', -⟩ := existsUnique_conjPl c.toRingEquiv v
    obtain ⟨x', e1, e2, -⟩ := conj_loc hC hc' x
    rw [hloc v v' x x' e1 hx (e2.trans hx), hψN v (fun hS' => hv v hS' rfl), hψN v' (fun hS' => hv v' hS'
      ((under_eq_iff_conjPl c h.rank h.ne v v').2 (Or.inr hc')).symm), div_one]
  · rcases (under_eq_iff_conjPl c h.rank h.ne w v).1 hv with rfl | hw'
    · refine ⟨id, fun k => ⟨_, rfl⟩, fun _ => Iff.rfl, fun _ => rfl, fun _ _ hx => hx, fun x hx => ?_⟩
      obtain ⟨w', hw', -⟩ := existsUnique_conjPl c.toRingEquiv v
      obtain ⟨x', e1, e2, -⟩ := conj_loc hC hw' x
      rw [hloc v w' x x' e1 hx (e2.trans hx), hψS v hwS, hψN w' (hS v hwS w' hw'), div_one]
      rfl
    · choose σ e1 e2 e3 using conj_loc hC (conjPl_symm hcc hw')
      refine ⟨σ, fun k => ⟨atFin v (Units.map (MonoidHomClass.toMonoidHom c.toRingEquiv) k), localIdele_inj w ?_⟩,
        fun x => by unfold IsUnitAt; rw [e2], e3, fun x n hx => localIdele_inj w ?_, fun x hx => ?_⟩
      · rw [← e1, hC.loc v w (conjPl_symm hcc hw')]
        congr 2
        exact Units.ext (hcc k)
      · rw [map_pow, ← e1, ← map_pow, ← map_pow, hx, map_one, map_one, map_one]
      · rw [hloc v w x _ (e1 x) hx ((e2 x).trans hx), hψN v (hS w hwS v hw'), hψS w hwS, one_div, inv_eq_one]

variable (v : HeightOneSpectrum (𝓞 L))

/- English proof (translation)
Rewrite using `[← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add]`. Simplify using the standard rewrite rules.
-/
theorem lt_one_iff_le (t : v.adicCompletion L) : Valued.v t < 1 ↔ Valued.v t ≤ WithZero.exp (-1 : ℤ) := by
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add]
  simp

open Classical in

def resInt (t : v.adicCompletion L) : 𝓞 L ⧸ v.asIdeal :=
  if h : Valued.v t ≤ 1 then Ideal.Quotient.mk v.asIdeal (ReciprocityTheory.Aut.adic_exists_approx v t h).choose else 0

/- English proof (translation)
Rewrite using `[tame_valued_int]`. Conclude with `v.valuation_le_one a`.
-/
theorem val_int_le (a : 𝓞 L) : Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) a) ≤ 1 := by
  rw [tame_valued_int]
  exact v.valuation_le_one a

/- English proof (translation)
Establish `ht : Valued.v t ≤ 1`. Rewrite using `[← sub_add_cancel t (algebraMap (𝓞 L) (v.adicCompletion L) a)]`. Conclude with `Valuation.map_add_le _ ha.le (val_int_le v a)`. Unfold `resInt`. Rewrite using `[dif_pos ht]`.

Conclude with `tame_mk_eq v (ReciprocityTheory.Aut.adic_exists_approx v t ht).choose_spec ha`.
-/
theorem resInt_eq {t : v.adicCompletion L} {a : 𝓞 L} (ha : Valued.v (t - algebraMap (𝓞 L) (v.adicCompletion L) a) < 1) :
    resInt v t = Ideal.Quotient.mk v.asIdeal a := by
  have ht : Valued.v t ≤ 1 := by
    rw [← sub_add_cancel t (algebraMap (𝓞 L) (v.adicCompletion L) a)]
    exact Valuation.map_add_le _ ha.le (val_int_le v a)
  unfold resInt
  rw [dif_pos ht]
  exact tame_mk_eq v (ReciprocityTheory.Aut.adic_exists_approx v t ht).choose_spec ha

def oneUnits : Subgroup (v.adicCompletion L)ˣ where
  carrier := {x | Valued.v ((x : v.adicCompletion L) - 1) < 1}
  one_mem' := by simp
  mul_mem' := fun {x y} hx hy => by
    have hx1 : Valued.v (x : v.adicCompletion L) = 1 := by
      have := Valuation.map_one_add_of_lt (Valued.v : Valuation (v.adicCompletion L) _) hx
      rwa [add_sub_cancel] at this
    show Valued.v ((x : v.adicCompletion L) * y - 1) < 1
    rw [show (x : v.adicCompletion L) * y - 1 = x * (y - 1) + (x - 1) by ring]
    refine Valuation.map_add_lt _ ?_ hx
    rwa [map_mul, hx1, one_mul]
  inv_mem' := fun {x} hx => by
    have hx1 : Valued.v (x : v.adicCompletion L) = 1 := by
      have := Valuation.map_one_add_of_lt (Valued.v : Valuation (v.adicCompletion L) _) hx
      rwa [add_sub_cancel] at this
    show Valued.v (((x⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1) < 1
    rw [Units.val_inv_eq_inv_val, show (x : v.adicCompletion L)⁻¹ - 1 = -((x : v.adicCompletion L) - 1) / x by
      field_simp; ring, map_div₀, Valuation.map_neg, hx1, div_one]
    exact hx

abbrev unifC : v.adicCompletion L := (atFin v (unif v) : (v.adicCompletion L)ˣ)

/- English proof (translation)
The claim follows from `unif_spec v`.
-/
theorem val_unifC : Valued.v (unifC v) = WithZero.exp (-1 : ℤ) := unif_spec v

/- English proof (translation)
Rewrite using `[map_div₀, val_unifC, div_le_one₀ WithZero.exp_pos]`. Conclude with `(lt_one_iff_le v t).1 h`.
-/
theorem val_div_le {t : v.adicCompletion L} (h : Valued.v t < 1) : Valued.v (t / unifC v) ≤ 1 := by
  rw [map_div₀, val_unifC, div_le_one₀ WithZero.exp_pos]
  exact (lt_one_iff_le v t).1 h

def logOne : oneUnits v →* Multiplicative (𝓞 L ⧸ v.asIdeal) where
  toFun x := Multiplicative.ofAdd (resInt v ((((x : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1) / unifC v))
  map_one' := by
    rw [resInt_eq v (a := 0) (by simp)]
    simp
  map_mul' x y := by
    obtain ⟨a, ha⟩ := ReciprocityTheory.Aut.adic_exists_approx v _ (val_div_le v x.2)
    obtain ⟨b, hb⟩ := ReciprocityTheory.Aut.adic_exists_approx v _ (val_div_le v y.2)
    rw [resInt_eq v ha, resInt_eq v hb, ← ofAdd_add, ← map_add]
    congr 1
    refine resInt_eq v ?_
    rw [Subgroup.coe_mul, Units.val_mul, map_add]
    have h0 : unifC v ≠ 0 := Units.ne_zero _
    have hx : Valued.v (((x : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1) < 1 := x.2
    have hy := val_div_le v y.2
    generalize ((x : (v.adicCompletion L)ˣ) : v.adicCompletion L) = s at *
    generalize ((y : (v.adicCompletion L)ˣ) : v.adicCompletion L) = t at *
    rw [show (s * t - 1) / unifC v - (algebraMap (𝓞 L) (v.adicCompletion L) a + algebraMap (𝓞 L) (v.adicCompletion L) b) =
      ((s - 1) / unifC v - algebraMap (𝓞 L) (v.adicCompletion L) a) +
        ((t - 1) / unifC v - algebraMap (𝓞 L) (v.adicCompletion L) b) + (s - 1) * ((t - 1) / unifC v) by ring]
    refine Valuation.map_add_lt _ (Valuation.map_add_lt _ ha hb) ?_
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hy) hx

/- English proof (translation)
Use `haveI : Finite (𝓞 L ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot`. Use `haveI := v.isPrime`. Use `haveI := Fact.mk hp`. Establish `h1 : p • (1 : 𝓞 L ⧸ v.asIdeal) = 0`. Rewrite using `[nsmul_one, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `hv`. Rewrite using `[← addOrderOf_eq_prime h1 one_ne_zero]`. Conclude with `addOrderOf_dvd_natCard _`.
-/
theorem dvd_card {p : ℕ} (hp : p.Prime) (hv : (p : 𝓞 L) ∈ v.asIdeal) : p ∣ Nat.card (𝓞 L ⧸ v.asIdeal) := by
  haveI : Finite (𝓞 L ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  haveI := v.isPrime
  haveI := Fact.mk hp
  have h1 : p • (1 : 𝓞 L ⧸ v.asIdeal) = 0 := by
    rw [nsmul_one, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hv
  rw [← addOrderOf_eq_prime h1 one_ne_zero]
  exact addOrderOf_dvd_natCard _

/- English proof (translation)
Use `haveI : Finite (𝓞 L ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot`. Use `((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hp.one_lt.ne' (Nat.dvd_one.1 ?_)).symm` and prove the remaining obligations. Establish `h2` using `Nat.dvd_sub (dvd_card v hp hv) h`. Establish `: 0 < Nat.card (𝓞 L ⧸ v.asIdeal)` using `Nat.card_pos`. Rewrite `h2` using `[Nat.sub_sub_self this]`. Then use the resulting hypothesis.
-/
theorem coprime_card {p : ℕ} (hp : p.Prime) (hv : (p : 𝓞 L) ∈ v.asIdeal) :
    (Nat.card (𝓞 L ⧸ v.asIdeal) - 1).Coprime p := by
  haveI : Finite (𝓞 L ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  refine ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hp.one_lt.ne' (Nat.dvd_one.1 ?_)).symm
  have h2 := Nat.dvd_sub (dvd_card v hp hv) h
  have : 0 < Nat.card (𝓞 L ⧸ v.asIdeal) := Nat.card_pos
  rwa [Nat.sub_sub_self this] at h2

/- English proof (translation)
Use `haveI : Finite (𝓞 L ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot`. Use `haveI := v.isMaximal`. Use `letI := Ideal.Quotient.field v.asIdeal`. Rewrite using `[← map_pow]`. Use `set y := x ^ (Nat.card (𝓞 L ⧸ v.asIdeal) - 1) with hy`.

Establish `h1 : resPart v y = 1`. Establish `: (resPart v).toHomUnits y = 1`. Rewrite using `[hy, map_pow, ← Nat.card_units]`. Conclude with `pow_card_eq_one'`. Conclude with `congrArg Units.val this`.

Establish `h2` using `(exists_unitPart_approx v y).choose_spec`. Establish `h3 : Ideal.Quotient.mk v.asIdeal (exists_unitPart_approx v y).choose = Ideal.Quotient.mk v.asIdeal 1` using `h1`. Rewrite `h3` using `[Ideal.Quotient.eq, ← tame_valued_lt_one_iff, map_sub, map_one]`. Use `show Valued.v ((unitPart v y : v.adicCompletion L) - 1) < 1`. Use `Valuation.map_add_lt _ h2 h3` as an intermediate fact.

Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem pow_unitPart_mem (x : (v.adicCompletion L)ˣ) :
    unitPart v x ^ (Nat.card (𝓞 L ⧸ v.asIdeal) - 1) ∈ oneUnits v := by
  haveI : Finite (𝓞 L ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  haveI := v.isMaximal
  letI := Ideal.Quotient.field v.asIdeal
  rw [← map_pow]
  set y := x ^ (Nat.card (𝓞 L ⧸ v.asIdeal) - 1) with hy
  have h1 : resPart v y = 1 := by
    have : (resPart v).toHomUnits y = 1 := by
      rw [hy, map_pow, ← Nat.card_units]
      exact pow_card_eq_one'
    exact congrArg Units.val this
  have h2 := (exists_unitPart_approx v y).choose_spec
  have h3 : Ideal.Quotient.mk v.asIdeal (exists_unitPart_approx v y).choose = Ideal.Quotient.mk v.asIdeal 1 := h1
  rw [Ideal.Quotient.eq, ← tame_valued_lt_one_iff, map_sub, map_one] at h3
  show Valued.v ((unitPart v y : v.adicCompletion L) - 1) < 1
  have := Valuation.map_add_lt _ h2 h3
  rwa [sub_add_sub_cancel] at this

/- English proof (translation)
Use `haveI : Finite (𝓞 L ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot`. Use `haveI := v.isPrime`. Use `set m := Nat.card (𝓞 L ⧸ v.asIdeal) - 1 with hm`. Establish `hne : Multiplicative.ofAdd (1 : 𝓞 L ⧸ v.asIdeal) ≠ 1` using `fun h => one_ne_zero (ofAdd_eq_one.1 h)`. Take `⟨ψ, hψ⟩` from `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Multiplicative (𝓞 L ⧸ v.asIdeal)) ℂ hne`.

Establish `hψp : ∀ t, ψ t ^ p = 1` using `fun t => by`. Rewrite using `[← map_pow]`. Establish `: t ^ p = 1`. Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Rewrite using `[toAdd_pow, nsmul_eq_mul, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem.2 hv, zero_mul, toAdd_one]`.

Rewrite using `[this, map_one]`. Set `f : (v.adicCompletion L)ˣ →* oneUnits v` to `((powMonoidHom m).comp (unitPart v)).codRestrict _ (pow_unitPart_mem v)`. Establish `hf : ∀ x (hx : x ∈ oneUnits v), f x = ⟨x, hx⟩ ^ m` using `fun x hx => by`. Establish `hx1 : IsUnitAt v x`. Use `Valuation.map_one_add_of_lt (Valued.v : Valuation (v.adicCompletion L) _) hx` as an intermediate fact.

Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis. Apply `Subtype.ext` to reduce the goal to its premises. Use `show unitPart v x ^ m = x ^ m`. Rewrite using `[unitPart_of_isUnitAt v hx1]`. Establish `h0 : unifC v ≠ 0` using `Units.ne_zero _`.

Establish `hlt : Valued.v (unifC v) < 1` using `(lt_one_iff_le v _).2 (val_unifC v).le`. Use `⟨ψ.comp ((logOne v).comp f), fun x => hψp _, fun x _ hx => ?_, ?_⟩` and prove the remaining obligations. Establish `hx' : x ∈ oneUnits v` using `(lt_one_iff_le v _).2 (hx.trans (WithZero.exp_le_exp.2 (by norm_num)))`. Establish `: logOne v ⟨x, hx'⟩ = 1` using `by show Multiplicative.ofAdd (resInt v (((x : v.adicCompletion L) - 1) / unifC v)) = 1`. Rewrite using `[resInt_eq v (a := 0), map_zero, ofAdd_zero]`.

Rewrite using `[map_zero, sub_zero, lt_one_iff_le, map_div₀, val_unifC, div_le_iff₀ WithZero.exp_pos, ← WithZero.exp_add]`. Conclude with `hx`. Rewrite using `[MonoidHom.comp_apply, MonoidHom.comp_apply, hf x hx', map_pow, this, one_pow, map_one]`. Establish `hk0 : 1 + ((unif v : Lˣ) : L) ≠ 0` using `fun h => by`. Establish `h1 : 1 + unifC v = 0`.

Use `congrArg (algebraMap L (v.adicCompletion L)) h` as an intermediate fact. Rewrite `this` using `[map_add, map_one, map_zero]`. Then use the resulting hypothesis. Use `Valuation.map_one_add_of_lt (Valued.v : Valuation (v.adicCompletion L) _) hlt` as an intermediate fact. Rewrite `this` using `[h1, map_zero]`. Conclude with `zero_ne_one this`.

Establish `ek : ((atFin v (Units.mk0 _ hk0) : (v.adicCompletion L)ˣ) : v.adicCompletion L) = 1 + unifC v` using `by show algebraMap L (v.adicCompletion L) (1 + _) = _`. Rewrite using `[map_add, map_one]`. Both sides reduce to the same expression. Establish `hx' : atFin v (Units.mk0 _ hk0) ∈ oneUnits v` using `by show Valued.v (((atFin v (Units.mk0 _ hk0) : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1) < 1`. Rewrite using `[ek, add_sub_cancel_left]` and apply the resulting hypothesis.

Use `⟨Units.mk0 _ hk0, ?_, (lt_one_iff_le v _).1 hx', fun h => hψ ?_⟩` and prove the remaining obligations. Unfold `IsUnitAt`. Rewrite using `[ek]`. Conclude with `Valuation.map_one_add_of_lt _ hlt`. Establish `: logOne v ⟨_, hx'⟩ = Multiplicative.ofAdd 1` using `by show Multiplicative.ofAdd (resInt v ((((atFin v (Units.mk0 _ hk0) : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1) / unifC v)) = _`.

Rewrite using `[ek, add_sub_cancel_left, div_self h0, resInt_eq v (a := 1) (by simp), map_one]`. Rewrite `h` using `[MonoidHom.comp_apply, MonoidHom.comp_apply, hf _ hx', map_pow, this, map_pow]`. Conclude with `(pow_eq_one_iff_of_coprime (coprime_card v hp hv)).1 ⟨h, hψp _⟩`.
-/
theorem exists_wild {p : ℕ} (hp : p.Prime) (hv : (p : 𝓞 L) ∈ v.asIdeal) :
    ∃ θ : (v.adicCompletion L)ˣ →* ℂˣ, (∀ x, θ x ^ p = 1) ∧
      (∀ x, IsUnitAt v x → Valued.v ((x : v.adicCompletion L) - 1) ≤ WithZero.exp (-2 : ℤ) → θ x = 1) ∧
      ∃ k : Lˣ, IsUnitAt v (atFin v k) ∧
        Valued.v (((atFin v k : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1) ≤ WithZero.exp (-1 : ℤ) ∧
        θ (atFin v k) ≠ 1 := by
  haveI : Finite (𝓞 L ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  haveI := v.isPrime
  set m := Nat.card (𝓞 L ⧸ v.asIdeal) - 1 with hm
  have hne : Multiplicative.ofAdd (1 : 𝓞 L ⧸ v.asIdeal) ≠ 1 := fun h => one_ne_zero (ofAdd_eq_one.1 h)
  obtain ⟨ψ, hψ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Multiplicative (𝓞 L ⧸ v.asIdeal)) ℂ hne
  have hψp : ∀ t, ψ t ^ p = 1 := fun t => by
    rw [← map_pow]
    have : t ^ p = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, nsmul_eq_mul, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem.2 hv,
        zero_mul, toAdd_one]
    rw [this, map_one]
  let f : (v.adicCompletion L)ˣ →* oneUnits v :=
    ((powMonoidHom m).comp (unitPart v)).codRestrict _ (pow_unitPart_mem v)
  have hf : ∀ x (hx : x ∈ oneUnits v), f x = ⟨x, hx⟩ ^ m := fun x hx => by
    have hx1 : IsUnitAt v x := by
      have := Valuation.map_one_add_of_lt (Valued.v : Valuation (v.adicCompletion L) _) hx
      rwa [add_sub_cancel] at this
    apply Subtype.ext
    show unitPart v x ^ m = x ^ m
    rw [unitPart_of_isUnitAt v hx1]
  have h0 : unifC v ≠ 0 := Units.ne_zero _
  have hlt : Valued.v (unifC v) < 1 := (lt_one_iff_le v _).2 (val_unifC v).le
  refine ⟨ψ.comp ((logOne v).comp f), fun x => hψp _, fun x _ hx => ?_, ?_⟩
  · have hx' : x ∈ oneUnits v := (lt_one_iff_le v _).2 (hx.trans (WithZero.exp_le_exp.2 (by norm_num)))
    have : logOne v ⟨x, hx'⟩ = 1 := by
      show Multiplicative.ofAdd (resInt v (((x : v.adicCompletion L) - 1) / unifC v)) = 1
      rw [resInt_eq v (a := 0), map_zero, ofAdd_zero]
      rw [map_zero, sub_zero, lt_one_iff_le, map_div₀, val_unifC, div_le_iff₀ WithZero.exp_pos, ← WithZero.exp_add]
      exact hx
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hf x hx', map_pow, this, one_pow, map_one]
  · have hk0 : 1 + ((unif v : Lˣ) : L) ≠ 0 := fun h => by
      have h1 : 1 + unifC v = 0 := by
        have := congrArg (algebraMap L (v.adicCompletion L)) h
        rwa [map_add, map_one, map_zero] at this
      have := Valuation.map_one_add_of_lt (Valued.v : Valuation (v.adicCompletion L) _) hlt
      rw [h1, map_zero] at this
      exact zero_ne_one this
    have ek : ((atFin v (Units.mk0 _ hk0) : (v.adicCompletion L)ˣ) : v.adicCompletion L) = 1 + unifC v := by
      show algebraMap L (v.adicCompletion L) (1 + _) = _
      rw [map_add, map_one]
      rfl
    have hx' : atFin v (Units.mk0 _ hk0) ∈ oneUnits v := by
      show Valued.v (((atFin v (Units.mk0 _ hk0) : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1) < 1
      rwa [ek, add_sub_cancel_left]
    refine ⟨Units.mk0 _ hk0, ?_, (lt_one_iff_le v _).1 hx', fun h => hψ ?_⟩
    · unfold IsUnitAt
      rw [ek]
      exact Valuation.map_one_add_of_lt _ hlt
    · have : logOne v ⟨_, hx'⟩ = Multiplicative.ofAdd 1 := by
        show Multiplicative.ofAdd (resInt v ((((atFin v (Units.mk0 _ hk0) : (v.adicCompletion L)ˣ) :
          v.adicCompletion L) - 1) / unifC v)) = _
        rw [ek, add_sub_cancel_left, div_self h0, resInt_eq v (a := 1) (by simp), map_one]
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hf _ hx', map_pow, this, map_pow] at h
      exact (pow_eq_one_iff_of_coprime (coprime_card v hp hv)).1 ⟨h, hψp _⟩

/- English proof (translation)
Take `⟨θ0, hne, hext⟩` from `UpperTheory.Mu.tame_ext_prime v hp hw hv (ε.comp (Units.map (algebraMap (𝓞 L) L).toMonoidHom))`. Take `⟨b, hb⟩ : ∃ b, θ0 b ≠ 1` from `by by_contra! hall`. Conclude with `hne (MonoidHom.ext hall)`. Take `⟨θ, ht, hr, -⟩` from `exists_tameLoc_of_residue L v θ0`. Take `⟨k, y, hk, hy⟩` from `exists_lift b`.

Use `⟨θ, ht, fun z hz => ?_, k, isUnitAt_of_residue hk hy, by rwa [hr k y b hk hy]⟩` and prove the remaining obligations. Take `⟨ζ, hζ⟩` from `UpperTheory.Mu.exists_unit_of_root hz`. Rewrite using `[hr z ζ (Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom ζ) hζ.symm rfl, hext ζ (hζ ▸ hz)]`. Conclude with `congrArg ε (Units.ext hζ)`.
-/
theorem exists_tame {p : ℕ} (hp : p.Prime) (hw : Units.torsionOrder L + 1 < p) (hv : (p : 𝓞 L) ∈ v.asIdeal) (ε : Lˣ →* ℂˣ) :
    ∃ θ : (v.adicCompletion L)ˣ →* ℂˣ, TameLoc v θ ∧
      (∀ k : Lˣ, (∃ m : ℕ, 0 < m ∧ (k : L) ^ m = 1) → θ (atFin v k) = ε k) ∧
      ∃ k : Lˣ, IsUnitAt v (atFin v k) ∧ θ (atFin v k) ≠ 1 := by
  obtain ⟨θ0, hne, hext⟩ := UpperTheory.Mu.tame_ext_prime v hp hw hv (ε.comp (Units.map (algebraMap (𝓞 L) L).toMonoidHom))
  obtain ⟨b, hb⟩ : ∃ b, θ0 b ≠ 1 := by
    by_contra! hall
    exact hne (MonoidHom.ext hall)
  obtain ⟨θ, ht, hr, -⟩ := exists_tameLoc_of_residue L v θ0
  obtain ⟨k, y, hk, hy⟩ := exists_lift b
  refine ⟨θ, ht, fun z hz => ?_, k, isUnitAt_of_residue hk hy, by rwa [hr k y b hk hy]⟩
  obtain ⟨ζ, hζ⟩ := UpperTheory.Mu.exists_unit_of_root hz
  rw [hr z ζ (Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom ζ) hζ.symm rfl, hext ζ (hζ ▸ hz)]
  exact congrArg ε (Units.ext hζ)

/- English proof (translation)
Take `⟨θ, ht, hθ, hk⟩` from `exists_tame v hp hw hv ((∏ i, (Units.map (φ i).toMonoidHom) ^ e i) * ∏ w ∈ S, (θ1 w).comp (atFin w))⁻¹`. Use `⟨θ, ht, fun k hk => ?_, hk⟩` and prove the remaining obligations. Rewrite using `[hθ k hk, MonoidHom.inv_apply, MonoidHom.mul_apply, MonoidHom.finsetProd_apply, MonoidHom.finsetProd_apply]`. Simplify using `only [MonoidHom.comp_apply, mul_inv, inv_mul_cancel_right]`. Establish `e1 : ((∏ i, ((Units.map (φ i).toMonoidHom) ^ e i) k : ℂˣ) : ℂ) = ∏ i, φ i (k : L) ^ e i`.

Rewrite using `[Units.coe_prod]`. Conclude with `Finset.prod_congr rfl fun i _ => by rw [MonoidHom.zpow_apply, Units.val_zpow_eq_zpow_val]; rfl`. Rewrite using `[← e1, ← Units.val_mul, mul_inv_cancel, Units.val_one]`.
-/
theorem exists_tame_par {p : ℕ} (hp : p.Prime) (hw : Units.torsionOrder L + 1 < p) (hv : (p : 𝓞 L) ∈ v.asIdeal)
    {I : Type} [Fintype I] (φ : I → L →+* ℂ) (e : I → ℤ) (S : Finset (HeightOneSpectrum (𝓞 L)))
    (θ1 : ∀ w : HeightOneSpectrum (𝓞 L), (w.adicCompletion L)ˣ →* ℂˣ) :
    ∃ θ : (v.adicCompletion L)ˣ →* ℂˣ, TameLoc v θ ∧
      (∀ k : Lˣ, (∃ m : ℕ, 0 < m ∧ (k : L) ^ m = 1) →
        (∏ i, φ i (k : L) ^ e i) * ((θ (atFin v k) * ∏ w ∈ S, θ1 w (atFin w k) : ℂˣ) : ℂ) = 1) ∧
      ∃ k : Lˣ, IsUnitAt v (atFin v k) ∧ θ (atFin v k) ≠ 1 := by
  obtain ⟨θ, ht, hθ, hk⟩ := exists_tame v hp hw hv
    ((∏ i, (Units.map (φ i).toMonoidHom) ^ e i) * ∏ w ∈ S, (θ1 w).comp (atFin w))⁻¹
  refine ⟨θ, ht, fun k hk => ?_, hk⟩
  rw [hθ k hk, MonoidHom.inv_apply, MonoidHom.mul_apply, MonoidHom.finsetProd_apply, MonoidHom.finsetProd_apply]
  simp only [MonoidHom.comp_apply, mul_inv, inv_mul_cancel_right]
  have e1 : ((∏ i, ((Units.map (φ i).toMonoidHom) ^ e i) k : ℂˣ) : ℂ) = ∏ i, φ i (k : L) ^ e i := by
    rw [Units.coe_prod]
    exact Finset.prod_congr rfl fun i _ => by rw [MonoidHom.zpow_apply, Units.val_zpow_eq_zpow_val]; rfl
  rw [← e1, ← Units.val_mul, mul_inv_cancel, Units.val_one]

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Formalism.L2.Host GlobalTheory.Mem.Chr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `h` and use `by obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D have hd := GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ he have hd' := GlobalTheory.IdemSupport.delta_conj hΦ hd have e1 : GlobalTheory.IdemSupport.cP w = w := by ext x rw [GlobalTheory.IdemSupport.mem_cP] refine ((conj …`.
-/
theorem not_conjPl_self {D : D7} {e : AE D} {w : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt e w)
    {c : D.host.E ≃ₐ[D.host.F] D.host.E} (hc : ∀ x, c x = D.host.conj x) : ¬ ConjPl c.toRingEquiv w w := fun h => by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hd := GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ he
  have hd' := GlobalTheory.IdemSupport.delta_conj hΦ hd
  have e1 : GlobalTheory.IdemSupport.cP w = w := by
    ext x
    rw [GlobalTheory.IdemSupport.mem_cP]
    refine ((conjPl_iff_mem _ _ _).1 h x _ ?_).symm
    rw [GlobalTheory.IdemSupport.cO_coe]
    exact ((hc x).trans (bridge_star_holds D.R D.host x).symm).symm
  rw [e1] at hd'
  have := GlobalTheory.IdemSupport.ev_mul (Φ := Φ) e (cA D e) w
  rw [he.1.2.1, GlobalTheory.IdemSupport.ev_zero, hd.2.1, hd'.2.1, one_mul] at this
  exact zero_ne_one this

/- English proof (translation)
Take `⟨h1, h2, -⟩` from `leastSplitAuxiliaryPrimeThetaChain_spec D`. Conclude with `UpperTheory.Mu.w_add_one_lt D.host h1.one_lt (Formalism.MainNotions.rPrAv D) h2`.
-/
theorem torsion_order_lt_auxiliary_prime (D : D7) : NumberField.Units.torsionOrder D.host.E + 1 < q0 D := by
  obtain ⟨h1, h2, -⟩ := leastSplitAuxiliaryPrimeThetaChain_spec D
  exact UpperTheory.Mu.w_add_one_lt D.host h1.one_lt (Formalism.MainNotions.rPrAv D) h2

/- English proof (translation)
Express the relevant statement in the definitionally equal form `algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ w.asIdeal ↔ _`. Rewrite using `[map_natCast]`.
-/
theorem natCast_mem_under {D : D7} (w : HeightOneSpectrum (𝓞 D.host.E)) (p : ℕ) :
    (p : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal ↔ (p : 𝓞 D.host.E) ∈ w.asIdeal := by
  change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ w.asIdeal ↔ _
  rw [map_natCast]

/- English proof (translation)
Break down `(S1_mem_OmF D).1 hv with h | h | h | h` into its components or cases. Use `exacts [⟨_, D.host.g_prime 0, h⟩, ⟨_, D.host.g_prime 1, h⟩, ⟨_, D.host.pde_prime, h⟩, ⟨_, D.host.pde'_prime, h⟩]`.
-/
theorem exists_prime_of_mem_chiGridBadPlaces {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ S1 D) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 D.host.F) ∈ v.asIdeal := by
  rcases (S1_mem_OmF D).1 hv with h | h | h | h
  exacts [⟨_, D.host.g_prime 0, h⟩, ⟨_, D.host.g_prime 1, h⟩, ⟨_, D.host.pde_prime, h⟩, ⟨_, D.host.pde'_prime, h⟩]

/- English proof (translation)
Take `⟨c, hc, hcm, -⟩` from `GlobalTheory.Mem.HostCM.host_cm D.R D.host`. Establish `hcm' : CMData D.host.F c (embTau D)` using `⟨hcm.real, hcm.cplx, hcm.rank, hcm.ne, hcm.bij.comp D.eTau.bijective⟩`. Establish `hW : ∀ w ∈ P.W0, ∃ v ∈ P.S0, P.w v = w` using `fun w hw => Finset.mem_image.1 hw`. Establish `hW' : ∀ v ∈ P.S0, P.w v ∈ P.W0` using `fun v hv => Finset.mem_image_of_mem _ hv`. Establish `hv0 : P.v0 ∈ P.S0` using `P.mem_S0_of_sum_eq.2 (Or.inl rfl)`.

Establish `hwild : ∀ w : HeightOneSpectrum (𝓞 D.host.E), ∃ θ : (w.adicCompletion D.host.E)ˣ →* ℂˣ, w.under (𝓞 D.host.F) ∈ S1 D → ∃ p : ℕ, p.Prime ∧ (p : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal ∧ (∀ x, θ x ^ p = 1) ∧ (∀ x, IsUnitAt w x → Valued.v ((x : w.adicCompletion D.host.E) - 1) ≤ …` using `fun w => by`. Distinguish the cases in `hw : w.under (𝓞 D.host.F) ∈ S1 D`. Take `⟨p, hp, hp'⟩` from `exists_prime_of_mem_chiGridBadPlaces hw`. Take `⟨θ, hθ⟩` from `exists_wild w hp ((natCast_mem_under w p).1 hp')`. Conclude with `⟨θ, fun _ => ⟨p, hp, hp', hθ⟩⟩`.

Conclude with `⟨1, fun h => absurd h hw⟩`. Use `choose θ1 hθ1 using hwild`. Use `set w0 := P.w P.v0 with hw0`. Establish `hu0 : w0.under (𝓞 D.host.F) = P.v0` using `P.under_w hv0`. Take `⟨θ0, ht0, hθ0, k0, hk0, hk0'⟩` from `exists_tame_par w0 (leastSplitAuxiliaryPrimeThetaChain_spec D).1 (torsion_order_lt_auxiliary_prime D) ((natCast_mem_under w0 _).1 (hu0 ▸ P.basePlace_over_qZero)) (embTau D) e (P.W0.erase w0) θ1`.

Set `θ : ∀ w : HeightOneSpectrum (𝓞 D.host.E), (w.adicCompletion D.host.E)ˣ →* ℂˣ` to `Function.update θ1 w0 θ0`. Establish `e0 : θ w0 = θ0` using `Function.update_self _ _ _`. Establish `e1 : ∀ w, w ≠ w0 → θ w = θ1 w` using `fun w hw => Function.update_of_ne hw _ _`. Establish `hcase : ∀ w ∈ P.W0, w = w0 ∨ (w ≠ w0 ∧ w.under (𝓞 D.host.F) ∈ S1 D)` using `fun w hw => by`. Take `⟨v, hv, rfl⟩` from `hW w hw`.

Break down `P.mem_S0_of_sum_eq.1 hv with rfl | h` into its components or cases. Conclude with `Or.inl rfl`. Use `Or.inr ⟨fun hh => h0 ?_, by rwa [P.under_w hv]⟩` and prove the remaining obligations. Rewrite using `[← hu0, ← hh, P.under_w hv]` and apply the resulting hypothesis. Take `⟨χ, hu, ht, hi, hunr, hloc⟩` from `exists_hecke_level hcm' e P.W0 θ (fun w hw => by`.

Break down `hcase w hw with rfl | ⟨h1, h2⟩` into its components or cases. Rewrite using `[e0]`. Conclude with `GlobalTheory.ModelChar.continuous_of_tameLoc ht0`. Take `⟨p, -, -, -, h, -⟩` from `hθ1 w h2`. Rewrite using `[e1 w h1]`.

Conclude with `continuous_of_level h)`. Use the proof step `(fun w hw x => by`. Break down `hcase w hw with rfl | ⟨h1, h2⟩` into its components or cases. Rewrite using `[e0]`. Conclude with `ht0.1 x`.

Take `⟨p, hp, -, h, -⟩` from `hθ1 w h2`. Rewrite using `[e1 w h1]`. Conclude with `Complex.norm_eq_one_of_pow_eq_one (by rw [← Units.val_pow_eq_pow_val, h, Units.val_one]) hp.ne_zero)`. Use the proof step `(fun w hw w' hcj hw' => by`. Take `⟨v, hv, rfl⟩` from `hW w hw`.

Take `⟨v', hv', rfl⟩` from `hW w' hw'`. Use `(under_eq_iff_conjPl c hcm.rank hcm.ne _ _).2 (Or.inr hcj)` as an intermediate fact. Rewrite `this` using `[P.under_w hv, P.under_w hv']`. Substitute `this` using the available equality. Take `⟨e, he⟩` from `P.w_split v' hv`.

Conclude with `not_conjPl_self he hc hcj)`. Use the proof step `(fun k hk => by`. Establish `ep : ∏ w ∈ P.W0.erase w0, θ w (atFin w k) = ∏ w ∈ P.W0.erase w0, θ1 w (atFin w k)` using `Finset.prod_congr rfl fun w hw => by rw [e1 w (Finset.ne_of_mem_erase hw)]`. Rewrite using `[← Finset.mul_prod_erase _ _ (hW' _ hv0), ← hw0, e0, ep]`. Conclude with `hθ0 k hk)`.

Use `⟨χ, hu, ht, hi, fun Q hQ => hunr Q fun w hw h => hQ ?_, fun Q hQ => ?_, fun Q hQ => ?_⟩` and prove the remaining obligations. Take `⟨v, hv, rfl⟩` from `hW w hw`. Rewrite using `[h, P.under_w hv]` and apply the resulting hypothesis. Establish `hQ0` using `P.mem_S0_of_sum_eq.2 (Or.inr hQ)`. Establish `hun` using `P.under_w hQ0`.

Take `⟨σ, s1, s2, s3, s4, s5⟩` from `hloc _ (hW' _ hQ0) Q hun.symm`. Take `⟨p, hp, hp', t1, t2, k, t3, t4, t5⟩` from `hθ1 (P.w (Q.under (𝓞 D.host.F))) (by rwa [hun])`. Rewrite `s5` using `[e1 _ (fun h => h0 (by rwa [← hu0, ← h, hun]))]`. Use `⟨⟨fun x hx hx' => (s5 x hx).2 (t2 _ ((s2 x).2 hx) (by rw [s3]; exact hx')), fun H => t5 ?_⟩, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `s1 k`.

Rewrite `t3`, `t4`, the goal using `[← hx]`. Rewrite `t4` using `[s3]`. Conclude with `(s5 x ((s2 x).1 t3)).1 (H x ((s2 x).1 t3) t4)`. Establish `hco` using `coprime_card Q hp ((natCast_mem_under Q p).1 (by rwa [hun] at hp'))`. Establish `hm : Nat.card (𝓞 D.host.E ⧸ Q.asIdeal) - 1 ≠ 0` using `fun h => by`.

Rewrite `hco` using `[h, Nat.coprime_zero_left]`. Conclude with `hp.one_lt.ne' hco`. Establish `hxu : IsUnitAt Q x`. Use `congrArg (fun y : (Q.adicCompletion D.host.E)ˣ => Valued.v (y : Q.adicCompletion D.host.E)) hx` as an intermediate fact. Simplify using `only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at this`.

Conclude with `(pow_eq_one_iff_left hm).1 this`. Use `(s5 x hxu).2 ((pow_eq_one_iff_of_coprime hco).1 ⟨?_, t1 _⟩)` and prove the remaining obligations. Rewrite using `[← map_pow, s4 x _ hx, map_one]`. Take `⟨σ, s1, s2, s3, -, s5⟩` from `hloc w0 (hW' _ hv0) Q (hQ.trans hu0.symm)`. Rewrite `s5` using `[e0]`.

Use `⟨fun x hx hx' => (s5 x hx).2 (ht0.2 _ ((s2 x).2 hx) (by rw [s3]; exact hx')), fun H => hk0' ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `s1 k0`. Rewrite `hk0`, the goal using `[← hx]`. Conclude with `(s5 x ((s2 x).1 hk0)).1 (H x ((s2 x).1 hk0))`.
-/
theorem exists_one (D : D7) (T : Type) (L : LevCh D T) (P : Places L) (h0 : P.v0 ∉ S1 D) (e : D.what₂.Tau → ℤ) :
    ∃ χ : HChar D.host.E, χ.IsUnitary ∧ χ.TrivOn D.host.F ∧ χ.HasInf (embTau D) (fun τ => 2 * e τ) ∧
      (∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.under (𝓞 D.host.F) ∉ P.S0 → χ.UnrAt Q) ∧
      (∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.under (𝓞 D.host.F) ∈ S1 D → (χ.LevelLe Q 2 ∧ ¬ χ.LevelLe Q 1) ∧
        ∀ x : (Q.adicCompletion D.host.E)ˣ, x ^ (Nat.card (𝓞 D.host.E ⧸ Q.asIdeal) - 1) = 1 → χ.loc Q x = 1) ∧
      ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.under (𝓞 D.host.F) = P.v0 → χ.LevelLe Q 1 ∧ ¬ χ.UnrAt Q := by
  classical
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  have hcm' : CMData D.host.F c (embTau D) :=
    ⟨hcm.real, hcm.cplx, hcm.rank, hcm.ne, hcm.bij.comp D.eTau.bijective⟩
  have hW : ∀ w ∈ P.W0, ∃ v ∈ P.S0, P.w v = w := fun w hw => Finset.mem_image.1 hw
  have hW' : ∀ v ∈ P.S0, P.w v ∈ P.W0 := fun v hv => Finset.mem_image_of_mem _ hv
  have hv0 : P.v0 ∈ P.S0 := P.mem_S0_of_sum_eq.2 (Or.inl rfl)
  have hwild : ∀ w : HeightOneSpectrum (𝓞 D.host.E), ∃ θ : (w.adicCompletion D.host.E)ˣ →* ℂˣ,
      w.under (𝓞 D.host.F) ∈ S1 D → ∃ p : ℕ, p.Prime ∧ (p : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal ∧
        (∀ x, θ x ^ p = 1) ∧
        (∀ x, IsUnitAt w x → Valued.v ((x : w.adicCompletion D.host.E) - 1) ≤ WithZero.exp (-2 : ℤ) → θ x = 1) ∧
        ∃ k : D.host.Eˣ, IsUnitAt w (atFin w k) ∧
          Valued.v (((atFin w k : (w.adicCompletion D.host.E)ˣ) : w.adicCompletion D.host.E) - 1) ≤
            WithZero.exp (-1 : ℤ) ∧ θ (atFin w k) ≠ 1 := fun w => by
    by_cases hw : w.under (𝓞 D.host.F) ∈ S1 D
    · obtain ⟨p, hp, hp'⟩ := exists_prime_of_mem_chiGridBadPlaces hw
      obtain ⟨θ, hθ⟩ := exists_wild w hp ((natCast_mem_under w p).1 hp')
      exact ⟨θ, fun _ => ⟨p, hp, hp', hθ⟩⟩
    · exact ⟨1, fun h => absurd h hw⟩
  choose θ1 hθ1 using hwild
  set w0 := P.w P.v0 with hw0
  have hu0 : w0.under (𝓞 D.host.F) = P.v0 := P.under_w hv0
  obtain ⟨θ0, ht0, hθ0, k0, hk0, hk0'⟩ := exists_tame_par w0 (leastSplitAuxiliaryPrimeThetaChain_spec D).1 (torsion_order_lt_auxiliary_prime D)
    ((natCast_mem_under w0 _).1 (hu0 ▸ P.basePlace_over_qZero)) (embTau D) e (P.W0.erase w0) θ1
  let θ : ∀ w : HeightOneSpectrum (𝓞 D.host.E), (w.adicCompletion D.host.E)ˣ →* ℂˣ := Function.update θ1 w0 θ0
  have e0 : θ w0 = θ0 := Function.update_self _ _ _
  have e1 : ∀ w, w ≠ w0 → θ w = θ1 w := fun w hw => Function.update_of_ne hw _ _
  have hcase : ∀ w ∈ P.W0, w = w0 ∨ (w ≠ w0 ∧ w.under (𝓞 D.host.F) ∈ S1 D) := fun w hw => by
    obtain ⟨v, hv, rfl⟩ := hW w hw
    rcases P.mem_S0_of_sum_eq.1 hv with rfl | h
    · exact Or.inl rfl
    · refine Or.inr ⟨fun hh => h0 ?_, by rwa [P.under_w hv]⟩
      rwa [← hu0, ← hh, P.under_w hv]
  obtain ⟨χ, hu, ht, hi, hunr, hloc⟩ := exists_hecke_level hcm' e P.W0 θ
    (fun w hw => by
      rcases hcase w hw with rfl | ⟨h1, h2⟩
      · rw [e0]; exact GlobalTheory.ModelChar.continuous_of_tameLoc ht0
      · obtain ⟨p, -, -, -, h, -⟩ := hθ1 w h2
        rw [e1 w h1]; exact continuous_of_level h)
    (fun w hw x => by
      rcases hcase w hw with rfl | ⟨h1, h2⟩
      · rw [e0]; exact ht0.1 x
      · obtain ⟨p, hp, -, h, -⟩ := hθ1 w h2
        rw [e1 w h1]
        exact Complex.norm_eq_one_of_pow_eq_one (by rw [← Units.val_pow_eq_pow_val, h, Units.val_one]) hp.ne_zero)
    (fun w hw w' hcj hw' => by
      obtain ⟨v, hv, rfl⟩ := hW w hw
      obtain ⟨v', hv', rfl⟩ := hW w' hw'
      have := (under_eq_iff_conjPl c hcm.rank hcm.ne _ _).2 (Or.inr hcj)
      rw [P.under_w hv, P.under_w hv'] at this
      subst this
      obtain ⟨e, he⟩ := P.w_split v' hv
      exact not_conjPl_self he hc hcj)
    (fun k hk => by
      have ep : ∏ w ∈ P.W0.erase w0, θ w (atFin w k) = ∏ w ∈ P.W0.erase w0, θ1 w (atFin w k) :=
        Finset.prod_congr rfl fun w hw => by rw [e1 w (Finset.ne_of_mem_erase hw)]
      rw [← Finset.mul_prod_erase _ _ (hW' _ hv0), ← hw0, e0, ep]
      exact hθ0 k hk)
  refine ⟨χ, hu, ht, hi, fun Q hQ => hunr Q fun w hw h => hQ ?_, fun Q hQ => ?_, fun Q hQ => ?_⟩
  · obtain ⟨v, hv, rfl⟩ := hW w hw
    rwa [h, P.under_w hv]
  · have hQ0 := P.mem_S0_of_sum_eq.2 (Or.inr hQ)
    have hun := P.under_w hQ0
    obtain ⟨σ, s1, s2, s3, s4, s5⟩ := hloc _ (hW' _ hQ0) Q hun.symm
    obtain ⟨p, hp, hp', t1, t2, k, t3, t4, t5⟩ := hθ1 (P.w (Q.under (𝓞 D.host.F))) (by rwa [hun])
    rw [e1 _ (fun h => h0 (by rwa [← hu0, ← h, hun]))] at s5
    refine ⟨⟨fun x hx hx' => (s5 x hx).2 (t2 _ ((s2 x).2 hx) (by rw [s3]; exact hx')), fun H => t5 ?_⟩, fun x hx => ?_⟩
    · obtain ⟨x, hx⟩ := s1 k
      rw [← hx] at t3 t4 ⊢
      rw [s3] at t4
      exact (s5 x ((s2 x).1 t3)).1 (H x ((s2 x).1 t3) t4)
    · have hco := coprime_card Q hp ((natCast_mem_under Q p).1 (by rwa [hun] at hp'))
      have hm : Nat.card (𝓞 D.host.E ⧸ Q.asIdeal) - 1 ≠ 0 := fun h => by
        rw [h, Nat.coprime_zero_left] at hco
        exact hp.one_lt.ne' hco
      have hxu : IsUnitAt Q x := by
        have := congrArg (fun y : (Q.adicCompletion D.host.E)ˣ => Valued.v (y : Q.adicCompletion D.host.E)) hx
        simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at this
        exact (pow_eq_one_iff_left hm).1 this
      refine (s5 x hxu).2 ((pow_eq_one_iff_of_coprime hco).1 ⟨?_, t1 _⟩)
      rw [← map_pow, s4 x _ hx, map_one]
  · obtain ⟨σ, s1, s2, s3, -, s5⟩ := hloc w0 (hW' _ hv0) Q (hQ.trans hu0.symm)
    rw [e0] at s5
    refine ⟨fun x hx hx' => (s5 x hx).2 (ht0.2 _ ((s2 x).2 hx) (by rw [s3]; exact hx')), fun H => hk0' ?_⟩
    obtain ⟨x, hx⟩ := s1 k0
    rw [← hx] at hk0 ⊢
    exact (s5 x ((s2 x).1 hk0)).1 (H x ((s2 x).1 hk0))

/- English proof (translation)
Introduce `D T L P C h0`. Use `choose χ hu ht hi hunr h1 h2 using fun i : ℕ => exists_one D T L P h0 fun τ => cen D C τ i`. Use `choose c hc using fun i => GlobalTheory.CharTransport.exists_chrEq D (χ i) (hu i)`. Use `⟨⟨χ, c, fun i _ _ => hc i, fun i _ _ => ht i, fun i _ _ => hi i, fun i _ _ => hunr i, fun i _ _ Q hQ => (h1 i Q hQ).1, fun i _ _ Q hQ => (h1 i Q ((S1_mem_OmF D).2 ?_)).2, fun i _ _ => h2 i⟩⟩` and prove the remaining obligations. Break down `hQ with h | h` into its components or cases.

Conclude with `Or.inr (Or.inr (Or.inl ((natCast_mem_under Q _).2 h)))`. Conclude with `Or.inr (Or.inr (Or.inr ((natCast_mem_under Q _).2 h)))`.
-/
theorem nonempty_chars : ∀ (D : D7) (T : Type) (L : LevCh D T) (P : Places L) (C : ℝ), P.v0 ∉ S1 D →
    Nonempty (Chars P C) := by
  intro D T L P C h0
  choose χ hu ht hi hunr h1 h2 using fun i : ℕ => exists_one D T L P h0 fun τ => cen D C τ i
  choose c hc using fun i => GlobalTheory.CharTransport.exists_chrEq D (χ i) (hu i)
  refine ⟨⟨χ, c, fun i _ _ => hc i, fun i _ _ => ht i, fun i _ _ => hi i, fun i _ _ => hunr i,
    fun i _ _ Q hQ => (h1 i Q hQ).1, fun i _ _ Q hQ => (h1 i Q ((S1_mem_OmF D).2 ?_)).2, fun i _ _ => h2 i⟩⟩
  rcases hQ with h | h
  · exact Or.inr (Or.inr (Or.inl ((natCast_mem_under Q _).2 h)))
  · exact Or.inr (Or.inr (Or.inr ((natCast_mem_under Q _).2 h)))

end GlobalTheory.GridChars
